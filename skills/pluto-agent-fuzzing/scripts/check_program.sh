#!/usr/bin/env bash
# Check one test program against Pluto, with PolCert in the loop.
#
# usage: check_program.sh PROG.loop [PLUTO FLAGS...]
#   Run inside the PolCert development image, from a built PolCert tree.
#   The same flags go to Pluto's polycc and to `polopt --pluto-compat`
#   (state --intratileopt or --nointratileopt explicitly).
#   PLUTO_ROOT  Pluto build with PolCert's export hooks (default: the image's
#               historical snapshot); its polycc gives Pluto's own output and
#               its tool/pluto is the optimizer that polopt calls.
#   POLOPT_FLAGS  flags for polopt when they must differ from Pluto's (polopt
#               refuses some combinations, e.g. --prevector with --parallel);
#               PolCert then still serves as the reference for the source.
#   TILE_SIZES  optional tile-size file for both compilers.
#   KEEP_DIR    keep the work directory of every result other than OK.
#
# Prints: <prog> <class> <detail>
#   PLUTO-BUG validator  PolCert rejected the proposal and Pluto's output is wrong;
#                        the detail names the rejecting stage
#   PLUTO-BUG reference  PolCert compiled it correctly and Pluto's output is wrong
#   POLCERT-INCOMPLETE   PolCert rejected, but Pluto's output is right
#   OK                   both outputs agree with the source
#   SOUNDNESS?           PolCert's output disagrees with the source: STOP, report it
#   SKIP                 source has UB, input unsupported, or Pluto crashed
set -u
prog=$(realpath "$1"); shift
name=$(basename "$prog" .loop)
here=$(cd "$(dirname "$0")" && pwd)
tree=$PWD
pluto_root=${PLUTO_ROOT:-/opt/polcert/pluto-buggy}
work=$(mktemp -d)
say() {
  echo "$name $*"
  if [ "$1" != OK ] && [ -n "${KEEP_DIR:-}" ]; then mkdir -p "$KEEP_DIR"; cp -r "$work" "$KEEP_DIR/$name"; fi
  rm -rf "$work"; rm -f "$tree"/polcert*.scop*; exit 0
}
cc() { gcc -w "$@" -lm 2>>"$work/cc.log"; }

# Run a C program in every configuration; print ok or wrong:<how>.
runs() {
  local c=$1 b=$work/$2
  cc -O0 "$c" -o "$b.seq" && cc -O0 -fopenmp "$c" -o "$b.omp" || { echo nocompile; return; }
  [ "$(timeout 20 "$b.seq" 2>/dev/null)" = "$exp" ] || { echo wrong:sequential; return; }
  [ "$(OMP_NUM_THREADS=1 timeout 20 "$b.omp" 2>/dev/null)" = "$exp" ] || { echo wrong:openmp-one-thread; return; }
  cc -O1 -fopenmp -fsanitize=undefined -fno-sanitize-recover=all "$c" -o "$b.san"
  OMP_NUM_THREADS=1 timeout 60 "$b.san" >"$b.san.out" 2>"$b.san.err" \
    && [ "$(cat "$b.san.out")" = "$exp" ] || { echo wrong:ubsan; return; }
  if grep -q 'pragma omp' "$c"; then
    local bad=0 t r
    for t in 2 4 8; do for r in 1 2 3 4; do
      [ "$(OMP_NUM_THREADS=$t timeout 20 "$b.omp" 2>/dev/null)" = "$exp" ] || bad=$((bad + 1))
    done; done
    [ $bad -eq 0 ] || { echo "wrong:race($bad/12)"; return; }
  fi
  echo ok
}

# 1. The source program in C, and its expected output.
python3 "$here/loop_programs.py" source "$prog" "$work/src.c" 2>"$work/conv.err" \
  || say SKIP "cannot convert: $(tail -1 "$work/conv.err")"
cc -O0 -fsanitize=undefined -fno-sanitize-recover=all "$work/src.c" -o "$work/ref" \
  && exp=$(timeout 60 "$work/ref") || say SKIP "source fails or has UB"

# 2. Pluto's own output, from the same Pluto that PolCert calls.
ts=(); if [ -n "${TILE_SIZES:-}" ]; then cp "$TILE_SIZES" "$work/tile.sizes"; ts=(--tile-sizes-file "$TILE_SIZES"); fi
(cd "$work" && timeout 120 "$pluto_root/polycc" src.c "$@" -o pluto.c >pluto.log 2>&1) && [ -s "$work/pluto.c" ] \
  && pluto=$(runs "$work/pluto.c" pluto) || pluto=crash

# 3. PolCert with all validators enabled.
if [ -n "${POLOPT_FLAGS+x}" ]; then read -ra oflags <<<"$POLOPT_FLAGS"; else oflags=("$@"); fi
POLCERT_PLUTO=$pluto_root/tool/pluto COMPCERT_CONFIG=$tree/polcert.ini \
  ./polopt --pluto-compat "${oflags[@]}" "${ts[@]}" "$prog" >"$work/polopt.out" 2>"$work/polopt.err"
if [ $? -ne 0 ]; then
  stage=$(grep -m1 -E 'validation failed|validation rejected|scheduler failed' "$work/polopt.err" | sed 's/.*runtime: //')
  [ -n "$stage" ] || say SKIP "pluto=$pluto; polopt: $(grep -m1 -E 'reject:|rror' "$work/polopt.err" | cut -c1-90)"
  case $pluto in
    wrong:*) say PLUTO-BUG validator "pluto=$pluto; $stage" ;;
    ok)      say POLCERT-INCOMPLETE "$stage" ;;
    *)       say SKIP "pluto $pluto; polopt: $stage" ;;
  esac
fi
awk '/== Optimized Loop ==/{f=1; next} /^== /{f=0} f' "$work/polopt.out" >"$work/opt.loop"
python3 "$here/loop_programs.py" optimized "$prog" "$work/opt.loop" "$work/polcert.c" 2>>"$work/conv.err" \
  || say SKIP "cannot convert PolCert's output"
polcert=$(runs "$work/polcert.c" polcert)

# 4. Three-way comparison.
[ "$polcert" = ok ] || say SOUNDNESS? "polcert=$polcert pluto=$pluto"
case $pluto in
  wrong:*) say PLUTO-BUG reference "pluto=$pluto; PolCert's output is correct" ;;
  ok)      say OK ;;
  *)       say SKIP "pluto $pluto; PolCert's output is correct" ;;
esac
