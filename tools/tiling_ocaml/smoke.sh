set -eu

ROOT_DIR="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
cd "$ROOT_DIR"

if [ ! -x _build/default/pluto_tiling_ocaml.exe ]; then
  dune build pluto_tiling_ocaml.exe
fi

_build/default/pluto_tiling_ocaml.exe validate --json fixtures/second_level_before.scop fixtures/second_level_after.scop > /tmp/second_level_report.json
rg -q '"shape_ok": true' /tmp/second_level_report.json
rg -q '"transformation_contract_ok": true' /tmp/second_level_report.json

_build/default/pluto_tiling_ocaml.exe extract fixtures/basic_before.scop fixtures/basic_after.scop
_build/default/pluto_tiling_ocaml.exe validate fixtures/basic_before.scop fixtures/basic_after.scop
_build/default/pluto_tiling_ocaml.exe validate --check-bounded-coverage fixtures/basic_before.scop fixtures/basic_after.scop

second_level_output="$(_build/default/pluto_tiling_ocaml.exe extract fixtures/second_level_before.scop fixtures/second_level_after.scop)"
printf '%s\n' "$second_level_output"
case "$second_level_output" in
  *"tile link: f1 = floor((k) / 32)"*"tile link: f0 = floor((f1) / 8)"*) ;;
  *)
    echo "expected second-level witness order f1 then f0" >&2
    exit 1
    ;;
esac
_build/default/pluto_tiling_ocaml.exe validate fixtures/second_level_before.scop fixtures/second_level_after.scop
python3 ../validate_pluto_tiling.py validate fixtures/second_level_before.scop fixtures/second_level_after.scop

_build/default/pluto_tiling_ocaml.exe extract --json fixtures/basic_before.scop fixtures/basic_after.scop > /tmp/basic_tiling_witness.json
_build/default/pluto_tiling_ocaml.exe check fixtures/basic_before.scop fixtures/basic_after.scop /tmp/basic_tiling_witness.json

sed 's/"tile_size": 32/"tile_size": 31/' /tmp/basic_tiling_witness.json > /tmp/basic_tiling_witness_bad.json
if _build/default/pluto_tiling_ocaml.exe check fixtures/basic_before.scop fixtures/basic_after.scop /tmp/basic_tiling_witness_bad.json; then
  echo "expected tampered witness to fail" >&2
  exit 1
fi

python3 ../validate_pluto_tiling.py extract --json fixtures/basic_before.scop fixtures/basic_after.scop > /tmp/py_witness.json
_build/default/pluto_tiling_ocaml.exe check fixtures/basic_before.scop fixtures/basic_after.scop /tmp/py_witness.json

_build/default/pluto_tiling_ocaml.exe extract --json fixtures/basic_before.scop fixtures/basic_after.scop > /tmp/ocaml_witness.json
python3 ../validate_pluto_tiling.py check fixtures/basic_before.scop fixtures/basic_after.scop /tmp/ocaml_witness.json

python3 ../validate_pluto_tiling.py extract fixtures/second_level_before.scop fixtures/second_level_after.scop
python3 ../validate_pluto_tiling.py extract --json fixtures/second_level_before.scop fixtures/second_level_after.scop > /tmp/py_second_level_witness.json
_build/default/pluto_tiling_ocaml.exe check fixtures/second_level_before.scop fixtures/second_level_after.scop /tmp/py_second_level_witness.json
_build/default/pluto_tiling_ocaml.exe extract --json fixtures/second_level_before.scop fixtures/second_level_after.scop > /tmp/ocaml_second_level_witness.json
python3 ../validate_pluto_tiling.py check fixtures/second_level_before.scop fixtures/second_level_after.scop /tmp/ocaml_second_level_witness.json

if _build/default/pluto_tiling_ocaml.exe check fixtures/second_level_before.scop fixtures/second_level_after.scop fixtures/second_level_bad_witness.json; then
  echo "expected unresolved second-level witness to fail" >&2
  exit 1
fi

if _build/default/pluto_tiling_ocaml.exe check --json fixtures/second_level_before.scop fixtures/second_level_after.scop fixtures/second_level_bad_witness.json > /tmp/second_level_bad.json; then
  echo "expected unresolved second-level witness json path to fail" >&2
  exit 1
fi
rg -q '"ok": false' /tmp/second_level_bad.json
rg -q '"error": "cannot topologically order tile links' /tmp/second_level_bad.json

echo "smoke: PASS"
