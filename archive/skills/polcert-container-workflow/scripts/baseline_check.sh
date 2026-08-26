#!/usr/bin/env bash
set -euo pipefail

container="${1:-gifted_curie}"
repo="${2:-/polcert}"

echo "[baseline] container=${container} repo=${repo}"

if ! docker ps --format '{{.Names}}' | grep -qx "${container}"; then
  echo "[error] container '${container}' is not running"
  exit 1
fi

docker exec "${container}" sh -lc "
set -e
cd '${repo}'
echo '[baseline] git branch/commit'
git branch --show-current
git rev-parse --short HEAD

echo '[baseline] opam switch env'
eval \$(opam env --switch=polcert --set-switch)
command -v ocamldep
command -v coqc

echo '[baseline] admitted scan'
make -s check-admitted

echo '[baseline] validator smoke test'
./polcert tests/csample3/polcert46ff92.scop.beforescheduling.scop tests/csample3/polcert46ff92.scop.afterscheduling.scop
"

echo "[baseline] done"
