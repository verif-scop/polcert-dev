#!/usr/bin/env bash
set -euo pipefail

cd /polcert

eval "$(opam env)"

bash /polcert/tools/ci/check_pluto_baseline.sh

make clean
opam exec -- make depend
opam exec -- make proof
opam exec -- make -s check-admitted
opam exec -- make extraction
opam exec -- make polopt
opam exec -- make polcert.ini
opam exec -- make polcert
opam exec -- make test
opam exec -- make test-iss-pluto-suite
opam exec -- make test-iss-pluto-live-suite
opam exec -- make test-polopt-loop-suite
