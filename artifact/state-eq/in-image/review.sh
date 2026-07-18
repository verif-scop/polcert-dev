#!/usr/bin/env bash
set -euo pipefail

eval "$(opam env --switch=polcert --set-switch)"
exec python3 /opt/polcert-artifact/run_claim_suite.py "$@"
