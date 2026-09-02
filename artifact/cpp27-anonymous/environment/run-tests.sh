#!/usr/bin/env bash
set -euo pipefail

cd /polcert
eval "$(opam env --switch=polcert)"

mode="${1:-smoke}"
shift || true

run_ci() {
  local shard shard_list
  if (($# > 1)); then
    printf 'usage: run-polcert-artifact ci [shard]\n' >&2
    return 2
  fi
  if (($# == 1)); then
    exec bash tools/ci/run_ci_shard.sh "$1"
  fi
  shard_list="$(bash tools/ci/run_ci_shard.sh --list)"
  if [[ -z "${shard_list}" ]]; then
    printf 'CI shard list is empty\n' >&2
    return 1
  fi
  while read -r shard; do
    bash tools/ci/run_ci_shard.sh "${shard}"
  done <<< "${shard_list}"
}

case "${mode}" in
  smoke)
    exec python3 tools/artifact/run_artifact_check.py --mode smoke
    ;;
  full)
    exec python3 tools/artifact/run_artifact_check.py --mode full
    ;;
  ci)
    run_ci "$@"
    ;;
  all)
    python3 tools/artifact/run_artifact_check.py --mode full
    run_ci
    ;;
  bugs)
    exec make test-pluto-bugs
    ;;
  performance)
    exec make test-end-to-end-generated-perf
    ;;
  proof)
    . tools/ci/ci_resources.sh
    jobs="$(ci_choose_jobs PROOF_JOBS 2 6144)"
    make clean
    make depend
    make -j"${jobs}" proof
    make -s check-admitted
    exec make -j"${jobs}" extraction
    ;;
  shell)
    exec bash
    ;;
  *)
    printf 'unknown mode: %s\n' "${mode}" >&2
    printf 'modes: smoke, full, ci [shard], bugs, performance, proof, all, shell\n' >&2
    exit 2
    ;;
esac
