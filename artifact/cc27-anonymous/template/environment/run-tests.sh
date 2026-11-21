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

run_bugs() {
  local output="$1"
  local status=0
  python3 /usr/local/lib/polcert/run-paper-bugs.py \
    --source-root /polcert --buggy-root "${POLCERT_BUGGY_ROOT}" \
    --fixed-pluto "${POLCERT_PLUTO}" --output "${output}/recorded-five" || status=1
  python3 /usr/local/lib/polcert/run-new-bugs.py \
    --source-root /polcert --historical-pluto "${POLCERT_BUGGY_PLUTO}" \
    --fixed-pluto "${POLCERT_PLUTO}" --inputs /usr/local/lib/polcert/new-bugs \
    --output "${output}/added" || status=1
  return "${status}"
}

case "${mode}" in
  smoke)
    exec make check-smoke
    ;;
  full)
    exec make check-full
    ;;
  ci)
    run_ci "$@"
    ;;
  all)
    make check-full
    run_ci
    ;;
  bugs)
    if (($#)); then
      bug_output="$1"
      shift
    else
      bug_output="$(mktemp -d /tmp/polcert-bugs.XXXXXX)"
    fi
    run_bugs "${bug_output}"
    ;;
  bugs-extended)
    exec make test-pluto-bugs
    ;;
  evaluation-data)
    exec python3 evaluation/bin/run_evaluation.py "$@"
    ;;
  proof)
    . tools/ci/ci_resources.sh
    jobs="$(ci_choose_jobs PROOF_JOBS 8 6144)"
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
    printf 'modes: smoke, full, ci [shard], bugs [output], bugs-extended, evaluation-data, proof, all, shell\n' >&2
    exit 2
    ;;
esac
