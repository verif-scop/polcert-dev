#!/usr/bin/env bash
set -eu

ROOT_DIR="$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)"
CONTAINER="${POLCERT_CONTAINER:-gifted_curie}"
CONTAINER_DIR="${POLCERT_CONTAINER_DIR:-/polcert}"

run_polopt() {
  local args="$1"
  docker exec "$CONTAINER" sh -lc "cd '$CONTAINER_DIR' && ./polopt $args"
}

require_contains() {
  local haystack="$1"
  local needle="$2"
  if ! printf '%s\n' "$haystack" | grep -Fq "$needle"; then
    printf 'expected output to contain: %s\n' "$needle" >&2
    exit 1
  fi
}

require_not_contains() {
  local haystack="$1"
  local needle="$2"
  if printf '%s\n' "$haystack" | grep -Fq "$needle"; then
    printf 'expected output not to contain: %s\n' "$needle" >&2
    exit 1
  fi
}

cd "$ROOT_DIR"

default_nodep="$(run_polopt "--parallel tests/polopt-generated/inputs/nodep.loop")"
require_contains "$default_nodep" "parallel for i0 in range(0, 4)"

default_manual_tiled_nodep="$(run_polopt "--parallel-current 0 tests/polopt-generated/inputs/nodep.loop")"
require_contains "$default_manual_tiled_nodep" "parallel for i0 in range(0, 4)"

iss_nodep="$(run_polopt "--iss --parallel tests/polopt-generated/inputs/nodep.loop")"
require_contains "$iss_nodep" "parallel for i0 in range(0, 4)"

iss_manual_tiled_nodep="$(run_polopt "--iss --parallel-current 0 tests/polopt-generated/inputs/nodep.loop")"
require_contains "$iss_manual_tiled_nodep" "parallel for i0 in range(0, 4)"

iss_affine_nodep="$(run_polopt "--iss --notile --parallel tests/polopt-generated/inputs/nodep.loop")"
require_contains "$iss_affine_nodep" "parallel for i0 in range(0, 100)"

iss_identity_manual_nodep="$(run_polopt "--iss --identity --parallel-current 0 tests/polopt-generated/inputs/nodep.loop")"
require_contains "$iss_identity_manual_nodep" "parallel for i0 in range(0, 100)"

iss_affine_manual_nodep="$(run_polopt "--iss --notile --parallel-current 0 tests/polopt-generated/inputs/nodep.loop")"
require_contains "$iss_affine_manual_nodep" "parallel for i0 in range(0, 100)"

manual_tiled_matmul="$(run_polopt "--parallel-current 1 tests/polopt-generated/inputs/matmul.loop")"
require_contains "$manual_tiled_matmul" "parallel for i1 in range(0, ((N + 31) / 32))"

iss_manual_tiled_matmul="$(run_polopt "--iss --parallel-current 1 tests/polopt-generated/inputs/matmul.loop")"
require_contains "$iss_manual_tiled_matmul" "parallel for i1 in range(0, ((N + 31) / 32))"

strict_matmul="$(run_polopt "--parallel --parallel-strict tests/polopt-generated/inputs/matmul.loop" 2>&1)"
require_contains "$strict_matmul" "[alarm] optimization triggered a checked fallback or warning"
require_not_contains "$strict_matmul" "parallel for"

iss_strict_matmul="$(run_polopt "--iss --parallel --parallel-strict tests/polopt-generated/inputs/matmul.loop" 2>&1)"
require_contains "$iss_strict_matmul" "[alarm] optimization triggered a checked fallback or warning"
require_not_contains "$iss_strict_matmul" "parallel for"

echo "polopt parallel smoke: PASS"
