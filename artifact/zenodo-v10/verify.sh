#!/usr/bin/env bash
set -euo pipefail

ROOT=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
cd "$ROOT"

IMAGE="polcert-artifact:state-eq-polyhedral-verification-complete-2026-08-29-v10"
IMAGE_ID="sha256:6404668840fdac7333abf47f8784b5514e7ca94baa7d47d48fc6e6c6b7d9510a"
IMAGE_ARCHIVE="polcert-v10-docker-image.tar"
EVIDENCE_ARCHIVE="polcert-v10-evidence.zip"

usage() {
  cat <<'EOF'
Usage: ./verify.sh {quick|full|evidence|checksums}

  quick      Run representative proof, executable, and rejection checks.
  full       Run all 30 artifact checks and copy their result tree.
  evidence   Print the summary of the frozen full artifact run.
  checksums  Verify the seven other files in this Zenodo package.
EOF
}

check_files() {
  sha256sum -c SHA256SUMS
}

load_image() {
  docker load -i "$IMAGE_ARCHIVE"
  local actual
  actual=$(docker image inspect "$IMAGE" --format '{{.Id}}')
  if [[ "$actual" != "$IMAGE_ID" ]]; then
    printf 'image ID mismatch: expected %s, got %s\n' "$IMAGE_ID" "$actual" >&2
    exit 1
  fi
}

run_quick() {
  check_files
  load_image
  docker run --rm --entrypoint bash "$IMAGE" -lc '
    set -euo pipefail
    eval "$(opam env --switch=polcert)"
    python3 tools/artifact/proof_report.py \
      --json-out /tmp/polcert-proof-report.json \
      --markdown-out /tmp/polcert-proof-report.md
    opam exec --switch=polcert -- make test-extracted-zero-fallback
    opam exec --switch=polcert -- make test-end-to-end-c-correctness
    opam exec --switch=polcert -- make test-pluto-bugs
  '
}

run_full() {
  check_files
  load_image

  local container="polcert-v10-full-$$"
  cleanup() {
    docker rm -f "$container" >/dev/null 2>&1 || true
  }
  trap cleanup EXIT

  docker create --name "$container" --entrypoint bash "$IMAGE" -lc '
    set -euo pipefail
    eval "$(opam env --switch=polcert)"
    python3 tools/artifact/run_artifact_check.py \
      --mode full \
      --output-root /tmp/polcert-artifact-check
  ' >/dev/null

  set +e
  docker start -a "$container"
  local status=$?
  set -e

  mkdir -p review-results
  rm -rf review-results/polcert-artifact-check
  docker cp \
    "$container:/tmp/polcert-artifact-check" \
    review-results/polcert-artifact-check

  if (( status != 0 )); then
    printf 'full evaluation failed; logs were copied to %s\n' \
      "$ROOT/review-results/polcert-artifact-check" >&2
    exit "$status"
  fi
  printf 'full results: %s\n' \
    "$ROOT/review-results/polcert-artifact-check/artifact-results.json"
}

show_evidence() {
  check_files
  python3 - "$EVIDENCE_ARCHIVE" <<'PY'
import json
import sys
import zipfile

with zipfile.ZipFile(sys.argv[1]) as archive:
    result = json.loads(
        archive.read("artifact-check/artifact-results.json").decode("utf-8")
    )

checks = result.get("results", [])
passed = sum(bool(check.get("ok")) for check in checks)
print(f"mode: {result.get('mode')}")
print(f"status: {'passed' if result.get('ok') else 'failed'}")
print(f"checks: {passed}/{len(checks)}")
print(f"elapsed: {sum(float(c.get('elapsed_seconds', 0)) for c in checks):.1f}s")
for check in checks:
    status = "PASS" if check.get("ok") else "FAIL"
    print(f"{status:4}  {check.get('elapsed_seconds', 0):8.1f}s  {check.get('name')}")
PY
}

case "${1:-}" in
  quick) run_quick ;;
  full) run_full ;;
  evidence) show_evidence ;;
  checksums) check_files ;;
  *) usage >&2; exit 2 ;;
esac
