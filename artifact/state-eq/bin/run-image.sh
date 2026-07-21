#!/usr/bin/env bash
set -euo pipefail

artifact_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
image="${POLCERT_ARTIFACT_IMAGE:-polcert-artifact:state-eq-2026-07-21-v3-candidate}"
output_dir="${POLCERT_ARTIFACT_OUTPUT:-$artifact_root/results}"
mode="full"

usage() {
  cat <<'EOF'
Usage: run-image.sh [--image NAME] [--output-dir PATH] [--mode smoke|full|extended]

Runs the built artifact with networking disabled. Results are written to the
mounted output directory.
EOF
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --image) image="$2"; shift 2 ;;
    --output-dir) output_dir="$2"; shift 2 ;;
    --mode) mode="$2"; shift 2 ;;
    -h|--help) usage; exit 0 ;;
    *) echo "unknown argument: $1" >&2; usage >&2; exit 2 ;;
  esac
done

if [[ "$mode" != "smoke" && "$mode" != "full" && "$mode" != "extended" ]]; then
  echo "mode must be smoke, full, or extended" >&2
  exit 2
fi

mkdir -p "$output_dir"
output_dir="$(cd "$output_dir" && pwd)"
if find "$output_dir" -mindepth 1 -maxdepth 1 -print -quit | grep -q .; then
  echo "output directory must be empty: $output_dir" >&2
  echo "use a new directory or run 'make clean-results' explicitly" >&2
  exit 2
fi

docker run --rm \
  --network none \
  --volume "$output_dir:/artifact-results" \
  "$image" "$mode"
