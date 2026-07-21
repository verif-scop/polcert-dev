#!/usr/bin/env bash
set -euo pipefail

artifact_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
manifest="$artifact_root/manifest.json"
source_repo="${POLCERT_SOURCE:-}"
image="${POLCERT_ARTIFACT_IMAGE:-polcert-artifact:state-eq-2026-07-21-v3-candidate}"
source_image="${POLCERT_ARTIFACT_SOURCE_IMAGE:-}"
output_dir="${POLCERT_ARTIFACT_BUILD_OUTPUT:-$artifact_root/build}"
validate_only=0

usage() {
  cat <<'EOF'
Usage: build-image.sh --source PATH [--image NAME] [--output-dir PATH] [--validate-only]

Builds the artifact from an exact git archive of the manifest commit. The
source checkout is read only; its worktree contents are never used as build
input.
EOF
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --source) source_repo="$2"; shift 2 ;;
    --image) image="$2"; shift 2 ;;
    --output-dir) output_dir="$2"; shift 2 ;;
    --validate-only) validate_only=1; shift ;;
    -h|--help) usage; exit 0 ;;
    *) echo "unknown argument: $1" >&2; usage >&2; exit 2 ;;
  esac
done

if [[ -z "$source_repo" ]]; then
  echo "--source PATH or POLCERT_SOURCE is required" >&2
  exit 2
fi

mkdir -p "$output_dir"
python3 "$artifact_root/bin/validate_source.py" \
  --source "$source_repo" \
  --manifest "$manifest" \
  --json-out "$output_dir/source-validation.json"

read_manifest() {
  python3 - "$manifest" "$1" <<'PY'
import json
import sys

value = json.load(open(sys.argv[1]))
for key in sys.argv[2].split("."):
    value = value[key]
print(value)
PY
}

base_image="$(read_manifest pluto.base_image)"
expected_base_digest="$(read_manifest pluto.base_image_digest)"
source_commit="$(read_manifest polcert.commit)"
source_tag="$(read_manifest polcert.tag)"
source_tree="$(read_manifest polcert.tree)"
artifact_id="$(read_manifest artifact.id)"
packaging_revision="$(read_manifest artifact.packaging_revision)"
pluto_commit="$(read_manifest pluto.commit)"
if [[ -z "$source_image" ]]; then
  source_image="polcert-artifact-source:${source_commit:0:12}"
fi

if ! docker image inspect "$base_image" >/dev/null 2>&1; then
  echo "[artifact-build] pulling missing Pluto base image $base_image" >&2
  docker pull "$base_image"
fi

actual_base_digests="$(docker image inspect "$base_image" --format '{{join .RepoDigests "\n"}}')"
if [[ "$actual_base_digests" != *"@$expected_base_digest"* ]]; then
  echo "Pluto base image digest mismatch" >&2
  echo "  expected: $expected_base_digest" >&2
  echo "  actual:   $actual_base_digests" >&2
  exit 1
fi

if [[ "$validate_only" -eq 1 ]]; then
  echo "[artifact-build] source and Pluto base image validation passed"
  exit 0
fi

stage="$(mktemp -d /tmp/polcert-state-eq-artifact.XXXXXX)"
trap 'rm -rf "$stage"' EXIT
archive="$stage/polcert-source.tar"
context="$stage/context"
mkdir -p "$context"

git -C "$source_repo" archive --format=tar --output="$archive" "$source_commit"
tar -xf "$archive" -C "$context"
archive_sha256="$(sha256sum "$archive" | awk '{print $1}')"

mapfile -t required_source_files < <(
  python3 - "$manifest" <<'PY'
import json
import sys

manifest = json.load(open(sys.argv[1]))
for path in manifest["reproducibility"]["source_context_required_files"]:
    print(path)
PY
)
if [[ "${#required_source_files[@]}" -eq 0 ]]; then
  echo "manifest source_context_required_files must not be empty" >&2
  exit 1
fi

# The frozen source .dockerignore excludes generated *.scop files globally.
# These four tracked differential fixtures are source inputs, so use a
# Dockerfile-specific ignore file to admit only the manifest-listed paths.
source_ignore="$context/Dockerfile.dockerignore"
cp "$context/.dockerignore" "$source_ignore"
printf '\n# Artifact-required tracked source fixtures\nDockerfile.dockerignore\n' >> "$source_ignore"
for path in "${required_source_files[@]}"; do
  if [[ "$path" = /* || "$path" == *".."* || ! -f "$context/$path" ]]; then
    echo "invalid or missing required source-context file: $path" >&2
    exit 1
  fi
  printf '!%s\n' "$path" >> "$source_ignore"
done

echo "[artifact-build] building exact source image $source_image"
docker build \
  --pull=false \
  --label "org.opencontainers.image.revision=$source_commit" \
  --label "io.polcert.source.tree=$source_tree" \
  --label "io.polcert.source.archive.sha256=$archive_sha256" \
  --tag "$source_image" \
  "$context"

fixture_check='test ! -e /polcert/Dockerfile.dockerignore'
for path in "${required_source_files[@]}"; do
  fixture_check+=" && test -f /polcert/$path"
done
docker run --rm --network none --entrypoint sh "$source_image" -eu -c "$fixture_check"
echo "[artifact-build] required tracked source fixtures are present"

echo "[artifact-build] verifying captured dependency closure"
python3 "$artifact_root/bin/dependency_lock.py" verify-image \
  --image "$source_image" \
  --lock "$artifact_root/locks/dependency-lock.json" \
  --manifest "$manifest"

echo "[artifact-build] adding reviewer entry point to $image"
docker build \
  --pull=false \
  --file "$artifact_root/Dockerfile" \
  --build-arg "POLCERT_SOURCE_IMAGE=$source_image" \
  --build-arg "POLCERT_ARTIFACT_ID=$artifact_id" \
  --build-arg "POLCERT_PACKAGING_REVISION=$packaging_revision" \
  --build-arg "POLCERT_SOURCE_TAG=$source_tag" \
  --build-arg "POLCERT_SOURCE_COMMIT=$source_commit" \
  --build-arg "POLCERT_SOURCE_TREE=$source_tree" \
  --build-arg "PLUTO_SOURCE_COMMIT=$pluto_commit" \
  --tag "$image" \
  "$artifact_root"

python3 "$artifact_root/bin/write_build_metadata.py" \
  --image "$image" \
  --source-image "$source_image" \
  --pluto-base-image "$base_image" \
  --source-archive-sha256 "$archive_sha256" \
  --manifest "$manifest" \
  --output "$output_dir/build-metadata.json"

echo "[artifact-build] image: $image"
echo "[artifact-build] metadata: $output_dir/build-metadata.json"
