#!/usr/bin/env bash
set -euo pipefail

artifact_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
manifest="$artifact_root/manifest.json"
source_repo="${POLCERT_SOURCE:-}"
image="${POLCERT_ARTIFACT_IMAGE:-polcert-artifact:state-eq-2026-08-26-v9-candidate}"
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
pluto_remote="$(read_manifest pluto.repository)"
source_commit="$(read_manifest polcert.commit)"
expected_archive_sha256="$(read_manifest polcert.archive_sha256)"
source_tag="$(read_manifest polcert.tag)"
source_tree="$(read_manifest polcert.tree)"
artifact_id="$(read_manifest artifact.id)"
packaging_revision="$(read_manifest artifact.packaging_revision)"
pluto_commit="$(read_manifest pluto.commit)"
dependency_image="$(read_manifest images.dependency_lock_origin.reference)"
expected_dependency_image_id="$(read_manifest images.dependency_lock_origin.local_image_id)"
if [[ -z "$source_image" ]]; then
  source_image="polcert-artifact-source:${source_commit:0:12}"
fi

python3 "$artifact_root/bin/validate_route_contract.py" \
  --source "$source_repo" \
  --commit "$source_commit"

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

if ! docker image inspect "$dependency_image" >/dev/null 2>&1; then
  echo "reviewed dependency origin image is missing: $dependency_image" >&2
  echo "import the image recorded by manifest.json before building" >&2
  exit 1
fi
actual_dependency_image_id="$(docker image inspect "$dependency_image" --format '{{.Id}}')"
if [[ "$actual_dependency_image_id" != "$expected_dependency_image_id" ]]; then
  echo "reviewed dependency origin image ID mismatch" >&2
  echo "  expected: $expected_dependency_image_id" >&2
  echo "  actual:   $actual_dependency_image_id" >&2
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
if [[ "$archive_sha256" != "$expected_archive_sha256" ]]; then
  echo "PolCert source archive SHA-256 mismatch" >&2
  echo "  expected: $expected_archive_sha256" >&2
  echo "  actual:   $archive_sha256" >&2
  exit 1
fi

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

# The source .dockerignore excludes generated *.scop files globally. These four
# tracked tiling-route fixtures are source inputs, so put the artifact-specific
# Dockerfile and its matching ignore file in the temporary context and admit
# only the manifest-listed paths.
source_dockerfile="$context/ArtifactSource.Dockerfile"
source_ignore="$source_dockerfile.dockerignore"
cp "$artifact_root/source-image.Dockerfile" "$source_dockerfile"
cp "$context/.dockerignore" "$source_ignore"
printf '\n# Artifact build controls are not source inputs\nArtifactSource.Dockerfile\nArtifactSource.Dockerfile.dockerignore\n' >> "$source_ignore"
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
  --file "$source_dockerfile" \
  --target development \
  --build-arg "POLCERT_DEPENDENCY_IMAGE=$dependency_image" \
  --build-arg "PLUTO_IMAGE=$base_image" \
  --build-arg "PLUTO_GIT_REMOTE=$pluto_remote" \
  --build-arg "PLUTO_GIT_COMMIT=$pluto_commit" \
  --build-arg "POLCERT_GIT_COMMIT=$source_commit" \
  --label "com.plutoverif.commit=$pluto_commit" \
  --label "com.plutoverif.remote=$pluto_remote" \
  --label "org.opencontainers.image.version=$source_tag" \
  --label "org.opencontainers.image.revision=$source_commit" \
  --label "io.polcert.artifact.id=$artifact_id" \
  --label "io.polcert.packaging.revision=$packaging_revision" \
  --label "io.polcert.publication.status=source-stage" \
  --label "io.polcert.source.tree=$source_tree" \
  --label "io.polcert.source.archive.sha256=$archive_sha256" \
  --label "io.polcert.pluto.revision=$pluto_commit" \
  --label "io.polcert.review.required.network=none" \
  --tag "$source_image" \
  "$context"

fixture_check='test ! -e /polcert/ArtifactSource.Dockerfile && test ! -e /polcert/ArtifactSource.Dockerfile.dockerignore'
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

docker run --rm --network none --entrypoint python3 "$image" -c \
  'import sys; sys.path.insert(0, "/opt/polcert-artifact"); import claim_evidence as c; assert len(c.expected_outer_routes("full")) == 13; assert len(c.expected_artifact_routes("full")) == 29; assert len(c.expected_artifact_routes("extended")) == 30'
echo "[artifact-build] reviewer Python compatibility passed"

python3 "$artifact_root/bin/write_build_metadata.py" \
  --image "$image" \
  --source-image "$source_image" \
  --pluto-base-image "$base_image" \
  --dependency-origin-image "$dependency_image" \
  --source-archive-sha256 "$archive_sha256" \
  --manifest "$manifest" \
  --output "$output_dir/build-metadata.json"

echo "[artifact-build] image: $image"
echo "[artifact-build] metadata: $output_dir/build-metadata.json"
