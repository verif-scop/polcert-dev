#!/usr/bin/env bash
set -euo pipefail

cd /polcert

# shellcheck disable=SC1091
source /polcert/tools/ci/pluto-baseline.env

if [[ "$PLUTO_IMAGE" == *:latest ]]; then
  echo "[ci] WARNING: PLUTO_IMAGE still uses :latest; publish and pin a versioned image tag such as ${PLUTO_VERSIONED_IMAGE:-<set PLUTO_VERSIONED_IMAGE>}" >&2
fi

require_match() {
  local name="$1"
  local expected="$2"
  local actual="$3"
  if [[ "$actual" != "$expected" ]]; then
    echo "[ci] Pluto baseline mismatch for $name" >&2
    echo "[ci]   expected: $expected" >&2
    echo "[ci]   actual:   $actual" >&2
    exit 1
  fi
}

baked_values=(
  "${POLCERT_PLUTO_IMAGE:-}"
  "${POLCERT_PLUTO_GIT_REMOTE:-}"
  "${POLCERT_PLUTO_GIT_COMMIT:-}"
)

baked_count=0
for value in "${baked_values[@]}"; do
  if [[ -n "$value" ]]; then
    baked_count=$((baked_count + 1))
  fi
done

if [[ "$baked_count" -ne 0 && "$baked_count" -ne 3 ]]; then
  echo "[ci] Incomplete baked Pluto metadata in image environment" >&2
  exit 1
fi

if [[ "$baked_count" -eq 3 ]]; then
  require_match "POLCERT_PLUTO_IMAGE" "$PLUTO_IMAGE" "${POLCERT_PLUTO_IMAGE}"
  require_match "POLCERT_PLUTO_GIT_REMOTE" "$PLUTO_GIT_REMOTE" "${POLCERT_PLUTO_GIT_REMOTE}"
  require_match "POLCERT_PLUTO_GIT_COMMIT" "$PLUTO_GIT_COMMIT" "${POLCERT_PLUTO_GIT_COMMIT}"
else
  echo "[ci] No baked Pluto metadata found; validating live /pluto checkout only"
fi

actual_remote="$(git -C /pluto remote get-url origin)"
require_match "/pluto origin" "$PLUTO_GIT_REMOTE" "$actual_remote"

actual_head="$(git -C /pluto rev-parse HEAD)"
if [[ "$actual_head" == "$PLUTO_GIT_COMMIT" ]]; then
  :
elif git -C /pluto merge-base --is-ancestor "$PLUTO_GIT_COMMIT" "$actual_head" &&
     git -C /pluto diff --quiet "$PLUTO_GIT_COMMIT..$actual_head" -- . ':(exclude)Dockerfile'; then
  echo "[ci] Pluto checkout includes packaging-only commits on top of the pinned compiler baseline" >&2
else
  echo "[ci] Pluto baseline mismatch for /pluto HEAD" >&2
  echo "[ci]   expected compiler baseline: $PLUTO_GIT_COMMIT" >&2
  echo "[ci]   actual HEAD:              $actual_head" >&2
  exit 1
fi

if ! git -C /pluto diff --quiet --ignore-submodules=dirty HEAD -- . ':(exclude)Dockerfile'; then
  echo "[ci] Pluto tracked compiler sources differ from the pinned baseline" >&2
  git -C /pluto status --short --branch >&2
  exit 1
fi

pluto_version_line="$(pluto --version 2>&1 | sed -n '1p' || true)"
short_commit="${PLUTO_GIT_COMMIT:0:7}"
if [[ "$pluto_version_line" != *"$short_commit"* ]]; then
  echo "[ci] Pluto binary version does not mention pinned commit $short_commit" >&2
  echo "[ci]   pluto --version: $pluto_version_line" >&2
  exit 1
fi

echo "[ci] Pluto baseline OK: $short_commit from $PLUTO_GIT_REMOTE"
