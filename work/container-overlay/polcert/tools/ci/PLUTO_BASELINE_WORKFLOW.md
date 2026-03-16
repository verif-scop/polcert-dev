# Pluto Baseline Workflow

This repository now treats the Pluto baseline as explicit CI input rather than
an implicit property of `hughshine/pluto-verif:latest`.

## Source of truth

`tools/ci/pluto-baseline.env` is the single source of truth for:

- `PLUTO_IMAGE`: the Pluto base image currently consumed by PolCert CI
- `PLUTO_BASELINE_TAG`: the versioned Git/image tag name to use when publishing
  the next pinned Pluto baseline
- `PLUTO_VERSIONED_IMAGE`: the versioned Pluto base image name that should
  eventually replace `PLUTO_IMAGE`
- `PLUTO_GIT_REMOTE`
- `PLUTO_GIT_COMMIT`

The PolCert Dockerfile defaults must stay aligned with this file.

`PLUTO_GIT_COMMIT` identifies the pinned Pluto compiler-source baseline.
The published Pluto image/tag may sit on top of that commit with a packaging-only
Dockerfile commit, but it must not change tracked compiler sources.

## Current shape

The current flow deliberately preserves the large Docker cache boundary:

1. PolCert still starts from a Pluto base image.
2. CI passes the Pluto baseline metadata into the PolCert image build.
3. `tools/ci/check_pluto_baseline.sh` verifies the live `/pluto` checkout and
   binary before the main build/test chain.

This keeps existing cache behavior while making Pluto version drift visible.

## Pluto-side packaging rule

The Pluto repository Dockerfile should build the current checkout. It should
not `reset --hard origin/master` during the image build.

That packaging rule is intentionally treated as separate from the Pluto
compiler-source baseline check. The checker allows `/pluto` to be a
Dockerfile-only descendant of `PLUTO_GIT_COMMIT`, but still rejects
compiler-source drift.

## How to publish a new pinned Pluto baseline

1. Make the desired Pluto source commit clean and stable in the Pluto repo.
2. Tag it in `verif-scop/pluto`:
   - Example: `polcert-pluto-baseline-7cb0892`
3. Build and publish the Pluto base image from the Pluto checkout:

```sh
docker build \
  --build-arg PLUTO_GIT_REMOTE=https://github.com/verif-scop/pluto.git \
  --build-arg PLUTO_GIT_COMMIT=7cb0892d42dd65fb083601750cad1a325688a366 \
  -t hughshine/pluto-verif:polcert-pluto-baseline-7cb0892 \
  /path/to/pluto
docker push hughshine/pluto-verif:polcert-pluto-baseline-7cb0892
```

4. Update `tools/ci/pluto-baseline.env`:
   - set `PLUTO_IMAGE=$PLUTO_VERSIONED_IMAGE`
5. Keep the PolCert Dockerfile defaults aligned with that file.
6. Rebuild and rerun the normal PolCert CI path.

## Validation checklist

After changing Pluto baseline data, rerun:

```sh
bash /polcert/tools/ci/check_pluto_baseline.sh
bash /polcert/tools/ci/run_ci.sh
python3 /polcert/tests/polopt-generated/tools/check_polopt_cases.py \
  --cases-dir /polcert/tests/polopt-generated/cases \
  --expect-total 62 \
  --min-changed 50 \
  --min-nontrivial-changed 50 \
  --require-tiled matmul matmul-init wavefront
```
