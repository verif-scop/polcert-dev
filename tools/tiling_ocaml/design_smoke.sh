set -eu

ROOT_DIR="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
cd "$ROOT_DIR"

if [ ! -x _build/default/design_validator_prototype.exe ]; then
  dune build design_validator_prototype.exe
fi

run_pass() {
  fixture="$1"
  _build/default/design_validator_prototype.exe "fixtures/design/$fixture" >/tmp/design_validator.out
}

run_fail() {
  fixture="$1"
  if _build/default/design_validator_prototype.exe "fixtures/design/$fixture" >/tmp/design_validator.err 2>&1; then
    echo "expected fixture $fixture to fail" >&2
    exit 1
  fi
}

run_pass second_level_positive.json
rg -q "canonical added iterators: \[f1, f0\]" /tmp/design_validator.out
rg -q "schedule bridge reconstructed" /tmp/design_validator.out

run_fail second_level_bad_cycle.json
rg -q "cannot topologically order tile links" /tmp/design_validator.err

run_fail second_level_bad_schedule.json
rg -q "reordered raw schedule does not match the expected canonical schedule" /tmp/design_validator.err

run_pass diamond_positive.json
rg -q "checked affine midpoint \+ ordinary affine floor-link tiling" /tmp/design_validator.out

run_fail diamond_bad_no_midpoint.json
rg -q "requires an explicit midpoint hyperplane set" /tmp/design_validator.err

run_fail diamond_bad_missing_hyperplane.json
rg -q "does not match any midpoint hyperplane" /tmp/design_validator.err

echo "design smoke: PASS"
