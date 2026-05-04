#!/usr/bin/env bash
set -euo pipefail

if [ "$#" -lt 1 ] || [ "$#" -gt 2 ]; then
  echo "usage: $0 INPUT_PATH [OUTPUT_PREFIX]" >&2
  exit 2
fi

input_path=$1
output_prefix=${2:-/tmp/refchecker-audit}
cli_path="${REFCHECKER_CLI:-/tmp/refchecker-venv/bin/academic-refchecker}"

if [ ! -x "$cli_path" ]; then
  echo "RefChecker CLI not found at $cli_path" >&2
  echo "Install it first:" >&2
  echo "  git clone https://github.com/markrussinovich/refchecker.git /tmp/refchecker" >&2
  echo "  python3 -m venv /tmp/refchecker-venv" >&2
  echo "  /tmp/refchecker-venv/bin/pip install -e /tmp/refchecker" >&2
  exit 2
fi

"$cli_path" \
  --paper "$input_path" \
  --report-file "${output_prefix}.json" \
  --report-format json \
  --output-file "${output_prefix}.txt"

echo "RefChecker reports:"
echo "  ${output_prefix}.json"
echo "  ${output_prefix}.txt"
