#!/usr/bin/env bash
set -euo pipefail

paper_root="${1:-doc/pluto-comprehensive/paper-local}"
sections_dir="$paper_root/latex/sections"

echo "== Scope boundary hotspots =="
rg -n \
  'diamond|parallel|unsupported|supported today|not supported|full-fledged|baseline|default end-to-end|experimental|theorem' \
  "$sections_dir" "$paper_root/TODO.md" "$paper_root/STATUS.md" "$paper_root/REVIEW_LOG.md" || true

echo
echo "== Predecessor anchors =="
rg -n \
  'leroy2009compcert|necula2000translation|courant2021verified|li2024affine|translation validation|semantic preservation' \
  "$sections_dir" "$paper_root/full-fledged-verified-polyhedral-compilation-draft.md" || true

echo
echo "== Theorem contract hotspots =="
rg -n \
  'StateEq|Refines|SeqLoop|extractor\(|prepared_codegen|Opt\(|Theorem|Lemma' \
  "$paper_root/latex/sections/correctness.tex" "$paper_root/latex/sections/relation.tex" || true
