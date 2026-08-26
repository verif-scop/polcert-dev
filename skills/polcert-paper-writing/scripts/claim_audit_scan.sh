#!/usr/bin/env bash
set -euo pipefail

paper_root="${1:-doc/pluto-comprehensive/paper-local}"
sections_dir="$paper_root/paper/sections"

echo "== Scope boundary hotspots =="
rg -n \
  'diamond|parallel|unsupported|supported today|not supported|full-fledged|baseline|default end-to-end|experimental|theorem' \
  "$sections_dir" "$paper_root/TODO.md" "$paper_root/STATUS.md" \
  "$paper_root/workflow/claims/contribution_contract.md" \
  "$paper_root/workflow/story/narrative.md" || true

echo
echo "== Predecessor anchors =="
rg -n \
  'leroy2009compcert|necula2000translation|courant2021verified|li2024affine|translation validation|semantic preservation' \
  "$sections_dir" "$paper_root/workflow/citations/citation_support.md" || true

echo
echo "== Theorem contract hotspots =="
rg -n \
  'StateEq|Refines|SeqLoop|extractor\(|prepared_codegen|Opt\(|Theorem|Lemma' \
  "$sections_dir/semantics.tex" "$sections_dir/tiling.tex" \
  "$sections_dir/transformations.tex" "$sections_dir/composition.tex" || true
