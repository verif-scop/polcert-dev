---
name: refchecker-reference-audit
description: Use Mark Russinovich's RefChecker to audit academic references in .bib, .tex, .pdf, or plain-text bibliographies. Trigger this when the user wants to check bibliography accuracy, DOI metadata, venue/year mismatches, suspicious citations, or paper-local reference quality.
---

# RefChecker Reference Audit

Use this skill when the user wants an external metadata audit of academic references, especially BibTeX databases and LaTeX paper bibliographies.

## Quick workflow

1. Prefer the BibTeX source of truth when it exists.
2. Run `scripts/run_refchecker_check.sh INPUT_PATH [OUTPUT_PREFIX]`.
3. Read both `${OUTPUT_PREFIX}.txt` and `${OUTPUT_PREFIX}.json`.
4. Separate likely real issues from probable indexer/tool false positives.
5. If the repository already has a local bibliography consistency script, run it too.

## Installation notes

This skill expects RefChecker to be available at:

- repo: `/tmp/refchecker`
- venv: `/tmp/refchecker-venv`
- CLI: `/tmp/refchecker-venv/bin/academic-refchecker`

If the CLI is missing, install it with:

```bash
git clone https://github.com/markrussinovich/refchecker.git /tmp/refchecker
python3 -m venv /tmp/refchecker-venv
/tmp/refchecker-venv/bin/pip install -e /tmp/refchecker
```

This usually needs network approval because `pip` and RefChecker query external services.

## Output handling

RefChecker reports are useful but not authoritative. Treat these as manual-review buckets:

- workshop papers with unstable venue metadata
- artifacts vs main conference proceedings
- preprint/arXiv records that collide with final DOI records
- older papers whose Semantic Scholar metadata is incomplete or mislinked
- author order/count mismatches on workshop pages and technical reports

Do not patch bibliography entries automatically just because RefChecker produced a "corrected" BibTeX block. Verify suspicious cases against the DOI landing page, publisher page, or the locally mirrored PDF.

## Polycert-specific note

For this repository, the paper-facing bibliography lives at:

- `doc/pluto-comprehensive/paper-local/latex/references.bib`

After the RefChecker pass, also run:

```bash
python3 doc/pluto-comprehensive/paper-local/bib/check_bibliography.py
```

That local script checks cited-key and curated-copy consistency, which RefChecker does not cover.
