# Source provenance

This repository is a fresh source snapshot for the accompanying paper. It does
not carry the development repository's Git history or private research logs.

- Formalization and generator source revision:
  `64900a1bfb13af4ba1d94cc1db1bb5f98b233cc2`. The previous snapshot (2026-10-10)
  used `bfff87da70d64f9c8dbedab8663d988f4aae5c8a`.
- Manuscript source revision: `f36351a` of the manuscript repository.
  `paper/note.tex` is `arxiv_ai_lean_v4_en.tex` at that revision with its
  source comments removed.
- The full version combines that paper with `paper/details.tex`, an appendix
  assembled from the existing construction and proof notes. It is not an
  independently inspected proof of the formalization.
- Lean: `leanprover/lean4:v4.31.0`; Mathlib:
  `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`.

[`source-manifest.json`](source-manifest.json) records SHA-256 hashes of the
unchanged files retained from the source revision, the chosen proof roots, and
the existing files adapted for the smaller package. The retained Lean modules
are the import dependencies of those roots. Construction recipes and Python
helpers are retained to regenerate the required machine tables and traces.
New entry-point modules, axiom-audit drivers, build scripts, and documentation
complete the package. The mathematical proof bodies were not rewritten during
extraction.

The source data are obtained from
[Morita's slides and their attachments](https://hiroshima.repo.nii.ac.jp/record/2000034/files/Morita_URTM.pdf).
The expected PDF SHA-256 is
`e36b9edd31d80d52d6f4cdc7433510e4c1ff3d9cf0359386ae3d3bd63f4b9524`.
The fetching script checks this hash before extracting the machine descriptions.
Those third-party data and their generated Lean tables are not committed.

The 2026-10-27 update re-extracted the import closure of the roots from the
new source revision by the same rules. It added the roots
`LeanUniv.FinalFewSym`, `LeanUniv.FinalMerge`, `URTM.CTSH4_48Main`, and
`URTM.Gen.W3_36654Same`, with their dependencies and the construction records of the five
two-symbol tables in `results/fewsym/records/`, which the generator script reads. One
retained file changed between the two source revisions
(`URTMMeta/Corners.lean`). The source revision changed the build configuration
of `legacy/small-urtm/lean-meta`; this package keeps its earlier path
dependency on `../lean`, so `lake-manifest.json` there is listed among the
adapted files.

The extraction preserves the two separate proof environments and their relative
paths. The verification script checks the copied specification and universality
definitions for agreement, builds the selected proof roots, and audits their
axiom dependencies. See [verification.md](verification.md) for the commands and
scope of these checks.
