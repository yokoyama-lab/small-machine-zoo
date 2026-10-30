# Source provenance

This repository is a fresh source snapshot for the accompanying paper. It does
not carry the development repository's Git history or private research logs.

- Formalization and generator source revision:
  `e6bc07d0a8768c28ee0868473c11f68df549749b`. The earlier snapshots used
  `f82eb315c9060980af5b9e99471db85f9792c575` (2026-10-30, first update),
  `f28072d0427b2bf6e0d571a6fc2d1733e0b00d4a` (2026-10-29),
  `64900a1bfb13af4ba1d94cc1db1bb5f98b233cc2` (2026-10-27), and
  `bfff87da70d64f9c8dbedab8663d988f4aae5c8a` (2026-10-10).
- Manuscript source revision: `e04dfa0` of the manuscript repository.
  `paper/note.tex` is `arxiv_v4_en.tex` at that revision with its source
  comments removed (the file was named `arxiv_ai_lean_v4_en.tex` before). It uses
  the preprint style `paper/arxiv.sty` (kourgeorge/arxiv-style, MIT license,
  unchanged below its license notice).
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

The 2026-10-29 update re-extracted from revision `f28072d0` by the same
rules. It added the roots `LeanUniv.Final4_48` (universality of the
reverse-counting machine with four states and 48 symbols, through the same
table written as a block conversion; the construction record
`results/kstate_blocks/records/urtm4-48.json` and one line of the generator
script were added) and `URTMMeta.ThreeStrictSpec` (the three-state two-symbol
theorem for tables that may list a quintuple more than once). One retained
file changed between the two source revisions only in a documentation comment
(`LeanUniv/FinalValues.lean`, which now names a module of the development
repository that is not part of this package). All other retained files are
unchanged.

The 2026-10-30 update re-extracted from revision `f82eb315` by the same
rules. It added the roots `LeanUniv.Final4_88` (universality of the
disjoint-ranges machine with four states and 88 symbols) and
`LeanUniv.Final3_659` (universality of the three-state machine with 659
symbols, the improved conversion of `(32,3)` without reflection). The new
record points `(4,41)` and `(5,38)` replace `(4,42)` and `(5,39)` as points of
the paper and among the 13 witnesses of `LeanUniv/FinalAgree.lean`; the
existing symbol-merging roots import them. Their merges allow two quintuples
to become the same quintuple, and the new module
`LeanUniv/SymMergeDedup.lean` carries universality across the removal of
repeated quintuples. The construction records and merge files of the two new
points were added to `results/symmerge-2026-10-05/`. Between the two source
revisions, `tools/gen_symmerge_lean.py` changed (the relaxed conflict
condition), the four `FinalSymMerge*` modules gained the new points,
`FinalAgree.lean` changed its witnesses, and the eight existing
`SymMerge<k>_<m>.lean` modules and `Final4_48.lean` changed only in a
documentation comment. Some comments of the new and changed files name a
directory of the development repository that is not part of this package
(`results/symmerge-relaxed-2026-10-29`). All other retained files are
unchanged. The plain-text tables of `(4,41)` and `(5,38)` in `tables/`
replace those of `(4,42)` and `(5,39)`.

The second 2026-10-30 update re-extracted from revision `e6bc07d0` by the
same rules. It added the root `LeanUniv.Final3_18476` (universality of the
three-state machine with 18,476 symbols, the intermediate machine of Morita's
three-state conversion of `(32,3)` with the up and down marks shared and all
counters kept). Its table is not written out; the new module
`LeanUniv/NumCount.lean` carries the counts through an injective numbering.
The new record point `(5,37)` replaces `(5,38)` as a point of the paper and
among the 13 witnesses of `LeanUniv/FinalAgree.lean`; the four
`FinalSymMerge*` modules gained it, and the theorems for `(5,38)` remain. Its
construction record and merge file were added to
`results/symmerge-2026-10-05/`, and its simulation module
`URTM/CTSH5_37Main.lean` is new. The new root also brings four modules of
`lean/` that were already in the previous source revision but outside the
previous closure (`URTM/CTSH3_18476Main.lean`, `URTM/CTSH3_36654Rev.lean`,
`URTM/Conv3PSim.lean`, `URTM/ConvRev.lean`), and the existence target now
also imports the generated module `URTM.Gen.V3_36654`. Between the two
source revisions, `tools/gen_symmerge_lean.py` changed only in its
documentation, which names a
directory and a branch of the development repository that are not part of
this package; the merge file of `(5,37)` names the same directory. All other
retained files are unchanged. The plain-text table of `(5,37)` in `tables/`
replaces that of `(5,38)`.

The extraction preserves the two separate proof environments and their relative
paths. The verification script checks the copied specification and universality
definitions for agreement, builds the selected proof roots, and audits their
axiom dependencies. See [verification.md](verification.md) for the commands and
scope of these checks.
