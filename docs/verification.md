# Build and verification

The repository pins Lean `leanprover/lean4:v4.31.0` and Mathlib
`fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` (tag `v4.31.0`).
Install elan, Python 3, Bash, Git, curl, and Poppler's `pdfdetach` first.
LaTeX is needed only for rebuilding the PDFs.

## Prepare

From the repository root:

```sh
bash tools/prepare.sh
```

This downloads the source PDF from the Hiroshima University repository, checks
its pinned SHA-256, extracts its nine URTM descriptions, generates the Lean
table/trace modules from the descriptions and construction recipes, and obtains
the Mathlib caches in both environments. Downloaded data and caches are ignored
by Git. This step makes network requests but does not invoke AI or run a new
optimization campaign.

## Verify

```sh
python3 tools/verify.py
```

The default command builds all three targets below, checks equality of copied
definitions, checks that the entry modules `LeanUniv.lean`, `URTMMeta.lean`, and
`PaperTraces.lean` import exactly the roots listed in `docs/source-manifest.json`,
and audits the imported theorem environments for axioms outside
`propext`, `Classical.choice`, and `Quot.sound`. Any failed build or unexpected
axiom makes the command fail; it never substitutes a missing proof.

For a separate target:

```sh
python3 tools/verify.py --target existence
python3 tools/verify.py --target nonexistence
python3 tools/verify.py --target traces
```

Build logs are saved under `out/verification/`. The nonexistence target includes
the exhaustive three-state proof, not just the two-state theorem. The traces
target includes the large `(3,36654)` examples, both by running the table and
through the step counts of Lemmas 5.9 and 5.10. Allow substantial time and
memory for a first build. Release validation used a machine with 64 GB of RAM;
individual Lean processes for the intermediate-value and blank-symbol checks
used about 13 GB and 20 GB, respectively, while running concurrently. These are
observations from this build, not guaranteed upper bounds or a measured minimum.

`LEAN_NUM_THREADS` controls Lean worker threads; the script defaults it to 4.
Mathlib caches accelerate dependency setup. The URTM modules are built from
the supplied source. To force a fresh rebuild of this repository's proofs,
remove only the `.lake/build` directories in `lean/`, `lean-univ/`,
`legacy/small-urtm/lean/`, and `legacy/small-urtm/lean-meta/`, then rerun verification.

## Rebuild the manuscripts

With `pdflatex` and the packages used by `paper/note.tex` installed:

```sh
python3 tools/build_paper.py
```

This produces `paper/note.pdf` and `paper/full.pdf`. The latter combines the
current paper with `paper/details.tex`; it is not maintained as a second
independent copy of the main text. Both files are built twice for references.

## What this checks

Successful verification establishes acceptance of the included formal proofs
and the reported axiom dependencies. It does not verify that the definitions
faithfully capture Morita's intended definitions. Rebuilding a final construction
does not replay the AI conversation or establish that the search was optimal.
The source-manifest hashes record extraction provenance; changing a hash together
with its file would not independently validate the change.

## Initial snapshot validation (2026-10-10)

All three targets built successfully from the extracted URTM sources with the
pinned Lean and Mathlib versions. Mathlib dependencies used their build caches.
The imported-environment audits reported:

| Target | Declarations | Theorems | Additional axioms / flagged declarations |
|---|---:|---:|---|
| existence | 10,603 | 7,041 | None / none |
| nonexistence | 8,257 | 6,654 | None / none |
| traces | 6,388 | 3,761 | None / none |

The allowed axioms were `propext`, `Classical.choice`, and `Quot.sound`.
No imported project declaration was unsafe, opaque, or marked `implemented_by`
or `extern`. The copied `Spec` and `Strict` definitions passed the agreement
checks. Source-code linter warnings did not cause build or audit failures.

Generation was also repeated from the files selected for distribution, with
Python site packages disabled. All 78 retained generated files matched the
files used for verification. The source PDF matched its pinned SHA-256.
Both manuscript PDFs built without LaTeX warnings or undefined references.

## Snapshot update validation (2026-10-27)

The update added the roots `LeanUniv.FinalFewSym`, `LeanUniv.FinalMerge`,
`URTM.CTSH4_48Main`, and `URTM.Gen.W3_36654Same`. Starting from a fresh clone,
`tools/prepare.sh` downloaded the source PDF, matched its pinned SHA-256,
generated the tables, and obtained the Mathlib caches. All three targets then
built from the URTM sources with the pinned Lean and Mathlib versions, and the
default `python3 tools/verify.py` passed. The imported-environment audits
reported:

| Target | Declarations | Theorems | Additional axioms / flagged declarations |
|---|---:|---:|---|
| existence | 11,144 | 7,396 | None / none |
| nonexistence | 8,258 | 6,655 | None / none |
| traces | 6,829 | 4,099 | None / none |

The allowed axioms were `propext`, `Classical.choice`, and `Quot.sound`, so no
proof uses `sorry` or `native_decide`. The copied `Spec` and `Strict`
definitions passed the agreement checks, and the entry modules matched the
manifest roots. Source-code linter warnings did not cause failures.

Each target was built separately with `LEAN_NUM_THREADS=4` under a 40 GB memory
limit, on a machine with 64 GB of RAM that was also running unrelated jobs.
The observed wall-clock times were about 2 h 23 min for existence, 43 min for
nonexistence, and 11 min for traces (the trace target reused modules already
built for existence). The longest single modules were `LeanUniv.Num3_600`
(about 2 h) and `LeanUniv.Values13_7` (about 75 min). The largest Lean process
used about 21 GB for existence, 9 GB for nonexistence, and 8 GB for traces.
These are observations from this build, not guaranteed bounds.

As a mutation check, the statement of `exists_urtm_92_2_of_10_8` was changed
to claim 91 states. `python3 tools/verify.py --target existence` then failed
with a type mismatch in `FinalFewSym.lean`; after restoring the file, the full
verification passed again. Generation was repeated from the files selected for
distribution, with Python site packages disabled; all 96 retained generated
files matched the files used for verification. Both manuscript PDFs built
without LaTeX errors, warnings, undefined references, or overfull or underfull
boxes.

## Snapshot update validation (2026-10-29)

The update added the roots `LeanUniv.Final4_48` and `URTMMeta.ThreeStrictSpec`.
The validation started from a fresh clone of the committed snapshot. The
public repository of the source PDF was down for maintenance (HTTP 503) at the
time, so `tools/fetch_data.sh` stored the maintenance page instead of the PDF,
and its SHA-256 check rejected it before any table was generated. The
validation therefore used a local copy of the PDF downloaded on an earlier
date, whose SHA-256 matches the pinned value
`e36b9edd31d80d52d6f4cdc7433510e4c1ff3d9cf0359386ae3d3bd63f4b9524`. With that
file in `data/`, `tools/prepare.sh` generated the tables and obtained the
Mathlib caches, and each of the three targets built from the URTM sources and
passed `tools/verify.py`. The imported-environment audits reported:

| Target | Declarations | Theorems | Additional axioms / flagged declarations |
|---|---:|---:|---|
| existence | 11,185 | 7,424 | None / none |
| nonexistence | 8,275 | 6,671 | None / none |
| traces | 6,829 | 4,099 | None / none |

The copied `Spec` and `Strict` definitions passed the agreement checks, and
the entry modules matched the manifest roots. Each target was built separately
with `LEAN_NUM_THREADS=4` under a 40 GB memory limit on a machine with 64 GB of
RAM. The observed wall-clock times were about 37 min for existence, 40 min for
nonexistence, and 10 min for traces; the longest single modules were
`LeanUniv.Values13_7` (about 26 min) and `LeanUniv.Num3_600` (about 12 min).
These are observations from this build, not guaranteed bounds. Both manuscript
PDFs built without LaTeX errors, warnings, or undefined references.

## Snapshot update validation (2026-10-30)

The update added the roots `LeanUniv.Final4_88` and `LeanUniv.Final3_659`,
and the existing roots now import the symbol-merging points `(4,41)` and
`(5,38)`. The validation copied the files of the snapshot into a new
directory. The public repository of the source PDF again returned HTTP 503,
so the validation used the local copy of the PDF described above, whose
SHA-256 matches the pinned value. With that file in `data/`,
`tools/prepare.sh` generated the tables and obtained the Mathlib caches. The
generated modules were identical to those generated at the source revision.
Each of the three targets then built from the URTM sources and passed
`tools/verify.py`. The imported-environment audits reported:

| Target | Declarations | Theorems | Additional axioms / flagged declarations |
|---|---:|---:|---|
| existence | 11,553 | 7,733 | None / none |
| nonexistence | 8,275 | 6,671 | None / none |
| traces | 6,829 | 4,099 | None / none |

The copied `Spec` and `Strict` definitions passed the agreement checks, and
the entry modules matched the manifest roots. Each target was built separately
with `LEAN_NUM_THREADS=4` under a 45 GB memory limit on a machine with 64 GB of
RAM, in the order nonexistence, existence, traces; the traces target reused
the modules of `lean/` built for the existence target. The observed wall-clock
times were about 43 min for nonexistence, 15 min for existence, and 11 min for
traces, with peak resident memory of about 9 GB, 22 GB, and 9 GB. The longest
single module was `LeanUniv.Values13_7` (about 8 min). These are observations
from this build, not guaranteed bounds.

The tables of the five merged machines in `tables/` were compared with the
tables `B` of `LeanUniv.SymMergeBook<k>_<m>` evaluated in the built
environment, after mapping the symbol names back to their Lean numbers. For
`(4,41)`, `(5,38)`, `(6,30)`, `(7,28)`, and `(8,21)` the quintuples agree as
sets and in order (142, 141, 160, 160, and 149 quintuples). Both manuscript
PDFs built without LaTeX errors, warnings, undefined references, or overfull
or underfull boxes.

## Snapshot update validation (2026-10-30, second update)

The update added the root `LeanUniv.Final3_18476`, and the existing roots now
import the symbol-merging point `(5,37)`. Only the existence target imports
changed or new files. The 132 source files of the nonexistence target and the
101 source and generated files of the traces target are byte-identical to
those validated for the previous update, so those two targets were not
rebuilt. The source PDF in `data/` matched its pinned SHA-256.
`tools/gen_all_lean.sh` regenerated the tables; the generated modules that
were already present were unchanged, and relative to the previous update the
only new generated module is `URTM.Gen.KB5_37`.

The existence target was built incrementally in a working copy that held an
earlier build of the snapshot, under a 40 GB memory limit with
`LEAN_NUM_THREADS=1`. Lake rebuilt the 51 modules whose sources or imports
differed from that build (including `URTM.Gen.KB5_37`, `LeanUniv.SymMerge5_37`, `LeanUniv.NumCount`,
`LeanUniv.Num3_18476`, `LeanUniv.U3_18476`, and `LeanUniv.Final3_18476`) and
reused the others by their recorded source hashes; it took 15 min with a peak
resident memory of about 19 GB. `URTM.Gen.V3_36654`, newly imported by this
target, was then removed from the build directory and rebuilt (101 s, about
8 GB). `python3 tools/verify.py --target existence` passed both times. The
imported-environment audit reported:

| Target | Declarations | Theorems | Additional axioms / flagged declarations |
|---|---:|---:|---|
| existence | 12,313 | 8,436 | None / none |

The copied `Spec` and `Strict` definitions passed the agreement checks, and
the entry modules matched the manifest roots. With comments removed, no Lean
file of the package contains `sorry`, `admit`, `axiom`, `native_decide`, or the other
forbidden tokens outside comments; the only matches are in the audit drivers
`tests/AxSweep.lean`. As a mutation check, the statement of
`exists_urtm_3_18476` was changed to claim 18,475 symbols; the existence
target then failed with a type mismatch in `Final3_18476.lean`, and passed
again after the file was restored.

The tables of the five merged machines in `tables/` were compared with the
tables `B` of `LeanUniv.SymMergeBook<k>_<m>` evaluated in the built
environment, as before. For `(4,41)`, `(5,37)`, `(6,30)`, `(7,28)`, and
`(8,21)` the quintuples agree as sets and in order (142, 145, 160, 160, and
149 quintuples); with one quintuple removed from the `(5,37)` table, the
comparison failed. Both manuscript PDFs built without LaTeX errors, warnings,
undefined references, or overfull or underfull boxes.
