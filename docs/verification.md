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
definitions, and audits the imported theorem environments for axioms outside
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
target includes the large `(3,36654)` examples. Allow substantial time and
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
current short paper with `paper/details.tex`; it is not maintained as a second
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
