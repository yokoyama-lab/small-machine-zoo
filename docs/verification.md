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
memory for a first build; the development project reported a peak near 28 GB
for a broader default build, so a machine with 32 GB or more is a reasonable
starting point, not a measured minimum for this extracted package.

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
