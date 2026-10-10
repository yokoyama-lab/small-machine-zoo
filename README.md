# Small universal reversible Turing machines

Companion materials for **Small Universal Reversible Turing Machines Constructed
by AI and Formally Verified in Lean without Human Inspection of the Formalization**,
Tetsuo Yokoyama, Nanzan University.

- [Short paper (PDF)](paper/note.pdf) · [LaTeX](paper/note.tex)
- [Extended paper (PDF)](paper/full.pdf), with construction details, proof outlines,
  and comparison with prior work · [Appendix source](paper/details.tex)
- [Claims and Lean entry points](docs/claims.md)
- [Build and verification instructions](docs/verification.md)

The seven new state–symbol pairs are `(3,600)`, `(4,42)`, `(5,39)`, `(6,30)`,
`(7,28)`, `(8,21)`, and `(85,2)`. Together with six of Morita's earlier machines,
they give 13 non-dominated points. The formalization also proves nonexistence
of URTMs with at most two states and of three-state, two-symbol URTMs, under
the definitions and conditions stated in the paper. These are upper bounds
by construction, not claims of global minimality.

The paper's protocol uses AI for construction, search, formalization, and proofs.
Lean checks the formal theorems. This does not establish that the formalization
faithfully expresses the intended mathematics; the author did not inspect that
correspondence. Read the qualifications in the paper with the results.

## Reproduce

Requirements: Linux, Python 3, Bash, Git, curl, `pdfdetach` (Poppler), and
[elan](https://github.com/leanprover/elan). Lean and Mathlib are pinned to
`v4.31.0`; the exact Mathlib and transitive dependency revisions are in the Lake
manifests. No solver or AI service is needed to rebuild the submitted proofs.

```sh
git clone https://github.com/yokoyama-lab/small-machine-zoo.git
cd small-machine-zoo
bash tools/prepare.sh
python3 tools/verify.py
```

The full verification includes the exhaustive three-state proof and the large
published trace checks. It is a substantial build; see the
[verification guide](docs/verification.md) for separate targets and resource notes.

## Contents

| Path | Purpose |
|---|---|
| `lean-univ/` | Universality, the 13 witnesses, agreement, counting, and symbol merging |
| `lean/` | Machine semantics, constructions, simulations, and trace certificates |
| `legacy/small-urtm/lean-meta/` | Computability, nonexistence theorems, and copied definitions |
| `legacy/small-urtm/lean/` | Decision procedures and the finite three-state enumeration |
| `tools/` | Fetching source data, regenerating tables, and verification |
| `results/`, `autoresearch/frontier/search_lib/records/` | Construction parameters used by the generators |
| `paper/` | Short and extended manuscript sources and PDFs |

The two proof environments use different `URTM` packages. They are deliberately
kept separate; the verification script compares the definitions copied between
them. The `legacy` path preserves the dependency layout and contains only the
retained proof dependencies and generator helpers, not the development history.
Some dependency modules retain historical comments about earlier records; the
current scope is the 13 points listed in the paper and `FinalAgree.dims`.

Morita's original machine descriptions are fetched from their public source,
checked against a fixed SHA-256, and regenerated locally. Original data,
generated tables, build caches, private work records, and conversation logs are
not included. This is a source snapshot with a fresh Git history.

## Provenance and license

[Source provenance](docs/provenance.md) records the source revisions and retained
file hashes. Existing code retains its [MIT license](LICENSE). The manuscripts
in `paper/` are copyright Tetsuo Yokoyama; no additional manuscript license is
granted by this repository. Source data retain their original rights.
