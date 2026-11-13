# Smaller universal reversible Turing machines

Companion materials for **Smaller Universal Reversible Turing Machines and the
Nonexistence of Two-State Ones**, Tetsuo Yokoyama, Nanzan University.

- [Paper (PDF)](paper/note.pdf) · [LaTeX](paper/note.tex)
- [Full version (PDF)](paper/full.pdf), with construction details and proof
  outlines · [Appendix source](paper/details.tex)
- [Claims and Lean entry points](docs/claims.md)
- [Build and verification instructions](docs/verification.md)

The seven new state–symbol pairs are `(3,600)`, `(4,41)`, `(5,37)`, `(6,30)`,
`(7,28)`, `(8,21)`, and `(85,2)`. Together with six of Morita's earlier machines,
they give 13 non-dominated points. The formalization also proves nonexistence
of URTMs with at most two states and of three-state, two-symbol URTMs, under
the definitions and conditions stated in the paper. These are upper bounds
by construction, not claims of global minimality. The other theorems of the
paper that are formalized are listed with their Lean names in
[docs/claims.md](docs/claims.md).

## Current record points (updated 2026-11-13)

After the paper, further constructions improved six of the paper's points. The
current non-dominated points are

`(3,600)`, `(4,38)`, `(5,36)`, `(6,28)`, `(7,26)`, `(8,21)`, `(9,8)`, `(10,7)`,
`(15,6)`, `(17,5)`, `(24,4)`, `(32,3)`, and `(85,2)` (13 points).

- `(4,38)`, `(5,36)`, `(6,28)`, and `(7,26)` dominate the paper's `(4,41)`,
  `(5,37)`, `(6,30)`, and `(7,28)`. They are obtained by block decomposition
  and symbol merging that allows coinciding rules, from `(10,7)` for `(4,38)`
  and `(5,36)` and from `(9,8)` for `(6,28)` and `(7,26)`.
- `(10,7)` dominates Morita's `(10,8)` and `(13,7)`. It is obtained from
  `(13,7)` by merging a state into another with tags on cells and then merging
  symbols, three times (through `(12,7)` and `(11,7)`). `(9,8)` is obtained from
  `(10,7)` by one more such step.
- `(3,600)`, `(8,21)`, `(85,2)`, and Morita's `(15,6)`, `(17,5)`, `(24,4)`, and
  `(32,3)` are unchanged.

The quintuple tables of all new machines are in [tables/](tables/README.md). The
existence of each of the six new points is proved in Lean, in the sense of the
same definition of universality, in the development repository
(see [docs/claims.md](docs/claims.md#results-after-the-paper)). Those Lean modules are not
yet part of this source snapshot, and the paper in `paper/` describes the
earlier 13 points. As before, these are upper bounds by construction, not claims
of minimality.

Lean checks the formal theorems relative to the definitions. This does not
establish that the definitions faithfully capture Morita's definitions, in
particular his definition of universality. Read the qualifications in the paper
with the results.

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
| `tables/` | Plain-text quintuple tables of the seven new URTMs of the paper and of the machines obtained later |

The two proof environments use different `URTM` packages. They are deliberately
kept separate; the verification script compares the definitions copied between
them. The `legacy` path preserves the dependency layout and contains only the
retained proof dependencies and generator helpers, not the development history.
Some dependency modules retain historical comments about earlier records; the
scope of the Lean code in this snapshot is the 13 points listed in the paper and `FinalAgree.dims`.

Morita's original machine descriptions are fetched from their public source,
checked against a fixed SHA-256, and regenerated locally. Original data,
generated tables, build caches, private work records, and conversation logs are
not included. This is a source snapshot with a fresh Git history.

## Provenance and license

[Source provenance](docs/provenance.md) records the source revisions and retained
file hashes. Existing code retains its [MIT license](LICENSE). The manuscripts
in `paper/` are copyright Tetsuo Yokoyama; no additional manuscript license is
granted by this repository. Source data retain their original rights.
