# Claims and Lean entry points

Read the theorem hypotheses in the linked source. The identifiers below refer
to formal statements, not to an independent guarantee that the definitions
match the intended mathematics.

## Existence and counting (`lean-univ`)

| Paper claim | Lean identifier / module |
|---|---|
| All 13 witnesses have the stated dimensions, determinism, reversibility, and universality | `URTM.Univ.FinalAgree.records_spec` in [FinalAgree.lean](../lean-univ/LeanUniv/FinalAgree.lean) |
| The witnesses agree on halting and decoded results | `URTM.Univ.FinalAgree.records_agree` in the same module |
| `(3,600)` | `URTM.Univ.Final3_600.exists_urtm_3_600` |
| `(4,42)`, `(5,39)`, `(6,30)`, `(7,28)`, `(8,21)` | `URTM.Univ.FinalSymMerge.exists_urtm_<m>_<n>` |
| `(85,2)` | `URTM.Univ.Final85_2.exists_urtm_85_2` |
| `(10,8)` | `URTM.Univ.Final10_8.exists_urtm_10_8` |
| `(13,7)`, `(15,6)`, `(17,5)`, `(24,4)`, `(32,3)` | `URTM.Univ.FinalMorita.exists_urtm_<m>_<n>` |
| Universality after dropping the two halting quintuples | [FinalBook.lean](../lean-univ/LeanUniv/FinalBook.lean), [FinalSymMergeBook.lean](../lean-univ/LeanUniv/FinalSymMergeBook.lean) |
| Counts including targets and without adding a missing blank | [FinalMoritaCount.lean](../lean-univ/LeanUniv/FinalMoritaCount.lean), [FinalSymMergeMoritaCount.lean](../lean-univ/LeanUniv/FinalSymMergeMoritaCount.lean) |
| Symbol-merging theorem | `URTM.Univ.SymMerge.isUTMStrict_mapQ` in [SymMerge.lean](../lean-univ/LeanUniv/SymMerge.lean) |
| Conversion formulas and intermediate counts | [FinalFormulas.lean](../lean-univ/LeanUniv/FinalFormulas.lean), [FinalValues.lean](../lean-univ/LeanUniv/FinalValues.lean) |

The shared specification is [Spec.lean](../lean-univ/LeanUniv/Spec.lean);
the strengthened universality condition is [Strict.lean](../lean-univ/LeanUniv/Strict.lean).
The paper's `rho` is named `s` in the symbol-merging source. Its machine index
`i` is named `n` in several Lean definitions. These are notation changes only.

## Nonexistence (`legacy/small-urtm/lean-meta`)

| Paper claim | Lean identifier / module |
|---|---|
| No URTM with at most two states | `URTM.Spec.no_le_two_state_URTM` in [Corners.lean](../legacy/small-urtm/lean-meta/URTMMeta/Corners.lean) |
| No one-symbol UTM | `URTM.Spec.no_one_symbol_UTM` in the same module |
| Uniform decidability for two-state RTMs | `URTM.Spec.halting_decidable_uniform` in [Uniform.lean](../legacy/small-urtm/lean-meta/URTMMeta/Uniform.lean) |
| The class of two-state RTMs is not universal | `URTM.Spec.two_state_class_not_universal` in [SpecThm.lean](../legacy/small-urtm/lean-meta/URTMMeta/SpecThm.lean) |
| Nonuniversality with at most one left-moving instruction and the stated zero-shift condition | [Pav73.lean](../legacy/small-urtm/lean-meta/URTMMeta/Pav73.lean) |
| No three-state, two-symbol URTM under the strengthened definition | `no_three_two_URTMStrict_all` in [ThreeStrictAll.lean](../legacy/small-urtm/lean-meta/URTMMeta/ThreeStrictAll.lean) |
| The restricted string-ID condition is not vacuous | [MoritaOverSingle.lean](../legacy/small-urtm/lean-meta/URTMMeta/MoritaOverSingle.lean), together with the `(85,2)` existence theorem in the other environment |

The two environments do not link into one Lean process. The proof of each
theorem is checked in its own environment, and equality of the copied `Spec`
and `Strict` source is checked separately. This is the cross-environment
qualification described in the paper.

## Published test runs (`lean`)

`PaperTraces.lean` imports the generated `URTM.Gen.C<m>_<n>` certificates for
eight of Morita's machines and `URTM.Gen.S3_36654` for the three large runs.
The latter proves the exact counts 471,798, 2,348,492, and 57,220. Run
`tools/prepare.sh` to produce these files before building.

The `(13,7)` example whose distributed comment says 1,073 is checked with the
corrected count 1,173. The original downloaded file is left unchanged; the
generator records the correction. Finite trace checks supplement the general
proofs and are not a proof of universality by themselves.
