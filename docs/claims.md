# Claims and Lean entry points

This table maps the statements of the paper ([note.tex](../paper/note.tex)) to
formal statements. Read the theorem hypotheses in the linked source. The
identifiers refer to formal statements, not to an independent guarantee that
the definitions match the intended mathematics.

## Definitions

| Paper | Lean |
|---|---|
| Quintuples, IDs, runs, halting, determinism, reversibility, `NStates`, `NSyms`, `toID`, `IsIDOf`, the enumeration `tm`, `IsUTM` | [Spec.lean](../lean-univ/LeanUniv/Spec.lean) (byte-identical copy in [lean-meta](../legacy/small-urtm/lean-meta/URTMMeta/Spec.lean)) |
| `IsUTMStrict` (definition of universality) | [Strict.lean](../lean-univ/LeanUniv/Strict.lean) (copy in [lean-meta](../legacy/small-urtm/lean-meta/URTMMeta/Strict.lean), identical up to imports) |
| Cyclic tag systems with halting condition | `URTM.CTSH` in [CTSH.lean](../lean/URTM/CTSH.lean) |
| For deterministic tables, `IsUTMStrict` implies the formulation on string IDs | `URTM.Univ.StringID.isUTM_Morita`, `isUTM_MoritaStrict` in [StringID.lean](../lean-univ/LeanUniv/StringID.lean); applied to the witnesses in [FinalString.lean](../lean-univ/LeanUniv/FinalString.lean) |

The paper's `rho` is named `s` in the symbol-merging source. Its machine index
`i` is named `n` in several Lean definitions. These are notation changes only.

## Constructions (Section 3)

| Paper statement | Lean identifier / module |
|---|---|
| Symbol-count formulas: `(2m+1)n`, `(m+1)n`, the reverse-counting bound `(max(m+,m-)+1)n`, the block formula, `N(2M-1)`, and the formula of the improved three-state conversion | `URTM.Univ.FinalFormulas.morita4_formula`, `kstate4_formula`, `eps4_formula`, `blocks_formula`, `morita3_formula`, `three_formula` in [FinalFormulas.lean](../lean-univ/LeanUniv/FinalFormulas.lean); `URTM.Univ.FinalValues.three_formula_eq` in [FinalValues.lean](../lean-univ/LeanUniv/FinalValues.lean) |
| State count of the `k`-bit two-symbol conversion | `morita2_formula` (two bits) in FinalFormulas.lean; `morita2k_formula` in FinalValues.lean |
| `(10,8)` gives 168, 88, and 48 symbols under the three four-state conversions | `morita4_10_8`, `kstate4_10_8`, `eps4_10_8` in FinalFormulas.lean |
| The reverse-counting machine with four states and 48 symbols simulates an arbitrary CTSH, and it is universal in the sense of the definition | `URTM.CTSH.U4_48.urtm4_48_simulates_ctsh` in [CTSH4_48Main.lean](../lean/URTM/CTSH4_48Main.lean); general theorem `URTM.KStateEps.econv_main` in [KStateEps.lean](../lean/URTM/KStateEps.lean); universality `URTM.Univ.Final4_48.exists_urtm_4_48` in [Final4_48.lean](../lean-univ/LeanUniv/Final4_48.lean), through the same table as a block conversion (`URTM.CTSH.U4_48B.same_as_eps` in [CTSH4_48BMain.lean](../lean/URTM/CTSH4_48BMain.lean)) |
| The six machines of the block-decomposition table, their counts, and their universality | `URTM.Univ.FinalBlocks.exists_urtm_<m>_<n>` in [FinalBlocks.lean](../lean-univ/LeanUniv/FinalBlocks.lean); `blocks_<m>_<n>` in FinalFormulas.lean |
| Merging the fixed tables of the block-decomposition table removes one to three symbols | `URTM.Univ.FinalMerge.exists_urtm_4_45`, `5_42`, `6_36`, `7_31`, `8_26` in [FinalMerge.lean](../lean-univ/LeanUniv/FinalMerge.lean) (five of the six tables; see the list at the end) |
| Theorem (symbol merging) | `URTM.Univ.SymMerge.isUTMStrict_mapQ` in [SymMerge.lean](../lean-univ/LeanUniv/SymMerge.lean) |
| Numbers of symbols before and after symbol merging | `UB_counts` and `U_counts` in `SymMerge<m>_<n>.lean`, for example [SymMerge4_42.lean](../lean-univ/LeanUniv/SymMerge4_42.lean) |
| Three states: 36,654, 18,476, 1,820, 659, and 600 symbols for `(32,3)` | `morita3_32_3`, `three_32_3` in FinalFormulas.lean; `shared3_32_3`, `pruned3_32_3`, `three_32_3_659`, `three_32_3_600_eq` in FinalValues.lean |
| Two symbols: `(24,4)` gives `(138,2)`; `(13,7)` gives 169, 149, 135, and 92 states | `morita2_24_4` in FinalFormulas.lean; `morita2_13_7`, `codeopt2_13_7`, `fewsym135_13_7`, `fewsym92_13_7` in FinalValues.lean |
| The two-symbol tables with 92, 92, 108, 115, and 115 states from `(10,8)`, `(24,4)`, `(15,6)`, `(17,5)`, and `(32,3)` are universal | `URTM.Univ.FinalFewSym.exists_urtm_92_2_of_10_8`, `exists_urtm_92_2_of_24_4`, `exists_urtm_108_2_of_15_6`, `exists_urtm_115_2_of_17_5`, `exists_urtm_115_2_of_32_3` in [FinalFewSym.lean](../lean-univ/LeanUniv/FinalFewSym.lean); CTSH simulation in `CTSH<m>_2_<m'>_<n'>Main.lean`, for example [CTSH92_2_10_8Main.lean](../lean/URTM/CTSH92_2_10_8Main.lean) |

## The 13 points (Section 4)

| Paper statement | Lean identifier / module |
|---|---|
| Theorem (existence) for all 13 points | `URTM.Univ.FinalAgree.records_spec` in [FinalAgree.lean](../lean-univ/LeanUniv/FinalAgree.lean) |
| `(3,600)` | `URTM.Univ.Final3_600.exists_urtm_3_600` |
| `(4,42)`, `(5,39)`, `(6,30)`, `(7,28)`, `(8,21)` | `URTM.Univ.FinalSymMerge.exists_urtm_<m>_<n>` |
| `(85,2)` | `URTM.Univ.Final85_2.exists_urtm_85_2` |
| `(10,8)` | `URTM.Univ.Final10_8.exists_urtm_10_8` |
| `(13,7)`, `(15,6)`, `(17,5)`, `(24,4)`, `(32,3)` | `URTM.Univ.FinalMorita.exists_urtm_<m>_<n>` |
| A machine that simulates an arbitrary CTSH, with primitive recursive encoding and readout, satisfies `IsUTMStrict` | `URTM.Univ.ChainGen.isUTMStrict_of_ctsh` in [ChainGen.lean](../lean-univ/LeanUniv/ChainGen.lean) |
| Proposition (agreement) | `URTM.Univ.Agree.isUTMStrict_agree` in [Agree.lean](../lean-univ/LeanUniv/Agree.lean); for the 13 witnesses, `URTM.Univ.FinalAgree.records_agree` |
| The theorem also holds without the two halting quintuples | [FinalBook.lean](../lean-univ/LeanUniv/FinalBook.lean), [FinalSymMergeBook.lean](../lean-univ/LeanUniv/FinalSymMergeBook.lean) |
| Every target is a source state, the blank occurs, every symbol is read and written, and the counts under Morita's convention | [FinalBlank.lean](../lean-univ/LeanUniv/FinalBlank.lean), [FinalBlank3_600.lean](../lean-univ/LeanUniv/FinalBlank3_600.lean), [FinalSymMergeBlank.lean](../lean-univ/LeanUniv/FinalSymMergeBlank.lean), [FinalMoritaCount.lean](../lean-univ/LeanUniv/FinalMoritaCount.lean), [FinalSymMergeMoritaCount.lean](../lean-univ/LeanUniv/FinalSymMergeMoritaCount.lean) |

## Nonexistence (Sections 5 and 6)

| Paper statement | Lean identifier / module |
|---|---|
| Theorem (halting of two-state RTMs), uniform in the table | `URTM.Spec.halting_decidable_uniform` in [Uniform.lean](../legacy/small-urtm/lean-meta/URTMMeta/Uniform.lean), with `TwoStateRTM` in Spec.lean |
| Corollary, first part | `URTM.Spec.no_le_two_state_URTM`, `no_le_two_state_URTMStrict` in [Corners.lean](../legacy/small-urtm/lean-meta/URTMMeta/Corners.lean) |
| Corollary, second part: one `tm(i)` that no deterministic and reversible table with at most two states simulates | `URTM.Spec.le_two_state_class_not_universal` in Corners.lean. `URTM.Spec.two_state_class_not_universal` in [SpecThm.lean](../legacy/small-urtm/lean-meta/URTMMeta/SpecThm.lean) is the special case with a single halting target |
| Theorem (at most one symbol) | `URTM.Spec.no_one_symbol_UTM` in Corners.lean |
| Theorem (at most one left-moving quintuple), and the mirror image | `URTM.Spec.no_URTM_oneL`, `no_URTM_oneR` in [Pav73.lean](../legacy/small-urtm/lean-meta/URTMMeta/Pav73.lean) |
| Theorem (three states and two symbols) | `URTM.Meta.no_three_two_URTMStrict_spec` in [ThreeStrictSpec.lean](../legacy/small-urtm/lean-meta/URTMMeta/ThreeStrictSpec.lean), with `Spec.Deterministic` and `Spec.Reversible` of Spec.lean. Its proof removes repeated quintuples (`URTM.Meta.isUTMStrict_congr_mem`: tables with the same members agree on `IsUTMStrict`) and applies `URTM.Meta.no_three_two_URTMStrict_all` in [ThreeStrictAll.lean](../legacy/small-urtm/lean-meta/URTMMeta/ThreeStrictAll.lean), whose hypothesis `RTM32` in [ThreeNorm.lean](../legacy/small-urtm/lean/URTM/ThreeNorm.lean) uses the Boolean `deterministic` and `reversible` checks |
| The string-ID form is not vacuous: the `(85,2)` witness satisfies it | `URTM.Meta.Sat.exists_moritaOver_single_of_strict` in [MoritaOverSingle.lean](../legacy/small-urtm/lean-meta/URTMMeta/MoritaOverSingle.lean), together with `exists_urtm_85_2` in the other environment |

The two environments do not link into one Lean process. The proof of each
theorem is checked in its own environment, and equality of the copied `Spec`
and `Strict` source is checked separately.

## Step counts and published runs (Section 7)

| Paper statement | Lean identifier / module |
|---|---|
| Exact step counts of Morita's Lemma 5.9 | `URTM.Conv59.step_sim_exact`, `run_sim_exact`, `halts_sim_exact` in [Conv59Exact.lean](../lean/URTM/Conv59Exact.lean) |
| Exact step counts of Morita's Lemma 5.10 | `URTM.Conv510.step_sim_exact`, `stepW_sim`, `haltsW_sim` in [Conv510Exact.lean](../lean/URTM/Conv510Exact.lean) |
| Halting step counts of the published test runs of eight of Morita's machines, with 1,173 for the `(13,7)` example whose file states 1,073 | Generated `URTM.Gen.C<m>_<n>`, imported by [PaperTraces.lean](../lean/PaperTraces.lean) |
| The three runs of `(3,36654)` take 471,798, 2,348,492, and 57,220 steps (running the table) | Generated `URTM.Gen.S3_36654` (`case1` to `case3`, `steps1` to `steps3`) |
| The same counts from the run of `(32,3)` and the step counts of Lemmas 5.9 and 5.10, and the two routes prove the same statement | Generated `URTM.Gen.W3_36654` and `URTM.Gen.W3_36654Same` (`same1` to `same3`), using [CTSH3_36654Cost.lean](../lean/URTM/CTSH3_36654Cost.lean) |

Run `tools/prepare.sh` to produce the generated files before building.
The original downloaded file is left unchanged; the generator records the
corrected `(13,7)` count. Finite trace checks supplement the general proofs and
are not a proof of universality by themselves.

## Statements without a Lean theorem in this repository

- The improved three-state conversion applied to the other five original
  machines gives between 802 and 1,209 symbols. These counts were computed
  outside Lean.
- The search table with 137 states before state merging. Lean checks the
  merged `(85,2)` table, not the table before merging.
- Merging the fixed `(9,27)` table (to 26 symbols). The other five tables of
  the block-decomposition table are covered by FinalMerge.lean.
- The remark that three states cannot be reached by block decomposition and
  merging of roles is an argument in the paper.
- The table of independently counted states and symbols is, as the paper
  states, a count outside the proof assistant.
- The agreement of a simulator and a checker implemented independently of Lean
  with the formalized model (`tools/simulate.py`, `tools/check_urtm.py`).
