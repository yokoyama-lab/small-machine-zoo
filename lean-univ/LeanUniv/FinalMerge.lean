/-
  **Five URTMs from merging two symbols of the block-converted tables**
  (results/symmerge-2026-10-04): URTM(4,45), (5,42), (6,36), (7,31), (8,26), in the sense of
  Morita Def. 7.1 with computable encoding and decoding.

  Each theorem: a deterministic and reversible TM with m states and n symbols satisfies
  `IsUTMStrict` (`LeanUniv/Strict.lean`; Morita 2017 Def. 7.1, the decoder must be right on
  **every** code of the halting ID). The witness is the table of `FinalBlocks` with symbols merged
  by a finite map (`MergeBlocks`, the same statement shape as `FinalBlocks`). Universality goes
  through the general theorem `SymMerge.isUTMStrict_mapQ` (merging symbols preserves Def. 7.1
  for a table whose halting IDs are in pseudo-states and hold symbols on which the merge is
  injective) and the strong form `BlockHalt.isUTMStrictHalt_block<base>`, which takes the shape
  of the halting IDs from the CTSH theorem of each block-converted machine. No hypotheses.
  Minimality is not claimed.
-/
import LeanUniv.MergeBlocks

namespace URTM.Univ.FinalMerge
open URTM URTM.Spec URTM.Univ.MergeBlocks

theorem exists_urtm_4_45 :
    ∃ U : List Quint, Deterministic U ∧ Reversible U ∧ NStates U = 4 ∧ NSyms U = 45 ∧
      IsUTMStrict U :=
  ⟨M4_45.U, M4_45.U_det, M4_45.U_rev, M4_45.U_counts.1, M4_45.U_counts.2, M4_45.isUTMStrict_U⟩

theorem exists_urtm_5_42 :
    ∃ U : List Quint, Deterministic U ∧ Reversible U ∧ NStates U = 5 ∧ NSyms U = 42 ∧
      IsUTMStrict U :=
  ⟨M5_42.U, M5_42.U_det, M5_42.U_rev, M5_42.U_counts.1, M5_42.U_counts.2, M5_42.isUTMStrict_U⟩

theorem exists_urtm_6_36 :
    ∃ U : List Quint, Deterministic U ∧ Reversible U ∧ NStates U = 6 ∧ NSyms U = 36 ∧
      IsUTMStrict U :=
  ⟨M6_36.U, M6_36.U_det, M6_36.U_rev, M6_36.U_counts.1, M6_36.U_counts.2, M6_36.isUTMStrict_U⟩

theorem exists_urtm_7_31 :
    ∃ U : List Quint, Deterministic U ∧ Reversible U ∧ NStates U = 7 ∧ NSyms U = 31 ∧
      IsUTMStrict U :=
  ⟨M7_31.U, M7_31.U_det, M7_31.U_rev, M7_31.U_counts.1, M7_31.U_counts.2, M7_31.isUTMStrict_U⟩

theorem exists_urtm_8_26 :
    ∃ U : List Quint, Deterministic U ∧ Reversible U ∧ NStates U = 8 ∧ NSyms U = 26 ∧
      IsUTMStrict U :=
  ⟨M8_26.U, M8_26.U_det, M8_26.U_rev, M8_26.U_counts.1, M8_26.U_counts.2, M8_26.isUTMStrict_U⟩

end URTM.Univ.FinalMerge
