/-
  **URTM(9,8) in the sense of Def. 7.1** (computable encoding and decoding included), and the
  versions as in `FinalBook`, `FinalBlank` and `FinalMoritaCount`.

  URTM(10,7) with case_y_1 merged into copy_n_3 and the symbols recoloured at the same time (the tag
  family L₁ and symbol merging solved jointly, results of 2026-11-04); the table is
  `URTM.CTSH.U9_8.T9` (lean/URTM/CTSH9_8.lean, 54 quintuples, 8 symbols). The witness is
  `U9_8.U = numT U9_8.num T9` (`U9_8.U_def`); the encoder is that of (13,7), the readout is the
  two-colour one of (10,7) (`MoritaGen2.readM2`). No hypotheses. Minimality is not claimed.
  It dominates (9,9).

  The witness without its two halting quintuples is `B` (52 quintuples, `book_urtm_9_8`).
-/
import LeanUniv.U9_8
import LeanUniv.Book
import LeanUniv.MoritaCount
import LeanUniv.MoritaGen2

namespace URTM.Univ.Final9_8
open URTM URTM.Spec URTM.Univ.DropGen URTM.Univ.MoritaGen URTM.Univ.MoritaGen2 URTM.Univ.MoritaCount

theorem exists_urtm_9_8 :
    ∃ U : List Quint, Deterministic U ∧ Reversible U ∧ NStates U = 9 ∧ NSyms U = 8 ∧
      IsUTMStrict U :=
  U9_8.exists_urtm_9_8

/-- The two halting quintuples (as for (13,7) and (10,7)). -/
def H : List Quint := [⟨0, 0, 0, .Z, 13⟩, ⟨1, 0, 0, .Z, 14⟩]
/-- **URTM(9,8) without its halting quintuples** (52 quintuples). -/
def B : List Quint := dropT U9_8.U H

theorem B_book :
    H = U9_8.U.filter (fun r => decide (r.q ∉ U9_8.U.map Quint.p)) ∧
    B.length + 2 = U9_8.U.length ∧ ∀ r ∈ B, r.q ∈ B.map Quint.p := by decide +kernel
theorem B_counts : NStates B = 9 ∧ NSyms B = 8 := by decide +kernel
theorem B_det : Deterministic B := deterministic_dropT _ U9_8.U_det
theorem B_rev : Reversible B := reversible_dropT _ U9_8.U_rev
theorem isUTMStrict_B : IsUTMStrict B :=
  ChainGen.isUTMStrict_drop_ctsh (encM_primrec _ _ _) (readM2_primrec _ _ _ _) U9_8.body_U
    U9_8.U_det (by decide +kernel) _ (fun _ _ => rfl) (by decide +kernel) (by decide +kernel)

theorem exists_urtm_9_8_book :
    ∃ U : List Quint, Deterministic U ∧ Reversible U ∧ NStates U = 9 ∧ NSyms U = 8 ∧
      IsUTMStrict U :=
  ⟨B, B_det, B_rev, B_counts.1, B_counts.2, isUTMStrict_B⟩

theorem book_urtm_9_8 :
    B = dropT U9_8.U H ∧
    H = U9_8.U.filter (fun r => decide (r.q ∉ U9_8.U.map Quint.p)) ∧
    B.length + 2 = U9_8.U.length ∧ (∀ r ∈ B, r.q ∈ B.map Quint.p) ∧
    Deterministic B ∧ Reversible B ∧ NStates B = 9 ∧ NSyms B = 8 ∧ IsUTMStrict B :=
  ⟨rfl, B_book.1, B_book.2.1, B_book.2.2, B_det, B_rev, B_counts.1, B_counts.2, isUTMStrict_B⟩

theorem B_blank :
    (∃ r ∈ B, r.s = 0) ∧ (symbols B).dedup.length = NSyms B ∧
    (∀ x ∈ symbols B, (∃ r ∈ B, r.s = x) ∧ (∃ r ∈ B, r.t = x)) ∧
    (states B).dedup.length = NStates B := by decide +kernel

theorem exists_urtm_9_8_blank :
    ∃ U : List Quint, Deterministic U ∧ Reversible U ∧
    NStates U = 9 ∧ NSyms U = 8 ∧ (∃ r ∈ U, r.s = 0) ∧
    (symbols U).dedup.length = 8 ∧
    (∀ x ∈ symbols U, (∃ r ∈ U, r.s = x) ∧ (∃ r ∈ U, r.t = x)) ∧
    (states U).dedup.length = 9 ∧ IsUTMStrict U :=
  ⟨B, B_det, B_rev, B_counts.1, B_counts.2, B_blank.1, B_blank.2.1.trans B_counts.2, B_blank.2.2.1,
    B_blank.2.2.2.trans B_counts.1, isUTMStrict_B⟩

theorem blank_desc_9_8 :
    (∃ r ∈ U9_8.U, r.s = 0) ∧ (symbols U9_8.U).dedup.length = NSyms U9_8.U ∧
    (∀ x ∈ symbols U9_8.U, (∃ r ∈ U9_8.U, r.s = x) ∧ (∃ r ∈ U9_8.U, r.t = x)) := by
  decide +kernel

theorem B_count : NStatesMorita B = 9 ∧ NSymsMorita B = 8 ∧ 0 ∈ symbols B := by decide +kernel

theorem exists_urtm_9_8_moritaCount :
    ∃ U : List Quint, Deterministic U ∧ Reversible U ∧
    NStatesMorita U = 9 ∧ NSymsMorita U = 8 ∧ 0 ∈ symbols U ∧ IsUTMStrict U :=
  ⟨B, B_det, B_rev, B_count.1, B_count.2.1, B_count.2.2, isUTMStrict_B⟩

theorem count_desc_9_8 :
    NStatesMorita U9_8.U = 9 + 2 ∧ NSymsMorita U9_8.U = 8 := by decide +kernel

end URTM.Univ.Final9_8
