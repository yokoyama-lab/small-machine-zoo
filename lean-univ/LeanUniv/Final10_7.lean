/-
  **URTM(10,7) in the sense of Def. 7.1** (computable encoding and decoding included), and the
  versions as in `FinalBook`, `FinalBlank` and `FinalMoritaCount`.

  URTM(11,7) with cycle_end merged into the merged state of case_y_2 / copy_y_2 and the symbols
  recoloured at the same time (the tag family L₁ and symbol merging solved jointly,
  results/joint-2026-11-02); `URTM.CTSH.U10_7.T10 = (T11.flatMap chg).eraseDups`
  (lean/URTM/CTSH10_7.lean, table not written out, 57 quintuples). The witness is
  `U10_7.U = numT U13_7.num T10` (`U10_7.U_def`); the encoder is that of (13,7), the readout counts
  the separators in both colours (`MoritaGen2.readM2`). No hypotheses. Minimality is not claimed.
  It dominates (11,7) and Morita's (10,8).

  The witness without its two halting quintuples is `B` (55 quintuples, `book_urtm_10_7`).
-/
import LeanUniv.U10_7
import LeanUniv.Book
import LeanUniv.MoritaCount
import LeanUniv.MoritaGen2

namespace URTM.Univ.Final10_7
open URTM URTM.Spec URTM.Univ.DropGen URTM.Univ.MoritaGen URTM.Univ.MoritaGen2 URTM.Univ.MoritaCount

theorem exists_urtm_10_7 :
    ∃ U : List Quint, Deterministic U ∧ Reversible U ∧ NStates U = 10 ∧ NSyms U = 7 ∧
      IsUTMStrict U :=
  U10_7.exists_urtm_10_7

/-- The two halting quintuples (as for (13,7)). -/
def H : List Quint := [⟨0, 0, 0, .Z, 13⟩, ⟨1, 0, 0, .Z, 14⟩]
/-- **URTM(10,7) without its halting quintuples** (55 quintuples). -/
def B : List Quint := dropT U10_7.U H

theorem B_book :
    H = U10_7.U.filter (fun r => decide (r.q ∉ U10_7.U.map Quint.p)) ∧
    B.length + 2 = U10_7.U.length ∧ ∀ r ∈ B, r.q ∈ B.map Quint.p := by decide +kernel
theorem B_counts : NStates B = 10 ∧ NSyms B = 7 := by decide +kernel
theorem B_det : Deterministic B := deterministic_dropT _ U10_7.U_det
theorem B_rev : Reversible B := reversible_dropT _ U10_7.U_rev
theorem isUTMStrict_B : IsUTMStrict B :=
  ChainGen.isUTMStrict_drop_ctsh (encM_primrec _ _ _) (readM2_primrec _ _ _ _) U10_7.body_U
    U10_7.U_det (by decide +kernel) _ (fun _ _ => rfl) (by decide +kernel) (by decide +kernel)

theorem exists_urtm_10_7_book :
    ∃ U : List Quint, Deterministic U ∧ Reversible U ∧ NStates U = 10 ∧ NSyms U = 7 ∧
      IsUTMStrict U :=
  ⟨B, B_det, B_rev, B_counts.1, B_counts.2, isUTMStrict_B⟩

theorem book_urtm_10_7 :
    B = dropT U10_7.U H ∧
    H = U10_7.U.filter (fun r => decide (r.q ∉ U10_7.U.map Quint.p)) ∧
    B.length + 2 = U10_7.U.length ∧ (∀ r ∈ B, r.q ∈ B.map Quint.p) ∧
    Deterministic B ∧ Reversible B ∧ NStates B = 10 ∧ NSyms B = 7 ∧ IsUTMStrict B :=
  ⟨rfl, B_book.1, B_book.2.1, B_book.2.2, B_det, B_rev, B_counts.1, B_counts.2, isUTMStrict_B⟩

theorem B_blank :
    (∃ r ∈ B, r.s = 0) ∧ (symbols B).dedup.length = NSyms B ∧
    (∀ x ∈ symbols B, (∃ r ∈ B, r.s = x) ∧ (∃ r ∈ B, r.t = x)) ∧
    (states B).dedup.length = NStates B := by decide +kernel

theorem exists_urtm_10_7_blank :
    ∃ U : List Quint, Deterministic U ∧ Reversible U ∧
    NStates U = 10 ∧ NSyms U = 7 ∧ (∃ r ∈ U, r.s = 0) ∧
    (symbols U).dedup.length = 7 ∧
    (∀ x ∈ symbols U, (∃ r ∈ U, r.s = x) ∧ (∃ r ∈ U, r.t = x)) ∧
    (states U).dedup.length = 10 ∧ IsUTMStrict U :=
  ⟨B, B_det, B_rev, B_counts.1, B_counts.2, B_blank.1, B_blank.2.1.trans B_counts.2, B_blank.2.2.1,
    B_blank.2.2.2.trans B_counts.1, isUTMStrict_B⟩

theorem blank_desc_10_7 :
    (∃ r ∈ U10_7.U, r.s = 0) ∧ (symbols U10_7.U).dedup.length = NSyms U10_7.U ∧
    (∀ x ∈ symbols U10_7.U, (∃ r ∈ U10_7.U, r.s = x) ∧ (∃ r ∈ U10_7.U, r.t = x)) := by
  decide +kernel

theorem B_count : NStatesMorita B = 10 ∧ NSymsMorita B = 7 ∧ 0 ∈ symbols B := by decide +kernel

theorem exists_urtm_10_7_moritaCount :
    ∃ U : List Quint, Deterministic U ∧ Reversible U ∧
    NStatesMorita U = 10 ∧ NSymsMorita U = 7 ∧ 0 ∈ symbols U ∧ IsUTMStrict U :=
  ⟨B, B_det, B_rev, B_count.1, B_count.2.1, B_count.2.2, isUTMStrict_B⟩

theorem count_desc_10_7 :
    NStatesMorita U10_7.U = 10 + 2 ∧ NSymsMorita U10_7.U = 7 := by decide +kernel

end URTM.Univ.Final10_7
