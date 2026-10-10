/-
  **URTM(6,37) as a Spec table, and its universality in the sense of Def. 7.1** (docs/24 P7b).

  `U = numT (Base10_8.numB 6) TpyB`: the block conversion of Morita's (10,8)
  (`URTM.Gen.KB6_37.TpyB = bconv T spB qsB ssB`, 181 quintuples; record of autoresearch/frontier), numbered by
  `BlockGen.numB`: states `Fin 6` by value, pseudo-states after them, `pl s ↦` the number of `s`
  in (10,8), `ctr i s ↦ 8·(i+1) +` that number.

  The exit layer is the zoo's theorem `URTM.CTSH.U6_37.urtm6_37_simulates_ctsh`; encoder and readout
  come from the base machine (`Base10_8.isUTMStrict_block10`).
-/
import LeanUniv.Base10_8
import URTM.CTSH6_37Main

namespace URTM.Univ.U6_37
open URTM URTM.CTSH URTM.Gen.K10_8 URTM.Univ.KToSpec
open URTM.KState (HaltsIn)
open URTM.KStateBlocks (bconv benc)
open URTM.Gen.KB6_37 (spB qsB ssB TpyB)

/-- **URTM(6,37) as a Spec table** (181 quintuples). -/
def U : List Quint := numT (Base10_8.numB 6) TpyB

/-- **Counts** (Morita's convention): 6 states, 37 symbols. -/
theorem U_counts : Spec.NStates U = 6 ∧ Spec.NSyms U = 37 := by decide +kernel
theorem U_det : Spec.Deterministic U := by decide +kernel
theorem U_rev : Spec.Reversible U := by decide +kernel

/-- The description-file convention, inherited from (10,8): the quintuples of `U` that enter a
    state without outgoing quintuples are exactly the images of the two halting quintuples of
    (10,8) (0-shift, reading a counter symbol, into the two different pseudo-states
    `halt`/`null`), and they are exactly the 0-shift quintuples of `U`. -/
theorem U_halting :
    U.filter (fun r => decide (r.q ∉ U.map Quint.p)) = [⟨4, 24, 0, .Z, 6⟩, ⟨3, 16, 0, .Z, 7⟩] ∧
    ∀ r ∈ U, (r.d = .Z ↔ r.q ∉ U.map Quint.p) := by decide +kernel

/-- The zoo's CTSH theorem for (6,37), on the generated table `TpyB`. -/
theorem hsim (C : CTSH) (w : List Ch) :
    (∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) → ∃ M rm, n ≤ M ∧
      HaltsIn TpyB M (benc T spB (URTM.CTSH.U10_8.encC C w)) (benc T spB (URTM.CTSH.U10_8.finCfg C vf mf rm))) ∧
    ((∀ n f, ¬ CHaltsIn C n (w, 0) f) →
      ∀ M c, ¬ HaltsIn TpyB M (benc T spB (URTM.CTSH.U10_8.encC C w)) c) := by
  obtain ⟨-, -, -, -, -, -, -, hT, hF, -, hN⟩ := URTM.CTSH.U6_37.urtm6_37_simulates_ctsh C w
  rw [hT] at hF hN
  exact ⟨hF, hN.mp⟩

/-- **URTM(6,37) is a UTM in the strict sense of Morita Def. 7.1.** -/
theorem isUTMStrict_U : Spec.IsUTMStrict U :=
  Base10_8.isUTMStrict_block10 spB TpyB hsim (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

end URTM.Univ.U6_37
