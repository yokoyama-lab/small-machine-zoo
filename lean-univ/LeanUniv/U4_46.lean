/-
  **URTM(4,46) as a Spec table, and its universality in the sense of Def. 7.1** (docs/24 P7b).

  `U = numT (Base10_8.numB 4) TpyB`: the block conversion of Morita's (10,8)
  (`URTM.Gen.KB4_46.TpyB = bconv T spB qsB ssB`, 157 quintuples; record of results/kstate_blocks), numbered by
  `BlockGen.numB`: states `Fin 4` by value, pseudo-states after them, `pl s ↦` the number of `s`
  in (10,8), `ctr i s ↦ 8·(i+1) +` that number.

  The exit layer is the zoo's theorem `URTM.CTSH.U4_46.urtm4_46_simulates_ctsh`; encoder and readout
  come from the base machine (`Base10_8.isUTMStrict_block10`).
-/
import LeanUniv.Base10_8
import URTM.CTSH4_46Main

namespace URTM.Univ.U4_46
open URTM URTM.CTSH URTM.Gen.K10_8 URTM.Univ.KToSpec
open URTM.KState (HaltsIn)
open URTM.KStateBlocks (bconv benc)
open URTM.Gen.KB4_46 (spB qsB ssB TpyB)

/-- **URTM(4,46) as a Spec table** (157 quintuples). -/
def U : List Quint := numT (Base10_8.numB 4) TpyB

/-- **Counts** (Morita's convention): 4 states, 46 symbols. -/
theorem U_counts : Spec.NStates U = 4 ∧ Spec.NSyms U = 46 := by decide +kernel
theorem U_det : Spec.Deterministic U := by decide +kernel
theorem U_rev : Spec.Reversible U := by decide +kernel

/-- The description-file convention, inherited from (10,8): the quintuples of `U` that enter a
    state without outgoing quintuples are exactly the images of the two halting quintuples of
    (10,8) (0-shift, reading a counter symbol, into the two different pseudo-states
    `halt`/`null`), and they are exactly the 0-shift quintuples of `U`. -/
theorem U_halting :
    U.filter (fun r => decide (r.q ∉ U.map Quint.p)) = [⟨2, 16, 0, .Z, 4⟩, ⟨3, 56, 0, .Z, 5⟩] ∧
    ∀ r ∈ U, (r.d = .Z ↔ r.q ∉ U.map Quint.p) := by decide +kernel

/-- The zoo's CTSH theorem for (4,46), on the generated table `TpyB`. -/
theorem hsim (C : CTSH) (w : List Ch) :
    (∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) → ∃ M rm, n ≤ M ∧
      HaltsIn TpyB M (benc T spB (URTM.CTSH.U10_8.encC C w)) (benc T spB (URTM.CTSH.U10_8.finCfg C vf mf rm))) ∧
    ((∀ n f, ¬ CHaltsIn C n (w, 0) f) →
      ∀ M c, ¬ HaltsIn TpyB M (benc T spB (URTM.CTSH.U10_8.encC C w)) c) := by
  obtain ⟨-, -, -, -, -, -, -, hT, hF, -, hN⟩ := URTM.CTSH.U4_46.urtm4_46_simulates_ctsh C w
  rw [hT] at hF hN
  exact ⟨hF, hN.mp⟩

/-- **URTM(4,46) is a UTM in the strict sense of Morita Def. 7.1.** -/
theorem isUTMStrict_U : Spec.IsUTMStrict U :=
  Base10_8.isUTMStrict_block10 spB TpyB hsim (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

end URTM.Univ.U4_46
