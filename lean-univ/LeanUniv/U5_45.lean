/-
  **URTM(5,45) as a Spec table, and its universality in the sense of Def. 7.1** (docs/24 P7b).

  `U = numT (Base15_6.numB 5) TpyB`: the block conversion of Morita's (15,6)
  (`URTM.Gen.KB5_45.TpyB = bconv T spB qsB ssB`, 164 quintuples; record of results/kstate_blocks), numbered by
  `BlockGen.numB`: states `Fin 5` by value, pseudo-states after them, `pl s ↦` the number of `s`
  in (15,6), `ctr i s ↦ 6·(i+1) +` that number.

  The exit layer is the zoo's theorem `URTM.CTSH.U5_45.urtm5_45_simulates_ctsh`; encoder and readout
  come from the base machine (`Base15_6.isUTMStrict_block15`).
-/
import LeanUniv.Base15_6
import URTM.CTSH5_45Main

namespace URTM.Univ.U5_45
open URTM URTM.CTSH URTM.Gen.K15_6 URTM.Univ.KToSpec
open URTM.KState (HaltsIn)
open URTM.KStateBlocks (bconv benc)
open URTM.Gen.KB5_45 (spB qsB ssB TpyB)

/-- **URTM(5,45) as a Spec table** (164 quintuples). -/
def U : List Quint := numT (Base15_6.numB 5) TpyB

/-- **Counts** (Morita's convention): 5 states, 45 symbols. -/
theorem U_counts : Spec.NStates U = 5 ∧ Spec.NSyms U = 45 := by decide +kernel
theorem U_det : Spec.Deterministic U := by decide +kernel
theorem U_rev : Spec.Reversible U := by decide +kernel

/-- The description-file convention, inherited from (15,6): the quintuples of `U` that enter a
    state without outgoing quintuples are exactly the images of the two halting quintuples of
    (15,6) (0-shift, reading a counter symbol, into the two different pseudo-states
    `halt`/`null`), and they are exactly the 0-shift quintuples of `U`. -/
theorem U_halting :
    U.filter (fun r => decide (r.q ∉ U.map Quint.p)) = [⟨4, 42, 0, .Z, 5⟩, ⟨4, 40, 4, .Z, 6⟩] ∧
    ∀ r ∈ U, (r.d = .Z ↔ r.q ∉ U.map Quint.p) := by decide +kernel

/-- The zoo's CTSH theorem for (5,45), on the generated table `TpyB`. -/
theorem hsim (C : CTSH) (w : List Ch) :
    (∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) → ∃ M rm, n ≤ M ∧
      HaltsIn TpyB M (benc T spB (URTM.CTSH.U15_6.encC15 C w)) (benc T spB (URTM.CTSH.U15_6.finCfg15 C vf mf rm))) ∧
    ((∀ n f, ¬ CHaltsIn C n (w, 0) f) →
      ∀ M c, ¬ HaltsIn TpyB M (benc T spB (URTM.CTSH.U15_6.encC15 C w)) c) := by
  obtain ⟨-, -, -, -, -, -, -, hT, hF, -, hN⟩ := URTM.CTSH.U5_45.urtm5_45_simulates_ctsh C w
  rw [hT] at hF hN
  exact ⟨hF, hN.mp⟩

/-- **URTM(5,45) is a UTM in the strict sense of Morita Def. 7.1.** -/
theorem isUTMStrict_U : Spec.IsUTMStrict U :=
  Base15_6.isUTMStrict_block15 spB TpyB hsim (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

end URTM.Univ.U5_45
