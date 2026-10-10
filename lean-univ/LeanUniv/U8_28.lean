/-
  **URTM(8,28) as a Spec table, and its universality in the sense of Def. 7.1** (docs/24 P7b).

  `U = numT (Base17_5.numB 8) TpyB`: the block conversion of Morita's (17,5)
  (`URTM.Gen.KB8_28.TpyB = bconv T spB qsB ssB`, 169 quintuples; record of autoresearch/frontier), numbered by
  `BlockGen.numB`: states `Fin 8` by value, pseudo-states after them, `pl s ↦` the number of `s`
  in (17,5), `ctr i s ↦ 5·(i+1) +` that number.

  The exit layer is the zoo's theorem `URTM.CTSH.U8_28.urtm8_28_simulates_ctsh`; encoder and readout
  come from the base machine (`Base17_5.isUTMStrict_block17`).
-/
import LeanUniv.Base17_5
import URTM.CTSH8_28Main

namespace URTM.Univ.U8_28
open URTM URTM.CTSH URTM.Gen.K17_5 URTM.Univ.KToSpec
open URTM.KState (HaltsIn)
open URTM.KStateBlocks (bconv benc)
open URTM.Gen.KB8_28 (spB qsB ssB TpyB)

/-- **URTM(8,28) as a Spec table** (169 quintuples). -/
def U : List Quint := numT (Base17_5.numB 8) TpyB

/-- **Counts** (Morita's convention): 8 states, 28 symbols. -/
theorem U_counts : Spec.NStates U = 8 ∧ Spec.NSyms U = 28 := by decide +kernel
theorem U_det : Spec.Deterministic U := by decide +kernel
theorem U_rev : Spec.Reversible U := by decide +kernel

/-- The description-file convention, inherited from (17,5): the quintuples of `U` that enter a
    state without outgoing quintuples are exactly the images of the two halting quintuples of
    (17,5) (0-shift, reading a counter symbol, into the two different pseudo-states
    `halt`/`null`), and they are exactly the 0-shift quintuples of `U`. -/
theorem U_halting :
    U.filter (fun r => decide (r.q ∉ U.map Quint.p)) = [⟨7, 40, 0, .Z, 8⟩, ⟨7, 39, 4, .Z, 9⟩] ∧
    ∀ r ∈ U, (r.d = .Z ↔ r.q ∉ U.map Quint.p) := by decide +kernel

/-- The zoo's CTSH theorem for (8,28), on the generated table `TpyB`. -/
theorem hsim (C : CTSH) (w : List Ch) :
    (∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) → ∃ M rm, n ≤ M ∧
      HaltsIn TpyB M (benc T spB (URTM.CTSH.U17_5.encC17 C w)) (benc T spB (URTM.CTSH.U17_5.finCfg17 C vf mf rm))) ∧
    ((∀ n f, ¬ CHaltsIn C n (w, 0) f) →
      ∀ M c, ¬ HaltsIn TpyB M (benc T spB (URTM.CTSH.U17_5.encC17 C w)) c) := by
  obtain ⟨-, -, -, -, -, -, -, hT, hF, -, hN⟩ := URTM.CTSH.U8_28.urtm8_28_simulates_ctsh C w
  rw [hT] at hF hN
  exact ⟨hF, hN.mp⟩

/-- **URTM(8,28) is a UTM in the strict sense of Morita Def. 7.1.** -/
theorem isUTMStrict_U : Spec.IsUTMStrict U :=
  Base17_5.isUTMStrict_block17 spB TpyB hsim (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

end URTM.Univ.U8_28
