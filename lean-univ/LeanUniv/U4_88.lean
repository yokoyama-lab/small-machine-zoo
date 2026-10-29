/-
  **URTM(4,88) as a Spec table, and its universality in the sense of Def. 7.1** (docs/03 §2).

  `U = numT (Base10_8.numB 4) TpyR`: the 4-state conversion of Theorem A (`KState.conv`) applied to
  Morita's (10,8), with the states `Hp Hm Ap Am` renamed to `0 1 2 3` (`URTM.CTSH.U4_88B.TpyR`,
  223 quintuples), numbered by `BlockGen.numB`: states `Fin 4` by value, pseudo-states after them,
  `pl s ↦` the number of `s` in (10,8), `ctr i s ↦ 8·(i+1) +` that number.

  The exit layer is the zoo's theorem `URTM.CTSH.U4_88B.urtm4_88B_simulates_ctsh` (the CTSH theorem
  `U10_8.urtm4_88_simulates_ctsh` moved along the renaming, with the encoding written as `benc`);
  encoder and readout come from the base machine (`Base10_8.isUTMStrict_block10`), as for (4,46)
  and (4,48).
-/
import LeanUniv.Base10_8
import URTM.CTSH4_88BMain

namespace URTM.Univ.U4_88
open URTM URTM.CTSH URTM.Gen.K10_8 URTM.Univ.KToSpec
open URTM.KState (HaltsIn conv)
open URTM.KStateBlocks (benc)
open URTM.KStateRen (renR)
open URTM.CTSH.U4_88B (spH TpyR idx)

/-- **URTM(4,88) as a Spec table** (223 quintuples). -/
def U : List Quint := numT (Base10_8.numB 4) TpyR

/-- The table is the conversion of Theorem A applied to (10,8), up to the names of the states. -/
theorem U_is_conv : U = numT (Base10_8.numB 4) ((conv T qs ss).map (renR idx)) := by
  rw [U, URTM.CTSH.U4_88B.TpyR_eq_conv]

/-- **Counts** (Morita's convention): 4 states, 88 symbols. -/
theorem U_counts : Spec.NStates U = 4 ∧ Spec.NSyms U = 88 := by decide +kernel
theorem U_det : Spec.Deterministic U := by decide +kernel
theorem U_rev : Spec.Reversible U := by decide +kernel

/-- The zoo's CTSH theorem for (4,88), on the renamed table `TpyR`. -/
theorem hsim (C : CTSH) (w : List Ch) :
    (∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) → ∃ M rm, n ≤ M ∧
      HaltsIn TpyR M (benc T spH (URTM.CTSH.U10_8.encC C w))
        (benc T spH (URTM.CTSH.U10_8.finCfg C vf mf rm))) ∧
    ((∀ n f, ¬ CHaltsIn C n (w, 0) f) →
      ∀ M c, ¬ HaltsIn TpyR M (benc T spH (URTM.CTSH.U10_8.encC C w)) c) :=
  ⟨URTM.CTSH.U4_88B.fwd C w, (URTM.CTSH.U4_88B.div C w).mp⟩

/-- **URTM(4,88) is a UTM in the strict sense of Morita Def. 7.1.** -/
theorem isUTMStrict_U : Spec.IsUTMStrict U :=
  Base10_8.isUTMStrict_block10 spH TpyR hsim (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

end URTM.Univ.U4_88
