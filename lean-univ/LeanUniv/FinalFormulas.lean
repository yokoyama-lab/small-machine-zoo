/-
  **The symbol-count formulas of the construction section, on the concrete machines.**

  The general theorems are in `LeanUniv.SymCount`; here they are applied to the tables behind the
  points of the paper, and the values of the formulas are evaluated by the kernel (`decide +kernel`).

  * Block conversion (`blocks_<m>_<n>`): the set `V` of counter values, the sizes `|X_i|` in the order
    of `V`, the number of symbols `n` of the base machine, the count `n + Σ_{i∈V} |X_i|` of the block
    machine (from `SymCount.bconv_nsym`), the bound `(|V| + 1)·n`, and the equality with `Spec.NSyms`
    of the witness of `FinalBlocks.exists_urtm_<m>_<n>`.
  * Morita's 4-state conversion of (10,8) (`morita4_10_8`): `(2m + 1)·n = 21·8 = 168`, also for the
    table of the description file.
  * The direction-split 4-state conversion of (10,8) (`kstate4_10_8`): `(m + 1)·n = 11·8 = 88`.
  * The ε-reversed 4-state conversion of (10,8) (`eps4_10_8`): `(max(m₊, m₋) + 1)·n = 6·8 = 48`
    (bound, and the table has exactly 48).
  * Morita's 2-symbol conversion of (24,4) (`morita2_24_4`): the number of states (with rules)
    `|D_go| + m + P_r + P_w`.
  * Morita's 3-state conversion of (32,3) (`morita3_32_3`): `N(2M − 1) = 298·123 = 36654`, with
    `N = m n² + n² + 1 = 298` and `M = m₊ n + 2n + 2 = 62`.
  * The improved 3-state conversion of (32,3), mirrored (`three_32_3`): the counter bound of the table
    is `need3`, and the count is at most `1 + n + (m₋n + |G|)(n + 1) + n(n + 2 + |R| + |G|) + (n + 2)`
    = 600 with `n = 3`, `m₋ = 18`, `|R| = |G| = 36`; the witness of `Final3_600` has 600 symbols.
-/
import LeanUniv.SymCount
import LeanUniv.FinalBlocks
import LeanUniv.Final3_600
import URTM.CTSH4_168Main
import URTM.CTSH138_2Main
import URTM.CTSH3_36654Main
import URTM.Gen.KE10_8

set_option maxRecDepth 100000
set_option linter.unusedSectionVars false

namespace URTM.Univ.FinalFormulas

open URTM.KState (Machine)
open URTM.KStateBlocks (bconv)
open URTM.Univ.SymCount

/-! ## The general theorems (restated here so that their statements are pinned) -/

section General
variable {Q P S : Type} [DecidableEq Q] [DecidableEq P] [DecidableEq S]

/-- **Block conversion, for every `T`, `sp`**: the symbols are `pl s` (`s` a symbol of `T`) and
    `ctr i s` (`i ∈ V`, `s ∈ X_i`); their number is `n_T + Σ_{i∈V} |X_i| ≤ (|V| + 1)·n`. -/
theorem blocks_formula {k : ℕ} (T : Machine Q P S) (sp : URTM.KStateBlocks.BSpec Q k) (qs : List Q)
    (ss : List S) (hQ : ∀ q, q ∈ qs) (hS : ∀ s, s ∈ ss) (hss : ss.Nodup) :
    (∀ x, x ∈ syms (bconv T sp qs ss) ↔
      (∃ s, x = .pl s ∧ s ∈ syms T) ∨ (∃ i s, x = .ctr i s ∧ i ∈ bV T sp qs ss ∧ s ∈ bX T sp qs ss i)) ∧
    nsym (bconv T sp qs ss) = nsym T + ((bV T sp qs ss).map (fun i => (bX T sp qs ss i).length)).sum ∧
    nsym (bconv T sp qs ss) ≤ ((bV T sp qs ss).length + 1) * ss.length :=
  ⟨fun _ => mem_syms_bconv hQ hS, bconv_nsym hQ hS hss, bconv_nsym_le hQ hS hss⟩

/-- **Morita's 4-state conversion, for every `T`**: `(2m + 1)·n` symbols. -/
theorem morita4_formula (T : Machine Q P S) (idx : Q → ℕ) (m : ℕ) (side : Q → Bool) (ss : List S)
    (hS : ∀ s, s ∈ ss) (hss : ss.Nodup) (hidx : ∀ q, idx q < m) (hm : 1 ≤ m) :
    nsym (URTM.Conv55.conv T idx m side ss) = (2 * m + 1) * ss.length :=
  conv55_nsym hS hss hidx hm

/-- **The direction-split 4-state conversion, for every `T`**: `(m + 1)·n` symbols. -/
theorem kstate4_formula (T : Machine Q P S) (qs : List Q) (ss : List S) (hW : URTM.KState.ZeroShiftHalts T)
    (hQ : ∀ q, q ∈ qs) (hS : ∀ s, s ∈ ss) (hss : ss.Nodup) (hm : 1 ≤ qs.length) :
    nsym (URTM.KState.conv T qs ss) = (qs.length + 1) * ss.length :=
  kconv_nsym hW hQ hS hss hm

/-- **The ε-reversed 4-state conversion, for every reversible `T`**: at most `(max(m₊, m₋) + 1)·n`. -/
theorem eps4_formula (T : Machine Q P S) (qs : List Q) (ss : List S) (hW : URTM.KState.ZeroShiftHalts T)
    (hR : URTM.KState.Reversible T) (hQ : ∀ q, q ∈ qs) (hS : ∀ s, s ∈ ss) :
    nsym (URTM.KStateEps.econv T qs ss) ≤
      (max (URTM.KState.plusList T qs).length (URTM.KState.minusList T qs).length + 1) * ss.length :=
  econv_nsym_le hW hR hQ hS

/-- **Morita's 2-symbol conversion (2-bit codes), for every `T`**: `|D_go| + m + P_r + P_w ≤ 2m + P_r + P_w`
    states. -/
theorem morita2_formula (T : Machine Q P S) (code : S → Bool × Bool) (dir : Q → URTM.Dir) (qs : List Q)
    (hQ : ∀ q, q ∈ qs) (hqs : qs.Nodup) :
    nst (URTM.Conv54.conv T code dir qs) =
      (dGo T qs).length + qs.length + (pR T code qs).length + (pW T code qs).length ∧
    nst (URTM.Conv54.conv T code dir qs) ≤ 2 * qs.length + (pR T code qs).length + (pW T code qs).length :=
  ⟨conv54_nst hQ hqs, conv54_nst_le hQ hqs⟩

/-- **Morita's 3-state conversion of a 1WU machine, for every `T`**: `N(2M − 1)` symbols. -/
theorem morita3_formula (T : Machine Q P S) (qL : Q) (s0 : S) (idx : Q → ℕ) (m : ℕ) (ss : List S)
    (H : URTM.Conv510.Hyp T qL s0 idx m ss) (hsrc : ∀ r ∈ T, r.p ≠ qL → 1 ≤ idx r.p ∧ idx r.p < m)
    (hss : ss.Nodup) (hm : 2 ≤ m) :
    nsym (URTM.Conv510.conv T qL s0 idx m ss) = (2 * m - 1) * ss.length :=
  conv510_nsym H hsrc hss hm

/-- **The improved 3-state conversion, for every `T`** (not mirrored and mirrored): with the counter
    bound `need3` on the symbols of the 1WU machine, at most
    `1 + n + (m₋n + |G|)(n + 1) + n(n + 2 + |R| + |G|) + (n + 2)` symbols. -/
theorem three_formula (T : Machine Q P S) (b : S) (ss : List S) (qm : List Q) (Rl Gl : List (Q × S))
    (idx : URTM.Conv1W.VSt Q S → ℕ) (need : URTM.Conv1W.VSym Q S → ℕ)
    (hneed : ∀ x ∈ URTM.Conv3S.wsyms ss qm Gl, need x = need3 ss.length Rl.length Gl.length x) :
    (URTM.Conv3S.Hyp T b ss qm Rl Gl idx need →
      (∀ r ∈ URTM.Conv1W.conv T b ss qm Rl Gl, r.p ≠ .L → 1 ≤ idx r.p ∧ idx r.p ≤ need r.s) →
      nsym (URTM.Conv3S.conv T b ss qm Rl Gl idx need) ≤
        1 + ss.length + (qm.length * ss.length + Gl.length) * (ss.length + 1) +
          ss.length * (ss.length + 2 + Rl.length + Gl.length) + (ss.length + 2)) ∧
    (URTM.Conv3S.Hyp (URTM.Conv3Base.mirror T) b ss qm Rl Gl idx need →
      (∀ r ∈ URTM.Conv1W.conv (URTM.Conv3Base.mirror T) b ss qm Rl Gl, r.p ≠ .L →
        1 ≤ idx r.p ∧ idx r.p ≤ need r.s) →
      nsym (URTM.Conv3S.convM T b ss qm Rl Gl idx need) ≤
        1 + ss.length + (qm.length * ss.length + Gl.length) * (ss.length + 1) +
          ss.length * (ss.length + 2 + Rl.length + Gl.length) + (ss.length + 2)) :=
  ⟨fun H hsrc => conv3S_nsym_formula H hsrc hneed, fun H hsrc => convM3S_nsym_formula H hsrc hneed⟩

end General

/-! ## Block conversion: the six points -/

theorem blocks_4_46 :
    bV URTM.Gen.K10_8.T URTM.Gen.KB4_46.spB URTM.Gen.KB4_46.qsB URTM.Gen.KB4_46.ssB = [1, 2, 3, 4, 6] ∧
    [1, 2, 3, 4, 6].map (fun i => (bX URTM.Gen.K10_8.T URTM.Gen.KB4_46.spB URTM.Gen.KB4_46.qsB
      URTM.Gen.KB4_46.ssB i).length) = [8, 8, 8, 8, 6] ∧
    nsym URTM.Gen.K10_8.T = 8 ∧
    nsym (bconv URTM.Gen.K10_8.T URTM.Gen.KB4_46.spB URTM.Gen.KB4_46.qsB URTM.Gen.KB4_46.ssB) =
      8 + (8 + 8 + 8 + 8 + 6) ∧
    8 + (8 + 8 + 8 + 8 + 6) ≤ (5 + 1) * 8 ∧
    URTM.Spec.NSyms URTM.Univ.U4_46.U =
      nsym (bconv URTM.Gen.K10_8.T URTM.Gen.KB4_46.spB URTM.Gen.KB4_46.qsB URTM.Gen.KB4_46.ssB) := by
  have hV : bV URTM.Gen.K10_8.T URTM.Gen.KB4_46.spB URTM.Gen.KB4_46.qsB URTM.Gen.KB4_46.ssB =
      [1, 2, 3, 4, 6] := by decide +kernel
  have hX : [1, 2, 3, 4, 6].map (fun i => (bX URTM.Gen.K10_8.T URTM.Gen.KB4_46.spB URTM.Gen.KB4_46.qsB
      URTM.Gen.KB4_46.ssB i).length) = [8, 8, 8, 8, 6] := by decide +kernel
  have hT : nsym URTM.Gen.K10_8.T = 8 := by decide +kernel
  have hN := bconv_nsym (sp := URTM.Gen.KB4_46.spB) URTM.Gen.KB4_46.hQB URTM.Gen.KB4_46.hSB
    (T := URTM.Gen.K10_8.T) (by decide)
  rw [hV, hX, hT] at hN
  have hN' : nsym (bconv URTM.Gen.K10_8.T URTM.Gen.KB4_46.spB URTM.Gen.KB4_46.qsB URTM.Gen.KB4_46.ssB) =
      8 + (8 + 8 + 8 + 8 + 6) := hN.trans rfl
  exact ⟨hV, hX, hT, hN', by decide, by rw [hN', URTM.Univ.U4_46.U_counts.2]⟩

theorem blocks_5_45 :
    bV URTM.Gen.K15_6.T URTM.Gen.KB5_45.spB URTM.Gen.KB5_45.qsB URTM.Gen.KB5_45.ssB =
      [1, 2, 3, 4, 5, 6, 7, 8] ∧
    [1, 2, 3, 4, 5, 6, 7, 8].map (fun i => (bX URTM.Gen.K15_6.T URTM.Gen.KB5_45.spB URTM.Gen.KB5_45.qsB
      URTM.Gen.KB5_45.ssB i).length) = [3, 5, 5, 5, 5, 5, 5, 6] ∧
    nsym URTM.Gen.K15_6.T = 6 ∧
    nsym (bconv URTM.Gen.K15_6.T URTM.Gen.KB5_45.spB URTM.Gen.KB5_45.qsB URTM.Gen.KB5_45.ssB) =
      6 + (3 + 5 + 5 + 5 + 5 + 5 + 5 + 6) ∧
    6 + (3 + 5 + 5 + 5 + 5 + 5 + 5 + 6) ≤ (8 + 1) * 6 ∧
    URTM.Spec.NSyms URTM.Univ.U5_45.U =
      nsym (bconv URTM.Gen.K15_6.T URTM.Gen.KB5_45.spB URTM.Gen.KB5_45.qsB URTM.Gen.KB5_45.ssB) := by
  have hV : bV URTM.Gen.K15_6.T URTM.Gen.KB5_45.spB URTM.Gen.KB5_45.qsB URTM.Gen.KB5_45.ssB =
      [1, 2, 3, 4, 5, 6, 7, 8] := by decide +kernel
  have hX : [1, 2, 3, 4, 5, 6, 7, 8].map (fun i => (bX URTM.Gen.K15_6.T URTM.Gen.KB5_45.spB
      URTM.Gen.KB5_45.qsB URTM.Gen.KB5_45.ssB i).length) = [3, 5, 5, 5, 5, 5, 5, 6] := by decide +kernel
  have hT : nsym URTM.Gen.K15_6.T = 6 := by decide +kernel
  have hN := bconv_nsym (sp := URTM.Gen.KB5_45.spB) URTM.Gen.KB5_45.hQB URTM.Gen.KB5_45.hSB
    (T := URTM.Gen.K15_6.T) (by decide)
  rw [hV, hX, hT] at hN
  have hN' : nsym (bconv URTM.Gen.K15_6.T URTM.Gen.KB5_45.spB URTM.Gen.KB5_45.qsB URTM.Gen.KB5_45.ssB) =
      6 + (3 + 5 + 5 + 5 + 5 + 5 + 5 + 6) := hN.trans rfl
  exact ⟨hV, hX, hT, hN', by decide, by rw [hN', URTM.Univ.U5_45.U_counts.2]⟩

theorem blocks_6_37 :
    bV URTM.Gen.K10_8.T URTM.Gen.KB6_37.spB URTM.Gen.KB6_37.qsB URTM.Gen.KB6_37.ssB = [1, 2, 5, 6] ∧
    [1, 2, 5, 6].map (fun i => (bX URTM.Gen.K10_8.T URTM.Gen.KB6_37.spB URTM.Gen.KB6_37.qsB
      URTM.Gen.KB6_37.ssB i).length) = [6, 7, 8, 8] ∧
    nsym URTM.Gen.K10_8.T = 8 ∧
    nsym (bconv URTM.Gen.K10_8.T URTM.Gen.KB6_37.spB URTM.Gen.KB6_37.qsB URTM.Gen.KB6_37.ssB) =
      8 + (6 + 7 + 8 + 8) ∧
    8 + (6 + 7 + 8 + 8) ≤ (4 + 1) * 8 ∧
    URTM.Spec.NSyms URTM.Univ.U6_37.U =
      nsym (bconv URTM.Gen.K10_8.T URTM.Gen.KB6_37.spB URTM.Gen.KB6_37.qsB URTM.Gen.KB6_37.ssB) := by
  have hV : bV URTM.Gen.K10_8.T URTM.Gen.KB6_37.spB URTM.Gen.KB6_37.qsB URTM.Gen.KB6_37.ssB =
      [1, 2, 5, 6] := by decide +kernel
  have hX : [1, 2, 5, 6].map (fun i => (bX URTM.Gen.K10_8.T URTM.Gen.KB6_37.spB URTM.Gen.KB6_37.qsB
      URTM.Gen.KB6_37.ssB i).length) = [6, 7, 8, 8] := by decide +kernel
  have hT : nsym URTM.Gen.K10_8.T = 8 := by decide +kernel
  have hN := bconv_nsym (sp := URTM.Gen.KB6_37.spB) URTM.Gen.KB6_37.hQB URTM.Gen.KB6_37.hSB
    (T := URTM.Gen.K10_8.T) (by decide)
  rw [hV, hX, hT] at hN
  have hN' : nsym (bconv URTM.Gen.K10_8.T URTM.Gen.KB6_37.spB URTM.Gen.KB6_37.qsB URTM.Gen.KB6_37.ssB) =
      8 + (6 + 7 + 8 + 8) := hN.trans rfl
  exact ⟨hV, hX, hT, hN', by decide, by rw [hN', URTM.Univ.U6_37.U_counts.2]⟩

theorem blocks_7_32 :
    bV URTM.Gen.K15_6.T URTM.Gen.KB7_32.spB URTM.Gen.KB7_32.qsB URTM.Gen.KB7_32.ssB = [1, 2, 3, 4, 5] ∧
    [1, 2, 3, 4, 5].map (fun i => (bX URTM.Gen.K15_6.T URTM.Gen.KB7_32.spB URTM.Gen.KB7_32.qsB
      URTM.Gen.KB7_32.ssB i).length) = [6, 5, 5, 5, 5] ∧
    nsym URTM.Gen.K15_6.T = 6 ∧
    nsym (bconv URTM.Gen.K15_6.T URTM.Gen.KB7_32.spB URTM.Gen.KB7_32.qsB URTM.Gen.KB7_32.ssB) =
      6 + (6 + 5 + 5 + 5 + 5) ∧
    6 + (6 + 5 + 5 + 5 + 5) ≤ (5 + 1) * 6 ∧
    URTM.Spec.NSyms URTM.Univ.U7_32.U =
      nsym (bconv URTM.Gen.K15_6.T URTM.Gen.KB7_32.spB URTM.Gen.KB7_32.qsB URTM.Gen.KB7_32.ssB) := by
  have hV : bV URTM.Gen.K15_6.T URTM.Gen.KB7_32.spB URTM.Gen.KB7_32.qsB URTM.Gen.KB7_32.ssB =
      [1, 2, 3, 4, 5] := by decide +kernel
  have hX : [1, 2, 3, 4, 5].map (fun i => (bX URTM.Gen.K15_6.T URTM.Gen.KB7_32.spB URTM.Gen.KB7_32.qsB
      URTM.Gen.KB7_32.ssB i).length) = [6, 5, 5, 5, 5] := by decide +kernel
  have hT : nsym URTM.Gen.K15_6.T = 6 := by decide +kernel
  have hN := bconv_nsym (sp := URTM.Gen.KB7_32.spB) URTM.Gen.KB7_32.hQB URTM.Gen.KB7_32.hSB
    (T := URTM.Gen.K15_6.T) (by decide)
  rw [hV, hX, hT] at hN
  have hN' : nsym (bconv URTM.Gen.K15_6.T URTM.Gen.KB7_32.spB URTM.Gen.KB7_32.qsB URTM.Gen.KB7_32.ssB) =
      6 + (6 + 5 + 5 + 5 + 5) := hN.trans rfl
  exact ⟨hV, hX, hT, hN', by decide, by rw [hN', URTM.Univ.U7_32.U_counts.2]⟩

theorem blocks_8_28 :
    bV URTM.Gen.K17_5.T URTM.Gen.KB8_28.spB URTM.Gen.KB8_28.qsB URTM.Gen.KB8_28.ssB = [2, 4, 5, 6, 7] ∧
    [2, 4, 5, 6, 7].map (fun i => (bX URTM.Gen.K17_5.T URTM.Gen.KB8_28.spB URTM.Gen.KB8_28.qsB
      URTM.Gen.KB8_28.ssB i).length) = [3, 5, 5, 5, 5] ∧
    nsym URTM.Gen.K17_5.T = 5 ∧
    nsym (bconv URTM.Gen.K17_5.T URTM.Gen.KB8_28.spB URTM.Gen.KB8_28.qsB URTM.Gen.KB8_28.ssB) =
      5 + (3 + 5 + 5 + 5 + 5) ∧
    5 + (3 + 5 + 5 + 5 + 5) ≤ (5 + 1) * 5 ∧
    URTM.Spec.NSyms URTM.Univ.U8_28.U =
      nsym (bconv URTM.Gen.K17_5.T URTM.Gen.KB8_28.spB URTM.Gen.KB8_28.qsB URTM.Gen.KB8_28.ssB) := by
  have hV : bV URTM.Gen.K17_5.T URTM.Gen.KB8_28.spB URTM.Gen.KB8_28.qsB URTM.Gen.KB8_28.ssB =
      [2, 4, 5, 6, 7] := by decide +kernel
  have hX : [2, 4, 5, 6, 7].map (fun i => (bX URTM.Gen.K17_5.T URTM.Gen.KB8_28.spB URTM.Gen.KB8_28.qsB
      URTM.Gen.KB8_28.ssB i).length) = [3, 5, 5, 5, 5] := by decide +kernel
  have hT : nsym URTM.Gen.K17_5.T = 5 := by decide +kernel
  have hN := bconv_nsym (sp := URTM.Gen.KB8_28.spB) URTM.Gen.KB8_28.hQB URTM.Gen.KB8_28.hSB
    (T := URTM.Gen.K17_5.T) (by decide)
  rw [hV, hX, hT] at hN
  have hN' : nsym (bconv URTM.Gen.K17_5.T URTM.Gen.KB8_28.spB URTM.Gen.KB8_28.qsB URTM.Gen.KB8_28.ssB) =
      5 + (3 + 5 + 5 + 5 + 5) := hN.trans rfl
  exact ⟨hV, hX, hT, hN', by decide, by rw [hN', URTM.Univ.U8_28.U_counts.2]⟩

theorem blocks_9_27 :
    bV URTM.Gen.K15_6.T URTM.Gen.KB9_27.spB URTM.Gen.KB9_27.qsB URTM.Gen.KB9_27.ssB = [1, 2, 3, 4] ∧
    [1, 2, 3, 4].map (fun i => (bX URTM.Gen.K15_6.T URTM.Gen.KB9_27.spB URTM.Gen.KB9_27.qsB
      URTM.Gen.KB9_27.ssB i).length) = [6, 5, 5, 5] ∧
    nsym URTM.Gen.K15_6.T = 6 ∧
    nsym (bconv URTM.Gen.K15_6.T URTM.Gen.KB9_27.spB URTM.Gen.KB9_27.qsB URTM.Gen.KB9_27.ssB) =
      6 + (6 + 5 + 5 + 5) ∧
    6 + (6 + 5 + 5 + 5) ≤ (4 + 1) * 6 ∧
    URTM.Spec.NSyms URTM.Univ.U9_27.U =
      nsym (bconv URTM.Gen.K15_6.T URTM.Gen.KB9_27.spB URTM.Gen.KB9_27.qsB URTM.Gen.KB9_27.ssB) := by
  have hV : bV URTM.Gen.K15_6.T URTM.Gen.KB9_27.spB URTM.Gen.KB9_27.qsB URTM.Gen.KB9_27.ssB =
      [1, 2, 3, 4] := by decide +kernel
  have hX : [1, 2, 3, 4].map (fun i => (bX URTM.Gen.K15_6.T URTM.Gen.KB9_27.spB URTM.Gen.KB9_27.qsB
      URTM.Gen.KB9_27.ssB i).length) = [6, 5, 5, 5] := by decide +kernel
  have hT : nsym URTM.Gen.K15_6.T = 6 := by decide +kernel
  have hN := bconv_nsym (sp := URTM.Gen.KB9_27.spB) URTM.Gen.KB9_27.hQB URTM.Gen.KB9_27.hSB
    (T := URTM.Gen.K15_6.T) (by decide)
  rw [hV, hX, hT] at hN
  have hN' : nsym (bconv URTM.Gen.K15_6.T URTM.Gen.KB9_27.spB URTM.Gen.KB9_27.qsB URTM.Gen.KB9_27.ssB) =
      6 + (6 + 5 + 5 + 5) := hN.trans rfl
  exact ⟨hV, hX, hT, hN', by decide, by rw [hN', URTM.Univ.U9_27.U_counts.2]⟩

/-! ## The 4-state conversions of (10,8) -/

/-- **Morita's 4-state conversion of (10,8)**: `(2m + 1)·n = 168` (the 10 states numbered `0..9`),
    for the converted machine and for the table of the description file `urtm4-168.txt`. -/
theorem morita4_10_8 :
    nsym (URTM.Conv55.conv URTM.CTSH.U4_168.T10' URTM.CTSH.U4_168.idx10 10 URTM.CTSH.U4_168.side10
      URTM.Gen.K10_8.ss) = (2 * 10 + 1) * 8 ∧
    nsym URTM.Gen.F4_168.T4 = 168 := by
  have h := conv55_nsym (T := URTM.CTSH.U4_168.T10') (idx := URTM.CTSH.U4_168.idx10) (side := URTM.CTSH.U4_168.side10)
    URTM.Gen.K10_8.hS (by decide) (fun q => by cases q <;> decide) (m := 10) (by decide)
  refine ⟨h.trans rfl, ?_⟩
  rw [nsym_congr URTM.CTSH.U4_168.rules4_sub URTM.CTSH.U4_168.rules4_sup, h]
  rfl

/-- **The direction-split 4-state conversion of (10,8)**: `(m + 1)·n = 88`. -/
theorem kstate4_10_8 :
    nsym (URTM.KState.conv URTM.Gen.K10_8.T URTM.Gen.K10_8.qs URTM.Gen.K10_8.ss) = (10 + 1) * 8 :=
  (kconv_nsym URTM.Gen.K10_8.hW URTM.Gen.K10_8.hQ URTM.Gen.K10_8.hS (by decide) (by decide)).trans rfl

/-- **The ε-reversed 4-state conversion of (10,8)**: `m₊ = m₋ = 5`, the bound
    `(max(m₊, m₋) + 1)·n = 48`, attained. -/
theorem eps4_10_8 :
    (URTM.KState.plusList URTM.Gen.K10_8.T URTM.Gen.KE10_8.qsE).length = 5 ∧
    (URTM.KState.minusList URTM.Gen.K10_8.T URTM.Gen.KE10_8.qsE).length = 5 ∧
    nsym (URTM.KStateEps.econv URTM.Gen.K10_8.T URTM.Gen.KE10_8.qsE URTM.Gen.K10_8.ss) ≤ (max 5 5 + 1) * 8 ∧
    nsym (URTM.KStateEps.econv URTM.Gen.K10_8.T URTM.Gen.KE10_8.qsE URTM.Gen.K10_8.ss) = 48 := by
  have hp : (URTM.KState.plusList URTM.Gen.K10_8.T URTM.Gen.KE10_8.qsE).length = 5 := by decide +kernel
  have hm : (URTM.KState.minusList URTM.Gen.K10_8.T URTM.Gen.KE10_8.qsE).length = 5 := by decide +kernel
  have h := econv_nsym_le URTM.Gen.K10_8.hW URTM.Gen.K10_8.hR URTM.Gen.KE10_8.hQE URTM.Gen.K10_8.hS
  rw [hp, hm] at h
  refine ⟨hp, hm, h.trans (le_of_eq rfl), ?_⟩
  rw [URTM.Gen.KE10_8.econv_eq_py]
  decide +kernel

/-! ## Morita's 2-symbol conversion of (24,4) -/

/-- **Morita's 2-symbol conversion of (24,4)** (2-bit codes, the halting quintuples dropped): every one
    of the 24 states has a rule into a real state, `P_r = P_w = 45`, and the converted machine and the
    table of the description file `urtm138-2.txt` have `2m + P_r + P_w = 48 + 45 + 45 = 138` states. -/
theorem morita2_24_4 :
    (dGo URTM.CTSH.U138_2.T24' URTM.Gen.K24_4.qs).length = 24 ∧
    (pR URTM.CTSH.U138_2.T24' URTM.CTSH.U138_2.code24 URTM.Gen.K24_4.qs).length = 45 ∧
    (pW URTM.CTSH.U138_2.T24' URTM.CTSH.U138_2.code24 URTM.Gen.K24_4.qs).length = 45 ∧
    nst (URTM.Conv54.conv URTM.CTSH.U138_2.T24' URTM.CTSH.U138_2.code24 URTM.CTSH.U138_2.dir24
      URTM.Gen.K24_4.qs) = 2 * 24 + 45 + 45 ∧
    nst URTM.Gen.F138_2.T138 = 138 := by
  have h1 : (dGo URTM.CTSH.U138_2.T24' URTM.Gen.K24_4.qs).length = 24 := by decide +kernel
  have h2 : (pR URTM.CTSH.U138_2.T24' URTM.CTSH.U138_2.code24 URTM.Gen.K24_4.qs).length = 45 := by
    decide +kernel
  have h3 : (pW URTM.CTSH.U138_2.T24' URTM.CTSH.U138_2.code24 URTM.Gen.K24_4.qs).length = 45 := by
    decide +kernel
  have h := conv54_nst (T := URTM.CTSH.U138_2.T24') (code := URTM.CTSH.U138_2.code24)
    (dir := URTM.CTSH.U138_2.dir24) URTM.Gen.K24_4.hQ (by decide)
  have hq : URTM.Gen.K24_4.qs.length = 24 := by decide
  rw [h1, h2, h3, hq] at h
  refine ⟨h1, h2, h3, h.trans rfl, ?_⟩
  rw [nst_congr URTM.CTSH.U138_2.rules138_sub URTM.CTSH.U138_2.rules138_sup, h]

/-! ## Morita's 3-state conversion of (32,3) -/

/-- **Morita's 3-state conversion of (32,3)**: the 1WU machine has `N = m n² + n² + 1 = 298` symbols
    and its states other than `q_L` are numbered below `M = m₊ n + 2n + 2 = 62` (`m₊ = 18`); the
    3-state machine has `N(2M − 1) = 36654` symbols. -/
theorem morita3_32_3 :
    URTM.CTSH.U3_36654.allW.length = 32 * 3 ^ 2 + 3 ^ 2 + 1 ∧
    URTM.CTSH.U3_36654.qp32.length = 18 ∧ 62 = 18 * 3 + 2 * 3 + 2 ∧
    nsym URTM.CTSH.U3_36654.Tdag = 298 * (2 * 62 - 1) ∧ 298 * (2 * 62 - 1) = 36654 := by
  have hW : URTM.CTSH.U3_36654.allW.length = 298 := by decide +kernel
  refine ⟨hW, by decide +kernel, rfl, ?_, rfl⟩
  have hsrc3 : ∀ r ∈ URTM.CTSH.U3_36654.That, r.p ≠ .L →
    1 ≤ URTM.CTSH.U3_36654.idx3 r.p ∧ URTM.CTSH.U3_36654.idx3 r.p < 62 := by
    decide +kernel
  have := conv510_nsym URTM.CTSH.U3_36654.hyp510 hsrc3 (by decide +kernel) (by decide)
  rw [URTM.CTSH.U3_36654.Tdag, this, hW, Nat.mul_comm]

/-! ## The improved 3-state conversion of (32,3), mirrored: 600 -/

/-- **The improved 3-state conversion of (32,3) (mirrored)**: the counter bound of the table is
    `need3 3 36 36` (`n = 3`, `|R| = |G| = 36`), `m₋ = 18`, and the 3-state machine has at most
    `1 + n + (m₋n + |G|)(n + 1) + n(n + 2 + |R| + |G|) + (n + 2) = 600` symbols; the witness of
    `Final3_600` has exactly 600. -/
theorem three_32_3 :
    (∀ x ∈ URTM.Conv3S.wsyms URTM.Gen.K32_3.ss URTM.Gen.T3_600.qmR URTM.Gen.T3_600.GlR,
      URTM.Gen.T3_600.need x = need3 3 36 36 x) ∧
    URTM.Gen.K32_3.ss.length = 3 ∧ URTM.Gen.T3_600.qmR.length = 18 ∧
    URTM.Gen.T3_600.RlR.length = 36 ∧ URTM.Gen.T3_600.GlR.length = 36 ∧
    nsym URTM.Gen.T3_600.T3py ≤ 1 + 3 + (18 * 3 + 36) * (3 + 1) + 3 * (3 + 2 + 36 + 36) + (3 + 2) ∧
    1 + 3 + (18 * 3 + 36) * (3 + 1) + 3 * (3 + 2 + 36 + 36) + (3 + 2) = 600 ∧
    URTM.Spec.NSyms URTM.Univ.U3_600.U = 600 := by
  have hneed : ∀ x ∈ URTM.Conv3S.wsyms URTM.Gen.K32_3.ss URTM.Gen.T3_600.qmR URTM.Gen.T3_600.GlR,
      URTM.Gen.T3_600.need x = need3 3 36 36 x := by decide +kernel
  have hl : URTM.Gen.K32_3.ss.length = 3 ∧ URTM.Gen.T3_600.qmR.length = 18 ∧
      URTM.Gen.T3_600.RlR.length = 36 ∧ URTM.Gen.T3_600.GlR.length = 36 := by decide +kernel
  obtain ⟨h1, h2, h3, h4⟩ := hl
  have h := convM3S_nsym_formula URTM.Gen.T3_600.hyp URTM.Gen.T3_600.hsrc
    (by rw [h1, h3, h4]; exact hneed)
  rw [URTM.Gen.T3_600.convM_eq_py, h1, h2, h3, h4] at h
  exact ⟨hneed, h1, h2, h3, h4, h, rfl, URTM.Univ.U3_600.U_counts.2⟩

end URTM.Univ.FinalFormulas
