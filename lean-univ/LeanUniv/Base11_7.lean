/-
  **Block conversions of URTM(11,7)** (results/symmerge-2026-10-05, record urtm11-7.k4.r47.m40; 2026-11-02):
  the base data for the block-converted tables built from `T11`, the table of URTM(11,7)
  (`URTM.CTSH.U11_7.T11 = T.map chg`, Morita's (13,7) with two pairs of states merged; `U11_7.lean`).
  Same role as `Base13_7` for Morita's (13,7).

  The types `St`, `Sy`, `Ps`, the numbering (`Base13_7.numB`), the encoder (`encM`) and the readout
  (`readM`) are those of (13,7): the initial configuration `encC11` is Morita's, and the readout only
  counts the separators ∗ before the mark Y and reads ϕ₁(v) after it (`U11_7.lean`). Only the final
  configurations differ (`finCfg11`: in `halt`, the erased symbols are `loN`, N or n, never ∗).

  * `henc`, `hnullfin`, `hhaltfin`: the initial and final configurations of (11,7) in the form used by
    `BlockGen.readM_fin` (they restate, as standalone lemmas, what `U11_7.body_U` proves inline).
  * `numB`: the numbering of (13,7) (`Base13_7.numB`), under the name the generated modules expect.
  * `strictBody_block11`, `isUTMStrict_block11`: `BlockGen.strictBody_block` / `isUTMStrict_block`
    specialised to the base `T11`, with the same hypotheses as `Base13_7.strictBody_block13`.
-/
import LeanUniv.Base13_7
import LeanUniv.U11_7

namespace URTM.Univ.Base11_7
open URTM URTM.CTSH URTM.Gen.K13_7 URTM.Univ.KToSpec URTM.Univ.NumGen URTM.Univ.MoritaGen
open URTM.KState (Tgt Cfg Machine HaltsIn KSym)
open URTM.KStateBlocks (BSpec benc rst)
open URTM.CTSH.U13_7 (nm13)
open URTM.CTSH.U11_7 (T11 encC11 finCfg11 finList11 loN)
open URTM.Univ.U13_7 (num lo13 hls)
open URTM.Univ.U11_7 (hlsN)

/-- The numbering of a block conversion of `T11` with `k` states: that of (13,7) (`Base13_7.numB`;
    the types `St`, `Ps`, `Sy` are the same). -/
abbrev numB (k : ℕ) : Numbering (Fin k) Ps (KSym Sy) := Base13_7.numB k

/-- The initial configuration is Morita's (that of (13,7)). -/
theorem henc (C : CTSH) (w : List Ch) :
    encC11 C w = ⟨.go .q0, (((Sim.RA lo13 .s5 .s0 C 0).length + 2 : ℕ) : ℤ),
      Sim.tp .s0 (Sy.s0 :: Sim.RA lo13 .s5 .s0 C 0 ++ Sy.s6 :: w.map lo13)⟩ := by
  simp [encC11, URTM.CTSH.U13_7.encC, URTM.CTSH.U13_7.rep, URTM.CTSH.U13_7.tapeList, nm13, lo13]

/-- The final configuration for `(λ, m)`: pseudo-state `null` (`h0`), `|C|` separators on the
    tape (as for (13,7)). -/
theorem hnullfin (C : CTSH) (mf : ℕ) (rm : List Ch) (hm : mf ≤ C.length) :
    ∃ (L : List Sy) (p : ℕ), p ≤ L.length ∧
      finCfg11 C [] mf rm = ⟨.halt .h0, p, Sim.tp .s0 L⟩ ∧ L.count .s5 = C.length := by
  refine ⟨finList11 C [] mf rm, (URTM.CTSH.U13_7.RA nm13 C mf).length + 2 + rm.length, ?_, ?_, ?_⟩
  · simp [finList11, URTM.CTSH.U13_7.tapeList]; omega
  · simp [finCfg11, nm13]
  · have h := count_RA lo13 Sy.s5 Sy.s0 hls (by decide) C hm
    simp only [finList11, URTM.CTSH.U13_7.tapeList, List.map_nil, List.append_nil, List.count_cons,
      List.count_append]
    rw [show (URTM.CTSH.U13_7.RA nm13 C mf).count Sy.s5 = C.length from h,
      show (rm.map (URTM.CTSH.U13_7.lo nm13)).count Sy.s5 = 0 from count_lo lo13 _ hls rm]
    simp [nm13]

/-- The final configuration for `(Y v, 0)`: pseudo-state `halt` (`h1`), the tape ends with
    `Y ϕ₁(v)`; the erased symbols before `$` are `loN rm` (N or n), which are not ∗. -/
theorem hhaltfin (C : CTSH) (v rm : List Ch) :
    ∃ (A : List Sy) (mk : Sy) (p : ℕ), p ≤ (A ++ mk :: v.map lo13).length ∧
      finCfg11 C (.Y :: v) 0 rm = ⟨.halt .h1, p, Sim.tp .s0 (A ++ mk :: v.map lo13)⟩ ∧
      (A ++ [mk]).count .s5 - 0 = C.length ∧ num.sym mk ≠ 0 ∧ num.sym mk ≠ 1 ∧
      num.sym mk ≠ 2 := by
  refine ⟨Sy.s0 :: URTM.CTSH.U13_7.RA nm13 C 0 ++ Sy.s6 :: rm.map loN, Sy.s3,
    (URTM.CTSH.U13_7.RA nm13 C 0).length, ?_, ?_, ?_, by decide, by decide, by decide⟩
  · simp; omega
  · simp [finCfg11, finList11, nm13, lo13]
  · have h := count_RA lo13 Sy.s5 Sy.s0 hls (by decide) C (Nat.zero_le _)
    simp only [List.count_cons, List.count_append, List.count_nil]
    rw [show (URTM.CTSH.U13_7.RA nm13 C 0).count Sy.s5 = C.length from h,
      show (rm.map loN).count Sy.s5 = 0 from count_lo loN _ hlsN rm]
    simp

/-- **Body form** of `isUTMStrict_block11`: the body of `IsUTMStrict` for a block conversion of
    `T11`, with the explicit encoder and decoder of (13,7). Same hypotheses as
    `Base13_7.strictBody_block13`, with `T11` in place of `T`. -/
theorem strictBody_block11 {k : ℕ} (sp : BSpec St k) (T' : Machine (Fin k) Ps (KSym Sy))
    (hsim : ∀ C w,
      (∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) → ∃ M rm, n ≤ M ∧
        HaltsIn T' M (benc T11 sp (encC11 C w)) (benc T11 sp (finCfg11 C vf mf rm))) ∧
      ((∀ n f, ¬ CHaltsIn C n (w, 0) f) →
        ∀ M c, ¬ HaltsIn T' M (benc T11 sp (encC11 C w)) c))
    (hU0 : (rst T11 sp .h St.q0).val ∈ Spec.states (numT (numB k) T'))
    (hUA : ∀ a ∈ [num.sym Sy.s6, 0, num.sym Sy.s5, 1, 2] ++ [1, 2],
      a = 0 ∨ a ∈ Spec.symbols (numT (numB k) T'))
    (hUK : ∀ a ∈ 0 :: [1, 2], 7 * (sp.v St.q0 + 1) + a = 0 ∨
      7 * (sp.v St.q0 + 1) + a ∈ Spec.symbols (numT (numB k) T')) :
    DropGen.StrictBody (numT (numB k) T')
      (ChainGen.cOf (fun C w => BlockGen.encB (rst T11 sp .h St.q0).val (7 * (sp.v St.q0 + 1))
        ((encM (num.st (.go St.q0)) (num.sym Sy.s6) (num.sym Sy.s5)) C w)))
      (GenDec.dOf (readM (k + [Ps.h0, Ps.h1].idxOf Ps.h1) (num.sym Sy.s5) 0)) :=
  BlockGen.strictBody_block num 7 Base13_7.sym_lt [.h0, .h1] _ T11 sp T' Sy.s0 (by decide) St.q0
    encC11 finCfg11 (fun C => (((Sim.RA lo13 .s5 .s0 C 0).length + 2 : ℕ) : ℤ))
    (encM (num.st (.go St.q0)) (num.sym Sy.s6) (num.sym Sy.s5))
    (fun C w => by rw [henc]; exact encM_eq num lo13 .s5 .s0 (by decide) Base13_7.hlo .q0 .s6 C w)
    (fun C w => by rw [henc])
    (fun C w => (hsim C w).1) (fun C w => (hsim C w).2)
    (readM (k + [Ps.h0, Ps.h1].idxOf Ps.h1) (num.sym Sy.s5) 0)
    (fun _ _ _ h => readM_toID _ _ _ (by decide) h)
    (fun C vf mf rm hf => BlockGen.readM_fin num lo13 .s5 .s0 .h0 .h1 0 Base13_7.hlo hls
      (fun h => k + [Ps.h0, Ps.h1].idxOf h)
      (fun h => absurd (Nat.add_left_cancel h) (by decide)) finCfg11 hnullfin hhaltfin
      C vf mf rm hf)
    [num.sym Sy.s6, 0, num.sym Sy.s5, 1, 2] [1, 2]
    (fun C w => BlockGen.encM_left _ _ _ C w) (fun C w => BlockGen.encM_right _ _ _ C w)
    hU0 hUA hUK

/-- **A block conversion of `T11` (URTM(11,7)) that simulates every CTSH is a UTM in the strict
    sense of Morita Def. 7.1**, given three finite facts about its table. -/
theorem isUTMStrict_block11 {k : ℕ} (sp : BSpec St k) (T' : Machine (Fin k) Ps (KSym Sy))
    (hsim : ∀ C w,
      (∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) → ∃ M rm, n ≤ M ∧
        HaltsIn T' M (benc T11 sp (encC11 C w)) (benc T11 sp (finCfg11 C vf mf rm))) ∧
      ((∀ n f, ¬ CHaltsIn C n (w, 0) f) →
        ∀ M c, ¬ HaltsIn T' M (benc T11 sp (encC11 C w)) c))
    (hU0 : (rst T11 sp .h St.q0).val ∈ Spec.states (numT (numB k) T'))
    (hUA : ∀ a ∈ [num.sym Sy.s6, 0, num.sym Sy.s5, 1, 2] ++ [1, 2],
      a = 0 ∨ a ∈ Spec.symbols (numT (numB k) T'))
    (hUK : ∀ a ∈ 0 :: [1, 2], 7 * (sp.v St.q0 + 1) + a = 0 ∨
      7 * (sp.v St.q0 + 1) + a ∈ Spec.symbols (numT (numB k) T')) :
    Spec.IsUTMStrict (numT (numB k) T') :=
  ChainGen.isUTMStrict_of_body_ctsh
    ((BlockGen.encB_primrec _ _).comp₂ (encM_primrec _ _ _)) (readM_primrec _ _ _)
    (strictBody_block11 sp T' hsim hU0 hUA hUK)

end URTM.Univ.Base11_7
