/-
  **Block conversions of URTM(15,6)** (docs/24 P7b): the base data for (5,45), (7,32) and (9,27).

  * `henc`, `hnullfin`, `hhaltfin`: the initial and final configurations of (15,6) in the form
    used by `MoritaGen` (they restate, as standalone lemmas, what `U15_6.isUTMStrict_U`
    proves inline).
  * `isUTMStrict_block15`: `BlockGen.isUTMStrict_block` specialised to the base (15,6), with
    the base encoder `MoritaGen.encM` and the base readout `MoritaGen.readM` (pseudo-state
    `halt` numbered `k + 0`).
-/
import LeanUniv.BlockGen
import LeanUniv.U15_6

namespace URTM.Univ.Base15_6
open URTM URTM.CTSH URTM.Gen.K15_6 URTM.Univ.KToSpec URTM.Univ.NumGen URTM.Univ.MoritaGen
open URTM.KState (Tgt Cfg Machine HaltsIn KSym)
open URTM.KStateBlocks (BSpec benc rst)
open URTM.Univ.U10_8 (loN)
open URTM.CTSH.U15_6 (nm15 encC15 finCfg15)
open URTM.CTSH.U17_5 (Core)
open URTM.Univ.U15_6 (num lo15 hls)

theorem hlo : ∀ c, num.sym (lo15 c) = loN c := by intro c; cases c <;> decide

/-- The initial configuration is Morita's. -/
theorem henc (C : CTSH) (w : List Ch) :
    encC15 C w = ⟨.go .q0, (((Sim.RA lo15 .s3 .s0 C 0).length + 2 : ℕ) : ℤ),
      Sim.tp .s0 (Sy.s0 :: Sim.RA lo15 .s3 .s0 C 0 ++ Sy.s4 :: w.map lo15)⟩ := by
  simp [encC15, URTM.CTSH.U15_6.encC, URTM.CTSH.U15_6.rep, Core.rep, Core.tapeList, nm15,
    lo15]

/-- The final configuration for `(λ, m)`: pseudo-state `null`, `|C|` separators on the tape. -/
theorem hnullfin (C : CTSH) (mf : ℕ) (rm : List Ch) (hm : mf ≤ C.length) :
    ∃ (L : List Sy) (p : ℕ), p ≤ L.length ∧
      finCfg15 C [] mf rm = ⟨.halt .h1, p, Sim.tp .s0 L⟩ ∧ L.count .s3 = C.length := by
  refine ⟨Core.finList nm15.toCore C [] mf rm, (Core.RA nm15.toCore C mf).length + 1,
    ?_, ?_, ?_⟩
  · simp [Core.finList, Core.tapeList]
  · simp [finCfg15, URTM.CTSH.U15_6.finCfg, Core.finCfg, nm15]
  · have h := count_RA lo15 Sy.s3 Sy.s0 hls (by decide) C hm
    simp only [Core.finList, Core.tapeList, List.map_nil, List.append_nil, List.count_cons,
      List.count_append, List.count_nil]
    rw [show (Core.RA nm15.toCore C mf).count Sy.s3 = C.length from h,
      show (rm.map (Core.lo nm15.toCore)).count Sy.s3 = 0 from count_lo lo15 _ hls rm]
    simp [nm15]

/-- The final configuration for `(Y v, 0)`: pseudo-state `halt`, the tape ends with `$ ϕ₁(v)`. -/
theorem hhaltfin (C : CTSH) (v rm : List Ch) :
    ∃ (A : List Sy) (mk : Sy) (p : ℕ), p ≤ (A ++ mk :: v.map lo15).length ∧
      finCfg15 C (.Y :: v) 0 rm = ⟨.halt .h0, p, Sim.tp .s0 (A ++ mk :: v.map lo15)⟩ ∧
      (A ++ [mk]).count .s3 - 0 = C.length ∧ num.sym mk ≠ 0 ∧ num.sym mk ≠ 1 ∧
      num.sym mk ≠ 2 := by
  refine ⟨Sy.s0 :: Core.RA nm15.toCore C 0 ++ Sy.s0 :: rm.map lo15, Sy.s4,
    (Core.RA nm15.toCore C 0).length, ?_, ?_, ?_, by decide, by decide, by decide⟩
  · simp; omega
  · simp [finCfg15, URTM.CTSH.U15_6.finCfg, Core.finCfg, Core.finList, nm15, lo15]
  · have h := count_RA lo15 Sy.s3 Sy.s0 hls (by decide) C (Nat.zero_le _)
    simp only [List.count_cons, List.count_append, List.count_nil]
    rw [show (Core.RA nm15.toCore C 0).count Sy.s3 = C.length from h,
      show (rm.map lo15).count Sy.s3 = 0 from count_lo lo15 _ hls rm]
    simp

theorem sym_lt (s : Sy) : num.sym s < 6 := by cases s <;> decide

/-- The numbering of a block conversion of (15,6) with `k` states. -/
def numB (k : ℕ) : Numbering (Fin k) Ps (KSym Sy) :=
  BlockGen.numB num 6 sym_lt [.h0, .h1] (by intro p; cases p <;> decide)

/-- **Body form** (docs/26) of `isUTMStrict_block15`: the body of `IsUTMStrict` for a block conversion of (15,6),
    with the explicit encoder and decoder. Same hypotheses. -/
theorem strictBody_block15 {k : ℕ} (sp : BSpec St k) (T' : Machine (Fin k) Ps (KSym Sy))
    (hsim : ∀ C w,
      (∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) → ∃ M rm, n ≤ M ∧
        HaltsIn T' M (benc T sp (encC15 C w)) (benc T sp (finCfg15 C vf mf rm))) ∧
      ((∀ n f, ¬ CHaltsIn C n (w, 0) f) →
        ∀ M c, ¬ HaltsIn T' M (benc T sp (encC15 C w)) c))
    (hU0 : (rst T sp .h St.q0).val ∈ Spec.states (numT (numB k) T'))
    (hUA : ∀ a ∈ [num.sym Sy.s4, 0, num.sym Sy.s3, 1, 2] ++ [1, 2],
      a = 0 ∨ a ∈ Spec.symbols (numT (numB k) T'))
    (hUK : ∀ a ∈ 0 :: [1, 2], 6 * (sp.v St.q0 + 1) + a = 0 ∨
      6 * (sp.v St.q0 + 1) + a ∈ Spec.symbols (numT (numB k) T')) :
    DropGen.StrictBody (numT (numB k) T')
      (ChainGen.cOf (fun C w => BlockGen.encB (rst T sp .h St.q0).val (6 * (sp.v St.q0 + 1))
        ((encM (num.st (.go St.q0)) (num.sym Sy.s4) (num.sym Sy.s3)) C w)))
      (GenDec.dOf (readM (k + [Ps.h0, Ps.h1].idxOf Ps.h0) (num.sym Sy.s3) 0)) :=
  BlockGen.strictBody_block num 6 sym_lt [.h0, .h1] _ T sp T' Sy.s0 (by decide) St.q0
    encC15 finCfg15 (fun C => (((Sim.RA lo15 .s3 .s0 C 0).length + 2 : ℕ) : ℤ))
    (encM (num.st (.go St.q0)) (num.sym Sy.s4) (num.sym Sy.s3))
    (fun C w => by rw [henc]; exact encM_eq num lo15 .s3 .s0 (by decide) hlo .q0 .s4 C w)
    (fun C w => by rw [henc])
    (fun C w => (hsim C w).1) (fun C w => (hsim C w).2)
    (readM (k + [Ps.h0, Ps.h1].idxOf Ps.h0) (num.sym Sy.s3) 0)
    (fun _ _ _ h => readM_toID _ _ _ (by decide) h)
    (fun C vf mf rm hf => BlockGen.readM_fin num lo15 .s3 .s0 .h1 .h0 0 hlo hls
      (fun h => k + [Ps.h0, Ps.h1].idxOf h)
      (fun h => absurd (Nat.add_left_cancel h) (by decide)) finCfg15 hnullfin hhaltfin
      C vf mf rm hf)
    [num.sym Sy.s4, 0, num.sym Sy.s3, 1, 2] [1, 2]
    (fun C w => BlockGen.encM_left _ _ _ C w) (fun C w => BlockGen.encM_right _ _ _ C w)
    hU0 hUA hUK

/-- **A block conversion of (15,6) that simulates every CTSH is a UTM in the strict sense of
    Morita Def. 7.1**, given three finite facts about its table. -/
theorem isUTMStrict_block15 {k : ℕ} (sp : BSpec St k) (T' : Machine (Fin k) Ps (KSym Sy))
    (hsim : ∀ C w,
      (∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) → ∃ M rm, n ≤ M ∧
        HaltsIn T' M (benc T sp (encC15 C w)) (benc T sp (finCfg15 C vf mf rm))) ∧
      ((∀ n f, ¬ CHaltsIn C n (w, 0) f) →
        ∀ M c, ¬ HaltsIn T' M (benc T sp (encC15 C w)) c))
    (hU0 : (rst T sp .h St.q0).val ∈ Spec.states (numT (numB k) T'))
    (hUA : ∀ a ∈ [num.sym Sy.s4, 0, num.sym Sy.s3, 1, 2] ++ [1, 2],
      a = 0 ∨ a ∈ Spec.symbols (numT (numB k) T'))
    (hUK : ∀ a ∈ 0 :: [1, 2], 6 * (sp.v St.q0 + 1) + a = 0 ∨
      6 * (sp.v St.q0 + 1) + a ∈ Spec.symbols (numT (numB k) T')) :
    Spec.IsUTMStrict (numT (numB k) T') :=
  ChainGen.isUTMStrict_of_body_ctsh
    ((BlockGen.encB_primrec _ _).comp₂ (encM_primrec _ _ _)) (readM_primrec _ _ _)
    (strictBody_block15 sp T' hsim hU0 hUA hUK)

end URTM.Univ.Base15_6
