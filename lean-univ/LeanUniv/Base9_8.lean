/-
  **Block conversions of URTM(9,8)** (results/symmerge-2026-10-05, records urtm9-8.k7.r46.m26 and urtm9-8.k6.r46.m28;
  2026-11-05, T28): the base data for the block-converted tables built from `T9`, the table of URTM(9,8)
  (`URTM.CTSH.U9_8.T9`, URTM(10,7) with case_y_1 and copy_n_3 merged and the symbols recoloured; `U9_8.lean`).
  Same role as `Base10_7` for URTM(10,7).

  The states `St` and pseudo-states `Ps` are those of (13,7); the symbols are the eight of `Sy8`, numbered by
  `U9_8.num` (`s0..s7 ↦ 0..7`), so the block numbering `numB` is `BlockGen.numB` with `n = 8` (a counter `ctr i s` is
  `8 (i + 1) + num s`). The encoder is Morita's written with the eight symbols (`encC9_eq`), the readout is that of
  (10,7): `MoritaGen2.readM2` counts the separators in both colours, ∗ (`s5`) and Y (`s3`), one Y too many in `halt`
  (`e = 1`). The final configurations are `finCfg9`: `(λ, m)` is `b · RA9(m) · $ · ϕ₁(rm)` in `null`, where `RA9(m)`
  holds `|C|` symbols ∗ or Y together (`U9_8.count_RA9`); `(Y v, 0)` is `b · RA(0) · Y · loN(rm) · $ · ϕ₁(v)` in
  `halt`, where `loN` writes N (`s4`) or T (`s7`).

  * `hlo`, `henc`, `hnullfin`, `hhaltfin`: the numbering of ϕ₁ and the initial and final configurations of (9,8) in the
    form used by `Base10_7.readM2_fin` (they restate, as standalone lemmas, what `U9_8.body_U` proves inline).
  * `sym_lt`, `numB`: the numbering of the block machines (`n = 8`).
  * `strictBody_block9_8`, `isUTMStrict_block9_8`: `BlockGen.strictBody_block` / `isUTMStrict_block` specialised to
    the base `T9` and the readout `readM2`, with the same hypotheses as `Base10_7.strictBody_block10_7` (with `8` in
    place of `7`).
-/
import LeanUniv.Base10_7
import LeanUniv.U9_8

namespace URTM.Univ.Base9_8
open URTM URTM.CTSH URTM.Gen.K13_7 URTM.Univ.KToSpec URTM.Univ.NumGen URTM.Univ.MoritaGen
  URTM.Univ.MoritaGen2
open URTM.KState (Tgt Cfg Machine HaltsIn KSym)
open URTM.KStateBlocks (BSpec benc rst)
open URTM.CTSH.U9_8 (Sy8 lo9 T9 RA9 RA9b RA9_length encC9 encC9_eq finCfg9 finList9 tapeList9 loN YNS lo_YNS)
open URTM.Univ.U9_8 (num hls hls3 hlsN5 hlsN3 YNS_count3 count_RA9)

theorem hlo : ∀ c, num.sym (lo9 c) = URTM.Univ.U10_8.loN c := by intro c; cases c <;> decide

/-- The initial configuration is Morita's, written with the eight symbols: `encC9_eq`. -/
theorem henc (C : CTSH) (w : List Ch) :
    encC9 C w = ⟨.go .q0, (((Sim.RA lo9 .s5 .s0 C 0).length + 2 : ℕ) : ℤ),
      Sim.tp .s0 (Sy8.s0 :: Sim.RA lo9 .s5 .s0 C 0 ++ Sy8.s6 :: w.map lo9)⟩ :=
  encC9_eq C w

/-- The final configuration for `(λ, m)`: pseudo-state `null` (`h0`), `|C|` separators ∗ or Y together on
    the tape (`count_RA9`; the words ϕ₁(rm) hold neither). -/
theorem hnullfin (C : CTSH) (mf : ℕ) (rm : List Ch) (hm : mf ≤ C.length) :
    ∃ (L : List Sy8) (p : ℕ), p ≤ L.length ∧
      finCfg9 C [] mf rm = ⟨.halt .h0, p, Sim.tp .s0 L⟩ ∧
      L.count .s5 + L.count .s3 = C.length := by
  refine ⟨finList9 C [] mf rm, (RA9b C mf).length + 2 + rm.length, ?_, ?_, ?_⟩
  · simp [finList9, tapeList9, RA9_length]; omega
  · simp [finCfg9]
  · have h : (RA9 C mf).count Sy8.s5 + (RA9 C mf).count Sy8.s3 = C.length :=
      (count_RA9 C mf).trans (count_RA lo9 Sy8.s5 Sy8.s0 hls (by decide) C hm)
    simp only [finList9, tapeList9, List.map_nil, List.append_nil, List.count_cons,
      List.count_append]
    rw [show (rm.map lo9).count Sy8.s5 = 0 from count_lo lo9 _ hls rm,
      show (rm.map lo9).count Sy8.s3 = 0 from count_lo lo9 _ hls3 rm]
    simp
    omega

/-- The final configuration for `(Y v, 0)`: pseudo-state `halt` (`h1`), the tape ends with
    `$ ϕ₁(v)` (the mark is `$`, `s6`); before it, `RA(0)` holds `|C|` separators ∗ and no Y, the mark Y
    after it is the one Y too many (`e = 1`), and the erased symbols `loN rm` are N or T, neither ∗ nor Y. -/
theorem hhaltfin (C : CTSH) (v rm : List Ch) :
    ∃ (A : List Sy8) (mk : Sy8) (p : ℕ), p ≤ (A ++ mk :: v.map lo9).length ∧
      finCfg9 C (.Y :: v) 0 rm = ⟨.halt .h1, p, Sim.tp .s0 (A ++ mk :: v.map lo9)⟩ ∧
      (A ++ [mk]).count .s5 + (A ++ [mk]).count .s3 - 1 = C.length ∧
      num.sym mk ≠ 0 ∧ num.sym mk ≠ 1 ∧ num.sym mk ≠ 2 := by
  refine ⟨Sy8.s0 :: RA9b C 0 ++ Sy8.s3 :: rm.map loN, Sy8.s6,
    (RA9b C 0).length, ?_, ?_, ?_, by decide, by decide, by decide⟩
  · simp; omega
  · simp [finCfg9, finList9]
  · have h := count_RA lo9 Sy8.s5 Sy8.s0 hls (by decide) C (Nat.zero_le _)
    have h3 : (RA9b C 0).count Sy8.s3 = 0 := by
      rw [RA9b, Sim.RA_zero, List.count_append]
      rw [YNS_count3 (Sim.Hi_mem lo_YNS (by simp [YNS]) C 0)]
      simp
    simp only [List.count_cons, List.count_append, List.count_nil]
    rw [show (RA9b C 0).count Sy8.s5 = C.length from h, h3,
      show (rm.map loN).count Sy8.s5 = 0 from count_lo loN _ hlsN5 rm,
      show (rm.map loN).count Sy8.s3 = 0 from count_lo loN _ hlsN3 rm]
    simp

theorem sym_lt (s : Sy8) : num.sym s < 8 := by cases s <;> decide

/-- The numbering of a block conversion of `T9` with `k` states (`BlockGen.numB` with `n = 8`). -/
def numB (k : ℕ) : Numbering (Fin k) Ps (KSym Sy8) :=
  BlockGen.numB num 8 sym_lt [.h0, .h1] (by intro p; cases p <;> decide)

/-- **Body form** of `isUTMStrict_block9_8`: the body of `IsUTMStrict` for a block conversion of
    `T9`, with the explicit encoder (Morita's with the eight symbols) and the two-colour readout `readM2` of
    (10,7). Same hypotheses as `Base10_7.strictBody_block10_7`, with `T9` in place of `T10` and `8` in place of `7`. -/
theorem strictBody_block9_8 {k : ℕ} (sp : BSpec St k) (T' : Machine (Fin k) Ps (KSym Sy8))
    (hsim : ∀ C w,
      (∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) → ∃ M rm, n ≤ M ∧
        HaltsIn T' M (benc T9 sp (encC9 C w)) (benc T9 sp (finCfg9 C vf mf rm))) ∧
      ((∀ n f, ¬ CHaltsIn C n (w, 0) f) →
        ∀ M c, ¬ HaltsIn T' M (benc T9 sp (encC9 C w)) c))
    (hU0 : (rst T9 sp .h St.q0).val ∈ Spec.states (numT (numB k) T'))
    (hUA : ∀ a ∈ [num.sym Sy8.s6, 0, num.sym Sy8.s5, 1, 2] ++ [1, 2],
      a = 0 ∨ a ∈ Spec.symbols (numT (numB k) T'))
    (hUK : ∀ a ∈ 0 :: [1, 2], 8 * (sp.v St.q0 + 1) + a = 0 ∨
      8 * (sp.v St.q0 + 1) + a ∈ Spec.symbols (numT (numB k) T')) :
    DropGen.StrictBody (numT (numB k) T')
      (ChainGen.cOf (fun C w => BlockGen.encB (rst T9 sp .h St.q0).val (8 * (sp.v St.q0 + 1))
        ((encM (num.st (.go St.q0)) (num.sym Sy8.s6) (num.sym Sy8.s5)) C w)))
      (GenDec.dOf (readM2 (k + [Ps.h0, Ps.h1].idxOf Ps.h1) (num.sym Sy8.s5) (num.sym Sy8.s3) 1)) :=
  BlockGen.strictBody_block num 8 sym_lt [.h0, .h1] _ T9 sp T' Sy8.s0 (by decide) St.q0
    encC9 finCfg9 (fun C => (((Sim.RA lo9 .s5 .s0 C 0).length + 2 : ℕ) : ℤ))
    (encM (num.st (.go St.q0)) (num.sym Sy8.s6) (num.sym Sy8.s5))
    (fun C w => by rw [henc]; exact encM_eq num lo9 .s5 .s0 (by decide) hlo .q0 .s6 C w)
    (fun C w => by rw [henc])
    (fun C w => (hsim C w).1) (fun C w => (hsim C w).2)
    (readM2 (k + [Ps.h0, Ps.h1].idxOf Ps.h1) (num.sym Sy8.s5) (num.sym Sy8.s3) 1)
    (fun _ _ _ h => readM2_toID _ _ _ _ (by decide) (by decide) h)
    (fun C vf mf rm hf => Base10_7.readM2_fin num lo9 .s5 .s3 .s0 .h0 .h1 1 hlo hls hls3
      (fun h => k + [Ps.h0, Ps.h1].idxOf h)
      (fun h => absurd (Nat.add_left_cancel h) (by decide)) finCfg9 hnullfin hhaltfin
      C vf mf rm hf)
    [num.sym Sy8.s6, 0, num.sym Sy8.s5, 1, 2] [1, 2]
    (fun C w => BlockGen.encM_left _ _ _ C w) (fun C w => BlockGen.encM_right _ _ _ C w)
    hU0 hUA hUK

/-- **A block conversion of `T9` (URTM(9,8)) that simulates every CTSH is a UTM in the strict
    sense of Morita Def. 7.1**, given three finite facts about its table. -/
theorem isUTMStrict_block9_8 {k : ℕ} (sp : BSpec St k) (T' : Machine (Fin k) Ps (KSym Sy8))
    (hsim : ∀ C w,
      (∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) → ∃ M rm, n ≤ M ∧
        HaltsIn T' M (benc T9 sp (encC9 C w)) (benc T9 sp (finCfg9 C vf mf rm))) ∧
      ((∀ n f, ¬ CHaltsIn C n (w, 0) f) →
        ∀ M c, ¬ HaltsIn T' M (benc T9 sp (encC9 C w)) c))
    (hU0 : (rst T9 sp .h St.q0).val ∈ Spec.states (numT (numB k) T'))
    (hUA : ∀ a ∈ [num.sym Sy8.s6, 0, num.sym Sy8.s5, 1, 2] ++ [1, 2],
      a = 0 ∨ a ∈ Spec.symbols (numT (numB k) T'))
    (hUK : ∀ a ∈ 0 :: [1, 2], 8 * (sp.v St.q0 + 1) + a = 0 ∨
      8 * (sp.v St.q0 + 1) + a ∈ Spec.symbols (numT (numB k) T')) :
    Spec.IsUTMStrict (numT (numB k) T') :=
  ChainGen.isUTMStrict_of_body_ctsh
    ((BlockGen.encB_primrec _ _).comp₂ (encM_primrec _ _ _)) (readM2_primrec _ _ _ _)
    (strictBody_block9_8 sp T' hsim hU0 hUA hUK)

end URTM.Univ.Base9_8
