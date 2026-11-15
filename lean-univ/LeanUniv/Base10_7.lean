/-
  **Block conversions of URTM(10,7)** (results/symmerge-2026-10-05, records urtm10-7.k6.r38.m29, urtm10-7.k4.r43.m38
  and urtm10-7.k5.r43.m36; 2026-11-04, T25): the base data for the block-converted tables built from `T10`, the
  table of URTM(10,7) (`URTM.CTSH.U10_7.T10 = (T11.flatMap chg).eraseDups`, URTM(11,7) with cycle_end merged into the
  merged state of case_y_2 / copy_y_2 and the symbols recoloured; `U10_7.lean`). Same role as `Base11_7` for
  URTM(11,7) and `Base13_7` for Morita's (13,7).

  The types `St`, `Sy`, `Ps`, the numbering (`Base13_7.numB`) and the encoder (`encM`) are those of (13,7): the
  initial configuration `encC10` is Morita's (`encC10_eq`). The readout is that of `U10_7`, not that of (13,7):
  `MoritaGen2.readM2` counts the separators in both colours, ∗ (`s5`) and Y (`s3`), one Y too many in `halt`
  (`e = 1`). The final configurations are `finCfg10`: `(λ, m)` is `b · RA10(m) · $ · ϕ₁(rm)` in `null`, where
  `RA10(m)` holds `|C|` symbols ∗ or Y together (`U10_7.count_RA10`); `(Y v, 0)` is
  `b · RA(0) · Y · loN(rm) · $ · ϕ₁(v)` in `halt`.

  * `readM2_fin`: `BlockGen.readM_fin` for the two-colour readout (the final shapes with the two counts, for an
    arbitrary numbering of the two pseudo-states). Same proof with the second count.
  * `henc`, `hnullfin`, `hhaltfin`: the initial and final configurations of (10,7) in the form used by
    `readM2_fin` (they restate, as standalone lemmas, what `U10_7.body_U` proves inline).
  * `numB`: the numbering of (13,7) (`Base13_7.numB`), under the name the generated modules expect.
  * `strictBody_block10_7`, `isUTMStrict_block10_7`: `BlockGen.strictBody_block` / `isUTMStrict_block`
    specialised to the base `T10` and the readout `readM2`, with the same hypotheses as
    `Base11_7.strictBody_block11`.
-/
import LeanUniv.Base13_7
import LeanUniv.U10_7

namespace URTM.Univ.Base10_7
open URTM URTM.CTSH URTM.Gen.K13_7 URTM.Univ.KToSpec URTM.Univ.NumGen URTM.Univ.MoritaGen
  URTM.Univ.MoritaGen2
open URTM.KState (Tgt Cfg Machine HaltsIn KSym)
open URTM.KStateBlocks (BSpec benc rst)
open URTM.CTSH.U13_7 (nm13)
open URTM.CTSH.U10_7 (T10 encC10 encC10_eq finCfg10 finList10 tapeList10 RA10 RA10_length)
open URTM.Univ.U13_7 (num lo13 hls)
open URTM.Univ.U10_7 (count_RA10 hls3 hlsN5 hlsN3 YNS_count3)

/-! ### The final shapes read by the two-colour readout, for any numbering of the pseudo-states -/

/-- `BlockGen.readM_fin` for `MoritaGen2.readM2`: the final shapes of the one-cell-per-letter family with the
    separators in two colours `st`, `st'` (as in `strictBody_morita2`) are read by
    `readM2 (stn hhalt) (N.sym st) (N.sym st') e` when the pseudo-states are numbered by `stn`. -/
theorem readM2_fin {Q P S : Type} [DecidableEq S] (N : Numbering Q P S) (lo : Ch → S)
    (st st' bk : S) (hnull hhalt : P) (e : ℕ) (hlo : ∀ c, N.sym (lo c) = URTM.Univ.U10_8.loN c)
    (hls : ∀ c, lo c ≠ st) (hls' : ∀ c, lo c ≠ st') (stn : P → ℕ) (hnh : stn hnull ≠ stn hhalt)
    (finC : CTSH → List Ch → ℕ → List Ch → Cfg Q P S)
    (hnullfin : ∀ C mf rm, mf ≤ C.length → ∃ (L : List S) (p : ℕ), p ≤ L.length ∧
      finC C [] mf rm = ⟨.halt hnull, p, Sim.tp bk L⟩ ∧ L.count st + L.count st' = C.length)
    (hhaltfin : ∀ C v rm, ∃ (A : List S) (mk : S) (p : ℕ), p ≤ (A ++ mk :: v.map lo).length ∧
      finC C (.Y :: v) 0 rm = ⟨.halt hhalt, p, Sim.tp bk (A ++ mk :: v.map lo)⟩ ∧
      (A ++ [mk]).count st + (A ++ [mk]).count st' - e = C.length ∧
      N.sym mk ≠ 0 ∧ N.sym mk ≠ 1 ∧ N.sym mk ≠ 2)
    (C : CTSH) (vf : List Ch) (mf : ℕ) (rm : List Ch) (hf : Halting C (vf, mf)) :
    ∃ (h : P) (L : List S) (p : ℕ), p ≤ L.length ∧
      finC C vf mf rm = ⟨.halt h, p, Sim.tp bk L⟩ ∧
      readM2 (stn hhalt) (N.sym st) (N.sym st') e (window (stn h) (L.map N.sym) p) =
        some (C.length, vf.map URTM.Univ.U10_8.loN) := by
  obtain ⟨hk, hv | hv⟩ := hf
  · obtain ⟨v, hv1, hv2⟩ := hv
    simp only at hv1 hv2
    subst hv1 hv2
    obtain ⟨A, mk, p, hp, hfin, hc, hm0, hm1, hm2⟩ := hhaltfin C v rm
    refine ⟨hhalt, _, p, hp, hfin, ?_⟩
    rw [List.map_append, List.map_cons, map_lo N lo hlo, readM2_halt _ _ _ _ _ _ hm0 hm1 hm2]
    have hcnt : (A.map N.sym ++ N.sym mk :: v.map URTM.Univ.U10_8.loN).count (N.sym st) =
        (A ++ [mk]).count st := by
      rw [← map_lo N lo hlo, ← List.map_cons, ← List.map_append,
        List.count_map_of_injective _ _ N.sym_inj]
      simp [List.count_append, List.count_cons, count_lo lo st hls]
    have hcnt' : (A.map N.sym ++ N.sym mk :: v.map URTM.Univ.U10_8.loN).count (N.sym st') =
        (A ++ [mk]).count st' := by
      rw [← map_lo N lo hlo, ← List.map_cons, ← List.map_append,
        List.count_map_of_injective _ _ N.sym_inj]
      simp [List.count_append, List.count_cons, count_lo lo st' hls']
    rw [hcnt, hcnt', hc]
  · simp only at hv
    subst hv
    obtain ⟨L, p, hp, hfin, hc⟩ := hnullfin C mf rm (by simp [CTSH.k] at hk; omega)
    refine ⟨hnull, L, p, hp, hfin, ?_⟩
    rw [readM2_null _ _ _ _ _ hnh, List.count_map_of_injective _ _ N.sym_inj,
      List.count_map_of_injective _ _ N.sym_inj, hc]
    rfl

/-! ### The base `T10` -/

/-- The numbering of a block conversion of `T10` with `k` states: that of (13,7) (`Base13_7.numB`;
    the types `St`, `Ps`, `Sy` are the same). -/
abbrev numB (k : ℕ) : Numbering (Fin k) Ps (KSym Sy) := Base13_7.numB k

/-- The initial configuration is Morita's (that of (13,7)): `encC10_eq`. -/
theorem henc (C : CTSH) (w : List Ch) :
    encC10 C w = ⟨.go .q0, (((Sim.RA lo13 .s5 .s0 C 0).length + 2 : ℕ) : ℤ),
      Sim.tp .s0 (Sy.s0 :: Sim.RA lo13 .s5 .s0 C 0 ++ Sy.s6 :: w.map lo13)⟩ := by
  rw [encC10_eq]
  simp [URTM.CTSH.U13_7.encC, URTM.CTSH.U13_7.rep, URTM.CTSH.U13_7.tapeList, nm13, lo13]

/-- The final configuration for `(λ, m)`: pseudo-state `null` (`h0`), `|C|` separators ∗ or Y together on
    the tape (`count_RA10`; the words ϕ₁(rm) hold neither). -/
theorem hnullfin (C : CTSH) (mf : ℕ) (rm : List Ch) (hm : mf ≤ C.length) :
    ∃ (L : List Sy) (p : ℕ), p ≤ L.length ∧
      finCfg10 C [] mf rm = ⟨.halt .h0, p, Sim.tp .s0 L⟩ ∧
      L.count .s5 + L.count .s3 = C.length := by
  refine ⟨finList10 C [] mf rm, (URTM.CTSH.U13_7.RA nm13 C mf).length + 2 + rm.length, ?_, ?_, ?_⟩
  · simp [finList10, tapeList10, RA10_length]; omega
  · simp [finCfg10, nm13]
  · have h : (RA10 C mf).count Sy.s5 + (RA10 C mf).count Sy.s3 = C.length :=
      (count_RA10 C mf).trans (count_RA lo13 Sy.s5 Sy.s0 hls (by decide) C hm)
    simp only [finList10, tapeList10, List.map_nil, List.append_nil, List.count_cons,
      List.count_append]
    rw [show (rm.map (URTM.CTSH.U13_7.lo nm13)).count Sy.s5 = 0 from count_lo lo13 _ hls rm,
      show (rm.map (URTM.CTSH.U13_7.lo nm13)).count Sy.s3 = 0 from count_lo lo13 _ hls3 rm]
    simp [nm13]
    omega

/-- The final configuration for `(Y v, 0)`: pseudo-state `halt` (`h1`), the tape ends with
    `$ ϕ₁(v)` (the mark is `$`, `s6`); before it, `RA(0)` holds `|C|` separators ∗ and no Y, the mark Y
    after it is the one Y too many (`e = 1`), and the erased symbols `loN rm` are N or n, neither ∗ nor Y. -/
theorem hhaltfin (C : CTSH) (v rm : List Ch) :
    ∃ (A : List Sy) (mk : Sy) (p : ℕ), p ≤ (A ++ mk :: v.map lo13).length ∧
      finCfg10 C (.Y :: v) 0 rm = ⟨.halt .h1, p, Sim.tp .s0 (A ++ mk :: v.map lo13)⟩ ∧
      (A ++ [mk]).count .s5 + (A ++ [mk]).count .s3 - 1 = C.length ∧
      num.sym mk ≠ 0 ∧ num.sym mk ≠ 1 ∧ num.sym mk ≠ 2 := by
  refine ⟨Sy.s0 :: URTM.CTSH.U13_7.RA nm13 C 0 ++ Sy.s3 :: rm.map URTM.CTSH.U11_7.loN, Sy.s6,
    (URTM.CTSH.U13_7.RA nm13 C 0).length, ?_, ?_, ?_, by decide, by decide, by decide⟩
  · simp; omega
  · simp [finCfg10, finList10, nm13, lo13]
  · have h := count_RA lo13 Sy.s5 Sy.s0 hls (by decide) C (Nat.zero_le _)
    have h3 : (URTM.CTSH.U13_7.RA nm13 C 0).count Sy.s3 = 0 := by
      rw [URTM.CTSH.U13_7.RA, Sim.RA_zero, List.count_append]
      rw [YNS_count3 (Sim.Hi_mem URTM.CTSH.U13_7.lo_YNS (by simp [URTM.CTSH.U13_7.YNS]) C 0)]
      simp [nm13]
    simp only [List.count_cons, List.count_append, List.count_nil]
    rw [show (URTM.CTSH.U13_7.RA nm13 C 0).count Sy.s5 = C.length from h, h3,
      show (rm.map URTM.CTSH.U11_7.loN).count Sy.s5 = 0 from
        count_lo URTM.CTSH.U11_7.loN _ hlsN5 rm,
      show (rm.map URTM.CTSH.U11_7.loN).count Sy.s3 = 0 from
        count_lo URTM.CTSH.U11_7.loN _ hlsN3 rm]
    simp

/-- **Body form** of `isUTMStrict_block10_7`: the body of `IsUTMStrict` for a block conversion of
    `T10`, with the explicit encoder of (13,7) and the two-colour readout `readM2` of (10,7). Same
    hypotheses as `Base11_7.strictBody_block11`, with `T10` in place of `T11`. -/
theorem strictBody_block10_7 {k : ℕ} (sp : BSpec St k) (T' : Machine (Fin k) Ps (KSym Sy))
    (hsim : ∀ C w,
      (∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) → ∃ M rm, n ≤ M ∧
        HaltsIn T' M (benc T10 sp (encC10 C w)) (benc T10 sp (finCfg10 C vf mf rm))) ∧
      ((∀ n f, ¬ CHaltsIn C n (w, 0) f) →
        ∀ M c, ¬ HaltsIn T' M (benc T10 sp (encC10 C w)) c))
    (hU0 : (rst T10 sp .h St.q0).val ∈ Spec.states (numT (numB k) T'))
    (hUA : ∀ a ∈ [num.sym Sy.s6, 0, num.sym Sy.s5, 1, 2] ++ [1, 2],
      a = 0 ∨ a ∈ Spec.symbols (numT (numB k) T'))
    (hUK : ∀ a ∈ 0 :: [1, 2], 7 * (sp.v St.q0 + 1) + a = 0 ∨
      7 * (sp.v St.q0 + 1) + a ∈ Spec.symbols (numT (numB k) T')) :
    DropGen.StrictBody (numT (numB k) T')
      (ChainGen.cOf (fun C w => BlockGen.encB (rst T10 sp .h St.q0).val (7 * (sp.v St.q0 + 1))
        ((encM (num.st (.go St.q0)) (num.sym Sy.s6) (num.sym Sy.s5)) C w)))
      (GenDec.dOf (readM2 (k + [Ps.h0, Ps.h1].idxOf Ps.h1) (num.sym Sy.s5) (num.sym Sy.s3) 1)) :=
  BlockGen.strictBody_block num 7 Base13_7.sym_lt [.h0, .h1] _ T10 sp T' Sy.s0 (by decide) St.q0
    encC10 finCfg10 (fun C => (((Sim.RA lo13 .s5 .s0 C 0).length + 2 : ℕ) : ℤ))
    (encM (num.st (.go St.q0)) (num.sym Sy.s6) (num.sym Sy.s5))
    (fun C w => by rw [henc]; exact encM_eq num lo13 .s5 .s0 (by decide) Base13_7.hlo .q0 .s6 C w)
    (fun C w => by rw [henc])
    (fun C w => (hsim C w).1) (fun C w => (hsim C w).2)
    (readM2 (k + [Ps.h0, Ps.h1].idxOf Ps.h1) (num.sym Sy.s5) (num.sym Sy.s3) 1)
    (fun _ _ _ h => readM2_toID _ _ _ _ (by decide) (by decide) h)
    (fun C vf mf rm hf => readM2_fin num lo13 .s5 .s3 .s0 .h0 .h1 1 Base13_7.hlo hls hls3
      (fun h => k + [Ps.h0, Ps.h1].idxOf h)
      (fun h => absurd (Nat.add_left_cancel h) (by decide)) finCfg10 hnullfin hhaltfin
      C vf mf rm hf)
    [num.sym Sy.s6, 0, num.sym Sy.s5, 1, 2] [1, 2]
    (fun C w => BlockGen.encM_left _ _ _ C w) (fun C w => BlockGen.encM_right _ _ _ C w)
    hU0 hUA hUK

/-- **A block conversion of `T10` (URTM(10,7)) that simulates every CTSH is a UTM in the strict
    sense of Morita Def. 7.1**, given three finite facts about its table. -/
theorem isUTMStrict_block10_7 {k : ℕ} (sp : BSpec St k) (T' : Machine (Fin k) Ps (KSym Sy))
    (hsim : ∀ C w,
      (∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) → ∃ M rm, n ≤ M ∧
        HaltsIn T' M (benc T10 sp (encC10 C w)) (benc T10 sp (finCfg10 C vf mf rm))) ∧
      ((∀ n f, ¬ CHaltsIn C n (w, 0) f) →
        ∀ M c, ¬ HaltsIn T' M (benc T10 sp (encC10 C w)) c))
    (hU0 : (rst T10 sp .h St.q0).val ∈ Spec.states (numT (numB k) T'))
    (hUA : ∀ a ∈ [num.sym Sy.s6, 0, num.sym Sy.s5, 1, 2] ++ [1, 2],
      a = 0 ∨ a ∈ Spec.symbols (numT (numB k) T'))
    (hUK : ∀ a ∈ 0 :: [1, 2], 7 * (sp.v St.q0 + 1) + a = 0 ∨
      7 * (sp.v St.q0 + 1) + a ∈ Spec.symbols (numT (numB k) T')) :
    Spec.IsUTMStrict (numT (numB k) T') :=
  ChainGen.isUTMStrict_of_body_ctsh
    ((BlockGen.encB_primrec _ _).comp₂ (encM_primrec _ _ _)) (readM2_primrec _ _ _ _)
    (strictBody_block10_7 sp T' hsim hU0 hUA hUK)

end URTM.Univ.Base10_7
