/-
  **The halting IDs of the block-converted machines** (results/symmerge-2026-10-04): the strong
  form `SymMerge.IsUTMStrictHalt` of Morita Def. 7.1 for the block conversions of (10,8), (15,6)
  and (17,5), with `F = List.range n` (`n` = the number of symbols of the base machine).

  `IsUTMStrict` for these machines (`BlockGen.strictBody_block`) is not enough for merging
  symbols: it does not say that the halting ID is in a pseudo-state. This file takes that fact
  from the same CTSH theorem of the machine (no new simulation argument):

  * `halt_shape`: if the Spec table `numT (numB …) T'` halts from the image of `benc T sp c₀`, the
    CTSH halts (the non-halting half of the CTSH theorem, contraposed), so `T'` halts at
    `benc T sp (fin vf mf rm)` (its halting half), and since the Spec table is deterministic this
    is the halting ID. Its state is a pseudo-state `.halt h` (numbered `k + …`, not a source state,
    which are `< k`), and `benc` writes plain symbols everywhere in a pseudo-state, numbered
    `N.sym s < n`.
  * `isUTMStrictHalt_block`: the strong form from the body `StrictBody` of `strictBody_block`.
  * `isUTMStrictHalt_block10` / `13` / `15` / `17`: the same for the four bases, from the hypotheses
    of `Base10_8.isUTMStrict_block10` (resp. 13, 15, 17) and the determinism of the table.
-/
import LeanUniv.Base10_8
import LeanUniv.Base13_7
import LeanUniv.Base15_6
import LeanUniv.Base17_5
import LeanUniv.SymMerge

namespace URTM.Univ.BlockHalt

set_option linter.unusedSectionVars false

open URTM URTM.CTSH URTM.Univ.KToSpec URTM.Univ.NumGen Relation
open URTM.KState (Tgt Cfg Machine HaltsIn KSym)
open URTM.KStateBlocks (BSpec benc rst)

/-- Halting IDs of a deterministic Spec table are unique. -/
theorem haltsAt_unique_spec {U : List Quint} (hdet : Spec.Deterministic U) {ι γ₁ γ₂ : Spec.ID}
    (h₁ : Spec.HaltsAt U ι γ₁) (h₂ : Spec.HaltsAt U ι γ₂) : γ₁ = γ₂ :=
  URTM.Univ.haltsAt_unique (r := Spec.Step U) (halt := Spec.Halted U)
    (fun _ _ _ => SymMerge.step_det hdet)
    (fun _ _ hy ⟨r, hr, ha, _⟩ => hy r hr ha) h₁ h₂

section Typed
variable {Q P S : Type} [DecidableEq Q] [DecidableEq P] [DecidableEq S] {k : ℕ}
  (N : Numbering Q P S) (n : ℕ) (hn : ∀ s, N.sym s < n) (ps : List P) (hp : ∀ p, p ∈ ps)
  (T : Machine Q P S) (sp : BSpec Q k)

/-- **The halting ID of a block-converted machine** reached from the image of `benc T sp c₀` is
    in a pseudo-state and holds only numbers `< n`, given the CTSH theorem of `T'` from `c₀` and
    that the final configurations of the base machine are in pseudo-states. -/
theorem halt_shape (T' : Machine (Fin k) P (KSym S)) (C : CTSH) (w : List Ch) (c₀ : Cfg Q P S)
    (fin : List Ch → ℕ → List Ch → Cfg Q P S) (δ : ℤ)
    (hdet : Spec.Deterministic (numT (BlockGen.numB N n hn ps hp) T'))
    (hsimF : ∀ m vf mf, CHaltsIn C m (w, 0) (vf, mf) →
      ∃ M rm, m ≤ M ∧ HaltsIn T' M (benc T sp c₀) (benc T sp (fin vf mf rm)))
    (hsimN : (∀ m f, ¬ CHaltsIn C m (w, 0) f) → ∀ M c, ¬ HaltsIn T' M (benc T sp c₀) c)
    (hfst : ∀ vf mf rm, Halting C (vf, mf) → ∃ h, (fin vf mf rm).st = .halt h)
    (γ : Spec.ID)
    (hγ : Spec.HaltsAt (numT (BlockGen.numB N n hn ps hp) T')
      (numCfg (BlockGen.numB N n hn ps hp) δ (benc T sp c₀)) γ) :
    γ.st ∉ (numT (BlockGen.numB N n hn ps hp) T').map Quint.p ∧ ∀ x, γ.tape x ∈ List.range n := by
  -- the CTSH halts, since `T'` does
  obtain ⟨m, ⟨vf, mf⟩, hf⟩ : ∃ m f, CHaltsIn C m (w, 0) f := by
    by_contra hne
    obtain ⟨M, c', h', -⟩ := (haltsAt_numCfg_iff T' δ _ γ).mp hγ
    exact hsimN (fun m f hf => hne ⟨m, f, hf⟩) M c' h'
  -- so `T'` halts at the image of a final configuration, which is the halting ID
  obtain ⟨M, rm, -, hM⟩ := hsimF m vf mf hf
  have h0 : Spec.HaltsAt (numT (BlockGen.numB N n hn ps hp) T')
      (numCfg (BlockGen.numB N n hn ps hp) δ (benc T sp c₀))
      (numCfg (BlockGen.numB N n hn ps hp) δ (benc T sp (fin vf mf rm))) :=
    (haltsAt_numCfg_iff T' δ _ _).mpr ⟨M, _, hM, rfl⟩
  rw [haltsAt_unique_spec hdet hγ h0]
  obtain ⟨h, hh⟩ := hfst vf mf rm hf.2
  generalize fin vf mf rm = e at hh ⊢
  obtain ⟨st, pos, tape⟩ := e
  obtain rfl : st = .halt h := hh
  refine ⟨fun hmem => ?_, fun x => List.mem_range.mpr (hn _)⟩
  obtain ⟨r, hr, hrp⟩ := List.mem_map.mp hmem
  obtain ⟨r₀, -, rfl⟩ := List.mem_map.mp hr
  have hlt := r₀.p.isLt
  simp only [numRule, numCfg, benc, BlockGen.numB, BlockGen.stB] at hrp
  omega

/-- **The strong form of Def. 7.1 for a block-converted machine**, from the body of
    `IsUTMStrict` (`BlockGen.strictBody_block`) and the determinism of the table. -/
theorem isUTMStrictHalt_block (T' : Machine (Fin k) P (KSym S)) (q0 : Q)
    (encC : CTSH → List Ch → Cfg Q P S) (finC : CTSH → List Ch → ℕ → List Ch → Cfg Q P S)
    (δ : CTSH → ℤ) (enc0 : CTSH → List Ch → Spec.Code) (henc0 : Primrec₂ enc0)
    (hencEq : ∀ C w, Spec.toID 0 (enc0 C w) = numCfg N (δ C) (encC C w))
    (hq0 : ∀ C w, (encC C w).st = .go q0)
    (hsimF : ∀ C w m vf mf, CHaltsIn C m (w, 0) (vf, mf) →
      ∃ M rm, m ≤ M ∧ HaltsIn T' M (benc T sp (encC C w)) (benc T sp (finC C vf mf rm)))
    (hsimN : ∀ C w, (∀ m f, ¬ CHaltsIn C m (w, 0) f) →
      ∀ M c, ¬ HaltsIn T' M (benc T sp (encC C w)) c)
    (hfst : ∀ C vf mf rm, Halting C (vf, mf) → ∃ h, (finC C vf mf rm).st = .halt h)
    (readN : Spec.Code → Option (ℕ × List ℕ)) (hread : Primrec readN)
    (hdet : Spec.Deterministic (numT (BlockGen.numB N n hn ps hp) T'))
    (hbody : DropGen.StrictBody (numT (BlockGen.numB N n hn ps hp) T')
      (ChainGen.cOf fun C w => BlockGen.encB (rst T sp .h q0).val (n * (sp.v q0 + 1)) (enc0 C w))
      (GenDec.dOf readN)) :
    SymMerge.IsUTMStrictHalt (numT (BlockGen.numB N n hn ps hp) T') (List.range n) :=
  SymMerge.isUTMStrictHalt_of_body
    (ChainGen.cOf_computable ((BlockGen.encB_primrec _ _).comp₂ henc0))
    (GenDec.dOf_computable hread) hbody fun _ _ _ γ hγ => by
      simp only [ChainGen.cOf] at hγ
      rw [BlockGen.encB_eq N n hn ps hp T sp (δ _) (encC _ _) q0 (hq0 _ _) _ (hencEq _ _)] at hγ
      exact halt_shape N n hn ps hp T sp T' _ _ (encC _ _) (finC _) (δ _) hdet (hsimF _ _)
        (hsimN _ _) (hfst _) γ hγ

end Typed

/-! ### The three bases -/

section B10
open URTM.Gen.K10_8
open URTM.Univ.U10_8 (num10_8 encList)

/-- **Block conversions of (10,8)**: the strong form, from the hypotheses of
    `Base10_8.isUTMStrict_block10` and the determinism of the table. -/
theorem isUTMStrictHalt_block10 {k : ℕ} (sp : BSpec St k) (T' : Machine (Fin k) Ps (KSym Sy))
    (hsim : ∀ C w,
      (∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) → ∃ M rm, n ≤ M ∧
        HaltsIn T' M (benc T sp (URTM.CTSH.U10_8.encC C w))
          (benc T sp (URTM.CTSH.U10_8.finCfg C vf mf rm))) ∧
      ((∀ n f, ¬ CHaltsIn C n (w, 0) f) →
        ∀ M c, ¬ HaltsIn T' M (benc T sp (URTM.CTSH.U10_8.encC C w)) c))
    (hdet : Spec.Deterministic (numT (Base10_8.numB k) T'))
    (hU0 : (rst T sp .h St.q0).val ∈ Spec.states (numT (Base10_8.numB k) T'))
    (hUA : ∀ a ∈ [7, 0, 6, 1, 2] ++ [1, 2], a = 0 ∨ a ∈ Spec.symbols (numT (Base10_8.numB k) T'))
    (hUK : ∀ a ∈ 0 :: [1, 2], 8 * (sp.v St.q0 + 1) + a = 0 ∨
      8 * (sp.v St.q0 + 1) + a ∈ Spec.symbols (numT (Base10_8.numB k) T')) :
    SymMerge.IsUTMStrictHalt (numT (Base10_8.numB k) T') (List.range 8) :=
  isUTMStrictHalt_block num10_8 8 Base10_8.syN_lt [.h0, .h1] (by intro p; cases p <;> decide) T sp
    T' St.q0 URTM.CTSH.U10_8.encC URTM.CTSH.U10_8.finCfg URTM.Univ.U10_8.δ encList
    ComputableEnc.encList_primrec URTM.Univ.U10_8.encList_eq (fun _ _ => rfl)
    (fun C w => (hsim C w).1) (fun C w => (hsim C w).2)
    (fun C vf mf rm hf => by
      obtain ⟨h, _, _, _, he, _⟩ := Base10_8.hfin k [.h0, .h1] C vf mf rm hf
      exact ⟨h, by rw [he]⟩)
    Base10_8.readN Base10_8.readN_primrec hdet (Base10_8.strictBody_block10 sp T' hsim hU0 hUA hUK)

end B10

section B13
open URTM.Gen.K13_7 URTM.Univ.MoritaGen
open URTM.CTSH.U13_7 (nm13 encC13 finCfg13)
open URTM.Univ.U13_7 (num lo13 hls)

/-- **Block conversions of (13,7)**: the strong form, from the hypotheses of
    `Base13_7.isUTMStrict_block13` and the determinism of the table. The pseudo-states of (13,7)
    are `h0 = null`, `h1 = halt`. -/
theorem isUTMStrictHalt_block13 {k : ℕ} (sp : BSpec St k) (T' : Machine (Fin k) Ps (KSym Sy))
    (hsim : ∀ C w,
      (∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) → ∃ M rm, n ≤ M ∧
        HaltsIn T' M (benc T sp (encC13 C w)) (benc T sp (finCfg13 C vf mf rm))) ∧
      ((∀ n f, ¬ CHaltsIn C n (w, 0) f) →
        ∀ M c, ¬ HaltsIn T' M (benc T sp (encC13 C w)) c))
    (hdet : Spec.Deterministic (numT (Base13_7.numB k) T'))
    (hU0 : (rst T sp .h St.q0).val ∈ Spec.states (numT (Base13_7.numB k) T'))
    (hUA : ∀ a ∈ [num.sym Sy.s6, 0, num.sym Sy.s5, 1, 2] ++ [1, 2],
      a = 0 ∨ a ∈ Spec.symbols (numT (Base13_7.numB k) T'))
    (hUK : ∀ a ∈ 0 :: [1, 2], 7 * (sp.v St.q0 + 1) + a = 0 ∨
      7 * (sp.v St.q0 + 1) + a ∈ Spec.symbols (numT (Base13_7.numB k) T')) :
    SymMerge.IsUTMStrictHalt (numT (Base13_7.numB k) T') (List.range 7) :=
  isUTMStrictHalt_block num 7 Base13_7.sym_lt [.h0, .h1] (by intro p; cases p <;> decide) T sp
    T' St.q0 encC13 finCfg13 (fun C => (((Sim.RA lo13 .s5 .s0 C 0).length + 2 : ℕ) : ℤ))
    (encM (num.st (.go St.q0)) (num.sym Sy.s6) (num.sym Sy.s5)) (encM_primrec _ _ _)
    (fun C w => by rw [Base13_7.henc]; exact encM_eq num lo13 .s5 .s0 (by decide) Base13_7.hlo .q0 .s6 C w)
    (fun C w => by rw [Base13_7.henc])
    (fun C w => (hsim C w).1) (fun C w => (hsim C w).2)
    (fun C vf mf rm hf => by
      obtain ⟨h, _, _, _, he, _⟩ := BlockGen.readM_fin num lo13 .s5 .s0 .h0 .h1 0 Base13_7.hlo hls
        (fun h => k + [Ps.h0, Ps.h1].idxOf h)
        (fun h => absurd (Nat.add_left_cancel h) (by decide)) finCfg13 Base13_7.hnullfin
        Base13_7.hhaltfin C vf mf rm hf
      exact ⟨h, by rw [he]⟩)
    (readM (k + [Ps.h0, Ps.h1].idxOf Ps.h1) (num.sym Sy.s5) 0) (readM_primrec _ _ _) hdet
    (Base13_7.strictBody_block13 sp T' hsim hU0 hUA hUK)

end B13

section B15
open URTM.Gen.K15_6 URTM.Univ.MoritaGen
open URTM.CTSH.U15_6 (nm15 encC15 finCfg15)
open URTM.Univ.U15_6 (num lo15 hls)

/-- **Block conversions of (15,6)**: the strong form, from the hypotheses of
    `Base15_6.isUTMStrict_block15` and the determinism of the table. -/
theorem isUTMStrictHalt_block15 {k : ℕ} (sp : BSpec St k) (T' : Machine (Fin k) Ps (KSym Sy))
    (hsim : ∀ C w,
      (∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) → ∃ M rm, n ≤ M ∧
        HaltsIn T' M (benc T sp (encC15 C w)) (benc T sp (finCfg15 C vf mf rm))) ∧
      ((∀ n f, ¬ CHaltsIn C n (w, 0) f) →
        ∀ M c, ¬ HaltsIn T' M (benc T sp (encC15 C w)) c))
    (hdet : Spec.Deterministic (numT (Base15_6.numB k) T'))
    (hU0 : (rst T sp .h St.q0).val ∈ Spec.states (numT (Base15_6.numB k) T'))
    (hUA : ∀ a ∈ [num.sym Sy.s4, 0, num.sym Sy.s3, 1, 2] ++ [1, 2],
      a = 0 ∨ a ∈ Spec.symbols (numT (Base15_6.numB k) T'))
    (hUK : ∀ a ∈ 0 :: [1, 2], 6 * (sp.v St.q0 + 1) + a = 0 ∨
      6 * (sp.v St.q0 + 1) + a ∈ Spec.symbols (numT (Base15_6.numB k) T')) :
    SymMerge.IsUTMStrictHalt (numT (Base15_6.numB k) T') (List.range 6) :=
  isUTMStrictHalt_block num 6 Base15_6.sym_lt [.h0, .h1] (by intro p; cases p <;> decide) T sp
    T' St.q0 encC15 finCfg15 (fun C => (((Sim.RA lo15 .s3 .s0 C 0).length + 2 : ℕ) : ℤ))
    (encM (num.st (.go St.q0)) (num.sym Sy.s4) (num.sym Sy.s3)) (encM_primrec _ _ _)
    (fun C w => by rw [Base15_6.henc]; exact encM_eq num lo15 .s3 .s0 (by decide) Base15_6.hlo .q0 .s4 C w)
    (fun C w => by rw [Base15_6.henc])
    (fun C w => (hsim C w).1) (fun C w => (hsim C w).2)
    (fun C vf mf rm hf => by
      obtain ⟨h, _, _, _, he, _⟩ := BlockGen.readM_fin num lo15 .s3 .s0 .h1 .h0 0 Base15_6.hlo hls
        (fun h => k + [Ps.h0, Ps.h1].idxOf h)
        (fun h => absurd (Nat.add_left_cancel h) (by decide)) finCfg15 Base15_6.hnullfin
        Base15_6.hhaltfin C vf mf rm hf
      exact ⟨h, by rw [he]⟩)
    (readM (k + [Ps.h0, Ps.h1].idxOf Ps.h0) (num.sym Sy.s3) 0) (readM_primrec _ _ _) hdet
    (Base15_6.strictBody_block15 sp T' hsim hU0 hUA hUK)

end B15

section B17
open URTM.Gen.K17_5 URTM.Univ.MoritaGen
open URTM.CTSH.U17_5 (nm17 encC17 finCfg17)
open URTM.Univ.U17_5 (num lo17 hls)

/-- **Block conversions of (17,5)**: the strong form, from the hypotheses of
    `Base17_5.isUTMStrict_block17` and the determinism of the table. -/
theorem isUTMStrictHalt_block17 {k : ℕ} (sp : BSpec St k) (T' : Machine (Fin k) Ps (KSym Sy))
    (hsim : ∀ C w,
      (∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) → ∃ M rm, n ≤ M ∧
        HaltsIn T' M (benc T sp (encC17 C w)) (benc T sp (finCfg17 C vf mf rm))) ∧
      ((∀ n f, ¬ CHaltsIn C n (w, 0) f) →
        ∀ M c, ¬ HaltsIn T' M (benc T sp (encC17 C w)) c))
    (hdet : Spec.Deterministic (numT (Base17_5.numB k) T'))
    (hU0 : (rst T sp .h St.q0).val ∈ Spec.states (numT (Base17_5.numB k) T'))
    (hUA : ∀ a ∈ [num.sym Sy.s4, 0, num.sym Sy.s3, 1, 2] ++ [1, 2],
      a = 0 ∨ a ∈ Spec.symbols (numT (Base17_5.numB k) T'))
    (hUK : ∀ a ∈ 0 :: [1, 2], 5 * (sp.v St.q0 + 1) + a = 0 ∨
      5 * (sp.v St.q0 + 1) + a ∈ Spec.symbols (numT (Base17_5.numB k) T')) :
    SymMerge.IsUTMStrictHalt (numT (Base17_5.numB k) T') (List.range 5) :=
  isUTMStrictHalt_block num 5 Base17_5.sym_lt [.h0, .h1] (by intro p; cases p <;> decide) T sp
    T' St.q0 encC17 finCfg17 (fun C => (((Sim.RA lo17 .s3 .s0 C 0).length + 2 : ℕ) : ℤ))
    (encM (num.st (.go St.q0)) (num.sym Sy.s4) (num.sym Sy.s3)) (encM_primrec _ _ _)
    (fun C w => by rw [Base17_5.henc]; exact encM_eq num lo17 .s3 .s0 (by decide) Base17_5.hlo .q0 .s4 C w)
    (fun C w => by rw [Base17_5.henc])
    (fun C w => (hsim C w).1) (fun C w => (hsim C w).2)
    (fun C vf mf rm hf => by
      obtain ⟨h, _, _, _, he, _⟩ := BlockGen.readM_fin num lo17 .s3 .s0 .h1 .h0 0 Base17_5.hlo hls
        (fun h => k + [Ps.h0, Ps.h1].idxOf h)
        (fun h => absurd (Nat.add_left_cancel h) (by decide)) finCfg17 Base17_5.hnullfin
        Base17_5.hhaltfin C vf mf rm hf
      exact ⟨h, by rw [he]⟩)
    (readM (k + [Ps.h0, Ps.h1].idxOf Ps.h0) (num.sym Sy.s3) 0) (readM_primrec _ _ _) hdet
    (Base17_5.strictBody_block17 sp T' hsim hU0 hUA hUK)

end B17

end URTM.Univ.BlockHalt
