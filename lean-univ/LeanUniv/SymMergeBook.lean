/-
  **Merging symbols, then removing the halting quintuples** (the analogue of `Book.lean` for the
  merged tables `SymMerge<k>_<m>.U` of `tools/gen_symmerge_lean.py`).

  `DropGen.isUTMStrict_drop` removes the 0-shift quintuples into pseudo-states and keeps Def. 7.1,
  but it needs an explicit encoder whose initial state is still a state of the smaller table.
  `SymMerge.IsUTMStrictHalt` hides the encoder in an existential, so it does not say in which state
  the encoded initial IDs start (an encoder that starts in a pseudo-state is not excluded by it).
  This file keeps the encoder:

  * `IsUTMStrictHaltAt U F q0`: `IsUTMStrictHalt U F` for an encoder `c` whose codes all start in
    the state `q0`, with the body stated as `DropGen.StrictBody U c d`.
    `IsUTMStrictHaltAt.isUTMStrictHalt` forgets `q0`.
  * `strictBody_mapQ`: the body of `SymMerge.isUTMStrict_mapQ` for the given encoder and decoder
    (the encoder `mapCode h ∘ c`, the decoder `d ∘ mapCode s`; the same proof).
  * `isUTMStrict_drop_mapQ`: **merge, then remove the halting quintuples `H` of the merged table**:
    `IsUTMStrict (dropT (mapQ h U) H)`, under the hypotheses of `isUTMStrict_mapQ` and of
    `DropGen.isUTMStrict_drop` (the removed quintuples are 0-shift quintuples into pseudo-states,
    `q0` is a state of the smaller table, no non-blank symbol is lost).
  * `isUTMStrictHaltAt_block` and the bases `isUTMStrictHaltAt_block10` / `13` / `15` / `17`: the
    hypotheses of `BlockHalt.isUTMStrictHalt_block` (resp. `…_block10` etc.), with the conclusion
    `IsUTMStrictHaltAt … (rst T sp .h q0).val`. The proofs are those of `BlockHalt` with the encoder
    `ChainGen.cOf (fun C w => BlockGen.encB (rst T sp .h q0).val …)` kept.
-/
import LeanUniv.BlockHalt

namespace URTM.Univ.SymMergeBook

set_option linter.unusedSectionVars false

/-! ### The strong form with the initial state named -/

section General
open URTM URTM.Spec URTM.Univ.DropGen URTM.Univ.SymMerge

/-- **`IsUTMStrictHalt` with the encoder's initial state named**: some computable encoder `c`
    and decoder `d` with the body of `IsUTMStrict U` (`DropGen.StrictBody`), every code `c p` in
    the state `q0`, and every halting ID reached from an encoded initial ID in a pseudo-state of
    `U` with every cell in `F`. -/
def IsUTMStrictHaltAt (U : List Quint) (F : List ℕ) (q0 : ℕ) : Prop :=
  ∃ (c : ℕ × Code → Code) (d : Code → Option Code), Computable c ∧ Computable d ∧
    (∀ p, (c p).1 = q0) ∧ StrictBody U c d ∧
    ∀ n a, IsIDOf (tm n) (toID 0 a) → ∀ γ, HaltsAt U (toID 0 (c (n, a))) γ →
      γ.st ∉ U.map Quint.p ∧ ∀ x, γ.tape x ∈ F

/-- Forgetting the initial state gives the strong form of `SymMerge`. -/
theorem IsUTMStrictHaltAt.isUTMStrictHalt {U : List Quint} {F : List ℕ} {q0 : ℕ}
    (h : IsUTMStrictHaltAt U F q0) : IsUTMStrictHalt U F := by
  obtain ⟨c, d, hc, hd, -, hb, hP⟩ := h
  exact isUTMStrictHalt_of_body hc hd hb hP

/-- **The body of `isUTMStrict_mapQ`** for the given encoder and decoder: the merged table with
    the encoder `mapCode h ∘ c` and the decoder `d ∘ mapCode s`. -/
theorem strictBody_mapQ {U : List Quint} {F : List ℕ} {h s : ℕ → ℕ} {c : ℕ × Code → Code}
    {d : Code → Option Code} (hb : StrictBody U c d)
    (hP : ∀ n a, IsIDOf (tm n) (toID 0 a) → ∀ γ, HaltsAt U (toID 0 (c (n, a))) γ →
      γ.st ∉ U.map Quint.p ∧ ∀ x, γ.tape x ∈ F)
    (hdet : Deterministic (mapQ h U)) (h0 : h 0 = 0) (s0 : s 0 = 0)
    (hsh : ∀ a ∈ F, s (h a) = a) :
    StrictBody (mapQ h U) (fun p => mapCode h (c p)) (fun g => d (mapCode s g)) := by
  intro n a ha
  obtain ⟨hID, hhalt, hnon⟩ := hb n a ha
  show IsIDOf (mapQ h U) (toID 0 (mapCode h (c (n, a)))) ∧ _ ∧ _
  rw [toID_mapCode h0]
  refine ⟨isIDOf_map h0 hID, fun β hβ => ?_, fun hn => not_halts_map h hdet (hnon hn)⟩
  obtain ⟨γ, hγ, ⟨g₀, hg₀⟩, hall⟩ := hhalt β hβ
  obtain ⟨hst, hF⟩ := hP n a ha γ hγ
  refine ⟨mapID h γ, ⟨reach_map h hγ.1, halted_map h hst⟩,
    ⟨mapCode h g₀, show toID γ.pos (mapCode h g₀) = mapID h γ by rw [toID_mapCode h0, hg₀]⟩,
    fun g hg => ?_⟩
  refine hall (mapCode s g) ?_
  have hg' : toID γ.pos g = mapID h γ := hg
  rw [toID_mapCode s0, hg', mapID_mapID hsh γ hF]

/-- **Merging symbols, then removing the halting quintuples, keeps Def. 7.1.** From the strong
    form with the initial state `q0`, the hypotheses of `SymMerge.isUTMStrict_mapQ` on the merge,
    and the hypotheses of `DropGen.isUTMStrict_drop` on the merged table: `H` consists of 0-shift
    quintuples of `mapQ h U` into states without outgoing quintuples, `q0` is a state of the
    smaller table, and every non-blank symbol of `mapQ h U` is a symbol of the smaller table. -/
theorem isUTMStrict_drop_mapQ {U H : List Quint} {F : List ℕ} {q0 : ℕ} {h s : ℕ → ℕ}
    (hU : IsUTMStrictHaltAt U F q0) (hdet : Deterministic (mapQ h U))
    (hh : Primrec h) (hs : Primrec s) (h0 : h 0 = 0) (s0 : s 0 = 0)
    (hsh : ∀ a ∈ F, s (h a) = a) (hH : HaltQuints (mapQ h U) H)
    (hq0 : q0 ∈ states (dropT (mapQ h U) H))
    (hsym : ∀ x ∈ symbols (mapQ h U), x = 0 ∨ x ∈ symbols (dropT (mapQ h U) H)) :
    IsUTMStrict (dropT (mapQ h U) H) := by
  obtain ⟨c, d, hc, hd, hq, hb, hP⟩ := hU
  exact isUTMStrict_drop ((mapCode_primrec hh).to_comp.comp hc)
    (hd.comp (mapCode_primrec hs).to_comp) hdet hH
    (fun n a _ => by show (c (n, a)).1 ∈ _; rw [hq]; exact hq0) hsym
    (strictBody_mapQ hb hP hdet h0 s0 hsh)

end General

/-! ### Block conversions: the strong form with the initial state -/

section Typed
open URTM URTM.CTSH URTM.Univ.KToSpec URTM.Univ.NumGen
open URTM.KState (Cfg Machine HaltsIn KSym)
open URTM.KStateBlocks (BSpec benc rst)

variable {Q P S : Type} [DecidableEq Q] [DecidableEq P] [DecidableEq S] {k : ℕ}
  (N : Numbering Q P S) (n : ℕ) (hn : ∀ s, N.sym s < n) (ps : List P) (hp : ∀ p, p ∈ ps)
  (T : Machine Q P S) (sp : BSpec Q k)

/-- **`BlockHalt.isUTMStrictHalt_block` with the initial state named**: the same hypotheses, and
    the encoder `ChainGen.cOf (fun C w => BlockGen.encB (rst T sp .h q0).val …)` starts in the state
    `(rst T sp .h q0).val`. -/
theorem isUTMStrictHaltAt_block (T' : Machine (Fin k) P (KSym S)) (q0 : Q)
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
    IsUTMStrictHaltAt (numT (BlockGen.numB N n hn ps hp) T') (List.range n)
      (rst T sp .h q0).val :=
  ⟨ChainGen.cOf fun C w => BlockGen.encB (rst T sp .h q0).val (n * (sp.v q0 + 1)) (enc0 C w),
    GenDec.dOf readN, ChainGen.cOf_computable ((BlockGen.encB_primrec _ _).comp₂ henc0),
    GenDec.dOf_computable hread, fun _ => rfl, hbody, fun _ _ _ γ hγ => by
      simp only [ChainGen.cOf] at hγ
      rw [BlockGen.encB_eq N n hn ps hp T sp (δ _) (encC _ _) q0 (hq0 _ _) _ (hencEq _ _)] at hγ
      exact BlockHalt.halt_shape N n hn ps hp T sp T' _ _ (encC _ _) (finC _) (δ _) hdet
        (hsimF _ _) (hsimN _ _) (hfst _) γ hγ⟩

end Typed

/-! ### The four bases (the proofs of `BlockHalt.isUTMStrictHalt_block10` etc.) -/

section B10
open URTM URTM.CTSH URTM.Univ.KToSpec
open URTM.KState (Machine HaltsIn KSym)
open URTM.KStateBlocks (BSpec benc rst)
open URTM.Gen.K10_8
open URTM.Univ.U10_8 (num10_8 encList)

/-- **Block conversions of (10,8)**: `BlockHalt.isUTMStrictHalt_block10` with the initial state. -/
theorem isUTMStrictHaltAt_block10 {k : ℕ} (sp : BSpec St k) (T' : Machine (Fin k) Ps (KSym Sy))
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
    IsUTMStrictHaltAt (numT (Base10_8.numB k) T') (List.range 8) (rst T sp .h St.q0).val :=
  isUTMStrictHaltAt_block num10_8 8 Base10_8.syN_lt [.h0, .h1] (by intro p; cases p <;> decide) T
    sp T' St.q0 URTM.CTSH.U10_8.encC URTM.CTSH.U10_8.finCfg URTM.Univ.U10_8.δ encList
    ComputableEnc.encList_primrec URTM.Univ.U10_8.encList_eq (fun _ _ => rfl)
    (fun C w => (hsim C w).1) (fun C w => (hsim C w).2)
    (fun C vf mf rm hf => by
      obtain ⟨h, _, _, _, he, _⟩ := Base10_8.hfin k [.h0, .h1] C vf mf rm hf
      exact ⟨h, by rw [he]⟩)
    Base10_8.readN Base10_8.readN_primrec hdet (Base10_8.strictBody_block10 sp T' hsim hU0 hUA hUK)

end B10

section B13
open URTM URTM.CTSH URTM.Univ.KToSpec
open URTM.KState (Machine HaltsIn KSym)
open URTM.KStateBlocks (BSpec benc rst)
open URTM.Gen.K13_7 URTM.Univ.MoritaGen
open URTM.CTSH.U13_7 (nm13 encC13 finCfg13)
open URTM.Univ.U13_7 (num lo13 hls)

/-- **Block conversions of (13,7)**: `BlockHalt.isUTMStrictHalt_block13` with the initial state. -/
theorem isUTMStrictHaltAt_block13 {k : ℕ} (sp : BSpec St k) (T' : Machine (Fin k) Ps (KSym Sy))
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
    IsUTMStrictHaltAt (numT (Base13_7.numB k) T') (List.range 7) (rst T sp .h St.q0).val :=
  isUTMStrictHaltAt_block num 7 Base13_7.sym_lt [.h0, .h1] (by intro p; cases p <;> decide) T sp
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
open URTM URTM.CTSH URTM.Univ.KToSpec
open URTM.KState (Machine HaltsIn KSym)
open URTM.KStateBlocks (BSpec benc rst)
open URTM.Gen.K15_6 URTM.Univ.MoritaGen
open URTM.CTSH.U15_6 (nm15 encC15 finCfg15)
open URTM.Univ.U15_6 (num lo15 hls)

/-- **Block conversions of (15,6)**: `BlockHalt.isUTMStrictHalt_block15` with the initial state. -/
theorem isUTMStrictHaltAt_block15 {k : ℕ} (sp : BSpec St k) (T' : Machine (Fin k) Ps (KSym Sy))
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
    IsUTMStrictHaltAt (numT (Base15_6.numB k) T') (List.range 6) (rst T sp .h St.q0).val :=
  isUTMStrictHaltAt_block num 6 Base15_6.sym_lt [.h0, .h1] (by intro p; cases p <;> decide) T sp
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
open URTM URTM.CTSH URTM.Univ.KToSpec
open URTM.KState (Machine HaltsIn KSym)
open URTM.KStateBlocks (BSpec benc rst)
open URTM.Gen.K17_5 URTM.Univ.MoritaGen
open URTM.CTSH.U17_5 (nm17 encC17 finCfg17)
open URTM.Univ.U17_5 (num lo17 hls)

/-- **Block conversions of (17,5)**: `BlockHalt.isUTMStrictHalt_block17` with the initial state. -/
theorem isUTMStrictHaltAt_block17 {k : ℕ} (sp : BSpec St k) (T' : Machine (Fin k) Ps (KSym Sy))
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
    IsUTMStrictHaltAt (numT (Base17_5.numB k) T') (List.range 5) (rst T sp .h St.q0).val :=
  isUTMStrictHaltAt_block num 5 Base17_5.sym_lt [.h0, .h1] (by intro p; cases p <;> decide) T sp
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

end URTM.Univ.SymMergeBook
