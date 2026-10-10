/-
  **Block conversions of URTM(10,8)** (docs/24 P7b): the base data for (4,46) and (6,37).

  * `readN`: the (10,8) readout `U10_8.readU` on numbers (`(|C|, ϕ₁(vf))`, no `CTSH.Ch`):
    `readN_eq`, `readN_toID` (from `PadInv.readU_toID`), `readN_primrec`.
  * `hfin`: the final configurations of (10,8) are on list tapes and are read by `readN`,
    whatever the state number.
  * `isUTMStrict_block10`: `BlockGen.isUTMStrict_block` specialised to the base (10,8).
-/
import LeanUniv.BlockGen
import Mathlib.Data.List.TakeWhile

namespace URTM.Univ.Base10_8
open URTM URTM.CTSH URTM.Gen.K10_8 URTM.Univ.KToSpec URTM.Univ.NumGen
open URTM.KState (Tgt Cfg Machine HaltsIn KSym)
open URTM.KStateBlocks (BSpec benc rst)
open URTM.Univ.U10_8 (loN chOf num10_8 syN readU encList)

/-! ### The (10,8) readout on numbers -/

/-- **Readout** (list level): with `L` the whole window, `pre` the part before the first
    `$ = 7`: `|C|` = the number of `∗ = 6` in `pre`; the final string = behind `$`, skip the
    upper-case letters `4, 5` and read the lower-case letters `1, 2`. `none` if there is no `$`. -/
def readN (g : Spec.Code) : Option (ℕ × List ℕ) :=
  match (g.2.1.reverse ++ g.2.2).dropWhile (· != 7) with
  | [] => none
  | _ :: post =>
    some (((g.2.1.reverse ++ g.2.2).takeWhile (· != 7)).count 6,
      (post.dropWhile (fun a => a == 4 || a == 5)).takeWhile (fun a => a == 1 || a == 2))

theorem loN_chOf_of_low (X : List ℕ) (h : ∀ a ∈ X, (a == 1 || a == 2) = true) :
    (X.map chOf).map loN = X := by
  induction X with
  | nil => rfl
  | cons a X ih =>
    have ha := h a (by simp)
    have ha' : a = 1 ∨ a = 2 := by simpa using ha
    rw [List.map_cons, List.map_cons, ih fun b hb => h b (by simp [hb])]
    rcases ha' with rfl | rfl <;> rfl

/-- `readN` is `U10_8.readU` with the final string mapped back to numbers. -/
theorem readN_eq (g : Spec.Code) : readN g = (readU g).map fun p => (p.1, p.2.1.map loN) := by
  rw [U10_8.readU_eq]
  simp only [readN]
  rcases (g.2.1.reverse ++ g.2.2).dropWhile (· != 7) with _ | ⟨x, post⟩
  · rfl
  · simp only [Option.map_some]
    rw [loN_chOf_of_low _ fun a ha =>
      List.mem_takeWhile_imp (p := fun a => a == 1 || a == 2) ha]

/-- **The readout depends only on the ID.** -/
theorem readN_toID {p : ℤ} {g g' : Spec.Code} (h : Spec.toID p g = Spec.toID p g') :
    readN g = readN g' := by
  rw [readN_eq, readN_eq, PadInv.readU_toID h]

/-- `readN` with its `match` as a `List.casesOn`. -/
def readN' (g : Spec.Code) : Option (ℕ × List ℕ) :=
  List.casesOn ((g.2.1.reverse ++ g.2.2).dropWhile (· != 7)) none fun _ post =>
    some (((g.2.1.reverse ++ g.2.2).takeWhile (· != 7)).count 6,
      (post.dropWhile (fun a => a == 4 || a == 5)).takeWhile (fun a => a == 1 || a == 2))

theorem readN_eq' (g : Spec.Code) : readN g = readN' g := by
  simp only [readN, readN']
  rcases (g.2.1.reverse ++ g.2.2).dropWhile (· != 7) with _ | ⟨x, post⟩ <;> rfl

open Primrec in
theorem readN_primrec : Primrec readN := by
  have hL : Primrec fun g : Spec.Code => g.2.1.reverse ++ g.2.2 :=
    list_append.comp (list_reverse.comp (fst.comp snd)) (snd.comp snd)
  have hpre : Primrec fun g : Spec.Code => (g.2.1.reverse ++ g.2.2).takeWhile (· != 7) :=
    (list_takeWhile (ComputableDec.nat_bne 7)).comp hL
  have p45 : Primrec fun a : ℕ => a == 4 || a == 5 :=
    Primrec.or.comp (Primrec.beq.comp .id (const 4)) (Primrec.beq.comp .id (const 5))
  have p12 : Primrec fun a : ℕ => a == 1 || a == 2 :=
    Primrec.or.comp (Primrec.beq.comp .id (const 1)) (Primrec.beq.comp .id (const 2))
  have hpost : Primrec fun q : Spec.Code × (ℕ × List ℕ) =>
      (q.2.2.dropWhile (fun a => a == 4 || a == 5)).takeWhile (fun a => a == 1 || a == 2) :=
    (list_takeWhile p12).comp ((list_dropWhile p45).comp (snd.comp snd))
  refine (list_casesOn ((list_dropWhile (ComputableDec.nat_bne 7)).comp hL) (const none)
    (option_some.comp (pair (ComputableDec.list_count (const 6) (hpre.comp fst)) hpost)).to₂).of_eq
    fun g => ?_
  rw [readN_eq']; rfl

/-! ### The final shapes of (10,8) -/

/-- The final configurations of (10,8) are on list tapes and are read by `readN`. -/
theorem hfin (k : ℕ) (ps : List Ps) (C : CTSH) (vf : List Ch) (mf : ℕ) (rm : List Ch)
    (hf : Halting C (vf, mf)) :
    ∃ (h : Ps) (L : List Sy) (p : ℕ), p ≤ L.length ∧
      URTM.CTSH.U10_8.finCfg C vf mf rm = ⟨.halt h, p, Sim.tp .s0 L⟩ ∧
      readN (window (k + ps.idxOf h) (L.map num10_8.sym) p) = some (C.length, vf.map loN) := by
  have hmf : mf ≤ C.length := by have := hf.1; simp [CTSH.k] at this; omega
  have hr : ∀ s p, readN (window s ((URTM.CTSH.U10_8.tapeList C mf rm vf).map syN) p) =
      some (C.length, vf.map loN) := by
    intro s p
    rw [readN_eq, U10_8.readU_window C mf hmf rm vf s p]
    rfl
  cases vf with
  | nil =>
    refine ⟨.h0, URTM.CTSH.U10_8.tapeList C mf rm [],
      (URTM.CTSH.U10_8.RA C mf).length + 2 + rm.length, ?_, ?_, hr _ _⟩
    · simp [URTM.CTSH.U10_8.tapeList]; omega
    · simp [URTM.CTSH.U10_8.finCfg, URTM.CTSH.U10_8.tapeOf]
  | cons c v =>
    have hm : mf = 0 := by
      rcases hf.2 with ⟨v', -, h2⟩ | h
      · exact h2
      · simp at h
    subst hm
    refine ⟨.h1, URTM.CTSH.U10_8.tapeList C 0 rm (c :: v), (URTM.CTSH.U10_8.RA C 0).length,
      ?_, ?_, hr _ _⟩
    · simp [URTM.CTSH.U10_8.tapeList]; omega
    · simp [URTM.CTSH.U10_8.finCfg, URTM.CTSH.U10_8.tapeOf]

/-! ### The block conversions -/

theorem syN_lt (s : Sy) : num10_8.sym s < 8 := by cases s <;> decide

theorem encList_left (C : CTSH) (w : List Ch) : ∀ a ∈ (encList C w).2.1, a ∈ [7, 0, 6, 1, 2] := by
  intro a ha
  simp only [encList, List.mem_append, List.mem_cons, List.mem_flatMap, List.mem_map,
    List.not_mem_nil, or_false] at ha
  rcases ha with (rfl | rfl | ⟨u, -, rfl | ⟨c, -, rfl⟩⟩) | rfl
  · simp
  · simp
  · simp
  · cases c <;> simp [loN]
  · simp

theorem encList_right (C : CTSH) (w : List Ch) : ∀ a ∈ (encList C w).2.2, a ∈ [1, 2] := by
  intro a ha
  obtain ⟨c, -, rfl⟩ := List.mem_map.mp ha
  cases c <;> simp [loN]

/-- The numbering of a block conversion of (10,8) with `k` states. -/
def numB (k : ℕ) : Numbering (Fin k) Ps (KSym Sy) :=
  BlockGen.numB num10_8 8 syN_lt [.h0, .h1] (by intro p; cases p <;> decide)

/-- **Body form** (docs/26) of `isUTMStrict_block10`: the body of `IsUTMStrict` for a block conversion of (10,8),
    with the explicit encoder and decoder. Same hypotheses. -/
theorem strictBody_block10 {k : ℕ} (sp : BSpec St k) (T' : Machine (Fin k) Ps (KSym Sy))
    (hsim : ∀ C w,
      (∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) → ∃ M rm, n ≤ M ∧
        HaltsIn T' M (benc T sp (URTM.CTSH.U10_8.encC C w))
          (benc T sp (URTM.CTSH.U10_8.finCfg C vf mf rm))) ∧
      ((∀ n f, ¬ CHaltsIn C n (w, 0) f) →
        ∀ M c, ¬ HaltsIn T' M (benc T sp (URTM.CTSH.U10_8.encC C w)) c))
    (hU0 : (rst T sp .h St.q0).val ∈ Spec.states (numT (numB k) T'))
    (hUA : ∀ a ∈ [7, 0, 6, 1, 2] ++ [1, 2], a = 0 ∨ a ∈ Spec.symbols (numT (numB k) T'))
    (hUK : ∀ a ∈ 0 :: [1, 2], 8 * (sp.v St.q0 + 1) + a = 0 ∨
      8 * (sp.v St.q0 + 1) + a ∈ Spec.symbols (numT (numB k) T')) :
    DropGen.StrictBody (numT (numB k) T')
      (ChainGen.cOf (fun C w => BlockGen.encB (rst T sp .h St.q0).val (8 * (sp.v St.q0 + 1))
        (encList C w)))
      (GenDec.dOf readN) :=
  BlockGen.strictBody_block num10_8 8 syN_lt [.h0, .h1] _ T sp T' Sy.s0 rfl St.q0
    URTM.CTSH.U10_8.encC URTM.CTSH.U10_8.finCfg URTM.Univ.U10_8.δ encList
    URTM.Univ.U10_8.encList_eq (fun _ _ => rfl)
    (fun C w => (hsim C w).1) (fun C w => (hsim C w).2) readN
    (fun _ _ _ h => readN_toID h) (fun C vf mf rm hf => hfin k _ C vf mf rm hf)
    [7, 0, 6, 1, 2] [1, 2] encList_left encList_right hU0 hUA hUK

/-- **A block conversion of (10,8) that simulates every CTSH is a UTM in the strict sense of
    Morita Def. 7.1**, given three finite facts about its table. -/
theorem isUTMStrict_block10 {k : ℕ} (sp : BSpec St k) (T' : Machine (Fin k) Ps (KSym Sy))
    (hsim : ∀ C w,
      (∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) → ∃ M rm, n ≤ M ∧
        HaltsIn T' M (benc T sp (URTM.CTSH.U10_8.encC C w))
          (benc T sp (URTM.CTSH.U10_8.finCfg C vf mf rm))) ∧
      ((∀ n f, ¬ CHaltsIn C n (w, 0) f) →
        ∀ M c, ¬ HaltsIn T' M (benc T sp (URTM.CTSH.U10_8.encC C w)) c))
    (hU0 : (rst T sp .h St.q0).val ∈ Spec.states (numT (numB k) T'))
    (hUA : ∀ a ∈ [7, 0, 6, 1, 2] ++ [1, 2], a = 0 ∨ a ∈ Spec.symbols (numT (numB k) T'))
    (hUK : ∀ a ∈ 0 :: [1, 2], 8 * (sp.v St.q0 + 1) + a = 0 ∨
      8 * (sp.v St.q0 + 1) + a ∈ Spec.symbols (numT (numB k) T')) :
    Spec.IsUTMStrict (numT (numB k) T') :=
  ChainGen.isUTMStrict_of_body_ctsh
    ((BlockGen.encB_primrec _ _).comp₂ ComputableEnc.encList_primrec) readN_primrec
    (strictBody_block10 sp T' hsim hU0 hUA hUK)

end URTM.Univ.Base10_8
