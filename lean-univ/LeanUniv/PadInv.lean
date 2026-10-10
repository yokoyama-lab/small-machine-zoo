/-
  **Blank-padding invariance** (fix of the 2026-10-03 audit, docs/24 末尾).

  `Spec.toID p g` appends infinitely many blanks `0` to both lists of the code `g`, so one ID
  has infinitely many codes `g` (they differ by trailing blanks). The output clause of
  `IsUTMStrict` therefore asks the decoder to be right on **every** code of the halting ID.
  This file proves that the (10,8) readout `U10_8.readU` (hence the decoder `d10_8`) does not
  see trailing blanks:

  * (in `CodePad`) `getD_of_toID`: two codes of the same ID (at the same head position) agree on the state and,
    index by index, on both lists (`getD _ 0`);
  * (in `CodePad`) `pad_of_getD`: two lists that agree index by index (`getD _ 0`) are one list `m` with
    `k` and `k'` blanks appended;
  * `readU_toID`: `toID p g = toID p g' → readU g = readU g'`.
-/
import LeanUniv.U10_8
import LeanUniv.CodePad

namespace URTM.Univ.PadInv
open URTM URTM.Spec URTM.Spec.CodePad

/-! ### `takeWhile` / `dropWhile` and blanks -/

theorem tw_append_rep {p : ℕ → Bool} (hp : p 0 = false) (A : List ℕ) (k : ℕ) :
    (A ++ List.replicate k 0).takeWhile p = A.takeWhile p := by
  induction A with
  | nil => cases k <;> simp [List.replicate_succ, hp]
  | cons a A ih =>
    simp only [List.cons_append, List.takeWhile_cons]
    split <;> simp [ih]

theorem dw_append_rep_false {p : ℕ → Bool} (hp : p 0 = false) (A : List ℕ) (k : ℕ) :
    (A ++ List.replicate k 0).dropWhile p = A.dropWhile p ++ List.replicate k 0 := by
  induction A with
  | nil => cases k <;> simp [List.replicate_succ, hp]
  | cons a A ih =>
    simp only [List.cons_append, List.dropWhile_cons]
    split <;> simp [ih]

theorem tw_rep_append {p : ℕ → Bool} (hp : p 0 = true) (k : ℕ) (A : List ℕ) :
    (List.replicate k 0 ++ A).takeWhile p = List.replicate k 0 ++ A.takeWhile p := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, hp, ih]

theorem dw_rep_append {p : ℕ → Bool} (hp : p 0 = true) (k : ℕ) (A : List ℕ) :
    (List.replicate k 0 ++ A).dropWhile p = A.dropWhile p := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, hp, ih]

theorem dw_rep {p : ℕ → Bool} (hp : p 0 = true) (k : ℕ) :
    (List.replicate k 0).dropWhile p = [] := by
  simpa using dw_rep_append hp k []

theorem dw_append_rep_true {p : ℕ → Bool} (hp : p 0 = true) (A : List ℕ) (k : ℕ) :
    (A.dropWhile p = [] → (A ++ List.replicate k 0).dropWhile p = []) ∧
    (∀ x t, A.dropWhile p = x :: t →
      (A ++ List.replicate k 0).dropWhile p = x :: (t ++ List.replicate k 0) ∧
      (A ++ List.replicate k 0).takeWhile p = A.takeWhile p) := by
  induction A with
  | nil => exact ⟨fun _ => dw_rep hp k, fun x t h => by simp at h⟩
  | cons a A ih =>
    cases ha : p a with
    | true =>
      simp only [List.cons_append, List.dropWhile_cons, List.takeWhile_cons, ha, if_true]
      exact ⟨ih.1, fun x t h => by rw [(ih.2 x t h).1, (ih.2 x t h).2]; simp⟩
    | false =>
      simp only [List.cons_append, List.dropWhile_cons, List.takeWhile_cons, ha]
      refine ⟨fun h => by simp at h, fun x t h => ?_⟩
      simp only [Bool.false_eq_true, if_false, List.cons.injEq] at h ⊢
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨⟨rfl, rfl⟩, trivial⟩

/-! ### The (10,8) readout does not see trailing blanks -/

open U10_8 in
theorem readU_padL (s : ℕ) (m r : List ℕ) (k : ℕ) :
    readU (s, m ++ List.replicate k 0, r) = readU (s, m, r) := by
  rw [readU_eq, readU_eq]
  simp only [List.reverse_append, List.reverse_replicate, List.append_assoc]
  rw [dw_rep_append (p := (· != 7)) rfl, tw_rep_append (p := (· != 7)) rfl]
  split <;> simp [List.count_append, List.count_replicate,
    tw_append_rep (p := (· != 0)) rfl]

open U10_8 in
theorem readU_padR (s : ℕ) (l m : List ℕ) (k : ℕ) :
    readU (s, l, m ++ List.replicate k 0) = readU (s, l, m) := by
  rw [readU_eq, readU_eq]
  simp only [← List.append_assoc]
  have H := dw_append_rep_true (p := (· != 7)) rfl (l.reverse ++ m) k
  rcases hA : (l.reverse ++ m).dropWhile (· != 7) with _ | ⟨x, t⟩
  · rw [H.1 hA]
  · obtain ⟨h1, h2⟩ := H.2 x t hA
    rw [h1, h2]
    simp only [dw_append_rep_false (p := fun a => a == 4 || a == 5) rfl,
      tw_append_rep (p := fun a => a == 1 || a == 2) rfl]

open U10_8 in
/-- **The readout depends only on the ID**, not on the code chosen for it. -/
theorem readU_toID {p : ℤ} {g g' : Code} (h : toID p g = toID p g') : readU g = readU g' := by
  obtain ⟨-, hl, hr⟩ := getD_of_toID h
  obtain ⟨m, k, k', e1, e2⟩ := pad_of_getD _ _ hl
  obtain ⟨m', j, j', e3, e4⟩ := pad_of_getD _ _ hr
  obtain ⟨s, l, r⟩ := g
  obtain ⟨s', l', r'⟩ := g'
  simp only at e1 e2 e3 e4
  subst e1 e2 e3 e4
  rw [readU_padR, readU_padL, readU_padR, readU_padL]
  rfl

end URTM.Univ.PadInv
