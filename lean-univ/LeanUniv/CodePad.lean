/-
  **Codes of one ID differ only by trailing blanks** (fix of the 2026-10-03 audit, docs/24 末尾).

  `Spec.toID p g` reads both lists of `g` with the blank `0` as default, so appending blanks to
  either list gives another code of the same ID. Conversely (`getD_of_toID`, `pad_of_getD`), two
  codes of one ID are one pair of lists with blanks appended. Depends on `Spec` only.
-/
import LeanUniv.Spec

namespace URTM.Spec.CodePad
open URTM URTM.Spec

/-! ### Codes of the same ID -/

theorem getD_append_replicate (l : List ℕ) (k i : ℕ) :
    (l ++ List.replicate k 0).getD i 0 = l.getD i 0 := by
  induction l generalizing i with
  | nil =>
    induction k generalizing i with
    | zero => rfl
    | succ k ih =>
      cases i with
      | zero => simp
      | succ n => simpa [List.replicate_succ] using ih n
  | cons a l ih =>
    cases i with
    | zero => simp
    | succ n => simpa using ih n

theorem eq_replicate_of_getD (l : List ℕ) (h : ∀ i, l.getD i 0 = 0) :
    l = List.replicate l.length 0 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have h0 : a = 0 := by simpa using h 0
    have hl := ih (fun i => by simpa using h (i + 1))
    rw [h0, List.length_cons, List.replicate_succ, ← hl]

/-- Lists that agree index by index (blank default) differ only by trailing blanks. -/
theorem pad_of_getD : ∀ (l l' : List ℕ), (∀ i, l.getD i 0 = l'.getD i 0) →
    ∃ m k k', l = m ++ List.replicate k 0 ∧ l' = m ++ List.replicate k' 0
  | [], l', h => ⟨[], 0, l'.length, rfl,
      by simpa using eq_replicate_of_getD l' (fun i => by simpa using (h i).symm)⟩
  | a :: l, [], h => ⟨[], (a :: l).length, 0,
      by simpa using eq_replicate_of_getD (a :: l) (fun i => by simpa using h i), rfl⟩
  | a :: l, b :: l', h => by
    have hab : a = b := by simpa using h 0
    obtain ⟨m, k, k', h1, h2⟩ := pad_of_getD l l' (fun i => by simpa using h (i + 1))
    exact ⟨a :: m, k, k', by simp [h1], by simp [h2, hab]⟩

/-- Two codes of the same ID (head at `p`) agree on the state and index by index on both lists. -/
theorem getD_of_toID {p : ℤ} {g g' : Code} (h : toID p g = toID p g') :
    g.1 = g'.1 ∧ (∀ i, g.2.1.getD i 0 = g'.2.1.getD i 0) ∧
      (∀ i, g.2.2.getD i 0 = g'.2.2.getD i 0) := by
  refine ⟨congrArg ID.st h, fun i => ?_, fun i => ?_⟩
  · have hx := congrFun (congrArg ID.tape h) (p - 1 - i)
    have hlt : ¬ p ≤ p - 1 - (i : ℤ) := by omega
    have e : (p - 1 - (p - 1 - (i : ℤ))).toNat = i := by omega
    simpa only [toID, if_neg hlt, e] using hx
  · have hx := congrFun (congrArg ID.tape h) (p + i)
    have hle : p ≤ p + (i : ℤ) := by omega
    have e : (p + (i : ℤ) - p).toNat = i := by omega
    simpa only [toID, if_pos hle, e] using hx

/-- Appending blanks to either list of a code gives a code of the same ID. -/
theorem toID_pad (p : ℤ) (s : ℕ) (l r : List ℕ) (k j : ℕ) :
    toID p (s, l ++ List.replicate k 0, r ++ List.replicate j 0) = toID p (s, l, r) := by
  simp only [toID, getD_append_replicate]

end URTM.Spec.CodePad
