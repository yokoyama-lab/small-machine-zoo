/-
  **Generic lemmas on codes** (docs/24 P7c, P7d).

  * `read_toID2`: a readout of the state and the two lists of the code that ignores blanks appended
    to either list depends only on the ID (the hypothesis `hdinv` of `isUTMStrict_of_chain`).
  * `getD_map_range`: a list given by a function on indices.
  * `ID_ext`: a Spec ID is determined by its three fields.
  * `codeOf γ m k`: the code of an ID `γ` that reads `m` cells to the left of the head and `k` cells
    from the head; `toID_codeOf`: it is a code of `γ` when the tape is blank outside that window.
-/
import LeanUniv.NumGen
import Mathlib.Data.List.GetD

namespace URTM.Univ.ReadGen
open URTM URTM.Univ.KToSpec

/-- A readout of the state and the two lists of the code that ignores blanks appended to either
    list depends only on the ID. -/
theorem read_toID2 {α : Type} (f : ℕ → List ℕ → List ℕ → α)
    (hl : ∀ s k l r, f s (l ++ List.replicate k 0) r = f s l r)
    (hr : ∀ s k l r, f s l (r ++ List.replicate k 0) = f s l r)
    {p : ℤ} {g g' : Spec.Code} (h : Spec.toID p g = Spec.toID p g') :
    f g.1 g.2.1 g.2.2 = f g'.1 g'.2.1 g'.2.2 := by
  obtain ⟨hs, hl', hr'⟩ := Spec.CodePad.getD_of_toID h
  obtain ⟨m, k, k', e1, e2⟩ := Spec.CodePad.pad_of_getD _ _ hl'
  obtain ⟨m', j, j', e3, e4⟩ := Spec.CodePad.pad_of_getD _ _ hr'
  obtain ⟨s, l, r⟩ := g
  obtain ⟨s', l', r'⟩ := g'
  simp only at hs e1 e2 e3 e4
  subst hs e1 e2 e3 e4
  rw [hl, hr, hl, hr]

theorem getD_map_range (f : ℕ → ℕ) (n t : ℕ) :
    ((List.range n).map f).getD t 0 = if t < n then f t else 0 := by
  split
  · rename_i h
    simp [List.getD_eq_getElem?_getD, h]
  · rename_i h
    rw [List.getD_eq_default _ _ (by simp; omega)]

/-- A Spec ID is determined by its three fields. -/
theorem ID_ext {a b : Spec.ID} (h1 : a.st = b.st) (h2 : a.pos = b.pos)
    (h3 : ∀ x, a.tape x = b.tape x) : a = b := by
  cases a; cases b
  simp only at h1 h2 h3
  subst h1 h2
  rw [show _ = _ from funext h3]

/-- The code of the ID `γ` that reads `m` cells to the left of the head and `k` cells from the
    head. -/
def codeOf (γ : Spec.ID) (m k : ℕ) : Spec.Code :=
  (γ.st, (List.range m).map (fun (i : ℕ) => γ.tape (γ.pos - 1 - (i : ℤ))),
    (List.range k).map (fun (i : ℕ) => γ.tape (γ.pos + (i : ℤ))))

/-- `codeOf γ m k` is a code of `γ` when the tape of `γ` is blank outside the window. -/
theorem toID_codeOf (γ : Spec.ID) (m k : ℕ)
    (h : ∀ x, (x < γ.pos - m ∨ γ.pos + k ≤ x) → γ.tape x = 0) :
    Spec.toID γ.pos (codeOf γ m k) = γ := by
  refine ID_ext rfl rfl fun x => ?_
  simp only [Spec.toID, codeOf]
  by_cases hx : γ.pos ≤ x
  · rw [if_pos hx, getD_map_range]
    by_cases hk : (x - γ.pos).toNat < k
    · rw [if_pos hk]
      congr 1
      omega
    · rw [if_neg hk, h x (.inr (by omega))]
  · rw [if_neg hx, getD_map_range]
    by_cases hm : (γ.pos - 1 - x).toNat < m
    · rw [if_pos hm]
      congr 1
      omega
    · rw [if_neg hm, h x (.inl (by omega))]

end URTM.Univ.ReadGen
