/-
  **2-tag systems** (Morita 2017 Def. 7.3 with m = 2; docs/24 §2 L2/L3, piece P3).

  Alphabet ℕ. The productions are a function `P : ℕ → Option (List ℕ)`: `P a = some w` is the
  rule `a → w`, `P a = none` makes `a` a halting symbol. For the finite alphabet `[0, S)` of a
  concrete system, a table `T : List (Option (List ℕ))` gives `P := ofTable T` (symbols
  `≥ T.length` are halting).

      a :: b :: s  ⇒  s ++ w      iff  P a = some w

  A word is *halting* (`Halt`) iff it has length < 2 or its first symbol is halting; exactly
  these words have no successor (`halt_iff_noStep`).

  `Short P w`: `w = [a]` with `a` non-halting. Such a word is halting in the 2-TS, but Morita's
  CTSH of Thm 7.2 does not halt on its image (the proof of Thm 7.2 ignores |α| < 2). The
  simulation in `TagToCTSH.lean` therefore assumes an invariant that excludes it; `NoShort`
  (no reachable word is `Short`) is the weakest such invariant.
-/
import Mathlib.Logic.Relation
import Mathlib.Data.List.Basic

namespace URTM.Univ.Tag
open Relation

/-- Productions of the table `T`: symbol `a` has rule `T[a]` (`none` = halting symbol);
    symbols outside the table are halting. -/
def ofTable (T : List (Option (List ℕ))) (a : ℕ) : Option (List ℕ) := T.getD a none

/-- One 2-TS step. -/
inductive Step (P : ℕ → Option (List ℕ)) : List ℕ → List ℕ → Prop
  | mk {a b : ℕ} {s w : List ℕ} : P a = some w → Step P (a :: b :: s) (s ++ w)

/-- Halting string: length < 2, or the first symbol is halting. -/
def Halt (P : ℕ → Option (List ℕ)) : List ℕ → Prop
  | [] => True
  | [_] => True
  | a :: _ :: _ => P a = none

/-- A one-letter word whose letter is non-halting (halting in the 2-TS only because of its
    length). -/
def Short (P : ℕ → Option (List ℕ)) (w : List ℕ) : Prop :=
  ∃ a v, w = [a] ∧ P a = some v

/-- No word reachable from `x` is `Short`. Closed under steps by construction. -/
def NoShort (P : ℕ → Option (List ℕ)) (x : List ℕ) : Prop :=
  ∀ y, ReflTransGen (Step P) x y → ¬ Short P y

theorem NoShort.step {P : ℕ → Option (List ℕ)} {x x' : List ℕ} (h : NoShort P x)
    (hs : Step P x x') : NoShort P x' :=
  fun y hy => h y (ReflTransGen.head hs hy)

theorem NoShort.not_short {P : ℕ → Option (List ℕ)} {x : List ℕ} (h : NoShort P x) :
    ¬ Short P x :=
  h x ReflTransGen.refl

theorem step_det {P : ℕ → Option (List ℕ)} {x y₁ y₂ : List ℕ} (h₁ : Step P x y₁)
    (h₂ : Step P x y₂) : y₁ = y₂ := by
  cases h₁ with
  | mk ha =>
    cases h₂ with
    | mk ha' => rw [ha] at ha'; cases ha'; rfl

/-- Every word halts or steps. -/
theorem halt_or_step (P : ℕ → Option (List ℕ)) (x : List ℕ) :
    Halt P x ∨ ∃ x', Step P x x' := by
  match x with
  | [] => exact .inl trivial
  | [_] => exact .inl trivial
  | a :: _ :: _ =>
    cases h : P a with
    | none => exact .inl h
    | some w => exact .inr ⟨_, .mk h⟩

/-- Halting strings are exactly the words without a successor. -/
theorem halt_iff_noStep (P : ℕ → Option (List ℕ)) (x : List ℕ) :
    Halt P x ↔ ∀ x', ¬ Step P x x' := by
  constructor
  · intro h x' hs
    cases hs with
    | mk ha => simp [Halt, ha] at h
  · intro h
    rcases halt_or_step P x with hh | ⟨x', hx'⟩
    · exact hh
    · exact absurd hx' (h _)

/-- Executable step (for tests). -/
def step? (P : ℕ → Option (List ℕ)) : List ℕ → Option (List ℕ)
  | a :: _ :: s => (P a).map (s ++ ·)
  | _ => none

theorem step?_sound {P : ℕ → Option (List ℕ)} {x x' : List ℕ} (h : step? P x = some x') :
    Step P x x' := by
  match x, h with
  | a :: _ :: s, h =>
    simp only [step?, Option.map_eq_some_iff] at h
    obtain ⟨w, hw, rfl⟩ := h
    exact .mk hw

/-- Run with fuel; the flag reports that a halting string was reached. -/
def run (P : ℕ → Option (List ℕ)) : ℕ → List ℕ → List ℕ × Bool
  | 0, x => (x, false)
  | fuel + 1, x => match step? P x with
    | none => (x, true)
    | some x' => run P fuel x'

end URTM.Univ.Tag
