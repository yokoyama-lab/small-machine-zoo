/-
  **2-tag systems** for piece P4 (docs/24 §2 L2; Morita 2017 Def. 7.3 with m = 2).

  Alphabet ℕ, productions `P : ℕ → Option (List ℕ)` (`P a = none`: `a` is a halting symbol):

      a :: b :: s  ⇒  s ++ w      iff  P a = some w

  A word is halting (`Halt`) iff it has length < 2 or its first symbol is halting.

  The semantics (`Step`, `Halt`, determinism, `step?`, `run`) is P3's `URTM.Univ.Tag`
  (`LeanUniv/TagSystem.lean`); this namespace holds only the sweep theory.

  General theory for the Cocke–Minsky gadgets:
  * `evens`/`odds`: the symbols at even / odd positions (the ones a 2-tag sweep reads);
  * `rp n a b = (a b)^n`;
  * `pass`: one aligned sweep over an even-length prefix `u` of the word, reading `evens u`;
  * `LStep`: the step relation restricted to targets of length ≥ 3 (for the length invariant
    that P3's CTSH layer needs), with `pass` proved in this stronger form.
-/
import LeanUniv.TagSystem

namespace URTM.Univ.Tag2
open Relation
open URTM.Univ.Tag (Step Halt)

/-! ### Semantics

The 2-TS semantics is P3's `URTM.Univ.Tag` (`LeanUniv/TagSystem.lean`): `Tag.Step`,
`Tag.Halt`, `Tag.step_det`, `Tag.step?`, `Tag.run`. (Integration: P4's own copy, which was
word-for-word identical, was removed; this file keeps only the general sweep theory.) -/

theorem halt_not_step {P : ℕ → Option (List ℕ)} {x x' : List ℕ} (h : Halt P x) :
    ¬ Step P x x' :=
  (Tag.halt_iff_noStep P x).1 h x'

/-! ### Even and odd positions -/

section EvOd
variable {α : Type*}

/-- The elements at even positions (0, 2, 4, …). -/
def evens : List α → List α
  | [] => []
  | [a] => [a]
  | a :: _ :: l => a :: evens l

/-- The elements at odd positions (1, 3, 5, …). -/
def odds (l : List α) : List α := evens l.tail

@[simp] theorem evens_nil : evens ([] : List α) = [] := rfl
@[simp] theorem odds_nil : odds ([] : List α) = [] := rfl
@[simp] theorem evens_cons (a : α) (l : List α) : evens (a :: l) = a :: odds l := by
  cases l <;> rfl
@[simp] theorem odds_cons (a : α) (l : List α) : odds (a :: l) = evens l := rfl

/-- `(a b)^n`. -/
def rp (n : ℕ) (a b : α) : List α := match n with
  | 0 => []
  | n + 1 => a :: b :: rp n a b

@[simp] theorem rp_zero (a b : α) : rp 0 a b = [] := rfl
theorem rp_succ (n : ℕ) (a b : α) : rp (n + 1) a b = a :: b :: rp n a b := rfl

@[simp] theorem length_rp (n : ℕ) (a b : α) : (rp n a b).length = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [rp_succ, ih]; omega

theorem rp_add (n m : ℕ) (a b : α) : rp (n + m) a b = rp n a b ++ rp m a b := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.add_right_comm, rp_succ, rp_succ, ih]; rfl

@[simp] theorem evens_rp_append (n : ℕ) (a b : α) (l : List α) :
    evens (rp n a b ++ l) = List.replicate n a ++ evens l := by
  induction n with
  | zero => simp
  | succ n ih => simp [rp_succ, ih, List.replicate_succ]

@[simp] theorem odds_rp_append (n : ℕ) (a b : α) (l : List α) :
    odds (rp n a b ++ l) = List.replicate n b ++ odds l := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp [rp_succ, ih, List.replicate_succ]

@[simp] theorem evens_rp (n : ℕ) (a b : α) : evens (rp n a b) = List.replicate n a := by
  simpa using evens_rp_append n a b []

@[simp] theorem odds_rp (n : ℕ) (a b : α) : odds (rp n a b) = List.replicate n b := by
  simpa using odds_rp_append n a b []

theorem evens_rep2_append (m : ℕ) (a : α) (l : List α) :
    evens (List.replicate (2 * m) a ++ l) = List.replicate m a ++ evens l := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by omega]
    simp only [List.replicate_succ, List.cons_append, evens_cons, odds_cons, ih]

theorem odds_rep2_append (m : ℕ) (a : α) (l : List α) :
    odds (List.replicate (2 * m) a ++ l) = List.replicate m a ++ odds l := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by omega]
    simp [List.replicate_succ, ih]

theorem evens_rep2_succ_append (m : ℕ) (a : α) (l : List α) :
    evens (List.replicate (2 * m + 1) a ++ l) = List.replicate (m + 1) a ++ odds l := by
  simp [List.replicate_succ, odds_rep2_append]

theorem odds_rep2_succ_append (m : ℕ) (a : α) (l : List α) :
    odds (List.replicate (2 * m + 1) a ++ l) = List.replicate m a ++ evens l := by
  rw [List.replicate_succ, List.cons_append, odds_cons, evens_rep2_append]

@[simp] theorem evens_rep2 (m : ℕ) (a : α) :
    evens (List.replicate (2 * m) a) = List.replicate m a := by
  simpa using evens_rep2_append m a []

@[simp] theorem odds_rep2 (m : ℕ) (a : α) :
    odds (List.replicate (2 * m) a) = List.replicate m a := by
  simpa using odds_rep2_append m a []

@[simp] theorem evens_rep2_succ (m : ℕ) (a : α) :
    evens (List.replicate (2 * m + 1) a) = List.replicate (m + 1) a := by
  simpa using evens_rep2_succ_append m a []

@[simp] theorem odds_rep2_succ (m : ℕ) (a : α) :
    odds (List.replicate (2 * m + 1) a) = List.replicate m a := by
  simpa using odds_rep2_succ_append m a []

@[simp] theorem flatten_replicate_single (n : ℕ) (c : α) :
    (List.replicate n [c]).flatten = List.replicate n c := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

@[simp] theorem flatten_replicate_pair (n : ℕ) (c d : α) :
    (List.replicate n [c, d]).flatten = rp n c d := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih, rp_succ]

@[simp] theorem flatten_replicate_quad (n : ℕ) (c d : α) :
    (List.replicate n [c, d, c, d]).flatten = rp (2 * n) c d := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega]
    simp [List.replicate_succ, ih, rp_succ]

theorem count_rp [DecidableEq α] (n : ℕ) (a b c : α) :
    (rp n a b).count c = n * [a, b].count c := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [rp_succ, show a :: b :: rp n a b = [a, b] ++ rp n a b from rfl, List.count_append, ih,
      Nat.succ_mul, Nat.add_comm]

end EvOd

/-! ### One aligned sweep (`pass`) -/

/-- The step relation restricted to targets of length ≥ 3. -/
def LStep (P : ℕ → Option (List ℕ)) (u v : List ℕ) : Prop := Step P u v ∧ 3 ≤ v.length

theorem LStep.step {P : ℕ → Option (List ℕ)} {u v : List ℕ} (h : LStep P u v) : Step P u v :=
  h.1

/-- The output of a sweep that reads the symbols `e`. -/
def out (P : ℕ → Option (List ℕ)) (e : List ℕ) : List ℕ := e.flatMap fun a => (P a).getD []

@[simp] theorem out_nil (P : ℕ → Option (List ℕ)) : out P [] = [] := rfl
@[simp] theorem out_cons (P : ℕ → Option (List ℕ)) (a : ℕ) (e : List ℕ) :
    out P (a :: e) = (P a).getD [] ++ out P e := rfl
@[simp] theorem out_append (P : ℕ → Option (List ℕ)) (e₁ e₂ : List ℕ) :
    out P (e₁ ++ e₂) = out P e₁ ++ out P e₂ := by simp [out]

@[simp] theorem out_replicate (P : ℕ → Option (List ℕ)) (n a : ℕ) :
    out P (List.replicate n a) = (List.replicate n ((P a).getD [])).flatten := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, out_cons, ih, List.replicate_succ, List.flatten_cons]

theorem out_replicate_pair (P : ℕ → Option (List ℕ)) (n a c d : ℕ) (h : P a = some [c, d]) :
    out P (List.replicate n a) = rp n c d := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, out_cons, ih, h]; rfl

theorem out_replicate_quad (P : ℕ → Option (List ℕ)) (n a c d : ℕ)
    (h : P a = some [c, d, c, d]) : out P (List.replicate n a) = rp (2 * n) c d := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, out_cons, ih, h, show 2 * (n + 1) = 1 + 1 + 2 * n by omega,
      rp_add, rp_add]
    rfl

/-- **One aligned sweep.** A 2-TS run over an even-length prefix `u` of the word reads exactly
    `evens u` and appends their productions; every word strictly inside the sweep has length
    ≥ 3 provided every production read is nonempty, and the final word has length ≥ 3.
    A nonempty sweep takes at least one step. -/
theorem pass (P : ℕ → Option (List ℕ)) :
    ∀ (n : ℕ) (u v : List ℕ), u.length = 2 * (n + 1) →
      (∀ a ∈ evens u, ∃ w, P a = some w ∧ w ≠ []) →
      3 ≤ (v ++ out P (evens u)).length →
      TransGen (LStep P) (u ++ v) (v ++ out P (evens u)) := by
  intro n
  induction n with
  | zero =>
    intro u v hu hP hlen
    match u, hu with
    | [a, b], _ =>
      obtain ⟨w, hw, -⟩ := hP a (by simp)
      simp only [evens_cons, odds_cons, evens_nil, out_cons, hw, Option.getD_some, out_nil,
        List.append_nil] at hlen ⊢
      exact TransGen.single ⟨by simpa using Step.mk (P := P) (b := b) (s := v) hw, hlen⟩
  | succ n ih =>
    intro u v hu hP hlen
    match u, hu with
    | a :: b :: s, hu =>
      have hs : s.length = 2 * (n + 1) := by simp at hu; omega
      obtain ⟨w, hw, hwne⟩ := hP a (by simp)
      have hP' : ∀ c ∈ evens s, ∃ w, P c = some w ∧ w ≠ [] := fun c hc => hP c (by simp [hc])
      have hev : evens (a :: b :: s) = a :: evens s := by simp
      rw [hev, out_cons, hw, Option.getD_some] at hlen ⊢
      have ih' := ih s (v ++ w) hs hP' (by simpa using hlen)
      simp only [List.append_assoc] at ih'
      refine TransGen.head ⟨?_, ?_⟩ ih'
      · simpa [List.append_assoc] using Step.mk (P := P) (b := b) (s := s ++ v) hw
      · have := List.length_pos_of_ne_nil hwne
        simp only [List.length_append]
        omega

/-- `pass` in the form used by the gadgets: the current word is `u ++ v`, the sweep reads the
    explicit list `e = evens u`, and the result is the explicit word `w₁`. -/
theorem pass' {P : ℕ → Option (List ℕ)} {u v w₀ w₁ e : List ℕ} (n : ℕ)
    (h₀ : u ++ v = w₀) (hu : u.length = 2 * (n + 1)) (he : evens u = e)
    (hP : ∀ a ∈ e, ∃ w, P a = some w ∧ w ≠ []) (h₁ : v ++ out P e = w₁)
    (hlen : 3 ≤ w₁.length) : TransGen (LStep P) w₀ w₁ := by
  subst h₀ h₁ he
  exact pass P n u v hu hP hlen

/-- A sweep over the whole current word. -/
theorem passAll {P : ℕ → Option (List ℕ)} {w₀ w₁ e : List ℕ} (n : ℕ)
    (hu : w₀.length = 2 * (n + 1)) (he : evens w₀ = e)
    (hP : ∀ a ∈ e, ∃ w, P a = some w ∧ w ≠ []) (h₁ : out P e = w₁)
    (hlen : 3 ≤ w₁.length) : TransGen (LStep P) w₀ w₁ :=
  pass' (u := w₀) (v := []) n (List.append_nil _) hu he hP (by simpa using h₁) hlen

end URTM.Univ.Tag2
