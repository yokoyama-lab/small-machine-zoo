/-
  **Dropping the halting quintuples keeps Morita Def. 7.1** (docs/26).

  Morita's description files write the two halting entries `(halt)`/`(null)` of the book's tables
  as 0-shift quintuples into pseudo-states (states without outgoing quintuples). This file shows,
  for an arbitrary table, that removing such quintuples keeps `IsUTMStrict`, with the same encoder
  and a decoder that first puts the halting ID back into the pseudo-state.

  * `StrictBody U c d`: the body of `IsUTMStrict U` for a given encoder `c` and decoder `d`
    (`IsUTMStrict U ↔ ∃ c d, Computable c ∧ Computable d ∧ StrictBody U c d`, by `Iff.rfl`).
  * `dropT U H`: `U` without the quintuples of `H`.
  * `fixCode H g`: if some `r ∈ H` applies to the code `g` (state `r.p`, `r.s` under the head),
    the code of the ID after `r` (state `r.q`, `r.t` under the head); otherwise `g`.
    `fixD H d := d ∘ fixCode H` is computable when `d` is (`fixD_computable`).
  * `strictBody_drop`: if `U` is deterministic and every `r ∈ H` is a 0-shift quintuple of `U`
    into a state without outgoing quintuples in `U`, then `StrictBody U c d` gives
    `StrictBody (dropT U H) c (fixD H d)`, provided the initial IDs `c (n, a)` start in a state of
    `dropT U H` and every symbol of `U` other than the blank is a symbol of `dropT U H`.
  * `isUTMStrict_drop`: the same with computability, ending in `IsUTMStrict (dropT U H)`.

  The run-level facts (`drop_path`, `drop_halts`) are the Spec-level analogue of the zoo's
  `SimLemmas.drop_simulates` (which is stated on the zoo's typed machines).
-/
import LeanUniv.Strict
import Mathlib.Computability.Primrec.List

namespace URTM.Univ.DropGen
open URTM URTM.Spec Relation

/-! ### The body of `IsUTMStrict` for a given encoder and decoder -/

/-- The body of `IsUTMStrict U` (Morita Def. 7.1, strict form) for the encoder `c` and the
    decoder `d`. -/
def StrictBody (U : List Quint) (c : ℕ × Code → Code) (d : Code → Option Code) : Prop :=
  ∀ n a, IsIDOf (tm n) (toID 0 a) →
    IsIDOf U (toID 0 (c (n, a))) ∧
    (∀ β, HaltsAt (tm n) (toID 0 a) β →
      ∃ γ, HaltsAt U (toID 0 (c (n, a))) γ ∧ (∃ g, toID γ.pos g = γ) ∧
        ∀ g, toID γ.pos g = γ → ∃ b, d g = some b ∧ toID β.pos b = β) ∧
    (¬ Halts (tm n) (toID 0 a) → ¬ Halts U (toID 0 (c (n, a))))

/-- `IsUTMStrict` is exactly "some computable `c`, `d` with `StrictBody`". -/
theorem isUTMStrict_iff (U : List Quint) :
    IsUTMStrict U ↔ ∃ c d, Computable c ∧ Computable d ∧ StrictBody U c d := Iff.rfl

theorem isUTMStrict_of_body {U : List Quint} {c : ℕ × Code → Code} {d : Code → Option Code}
    (hc : Computable c) (hd : Computable d) (h : StrictBody U c d) : IsUTMStrict U :=
  ⟨c, d, hc, hd, h⟩

/-! ### The table without the halting quintuples -/

/-- `U` without the quintuples of `H`. -/
def dropT (U H : List Quint) : List Quint := U.filter (fun r => decide (r ∉ H))

theorem mem_dropT {U H : List Quint} {r : Quint} : r ∈ dropT U H ↔ r ∈ U ∧ r ∉ H := by
  simp [dropT]

theorem dropT_sub {U H : List Quint} {r : Quint} (h : r ∈ dropT U H) : r ∈ U :=
  (mem_dropT.mp h).1

theorem deterministic_dropT {U : List Quint} (H : List Quint) (hD : Deterministic U) :
    Deterministic (dropT U H) :=
  fun r₁ h₁ r₂ h₂ => hD r₁ (dropT_sub h₁) r₂ (dropT_sub h₂)

theorem reversible_dropT {U : List Quint} (H : List Quint) (hR : Reversible U) :
    Reversible (dropT U H) :=
  fun r₁ h₁ r₂ h₂ => hR r₁ (dropT_sub h₁) r₂ (dropT_sub h₂)

/-- The conditions on the removed quintuples: each is a 0-shift quintuple of `U` into a state
    without outgoing quintuples in `U` (a pseudo-state). -/
def HaltQuints (U H : List Quint) : Prop :=
  ∀ r ∈ H, r ∈ U ∧ r.d = .Z ∧ ∀ r' ∈ U, r'.p ≠ r.q

instance (U H : List Quint) : Decidable (HaltQuints U H) := by
  unfold HaltQuints; infer_instance

/-! ### Runs -/

section Runs
variable {U H : List Quint}

theorem step_of_drop {c c' : ID} (h : Step (dropT U H) c c') : Step U c c' :=
  let ⟨r, hr, h₁, h₂⟩ := h; ⟨r, dropT_sub hr, h₁, h₂⟩

theorem rtg_of_drop {c c' : ID} (h : ReflTransGen (Step (dropT U H)) c c') :
    ReflTransGen (Step U) c c' :=
  h.mono fun _ _ => step_of_drop

theorem halted_drop {c : ID} (h : Halted U c) : Halted (dropT U H) c :=
  fun r hr => h r (dropT_sub hr)

/-- After a removed quintuple the machine is in a pseudo-state: halted in `U`. -/
theorem halted_apply (hH : HaltQuints U H) {r : Quint} (hr : r ∈ H) (c : ID) :
    Halted U (apply r c) :=
  fun r' hr' ha => (hH r hr).2.2 r' hr' ha.1

/-- A run of `U` either does not use a removed quintuple, or uses one exactly at its end. -/
theorem drop_path (hH : HaltQuints U H) {y γ : ID} (h : ReflTransGen (Step U) y γ) :
    ReflTransGen (Step (dropT U H)) y γ ∨
      ∃ γ' r, r ∈ H ∧ ReflTransGen (Step (dropT U H)) y γ' ∧ Applicable r γ' ∧ γ = apply r γ' := by
  induction h with
  | refl => exact .inl .refl
  | tail _ hbc ih =>
    obtain ⟨r₀, hr₀, ha₀, rfl⟩ := hbc
    rcases ih with ih | ⟨γ', r, hr, -, -, rfl⟩
    · by_cases hH₀ : r₀ ∈ H
      · exact .inr ⟨_, r₀, hH₀, ih, ha₀, rfl⟩
      · exact .inl (ih.tail ⟨r₀, mem_dropT.mpr ⟨hr₀, hH₀⟩, ha₀, rfl⟩)
    · exact absurd ha₀.1 ((hH r hr).2.2 r₀ hr₀)

/-- A halting run of `U` gives a halting run of `dropT U H`: to the same ID, or to the ID just
    before the removed quintuple. -/
theorem drop_haltsAt (hD : Deterministic U) (hH : HaltQuints U H) {y γ : ID}
    (h : HaltsAt U y γ) :
    (HaltsAt (dropT U H) y γ ∧ Halted U γ) ∨
      ∃ γ' r, r ∈ H ∧ HaltsAt (dropT U H) y γ' ∧ Applicable r γ' ∧ γ = apply r γ' := by
  rcases drop_path hH h.1 with hp | ⟨γ', r, hr, hp, ha, rfl⟩
  · exact .inl ⟨⟨hp, halted_drop h.2⟩, h.2⟩
  · refine .inr ⟨γ', r, hr, ⟨hp, fun r' hr' ha' => ?_⟩, ha, rfl⟩
    have := hD r' (dropT_sub hr') r (hH r hr).1 (ha'.1.trans ha.1.symm) (ha'.2.trans ha.2.symm)
    subst this
    exact (mem_dropT.mp hr').2 hr

/-- A halting run of `dropT U H` gives a halting run of `U`. -/
theorem halts_of_drop (hH : HaltQuints U H) {y : ID} (h : Halts (dropT U H) y) : Halts U y := by
  obtain ⟨γ', hp, hh⟩ := h
  by_cases hU : Halted U γ'
  · exact ⟨γ', rtg_of_drop hp, hU⟩
  · simp only [Halted, not_forall, not_not] at hU
    obtain ⟨r, hr, ha⟩ := hU
    have hrH : r ∈ H := by
      by_contra hn; exact hh r (mem_dropT.mpr ⟨hr, hn⟩) ha
    exact ⟨_, (rtg_of_drop hp).tail ⟨r, hr, ha, rfl⟩, halted_apply hH hrH _⟩

end Runs

/-! ### Codes -/

/-- The code with state `q` and `t` written under the head. -/
def setCode (q t : ℕ) (g : Code) : Code := (q, g.2.1, t :: g.2.2.tail)

theorem toID_setCode (p : ℤ) (q t : ℕ) (g : Code) :
    toID p (setCode q t g) = ⟨q, p, Function.update (toID p g).tape p t⟩ := by
  simp only [toID, setCode]
  congr 1
  funext x
  by_cases hx : x = p
  · subst hx; simp
  · rw [Function.update_of_ne hx]
    by_cases h1 : p ≤ x
    · rw [if_pos h1, if_pos h1]
      obtain ⟨j, hj⟩ : ∃ j : ℕ, x - p = ((j + 1 : ℕ) : ℤ) := ⟨(x - p - 1).toNat, by omega⟩
      rw [hj, Int.toNat_natCast, List.getD_cons_succ]
      rcases g.2.2 with _ | ⟨a, l⟩ <;> simp
    · rw [if_neg h1, if_neg h1]

/-- The head cell of `toID p g`. -/
theorem toID_head (p : ℤ) (g : Code) : (toID p g).tape p = g.2.2.getD 0 0 := by
  simp [toID]

/-- `r` applies to the code `g` (Bool form). -/
def fires (r : Quint) (g : Code) : Bool := r.p == g.1 && r.s == g.2.2.getD 0 0

theorem fires_iff (r : Quint) (p : ℤ) (g : Code) :
    fires r g = true ↔ Applicable r (toID p g) := by
  simp [fires, Applicable, toID]

/-- **The code repair**: the code after the first removed quintuple that applies. -/
def fixCode : List Quint → Code → Code
  | [], g => g
  | r :: H, g => bif fires r g then setCode r.q r.t g else fixCode H g

theorem fixCode_none {H : List Quint} {g : Code} (h : ∀ r ∈ H, fires r g = false) :
    fixCode H g = g := by
  induction H with
  | nil => rfl
  | cons r H ih =>
    simp only [fixCode, h r (by simp), cond_false]
    exact ih fun r' hr' => h r' (by simp [hr'])

theorem fixCode_of_mem {H : List Quint} {g : Code} {r : Quint} (hr : r ∈ H)
    (hm : fires r g = true)
    (huniq : ∀ r' ∈ H, fires r' g = true → r' = r) :
    fixCode H g = setCode r.q r.t g := by
  induction H with
  | nil => simp at hr
  | cons r₀ H ih =>
    simp only [fixCode]
    cases hm₀ : fires r₀ g
    · simp only [cond_false]
      rcases List.mem_cons.mp hr with rfl | hr'
      · rw [hm] at hm₀; cases hm₀
      · exact ih hr' fun r' h' => huniq r' (by simp [h'])
    · simp only [cond_true]
      rw [huniq r₀ (by simp) hm₀]

open Primrec in
theorem fires_primrec (r : Quint) : Primrec (fires r) :=
  Primrec.and.comp (Primrec.beq.comp (const r.p) fst)
    (Primrec.beq.comp (const r.s) ((list_getD 0).comp (snd.comp snd) (const 0)))

open Primrec in
theorem setCode_primrec (q t : ℕ) : Primrec (setCode q t) :=
  pair (const q) (pair (fst.comp snd) (list_cons.comp (const t) (list_tail.comp (snd.comp snd))))

theorem fixCode_primrec : ∀ H : List Quint, Primrec (fixCode H)
  | [] => Primrec.id
  | r :: H => (Primrec.cond (fires_primrec r) (setCode_primrec r.q r.t)
      (fixCode_primrec H)).of_eq fun _ => rfl

/-- The decoder for the table without `H`: repair the code, then decode. -/
def fixD (H : List Quint) (d : Code → Option Code) (g : Code) : Option Code := d (fixCode H g)

theorem fixD_computable (H : List Quint) {d : Code → Option Code} (hd : Computable d) :
    Computable (fixD H d) :=
  hd.comp (fixCode_primrec H).to_comp

/-! ### The main theorem -/

/-- **Removing the halting quintuples keeps the body of `IsUTMStrict`**, with the same encoder
    and the repaired decoder `fixD H d`. -/
theorem strictBody_drop {U H : List Quint} {c : ℕ × Code → Code} {d : Code → Option Code}
    (hD : Deterministic U) (hH : HaltQuints U H)
    (hst : ∀ n a, IsIDOf (tm n) (toID 0 a) → (c (n, a)).1 ∈ states (dropT U H))
    (hsym : ∀ x ∈ symbols U, x = 0 ∨ x ∈ symbols (dropT U H))
    (h : StrictBody U c d) : StrictBody (dropT U H) c (fixD H d) := by
  intro n a ha
  obtain ⟨hID, hhalt, hnon⟩ := h n a ha
  refine ⟨⟨hID.1, hst n a ha, fun x => ?_⟩, fun β hβ => ?_,
    fun hn hh => hnon hn (halts_of_drop hH hh)⟩
  · rcases hID.2.2 x with h0 | hx
    · exact .inl h0
    · rcases hsym _ hx with h0 | h'
      · exact .inl h0
      · exact .inr h'
  obtain ⟨γ, hγ, ⟨g₀, hg₀⟩, hall⟩ := hhalt β hβ
  rcases drop_haltsAt hD hH hγ with ⟨hγ', hU⟩ | ⟨γ', r, hr, hγ', har, rfl⟩
  · -- no removed quintuple was used: the same halting ID, and the repair does nothing
    refine ⟨γ, hγ', ⟨g₀, hg₀⟩, fun g hg => ?_⟩
    have hnm : ∀ r ∈ H, fires r g = false := by
      intro r hr
      cases hm : fires r g
      · rfl
      · exact absurd ((fires_iff r γ.pos g).mp hm) (hg ▸ hU r (hH r hr).1)
    simp only [fixD, fixCode_none hnm]
    exact hall g hg
  · -- the run of `U` ended with the removed quintuple `r` from `γ'`
    have hd0 : shift r.d = 0 := by rw [(hH r hr).2.1]; rfl
    have hpos : (apply r γ').pos = γ'.pos := by simp [apply, hd0]
    have key : ∀ g, toID γ'.pos g = γ' → toID (apply r γ').pos (setCode r.q r.t g) = apply r γ' := by
      intro g hg
      rw [hpos, toID_setCode, hg]
      simp [apply, hd0]
    refine ⟨γ', hγ', ⟨setCode r.p r.s g₀, ?_⟩, fun g hg => ?_⟩
    · -- a code of γ': the code of `apply r γ'` with `r.p` and `r.s` put back
      have h2 : toID γ'.pos g₀ = apply r γ' := by rw [← hpos]; exact hg₀
      rw [toID_setCode, h2]
      obtain ⟨st, pos, tape⟩ := γ'
      obtain ⟨hp, hs⟩ := har
      simp only at hp hs
      simp only [apply, Function.update_idem, hp, hs, Function.update_eq_self]
    · have hm : fires r g = true := (fires_iff r γ'.pos g).mpr (hg ▸ har)
      have huniq : ∀ r' ∈ H, fires r' g = true → r' = r := by
        intro r' hr' hm'
        have ha' := (fires_iff r' γ'.pos g).mp hm'
        rw [hg] at ha'
        exact hD r' (hH r' hr').1 r (hH r hr).1 (ha'.1.trans har.1.symm) (ha'.2.trans har.2.symm)
      simp only [fixD, fixCode_of_mem hr hm huniq]
      exact hall _ (key g hg)

/-- **Removing the halting quintuples keeps `IsUTMStrict`** (for an explicit encoder and decoder
    whose body is known). -/
theorem isUTMStrict_drop {U H : List Quint} {c : ℕ × Code → Code} {d : Code → Option Code}
    (hc : Computable c) (hd : Computable d)
    (hD : Deterministic U) (hH : HaltQuints U H)
    (hst : ∀ n a, IsIDOf (tm n) (toID 0 a) → (c (n, a)).1 ∈ states (dropT U H))
    (hsym : ∀ x ∈ symbols U, x = 0 ∨ x ∈ symbols (dropT U H))
    (h : StrictBody U c d) : IsUTMStrict (dropT U H) :=
  isUTMStrict_of_body hc (fixD_computable H hd) (strictBody_drop hD hH hst hsym h)

/-! ### A toy check of the definitions (kernel `decide`) -/

section Examples

/-- A toy table with one halting quintuple `⟨1, 0, 0, Z, 2⟩` into the pseudo-state 2. -/
private def toyU : List Quint := [⟨0, 0, 1, .R, 1⟩, ⟨1, 1, 1, .L, 0⟩, ⟨1, 0, 0, .Z, 2⟩]
private def toyH : List Quint := [⟨1, 0, 0, .Z, 2⟩]

example : dropT toyU toyH = [⟨0, 0, 1, .R, 1⟩, ⟨1, 1, 1, .L, 0⟩] := by decide
example : HaltQuints toyU toyH := by decide
example : ¬ HaltQuints toyU [⟨0, 0, 1, .R, 1⟩] := by decide
example : fixCode toyH (1, [], []) = (2, [], [0]) := by decide
example : fixCode toyH (1, [], [1]) = (1, [], [1]) := by decide
example : fixCode toyH (0, [], []) = (0, [], []) := by decide

end Examples

end URTM.Univ.DropGen
