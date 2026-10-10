/-
  **Numbering bridge from the zoo's typed machines to Spec** (docs/24 §2 L4 (a)(b), piece P6).

  The zoo's record machines are typed: `T : KState.Machine Q P S` with real states `Q`,
  pseudo (halting) states `P` and symbols `S`, configurations `Cfg Q P S` on `ℤ → S` tapes.
  Spec (`LeanUniv/Spec.lean`) speaks about `List Quint` over `ℕ` with blank `0`.

  * A `Numbering` is a pair of injections `st : Tgt Q P → ℕ`, `sym : S → ℕ`. The Spec table is
    `numT N T = T.map (numRule N)`; configurations map by `numCfg N δ`, which also translates
    the head position by `δ` (the "shift" of L4 (b)): the K-position `x + δ` becomes the Spec
    position `x`.
  * `step_numCfg`: a Spec step from `numCfg N δ c` is exactly the image of a typed step
    (both directions; no hypothesis on the machine).
  * `halted_numCfg`, `reach_numCfg`, `numCfg_reach`, `haltsAt_numCfg_iff`: the same for
    halting and for runs.
  * `numCfg_tp`: a typed configuration whose tape is a finite list `L` (blank outside,
    `CTSH.Sim.tp`) with the head at index `p ≤ |L|` is the Spec ID `toID (p - δ)` of an explicit
    code (window), provided `sym blank = 0`.
  * `isIDOf_toID`: a sufficient, decidable-by-inspection condition for `IsIDOf U (toID p z)`.

  The counts `NStates`/`NSyms` and `Deterministic`/`Reversible` of a concrete `numT N T` are
  checked by `decide +kernel` in the instance files (e.g. `LeanUniv/U10_8.lean`).
  No proof holes and no new axioms (`tests/check.sh`).
-/
import LeanUniv.Spec
import URTM.CTSHSim
import Mathlib.Data.Int.Interval

namespace URTM.Univ.KToSpec
open URTM URTM.KState Relation

variable {Q P S : Type}

/-! ### Numbering -/

/-- Injective numbering of the (real and pseudo) states and of the symbols. -/
structure Numbering (Q P S : Type) where
  st : Tgt Q P → ℕ
  sym : S → ℕ
  st_inj : Function.Injective st
  sym_inj : Function.Injective sym

variable (N : Numbering Q P S)

/-- A typed rule as a Spec quintuple. -/
def numRule (r : Rule Q P S) : Quint :=
  ⟨N.st (.go r.p), N.sym r.s, N.sym r.t, r.d, N.st r.q⟩

/-- The Spec table of a typed machine. -/
def numT (T : Machine Q P S) : List Quint := T.map (numRule N)

/-- A typed configuration as a Spec ID, with the head position translated by `δ`
    (typed position `x + δ` ↦ Spec position `x`). -/
def numCfg (δ : ℤ) (c : Cfg Q P S) : Spec.ID :=
  ⟨N.st c.st, c.pos - δ, fun x => N.sym (c.tape (x + δ))⟩

theorem shift_eq_mv (d : Dir) : Spec.shift d = mv d := by cases d <;> rfl

theorem apply_numRule (δ : ℤ) (r : Rule Q P S) (c : Cfg Q P S) :
    Spec.apply (numRule N r) (numCfg N δ c) = numCfg N δ (fire r c) := by
  simp only [Spec.apply, numRule, numCfg, fire, shift_eq_mv]
  congr 1
  · omega
  · funext x
    simp only [Function.update, upd, eq_rec_constant, dite_eq_ite]
    by_cases h : x = c.pos - δ
    · rw [if_pos h, if_pos (by omega)]
    · rw [if_neg h, if_neg (by omega)]

variable {N}

/-- **Step correspondence.** A Spec step of `numT N T` from the image of `c` is the image of a
    typed step of `T` from `c`, and conversely. -/
theorem step_numCfg (T : Machine Q P S) (δ : ℤ) (c : Cfg Q P S) (γ : Spec.ID) :
    Spec.Step (numT N T) (numCfg N δ c) γ ↔ ∃ c', Step T c c' ∧ γ = numCfg N δ c' := by
  constructor
  · rintro ⟨r', hr', ⟨hp, hs⟩, rfl⟩
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hr'
    simp only [numRule, numCfg, sub_add_cancel] at hp hs
    refine ⟨fire r c, ⟨r, hr, (N.st_inj hp).symm, (N.sym_inj hs).symm, rfl⟩, ?_⟩
    exact apply_numRule N δ r c
  · rintro ⟨c', ⟨r, hr, hst, hs, rfl⟩, rfl⟩
    refine ⟨numRule N r, List.mem_map.mpr ⟨r, hr, rfl⟩, ⟨?_, ?_⟩, (apply_numRule N δ r c).symm⟩
    · simp [numRule, numCfg, hst]
    · simp [numRule, numCfg, hs]

theorem spec_halted_iff (U : List Quint) (γ : Spec.ID) :
    Spec.Halted U γ ↔ ∀ γ', ¬ Spec.Step U γ γ' := by
  constructor
  · rintro h γ' ⟨r, hr, ha, -⟩
    exact h r hr ha
  · intro h r hr ha
    exact h _ ⟨r, hr, ha, rfl⟩

/-- **Halting correspondence.** -/
theorem halted_numCfg (T : Machine Q P S) (δ : ℤ) (c : Cfg Q P S) :
    Spec.Halted (numT N T) (numCfg N δ c) ↔ Halted T c := by
  rw [spec_halted_iff]
  constructor
  · intro h c' hc
    exact h _ ((step_numCfg T δ c _).mpr ⟨c', hc, rfl⟩)
  · intro h γ hγ
    obtain ⟨c', hc, -⟩ := (step_numCfg T δ c γ).mp hγ
    exact h c' hc

/-- Spec runs from an image are images of typed runs. -/
theorem reach_numCfg {T : Machine Q P S} {δ : ℤ} {c : Cfg Q P S} {γ : Spec.ID}
    (h : ReflTransGen (Spec.Step (numT N T)) (numCfg N δ c) γ) :
    ∃ n c', StepN T n c c' ∧ γ = numCfg N δ c' := by
  induction h with
  | refl => exact ⟨0, c, .refl c, rfl⟩
  | tail _ hst ih =>
    obtain ⟨n, c', hn, rfl⟩ := ih
    obtain ⟨c'', hc'', rfl⟩ := (step_numCfg T δ c' _).mp hst
    exact ⟨n + 1, c'', hn.trans (StepN.single hc''), rfl⟩

/-- Typed runs map to Spec runs. -/
theorem numCfg_reach {T : Machine Q P S} {δ : ℤ} {n : ℕ} {c c' : Cfg Q P S}
    (h : StepN T n c c') : ReflTransGen (Spec.Step (numT N T)) (numCfg N δ c) (numCfg N δ c') := by
  induction h with
  | refl => exact .refl
  | cons hs _ ih => exact .head ((step_numCfg T δ _ _).mpr ⟨_, hs, rfl⟩) ih

/-- **Run-level halting correspondence.** -/
theorem haltsAt_numCfg_iff (T : Machine Q P S) (δ : ℤ) (c : Cfg Q P S) (γ : Spec.ID) :
    Spec.HaltsAt (numT N T) (numCfg N δ c) γ ↔
      ∃ n c', HaltsIn T n c c' ∧ γ = numCfg N δ c' := by
  constructor
  · rintro ⟨hr, hh⟩
    obtain ⟨n, c', hn, rfl⟩ := reach_numCfg hr
    exact ⟨n, c', ⟨hn, (halted_numCfg T δ c').mp hh⟩, rfl⟩
  · rintro ⟨n, c', ⟨hn, hh⟩, rfl⟩
    exact ⟨numCfg_reach hn, (halted_numCfg T δ c').mpr hh⟩

theorem halts_numCfg_iff (T : Machine Q P S) (δ : ℤ) (c : Cfg Q P S) :
    Spec.Halts (numT N T) (numCfg N δ c) ↔ ∃ n c', HaltsIn T n c c' := by
  constructor
  · rintro ⟨γ, hγ⟩
    obtain ⟨n, c', h, -⟩ := (haltsAt_numCfg_iff T δ c γ).mp hγ
    exact ⟨n, c', h⟩
  · rintro ⟨n, c', h⟩
    exact ⟨_, (haltsAt_numCfg_iff T δ c _).mpr ⟨n, c', h, rfl⟩⟩

/-! ### Finite list tapes as Spec codes (the window, L4 (b)) -/

/-- The code of a list tape `L` (index `i` at typed position `i`) with the head at index `p`:
    the left part nearest-first, the right part from the head. -/
def window (s : ℕ) (L : List ℕ) (p : ℕ) : Spec.Code := (s, (L.take p).reverse, L.drop p)

theorem getD_map_zero {α : Type} (f : α → ℕ) (bk : α) (hbk : f bk = 0) (l : List α) (i : ℕ) :
    (l.map f).getD i 0 = f (l.getD i bk) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> simp [hbk]

/-- **Window lemma.** A typed configuration with a finite list tape (blank `bk` outside) and
    the head at index `p ≤ |L|` is, after numbering with `sym bk = 0` and translating by `δ`,
    the Spec ID `toID (p - δ)` of the window code. -/
theorem numCfg_tp (bk : S) (hbk : N.sym bk = 0) (δ : ℤ) (q : Tgt Q P) (L : List S) (p : ℕ)
    (hp : p ≤ L.length) :
    numCfg N δ ⟨q, p, CTSH.Sim.tp bk L⟩ = Spec.toID ((p : ℤ) - δ) (window (N.st q) (L.map N.sym) p) := by
  simp only [numCfg, Spec.toID, window]
  congr 1
  funext x
  split_ifs with h
  · -- right of (or at) the head
    obtain ⟨j, hj⟩ : ∃ j : ℕ, x + δ = (j : ℤ) := ⟨(x + δ).toNat, by omega⟩
    rw [hj, CTSH.Sim.tp_ofNat, ← List.map_drop, getD_map_zero N.sym bk hbk]
    congr 1
    simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]
    congr 2
    omega
  · rw [← List.map_take, ← List.map_reverse, getD_map_zero N.sym bk hbk]
    congr 1
    rcases lt_or_ge (x + δ) 0 with hneg | hnn
    · obtain ⟨k, hk⟩ : ∃ k : ℕ, x + δ = Int.negSucc k := ⟨(-(x + δ) - 1).toNat, by omega⟩
      rw [hk]
      simp only [CTSH.Sim.tp, List.getD_eq_getElem?_getD]
      rw [List.getElem?_eq_none (by simp; omega)]
      rfl
    · obtain ⟨j, hj⟩ : ∃ j : ℕ, x + δ = (j : ℤ) := ⟨(x + δ).toNat, by omega⟩
      rw [hj, CTSH.Sim.tp_ofNat]
      have hjp : j < p := by omega
      simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_reverse (by simp; omega)]
      simp only [List.length_take, Nat.min_eq_left hp, List.getElem?_take]
      rw [if_pos (by omega)]
      congr 2
      omega

/-! ### `IsIDOf` of a code -/

theorem toID_finite (p : ℤ) (z : Spec.Code) : (Spec.toID p z).Finite := by
  apply (Set.finite_Icc (p - z.2.1.length) (p + z.2.2.length)).subset
  intro x hx
  simp only [Set.mem_setOf_eq, Spec.toID] at hx
  simp only [Set.mem_Icc]
  split_ifs at hx with h
  · refine ⟨by omega, ?_⟩
    by_contra hc
    exact hx (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl)
  · refine ⟨?_, by omega⟩
    by_contra hc
    exact hx (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl)

/-- A sufficient condition for `IsIDOf U (toID p z)`: the state is a state of `U` and every
    entry of the two lists is blank or a symbol of `U`. -/
theorem isIDOf_toID (U : List Quint) (p : ℤ) (z : Spec.Code) (hst : z.1 ∈ Spec.states U)
    (hsym : ∀ a ∈ z.2.1 ++ z.2.2, a = 0 ∨ a ∈ Spec.symbols U) : Spec.IsIDOf U (Spec.toID p z) := by
  refine ⟨toID_finite p z, hst, fun x => ?_⟩
  simp only [Spec.toID]
  have key : ∀ (l : List ℕ) (i : ℕ), (∀ a ∈ l, a = 0 ∨ a ∈ Spec.symbols U) →
      l.getD i 0 = 0 ∨ l.getD i 0 ∈ Spec.symbols U := by
    intro l i hl
    rw [List.getD_eq_getElem?_getD]
    cases h : l[i]? with
    | none => exact .inl rfl
    | some a => exact hl a (List.mem_of_getElem? h)
  split_ifs
  · exact key _ _ fun a ha => hsym a (List.mem_append_right _ ha)
  · exact key _ _ fun a ha => hsym a (List.mem_append_left _ ha)

end URTM.Univ.KToSpec
