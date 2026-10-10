/-
  **Merging symbols (Kudlek–Rogozhin) preserves universality** (results/symmerge-2026-10-04).

  Kudlek–Rogozhin (DLT 2001, p. 313) identified two symbols of Rogozhin's UTM(3,10) and obtained
  UTM(3,9). This file states and proves the general form of that step for Spec tables
  (`LeanUniv/Spec.lean`, `LeanUniv/Strict.lean`), in the words of Spec only:

  * `mapQ h U`: the table `U` with `h` applied to the read and the written symbol of every
    quintuple (states and directions unchanged).
  * `IsUTMStrictHalt U F`: `IsUTMStrict U` (Morita Def. 7.1, strict form) with one more clause
    for the encoder `c`: **every** halting ID `γ` that `U` reaches from an encoded initial ID
    `c (n, a)` is in a state without outgoing quintuples of `U` (a pseudo-state), and every cell
    of `γ` holds a symbol of the list `F`.
  * `isUTMStrict_mapQ`: if `IsUTMStrictHalt U F`, the merged table `mapQ h U` is deterministic,
    `h` and its section `s` are primitive recursive with `h 0 = 0`, `s 0 = 0`, and
    `s (h a) = a` for every `a ∈ F`, then `IsUTMStrict (mapQ h U)`.
    The encoder is `c` followed by `h` on every entry, the decoder is `s` on every entry
    followed by `d`.

  Why each hypothesis (they are all used):
  * Each step of `U` maps to a step of `mapQ h U` (the image quintuple applies to the image ID),
    with no condition. So runs of `U` map to runs of `mapQ h U`.
  * Halting: the halting ID `γ` of `U` is in a pseudo-state, so no quintuple of `mapQ h U`
    (whose source states are those of `U`) applies to its image. A halting ID in a real state
    could be woken up by the merge; the clause of `IsUTMStrictHalt` excludes it.
  * Non-halting: when `U` does not halt, every ID it reaches has an applicable quintuple, hence
    so does its image; since `mapQ h U` is deterministic, its run from the image of the initial
    ID is the image of the run of `U`, and never halts.
  * Output: a code `g` of the image of `γ` gives the code `s ∘ g` of `γ` itself, because the
    cells of `γ` are in `F` and `s ∘ h = id` there (`s 0 = 0` keeps the blank outside the code).
-/
import LeanUniv.DropGen

namespace URTM.Univ.SymMerge
open URTM URTM.Spec Relation

/-! ### The maps -/

/-- The quintuple `r` with `h` applied to its read and written symbols. -/
def mapR (h : ℕ → ℕ) (r : Quint) : Quint := ⟨r.p, h r.s, h r.t, r.d, r.q⟩

/-- **The merged table**: `h` applied to the read and written symbols of every quintuple. -/
def mapQ (h : ℕ → ℕ) (U : List Quint) : List Quint := U.map (mapR h)

/-- `h` applied to every cell of an ID. -/
def mapID (h : ℕ → ℕ) (c : ID) : ID := ⟨c.st, c.pos, fun x => h (c.tape x)⟩

/-- `h` applied to every entry of a code. -/
def mapCode (h : ℕ → ℕ) (z : Code) : Code := (z.1, z.2.1.map h, z.2.2.map h)

/-- **A finite symbol map**: `a ↦ b` for the first pair `(a, b)` of `pairs` with first entry
    `a`, and the identity elsewhere. -/
def symMap (pairs : List (ℕ × ℕ)) (a : ℕ) : ℕ :=
  pairs.foldr (fun p r => if a = p.1 then p.2 else r) a

/-! ### The strong form of Def. 7.1 -/

/-- **`IsUTMStrict` plus the shape of the halting IDs**: as `IsUTMStrict U`, and in addition every
    halting ID `γ` reached from an encoded initial ID `c (n, a)` is in a state that is not the
    source state of any quintuple of `U`, and every cell of `γ` holds a symbol of `F`. -/
def IsUTMStrictHalt (U : List Quint) (F : List ℕ) : Prop :=
  ∃ (c : ℕ × Code → Code) (d : Code → Option Code), Computable c ∧ Computable d ∧
    ∀ n a, IsIDOf (tm n) (toID 0 a) →
      IsIDOf U (toID 0 (c (n, a))) ∧
      (∀ β, HaltsAt (tm n) (toID 0 a) β →
        ∃ γ, HaltsAt U (toID 0 (c (n, a))) γ ∧ (∃ g, toID γ.pos g = γ) ∧
          ∀ g, toID γ.pos g = γ → ∃ b, d g = some b ∧ toID β.pos b = β) ∧
      (¬ Halts (tm n) (toID 0 a) → ¬ Halts U (toID 0 (c (n, a)))) ∧
      (∀ γ, HaltsAt U (toID 0 (c (n, a))) γ → γ.st ∉ U.map Quint.p ∧ ∀ x, γ.tape x ∈ F)

/-- The strong form implies `IsUTMStrict` (it only adds a conjunct). -/
theorem IsUTMStrictHalt.isUTMStrict {U : List Quint} {F : List ℕ} (h : IsUTMStrictHalt U F) :
    IsUTMStrict U := by
  obtain ⟨c, d, hc, hd, h⟩ := h
  exact ⟨c, d, hc, hd, fun n a ha => ⟨(h n a ha).1, (h n a ha).2.1, (h n a ha).2.2.1⟩⟩

/-- The strong form from the body of `IsUTMStrict` and the clause on the halting IDs. -/
theorem isUTMStrictHalt_of_body {U : List Quint} {F : List ℕ} {c : ℕ × Code → Code}
    {d : Code → Option Code} (hc : Computable c) (hd : Computable d)
    (hb : DropGen.StrictBody U c d)
    (hP : ∀ n a, IsIDOf (tm n) (toID 0 a) → ∀ γ, HaltsAt U (toID 0 (c (n, a))) γ →
      γ.st ∉ U.map Quint.p ∧ ∀ x, γ.tape x ∈ F) :
    IsUTMStrictHalt U F :=
  ⟨c, d, hc, hd, fun n a ha => ⟨(hb n a ha).1, (hb n a ha).2.1, (hb n a ha).2.2, hP n a ha⟩⟩

/-! ### Codes and IDs -/

theorem getD_map_zero (h : ℕ → ℕ) (h0 : h 0 = 0) (l : List ℕ) (i : ℕ) :
    (l.map h).getD i 0 = h (l.getD i 0) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> simp [h0]

theorem toID_mapCode {h : ℕ → ℕ} (h0 : h 0 = 0) (p : ℤ) (z : Code) :
    toID p (mapCode h z) = mapID h (toID p z) := by
  simp only [toID, mapCode, mapID]
  congr 1
  funext x
  split_ifs <;> exact getD_map_zero h h0 _ _

theorem mapID_mapID {h s : ℕ → ℕ} {F : List ℕ} (hsh : ∀ a ∈ F, s (h a) = a) (γ : ID)
    (hF : ∀ x, γ.tape x ∈ F) : mapID s (mapID h γ) = γ := by
  obtain ⟨st, pos, tape⟩ := γ
  simp only [mapID, ID.mk.injEq, true_and]
  funext x
  exact hsh _ (hF x)

open Primrec in
theorem mapCode_primrec {h : ℕ → ℕ} (hh : Primrec h) : Primrec (mapCode h) :=
  pair fst (pair (list_map (fst.comp snd) (hh.comp snd).to₂)
    (list_map (snd.comp snd) (hh.comp snd).to₂))

theorem symMap_cons (p : ℕ × ℕ) (pairs : List (ℕ × ℕ)) (a : ℕ) :
    symMap (p :: pairs) a = if a = p.1 then p.2 else symMap pairs a := rfl

/-- A finite symbol map is primitive recursive. -/
theorem symMap_primrec (pairs : List (ℕ × ℕ)) : Primrec (symMap pairs) := by
  induction pairs with
  | nil => exact Primrec.id
  | cons p pairs ih =>
    exact (Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const p.1)) (Primrec.const p.2)
      ih).of_eq fun a => (symMap_cons p pairs a).symm

/-! ### Steps and runs -/

theorem mem_mapQ {h : ℕ → ℕ} {U : List Quint} {r' : Quint} :
    r' ∈ mapQ h U ↔ ∃ r ∈ U, mapR h r = r' := List.mem_map

theorem applicable_map (h : ℕ → ℕ) {r : Quint} {c : ID} (ha : Applicable r c) :
    Applicable (mapR h r) (mapID h c) :=
  ⟨ha.1, congrArg h ha.2⟩

theorem apply_map (h : ℕ → ℕ) (r : Quint) (c : ID) :
    apply (mapR h r) (mapID h c) = mapID h (apply r c) := by
  simp only [apply, mapR, mapID, ID.mk.injEq, true_and]
  funext x
  by_cases hx : x = c.pos
  · subst hx; simp
  · simp [Function.update_of_ne hx]

theorem step_map (h : ℕ → ℕ) {U : List Quint} {c c' : ID} (hs : Step U c c') :
    Step (mapQ h U) (mapID h c) (mapID h c') := by
  obtain ⟨r, hr, ha, rfl⟩ := hs
  exact ⟨mapR h r, mem_mapQ.mpr ⟨r, hr, rfl⟩, applicable_map h ha, (apply_map h r c).symm⟩

theorem reach_map (h : ℕ → ℕ) {U : List Quint} {c c' : ID} (hr : ReflTransGen (Step U) c c') :
    ReflTransGen (Step (mapQ h U)) (mapID h c) (mapID h c') := by
  induction hr with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail (step_map h hs)

/-- **Halting**: the image of an ID in a pseudo-state of `U` is a halting ID of `mapQ h U`. -/
theorem halted_map (h : ℕ → ℕ) {U : List Quint} {γ : ID} (hst : γ.st ∉ U.map Quint.p) :
    Halted (mapQ h U) (mapID h γ) := by
  intro r' hr' ha
  obtain ⟨r, hr, rfl⟩ := mem_mapQ.mp hr'
  exact hst (List.mem_map.mpr ⟨r, hr, ha.1⟩)

theorem step_det {V : List Quint} (hV : Deterministic V) {c c₁ c₂ : ID} (h₁ : Step V c c₁)
    (h₂ : Step V c c₂) : c₁ = c₂ := by
  obtain ⟨r₁, hr₁, ha₁, rfl⟩ := h₁
  obtain ⟨r₂, hr₂, ha₂, rfl⟩ := h₂
  rw [hV r₁ hr₁ r₂ hr₂ (ha₁.1.trans ha₂.1.symm) (ha₁.2.trans ha₂.2.symm)]

theorem not_halted_of_not_halts {U : List Quint} {ι c : ID} (hn : ¬ Halts U ι)
    (hc : ReflTransGen (Step U) ι c) : ∃ r ∈ U, Applicable r c := by
  by_contra hne
  exact hn ⟨c, hc, fun r hr ha => hne ⟨r, hr, ha⟩⟩

/-- **Non-halting**: if `U` does not halt from `ι` and `mapQ h U` is deterministic, then
    `mapQ h U` does not halt from the image of `ι`. -/
theorem not_halts_map (h : ℕ → ℕ) {U : List Quint} (hdet : Deterministic (mapQ h U)) {ι : ID}
    (hn : ¬ Halts U ι) : ¬ Halts (mapQ h U) (mapID h ι) := by
  rintro ⟨δ, hr, hδ⟩
  -- every ID reached by the merged table is the image of an ID reached by `U`
  have key : ∀ e, ReflTransGen (Step (mapQ h U)) (mapID h ι) e →
      ∃ c, ReflTransGen (Step U) ι c ∧ e = mapID h c := by
    intro e he
    induction he with
    | refl => exact ⟨ι, .refl, rfl⟩
    | tail _ hbe ih =>
      obtain ⟨c, hc, rfl⟩ := ih
      obtain ⟨r, hr, ha⟩ := not_halted_of_not_halts hn hc
      have hs : Step U c (apply r c) := ⟨r, hr, ha, rfl⟩
      exact ⟨apply r c, hc.tail hs, step_det hdet hbe (step_map h hs)⟩
  obtain ⟨c, hc, rfl⟩ := key δ hr
  obtain ⟨r, hr', ha⟩ := not_halted_of_not_halts hn hc
  exact hδ (mapR h r) (mem_mapQ.mpr ⟨r, hr', rfl⟩) (applicable_map h ha)

/-! ### IDs of the merged table -/

theorem states_mapQ (h : ℕ → ℕ) (U : List Quint) : states (mapQ h U) = states U := by
  simp only [states, mapQ, List.flatMap_map, mapR]

theorem mem_symbols_mapQ (h : ℕ → ℕ) {U : List Quint} {a : ℕ} (ha : a ∈ symbols U) :
    h a ∈ symbols (mapQ h U) := by
  simp only [symbols, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at ha ⊢
  obtain ⟨r, hr, rfl | rfl⟩ := ha
  · exact ⟨mapR h r, mem_mapQ.mpr ⟨r, hr, rfl⟩, .inl rfl⟩
  · exact ⟨mapR h r, mem_mapQ.mpr ⟨r, hr, rfl⟩, .inr rfl⟩

theorem isIDOf_map {h : ℕ → ℕ} (h0 : h 0 = 0) {U : List Quint} {c : ID} (hc : IsIDOf U c) :
    IsIDOf (mapQ h U) (mapID h c) := by
  obtain ⟨hfin, hst, hsym⟩ := hc
  refine ⟨hfin.subset fun x hx => ?_, by rw [states_mapQ]; exact hst, fun x => ?_⟩
  · intro h'
    exact hx (by simp only [mapID, h', h0])
  · rcases hsym x with h' | h'
    · exact .inl (by simp only [mapID, h', h0])
    · exact .inr (mem_symbols_mapQ h h')

/-! ### The theorem -/

/-- **Merging symbols preserves universality.** If `U` is a UTM in the strict sense of Morita
    Def. 7.1 whose halting IDs (from the encoded initial IDs) are in pseudo-states and hold only
    symbols of `F` (`IsUTMStrictHalt U F`), the merged table `mapQ h U` is deterministic, and
    `h`, `s` are primitive recursive with `h 0 = 0`, `s 0 = 0` and `s ∘ h = id` on `F`, then
    `mapQ h U` is a UTM in the strict sense of Def. 7.1. -/
theorem isUTMStrict_mapQ {U : List Quint} {F : List ℕ} {h s : ℕ → ℕ}
    (hU : IsUTMStrictHalt U F) (hdet : Deterministic (mapQ h U))
    (hh : Primrec h) (hs : Primrec s) (h0 : h 0 = 0) (s0 : s 0 = 0)
    (hsh : ∀ a ∈ F, s (h a) = a) : IsUTMStrict (mapQ h U) := by
  obtain ⟨c, d, hc, hd, hb⟩ := hU
  refine ⟨fun p => mapCode h (c p), fun g => d (mapCode s g),
    (mapCode_primrec hh).to_comp.comp hc, hd.comp (mapCode_primrec hs).to_comp,
    fun n a ha => ?_⟩
  obtain ⟨hID, hhalt, hnon, hP⟩ := hb n a ha
  rw [toID_mapCode h0]
  refine ⟨isIDOf_map h0 hID, fun β hβ => ?_, fun hn => not_halts_map h hdet (hnon hn)⟩
  obtain ⟨γ, hγ, ⟨g₀, hg₀⟩, hall⟩ := hhalt β hβ
  obtain ⟨hst, hF⟩ := hP γ hγ
  refine ⟨mapID h γ, ⟨reach_map h hγ.1, halted_map h hst⟩,
    ⟨mapCode h g₀, show toID γ.pos (mapCode h g₀) = mapID h γ by rw [toID_mapCode h0, hg₀]⟩,
    fun g hg => ?_⟩
  refine hall (mapCode s g) ?_
  have hg' : toID γ.pos g = mapID h γ := hg
  rw [toID_mapCode s0, hg', mapID_mapID hsh γ hF]

end URTM.Univ.SymMerge
