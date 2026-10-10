/-
  **L0: Spec's two-sided-tape IDs ↔ finite codes, with the exact final ID** (docs/24 §2 L0, piece P1).

  The code-level system is a zipper on `Code = ℕ × List ℕ × List ℕ` (left part nearest-first,
  right part from the head; blanks beyond the ends), adapted from
  `legacy/small-urtm/lean-meta/URTMMeta/Zipper.lean` (copied, not imported: other package).
  Table look-up is first-match (`look`), so the zipper step is a function for every table; for a
  deterministic table it agrees with Spec's relational `Step`.

  **Normalisation.** Later layers encode a code by numbers (`Σ L_k B^k`), which cannot see
  trailing blanks. Exact readback therefore needs codes without trailing blanks (`norm z = z`).
  The code-level step `cstep` first normalises an unnormalised code (one invisible step:
  `toID p (norm z) = toID p z`) and otherwise performs the zipper step followed by
  normalisation. Its halting codes are the normalised codes on which no rule applies.

  Main statements:
  * `entry` : for a deterministic table, Spec's run from `toID 0 a` is run-level simulated
    (`RunSim`, readback `toID β.pos z = β`) by `cstep` from `a` itself;
  * `entry_tm` : the same for `tm n` under `IsIDOf (tm n) (toID 0 a)`, with the computable
    table `tbl n` in place of `tm n` (the shape of the bridge hypothesis `hin`);
  * `haltsAt_toID_iff` : exact halting ID of Spec in terms of the plain zipper run.
-/
import LeanUniv.ExactSim

namespace URTM.Univ.L0
open URTM URTM.Spec Relation

/-! ### Zipper step -/

/-- Direction number (`L` = 0, `Z` = 1, `R` = 2). -/
def dnum : Dir → ℕ
  | .L => 0
  | .Z => 1
  | .R => 2

/-- Right-hand side of a rule: (written symbol, direction number, next state). -/
def rhs (r : Quint) : ℕ × ℕ × ℕ := (r.t, dnum r.d, r.q)

/-- First-match table look-up. -/
def look : List Quint → ℕ → ℕ → Option (ℕ × ℕ × ℕ)
  | [], _, _ => none
  | r :: T, q, s => if r.p = q ∧ r.s = s then some (rhs r) else look T q s

theorem look_some {T : List Quint} {q s : ℕ} {o : ℕ × ℕ × ℕ} (h : look T q s = some o) :
    ∃ r ∈ T, r.p = q ∧ r.s = s ∧ rhs r = o := by
  induction T with
  | nil => simp [look] at h
  | cons r T ih =>
    unfold look at h
    split_ifs at h with hr
    · exact ⟨r, List.mem_cons_self .., hr.1, hr.2, Option.some.inj h⟩
    · obtain ⟨r', hr', h1, h2, h3⟩ := ih h
      exact ⟨r', List.mem_cons_of_mem _ hr', h1, h2, h3⟩

theorem look_none {T : List Quint} {q s : ℕ} (h : look T q s = none) :
    ∀ r ∈ T, ¬ (r.p = q ∧ r.s = s) := by
  induction T with
  | nil => simp
  | cons r T ih =>
    unfold look at h
    split_ifs at h with hr
    intro r' hr'
    rcases List.mem_cons.mp hr' with rfl | hr'
    · exact hr
    · exact ih h r' hr'

/-- Apply a right-hand side (written symbol, direction number, next state) at the head. -/
def mv (o : ℕ × ℕ × ℕ) (z : Code) : Code :=
  if o.2.1 = 0 then (o.2.2, z.2.1.tail, z.2.1.headD 0 :: o.1 :: z.2.2.tail)
  else if o.2.1 = 1 then (o.2.2, z.2.1, o.1 :: z.2.2.tail)
  else (o.2.2, o.1 :: z.2.1, z.2.2.tail)

/-- Zipper step; `none` when no rule applies. -/
def zstep (T : List Quint) (z : Code) : Option Code :=
  (look T z.1 (z.2.2.headD 0)).map fun o => mv o z

/-! ### Normalisation (trailing blanks) -/

/-- `s :: l`, except that a blank in front of the empty list is dropped. -/
def consT (s : ℕ) (l : List ℕ) : List ℕ := if s = 0 ∧ l = [] then [] else s :: l

/-- Remove trailing blanks. -/
def trim : List ℕ → List ℕ
  | [] => []
  | a :: l => consT a (trim l)

/-- Remove trailing blanks on both sides. -/
def norm (z : Code) : Code := (z.1, trim z.2.1, trim z.2.2)

/-- **Code-level step**: normalise first; on a normalised code, zipper step then normalise. -/
def cstep (T : List Quint) (z : Code) : Option Code :=
  if norm z = z then (zstep T z).map norm else some (norm z)

/-- Code-level step relation. -/
def CStep (T : List Quint) (z z' : Code) : Prop := cstep T z = some z'

/-- Code-level halting: a normalised code on which no rule applies. -/
def CHalt (T : List Quint) (z : Code) : Prop := cstep T z = none

theorem getD_consT (s : ℕ) (l : List ℕ) (k : ℕ) : (consT s l).getD k 0 = (s :: l).getD k 0 := by
  unfold consT
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h; cases k <;> simp
  · rfl

theorem getD_trim (l : List ℕ) (k : ℕ) : (trim l).getD k 0 = l.getD k 0 := by
  induction l generalizing k with
  | nil => rfl
  | cons a l ih =>
    rw [trim, getD_consT]
    cases k with
    | zero => rfl
    | succ k => simp only [List.getD_cons_succ, ih]

theorem mem_consT {s x : ℕ} {l : List ℕ} (h : x ∈ consT s l) : x ∈ s :: l := by
  unfold consT at h; split_ifs at h
  · simp at h
  · exact h

theorem mem_trim {x : ℕ} {l : List ℕ} (h : x ∈ trim l) : x ∈ l := by
  induction l with
  | nil => simp [trim] at h
  | cons a l ih =>
    rcases List.mem_cons.mp (mem_consT h) with rfl | h'
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (ih h')

theorem trim_consT (s : ℕ) (l : List ℕ) (hl : trim l = l) : trim (consT s l) = consT s l := by
  unfold consT; split_ifs <;> simp [trim, consT, *]

theorem trim_trim (l : List ℕ) : trim (trim l) = trim l := by
  induction l with
  | nil => rfl
  | cons a l ih => exact trim_consT a _ ih

theorem norm_norm (z : Code) : norm (norm z) = norm z := by
  simp [norm, trim_trim]

theorem trim_eq_consT (R : List ℕ) : trim R = consT (R.headD 0) (trim R.tail) := by
  cases R with
  | nil => simp [trim, consT]
  | cons a l => rfl

theorem headD_eq_getD (l : List ℕ) : l.headD 0 = l.getD 0 0 := by cases l <;> rfl

theorem headD_trim (l : List ℕ) : (trim l).headD 0 = l.headD 0 := by
  rw [headD_eq_getD, headD_eq_getD, getD_trim]

theorem toID_norm (p : ℤ) (z : Code) : toID p (norm z) = toID p z := by
  simp only [toID, norm, getD_trim]

/-! ### One zipper step = one Spec step -/

theorem getD_tail (l : List ℕ) (n : ℕ) : l.tail.getD n 0 = l.getD (n + 1) 0 := by
  cases l <;> simp

/-- The tape of `toID`. -/
def tapeOf (p : ℤ) (L R : List ℕ) : ℤ → ℕ := fun x =>
  if p ≤ x then R.getD (x - p).toNat 0 else L.getD (p - 1 - x).toNat 0

theorem toID_tape (p : ℤ) (z : Code) : (toID p z).tape = tapeOf p z.2.1 z.2.2 := rfl

theorem tape_Z (p : ℤ) (L R : List ℕ) (t : ℕ) :
    Function.update (tapeOf p L R) p t = tapeOf p L (t :: R.tail) := by
  funext x
  rw [Function.update_apply]
  unfold tapeOf
  by_cases hx : x = p
  · subst hx; simp
  · rw [if_neg hx]
    by_cases hpx : p ≤ x
    · have hk : (x - p).toNat = (x - p - 1).toNat + 1 := by omega
      rw [if_pos hpx, if_pos hpx, hk, List.getD_cons_succ, getD_tail]
    · rw [if_neg hpx, if_neg hpx]

theorem tape_R (p : ℤ) (L R : List ℕ) (t : ℕ) :
    Function.update (tapeOf p L R) p t = tapeOf (p + 1) (t :: L) R.tail := by
  funext x
  rw [Function.update_apply]
  unfold tapeOf
  by_cases hx : x = p
  · subst hx
    rw [if_pos rfl, if_neg (by omega)]
    have : (x + 1 - 1 - x).toNat = 0 := by omega
    rw [this]; rfl
  · rw [if_neg hx]
    by_cases hpx : p ≤ x
    · have hpx' : p + 1 ≤ x := by omega
      have hk : (x - p).toNat = (x - (p + 1)).toNat + 1 := by omega
      rw [if_pos hpx, if_pos hpx', hk, getD_tail]
    · have hpx' : ¬ p + 1 ≤ x := by omega
      have hk : (p + 1 - 1 - x).toNat = (p - 1 - x).toNat + 1 := by omega
      rw [if_neg hpx, if_neg hpx', hk, List.getD_cons_succ]

theorem tape_L (p : ℤ) (L R : List ℕ) (t : ℕ) :
    Function.update (tapeOf p L R) p t = tapeOf (p - 1) L.tail (L.headD 0 :: t :: R.tail) := by
  funext x
  rw [Function.update_apply]
  unfold tapeOf
  by_cases hx : x = p
  · subst hx
    rw [if_pos rfl, if_pos (by omega)]
    have : (x - (x - 1)).toNat = 0 + 1 := by omega
    rw [this, List.getD_cons_succ]; rfl
  · rw [if_neg hx]
    by_cases hpx : p ≤ x
    · have hpx' : p - 1 ≤ x := by omega
      have hk : (x - (p - 1)).toNat = (x - p - 1).toNat + 1 + 1 := by omega
      have hk' : (x - p).toNat = (x - p - 1).toNat + 1 := by omega
      rw [if_pos hpx, if_pos hpx', hk, hk', List.getD_cons_succ, List.getD_cons_succ, getD_tail]
    · by_cases hx1 : x = p - 1
      · subst hx1
        rw [if_neg hpx, if_pos (by omega)]
        have h0 : (p - 1 - (p - 1)).toNat = 0 := by omega
        rw [h0, List.getD_cons_zero, headD_eq_getD]
      · have hpx' : ¬ p - 1 ≤ x := by omega
        have hk : (p - 1 - x).toNat = (p - 1 - 1 - x).toNat + 1 := by omega
        rw [if_neg hpx, if_neg hpx', hk, getD_tail]

/-- Spec's `apply` on `toID p z` is `toID` of the zipper move, with the head moved. -/
theorem apply_toID (r : Quint) (p : ℤ) (z : Code) :
    apply r (toID p z) = toID (p + shift r.d) (mv (rhs r) z) := by
  obtain ⟨st, L, R⟩ := z
  have e : apply r (toID p (st, L, R)) =
      ⟨r.q, p + shift r.d, Function.update (tapeOf p L R) p r.t⟩ := rfl
  rw [e]
  cases hd : r.d with
  | L =>
    simp only [tape_L, shift, mv, rhs, dnum, hd, if_true]
    rw [show p + -1 = p - 1 by omega]; rfl
  | Z =>
    simp only [tape_Z, shift, mv, rhs, dnum, hd, add_zero]
    rfl
  | R =>
    simp only [tape_R, shift, mv, rhs, dnum, hd]
    rfl

theorem read_toID (p : ℤ) (z : Code) : (toID p z).tape (toID p z).pos = z.2.2.headD 0 := by
  simp only [toID, le_refl, if_true, sub_self, Int.toNat_zero]
  exact (headD_eq_getD _).symm

/-- Head displacement of a direction number. -/
def dshift (k : ℕ) : ℤ := if k = 0 then -1 else if k = 1 then 0 else 1

theorem shift_eq (d : Dir) : shift d = dshift (dnum d) := by cases d <;> rfl

theorem step_of_look {T : List Quint} {z : Code} {o : ℕ × ℕ × ℕ}
    (h : look T z.1 (z.2.2.headD 0) = some o) (p : ℤ) :
    Step T (toID p z) (toID (p + dshift o.2.1) (mv o z)) := by
  obtain ⟨r, hr, hp, hs, rfl⟩ := look_some h
  refine ⟨r, hr, ⟨hp, by rw [read_toID]; exact hs⟩, ?_⟩
  rw [apply_toID, shift_eq]; rfl

theorem step_of_zstep {T : List Quint} {z z' : Code} (h : zstep T z = some z') (p : ℤ) :
    ∃ p', Step T (toID p z) (toID p' z') := by
  unfold zstep at h
  cases hl : look T z.1 (z.2.2.headD 0) with
  | none => rw [hl] at h; cases h
  | some o =>
    rw [hl] at h; cases h
    exact ⟨_, step_of_look hl p⟩

theorem halted_of_zstep {T : List Quint} {z : Code} (h : zstep T z = none) (p : ℤ) :
    Halted T (toID p z) := by
  unfold zstep at h
  cases hl : look T z.1 (z.2.2.headD 0) with
  | some o => rw [hl] at h; cases h
  | none =>
    intro r hr ⟨hp, hs⟩
    exact look_none hl r hr ⟨hp, by rw [hs, read_toID]⟩

theorem look_of_step {T : List Quint} (hdet : Deterministic T) {z : Code} {p : ℤ} {c : ID}
    (h : Step T (toID p z) c) :
    ∃ o, look T z.1 (z.2.2.headD 0) = some o ∧ c = toID (p + dshift o.2.1) (mv o z) := by
  obtain ⟨r, hr, ⟨hp, hs⟩, rfl⟩ := h
  rw [read_toID] at hs
  cases hl : look T z.1 (z.2.2.headD 0) with
  | none => exact absurd ⟨hp, hs⟩ (look_none hl r hr)
  | some o =>
    obtain ⟨r', hr', hp', hs', rfl⟩ := look_some hl
    obtain rfl : r' = r := hdet r' hr' r hr (hp'.trans hp.symm) (hs'.trans hs.symm)
    refine ⟨_, rfl, ?_⟩
    rw [apply_toID, shift_eq]; rfl

theorem zstep_of_step {T : List Quint} (hdet : Deterministic T) {z : Code} {p : ℤ} {c : ID}
    (h : Step T (toID p z) c) : ∃ z' p', zstep T z = some z' ∧ c = toID p' z' := by
  obtain ⟨o, hl, rfl⟩ := look_of_step hdet h
  exact ⟨_, _, by simp only [zstep, hl, Option.map_some], rfl⟩

theorem zstep_none_of_halted {T : List Quint} {z : Code} {p : ℤ} (h : Halted T (toID p z)) :
    zstep T z = none := by
  cases hz : zstep T z with
  | none => rfl
  | some z' =>
    obtain ⟨p', r, hr, ha, -⟩ := step_of_zstep hz p
    exact absurd ha (h r hr)

/-! ### The code-level system `cstep` -/

theorem cstep_normal {T : List Quint} {z : Code} (hz : norm z = z) :
    cstep T z = (zstep T z).map norm := by simp [cstep, hz]

theorem cstep_not_normal {T : List Quint} {z : Code} (hz : norm z ≠ z) :
    cstep T z = some (norm z) := by simp [cstep, hz]

theorem chalt_iff {T : List Quint} {z : Code} : CHalt T z ↔ norm z = z ∧ zstep T z = none := by
  unfold CHalt cstep
  split_ifs with h <;> simp [h]

/-- The ID-level relation "`c` is `z` placed somewhere". -/
def At (c : ID) (z : Code) : Prop := ∃ p, c = toID p z

/-- A code step is matched by zero or one Spec step. -/
theorem spec_of_cstep {T : List Quint} {z z' : Code} (h : CStep T z z') {c : ID} (hc : At c z) :
    ∃ c', ReflTransGen (Step T) c c' ∧ At c' z' := by
  obtain ⟨p, rfl⟩ := hc
  unfold CStep cstep at h
  split_ifs at h with hn
  · cases hz : zstep T z with
    | none => rw [hz] at h; cases h
    | some z'' =>
      rw [hz] at h; cases h
      obtain ⟨p', hs⟩ := step_of_zstep hz p
      exact ⟨_, ReflTransGen.single hs, p', (toID_norm p' z'').symm⟩
  · cases h
    exact ⟨_, ReflTransGen.refl, p, (toID_norm p z).symm⟩

/-- A Spec step (deterministic table) is matched by one or two code steps. -/
theorem cstep_of_spec {T : List Quint} (hdet : Deterministic T) {c c' : ID} (h : Step T c c')
    {z : Code} (hc : At c z) : ∃ z', TransGen (CStep T) z z' ∧ At c' z' := by
  obtain ⟨p, rfl⟩ := hc
  have main : ∀ z, norm z = z → Step T (toID p z) c' → ∃ z', CStep T z z' ∧ At c' z' := by
    intro z hn hs
    obtain ⟨z'', p', hz, rfl⟩ := zstep_of_step hdet hs
    exact ⟨norm z'', by simp [CStep, cstep_normal hn, hz], p', (toID_norm p' z'').symm⟩
  by_cases hn : norm z = z
  · obtain ⟨z', h1, h2⟩ := main z hn h
    exact ⟨z', TransGen.single h1, h2⟩
  · rw [← toID_norm] at h
    obtain ⟨z', h1, h2⟩ := main (norm z) (norm_norm z) h
    exact ⟨z', TransGen.head (cstep_not_normal hn) (TransGen.single h1), h2⟩

/-- A halting Spec ID is reached by a halting code in zero or one code steps. -/
theorem chalt_of_halted {T : List Quint} {c : ID} {z : Code} (hc : At c z) (h : Halted T c) :
    ∃ z', ReflTransGen (CStep T) z z' ∧ CHalt T z' ∧ At c z' := by
  obtain ⟨p, rfl⟩ := hc
  by_cases hn : norm z = z
  · exact ⟨z, ReflTransGen.refl, chalt_iff.mpr ⟨hn, zstep_none_of_halted h⟩, p, rfl⟩
  · rw [← toID_norm] at h
    exact ⟨norm z, ReflTransGen.single (cstep_not_normal hn),
      chalt_iff.mpr ⟨norm_norm z, zstep_none_of_halted h⟩, p, (toID_norm p z).symm⟩

theorem halted_of_chalt {T : List Quint} {c : ID} {z : Code} (hc : At c z) (h : CHalt T z) :
    Halted T c := by
  obtain ⟨p, rfl⟩ := hc
  exact halted_of_zstep (chalt_iff.mp h).2 p

/-- **L0 (run level)**: for a deterministic table, Spec's run from `toID 0 a` is simulated by the
    code-level system from `a`, and the halting code reads back to the halting ID exactly
    (`toID β.pos z = β`). -/
theorem entry {T : List Quint} (hdet : Deterministic T) (a : Code) :
    RunSim (Step T) (Halted T) (CStep T) (CHalt T) (fun β z => toID β.pos z = β) (toID 0 a) a := by
  have fwd : ∀ c, ReflTransGen (Step T) (toID 0 a) c → ∃ z, ReflTransGen (CStep T) a z ∧ At c z := by
    intro c h
    induction h with
    | refl => exact ⟨a, ReflTransGen.refl, 0, rfl⟩
    | tail _ hs ih =>
      obtain ⟨z, hz, hcz⟩ := ih
      obtain ⟨z', hz', hc'⟩ := cstep_of_spec hdet hs hcz
      exact ⟨z', hz.trans hz'.to_reflTransGen, hc'⟩
  have bwd : ∀ z, ReflTransGen (CStep T) a z → ∃ c, ReflTransGen (Step T) (toID 0 a) c ∧ At c z := by
    intro z h
    induction h with
    | refl => exact ⟨_, ReflTransGen.refl, 0, rfl⟩
    | tail _ hs ih =>
      obtain ⟨c, hc, hcz⟩ := ih
      obtain ⟨c', hc', hcz'⟩ := spec_of_cstep hs hcz
      exact ⟨c', hc.trans hc', hcz'⟩
  refine ⟨fun β ⟨hβ, hh⟩ => ?_, fun hn ⟨z, hz, hh⟩ => ?_⟩
  · obtain ⟨z, hz, hβz⟩ := fwd β hβ
    obtain ⟨z', hz', hh', p, hp⟩ := chalt_of_halted hβz hh
    exact ⟨z', ⟨hz.trans hz', hh'⟩, by subst hp; rfl⟩
  · obtain ⟨c, hc, hcz⟩ := bwd z hz
    exact hn ⟨c, hc, halted_of_chalt hcz hh⟩

/-! ### Exact halting ID in terms of the plain zipper run -/

/-- Zipper step that also tracks the head position. -/
def pstep (T : List Quint) (pz : ℤ × Code) : Option (ℤ × Code) :=
  (look T pz.2.1 (pz.2.2.2.headD 0)).map fun o => (pz.1 + dshift o.2.1, mv o pz.2)

/-- Positioned zipper step relation. -/
def PStep (T : List Quint) (a b : ℤ × Code) : Prop := pstep T a = some b

theorem pstep_snd {T : List Quint} {p : ℤ} {z : Code} :
    (pstep T (p, z)).map Prod.snd = zstep T z := by
  simp [pstep, zstep, Option.map_map, Function.comp_def]

/-- **`haltsAt_toID_iff`** (docs/24 §2 L0): for a deterministic table, Spec halts from
    `toID p z` at `β` iff the positioned zipper run from `(p, z)` reaches `(p', z')` with no
    applicable rule and `β = toID p' z'`. -/
theorem haltsAt_toID_iff {T : List Quint} (hdet : Deterministic T) (p : ℤ) (z : Code) (β : ID) :
    HaltsAt T (toID p z) β ↔
      ∃ p' z', ReflTransGen (PStep T) (p, z) (p', z') ∧ zstep T z' = none ∧ β = toID p' z' := by
  constructor
  · rintro ⟨h, hh⟩
    suffices ∀ c, ReflTransGen (Step T) (toID p z) c →
        ∃ p' z', ReflTransGen (PStep T) (p, z) (p', z') ∧ c = toID p' z' by
      obtain ⟨p', z', hz, rfl⟩ := this β h
      exact ⟨p', z', hz, zstep_none_of_halted hh, rfl⟩
    intro c h
    induction h with
    | refl => exact ⟨p, z, ReflTransGen.refl, rfl⟩
    | tail _ hs ih =>
      obtain ⟨p', z', hz, rfl⟩ := ih
      obtain ⟨o, hl, rfl⟩ := look_of_step hdet hs
      exact ⟨_, _, hz.tail (by simp only [PStep, pstep, hl, Option.map_some]), rfl⟩
  · rintro ⟨p', z', hz, hn, rfl⟩
    refine ⟨?_, halted_of_zstep hn p'⟩
    suffices ∀ b, ReflTransGen (PStep T) (p, z) b → ReflTransGen (Step T) (toID p z) (toID b.1 b.2)
      from this _ hz
    intro b hb
    induction hb with
    | refl => exact ReflTransGen.refl
    | tail _ hs ih =>
      rename_i b c _
      unfold PStep pstep at hs
      cases hl : look T b.2.1 (b.2.2.2.headD 0) with
      | none => rw [hl] at hs; cases hs
      | some o =>
        rw [hl] at hs; cases hs
        exact ih.tail (step_of_look hl b.1)

/-! ### `tm n` and its computable table -/

/-- The table decoded from `n` (Spec's `tm n` before the determinism test). Computable. -/
def tbl (n : ℕ) : List Quint := (Denumerable.ofNat (List (ℕ × ℕ × ℕ × ℕ × ℕ)) n).map quintOfNat

theorem tm_eq_tbl {n : ℕ} (h : tm n ≠ []) : tm n = tbl n ∧ Deterministic (tbl n) := by
  unfold tm at h ⊢
  dsimp only at h ⊢
  split_ifs at h ⊢ with hd
  · exact ⟨rfl, hd⟩
  · exact absurd rfl h

theorem tm_ne_nil_of_isIDOf {n : ℕ} {c : ID} (h : IsIDOf (tm n) c) : tm n ≠ [] := by
  intro h0
  have := h.2.1
  rw [h0] at this
  simp [states] at this

/-- The symbols of the code `a` are those of the tape of `toID 0 a`. -/
theorem syms_of_isIDOf {T : List Quint} {a : Code} (h : IsIDOf T (toID 0 a)) :
    ∀ x ∈ a.2.1 ++ a.2.2, x = 0 ∨ x ∈ symbols T := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
    have := h.2.2 (-1 - (k : ℤ))
    have e : (toID 0 a).tape (-1 - (k : ℤ)) = a.2.1[k] := by
      simp only [toID]
      rw [if_neg (by omega)]
      have : (0 - 1 - (-1 - (k : ℤ))).toNat = k := by omega
      rw [this, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; rfl
    rwa [e] at this
  · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
    have := h.2.2 (k : ℤ)
    have e : (toID 0 a).tape (k : ℤ) = a.2.2[k] := by
      simp only [toID]
      rw [if_pos (by omega)]
      have : ((k : ℤ) - 0).toNat = k := by omega
      rw [this, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; rfl
    rwa [e] at this

/-- **L0 for `tm n`** (the shape of the bridge hypothesis `hin` of `isUTMStrict_of_chain`,
    without the invariant, which is L1's): for `toID 0 a ∈ ID(tm n)`, the symbols of `a` are
    blank or symbols of `tbl n`, and Spec's run of `tm n` is run-level simulated by the
    code-level system of the computable table `tbl n`. -/
theorem entry_tm (n : ℕ) (a : Code) (h : IsIDOf (tm n) (toID 0 a)) :
    (∀ x ∈ a.2.1 ++ a.2.2, x = 0 ∨ x ∈ symbols (tbl n)) ∧
    RunSim (Step (tm n)) (Halted (tm n)) (CStep (tbl n)) (CHalt (tbl n))
      (fun β z => toID β.pos z = β) (toID 0 a) a := by
  obtain ⟨he, hdet⟩ := tm_eq_tbl (tm_ne_nil_of_isIDOf h)
  rw [he] at h ⊢
  exact ⟨syms_of_isIDOf h, entry hdet a⟩

end URTM.Univ.L0
