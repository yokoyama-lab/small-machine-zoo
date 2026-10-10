/-
  **Symbol-count formulas of the conversions, as theorems** (the formulas of the paper's section on
  the construction of the new points).

  `syms M` lists the symbols read or written by the rules of a machine `M` (`KState.Machine`), and
  `nsym M` is the number of distinct ones. For a machine without a rule that reads or writes the
  blank, the numbered table of `M` has `Spec.NSyms = nsym M` (checked for the concrete machines in
  `FinalFormulas`).

  * Block conversion `KStateBlocks.bconv T sp qs ss` (`bconv_nsym`, `bconv_nsym_le`,
    `mem_syms_bconv`): the symbols are exactly `pl s` for the symbols `s` of `T` and `ctr i s` for
    `i ∈ bV` and `s ∈ bX i`, where `bX i` is the set of symbols `s` such that some state `q` reads
    `s` or is entered writing `s`, and `i` lies between the sentinel `σ_q` of the block of `q` and the
    value `v q` (both ends included); `bV` is the set of `i` with `bX i` nonempty. Hence
    `nsym (bconv …) = nsym T + Σ_{i ∈ bV} |bX i| ≤ (|bV| + 1)·n`.
  No hypothesis on `T` beyond the enumerations: the statement is about the syntax of the table.
  * Morita's 4-state conversion `Conv55.conv` (`conv55_nsym`): exactly `(2m + 1)·n`.
  * The direction-split 4-state conversion `KState.conv` (`kconv_nsym`): exactly `(m + 1)·n`.
  * The ε-reversed 4-state conversion `KStateEps.econv` (`econv_nsym_le`): at most `(max(m₊, m₋) + 1)·n`.
  * Morita's 2-symbol conversion with 2-bit codes `Conv54.conv` (`conv54_nst`): `nst = |D_go| + m + P_r + P_w`
    states (`nst` counts the current states of the rules, as `Spec.NStates`).
  * Morita's 3-state conversion of a 1WU machine `Conv510.conv` (`conv510_nsym`): exactly `N(2M − 1)`.
  * The improved 3-state conversion `Conv3S.conv` / `convM` (`conv3S_nsym_formula`, `convM3S_nsym_formula`):
    at most `1 + n + (m₋n + |G|)(n + 1) + n(n + 2 + |R| + |G|) + (n + 2)` when the counter bound is `need3`.
  mathlib's `List.dedup` is used for counting; no `sorry`, no new axiom, no `native_decide`.
-/
import Mathlib.Data.List.Dedup
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.Ring
import Aesop
import URTM.KStateBlocks
import URTM.Conv54
import URTM.Conv510
import URTM.Conv3S

namespace URTM.Univ.SymCount

set_option linter.unusedSectionVars false

open URTM (Dir)
open URTM.KState (Machine Rule KSym Tgt dir)
open URTM.KStateEps (readB writeB)
open URTM.KStateBlocks (BSpec bconv brule1 shut sgq path path1 fwdv bwdv mem_dedupL mem_brule1 mem_shut
  shut_r2 shut_r3 shut_r4 shut_r5 mem_path_le mem_path_gt mem_path1_le mem_path1_gt)

/-! ## 1. Symbols of a machine -/

section Gen
variable {Q P S : Type}

/-- The symbols read or written by the rules (with repetitions). -/
def syms (M : Machine Q P S) : List S := M.flatMap (fun r => [r.s, r.t])

/-- **Number of symbols**: the number of distinct symbols read or written by the rules. -/
def nsym [DecidableEq S] (M : Machine Q P S) : ℕ := (syms M).dedup.length

theorem mem_syms {M : Machine Q P S} {x : S} : x ∈ syms M ↔ ∃ r ∈ M, x = r.s ∨ x = r.t := by
  simp [syms, List.mem_flatMap]

theorem s_mem_syms {M : Machine Q P S} {r : Rule Q P S} (h : r ∈ M) : r.s ∈ syms M :=
  mem_syms.2 ⟨r, h, .inl rfl⟩

theorem t_mem_syms {M : Machine Q P S} {r : Rule Q P S} (h : r ∈ M) : r.t ∈ syms M :=
  mem_syms.2 ⟨r, h, .inr rfl⟩

/-- A duplicate-free list with the same members as `syms M` has length `nsym M`. -/
theorem nsym_eq_of [DecidableEq S] {M : Machine Q P S} {L : List S} (hL : L.Nodup)
    (h : ∀ x, x ∈ syms M ↔ x ∈ L) : nsym M = L.length := by
  unfold nsym
  refine List.Perm.length_eq ((List.perm_ext_iff_of_nodup (List.nodup_dedup _) hL).2 ?_)
  intro x; rw [List.mem_dedup]; exact h x

/-- If every symbol of `M` is in `L`, then `nsym M ≤ |L|`. -/
theorem nsym_le_of [DecidableEq S] {M : Machine Q P S} {L : List S} (h : ∀ x ∈ syms M, x ∈ L) :
    nsym M ≤ L.length := by
  unfold nsym
  exact (List.subperm_of_subset (List.nodup_dedup _) (fun x hx => h x (List.mem_dedup.1 hx))).length_le

end Gen

/-! ## 2. The symbols of `T` among an enumeration -/

section Base
variable {Q P S : Type} [DecidableEq S]

/-- The symbols of `T`, in the order of `ss`. -/
def symL (T : Machine Q P S) (ss : List S) : List S :=
  ss.filter (fun s => T.any (fun r => decide (r.s = s) || decide (r.t = s)))

theorem mem_symL {T : Machine Q P S} {ss : List S} (hS : ∀ s, s ∈ ss) {s : S} :
    s ∈ symL T ss ↔ s ∈ syms T := by
  simp only [symL, List.mem_filter, List.any_eq_true, Bool.or_eq_true, decide_eq_true_eq, mem_syms]
  constructor
  · rintro ⟨-, r, hr, h⟩; exact ⟨r, hr, h.elim (fun e => .inl e.symm) (fun e => .inr e.symm)⟩
  · rintro ⟨r, hr, h⟩; exact ⟨hS s, r, hr, h.elim (fun e => .inl e.symm) (fun e => .inr e.symm)⟩

theorem nsym_eq_symL {T : Machine Q P S} {ss : List S} (hS : ∀ s, s ∈ ss) (hss : ss.Nodup) :
    nsym T = (symL T ss).length :=
  nsym_eq_of (hss.filter _) (fun _ => (mem_symL hS).symm)

theorem nsym_le_card {T : Machine Q P S} {ss : List S} (hS : ∀ s, s ∈ ss) (hss : ss.Nodup) :
    nsym T ≤ ss.length := by
  rw [nsym_eq_symL hS hss]; exact List.length_filter_le _ _

end Base

/-! ## 3. Block conversion -/

section Blocks
variable {Q P S : Type} [DecidableEq Q] [DecidableEq P] [DecidableEq S] {k : ℕ}

/-- `q` reads `s` or is entered writing `s`. -/
def touch (T : Machine Q P S) (q : Q) (s : S) : Bool := readB T q s || writeB T q s

/-- `i` lies between the sentinel of the block of `q` and the value of `q` (both included). -/
def inI (T : Machine Q P S) (sp : BSpec Q k) (q : Q) (i : ℕ) : Bool :=
  decide (min (sgq T sp q) (sp.v q) ≤ i ∧ i ≤ max (sgq T sp q) (sp.v q))

/-- **`X_i`**: the symbols that occur with counter value `i` (in the order of `ss`). -/
def bX (T : Machine Q P S) (sp : BSpec Q k) (qs : List Q) (ss : List S) (i : ℕ) : List S :=
  ss.filter (fun s => qs.any (fun q => touch T q s && inI T sp q i))

/-- An upper bound of the counter values: the largest sentinel or value. -/
def bTop (T : Machine Q P S) (sp : BSpec Q k) (qs : List Q) : ℕ :=
  qs.foldr (fun q a => max (max (sgq T sp q) (sp.v q)) a) 0

/-- **`V`**: the counter values used (increasing). -/
def bV (T : Machine Q P S) (sp : BSpec Q k) (qs : List Q) (ss : List S) : List ℕ :=
  (List.range (bTop T sp qs + 1)).filter (fun i => !(bX T sp qs ss i).isEmpty)

theorem le_bTop {T : Machine Q P S} {sp : BSpec Q k} :
    ∀ {qs : List Q} {q : Q}, q ∈ qs → max (sgq T sp q) (sp.v q) ≤ bTop T sp qs
  | [], _, h => absurd h List.not_mem_nil
  | a :: l, q, h => by
    simp only [bTop, List.foldr_cons] at *
    rcases List.mem_cons.1 h with rfl | h
    · exact le_max_left _ _
    · exact le_trans (le_bTop h) (le_max_right _ _)

variable {T : Machine Q P S} {sp : BSpec Q k} {qs : List Q} {ss : List S}

theorem mem_bX (hQ : ∀ q, q ∈ qs) (hS : ∀ s, s ∈ ss) {i : ℕ} {s : S} :
    s ∈ bX T sp qs ss i ↔ ∃ q, touch T q s = true ∧ inI T sp q i = true := by
  simp only [bX, List.mem_filter, List.any_eq_true, Bool.and_eq_true]
  exact ⟨fun ⟨_, q, _, h⟩ => ⟨q, h⟩, fun ⟨q, h⟩ => ⟨hS s, q, hQ q, h⟩⟩

theorem mem_bV_bX (hQ : ∀ q, q ∈ qs) (hS : ∀ s, s ∈ ss) {i : ℕ} {s : S} :
    (i ∈ bV T sp qs ss ∧ s ∈ bX T sp qs ss i) ↔ ∃ q, touch T q s = true ∧ inI T sp q i = true := by
  constructor
  · exact fun h => (mem_bX hQ hS).1 h.2
  · intro h
    refine ⟨?_, (mem_bX hQ hS).2 h⟩
    obtain ⟨q, -, hi⟩ := id h
    simp only [inI, decide_eq_true_eq] at hi
    have := le_bTop (T := T) (sp := sp) (hQ q)
    simp only [bV, List.mem_filter, List.mem_range, Bool.not_eq_true', List.isEmpty_eq_false_iff]
    refine ⟨by omega, List.ne_nil_of_mem ((mem_bX hQ hS).2 h)⟩

/-- Symbols of the converted table, described through `T` and `sp`. -/
def Good (T : Machine Q P S) (sp : BSpec Q k) (x : KSym S) : Prop :=
  (∃ s, x = .pl s ∧ s ∈ syms T) ∨
  (∃ i s, x = .ctr i s ∧ ∃ q, touch T q s = true ∧ inI T sp q i = true)

theorem readB_true {q : Q} {s : S} : readB T q s = true ↔ ∃ r ∈ T, r.p = q ∧ r.s = s := by
  simp [readB, List.any_eq_true]

theorem writeB_true {q : Q} {t : S} : writeB T q t = true ↔ ∃ r ∈ T, r.q = .go q ∧ r.t = t := by
  simp [writeB, List.any_eq_true]

theorem syms_of_readB {q : Q} {s : S} (h : readB T q s = true) : s ∈ syms T := by
  obtain ⟨r, hr, -, rfl⟩ := readB_true.1 h; exact s_mem_syms hr

theorem syms_of_writeB {q : Q} {t : S} (h : writeB T q t = true) : t ∈ syms T := by
  obtain ⟨r, hr, -, rfl⟩ := writeB_true.1 h; exact t_mem_syms hr

theorem inI_v (q : Q) : inI T sp q (sp.v q) = true := by
  simp only [inI, decide_eq_true_eq]; omega

theorem inI_sg (q : Q) : inI T sp q (sgq T sp q) = true := by
  simp only [inI, decide_eq_true_eq]; omega

theorem inI_path {q : Q} {j : ℕ} (h : j ∈ path (sgq T sp q) (sp.v q)) :
    inI T sp q j = true ∧ inI T sp q (fwdv (sgq T sp q) (sp.v q) j) = true := by
  simp only [inI, decide_eq_true_eq, fwdv]
  by_cases hab : sgq T sp q ≤ sp.v q
  · have := (mem_path_le hab).1 h; rw [if_pos hab]; omega
  · have := (mem_path_gt (by omega)).1 h; rw [if_neg hab]; omega

theorem inI_path1 {q : Q} {i : ℕ} (h : i ∈ path1 (sgq T sp q) (sp.v q)) :
    inI T sp q i = true ∧ inI T sp q (bwdv (sgq T sp q) (sp.v q) i) = true := by
  simp only [inI, decide_eq_true_eq, bwdv]
  by_cases hab : sgq T sp q ≤ sp.v q
  · have := (mem_path1_le hab).1 h; rw [if_pos hab]; omega
  · have := (mem_path1_gt (by omega)).1 h; rw [if_neg hab]; omega

/-- Every value of the interval is the sentinel or on `path1`. -/
theorem inI_cases {q : Q} {i : ℕ} (h : inI T sp q i = true) :
    i = sgq T sp q ∨ i ∈ path1 (sgq T sp q) (sp.v q) := by
  simp only [inI, decide_eq_true_eq] at h
  by_cases hab : sgq T sp q ≤ sp.v q
  · rw [mem_path1_le hab]; omega
  · rw [mem_path1_gt (by omega)]; omega

/-- A value on `path1` is the image under `fwdv` of a value on `path`. -/
theorem path1_fwdv {a b i : ℕ} (h : i ∈ path1 a b) : bwdv a b i ∈ path a b ∧ fwdv a b (bwdv a b i) = i := by
  unfold fwdv bwdv
  by_cases hab : a ≤ b
  · have := (mem_path1_le hab).1 h; rw [if_pos hab, if_pos hab, mem_path_le hab]; omega
  · have := (mem_path1_gt (by omega)).1 h; rw [if_neg hab, if_neg hab, mem_path_gt (by omega)]; omega

theorem syms_shut {q : Q} {x : KSym S} {ρ : Rule (Fin k) P (KSym S)} (hρ : ρ ∈ shut T sp ss q)
    (hx : x = ρ.s ∨ x = ρ.t) : Good T sp x := by
  unfold shut at hρ
  simp only [List.mem_append, List.mem_flatMap, List.mem_filter, List.mem_cons, List.mem_map] at hρ
  rcases hρ with ⟨s₂, ⟨-, hr⟩, h | ⟨j, hj, h⟩⟩ | ⟨t, ⟨-, hw⟩, h | ⟨i, hi, h⟩⟩
  · subst h
    rcases hx with rfl | rfl
    · exact .inl ⟨s₂, rfl, syms_of_readB hr⟩
    · exact .inr ⟨_, s₂, rfl, q, by simp [touch, hr], inI_sg q⟩
  · subst h
    have := inI_path (T := T) (sp := sp) hj
    rcases hx with rfl | rfl
    · exact .inr ⟨_, s₂, rfl, q, by simp [touch, hr], this.1⟩
    · exact .inr ⟨_, s₂, rfl, q, by simp [touch, hr], this.2⟩
  · subst h
    rcases hx with rfl | rfl
    · exact .inr ⟨_, t, rfl, q, by simp [touch, hw], inI_sg q⟩
    · exact .inl ⟨t, rfl, syms_of_writeB hw⟩
  · subst h
    have := inI_path1 (T := T) (sp := sp) hi
    rcases hx with rfl | rfl
    · exact .inr ⟨_, t, rfl, q, by simp [touch, hw], this.1⟩
    · exact .inr ⟨_, t, rfl, q, by simp [touch, hw], this.2⟩

theorem syms_brule1 {r : Rule Q P S} (hr : r ∈ T) {x : KSym S}
    (hx : x = (brule1 T sp r).s ∨ x = (brule1 T sp r).t) : Good T sp x := by
  obtain ⟨p, s, t, d, q⟩ := r
  cases q with
  | go q =>
    simp only [brule1] at hx
    rcases hx with rfl | rfl
    · exact .inr ⟨_, s, rfl, p, by simp [touch, readB_true]; exact .inl ⟨_, hr, rfl, rfl⟩, inI_v p⟩
    · exact .inr ⟨_, t, rfl, q, by simp [touch, writeB_true]; exact .inr ⟨_, hr, rfl, rfl⟩, inI_v q⟩
  | halt h =>
    simp only [brule1] at hx
    rcases hx with rfl | rfl
    · exact .inr ⟨_, s, rfl, p, by simp [touch, readB_true]; exact .inl ⟨_, hr, rfl, rfl⟩, inI_v p⟩
    · exact .inl ⟨t, rfl, t_mem_syms hr⟩

/-- **The symbols of the block conversion, described through `T` and `sp`.** -/
theorem mem_syms_bconv_good (hQ : ∀ q, q ∈ qs) (hS : ∀ s, s ∈ ss) {x : KSym S} :
    x ∈ syms (bconv T sp qs ss) ↔ Good T sp x := by
  constructor
  · intro h
    obtain ⟨ρ, hρ, hx⟩ := mem_syms.1 h
    rcases List.mem_append.1 (mem_dedupL.1 hρ) with h1 | h1
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 h1
      exact syms_brule1 hr hx
    · obtain ⟨q, -, hq⟩ := List.mem_flatMap.1 h1
      exact syms_shut hq hx
  · rintro (⟨s, rfl, hs⟩ | ⟨i, s, rfl, q, hq, hi⟩)
    · obtain ⟨r, hr, hs⟩ := mem_syms.1 hs
      rcases hs with rfl | rfl
      · exact s_mem_syms (mem_shut hQ (shut_r2 (sp := sp) hS (readB_true.2 ⟨r, hr, rfl, rfl⟩)))
      · obtain ⟨p, s, t, d, q⟩ := r
        cases q with
        | go q => exact t_mem_syms (mem_shut hQ (shut_r4 (sp := sp) hS (writeB_true.2 ⟨_, hr, rfl, rfl⟩)))
        | halt h =>
          have := t_mem_syms (mem_brule1 (sp := sp) (qs := qs) (ss := ss) hr)
          simpa [brule1] using this
    · simp only [touch, Bool.or_eq_true] at hq
      rcases inI_cases hi with rfl | hi1
      · rcases hq with hr | hw
        · exact t_mem_syms (mem_shut hQ (shut_r2 (sp := sp) hS hr))
        · exact s_mem_syms (mem_shut hQ (shut_r4 (sp := sp) hS hw))
      · rcases hq with hr | hw
        · obtain ⟨hj, he⟩ := path1_fwdv hi1
          have := t_mem_syms (mem_shut hQ (shut_r5 (sp := sp) hS hr hj))
          simpa [he] using this
        · exact s_mem_syms (mem_shut hQ (shut_r3 (sp := sp) hS hw hi1))

/-- **The symbols of the block conversion**: `pl s` for the symbols `s` of `T`, and `ctr i s` for
    `i ∈ V` and `s ∈ X_i`. -/
theorem mem_syms_bconv (hQ : ∀ q, q ∈ qs) (hS : ∀ s, s ∈ ss) {x : KSym S} :
    x ∈ syms (bconv T sp qs ss) ↔
      (∃ s, x = .pl s ∧ s ∈ syms T) ∨
      (∃ i s, x = .ctr i s ∧ i ∈ bV T sp qs ss ∧ s ∈ bX T sp qs ss i) := by
  rw [mem_syms_bconv_good hQ hS, Good]
  simp only [mem_bV_bX hQ hS]

/-- The list `pl s` (s a symbol of `T`) followed by the `ctr i s` (`i ∈ V`, `s ∈ X_i`). -/
def bList (T : Machine Q P S) (sp : BSpec Q k) (qs : List Q) (ss : List S) : List (KSym S) :=
  (symL T ss).map .pl ++ (bV T sp qs ss).flatMap (fun i => (bX T sp qs ss i).map (.ctr i))

theorem bList_nodup (hss : ss.Nodup) : (bList T sp qs ss).Nodup := by
  unfold bList
  refine List.nodup_append.2 ⟨?_, ?_, ?_⟩
  · exact (hss.filter _).map (fun _ _ h => by injection h)
  · refine List.nodup_flatMap.2 ⟨fun i _ => (hss.filter _).map (fun _ _ h => by injection h), ?_⟩
    refine (List.nodup_range.filter _).pairwise_of_forall_ne (fun a _ b _ hab => ?_)
    simp only [Function.onFun]
    rw [List.disjoint_left]
    intro x hx hy
    obtain ⟨s, -, rfl⟩ := List.mem_map.1 hx
    obtain ⟨s', -, h⟩ := List.mem_map.1 hy
    injection h with h1; exact hab h1.symm
  · intro x hx y hy hxy
    subst hxy
    obtain ⟨s, -, rfl⟩ := List.mem_map.1 hx
    obtain ⟨i, -, h⟩ := List.mem_flatMap.1 hy
    obtain ⟨s', -, h⟩ := List.mem_map.1 h
    cases h

theorem bList_length :
    (bList T sp qs ss).length =
      (symL T ss).length + ((bV T sp qs ss).map (fun i => (bX T sp qs ss i).length)).sum := by
  simp [bList, List.length_flatMap]

/-- **Symbol count of the block conversion**: `nsym (bconv T sp qs ss) = n_T + Σ_{i ∈ V} |X_i|`,
    where `n_T = nsym T` is the number of symbols of `T`. -/
theorem bconv_nsym (hQ : ∀ q, q ∈ qs) (hS : ∀ s, s ∈ ss) (hss : ss.Nodup) :
    nsym (bconv T sp qs ss) =
      nsym T + ((bV T sp qs ss).map (fun i => (bX T sp qs ss i).length)).sum := by
  rw [nsym_eq_symL hS hss, ← bList_length]
  refine nsym_eq_of (bList_nodup hss) (fun x => ?_)
  rw [mem_syms_bconv hQ hS]
  simp only [bList, List.mem_append, List.mem_map, List.mem_flatMap, mem_symL hS]
  constructor
  · rintro (⟨s, rfl, hs⟩ | ⟨i, s, rfl, hi, hs⟩)
    · exact .inl ⟨s, hs, rfl⟩
    · exact .inr ⟨i, hi, s, hs, rfl⟩
  · rintro (⟨s, hs, rfl⟩ | ⟨i, hi, s, hs, rfl⟩)
    · exact .inl ⟨s, rfl, hs⟩
    · exact .inr ⟨i, s, rfl, hi, hs⟩

theorem sum_le_mul {l : List ℕ} {f : ℕ → ℕ} {c : ℕ} (h : ∀ i ∈ l, f i ≤ c) :
    (l.map f).sum ≤ l.length * c := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h1 := h a List.mem_cons_self
    have h2 := ih (fun i hi => h i (List.mem_cons_of_mem _ hi))
    rw [Nat.succ_mul]; omega

/-- **Upper bound**: `nsym (bconv T sp qs ss) ≤ (|V| + 1)·n` with `n = |ss|`. -/
theorem bconv_nsym_le (hQ : ∀ q, q ∈ qs) (hS : ∀ s, s ∈ ss) (hss : ss.Nodup) :
    nsym (bconv T sp qs ss) ≤ ((bV T sp qs ss).length + 1) * ss.length := by
  rw [bconv_nsym hQ hS hss, Nat.succ_mul]
  have h1 := nsym_le_card (T := T) hS hss
  have h2 := sum_le_mul (l := bV T sp qs ss) (f := fun i => (bX T sp qs ss i).length) (c := ss.length)
    (fun i _ => List.length_filter_le _ _)
  omega

end Blocks

/-! ## 4. Helpers for duplicate-free lists -/

section Helpers

theorem nodup_flatMap_owner {α β : Type} {l : List α} {f : α → List β} (own : β → α) (hl : l.Nodup)
    (hf : ∀ a ∈ l, (f a).Nodup) (ho : ∀ a ∈ l, ∀ x ∈ f a, own x = a) : (l.flatMap f).Nodup := by
  refine List.nodup_flatMap.2 ⟨hf, hl.pairwise_of_forall_ne fun a ha b hb hab => ?_⟩
  simp only [Function.onFun]
  rw [List.disjoint_left]
  intro x hx hy
  exact hab ((ho a ha x hx).symm.trans (ho b hb x hy))

theorem sum_map_const {α : Type} (l : List α) (c : ℕ) : (l.map fun _ => c).sum = l.length * c := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; ring

theorem syms_mono {Q P S : Type} {M M' : Machine Q P S} (h : ∀ r ∈ M, r ∈ M') {x : S} (hx : x ∈ syms M) :
    x ∈ syms M' := by
  obtain ⟨r, hr, e⟩ := mem_syms.1 hx; exact mem_syms.2 ⟨r, h r hr, e⟩

/-- **Number of states**: the number of distinct current states of the rules (pseudo-states have
    no rules and are not counted, as in `Spec.NStates`). -/
def nst {Q P S : Type} [DecidableEq Q] (M : Machine Q P S) : ℕ := (M.map (·.p)).dedup.length

theorem nst_eq_of {Q P S : Type} [DecidableEq Q] {M : Machine Q P S} {L : List Q} (hL : L.Nodup)
    (h : ∀ x, (∃ r ∈ M, r.p = x) ↔ x ∈ L) : nst M = L.length := by
  unfold nst
  refine List.Perm.length_eq ((List.perm_ext_iff_of_nodup (List.nodup_dedup _) hL).2 ?_)
  intro x; rw [List.mem_dedup, List.mem_map]; exact h x

theorem nsym_congr {Q P S : Type} [DecidableEq S] {M M' : Machine Q P S} (h₁ : ∀ r ∈ M, r ∈ M')
    (h₂ : ∀ r ∈ M', r ∈ M) : nsym M = nsym M' := by
  unfold nsym
  refine List.Perm.length_eq ((List.perm_ext_iff_of_nodup (List.nodup_dedup _) (List.nodup_dedup _)).2 ?_)
  intro x
  simp only [List.mem_dedup]
  exact ⟨syms_mono h₁, syms_mono h₂⟩

theorem nst_congr {Q P S : Type} [DecidableEq Q] {M M' : Machine Q P S} (h₁ : ∀ r ∈ M, r ∈ M')
    (h₂ : ∀ r ∈ M', r ∈ M) : nst M = nst M' := by
  unfold nst
  refine List.Perm.length_eq ((List.perm_ext_iff_of_nodup (List.nodup_dedup _) (List.nodup_dedup _)).2 ?_)
  intro x
  simp only [List.mem_dedup, List.mem_map]
  exact ⟨fun ⟨r, hr, e⟩ => ⟨r, h₁ r hr, e⟩, fun ⟨r, hr, e⟩ => ⟨r, h₂ r hr, e⟩⟩

end Helpers

/-! ## 5. Morita's 4-state conversion (Theorem 5.5, `Conv55.conv`): `(2m + 1)·n` -/

section Conv55
open URTM.Conv55 (FSym)
variable {Q P S : Type} [DecidableEq S]

/-- The symbols `u`, `[u, k↑]`, `[u, k↓]` for `u ∈ ss` and `k < m`. -/
def fList (m : ℕ) (ss : List S) : List (FSym S) :=
  ss.flatMap (fun u => FSym.pl u :: ((List.range m).map (FSym.up u) ++ (List.range m).map (FSym.dn u)))

def fOwn : FSym S → S
  | .pl u => u
  | .up u _ => u
  | .dn u _ => u

theorem fList_length (m : ℕ) (ss : List S) : (fList m ss).length = (2 * m + 1) * ss.length := by
  simp only [fList, List.length_flatMap, List.length_cons, List.length_append, List.length_map,
    List.length_range, sum_map_const]
  ring

theorem fList_nodup {m : ℕ} {ss : List S} (hss : ss.Nodup) : (fList m ss).Nodup := by
  refine nodup_flatMap_owner fOwn hss (fun u _ => ?_) (fun u _ x hx => ?_)
  · refine List.nodup_cons.2 ⟨by simp, List.Nodup.append ?_ ?_ ?_⟩
    · exact List.nodup_range.map (fun _ _ h => by injection h)
    · exact List.nodup_range.map (fun _ _ h => by injection h)
    · rw [List.disjoint_left]; simp
  · simp only [List.mem_cons, List.mem_append, List.mem_map, List.mem_range] at hx
    rcases hx with rfl | ⟨k, -, rfl⟩ | ⟨k, -, rfl⟩ <;> rfl

theorem mem_fList {m : ℕ} {ss : List S} (hS : ∀ s, s ∈ ss) {x : FSym S} :
    x ∈ fList m ss ↔ (∃ u, x = .pl u) ∨ (∃ u k, k < m ∧ x = .up u k) ∨ (∃ u k, k < m ∧ x = .dn u k) := by
  simp only [fList, List.mem_flatMap, List.mem_cons, List.mem_append, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨u, -, rfl | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩⟩
    · exact .inl ⟨u, rfl⟩
    · exact .inr (.inl ⟨u, k, hk, rfl⟩)
    · exact .inr (.inr ⟨u, k, hk, rfl⟩)
  · rintro (⟨u, rfl⟩ | ⟨u, k, hk, rfl⟩ | ⟨u, k, hk, rfl⟩)
    · exact ⟨u, hS u, .inl rfl⟩
    · exact ⟨u, hS u, .inr (.inl ⟨k, hk, rfl⟩)⟩
    · exact ⟨u, hS u, .inr (.inr ⟨k, hk, rfl⟩)⟩

/-- **Morita's 4-state conversion has exactly `(2m + 1)·n` symbols** (`m` the number range of the
    states, `idx q < m`; `n = |ss|`). For the 10 states of (10,8): 21·8 = 168. -/
theorem conv55_nsym {T : Machine Q P S} {idx : Q → ℕ} {m : ℕ} {side : Q → Bool} {ss : List S}
    (hS : ∀ s, s ∈ ss) (hss : ss.Nodup) (hidx : ∀ q, idx q < m) (hm : 1 ≤ m) :
    nsym (URTM.Conv55.conv T idx m side ss) = (2 * m + 1) * ss.length := by
  rw [← fList_length m ss]
  refine nsym_eq_of (fList_nodup hss) (fun x => ⟨fun h => ?_, fun h => ?_⟩)
  · obtain ⟨ρ, hρ, hx⟩ := mem_syms.1 h
    rcases List.mem_append.1 hρ with h1 | h1
    · obtain ⟨r, -, he⟩ := List.mem_filterMap.1 h1
      obtain ⟨p, s, t, d, q⟩ := r
      cases q with
      | go q =>
        simp only [URTM.Conv55.convRule, Option.some.injEq] at he
        subst he
        have := hidx p; have := hidx q
        rcases hx with rfl | rfl <;> simp [mem_fList hS] <;> omega
      | halt h => simp [URTM.Conv55.convRule] at he
    · obtain ⟨u, -, h2⟩ := List.mem_flatMap.1 h1
      simp only [URTM.Conv55.symRules, List.mem_append, List.mem_cons, List.mem_flatMap, List.mem_range,
        List.not_mem_nil, or_false] at h2
      rcases h2 with (h | h | h | h) | ⟨k, hk, h | h | h | h⟩ <;> subst h <;>
        rcases hx with rfl | rfl <;> simp [mem_fList hS] <;> omega
  · rcases (mem_fList hS).1 h with ⟨u, rfl⟩ | ⟨u, k, hk, rfl⟩ | ⟨u, k, hk, rfl⟩
    · exact s_mem_syms (URTM.Conv55.mem_sym (T := T) (idx := idx) (side := side) (hS u)
        (ρ := (⟨.R0, .pl u, .up u 0, .L, .go .L0⟩ : Rule URTM.Conv55.FSt P (FSym S))) (by simp [URTM.Conv55.symRules]))
    · rcases k with _ | k
      · exact t_mem_syms (URTM.Conv55.mem_sym (T := T) (idx := idx) (side := side) (hS u)
          (ρ := (⟨.R0, .pl u, .up u 0, .L, .go .L0⟩ : Rule URTM.Conv55.FSt P (FSym S))) (by simp [URTM.Conv55.symRules]))
      · exact t_mem_syms (URTM.Conv55.mem_cnt (T := T) (idx := idx) (side := side) (hS u) (k := k) hk
          (ρ := (⟨.R1, .up u k, .up u (k + 1), .L, .go .L0⟩ : Rule URTM.Conv55.FSt P (FSym S))) (by simp))
    · rcases k with _ | k
      · exact s_mem_syms (URTM.Conv55.mem_sym (T := T) (idx := idx) (side := side) (hS u)
          (ρ := (⟨.L0, .dn u 0, .pl u, .R, .go .R0⟩ : Rule URTM.Conv55.FSt P (FSym S))) (by simp [URTM.Conv55.symRules]))
      · exact s_mem_syms (URTM.Conv55.mem_cnt (T := T) (idx := idx) (side := side) (hS u) (k := k) hk
          (ρ := (⟨.L0, .dn u (k + 1), .dn u k, .R, .go .R1⟩ : Rule URTM.Conv55.FSt P (FSym S))) (by simp))

end Conv55

/-! ## 6. The 4-state conversion with direction-split ranges (`KState.conv`): `(m + 1)·n` -/

section KConv
open URTM.KState (KSt lo hi shuttle symUniverse ctrs ZeroShiftHalts)
variable {Q P S : Type} [DecidableEq Q] [DecidableEq P] [DecidableEq S]

theorem mem_ctrs_iff {ss : List S} {x : KSym S} :
    ∀ {m : ℕ}, x ∈ ctrs ss m ↔ ∃ i s, x = .ctr i s ∧ 1 ≤ i ∧ i ≤ m ∧ s ∈ ss
  | 0 => by simp [ctrs]
  | m + 1 => by
    simp only [ctrs, List.mem_append, List.mem_map, mem_ctrs_iff (m := m)]
    constructor
    · rintro (⟨i, s, rfl, h1, h2, hs⟩ | ⟨s, hs, rfl⟩)
      · exact ⟨i, s, rfl, h1, by omega, hs⟩
      · exact ⟨m + 1, s, rfl, by omega, le_refl _, hs⟩
    · rintro ⟨i, s, rfl, h1, h2, hs⟩
      by_cases h : i = m + 1
      · exact .inr ⟨s, hs, by rw [h]⟩
      · exact .inl ⟨i, s, rfl, h1, by omega, hs⟩

theorem ctrs_nodup {ss : List S} (hss : ss.Nodup) : ∀ {m : ℕ}, (ctrs ss m).Nodup
  | 0 => List.nodup_nil
  | m + 1 => by
    refine List.Nodup.append (ctrs_nodup hss) (hss.map (fun _ _ h => by injection h)) ?_
    rw [List.disjoint_left]
    intro x hx hy
    obtain ⟨i, s, rfl, -, h2, -⟩ := mem_ctrs_iff.1 hx
    obtain ⟨s', -, h⟩ := List.mem_map.1 hy
    injection h with h; omega

theorem symUniverse_nodup {m : ℕ} {ss : List S} (hss : ss.Nodup) : (symUniverse m ss).Nodup := by
  refine List.Nodup.append (hss.map (fun _ _ h => by injection h)) (ctrs_nodup hss) ?_
  rw [List.disjoint_left]
  intro x hx hy
  obtain ⟨s, -, rfl⟩ := List.mem_map.1 hx
  obtain ⟨i, s', h, -⟩ := mem_ctrs_iff.1 hy
  cases h

theorem shuttle_syms {mp mm : ℕ} {ss : List S} {d : Dir} (hle : lo mp d ≤ hi mp mm d) {x : S} (hx : x ∈ ss) :
    KSym.pl x ∈ syms (shuttle (P := P) mp mm ss d) ∧
    ∀ i, lo mp d ≤ i → i ≤ hi mp mm d → KSym.ctr i x ∈ syms (shuttle (P := P) mp mm ss d) := by
  have r2 : (⟨URTM.KState.H d, .pl x, .ctr (lo mp d) x, URTM.KState.opp d, .go (URTM.KState.A (URTM.KState.opp d))⟩ :
      Rule KSt P (KSym S)) ∈ shuttle mp mm ss d := by
    unfold shuttle; rw [if_pos hle]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map.2 ⟨x, hx, rfl⟩)))
  refine ⟨s_mem_syms r2, fun i h1 h2 => ?_⟩
  by_cases hi : i = lo mp d
  · subst hi; exact t_mem_syms r2
  · have r3 : (⟨URTM.KState.A (URTM.KState.opp d), .ctr i x, .ctr (i - 1) x, d, .go (URTM.KState.A d)⟩ :
        Rule KSt P (KSym S)) ∈ shuttle mp mm ss d := by
      unfold shuttle; rw [if_pos hle]
      refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ?_))
      exact List.mem_flatMap.2 ⟨i, List.mem_range'_1.2 ⟨by omega, by omega⟩, List.mem_map.2 ⟨x, hx, rfl⟩⟩
    exact s_mem_syms r3

/-- **Upper bound** `(m + 1)·n` for `KState.conv` (`m = |qs|`). -/
theorem kconv_nsym_le {T : Machine Q P S} {qs : List Q} {ss : List S} (hW : ZeroShiftHalts T)
    (hQ : ∀ q, q ∈ qs) (hS : ∀ s, s ∈ ss) :
    nsym (URTM.KState.conv T qs ss) ≤ (qs.length + 1) * ss.length := by
  rw [← URTM.KState.symUniverse_length]
  refine nsym_le_of (fun x hx => ?_)
  obtain ⟨ρ, hρ, rfl | rfl⟩ := mem_syms.1 hx
  · exact (URTM.KState.conv_symbols_mem hW hQ hS hρ).1
  · exact (URTM.KState.conv_symbols_mem hW hQ hS hρ).2

/-- **`KState.conv` has exactly `(m + 1)·n` symbols** (`m = |qs| ≥ 1`, `n = |ss|`). For (10,8): 88. -/
theorem kconv_nsym {T : Machine Q P S} {qs : List Q} {ss : List S} (hW : ZeroShiftHalts T)
    (hQ : ∀ q, q ∈ qs) (hS : ∀ s, s ∈ ss) (hss : ss.Nodup) (hm : 1 ≤ qs.length) :
    nsym (URTM.KState.conv T qs ss) = (qs.length + 1) * ss.length := by
  rw [← URTM.KState.symUniverse_length]
  refine nsym_eq_of (symUniverse_nodup hss) (fun x => ⟨fun hx => ?_, fun hx => ?_⟩)
  · obtain ⟨ρ, hρ, rfl | rfl⟩ := mem_syms.1 hx
    · exact (URTM.KState.conv_symbols_mem hW hQ hS hρ).1
    · exact (URTM.KState.conv_symbols_mem hW hQ hS hρ).2
  · have hpm := URTM.KState.plus_minus_length (T := T) qs
    set mp := (URTM.KState.plusList T qs).length
    set mm := (URTM.KState.minusList T qs).length
    have subR : ∀ r ∈ shuttle (P := P) mp mm ss .R, r ∈ URTM.KState.conv T qs ss := fun r hr =>
      List.mem_append_left _ (List.mem_append_right _ hr)
    have subL : ∀ r ∈ shuttle (P := P) mp mm ss .L, r ∈ URTM.KState.conv T qs ss := fun r hr =>
      List.mem_append_right _ hr
    unfold symUniverse at hx
    rcases List.mem_append.1 hx with hx | hx
    · obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hx
      by_cases h : 1 ≤ mp
      · exact syms_mono subR (shuttle_syms (d := .R) (by simpa using h) hs).1
      · exact syms_mono subL (shuttle_syms (d := .L) (by simp; omega) hs).1
    · obtain ⟨i, s, rfl, h1, h2, hs⟩ := mem_ctrs_iff.1 hx
      by_cases h : i ≤ mp
      · exact syms_mono subR ((shuttle_syms (d := .R) (by simp; omega) hs).2 i (by simpa using h1) (by simpa using h))
      · exact syms_mono subL ((shuttle_syms (d := .L) (by simp; omega) hs).2 i (by simp; omega) (by simp; omega))

end KConv

/-! ## 7. The ε-reversed 4-state conversion (`KStateEps.econv`): `(max(m₊, m₋) + 1)·n` -/

section EConv
open URTM.KState (ZeroShiftHalts Reversible plusList minusList)
variable {Q P S : Type} [DecidableEq Q] [DecidableEq P] [DecidableEq S]

/-- **Upper bound** `(max(m₊, m₋) + 1)·n` for `KStateEps.econv` (only the syntactically needed
    rules are kept, so the bound need not be attained). For (10,8): 48, attained. -/
theorem econv_nsym_le {T : Machine Q P S} {qs : List Q} {ss : List S} (hW : ZeroShiftHalts T)
    (hR : Reversible T) (hQ : ∀ q, q ∈ qs) (hS : ∀ s, s ∈ ss) :
    nsym (URTM.KStateEps.econv T qs ss) ≤
      (max (plusList T qs).length (minusList T qs).length + 1) * ss.length := by
  rw [← URTM.KStateEps.symUniverse_emax_length (T := T) qs ss]
  refine nsym_le_of (fun x hx => ?_)
  obtain ⟨ρ, hρ, rfl | rfl⟩ := mem_syms.1 hx
  · exact (URTM.KStateEps.econvWith_symbols_mem hW hR (URTM.KStateEps.ecanon_good hQ) hS hρ).1
  · exact (URTM.KStateEps.econvWith_symbols_mem hW hR (URTM.KStateEps.ecanon_good hQ) hS hρ).2

end EConv

/-! ## 8. Morita's 2-symbol conversion (Theorem 5.4, 2-bit codes, `Conv54.conv`): `2m + P_r + P_w` -/

section Conv54
open URTM.Conv54 (BSt)
variable {Q P S : Type} [DecidableEq Q]

/-- `p` has a rule into a real state. -/
def goFrom (T : Machine Q P S) (p : Q) : Bool := T.any (fun r => decide (r.p = p) && r.q.isGo)

/-- `p` has a rule into a real state reading a symbol whose code starts with `x`. -/
def rdPre (T : Machine Q P S) (code : S → Bool × Bool) (p : Q) (x : Bool) : Bool :=
  T.any (fun r => decide (r.p = p) && r.q.isGo && decide ((code r.s).1 = x))

/-- `r` enters the real state `q`. -/
def isTo (r : Rule Q P S) (q : Q) : Bool :=
  match r.q with
  | .go q' => decide (q' = q)
  | .halt _ => false

/-- some rule enters `q` writing a symbol whose code starts with `x`. -/
def wrPre (T : Machine Q P S) (code : S → Bool × Bool) (q : Q) (x : Bool) : Bool :=
  T.any (fun r => isTo r q && decide ((code r.t).1 = x))

def pairs (qs : List Q) : List (Q × Bool) := qs.flatMap (fun q => [(q, false), (q, true)])

/-- The states with a rule into a real state. -/
def dGo (T : Machine Q P S) (qs : List Q) : List Q := qs.filter (goFrom T)
/-- **`P_r`**: the pairs (state, first bit of a code it reads). -/
def pR (T : Machine Q P S) (code : S → Bool × Bool) (qs : List Q) : List (Q × Bool) :=
  (pairs qs).filter (fun a => rdPre T code a.1 a.2)
/-- **`P_w`**: the pairs (state, first bit of a code written when entering it). -/
def pW (T : Machine Q P S) (code : S → Bool × Bool) (qs : List Q) : List (Q × Bool) :=
  (pairs qs).filter (fun a => wrPre T code a.1 a.2)

def sList (T : Machine Q P S) (code : S → Bool × Bool) (qs : List Q) : List (BSt Q) :=
  (dGo T qs).map .r ++ (pR T code qs).map (fun a => .r1 a.1 a.2) ++
    (pW T code qs).map (fun a => .w a.1 a.2) ++ qs.map .s

theorem mem_pairs {qs : List Q} {a : Q × Bool} : a ∈ pairs qs ↔ a.1 ∈ qs := by
  obtain ⟨q, b⟩ := a
  cases b <;> simp [pairs]

theorem pairs_nodup {qs : List Q} (hqs : qs.Nodup) : (pairs qs).Nodup :=
  nodup_flatMap_owner Prod.fst hqs (fun _ _ => by simp) (fun a _ x hx => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> rfl)

theorem sList_nodup {T : Machine Q P S} {code : S → Bool × Bool} {qs : List Q} (hqs : qs.Nodup) :
    (sList T code qs).Nodup := by
  have hp := pairs_nodup hqs
  unfold sList
  refine List.Nodup.append (List.Nodup.append (List.Nodup.append ?_ ?_ ?_) ?_ ?_) ?_ ?_
  · exact (hqs.filter _).map (fun _ _ h => by injection h)
  · exact (hp.filter _).map (fun a b h => by injection h with h1 h2; exact Prod.ext h1 h2)
  · rw [List.disjoint_left]; intro a ha hb
    simp only [List.mem_map] at ha hb; aesop
  · exact (hp.filter _).map (fun a b h => by injection h with h1 h2; exact Prod.ext h1 h2)
  · rw [List.disjoint_left]; intro a ha hb
    simp only [List.mem_append, List.mem_map] at ha hb; aesop
  · exact hqs.map (fun _ _ h => by injection h)
  · rw [List.disjoint_left]; intro a ha hb
    simp only [List.mem_append, List.mem_map] at ha hb; aesop

theorem mem_sList {T : Machine Q P S} {code : S → Bool × Bool} {qs : List Q} (hQ : ∀ q, q ∈ qs)
    {x : BSt Q} : x ∈ sList T code qs ↔
      (∃ p, x = .r p ∧ goFrom T p = true) ∨ (∃ p b, x = .r1 p b ∧ rdPre T code p b = true) ∨
      (∃ q b, x = .w q b ∧ wrPre T code q b = true) ∨ (∃ q, x = .s q) := by
  simp only [sList, dGo, pR, pW, List.mem_append, List.mem_map, List.mem_filter, mem_pairs, Prod.exists]
  constructor
  · rintro (((⟨p, ⟨-, h⟩, rfl⟩ | ⟨p, b, ⟨-, h⟩, rfl⟩) | ⟨q, b, ⟨-, h⟩, rfl⟩) | ⟨q, -, rfl⟩)
    · exact .inl ⟨p, rfl, h⟩
    · exact .inr (.inl ⟨p, b, rfl, h⟩)
    · exact .inr (.inr (.inl ⟨q, b, rfl, h⟩))
    · exact .inr (.inr (.inr ⟨q, rfl⟩))
  · rintro (⟨p, rfl, h⟩ | ⟨p, b, rfl, h⟩ | ⟨q, b, rfl, h⟩ | ⟨q, rfl⟩)
    · exact .inl (.inl (.inl ⟨p, ⟨hQ p, h⟩, rfl⟩))
    · exact .inl (.inl (.inr ⟨p, b, ⟨hQ p, h⟩, rfl⟩))
    · exact .inl (.inr ⟨q, b, ⟨hQ q, h⟩, rfl⟩)
    · exact .inr ⟨q, hQ q, rfl⟩

/-- **Number of states of Morita's 2-symbol conversion** (2-bit codes, `Conv54.conv`):
    `|D_go| + m + P_r + P_w`, where `D_go` are the states with a rule into a real state
    (`|D_go| ≤ m`, so the count is at most `2m + P_r + P_w`, Morita's `mk + P_r + P_w` with `k = 2`). -/
theorem conv54_nst {T : Machine Q P S} {code : S → Bool × Bool} {dir : Q → Dir} {qs : List Q}
    (hQ : ∀ q, q ∈ qs) (hqs : qs.Nodup) :
    nst (URTM.Conv54.conv T code dir qs) =
      (dGo T qs).length + qs.length + (pR T code qs).length + (pW T code qs).length := by
  have hlen : (sList T code qs).length =
      (dGo T qs).length + qs.length + (pR T code qs).length + (pW T code qs).length := by
    simp only [sList, List.length_append, List.length_map]; omega
  rw [← hlen]
  refine nst_eq_of (sList_nodup hqs) (fun x => ⟨fun h => ?_, fun h => ?_⟩)
  · obtain ⟨ρ, hρ, rfl⟩ := h
    rw [mem_sList hQ]
    simp only [URTM.Conv54.conv, List.mem_append, List.mem_filterMap, List.mem_flatMap] at hρ
    rcases hρ with ((⟨r, hr, he⟩ | ⟨r, hr, he⟩) | ⟨r, hr, he⟩) | ⟨q, -, hq⟩
    · obtain ⟨p, s, t, d, q⟩ := r
      cases q with
      | go q =>
        simp only [URTM.Conv54.rRule, Option.some.injEq] at he; subst he
        exact .inl ⟨p, rfl, List.any_eq_true.2 ⟨_, hr, by simp [Tgt.isGo]⟩⟩
      | halt h => simp [URTM.Conv54.rRule] at he
    · obtain ⟨p, s, t, d, q⟩ := r
      cases q with
      | go q =>
        simp only [URTM.Conv54.tRule, Option.some.injEq] at he; subst he
        exact .inr (.inl ⟨p, _, rfl, List.any_eq_true.2 ⟨_, hr, by simp [Tgt.isGo]⟩⟩)
      | halt h => simp [URTM.Conv54.tRule] at he
    · obtain ⟨p, s, t, d, q⟩ := r
      cases q with
      | go q =>
        simp only [URTM.Conv54.wRule, Option.some.injEq] at he; subst he
        exact .inr (.inr (.inl ⟨q, _, rfl, List.any_eq_true.2 ⟨_, hr, by simp [isTo]⟩⟩))
      | halt h => simp [URTM.Conv54.wRule] at he
    · simp only [URTM.Conv54.sRules, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl <;> exact .inr (.inr (.inr ⟨q, rfl⟩))
  · rw [mem_sList hQ] at h
    simp only [URTM.Conv54.conv, List.mem_append, List.mem_filterMap, List.mem_flatMap]
    rcases h with ⟨p, rfl, h⟩ | ⟨p, b, rfl, h⟩ | ⟨q, b, rfl, h⟩ | ⟨q, rfl⟩
    · obtain ⟨r, hr, h⟩ := List.any_eq_true.1 h
      obtain ⟨p', s, t, d, q⟩ := r
      cases q with
      | go q =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨rfl, -⟩ := h
        exact ⟨_, .inl (.inl (.inl ⟨_, hr, rfl⟩)), rfl⟩
      | halt _ => simp [Tgt.isGo] at h
    · obtain ⟨r, hr, h⟩ := List.any_eq_true.1 h
      obtain ⟨p', s, t, d, q⟩ := r
      cases q with
      | go q =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨rfl, -⟩, rfl⟩ := h
        exact ⟨_, .inl (.inl (.inr ⟨_, hr, rfl⟩)), rfl⟩
      | halt _ => simp [Tgt.isGo] at h
    · obtain ⟨r, hr, h⟩ := List.any_eq_true.1 h
      obtain ⟨p', s, t, d, q'⟩ := r
      cases q' with
      | go q' =>
        simp only [isTo, Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨_, .inl (.inr ⟨_, hr, rfl⟩), rfl⟩
      | halt _ => simp [isTo] at h
    · exact ⟨_, .inr ⟨q, hQ q, List.mem_cons_self⟩, rfl⟩

theorem conv54_nst_le {T : Machine Q P S} {code : S → Bool × Bool} {dir : Q → Dir} {qs : List Q}
    (hQ : ∀ q, q ∈ qs) (hqs : qs.Nodup) :
    nst (URTM.Conv54.conv T code dir qs) ≤ 2 * qs.length + (pR T code qs).length + (pW T code qs).length := by
  rw [conv54_nst hQ hqs]
  have : (dGo T qs).length ≤ qs.length := List.length_filter_le _ _
  omega

end Conv54

/-! ## 9. Morita's 3-state conversion of a 1WU machine (Lemma 5.10, `Conv510.conv`): `N(2M − 1)` -/

section Conv510
open URTM.Conv55 (FSym)
variable {Q P S : Type} [DecidableEq Q] [DecidableEq S]

/-- The symbols `u`, `[u, k↑]`, `[u, k↓]` for `u ∈ ss` and `1 ≤ k < m`. -/
def gList (m : ℕ) (ss : List S) : List (FSym S) :=
  ss.flatMap (fun u => FSym.pl u :: ((List.range (m - 1)).map (fun k => FSym.up u (k + 1)) ++
    (List.range (m - 1)).map (fun k => FSym.dn u (k + 1))))

theorem gList_length {m : ℕ} (hm : 1 ≤ m) (ss : List S) : (gList m ss).length = (2 * m - 1) * ss.length := by
  simp only [gList, List.length_flatMap, List.length_cons, List.length_append, List.length_map,
    List.length_range, sum_map_const]
  rw [Nat.mul_comm]; congr 1; omega

theorem gList_nodup {m : ℕ} {ss : List S} (hss : ss.Nodup) : (gList m ss).Nodup := by
  refine nodup_flatMap_owner fOwn hss (fun u _ => ?_) (fun u _ x hx => ?_)
  · refine List.nodup_cons.2 ⟨by simp, List.Nodup.append ?_ ?_ ?_⟩
    · exact List.nodup_range.map (fun a b h => by injection h with _ h; omega)
    · exact List.nodup_range.map (fun a b h => by injection h with _ h; omega)
    · rw [List.disjoint_left]; simp
  · simp only [List.mem_cons, List.mem_append, List.mem_map, List.mem_range] at hx
    rcases hx with rfl | ⟨k, -, rfl⟩ | ⟨k, -, rfl⟩ <;> rfl

theorem mem_gList {m : ℕ} {ss : List S} (hS : ∀ s, s ∈ ss) {x : FSym S} :
    x ∈ gList m ss ↔ (∃ u, x = .pl u) ∨ (∃ u k, 1 ≤ k ∧ k < m ∧ x = .up u k) ∨
      (∃ u k, 1 ≤ k ∧ k < m ∧ x = .dn u k) := by
  simp only [gList, List.mem_flatMap, List.mem_cons, List.mem_append, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨u, -, rfl | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩⟩
    · exact .inl ⟨u, rfl⟩
    · exact .inr (.inl ⟨u, k + 1, by omega, by omega, rfl⟩)
    · exact .inr (.inr ⟨u, k + 1, by omega, by omega, rfl⟩)
  · rintro (⟨u, rfl⟩ | ⟨u, k, h1, hk, rfl⟩ | ⟨u, k, h1, hk, rfl⟩)
    · exact ⟨u, hS u, .inl rfl⟩
    · exact ⟨u, hS u, .inr (.inl ⟨k - 1, by omega, by congr 1; omega⟩)⟩
    · exact ⟨u, hS u, .inr (.inr ⟨k - 1, by omega, by congr 1; omega⟩)⟩

/-- **Morita's 3-state conversion has exactly `N(2M − 1)` symbols** (`N = |ss|` the symbols of the
    1WU machine, `M = m` the number range of its states, `1 ≤ idx q < m` for the states other than
    `q_L`). For (32,3): `N = 298`, `M = 62`, 36654. -/
theorem conv510_nsym {T : Machine Q P S} {qL : Q} {s0 : S} {idx : Q → ℕ} {m : ℕ} {ss : List S}
    (H : URTM.Conv510.Hyp T qL s0 idx m ss)
    (hsrc : ∀ r ∈ T, r.p ≠ qL → 1 ≤ idx r.p ∧ idx r.p < m) (hss : ss.Nodup) (hm : 2 ≤ m) :
    nsym (URTM.Conv510.conv T qL s0 idx m ss) = (2 * m - 1) * ss.length := by
  rw [← gList_length (by omega) ss]
  have hS := H.hS
  refine nsym_eq_of (gList_nodup hss) (fun x => ⟨fun h => ?_, fun h => ?_⟩)
  · obtain ⟨ρ, hρ, hx⟩ := mem_syms.1 h
    rcases URTM.Conv510.mem_conv hρ with ⟨r, hr, he⟩ | ⟨u, -, hu⟩
    · obtain ⟨q, hq, h3⟩ := URTM.Conv510.convRule_spec he
      rcases h3 with ⟨hp, hd, rfl⟩ | ⟨hp, hd, rfl⟩ | ⟨hp, hd, rfl⟩
      · have := URTM.Conv510.idxOK_spec (H.hidx r hr) hq (URTM.Conv510.shape_R (H.hshape r hr) hd hq)
        rcases hx with rfl | rfl <;> simp [mem_gList hS] <;> omega
      · have := URTM.Conv510.idxOK_spec (H.hidx r hr) hq (URTM.Conv510.shape_R (H.hshape r hr) hd hq)
        have := hsrc r hr hp
        rcases hx with rfl | rfl <;> simp [mem_gList hS] <;> omega
      · have := hsrc r hr hp
        rcases hx with rfl | rfl <;> simp [mem_gList hS] <;> omega
    · rcases URTM.Conv510.sym_spec hu with rfl | rfl | ⟨-, rfl⟩ | ⟨k, hk, rfl | rfl⟩ <;>
        rcases hx with rfl | rfl <;> simp [mem_gList hS] <;> omega
  · rcases (mem_gList hS).1 h with ⟨u, rfl⟩ | ⟨u, k, h1, hk, rfl⟩ | ⟨u, k, h1, hk, rfl⟩
    · exact s_mem_syms (URTM.Conv510.mem_sym (T := T) (qL := qL) (idx := idx) (hS u)
        (ρ := (⟨.R0, .pl u, .up u 1, .L, .go .L⟩ : Rule URTM.Conv510.TSt P (FSym S)))
        (by simp [URTM.Conv510.symRules]))
    · obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      rcases k with _ | k
      · exact t_mem_syms (URTM.Conv510.mem_sym (T := T) (qL := qL) (idx := idx) (hS u)
          (ρ := (⟨.R0, .pl u, .up u 1, .L, .go .L⟩ : Rule URTM.Conv510.TSt P (FSym S)))
          (by simp [URTM.Conv510.symRules]))
      · exact t_mem_syms (URTM.Conv510.mem_cnt (T := T) (qL := qL) (idx := idx) (hS u) (k := k) (by omega)
          (ρ := (⟨.R1, .up u (k + 1), .up u (k + 2), .L, .go .L⟩ : Rule URTM.Conv510.TSt P (FSym S))) (by simp))
    · obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      rcases k with _ | k
      · exact s_mem_syms (URTM.Conv510.mem_sym (T := T) (qL := qL) (idx := idx) (hS u)
          (ρ := (⟨.L, .dn u 1, .pl u, .R, .go .R0⟩ : Rule URTM.Conv510.TSt P (FSym S)))
          (by simp [URTM.Conv510.symRules]))
      · exact s_mem_syms (URTM.Conv510.mem_cnt (T := T) (qL := qL) (idx := idx) (hS u) (k := k) (by omega)
          (ρ := (⟨.L, .dn u (k + 2), .dn u (k + 1), .R, .go .R1⟩ : Rule URTM.Conv510.TSt P (FSym S))) (by simp))

end Conv510

/-! ## 10. The improved 3-state conversion (`Conv3S.conv`, `Conv3S.convM`):
    `1 + n + (m₋n + |G|)(n + 1) + n(n + 2 + |R| + |G|) + (n + 2)` -/

section Conv3
open URTM.Conv1W (VSym VSt)
open URTM.Conv3P (CSym univ)
open URTM.Conv3Base (mirror)
variable {Q P S : Type} [DecidableEq Q] [DecidableEq S]

theorem univ_length {α : Type} (need : α → ℕ) (syms : List α) :
    (univ need syms).length = syms.length + (syms.map need).sum := by
  simp [univ, List.length_flatMap]

theorem univ_congr {α : Type} {need need' : α → ℕ} {syms : List α} (h : ∀ x ∈ syms, need x = need' x) :
    univ need syms = univ need' syms := by
  unfold univ
  congr 1
  exact List.flatMap_congr (fun x hx => by rw [h x hx])

/-- The counter bound of the improved 3-state conversion: the largest number of a state of the
    1WU machine that reads the symbol, with the states numbered `c s` (n), `e1`, `e2`, `r p v` (|R|),
    `g p v` (|G|): the blank is read by `c s`, `e1`, `e2`; a plain symbol by `c s`, `r`, `g`; a mark by `c s`. -/
def need3 (n R G : ℕ) : VSym Q S → ℕ
  | .bl => n + 2
  | .pl _ => n + 2 + R + G
  | .mk _ _ => n
  | .mkp _ _ => n

theorem sum_flatMap_const {α β : Type} (l : List α) (f : α → List β) (g : β → ℕ) (c : ℕ)
    (h : ∀ a ∈ l, ((f a).map g).sum = c) : ((l.flatMap f).map g).sum = l.length * c := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.length_cons,
      h a List.mem_cons_self, ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]
    ring

theorem length_flatMap_const {α β : Type} (l : List α) (f : α → List β) (c : ℕ)
    (h : ∀ a ∈ l, (f a).length = c) : (l.flatMap f).length = l.length * c := by
  have := sum_flatMap_const l f (fun _ => 1) c (fun a ha => by simp [h a ha])
  simpa [sum_map_const] using this

/-- **The symbol count of the improved 3-state conversion, as a formula**: with the counter bound
    `need3`, `|univ| = 1 + n + (m₋n + |G|)(n + 1) + n(n + 2 + |R| + |G|) + (n + 2)`
    (`n = |ss|`, `m₋ = |qm|`, `|G| = |Gl|`, `R` the number of `r` states). -/
theorem univ_need3_length (ss : List S) (qm : List Q) (Gl : List (Q × S)) (R : ℕ) :
    (univ (need3 ss.length R Gl.length) (URTM.Conv3S.wsyms ss qm Gl)).length =
      1 + ss.length + (qm.length * ss.length + Gl.length) * (ss.length + 1) +
        ss.length * (ss.length + 2 + R + Gl.length) + (ss.length + 2) := by
  rw [univ_length]
  have h1 := sum_flatMap_const qm (fun p => ss.map (VSym.mk p)) (need3 ss.length R Gl.length)
    (ss.length * ss.length)
    (fun a _ => by simp [List.map_map, Function.comp_def, need3])
  have h2 := length_flatMap_const qm (fun p => ss.map (VSym.mk p)) ss.length (fun a _ => by simp)
  simp only [URTM.Conv3S.wsyms, URTM.Conv1W.allSyms, List.length_cons, List.length_append, List.length_map,
    List.map_cons, List.map_append, List.sum_cons, List.sum_append, List.map_map, Function.comp_def, need3,
    sum_map_const, h1, h2]
  ring

/-- **Upper bound** for the improved 3-state conversion (not mirrored). -/
theorem conv3S_nsym_le {T : Machine Q P S} {b : S} {ss : List S} {qm : List Q} {Rl Gl : List (Q × S)}
    {idx : VSt Q S → ℕ} {need : VSym Q S → ℕ} (H : URTM.Conv3S.Hyp T b ss qm Rl Gl idx need)
    (hsrc : ∀ r ∈ URTM.Conv1W.conv T b ss qm Rl Gl, r.p ≠ .L → 1 ≤ idx r.p ∧ idx r.p ≤ need r.s) :
    nsym (URTM.Conv3S.conv T b ss qm Rl Gl idx need) ≤ (univ need (URTM.Conv3S.wsyms ss qm Gl)).length := by
  refine nsym_le_of (fun x hx => ?_)
  obtain ⟨ρ, hρ, rfl | rfl⟩ := mem_syms.1 hx
  · exact (URTM.Conv3P.conv_syms (fun _ h => URTM.Conv3S.w_syms H h) (fun _ h => URTM.Conv3S.w_shape h)
      H.hidx hsrc ρ hρ).1
  · exact (URTM.Conv3P.conv_syms (fun _ h => URTM.Conv3S.w_syms H h) (fun _ h => URTM.Conv3S.w_shape h)
      H.hidx hsrc ρ hρ).2

/-- **Upper bound** for the mirrored improved 3-state conversion (the form of (3,600)). -/
theorem convM3S_nsym_le {T : Machine Q P S} {b : S} {ss : List S} {qm : List Q} {Rl Gl : List (Q × S)}
    {idx : VSt Q S → ℕ} {need : VSym Q S → ℕ} (H : URTM.Conv3S.Hyp (mirror T) b ss qm Rl Gl idx need)
    (hsrc : ∀ r ∈ URTM.Conv1W.conv (mirror T) b ss qm Rl Gl, r.p ≠ .L → 1 ≤ idx r.p ∧ idx r.p ≤ need r.s) :
    nsym (URTM.Conv3S.convM T b ss qm Rl Gl idx need) ≤ (univ need (URTM.Conv3S.wsyms ss qm Gl)).length := by
  refine nsym_le_of (fun x hx => ?_)
  obtain ⟨ρ, hρ, rfl | rfl⟩ := mem_syms.1 hx
  · exact (URTM.Conv3S.convM_syms H hsrc ρ hρ).1
  · exact (URTM.Conv3S.convM_syms H hsrc ρ hρ).2

/-- **The formula as a bound** (not mirrored): if the counter bound is `need3` on the symbols of
    the 1WU machine, the 3-state machine has at most
    `1 + n + (m₋n + |G|)(n + 1) + n(n + 2 + |R| + |G|) + (n + 2)` symbols. -/
theorem conv3S_nsym_formula {T : Machine Q P S} {b : S} {ss : List S} {qm : List Q} {Rl Gl : List (Q × S)}
    {idx : VSt Q S → ℕ} {need : VSym Q S → ℕ} (H : URTM.Conv3S.Hyp T b ss qm Rl Gl idx need)
    (hsrc : ∀ r ∈ URTM.Conv1W.conv T b ss qm Rl Gl, r.p ≠ .L → 1 ≤ idx r.p ∧ idx r.p ≤ need r.s)
    (hneed : ∀ x ∈ URTM.Conv3S.wsyms ss qm Gl, need x = need3 ss.length Rl.length Gl.length x) :
    nsym (URTM.Conv3S.conv T b ss qm Rl Gl idx need) ≤
      1 + ss.length + (qm.length * ss.length + Gl.length) * (ss.length + 1) +
        ss.length * (ss.length + 2 + Rl.length + Gl.length) + (ss.length + 2) := by
  rw [← univ_need3_length ss qm Gl Rl.length, ← univ_congr hneed]
  exact conv3S_nsym_le H hsrc

/-- The same for the mirrored conversion. -/
theorem convM3S_nsym_formula {T : Machine Q P S} {b : S} {ss : List S} {qm : List Q} {Rl Gl : List (Q × S)}
    {idx : VSt Q S → ℕ} {need : VSym Q S → ℕ} (H : URTM.Conv3S.Hyp (mirror T) b ss qm Rl Gl idx need)
    (hsrc : ∀ r ∈ URTM.Conv1W.conv (mirror T) b ss qm Rl Gl, r.p ≠ .L → 1 ≤ idx r.p ∧ idx r.p ≤ need r.s)
    (hneed : ∀ x ∈ URTM.Conv3S.wsyms ss qm Gl, need x = need3 ss.length Rl.length Gl.length x) :
    nsym (URTM.Conv3S.convM T b ss qm Rl Gl idx need) ≤
      1 + ss.length + (qm.length * ss.length + Gl.length) * (ss.length + 1) +
        ss.length * (ss.length + 2 + Rl.length + Gl.length) + (ss.length + 2) := by
  rw [← univ_need3_length ss qm Gl Rl.length, ← univ_congr hneed]
  exact convM3S_nsym_le H hsrc

end Conv3

end URTM.Univ.SymCount
