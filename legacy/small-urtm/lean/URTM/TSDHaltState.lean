/-
  2 状態 RTM の停止問題の決定可能性 その 12: 停止用の疑似状態。**手書き**。

  2 つの状態 q₀, q₁ のほかに、出ていく規則を持たない停止用の状態 qf へ入る規則があってもよい
  （Morita の表の「最終状態」）。qf へ入る規則を取り除いた表 `dropInto qf tbl` は 2 状態の可逆な表で、
  停止するかどうかは変わらない（取り除いた表は qf へ入る 1 歩手前で止まる）。
    * `QHalts_drop_iff` : 停止性の同値（決定性 Def. 5.3 を使う）
    * `decide2_halt_correct` : 停止用の疑似状態を許した 2 状態の可逆 TM の停止問題も決定可能
-/
import URTM.TSDFinal

namespace URTM.TwoState

def dropInto (qf : Nat) (tbl : List Quint) : List Quint := tbl.filter (fun r => r.q != qf)

theorem all_filter {α : Type} (g P : α → Bool) :
    ∀ (l : List α), l.all g = true → (l.filter P).all g = true := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons x xs ih =>
    intro h
    have h0 : (g x && xs.all g) = true := h
    obtain ⟨h1, h2⟩ := and_true_split h0
    by_cases hp : P x = true
    · rw [List.filter_cons_of_pos hp]
      show (g x && (xs.filter P).all g) = true
      rw [h1, ih h2]; rfl
    · rw [List.filter_cons_of_neg hp]; exact ih h2

theorem allPairs_filter (f : Quint → Quint → Bool) (P : Quint → Bool) :
    ∀ (l : List Quint), allPairs f l = true → allPairs f (l.filter P) = true := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons x xs ih =>
    intro h
    have h0 : (xs.all (f x) && allPairs f xs) = true := h
    obtain ⟨h1, h2⟩ := and_true_split h0
    by_cases hp : P x = true
    · rw [List.filter_cons_of_pos hp]
      show ((xs.filter P).all (f x) && allPairs f (xs.filter P)) = true
      rw [all_filter _ _ xs h1, ih h2]; rfl
    · rw [List.filter_cons_of_neg hp]; exact ih h2

/-- 絞った表の表引き（前から最初に一致するもの）。 -/
theorem find?_filter_eq (P : Quint → Bool) (p s : Nat) :
    ∀ (l : List Quint), find? (l.filter P) p s = l.find? (fun r => P r && (r.p == p && r.s == s)) := by
  intro l
  induction l with
  | nil => rfl
  | cons x xs ih =>
    unfold find? at ih ⊢
    cases hpx : P x <;> cases hk : (x.p == p && x.s == s) <;>
      simp [List.filter_cons, List.find?_cons, hpx, hk, ih]

/-- 最初に p で一致するものが q も満たすなら、「q かつ p」で最初に一致するのもそれ。 -/
theorem find?_and_of {α : Type} (p q : α → Bool) :
    ∀ (l : List α) (r : α), l.find? p = some r → q r = true →
      l.find? (fun x => q x && p x) = some r := by
  intro l
  induction l with
  | nil => intro r h; simp at h
  | cons x xs ih =>
    intro r h hq
    cases hpx : p x
    · rw [List.find?_cons, hpx] at h
      simp only at h
      rw [List.find?_cons]
      simp only [hpx, Bool.and_false]
      exact ih r h hq
    · rw [List.find?_cons, hpx] at h
      simp only [Option.some.injEq] at h
      subst h
      rw [List.find?_cons]
      simp [hpx, hq]

theorem det_unique {tbl : List Quint} (hdet : deterministic tbl = true) {r r' : Quint}
    (hr : r ∈ tbl) (hr' : r' ∈ tbl) (hp : r.p = r'.p) (hs : r.s = r'.s) : r = r' := by
  rcases allPairs_sound hdet hr hr' with h | h | h
  · exact h
  · unfold detPair at h; simp [hp, hs] at h
  · unfold detPair at h; simp [hp, hs] at h

section Drop
variable {tbl : List Quint} {qf : Nat}

theorem qstep_drop (hdet : deterministic tbl = true) (hno : ∀ r ∈ tbl, r.p ≠ qf)
    (c : QConf) :
    (qstep (dropInto qf tbl) c = none ∧
      (qstep tbl c = none ∨ ∃ c', qstep tbl c = some c' ∧ c'.st = qf)) ∨
    ∃ c', qstep (dropInto qf tbl) c = some c' ∧ qstep tbl c = some c' ∧ c'.st ≠ qf := by
  have hf := find?_filter_eq (fun r => r.q != qf) c.st (c.tape c.pos) tbl
  unfold qstep dropInto
  rw [hf]
  cases h : find? tbl c.st (c.tape c.pos) with
  | none =>
    left
    refine ⟨?_, Or.inl rfl⟩
    have : tbl.find? (fun r => (r.q != qf) && (r.p == c.st && r.s == c.tape c.pos)) = none := by
      apply List.find?_eq_none.mpr
      intro r hr hk
      have hk' := (and_true_split hk).2
      unfold find? at h
      exact (List.find?_eq_none.mp h r hr) hk'
    rw [this]
  | some r =>
    obtain ⟨hr, hrp, hrs⟩ := find?_spec h
    by_cases hq : r.q = qf
    · left
      refine ⟨?_, Or.inr ⟨_, rfl, hq⟩⟩
      have : tbl.find? (fun r => (r.q != qf) && (r.p == c.st && r.s == c.tape c.pos)) = none := by
        apply List.find?_eq_none.mpr
        intro r' hr' hk
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hk
        have := det_unique hdet hr hr' (by rw [hrp, hk.2.1]) (by rw [hrs, hk.2.2])
        rw [← this] at hk; exact hk.1 hq
      rw [this]
    · right
      refine ⟨_, ?_, rfl, hq⟩
      have : tbl.find? (fun r => (r.q != qf) && (r.p == c.st && r.s == c.tape c.pos)) = some r := by
        unfold find? at h
        exact find?_and_of _ (fun r => r.q != qf) tbl r h (by simpa using hq)
      rw [this]

theorem qstep_qf (hno : ∀ r ∈ tbl, r.p ≠ qf) (c : QConf) (hc : c.st = qf) : qstep tbl c = none := by
  unfold qstep
  cases h : find? tbl c.st (c.tape c.pos) with
  | none => rfl
  | some r =>
    obtain ⟨hr, hrp, _⟩ := find?_spec h
    exact absurd (hrp.trans hc) (hno r hr)

theorem QHalts_drop_iff (hdet : deterministic tbl = true) (hno : ∀ r ∈ tbl, r.p ≠ qf)
    (c : QConf) (hc : c.st ≠ qf) : QHalts (dropInto qf tbl) c ↔ QHalts tbl c := by
  have h1 : ∀ n (c : QConf), c.st ≠ qf → qrun (dropInto qf tbl) n c = none →
      qrun tbl (n + 1) c = none := by
    intro n
    induction n with
    | zero => intro c _ h; simp [qrun] at h
    | succ n ih =>
      intro c hc h
      rcases qstep_drop hdet hno c with ⟨_, hB | ⟨c', hc', hq⟩⟩ | ⟨c', hA, hB, hq⟩
      · exact qrun_succ_none tbl _ hB
      · rw [qrun_succ_some tbl _ hc']
        exact qrun_succ_none tbl _ (qstep_qf hno c' hq)
      · rw [qrun_succ_some _ n hA] at h
        rw [qrun_succ_some tbl _ hB]
        exact ih c' hq h
  have h2 : ∀ n (c : QConf), c.st ≠ qf → qrun tbl n c = none →
      qrun (dropInto qf tbl) n c = none := by
    intro n
    induction n with
    | zero => intro c _ h; simp [qrun] at h
    | succ n ih =>
      intro c hc h
      rcases qstep_drop hdet hno c with ⟨hA, _⟩ | ⟨c', hA, hB, hq⟩
      · exact qrun_succ_none _ _ hA
      · rw [qrun_succ_some tbl n hB] at h
        rw [qrun_succ_some _ n hA]
        exact ih c' hq h
  constructor
  · rintro ⟨n, hn⟩; exact ⟨n + 1, h1 n c hc hn⟩
  · rintro ⟨n, hn⟩; exact ⟨n, h2 n c hc hn⟩

end Drop

/-- **停止用の疑似状態を許した主定理**: 状態 q₀, q₁ と、出ていく規則の無い停止用状態 qf。 -/
theorem decide2_halt_correct (tbl : List Quint) (hdet : deterministic tbl = true)
    (hrev : reversible tbl = true) (q₀ q₁ qf : Nat) (hne : q₀ ≠ q₁) (hf0 : qf ≠ q₀) (hf1 : qf ≠ q₁)
    (hstates : ∀ r ∈ tbl, r.q = q₀ ∨ r.q = q₁ ∨ r.q = qf) (hno : ∀ r ∈ tbl, r.p ≠ qf)
    (nsym : Nat) (hcl : QClosed tbl nsym) (a b : Int) (c : QConf) (hst : c.st = q₀ ∨ c.st = q₁)
    (hinit : ∀ x, c.tape x < nsym) (hab : a ≤ b) (ha : a ≤ c.pos) (hb : c.pos ≤ b)
    (hsupp : ∀ x, (x < a ∨ b < x) → c.tape x = 0) :
    decide2 (dropInto qf tbl) q₀ q₁ nsym a b c = true ↔ QHalts tbl c := by
  have hc : c.st ≠ qf := by rcases hst with h | h <;> rw [h] <;> exact fun e => by simp_all
  rw [← QHalts_drop_iff hdet hno c hc]
  refine decide2_correct _ (allPairs_filter _ _ _ hrev) q₀ q₁ hne ?_ nsym ?_ a b c hst hinit
    hab ha hb hsupp
  · intro r hr
    obtain ⟨hr1, hr2⟩ := List.mem_filter.mp hr
    have : r.q ≠ qf := by simpa using hr2
    rcases hstates r hr1 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h this
  · intro r hr hs
    exact hcl r (List.mem_filter.mp hr).1 hs

end URTM.TwoState
