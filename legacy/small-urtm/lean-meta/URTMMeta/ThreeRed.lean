/-
  3 状態 2 記号の URTM（段階 2b）その 1: **2 状態の機械への帰着**（`QConf` の上の補題）。**手書き**。

  状態 e へ入る規則がどれも e 自身から出る（`SelfOnly`。入る規則が 1 本も無い場合を含む）なら、
  e を離れた後の実行は、e から出る規則を除いた表 `dropFrom e tbl` の実行と一致する。
  `dropFrom e tbl` は 2 状態の RTM（`TwoStateRTM`）なので、2 状態の有界停止 `bounded_halting` が使える。
  機械モデルは 3 状態の定理と同じ `QConf`・`qrun`（両側無限テープの五つ組 TM）で、橋渡しは要らない。

    * `qrun_dropFrom` : e 以外の状態から始めれば、元の表と `dropFrom e tbl` の実行は一致する
    * `halts_off`     : e 以外の状態から始めた停止は `bnd nsym a b + 1` 歩で決まる
    * `halts_tail`    : k ≤ K 歩目に e 以外の状態に居る実行の停止は `K + (bnd nsym (a − K) (b + K) + 1)` 歩で決まる
    * `realize_det` / `realize_rev` : 正規形の表は決定的・可逆（Bool の検査の形。可逆性は符号が重ならないことから）
    * `realize_twoState` / `normT_twoState` : 正規形の表から状態 e を出る規則を除くと 2 状態の RTM
-/
import URTMMeta.Bounded
import URTM.ThreeNorm

namespace URTM.Meta
open URTM URTM.TwoState URTM.Three

/-! ### 状態 e から出る規則を除いた表 -/

/-- 状態 e から出る規則を除いた表。 -/
def dropFrom (e : Nat) (tbl : List Quint) : List Quint := tbl.filter (fun r => r.p != e)

/-- 状態 e へ入る規則はどれも e から出る（e は初めにしか居られない。入る規則が無い場合を含む）。 -/
def SelfOnly (tbl : List Quint) (e : Nat) : Prop := ∀ r ∈ tbl, r.q = e → r.p = e

theorem selfOnly_spec {tbl : List Quint} {e : Nat} (h : selfOnly tbl e = true) : SelfOnly tbl e := by
  intro r hr hq
  unfold selfOnly at h
  have := List.all_eq_true.mp h r hr
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at this
  rcases this with h | h
  · exact absurd hq h
  · exact h

theorem find?_dropFrom (tbl : List Quint) {e p : Nat} (s : Nat) (hp : p ≠ e) :
    find? (dropFrom e tbl) p s = find? tbl p s := by
  unfold find? dropFrom
  induction tbl with
  | nil => rfl
  | cons r tbl ih =>
    by_cases hr : r.p = e
    · have hne : ¬ e = p := fun h => hp h.symm
      simp [hr, hne, ih]
    · simp [List.find?_cons, hr, ih]

theorem qstep_dropFrom (tbl : List Quint) {e : Nat} {c : QConf} (hc : c.st ≠ e) :
    qstep (dropFrom e tbl) c = qstep tbl c := by
  unfold qstep; rw [find?_dropFrom tbl _ hc]

/-- e 以外の状態から始めれば、e へは入らないので、実行は `dropFrom e tbl` の実行と一致する。 -/
theorem qrun_dropFrom {tbl : List Quint} {e : Nat} (hso : SelfOnly tbl e) :
    ∀ n (c : QConf), c.st ≠ e → qrun (dropFrom e tbl) n c = qrun tbl n c := by
  intro n
  induction n with
  | zero => intro c _; rfl
  | succ n ih =>
    intro c hc
    have hq := qstep_dropFrom tbl hc
    cases hs : qstep tbl c with
    | none => rw [qrun_succ_none _ n hs, qrun_succ_none _ n (hq.trans hs)]
    | some c' =>
      obtain ⟨r, hr, hf, he⟩ := qstep_some hs
      have hp : r.p = c.st := (find?_spec hf).2.1
      have hc' : c'.st ≠ e := by
        rw [he]; show r.q ≠ e
        intro hq'; exact hc (hp ▸ hso r hr hq')
      rw [qrun_succ_some _ n hs, qrun_succ_some _ n (hq.trans hs)]
      exact ih c' hc'

/-- 3 状態 {e, qa, qb} の決定的・可逆な表から e を出る規則を除くと、qa, qb の 2 状態の RTM
    （e は出ていく規則の無い停止用の状態として扱う）。 -/
theorem twoState_dropFrom {tbl : List Quint} {e qa qb : Nat} (hdet : deterministic tbl = true)
    (hrev : reversible tbl = true) (hab : qa ≠ qb) (hea : e ≠ qa) (heb : e ≠ qb)
    (hsrc : ∀ r ∈ tbl, r.p = e ∨ r.p = qa ∨ r.p = qb)
    (hdst : ∀ r ∈ tbl, r.q = e ∨ r.q = qa ∨ r.q = qb) :
    TwoStateRTM (dropFrom e tbl) qa qb e where
  det := allPairs_filter _ _ _ hdet
  rev := allPairs_filter _ _ _ hrev
  ne := hab
  f0 := hea
  f1 := heb
  src := fun r hr => by
    obtain ⟨hm, hp⟩ := List.mem_filter.mp hr
    have hne : r.p ≠ e := by simpa using hp
    rcases hsrc r hm with h | h | h
    · exact absurd h hne
    · exact Or.inl h
    · exact Or.inr h
  dst := fun r hr => by
    rcases hdst r (List.mem_filter.mp hr).1 with h | h | h
    · exact Or.inr (Or.inr h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

/-! ### 窓と記号の保存 -/

/-- 1 歩で窓は左右に高々 1 ずつ広がる。 -/
theorem qstep_window {tbl : List Quint} {c c' : QConf} (h : qstep tbl c = some c') {a b : Int}
    (ha : a ≤ c.pos) (hb : c.pos ≤ b) (hz : ∀ x, (x < a ∨ b < x) → c.tape x = 0) :
    a - 1 ≤ c'.pos ∧ c'.pos ≤ b + 1 ∧ ∀ x, (x < a - 1 ∨ b + 1 < x) → c'.tape x = 0 := by
  obtain ⟨r, _, _, rfl⟩ := qstep_some h
  refine ⟨?_, ?_, fun x hx => ?_⟩
  · show a - 1 ≤ move r.d c.pos
    cases r.d <;> simp only [move] <;> omega
  · show move r.d c.pos ≤ b + 1
    cases r.d <;> simp only [move] <;> omega
  · show write c.tape c.pos r.t x = 0
    rw [write_off _ _ _ (by omega)]; exact hz x (by omega)

/-- k 歩で窓は左右に高々 k ずつ広がる。 -/
theorem qrun_window {tbl : List Quint} :
    ∀ (k : Nat) {c c' : QConf}, qrun tbl k c = some c' → ∀ {a b : Int}, a ≤ c.pos → c.pos ≤ b →
      (∀ x, (x < a ∨ b < x) → c.tape x = 0) →
      a - k ≤ c'.pos ∧ c'.pos ≤ b + k ∧ ∀ x, (x < a - k ∨ b + k < x) → c'.tape x = 0 := by
  intro k
  induction k with
  | zero =>
    intro c c' h a b ha hb hz
    have hc : c = c' := by simpa [qrun] using h
    subst hc
    exact ⟨by omega, by omega, fun x hx => hz x (by omega)⟩
  | succ k ih =>
    intro c c' h a b ha hb hz
    cases hs : qstep tbl c with
    | none => rw [qrun_succ_none tbl k hs] at h; cases h
    | some c₁ =>
      rw [qrun_succ_some tbl k hs] at h
      obtain ⟨h1, h2, h3⟩ := qstep_window hs ha hb hz
      obtain ⟨g1, g2, g3⟩ := ih h h1 h2 h3
      exact ⟨by omega, by omega, fun x hx => g3 x (by omega)⟩

/-- 記号は nsym 未満のまま。 -/
theorem qrun_tape_lt {tbl : List Quint} {nsym : Nat} (hcl : QClosed tbl nsym) :
    ∀ (k : Nat) {c c' : QConf}, qrun tbl k c = some c' → (∀ x, c.tape x < nsym) →
      ∀ x, c'.tape x < nsym := by
  intro k
  induction k with
  | zero =>
    intro c c' h hc
    have hcc : c = c' := by simpa [qrun] using h
    subst hcc; exact hc
  | succ k ih =>
    intro c c' h hc
    cases hs : qstep tbl c with
    | none => rw [qrun_succ_none tbl k hs] at h; cases h
    | some c₁ =>
      rw [qrun_succ_some tbl k hs] at h
      refine ih h fun x => ?_
      obtain ⟨r, hr, hf, rfl⟩ := qstep_some hs
      show write c.tape c.pos r.t x < nsym
      unfold write; split
      · exact hcl r hr (by rw [(find?_spec hf).2.2]; exact hc _)
      · exact hc x

/-! ### 2 状態の有界停止への帰着 -/

section
variable {tbl : List Quint} {e qa qb : Nat} (hT : TwoStateRTM (dropFrom e tbl) qa qb e)
  (hso : SelfOnly tbl e) {nsym : Nat} (hcl : QClosed tbl nsym)
include hT hso hcl

/-- e 以外の状態から始めた停止は、2 状態の上界で決まる。 -/
theorem halts_off (a b : Int) (c : QConf) (hc : c.st ≠ e) (hinit : ∀ x, c.tape x < nsym)
    (ha : a ≤ c.pos) (hb : c.pos ≤ b) (hsupp : ∀ x, (x < a ∨ b < x) → c.tape x = 0) :
    QHalts tbl c ↔ qrun tbl (bnd nsym a b + 1) c = none := by
  have hcl' : QClosed (dropFrom e tbl) nsym := fun r hr => hcl r (List.mem_filter.mp hr).1
  have h := bounded_halting hT nsym hcl' a b c hinit (by omega) ha hb hsupp
  rw [qrun_dropFrom hso _ c hc] at h
  rw [← h]
  exact exists_congr fun n => by rw [qrun_dropFrom hso n c hc]

/-- **末尾は 2 状態**: k ≤ K 歩目に e 以外の状態に居る実行は、止まるなら
    `K + (bnd nsym (a − K) (b + K) + 1)` 歩で止まっている。 -/
theorem halts_tail {a b : Int} {c c' : QConf} {k K : Nat} (hk : qrun tbl k c = some c')
    (hc' : c'.st ≠ e) (hkK : k ≤ K) (hinit : ∀ x, c.tape x < nsym) (ha : a ≤ c.pos) (hb : c.pos ≤ b)
    (hsupp : ∀ x, (x < a ∨ b < x) → c.tape x = 0) (hH : QHalts tbl c) :
    qrun tbl (K + (bnd nsym (a - K) (b + K) + 1)) c = none := by
  obtain ⟨g1, g2, g3⟩ := qrun_window k hk ha hb hsupp
  have hH' : QHalts tbl c' := by
    obtain ⟨n, hn⟩ := hH
    refine ⟨n, ?_⟩
    have := qrun_none_mono tbl c n (k + n) hn (by omega)
    rw [qrun_add, hk] at this; exact this
  have h := (halts_off hT hso hcl (a - K) (b + K) c' hc' (qrun_tape_lt hcl k hk hinit) (by omega)
    (by omega) (fun x hx => g3 x (by omega))).mp hH'
  have h2 : qrun tbl (k + (bnd nsym (a - K) (b + K) + 1)) c = none := by
    rw [qrun_add, hk]; exact h
  exact qrun_none_mono tbl c _ _ h2 (by omega)

end

/-! ### 正規形の表は決定的・可逆 -/

theorem allPairs_of_pairwise (f : Quint → Quint → Bool) :
    ∀ l : List Quint, l.Pairwise (fun a b => f a b = true) → allPairs f l = true
  | [], _ => rfl
  | x :: xs, h => by
    rw [List.pairwise_cons] at h
    show (xs.all (f x) && allPairs f xs) = true
    rw [Bool.and_eq_true, List.all_eq_true]
    exact ⟨h.1, allPairs_of_pairwise f xs h.2⟩

/-- 正規形の表は欄の番号 2p + s の順に並ぶ。 -/
theorem realize_sorted (c0 c1 c2 c3 c4 c5 : Nat) (D : List Dir) :
    (realize [c0, c1, c2, c3, c4, c5] D).Pairwise (fun a b => 2 * a.p + a.s < 2 * b.p + b.s) := by
  simp only [realize, quintOf, List.getD_cons_zero, List.getD_cons_succ]
  by_cases e0 : c0 = 0 <;> by_cases e1 : c1 = 0 <;> by_cases e2 : c2 = 0 <;>
    by_cases e3 : c3 = 0 <;> by_cases e4 : c4 = 0 <;> by_cases e5 : c5 = 0 <;>
    simp [e0, e1, e2, e3, e4, e5]

/-- 0 でない符号は欄ごとに異なる（`injCodes` の命題版。可逆性にあたる）。 -/
def InjCodes (es : List Nat) : Prop :=
  ∀ i j, i < 6 → j < 6 → es.getD i 0 ≠ 0 → es.getD i 0 = es.getD j 0 → i = j

/-- 正規形の表の五つ組は、0 でない符号 c を持つ欄 (i, s) から決まる。 -/
theorem mem_realize6 {c0 c1 c2 c3 c4 c5 : Nat} {D : List Dir} {r : Quint}
    (h : r ∈ realize [c0, c1, c2, c3, c4, c5] D) :
    ∃ i s c, i < 3 ∧ s < 2 ∧ c = [c0, c1, c2, c3, c4, c5].getD (2 * i + s) 0 ∧
      c ∈ [c0, c1, c2, c3, c4, c5] ∧ c ≠ 0 ∧
      r = ⟨i, s, (c - 1) % 2, D.getD ((c - 1) / 2) Dir.L, (c - 1) / 2⟩ := by
  have key : ∀ i s c, r ∈ quintOf D i s c →
      c ≠ 0 ∧ r = ⟨i, s, (c - 1) % 2, D.getD ((c - 1) / 2) Dir.L, (c - 1) / 2⟩ := by
    intro i s c hm
    unfold quintOf at hm
    split at hm
    · simp at hm
    · rename_i hc; exact ⟨hc, by simpa using hm⟩
  unfold realize at h
  simp only [List.mem_append, List.getD_cons_zero, List.getD_cons_succ] at h
  rcases h with ((((h | h) | h) | h) | h) | h
  · obtain ⟨h1, h2⟩ := key _ _ _ h; exact ⟨0, 0, c0, by omega, by omega, rfl, by simp, h1, h2⟩
  · obtain ⟨h1, h2⟩ := key _ _ _ h; exact ⟨0, 1, c1, by omega, by omega, rfl, by simp, h1, h2⟩
  · obtain ⟨h1, h2⟩ := key _ _ _ h; exact ⟨1, 0, c2, by omega, by omega, rfl, by simp, h1, h2⟩
  · obtain ⟨h1, h2⟩ := key _ _ _ h; exact ⟨1, 1, c3, by omega, by omega, rfl, by simp, h1, h2⟩
  · obtain ⟨h1, h2⟩ := key _ _ _ h; exact ⟨2, 0, c4, by omega, by omega, rfl, by simp, h1, h2⟩
  · obtain ⟨h1, h2⟩ := key _ _ _ h; exact ⟨2, 1, c5, by omega, by omega, rfl, by simp, h1, h2⟩

section
variable {c0 c1 c2 c3 c4 c5 : Nat} {D : List Dir}

/-- 正規形の表は決定的（Bool の検査の形）。 -/
theorem realize_det : deterministic (realize [c0, c1, c2, c3, c4, c5] D) = true := by
  refine allPairs_of_pairwise _ _ ((realize_sorted c0 c1 c2 c3 c4 c5 D).imp ?_)
  intro a b hab
  unfold detPair
  by_cases hp : a.p = b.p
  · have hs : a.s ≠ b.s := fun hs => by rw [hp, hs] at hab; omega
    simp [hs]
  · simp [hp]

/-- 0 でない符号が欄ごとに異なれば、正規形の表は可逆（Bool の検査の形）。 -/
theorem realize_rev (hinj : InjCodes [c0, c1, c2, c3, c4, c5]) :
    reversible (realize [c0, c1, c2, c3, c4, c5] D) = true := by
  refine allPairs_of_pairwise _ _ (List.Pairwise.imp_of_mem ?_ (realize_sorted c0 c1 c2 c3 c4 c5 D))
  intro a b ha hb hab
  obtain ⟨i, s, ca, hi, hs, hca, _, hc, rfl⟩ := mem_realize6 ha
  obtain ⟨i', s', cb, hi', hs', hcb, _, hc', rfl⟩ := mem_realize6 hb
  have hne : ca ≠ cb := by
    intro heq
    have := hinj (2 * i + s) (2 * i' + s') (by omega) (by omega) (hca ▸ hc) (by rw [← hca, ← hcb]; exact heq)
    simp only at hab
    omega
  unfold revPair
  simp only
  by_cases hq : (ca - 1) / 2 = (cb - 1) / 2
  · have ht : (ca - 1) % 2 ≠ (cb - 1) % 2 := by omega
    simp [hq, ht]
  · simp [hq]

/-- 符号が 7 未満なら、正規形の表の状態は 0, 1, 2。 -/
theorem realize_states (hlt : ∀ c ∈ [c0, c1, c2, c3, c4, c5], c < 7) {r : Quint}
    (h : r ∈ realize [c0, c1, c2, c3, c4, c5] D) : r.p < 3 ∧ r.q < 3 := by
  obtain ⟨i, s, c, hi, _, _, hm, _, rfl⟩ := mem_realize6 h
  have := hlt c hm
  exact ⟨hi, by show (c - 1) / 2 < 3; omega⟩

/-- **正規形の表から状態 e を出る規則を除くと 2 状態の RTM**（残りの 2 状態を qa, qb とする）。 -/
theorem realize_twoState (hlt : ∀ c ∈ [c0, c1, c2, c3, c4, c5], c < 7)
    (hinj : InjCodes [c0, c1, c2, c3, c4, c5]) {e : Nat} (he : e < 3) :
    ∃ qa qb, TwoStateRTM (dropFrom e (realize [c0, c1, c2, c3, c4, c5] D)) qa qb e := by
  have hdet := realize_det (c0 := c0) (c1 := c1) (c2 := c2) (c3 := c3) (c4 := c4) (c5 := c5) (D := D)
  have hrev := realize_rev (D := D) hinj
  have hst := fun r hr => realize_states (D := D) hlt (r := r) hr
  rcases (show e = 0 ∨ e = 1 ∨ e = 2 by omega) with rfl | rfl | rfl
  · exact ⟨1, 2, twoState_dropFrom hdet hrev (by decide) (by decide) (by decide)
      (fun r hr => by have := (hst r hr).1; omega) (fun r hr => by have := (hst r hr).2; omega)⟩
  · exact ⟨0, 2, twoState_dropFrom hdet hrev (by decide) (by decide) (by decide)
      (fun r hr => by have := (hst r hr).1; omega) (fun r hr => by have := (hst r hr).2; omega)⟩
  · exact ⟨0, 1, twoState_dropFrom hdet hrev (by decide) (by decide) (by decide)
      (fun r hr => by have := (hst r hr).1; omega) (fun r hr => by have := (hst r hr).2; omega)⟩

end

section
variable {tbl : List Quint} {q₀ q₁ q₂ σ : Nat}

/-- 任意の表の正規形の符号は、0 でないものが欄ごとに異なる（`codeOf_inj`）。 -/
theorem absCodes_inj (H : RTM32 tbl q₀ q₁ q₂ σ) : InjCodes (absCodes q₀ q₁ q₂ σ tbl) := by
  intro i j hi hj hne heq
  have gi := absCodes_getD (tbl := tbl) (q₀ := q₀) (q₁ := q₁) (q₂ := q₂) (σ := σ)
    (i := i / 2) (s := i % 2) (by omega) (by omega)
  have gj := absCodes_getD (tbl := tbl) (q₀ := q₀) (q₁ := q₁) (q₂ := q₂) (σ := σ)
    (i := j / 2) (s := j % 2) (by omega) (by omega)
  rw [show 2 * (i / 2) + i % 2 = i by omega] at gi
  rw [show 2 * (j / 2) + j % 2 = j by omega] at gj
  rw [gi] at hne
  rw [gi, gj] at heq
  obtain ⟨e1, e2⟩ := codeOf_inj H (by omega) (by omega) (by omega) (by omega) hne heq
  omega

/-- **正規形の表 `normT` から状態 e を出る規則を除くと 2 状態の RTM**。 -/
theorem normT_twoState (H : RTM32 tbl q₀ q₁ q₂ σ) {e : Nat} (he : e < 3) :
    ∃ qa qb, TwoStateRTM
      (dropFrom e (normT (tbl := tbl) (q₀ := q₀) (q₁ := q₁) (q₂ := q₂) (σ := σ))) qa qb e :=
  realize_twoState (absCodes_lt H) (absCodes_inj H) he

end

end URTM.Meta
