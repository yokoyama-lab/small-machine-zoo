/-
  3 状態 2 記号の URTM（段階 2e の 6）: **群 D のうち「2 段の転送をするセル」の 2 類**（class 21, 57、24 表）。**手書き**。

  向き: 開いている側を右にそろえる。右へ動いて入る状態は e（要求）だけ。**セルの規則**（`Cell2`）:
  (e,0) → (1, L, q1)（中身 0 への要求は即答）、(e,1) → (f', R, e)（中身 1 への要求は転送）、
  (q1,f') → (0, L, q2)（応答 q1 には q2 で即答）、(q2,f') → (g, R, e)（応答 q2 にはもう一度転送）、
  (q1,g) → (0, L, q1)（2 回目の応答 q1 には q1 で即答）。2 回目の応答が q2 なら止まるが、空白から始まるカスケードでは起きない。
  応答の列を 3 文字 a = 0, b = 1, c = 2 に細分すると（a, c は q1、b は q2。c は b の直後の q1）、細分した列 w' は
  文字の射 σ(a) = bc、σ(b) = a、σ(c) = a の不動点 w' = a σ(w') になる（`dinv`）。窓の自動機械は w' の射影を読むので、
  `ThreeI` の `dfa_morph`（文字 3 つ）と上界 `mrI` がそのまま使える。
-/
import URTMMeta.ThreeI

namespace URTM.Meta
open URTM URTM.TwoState URTM.Three

/-! ### セルの規則 -/

/-- 右側の 2 段の転送をするセルの規則（上の説明）。 -/
structure Cell2 (tbl : List Quint) (e q1 q2 f' g : Nat) : Prop where
  h00 : find? tbl e 0 = some ⟨e, 0, 1, Dir.L, q1⟩
  h01 : find? tbl e 1 = some ⟨e, 1, f', Dir.R, e⟩
  hA : find? tbl q1 f' = some ⟨q1, f', 0, Dir.L, q2⟩
  hB1 : find? tbl q2 f' = some ⟨q2, f', g, Dir.R, e⟩
  hB2 : find? tbl q1 g = some ⟨q1, g, 0, Dir.L, q1⟩
  hent : ∀ ρ ∈ tbl, ρ.d = Dir.R → ρ.q = e

/-! ### 空白から始まるカスケード（細分した文字で） -/

/-- 文字の射 σ: a ↦ bc、b ↦ a、c ↦ a（a = 0, b = 1, c = 2）。 -/
def dsig : Nat → List Nat
  | 0 => [1, 2]
  | _ => [0]

/-- 次の要求で出す文字（y = 0 なら a、y = 2 なら c、y = 1 なら無し）。 -/
def dpend (y : Nat) : List Nat := if y = 0 then [0] else if y = 2 then [2] else []

/-- 1 番目のセルの 1 回の要求: (状態 y, 消費した数, 出した文字の列)。y = 1 は中身 1、y = 0・2 は中身 0
    （0 は次に a、2 は次に c を出す）。y = 1 で読んだ文字が b なら、続く c も読んで a を出す。 -/
def dstep (s : Nat × Nat × List Nat) : Nat × Nat × List Nat :=
  if s.1 = 0 then (1, s.2.1, s.2.2 ++ [0])
  else if s.1 = 2 then (1, s.2.1, s.2.2 ++ [2])
  else if s.2.2.getD s.2.1 0 = 1 then (0, s.2.1 + 2, s.2.2 ++ [0])
  else (2, s.2.1 + 1, s.2.2 ++ [1])

/-- n 回の要求のあとの 1 番目のセル。 -/
def dst : Nat → Nat × Nat × List Nat
  | 0 => (0, 0, [])
  | n + 1 => dstep (dst n)

/-- n 回目の応答（細分した文字）。 -/
def wl (n : Nat) : Nat := (dst (n + 1)).2.2.getD n 0

/-- 文字から応答の状態へ（b は q2、a・c は q1）。 -/
def dproj (q1 q2 ℓ : Nat) : Nat := if ℓ = 1 then q2 else q1

/-- n 回の訪問のあとの右の中身（セル k の記号）。 -/
def pd : Nat → Nat → Nat
  | n, 0 => if (dst n).1 = 1 then 1 else 0
  | n, k + 1 => pd (dst n).2.1 k

theorem dst_succ (n : Nat) : dst (n + 1) = dstep (dst n) := rfl

theorem getD_snoc (l : List Nat) (x i : Nat) :
    (l ++ [x]).getD i 0 = if i < l.length then l.getD i 0 else if i = l.length then x else 0 := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_eq_none (by simp; omega)]; rfl

theorem dsig_len (x : Nat) : 1 ≤ (dsig x).length ∧ (dsig x).length ≤ 2 := by
  unfold dsig; split <;> simp

theorem flatMap_dsig_len : ∀ l : List Nat, l.length ≤ (l.flatMap dsig).length
  | [] => by simp
  | x :: l => by
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have := (dsig_len x).1; have := flatMap_dsig_len l; omega

theorem take_succ_getD {l : List Nat} {m : Nat} (h : m < l.length) :
    l.take (m + 1) = l.take m ++ [l.getD m 0] := by
  rw [List.take_add_one, List.getElem?_eq_getElem h]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

/-- カスケードの不変条件（n 回の要求のあとの状態 y、消費した数 m、出した文字の列 out）。 -/
structure DI (n y m : Nat) (out : List Nat) : Prop where
  len : out.length = n
  ylt : y < 3
  vals : ∀ i, out.getD i 0 < 3
  inv : 0 :: (out.take m).flatMap dsig = out ++ dpend y
  y2 : y = 2 ↔ (1 ≤ n ∧ out.getD (n - 1) 0 = 1)
  bnd : m = 0 ∨ out.getD (m - 1) 0 ≠ 1
  cpre : ∀ i, i < n → out.getD i 0 = 2 → 1 ≤ i ∧ out.getD (i - 1) 0 = 1
  bfol : ∀ i, i + 1 < n → out.getD i 0 = 1 → out.getD (i + 1) 0 = 2
  mle : m ≤ n

section dcases
variable {n y m : Nat} {out : List Nat}

/-- y = 1 なら、消費した数は n より小さい（不変条件の長さから）。 -/
theorem DI.m_lt (h : DI n 1 m out) : m < n := by
  have hl := congrArg List.length h.inv
  have hp : dpend 1 = [] := rfl
  rw [hp, List.append_nil, List.length_cons, h.len] at hl
  have := flatMap_dsig_len (out.take m)
  rw [List.length_take, h.len] at this
  omega

theorem DI.c0 (h : DI n 0 m out) : DI (n + 1) 1 m (out ++ [0]) := by
  obtain ⟨hlen, -, hvals, hinv, hy2, hbnd, hcpre, hbfol, hmle⟩ := h
  have gs : ∀ i, (out ++ [0]).getD i 0 = if i < n then out.getD i 0 else if i = n then 0 else 0 := by
    intro i; rw [getD_snoc, hlen]
  have hn1 : ¬ (1 ≤ n ∧ out.getD (n - 1) 0 = 1) := fun hh => absurd (hy2.mpr hh) (by decide)
  refine ⟨by simp [hlen], by decide, ?_, ?_, ?_, ?_, ?_, ?_, by omega⟩
  · intro i; rw [gs]; split_ifs
    · exact hvals i
    all_goals decide
  · rw [List.take_append_of_le_length (by rw [hlen]; exact hmle), hinv]; simp [dpend]
  · rw [show n + 1 - 1 = n by omega, gs, if_neg (Nat.lt_irrefl n), if_pos rfl]; simp
  · rcases Nat.eq_zero_or_pos m with h0 | h0
    · exact Or.inl h0
    · right; rcases hbnd with h1 | h1
      · omega
      · rw [gs, if_pos (by omega)]; exact h1
  · intro i hi h2'
    rcases Nat.lt_or_ge i n with hi1 | hi1
    · rw [gs, if_pos hi1] at h2'
      obtain ⟨a1, a2⟩ := hcpre i hi1 h2'
      exact ⟨a1, by rw [gs, if_pos (by omega)]; exact a2⟩
    · rw [gs, if_neg (by omega), if_pos (by omega)] at h2'
      exact absurd h2' (by decide)
  · intro i hi h1'
    have hi1 : i < n := by omega
    rw [gs, if_pos hi1] at h1'
    by_cases hin : i + 1 < n
    · rw [gs, if_pos hin]; exact hbfol i hin h1'
    · exfalso; exact hn1 ⟨by omega, by rw [show n - 1 = i by omega]; exact h1'⟩

theorem DI.c2 (h : DI n 2 m out) : DI (n + 1) 1 m (out ++ [2]) := by
  obtain ⟨hlen, -, hvals, hinv, hy2, hbnd, hcpre, hbfol, hmle⟩ := h
  have gs : ∀ i, (out ++ [2]).getD i 0 = if i < n then out.getD i 0 else if i = n then 2 else 0 := by
    intro i; rw [getD_snoc, hlen]
  obtain ⟨hn1, hn2⟩ := hy2.mp rfl
  refine ⟨by simp [hlen], by decide, ?_, ?_, ?_, ?_, ?_, ?_, by omega⟩
  · intro i; rw [gs]; split_ifs
    · exact hvals i
    all_goals decide
  · rw [List.take_append_of_le_length (by rw [hlen]; exact hmle), hinv]; simp [dpend]
  · rw [show n + 1 - 1 = n by omega, gs, if_neg (Nat.lt_irrefl n), if_pos rfl]; simp
  · rcases Nat.eq_zero_or_pos m with h0 | h0
    · exact Or.inl h0
    · right; rcases hbnd with h1 | h1
      · omega
      · rw [gs, if_pos (by omega)]; exact h1
  · intro i hi h2'
    rcases Nat.lt_or_ge i n with hi1 | hi1
    · rw [gs, if_pos hi1] at h2'
      obtain ⟨a1, a2⟩ := hcpre i hi1 h2'
      exact ⟨a1, by rw [gs, if_pos (by omega)]; exact a2⟩
    · obtain rfl : i = n := by omega
      exact ⟨hn1, by rw [gs, if_pos (by omega)]; exact hn2⟩
  · intro i hi h1'
    have hi1 : i < n := by omega
    rw [gs, if_pos hi1] at h1'
    by_cases hin : i + 1 < n
    · rw [gs, if_pos hin]; exact hbfol i hin h1'
    · rw [gs, if_neg hin, if_pos (by omega)]

theorem DI.cb (h : DI n 1 m out) (hb : out.getD m 0 = 1) : DI (n + 1) 0 (m + 2) (out ++ [0]) := by
  have hm := h.m_lt
  obtain ⟨hlen, -, hvals, hinv, hy2, hbnd, hcpre, hbfol, hmle⟩ := h
  have gs : ∀ i, (out ++ [0]).getD i 0 = if i < n then out.getD i 0 else if i = n then 0 else 0 := by
    intro i; rw [getD_snoc, hlen]
  have hn1 : ¬ (1 ≤ n ∧ out.getD (n - 1) 0 = 1) := fun hh => absurd (hy2.mpr hh) (by decide)
  have hm1 : m + 1 < n := by
    by_contra hc
    exact hn1 ⟨by omega, by rw [show n - 1 = m by omega]; exact hb⟩
  have hc := hbfol m hm1 hb
  refine ⟨by simp [hlen], by decide, ?_, ?_, ?_, ?_, ?_, ?_, by omega⟩
  · intro i; rw [gs]; split_ifs
    · exact hvals i
    all_goals decide
  · rw [List.take_append_of_le_length (by rw [hlen]; omega),
      show m + 2 = (m + 1) + 1 by omega, take_succ_getD (by rw [hlen]; omega),
      take_succ_getD (by rw [hlen]; omega), hb, hc, List.flatMap_append, List.flatMap_append,
      ← List.cons_append, ← List.cons_append, hinv]
    simp [dsig, dpend]
  · rw [show n + 1 - 1 = n by omega, gs, if_neg (Nat.lt_irrefl n), if_pos rfl]; simp
  · right
    rw [show m + 2 - 1 = m + 1 by omega, gs, if_pos hm1, hc]; decide
  · intro i hi h2'
    rcases Nat.lt_or_ge i n with hi1 | hi1
    · rw [gs, if_pos hi1] at h2'
      obtain ⟨a1, a2⟩ := hcpre i hi1 h2'
      exact ⟨a1, by rw [gs, if_pos (by omega)]; exact a2⟩
    · rw [gs, if_neg (by omega), if_pos (by omega)] at h2'
      exact absurd h2' (by decide)
  · intro i hi h1'
    have hi1 : i < n := by omega
    rw [gs, if_pos hi1] at h1'
    by_cases hin : i + 1 < n
    · rw [gs, if_pos hin]; exact hbfol i hin h1'
    · exfalso; exact hn1 ⟨by omega, by rw [show n - 1 = i by omega]; exact h1'⟩

theorem DI.ca (h : DI n 1 m out) (ha : out.getD m 0 ≠ 1) : DI (n + 1) 2 (m + 1) (out ++ [1]) := by
  have hm := h.m_lt
  obtain ⟨hlen, -, hvals, hinv, hy2, hbnd, hcpre, hbfol, hmle⟩ := h
  have gs : ∀ i, (out ++ [1]).getD i 0 = if i < n then out.getD i 0 else if i = n then 1 else 0 := by
    intro i; rw [getD_snoc, hlen]
  have hn1 : ¬ (1 ≤ n ∧ out.getD (n - 1) 0 = 1) := fun hh => absurd (hy2.mpr hh) (by decide)
  have ha0 : out.getD m 0 = 0 := by
    have := hvals m
    by_contra hne
    have h2 : out.getD m 0 = 2 := by omega
    obtain ⟨a1, a2⟩ := hcpre m hm h2
    rcases hbnd with h0 | h0
    · omega
    · exact h0 a2
  refine ⟨by simp [hlen], by decide, ?_, ?_, ?_, ?_, ?_, ?_, by omega⟩
  · intro i; rw [gs]; split_ifs
    · exact hvals i
    all_goals decide
  · rw [List.take_append_of_le_length (by rw [hlen]; omega), take_succ_getD (by rw [hlen]; omega), ha0,
      List.flatMap_append, ← List.cons_append, hinv]
    simp [dsig, dpend]
  · rw [show n + 1 - 1 = n by omega, gs, if_neg (Nat.lt_irrefl n), if_pos rfl]; simp
  · right
    rw [show m + 1 - 1 = m by omega, gs, if_pos hm, ha0]; decide
  · intro i hi h2'
    rcases Nat.lt_or_ge i n with hi1 | hi1
    · rw [gs, if_pos hi1] at h2'
      obtain ⟨a1, a2⟩ := hcpre i hi1 h2'
      exact ⟨a1, by rw [gs, if_pos (by omega)]; exact a2⟩
    · rw [gs, if_neg (by omega), if_pos (by omega)] at h2'
      exact absurd h2' (by decide)
  · intro i hi h1'
    have hi1 : i < n := by omega
    rw [gs, if_pos hi1] at h1'
    by_cases hin : i + 1 < n
    · rw [gs, if_pos hin]; exact hbfol i hin h1'
    · exfalso; exact hn1 ⟨by omega, by rw [show n - 1 = i by omega]; exact h1'⟩

end dcases

theorem dstep_y1b (m : Nat) (out : List Nat) (h : out.getD m 0 = 1) :
    dstep (1, m, out) = (0, m + 2, out ++ [0]) := by
  unfold dstep
  rw [if_neg (by simp), if_neg (by simp), if_pos h]

theorem dstep_y1a (m : Nat) (out : List Nat) (h : out.getD m 0 ≠ 1) :
    dstep (1, m, out) = (2, m + 1, out ++ [1]) := by
  unfold dstep
  rw [if_neg (by simp), if_neg (by simp), if_neg h]

/-- **カスケードの不変条件はいつも成り立つ**。 -/
theorem dinv : ∀ n, DI n (dst n).1 (dst n).2.1 (dst n).2.2
  | 0 => {
      len := rfl
      ylt := by decide
      vals := fun i => by simp [dst]
      inv := rfl
      y2 := by simp [dst]
      bnd := Or.inl rfl
      cpre := fun i hi => absurd hi (by omega)
      bfol := fun i hi => absurd hi (by omega)
      mle := le_refl 0 }
  | n + 1 => by
    have h := dinv n
    rw [dst_succ]
    rcases hd : dst n with ⟨y, m, out⟩
    rw [hd] at h
    have hylt := h.ylt
    rcases (by omega : y = 0 ∨ y = 1 ∨ y = 2) with rfl | rfl | rfl
    · exact h.c0
    · by_cases hb : out.getD m 0 = 1
      · rw [dstep_y1b m out hb]; exact h.cb hb
      · rw [dstep_y1a m out hb]; exact h.ca hb
    · exact h.c2

theorem DI.m1_lt {n m : Nat} {out : List Nat} (h : DI n 1 m out) (hb : out.getD m 0 = 1) : m + 1 < n := by
  have hm := h.m_lt
  by_contra hc
  have := h.y2.mpr ⟨by omega, by rw [show n - 1 = m by omega]; exact hb⟩
  exact absurd this (by decide)

/-- n 回目の要求の直後の状態（4 通り）。 -/
theorem dst_cases (n : Nat) :
    ((dst n).1 = 0 ∧ dst (n + 1) = (1, (dst n).2.1, (dst n).2.2 ++ [0])) ∨
    ((dst n).1 = 2 ∧ dst (n + 1) = (1, (dst n).2.1, (dst n).2.2 ++ [2])) ∨
    ((dst n).1 = 1 ∧ (dst n).2.2.getD (dst n).2.1 0 = 1 ∧
      dst (n + 1) = (0, (dst n).2.1 + 2, (dst n).2.2 ++ [0])) ∨
    ((dst n).1 = 1 ∧ (dst n).2.2.getD (dst n).2.1 0 ≠ 1 ∧
      dst (n + 1) = (2, (dst n).2.1 + 1, (dst n).2.2 ++ [1])) := by
  rw [dst_succ]
  have hylt := (dinv n).ylt
  rcases hd : dst n with ⟨y, m, out⟩
  rw [hd] at hylt
  simp only
  rcases (by omega : y = 0 ∨ y = 1 ∨ y = 2) with rfl | rfl | rfl
  · exact Or.inl ⟨rfl, rfl⟩
  · by_cases hb : out.getD m 0 = 1
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, hb, dstep_y1b m out hb⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨rfl, hb, dstep_y1a m out hb⟩))
  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)

theorem wl_of {n y' m' x : Nat} (h : dst (n + 1) = (y', m', (dst n).2.2 ++ [x])) : wl n = x := by
  unfold wl; rw [h]
  show ((dst n).2.2 ++ [x]).getD n 0 = x
  rw [getD_snoc, (dinv n).len, if_neg (Nat.lt_irrefl n), if_pos rfl]

theorem dst_get_succ (n i : Nat) (hi : i < n) : (dst (n + 1)).2.2.getD i 0 = (dst n).2.2.getD i 0 := by
  have hl := (dinv n).len
  rcases dst_cases n with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩ <;>
    (rw [h]; show ((dst n).2.2 ++ [_]).getD i 0 = _; rw [getD_snoc, hl, if_pos hi])

theorem dst_get (n i : Nat) (hi : i < n) : (dst n).2.2.getD i 0 = wl i := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge i n with h | h
    · rw [dst_get_succ n i h, ih h]
    · obtain rfl : i = n := by omega
      rfl

/-! ### 訪問 -/

section visit2
variable {tbl : List Quint} {e q1 q2 f' g : Nat} (H : Cell2 tbl e q1 q2 f' g)
include H

/-- **カスケードの訪問**: 右の中身が `pd n` なら、状態 e で b+1 に入った訪問は応答 `dproj q1 q2 (wl n)` で b に戻り、
    中身は `pd (n+1)` になる。訪問中のヘッドは b+1 から b+1+n。 -/
theorem cell2_visit : ∀ n (b : Int) (t : Int → Nat), rpart b t = pd n →
    ∃ k t', qrun tbl k ⟨e, b + 1, t⟩ = some ⟨dproj q1 q2 (wl n), b, t'⟩ ∧
      (∀ x, x ≤ b → t' x = t x) ∧ rpart b t' = pd (n + 1) ∧
      ∀ i, i < k → ∀ d, qrun tbl i ⟨e, b + 1, t⟩ = some d → b + 1 ≤ d.pos ∧ d.pos ≤ b + 1 + n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro b t ht
  have hx0 : t (b + 1) = if (dst n).1 = 1 then 1 else 0 := by
    have := congrFun ht 0; simpa [rpart, pd] using this
  -- 即答（中身 0）
  have imm : ∀ x, (dst n).1 ≠ 1 → dst (n + 1) = (1, (dst n).2.1, (dst n).2.2 ++ [x]) → x ≠ 1 →
      ∃ k t', qrun tbl k ⟨e, b + 1, t⟩ = some ⟨dproj q1 q2 (wl n), b, t'⟩ ∧
        (∀ x, x ≤ b → t' x = t x) ∧ rpart b t' = pd (n + 1) ∧
        ∀ i, i < k → ∀ d, qrun tbl i ⟨e, b + 1, t⟩ = some d → b + 1 ≤ d.pos ∧ d.pos ≤ b + 1 + n := by
    intro x hy hn1 hx
    have ht0 : t (b + 1) = 0 := by rw [hx0, if_neg hy]
    have hw : dproj q1 q2 (wl n) = q1 := by rw [wl_of hn1]; unfold dproj; rw [if_neg hx]
    refine ⟨1, write t (b + 1) 1, ?_, fun x hx' => write_off _ _ _ (by omega), ?_, ?_⟩
    · rw [qrun_succ_some tbl 0 (qstep_of_find (by simp only; rw [ht0]; exact H.h00))]
      show some (⟨q1, move Dir.L (b + 1), write t (b + 1) 1⟩ : QConf) =
        some (⟨dproj q1 q2 (wl n), b, write t (b + 1) 1⟩ : QConf)
      rw [hw]; simp [move]
    · funext k
      cases k with
      | zero =>
        show write t (b + 1) 1 (b + 1 + ((0 : Nat) : Int)) = pd (n + 1) 0
        simp only [pd, write, hn1]; simp
      | succ k =>
        show write t (b + 1) 1 (b + 1 + ((k + 1 : Nat) : Int)) = pd (n + 1) (k + 1)
        rw [write_off _ _ _ (by omega)]
        have := congrFun ht (k + 1)
        simp only [rpart] at this
        rw [this]
        show pd (dst n).2.1 k = pd (dst (n + 1)).2.1 k
        rw [hn1]
    · intro i hi d hd
      obtain rfl : i = 0 := by omega
      simp only [qrun, Option.some.injEq] at hd
      subst hd; simp only; omega
  rcases dst_cases n with ⟨hy, hn1⟩ | ⟨hy, hn1⟩ | ⟨hy, hb, hn1⟩ | ⟨hy, ha, hn1⟩
  · exact imm 0 (by rw [hy]; decide) hn1 (by decide)
  · exact imm 2 (by rw [hy]; decide) hn1 (by decide)
  all_goals
    have hI : DI n 1 (dst n).2.1 (dst n).2.2 := hy ▸ dinv n
    have hm := hI.m_lt
    have ht1 : t (b + 1) = 1 := by rw [hx0, if_pos hy]
    have hs1 : qstep tbl ⟨e, b + 1, t⟩ = some ⟨e, b + 1 + 1, write t (b + 1) f'⟩ := by
      rw [qstep_of_find (by simp only; rw [ht1]; exact H.h01)]; rfl
    have hr1 : rpart (b + 1) (write t (b + 1) f') = pd (dst n).2.1 := by
      funext k
      show write t (b + 1) f' (b + 1 + 1 + k) = _
      rw [write_off _ _ _ (by omega)]
      have := congrFun ht (k + 1)
      simp only [rpart] at this
      rw [show b + 1 + 1 + (k : Int) = b + 1 + ((k + 1 : Nat) : Int) by push_cast; omega, this]
      rfl
    obtain ⟨k1, t2, hrun1, hag1, hr2, hpos1⟩ := ih _ hm (b + 1) _ hr1
    have ht2 : t2 (b + 1) = f' := by rw [hag1 _ le_rfl]; simp [write]
    have e1 : qrun tbl 1 ⟨e, b + 1, t⟩ = some ⟨e, b + 1 + 1, write t (b + 1) f'⟩ := by
      rw [qrun_succ_some tbl 0 hs1]; rfl
  · -- b を読んだ: もう一度転送
    have hm1 := hI.m1_lt hb
    have hbw : wl (dst n).2.1 = 1 := by rw [← dst_get n _ hm]; exact hb
    have hc : wl ((dst n).2.1 + 1) = 2 := by rw [← dst_get n _ hm1]; exact hI.bfol _ hm1 hb
    have hq : dproj q1 q2 (wl (dst n).2.1) = q2 := by unfold dproj; rw [if_pos hbw]
    have hs2 : qstep tbl ⟨dproj q1 q2 (wl (dst n).2.1), b + 1, t2⟩ =
        some ⟨e, b + 1 + 1, write t2 (b + 1) g⟩ := by
      rw [hq, qstep_of_find (by simp only; rw [ht2]; exact H.hB1)]; rfl
    have hr3 : rpart (b + 1) (write t2 (b + 1) g) = pd ((dst n).2.1 + 1) := by
      funext k
      show write t2 (b + 1) g (b + 1 + 1 + k) = _
      rw [write_off _ _ _ (by omega)]
      exact congrFun hr2 k
    obtain ⟨k2, t3, hrun2, hag2, hr4, hpos2⟩ := ih _ (by omega) (b + 1) _ hr3
    have ht3 : t3 (b + 1) = g := by rw [hag2 _ le_rfl]; simp [write]
    have hq' : dproj q1 q2 (wl ((dst n).2.1 + 1)) = q1 := by rw [hc]; rfl
    have hs3 : qstep tbl ⟨dproj q1 q2 (wl ((dst n).2.1 + 1)), b + 1, t3⟩ =
        some ⟨q1, b, write t3 (b + 1) 0⟩ := by
      rw [hq', qstep_of_find (by simp only; rw [ht3]; exact H.hB2)]
      show some (⟨q1, b + 1 - 1, _⟩ : QConf) = _
      rw [show b + 1 - 1 = b by omega]
    have e2 : qrun tbl 1 ⟨dproj q1 q2 (wl (dst n).2.1), b + 1, t2⟩ =
        some ⟨e, b + 1 + 1, write t2 (b + 1) g⟩ := by
      rw [qrun_succ_some tbl 0 hs2]; rfl
    have e3 : qrun tbl 1 ⟨dproj q1 q2 (wl ((dst n).2.1 + 1)), b + 1, t3⟩ =
        some ⟨q1, b, write t3 (b + 1) 0⟩ := by
      rw [qrun_succ_some tbl 0 hs3]; rfl
    have hw : dproj q1 q2 (wl n) = q1 := by rw [wl_of hn1]; rfl
    refine ⟨1 + (k1 + (1 + (k2 + 1))), write t3 (b + 1) 0, ?_, ?_, ?_, ?_⟩
    · rw [qrun_add, e1, Option.bind_some, qrun_add, hrun1, Option.bind_some, qrun_add, e2,
        Option.bind_some, qrun_add, hrun2, Option.bind_some, e3, hw]
    · intro x hxb
      rw [write_off _ _ _ (by omega), hag2 x (by omega), write_off _ _ _ (by omega), hag1 x (by omega),
        write_off _ _ _ (by omega)]
    · funext k
      cases k with
      | zero =>
        show write t3 (b + 1) 0 (b + 1 + ((0 : Nat) : Int)) = pd (n + 1) 0
        simp only [pd, write, hn1]; simp
      | succ k =>
        show write t3 (b + 1) 0 (b + 1 + ((k + 1 : Nat) : Int)) = pd (n + 1) (k + 1)
        rw [write_off _ _ _ (by omega)]
        have := congrFun hr4 k
        simp only [rpart] at this
        rw [show b + 1 + ((k + 1 : Nat) : Int) = b + 1 + 1 + (k : Int) by push_cast; omega, this]
        show pd ((dst n).2.1 + 1 + 1) k = pd (dst (n + 1)).2.1 k
        rw [hn1]
    · intro i hi d hd
      rcases Nat.eq_zero_or_pos i with h0 | hpos
      · subst h0; simp only [qrun, Option.some.injEq] at hd; subst hd; simp only; omega
      · obtain ⟨i', rfl⟩ : ∃ i', i = 1 + i' := ⟨i - 1, by omega⟩
        rw [qrun_add, e1, Option.bind_some] at hd
        rcases Nat.lt_or_ge i' k1 with hlt | hge
        · have := hpos1 i' hlt d hd; constructor <;> omega
        · obtain ⟨j, rfl⟩ : ∃ j, i' = k1 + j := ⟨i' - k1, by omega⟩
          rw [qrun_add, hrun1, Option.bind_some] at hd
          rcases Nat.eq_zero_or_pos j with hj0 | hjpos
          · subst hj0; simp only [qrun, Option.some.injEq] at hd; subst hd; simp only; omega
          · obtain ⟨j', rfl⟩ : ∃ j', j = 1 + j' := ⟨j - 1, by omega⟩
            rw [qrun_add, e2, Option.bind_some] at hd
            rcases Nat.lt_or_ge j' k2 with hlt2 | hge2
            · have := hpos2 j' hlt2 d hd; constructor <;> omega
            · obtain rfl : j' = k2 := by omega
              rw [hrun2] at hd
              simp only [Option.some.injEq] at hd
              subst hd; simp only; omega
  · -- a を読んだ: q2 で即答
    have haw : wl (dst n).2.1 ≠ 1 := by rw [← dst_get n _ hm]; exact ha
    have hq : dproj q1 q2 (wl (dst n).2.1) = q1 := by unfold dproj; rw [if_neg haw]
    have hs2 : qstep tbl ⟨dproj q1 q2 (wl (dst n).2.1), b + 1, t2⟩ = some ⟨q2, b, write t2 (b + 1) 0⟩ := by
      rw [hq, qstep_of_find (by simp only; rw [ht2]; exact H.hA)]
      show some (⟨q2, b + 1 - 1, _⟩ : QConf) = _
      rw [show b + 1 - 1 = b by omega]
    have e2 : qrun tbl 1 ⟨dproj q1 q2 (wl (dst n).2.1), b + 1, t2⟩ = some ⟨q2, b, write t2 (b + 1) 0⟩ := by
      rw [qrun_succ_some tbl 0 hs2]; rfl
    have hw : dproj q1 q2 (wl n) = q2 := by rw [wl_of hn1]; rfl
    refine ⟨1 + (k1 + 1), write t2 (b + 1) 0, ?_, ?_, ?_, ?_⟩
    · rw [qrun_add, e1, Option.bind_some, qrun_add, hrun1, Option.bind_some, e2, hw]
    · intro x hxb
      rw [write_off _ _ _ (by omega), hag1 x (by omega), write_off _ _ _ (by omega)]
    · funext k
      cases k with
      | zero =>
        show write t2 (b + 1) 0 (b + 1 + ((0 : Nat) : Int)) = pd (n + 1) 0
        simp only [pd, write, hn1]; simp
      | succ k =>
        show write t2 (b + 1) 0 (b + 1 + ((k + 1 : Nat) : Int)) = pd (n + 1) (k + 1)
        rw [write_off _ _ _ (by omega)]
        have := congrFun hr2 k
        simp only [rpart] at this
        rw [show b + 1 + ((k + 1 : Nat) : Int) = b + 1 + 1 + (k : Int) by push_cast; omega, this]
        show pd ((dst n).2.1 + 1) k = pd (dst (n + 1)).2.1 k
        rw [hn1]
    · intro i hi d hd
      rcases Nat.eq_zero_or_pos i with h0 | hpos
      · subst h0; simp only [qrun, Option.some.injEq] at hd; subst hd; simp only; omega
      · obtain ⟨i', rfl⟩ : ∃ i', i = 1 + i' := ⟨i - 1, by omega⟩
        rw [qrun_add, e1, Option.bind_some] at hd
        rcases Nat.lt_or_ge i' k1 with hlt | hge
        · have := hpos1 i' hlt d hd; constructor <;> omega
        · obtain rfl : i' = k1 := by omega
          rw [hrun1] at hd
          simp only [Option.some.injEq] at hd
          subst hd; simp only; omega

end visit2


/-! ### 実行との対応（`run_chain` の写し） -/

/-- 応答の列の n 番目から V 個（状態に戻したもの）。 -/
def wslJ (q1 q2 n V : Nat) : List Nat := (List.range V).map fun i => dproj q1 q2 (wl (n + i))

theorem wslJ_succ (q1 q2 n V : Nat) : wslJ q1 q2 n (V + 1) = dproj q1 q2 (wl n) :: wslJ q1 q2 (n + 1) V := by
  unfold wslJ
  rw [List.range_succ_eq_map]
  simp only [List.map_cons, List.map_map, Nat.add_zero]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp]
  congr 2; omega

section chain2
variable {tbl : List Quint} {e q1 q2 f' g : Nat} (H : Cell2 tbl e q1 q2 f' g)
  {c0 : QConf} {T : Nat} (hR : QHaltRun tbl c0 T) {lo b : Int}
  (hzero : ∀ t, t ≤ T → ∀ x, x < lo → (qtr tbl c0 t).tape x = 0)
  (h2 : ∀ t, t ≤ T → ∀ x, (qtr tbl c0 t).tape x < 2)
include H hR hzero h2

/-- **実行と自動機械の対応**: 時刻 t0 に b 以下に居て右の中身が `pc n` なら、自動機械の連鎖は応答 wc n, wc (n+1), … を
    読んでちょうど V 個目で初めて「止まった」に入り、以後のヘッドは b+1+n+V 以下（V は残りの訪問の数）。 -/
theorem run_chain2 : ∀ m t0 n, T - t0 = m → t0 ≤ T → (qtr tbl c0 t0).pos ≤ b →
    rpart b (qtr tbl c0 t0).tape = pd n →
    ∃ V, (wslJ q1 q2 n V).foldl (wdelta tbl lo b) (phase tbl lo b (qtr tbl c0 t0)) = none ∧
      (∀ i, i < V → (wslJ q1 q2 n i).foldl (wdelta tbl lo b) (phase tbl lo b (qtr tbl c0 t0)) ≠ none) ∧
      ∀ t, t0 ≤ t → t ≤ T → (qtr tbl c0 t).pos ≤ b + 1 + n + V := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro t0 n hm ht0 hb0 hrp
  classical
  have hrun : ∀ s, t0 + s ≤ T → qrun tbl s (qtr tbl c0 t0) = some (qtr tbl c0 (t0 + s)) :=
    fun s hs => hR.run_mid t0 s hs
  have hdead : ∀ s, T < t0 + s → qrun tbl s (qtr tbl c0 t0) = none := by
    intro s hs
    exact qrun_none_mono tbl _ (T + 1 - t0) s (hR.run_from t0 ht0) (by omega)
  have hE : ∃ t, wev tbl b (qtr tbl c0 t0) t :=
    ⟨T - t0, by unfold wev; rw [hdead _ (by omega)]; trivial⟩
  obtain ⟨ts, hts⟩ : ∃ ts, ts = Nat.find hE := ⟨_, rfl⟩
  have hno : ∀ s, s < ts → ¬ wev tbl b (qtr tbl c0 t0) s := fun s hs => Nat.find_min hE (hts ▸ hs)
  -- 出来事の前は b 以下で、実行は生きている
  have hbelow : ∀ s, s ≤ ts → t0 + s ≤ T ∧ (qtr tbl c0 (t0 + s)).pos ≤ b := by
    intro s hs
    rcases Nat.eq_zero_or_pos s with h0 | hpos
    · subst h0; exact ⟨by omega, hb0⟩
    · have h' := hno (s - 1) (by omega)
      unfold wev at h'
      rw [show s - 1 + 1 = s by omega] at h'
      by_cases hsT : t0 + s ≤ T
      · rw [hrun s hsT] at h'; exact ⟨hsT, by simp only at h'; omega⟩
      · rw [hdead s (by omega)] at h'; exact absurd trivial h'
  have hev : wev tbl b (qtr tbl c0 t0) ts := hts ▸ Nat.find_spec hE
  unfold wev at hev
  have hph : phase tbl lo b (qtr tbl c0 t0) = wres lo b (qrun tbl (ts + 1) (qtr tbl c0 t0)) := by
    unfold phase; rw [dif_pos hE, ← hts]
  obtain ⟨hts1, hbts⟩ := hbelow (ts) le_rfl
  by_cases hT : t0 + ts + 1 ≤ T
  · -- 訪問が始まる
    rw [hrun (ts + 1) (by omega)] at hev hph
    obtain ⟨t1, ht1⟩ : ∃ t1, t1 = t0 + ts := ⟨_, rfl⟩
    have ht1' : t0 + (ts + 1) = t1 + 1 := by omega
    rw [ht1'] at hev hph
    have hbt1 : (qtr tbl c0 t1).pos ≤ b := by rw [ht1]; exact hbts
    obtain ⟨ρ, hρ, _, e1⟩ := qstep_some (hR.step t1 (by omega))
    have hd : ρ.d = Dir.R := by
      cases hrd : ρ.d with
      | L => rw [e1, hrd] at hev; simp [move] at hev; omega
      | Z => rw [e1, hrd] at hev; simp [move] at hev; omega
      | R => rfl
    have hpos1 : (qtr tbl c0 (t1 + 1)).pos = b + 1 := by
      have := hev; rw [e1, hd] at this ⊢; simp [move] at this ⊢; omega
    have hst1 : (qtr tbl c0 (t1 + 1)).st = e := by rw [e1]; exact H.hent ρ hρ hd
    have hq1 : qtr tbl c0 (t1 + 1) = ⟨e, b + 1, (qtr tbl c0 (t1 + 1)).tape⟩ := by
      rw [← hst1, ← hpos1]
    -- 右の中身は pc n のまま
    have hrp1 : rpart b (qtr tbl c0 (t1 + 1)).tape = pd n := by
      have := rpart_const hR b (t0 := t0) (ts + 1) (by omega) (fun u h1 h2' => by
        have := (hbelow (u - t0) (by omega)).2
        rwa [show t0 + (u - t0) = u by omega] at this)
      rw [ht1'] at this; rw [this]; exact hrp
    obtain ⟨k, t', hvis, hag, hr', hvpos⟩ := cell2_visit H n b _ hrp1
    rw [← hq1] at hvis
    obtain ⟨hkT, hq2⟩ := qtr_of_run hR (by omega) hvis
    -- 帰納法
    obtain ⟨V', hV1, hV2, hV3⟩ := ih (T - (t1 + 1 + k)) (by omega) (t1 + 1 + k) (n + 1) rfl hkT
      (by rw [hq2]) (by rw [hq2]; exact hr')
    -- 自動機械の 1 歩は、戻った配置からの段
    have hstep : wdelta tbl lo b (phase tbl lo b (qtr tbl c0 t0)) (dproj q1 q2 (wl n)) =
        phase tbl lo b (qtr tbl c0 (t1 + 1 + k)) := by
      rw [hph]
      show phase tbl lo b ⟨dproj q1 q2 (wl n), b, wdec lo b (wenc lo b (qtr tbl c0 (t1 + 1)).tape)⟩ = _
      apply phase_cut _ (le_refl b)
      rw [hq2]
      refine cut_eq_of (c₁ := ⟨dproj q1 q2 (wl n), b, wdec lo b (wenc lo b (qtr tbl c0 (t1 + 1)).tape)⟩)
        (c₂ := ⟨dproj q1 q2 (wl n), b, t'⟩) b rfl rfl ?_
      intro x hx
      show wdec lo b (wenc lo b (qtr tbl c0 (t1 + 1)).tape) x = t' x
      rw [hag x hx]
      by_cases hxl : lo ≤ x
      · exact wdec_wenc (h2 (t1 + 1) (by omega)) hxl hx
      · rw [wdec_out (by omega), hzero (t1 + 1) (by omega) x (by omega)]
    refine ⟨V' + 1, ?_, ?_, ?_⟩
    · rw [wslJ_succ, List.foldl_cons, hstep]; exact hV1
    · intro i hi
      rcases Nat.eq_zero_or_pos i with h0 | hpos
      · subst h0; simp only [wslJ, List.range_zero, List.map_nil, List.foldl_nil]
        rw [hph]; simp [wres]
      · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
        rw [wslJ_succ, List.foldl_cons, hstep]; exact hV2 i' (by omega)
    · intro t htt0 htT
      by_cases hA : t ≤ t1
      · have := (hbelow (t - t0) (by omega)).2
        rw [show t0 + (t - t0) = t by omega] at this; omega
      · by_cases hB : t < t1 + 1 + k
        · have hr1 : qrun tbl (t - (t1 + 1)) ⟨e, b + 1, (qtr tbl c0 (t1 + 1)).tape⟩ = some (qtr tbl c0 t) := by
            rw [← hq1, hR.run_at (by omega)]; congr 1; congr 1; omega
          have := hvpos (t - (t1 + 1)) (by omega) _ hr1
          omega
        · have := hV3 t (by omega) htT
          push_cast at this ⊢; omega
  · -- 窓の中で止まる
    have hTe : t0 + ts = T := by omega
    rw [hdead (ts + 1) (by omega)] at hph
    refine ⟨0, ?_, fun i hi => absurd hi (by omega), ?_⟩
    · simp only [wslJ, List.range_zero, List.map_nil, List.foldl_nil]; rw [hph]; rfl
    · intro t htt0 htT
      have := (hbelow (t - t0) (by omega)).2
      rw [show t0 + (t - t0) = t by omega] at this; omega

end chain2

/-! ### 応答の列は文字の射の不動点: w' = a σ(w') -/

/-- 消費した数は要求の数の半分以上。 -/
theorem dst_m_ge (n : Nat) : n ≤ 2 * (dst n).2.1 + 1 := by
  have hI := dinv n
  have hl := congrArg List.length hI.inv
  rw [List.length_cons, List.length_append, hI.len] at hl
  have h1 := len_flatMap_le (f := dsig) (B := 2) ((dst n).2.2.take (dst n).2.1) (fun x _ => (dsig_len x).2)
  rw [List.length_take, hI.len] at h1
  omega

/-- **U_j = a σ(a) … σ^j(a) は細分した応答の列の接頭辞**。 -/
theorem ublkJ_prefix : ∀ j i, i < (ublk dsig 0 j).length → wl i = (ublk dsig 0 j).getD i 0
  | 0, i, hi => by
    simp only [ublk, List.length_singleton] at hi
    obtain rfl : i = 0 := by omega
    rfl
  | j + 1, i, hi => by
    have ih := ublkJ_prefix j
    set u := ublk dsig 0 j with hu
    set M := (ublk dsig 0 (j + 1)).length with hM
    set n := 2 * u.length + M + 1 with hn
    have hI := dinv n
    have hmn : u.length ≤ (dst n).2.1 := by have := dst_m_ge n; omega
    have hmle := hI.mle
    have hl := hI.len
    have htake : ((dst n).2.2.take (dst n).2.1).take u.length = u := by
      rw [List.take_take, Nat.min_eq_left hmn]
      apply List.ext_getElem
      · rw [List.length_take, hl]; omega
      · intro k hk1 hk2
        rw [List.getElem_take]
        have hk1' : k < n := by rw [List.length_take] at hk1; omega
        have e1 := dst_get n k hk1'
        have e2 := ih k hk2
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hl]; exact hk1'),
          Option.getD_some] at e1
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk2, Option.getD_some] at e2
        rw [e1, e2]
    have hinv := hI.inv
    rw [← List.take_append_drop u.length ((dst n).2.2.take (dst n).2.1), htake,
      List.flatMap_append, ← List.cons_append] at hinv
    have hpre : ublk dsig 0 (j + 1) = 0 :: u.flatMap dsig := rfl
    have hiM : i < M := hi
    have hin : i < n := by omega
    have := congrArg (fun l => l.getD i 0) hinv
    rw [List.getD_append _ _ _ _ (by rw [← hpre]; exact hi), List.getD_append _ _ _ _ (by rw [hl]; exact hin),
      ← hpre] at this
    rw [this, dst_get n i hin]

theorem vblkJ_get (J i : Nat) (hi : i < (vblk dsig 0 J).length) : (vblk dsig 0 J).getD i 0 = wl i := by
  have hl : i < (ublk dsig 0 J).length := by
    rw [ublk_eq_vblk]
    show i < (vblk dsig 0 J ++ pw dsig J 0).length
    rw [List.length_append]; omega
  rw [ublkJ_prefix J i hl, ublk_eq_vblk]
  show (vblk dsig 0 J).getD i 0 = (vblk dsig 0 J ++ pw dsig J 0).getD i 0
  rw [List.getD_append _ _ _ _ hi]

theorem wslJ_vblk (q1 q2 J V : Nat) (hV : V ≤ (vblk dsig 0 J).length) :
    wslJ q1 q2 0 V = ((vblk dsig 0 J).take V).map (dproj q1 q2) := by
  apply List.ext_getElem
  · simp only [wslJ, List.length_map, List.length_range, List.length_take]; omega
  · intro i h1 h2
    have hi : i < (vblk dsig 0 J).length := by
      simp only [wslJ, List.length_map, List.length_range] at h1; omega
    simp only [wslJ, List.getElem_map, List.getElem_range, List.getElem_take, Nat.zero_add]
    have := vblkJ_get J i hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at this
    rw [this]

/-! ### 右側の有界性 -/

section rboundJ
variable {tbl : List Quint} {e q1 q2 f' g : Nat} (H : Cell2 tbl e q1 q2 f' g)
  {c0 : QConf} {T : Nat} (hR : QHaltRun tbl c0 T) {lo b : Int}
  (hzero : ∀ t, t ≤ T → ∀ x, x < lo → (qtr tbl c0 t).tape x = 0)
  (h2 : ∀ t, t ≤ T → ∀ x, (qtr tbl c0 t).tape x < 2)
include H hR hzero h2

/-- **右側の有界性（2 段の転送をするセル）**: 初め b より右が空白なら、止まる実行のヘッドは b + 2 ^ cardI W 以下。
    自動機械は細分した文字を射影してから読む（δ'(s, ℓ) = δ(s, dproj ℓ)）。 -/
theorem right_boundJ (hb : c0.pos ≤ b) (hz : ∀ x, b < x → c0.tape x = 0) :
    ∀ t, t ≤ T → (qtr tbl c0 t).pos ≤ b + ((2 ^ cardI (wW lo b) : Nat) : Int) := by
  classical
  have hrp : rpart b (qtr tbl c0 0).tape = pd 0 := by
    funext k
    show c0.tape (b + 1 + (k : Int)) = pd 0 k
    rw [hz _ (by omega)]
    cases k with
    | zero => rfl
    | succ k =>
      show 0 = pd 0 k
      induction k with
      | zero => rfl
      | succ k ih => exact ih
  obtain ⟨V, hV1, hV2, hV3⟩ := run_chain2 H hR hzero h2 (T - 0) 0 0 rfl (Nat.zero_le _) hb hrp
  have hψ : ∀ q, 1 ≤ (dsig q).length ∧ (dsig q).length ≤ 2 := dsig_len
  have hψ2 : ∀ q, q < 3 → ∀ x ∈ dsig q, x < 3 := by
    intro q _ x hx
    unfold dsig at hx
    split at hx <;> simp at hx <;> omega
  let δ' : WS lo b → Nat → WS lo b := fun s ℓ => wdelta tbl lo b s (dproj q1 q2 ℓ)
  have hfold : ∀ (l : List Nat) s, l.foldl δ' s = (l.map (dproj q1 q2)).foldl (wdelta tbl lo b) s := by
    intro l s; rw [List.foldl_map]
  have habs : ∀ u : List Nat, u.foldl (wdelta tbl lo b) none = none := by
    intro u
    induction u with
    | nil => rfl
    | cons x u ih => exact ih
  have hJ : ∃ J, (vblk dsig 0 J).foldl δ' (phase tbl lo b (qtr tbl c0 0)) = none := by
    refine ⟨V + 1, ?_⟩
    have hl := (vblk_len dsig hψ 0 (V + 1)).1
    rw [hfold, ← List.take_append_drop V (vblk dsig 0 (V + 1)), List.map_append, List.foldl_append,
      ← wslJ_vblk q1 q2 (V + 1) V (by omega), hV1, habs]
  have hC := dfa_morph dsig δ' none (fun _ => rfl) 0 (by decide) hψ2 _ hJ
  rw [card_WS] at hC
  have hL := (vblk_len dsig hψ 0 (cardI (wW lo b))).2
  have hVL : V ≤ (vblk dsig 0 (cardI (wW lo b))).length := by
    by_contra hlt
    apply hV2 (vblk dsig 0 (cardI (wW lo b))).length (by omega)
    rw [wslJ_vblk q1 q2 _ _ le_rfl, List.take_length, ← hfold]
    exact hC
  have hVP : V < 2 ^ cardI (wW lo b) := lt_of_le_of_lt hVL hL
  intro t ht
  have := hV3 t (Nat.zero_le _) ht
  omega

end rboundJ

/-- **有界停止**（右が 2 段の転送をするセル、左が段階 1 の証明書。上界は `ThreeI` と同じ `mrI`）。 -/
theorem halts_iff_boundJ {tbl : List Quint} (hsrc : Src3 tbl) (hcl : QClosed tbl 2) (hdir : DirConsistent tbl)
    {e q1 q2 f' g : Nat} (H : Cell2 tbl e q1 q2 f' g)
    {CL : List (List Nat)} {ML : Nat} (hLc : closedR (mirTbl tbl) CL ML = true)
    (c : QConf) (a b : Int) (ha : a ≤ c.pos) (hb : c.pos ≤ b)
    (hz : ∀ x, (x < a ∨ b < x) → c.tape x = 0) (h2 : ∀ x, c.tape x < 2) :
    QHalts tbl c ↔ qrun tbl (bound3 (mrI ML a b) ML a b) c = none := by
  constructor
  · intro hH
    obtain ⟨T, hR⟩ := qhalts_haltRun hH
    have hl := left_bound hR hdir hLc a ha (fun x hx => hz x (Or.inl hx))
    have hzero : ∀ t, t ≤ T → ∀ x, x < a - ML → (qtr tbl c t).tape x = 0 := by
      intro t ht x hx
      have := hR.cell_frozen x 0 t (by omega) (fun u _ h2' he => by
        have h1 := hl u (by omega)
        unfold QP at he; rw [he] at h1; omega)
      rw [Nat.zero_add] at this
      rw [this]; exact hz x (Or.inl (by omega))
    have hr := right_boundJ H hR hzero (fun t ht => hR.tape_lt hcl h2 t ht) hb (fun x hx => hz x (Or.inr hx))
    have hW : wW (a - ML) b = (b - a + ML + 1).toNat := by unfold wW; congr 1; omega
    rw [hW] at hr
    exact bound_of_window hsrc hcl hR (mrI ML a b) ML a b hz h2 hl hr
  · intro h; exact ⟨_, h⟩

/-! ### Bool の検査 -/

/-- 2 段の転送をするセルの規則が、要求の状態 e・応答の状態 q1, q2 と f', g で立つ。 -/
def cell2With (tbl : List Quint) (e q1 q2 f' g : Nat) : Bool :=
  decide (find? tbl e 0 = some ⟨e, 0, 1, Dir.L, q1⟩) && decide (find? tbl e 1 = some ⟨e, 1, f', Dir.R, e⟩) &&
  decide (find? tbl q1 f' = some ⟨q1, f', 0, Dir.L, q2⟩) && decide (find? tbl q2 f' = some ⟨q2, f', g, Dir.R, e⟩) &&
  decide (find? tbl q1 g = some ⟨q1, g, 0, Dir.L, q1⟩) &&
  tbl.all fun ρ => decide (ρ.d = Dir.R → ρ.q = e)

/-- 要求の状態と応答の状態の割り当て（6 通り）。 -/
def cell2Roles : List (Nat × Nat × Nat) := [(0, 1, 2), (0, 2, 1), (1, 0, 2), (1, 2, 0), (2, 0, 1), (2, 1, 0)]

/-- **2 段の転送をするセルの規則の検査**。 -/
def cell2Chk (tbl : List Quint) : Bool :=
  cell2Roles.any fun r => [0, 1].any fun f' => [0, 1].any fun g => cell2With tbl r.1 r.2.1 r.2.2 f' g

theorem cell2With_spec {tbl : List Quint} {e q1 q2 f' g : Nat} (h : cell2With tbl e q1 q2 f' g = true) :
    Cell2 tbl e q1 q2 f' g := by
  unfold cell2With at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h00, h01⟩, hA⟩, hB1⟩, hB2⟩, hent⟩ := h
  exact ⟨h00, h01, hA, hB1, hB2, fun ρ hρ hd => hent ρ hρ hd⟩

theorem cell2Chk_spec {tbl : List Quint} (h : cell2Chk tbl = true) :
    ∃ e q1 q2 f' g, Cell2 tbl e q1 q2 f' g := by
  unfold cell2Chk at h
  simp only [List.any_eq_true] at h
  obtain ⟨r, -, f', -, g, -, hw⟩ := h
  exact ⟨_, _, _, _, _, cell2With_spec hw⟩

/-- 右に 2 段の転送をするセル、左に段階 1 の証明書が立つ。 -/
def sideJ (tbl : List Quint) : Bool := cell2Chk tbl && checkR (mirTbl tbl)

/-- **群 D の 2 段の転送をするセルの 2 類の検査**: 表か、その鏡像が `sideJ`。 -/
def grpJ (es : List Nat) (D : List Dir) : Bool :=
  sideJ (URTM.Three.realize es D) || sideJ (mirTbl (URTM.Three.realize es D))

/-- 段階 2e の 6 の例外: `isExcI` の表のうち、この 2 類に当たらない表。 -/
def isExcJ (es : List Nat) (D : List Dir) : Bool := isExcI es D && !grpJ es D

theorem sideJ_bound {tbl : List Quint} (hsrc : Src3 tbl) (hcl : QClosed tbl 2) (hdir : DirConsistent tbl)
    (h : sideJ tbl = true) :
    ∃ ML : Nat, ∀ (c : QConf) (a b : Int), a ≤ c.pos → c.pos ≤ b →
      (∀ x, (x < a ∨ b < x) → c.tape x = 0) → (∀ x, c.tape x < 2) →
      (QHalts tbl c ↔ qrun tbl (bound3 (mrI ML a b) ML a b) c = none) := by
  unfold sideJ at h
  obtain ⟨hc, hL⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨CL, ML, hLc⟩ := checkR_spec hL
  obtain ⟨e, q1, q2, f', g, H⟩ := cell2Chk_spec hc
  exact ⟨ML, fun c a b ha hb hz h2 => halts_iff_boundJ hsrc hcl hdir H hLc c a b ha hb hz h2⟩

theorem sideJ_mir_bound {tbl : List Quint} (hsrc : Src3 tbl) (hcl : QClosed tbl 2) (hdir : DirConsistent tbl)
    (h : sideJ (mirTbl tbl) = true) :
    ∃ ML : Nat, ∀ (c : QConf) (a b : Int), a ≤ c.pos → c.pos ≤ b →
      (∀ x, (x < a ∨ b < x) → c.tape x = 0) → (∀ x, c.tape x < 2) →
      (QHalts tbl c ↔ qrun tbl (bound3 (mrI ML a b) ML a b) c = none) := by
  rw [mirTbl_eq] at h
  obtain ⟨ML, hb⟩ := sideJ_bound (src3_mir hsrc) (closed_mir hcl) (dirConsistent_mir hdir) h
  refine ⟨ML, fun c a b ha hb' hz h2 => ?_⟩
  have := hb (mirQ c) (-b) (-a) (by show -b ≤ -c.pos; omega) (by show -c.pos ≤ -a; omega)
    (fun x hx => by show c.tape (-x) = 0; exact hz (-x) (by omega)) (fun x => h2 (-x))
  rw [QHalts_mir, qrun_mir] at this
  have e1 : mrI ML (-b) (-a) = mrI ML a b := by
    unfold mrI; rw [show -a - -b + (ML : Int) + 1 = b - a + ML + 1 by omega]
  have e : bound3 (mrI ML a b) ML (-b) (-a) = bound3 (mrI ML a b) ML a b := by
    unfold bound3
    rw [show -a + ((mrI ML a b : Nat) : Int) - (-b - ML) + 1 = b + (mrI ML a b : Nat) - (a - ML) + 1 by omega]
  rw [e1, e] at this
  rw [this]
  cases qrun tbl (bound3 (mrI ML a b) ML a b) c <;> simp

section
variable {tbl : List Quint} {q₀ q₁ q₂ sg : Nat}

/-- **2 類の有界停止**（任意の表の正規形）。 -/
theorem okJ_bound (H : RTM32 tbl q₀ q₁ q₂ sg)
    (hok : grpJ (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl) = true) :
    ∃ ML : Nat, ∀ (c : QConf) (m n : ℕ), -(m : ℤ) ≤ c.pos → c.pos ≤ (n : ℤ) →
      (∀ x, (x < -(m : ℤ) ∨ (n : ℤ) < x) → c.tape x = 0) → (∀ x, c.tape x < 2) →
      (QHalts (normT (tbl := tbl) (q₀ := q₀) (q₁ := q₁) (q₂ := q₂) (σ := sg)) c ↔
        qrun (normT (tbl := tbl) (q₀ := q₀) (q₁ := q₁) (q₂ := q₂) (σ := sg)) (bndI ML (m + n)) c
          = none) := by
  have hsrc := realize_src3 (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl)
  have hcl := realize_closed (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl)
  have hdir := realize_dir (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl)
  unfold grpJ at hok
  obtain ⟨ML, hb⟩ : ∃ ML : Nat, ∀ (c : QConf) (a b : Int), a ≤ c.pos → c.pos ≤ b →
      (∀ x, (x < a ∨ b < x) → c.tape x = 0) → (∀ x, c.tape x < 2) →
      (QHalts (URTM.Three.realize (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl)) c ↔
        qrun (URTM.Three.realize (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl))
          (bound3 (mrI ML a b) ML a b) c = none) := by
    rcases Bool.or_eq_true_iff.mp hok with h | h
    · exact sideJ_bound hsrc hcl hdir h
    · exact sideJ_mir_bound hsrc hcl hdir h
  refine ⟨ML, fun c m n ha hb' hz h2 => ?_⟩
  rw [← boundI_eq]
  exact hb c _ _ ha hb' hz h2

/-- **3 状態 2 記号の RTM の停止問題は、U の ID の上で計算可能**（`isExcJ` の表を除く）。 -/
theorem three_halting_computable_J (H : RTM32 tbl q₀ q₁ q₂ sg)
    (hne : isExcJ (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl) = false) :
    ∃ f : ZID → Bool, Computable f ∧
      ∀ z, (∀ a ∈ z.2.1 ++ z.2.2, a = 0 ∨ a ∈ [sg]) → (ZHalts tbl z ↔ f z = true) := by
  cases hI : isExcI (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl) with
  | false => exact three_halting_computable_I H hI
  | true =>
    have hJ : grpJ (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl) = true := by
      unfold isExcJ at hne; rw [hI] at hne; simpa using hne
    obtain ⟨ML, hb⟩ := okJ_bound H hJ
    exact halting_computable_of_bound H (bndI_primrec ML) hb

/-- **定理（段階 2e の 6）: `isExcJ` の表を除き、3 状態 2 記号の URTM は存在しない**（Morita Def. 7.1、
    U の記号集合 {0, sg} の上の ID への符号化）。 -/
theorem no_three_two_URTM_J (H : RTM32 tbl q₀ q₁ q₂ sg)
    (hne : isExcJ (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl) = false) :
    ¬ IsUTM_MoritaOver tbl [sg] :=
  not_UTM_of_halting_computable (three_halting_computable_J H hne)

end

/-! ### 残る例外の数

段階 2e の 5 の例外の上界 192 表（`excIKeys`）のうち、`grpJ` に当たる 24 表（2 類）の鍵を一覧 `j24Keys` に書き、
それらが `grpJ` に当たることを kernel で確かめる。残る例外はその外の 168 表に**含まれる**（上界）。 -/

/-- `grpJ` に当たる 24 表の鍵（Python で生成。下の `j24_grpJ` が kernel で検査する）。 -/
def j24Keys : List Nat := [
  241385, 253985, 298087, 326647, 716637, 736393, 757821, 793657, 1030333, 1035915, 1048573, 1052163,
  2206823, 2212405, 2225063, 2228653, 2363723, 2383479, 2404907, 2440743, 2829663, 2842263, 2886365, 2914925
]

theorem j24_grpJ : j24Keys.all (fun k => grpJ (unkey k).1 (unkey k).2) = true := by decide +kernel

theorem j24_sub : j24Keys.all (fun k => excIKeys.contains k) = true := by decide +kernel

/-- 段階 2e の 6 の例外の鍵（の上界）。 -/
def excJKeys : List Nat := excIKeys.filter fun k => !j24Keys.contains k

/-- **段階 2e の 6 の例外の表（の上界）の一覧**。 -/
def excJTables : List (List Nat × List Dir) := excJKeys.map unkey

/-- **主定理の仮定が外れる表は一覧に載る**（符号 6 つ・向き 3 つの表について）。 -/
theorem mem_excJTables {es : List Nat} {D : List Dir} (h : ValidKey es D) (hx : isExcJ es D = true) :
    (es, D) ∈ excJTables := by
  unfold isExcJ at hx
  obtain ⟨hI, hJ⟩ := Bool.and_eq_true_iff.mp hx
  obtain ⟨k, hk, he⟩ := List.mem_map.mp (mem_excITables h hI)
  refine List.mem_map.mpr ⟨k, List.mem_filter.mpr ⟨hk, ?_⟩, he⟩
  cases hc : j24Keys.contains k
  · rfl
  · exfalso
    have := List.all_eq_true.mp j24_grpJ k (List.contains_iff_mem.mp hc)
    rw [he] at this
    simp only [this, Bool.not_true] at hJ
    exact Bool.false_ne_true hJ

/-- **段階 2e の 6 の例外は高々 168 表**（192 − 24。kernel の評価）。 -/
theorem excJKeys_length : excJKeys.length = 168 := by decide +kernel

theorem excJTables_length : excJTables.length = 168 := by
  unfold excJTables; rw [List.length_map, excJKeys_length]

end URTM.Meta
