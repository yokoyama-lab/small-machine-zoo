/-
  3 状態 2 記号 RTM の停止問題の決定可能性 その 8: **任意の表から正規形の表への帰着**。**手書き**。

  Morita の数え方（停止用の疑似状態は状態数に数えない）で 3 状態 2 記号の決定的・可逆な五つ組の表
  `RTM32 tbl q₀ q₁ q₂ σ`（働く状態 q₀, q₁, q₂、記号は空白 0 と σ）を、状態の付け替え（q_i ↦ i、
  それ以外 ↦ 3）と記号の付け替え（σ ↦ 1）で正規形の表 `realize (absCodes …) (absDirs …)` に移す。
  働かない状態へ入る規則は、正規形では「規則が無い」にする（どちらも高々 1 歩の差で止まる）。

    * `halts_norm` : 記号が 0 と σ だけの配置について、元の表が止まる ⟺ 正規形の表が止まる
    * `absCodes_lt` / `absCodes_fresh` : 正規形の符号は 7 未満で、0 でないものは重ならない（可逆性）
-/
import URTM.ThreeEnumSound
import URTM.TwoState

namespace URTM.Three
open URTM URTM.TwoState

/-- **3 状態 2 記号の RTM**（Morita Def. 5.4 の決定性・可逆性。停止用の疑似状態は数えない）。
    五つ組はどれも q₀, q₁, q₂ のどれかから出る（入る先は任意。それ以外の状態は出ていく五つ組を持たない
    停止用の疑似状態）。記号は空白 0 と σ の 2 つ。 -/
structure RTM32 (tbl : List Quint) (q₀ q₁ q₂ σ : Nat) : Prop where
  det : deterministic tbl = true
  rev : reversible tbl = true
  n01 : q₀ ≠ q₁
  n02 : q₀ ≠ q₂
  n12 : q₁ ≠ q₂
  src : ∀ r ∈ tbl, r.p = q₀ ∨ r.p = q₁ ∨ r.p = q₂
  sig : σ ≠ 0
  sym : ∀ r ∈ tbl, (r.s = 0 ∨ r.s = σ) ∧ (r.t = 0 ∨ r.t = σ)

section
variable (q₀ q₁ q₂ σ : Nat)

def stN (x : Nat) : Nat := if x = q₀ then 0 else if x = q₁ then 1 else if x = q₂ then 2 else 3
def symN (y : Nat) : Nat := if y = σ then 1 else y
def qOf (i : Nat) : Nat := if i = 0 then q₀ else if i = 1 then q₁ else q₂
def symOf (s : Nat) : Nat := if s = 0 then 0 else σ

/-- 正規形の欄 (i, s) の符号。 -/
def codeOf (tbl : List Quint) (i s : Nat) : Nat :=
  match find? tbl (qOf q₀ q₁ q₂ i) (symOf σ s) with
  | none => 0
  | some r => if stN q₀ q₁ q₂ r.q < 3 then 1 + 2 * stN q₀ q₁ q₂ r.q + symN σ r.t else 0

def absCodes (tbl : List Quint) : List Nat :=
  [codeOf q₀ q₁ q₂ σ tbl 0 0, codeOf q₀ q₁ q₂ σ tbl 0 1, codeOf q₀ q₁ q₂ σ tbl 1 0,
   codeOf q₀ q₁ q₂ σ tbl 1 1, codeOf q₀ q₁ q₂ σ tbl 2 0, codeOf q₀ q₁ q₂ σ tbl 2 1]

/-- 状態 q へ入るときの向き（入る五つ組が無ければ L。使われない）。 -/
def dirOfQ (tbl : List Quint) (q : Nat) : Dir :=
  match tbl.find? (fun r => r.q == q) with
  | some r => r.d
  | none => Dir.L

def absDirs (tbl : List Quint) : List Dir := [dirOfQ tbl q₀, dirOfQ tbl q₁, dirOfQ tbl q₂]

def normC (c : QConf) : QConf := ⟨stN q₀ q₁ q₂ c.st, c.pos, fun x => symN σ (c.tape x)⟩

end

section
variable {tbl : List Quint} {q₀ q₁ q₂ σ : Nat} (H : RTM32 tbl q₀ q₁ q₂ σ)
include H

theorem stN_qOf {i : Nat} (hi : i < 3) : stN q₀ q₁ q₂ (qOf q₀ q₁ q₂ i) = i := by
  have h01 := H.n01; have h02 := H.n02; have h12 := H.n12
  have h10 := Ne.symm h01; have h20 := Ne.symm h02; have h21 := Ne.symm h12
  unfold stN qOf
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl <;> simp [h10, h20, h21]

omit H in
theorem stN_lt_iff {x : Nat} : stN q₀ q₁ q₂ x < 3 ↔ x = q₀ ∨ x = q₁ ∨ x = q₂ := by
  unfold stN; split <;> (try split) <;> (try split) <;> simp_all

theorem qOf_stN {x : Nat} (hx : stN q₀ q₁ q₂ x < 3) : qOf q₀ q₁ q₂ (stN q₀ q₁ q₂ x) = x := by
  unfold stN at hx ⊢; unfold qOf
  by_cases h0 : x = q₀
  · simp [h0]
  · by_cases h1 : x = q₁
    · simp [h1, H.n01.symm]
    · by_cases h2 : x = q₂
      · simp [h2, H.n02.symm, H.n12.symm]
      · simp [h0, h1, h2] at hx

theorem symN_lt {y : Nat} (hy : y = 0 ∨ y = σ) : symN σ y < 2 := by
  unfold symN; rcases hy with rfl | rfl
  · simp [Ne.symm H.sig]
  · simp

theorem symOf_symN {y : Nat} (hy : y = 0 ∨ y = σ) : symOf σ (symN σ y) = y := by
  unfold symN symOf; rcases hy with rfl | rfl
  · simp [Ne.symm H.sig]
  · simp

theorem symN_inj {y y' : Nat} (hy : y = 0 ∨ y = σ) (hy' : y' = 0 ∨ y' = σ)
    (h : symN σ y = symN σ y') : y = y' := by
  rw [← symOf_symN H hy, ← symOf_symN H hy', h]

theorem dirOfQ_eq {r : Quint} (hr : r ∈ tbl) : dirOfQ tbl r.q = r.d := by
  unfold dirOfQ
  cases hf : tbl.find? (fun x => x.q == r.q) with
  | none =>
    have := List.find?_eq_none.mp hf r hr
    simp at this
  | some r' =>
    have hm := List.mem_of_find?_eq_some hf
    have hq := List.find?_some hf
    simp only [beq_iff_eq] at hq
    exact same_next_state_same_dir H.rev hm hr hq

theorem tape_ok_write {c : QConf} (hc : ∀ x, c.tape x = 0 ∨ c.tape x = σ) {r : Quint} (hr : r ∈ tbl) :
    ∀ x, write c.tape c.pos r.t x = 0 ∨ write c.tape c.pos r.t x = σ := by
  intro x; unfold write; split
  · exact (H.sym r hr).2
  · exact hc x

theorem codeOf_lt (i s : Nat) : codeOf q₀ q₁ q₂ σ tbl i s < 7 := by
  unfold codeOf
  split
  · omega
  · rename_i r hf
    have hr := (find?_spec hf).1
    split
    · rename_i hlt
      have := symN_lt H (H.sym r hr).2
      omega
    · omega

/-- 正規形の表。 -/
abbrev normT : List Quint := realize (absCodes q₀ q₁ q₂ σ tbl) (absDirs q₀ q₁ q₂ tbl)

omit H in
theorem absCodes_getD {i s : Nat} (hi : i < 3) (hs : s < 2) :
    (absCodes q₀ q₁ q₂ σ tbl).getD (2 * i + s) 0 = codeOf q₀ q₁ q₂ σ tbl i s := by
  unfold absCodes
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl <;>
    rcases (show s = 0 ∨ s = 1 by omega) with rfl | rfl <;> rfl

omit H in
theorem find?_normT {i s : Nat} (hi : i < 3) (hs : s < 2) :
    find? (normT (tbl := tbl) (q₀ := q₀) (q₁ := q₁) (q₂ := q₂) (σ := σ)) i s =
      if codeOf q₀ q₁ q₂ σ tbl i s = 0 then none else
        some ⟨i, s, (codeOf q₀ q₁ q₂ σ tbl i s - 1) % 2,
          (absDirs q₀ q₁ q₂ tbl).getD ((codeOf q₀ q₁ q₂ σ tbl i s - 1) / 2) Dir.L,
          (codeOf q₀ q₁ q₂ σ tbl i s - 1) / 2⟩ := by
  obtain ⟨c, hc, hf⟩ := find?_realize (codeOf q₀ q₁ q₂ σ tbl 0 0) (codeOf q₀ q₁ q₂ σ tbl 0 1)
    (codeOf q₀ q₁ q₂ σ tbl 1 0) (codeOf q₀ q₁ q₂ σ tbl 1 1) (codeOf q₀ q₁ q₂ σ tbl 2 0)
    (codeOf q₀ q₁ q₂ σ tbl 2 1) (absDirs q₀ q₁ q₂ tbl) i s hi hs
  have hc' : c = codeOf q₀ q₁ q₂ σ tbl i s := by
    rw [hc]; exact absCodes_getD hi hs
  subst hc'
  exact hf

/-- **1 歩の対応**。 -/
theorem step_norm (c : QConf) (hc : ∀ x, c.tape x = 0 ∨ c.tape x = σ) :
    (qstep tbl c = none ∧ qstep (normT (tbl := tbl) (q₀ := q₀) (q₁ := q₁) (q₂ := q₂) (σ := σ))
        (normC q₀ q₁ q₂ σ c) = none) ∨
    (∃ c', qstep tbl c = some c' ∧ qstep tbl c' = none ∧
      qstep (normT (tbl := tbl) (q₀ := q₀) (q₁ := q₁) (q₂ := q₂) (σ := σ)) (normC q₀ q₁ q₂ σ c) = none) ∨
    (∃ c', qstep tbl c = some c' ∧
      qstep (normT (tbl := tbl) (q₀ := q₀) (q₁ := q₁) (q₂ := q₂) (σ := σ)) (normC q₀ q₁ q₂ σ c) =
        some (normC q₀ q₁ q₂ σ c') ∧ ∀ x, c'.tape x = 0 ∨ c'.tape x = σ) := by
  -- 働かない状態からは規則が無い
  have noRule : ∀ (x : QConf), ¬ (x.st = q₀ ∨ x.st = q₁ ∨ x.st = q₂) → qstep tbl x = none := by
    intro x hx
    unfold qstep
    cases hf : find? tbl x.st (x.tape x.pos) with
    | none => rfl
    | some r =>
      obtain ⟨hm, hp, _⟩ := find?_spec hf
      exact absurd (hp ▸ H.src r hm) hx
  have hnormSt : (normC q₀ q₁ q₂ σ c).st = stN q₀ q₁ q₂ c.st := rfl
  by_cases hw : c.st = q₀ ∨ c.st = q₁ ∨ c.st = q₂
  · -- 働く状態 q_i
    have hlt : stN q₀ q₁ q₂ c.st < 3 := stN_lt_iff.mpr hw
    have hqi : qOf q₀ q₁ q₂ (stN q₀ q₁ q₂ c.st) = c.st := qOf_stN H hlt
    have hv01 : c.tape c.pos = 0 ∨ c.tape c.pos = σ := hc c.pos
    have hs2 : symN σ (c.tape c.pos) < 2 := symN_lt H hv01
    have hsv : symOf σ (symN σ (c.tape c.pos)) = c.tape c.pos := symOf_symN H hv01
    have hreadN : (normC q₀ q₁ q₂ σ c).tape (normC q₀ q₁ q₂ σ c).pos = symN σ (c.tape c.pos) := rfl
    have hcode : codeOf q₀ q₁ q₂ σ tbl (stN q₀ q₁ q₂ c.st) (symN σ (c.tape c.pos)) =
        (match find? tbl c.st (c.tape c.pos) with
         | none => 0
         | some r => if stN q₀ q₁ q₂ r.q < 3 then 1 + 2 * stN q₀ q₁ q₂ r.q + symN σ r.t else 0) := by
      unfold codeOf; rw [hqi, hsv]
    have hfN := find?_normT (tbl := tbl) (q₀ := q₀) (q₁ := q₁) (q₂ := q₂) (σ := σ) hlt hs2
    unfold qstep
    rw [hreadN, hnormSt, hfN, hcode]
    cases hf : find? tbl c.st (c.tape c.pos) with
    | none =>
      left
      simp
    | some r =>
      obtain ⟨hm, hp, hs⟩ := find?_spec hf
      simp only
      by_cases hrq : stN q₀ q₁ q₂ r.q < 3
      · -- 働く状態へ入る
        right; right
        rw [if_pos hrq]
        refine ⟨_, rfl, ?_, tape_ok_write H hc hm⟩
        have ht2 := symN_lt H (H.sym r hm).2
        rw [if_neg (by omega)]
        have hj : (1 + 2 * stN q₀ q₁ q₂ r.q + symN σ r.t - 1) / 2 = stN q₀ q₁ q₂ r.q := by omega
        have ht : (1 + 2 * stN q₀ q₁ q₂ r.q + symN σ r.t - 1) % 2 = symN σ r.t := by omega
        rw [hj, ht]
        have hd : (absDirs q₀ q₁ q₂ tbl).getD (stN q₀ q₁ q₂ r.q) Dir.L = r.d := by
          have hq := qOf_stN H hrq
          rw [← dirOfQ_eq H hm, ← hq]
          unfold absDirs
          rw [hq]
          have := stN_lt_iff.mp hrq
          rcases (show stN q₀ q₁ q₂ r.q = 0 ∨ stN q₀ q₁ q₂ r.q = 1 ∨ stN q₀ q₁ q₂ r.q = 2 by omega)
            with h | h | h <;> rw [h] <;> simp only [List.getD_cons_zero, List.getD_cons_succ] <;>
            rw [← hq, h] <;> rfl
        rw [hd]
        show some _ = some (normC q₀ q₁ q₂ σ _)
        unfold normC
        congr 1
        congr 1
        funext x
        unfold write
        by_cases hx : x = c.pos <;> simp [hx]
      · -- 働かない状態へ入る: 正規形は規則無し、元の表は次の 1 歩で止まる
        right; left
        rw [if_neg hrq]
        refine ⟨_, rfl, noRule _ ?_, by simp⟩
        show ¬ (r.q = q₀ ∨ r.q = q₁ ∨ r.q = q₂)
        exact fun h => hrq (stN_lt_iff.mpr h)
  · left
    refine ⟨noRule c hw, ?_⟩
    unfold qstep
    cases hf : find? (normT (tbl := tbl) (q₀ := q₀) (q₁ := q₁) (q₂ := q₂) (σ := σ))
        (normC q₀ q₁ q₂ σ c).st _ with
    | none => rfl
    | some r =>
      obtain ⟨hm, hp, _⟩ := find?_spec hf
      have := realize_src3 _ _ r hm
      rw [hp, hnormSt] at this
      exact absurd (stN_lt_iff.mp this) hw

/-- **元の表が止まる ⟺ 正規形の表が止まる**（記号が 0 と σ だけの配置で）。 -/
theorem halts_norm (c : QConf) (hc : ∀ x, c.tape x = 0 ∨ c.tape x = σ) :
    QHalts tbl c ↔ QHalts (normT (tbl := tbl) (q₀ := q₀) (q₁ := q₁) (q₂ := q₂) (σ := σ))
      (normC q₀ q₁ q₂ σ c) := by
  constructor
  · rintro ⟨n, hn⟩
    induction n generalizing c with
    | zero => simp [qrun] at hn
    | succ n ih =>
      rcases step_norm H c hc with ⟨_, h2⟩ | ⟨_, _, _, h2⟩ | ⟨c', h1, h2, hc'⟩
      · exact ⟨1, qrun_succ_none _ 0 h2⟩
      · exact ⟨1, qrun_succ_none _ 0 h2⟩
      · rw [qrun_succ_some _ n h1] at hn
        obtain ⟨m, hm⟩ := ih c' hc' hn
        exact ⟨m + 1, by rw [qrun_succ_some _ m h2]; exact hm⟩
  · rintro ⟨n, hn⟩
    induction n generalizing c with
    | zero => simp [qrun] at hn
    | succ n ih =>
      rcases step_norm H c hc with ⟨h1, _⟩ | ⟨c', h1, h1', _⟩ | ⟨c', h1, h2, hc'⟩
      · exact ⟨1, qrun_succ_none _ 0 h1⟩
      · exact ⟨2, by rw [qrun_succ_some _ 1 h1, qrun_succ_none _ 0 h1']⟩
      · rw [qrun_succ_some _ n h2] at hn
        obtain ⟨m, hm⟩ := ih c' hc' hn
        exact ⟨m + 1, by rw [qrun_succ_some _ m h1]; exact hm⟩

/-! ### 符号の性質（全列挙に載ること） -/

theorem absCodes_lt : ∀ c ∈ absCodes q₀ q₁ q₂ σ tbl, c < 7 := by
  intro c hc
  unfold absCodes at hc
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with h | h | h | h | h | h <;> rw [h] <;> exact codeOf_lt H _ _

/-- 0 でない符号は欄ごとに異なる（可逆性）。 -/
theorem codeOf_inj {i s i' s' : Nat} (hi : i < 3) (hs : s < 2) (hi' : i' < 3) (hs' : s' < 2)
    (hne : codeOf q₀ q₁ q₂ σ tbl i s ≠ 0)
    (heq : codeOf q₀ q₁ q₂ σ tbl i s = codeOf q₀ q₁ q₂ σ tbl i' s') : i = i' ∧ s = s' := by
  unfold codeOf at hne heq
  cases hf : find? tbl (qOf q₀ q₁ q₂ i) (symOf σ s) with
  | none => rw [hf] at hne; exact absurd rfl hne
  | some r =>
    cases hf' : find? tbl (qOf q₀ q₁ q₂ i') (symOf σ s') with
    | none => rw [hf, hf'] at heq; rw [hf] at hne; simp only at heq hne; omega
    | some r' =>
      rw [hf, hf'] at heq; rw [hf] at hne
      simp only at heq hne
      obtain ⟨hm, hp, hs1⟩ := find?_spec hf
      obtain ⟨hm', hp', hs1'⟩ := find?_spec hf'
      have ht := symN_lt H (H.sym r hm).2
      have ht' := symN_lt H (H.sym r' hm').2
      by_cases h1 : stN q₀ q₁ q₂ r.q < 3
      · rw [if_pos h1] at heq
        by_cases h2 : stN q₀ q₁ q₂ r'.q < 3
        · rw [if_pos h2] at heq
          have hq : stN q₀ q₁ q₂ r.q = stN q₀ q₁ q₂ r'.q := by omega
          have htt : symN σ r.t = symN σ r'.t := by omega
          have hqq : r.q = r'.q := by rw [← qOf_stN H h1, ← qOf_stN H h2, hq]
          have htq : r.t = r'.t := symN_inj H (H.sym r hm).2 (H.sym r' hm').2 htt
          have hrr := rule_unique_of_write_next H.rev hm hm' hqq htq
          subst hrr
          have e1 : qOf q₀ q₁ q₂ i = qOf q₀ q₁ q₂ i' := by rw [← hp, hp']
          have e2 : symOf σ s = symOf σ s' := by rw [← hs1, hs1']
          constructor
          · have := congrArg (stN q₀ q₁ q₂) e1
            rwa [stN_qOf H hi, stN_qOf H hi'] at this
          · unfold symOf at e2
            have := H.sig
            rcases (show s = 0 ∨ s = 1 by omega) with rfl | rfl <;>
              rcases (show s' = 0 ∨ s' = 1 by omega) with rfl | rfl <;> simp_all
        · rw [if_neg h2] at heq; omega
      · rw [if_neg h1] at hne; exact absurd rfl hne

end

end URTM.Three
