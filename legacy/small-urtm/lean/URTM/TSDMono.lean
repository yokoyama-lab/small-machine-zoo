/-
  2 状態 RTM の停止問題の決定可能性 その 10: 単調な場合（docs/10 §2.1）。**手書き**。

  左へ動く規則が 1 本も無い表（右か 0 シフトだけ）。ヘッドは左へ戻らない。
    * `qescape` : 状態が同じで、δ ≥ 1 だけ右にずれ、右側の中身がずれて一致する配置へ着いたら
      停止しない（右しか見ない機械の自己相似）
    * `mono_pos_bound` : 停止する実行では、ヘッドは b+2 を越えない（空白の新しいセルに着いたときの
      状態は 2 通りしかないので、3 つ目の新しいセルに着く前に同じ状態が繰り返す）
    * `mono_time_bound` : 停止までの歩数は `monoBound nsym a b` 未満
-/
import URTM.TSDMorita

namespace URTM.TwoState

/-! ## 五つ組 TM の実行の基本 -/

theorem qrun_succ_none (tbl : List Quint) (n : Nat) {c : QConf} (h : qstep tbl c = none) :
    qrun tbl (n + 1) c = none := by simp [qrun, h]

theorem qrun_succ_some (tbl : List Quint) (n : Nat) {c c' : QConf} (h : qstep tbl c = some c') :
    qrun tbl (n + 1) c = qrun tbl n c' := by simp [qrun, h]

theorem qrun_add (tbl : List Quint) :
    ∀ (a b : Nat) (x : QConf), qrun tbl (a + b) x = (qrun tbl a x).bind (fun y => qrun tbl b y) := by
  intro a
  induction a with
  | zero => intro b x; rw [Nat.zero_add]; rfl
  | succ a ih =>
    intro b x
    rw [show a + 1 + b = (a + b) + 1 by omega]
    cases hs : qstep tbl x with
    | none => rw [qrun_succ_none tbl (a + b) hs, qrun_succ_none tbl a hs]; rfl
    | some x' => rw [qrun_succ_some tbl (a + b) hs, qrun_succ_some tbl a hs, ih b x']

theorem qrun_succ_right (tbl : List Quint) (n : Nat) (c : QConf) :
    qrun tbl (n + 1) c = (qrun tbl n c).bind (qstep tbl) := by
  rw [qrun_add tbl n 1 c]
  cases qrun tbl n c with
  | none => rfl
  | some y =>
    show qrun tbl 1 y = qstep tbl y
    cases hs : qstep tbl y with
    | none => rw [qrun_succ_none tbl 0 hs]
    | some y' => rw [qrun_succ_some tbl 0 hs]; rfl

theorem qrun_none_mono (tbl : List Quint) (c : QConf) (n m : Nat)
    (h : qrun tbl n c = none) (hnm : n ≤ m) : qrun tbl m c = none := by
  rw [show m = n + (m - n) by omega, qrun_add, h]; rfl

def qtr (tbl : List Quint) (c : QConf) (t : Nat) : QConf := (qrun tbl t c).getD c

structure QHaltRun (tbl : List Quint) (c : QConf) (T : Nat) : Prop where
  alive : qrun tbl T c ≠ none
  dead : qrun tbl (T + 1) c = none

theorem qhalts_haltRun {tbl : List Quint} {c : QConf} (h : QHalts tbl c) :
    ∃ T, QHaltRun tbl c T := by
  obtain ⟨n, hn⟩ := h
  have key : ∀ n, qrun tbl n c = none → ∃ T, qrun tbl T c ≠ none ∧ qrun tbl (T + 1) c = none := by
    intro n
    induction n with
    | zero => intro h; simp [qrun] at h
    | succ n ih =>
      intro h
      by_cases hn : qrun tbl n c = none
      · exact ih hn
      · exact ⟨n, hn, h⟩
  obtain ⟨T, h1, h2⟩ := key n hn
  exact ⟨T, ⟨h1, h2⟩⟩

section QRun
variable {tbl : List Quint} {c : QConf} {T : Nat}

theorem QHaltRun.run (hR : QHaltRun tbl c T) (t : Nat) (ht : t ≤ T) :
    qrun tbl t c = some (qtr tbl c t) := by
  cases h : qrun tbl t c with
  | none => exact absurd (qrun_none_mono tbl c t T h ht) hR.alive
  | some x => simp [qtr, h]

theorem QHaltRun.step (hR : QHaltRun tbl c T) (t : Nat) (ht : t < T) :
    qstep tbl (qtr tbl c t) = some (qtr tbl c (t + 1)) := by
  have h1 := hR.run (t + 1) (by omega)
  rw [qrun_succ_right, hR.run t (by omega)] at h1
  exact h1

theorem QHaltRun.run_mid (hR : QHaltRun tbl c T) (t n : Nat) (h : t + n ≤ T) :
    qrun tbl n (qtr tbl c t) = some (qtr tbl c (t + n)) := by
  have h1 := hR.run (t + n) h
  rw [qrun_add, hR.run t (by omega)] at h1
  exact h1

theorem QHaltRun.run_from (hR : QHaltRun tbl c T) (t : Nat) (ht : t ≤ T) :
    qrun tbl (T + 1 - t) (qtr tbl c t) = none := by
  have h := hR.dead
  rw [show T + 1 = t + (T + 1 - t) by omega, qrun_add, hR.run t ht] at h
  exact h

theorem QHaltRun.no_repeat (hR : QHaltRun tbl c T) (i j : Nat) (hij : i < j) (hj : j ≤ T)
    (he : qtr tbl c i = qtr tbl c j) : False := by
  have hrun : qrun tbl (j - i) (qtr tbl c i) = some (qtr tbl c i) := by
    have := hR.run_mid i (j - i) (by omega)
    rw [show i + (j - i) = j by omega, ← he] at this; exact this
  have hall : ∀ q, qrun tbl (q * (j - i)) (qtr tbl c i) = some (qtr tbl c i) := by
    intro q
    induction q with
    | zero => rw [Nat.zero_mul]; rfl
    | succ q ih => rw [Nat.succ_mul, qrun_add, ih]; exact hrun
  have hle : T + 1 - i ≤ (T + 1 - i) * (j - i) := by
    have := Nat.mul_le_mul_left (T + 1 - i) (show 1 ≤ j - i by omega); simpa using this
  have := qrun_none_mono tbl _ _ _ (hR.run_from i (by omega)) hle
  rw [hall] at this; exact absurd this (by simp)

end QRun

/-! ## 右単調な表 -/

def RightMono (tbl : List Quint) : Prop := ∀ r ∈ tbl, r.d ≠ Dir.L

theorem qstep_some {tbl : List Quint} {c c' : QConf} (h : qstep tbl c = some c') :
    ∃ r, r ∈ tbl ∧ find? tbl c.st (c.tape c.pos) = some r ∧
      c' = ⟨r.q, move r.d c.pos, write c.tape c.pos r.t⟩ := by
  unfold qstep at h
  cases hf : find? tbl c.st (c.tape c.pos) with
  | none => rw [hf] at h; exact absurd h (by simp)
  | some r =>
    rw [hf] at h
    exact ⟨r, (find?_spec hf).1, rfl, (Option.some.inj h).symm⟩

theorem mono_pos {tbl : List Quint} (hm : RightMono tbl) {c c' : QConf}
    (h : qstep tbl c = some c') : c'.pos = c.pos ∨ c'.pos = c.pos + 1 := by
  obtain ⟨r, hr, _, rfl⟩ := qstep_some h
  have := hm r hr
  cases hd : r.d with
  | L => exact absurd hd this
  | Z => left; rfl
  | R => right; rfl

def shiftQ (c : QConf) (δ : Int) : QConf := ⟨c.st, c.pos + δ, shiftT c.tape δ⟩

theorem qstep_shift (tbl : List Quint) (c : QConf) (δ : Int) :
    qstep tbl (shiftQ c δ) = (qstep tbl c).map (fun x => shiftQ x δ) := by
  have hread : (shiftQ c δ).tape (shiftQ c δ).pos = c.tape c.pos := by
    show shiftT c.tape δ (c.pos + δ) = _; rw [shiftT_apply]; congr 1; omega
  unfold qstep
  rw [hread]
  show (match find? tbl c.st (c.tape c.pos) with
    | none => none
    | some r => some (⟨r.q, move r.d (c.pos + δ), write (shiftT c.tape δ) (c.pos + δ) r.t⟩ : QConf)) = _
  cases find? tbl c.st (c.tape c.pos) with
  | none => rfl
  | some r =>
    show some _ = some (shiftQ _ δ)
    rw [move_shift, write_shift]; rfl

theorem qrun_shift (tbl : List Quint) :
    ∀ (n : Nat) (c : QConf) (δ : Int),
      qrun tbl n (shiftQ c δ) = (qrun tbl n c).map (fun x => shiftQ x δ) := by
  intro n
  induction n with
  | zero => intro c δ; rfl
  | succ n ih =>
    intro c δ
    cases hs : qstep tbl c with
    | none =>
      have hs' : qstep tbl (shiftQ c δ) = none := by rw [qstep_shift, hs]; rfl
      rw [qrun_succ_none tbl n hs', qrun_succ_none tbl n hs]; rfl
    | some c' =>
      have hs' : qstep tbl (shiftQ c δ) = some (shiftQ c' δ) := by rw [qstep_shift, hs]; rfl
      rw [qrun_succ_some tbl n hs', qrun_succ_some tbl n hs, ih]

/-- 右側 [k,∞) と状態・位置が一致（位置は k 以上）。 -/
def AgreeQ (k : Int) (c₁ c₂ : QConf) : Prop :=
  c₁.st = c₂.st ∧ c₁.pos = c₂.pos ∧ k ≤ c₁.pos ∧ ∀ x, k ≤ x → c₁.tape x = c₂.tape x

theorem qstep_local {tbl : List Quint} (hm : RightMono tbl) {k : Int} {c₁ c₂ : QConf}
    (H : AgreeQ k c₁ c₂) :
    (qstep tbl c₁ = none ∧ qstep tbl c₂ = none) ∨
    ∃ d₁ d₂, qstep tbl c₁ = some d₁ ∧ qstep tbl c₂ = some d₂ ∧ AgreeQ k d₁ d₂ := by
  obtain ⟨hs, hp, hk, ht⟩ := H
  have hread : c₂.tape c₂.pos = c₁.tape c₁.pos := by rw [← hp]; exact (ht _ hk).symm
  unfold qstep
  rw [hread, ← hs]
  cases hf : find? tbl c₁.st (c₁.tape c₁.pos) with
  | none => left; exact ⟨rfl, rfl⟩
  | some r =>
    right
    refine ⟨_, _, rfl, rfl, rfl, by rw [hp], ?_, ?_⟩
    · have := hm r (find?_spec hf).1
      show k ≤ move r.d c₁.pos
      cases hd : r.d with
      | L => exact absurd hd this
      | Z => rw [move_Z]; exact hk
      | R => rw [move_R]; omega
    · intro x hx
      show write c₁.tape c₁.pos r.t x = write c₂.tape c₂.pos r.t x
      unfold write; rw [← hp]
      by_cases he : x = c₁.pos
      · simp [he]
      · simp [he, ht x hx]

theorem qrun_local {tbl : List Quint} (hm : RightMono tbl) {k : Int} :
    ∀ (n : Nat) (c₁ c₂ : QConf), AgreeQ k c₁ c₂ →
      (qrun tbl n c₁ = none ∧ qrun tbl n c₂ = none) ∨
      ∃ d₁ d₂, qrun tbl n c₁ = some d₁ ∧ qrun tbl n c₂ = some d₂ ∧ AgreeQ k d₁ d₂ := by
  intro n
  induction n with
  | zero => intro c₁ c₂ H; exact Or.inr ⟨c₁, c₂, rfl, rfl, H⟩
  | succ n ih =>
    intro c₁ c₂ H
    rcases qstep_local hm H with ⟨e1, e2⟩ | ⟨d₁, d₂, e1, e2, H'⟩
    · left; exact ⟨qrun_succ_none tbl n e1, qrun_succ_none tbl n e2⟩
    · rw [qrun_succ_some tbl n e1, qrun_succ_some tbl n e2]
      exact ih d₁ d₂ H'

/-- **右単調な機械の自己相似の逃走**。 -/
theorem qescape {tbl : List Quint} (hm : RightMono tbl) (c c' : QConf) (Δ : Nat) (δ : Int)
    (hδ : 1 ≤ δ) (hrun : qrun tbl Δ c = some c') (hst : c'.st = c.st)
    (hpos : c'.pos = c.pos + δ) (htape : ∀ x, c'.pos ≤ x → c'.tape x = c.tape (x - δ)) :
    ∀ n, qrun tbl n c ≠ none := by
  have hΔ : 1 ≤ Δ := by
    rcases Nat.eq_zero_or_pos Δ with h | h
    · subst h
      have : c = c' := Option.some.inj hrun
      rw [this] at hpos; omega
    · exact h
  have iter : ∀ j : Nat, ∃ cj, qrun tbl (j * Δ) c = some cj ∧
      AgreeQ (c.pos + j * δ) cj (shiftQ c (j * δ)) := by
    intro j
    induction j with
    | zero =>
      refine ⟨c, by rw [Nat.zero_mul]; rfl, rfl, by simp [shiftQ], by simp, fun x _ => ?_⟩
      show c.tape x = c.tape (x - ((0 : Nat) : Int) * δ); simp
    | succ j ih =>
      obtain ⟨cj, hcj, hag⟩ := ih
      have hsh : qrun tbl Δ (shiftQ c (j * δ)) = some (shiftQ c' (j * δ)) := by
        rw [qrun_shift, hrun]; rfl
      have hag' : AgreeQ (c.pos + j * δ) (shiftQ c (j * δ)) cj :=
        ⟨hag.1.symm, hag.2.1.symm, by rw [← hag.2.1]; exact hag.2.2.1,
          fun x hx => (hag.2.2.2 x hx).symm⟩
      rcases qrun_local hm Δ _ _ hag' with ⟨h1, _⟩ | ⟨d₁, d₂, h1, h2, hag2⟩
      · rw [hsh] at h1; exact absurd h1 (by simp)
      · rw [hsh] at h1
        have e := (Option.some.inj h1).symm
        subst e
        refine ⟨d₂, by rw [Nat.succ_mul, qrun_add, hcj]; exact h2, ?_, ?_, ?_, ?_⟩
        · rw [← hag2.1]; exact hst
        · rw [← hag2.2.1]; show c'.pos + j * δ = c.pos + ((j + 1 : Nat) : Int) * δ
          rw [hpos]; push_cast; rw [Int.add_mul]; omega
        · rw [← hag2.2.1]; show c.pos + ((j + 1 : Nat) : Int) * δ ≤ c'.pos + j * δ
          rw [hpos]; push_cast; rw [Int.add_mul]; omega
        · intro x hx
          have hx' : c.pos + (j : Int) * δ ≤ x := by
            push_cast at hx; rw [Int.add_mul] at hx; omega
          rw [← hag2.2.2.2 x hx']
          show c'.tape (x - j * δ) = c.tape (x - ((j + 1 : Nat) : Int) * δ)
          rw [htape (x - j * δ) (by push_cast at hx; rw [Int.add_mul] at hx; omega)]
          congr 1; push_cast; rw [Int.add_mul]; omega
  intro n hn
  obtain ⟨cj, hcj, _⟩ := iter n
  have hle : n ≤ n * Δ := by have := Nat.mul_le_mul_left n hΔ; simpa using this
  rw [qrun_none_mono tbl c n (n * Δ) hn hle] at hcj
  exact absurd hcj (by simp)

end URTM.TwoState
