/-
  **補題 4.1**（`docs/10_no_two_state_urtm.md` §4）の Lean 化。**手書き**。キュー R13。

  主張: 半直線 H = [k, ∞) について、
    * 1 回の**滞在**（入場から退場まで）の歩数・結末・退場時の H の中身は、
      **入場時の H の中身だけ**で決まる（左側の中身に一切依らない）
    * **m 回目の入場時の H の中身は、H の初期の中身と m だけの関数**である

  これが「任意の境界で左右の半直線は情報を交換できない」の正確な形であり、
  非存在定理（2 状態 URTM は存在しない）で空白半直線を自律系として解析できる根拠になる。

  土台は `URTM/TwoStateLocality.lean`（局所性補題）。ここで足すもの:
    * `step_frozen_right` / `run_frozen_right` — 局所性補題の**鏡像**
    * `excursion` — H の中の滞在。`excursion_local` がその局所性
    * `sojournOut` — H の外の滞在。再入場はつねに (位置 k, 方向 R) で、H は凍結
    * `hAfter` — **抽象 H 機械**（左側を一切見ずに H だけを m 回まわす）
    * `entryAt_hAfter` — 実行中の m 回目の入場が、抽象 H 機械の m 段目と一致する

  ⚠ 燃料（fuel）つきで定義してある。燃料切れは `timeout` で、**結果ではない**。

  実装メモ: 燃料再帰の定義を `rw`/`unfold` で開くと match が iota 簡約されずに詰まる。
  **場合ごとに畳んだ補題**（`excursion_succ_*` 等）を先に用意して、そちらだけを使う。
-/
import URTM.TwoStateLocality

namespace URTM.TwoState

/-! ## 0. 小道具 -/

theorem move_L (p : Int) : move Dir.L p = p - 1 := rfl
theorem move_Z (p : Int) : move Dir.Z p = p := rfl
theorem move_R (p : Int) : move Dir.R p = p + 1 := rfl

/-- `step2` が `some` を返したときの中身。 -/
theorem step2_some (π : Rule) {c c' : Conf2}
    (h : step2 π c = some c') :
    ∃ v d', π c.dir (c.tape c.pos) = some (v, d') ∧
      c'.tape = write c.tape c.pos v ∧ c'.pos = move d' c.pos ∧ c'.dir = d' := by
  unfold step2 at h
  cases hr : π c.dir (c.tape c.pos) with
  | none => rw [hr] at h; exact absurd h (by simp)
  | some vd =>
    obtain ⟨v, d'⟩ := vd
    rw [hr] at h
    have hc : c' = ⟨write c.tape c.pos v, move d' c.pos, d'⟩ := (Option.some.inj h).symm
    exact ⟨v, d', by first | exact hr | rfl, by rw [hc], by rw [hc], by rw [hc]⟩

/-! ## 1. 凍結の鏡像（ヘッドが k 未満なら k 以上は動かない） -/

theorem step_frozen_right (π : Rule) {k : Int} {c c' : Conf2}
    (hk : c.pos < k) (h : step2 π c = some c') :
    ∀ i, k ≤ i → c'.tape i = c.tape i := by
  intro i hi
  obtain ⟨v, d', _, ht, _, _⟩ := step2_some π h
  rw [ht]
  show write c.tape c.pos v i = c.tape i
  unfold write
  have hne : i ≠ c.pos := by
    intro he
    rw [he] at hi
    exact absurd hk (Int.not_lt.mpr hi)
  simp [hne]

theorem run_frozen_right (π : Rule) {k : Int} :
    ∀ (n : Nat) (c c' : Conf2),
      (∀ j, j ≤ n → ∀ cj, run2 π j c = some cj → cj.pos < k) →
      run2 π n c = some c' →
      ∀ i, k ≤ i → c'.tape i = c.tape i := by
  intro n
  induction n with
  | zero =>
    intro c c' _ h i _
    have : c = c' := Option.some.inj h
    rw [this]
  | succ n ih =>
    intro c c' hpos h i hi
    unfold run2 at h
    cases hs : step2 π c with
    | none => rw [hs] at h; exact absurd h (by simp)
    | some c₁ =>
      rw [hs] at h
      have hk0 : c.pos < k := hpos 0 (Nat.zero_le _) c rfl
      have h1 : c₁.tape i = c.tape i := step_frozen_right π hk0 hs i hi
      have hpos' : ∀ j, j ≤ n → ∀ cj, run2 π j c₁ = some cj → cj.pos < k := by
        intro j hj cj hj'
        apply hpos (j + 1) (Nat.succ_le_succ hj) cj
        unfold run2
        rw [hs]
        exact hj'
      rw [ih c₁ c' hpos' h i hi, h1]

/-! ## 2. 滞在（sojourn）の結果 -/

/-- 領域の中の滞在の結末。 -/
inductive Sojourn where
  | left (steps : Nat) (c : Conf2)     -- 領域を出た（退場）
  | halted (steps : Nat) (c : Conf2)   -- 領域の中で停止した
  | timeout                            -- 燃料切れ（**結果ではない**）

/-- 2 つの滞在が「H の上で一致」している。 -/
def SojournAgree (k : Int) : Sojourn → Sojourn → Prop
  | Sojourn.left s₁ d₁, Sojourn.left s₂ d₂ => s₁ = s₂ ∧ AgreeFrom k d₁ d₂
  | Sojourn.halted s₁ d₁, Sojourn.halted s₂ d₂ => s₁ = s₂ ∧ AgreeFrom k d₁ d₂
  | Sojourn.timeout, Sojourn.timeout => True
  | _, _ => False

/-! ## 3. H = [k,∞) の中の滞在 -/

/-- ヘッドが k 未満へ出るまで走らせる。 -/
def excursion (π : Rule) (k : Int) : Nat → Conf2 → Sojourn
  | 0, _ => Sojourn.timeout
  | n + 1, c =>
    match step2 π c with
    | none => Sojourn.halted 0 c
    | some c' =>
      if c'.pos < k then Sojourn.left 1 c'
      else
        match excursion π k n c' with
        | Sojourn.left s d => Sojourn.left (s + 1) d
        | Sojourn.halted s d => Sojourn.halted (s + 1) d
        | Sojourn.timeout => Sojourn.timeout

theorem excursion_zero (π : Rule) (k : Int) (c : Conf2) :
    excursion π k 0 c = Sojourn.timeout := rfl

theorem excursion_halt (π : Rule) (k : Int) (n : Nat) {c : Conf2}
    (h : step2 π c = none) : excursion π k (n + 1) c = Sojourn.halted 0 c := by
  simp [excursion, h]

theorem excursion_exit (π : Rule) (k : Int) (n : Nat) {c c' : Conf2}
    (h : step2 π c = some c') (hlt : c'.pos < k) :
    excursion π k (n + 1) c = Sojourn.left 1 c' := by
  simp [excursion, h, hlt]

theorem excursion_stay_left (π : Rule) (k : Int) (n : Nat) {c c' d : Conf2} {s : Nat}
    (h : step2 π c = some c') (hlt : ¬ c'.pos < k)
    (h2 : excursion π k n c' = Sojourn.left s d) :
    excursion π k (n + 1) c = Sojourn.left (s + 1) d := by
  simp [excursion, h, hlt, h2]

theorem excursion_stay_halted (π : Rule) (k : Int) (n : Nat) {c c' d : Conf2} {s : Nat}
    (h : step2 π c = some c') (hlt : ¬ c'.pos < k)
    (h2 : excursion π k n c' = Sojourn.halted s d) :
    excursion π k (n + 1) c = Sojourn.halted (s + 1) d := by
  simp [excursion, h, hlt, h2]

theorem excursion_stay_timeout (π : Rule) (k : Int) (n : Nat) {c c' : Conf2}
    (h : step2 π c = some c') (hlt : ¬ c'.pos < k)
    (h2 : excursion π k n c' = Sojourn.timeout) :
    excursion π k (n + 1) c = Sojourn.timeout := by
  simp [excursion, h, hlt, h2]

/-- 退場したなら、退場先は本当に k 未満にある。 -/
theorem excursion_exits (π : Rule) (k : Int) :
    ∀ (n : Nat) {c d : Conf2} {s : Nat},
      excursion π k n c = Sojourn.left s d → d.pos < k := by
  intro n
  induction n with
  | zero => intro c d s h; rw [excursion_zero] at h; exact absurd h (by simp)
  | succ n ih =>
    intro c d s h
    cases hs : step2 π c with
    | none => rw [excursion_halt π k n hs] at h; exact absurd h (by simp)
    | some c' =>
      by_cases hlt : c'.pos < k
      · rw [excursion_exit π k n hs hlt] at h
        injection h with _ hd
        rw [← hd]; exact hlt
      · cases h2 : excursion π k n c' with
        | left s₂ d₂ =>
          rw [excursion_stay_left π k n hs hlt h2] at h
          injection h with _ hd
          rw [← hd]; exact ih h2
        | halted s₂ d₂ => rw [excursion_stay_halted π k n hs hlt h2] at h; exact absurd h (by simp)
        | timeout => rw [excursion_stay_timeout π k n hs hlt h2] at h; exact absurd h (by simp)

/-- **補題 4.1（前半）**: H の中の 1 回の滞在は、入場時の H の中身だけで決まる。
    左側の中身がどれだけ違っても、歩数・結末・退場時の H の中身は同じ。 -/
theorem excursion_local (π : Rule) (k : Int) :
    ∀ (n : Nat) {c₁ c₂ : Conf2}, k ≤ c₁.pos → AgreeFrom k c₁ c₂ →
      SojournAgree k (excursion π k n c₁) (excursion π k n c₂) := by
  intro n
  induction n with
  | zero =>
    intro c₁ c₂ _ _
    rw [excursion_zero, excursion_zero]
    exact trivial
  | succ n ih =>
    intro c₁ c₂ hk H
    rcases step_local_right π hk H with ⟨e1, e2⟩ | ⟨d₁, d₂, e1, e2, H'⟩
    · rw [excursion_halt π k n e1, excursion_halt π k n e2]
      exact ⟨rfl, H⟩
    · have hpos : d₁.pos = d₂.pos := H'.2.1
      by_cases hlt : d₁.pos < k
      · have hlt2 : d₂.pos < k := by rw [← hpos]; exact hlt
        rw [excursion_exit π k n e1 hlt, excursion_exit π k n e2 hlt2]
        exact ⟨rfl, H'⟩
      · have hlt2 : ¬ d₂.pos < k := by rw [← hpos]; exact hlt
        have hk' : k ≤ d₁.pos := Int.not_lt.mp hlt
        have hrec := ih hk' H'
        cases h1 : excursion π k n d₁ with
        | left s₁ f₁ =>
          cases h2 : excursion π k n d₂ with
          | left s₂ f₂ =>
            rw [h1, h2] at hrec
            rw [excursion_stay_left π k n e1 hlt h1, excursion_stay_left π k n e2 hlt2 h2]
            exact ⟨congrArg (· + 1) hrec.1, hrec.2⟩
          | halted s₂ f₂ => rw [h1, h2] at hrec; exact absurd hrec not_false
          | timeout => rw [h1, h2] at hrec; exact absurd hrec not_false
        | halted s₁ f₁ =>
          cases h2 : excursion π k n d₂ with
          | left s₂ f₂ => rw [h1, h2] at hrec; exact absurd hrec not_false
          | halted s₂ f₂ =>
            rw [h1, h2] at hrec
            rw [excursion_stay_halted π k n e1 hlt h1, excursion_stay_halted π k n e2 hlt2 h2]
            exact ⟨congrArg (· + 1) hrec.1, hrec.2⟩
          | timeout => rw [h1, h2] at hrec; exact absurd hrec not_false
        | timeout =>
          cases h2 : excursion π k n d₂ with
          | left s₂ f₂ => rw [h1, h2] at hrec; exact absurd hrec not_false
          | halted s₂ f₂ => rw [h1, h2] at hrec; exact absurd hrec not_false
          | timeout =>
            rw [excursion_stay_timeout π k n e1 hlt h1, excursion_stay_timeout π k n e2 hlt2 h2]
            exact trivial

/-! ## 4. H の外の滞在（再入場はつねに (k, R) で、H は凍結される） -/

/-- ヘッドが k 以上へ入るまで走らせる。 -/
def sojournOut (π : Rule) (k : Int) : Nat → Conf2 → Sojourn
  | 0, _ => Sojourn.timeout
  | n + 1, c =>
    match step2 π c with
    | none => Sojourn.halted 0 c
    | some c' =>
      if k ≤ c'.pos then Sojourn.left 1 c'
      else
        match sojournOut π k n c' with
        | Sojourn.left s d => Sojourn.left (s + 1) d
        | Sojourn.halted s d => Sojourn.halted (s + 1) d
        | Sojourn.timeout => Sojourn.timeout

theorem sojournOut_zero (π : Rule) (k : Int) (c : Conf2) :
    sojournOut π k 0 c = Sojourn.timeout := rfl

theorem sojournOut_halt (π : Rule) (k : Int) (n : Nat) {c : Conf2}
    (h : step2 π c = none) : sojournOut π k (n + 1) c = Sojourn.halted 0 c := by
  simp [sojournOut, h]

theorem sojournOut_enter1 (π : Rule) (k : Int) (n : Nat) {c c' : Conf2}
    (h : step2 π c = some c') (hge : k ≤ c'.pos) :
    sojournOut π k (n + 1) c = Sojourn.left 1 c' := by
  simp [sojournOut, h, hge]

theorem sojournOut_stay_left (π : Rule) (k : Int) (n : Nat) {c c' d : Conf2} {s : Nat}
    (h : step2 π c = some c') (hge : ¬ k ≤ c'.pos)
    (h2 : sojournOut π k n c' = Sojourn.left s d) :
    sojournOut π k (n + 1) c = Sojourn.left (s + 1) d := by
  simp [sojournOut, h, hge, h2]

theorem sojournOut_stay_halted (π : Rule) (k : Int) (n : Nat) {c c' d : Conf2} {s : Nat}
    (h : step2 π c = some c') (hge : ¬ k ≤ c'.pos)
    (h2 : sojournOut π k n c' = Sojourn.halted s d) :
    sojournOut π k (n + 1) c = Sojourn.halted (s + 1) d := by
  simp [sojournOut, h, hge, h2]

theorem sojournOut_stay_timeout (π : Rule) (k : Int) (n : Nat) {c c' : Conf2}
    (h : step2 π c = some c') (hge : ¬ k ≤ c'.pos)
    (h2 : sojournOut π k n c' = Sojourn.timeout) :
    sojournOut π k (n + 1) c = Sojourn.timeout := by
  simp [sojournOut, h, hge, h2]

/-- 1 歩で k 未満から k 以上へ移るなら、着地はちょうど k で、方向は右。 -/
theorem cross_at_k (π : Rule) {k : Int} {c c' : Conf2}
    (hk : c.pos < k) (h : step2 π c = some c') (hk' : k ≤ c'.pos) :
    c'.pos = k ∧ c'.dir = Dir.R := by
  obtain ⟨v, d', _, _, hp, hd⟩ := step2_some π h
  cases hdd : d' with
  | L =>
    exfalso
    rw [hdd, move_L] at hp
    omega
  | Z =>
    exfalso
    rw [hdd, move_Z] at hp
    omega
  | R =>
    rw [hdd, move_R] at hp
    exact ⟨by omega, by rw [hd, hdd]⟩

/-- **補題 4.1（後半の土台）**: H の外の滞在から戻ってくるとき、
    ヘッドはちょうど k に方向 R で入り、**H の中身は変わっていない**。 -/
theorem sojournOut_enter (π : Rule) (k : Int) :
    ∀ (n : Nat) {c d : Conf2} {s : Nat}, c.pos < k →
      sojournOut π k n c = Sojourn.left s d →
      d.pos = k ∧ d.dir = Dir.R ∧ ∀ i, k ≤ i → d.tape i = c.tape i := by
  intro n
  induction n with
  | zero => intro c d s _ h; rw [sojournOut_zero] at h; exact absurd h (by simp)
  | succ n ih =>
    intro c d s hk h
    cases hs : step2 π c with
    | none => rw [sojournOut_halt π k n hs] at h; exact absurd h (by simp)
    | some c' =>
      by_cases hge : k ≤ c'.pos
      · rw [sojournOut_enter1 π k n hs hge] at h
        injection h with _ hd
        obtain ⟨hp, hdir⟩ := cross_at_k π hk hs hge
        exact ⟨by rw [← hd]; exact hp, by rw [← hd]; exact hdir,
               fun i hi => by rw [← hd]; exact step_frozen_right π hk hs i hi⟩
      · have hlt : c'.pos < k := Int.not_le.mp hge
        cases h2 : sojournOut π k n c' with
        | left s₂ d₂ =>
          rw [sojournOut_stay_left π k n hs hge h2] at h
          injection h with _ hd
          obtain ⟨hp, hdir, hfr⟩ := ih hlt h2
          refine ⟨by rw [← hd]; exact hp, by rw [← hd]; exact hdir, ?_⟩
          intro i hi
          rw [← hd, hfr i hi]
          exact step_frozen_right π hk hs i hi
        | halted s₂ d₂ =>
          rw [sojournOut_stay_halted π k n hs hge h2] at h; exact absurd h (by simp)
        | timeout =>
          rw [sojournOut_stay_timeout π k n hs hge h2] at h; exact absurd h (by simp)

/-! ## 5. 抽象 H 機械（左側を一切見ない） -/

/-- H の中身だけを m 回まわす。入場配置はつねに (テープ t, 位置 k, 方向 R)。
    **左側の情報は一切入らない。** -/
def hAfter (π : Rule) (k : Int) (fuel : Nat) : Nat → (Int → Nat) → Option (Int → Nat)
  | 0, t => some t
  | m + 1, t =>
    match excursion π k fuel ⟨t, k, Dir.R⟩ with
    | Sojourn.left _ d => hAfter π k fuel m d.tape
    | _ => none

theorem hAfter_zero (π : Rule) (k : Int) (fuel : Nat) (t : Int → Nat) :
    hAfter π k fuel 0 t = some t := rfl

theorem hAfter_succ_left (π : Rule) (k : Int) (fuel m : Nat) {t : Int → Nat}
    {s : Nat} {d : Conf2} (h : excursion π k fuel ⟨t, k, Dir.R⟩ = Sojourn.left s d) :
    hAfter π k fuel (m + 1) t = hAfter π k fuel m d.tape := by
  simp [hAfter, h]

theorem hAfter_succ_halted (π : Rule) (k : Int) (fuel m : Nat) {t : Int → Nat}
    {s : Nat} {d : Conf2} (h : excursion π k fuel ⟨t, k, Dir.R⟩ = Sojourn.halted s d) :
    hAfter π k fuel (m + 1) t = none := by
  simp [hAfter, h]

theorem hAfter_succ_timeout (π : Rule) (k : Int) (fuel m : Nat) {t : Int → Nat}
    (h : excursion π k fuel ⟨t, k, Dir.R⟩ = Sojourn.timeout) :
    hAfter π k fuel (m + 1) t = none := by
  simp [hAfter, h]

/-- 2 つの `Option (Int → Nat)` が H の上で一致。 -/
def OptAgreeFrom (k : Int) : Option (Int → Nat) → Option (Int → Nat) → Prop
  | some t₁, some t₂ => ∀ i, k ≤ i → t₁ i = t₂ i
  | none, none => True
  | _, _ => False

/-- **補題 4.1（well-defined 部分）**: 抽象 H 機械は H の中身だけに依存する。 -/
theorem hAfter_congr (π : Rule) (k : Int) (fuel : Nat) :
    ∀ (m : Nat) {t₁ t₂ : Int → Nat}, (∀ i, k ≤ i → t₁ i = t₂ i) →
      OptAgreeFrom k (hAfter π k fuel m t₁) (hAfter π k fuel m t₂) := by
  intro m
  induction m with
  | zero => intro t₁ t₂ h; rw [hAfter_zero, hAfter_zero]; exact h
  | succ m ih =>
    intro t₁ t₂ h
    have hA : AgreeFrom k (⟨t₁, k, Dir.R⟩ : Conf2) ⟨t₂, k, Dir.R⟩ := ⟨h, rfl, rfl⟩
    have hk : k ≤ (⟨t₁, k, Dir.R⟩ : Conf2).pos := Int.le_refl k
    have hloc := excursion_local π k fuel hk hA
    cases h1 : excursion π k fuel (⟨t₁, k, Dir.R⟩ : Conf2) with
    | left s₁ d₁ =>
      cases h2 : excursion π k fuel (⟨t₂, k, Dir.R⟩ : Conf2) with
      | left s₂ d₂ =>
        rw [h1, h2] at hloc
        rw [hAfter_succ_left π k fuel m h1, hAfter_succ_left π k fuel m h2]
        exact ih hloc.2.1
      | halted s₂ d₂ => rw [h1, h2] at hloc; exact absurd hloc not_false
      | timeout => rw [h1, h2] at hloc; exact absurd hloc not_false
    | halted s₁ d₁ =>
      cases h2 : excursion π k fuel (⟨t₂, k, Dir.R⟩ : Conf2) with
      | left s₂ d₂ => rw [h1, h2] at hloc; exact absurd hloc not_false
      | halted s₂ d₂ =>
        rw [hAfter_succ_halted π k fuel m h1, hAfter_succ_halted π k fuel m h2]
        exact trivial
      | timeout => rw [h1, h2] at hloc; exact absurd hloc not_false
    | timeout =>
      cases h2 : excursion π k fuel (⟨t₂, k, Dir.R⟩ : Conf2) with
      | left s₂ d₂ => rw [h1, h2] at hloc; exact absurd hloc not_false
      | halted s₂ d₂ => rw [h1, h2] at hloc; exact absurd hloc not_false
      | timeout =>
        rw [hAfter_succ_timeout π k fuel m h1, hAfter_succ_timeout π k fuel m h2]
        exact trivial

/-! ## 6. 実行中の m 回目の入場 -/

/-- 実行中の m 回目の入場配置（入場済みの配置から数える）。
    滞在 → 外の滞在 → 滞在 → … と交互に進む。 -/
def entryAt (π : Rule) (k : Int) (fuel : Nat) : Nat → Conf2 → Option Conf2
  | 0, c => some c
  | m + 1, c =>
    match excursion π k fuel c with
    | Sojourn.left _ d =>
      match sojournOut π k fuel d with
      | Sojourn.left _ e => entryAt π k fuel m e
      | _ => none
    | _ => none

theorem entryAt_zero (π : Rule) (k : Int) (fuel : Nat) (c : Conf2) :
    entryAt π k fuel 0 c = some c := rfl

theorem entryAt_succ (π : Rule) (k : Int) (fuel m : Nat) {c d e : Conf2} {s₁ s₂ : Nat}
    (h1 : excursion π k fuel c = Sojourn.left s₁ d)
    (h2 : sojournOut π k fuel d = Sojourn.left s₂ e) :
    entryAt π k fuel (m + 1) c = entryAt π k fuel m e := by
  simp [entryAt, h1, h2]

theorem entryAt_succ_out_halted (π : Rule) (k : Int) (fuel m : Nat) {c d e : Conf2}
    {s₁ s₂ : Nat} (h1 : excursion π k fuel c = Sojourn.left s₁ d)
    (h2 : sojournOut π k fuel d = Sojourn.halted s₂ e) :
    entryAt π k fuel (m + 1) c = none := by
  simp [entryAt, h1, h2]

theorem entryAt_succ_out_timeout (π : Rule) (k : Int) (fuel m : Nat) {c d : Conf2}
    {s₁ : Nat} (h1 : excursion π k fuel c = Sojourn.left s₁ d)
    (h2 : sojournOut π k fuel d = Sojourn.timeout) :
    entryAt π k fuel (m + 1) c = none := by
  simp [entryAt, h1, h2]

theorem entryAt_succ_halted (π : Rule) (k : Int) (fuel m : Nat) {c d : Conf2} {s : Nat}
    (h1 : excursion π k fuel c = Sojourn.halted s d) :
    entryAt π k fuel (m + 1) c = none := by
  simp [entryAt, h1]

theorem entryAt_succ_timeout (π : Rule) (k : Int) (fuel m : Nat) {c : Conf2}
    (h1 : excursion π k fuel c = Sojourn.timeout) :
    entryAt π k fuel (m + 1) c = none := by
  simp [entryAt, h1]

/-- **補題 4.1（本体）**: 実行中の m 回目の入場時の H の中身は、
    **H の初期の中身と m だけの関数**である（左側の中身に依らない）。

    正確には、実行が m 回目の入場に達したなら、そのときの H の中身は
    抽象 H 機械 `hAfter π k fuel m`（左側を一切見ない）の出力と H の上で一致し、
    ヘッドはつねに (位置 k, 方向 R) にある。 -/
theorem entryAt_hAfter (π : Rule) (k : Int) (fuel : Nat) :
    ∀ (m : Nat) {c d : Conf2}, c.pos = k → c.dir = Dir.R →
      entryAt π k fuel m c = some d →
      d.pos = k ∧ d.dir = Dir.R ∧
      ∃ t, hAfter π k fuel m c.tape = some t ∧ ∀ i, k ≤ i → d.tape i = t i := by
  intro m
  induction m with
  | zero =>
    intro c d hp hd h
    rw [entryAt_zero] at h
    have hcd : c = d := Option.some.inj h
    subst hcd
    exact ⟨hp, hd, c.tape, hAfter_zero π k fuel c.tape, fun _ _ => rfl⟩
  | succ m ih =>
    intro c d hp hd h
    -- 実行の滞在は、抽象機械の滞在とまったく同じ配置から始まる
    have hc : (⟨c.tape, k, Dir.R⟩ : Conf2) = c := by
      rw [← hp, ← hd]
    cases h1 : excursion π k fuel c with
    | left s₁ d₁ =>
      cases h2 : sojournOut π k fuel d₁ with
      | left s₂ e =>
        rw [entryAt_succ π k fuel m h1 h2] at h
        have hd₁ : d₁.pos < k := excursion_exits π k fuel h1
        obtain ⟨hep, hedir, hefr⟩ := sojournOut_enter π k fuel hd₁ h2
        obtain ⟨hdp, hddir, t, hht, hagree⟩ := ih hep hedir h
        refine ⟨hdp, hddir, ?_⟩
        -- 抽象側: hAfter (m+1) c.tape = hAfter m d₁.tape
        have h1' : excursion π k fuel (⟨c.tape, k, Dir.R⟩ : Conf2) = Sojourn.left s₁ d₁ := by
          rw [hc]; exact h1
        have habs : hAfter π k fuel (m + 1) c.tape = hAfter π k fuel m d₁.tape :=
          hAfter_succ_left π k fuel m h1'
        -- e.tape と d₁.tape は H 上で一致するので hAfter も一致
        have hcong := hAfter_congr π k fuel m (t₁ := e.tape) (t₂ := d₁.tape) hefr
        rw [hht] at hcong
        cases h3 : hAfter π k fuel m d₁.tape with
        | none => rw [h3] at hcong; exact absurd hcong not_false
        | some t' =>
          rw [h3] at hcong
          refine ⟨t', by rw [habs, h3], ?_⟩
          intro i hi
          rw [hagree i hi]
          exact hcong i hi
      | halted s₂ e =>
        rw [entryAt_succ_out_halted π k fuel m h1 h2] at h; exact absurd h (by simp)
      | timeout =>
        rw [entryAt_succ_out_timeout π k fuel m h1 h2] at h; exact absurd h (by simp)
    | halted s₁ d₁ =>
      rw [entryAt_succ_halted π k fuel m h1] at h; exact absurd h (by simp)
    | timeout =>
      rw [entryAt_succ_timeout π k fuel m h1] at h; exact absurd h (by simp)

/-! ## 7. 空虚でないことの確認（m ≥ 1 の入場が実際に起きる具体例） -/

/-- H に入ると 1 歩で記号を反転して退場し、外では 1 歩で再入場する機械。 -/
def demoπ : Rule := fun d s =>
  match d with
  | Dir.R => some (1 - s, Dir.L)
  | Dir.L => some (s, Dir.R)
  | Dir.Z => none

def demoT : Int → Nat := fun _ => 0
def demoC : Conf2 := ⟨demoT, 0, Dir.R⟩
def demoOut : Conf2 := ⟨write demoT 0 1, -1, Dir.L⟩
def demoBack : Conf2 := ⟨write (write demoT 0 1) (-1) 0, 0, Dir.R⟩

theorem demo_step1 : step2 demoπ demoC = some demoOut := rfl
theorem demo_step2 : step2 demoπ demoOut = some demoBack := rfl

theorem demo_exc : excursion demoπ 0 1 demoC = Sojourn.left 1 demoOut :=
  excursion_exit demoπ 0 0 demo_step1 (by decide)

theorem demo_out : sojournOut demoπ 0 1 demoOut = Sojourn.left 1 demoBack :=
  sojournOut_enter1 demoπ 0 0 demo_step2 (by decide)

/-- **1 回目の入場が実際に起きる**（`entryAt` が `some` を返す）。 -/
theorem demo_entry1 : entryAt demoπ 0 1 1 demoC = some demoBack := by
  rw [entryAt_succ demoπ 0 1 0 demo_exc demo_out, entryAt_zero]

/-- 補題 4.1 をその具体例に当てたもの（仮説がすべて外れる ＝ 空虚でない）。 -/
theorem demo_lemma41 :
    demoBack.pos = 0 ∧ demoBack.dir = Dir.R ∧
    ∃ t, hAfter demoπ 0 1 1 demoC.tape = some t ∧ ∀ i, 0 ≤ i → demoBack.tape i = t i :=
  entryAt_hAfter demoπ 0 1 1 rfl rfl demo_entry1

end URTM.TwoState
