/-
  `decideHalt` の正しさへ向けた土台層。**手書き**。キュー R13。

  `excursion` / `sojournOut` は燃料つきなので、そのままでは「停止する／しない」を
  **同値**で述べられない（燃料切れ `timeout` と本当の発散が混ざる）。ここでは:

    * **燃料の単調性** — 一度 `timeout` でない答えが出たら、燃料を増やしても同じ答え
    * **燃料に依らない結末**（Prop 版）— `Exits` / `HaltsInside` / `Diverges`
      と、それらが排他的であること
    * **平行移動不変性** — テープ全体を δ ずらすと、境界も δ ずれるだけ

  平行移動不変性は補題 C（空白半直線の応答列）の**自己相似の時間論法**で使う:
  空白半直線 [k,∞) と [k+1,∞) は平行移動で写り合うので、応答列が同一になる。

  ⚠ ここまでは補題 C そのものではない。C の**前提を用意する**層である。
-/
import URTM.TwoStateEntry

namespace URTM.TwoState

/-! ## 1. 燃料の単調性 -/

theorem excursion_succ_of_ne_timeout (π : Rule) (k : Int) :
    ∀ (n : Nat) (c : Conf2), excursion π k n c ≠ Sojourn.timeout →
      excursion π k (n + 1) c = excursion π k n c := by
  intro n
  induction n with
  | zero => intro c h; exact absurd (excursion_zero π k c) h
  | succ n ih =>
    intro c h
    cases hs : step2 π c with
    | none => rw [excursion_halt π k n hs, excursion_halt π k (n + 1) hs]
    | some c' =>
      by_cases hlt : c'.pos < k
      · rw [excursion_exit π k n hs hlt, excursion_exit π k (n + 1) hs hlt]
      · -- 内側の答えが timeout なら外も timeout（仮定に反する）
        have hne : excursion π k n c' ≠ Sojourn.timeout := by
          intro hT
          exact h (excursion_stay_timeout π k n hs hlt hT)
        have hrec := ih c' hne
        cases h2 : excursion π k n c' with
        | left s d =>
          rw [excursion_stay_left π k n hs hlt h2,
              excursion_stay_left π k (n + 1) hs hlt (by rw [hrec, h2])]
        | halted s d =>
          rw [excursion_stay_halted π k n hs hlt h2,
              excursion_stay_halted π k (n + 1) hs hlt (by rw [hrec, h2])]
        | timeout => exact absurd h2 hne

theorem excursion_mono (π : Rule) (k : Int) :
    ∀ (n n' : Nat) (c : Conf2), n ≤ n' → excursion π k n c ≠ Sojourn.timeout →
      excursion π k n' c = excursion π k n c := by
  intro n n'
  induction n' with
  | zero =>
    intro c hle h
    have : n = 0 := Nat.le_zero.mp hle
    rw [this]
  | succ m ih =>
    intro c hle h
    rcases Nat.lt_or_ge n (m + 1) with hlt | hge
    · have hnm : n ≤ m := Nat.lt_succ_iff.mp hlt
      have hrec := ih c hnm h
      rw [excursion_succ_of_ne_timeout π k m c (by rw [hrec]; exact h), hrec]
    · have : n = m + 1 := Nat.le_antisymm hle hge
      rw [this]

theorem sojournOut_succ_of_ne_timeout (π : Rule) (k : Int) :
    ∀ (n : Nat) (c : Conf2), sojournOut π k n c ≠ Sojourn.timeout →
      sojournOut π k (n + 1) c = sojournOut π k n c := by
  intro n
  induction n with
  | zero => intro c h; exact absurd (sojournOut_zero π k c) h
  | succ n ih =>
    intro c h
    cases hs : step2 π c with
    | none => rw [sojournOut_halt π k n hs, sojournOut_halt π k (n + 1) hs]
    | some c' =>
      by_cases hge : k ≤ c'.pos
      · rw [sojournOut_enter1 π k n hs hge, sojournOut_enter1 π k (n + 1) hs hge]
      · have hne : sojournOut π k n c' ≠ Sojourn.timeout := by
          intro hT
          exact h (sojournOut_stay_timeout π k n hs hge hT)
        have hrec := ih c' hne
        cases h2 : sojournOut π k n c' with
        | left s d =>
          rw [sojournOut_stay_left π k n hs hge h2,
              sojournOut_stay_left π k (n + 1) hs hge (by rw [hrec, h2])]
        | halted s d =>
          rw [sojournOut_stay_halted π k n hs hge h2,
              sojournOut_stay_halted π k (n + 1) hs hge (by rw [hrec, h2])]
        | timeout => exact absurd h2 hne

theorem sojournOut_mono (π : Rule) (k : Int) :
    ∀ (n n' : Nat) (c : Conf2), n ≤ n' → sojournOut π k n c ≠ Sojourn.timeout →
      sojournOut π k n' c = sojournOut π k n c := by
  intro n n'
  induction n' with
  | zero =>
    intro c hle h
    have : n = 0 := Nat.le_zero.mp hle
    rw [this]
  | succ m ih =>
    intro c hle h
    rcases Nat.lt_or_ge n (m + 1) with hlt | hge
    · have hnm : n ≤ m := Nat.lt_succ_iff.mp hlt
      have hrec := ih c hnm h
      rw [sojournOut_succ_of_ne_timeout π k m c (by rw [hrec]; exact h), hrec]
    · have : n = m + 1 := Nat.le_antisymm hle hge
      rw [this]

/-! ## 2. 燃料に依らない結末 -/

/-- 半直線 [k,∞) から**退場する**（燃料をいくらでも足せば `left` が出る）。 -/
def Exits (π : Rule) (k : Int) (c : Conf2) : Prop :=
  ∃ n s d, excursion π k n c = Sojourn.left s d

/-- 半直線の**中で停止する**。 -/
def HaltsInside (π : Rule) (k : Int) (c : Conf2) : Prop :=
  ∃ n s d, excursion π k n c = Sojourn.halted s d

/-- 退場も停止もしない（＝右へ逃走するか、中で無限ループ）。 -/
def Diverges (π : Rule) (k : Int) (c : Conf2) : Prop :=
  ¬ Exits π k c ∧ ¬ HaltsInside π k c

/-- 退場と中での停止は両立しない（単調性から）。 -/
theorem not_exits_and_halts (π : Rule) (k : Int) (c : Conf2) :
    ¬ (Exits π k c ∧ HaltsInside π k c) := by
  rintro ⟨⟨n₁, s₁, d₁, h₁⟩, ⟨n₂, s₂, d₂, h₂⟩⟩
  rcases Nat.le_total n₁ n₂ with hle | hle
  · have hne : excursion π k n₁ c ≠ Sojourn.timeout := by rw [h₁]; simp
    rw [excursion_mono π k n₁ n₂ c hle hne, h₁] at h₂
    exact absurd h₂ (by simp)
  · have hne : excursion π k n₂ c ≠ Sojourn.timeout := by rw [h₂]; simp
    rw [excursion_mono π k n₂ n₁ c hle hne, h₂] at h₁
    exact absurd h₁ (by simp)

/-- 3 つの結末はちょうど 1 つ起きる。 -/
theorem outcome_trichotomy (π : Rule) (k : Int) (c : Conf2) :
    (Exits π k c ∧ ¬ HaltsInside π k c ∧ ¬ Diverges π k c) ∨
    (¬ Exits π k c ∧ HaltsInside π k c ∧ ¬ Diverges π k c) ∨
    (¬ Exits π k c ∧ ¬ HaltsInside π k c ∧ Diverges π k c) := by
  by_cases he : Exits π k c
  · have hh : ¬ HaltsInside π k c := fun hh => not_exits_and_halts π k c ⟨he, hh⟩
    exact Or.inl ⟨he, hh, fun hd => hd.1 he⟩
  · by_cases hh : HaltsInside π k c
    · exact Or.inr (Or.inl ⟨he, hh, fun hd => hd.2 hh⟩)
    · exact Or.inr (Or.inr ⟨he, hh, ⟨he, hh⟩⟩)

/-- 退場するときの歩数と行き先は一意。 -/
theorem exits_unique (π : Rule) (k : Int) (c : Conf2) {n₁ n₂ s₁ s₂ : Nat} {d₁ d₂ : Conf2}
    (h₁ : excursion π k n₁ c = Sojourn.left s₁ d₁)
    (h₂ : excursion π k n₂ c = Sojourn.left s₂ d₂) : s₁ = s₂ ∧ d₁ = d₂ := by
  rcases Nat.le_total n₁ n₂ with hle | hle
  · have hne : excursion π k n₁ c ≠ Sojourn.timeout := by rw [h₁]; simp
    rw [excursion_mono π k n₁ n₂ c hle hne, h₁] at h₂
    injection h₂ with a b
    exact ⟨by first | exact a | exact a.symm, by first | exact b | exact b.symm⟩
  · have hne : excursion π k n₂ c ≠ Sojourn.timeout := by rw [h₂]; simp
    rw [excursion_mono π k n₂ n₁ c hle hne, h₂] at h₁
    injection h₁ with a b
    exact ⟨by first | exact a | exact a.symm, by first | exact b | exact b.symm⟩

/-! ## 3. 平行移動不変性（補題 C の自己相似論法の前提） -/

/-- テープ全体を δ だけ右へずらす。 -/
def shiftT (t : Int → Nat) (δ : Int) : Int → Nat := fun i => t (i - δ)

/-- 配置を δ だけ右へずらす。 -/
def shiftC (c : Conf2) (δ : Int) : Conf2 := ⟨shiftT c.tape δ, c.pos + δ, c.dir⟩

theorem shiftT_apply (t : Int → Nat) (δ i : Int) : shiftT t δ i = t (i - δ) := rfl

/-- 読み出しはずらしても同じ。 -/
theorem shift_read (c : Conf2) (δ : Int) :
    (shiftC c δ).tape (shiftC c δ).pos = c.tape c.pos := by
  show shiftT c.tape δ (c.pos + δ) = c.tape c.pos
  rw [shiftT_apply]
  congr 1
  omega

/-- 書込はずらしと可換。 -/
theorem write_shift (t : Int → Nat) (p : Int) (v : Nat) (δ : Int) :
    write (shiftT t δ) (p + δ) v = shiftT (write t p v) δ := by
  funext i
  show (if i = p + δ then v else shiftT t δ i) = (if i - δ = p then v else t (i - δ))
  by_cases h : i = p + δ
  · have _h2 : i - δ = p := by omega
    simp [h]
  · have h2 : ¬ i - δ = p := by omega
    simp [h, h2, shiftT_apply]

/-- 移動はずらしと可換。 -/
theorem move_shift (d : Dir) (p δ : Int) : move d (p + δ) = move d p + δ := by
  cases d
  · rw [move_L, move_L]; omega
  · rw [move_Z, move_Z]
  · rw [move_R, move_R]; omega

/-- **1 ステップは平行移動と可換**。 -/
theorem step2_shift (π : Rule) (c : Conf2) (δ : Int) :
    step2 π (shiftC c δ) = (step2 π c).map (fun x => shiftC x δ) := by
  have hread : (shiftC c δ).tape (shiftC c δ).pos = c.tape c.pos := shift_read c δ
  have hdir : (shiftC c δ).dir = c.dir := rfl
  cases hr : π c.dir (c.tape c.pos) with
  | none =>
    have h1 : step2 π (shiftC c δ) = none := by unfold step2; rw [hdir, hread, hr]
    have h2 : step2 π c = none := by unfold step2; rw [hr]
    rw [h1, h2]; rfl
  | some vd =>
    obtain ⟨v, d'⟩ := vd
    have h2 : step2 π c = some ⟨write c.tape c.pos v, move d' c.pos, d'⟩ := by
      unfold step2; rw [hr]
    have h1 : step2 π (shiftC c δ)
        = some ⟨write (shiftC c δ).tape (shiftC c δ).pos v, move d' (shiftC c δ).pos, d'⟩ := by
      unfold step2; rw [hdir, hread, hr]
    rw [h1, h2]
    show some _ = some (shiftC _ δ)
    congr 1
    show (⟨write (shiftT c.tape δ) (c.pos + δ) v, move d' (c.pos + δ), d'⟩ : Conf2)
        = ⟨shiftT (write c.tape c.pos v) δ, move d' c.pos + δ, d'⟩
    rw [write_shift, move_shift]

/-- 滞在の結末をずらす。 -/
def shiftS (r : Sojourn) (δ : Int) : Sojourn :=
  match r with
  | Sojourn.left s d => Sojourn.left s (shiftC d δ)
  | Sojourn.halted s d => Sojourn.halted s (shiftC d δ)
  | Sojourn.timeout => Sojourn.timeout

/-- **補題 C の前提: 空白半直線は平行移動で写り合う。**
    境界 k の滞在を δ ずらすと、境界 k+δ の滞在になる。 -/
theorem excursion_shift (π : Rule) (k δ : Int) :
    ∀ (n : Nat) (c : Conf2),
      excursion π (k + δ) n (shiftC c δ) = shiftS (excursion π k n c) δ := by
  intro n
  induction n with
  | zero => intro c; rw [excursion_zero, excursion_zero]; rfl
  | succ n ih =>
    intro c
    cases hs : step2 π c with
    | none =>
      have hs' : step2 π (shiftC c δ) = none := by rw [step2_shift, hs]; rfl
      rw [excursion_halt π (k + δ) n hs', excursion_halt π k n hs]
      rfl
    | some c' =>
      have hs' : step2 π (shiftC c δ) = some (shiftC c' δ) := by rw [step2_shift, hs]; rfl
      have hpos : (shiftC c' δ).pos = c'.pos + δ := rfl
      by_cases hlt : c'.pos < k
      · have hlt' : (shiftC c' δ).pos < k + δ := by rw [hpos]; omega
        rw [excursion_exit π (k + δ) n hs' hlt', excursion_exit π k n hs hlt]
        rfl
      · have hlt' : ¬ (shiftC c' δ).pos < k + δ := by rw [hpos]; omega
        have hrec := ih c'
        cases h2 : excursion π k n c' with
        | left s d =>
          rw [h2] at hrec
          rw [excursion_stay_left π (k + δ) n hs' hlt' hrec,
              excursion_stay_left π k n hs hlt h2]
          rfl
        | halted s d =>
          rw [h2] at hrec
          rw [excursion_stay_halted π (k + δ) n hs' hlt' hrec,
              excursion_stay_halted π k n hs hlt h2]
          rfl
        | timeout =>
          rw [h2] at hrec
          rw [excursion_stay_timeout π (k + δ) n hs' hlt' hrec,
              excursion_stay_timeout π k n hs hlt h2]
          rfl

/-- 全セル空白のテープ。 -/
def blankT : Int → Nat := fun _ => 0

/-- 空白テープはずらしても空白。 -/
theorem shiftT_blank (δ : Int) : shiftT blankT δ = blankT := rfl

/-- **空白半直線の自己相似性**: 境界 k の入場と境界 k+δ の入場は、
    歩数まで込みで同型（結末の型が一致し、退場先も平行移動で対応する）。 -/
theorem excursion_blank_shift (π : Rule) (k δ : Int) (n : Nat) :
    excursion π (k + δ) n ⟨blankT, k + δ, Dir.R⟩
      = shiftS (excursion π k n ⟨blankT, k, Dir.R⟩) δ := by
  have h : (shiftC ⟨blankT, k, Dir.R⟩ δ) = (⟨blankT, k + δ, Dir.R⟩ : Conf2) := by
    show (⟨shiftT blankT δ, k + δ, Dir.R⟩ : Conf2) = ⟨blankT, k + δ, Dir.R⟩
    rw [shiftT_blank]
  rw [← h, excursion_shift]

end URTM.TwoState
