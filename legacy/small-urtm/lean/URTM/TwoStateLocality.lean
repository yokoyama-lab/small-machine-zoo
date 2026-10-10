/-
  2 状態 RTM（方向状態機械）の**局所性補題**。**手書き**。/goal「2 状態 URTM の非存在」の核。

  構造定理（URTM/TwoState.lean）により 2 状態 RTM は「状態 ＝ 直前の移動方向」の機械
  （方向状態機械）に帰着する。ここではその機械を両側無限テープ上で直接定義し、
  **ヘッドが位置 k 以上に居る間は、k 未満のセルは読まれも書かれもしない**ことを示す。

    * `step_frozen_left` : ヘッドが k 以上なら 1 ステップで k 未満のセルは不変
    * `step_local_right` : k 以上のセルとヘッドが一致する 2 配置は、1 ステップ後も
                           k 以上で一致する（k 未満の中身に依存しない）
    * `run_frozen_left` / `run_local_right` : それを n ステップに伸ばしたもの

  これが「任意の境界で左右の半直線は情報を交換できない」の機械証明である。
  非存在定理の残りの部分（半直線の応答列が m だけの関数 → 空白半直線の解析 →
  中央有限領域の周期性 → 停止問題の決定可能性 → Def.7.1 との矛盾）は
  docs/10_no_two_state_urtm.md の紙の証明。**層は人間が判断する。**
-/
import URTM.Basic

namespace URTM.TwoState

/-- 両側無限テープ上の配置。状態は方向そのもの（構造定理による）。 -/
structure Conf2 where
  tape : Int → Nat
  pos : Int
  dir : Dir

/-- 遷移規則 π : (直前の方向, 記号) ⇀ (書込記号, 次の方向)。 -/
abbrev Rule := Dir → Nat → Option (Nat × Dir)

def move (d : Dir) (p : Int) : Int :=
  match d with
  | Dir.L => p - 1
  | Dir.Z => p
  | Dir.R => p + 1

def write (t : Int → Nat) (p : Int) (v : Nat) : Int → Nat :=
  fun i => if i = p then v else t i

/-- 1 ステップ。規則が無ければ停止（`none`）。 -/
def step2 (π : Rule) (c : Conf2) : Option Conf2 :=
  match π c.dir (c.tape c.pos) with
  | none => none
  | some (v, d') => some ⟨write c.tape c.pos v, move d' c.pos, d'⟩

/-- n ステップ（途中で停止したら `none`）。 -/
def run2 (π : Rule) : Nat → Conf2 → Option Conf2
  | 0, c => some c
  | n + 1, c =>
    match step2 π c with
    | none => none
    | some c' => run2 π n c'

/-- k 以上のセルで一致し、ヘッドの位置と方向も一致する。 -/
def AgreeFrom (k : Int) (c₁ c₂ : Conf2) : Prop :=
  (∀ i, k ≤ i → c₁.tape i = c₂.tape i) ∧ c₁.pos = c₂.pos ∧ c₁.dir = c₂.dir

/-! ## 1 ステップの局所性 -/

/-- ヘッドが k 以上に居れば、1 ステップで k 未満のセルは変わらない。 -/
theorem step_frozen_left (π : Rule) {k : Int} {c c' : Conf2}
    (hk : k ≤ c.pos) (h : step2 π c = some c') :
    ∀ i, i < k → c'.tape i = c.tape i := by
  intro i hi
  unfold step2 at h
  cases hr : π c.dir (c.tape c.pos) with
  | none => rw [hr] at h; exact absurd h (by simp)
  | some vd =>
    rw [hr] at h
    obtain ⟨v, d'⟩ := vd
    have hc : c' = ⟨write c.tape c.pos v, move d' c.pos, d'⟩ := by
      have := Option.some.inj h
      exact this.symm
    rw [hc]
    show write c.tape c.pos v i = c.tape i
    unfold write
    have hne : i ≠ c.pos := by
      intro he
      rw [he] at hi
      exact absurd hk (Int.not_le.mpr hi)
    simp [hne]

/-- k 以上で一致する 2 配置（ヘッドも k 以上）は、1 ステップ後も k 以上で一致する。
    停止の有無も一致する。 -/
theorem step_local_right (π : Rule) {k : Int} {c₁ c₂ : Conf2}
    (hk : k ≤ c₁.pos) (H : AgreeFrom k c₁ c₂) :
    (step2 π c₁ = none ∧ step2 π c₂ = none) ∨
    ∃ c₁' c₂', step2 π c₁ = some c₁' ∧ step2 π c₂ = some c₂' ∧ AgreeFrom k c₁' c₂' := by
  obtain ⟨Ht, Hp, Hd⟩ := H
  have hread : c₂.tape c₂.pos = c₁.tape c₁.pos := by
    rw [← Hp]; exact (Ht c₁.pos hk).symm
  unfold step2
  rw [← Hd, hread]
  cases hr : π c₁.dir (c₁.tape c₁.pos) with
  | none => exact Or.inl ⟨rfl, rfl⟩
  | some vd =>
    obtain ⟨v, d'⟩ := vd
    refine Or.inr ⟨_, _, rfl, rfl, ?_, ?_, rfl⟩
    · intro i hi
      show write c₁.tape c₁.pos v i = write c₂.tape c₂.pos v i
      unfold write
      rw [← Hp]
      by_cases he : i = c₁.pos
      · simp [he]
      · simp [he, Ht i hi]
    · show move d' c₁.pos = move d' c₂.pos
      rw [Hp]

/-! ## n ステップへ -/

/-- ヘッドが n ステップの間ずっと k 以上に居るなら、k 未満のセルは不変。
    「ずっと k 以上」は各ステップの配置で述べる。 -/
theorem run_frozen_left (π : Rule) {k : Int} :
    ∀ (n : Nat) (c c' : Conf2),
      (∀ j, j ≤ n → ∀ cj, run2 π j c = some cj → k ≤ cj.pos) →
      run2 π n c = some c' →
      ∀ i, i < k → c'.tape i = c.tape i := by
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
      have hk0 : k ≤ c.pos := hpos 0 (Nat.zero_le _) c rfl
      have h1 : c₁.tape i = c.tape i := step_frozen_left π hk0 hs i hi
      have hpos' : ∀ j, j ≤ n → ∀ cj, run2 π j c₁ = some cj → k ≤ cj.pos := by
        intro j hj cj hj'
        apply hpos (j + 1) (Nat.succ_le_succ hj) cj
        unfold run2
        rw [hs]
        exact hj'
      rw [ih c₁ c' hpos' h i hi, h1]

/-- k 以上で一致する 2 配置は、ヘッドが k 以上に居る限り、n ステップ後も k 以上で一致し、
    停止のタイミングも一致する。**k 未満の中身は結果に一切影響しない。** -/
theorem run_local_right (π : Rule) {k : Int} :
    ∀ (n : Nat) (c₁ c₂ : Conf2),
      AgreeFrom k c₁ c₂ →
      (∀ j, j < n → ∀ cj, run2 π j c₁ = some cj → k ≤ cj.pos) →
      (run2 π n c₁ = none ∧ run2 π n c₂ = none) ∨
      ∃ c₁' c₂', run2 π n c₁ = some c₁' ∧ run2 π n c₂ = some c₂' ∧ AgreeFrom k c₁' c₂' := by
  intro n
  induction n with
  | zero =>
    intro c₁ c₂ H _
    exact Or.inr ⟨c₁, c₂, rfl, rfl, H⟩
  | succ n ih =>
    intro c₁ c₂ H hpos
    have hk0 : k ≤ c₁.pos := hpos 0 (Nat.zero_lt_succ _) c₁ rfl
    rcases step_local_right π hk0 H with ⟨e1, e2⟩ | ⟨d₁, d₂, e1, e2, H'⟩
    · left
      constructor
      · unfold run2; rw [e1]
      · unfold run2; rw [e2]
    · have hpos' : ∀ j, j < n → ∀ cj, run2 π j d₁ = some cj → k ≤ cj.pos := by
        intro j hj cj hj'
        apply hpos (j + 1) (Nat.succ_lt_succ hj) cj
        unfold run2; rw [e1]; exact hj'
      rcases ih d₁ d₂ H' hpos' with ⟨f1, f2⟩ | ⟨g₁, g₂, f1, f2, H''⟩
      · left
        constructor
        · unfold run2; rw [e1]; exact f1
        · unfold run2; rw [e2]; exact f2
      · right
        refine ⟨g₁, g₂, ?_, ?_, H''⟩
        · unfold run2; rw [e1]; exact f1
        · unfold run2; rw [e2]; exact f2

end URTM.TwoState
