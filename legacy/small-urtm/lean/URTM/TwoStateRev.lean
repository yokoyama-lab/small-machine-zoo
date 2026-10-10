/-
  **可逆性を使う層**。**手書き**。キュー R13（`decideHalt` へ向けて）。

  ここまでの層は可逆性を一度も使っていなかった（局所性・入れ子・平行移動は
  決定性だけで出る）。可逆性を入れると次が出る:

    * `step2_injective` — 1 ステップは**単射**（Morita Def. 5.4 から）
    * `run2_no_rho` — **設定が一度でも繰り返せば、出発点に戻る**（軌道は ρ 形にならず
      純粋な周期になる）

  これは `decideHalt` の要になる。非可逆なら「途中で合流して周期に入る」があり得るので
  周期検出は「見たことのある設定」を全部覚える必要があるが、可逆なら
  **出発点に戻るかどうかだけ見ればよい**。

  したがって滞在の結末は次の 4 つに分かれる:
    退場 / 中で停止 / **出発点へ戻る（＝以後ずっと同じことを繰り返す＝発散）** / 無限に遠ざかる
-/
import URTM.TwoStateNest

namespace URTM.TwoState

/-! ## 1. 可逆性 -/

/-- Morita Def. 5.4 の可逆性を方向状態機械に写したもの。
    「同じ次状態（＝同じ方向）へ同じ記号を書く規則は同一」。 -/
def Rev (π : Rule) : Prop :=
  ∀ d₁ s₁ d₂ s₂ v e, π d₁ s₁ = some (v, e) → π d₂ s₂ = some (v, e) →
    d₁ = d₂ ∧ s₁ = s₂

/-- 移動は単射。 -/
theorem move_injective (d : Dir) {p q : Int} (h : move d p = move d q) : p = q := by
  cases d
  · rw [move_L, move_L] at h; omega
  · rw [move_Z, move_Z] at h; exact h
  · rw [move_R, move_R] at h; omega

/-- 書込を戻す: `write t p v` の p 番地は v。 -/
theorem write_at (t : Int → Nat) (p : Int) (v : Nat) : write t p v p = v := by
  unfold write; simp

/-- 書込を戻す: p 以外は元のまま。 -/
theorem write_off (t : Int → Nat) (p : Int) (v : Nat) {i : Int} (h : i ≠ p) :
    write t p v i = t i := by
  unfold write; simp [h]

/-- **1 ステップは単射**（可逆性から）。 -/
theorem step2_injective (π : Rule) (hrev : Rev π) {c₁ c₂ d : Conf2}
    (h₁ : step2 π c₁ = some d) (h₂ : step2 π c₂ = some d) : c₁ = c₂ := by
  obtain ⟨v₁, e₁, hr₁, ht₁, hp₁, hd₁⟩ := step2_some π h₁
  obtain ⟨v₂, e₂, hr₂, ht₂, hp₂, hd₂⟩ := step2_some π h₂
  -- 方向が一致
  have he : e₁ = e₂ := by rw [← hd₁, ← hd₂]
  -- 位置が一致（move は単射）
  have hpos : c₁.pos = c₂.pos := by
    apply move_injective e₁
    rw [← hp₁, hp₂, he]
  -- 書いた記号が一致
  have hv : v₁ = v₂ := by
    have a₁ : d.tape c₁.pos = v₁ := by rw [ht₁]; exact write_at _ _ _
    have a₂ : d.tape c₂.pos = v₂ := by rw [ht₂]; exact write_at _ _ _
    rw [← a₁, ← a₂, hpos]
  -- 可逆性から規則が同一 ⇒ 方向と読んだ記号が一致
  have hrr₂ : π c₂.dir (c₂.tape c₂.pos) = some (v₁, e₁) := by rw [hr₂, hv, he]
  obtain ⟨hdir, hread⟩ := hrev _ _ _ _ v₁ e₁ hr₁ hrr₂
  -- テープが一致
  have htape : c₁.tape = c₂.tape := by
    funext i
    by_cases hi : i = c₁.pos
    · rw [hi, hread, hpos]
    · have hi₂ : i ≠ c₂.pos := by rw [← hpos]; exact hi
      have e₁' : d.tape i = c₁.tape i := by rw [ht₁]; exact write_off _ _ _ hi
      have e₂' : d.tape i = c₂.tape i := by rw [ht₂]; exact write_off _ _ _ hi₂
      rw [← e₁', e₂']
  cases c₁ with
  | mk t₁ p₁ dd₁ =>
    cases c₂ with
    | mk t₂ p₂ dd₂ =>
      simp only [Conf2.mk.injEq]
      exact ⟨htape, hpos, hdir⟩

/-! ## 2. 実行の分解 -/

theorem run2_succ_none (π : Rule) (n : Nat) {c : Conf2} (h : step2 π c = none) :
    run2 π (n + 1) c = none := by simp [run2, h]

theorem run2_succ_some (π : Rule) (n : Nat) {c c' : Conf2} (h : step2 π c = some c') :
    run2 π (n + 1) c = run2 π n c' := by simp [run2, h]

theorem run2_one (π : Rule) (c : Conf2) : run2 π 1 c = step2 π c := by
  cases hs : step2 π c with
  | none => rw [run2_succ_none π 0 hs]
  | some c' => rw [run2_succ_some π 0 hs]; rfl

/-- 実行は歩数について分解できる。 -/
theorem run2_add (π : Rule) :
    ∀ (a b : Nat) (x : Conf2),
      run2 π (a + b) x = (run2 π a x).bind (fun y => run2 π b y) := by
  intro a
  induction a with
  | zero => intro b x; rw [Nat.zero_add]; rfl
  | succ a ih =>
    intro b x
    have h : a + 1 + b = (a + b) + 1 := by omega
    rw [h]
    cases hs : step2 π x with
    | none => rw [run2_succ_none π (a + b) hs, run2_succ_none π a hs]; rfl
    | some x' => rw [run2_succ_some π (a + b) hs, run2_succ_some π a hs, ih b x']

/-- 右から 1 歩はがす形。 -/
theorem run2_succ_right (π : Rule) (n : Nat) (c : Conf2) :
    run2 π (n + 1) c = (run2 π n c).bind (step2 π) := by
  rw [run2_add π n 1 c]
  cases h : run2 π n c with
  | none => rfl
  | some y => show run2 π 1 y = step2 π y; exact run2_one π y

/-! ## 3. 可逆なら軌道は ρ 形にならない -/

/-- **設定が一度でも繰り返せば、出発点に戻る。**
    すなわち可逆な機械の軌道は「しっぽ＋輪」（ρ 形）にならず、純粋な周期になる。 -/
theorem run2_no_rho (π : Rule) (hrev : Rev π) :
    ∀ (i m : Nat) (c x : Conf2),
      run2 π i c = some x → run2 π (i + m) c = some x →
      run2 π m c = some c := by
  intro i
  induction i with
  | zero =>
    intro m c x h₁ h₂
    have hx : c = x := Option.some.inj h₁
    rw [Nat.zero_add] at h₂
    rw [← hx] at h₂
    exact h₂
  | succ i ih =>
    intro m c x h₁ h₂
    -- 右から 1 歩はがす
    rw [run2_succ_right π i c] at h₁
    have h₂' : run2 π ((i + m) + 1) c = some x := by
      have : i + 1 + m = i + m + 1 := by omega
      rw [← this]; exact h₂
    rw [run2_succ_right π (i + m) c] at h₂'
    -- run2 i c と run2 (i+m) c は、どちらも 1 歩後に x になる
    cases hy : run2 π i c with
    | none => rw [hy] at h₁; exact absurd h₁ (by simp)
    | some y =>
      cases hz : run2 π (i + m) c with
      | none => rw [hz] at h₂'; exact absurd h₂' (by simp)
      | some z =>
        rw [hy] at h₁
        rw [hz] at h₂'
        have hstep₁ : step2 π y = some x := h₁
        have hstep₂ : step2 π z = some x := h₂'
        have : y = z := step2_injective π hrev hstep₁ hstep₂
        exact ih m c y hy (by rw [hz, this])

/-- **戻ってきたら永久に繰り返す**: `run2 π m c = some c` なら、どの倍数でも同じ設定に戻る。 -/
theorem run2_periodic (π : Rule) :
    ∀ (q m : Nat) (c : Conf2), run2 π m c = some c → run2 π (m * q) c = some c := by
  intro q
  induction q with
  | zero => intro m c _; rw [Nat.mul_zero]; rfl
  | succ q ih =>
    intro m c h
    rw [Nat.mul_succ, run2_add π (m * q) m c, ih m c h]
    exact h

end URTM.TwoState
