/-
  2 状態 RTM の停止問題の決定可能性 その 2: 半直線の滞在と自己相似の逃走。**手書き**。

    * `Soj`     : 半直線 [k,∞) の中の 1 回の滞在（n 歩で初めて k 未満へ出る）
    * `Chain`   : 空白から始めて j 回の滞在を終えたあとの中身（関係として）
    * `Chain_func` / `Chain_shift` : 関数的（[k,∞) の上で一意）で、平行移動と可換
    * `selfsim_never_halts` : **自己相似の逃走補題**。位置 k・向き R の配置から
      k 以上に留まったまま Δ ≥ 1 歩で位置 k+1・向き R に着き、そのとき [k+1,∞) の中身が
      出発時の [k,∞) の中身を 1 つ右へずらしたものなら、**実行は停止しない**。
      （docs/10 §5.1 の「入れ子逃走」。穴 C-1c-i の `¬ HaltsInside` 側に当たる）
-/
import URTM.TSDTraj

namespace URTM.TwoState

/-! ## 平行移動と実行 -/

theorem run2_shift (π : Rule) :
    ∀ (n : Nat) (c : Conf2) (δ : Int),
      run2 π n (shiftC c δ) = (run2 π n c).map (fun x => shiftC x δ) := by
  intro n
  induction n with
  | zero => intro c δ; rfl
  | succ n ih =>
    intro c δ
    cases hs : step2 π c with
    | none =>
      have hs' : step2 π (shiftC c δ) = none := by rw [step2_shift, hs]; rfl
      rw [run2_succ_none π n hs', run2_succ_none π n hs]; rfl
    | some c' =>
      have hs' : step2 π (shiftC c δ) = some (shiftC c' δ) := by rw [step2_shift, hs]; rfl
      rw [run2_succ_some π n hs', run2_succ_some π n hs, ih]

theorem shiftT_zero (t : Int → Nat) : shiftT t 0 = t := by
  funext x; simp [shiftT]

theorem AgreeFrom.symm {k : Int} {c₁ c₂ : Conf2} (h : AgreeFrom k c₁ c₂) : AgreeFrom k c₂ c₁ :=
  ⟨fun i hi => (h.1 i hi).symm, h.2.1.symm, h.2.2.symm⟩

/-! ## 自己相似の逃走補題 -/

theorem selfsim_iter (π : Rule) (c c' : Conf2) (Δ : Nat)
    (hrun : run2 π Δ c = some c')
    (hstay : ∀ j, j < Δ → ∀ cj, run2 π j c = some cj → c.pos ≤ cj.pos)
    (hpos : c'.pos = c.pos + 1) (hdir : c'.dir = c.dir)
    (htape : ∀ x, c.pos + 1 ≤ x → c'.tape x = c.tape (x - 1)) :
    ∀ (j : Nat), ∃ cj, run2 π (j * Δ) c = some cj ∧
      AgreeFrom (c.pos + j) cj (shiftC c j) := by
  intro j
  induction j with
  | zero =>
    refine ⟨c, by simp [run2_zero], ?_⟩
    refine ⟨fun i _ => ?_, by simp [shiftC], rfl⟩
    show c.tape i = shiftT c.tape ((0 : Nat) : Int) i
    simp [shiftT]
  | succ j ih =>
    obtain ⟨cj, hcj, hag⟩ := ih
    -- ずらした配置から Δ 歩: ずらした c' に着く
    have hsh : run2 π Δ (shiftC c j) = some (shiftC c' j) := by
      rw [run2_shift, hrun]; rfl
    have hstay' : ∀ i, i < Δ → ∀ ci, run2 π i (shiftC c j) = some ci →
        c.pos + j ≤ ci.pos := by
      intro i hi ci hci
      rw [run2_shift] at hci
      cases hr : run2 π i c with
      | none => rw [hr] at hci; exact absurd hci (by simp)
      | some x =>
        rw [hr] at hci
        have hx := hstay i hi x hr
        have : ci = shiftC x j := (Option.some.inj hci).symm
        rw [this]; show c.pos + j ≤ x.pos + j; omega
    rcases run_local_right π Δ (shiftC c j) cj hag.symm hstay' with ⟨h1, _⟩ | ⟨d₁, d₂, h1, h2, hag2⟩
    · rw [hsh] at h1; exact absurd h1 (by simp)
    · rw [hsh] at h1
      have hd1 : d₁ = shiftC c' j := (Option.some.inj h1).symm
      subst hd1
      refine ⟨d₂, ?_, ?_⟩
      · have e : (j + 1) * Δ = j * Δ + Δ := by rw [Nat.succ_mul]
        rw [e, run2_add, hcj]; exact h2
      · refine ⟨fun x hx => ?_, ?_, ?_⟩
        · have h3 := hag2.1 x (by push_cast at hx ⊢; omega)
          rw [← h3]
          show c'.tape (x - j) = c.tape (x - ((j + 1 : Nat) : Int))
          rw [htape (x - j) (by push_cast at hx; omega)]
          congr 1; push_cast; omega
        · rw [← hag2.2.1]; show c'.pos + j = c.pos + ((j + 1 : Nat) : Int)
          rw [hpos]; push_cast; omega
        · rw [← hag2.2.2]; show c'.dir = c.dir; exact hdir

/-- **自己相似の逃走補題**。 -/
theorem selfsim_never_halts (π : Rule) (c c' : Conf2) (Δ : Nat) (hΔ : 1 ≤ Δ)
    (hrun : run2 π Δ c = some c')
    (hstay : ∀ j, j < Δ → ∀ cj, run2 π j c = some cj → c.pos ≤ cj.pos)
    (hpos : c'.pos = c.pos + 1) (hdir : c'.dir = c.dir)
    (htape : ∀ x, c.pos + 1 ≤ x → c'.tape x = c.tape (x - 1)) :
    ∀ n, run2 π n c ≠ none := by
  intro n hn
  obtain ⟨cj, hcj, _⟩ := selfsim_iter π c c' Δ hrun hstay hpos hdir htape n
  have hle : n ≤ n * Δ := by
    have := Nat.mul_le_mul_left n hΔ; simpa using this
  rw [run2_none_mono π c n (n * Δ) hn hle] at hcj
  exact absurd hcj (by simp)

/-! ## 滞在 -/

/-- 半直線 [k,∞) の中の滞在: n 歩で初めて k 未満へ出て、着いた配置は c'。 -/
def Soj (π : Rule) (k : Int) (c : Conf2) (n : Nat) (c' : Conf2) : Prop :=
  run2 π n c = some c' ∧ c'.pos < k ∧
    ∀ j, j < n → ∀ cj, run2 π j c = some cj → k ≤ cj.pos

theorem Soj_local (π : Rule) {k : Int} {c d : Conf2} {n : Nat} {c' : Conf2}
    (hag : AgreeFrom k c d) (h : Soj π k c n c') :
    ∃ d', Soj π k d n d' ∧ AgreeFrom k c' d' := by
  obtain ⟨h1, h2, h3⟩ := h
  rcases run_local_right π n c d hag h3 with ⟨e1, _⟩ | ⟨c₁, d₁, e1, e2, hag1⟩
  · rw [h1] at e1; exact absurd e1 (by simp)
  · rw [h1] at e1
    have hc : c₁ = c' := (Option.some.inj e1).symm
    subst hc
    refine ⟨d₁, ⟨e2, by rw [← hag1.2.1]; exact h2, ?_⟩, hag1⟩
    intro j hj dj hdj
    have h3' : ∀ i, i < j → ∀ ci, run2 π i c = some ci → k ≤ ci.pos :=
      fun i hi ci hci => h3 i (by omega) ci hci
    rcases run_local_right π j c d hag h3' with ⟨f1, f2⟩ | ⟨cj, dj', f1, f2, hag2⟩
    · rw [hdj] at f2; exact absurd f2 (by simp)
    · rw [hdj] at f2
      have : dj' = dj := (Option.some.inj f2).symm
      subst this
      rw [← hag2.2.1]
      exact h3 j hj cj f1

theorem Soj_unique (π : Rule) {k : Int} {c : Conf2} {n m : Nat} {c₁ c₂ : Conf2}
    (h₁ : Soj π k c n c₁) (h₂ : Soj π k c m c₂) : n = m ∧ c₁ = c₂ := by
  obtain ⟨a1, a2, a3⟩ := h₁
  obtain ⟨b1, b2, b3⟩ := h₂
  have hnm : n = m := by
    rcases Nat.lt_trichotomy n m with h | h | h
    · have := b3 n h c₁ a1; omega
    · exact h
    · have := a3 m h c₂ b1; omega
  subst hnm
  rw [a1] at b1
  exact ⟨rfl, Option.some.inj b1⟩

theorem Soj_shift (π : Rule) {k : Int} {c : Conf2} {n : Nat} {c' : Conf2} (δ : Int)
    (h : Soj π k c n c') : Soj π (k + δ) (shiftC c δ) n (shiftC c' δ) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by rw [run2_shift, h1]; rfl, by show c'.pos + δ < k + δ; omega, ?_⟩
  intro j hj cj hcj
  rw [run2_shift] at hcj
  cases hr : run2 π j c with
  | none => rw [hr] at hcj; exact absurd hcj (by simp)
  | some x =>
    rw [hr] at hcj
    have := h3 j hj x hr
    have e : cj = shiftC x δ := (Option.some.inj hcj).symm
    rw [e]; show k + δ ≤ x.pos + δ; omega

/-! ## 滞在の連鎖（空白半直線の入場時の中身） -/

/-- 半直線 [k,∞) の中身が u から始まり、j 回の滞在（入場 → 退場。入場時は位置 k・向き R）を
    終えたときの中身が u'（[k,∞) の上で）。 -/
def Chain (π : Rule) (k : Int) : Nat → (Int → Nat) → (Int → Nat) → Prop
  | 0, u, u' => ∀ x, k ≤ x → u' x = u x
  | j + 1, u, u' => ∃ w n c', Chain π k j u w ∧ Soj π k ⟨w, k, Dir.R⟩ n c' ∧
      ∀ x, k ≤ x → u' x = c'.tape x

theorem Chain_congr (π : Rule) (k : Int) :
    ∀ (j : Nat) (u X Y : Int → Nat), Chain π k j u X → (∀ x, k ≤ x → Y x = X x) →
      Chain π k j u Y := by
  intro j
  cases j with
  | zero => intro u X Y h hY x hx; rw [hY x hx]; exact h x hx
  | succ j =>
    intro u X Y h hY
    obtain ⟨w, n, c', h1, h2, h3⟩ := h
    exact ⟨w, n, c', h1, h2, fun x hx => by rw [hY x hx]; exact h3 x hx⟩

theorem Chain_func (π : Rule) (k : Int) :
    ∀ (j : Nat) (u X Y : Int → Nat), Chain π k j u X → Chain π k j u Y →
      ∀ x, k ≤ x → X x = Y x := by
  intro j
  induction j with
  | zero => intro u X Y hX hY x hx; rw [hX x hx, hY x hx]
  | succ j ih =>
    intro u X Y hX hY x hx
    obtain ⟨w₁, n₁, c₁, h11, h12, h13⟩ := hX
    obtain ⟨w₂, n₂, c₂, h21, h22, h23⟩ := hY
    have hw := ih u w₁ w₂ h11 h21
    have hag : AgreeFrom k ⟨w₁, k, Dir.R⟩ ⟨w₂, k, Dir.R⟩ := ⟨hw, rfl, rfl⟩
    obtain ⟨d', hd1, hd2⟩ := Soj_local π hag h12
    obtain ⟨_, he⟩ := Soj_unique π hd1 h22
    subst he
    rw [h13 x hx, h23 x hx]
    exact hd2.1 x hx

theorem Chain_shift (π : Rule) (k δ : Int) :
    ∀ (j : Nat) (u X : Int → Nat), Chain π k j u X →
      Chain π (k + δ) j (shiftT u δ) (shiftT X δ) := by
  intro j
  induction j with
  | zero =>
    intro u X h x hx
    show X (x - δ) = u (x - δ)
    exact h (x - δ) (by omega)
  | succ j ih =>
    intro u X h
    obtain ⟨w, n, c', h1, h2, h3⟩ := h
    refine ⟨shiftT w δ, n, shiftC c' δ, ih u w h1, ?_, ?_⟩
    · have := Soj_shift π δ h2
      exact this
    · intro x hx
      show X (x - δ) = c'.tape (x - δ)
      exact h3 (x - δ) (by omega)

end URTM.TwoState
