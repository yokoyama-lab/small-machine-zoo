/-
  3 状態 2 記号 RTM の停止問題の決定可能性 その 3: **局所性と並進周期**（単調性を仮定しない版）。**手書き**。

  `TSDMono` の `qrun_local`・`qescape` は右単調な表を仮定していた。ここではその仮定を外し、
  代わりに「実行のあいだヘッドが k 以上に居続ける」ことを仮定する。
    * `qrun_agreeG` : 状態・位置が同じで [k, ∞) の中身が一致する 2 つの配置は、
      一方のヘッドが k 以上に居るあいだ、同じように動く
    * `qescapeG` : Δ ≥ 1 歩で状態が同じ・δ ≥ 0 だけ右・[L₀+δ, ∞) の中身がずれて一致する配置へ着き、
      そのあいだヘッドが L₀ 以上なら、以後ずっと止まらず、ヘッドは L₀ 以上に居る
-/
import URTM.TSDFinal

namespace URTM.TwoState

/-- 状態・位置が同じで、[k, ∞) の中身が一致する。 -/
def AgreeG (k : Int) (c₁ c₂ : QConf) : Prop :=
  c₁.st = c₂.st ∧ c₁.pos = c₂.pos ∧ ∀ x, k ≤ x → c₁.tape x = c₂.tape x

theorem qstep_agreeG {tbl : List Quint} {k : Int} {c₁ c₂ : QConf} (H : AgreeG k c₁ c₂)
    (hk : k ≤ c₁.pos) :
    (qstep tbl c₁ = none ∧ qstep tbl c₂ = none) ∨
    ∃ d₁ d₂, qstep tbl c₁ = some d₁ ∧ qstep tbl c₂ = some d₂ ∧ AgreeG k d₁ d₂ := by
  obtain ⟨hs, hp, ht⟩ := H
  have hread : c₂.tape c₂.pos = c₁.tape c₁.pos := by rw [← hp]; exact (ht _ hk).symm
  unfold qstep
  rw [hread, ← hs]
  cases hf : find? tbl c₁.st (c₁.tape c₁.pos) with
  | none => left; exact ⟨rfl, rfl⟩
  | some r =>
    right
    refine ⟨_, _, rfl, rfl, rfl, by rw [hp], ?_⟩
    intro x hx
    show write c₁.tape c₁.pos r.t x = write c₂.tape c₂.pos r.t x
    unfold write; rw [← hp]
    by_cases he : x = c₁.pos
    · simp [he]
    · simp [he, ht x hx]

/-- 一方（c₁）の実行でヘッドが k 以上に居続けるあいだ、2 つの実行は同じように進む。 -/
theorem qrun_agreeG {tbl : List Quint} {k : Int} :
    ∀ (n : Nat) (c₁ c₂ : QConf), AgreeG k c₁ c₂ →
      (∀ t, t < n → ∀ d, qrun tbl t c₁ = some d → k ≤ d.pos) →
      (qrun tbl n c₁ = none ∧ qrun tbl n c₂ = none) ∨
      ∃ d₁ d₂, qrun tbl n c₁ = some d₁ ∧ qrun tbl n c₂ = some d₂ ∧ AgreeG k d₁ d₂ := by
  intro n
  induction n with
  | zero => intro c₁ c₂ H _; exact Or.inr ⟨c₁, c₂, rfl, rfl, H⟩
  | succ n ih =>
    intro c₁ c₂ H hpos
    have hk : k ≤ c₁.pos := hpos 0 (by omega) c₁ rfl
    rcases qstep_agreeG (tbl := tbl) H hk with ⟨e1, e2⟩ | ⟨d₁, d₂, e1, e2, H'⟩
    · left; exact ⟨qrun_succ_none tbl n e1, qrun_succ_none tbl n e2⟩
    · rw [qrun_succ_some tbl n e1, qrun_succ_some tbl n e2]
      refine ih d₁ d₂ H' fun t ht d hd => hpos (t + 1) (by omega) d ?_
      rw [qrun_succ_some tbl t e1]; exact hd

theorem AgreeG.symm {k : Int} {c₁ c₂ : QConf} (H : AgreeG k c₁ c₂) : AgreeG k c₂ c₁ :=
  ⟨H.1.symm, H.2.1.symm, fun x hx => (H.2.2 x hx).symm⟩

theorem AgreeG.mono {k k' : Int} {c₁ c₂ : QConf} (H : AgreeG k c₁ c₂) (h : k ≤ k') :
    AgreeG k' c₁ c₂ :=
  ⟨H.1, H.2.1, fun x hx => H.2.2 x (by omega)⟩

theorem qrun_shift_pos {tbl : List Quint} {c : QConf} {δ : Int} {t : Nat} {d : QConf}
    (h : qrun tbl t (shiftQ c δ) = some d) : ∃ e, qrun tbl t c = some e ∧ d = shiftQ e δ := by
  rw [qrun_shift] at h
  cases he : qrun tbl t c with
  | none => rw [he] at h; exact absurd h (by simp)
  | some e => rw [he] at h; exact ⟨e, rfl, (Option.some.inj h).symm⟩

/-- **単調性を仮定しない自己相似の逃走**。 -/
theorem qescapeG {tbl : List Quint} (c c' : QConf) (Δ : Nat) (δ L₀ : Int)
    (hΔ : 1 ≤ Δ) (hδ : 0 ≤ δ) (hrun : qrun tbl Δ c = some c')
    (hposr : ∀ t, t < Δ → ∀ d, qrun tbl t c = some d → L₀ ≤ d.pos)
    (hst : c'.st = c.st) (hpos : c'.pos = c.pos + δ)
    (htape : ∀ x, L₀ + δ ≤ x → c'.tape x = c.tape (x - δ)) :
    ∀ n, (∃ d, qrun tbl n c = some d ∧ L₀ ≤ d.pos) := by
  have hc0 : L₀ ≤ c.pos := hposr 0 hΔ c rfl
  -- 周期 j 回の後の配置は shiftQ c (jδ) と [L₀ + jδ, ∞) で一致する
  have iter : ∀ j : Nat, ∃ cj, qrun tbl (j * Δ) c = some cj ∧
      AgreeG (L₀ + j * δ) (shiftQ c (j * δ)) cj := by
    intro j
    induction j with
    | zero =>
      refine ⟨c, by rw [Nat.zero_mul]; rfl, ?_, ?_, ?_⟩
      · rfl
      · show c.pos + ((0 : Nat) : Int) * δ = c.pos; simp
      · intro x _; show c.tape (x - ((0 : Nat) : Int) * δ) = c.tape x; simp
    | succ j ih =>
      obtain ⟨cj, hcj, hag⟩ := ih
      have hsh : qrun tbl Δ (shiftQ c (j * δ)) = some (shiftQ c' (j * δ)) := by
        rw [qrun_shift, hrun]; rfl
      have hposS : ∀ t, t < Δ → ∀ d, qrun tbl t (shiftQ c (j * δ)) = some d →
          L₀ + j * δ ≤ d.pos := by
        intro t ht d hd
        obtain ⟨e, he, rfl⟩ := qrun_shift_pos hd
        have := hposr t ht e he
        show L₀ + j * δ ≤ e.pos + j * δ; omega
      rcases qrun_agreeG Δ _ _ hag hposS with ⟨h1, _⟩ | ⟨d₁, d₂, h1, h2, hag2⟩
      · rw [hsh] at h1; exact absurd h1 (by simp)
      · rw [hsh] at h1
        have e := (Option.some.inj h1)
        subst e
        refine ⟨d₂, by rw [Nat.succ_mul, qrun_add, hcj]; exact h2, ?_, ?_, ?_⟩
        · rw [← hag2.1]; exact hst.symm
        · rw [← hag2.2.1]; show c.pos + ((j + 1 : Nat) : Int) * δ = c'.pos + j * δ
          rw [hpos]; push_cast; rw [Int.add_mul]; omega
        · intro x hx
          have hjδ : 0 ≤ (j : Int) * δ := Int.mul_nonneg (by omega) hδ
          have hx' : L₀ + (j : Int) * δ ≤ x := by
            push_cast at hx; rw [Int.add_mul] at hx; omega
          rw [← hag2.2.2 x hx']
          show c.tape (x - ((j + 1 : Nat) : Int) * δ) = c'.tape (x - j * δ)
          rw [htape (x - j * δ) (by push_cast at hx; rw [Int.add_mul] at hx; omega)]
          congr 1; push_cast; rw [Int.add_mul]; omega
  intro n
  -- n = j·Δ + r (r < Δ)
  obtain ⟨j, r, hr, hn⟩ : ∃ j r, r < Δ ∧ n = j * Δ + r :=
    ⟨n / Δ, n % Δ, Nat.mod_lt _ (by omega), by
      have := Nat.div_add_mod n Δ; rw [Nat.mul_comm] at this; omega⟩
  subst hn
  obtain ⟨cj, hcj, hag⟩ := iter j
  have hjδ : 0 ≤ (j : Int) * δ := Int.mul_nonneg (by omega) hδ
  have hposS : ∀ t, t < r → ∀ d, qrun tbl t (shiftQ c (j * δ)) = some d →
      L₀ + j * δ ≤ d.pos := by
    intro t ht d hd
    obtain ⟨e, he, rfl⟩ := qrun_shift_pos hd
    have := hposr t (by omega) e he
    show L₀ + j * δ ≤ e.pos + j * δ; omega
  -- 残りの r 歩: shiftQ の側は止まらない（Δ 歩で c' に着く実行の途中）
  have halive : ∃ e, qrun tbl r c = some e ∧ L₀ ≤ e.pos := by
    have hsplit : qrun tbl Δ c = (qrun tbl r c).bind (qrun tbl (Δ - r)) := by
      rw [← qrun_add, show r + (Δ - r) = Δ by omega]
    cases he : qrun tbl r c with
    | none => rw [he] at hsplit; rw [hrun] at hsplit; exact absurd hsplit (by simp)
    | some e => exact ⟨e, rfl, hposr r hr e he⟩
  obtain ⟨e, he, hepos⟩ := halive
  have hshr : qrun tbl r (shiftQ c (j * δ)) = some (shiftQ e (j * δ)) := by
    rw [qrun_shift, he]; rfl
  rcases qrun_agreeG r _ _ hag hposS with ⟨h1, _⟩ | ⟨d₁, d₂, h1, h2, hag2⟩
  · rw [hshr] at h1; exact absurd h1 (by simp)
  · rw [hshr] at h1
    have e1 := Option.some.inj h1
    subst e1
    refine ⟨d₂, by rw [qrun_add, hcj]; exact h2, ?_⟩
    rw [← hag2.2.1]
    show L₀ ≤ e.pos + j * δ; omega

end URTM.TwoState
