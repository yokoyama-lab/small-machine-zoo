/-
  2 状態 RTM の停止問題の決定可能性（docs/10 の穴の充填）その 1: 実行の軌道。**手書き**。

  停止する実行を時刻の列 `tr π c t`（t ≤ T）として扱う土台。
    * `HaltRun π c T` : 実行は時刻 T まで生きていて、T で停止する
    * `halts_iff`     : `Halts`（ある n で `run2` が `none`）と `HaltRun` の関係
    * 1 歩の性質（0 シフトなしなら位置は ±1、書き換えはヘッドの位置だけ）
    * 境界 k をまたぐ回数 `Ent k t`、最初・最後の時刻の補題、凍結補題
-/
import URTM.TwoStateRev
import URTM.TwoStateOutcome

namespace URTM.TwoState

/-- 0 シフト規則が無い（構造定理 `no_zero_shift_of_two_states` の結論の形）。 -/
def NoZ (π : Rule) : Prop := ∀ d s v d', π d s = some (v, d') → d' ≠ Dir.Z

/-- 停止する（ある歩数で実行が `none` になる）。 -/
def Halts (π : Rule) (c : Conf2) : Prop := ∃ n, run2 π n c = none

theorem run2_zero (π : Rule) (c : Conf2) : run2 π 0 c = some c := rfl

theorem run2_none_mono (π : Rule) (c : Conf2) (n m : Nat)
    (h : run2 π n c = none) (hnm : n ≤ m) : run2 π m c = none := by
  have e : m = n + (m - n) := by omega
  rw [e, run2_add, h]
  rfl

/-- 軌道。停止後は意味を持たない（`getD` の既定値）。 -/
def tr (π : Rule) (c : Conf2) (t : Nat) : Conf2 := (run2 π t c).getD c

/-- 時刻 T まで生きていて、T で停止する実行。 -/
structure HaltRun (π : Rule) (c : Conf2) (T : Nat) : Prop where
  alive : run2 π T c ≠ none
  dead : run2 π (T + 1) c = none

theorem first_none (π : Rule) (c : Conf2) :
    ∀ n, run2 π n c = none → ∃ T, run2 π T c ≠ none ∧ run2 π (T + 1) c = none := by
  intro n
  induction n with
  | zero => intro h; rw [run2_zero] at h; exact absurd h (by simp)
  | succ n ih =>
    intro h
    by_cases hn : run2 π n c = none
    · exact ih hn
    · exact ⟨n, hn, h⟩

theorem halts_haltRun {π : Rule} {c : Conf2} (h : Halts π c) : ∃ T, HaltRun π c T := by
  obtain ⟨n, hn⟩ := h
  obtain ⟨T, h1, h2⟩ := first_none π c n hn
  exact ⟨T, ⟨h1, h2⟩⟩

theorem haltRun_halts {π : Rule} {c : Conf2} {T : Nat} (h : HaltRun π c T) : Halts π c :=
  ⟨T + 1, h.dead⟩

section Run
variable {π : Rule} {c : Conf2} {T : Nat}

theorem HaltRun.run (hR : HaltRun π c T) (t : Nat) (ht : t ≤ T) :
    run2 π t c = some (tr π c t) := by
  cases h : run2 π t c with
  | none => exact absurd (run2_none_mono π c t T h ht) hR.alive
  | some x => simp [tr, h]

theorem HaltRun.step (hR : HaltRun π c T) (t : Nat) (ht : t < T) :
    step2 π (tr π c t) = some (tr π c (t + 1)) := by
  have h1 := hR.run (t + 1) (by omega)
  rw [run2_succ_right, hR.run t (by omega)] at h1
  exact h1

theorem HaltRun.halt (hR : HaltRun π c T) : step2 π (tr π c T) = none := by
  have h1 := hR.dead
  rw [run2_succ_right, hR.run T (Nat.le_refl _)] at h1
  exact h1

theorem tr_zero (π : Rule) (c : Conf2) : tr π c 0 = c := rfl

/-- 時刻 t から先の実行（停止までの残り）。 -/
theorem HaltRun.run_from (hR : HaltRun π c T) (t : Nat) (ht : t ≤ T) :
    run2 π (T + 1 - t) (tr π c t) = none := by
  have h := hR.dead
  have e : T + 1 = t + (T + 1 - t) := by omega
  rw [e, run2_add, hR.run t ht] at h
  exact h

theorem HaltRun.run_mid (hR : HaltRun π c T) (t n : Nat) (h : t + n ≤ T) :
    run2 π n (tr π c t) = some (tr π c (t + n)) := by
  have h1 := hR.run (t + n) h
  rw [run2_add, hR.run t (by omega)] at h1
  exact h1

end Run

/-! ## 1 歩の性質 -/

theorem step2_pos_dir (π : Rule) (hZ : NoZ π) {c c' : Conf2} (h : step2 π c = some c') :
    (c'.pos = c.pos + 1 ∧ c'.dir = Dir.R) ∨ (c'.pos = c.pos - 1 ∧ c'.dir = Dir.L) := by
  obtain ⟨v, d', hr, _, hp, hd⟩ := step2_some π h
  have hz := hZ _ _ _ _ hr
  cases d' with
  | L => right; exact ⟨by rw [hp]; rfl, hd⟩
  | Z => exact absurd rfl hz
  | R => left; exact ⟨by rw [hp]; rfl, hd⟩

theorem step2_tape_off (π : Rule) {c c' : Conf2} (h : step2 π c = some c') (x : Int)
    (hx : x ≠ c.pos) : c'.tape x = c.tape x := by
  obtain ⟨v, d', _, ht, _, _⟩ := step2_some π h
  rw [ht]; exact write_off c.tape c.pos v hx

section Traj
variable {π : Rule} {c : Conf2} {T : Nat}

/-- 位置の略記。 -/
abbrev P (π : Rule) (c : Conf2) (t : Nat) : Int := (tr π c t).pos

theorem HaltRun.stepMove (hZ : NoZ π) (hR : HaltRun π c T) (t : Nat) (ht : t < T) :
    (P π c (t + 1) = P π c t + 1 ∧ (tr π c (t + 1)).dir = Dir.R) ∨
    (P π c (t + 1) = P π c t - 1 ∧ (tr π c (t + 1)).dir = Dir.L) :=
  step2_pos_dir π hZ (hR.step t ht)

theorem HaltRun.move1 (hZ : NoZ π) (hR : HaltRun π c T) (t : Nat) (ht : t < T) :
    P π c (t + 1) = P π c t + 1 ∨ P π c (t + 1) = P π c t - 1 := by
  rcases hR.stepMove hZ t ht with ⟨h, _⟩ | ⟨h, _⟩
  · exact Or.inl h
  · exact Or.inr h

theorem HaltRun.tape_off (hR : HaltRun π c T) (t : Nat) (ht : t < T) (x : Int)
    (hx : x ≠ P π c t) : (tr π c (t + 1)).tape x = (tr π c t).tape x :=
  step2_tape_off π (hR.step t ht) x hx

/-- ヘッドが来ない間、そのセルは変わらない。 -/
theorem HaltRun.cell_frozen (hR : HaltRun π c T) (x : Int) :
    ∀ (t₁ n : Nat), t₁ + n ≤ T → (∀ u, t₁ ≤ u → u < t₁ + n → P π c u ≠ x) →
      (tr π c (t₁ + n)).tape x = (tr π c t₁).tape x := by
  intro t₁ n
  induction n with
  | zero => intro _ _; rfl
  | succ n ih =>
    intro h hne
    have e : t₁ + (n + 1) = (t₁ + n) + 1 := by omega
    rw [e, hR.tape_off (t₁ + n) (by omega) x (fun he => hne (t₁ + n) (by omega) (by omega) he.symm)]
    exact ih (by omega) (fun u h1 h2 => hne u h1 (by omega))

/-- 半直線 [k,∞) の凍結: ヘッドが k 未満に居る間、k 以上は変わらない。 -/
theorem HaltRun.frozen_right (hR : HaltRun π c T) (k : Int) (t₁ t₂ : Nat) (h12 : t₁ ≤ t₂)
    (h2 : t₂ ≤ T) (hlt : ∀ u, t₁ ≤ u → u < t₂ → P π c u < k) :
    ∀ x, k ≤ x → (tr π c t₂).tape x = (tr π c t₁).tape x := by
  intro x hx
  have e : t₂ = t₁ + (t₂ - t₁) := by omega
  rw [e]
  exact hR.cell_frozen x t₁ (t₂ - t₁) (by omega)
    (fun u h1 h3 he => by have := hlt u h1 (by omega); omega)

theorem HaltRun.frozen_left (hR : HaltRun π c T) (k : Int) (t₁ t₂ : Nat) (h12 : t₁ ≤ t₂)
    (h2 : t₂ ≤ T) (hgt : ∀ u, t₁ ≤ u → u < t₂ → k < P π c u) :
    ∀ x, x ≤ k → (tr π c t₂).tape x = (tr π c t₁).tape x := by
  intro x hx
  have e : t₂ = t₁ + (t₂ - t₁) := by omega
  rw [e]
  exact hR.cell_frozen x t₁ (t₂ - t₁) (by omega)
    (fun u h1 h3 he => by have := hgt u h1 (by omega); omega)

end Traj

/-! ## 最初の時刻・最後の時刻（汎用） -/

theorem exists_first (Q : Nat → Prop) [DecidablePred Q] :
    ∀ (n a : Nat), Q (a + n) →
      ∃ x, a ≤ x ∧ x ≤ a + n ∧ Q x ∧ ∀ u, a ≤ u → u < x → ¬ Q u := by
  intro n
  induction n with
  | zero => intro a h; exact ⟨a, Nat.le_refl _, by omega, by simpa using h,
      fun u h1 h2 => absurd h2 (by omega)⟩
  | succ n ih =>
    intro a h
    by_cases ha : Q a
    · exact ⟨a, Nat.le_refl _, by omega, ha, fun u h1 h2 => absurd h2 (by omega)⟩
    · have e : a + (n + 1) = (a + 1) + n := by omega
      rw [e] at h
      obtain ⟨x, h1, h2, h3, h4⟩ := ih (a + 1) h
      refine ⟨x, by omega, by omega, h3, fun u hu1 hu2 => ?_⟩
      by_cases hu : u = a
      · rw [hu]; exact ha
      · exact h4 u (by omega) hu2

theorem exists_last (Q : Nat → Prop) [DecidablePred Q] :
    ∀ (n a : Nat), Q a →
      ∃ x, a ≤ x ∧ x ≤ a + n ∧ Q x ∧ ∀ u, x < u → u ≤ a + n → ¬ Q u := by
  intro n
  induction n with
  | zero => intro a h; exact ⟨a, Nat.le_refl _, by omega, h,
      fun u h1 h2 => absurd h2 (by omega)⟩
  | succ n ih =>
    intro a h
    obtain ⟨x, h1, h2, h3, h4⟩ := ih a h
    by_cases hq : Q (a + (n + 1))
    · exact ⟨a + (n + 1), by omega, Nat.le_refl _, hq, fun u hu1 hu2 => absurd hu2 (by omega)⟩
    · refine ⟨x, h1, by omega, h3, fun u hu1 hu2 => ?_⟩
      by_cases hu : u = a + (n + 1)
      · rw [hu]; exact hq
      · exact h4 u hu1 (by omega)

/-! ## 境界をまたぐ -/

section Cross
variable {π : Rule} {c : Conf2} {T : Nat}

/-- 位置が k 未満から k 以上へ上がるなら、途中で k-1 → k の 1 歩がある。 -/
theorem HaltRun.cross_up (hZ : NoZ π) (hR : HaltRun π c T) (k : Int) (t₁ t₂ : Nat)
    (h12 : t₁ < t₂) (h2 : t₂ ≤ T) (hlo : P π c t₁ < k) (hhi : k ≤ P π c t₂) :
    ∃ s, t₁ ≤ s ∧ s < t₂ ∧ P π c s = k - 1 ∧ P π c (s + 1) = k ∧
      ∀ u, t₁ ≤ u → u ≤ s → P π c u < k := by
  have e : t₂ = t₁ + (t₂ - t₁) := by omega
  obtain ⟨x, hx1, hx2, hx3, hx4⟩ :=
    exists_first (fun u => k ≤ P π c u) (t₂ - t₁) t₁ (by rw [← e]; exact hhi)
  have hx0 : x ≠ t₁ := by intro h; rw [h] at hx3; omega
  obtain ⟨s, rfl⟩ : ∃ s, x = s + 1 := ⟨x - 1, by omega⟩
  have hs : ¬ k ≤ P π c s := hx4 s (by omega) (by omega)
  rcases hR.move1 hZ s (by omega) with h | h
  · refine ⟨s, by omega, by omega, by omega, by omega, fun u h1 h2 => ?_⟩
    have := hx4 u h1 (by omega); omega
  · omega

/-- 位置が k 以上から k 未満へ下がるなら、途中で k → k-1 の 1 歩がある。 -/
theorem HaltRun.cross_down (hZ : NoZ π) (hR : HaltRun π c T) (k : Int) (t₁ t₂ : Nat)
    (h12 : t₁ < t₂) (h2 : t₂ ≤ T) (hhi : k ≤ P π c t₁) (hlo : P π c t₂ < k) :
    ∃ s, t₁ ≤ s ∧ s < t₂ ∧ P π c s = k ∧ P π c (s + 1) = k - 1 ∧
      ∀ u, t₁ ≤ u → u ≤ s → k ≤ P π c u := by
  have e : t₂ = t₁ + (t₂ - t₁) := by omega
  obtain ⟨x, hx1, hx2, hx3, hx4⟩ :=
    exists_first (fun u => P π c u < k) (t₂ - t₁) t₁ (by rw [← e]; exact hlo)
  have hx0 : x ≠ t₁ := by intro h; rw [h] at hx3; omega
  obtain ⟨s, rfl⟩ : ∃ s, x = s + 1 := ⟨x - 1, by omega⟩
  have hs : ¬ P π c s < k := hx4 s (by omega) (by omega)
  rcases hR.move1 hZ s (by omega) with h | h
  · omega
  · refine ⟨s, by omega, by omega, by omega, by omega, fun u h1 h2 => ?_⟩
    have := hx4 u h1 (by omega); omega

/-- 入場の 1 歩: 位置 k-1 → k。 -/
def EntStep (π : Rule) (c : Conf2) (k : Int) (t : Nat) : Prop :=
  P π c t = k - 1 ∧ P π c (t + 1) = k

instance (π : Rule) (c : Conf2) (k : Int) (t : Nat) : Decidable (EntStep π c k t) := by
  unfold EntStep; infer_instance

/-- 時刻 t までの [k,∞) への入場回数。 -/
def Ent (π : Rule) (c : Conf2) (k : Int) : Nat → Nat
  | 0 => 0
  | t + 1 => Ent π c k t + if EntStep π c k t then 1 else 0

theorem Ent_succ_of (π : Rule) (c : Conf2) (k : Int) (t : Nat) (h : EntStep π c k t) :
    Ent π c k (t + 1) = Ent π c k t + 1 := by simp [Ent, h]

theorem Ent_succ_not (π : Rule) (c : Conf2) (k : Int) (t : Nat) (h : ¬ EntStep π c k t) :
    Ent π c k (t + 1) = Ent π c k t := by simp [Ent, h]

theorem Ent_succ_le (π : Rule) (c : Conf2) (k : Int) (t : Nat) :
    Ent π c k (t + 1) ≤ Ent π c k t + 1 := by
  by_cases h : EntStep π c k t
  · rw [Ent_succ_of π c k t h]; omega
  · rw [Ent_succ_not π c k t h]; omega

theorem Ent_mono (π : Rule) (c : Conf2) (k : Int) :
    ∀ (t n : Nat), Ent π c k t ≤ Ent π c k (t + n) := by
  intro t n
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    have e : t + (n + 1) = (t + n) + 1 := by omega
    rw [e]
    by_cases h : EntStep π c k (t + n)
    · rw [Ent_succ_of π c k _ h]; omega
    · rw [Ent_succ_not π c k _ h]; exact ih

theorem Ent_mono' (π : Rule) (c : Conf2) (k : Int) {t₁ t₂ : Nat} (h : t₁ ≤ t₂) :
    Ent π c k t₁ ≤ Ent π c k t₂ := by
  have e : t₂ = t₁ + (t₂ - t₁) := by omega
  rw [e]; exact Ent_mono π c k t₁ _

/-- 入場が無い区間では回数は変わらない。 -/
theorem Ent_const (π : Rule) (c : Conf2) (k : Int) :
    ∀ (t n : Nat), (∀ u, t ≤ u → u < t + n → ¬ EntStep π c k u) →
      Ent π c k (t + n) = Ent π c k t := by
  intro t n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro h
    have e : t + (n + 1) = (t + n) + 1 := by omega
    rw [e, Ent_succ_not π c k _ (h (t + n) (by omega) (by omega))]
    exact ih (fun u h1 h2 => h u h1 (by omega))

/-- 回数が増えたなら、その区間に入場の 1 歩がある。 -/
theorem Ent_grow (π : Rule) (c : Conf2) (k : Int) (t₁ t₂ : Nat) (h12 : t₁ ≤ t₂)
    (h : Ent π c k t₁ < Ent π c k t₂) : ∃ s, t₁ ≤ s ∧ s < t₂ ∧ EntStep π c k s := by
  by_cases hc : ∃ s, t₁ ≤ s ∧ s < t₂ ∧ EntStep π c k s
  · exact hc
  · have e : t₂ = t₁ + (t₂ - t₁) := by omega
    have := Ent_const π c k t₁ (t₂ - t₁)
      (fun u h1 h2 hs => hc ⟨u, h1, by omega, hs⟩)
    rw [← e] at this; omega

/-- 入場回数が同じで、はじめ k 未満なら、ずっと k 未満。 -/
theorem HaltRun.stay_below (hZ : NoZ π) (hR : HaltRun π c T) (k : Int) (t₁ t₂ : Nat)
    (h12 : t₁ ≤ t₂) (h2 : t₂ ≤ T) (hlo : P π c t₁ < k)
    (hE : Ent π c k t₂ = Ent π c k t₁) : ∀ u, t₁ ≤ u → u ≤ t₂ → P π c u < k := by
  intro u h1 h3
  by_cases hu : P π c u < k
  · exact hu
  · have hne : t₁ ≠ u := by intro h; rw [h] at hlo; exact hu hlo
    obtain ⟨s, hs1, hs2, hs3, hs4, _⟩ :=
      hR.cross_up hZ k t₁ u (by omega) (by omega) hlo (by omega)
    have hs : EntStep π c k s := ⟨hs3, hs4⟩
    have hle1 := Ent_mono' π c k (show s + 1 ≤ t₂ by omega)
    have hle2 := Ent_mono' π c k (show t₁ ≤ s by omega)
    rw [Ent_succ_of π c k s hs] at hle1
    omega

/-- 入場の直後は向き R。 -/
theorem HaltRun.entry_dir (hZ : NoZ π) (hR : HaltRun π c T) (k : Int) (s : Nat) (hs : s < T)
    (h : EntStep π c k s) : (tr π c (s + 1)).dir = Dir.R := by
  rcases hR.stepMove hZ s hs with ⟨_, hd⟩ | ⟨hp, _⟩
  · exact hd
  · have := h.1; have := h.2; omega

/-- 最後の入場: ヘッドが k 以上に居るなら、直近の入場の 1 歩 s があり、
    そこから今までずっと k 以上で、入場回数は変わっていない。 -/
theorem HaltRun.last_entry (hZ : NoZ π) (hR : HaltRun π c T) (k : Int) (t : Nat)
    (ht : t ≤ T) (h0 : P π c 0 < k) (hk : k ≤ P π c t) :
    ∃ s, s < t ∧ EntStep π c k s ∧ Ent π c k (s + 1) = Ent π c k t ∧
      ∀ u, s < u → u ≤ t → k ≤ P π c u := by
  have ht0 : 0 < t := by
    rcases Nat.eq_zero_or_pos t with h | h
    · rw [h] at hk; omega
    · exact h
  obtain ⟨s0, _, hs0, hs1, hs2, _⟩ := hR.cross_up hZ k 0 t ht0 ht h0 hk
  obtain ⟨s, hsa, hsb, hsE, hsL⟩ :=
    exists_last (fun u => EntStep π c k u) (t - 1 - s0) s0 ⟨hs1, hs2⟩
  have hst : s < t := by omega
  refine ⟨s, hst, hsE, ?_, ?_⟩
  · have e : t = (s + 1) + (t - (s + 1)) := by omega
    rw [e, Ent_const π c k (s + 1) (t - (s + 1)) (fun u h1 h2 => hsL u (by omega) (by omega))]
  · intro u hu1 hu2
    by_cases hc : k ≤ P π c u
    · exact hc
    · exfalso
      -- 一度 k 未満へ下りたなら、t までにまた入場しているはず
      have hlo : P π c u < k := by omega
      have hne : u ≠ t := by intro h; rw [h] at hlo; omega
      obtain ⟨s', hs'1, hs'2, hs'3, hs'4, _⟩ :=
        hR.cross_up hZ k u t (by omega) ht hlo hk
      exact hsL s' (by omega) (by omega) ⟨hs'3, hs'4⟩

end Cross

end URTM.TwoState
