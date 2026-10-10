/-
  **入れ子補題**（C-1c の核）。**手書き**。キュー R13。

  補題 C の m ≥ 2 は「**添字 m の副入場が起きたら発散**」に帰着する。その証明は:

    子（境界 k+1 の滞在）は親（境界 k の滞在）に**真に含まれる**ので**厳密に短い**。
    ところが自己相似性（平行移動不変性）は「子と親は同じ長さ」と言う。矛盾。

  ここではその前半 — **境界を 1 つ内側へずらすと滞在は厳密に早く終わる** — を証明する。

    `excursion_boundary_lt` :
        k + 1 ≤ c.pos かつ 境界 k の滞在が S 歩で退場するなら、
        境界 k+1 の滞在は S' < S 歩で退場する。

  証明の要: 境界 k から出る（pos < k）ためには、その 1 歩前に **pos = k** でなければならない
  （1 歩の移動は −1/0/+1 なので、k 以上から k 未満へ落ちるには pos = k から −1 するしかない）。
  その時点で境界 k+1 の滞在はすでに終わっている。

  後半（自己相似性との矛盾）は `excursion_shift`（`TwoStateOutcome.lean`）と
  組み合わせて使う。**0 シフト規則の有無に依らない**（Z があっても k をまたげない）。
-/
import URTM.TwoStateBlank

namespace URTM.TwoState

/-! ## 1. 退場の歩数は 1 以上 -/

theorem excursion_left_pos (π : Rule) (k : Int) :
    ∀ (n : Nat) {c d : Conf2} {s : Nat},
      excursion π k n c = Sojourn.left s d → 1 ≤ s := by
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
        injection h with hsv _
        omega
      · cases h2 : excursion π k n c' with
        | left s₂ d₂ =>
          rw [excursion_stay_left π k n hs hlt h2] at h
          injection h with hsv _
          rw [← hsv]
          omega
        | halted s₂ d₂ =>
          rw [excursion_stay_halted π k n hs hlt h2] at h; exact absurd h (by simp)
        | timeout =>
          rw [excursion_stay_timeout π k n hs hlt h2] at h; exact absurd h (by simp)

/-! ## 2. 1 歩の移動幅 -/

/-- 1 歩の移動は高々 1（−1 / 0 / +1）。 -/
theorem step2_pos_ge (π : Rule) {c c' : Conf2} (h : step2 π c = some c') :
    c.pos - 1 ≤ c'.pos := by
  obtain ⟨v, d', _, _, hp, _⟩ := step2_some π h
  cases hd : d' with
  | L => rw [hd, move_L] at hp; omega
  | Z => rw [hd, move_Z] at hp; omega
  | R => rw [hd, move_R] at hp; omega

/-! ## 3. 入れ子補題 -/

/-- **入れ子補題**: 境界を 1 つ内側（k → k+1）へずらすと、滞在は**厳密に早く**終わる。

    ヘッドが k+1 以上から出発して境界 k を越えて退場するなら、
    その途中で必ず pos = k を通る。その時点で境界 k+1 の滞在は終わっている。 -/
theorem excursion_boundary_lt (π : Rule) (k : Int) :
    ∀ (n : Nat) {c d : Conf2} {s : Nat},
      k + 1 ≤ c.pos → excursion π k n c = Sojourn.left s d →
      ∃ s' d', s' < s ∧ excursion π (k + 1) n c = Sojourn.left s' d' := by
  intro n
  induction n with
  | zero => intro c d s _ h; rw [excursion_zero] at h; exact absurd h (by simp)
  | succ n ih =>
    intro c d s hk h
    cases hs : step2 π c with
    | none => rw [excursion_halt π k n hs] at h; exact absurd h (by simp)
    | some c' =>
      -- 1 歩では k 未満へ落ちられない（k+1 以上に居るので）
      have hge : k ≤ c'.pos := by
        have := step2_pos_ge π hs
        omega
      have hlt : ¬ c'.pos < k := by omega
      cases h2 : excursion π k n c' with
      | left s₂ d₂ =>
        rw [excursion_stay_left π k n hs hlt h2] at h
        injection h with hsv hdv
        have hs₂ : 1 ≤ s₂ := excursion_left_pos π k n h2
        by_cases hb : c'.pos < k + 1
        · -- ちょうど pos = k。境界 k+1 の滞在はここで終わる
          refine ⟨1, c', ?_, excursion_exit π (k + 1) n hs hb⟩
          rw [← hsv]
          omega
        · -- まだ k+1 以上。帰納法
          have hk' : k + 1 ≤ c'.pos := by omega
          obtain ⟨s', d', hlt', h'⟩ := ih hk' h2
          refine ⟨s' + 1, d', ?_, excursion_stay_left π (k + 1) n hs hb h'⟩
          rw [← hsv]
          omega
      | halted s₂ d₂ =>
        rw [excursion_stay_halted π k n hs hlt h2] at h; exact absurd h (by simp)
      | timeout =>
        rw [excursion_stay_timeout π k n hs hlt h2] at h; exact absurd h (by simp)

/-! ## 4. 自己相似性との矛盾（発散の判定） -/

/-- **発散の判定**: 配置 c が「1 つ右へずらした自分自身」と
    境界 k+1 の上で一致しているなら、境界 k の滞在は**退場しない**。

    直観: 子（境界 k+1 の滞在）は親（境界 k の滞在）より厳密に短い（入れ子補題）。
    ところが自己相似性は「子と親は同じ長さ」と言う。矛盾。 -/
theorem no_exit_of_self_similar (π : Rule) (k : Int) (c : Conf2)
    (hk : k + 1 ≤ c.pos)
    (hsim : AgreeFrom (k + 1) c (shiftC c 1)) :
    ¬ Exits π k c := by
  rintro ⟨n, s, d, hn⟩
  -- 子は厳密に短い
  obtain ⟨s', d', hlt, h'⟩ := excursion_boundary_lt π k n hk hn
  -- 自己相似性: 境界 k+1 での c の滞在は、境界 k での c の滞在の平行移動
  have hshift : excursion π (k + 1) n (shiftC c 1) = shiftS (excursion π k n c) 1 := by
    have := excursion_shift π k 1 n c
    exact this
  rw [hn] at hshift
  -- 境界 k+1 では c と shiftC c 1 が一致するので、滞在も一致
  have hk1 : k + 1 ≤ c.pos := hk
  have hloc := excursion_local π (k + 1) n hk1 hsim
  rw [h', hshift] at hloc
  -- hloc : SojournAgree (k+1) (left s' d') (left s (shiftC d 1))
  have : s' = s := hloc.1
  omega

end URTM.TwoState
