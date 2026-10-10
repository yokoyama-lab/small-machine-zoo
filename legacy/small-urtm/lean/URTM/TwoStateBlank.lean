/-
  補題 C（空白半直線の応答列）へ向けた層。**手書き**。キュー R13（C-1）。

  ここで閉じるもの:
    * **逃走補題** `blank_escape` — 空白の右側でヘッドが「右へ動く」規則に当たり続けると、
      境界より左へは二度と出ず、停止もしない。**自己相似の再帰を使わずに証明できる。**
    * **空白半直線の 1 回目の応答の完全な決定** `blankResp1_correct` —
      `π Dir.R 0` の 3 通りだけで、退場／停止／発散が決まる。**これが補題 C の m=1 の場合**
    * **セルの有限オートマトン** `cellStep` の定義と燃料単調性
      （1 回の入場処理を「副入場を挟んだ内側ループ」として計算する。m ≥ 2 で使う）

  まだ閉じていないもの（`docs/10` §6.2.1 の C-1 の残り）:
    m ≥ 2 の応答。ここは **B′ = [k+1,∞) の j 回目の入場**を経由するので、
    平行移動不変性（`excursion_blank_shift`）と、
    「添字 m の副入場が起きたら発散」の**入れ子の歩数の議論**が要る。
-/
import URTM.TwoStateOutcome

namespace URTM.TwoState

/-! ## 1. 逃走補題 -/

/-- **逃走補題**: 位置 `c.pos` から右がすべて空白で、状態が R で、
    `π Dir.R 0 = some (t, Dir.R)`（空白を読んで右へ動く）なら、
    境界 k（≤ c.pos）より左へは決して出ず、停止もしない。

    証明: ヘッドは毎歩ちょうど 1 つ右の**まだ触っていない空白セル**へ進む。
    書き込むのは自分の居たセルだけなので、右側は空白のまま保たれる。 -/
theorem blank_escape (π : Rule) (k : Int) (t : Nat)
    (h : π Dir.R 0 = some (t, Dir.R)) :
    ∀ (n : Nat) (c : Conf2), k ≤ c.pos → c.dir = Dir.R →
      (∀ i, c.pos ≤ i → c.tape i = 0) →
      excursion π k n c = Sojourn.timeout := by
  intro n
  induction n with
  | zero => intro c _ _ _; exact excursion_zero π k c
  | succ n ih =>
    intro c hk hd hblank
    have hread : c.tape c.pos = 0 := hblank c.pos (Int.le_refl _)
    have hstep : step2 π c = some ⟨write c.tape c.pos t, c.pos + 1, Dir.R⟩ := by
      unfold step2
      rw [hd, hread, h]
      rfl
    have hlt : ¬ (⟨write c.tape c.pos t, c.pos + 1, Dir.R⟩ : Conf2).pos < k := by
      show ¬ c.pos + 1 < k
      omega
    have hblank' : ∀ i, (⟨write c.tape c.pos t, c.pos + 1, Dir.R⟩ : Conf2).pos ≤ i →
        (⟨write c.tape c.pos t, c.pos + 1, Dir.R⟩ : Conf2).tape i = 0 := by
      intro i hi
      have hi' : c.pos + 1 ≤ i := hi
      show write c.tape c.pos t i = 0
      unfold write
      have hne : ¬ i = c.pos := by omega
      simp only [hne, if_false]
      exact hblank i (by omega)
    exact excursion_stay_timeout π k n hstep hlt
      (ih ⟨write c.tape c.pos t, c.pos + 1, Dir.R⟩ (by show k ≤ c.pos + 1; omega) rfl hblank')

/-- 逃走するときは、退場もしないし中で停止もしない。 -/
theorem blank_diverges (π : Rule) (k : Int) (t : Nat)
    (h : π Dir.R 0 = some (t, Dir.R)) :
    Diverges π k ⟨blankT, k, Dir.R⟩ := by
  have hall : ∀ n, excursion π k n (⟨blankT, k, Dir.R⟩ : Conf2) = Sojourn.timeout := by
    intro n
    exact blank_escape π k t h n ⟨blankT, k, Dir.R⟩ (Int.le_refl _) rfl (fun _ _ => rfl)
  constructor
  · rintro ⟨n, s, d, hn⟩; rw [hall n] at hn; exact absurd hn (by simp)
  · rintro ⟨n, s, d, hn⟩; rw [hall n] at hn; exact absurd hn (by simp)

/-! ## 2. 空白半直線の 1 回目の応答（補題 C の m = 1） -/

/-- 空白を読んで左へ動くなら、1 歩で退場する。 -/
theorem blank_first_exit (π : Rule) (k : Int) (t : Nat)
    (h : π Dir.R 0 = some (t, Dir.L)) :
    excursion π k 1 ⟨blankT, k, Dir.R⟩
      = Sojourn.left 1 ⟨write blankT k t, k - 1, Dir.L⟩ := by
  have hd : (⟨blankT, k, Dir.R⟩ : Conf2).dir = Dir.R := rfl
  have hr : (⟨blankT, k, Dir.R⟩ : Conf2).tape (⟨blankT, k, Dir.R⟩ : Conf2).pos = 0 := rfl
  have hstep : step2 π (⟨blankT, k, Dir.R⟩ : Conf2)
      = some ⟨write blankT k t, k - 1, Dir.L⟩ := by
    unfold step2
    rw [hd, hr, h]
    rfl
  exact excursion_exit π k 0 hstep (by show k - 1 < k; omega)

/-- 空白を読んで規則が無いなら、その場で停止する。 -/
theorem blank_first_halt (π : Rule) (k : Int) (h : π Dir.R 0 = none) :
    excursion π k 1 ⟨blankT, k, Dir.R⟩ = Sojourn.halted 0 ⟨blankT, k, Dir.R⟩ := by
  have hd : (⟨blankT, k, Dir.R⟩ : Conf2).dir = Dir.R := rfl
  have hr : (⟨blankT, k, Dir.R⟩ : Conf2).tape (⟨blankT, k, Dir.R⟩ : Conf2).pos = 0 := rfl
  have hstep : step2 π (⟨blankT, k, Dir.R⟩ : Conf2) = none := by
    unfold step2
    rw [hd, hr, h]
  exact excursion_halt π k 0 hstep

/-- 半直線の応答（結末だけを見る 3 値）。 -/
inductive Resp where
  | exit
  | halt
  | diverge
  deriving DecidableEq, Repr

/-- **1 回目の応答は `π Dir.R 0` だけで決まる**（計算可能）。 -/
def blankResp1 (π : Rule) : Resp :=
  match π Dir.R 0 with
  | none => Resp.halt
  | some (_, Dir.L) => Resp.exit
  | some (_, Dir.R) => Resp.diverge
  | some (_, Dir.Z) => Resp.diverge   -- 2 状態 RTM では 0 シフトは起きない（構造定理）

/-- **補題 C の m = 1**: `blankResp1` が実際の結末と一致する。
    0 シフト規則が無いこと（構造定理から従う）だけを仮定する。 -/
theorem blankResp1_correct (π : Rule) (k : Int)
    (hZ : ∀ v, π Dir.R 0 ≠ some (v, Dir.Z)) :
    (blankResp1 π = Resp.exit ↔ Exits π k ⟨blankT, k, Dir.R⟩) ∧
    (blankResp1 π = Resp.halt ↔ HaltsInside π k ⟨blankT, k, Dir.R⟩) ∧
    (blankResp1 π = Resp.diverge ↔ Diverges π k ⟨blankT, k, Dir.R⟩) := by
  cases hr : π Dir.R 0 with
  | none =>
    have hb : blankResp1 π = Resp.halt := by unfold blankResp1; rw [hr]
    have hh : HaltsInside π k (⟨blankT, k, Dir.R⟩ : Conf2) :=
      ⟨1, 0, ⟨blankT, k, Dir.R⟩, blank_first_halt π k hr⟩
    have hne : ¬ Exits π k (⟨blankT, k, Dir.R⟩ : Conf2) :=
      fun he => not_exits_and_halts π k _ ⟨he, hh⟩
    refine ⟨⟨fun hx => absurd (hb ▸ hx) (by simp), fun hx => absurd hx hne⟩,
            ⟨fun _ => hh, fun _ => hb⟩,
            ⟨fun hx => absurd (hb ▸ hx) (by simp), fun hx => absurd hh hx.2⟩⟩
  | some vd =>
    obtain ⟨v, d⟩ := vd
    cases hd : d with
    | L =>
      have hb : blankResp1 π = Resp.exit := by unfold blankResp1; rw [hr, hd]
      have he : Exits π k (⟨blankT, k, Dir.R⟩ : Conf2) :=
        ⟨1, 1, _, blank_first_exit π k v (by rw [hr, hd])⟩
      have hnh : ¬ HaltsInside π k (⟨blankT, k, Dir.R⟩ : Conf2) :=
        fun hh => not_exits_and_halts π k _ ⟨he, hh⟩
      refine ⟨⟨fun _ => he, fun _ => hb⟩,
              ⟨fun hx => absurd (hb ▸ hx) (by simp), fun hx => absurd hx hnh⟩,
              ⟨fun hx => absurd (hb ▸ hx) (by simp), fun hx => absurd he hx.1⟩⟩
    | R =>
      have hb : blankResp1 π = Resp.diverge := by unfold blankResp1; rw [hr, hd]
      have hdv : Diverges π k (⟨blankT, k, Dir.R⟩ : Conf2) :=
        blank_diverges π k v (by rw [hr, hd])
      refine ⟨⟨fun hx => absurd (hb ▸ hx) (by simp), fun hx => absurd hx hdv.1⟩,
              ⟨fun hx => absurd (hb ▸ hx) (by simp), fun hx => absurd hx hdv.2⟩,
              ⟨fun _ => hdv, fun _ => hb⟩⟩
    | Z => exact absurd (by rw [hr, hd]) (hZ v)

/-! ## 3. セルの有限オートマトン（m ≥ 2 で使う） -/

/-- セル k の 1 回の入場処理の結末（副入場がすべて返ってくると仮定したときの挙動）。 -/
inductive CellOut where
  | exit (t : Nat) (g : Nat)   -- 記号 t を残して退場。途中で g 回の副入場
  | halt (g : Nat)             -- g 回の副入場のあと未定義規則
  | loop                       -- 副入場が無限に続く（セル単体のループ）
  deriving DecidableEq, Repr

/-- 副入場から戻ってきたあとの内側ループ。状態 L でセルの記号 t を読む。 -/
def cellLoop (π : Rule) : Nat → Nat → Nat → CellOut
  | 0, _, _ => CellOut.loop
  | n + 1, t, g =>
    match π Dir.L t with
    | none => CellOut.halt g
    | some (t', d') =>
      match d' with
      | Dir.L => CellOut.exit t' g
      | Dir.R => cellLoop π n t' (g + 1)
      | Dir.Z => CellOut.loop      -- 構造定理により 2 状態 RTM では起きない

/-- セル k の 1 回の入場処理。状態 R で記号 s を読むところから始まる。 -/
def cellStep (π : Rule) (fuel : Nat) (s : Nat) : CellOut :=
  match π Dir.R s with
  | none => CellOut.halt 0
  | some (t, d') =>
    match d' with
    | Dir.L => CellOut.exit t 0
    | Dir.R => cellLoop π fuel t 1
    | Dir.Z => CellOut.loop

theorem cellLoop_zero (π : Rule) (t g : Nat) : cellLoop π 0 t g = CellOut.loop := rfl

theorem cellLoop_halt (π : Rule) (n t g : Nat) (h : π Dir.L t = none) :
    cellLoop π (n + 1) t g = CellOut.halt g := by simp [cellLoop, h]

theorem cellLoop_exit (π : Rule) (n t g t' : Nat) (h : π Dir.L t = some (t', Dir.L)) :
    cellLoop π (n + 1) t g = CellOut.exit t' g := by simp [cellLoop, h]

theorem cellLoop_step (π : Rule) (n t g t' : Nat) (h : π Dir.L t = some (t', Dir.R)) :
    cellLoop π (n + 1) t g = cellLoop π n t' (g + 1) := by simp [cellLoop, h]

/-- 燃料の単調性（`loop` でない答えが出たら燃料を増やしても同じ）。 -/
theorem cellLoop_succ_of_ne_loop (π : Rule) :
    ∀ (n t g : Nat), cellLoop π n t g ≠ CellOut.loop →
      cellLoop π (n + 1) t g = cellLoop π n t g := by
  intro n
  induction n with
  | zero => intro t g h; exact absurd (cellLoop_zero π t g) h
  | succ n ih =>
    intro t g h
    cases hr : π Dir.L t with
    | none => rw [cellLoop_halt π n t g hr, cellLoop_halt π (n + 1) t g hr]
    | some vd =>
      obtain ⟨t', d'⟩ := vd
      cases hd : d' with
      | L =>
        rw [cellLoop_exit π n t g t' (by rw [hr, hd]),
            cellLoop_exit π (n + 1) t g t' (by rw [hr, hd])]
      | R =>
        have hne : cellLoop π n t' (g + 1) ≠ CellOut.loop := by
          intro hL
          rw [cellLoop_step π n t g t' (by rw [hr, hd]), hL] at h
          exact h rfl
        rw [cellLoop_step π n t g t' (by rw [hr, hd]),
            cellLoop_step π (n + 1) t g t' (by rw [hr, hd]), ih t' (g + 1) hne]
      | Z =>
        exfalso
        apply h
        show cellLoop π (n + 1) t g = CellOut.loop
        simp [cellLoop, hr, hd]

theorem cellLoop_mono (π : Rule) :
    ∀ (n n' t g : Nat), n ≤ n' → cellLoop π n t g ≠ CellOut.loop →
      cellLoop π n' t g = cellLoop π n t g := by
  intro n n'
  induction n' with
  | zero =>
    intro t g hle h
    have : n = 0 := Nat.le_zero.mp hle
    rw [this]
  | succ m ih =>
    intro t g hle h
    rcases Nat.lt_or_ge n (m + 1) with hlt | hge
    · have hnm : n ≤ m := Nat.lt_succ_iff.mp hlt
      have hrec := ih t g hnm h
      rw [cellLoop_succ_of_ne_loop π m t g (by rw [hrec]; exact h), hrec]
    · have : n = m + 1 := Nat.le_antisymm hle hge
      rw [this]

theorem cellStep_mono (π : Rule) (n n' s : Nat) (hle : n ≤ n')
    (h : cellStep π n s ≠ CellOut.loop) : cellStep π n' s = cellStep π n s := by
  unfold cellStep
  cases hr : π Dir.R s with
  | none => rfl
  | some vd =>
    obtain ⟨t, d'⟩ := vd
    cases hd : d' with
    | L => rfl
    | R =>
      have hne : cellLoop π n t 1 ≠ CellOut.loop := by
        intro hL
        apply h
        unfold cellStep
        rw [hr, hd]
        exact hL
      exact cellLoop_mono π n n' t 1 hle hne
    | Z => rfl

end URTM.TwoState
