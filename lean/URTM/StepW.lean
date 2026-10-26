/-
  重みつきの計算過程 `StepW T κ n w a b`: 機械 T で配置 a から b へちょうど n ステップ、途中の各ステップで
  入った状態 st の重み κ st の和が w。

  Morita 2017, Lemma 5.10 の歩数（T̂ の 1 ステップを T† は入った状態に応じて 1 または 2j + 1 ステップで模倣する）を
  T̂ の実行に沿って足し合わせるために使う（`Conv510Exact.lean` の `stepW_sim`）。重みが状態だけで決まる形にしてあるのは、
  カーネルの評価でジッパーを回しながら和を取れるようにするため（`KRunW.lean`）。

  mathlib 非依存。未証明の穴・新規公理・native_decide を使わない。
-/
import URTM.KState

namespace URTM.KState

variable {Q P S : Type}

/-- 重みつきの計算過程。`cons` は 1 ステップ c → c' の重み `κ c'.st`（入った状態の重み）を足す。 -/
inductive StepW (T : Machine Q P S) (κ : Tgt Q P → Nat) : Nat → Nat → Cfg Q P S → Cfg Q P S → Prop
  | refl (c : Cfg Q P S) : StepW T κ 0 0 c c
  | cons {n w : Nat} {c c' c'' : Cfg Q P S} : Step T c c' → StepW T κ n w c' c'' →
      StepW T κ (n + 1) (κ c'.st + w) c c''

namespace StepW

variable {T : Machine Q P S} {κ : Tgt Q P → Nat}

/-- 重みを忘れると普通の計算過程。 -/
theorem toStepN : ∀ {n w : Nat} {a b : Cfg Q P S}, StepW T κ n w a b → StepN T n a b
  | _, _, _, _, .refl _ => .refl _
  | _, _, _, _, .cons h₁ h₂ => .cons h₁ (toStepN h₂)

theorem single {a b : Cfg Q P S} (h : Step T a b) : StepW T κ 1 (κ b.st) a b := by
  have := StepW.cons (κ := κ) h (.refl b)
  simpa using this

theorem trans {n w n' w' : Nat} {a b c : Cfg Q P S}
    (h₁ : StepW T κ n w a b) (h₂ : StepW T κ n' w' b c) : StepW T κ (n + n') (w + w') a c := by
  induction h₁ with
  | refl => simpa using h₂
  | @cons n w c c' c'' hs _ ih =>
    have := StepW.cons hs (ih h₂)
    rwa [show n + n' + 1 = n + 1 + n' by omega, show κ c'.st + (w + w') = κ c'.st + w + w' by omega] at this

end StepW

end URTM.KState
