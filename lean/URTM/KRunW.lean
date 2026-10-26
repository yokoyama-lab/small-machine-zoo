/-
  `KRunF` の検査器の重みつき版: 規則を関数 `f` で引いてジッパーを進めながら、各ステップで入った状態の重み
  `κ` を足す。健全性は `StepW`（`StepW.lean`）を返す。

  URTM(3,36654) の試験例について、T̂（Lemma 5.9 の変換）の実行に沿って Lemma 5.10 の歩数（`Conv510.cost`）を
  足し、T† のステップ数を T† を回さずに出すために使う（`CTSH3_36654Cost.lean`）。

  * `frunW bk f κ n w z` — n ステップ進め、重みの和を w に足していく（和は毎ステップ数に評価させる。
    `Nat` の場合分けにかけるのは、カーネルの評価で未評価の足し算の入れ子を積み上げないため）。
  * `freachW bk f κ n z m w` — z からちょうど n ステップで m に達し、重みの和がちょうど w。

  mathlib 非依存。未証明の穴・新規公理・native_decide を使わない。
-/
import URTM.KRunF
import URTM.StepW

namespace URTM.KState.RunF

open URTM URTM.KState URTM.KState.Run

variable {Q P S : Type} [DecidableEq Q] [DecidableEq S]

/-- n ステップの実行と重みの和（w は足し込み先）。 -/
def frunW (bk : S) (f : Q → S → Option (Rule Q P S)) (κ : Tgt Q P → Nat) :
    Nat → Nat → Zip Q P S → Option (Zip Q P S × Nat)
  | 0, w, z => some (z, w)
  | n + 1, w, z =>
    match fstep bk f z with
    | none => none
    | some z' =>
      match w + κ z'.st with
      | 0 => frunW bk f κ n 0 z'
      | w' + 1 => frunW bk f κ n (w' + 1) z'

/-- 途中までの検査器: z からちょうど n ステップで m に達し、入った状態の重みの和がちょうど w。 -/
def freachW [DecidableEq P] (bk : S) (f : Q → S → Option (Rule Q P S)) (κ : Tgt Q P → Nat)
    (n : Nat) (z m : Zip Q P S) (w : Nat) : Bool :=
  match frunW bk f κ n 0 z with
  | none => false
  | some (z', w') => decide (z' = m) && w' == w

section Sound
variable {T : Machine Q P S} {f : Q → S → Option (Rule Q P S)} {bk : S} {κ : Tgt Q P → Nat}

theorem frunW_sound (hs : ∀ p s r, f p s = some r → r ∈ T) :
    ∀ (n w₀ : Nat) {z e : Zip Q P S} {w₁ : Nat}, frunW bk f κ n w₀ z = some (e, w₁) →
      ∃ w, w₁ = w₀ + w ∧ StepW T κ n w (z.cfg bk) (e.cfg bk)
  | 0, w₀, z, e, w₁, h => by
    simp only [frunW, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨0, rfl, .refl _⟩
  | n + 1, w₀, z, e, w₁, h => by
    simp only [frunW] at h
    split at h
    · cases h
    · rename_i z' hz
      have hstep := fstep_sound hs hz
      have key : ∀ v, v = w₀ + κ z'.st → frunW bk f κ n v z' = some (e, w₁) →
          ∃ w, w₁ = w₀ + w ∧ StepW T κ (n + 1) w (z.cfg bk) (e.cfg bk) := by
        intro v hv hr
        obtain ⟨w, hw, hW⟩ := frunW_sound hs n v hr
        refine ⟨κ z'.st + w, by omega, ?_⟩
        have := StepW.cons hstep hW
        rwa [show (z'.cfg bk).st = z'.st from rfl] at this
      split at h
      · rename_i h0; exact key 0 h0.symm h
      · rename_i w' h1; exact key (w' + 1) h1.symm h

/-- **健全性**: 重みつきの検査器が通れば、`T` は z の表す配置から m の表す配置へちょうど n ステップで進み、
    入った状態の重みの和はちょうど w。 -/
theorem stepW_of_reachW [DecidableEq P] (hs : ∀ p s r, f p s = some r → r ∈ T) {n w : Nat} {z m : Zip Q P S}
    (h : freachW bk f κ n z m w = true) : StepW T κ n w (z.cfg bk) (m.cfg bk) := by
  simp only [freachW] at h
  split at h
  · cases h
  · rename_i z' w' hz
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨w, hw, hW⟩ := frunW_sound hs n 0 hz
    rw [hw, Nat.zero_add]; exact hW

end Sound

end URTM.KState.RunF
