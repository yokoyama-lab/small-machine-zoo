/-
  3 状態 2 記号の URTM の非存在を、**本文の 14 点と同じ強い万能性 `IsUTMStrict`** の上で述べる。**手書き**。

  段階 1〜2d の主定理（`no_three_two_URTM`・`_A`・`_B`・`_C`・`_D`）の結論は `¬ IsUTM_MoritaOver tbl [sg]`
  （Def. 7.1 を zipper の上で、c の値の記号を {0, sg} に制限したもの）。ここではそれを、lean-univ の存在定理の
  結論と同じ `Spec.IsUTMStrict tbl`（`Strict.lean`。lean-univ の写し）の否定に移す。合成するのは次の 3 つ:

    * `IsUTM_MoritaOver.mono` : 記号集合 Γ を広げても（{0} ∪ Γ ⊆ {0} ∪ Γ'）`IsUTM_MoritaOver` は保たれる
    * `rtm32_symbols` / `rtm32_deterministic` : `RTM32 tbl q₀ q₁ q₂ sg` の表に現れる記号は 0 か sg で、
      表は仕様の意味で決定的（`deterministic tbl = true` は同じ五つ組の重複も許さないので、そのまま出る）
    * `Sat.IsUTMStrict.moritaOver` : 決定的な U で `IsUTMStrict U → IsUTM_MoritaOver U (symbols U)`

  主定理 `no_three_two_URTMStrict_D`: `isExcD` の表を除き、3 状態 2 記号の RTM は `IsUTMStrict` の意味で
  万能でない。まとめの形 `three_two_URTMStrict_summary`: 例外の一覧 `excDTables`（正規形の表 720 個）に
  載らない 3 状態 2 記号の RTM は `IsUTMStrict` でない。

  既存の定理の文は変えない（追加だけ）。
-/
import URTMMeta.ThreeD
import URTMMeta.MoritaOverSat

namespace URTM.Meta
open URTM URTM.TwoState URTM.Three

/-! ### 記号集合についての単調性 -/

/-- **単調性**: c の値の記号が {0} ∪ Γ に入るなら、{0} ∪ Γ' ⊇ {0} ∪ Γ にも入る。 -/
theorem SimulatesEnumOver.mono {tbl : List Quint} {Γ Γ' : List Nat} {E : ℕ → List Quint}
    (h : SimulatesEnumOver tbl Γ E) (hΓ : ∀ a ∈ Γ, a = 0 ∨ a ∈ Γ') : SimulatesEnumOver tbl Γ' E := by
  obtain ⟨c, d, hc, hd, h⟩ := h
  refine ⟨c, d, hc, hd, fun n α hα => ?_⟩
  obtain ⟨hs, hh, hn⟩ := h n α hα
  refine ⟨fun a ha => ?_, hh, hn⟩
  rcases hs a ha with h0 | hm
  · exact Or.inl h0
  · exact hΓ a hm

/-- **単調性**（`IsUTM_MoritaOver`）。 -/
theorem IsUTM_MoritaOver.mono {tbl : List Quint} {Γ Γ' : List Nat} (h : IsUTM_MoritaOver tbl Γ)
    (hΓ : ∀ a ∈ Γ, a = 0 ∨ a ∈ Γ') : IsUTM_MoritaOver tbl Γ' :=
  SimulatesEnumOver.mono h hΓ

/-! ### `RTM32` の表の記号と決定性 -/

/-- 計算用の決定性（`allPairs detPair`）から仕様の決定性（`Spec.Deterministic`）へ。 -/
theorem spec_det_of_deterministic {T : List Quint} (h : deterministic T = true) : Spec.Deterministic T := by
  induction T with
  | nil => intro r₁ h₁; cases h₁
  | cons x xs ih =>
    have h' : (xs.all (detPair x) && allPairs detPair xs) = true := h
    obtain ⟨hx, hxs⟩ := Bool.and_eq_true_iff.mp h'
    intro r₁ h₁ r₂ h₂ hp hs
    rcases List.mem_cons.mp h₁ with e₁ | m₁ <;> rcases List.mem_cons.mp h₂ with e₂ | m₂
    · rw [e₁, e₂]
    · subst e₁
      have := List.all_eq_true.mp hx r₂ m₂
      simp [detPair, hp, hs] at this
    · subst e₂
      have := List.all_eq_true.mp hx r₁ m₁
      simp [detPair, hp, hs] at this
    · exact ih hxs r₁ m₁ r₂ m₂ hp hs

section
variable {tbl : List Quint} {q₀ q₁ q₂ sg : Nat}

/-- **`RTM32` の表に現れる記号は 0 か sg**（`Spec.symbols` は読む記号と書く記号を集めたもの）。 -/
theorem rtm32_symbols (H : RTM32 tbl q₀ q₁ q₂ sg) : ∀ a ∈ Spec.symbols tbl, a = 0 ∨ a = sg := by
  intro a ha
  unfold Spec.symbols at ha
  obtain ⟨r, hr, ha⟩ := List.mem_flatMap.mp ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact (H.sym r hr).1
  · exact (H.sym r hr).2

/-- **`RTM32` の表は仕様の意味で決定的**。 -/
theorem rtm32_deterministic (H : RTM32 tbl q₀ q₁ q₂ sg) : Spec.Deterministic tbl :=
  spec_det_of_deterministic H.det

/-- **`IsUTMStrict` の `RTM32` の表は `IsUTM_MoritaOver tbl [sg]`**
    （`Sat.IsUTMStrict.moritaOver` と単調性の合成）。 -/
theorem rtm32_moritaOver_of_strict (H : RTM32 tbl q₀ q₁ q₂ sg) (hU : Spec.IsUTMStrict tbl) :
    IsUTM_MoritaOver tbl [sg] :=
  (Sat.IsUTMStrict.moritaOver (rtm32_deterministic H) hU).mono fun a ha =>
    (rtm32_symbols H a ha).imp_right List.mem_singleton.mpr

/-! ### 主定理（`IsUTMStrict` の形） -/

/-- 段階 1（`isExc`）の `IsUTMStrict` 版。 -/
theorem no_three_two_URTMStrict (H : RTM32 tbl q₀ q₁ q₂ sg)
    (hne : isExc (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl) = false) :
    ¬ Spec.IsUTMStrict tbl := fun hU =>
  no_three_two_URTM H hne (rtm32_moritaOver_of_strict H hU)

/-- 段階 2b 群 A（`isExcA`）の `IsUTMStrict` 版。 -/
theorem no_three_two_URTMStrict_A (H : RTM32 tbl q₀ q₁ q₂ sg)
    (hne : isExcA (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl) = false) :
    ¬ Spec.IsUTMStrict tbl := fun hU =>
  no_three_two_URTM_A H hne (rtm32_moritaOver_of_strict H hU)

/-- 段階 2b 群 B（`isExcB`）の `IsUTMStrict` 版。 -/
theorem no_three_two_URTMStrict_B (H : RTM32 tbl q₀ q₁ q₂ sg)
    (hne : isExcB (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl) = false) :
    ¬ Spec.IsUTMStrict tbl := fun hU =>
  no_three_two_URTM_B H hne (rtm32_moritaOver_of_strict H hU)

/-- 段階 2b 群 C（`isExcC`）の `IsUTMStrict` 版。 -/
theorem no_three_two_URTMStrict_C (H : RTM32 tbl q₀ q₁ q₂ sg)
    (hne : isExcC (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl) = false) :
    ¬ Spec.IsUTMStrict tbl := fun hU =>
  no_three_two_URTM_C H hne (rtm32_moritaOver_of_strict H hU)

/-- **定理（段階 2d、`IsUTMStrict` の形）: `isExcD` の表を除き、3 状態 2 記号の RTM は
    `IsUTMStrict`（本文の 14 点と同じ万能性）の意味で万能でない**。 -/
theorem no_three_two_URTMStrict_D (H : RTM32 tbl q₀ q₁ q₂ sg)
    (hne : isExcD (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl) = false) :
    ¬ Spec.IsUTMStrict tbl := fun hU =>
  no_three_two_URTM_D H hne (rtm32_moritaOver_of_strict H hU)

/-- **一覧の形**: 正規形の表が例外の一覧 `excDTables` に載らない 3 状態 2 記号の RTM は `IsUTMStrict` でない。 -/
theorem no_three_two_URTMStrict_of_not_mem (H : RTM32 tbl q₀ q₁ q₂ sg)
    (hm : (absCodes q₀ q₁ q₂ sg tbl, absDirs q₀ q₁ q₂ tbl) ∉ excDTables) :
    ¬ Spec.IsUTMStrict tbl := by
  apply no_three_two_URTMStrict_D H
  cases hx : isExcD (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl)
  · rfl
  · exact absurd (mem_excDTables ⟨rfl, absCodes_lt H, rfl⟩ hx) hm

end

/-- **まとめ**: 例外の一覧 `excDTables` は正規形の表 720 個で、その外の 3 状態 2 記号の RTM
    （Morita の数え方。停止用の疑似状態は数えない）は `IsUTMStrict` の意味で万能でない。

    720 は候補の一覧 `excDTables` の長さで、例外の数の**上界**である。この定理は一覧の外が万能でないことを
    言うだけで、一覧の 720 表がすべて（あるいはどれかが）万能だとは言わない（例外がちょうど 720 とは言わない）。
    `RTM32 tbl q₀ q₁ q₂ sg` は五つ組の出る状態が q₀, q₁, q₂ のどれか、記号が 0 か sg であることを言うので、
    対象は**高々** 3 状態 2 記号の RTM（規則を持たない状態や、表に現れない sg も許す）。 -/
theorem three_two_URTMStrict_summary :
    excDTables.length = 720 ∧
    ∀ (tbl : List Quint) (q₀ q₁ q₂ sg : Nat), RTM32 tbl q₀ q₁ q₂ sg →
      (absCodes q₀ q₁ q₂ sg tbl, absDirs q₀ q₁ q₂ tbl) ∉ excDTables → ¬ Spec.IsUTMStrict tbl :=
  ⟨excDTables_length, fun _ _ _ _ _ H hm => no_three_two_URTMStrict_of_not_mem H hm⟩

end URTM.Meta
