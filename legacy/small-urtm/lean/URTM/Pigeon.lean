/-
  **鳩の巣原理**（自前）。**手書き**。キュー R13（`decideHalt` へ向けて）。

  補題 C（空白半直線の応答列が最終的に周期的）と補題 D（中央有限領域が最終的に周期的）は
  どちらも「有限集合に値を取る列は必ず重複する」を使う。このリポジトリは **mathlib に
  依存しない**方針なので、`Finset` / `Fintype` は使えない。ここで自前に証明する。

    `pigeon` : 値がすべて N 未満なら、添字 0..N のどこかで必ず重複する
    `orbit_repeat` : 決定的な軌道（`s (i+1) = F (s i)`）は N+1 歩以内に必ず重複する
    `orbit_periodic` : 重複したら以後ずっと周期的

  証明: N についての帰納。f(N+1) と同じ値が前に無ければ、値域から f(N+1) を 1 つ抜いて
  詰め直した g を作ると、g は N 未満に収まるので帰納法が使える。
-/
namespace URTM

/-- **鳩の巣**: `f i < N`（i ≤ N）なら、`i < j ≤ N` で `f i = f j` となる組がある。 -/
theorem pigeon :
    ∀ (N : Nat) (f : Nat → Nat), (∀ i, i ≤ N → f i < N) →
      ∃ i j, i < j ∧ j ≤ N ∧ f i = f j := by
  intro N
  induction N with
  | zero =>
    intro f hf
    exact absurd (hf 0 (Nat.le_refl 0)) (by omega)
  | succ N ih =>
    intro f hf
    by_cases hdup : ∃ i, i < N + 1 ∧ f i = f (N + 1)
    · obtain ⟨i, hi, he⟩ := hdup
      exact ⟨i, N + 1, hi, Nat.le_refl _, he⟩
    · -- 前に同じ値が無いなら、値域から f (N+1) を抜いて詰め直す
      have hne : ∀ i, i < N + 1 → f i ≠ f (N + 1) := by
        intro i hi he
        exact hdup ⟨i, hi, he⟩
      have hv : f (N + 1) ≤ N := by
        have := hf (N + 1) (Nat.le_refl _)
        omega
      have hg : ∀ i, i ≤ N →
          (if f i < f (N + 1) then f i else f i - 1) < N := by
        intro i hi
        have h1 : f i < N + 1 := hf i (by omega)
        have h2 : f i ≠ f (N + 1) := hne i (by omega)
        by_cases hc : f i < f (N + 1)
        · simp only [hc, if_true]; omega
        · simp only [hc, if_false]; omega
      obtain ⟨i, j, hij, hjN, hgij⟩ :=
        ih (fun i => if f i < f (N + 1) then f i else f i - 1) hg
      refine ⟨i, j, hij, by omega, ?_⟩
      have h1 : f i ≠ f (N + 1) := hne i (by omega)
      have h2 : f j ≠ f (N + 1) := hne j (by omega)
      have hi1 : f i < N + 1 := hf i (by omega)
      have hj1 : f j < N + 1 := hf j (by omega)
      by_cases ha : f i < f (N + 1) <;> by_cases hb : f j < f (N + 1) <;>
        simp only [ha, hb, if_true, if_false] at hgij <;> omega

/-! ## 軌道の周期性 -/

/-- 決定的な軌道 `orbit F s₀ i`（`F` を i 回適用）。 -/
def orbit (F : Nat → Nat) : Nat → Nat → Nat
  | 0, s => s
  | i + 1, s => orbit F i (F s)

theorem orbit_succ (F : Nat → Nat) (i : Nat) (s : Nat) :
    orbit F (i + 1) s = orbit F i (F s) := rfl

/-- 軌道は歩数について分解できる。 -/
theorem orbit_add (F : Nat → Nat) :
    ∀ (a b s : Nat), orbit F (a + b) s = orbit F b (orbit F a s) := by
  intro a
  induction a with
  | zero => intro b s; rw [Nat.zero_add]; rfl
  | succ a ih =>
    intro b s
    have h : a + 1 + b = (a + b) + 1 := by omega
    rw [h, orbit_succ, ih b (F s), orbit_succ]

theorem orbit_one (F : Nat → Nat) (s : Nat) : orbit F 1 s = F s := rfl

/-- 軌道を**後ろから** 1 歩はがす。 -/
theorem orbit_succ_right (F : Nat → Nat) (n s : Nat) :
    orbit F (n + 1) s = F (orbit F n s) := by
  rw [orbit_add F n 1 s]; rfl

/-- **軌道は N+1 歩以内に必ず重複する**（値がすべて N 未満なら）。 -/
theorem orbit_repeat (F : Nat → Nat) (N s₀ : Nat)
    (hb : ∀ i, orbit F i s₀ < N) :
    ∃ i j, i < j ∧ j ≤ N ∧ orbit F i s₀ = orbit F j s₀ :=
  pigeon N (fun i => orbit F i s₀) (fun i _ => hb i)

/-- **重複したら以後ずっと周期的**: `orbit i = orbit j`（i < j）なら、
    周期 `j - i` で i 以降ずっと繰り返す。 -/
theorem orbit_periodic (F : Nat → Nat) (s₀ i j : Nat) (hij : i < j)
    (h : orbit F i s₀ = orbit F j s₀) :
    ∀ q, orbit F (i + (j - i) * q) s₀ = orbit F i s₀ := by
  intro q
  induction q with
  | zero => rw [Nat.mul_zero, Nat.add_zero]
  | succ q ihq =>
    have hstep : orbit F (i + (j - i) * (q + 1)) s₀
        = orbit F (j - i) (orbit F (i + (j - i) * q) s₀) := by
      have harith : i + (j - i) * (q + 1) = (i + (j - i) * q) + (j - i) := by
        rw [Nat.mul_succ]; omega
      rw [harith, orbit_add]
    rw [hstep, ihq]
    -- orbit (j - i) (orbit i s₀) = orbit j s₀ = orbit i s₀
    have hji : i + (j - i) = j := by omega
    have : orbit F (j - i) (orbit F i s₀) = orbit F j s₀ := by
      rw [← orbit_add, hji]
    rw [this, ← h]

end URTM
