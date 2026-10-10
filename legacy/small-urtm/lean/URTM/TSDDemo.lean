/-
  2 状態 RTM の停止問題の決定可能性 その 13: 空虚でないことの確認。**手書き**。

  主定理 `decide2_correct` の仮定が具体的な表で満たされ、判定が **true になる例と false になる例の
  両方**があることを示す（`decide2` の値そのものは `haltBound` 歩の実行なので評価しない。
  値は主定理から従う）。どちらも場合 (iii)（左右両方の移動がある）の表。
-/
import URTM.TSDHaltState

namespace URTM.TwoState

def blankQ (st : Nat) : QConf := ⟨st, 0, fun _ => 0⟩

/-! ## 停止する例: 右へ 1 を書いて戻り、その 1 を読むと規則が無い -/

def haltTbl : List Quint := [⟨0, 0, 1, Dir.R, 1⟩, ⟨1, 0, 0, Dir.L, 0⟩]

theorem haltTbl_rev : reversible haltTbl = true := by decide
theorem haltTbl_det : deterministic haltTbl = true := by decide

theorem haltTbl_halts : QHalts haltTbl (blankQ 0) := ⟨3, by rfl⟩

theorem haltTbl_decide :
    decide2 haltTbl 0 1 2 0 0 (blankQ 0) = true := by
  refine (decide2_correct haltTbl haltTbl_rev 0 1 (by decide) ?_ 2 ?_ 0 0 (blankQ 0)
    (Or.inl rfl) (fun _ => by show 0 < 2; omega) (Int.le_refl _) (Int.le_refl _) (Int.le_refl _)
    (fun _ _ => rfl)).mpr haltTbl_halts
  · intro r hr; simp [haltTbl] at hr; rcases hr with rfl | rfl <;> simp
  · intro r hr _; simp [haltTbl] at hr; rcases hr with rfl | rfl <;> simp

/-! ## 停止しない例: 状態 1 で空白を読むと 1 を書いて右へ（永久に右へ逃走） -/

def escTbl : List Quint := [⟨1, 0, 1, Dir.R, 1⟩, ⟨0, 0, 0, Dir.L, 0⟩]

theorem escTbl_rev : reversible escTbl = true := by decide

theorem escTbl_never : ∀ (n : Nat) (p : Int) (t : Int → Nat), (∀ x, p ≤ x → t x = 0) →
    qrun escTbl n ⟨1, p, t⟩ ≠ none := by
  intro n
  induction n with
  | zero => intro p t _; simp [qrun]
  | succ n ih =>
    intro p t ht
    have hs : qstep escTbl ⟨1, p, t⟩ = some ⟨1, p + 1, write t p 1⟩ := by
      unfold qstep
      show (match find? escTbl 1 (t p) with
        | none => none
        | some r => some (⟨r.q, move r.d p, write t p r.t⟩ : QConf)) = _
      rw [ht p (Int.le_refl _)]
      rfl
    rw [qrun_succ_some escTbl n hs]
    apply ih
    intro x hx
    unfold write
    rw [if_neg (by omega)]
    exact ht x (by omega)

theorem escTbl_not_halts : ¬ QHalts escTbl (blankQ 1) := by
  rintro ⟨n, hn⟩
  exact escTbl_never n 0 _ (fun _ _ => rfl) hn

theorem escTbl_decide :
    decide2 escTbl 0 1 2 0 0 (blankQ 1) = false := by
  have h := decide2_correct escTbl escTbl_rev 0 1 (by decide) ?_ 2 ?_ 0 0 (blankQ 1)
    (Or.inr rfl) (fun _ => by show 0 < 2; omega) (Int.le_refl _) (Int.le_refl _) (Int.le_refl _)
    (fun _ _ => rfl)
  · cases hd : decide2 escTbl 0 1 2 0 0 (blankQ 1) with
    | false => rfl
    | true => exact absurd (h.mp hd) escTbl_not_halts
  · intro r hr; simp [escTbl] at hr; rcases hr with rfl | rfl <;> simp
  · intro r hr _; simp [escTbl] at hr; rcases hr with rfl | rfl <;> simp

end URTM.TwoState
