/-
  **Morita の数え方（Def. 5.1/5.2）による状態数・記号数**。`Strict.lean` の `NStates`・`NSyms` と**併置**する
  （既存の定義と定理の文は変えない）。

  Morita 2017 Def. 5.1/5.2 では δ ⊆ Q × S × S × {−1, 0, +1} × Q なので、五つ組の行き先の状態も Q に入る。
  m = |Q|、n = |S|（S は空白 s₀ を含む）。表 `U` に現れるものだけを数えると
  * `NStatesMorita U`: 出発の状態と行き先の状態の和の個数（`Spec.states U = U.flatMap [p, q]`）。
  * `NSymsMorita U`: 読む記号と書く記号の和の個数（`Spec.symbols U = U.flatMap [s, t]`）。空白 0 を足さない。
    空白が表に現れることは別に述べる（`FinalMoritaCount`）。
  `NStates` は行き先にしか現れない状態（`halt`/`null` のような疑似状態）を数えず、`NSyms` は空白 0 を
  常に数える。違いは `FinalMoritaCount` の定理で、記録 14 点の証人では一致し、記述ファイルの表では
  状態数が 2 多いことを示す。

  **Morita's counts (Def. 5.1/5.2)**, beside `NStates`/`NSyms`: the distinct states that occur as source
  or target, and the distinct symbols that occur as read or written symbol (the blank is not added).
-/
import LeanUniv.Spec

namespace URTM.Univ.MoritaCount
open URTM

/-- Number of states as in Morita Def. 5.1/5.2: distinct source **and target** states of the table. -/
def NStatesMorita (U : List Quint) : ℕ := (Spec.states U).dedup.length

/-- Number of symbols as in Morita Def. 5.1/5.2: distinct read and written symbols of the table
    (the blank is counted only if it occurs). -/
def NSymsMorita (U : List Quint) : ℕ := (Spec.symbols U).dedup.length

/-- If some quintuple reads the blank, the blank occurs among the symbols of the table. -/
theorem zero_mem_symbols {U : List Quint} (h : ∃ r ∈ U, r.s = 0) : 0 ∈ Spec.symbols U := by
  obtain ⟨r, hr, h0⟩ := h
  unfold Spec.symbols
  exact List.mem_flatMap.2 ⟨r, hr, by simp [h0]⟩

/-! Sanity checks on toy tables. -/

example : NStatesMorita [⟨0, 0, 1, .R, 1⟩, ⟨1, 0, 2, .L, 0⟩, ⟨1, 1, 1, .Z, 2⟩] = 3 := by decide
example : NSymsMorita [⟨0, 1, 1, .R, 0⟩] = 1 := by decide

end URTM.Univ.MoritaCount
