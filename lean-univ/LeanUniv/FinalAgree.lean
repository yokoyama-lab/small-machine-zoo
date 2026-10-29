/-
  **13 点の URTM のどの 2 つも同じ計算をする**（`Agree.isUTMStrict_agree` を 13 点の証人に当てたもの）。**手書き**。

  13 点（支配されない URTM の記録点）の存在定理の証人を、存在定理の ∃ を開けずに、各 Final モジュールが
  使う表の定数そのもので並べる（`W`）。並びは状態数の昇順で、`dims` がその (状態数, 記号数) を与える。
  | i | (m, n) | 証人 | 存在定理 |
  |---|---|---|---|
  | 0 | (3,600) | `U3_600.U` | `Final3_600.exists_urtm_3_600` |
  | 1 | (4,41) | `SymMerge4_41.U` | `FinalSymMerge.exists_urtm_4_41` |
  | 2 | (5,38) | `SymMerge5_38.U` | `FinalSymMerge.exists_urtm_5_38` |
  | 3 | (6,30) | `SymMerge6_30.U` | `FinalSymMerge.exists_urtm_6_30` |
  | 4 | (7,28) | `SymMerge7_28.U` | `FinalSymMerge.exists_urtm_7_28` |
  | 5 | (8,21) | `SymMerge8_21.U` | `FinalSymMerge.exists_urtm_8_21` |
  | 6 | (10,8) | `U10_8.U` | `Final10_8.exists_urtm_10_8` |
  | 7 | (13,7) | `U13_7.U` | `FinalMorita.exists_urtm_13_7` |
  | 8 | (15,6) | `U15_6.U` | `FinalMorita.exists_urtm_15_6` |
  | 9 | (17,5) | `U17_5.U` | `FinalMorita.exists_urtm_17_5` |
  | 10 | (24,4) | `U24_4.U` | `FinalMorita.exists_urtm_24_4` |
  | 11 | (32,3) | `U32_3.U` | `FinalMorita.exists_urtm_32_3` |
  | 12 | (85,2) | `U85_2.U` | `Final85_2.exists_urtm_85_2` |

  * `records_spec`: 各 `W i` は決定的かつ可逆で、状態数と記号数は `dims i`、`IsUTMStrict` を満たす
    （存在定理の連言と同じ事実を、同じ定理から取る。(10,8) の `IsUTMStrict` は `Final10_8` と同じく
    `Chain10_8.isUTMStrict_U10_8_of_computable` に符号化・復号の計算可能性を渡したもの）。
  * `records_agree`: どの `i, j` についても `Agree.Agrees (W i) (W j)`（`Agree.isUTMStrict_agree` の結論。
    同じ `(n, a)` について両方が一緒に停止するか一緒に停止せず、その停止は `tm n` の停止と一致し、両方が
    停止したなら、それぞれの停止 ID のどの符号を復号しても `tm n` の同じ停止 ID の符号になる）。
  文が触れる `W`・`dims`・`Agrees` の本体（表の定数を含む）は lean-univ の文の固定（tests/pins.expected）が押さえる。

  **Any two of the 13 record URTMs compute the same thing.** `W` lists the witnesses of the 13 existence theorems
  as the table constants that the Final modules use (not through the ∃), by increasing number of states; `dims`
  gives their (states, symbols). `records_spec`: each `W i` is deterministic, reversible, has the counts `dims i`
  and satisfies `IsUTMStrict`. `records_agree`: `Agrees (W i) (W j)` for all `i, j`.
-/
import LeanUniv.Agree
import LeanUniv.Final3_600
import LeanUniv.FinalSymMerge
import LeanUniv.Final10_8
import LeanUniv.FinalMorita
import LeanUniv.Final85_2
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

namespace URTM.Univ.FinalAgree
open URTM URTM.Spec URTM.Univ.Agree

-- Unfolding `U := U0.dedup` during the unification after `fin_cases` hits the recursion limit, so keep it folded.
attribute [local irreducible] SymMerge4_41.U SymMerge5_38.U

/-- **The 13 record machines** (the witnesses of the 13 existence theorems), by increasing number of states:
    (3,600) (4,41) (5,38) (6,30) (7,28) (8,21) (10,8) (13,7) (15,6) (17,5) (24,4) (32,3) (85,2). -/
def W : Fin 13 → List Quint :=
  ![U3_600.U, SymMerge4_41.U, SymMerge5_38.U, SymMerge6_30.U, SymMerge7_28.U, SymMerge8_21.U,
    U10_8.U, U13_7.U, U15_6.U, U17_5.U, U24_4.U, U32_3.U, U85_2.U]

/-- (number of states, number of symbols) of `W i`. -/
def dims : Fin 13 → ℕ × ℕ :=
  ![(3, 600), (4, 41), (5, 38), (6, 30), (7, 28), (8, 21), (10, 8), (13, 7), (15, 6), (17, 5), (24, 4),
    (32, 3), (85, 2)]

/-- **The 13 record machines are URTMs**: each `W i` is deterministic and reversible, has `(dims i).1` states
    and `(dims i).2` symbols, and satisfies `IsUTMStrict` (Morita Def. 7.1). -/
theorem records_spec : ∀ i : Fin 13,
    Deterministic (W i) ∧ Reversible (W i) ∧ NStates (W i) = (dims i).1 ∧ NSyms (W i) = (dims i).2 ∧
      IsUTMStrict (W i) := by
  intro i
  fin_cases i
  · exact ⟨U3_600.U_det, U3_600.U_rev, U3_600.U_counts.1, U3_600.U_counts.2, U3_600.isUTMStrict_U⟩
  · exact ⟨SymMerge4_41.U_det, SymMerge4_41.U_rev, SymMerge4_41.U_counts.1, SymMerge4_41.U_counts.2,
      SymMerge4_41.isUTMStrict_U⟩
  · exact ⟨SymMerge5_38.U_det, SymMerge5_38.U_rev, SymMerge5_38.U_counts.1, SymMerge5_38.U_counts.2,
      SymMerge5_38.isUTMStrict_U⟩
  · exact ⟨SymMerge6_30.U_det, SymMerge6_30.U_rev, SymMerge6_30.U_counts.1, SymMerge6_30.U_counts.2,
      SymMerge6_30.isUTMStrict_U⟩
  · exact ⟨SymMerge7_28.U_det, SymMerge7_28.U_rev, SymMerge7_28.U_counts.1, SymMerge7_28.U_counts.2,
      SymMerge7_28.isUTMStrict_U⟩
  · exact ⟨SymMerge8_21.U_det, SymMerge8_21.U_rev, SymMerge8_21.U_counts.1, SymMerge8_21.U_counts.2,
      SymMerge8_21.isUTMStrict_U⟩
  · exact ⟨U10_8.U_det, U10_8.U_rev, U10_8.U_counts.1, U10_8.U_counts.2,
      Chain10_8.isUTMStrict_U10_8_of_computable ComputableEnc.c10_8_computable
        ComputableDec.d10_8_computable⟩
  · exact ⟨U13_7.U_det, U13_7.U_rev, U13_7.U_counts.1, U13_7.U_counts.2, U13_7.isUTMStrict_U⟩
  · exact ⟨U15_6.U_det, U15_6.U_rev, U15_6.U_counts.1, U15_6.U_counts.2, U15_6.isUTMStrict_U⟩
  · exact ⟨U17_5.U_det, U17_5.U_rev, U17_5.U_counts.1, U17_5.U_counts.2, U17_5.isUTMStrict_U⟩
  · exact ⟨U24_4.U_det, U24_4.U_rev, U24_4.U_counts.1, U24_4.U_counts.2, U24_4.isUTMStrict_U⟩
  · exact ⟨U32_3.U_det, U32_3.U_rev, U32_3.U_counts.1, U32_3.U_counts.2, U32_3.isUTMStrict_U⟩
  · exact ⟨U85_2.U_det, U85_2.U_rev, U85_2.U_counts.1, U85_2.U_counts.2, U85_2.isUTMStrict_U⟩

/-- **Any two of the 13 record URTMs compute the same thing** (`Agree.isUTMStrict_agree` on the witnesses):
    for all `i, j`, `W i` and `W j` have computable encoders and decoders under which, for every TM `tm n` and
    every finite ID `a` of it, `W i` halts ⇔ `W j` halts ⇔ `tm n` halts, and when both halt every code of either
    halting ID decodes to a code of the same halting ID of `tm n` (`Agree.Agrees`). -/
theorem records_agree : ∀ i j : Fin 13, Agrees (W i) (W j) := fun i j =>
  agree_of_isUTMStrict (records_spec i).1 (records_spec j).1 (records_spec i).2.2.2.2
    (records_spec j).2.2.2.2

end URTM.Univ.FinalAgree
