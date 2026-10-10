/-
  **Morita の数え方（Def. 5.1/5.2、`MoritaCount`）による記録 14 点**。既存の `NStates`・`NSyms` による定理
  （`FinalBook`・`Final85_2`・`Final3_600`）はそのまま残し、数え方だけを替えた形を併置する。

  * `count_<…>`: 証人（停止の五つ組 2 本を除いた表 `Book.B<m>_<n>` 12 台、`U85_2.U`、`U3_600.U`）について。
    `Book.B<m>_<n>` のうち Morita の 6 台は書籍本文の表、ブロック化の 6 台は書籍に無いのでその類比（`Book.lean` の冒頭）。
    `NStatesMorita W = m ∧ NSymsMorita W = n ∧ 0 ∈ Spec.symbols W`（行き先の状態も数え、空白は表に現れる）。
    `FinalBlank.blank_<…>`（`decide +kernel`）と既存の `NStates`・`NSyms` の値から導く。
  * `exists_urtm_<m>_<n>_moritaCount`: `∃ U, Deterministic U ∧ Reversible U ∧ NStatesMorita U = m ∧
    NSymsMorita U = n ∧ 0 ∈ Spec.symbols U ∧ IsUTMStrict U`。
  * `count_desc_<m>_<n>`: 記述ファイルの表 `U<m>_<n>.U`（疑似状態 `halt`/`null` へ入る五つ組 2 本を含む）では
    `NStatesMorita = m + 2`、`NSymsMorita = n`（`decide +kernel`）。この数え方では疑似状態 2 つも状態に数える。

  **Morita's counts for the 14 record points**, beside the existing theorems (unchanged).
-/
import LeanUniv.MoritaCount
import LeanUniv.FinalBlank
import LeanUniv.FinalBlank3_600

namespace URTM.Univ.FinalMoritaCount
open URTM URTM.Univ.Book URTM.Univ.MoritaCount URTM.Univ.FinalBlank

/-! ### The 14 record witnesses -/

theorem count_book_10_8 :
    NStatesMorita B10_8 = 10 ∧ NSymsMorita B10_8 = 8 ∧ 0 ∈ Spec.symbols B10_8 :=
  ⟨blank_book_10_8.2.2.2.trans B10_8_counts.1, blank_book_10_8.2.1.trans B10_8_counts.2,
    zero_mem_symbols blank_book_10_8.1⟩

theorem count_book_13_7 :
    NStatesMorita B13_7 = 13 ∧ NSymsMorita B13_7 = 7 ∧ 0 ∈ Spec.symbols B13_7 :=
  ⟨blank_book_13_7.2.2.2.trans B13_7_counts.1, blank_book_13_7.2.1.trans B13_7_counts.2,
    zero_mem_symbols blank_book_13_7.1⟩

theorem count_book_15_6 :
    NStatesMorita B15_6 = 15 ∧ NSymsMorita B15_6 = 6 ∧ 0 ∈ Spec.symbols B15_6 :=
  ⟨blank_book_15_6.2.2.2.trans B15_6_counts.1, blank_book_15_6.2.1.trans B15_6_counts.2,
    zero_mem_symbols blank_book_15_6.1⟩

theorem count_book_17_5 :
    NStatesMorita B17_5 = 17 ∧ NSymsMorita B17_5 = 5 ∧ 0 ∈ Spec.symbols B17_5 :=
  ⟨blank_book_17_5.2.2.2.trans B17_5_counts.1, blank_book_17_5.2.1.trans B17_5_counts.2,
    zero_mem_symbols blank_book_17_5.1⟩

theorem count_book_24_4 :
    NStatesMorita B24_4 = 24 ∧ NSymsMorita B24_4 = 4 ∧ 0 ∈ Spec.symbols B24_4 :=
  ⟨blank_book_24_4.2.2.2.trans B24_4_counts.1, blank_book_24_4.2.1.trans B24_4_counts.2,
    zero_mem_symbols blank_book_24_4.1⟩

theorem count_book_32_3 :
    NStatesMorita B32_3 = 32 ∧ NSymsMorita B32_3 = 3 ∧ 0 ∈ Spec.symbols B32_3 :=
  ⟨blank_book_32_3.2.2.2.trans B32_3_counts.1, blank_book_32_3.2.1.trans B32_3_counts.2,
    zero_mem_symbols blank_book_32_3.1⟩

theorem count_book_4_46 :
    NStatesMorita B4_46 = 4 ∧ NSymsMorita B4_46 = 46 ∧ 0 ∈ Spec.symbols B4_46 :=
  ⟨blank_book_4_46.2.2.2.trans B4_46_counts.1, blank_book_4_46.2.1.trans B4_46_counts.2,
    zero_mem_symbols blank_book_4_46.1⟩

theorem count_book_5_45 :
    NStatesMorita B5_45 = 5 ∧ NSymsMorita B5_45 = 45 ∧ 0 ∈ Spec.symbols B5_45 :=
  ⟨blank_book_5_45.2.2.2.trans B5_45_counts.1, blank_book_5_45.2.1.trans B5_45_counts.2,
    zero_mem_symbols blank_book_5_45.1⟩

theorem count_book_6_37 :
    NStatesMorita B6_37 = 6 ∧ NSymsMorita B6_37 = 37 ∧ 0 ∈ Spec.symbols B6_37 :=
  ⟨blank_book_6_37.2.2.2.trans B6_37_counts.1, blank_book_6_37.2.1.trans B6_37_counts.2,
    zero_mem_symbols blank_book_6_37.1⟩

theorem count_book_7_32 :
    NStatesMorita B7_32 = 7 ∧ NSymsMorita B7_32 = 32 ∧ 0 ∈ Spec.symbols B7_32 :=
  ⟨blank_book_7_32.2.2.2.trans B7_32_counts.1, blank_book_7_32.2.1.trans B7_32_counts.2,
    zero_mem_symbols blank_book_7_32.1⟩

theorem count_book_8_28 :
    NStatesMorita B8_28 = 8 ∧ NSymsMorita B8_28 = 28 ∧ 0 ∈ Spec.symbols B8_28 :=
  ⟨blank_book_8_28.2.2.2.trans B8_28_counts.1, blank_book_8_28.2.1.trans B8_28_counts.2,
    zero_mem_symbols blank_book_8_28.1⟩

theorem count_book_9_27 :
    NStatesMorita B9_27 = 9 ∧ NSymsMorita B9_27 = 27 ∧ 0 ∈ Spec.symbols B9_27 :=
  ⟨blank_book_9_27.2.2.2.trans B9_27_counts.1, blank_book_9_27.2.1.trans B9_27_counts.2,
    zero_mem_symbols blank_book_9_27.1⟩

theorem count_85_2 :
    NStatesMorita U85_2.U = 85 ∧ NSymsMorita U85_2.U = 2 ∧ 0 ∈ Spec.symbols U85_2.U :=
  ⟨blank_85_2.2.2.2.trans U85_2.U_counts.1, blank_85_2.2.1.trans U85_2.U_counts.2,
    zero_mem_symbols blank_85_2.1⟩

theorem count_3_600 :
    NStatesMorita U3_600.U = 3 ∧ NSymsMorita U3_600.U = 600 ∧ 0 ∈ Spec.symbols U3_600.U :=
  ⟨blank_3_600.2.2.2.trans U3_600.U_counts.1, blank_3_600.2.1.trans U3_600.U_counts.2,
    zero_mem_symbols blank_3_600.1⟩

/-! ### Existence with Morita's counts -/

theorem exists_urtm_10_8_moritaCount :
    ∃ U : List Quint, Spec.Deterministic U ∧ Spec.Reversible U ∧
    NStatesMorita U = 10 ∧ NSymsMorita U = 8 ∧ 0 ∈ Spec.symbols U ∧ Spec.IsUTMStrict U :=
  ⟨B10_8, B10_8_det, B10_8_rev, count_book_10_8.1, count_book_10_8.2.1, count_book_10_8.2.2, isUTMStrict_B10_8⟩

theorem exists_urtm_13_7_moritaCount :
    ∃ U : List Quint, Spec.Deterministic U ∧ Spec.Reversible U ∧
    NStatesMorita U = 13 ∧ NSymsMorita U = 7 ∧ 0 ∈ Spec.symbols U ∧ Spec.IsUTMStrict U :=
  ⟨B13_7, B13_7_det, B13_7_rev, count_book_13_7.1, count_book_13_7.2.1, count_book_13_7.2.2, isUTMStrict_B13_7⟩

theorem exists_urtm_15_6_moritaCount :
    ∃ U : List Quint, Spec.Deterministic U ∧ Spec.Reversible U ∧
    NStatesMorita U = 15 ∧ NSymsMorita U = 6 ∧ 0 ∈ Spec.symbols U ∧ Spec.IsUTMStrict U :=
  ⟨B15_6, B15_6_det, B15_6_rev, count_book_15_6.1, count_book_15_6.2.1, count_book_15_6.2.2, isUTMStrict_B15_6⟩

theorem exists_urtm_17_5_moritaCount :
    ∃ U : List Quint, Spec.Deterministic U ∧ Spec.Reversible U ∧
    NStatesMorita U = 17 ∧ NSymsMorita U = 5 ∧ 0 ∈ Spec.symbols U ∧ Spec.IsUTMStrict U :=
  ⟨B17_5, B17_5_det, B17_5_rev, count_book_17_5.1, count_book_17_5.2.1, count_book_17_5.2.2, isUTMStrict_B17_5⟩

theorem exists_urtm_24_4_moritaCount :
    ∃ U : List Quint, Spec.Deterministic U ∧ Spec.Reversible U ∧
    NStatesMorita U = 24 ∧ NSymsMorita U = 4 ∧ 0 ∈ Spec.symbols U ∧ Spec.IsUTMStrict U :=
  ⟨B24_4, B24_4_det, B24_4_rev, count_book_24_4.1, count_book_24_4.2.1, count_book_24_4.2.2, isUTMStrict_B24_4⟩

theorem exists_urtm_32_3_moritaCount :
    ∃ U : List Quint, Spec.Deterministic U ∧ Spec.Reversible U ∧
    NStatesMorita U = 32 ∧ NSymsMorita U = 3 ∧ 0 ∈ Spec.symbols U ∧ Spec.IsUTMStrict U :=
  ⟨B32_3, B32_3_det, B32_3_rev, count_book_32_3.1, count_book_32_3.2.1, count_book_32_3.2.2, isUTMStrict_B32_3⟩

theorem exists_urtm_4_46_moritaCount :
    ∃ U : List Quint, Spec.Deterministic U ∧ Spec.Reversible U ∧
    NStatesMorita U = 4 ∧ NSymsMorita U = 46 ∧ 0 ∈ Spec.symbols U ∧ Spec.IsUTMStrict U :=
  ⟨B4_46, B4_46_det, B4_46_rev, count_book_4_46.1, count_book_4_46.2.1, count_book_4_46.2.2, isUTMStrict_B4_46⟩

theorem exists_urtm_5_45_moritaCount :
    ∃ U : List Quint, Spec.Deterministic U ∧ Spec.Reversible U ∧
    NStatesMorita U = 5 ∧ NSymsMorita U = 45 ∧ 0 ∈ Spec.symbols U ∧ Spec.IsUTMStrict U :=
  ⟨B5_45, B5_45_det, B5_45_rev, count_book_5_45.1, count_book_5_45.2.1, count_book_5_45.2.2, isUTMStrict_B5_45⟩

theorem exists_urtm_6_37_moritaCount :
    ∃ U : List Quint, Spec.Deterministic U ∧ Spec.Reversible U ∧
    NStatesMorita U = 6 ∧ NSymsMorita U = 37 ∧ 0 ∈ Spec.symbols U ∧ Spec.IsUTMStrict U :=
  ⟨B6_37, B6_37_det, B6_37_rev, count_book_6_37.1, count_book_6_37.2.1, count_book_6_37.2.2, isUTMStrict_B6_37⟩

theorem exists_urtm_7_32_moritaCount :
    ∃ U : List Quint, Spec.Deterministic U ∧ Spec.Reversible U ∧
    NStatesMorita U = 7 ∧ NSymsMorita U = 32 ∧ 0 ∈ Spec.symbols U ∧ Spec.IsUTMStrict U :=
  ⟨B7_32, B7_32_det, B7_32_rev, count_book_7_32.1, count_book_7_32.2.1, count_book_7_32.2.2, isUTMStrict_B7_32⟩

theorem exists_urtm_8_28_moritaCount :
    ∃ U : List Quint, Spec.Deterministic U ∧ Spec.Reversible U ∧
    NStatesMorita U = 8 ∧ NSymsMorita U = 28 ∧ 0 ∈ Spec.symbols U ∧ Spec.IsUTMStrict U :=
  ⟨B8_28, B8_28_det, B8_28_rev, count_book_8_28.1, count_book_8_28.2.1, count_book_8_28.2.2, isUTMStrict_B8_28⟩

theorem exists_urtm_9_27_moritaCount :
    ∃ U : List Quint, Spec.Deterministic U ∧ Spec.Reversible U ∧
    NStatesMorita U = 9 ∧ NSymsMorita U = 27 ∧ 0 ∈ Spec.symbols U ∧ Spec.IsUTMStrict U :=
  ⟨B9_27, B9_27_det, B9_27_rev, count_book_9_27.1, count_book_9_27.2.1, count_book_9_27.2.2, isUTMStrict_B9_27⟩

theorem exists_urtm_85_2_moritaCount :
    ∃ U : List Quint, Spec.Deterministic U ∧ Spec.Reversible U ∧
    NStatesMorita U = 85 ∧ NSymsMorita U = 2 ∧ 0 ∈ Spec.symbols U ∧ Spec.IsUTMStrict U :=
  ⟨U85_2.U, U85_2.U_det, U85_2.U_rev, count_85_2.1, count_85_2.2.1, count_85_2.2.2, U85_2.isUTMStrict_U⟩

theorem exists_urtm_3_600_moritaCount :
    ∃ U : List Quint, Spec.Deterministic U ∧ Spec.Reversible U ∧
    NStatesMorita U = 3 ∧ NSymsMorita U = 600 ∧ 0 ∈ Spec.symbols U ∧ Spec.IsUTMStrict U :=
  ⟨U3_600.U, U3_600.U_det, U3_600.U_rev, count_3_600.1, count_3_600.2.1, count_3_600.2.2, U3_600.isUTMStrict_U⟩

/-! ### The description-file tables: the two pseudo-states are counted -/

theorem count_desc_10_8 :
    NStatesMorita U10_8.U = 10 + 2 ∧ NSymsMorita U10_8.U = 8 := by
  decide +kernel

theorem count_desc_13_7 :
    NStatesMorita U13_7.U = 13 + 2 ∧ NSymsMorita U13_7.U = 7 := by
  decide +kernel

theorem count_desc_15_6 :
    NStatesMorita U15_6.U = 15 + 2 ∧ NSymsMorita U15_6.U = 6 := by
  decide +kernel

theorem count_desc_17_5 :
    NStatesMorita U17_5.U = 17 + 2 ∧ NSymsMorita U17_5.U = 5 := by
  decide +kernel

theorem count_desc_24_4 :
    NStatesMorita U24_4.U = 24 + 2 ∧ NSymsMorita U24_4.U = 4 := by
  decide +kernel

theorem count_desc_32_3 :
    NStatesMorita U32_3.U = 32 + 2 ∧ NSymsMorita U32_3.U = 3 := by
  decide +kernel

theorem count_desc_4_46 :
    NStatesMorita U4_46.U = 4 + 2 ∧ NSymsMorita U4_46.U = 46 := by
  decide +kernel

theorem count_desc_5_45 :
    NStatesMorita U5_45.U = 5 + 2 ∧ NSymsMorita U5_45.U = 45 := by
  decide +kernel

theorem count_desc_6_37 :
    NStatesMorita U6_37.U = 6 + 2 ∧ NSymsMorita U6_37.U = 37 := by
  decide +kernel

theorem count_desc_7_32 :
    NStatesMorita U7_32.U = 7 + 2 ∧ NSymsMorita U7_32.U = 32 := by
  decide +kernel

theorem count_desc_8_28 :
    NStatesMorita U8_28.U = 8 + 2 ∧ NSymsMorita U8_28.U = 28 := by
  decide +kernel

theorem count_desc_9_27 :
    NStatesMorita U9_27.U = 9 + 2 ∧ NSymsMorita U9_27.U = 27 := by
  decide +kernel

end URTM.Univ.FinalMoritaCount
