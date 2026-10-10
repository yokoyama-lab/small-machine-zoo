/-
  **書籍本文の表（停止の五つ組 2 本を除いた表）そのものの万能性（Morita Def. 7.1）**（docs/26）

  12 点 (13,7)(15,6)(17,5)(24,4)(32,3)(10,8) と、ブロック化の 6 点 (4,46)(5,45)(6,37)(7,32)(8,28)(9,27)。
  `FinalMorita`・`Final10_8`・`FinalBlocks` の証人は Morita の記述ファイルの表（本文の表に、疑似状態
  `halt`/`null` への 0 シフトの五つ組 2 本を足したもの）だった。ここでの証人 `Book.B<m>_<n>` はその 2 本
  `Book.H<m>_<n>` を除いた表 `DropGen.dropT U H` で、書籍本文が `(halt)`・`(null)` と記す欄は五つ組を持たない。
  ブロック化の 6 点は書籍に無い機械なので「本文の表」ではなく、その類比（停止の五つ組の像 2 本を除いた表）。

  * `exists_urtm_<m>_<n>_book`: 依頼の形 `∃ U, Deterministic U ∧ Reversible U ∧ NStates U = m ∧
    NSyms U = n ∧ IsUTMStrict U`（証人は `Book.B<m>_<n>`）。
  * `book_urtm_<m>_<n>`: 証人を名指しした形。`Book.B<m>_<n> = dropT U<m>_<n>.U H`、`H` は記述ファイルの表の
    うち出ていく五つ組を持たない状態へ入る五つ組の全体、五つ組は 2 本少なく、残った五つ組はどれも
    出ていく五つ組を持つ状態へ入る（疑似状態が残らない）。そのうえで決定性・可逆性・状態数・記号数・`IsUTMStrict`。
  状態数・記号数は記述ファイルの表と同じ（除いた 2 本の状態と記号は、ほかの五つ組にも現れる）。

  **Universality (Def. 7.1) of the tables without the two halting quintuples.** No hypotheses.
-/
import LeanUniv.Book

namespace URTM.Univ.FinalBook
open URTM URTM.Spec URTM.Univ.Book URTM.Univ.DropGen

theorem exists_urtm_13_7_book :
    ∃ U : List Quint, Deterministic U ∧ Reversible U ∧ NStates U = 13 ∧ NSyms U = 7 ∧
      IsUTMStrict U :=
  ⟨B13_7, B13_7_det, B13_7_rev, B13_7_counts.1, B13_7_counts.2, isUTMStrict_B13_7⟩

theorem book_urtm_13_7 :
    B13_7 = dropT U13_7.U H13_7 ∧
    H13_7 = U13_7.U.filter (fun r => decide (r.q ∉ U13_7.U.map Quint.p)) ∧
    B13_7.length + 2 = U13_7.U.length ∧ (∀ r ∈ B13_7, r.q ∈ B13_7.map Quint.p) ∧
    Deterministic B13_7 ∧ Reversible B13_7 ∧ NStates B13_7 = 13 ∧ NSyms B13_7 = 7 ∧
      IsUTMStrict B13_7 :=
  ⟨rfl, B13_7_book.1, by decide +kernel, B13_7_book.2.2, B13_7_det, B13_7_rev, B13_7_counts.1,
    B13_7_counts.2, isUTMStrict_B13_7⟩

theorem exists_urtm_15_6_book :
    ∃ U : List Quint, Deterministic U ∧ Reversible U ∧ NStates U = 15 ∧ NSyms U = 6 ∧
      IsUTMStrict U :=
  ⟨B15_6, B15_6_det, B15_6_rev, B15_6_counts.1, B15_6_counts.2, isUTMStrict_B15_6⟩

theorem book_urtm_15_6 :
    B15_6 = dropT U15_6.U H15_6 ∧
    H15_6 = U15_6.U.filter (fun r => decide (r.q ∉ U15_6.U.map Quint.p)) ∧
    B15_6.length + 2 = U15_6.U.length ∧ (∀ r ∈ B15_6, r.q ∈ B15_6.map Quint.p) ∧
    Deterministic B15_6 ∧ Reversible B15_6 ∧ NStates B15_6 = 15 ∧ NSyms B15_6 = 6 ∧
      IsUTMStrict B15_6 :=
  ⟨rfl, B15_6_book.1, by decide +kernel, B15_6_book.2.2, B15_6_det, B15_6_rev, B15_6_counts.1,
    B15_6_counts.2, isUTMStrict_B15_6⟩

theorem exists_urtm_17_5_book :
    ∃ U : List Quint, Deterministic U ∧ Reversible U ∧ NStates U = 17 ∧ NSyms U = 5 ∧
      IsUTMStrict U :=
  ⟨B17_5, B17_5_det, B17_5_rev, B17_5_counts.1, B17_5_counts.2, isUTMStrict_B17_5⟩

theorem book_urtm_17_5 :
    B17_5 = dropT U17_5.U H17_5 ∧
    H17_5 = U17_5.U.filter (fun r => decide (r.q ∉ U17_5.U.map Quint.p)) ∧
    B17_5.length + 2 = U17_5.U.length ∧ (∀ r ∈ B17_5, r.q ∈ B17_5.map Quint.p) ∧
    Deterministic B17_5 ∧ Reversible B17_5 ∧ NStates B17_5 = 17 ∧ NSyms B17_5 = 5 ∧
      IsUTMStrict B17_5 :=
  ⟨rfl, B17_5_book.1, by decide +kernel, B17_5_book.2.2, B17_5_det, B17_5_rev, B17_5_counts.1,
    B17_5_counts.2, isUTMStrict_B17_5⟩

theorem exists_urtm_24_4_book :
    ∃ U : List Quint, Deterministic U ∧ Reversible U ∧ NStates U = 24 ∧ NSyms U = 4 ∧
      IsUTMStrict U :=
  ⟨B24_4, B24_4_det, B24_4_rev, B24_4_counts.1, B24_4_counts.2, isUTMStrict_B24_4⟩

theorem book_urtm_24_4 :
    B24_4 = dropT U24_4.U H24_4 ∧
    H24_4 = U24_4.U.filter (fun r => decide (r.q ∉ U24_4.U.map Quint.p)) ∧
    B24_4.length + 2 = U24_4.U.length ∧ (∀ r ∈ B24_4, r.q ∈ B24_4.map Quint.p) ∧
    Deterministic B24_4 ∧ Reversible B24_4 ∧ NStates B24_4 = 24 ∧ NSyms B24_4 = 4 ∧
      IsUTMStrict B24_4 :=
  ⟨rfl, B24_4_book.1, by decide +kernel, B24_4_book.2.2, B24_4_det, B24_4_rev, B24_4_counts.1,
    B24_4_counts.2, isUTMStrict_B24_4⟩

theorem exists_urtm_32_3_book :
    ∃ U : List Quint, Deterministic U ∧ Reversible U ∧ NStates U = 32 ∧ NSyms U = 3 ∧
      IsUTMStrict U :=
  ⟨B32_3, B32_3_det, B32_3_rev, B32_3_counts.1, B32_3_counts.2, isUTMStrict_B32_3⟩

theorem book_urtm_32_3 :
    B32_3 = dropT U32_3.U H32_3 ∧
    H32_3 = U32_3.U.filter (fun r => decide (r.q ∉ U32_3.U.map Quint.p)) ∧
    B32_3.length + 2 = U32_3.U.length ∧ (∀ r ∈ B32_3, r.q ∈ B32_3.map Quint.p) ∧
    Deterministic B32_3 ∧ Reversible B32_3 ∧ NStates B32_3 = 32 ∧ NSyms B32_3 = 3 ∧
      IsUTMStrict B32_3 :=
  ⟨rfl, B32_3_book.1, by decide +kernel, B32_3_book.2.2, B32_3_det, B32_3_rev, B32_3_counts.1,
    B32_3_counts.2, isUTMStrict_B32_3⟩

theorem exists_urtm_10_8_book :
    ∃ U : List Quint, Deterministic U ∧ Reversible U ∧ NStates U = 10 ∧ NSyms U = 8 ∧
      IsUTMStrict U :=
  ⟨B10_8, B10_8_det, B10_8_rev, B10_8_counts.1, B10_8_counts.2, isUTMStrict_B10_8⟩

theorem book_urtm_10_8 :
    B10_8 = dropT U10_8.U H10_8 ∧
    H10_8 = U10_8.U.filter (fun r => decide (r.q ∉ U10_8.U.map Quint.p)) ∧
    B10_8.length + 2 = U10_8.U.length ∧ (∀ r ∈ B10_8, r.q ∈ B10_8.map Quint.p) ∧
    Deterministic B10_8 ∧ Reversible B10_8 ∧ NStates B10_8 = 10 ∧ NSyms B10_8 = 8 ∧
      IsUTMStrict B10_8 :=
  ⟨rfl, B10_8_book.1, by decide +kernel, B10_8_book.2.2, B10_8_det, B10_8_rev, B10_8_counts.1,
    B10_8_counts.2, isUTMStrict_B10_8⟩

theorem exists_urtm_4_46_book :
    ∃ U : List Quint, Deterministic U ∧ Reversible U ∧ NStates U = 4 ∧ NSyms U = 46 ∧
      IsUTMStrict U :=
  ⟨B4_46, B4_46_det, B4_46_rev, B4_46_counts.1, B4_46_counts.2, isUTMStrict_B4_46⟩

theorem book_urtm_4_46 :
    B4_46 = dropT U4_46.U H4_46 ∧
    H4_46 = U4_46.U.filter (fun r => decide (r.q ∉ U4_46.U.map Quint.p)) ∧
    B4_46.length + 2 = U4_46.U.length ∧ (∀ r ∈ B4_46, r.q ∈ B4_46.map Quint.p) ∧
    Deterministic B4_46 ∧ Reversible B4_46 ∧ NStates B4_46 = 4 ∧ NSyms B4_46 = 46 ∧
      IsUTMStrict B4_46 :=
  ⟨rfl, B4_46_book.1, by decide +kernel, B4_46_book.2.2, B4_46_det, B4_46_rev, B4_46_counts.1,
    B4_46_counts.2, isUTMStrict_B4_46⟩

theorem exists_urtm_5_45_book :
    ∃ U : List Quint, Deterministic U ∧ Reversible U ∧ NStates U = 5 ∧ NSyms U = 45 ∧
      IsUTMStrict U :=
  ⟨B5_45, B5_45_det, B5_45_rev, B5_45_counts.1, B5_45_counts.2, isUTMStrict_B5_45⟩

theorem book_urtm_5_45 :
    B5_45 = dropT U5_45.U H5_45 ∧
    H5_45 = U5_45.U.filter (fun r => decide (r.q ∉ U5_45.U.map Quint.p)) ∧
    B5_45.length + 2 = U5_45.U.length ∧ (∀ r ∈ B5_45, r.q ∈ B5_45.map Quint.p) ∧
    Deterministic B5_45 ∧ Reversible B5_45 ∧ NStates B5_45 = 5 ∧ NSyms B5_45 = 45 ∧
      IsUTMStrict B5_45 :=
  ⟨rfl, B5_45_book.1, by decide +kernel, B5_45_book.2.2, B5_45_det, B5_45_rev, B5_45_counts.1,
    B5_45_counts.2, isUTMStrict_B5_45⟩

theorem exists_urtm_6_37_book :
    ∃ U : List Quint, Deterministic U ∧ Reversible U ∧ NStates U = 6 ∧ NSyms U = 37 ∧
      IsUTMStrict U :=
  ⟨B6_37, B6_37_det, B6_37_rev, B6_37_counts.1, B6_37_counts.2, isUTMStrict_B6_37⟩

theorem book_urtm_6_37 :
    B6_37 = dropT U6_37.U H6_37 ∧
    H6_37 = U6_37.U.filter (fun r => decide (r.q ∉ U6_37.U.map Quint.p)) ∧
    B6_37.length + 2 = U6_37.U.length ∧ (∀ r ∈ B6_37, r.q ∈ B6_37.map Quint.p) ∧
    Deterministic B6_37 ∧ Reversible B6_37 ∧ NStates B6_37 = 6 ∧ NSyms B6_37 = 37 ∧
      IsUTMStrict B6_37 :=
  ⟨rfl, B6_37_book.1, by decide +kernel, B6_37_book.2.2, B6_37_det, B6_37_rev, B6_37_counts.1,
    B6_37_counts.2, isUTMStrict_B6_37⟩

theorem exists_urtm_7_32_book :
    ∃ U : List Quint, Deterministic U ∧ Reversible U ∧ NStates U = 7 ∧ NSyms U = 32 ∧
      IsUTMStrict U :=
  ⟨B7_32, B7_32_det, B7_32_rev, B7_32_counts.1, B7_32_counts.2, isUTMStrict_B7_32⟩

theorem book_urtm_7_32 :
    B7_32 = dropT U7_32.U H7_32 ∧
    H7_32 = U7_32.U.filter (fun r => decide (r.q ∉ U7_32.U.map Quint.p)) ∧
    B7_32.length + 2 = U7_32.U.length ∧ (∀ r ∈ B7_32, r.q ∈ B7_32.map Quint.p) ∧
    Deterministic B7_32 ∧ Reversible B7_32 ∧ NStates B7_32 = 7 ∧ NSyms B7_32 = 32 ∧
      IsUTMStrict B7_32 :=
  ⟨rfl, B7_32_book.1, by decide +kernel, B7_32_book.2.2, B7_32_det, B7_32_rev, B7_32_counts.1,
    B7_32_counts.2, isUTMStrict_B7_32⟩

theorem exists_urtm_8_28_book :
    ∃ U : List Quint, Deterministic U ∧ Reversible U ∧ NStates U = 8 ∧ NSyms U = 28 ∧
      IsUTMStrict U :=
  ⟨B8_28, B8_28_det, B8_28_rev, B8_28_counts.1, B8_28_counts.2, isUTMStrict_B8_28⟩

theorem book_urtm_8_28 :
    B8_28 = dropT U8_28.U H8_28 ∧
    H8_28 = U8_28.U.filter (fun r => decide (r.q ∉ U8_28.U.map Quint.p)) ∧
    B8_28.length + 2 = U8_28.U.length ∧ (∀ r ∈ B8_28, r.q ∈ B8_28.map Quint.p) ∧
    Deterministic B8_28 ∧ Reversible B8_28 ∧ NStates B8_28 = 8 ∧ NSyms B8_28 = 28 ∧
      IsUTMStrict B8_28 :=
  ⟨rfl, B8_28_book.1, by decide +kernel, B8_28_book.2.2, B8_28_det, B8_28_rev, B8_28_counts.1,
    B8_28_counts.2, isUTMStrict_B8_28⟩

theorem exists_urtm_9_27_book :
    ∃ U : List Quint, Deterministic U ∧ Reversible U ∧ NStates U = 9 ∧ NSyms U = 27 ∧
      IsUTMStrict U :=
  ⟨B9_27, B9_27_det, B9_27_rev, B9_27_counts.1, B9_27_counts.2, isUTMStrict_B9_27⟩

theorem book_urtm_9_27 :
    B9_27 = dropT U9_27.U H9_27 ∧
    H9_27 = U9_27.U.filter (fun r => decide (r.q ∉ U9_27.U.map Quint.p)) ∧
    B9_27.length + 2 = U9_27.U.length ∧ (∀ r ∈ B9_27, r.q ∈ B9_27.map Quint.p) ∧
    Deterministic B9_27 ∧ Reversible B9_27 ∧ NStates B9_27 = 9 ∧ NSyms B9_27 = 27 ∧
      IsUTMStrict B9_27 :=
  ⟨rfl, B9_27_book.1, by decide +kernel, B9_27_book.2.2, B9_27_det, B9_27_rev, B9_27_counts.1,
    B9_27_counts.2, isUTMStrict_B9_27⟩

end URTM.Univ.FinalBook
