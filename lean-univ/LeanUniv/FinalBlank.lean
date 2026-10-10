/-
  **空白は表に現れ、記号数・状態数は水増ししていない**（査読の問い: `NSyms U = ({0} ∪ symbols U).dedup.length`
  は、表に現れない空白 0 を数えて記号数を 1 増やしていないか）。

  記録 14 点の証人（停止の五つ組 2 本を除いた表 `Book.B<m>_<n>` 12 台、`U85_2.U`、`U3_600.U`）のそれぞれについて。
  `Book.B<m>_<n>` のうち Morita の 6 台（(10,8)(13,7)(15,6)(17,5)(24,4)(32,3)）は書籍本文の表そのもの、
  ブロック化の 6 台（(4,46)(5,45)(6,37)(7,32)(8,28)(9,27)）は書籍に無い機械なので、その類比（ブロック化から
  停止の五つ組 2 本の像を除いた表。`Book.lean` の冒頭）。
  * `blank_<…>`: (i) 空白 0 を読む五つ組がある、(ii) `(symbols U).dedup.length = NSyms U`（`NSyms` が足す 0 は
    もともと表にある）、(iii) 表に現れる記号はどれも、ある五つ組が読み、ある五つ組が書く（読むだけ・書くだけの
    記号が無い）、(iv) `(states U).dedup.length = NStates U`（行き先にしか現れない状態が無い）。
  * `exists_urtm_<m>_<n>_blank`: (i)〜(iv) を `exists_urtm_<m>_<n>_book` 等の形に足した存在定理。
  記述ファイル版の 12 台（`U<m>_<n>.U`、疑似状態 `halt`/`null` への五つ組 2 本を含む表）は `blank_desc_<m>_<n>` で
  (i)〜(iii) だけを述べる。疑似状態は行き先にだけ現れるので (iv) は成り立たない（`NStates` はそれを数えない）。

  (3,600) の証人 `U3_600.U` の 2 本は `FinalBlank3_600`（カーネルの検査に数分かかるので別のモジュール）。証明はどれも `decide +kernel`（カーネルによる評価）。(3,600) の (iii) だけは、相異なる 600 記号の上で `Bool` の計算として確かめてから `List.mem_dedup` で戻す（素直な形はカーネルで 30 GB を超える）。

  **The blank occurs in every record witness and the counts are not inflated.** For each of the 14
  witnesses: some quintuple reads the blank 0; `NSyms` equals the number of distinct symbols that
  occur in the table; every occurring symbol is both read and written by some quintuple; and
  `NStates` equals the number of distinct states that occur (no target-only state).
-/
import LeanUniv.FinalBook
import LeanUniv.Final85_2
import LeanUniv.FinalMorita
import LeanUniv.FinalBlocks
import LeanUniv.Final10_8

namespace URTM.Univ.FinalBlank
open URTM URTM.Univ.Book

/-! ### The 14 record witnesses -/

theorem blank_book_10_8 :
    (∃ r ∈ B10_8, r.s = 0) ∧ (Spec.symbols B10_8).dedup.length = Spec.NSyms B10_8 ∧
    (∀ x ∈ Spec.symbols B10_8, (∃ r ∈ B10_8, r.s = x) ∧ (∃ r ∈ B10_8, r.t = x)) ∧
    (Spec.states B10_8).dedup.length = Spec.NStates B10_8 := by
  decide +kernel

theorem blank_book_13_7 :
    (∃ r ∈ B13_7, r.s = 0) ∧ (Spec.symbols B13_7).dedup.length = Spec.NSyms B13_7 ∧
    (∀ x ∈ Spec.symbols B13_7, (∃ r ∈ B13_7, r.s = x) ∧ (∃ r ∈ B13_7, r.t = x)) ∧
    (Spec.states B13_7).dedup.length = Spec.NStates B13_7 := by
  decide +kernel

theorem blank_book_15_6 :
    (∃ r ∈ B15_6, r.s = 0) ∧ (Spec.symbols B15_6).dedup.length = Spec.NSyms B15_6 ∧
    (∀ x ∈ Spec.symbols B15_6, (∃ r ∈ B15_6, r.s = x) ∧ (∃ r ∈ B15_6, r.t = x)) ∧
    (Spec.states B15_6).dedup.length = Spec.NStates B15_6 := by
  decide +kernel

theorem blank_book_17_5 :
    (∃ r ∈ B17_5, r.s = 0) ∧ (Spec.symbols B17_5).dedup.length = Spec.NSyms B17_5 ∧
    (∀ x ∈ Spec.symbols B17_5, (∃ r ∈ B17_5, r.s = x) ∧ (∃ r ∈ B17_5, r.t = x)) ∧
    (Spec.states B17_5).dedup.length = Spec.NStates B17_5 := by
  decide +kernel

theorem blank_book_24_4 :
    (∃ r ∈ B24_4, r.s = 0) ∧ (Spec.symbols B24_4).dedup.length = Spec.NSyms B24_4 ∧
    (∀ x ∈ Spec.symbols B24_4, (∃ r ∈ B24_4, r.s = x) ∧ (∃ r ∈ B24_4, r.t = x)) ∧
    (Spec.states B24_4).dedup.length = Spec.NStates B24_4 := by
  decide +kernel

theorem blank_book_32_3 :
    (∃ r ∈ B32_3, r.s = 0) ∧ (Spec.symbols B32_3).dedup.length = Spec.NSyms B32_3 ∧
    (∀ x ∈ Spec.symbols B32_3, (∃ r ∈ B32_3, r.s = x) ∧ (∃ r ∈ B32_3, r.t = x)) ∧
    (Spec.states B32_3).dedup.length = Spec.NStates B32_3 := by
  decide +kernel

theorem blank_book_4_46 :
    (∃ r ∈ B4_46, r.s = 0) ∧ (Spec.symbols B4_46).dedup.length = Spec.NSyms B4_46 ∧
    (∀ x ∈ Spec.symbols B4_46, (∃ r ∈ B4_46, r.s = x) ∧ (∃ r ∈ B4_46, r.t = x)) ∧
    (Spec.states B4_46).dedup.length = Spec.NStates B4_46 := by
  decide +kernel

theorem blank_book_5_45 :
    (∃ r ∈ B5_45, r.s = 0) ∧ (Spec.symbols B5_45).dedup.length = Spec.NSyms B5_45 ∧
    (∀ x ∈ Spec.symbols B5_45, (∃ r ∈ B5_45, r.s = x) ∧ (∃ r ∈ B5_45, r.t = x)) ∧
    (Spec.states B5_45).dedup.length = Spec.NStates B5_45 := by
  decide +kernel

theorem blank_book_6_37 :
    (∃ r ∈ B6_37, r.s = 0) ∧ (Spec.symbols B6_37).dedup.length = Spec.NSyms B6_37 ∧
    (∀ x ∈ Spec.symbols B6_37, (∃ r ∈ B6_37, r.s = x) ∧ (∃ r ∈ B6_37, r.t = x)) ∧
    (Spec.states B6_37).dedup.length = Spec.NStates B6_37 := by
  decide +kernel

theorem blank_book_7_32 :
    (∃ r ∈ B7_32, r.s = 0) ∧ (Spec.symbols B7_32).dedup.length = Spec.NSyms B7_32 ∧
    (∀ x ∈ Spec.symbols B7_32, (∃ r ∈ B7_32, r.s = x) ∧ (∃ r ∈ B7_32, r.t = x)) ∧
    (Spec.states B7_32).dedup.length = Spec.NStates B7_32 := by
  decide +kernel

theorem blank_book_8_28 :
    (∃ r ∈ B8_28, r.s = 0) ∧ (Spec.symbols B8_28).dedup.length = Spec.NSyms B8_28 ∧
    (∀ x ∈ Spec.symbols B8_28, (∃ r ∈ B8_28, r.s = x) ∧ (∃ r ∈ B8_28, r.t = x)) ∧
    (Spec.states B8_28).dedup.length = Spec.NStates B8_28 := by
  decide +kernel

theorem blank_book_9_27 :
    (∃ r ∈ B9_27, r.s = 0) ∧ (Spec.symbols B9_27).dedup.length = Spec.NSyms B9_27 ∧
    (∀ x ∈ Spec.symbols B9_27, (∃ r ∈ B9_27, r.s = x) ∧ (∃ r ∈ B9_27, r.t = x)) ∧
    (Spec.states B9_27).dedup.length = Spec.NStates B9_27 := by
  decide +kernel

theorem blank_85_2 :
    (∃ r ∈ U85_2.U, r.s = 0) ∧ (Spec.symbols U85_2.U).dedup.length = Spec.NSyms U85_2.U ∧
    (∀ x ∈ Spec.symbols U85_2.U, (∃ r ∈ U85_2.U, r.s = x) ∧ (∃ r ∈ U85_2.U, r.t = x)) ∧
    (Spec.states U85_2.U).dedup.length = Spec.NStates U85_2.U := by
  decide +kernel

/-! ### Existence with the blank and the counts read off the table -/

theorem exists_urtm_10_8_blank :
    ∃ U : List Quint, Spec.Deterministic U ∧ Spec.Reversible U ∧
    Spec.NStates U = 10 ∧ Spec.NSyms U = 8 ∧ (∃ r ∈ U, r.s = 0) ∧
    (Spec.symbols U).dedup.length = 8 ∧
    (∀ x ∈ Spec.symbols U, (∃ r ∈ U, r.s = x) ∧ (∃ r ∈ U, r.t = x)) ∧
    (Spec.states U).dedup.length = 10 ∧ Spec.IsUTMStrict U :=
  ⟨B10_8, B10_8_det, B10_8_rev, B10_8_counts.1, B10_8_counts.2, (blank_book_10_8).1,
    (blank_book_10_8).2.1.trans B10_8_counts.2, (blank_book_10_8).2.2.1,
    (blank_book_10_8).2.2.2.trans B10_8_counts.1, isUTMStrict_B10_8⟩

theorem exists_urtm_13_7_blank :
    ∃ U : List Quint, Spec.Deterministic U ∧ Spec.Reversible U ∧
    Spec.NStates U = 13 ∧ Spec.NSyms U = 7 ∧ (∃ r ∈ U, r.s = 0) ∧
    (Spec.symbols U).dedup.length = 7 ∧
    (∀ x ∈ Spec.symbols U, (∃ r ∈ U, r.s = x) ∧ (∃ r ∈ U, r.t = x)) ∧
    (Spec.states U).dedup.length = 13 ∧ Spec.IsUTMStrict U :=
  ⟨B13_7, B13_7_det, B13_7_rev, B13_7_counts.1, B13_7_counts.2, (blank_book_13_7).1,
    (blank_book_13_7).2.1.trans B13_7_counts.2, (blank_book_13_7).2.2.1,
    (blank_book_13_7).2.2.2.trans B13_7_counts.1, isUTMStrict_B13_7⟩

theorem exists_urtm_15_6_blank :
    ∃ U : List Quint, Spec.Deterministic U ∧ Spec.Reversible U ∧
    Spec.NStates U = 15 ∧ Spec.NSyms U = 6 ∧ (∃ r ∈ U, r.s = 0) ∧
    (Spec.symbols U).dedup.length = 6 ∧
    (∀ x ∈ Spec.symbols U, (∃ r ∈ U, r.s = x) ∧ (∃ r ∈ U, r.t = x)) ∧
    (Spec.states U).dedup.length = 15 ∧ Spec.IsUTMStrict U :=
  ⟨B15_6, B15_6_det, B15_6_rev, B15_6_counts.1, B15_6_counts.2, (blank_book_15_6).1,
    (blank_book_15_6).2.1.trans B15_6_counts.2, (blank_book_15_6).2.2.1,
    (blank_book_15_6).2.2.2.trans B15_6_counts.1, isUTMStrict_B15_6⟩

theorem exists_urtm_17_5_blank :
    ∃ U : List Quint, Spec.Deterministic U ∧ Spec.Reversible U ∧
    Spec.NStates U = 17 ∧ Spec.NSyms U = 5 ∧ (∃ r ∈ U, r.s = 0) ∧
    (Spec.symbols U).dedup.length = 5 ∧
    (∀ x ∈ Spec.symbols U, (∃ r ∈ U, r.s = x) ∧ (∃ r ∈ U, r.t = x)) ∧
    (Spec.states U).dedup.length = 17 ∧ Spec.IsUTMStrict U :=
  ⟨B17_5, B17_5_det, B17_5_rev, B17_5_counts.1, B17_5_counts.2, (blank_book_17_5).1,
    (blank_book_17_5).2.1.trans B17_5_counts.2, (blank_book_17_5).2.2.1,
    (blank_book_17_5).2.2.2.trans B17_5_counts.1, isUTMStrict_B17_5⟩

theorem exists_urtm_24_4_blank :
    ∃ U : List Quint, Spec.Deterministic U ∧ Spec.Reversible U ∧
    Spec.NStates U = 24 ∧ Spec.NSyms U = 4 ∧ (∃ r ∈ U, r.s = 0) ∧
    (Spec.symbols U).dedup.length = 4 ∧
    (∀ x ∈ Spec.symbols U, (∃ r ∈ U, r.s = x) ∧ (∃ r ∈ U, r.t = x)) ∧
    (Spec.states U).dedup.length = 24 ∧ Spec.IsUTMStrict U :=
  ⟨B24_4, B24_4_det, B24_4_rev, B24_4_counts.1, B24_4_counts.2, (blank_book_24_4).1,
    (blank_book_24_4).2.1.trans B24_4_counts.2, (blank_book_24_4).2.2.1,
    (blank_book_24_4).2.2.2.trans B24_4_counts.1, isUTMStrict_B24_4⟩

theorem exists_urtm_32_3_blank :
    ∃ U : List Quint, Spec.Deterministic U ∧ Spec.Reversible U ∧
    Spec.NStates U = 32 ∧ Spec.NSyms U = 3 ∧ (∃ r ∈ U, r.s = 0) ∧
    (Spec.symbols U).dedup.length = 3 ∧
    (∀ x ∈ Spec.symbols U, (∃ r ∈ U, r.s = x) ∧ (∃ r ∈ U, r.t = x)) ∧
    (Spec.states U).dedup.length = 32 ∧ Spec.IsUTMStrict U :=
  ⟨B32_3, B32_3_det, B32_3_rev, B32_3_counts.1, B32_3_counts.2, (blank_book_32_3).1,
    (blank_book_32_3).2.1.trans B32_3_counts.2, (blank_book_32_3).2.2.1,
    (blank_book_32_3).2.2.2.trans B32_3_counts.1, isUTMStrict_B32_3⟩

theorem exists_urtm_4_46_blank :
    ∃ U : List Quint, Spec.Deterministic U ∧ Spec.Reversible U ∧
    Spec.NStates U = 4 ∧ Spec.NSyms U = 46 ∧ (∃ r ∈ U, r.s = 0) ∧
    (Spec.symbols U).dedup.length = 46 ∧
    (∀ x ∈ Spec.symbols U, (∃ r ∈ U, r.s = x) ∧ (∃ r ∈ U, r.t = x)) ∧
    (Spec.states U).dedup.length = 4 ∧ Spec.IsUTMStrict U :=
  ⟨B4_46, B4_46_det, B4_46_rev, B4_46_counts.1, B4_46_counts.2, (blank_book_4_46).1,
    (blank_book_4_46).2.1.trans B4_46_counts.2, (blank_book_4_46).2.2.1,
    (blank_book_4_46).2.2.2.trans B4_46_counts.1, isUTMStrict_B4_46⟩

theorem exists_urtm_5_45_blank :
    ∃ U : List Quint, Spec.Deterministic U ∧ Spec.Reversible U ∧
    Spec.NStates U = 5 ∧ Spec.NSyms U = 45 ∧ (∃ r ∈ U, r.s = 0) ∧
    (Spec.symbols U).dedup.length = 45 ∧
    (∀ x ∈ Spec.symbols U, (∃ r ∈ U, r.s = x) ∧ (∃ r ∈ U, r.t = x)) ∧
    (Spec.states U).dedup.length = 5 ∧ Spec.IsUTMStrict U :=
  ⟨B5_45, B5_45_det, B5_45_rev, B5_45_counts.1, B5_45_counts.2, (blank_book_5_45).1,
    (blank_book_5_45).2.1.trans B5_45_counts.2, (blank_book_5_45).2.2.1,
    (blank_book_5_45).2.2.2.trans B5_45_counts.1, isUTMStrict_B5_45⟩

theorem exists_urtm_6_37_blank :
    ∃ U : List Quint, Spec.Deterministic U ∧ Spec.Reversible U ∧
    Spec.NStates U = 6 ∧ Spec.NSyms U = 37 ∧ (∃ r ∈ U, r.s = 0) ∧
    (Spec.symbols U).dedup.length = 37 ∧
    (∀ x ∈ Spec.symbols U, (∃ r ∈ U, r.s = x) ∧ (∃ r ∈ U, r.t = x)) ∧
    (Spec.states U).dedup.length = 6 ∧ Spec.IsUTMStrict U :=
  ⟨B6_37, B6_37_det, B6_37_rev, B6_37_counts.1, B6_37_counts.2, (blank_book_6_37).1,
    (blank_book_6_37).2.1.trans B6_37_counts.2, (blank_book_6_37).2.2.1,
    (blank_book_6_37).2.2.2.trans B6_37_counts.1, isUTMStrict_B6_37⟩

theorem exists_urtm_7_32_blank :
    ∃ U : List Quint, Spec.Deterministic U ∧ Spec.Reversible U ∧
    Spec.NStates U = 7 ∧ Spec.NSyms U = 32 ∧ (∃ r ∈ U, r.s = 0) ∧
    (Spec.symbols U).dedup.length = 32 ∧
    (∀ x ∈ Spec.symbols U, (∃ r ∈ U, r.s = x) ∧ (∃ r ∈ U, r.t = x)) ∧
    (Spec.states U).dedup.length = 7 ∧ Spec.IsUTMStrict U :=
  ⟨B7_32, B7_32_det, B7_32_rev, B7_32_counts.1, B7_32_counts.2, (blank_book_7_32).1,
    (blank_book_7_32).2.1.trans B7_32_counts.2, (blank_book_7_32).2.2.1,
    (blank_book_7_32).2.2.2.trans B7_32_counts.1, isUTMStrict_B7_32⟩

theorem exists_urtm_8_28_blank :
    ∃ U : List Quint, Spec.Deterministic U ∧ Spec.Reversible U ∧
    Spec.NStates U = 8 ∧ Spec.NSyms U = 28 ∧ (∃ r ∈ U, r.s = 0) ∧
    (Spec.symbols U).dedup.length = 28 ∧
    (∀ x ∈ Spec.symbols U, (∃ r ∈ U, r.s = x) ∧ (∃ r ∈ U, r.t = x)) ∧
    (Spec.states U).dedup.length = 8 ∧ Spec.IsUTMStrict U :=
  ⟨B8_28, B8_28_det, B8_28_rev, B8_28_counts.1, B8_28_counts.2, (blank_book_8_28).1,
    (blank_book_8_28).2.1.trans B8_28_counts.2, (blank_book_8_28).2.2.1,
    (blank_book_8_28).2.2.2.trans B8_28_counts.1, isUTMStrict_B8_28⟩

theorem exists_urtm_9_27_blank :
    ∃ U : List Quint, Spec.Deterministic U ∧ Spec.Reversible U ∧
    Spec.NStates U = 9 ∧ Spec.NSyms U = 27 ∧ (∃ r ∈ U, r.s = 0) ∧
    (Spec.symbols U).dedup.length = 27 ∧
    (∀ x ∈ Spec.symbols U, (∃ r ∈ U, r.s = x) ∧ (∃ r ∈ U, r.t = x)) ∧
    (Spec.states U).dedup.length = 9 ∧ Spec.IsUTMStrict U :=
  ⟨B9_27, B9_27_det, B9_27_rev, B9_27_counts.1, B9_27_counts.2, (blank_book_9_27).1,
    (blank_book_9_27).2.1.trans B9_27_counts.2, (blank_book_9_27).2.2.1,
    (blank_book_9_27).2.2.2.trans B9_27_counts.1, isUTMStrict_B9_27⟩

theorem exists_urtm_85_2_blank :
    ∃ U : List Quint, Spec.Deterministic U ∧ Spec.Reversible U ∧
    Spec.NStates U = 85 ∧ Spec.NSyms U = 2 ∧ (∃ r ∈ U, r.s = 0) ∧
    (Spec.symbols U).dedup.length = 2 ∧
    (∀ x ∈ Spec.symbols U, (∃ r ∈ U, r.s = x) ∧ (∃ r ∈ U, r.t = x)) ∧
    (Spec.states U).dedup.length = 85 ∧ Spec.IsUTMStrict U :=
  ⟨U85_2.U, U85_2.U_det, U85_2.U_rev, U85_2.U_counts.1, U85_2.U_counts.2, (blank_85_2).1,
    (blank_85_2).2.1.trans U85_2.U_counts.2, (blank_85_2).2.2.1,
    (blank_85_2).2.2.2.trans U85_2.U_counts.1, U85_2.isUTMStrict_U⟩

/-! ### The description-file tables (with the two quintuples into `halt`/`null`) -/

theorem blank_desc_10_8 :
    (∃ r ∈ U10_8.U, r.s = 0) ∧ (Spec.symbols U10_8.U).dedup.length = Spec.NSyms U10_8.U ∧
    (∀ x ∈ Spec.symbols U10_8.U, (∃ r ∈ U10_8.U, r.s = x) ∧ (∃ r ∈ U10_8.U, r.t = x)) := by
  decide +kernel

theorem blank_desc_13_7 :
    (∃ r ∈ U13_7.U, r.s = 0) ∧ (Spec.symbols U13_7.U).dedup.length = Spec.NSyms U13_7.U ∧
    (∀ x ∈ Spec.symbols U13_7.U, (∃ r ∈ U13_7.U, r.s = x) ∧ (∃ r ∈ U13_7.U, r.t = x)) := by
  decide +kernel

theorem blank_desc_15_6 :
    (∃ r ∈ U15_6.U, r.s = 0) ∧ (Spec.symbols U15_6.U).dedup.length = Spec.NSyms U15_6.U ∧
    (∀ x ∈ Spec.symbols U15_6.U, (∃ r ∈ U15_6.U, r.s = x) ∧ (∃ r ∈ U15_6.U, r.t = x)) := by
  decide +kernel

theorem blank_desc_17_5 :
    (∃ r ∈ U17_5.U, r.s = 0) ∧ (Spec.symbols U17_5.U).dedup.length = Spec.NSyms U17_5.U ∧
    (∀ x ∈ Spec.symbols U17_5.U, (∃ r ∈ U17_5.U, r.s = x) ∧ (∃ r ∈ U17_5.U, r.t = x)) := by
  decide +kernel

theorem blank_desc_24_4 :
    (∃ r ∈ U24_4.U, r.s = 0) ∧ (Spec.symbols U24_4.U).dedup.length = Spec.NSyms U24_4.U ∧
    (∀ x ∈ Spec.symbols U24_4.U, (∃ r ∈ U24_4.U, r.s = x) ∧ (∃ r ∈ U24_4.U, r.t = x)) := by
  decide +kernel

theorem blank_desc_32_3 :
    (∃ r ∈ U32_3.U, r.s = 0) ∧ (Spec.symbols U32_3.U).dedup.length = Spec.NSyms U32_3.U ∧
    (∀ x ∈ Spec.symbols U32_3.U, (∃ r ∈ U32_3.U, r.s = x) ∧ (∃ r ∈ U32_3.U, r.t = x)) := by
  decide +kernel

theorem blank_desc_4_46 :
    (∃ r ∈ U4_46.U, r.s = 0) ∧ (Spec.symbols U4_46.U).dedup.length = Spec.NSyms U4_46.U ∧
    (∀ x ∈ Spec.symbols U4_46.U, (∃ r ∈ U4_46.U, r.s = x) ∧ (∃ r ∈ U4_46.U, r.t = x)) := by
  decide +kernel

theorem blank_desc_5_45 :
    (∃ r ∈ U5_45.U, r.s = 0) ∧ (Spec.symbols U5_45.U).dedup.length = Spec.NSyms U5_45.U ∧
    (∀ x ∈ Spec.symbols U5_45.U, (∃ r ∈ U5_45.U, r.s = x) ∧ (∃ r ∈ U5_45.U, r.t = x)) := by
  decide +kernel

theorem blank_desc_6_37 :
    (∃ r ∈ U6_37.U, r.s = 0) ∧ (Spec.symbols U6_37.U).dedup.length = Spec.NSyms U6_37.U ∧
    (∀ x ∈ Spec.symbols U6_37.U, (∃ r ∈ U6_37.U, r.s = x) ∧ (∃ r ∈ U6_37.U, r.t = x)) := by
  decide +kernel

theorem blank_desc_7_32 :
    (∃ r ∈ U7_32.U, r.s = 0) ∧ (Spec.symbols U7_32.U).dedup.length = Spec.NSyms U7_32.U ∧
    (∀ x ∈ Spec.symbols U7_32.U, (∃ r ∈ U7_32.U, r.s = x) ∧ (∃ r ∈ U7_32.U, r.t = x)) := by
  decide +kernel

theorem blank_desc_8_28 :
    (∃ r ∈ U8_28.U, r.s = 0) ∧ (Spec.symbols U8_28.U).dedup.length = Spec.NSyms U8_28.U ∧
    (∀ x ∈ Spec.symbols U8_28.U, (∃ r ∈ U8_28.U, r.s = x) ∧ (∃ r ∈ U8_28.U, r.t = x)) := by
  decide +kernel

theorem blank_desc_9_27 :
    (∃ r ∈ U9_27.U, r.s = 0) ∧ (Spec.symbols U9_27.U).dedup.length = Spec.NSyms U9_27.U ∧
    (∀ x ∈ Spec.symbols U9_27.U, (∃ r ∈ U9_27.U, r.s = x) ∧ (∃ r ∈ U9_27.U, r.t = x)) := by
  decide +kernel

end URTM.Univ.FinalBlank
