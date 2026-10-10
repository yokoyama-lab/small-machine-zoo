/-
  **主定理 26 本の原典の形（文字列上の ID）への移送**（docs/28 (d)）。

  `Final*.exists_urtm_<m>_<n>`（14 本）と `FinalBook.exists_urtm_<m>_<n>_book`（12 本）の結論
  `∃ U, Deterministic U ∧ Reversible U ∧ NStates U = m ∧ NSyms U = n ∧ IsUTMStrict U`
  （両側無限テープの ID）の `IsUTMStrict U` を、文字列上の ID（`ZID` = αqβ）の Def. 7.1
  `Meta.IsUTM_Morita U`（legacy `Morita.lean` の定義の字句どおりの写し）と、その強い形
  `StringID.IsUTM_MoritaStrict U`（c(n, α) ∈ ID(U)、両端の空白に依らない復号）に置き換えた形で述べる。
  仮定は無い（`Deterministic U` は元の定理の結論にある）。
-/
import LeanUniv.StringID
import LeanUniv.Final10_8
import LeanUniv.FinalMorita
import LeanUniv.FinalBlocks
import LeanUniv.Final85_2
import LeanUniv.Final3_600
import LeanUniv.FinalBook

namespace URTM.Univ.FinalString
open URTM URTM.Spec URTM.Univ.StringID
open URTM.Meta (IsUTM_Morita)

/-- 元の形から原典の形へ。 -/
theorem of_strict {m k : ℕ}
    (h : ∃ U : List Quint, Deterministic U ∧ Reversible U ∧ NStates U = m ∧ NSyms U = k ∧
      IsUTMStrict U) :
    ∃ U : List Quint, Deterministic U ∧ Reversible U ∧ NStates U = m ∧ NSyms U = k ∧
      IsUTM_Morita U ∧ IsUTM_MoritaStrict U := by
  obtain ⟨U, hd, hr, hm, hk, hU⟩ := h
  exact ⟨U, hd, hr, hm, hk, isUTM_Morita hd hU, isUTM_MoritaStrict hd hU⟩

theorem exists_urtm_10_8_morita :
    ∃ U : List Quint, Deterministic U ∧ Reversible U ∧ NStates U = 10 ∧ NSyms U = 8 ∧
      IsUTM_Morita U ∧ IsUTM_MoritaStrict U :=
  of_strict URTM.Univ.Final10_8.exists_urtm_10_8

theorem exists_urtm_13_7_morita :
    ∃ U : List Quint, Deterministic U ∧ Reversible U ∧ NStates U = 13 ∧ NSyms U = 7 ∧
      IsUTM_Morita U ∧ IsUTM_MoritaStrict U :=
  of_strict URTM.Univ.FinalMorita.exists_urtm_13_7

theorem exists_urtm_15_6_morita :
    ∃ U : List Quint, Deterministic U ∧ Reversible U ∧ NStates U = 15 ∧ NSyms U = 6 ∧
      IsUTM_Morita U ∧ IsUTM_MoritaStrict U :=
  of_strict URTM.Univ.FinalMorita.exists_urtm_15_6

theorem exists_urtm_17_5_morita :
    ∃ U : List Quint, Deterministic U ∧ Reversible U ∧ NStates U = 17 ∧ NSyms U = 5 ∧
      IsUTM_Morita U ∧ IsUTM_MoritaStrict U :=
  of_strict URTM.Univ.FinalMorita.exists_urtm_17_5

theorem exists_urtm_24_4_morita :
    ∃ U : List Quint, Deterministic U ∧ Reversible U ∧ NStates U = 24 ∧ NSyms U = 4 ∧
      IsUTM_Morita U ∧ IsUTM_MoritaStrict U :=
  of_strict URTM.Univ.FinalMorita.exists_urtm_24_4

theorem exists_urtm_32_3_morita :
    ∃ U : List Quint, Deterministic U ∧ Reversible U ∧ NStates U = 32 ∧ NSyms U = 3 ∧
      IsUTM_Morita U ∧ IsUTM_MoritaStrict U :=
  of_strict URTM.Univ.FinalMorita.exists_urtm_32_3

theorem exists_urtm_4_46_morita :
    ∃ U : List Quint, Deterministic U ∧ Reversible U ∧ NStates U = 4 ∧ NSyms U = 46 ∧
      IsUTM_Morita U ∧ IsUTM_MoritaStrict U :=
  of_strict URTM.Univ.FinalBlocks.exists_urtm_4_46

theorem exists_urtm_5_45_morita :
    ∃ U : List Quint, Deterministic U ∧ Reversible U ∧ NStates U = 5 ∧ NSyms U = 45 ∧
      IsUTM_Morita U ∧ IsUTM_MoritaStrict U :=
  of_strict URTM.Univ.FinalBlocks.exists_urtm_5_45

theorem exists_urtm_6_37_morita :
    ∃ U : List Quint, Deterministic U ∧ Reversible U ∧ NStates U = 6 ∧ NSyms U = 37 ∧
      IsUTM_Morita U ∧ IsUTM_MoritaStrict U :=
  of_strict URTM.Univ.FinalBlocks.exists_urtm_6_37

theorem exists_urtm_7_32_morita :
    ∃ U : List Quint, Deterministic U ∧ Reversible U ∧ NStates U = 7 ∧ NSyms U = 32 ∧
      IsUTM_Morita U ∧ IsUTM_MoritaStrict U :=
  of_strict URTM.Univ.FinalBlocks.exists_urtm_7_32

theorem exists_urtm_8_28_morita :
    ∃ U : List Quint, Deterministic U ∧ Reversible U ∧ NStates U = 8 ∧ NSyms U = 28 ∧
      IsUTM_Morita U ∧ IsUTM_MoritaStrict U :=
  of_strict URTM.Univ.FinalBlocks.exists_urtm_8_28

theorem exists_urtm_9_27_morita :
    ∃ U : List Quint, Deterministic U ∧ Reversible U ∧ NStates U = 9 ∧ NSyms U = 27 ∧
      IsUTM_Morita U ∧ IsUTM_MoritaStrict U :=
  of_strict URTM.Univ.FinalBlocks.exists_urtm_9_27

theorem exists_urtm_85_2_morita :
    ∃ U : List Quint, Deterministic U ∧ Reversible U ∧ NStates U = 85 ∧ NSyms U = 2 ∧
      IsUTM_Morita U ∧ IsUTM_MoritaStrict U :=
  of_strict URTM.Univ.Final85_2.exists_urtm_85_2

theorem exists_urtm_3_600_morita :
    ∃ U : List Quint, Deterministic U ∧ Reversible U ∧ NStates U = 3 ∧ NSyms U = 600 ∧
      IsUTM_Morita U ∧ IsUTM_MoritaStrict U :=
  of_strict URTM.Univ.Final3_600.exists_urtm_3_600

theorem exists_urtm_13_7_book_morita :
    ∃ U : List Quint, Deterministic U ∧ Reversible U ∧ NStates U = 13 ∧ NSyms U = 7 ∧
      IsUTM_Morita U ∧ IsUTM_MoritaStrict U :=
  of_strict URTM.Univ.FinalBook.exists_urtm_13_7_book

theorem exists_urtm_15_6_book_morita :
    ∃ U : List Quint, Deterministic U ∧ Reversible U ∧ NStates U = 15 ∧ NSyms U = 6 ∧
      IsUTM_Morita U ∧ IsUTM_MoritaStrict U :=
  of_strict URTM.Univ.FinalBook.exists_urtm_15_6_book

theorem exists_urtm_17_5_book_morita :
    ∃ U : List Quint, Deterministic U ∧ Reversible U ∧ NStates U = 17 ∧ NSyms U = 5 ∧
      IsUTM_Morita U ∧ IsUTM_MoritaStrict U :=
  of_strict URTM.Univ.FinalBook.exists_urtm_17_5_book

theorem exists_urtm_24_4_book_morita :
    ∃ U : List Quint, Deterministic U ∧ Reversible U ∧ NStates U = 24 ∧ NSyms U = 4 ∧
      IsUTM_Morita U ∧ IsUTM_MoritaStrict U :=
  of_strict URTM.Univ.FinalBook.exists_urtm_24_4_book

theorem exists_urtm_32_3_book_morita :
    ∃ U : List Quint, Deterministic U ∧ Reversible U ∧ NStates U = 32 ∧ NSyms U = 3 ∧
      IsUTM_Morita U ∧ IsUTM_MoritaStrict U :=
  of_strict URTM.Univ.FinalBook.exists_urtm_32_3_book

theorem exists_urtm_10_8_book_morita :
    ∃ U : List Quint, Deterministic U ∧ Reversible U ∧ NStates U = 10 ∧ NSyms U = 8 ∧
      IsUTM_Morita U ∧ IsUTM_MoritaStrict U :=
  of_strict URTM.Univ.FinalBook.exists_urtm_10_8_book

theorem exists_urtm_4_46_book_morita :
    ∃ U : List Quint, Deterministic U ∧ Reversible U ∧ NStates U = 4 ∧ NSyms U = 46 ∧
      IsUTM_Morita U ∧ IsUTM_MoritaStrict U :=
  of_strict URTM.Univ.FinalBook.exists_urtm_4_46_book

theorem exists_urtm_5_45_book_morita :
    ∃ U : List Quint, Deterministic U ∧ Reversible U ∧ NStates U = 5 ∧ NSyms U = 45 ∧
      IsUTM_Morita U ∧ IsUTM_MoritaStrict U :=
  of_strict URTM.Univ.FinalBook.exists_urtm_5_45_book

theorem exists_urtm_6_37_book_morita :
    ∃ U : List Quint, Deterministic U ∧ Reversible U ∧ NStates U = 6 ∧ NSyms U = 37 ∧
      IsUTM_Morita U ∧ IsUTM_MoritaStrict U :=
  of_strict URTM.Univ.FinalBook.exists_urtm_6_37_book

theorem exists_urtm_7_32_book_morita :
    ∃ U : List Quint, Deterministic U ∧ Reversible U ∧ NStates U = 7 ∧ NSyms U = 32 ∧
      IsUTM_Morita U ∧ IsUTM_MoritaStrict U :=
  of_strict URTM.Univ.FinalBook.exists_urtm_7_32_book

theorem exists_urtm_8_28_book_morita :
    ∃ U : List Quint, Deterministic U ∧ Reversible U ∧ NStates U = 8 ∧ NSyms U = 28 ∧
      IsUTM_Morita U ∧ IsUTM_MoritaStrict U :=
  of_strict URTM.Univ.FinalBook.exists_urtm_8_28_book

theorem exists_urtm_9_27_book_morita :
    ∃ U : List Quint, Deterministic U ∧ Reversible U ∧ NStates U = 9 ∧ NSyms U = 27 ∧
      IsUTM_Morita U ∧ IsUTM_MoritaStrict U :=
  of_strict URTM.Univ.FinalBook.exists_urtm_9_27_book

end URTM.Univ.FinalString
