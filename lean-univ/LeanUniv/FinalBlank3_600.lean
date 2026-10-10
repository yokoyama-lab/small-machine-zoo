/-
  **空白は表に現れ、記号数・状態数は水増ししていない**（査読の問い: `NSyms U = ({0} ∪ symbols U).dedup.length`
  は、表に現れない空白 0 を数えて記号数を 1 増やしていないか）。

  記録 14 点の証人（書籍本文の表 `Book.B<m>_<n>` 12 台、`U85_2.U`、`U3_600.U`）のそれぞれについて
  * `blank_<…>`: (i) 空白 0 を読む五つ組がある、(ii) `(symbols U).dedup.length = NSyms U`（`NSyms` が足す 0 は
    もともと表にある）、(iii) 表に現れる記号はどれも、ある五つ組が読み、ある五つ組が書く（読むだけ・書くだけの
    記号が無い）、(iv) `(states U).dedup.length = NStates U`（行き先にしか現れない状態が無い）。
  * `exists_urtm_<m>_<n>_blank`: (i)〜(iv) を `exists_urtm_<m>_<n>_book` 等の形に足した存在定理。
  記述ファイル版の 12 台（`U<m>_<n>.U`、疑似状態 `halt`/`null` への五つ組 2 本を含む表）は `blank_desc_<m>_<n>` で
  (i)〜(iii) だけを述べる。疑似状態は行き先にだけ現れるので (iv) は成り立たない（`NStates` はそれを数えない）。

  このモジュールは (3,600) の証人 `U3_600.U` だけを扱う（ほかは `FinalBlank`）。証明はどれも `decide +kernel`（カーネルによる評価）。(3,600) の (iii) だけは、相異なる 600 記号の上で `Bool` の計算として確かめてから `List.mem_dedup` で戻す（素直な形はカーネルで 30 GB を超える）。

  **The blank occurs in every record witness and the counts are not inflated.** For each of the 14
  witnesses: some quintuple reads the blank 0; `NSyms` equals the number of distinct symbols that
  occur in the table; every occurring symbol is both read and written by some quintuple; and
  `NStates` equals the number of distinct states that occur (no target-only state).
-/
import LeanUniv.Final3_600

namespace URTM.Univ.FinalBlank
open URTM

/-! ### The witness `U3_600.U` (1572 quintuples; in its own module because the kernel check takes minutes) -/

-- `dedup` of the 3144 symbol occurrences inside `decide` exceeds the default heartbeat budget
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem blank_3_600 :
    (∃ r ∈ U3_600.U, r.s = 0) ∧ (Spec.symbols U3_600.U).dedup.length = Spec.NSyms U3_600.U ∧
    (∀ x ∈ Spec.symbols U3_600.U, (∃ r ∈ U3_600.U, r.s = x) ∧ (∃ r ∈ U3_600.U, r.t = x)) ∧
    (Spec.states U3_600.U).dedup.length = Spec.NStates U3_600.U := by
  refine ⟨by decide +kernel, by decide +kernel, fun x hx => ?_, by decide +kernel⟩
  -- (iii) naively (every occurrence × every quintuple) exhausts 30 GB in the kernel; checked
  -- instead on the 600 distinct symbols, as a `Bool` computation (about 2.5 min, 22 GB)
  have h : (Spec.symbols U3_600.U).dedup.all (fun x =>
      (U3_600.U.map Quint.s).contains x && (U3_600.U.map Quint.t).contains x) = true := by
    decide +kernel
  have h' := List.all_eq_true.1 h x (List.mem_dedup.2 hx)
  simp only [Bool.and_eq_true, List.contains_iff_mem, List.mem_map] at h'
  exact h'

/-! ### Existence with the blank and the counts read off the table -/

theorem exists_urtm_3_600_blank :
    ∃ U : List Quint, Spec.Deterministic U ∧ Spec.Reversible U ∧
    Spec.NStates U = 3 ∧ Spec.NSyms U = 600 ∧ (∃ r ∈ U, r.s = 0) ∧
    (Spec.symbols U).dedup.length = 600 ∧
    (∀ x ∈ Spec.symbols U, (∃ r ∈ U, r.s = x) ∧ (∃ r ∈ U, r.t = x)) ∧
    (Spec.states U).dedup.length = 3 ∧ Spec.IsUTMStrict U :=
  ⟨U3_600.U, U3_600.U_det, U3_600.U_rev, U3_600.U_counts.1, U3_600.U_counts.2, (blank_3_600).1,
    (blank_3_600).2.1.trans U3_600.U_counts.2, (blank_3_600).2.2.1,
    (blank_3_600).2.2.2.trans U3_600.U_counts.1, U3_600.isUTMStrict_U⟩


end URTM.Univ.FinalBlank
