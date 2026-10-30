/-
  URTM(3,36654) が可逆であること（Morita 2017, Def. 5.4）。

  これまで (3,36654) の可逆性は Lean に無く、Python の検査器（層2）に頼っていた（決定性だけ `hD3`）。
  ここでは (32,3) の可逆性（`Gen.K32_3.hR`、カーネルの `decide`）から、
  Lemma 5.9 の可逆性の保存（`ConvRev.conv59_rev`）と Lemma 5.10 の可逆性の保存（`ConvRev.conv510_rev`）を経て、
  記述ファイルの 37936 本 `T3` の可逆性を導く（`T3` ⊆ T† は `sub3`）。

  生成モジュールに依存するので、`tools/gen_all_lean.sh`（CI）が書く `URTM.lean` 経由でビルドされる。
  未証明の穴・新規公理・native_decide を使わない。
-/
import URTM.CTSH3_36654Thm
import URTM.ConvRev

namespace URTM.CTSH.U3_36654

open URTM URTM.KState URTM.CTSH URTM.SimLemmas URTM.Gen.K32_3 URTM.Gen.F3_36654 URTM.Gen.V3_36654

/-- qp32 の状態にはどれも右移動で入る規則がある（qp32 の定義そのもの）。 -/
theorem qp32_spec : ∀ p' ∈ qp32, ∃ r ∈ T32', r.q = .go p' ∧ r.d = .R := by
  intro p' hp
  simp only [qp32, List.mem_filter, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at hp
  exact hp.2

/-- T̂（Lemma 5.9 の変換、1580 本）は可逆。 -/
theorem hRhat : Reversible That := ConvRev.conv59_rev (Reversible.mono sub32' hR) qp32_spec

/-- T†（Lemma 5.10 の変換、37936 本）は可逆。 -/
theorem hRdag : Reversible Tdag := ConvRev.conv510_rev hRhat hyp510.hshape hyp510.hinj

/-- **URTM(3,36654)（記述ファイルの 37936 本）は決定的かつ可逆**。 -/
theorem urtm3_36654_det_rev : Deterministic T3 ∧ Reversible T3 :=
  ⟨hD3, Reversible.mono sub3 hRdag⟩

end URTM.CTSH.U3_36654
