/-
  3 状態 2 記号の URTM の非存在を、**例外なしで**、本文の 14 点と同じ強い万能性 `IsUTMStrict` の上で述べる。**手書き**。

  `ThreeM.no_three_two_URTM_all`（どの `RTM32` の表も `IsUTM_MoritaOver tbl [sg]` でない）と、
  `ThreeStrict.rtm32_moritaOver_of_strict`（`RTM32` の表が `Spec.IsUTMStrict` なら `IsUTM_MoritaOver tbl [sg]`）の合成。
  `Spec.IsUTMStrict` は lean-univ の存在定理の結論と同じ定義（`Strict.lean`。lean-univ の写しで、字句の一致は検査で見る）。

  既存の定理の文は変えない（追加だけ）。ThreeStrict が ThreeM に依存しないよう、別のファイルに置く。
-/
import URTMMeta.ThreeStrict
import URTMMeta.ThreeM

namespace URTM.Meta
open URTM URTM.TwoState URTM.Three

variable {tbl : List Quint} {q₀ q₁ q₂ sg : Nat}

/-- **主定理**: どの 3 状態 2 記号の RTM（`RTM32 tbl q₀ q₁ q₂ sg`）も `IsUTMStrict` の意味で万能でない。 -/
theorem no_three_two_URTMStrict_all (H : RTM32 tbl q₀ q₁ q₂ sg) : ¬ Spec.IsUTMStrict tbl := fun hU =>
  no_three_two_URTM_all H (rtm32_moritaOver_of_strict H hU)

end URTM.Meta
