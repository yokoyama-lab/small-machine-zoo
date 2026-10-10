/-
  **URTM(10,8) の存在（Morita Def. 7.1 の意味で、計算可能な符号化と復号を含めて）**

  `exists_urtm_10_8`: 状態数 10・記号数 8 の決定的かつ可逆な TM で、`IsUTMStrict`
  （Morita Def. 7.1 そのもの。任意の 1 本テープ TM の任意の ID を、計算可能な符号化 c で
  U の ID に写し、U が停止すればその停止 ID を計算可能な復号 d で元の TM の停止 ID に戻し、
  停止しないなら U も停止しない。c(n,α) が U の ID であることも含む。2026-10-03 から、復号は
  停止 ID の**どの**符号（末尾の空白の数が違うもの）に対しても正しいことを要求する）を満たすものが存在する。
  連鎖は tm n → TRM → 2-TS → CTSH → URTM(10,8)。仮定は無い。

  **Existence of URTM(10,8) in the exact sense of Morita's Def. 7.1**, including computable encoding
  and decoding: there is a deterministic reversible TM with 10 states and 8 symbols satisfying
  `IsUTMStrict`. Chain: tm n → TRM → 2-TS → CTSH → URTM(10,8). No hypotheses.
-/
import LeanUniv.Chain10_8
import LeanUniv.ComputableEnc
import LeanUniv.ComputableDec

namespace URTM.Univ.Final10_8
open URTM URTM.Spec

theorem exists_urtm_10_8 :
    ∃ U : List Quint, Deterministic U ∧ Reversible U ∧ NStates U = 10 ∧ NSyms U = 8 ∧
      IsUTMStrict U :=
  Chain10_8.exists_urtm_10_8_of_computable ComputableEnc.c10_8_computable
    ComputableDec.d10_8_computable

end URTM.Univ.Final10_8
