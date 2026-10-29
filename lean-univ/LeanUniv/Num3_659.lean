/-
  **URTM(3,659) as a Spec table**: numbering, counts, determinism, reversibility.

  `U = numT num T3py`: the 3-state machine `URTM.Gen.T3_659.T3py` (1757 quintuples; the improved
  3-state conversion of docs/09, **not mirrored**, applied to Morita's (32,3) without its halting
  quintuples). The numbering `num` is the one of URTM(3,600) (`LeanUniv/Num3_600.lean`): it is
  defined on all of `Tgt TSt Ps` and `CSym (VSym St Sy)` and is injective, so it serves both tables.
  States `L, R0, R1 ↦ 0, 1, 2`; `pl x ↦ vN x`, `ct x k ↦ 196·(k+1) + vN x`, with
  `bl ↦ 0`, `pl s ↦ 1 + s`, `mk p s ↦ 4 + 3p + s`, `mkp p v ↦ 100 + 3p + v`. The blank is `pl bl ↦ 0`.

  * `U_is_conv`: `U` is the numbering of the value of the general conversion `Conv3S.conv` on
    `dropHalt T` ((32,3) without its halting quintuples), so the witness of `Final3_659` is that table.
  * `U_counts`: 3 states, 659 symbols (`decide +kernel`).
  * `U_det`, `U_rev`: from `Sim3_659.urtm3_659_simulates_ctsh` through the injective numbering.
  * `U_noPseudo`: no halting quintuple and no pseudo-state.
-/
import LeanUniv.Num3_600
import LeanUniv.Sim3_659

namespace URTM.Univ.U3_659
open URTM URTM.Gen.K32_3 URTM.Gen.T3_659 URTM.Univ.KToSpec
open URTM.Univ.U3_600 (num numT_det numT_rev)

/-- **URTM(3,659) as a Spec table** (1757 quintuples), numbered as URTM(3,600). -/
def U : List Quint := numT num T3py

/-- The witness is the numbering of the general conversion `Conv3S.conv` (improved 3-state conversion,
    not mirrored) applied to Morita's (32,3) without its halting quintuples. -/
theorem U_is_conv :
    U = numT num (Conv3S.conv (SimLemmas.dropHalt T) Sy.s0 ss qm Rl Gl idx need) :=
  (congrArg (numT num) URTM.Gen.T3_659.conv_eq_py).symm

set_option maxRecDepth 100000 in
/-- **Counts** (Morita's convention): 3 states, 659 symbols. -/
theorem U_counts : Spec.NStates U = 3 ∧ Spec.NSyms U = 659 := by decide +kernel

theorem U_det : Spec.Deterministic U :=
  numT_det num T3py (URTM.Univ.Sim3_659.urtm3_659_simulates_ctsh [] []).1

theorem U_rev : Spec.Reversible U :=
  numT_rev num T3py (URTM.Univ.Sim3_659.urtm3_659_simulates_ctsh [] []).2.1

set_option maxRecDepth 100000 in
/-- `U` has no halting quintuple and no pseudo-state: every target state has outgoing
    quintuples, and no quintuple is a 0-shift. It halts where no quintuple applies. -/
theorem U_noPseudo : ∀ r ∈ U, r.q ∈ U.map Quint.p ∧ r.d ≠ .Z := by decide +kernel

end URTM.Univ.U3_659
