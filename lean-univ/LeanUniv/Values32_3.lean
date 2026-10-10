/-
  **The 3-state conversion of (32,3), step by step** (the materials of `FinalValues`; the values 18476, 1820
  and 659 of the paper's table on the 3-state and 2-symbol conversions, and 600 as an equality).

  * 18476: Morita's 1WU machine `That` (Lemma 5.9, `CTSH3_36654Main`), Morita's numbering `idx3`, and the
    3-state conversion with ↑ and ↓ merged and every counter kept (`Conv3P.conv` with `need x = 61 = M − 1`).
  * 1820: the same 1WU machine and conversion, with the numbering and the counter bound `need` of
    `tools/threestate.py` (onewu=pair, counter=pruned, order=auto), imported by `tools/gen_pair3_lean.py`
    (`URTM.Gen.P3_1820`); Lean checks the local hypotheses of `Conv3P` (`Conv3P.Hyp`, `hsrc`).
  * 659: the improved 3-state conversion `Conv3S.conv` (not mirrored) of (32,3) without its halting rules, with
    the parameters of `tools/threestate.py` (onewu=single, counter=pruned, mirror=0), imported by
    `tools/gen_threestate_lean.py --no-mirror` (`URTM.Gen.T3_659`, which also checks that the Lean conversion
    equals the Python table rule by rule).
  * 600: the mirrored conversion (`URTM.Gen.T3_600`), now as an equality.

  No `sorry`, no new axiom, no `native_decide`.
-/
import LeanUniv.SymExact
import URTM.Gen.T3_600
import URTM.Gen.T3_659
import URTM.Gen.P3_1820

set_option maxRecDepth 100000

namespace URTM.Univ.Values32_3

open URTM URTM.KState URTM.Gen.K32_3
open URTM.Univ.SymCount (nsym need3)
open URTM.Univ.SymExact
open URTM.CTSH.U3_36654 (That allW allW_all idx3 hyp510)

theorem allW_length : allW.length = 298 := by decide +kernel

theorem hsrc3 : ∀ r ∈ That, r.p ≠ .L → 1 ≤ idx3 r.p ∧ idx3 r.p < 62 := by decide +kernel

/-- **18476**: ↑ and ↓ merged, every counter `1..61` kept, on Morita's 1WU machine of (32,3). -/
theorem shared_32_3 : nsym (Conv3P.conv That .L .bl idx3 (fun _ => 61) allW) = 298 * 62 := by
  have h := shared_nsym (m := 62) hyp510 hsrc3 URTM.Gen.P3_1820.allW_nodup (by decide)
  rw [allW_length] at h
  exact h

/-- **1820**: the counters cut at `need` (the numbering and `need` of `threestate.py`). -/
theorem pruned_32_3 :
    nsym (Conv3P.conv That .L .bl URTM.Gen.P3_1820.idxP URTM.Gen.P3_1820.needP allW) =
      allW.length + (allW.map URTM.Gen.P3_1820.needP).sum := by
  refine conv3P_nsym (fun _ _ => ⟨allW_all _, allW_all _⟩) hyp510.hshape URTM.Gen.P3_1820.hyp.hidx
    URTM.Gen.P3_1820.hsrc URTM.Gen.P3_1820.allW_nodup (fun _ => ?_)
  decide +kernel

theorem params659 :
    ss.length = 3 ∧ URTM.Gen.T3_659.qm.length = 14 ∧ URTM.Gen.T3_659.Rl.length = 46 ∧
      URTM.Gen.T3_659.Gl.length = 47 := by decide +kernel

theorem need659 : ∀ x ∈ Conv3S.wsyms ss URTM.Gen.T3_659.qm URTM.Gen.T3_659.Gl,
    URTM.Gen.T3_659.need x = need3 3 46 47 x := by decide +kernel

theorem nodup659 : ss.Nodup ∧ URTM.Gen.T3_659.qm.Nodup ∧ URTM.Gen.T3_659.Gl.Nodup := by decide +kernel

/-- **659**: the improved 3-state conversion, not mirrored. -/
theorem three_659 :
    nsym (Conv3S.conv URTM.Gen.T3_659.T' Sy.s0 ss URTM.Gen.T3_659.qm URTM.Gen.T3_659.Rl URTM.Gen.T3_659.Gl
      URTM.Gen.T3_659.idx URTM.Gen.T3_659.need) = 1 + 3 + (14 * 3 + 47) * (3 + 1) + 3 * (3 + 2 + 46 + 47) + (3 + 2) := by
  obtain ⟨h1, h2, h3, h4⟩ := params659
  have h := conv3S_nsym_eq URTM.Gen.T3_659.hyp URTM.Gen.T3_659.hsrc (by rw [h1, h3, h4]; exact need659)
    nodup659.1 nodup659.2.1 nodup659.2.2
  rw [h1, h2, h3, h4] at h
  exact h

theorem params600 :
    ss.length = 3 ∧ URTM.Gen.T3_600.qmR.length = 18 ∧ URTM.Gen.T3_600.RlR.length = 36 ∧
      URTM.Gen.T3_600.GlR.length = 36 := by decide +kernel

theorem need600 : ∀ x ∈ Conv3S.wsyms ss URTM.Gen.T3_600.qmR URTM.Gen.T3_600.GlR,
    URTM.Gen.T3_600.need x = need3 3 36 36 x := by decide +kernel

theorem nodup600 : ss.Nodup ∧ URTM.Gen.T3_600.qmR.Nodup ∧ URTM.Gen.T3_600.GlR.Nodup := by decide +kernel

/-- **600 as an equality**: the improved 3-state conversion, mirrored. -/
theorem three_600 :
    nsym (Conv3S.convM URTM.Gen.T3_600.T' Sy.s0 ss URTM.Gen.T3_600.qmR URTM.Gen.T3_600.RlR URTM.Gen.T3_600.GlR
      URTM.Gen.T3_600.idx URTM.Gen.T3_600.need) = 1 + 3 + (18 * 3 + 36) * (3 + 1) + 3 * (3 + 2 + 36 + 36) + (3 + 2) := by
  obtain ⟨h1, h2, h3, h4⟩ := params600
  have h := convM3S_nsym_eq URTM.Gen.T3_600.hyp URTM.Gen.T3_600.hsrc (by rw [h1, h3, h4]; exact need600)
    nodup600.1 nodup600.2.1 nodup600.2.2
  rw [h1, h2, h3, h4] at h
  exact h

end URTM.Univ.Values32_3
