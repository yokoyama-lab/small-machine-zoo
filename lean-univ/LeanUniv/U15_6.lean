/-
  **Morita's URTM(15,6) as a Spec table, and its universality in the sense of Def. 7.1**
  (docs/24 P7a).

  `U = numT num T`: the zoo's typed table `URTM.Gen.K15_6.T` (generated from Morita's description
  file `data/urtm/urtm15-6.txt`) numbered by enumeration: real states `q0..q14 ↦ 0..14`,
  pseudo-states `halt (h0) ↦ 15`, `null (h1) ↦ 16`, symbols `s0..s5 ↦ 0..5`
  (`b y n ∗ $ yd`; blank `b ↦ 0`).

  Initial and final tapes are those of (17,5) (`URTM.CTSH.U17_5.Core`). Readout
  `MoritaGen.readM 15 3 0`.
-/
import LeanUniv.MoritaGen
import URTM.CTSH15_6Main

namespace URTM.Univ.U15_6
open URTM URTM.CTSH URTM.Gen.K15_6 URTM.Univ.KToSpec URTM.Univ.NumGen URTM.Univ.MoritaGen
open URTM.CTSH.U15_6 (nm15 encC15 finCfg15 urtm15_6_simulates_ctsh)
open URTM.CTSH.U17_5 (Core)

/-- The numbering of URTM(15,6). -/
def num : Numbering St Ps Sy :=
  numOf qs [.h0, .h1] ss hQ (by intro p; cases p <;> decide) hS

/-- **URTM(15,6) as a Spec table** (64 quintuples). -/
def U : List Quint := numT num T

/-- **Counts** (Morita's convention): 15 states, 6 symbols. -/
theorem U_counts : Spec.NStates U = 15 ∧ Spec.NSyms U = 6 := by decide +kernel
theorem U_det : Spec.Deterministic U := by decide +kernel
theorem U_rev : Spec.Reversible U := by decide +kernel

/-- **The description-file convention** (as for (10,8), `U10_8.U_zeroShift`). Morita's description
    file says: "There are 62 rules (except halting rules) in total. Note that, here, halting states
    "halt" and "null" are added to indicate which case occurred, but they should not be counted as
    the number of states." So `U` is the 62 quintuples plus the two halting quintuples
    `[case_y_1_,b,b,0,halt]` and `[case_y_2_,$,$,0,null]`: the quintuples of `U` that enter a state without
    outgoing quintuples are exactly these two (0-shift, into two different pseudo-states), and
    they are exactly the 0-shift quintuples of `U`. `Spec.NStates` counts the states with outgoing
    quintuples. -/
theorem U_halting :
    U.filter (fun r => decide (r.q ∉ U.map Quint.p)) = [⟨1, 0, 0, .Z, 15⟩, ⟨2, 4, 4, .Z, 16⟩] ∧
    ∀ r ∈ U, (r.d = .Z ↔ r.q ∉ U.map Quint.p) := by decide +kernel

/-- ϕ₁ of the typed machine. -/
abbrev lo15 : Ch → Sy := Core.lo nm15.toCore

theorem hls : ∀ c, lo15 c ≠ Sy.s3 := by intro c; cases c <;> decide

/-- **Body form** (docs/26): the body of `IsUTMStrict U` for the explicit encoder and decoder. -/
theorem body_U : DropGen.StrictBody U
    (ChainGen.cOf (encM (num.st (.go .q0)) (num.sym .s4) (num.sym .s3)))
    (GenDec.dOf (readM (num.st (.halt .h0)) (num.sym .s3) 0)) := by
  refine strictBody_morita num T lo15 .s3 .s0 .s4 .q0 .h1 .h0 0
    (by decide) (by intro c; cases c <;> decide) hls (by decide) (by decide)
    encC15 finCfg15 (fun C w => ?_) urtm15_6_simulates_ctsh
    (fun C mf rm hm => ?_) (fun C v rm => ?_) (by decide +kernel) (by decide +kernel)
  · simp [encC15, URTM.CTSH.U15_6.encC, URTM.CTSH.U15_6.rep, Core.rep, Core.tapeList, nm15,
      lo15]
  · refine ⟨Core.finList nm15.toCore C [] mf rm, (Core.RA nm15.toCore C mf).length + 1,
      ?_, ?_, ?_⟩
    · simp [Core.finList, Core.tapeList]
    · simp [finCfg15, URTM.CTSH.U15_6.finCfg, Core.finCfg, nm15]
    · have h := count_RA lo15 Sy.s3 Sy.s0 hls (by decide) C hm
      simp only [Core.finList, Core.tapeList, List.map_nil, List.append_nil, List.count_cons,
        List.count_append, List.count_nil]
      rw [show (Core.RA nm15.toCore C mf).count Sy.s3 = C.length from h,
        show (rm.map (Core.lo nm15.toCore)).count Sy.s3 = 0 from count_lo lo15 _ hls rm]
      simp [nm15]
  · refine ⟨Sy.s0 :: Core.RA nm15.toCore C 0 ++ Sy.s0 :: rm.map lo15, Sy.s4,
      (Core.RA nm15.toCore C 0).length, ?_, ?_, ?_, by decide, by decide, by decide⟩
    · simp; omega
    · simp [finCfg15, URTM.CTSH.U15_6.finCfg, Core.finCfg, Core.finList, nm15, lo15]
    · have h := count_RA lo15 Sy.s3 Sy.s0 hls (by decide) C (Nat.zero_le _)
      simp only [List.count_cons, List.count_append, List.count_nil]
      rw [show (Core.RA nm15.toCore C 0).count Sy.s3 = C.length from h,
        show (rm.map lo15).count Sy.s3 = 0 from count_lo lo15 _ hls rm]
      simp

/-- **URTM(15,6) is a UTM in the strict sense of Morita Def. 7.1.** -/
theorem isUTMStrict_U : Spec.IsUTMStrict U :=
  ChainGen.isUTMStrict_of_body_ctsh (encM_primrec _ _ _) (readM_primrec _ _ _) body_U

end URTM.Univ.U15_6
