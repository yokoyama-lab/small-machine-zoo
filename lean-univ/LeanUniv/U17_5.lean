/-
  **Morita's URTM(17,5) as a Spec table, and its universality in the sense of Def. 7.1**
  (docs/24 P7a).

  `U = numT num T`: the zoo's typed table `URTM.Gen.K17_5.T` (generated from Morita's description
  file `data/urtm/urtm17-5.txt`) numbered by enumeration: real states `q0..q16 ↦ 0..16`,
  pseudo-states `halt (h0) ↦ 17`, `null (h1) ↦ 18`, symbols `s0..s4 ↦ 0..4`
  (`b y n ∗ $`; blank `b ↦ 0`).

  Final tapes (`URTM.CTSH.U17_5.Core.finList`): `(λ, m)`: `b · RA(m) · $ · ϕ₁(rm) · $` in `null`;
  `(Y v, 0)`: `b · RA(0) · b · ϕ₁(rm) · $ · ϕ₁(v)` in `halt` (the `$` stands for the leading `Y`).
  Readout `MoritaGen.readM 17 3 0`.
-/
import LeanUniv.MoritaGen
import URTM.CTSH17_5Main

namespace URTM.Univ.U17_5
open URTM URTM.CTSH URTM.Gen.K17_5 URTM.Univ.KToSpec URTM.Univ.NumGen URTM.Univ.MoritaGen
open URTM.CTSH.U17_5 (nm17 encC17 finCfg17 urtm17_5_simulates_ctsh Core)

/-- The numbering of URTM(17,5). -/
def num : Numbering St Ps Sy :=
  numOf qs [.h0, .h1] ss hQ (by intro p; cases p <;> decide) hS

/-- **URTM(17,5) as a Spec table** (69 quintuples). -/
def U : List Quint := numT num T

/-- **Counts** (Morita's convention): 17 states, 5 symbols. -/
theorem U_counts : Spec.NStates U = 17 ∧ Spec.NSyms U = 5 := by decide +kernel
theorem U_det : Spec.Deterministic U := by decide +kernel
theorem U_rev : Spec.Reversible U := by decide +kernel

/-- **The description-file convention** (as for (10,8), `U10_8.U_zeroShift`). Morita's description
    file says: "There are 67 rules (except halting rules) in total. Note that, here, halting states
    "halt" and "null" are added to indicate which case occurred, but they should not be counted as
    the number of states." So `U` is the 67 quintuples plus the two halting quintuples
    `[case_y_1_,b,b,0,halt]` and `[case_y_2_,$,$,0,null]`: the quintuples of `U` that enter a state without
    outgoing quintuples are exactly these two (0-shift, into two different pseudo-states), and
    they are exactly the 0-shift quintuples of `U`. `Spec.NStates` counts the states with outgoing
    quintuples. -/
theorem U_halting :
    U.filter (fun r => decide (r.q ∉ U.map Quint.p)) = [⟨1, 0, 0, .Z, 17⟩, ⟨2, 4, 4, .Z, 18⟩] ∧
    ∀ r ∈ U, (r.d = .Z ↔ r.q ∉ U.map Quint.p) := by decide +kernel

/-- ϕ₁ of the typed machine. -/
abbrev lo17 : Ch → Sy := Core.lo nm17.toCore

theorem hls : ∀ c, lo17 c ≠ Sy.s3 := by intro c; cases c <;> decide

/-- **Body form** (docs/26): the body of `IsUTMStrict U` for the explicit encoder and decoder. -/
theorem body_U : DropGen.StrictBody U
    (ChainGen.cOf (encM (num.st (.go .q0)) (num.sym .s4) (num.sym .s3)))
    (GenDec.dOf (readM (num.st (.halt .h0)) (num.sym .s3) 0)) := by
  refine strictBody_morita num T lo17 .s3 .s0 .s4 .q0 .h1 .h0 0
    (by decide) (by intro c; cases c <;> decide) hls (by decide) (by decide)
    encC17 finCfg17 (fun C w => ?_) urtm17_5_simulates_ctsh
    (fun C mf rm hm => ?_) (fun C v rm => ?_) (by decide +kernel) (by decide +kernel)
  · simp [encC17, URTM.CTSH.U17_5.encC, URTM.CTSH.U17_5.rep, Core.rep, Core.tapeList, nm17,
      lo17]
  · refine ⟨Core.finList nm17.toCore C [] mf rm, (Core.RA nm17.toCore C mf).length + 1,
      ?_, ?_, ?_⟩
    · simp [Core.finList, Core.tapeList]
    · simp [finCfg17, URTM.CTSH.U17_5.finCfg, Core.finCfg, nm17]
    · have h := count_RA lo17 Sy.s3 Sy.s0 hls (by decide) C hm
      simp only [Core.finList, Core.tapeList, List.map_nil, List.append_nil, List.count_cons,
        List.count_append, List.count_nil]
      rw [show (Core.RA nm17.toCore C mf).count Sy.s3 = C.length from h,
        show (rm.map (Core.lo nm17.toCore)).count Sy.s3 = 0 from count_lo lo17 _ hls rm]
      simp [nm17]
  · refine ⟨Sy.s0 :: Core.RA nm17.toCore C 0 ++ Sy.s0 :: rm.map lo17, Sy.s4,
      (Core.RA nm17.toCore C 0).length, ?_, ?_, ?_, by decide, by decide, by decide⟩
    · simp; omega
    · simp [finCfg17, URTM.CTSH.U17_5.finCfg, Core.finCfg, Core.finList, nm17, lo17]
    · have h := count_RA lo17 Sy.s3 Sy.s0 hls (by decide) C (Nat.zero_le _)
      simp only [List.count_cons, List.count_append, List.count_nil]
      rw [show (Core.RA nm17.toCore C 0).count Sy.s3 = C.length from h,
        show (rm.map lo17).count Sy.s3 = 0 from count_lo lo17 _ hls rm]
      simp

/-- **URTM(17,5) is a UTM in the strict sense of Morita Def. 7.1.** -/
theorem isUTMStrict_U : Spec.IsUTMStrict U :=
  ChainGen.isUTMStrict_of_body_ctsh (encM_primrec _ _ _) (readM_primrec _ _ _) body_U

end URTM.Univ.U17_5
