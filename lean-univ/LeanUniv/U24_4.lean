/-
  **Morita's URTM(24,4) as a Spec table, and its universality in the sense of Def. 7.1**
  (docs/24 P7a).

  `U = numT num T`: the zoo's typed table `URTM.Gen.K24_4.T` (generated from Morita's description
  file `data/urtm/urtm24-4.txt`) numbered by enumeration: real states `q0..q23 ↦ 0..23`,
  pseudo-states `null (h0) ↦ 24`, `halt (h1) ↦ 25`, symbols `s0..s3 ↦ 0..3`
  (`b y n ∗`; blank `b ↦ 0`).

  Final tapes (`URTM.CTSH.U24_4.finList`): `(λ, m)`: `b · RA(m) · b · ϕ₁(rm)` in `null`;
  `(Y v, 0)`: `b · RA(0) · b · ϕ₁(rm) · ∗ · ϕ₁(v)` in `halt` (the rightmost `∗` stands for the
  leading `Y`, so the tape holds `|C| + 1` separators). Readout `MoritaGen.readM 25 3 1`.
-/
import LeanUniv.MoritaGen
import URTM.CTSH24_4Main

namespace URTM.Univ.U24_4
open URTM URTM.CTSH URTM.Gen.K24_4 URTM.Univ.KToSpec URTM.Univ.NumGen URTM.Univ.MoritaGen
open URTM.CTSH.U24_4 (nm24 encC24 finCfg24 urtm24_4_simulates_ctsh)

/-- The numbering of URTM(24,4). -/
def num : Numbering St Ps Sy :=
  numOf qs [.h0, .h1] ss hQ (by intro p; cases p <;> decide) hS

/-- **URTM(24,4) as a Spec table** (84 quintuples). -/
def U : List Quint := numT num T

/-- **Counts** (Morita's convention): 24 states, 4 symbols. -/
theorem U_counts : Spec.NStates U = 24 ∧ Spec.NSyms U = 4 := by decide +kernel
theorem U_det : Spec.Deterministic U := by decide +kernel
theorem U_rev : Spec.Reversible U := by decide +kernel

/-- **The description-file convention** (as for (10,8), `U10_8.U_zeroShift`). Morita's description
    file says: "There are 82 rules (except halting rules) in total. Note that, here, halting states
    "halt" and "null" are added to indicate which case occurred, but they should not be counted as
    the number of states." So `U` is the 82 quintuples plus the two halting quintuples
    `[begin_,b,b,0,null]` and `[case_y_2_,b,b,0,halt]`: the quintuples of `U` that enter a state without
    outgoing quintuples are exactly these two (0-shift, into two different pseudo-states), and
    they are exactly the 0-shift quintuples of `U`. `Spec.NStates` counts the states with outgoing
    quintuples. -/
theorem U_halting :
    U.filter (fun r => decide (r.q ∉ U.map Quint.p)) = [⟨0, 0, 0, .Z, 24⟩, ⟨2, 0, 0, .Z, 25⟩] ∧
    ∀ r ∈ U, (r.d = .Z ↔ r.q ∉ U.map Quint.p) := by decide +kernel

/-- ϕ₁ of the typed machine. -/
abbrev lo24 : Ch → Sy := URTM.CTSH.U24_4.lo nm24

theorem hls : ∀ c, lo24 c ≠ Sy.s3 := by intro c; cases c <;> decide

/-- **Body form** (docs/26): the body of `IsUTMStrict U` for the explicit encoder and decoder. -/
theorem body_U : DropGen.StrictBody U
    (ChainGen.cOf (encM (num.st (.go .q0)) (num.sym .s0) (num.sym .s3)))
    (GenDec.dOf (readM (num.st (.halt .h1)) (num.sym .s3) 1)) := by
  refine strictBody_morita num T lo24 .s3 .s0 .s0 .q0 .h0 .h1 1
    (by decide) (by intro c; cases c <;> decide) hls (by decide) (by decide)
    encC24 finCfg24 (fun C w => ?_) urtm24_4_simulates_ctsh
    (fun C mf rm hm => ?_) (fun C v rm => ?_) (by decide +kernel) (by decide +kernel)
  · simp [encC24, URTM.CTSH.U24_4.encC, URTM.CTSH.U24_4.rep, URTM.CTSH.U24_4.tapeList,
      URTM.CTSH.U24_4.RA, nm24, lo24]
  · refine ⟨URTM.CTSH.U24_4.finList nm24 C [] mf rm,
      (URTM.CTSH.U24_4.RA nm24 C mf).length + 2 + rm.length, ?_, ?_, ?_⟩
    · simp [URTM.CTSH.U24_4.finList, URTM.CTSH.U24_4.tapeList]; omega
    · simp [finCfg24, URTM.CTSH.U24_4.finCfg, nm24]
    · have h := count_RA lo24 Sy.s3 Sy.s0 hls (by decide) C hm
      simp only [URTM.CTSH.U24_4.finList, URTM.CTSH.U24_4.tapeList, List.map_nil,
        List.append_nil, List.count_cons, List.count_append]
      rw [show (URTM.CTSH.U24_4.RA nm24 C mf).count Sy.s3 = C.length from h,
        show (rm.map (URTM.CTSH.U24_4.lo nm24)).count Sy.s3 = 0 from count_lo lo24 _ hls rm]
      simp [nm24]
  · refine ⟨Sy.s0 :: URTM.CTSH.U24_4.RA nm24 C 0 ++ Sy.s0 :: rm.map lo24, Sy.s3,
      (URTM.CTSH.U24_4.RA nm24 C 0).length, ?_, ?_, ?_, by decide, by decide, by decide⟩
    · simp; omega
    · simp [finCfg24, URTM.CTSH.U24_4.finCfg, URTM.CTSH.U24_4.finList, nm24, lo24]
    · have h := count_RA lo24 Sy.s3 Sy.s0 hls (by decide) C (Nat.zero_le _)
      simp only [List.count_cons, List.count_append, List.count_nil]
      rw [show (URTM.CTSH.U24_4.RA nm24 C 0).count Sy.s3 = C.length from h,
        show (rm.map lo24).count Sy.s3 = 0 from count_lo lo24 _ hls rm]
      simp

/-- **URTM(24,4) is a UTM in the strict sense of Morita Def. 7.1.** -/
theorem isUTMStrict_U : Spec.IsUTMStrict U :=
  ChainGen.isUTMStrict_of_body_ctsh (encM_primrec _ _ _) (readM_primrec _ _ _) body_U

end URTM.Univ.U24_4
