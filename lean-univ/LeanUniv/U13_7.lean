/-
  **Morita's URTM(13,7) as a Spec table, and its universality in the sense of Def. 7.1**
  (docs/24 P7a).

  `U = numT num T`: the zoo's typed table `URTM.Gen.K13_7.T` (generated from Morita's description
  file `data/urtm/urtm13-7.txt`) numbered by enumeration: real states `q0..q12 ↦ 0..12`,
  pseudo-states `null (h0) ↦ 13`, `halt (h1) ↦ 14`, symbols `s0..s6 ↦ 0..6`
  (`b y n Y N ∗ $`; blank `b ↦ 0`).

  Final tapes (`URTM.CTSH.U13_7.finList`): `(λ, m)`: `b · RA(m) · $ · ϕ₁(rm)` in `null`;
  `(Y v, 0)`: `b · RA(0) · $ · ϕ₁(rm) · Y · ϕ₁(v)` in `halt`. Readout `MoritaGen.readM 14 5 0`.
-/
import LeanUniv.MoritaGen
import URTM.CTSH13_7Main

namespace URTM.Univ.U13_7
open URTM URTM.CTSH URTM.Gen.K13_7 URTM.Univ.KToSpec URTM.Univ.NumGen URTM.Univ.MoritaGen
open URTM.CTSH.U13_7 (nm13 encC13 finCfg13 urtm13_7_simulates_ctsh)

/-- The numbering of URTM(13,7). -/
def num : Numbering St Ps Sy :=
  numOf qs [.h0, .h1] ss hQ (by intro p; cases p <;> decide) hS

/-- **URTM(13,7) as a Spec table** (59 quintuples). -/
def U : List Quint := numT num T

/-- **Counts** (Morita's convention): 13 states, 7 symbols. -/
theorem U_counts : Spec.NStates U = 13 ∧ Spec.NSyms U = 7 := by decide +kernel
theorem U_det : Spec.Deterministic U := by decide +kernel
theorem U_rev : Spec.Reversible U := by decide +kernel

/-- **The description-file convention** (as for (10,8), `U10_8.U_zeroShift`). Morita's description
    file says: "There are 57 rules (except halting rules) in total. Note that, here, halting states
    "halt" and "null" are added to indicate which case occurred, but they should not be counted as
    the number of states." So `U` is the 57 quintuples plus the two halting quintuples
    `[begin_,b,b,0,null]` and `[case_y_1_,b,b,0,halt]`: the quintuples of `U` that enter a state without
    outgoing quintuples are exactly these two (0-shift, into two different pseudo-states), and
    they are exactly the 0-shift quintuples of `U`. `Spec.NStates` counts the states with outgoing
    quintuples. -/
theorem U_halting :
    U.filter (fun r => decide (r.q ∉ U.map Quint.p)) = [⟨0, 0, 0, .Z, 13⟩, ⟨1, 0, 0, .Z, 14⟩] ∧
    ∀ r ∈ U, (r.d = .Z ↔ r.q ∉ U.map Quint.p) := by decide +kernel

/-- ϕ₁ of the typed machine. -/
abbrev lo13 : Ch → Sy := URTM.CTSH.U13_7.lo nm13

theorem hls : ∀ c, lo13 c ≠ Sy.s5 := by intro c; cases c <;> decide

/-- **Body form** (docs/26): the body of `IsUTMStrict U` for the explicit encoder and decoder. -/
theorem body_U : DropGen.StrictBody U
    (ChainGen.cOf (encM (num.st (.go .q0)) (num.sym .s6) (num.sym .s5)))
    (GenDec.dOf (readM (num.st (.halt .h1)) (num.sym .s5) 0)) := by
  refine strictBody_morita num T lo13 .s5 .s0 .s6 .q0 .h0 .h1 0
    (by decide) (by intro c; cases c <;> decide) hls (by decide) (by decide)
    encC13 finCfg13 (fun C w => ?_) urtm13_7_simulates_ctsh
    (fun C mf rm hm => ?_) (fun C v rm => ?_) (by decide +kernel) (by decide +kernel)
  · simp [encC13, URTM.CTSH.U13_7.encC, URTM.CTSH.U13_7.rep, URTM.CTSH.U13_7.tapeList, nm13,
      lo13]
  · refine ⟨URTM.CTSH.U13_7.finList nm13 C [] mf rm,
      (URTM.CTSH.U13_7.RA nm13 C mf).length + 2 + rm.length, ?_, ?_, ?_⟩
    · simp [URTM.CTSH.U13_7.finList, URTM.CTSH.U13_7.tapeList]; omega
    · simp [finCfg13, URTM.CTSH.U13_7.finCfg, nm13]
    · have h := count_RA lo13 Sy.s5 Sy.s0 hls (by decide) C hm
      simp only [URTM.CTSH.U13_7.finList, URTM.CTSH.U13_7.tapeList, List.map_nil,
        List.append_nil, List.count_cons, List.count_append]
      rw [show (URTM.CTSH.U13_7.RA nm13 C mf).count Sy.s5 = C.length from h,
        show (rm.map (URTM.CTSH.U13_7.lo nm13)).count Sy.s5 = 0 from count_lo lo13 _ hls rm]
      simp [nm13]
  · refine ⟨Sy.s0 :: URTM.CTSH.U13_7.RA nm13 C 0 ++ Sy.s6 :: rm.map lo13, Sy.s3,
      (URTM.CTSH.U13_7.RA nm13 C 0).length, ?_, ?_, ?_, by decide, by decide, by decide⟩
    · simp; omega
    · simp [finCfg13, URTM.CTSH.U13_7.finCfg, URTM.CTSH.U13_7.finList, nm13, lo13]
    · have h := count_RA lo13 Sy.s5 Sy.s0 hls (by decide) C (Nat.zero_le _)
      simp only [List.count_cons, List.count_append, List.count_nil]
      rw [show (URTM.CTSH.U13_7.RA nm13 C 0).count Sy.s5 = C.length from h,
        show (rm.map lo13).count Sy.s5 = 0 from count_lo lo13 _ hls rm]
      simp

/-- **URTM(13,7) is a UTM in the strict sense of Morita Def. 7.1.** -/
theorem isUTMStrict_U : Spec.IsUTMStrict U :=
  ChainGen.isUTMStrict_of_body_ctsh (encM_primrec _ _ _) (readM_primrec _ _ _) body_U

end URTM.Univ.U13_7
