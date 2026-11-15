/-
  **URTM(11,7) as a Spec table, and its universality in the sense of Def. 7.1** (2026-11-01).

  `U = numT U13_7.num T11`: Morita's URTM(13,7) (`URTM.Gen.K13_7.T`) with copy_y_2 merged into case_y_2
  and copy_n_2 merged into copy_end, the differences carried by rewriting y or n to N during sweeps
  (`URTM.CTSH.U11_7.T11 = T.map chg`, lean/URTM/CTSH11_7.lean; the table is not written out).
  Same numbering, encoder and readout as URTM(13,7) (`U13_7`): states `q0..q12 ↦ 0..12` (q6 and q9 do
  not occur in `T11`), pseudo-states `null ↦ 13`, `halt ↦ 14`, symbols `s0..s6 ↦ 0..6`.

  Final tapes (`URTM.CTSH.U11_7.finList11`): `(λ, m)`: as for (13,7); `(Y v, 0)`:
  `b · RA(0) · $ · loN(rm) · Y · ϕ₁(v)` in `halt`, where the erased symbols `loN(rm)` are N or n
  (the sweep of case_y_1 stopped halfway). The readout `readM 14 5 0` only counts the separators ∗
  before the mark Y and reads ϕ₁(v) after it, so it is the readout of (13,7).
-/
import LeanUniv.U13_7
import URTM.CTSH11_7

namespace URTM.Univ.U11_7
open URTM URTM.CTSH URTM.Gen.K13_7 URTM.Univ.KToSpec URTM.Univ.NumGen URTM.Univ.MoritaGen
open URTM.CTSH.U13_7 (nm13)
open URTM.CTSH.U11_7 (T11 encC11 finCfg11 finList11 loN urtm11_7_simulates_ctsh)

/-- **URTM(11,7) as a Spec table** (59 quintuples). -/
def U : List Quint := numT U13_7.num T11

/-- The witness is the numbering of `T.map chg` (pinned by `tests/check.sh`). -/
theorem U_def : U = numT U13_7.num (URTM.Gen.K13_7.T.map URTM.CTSH.U11_7.chg) := rfl

theorem U_length : U.length = 59 := by decide +kernel
/-- **Counts**: 11 states, 7 symbols. -/
theorem U_counts : Spec.NStates U = 11 ∧ Spec.NSyms U = 7 := by decide +kernel
theorem U_det : Spec.Deterministic U := by decide +kernel
theorem U_rev : Spec.Reversible U := by decide +kernel

/-- As for (13,7): the quintuples that enter a state without outgoing quintuples are exactly the two
    0-shift halting quintuples. -/
theorem U_halting :
    U.filter (fun r => decide (r.q ∉ U.map Quint.p)) = [⟨0, 0, 0, .Z, 13⟩, ⟨1, 0, 0, .Z, 14⟩] ∧
    ∀ r ∈ U, (r.d = .Z ↔ r.q ∉ U.map Quint.p) := by decide +kernel

theorem hlsN : ∀ c, loN c ≠ Sy.s5 := by intro c; cases c <;> decide

/-- **Body form**: the body of `IsUTMStrict U` for the encoder and decoder of (13,7). -/
theorem body_U : DropGen.StrictBody U
    (ChainGen.cOf (encM (U13_7.num.st (.go .q0)) (U13_7.num.sym .s6) (U13_7.num.sym .s5)))
    (GenDec.dOf (readM (U13_7.num.st (.halt .h1)) (U13_7.num.sym .s5) 0)) := by
  refine strictBody_morita U13_7.num T11 U13_7.lo13 .s5 .s0 .s6 .q0 .h0 .h1 0
    (by decide) (by intro c; cases c <;> decide) U13_7.hls (by decide) (by decide)
    encC11 finCfg11 (fun C w => ?_) urtm11_7_simulates_ctsh
    (fun C mf rm hm => ?_) (fun C v rm => ?_) (by decide +kernel) (by decide +kernel)
  · simp [encC11, URTM.CTSH.U13_7.encC, URTM.CTSH.U13_7.rep, URTM.CTSH.U13_7.tapeList, nm13,
      U13_7.lo13]
  · refine ⟨finList11 C [] mf rm,
      (URTM.CTSH.U13_7.RA nm13 C mf).length + 2 + rm.length, ?_, ?_, ?_⟩
    · simp [finList11, URTM.CTSH.U13_7.tapeList]; omega
    · simp [finCfg11, nm13]
    · have h := count_RA U13_7.lo13 Sy.s5 Sy.s0 U13_7.hls (by decide) C hm
      simp only [finList11, URTM.CTSH.U13_7.tapeList, List.map_nil,
        List.append_nil, List.count_cons, List.count_append]
      rw [show (URTM.CTSH.U13_7.RA nm13 C mf).count Sy.s5 = C.length from h,
        show (rm.map (URTM.CTSH.U13_7.lo nm13)).count Sy.s5 = 0 from count_lo U13_7.lo13 _ U13_7.hls rm]
      simp [nm13]
  · refine ⟨Sy.s0 :: URTM.CTSH.U13_7.RA nm13 C 0 ++ Sy.s6 :: rm.map loN, Sy.s3,
      (URTM.CTSH.U13_7.RA nm13 C 0).length, ?_, ?_, ?_, by decide, by decide, by decide⟩
    · simp; omega
    · simp [finCfg11, finList11, nm13, U13_7.lo13]
    · have h := count_RA U13_7.lo13 Sy.s5 Sy.s0 U13_7.hls (by decide) C (Nat.zero_le _)
      simp only [List.count_cons, List.count_append, List.count_nil]
      rw [show (URTM.CTSH.U13_7.RA nm13 C 0).count Sy.s5 = C.length from h,
        show (rm.map loN).count Sy.s5 = 0 from count_lo loN _ hlsN rm]
      simp

/-- **URTM(11,7) is a UTM in the strict sense of Morita Def. 7.1.** -/
theorem isUTMStrict_U : Spec.IsUTMStrict U :=
  ChainGen.isUTMStrict_of_body_ctsh (encM_primrec _ _ _) (readM_primrec _ _ _) body_U

/-- **Existence of URTM(11,7)** in the exact sense of Morita's Def. 7.1. No hypotheses. -/
theorem exists_urtm_11_7 :
    ∃ U : List Quint, Spec.Deterministic U ∧ Spec.Reversible U ∧ Spec.NStates U = 11 ∧
      Spec.NSyms U = 7 ∧ Spec.IsUTMStrict U :=
  ⟨U, U_det, U_rev, U_counts.1, U_counts.2, isUTMStrict_U⟩

end URTM.Univ.U11_7
