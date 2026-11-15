/-
  **URTM(10,7) as a Spec table, and its universality in the sense of Def. 7.1** (2026-11-02).

  `U = numT U13_7.num T10`: URTM(11,7) (`URTM.CTSH.U11_7.T11`) with cycle_end merged into the merged
  state M of case_y_2 / copy_y_2 and the symbols recoloured at the same time
  (`URTM.CTSH.U10_7.T10 = (T11.flatMap chg).eraseDups`, lean/URTM/CTSH10_7.lean; the table is not
  written out, 57 quintuples). Same numbering and encoder as URTM(13,7) (`U13_7`): states
  `q0..q12 ↦ 0..12` (q6, q9 and q12 do not occur in `T10`), pseudo-states `null ↦ 13`, `halt ↦ 14`,
  symbols `s0..s6 ↦ 0..6`. The symbol `s4` (`N` of (13,7)) is the colour `*_t3` of the found table.

  Final tapes (`URTM.CTSH.U10_7.finList10`): `(λ, m)`: `b · RA10(m) · $ · ϕ₁(rm)` in `null`, where
  `RA10(m)` is `RA(m)` with the separators `∗` after the phase marker written `Y`; `(Y v, 0)`:
  `b · RA(0) · Y · loN(rm) · $ · ϕ₁(v)` in `halt`. The readout `readM2 14 5 3 1` counts the separators
  `∗` and `Y` (one `Y` too many in `halt`, hence `e = 1`) and reads ϕ₁(v) after the last symbol that
  is not y or n, i.e. after the mark `$`. So the decoding differs by halting state only in which
  symbols are counted; the words y, n are read as they are.
-/
import LeanUniv.U13_7
import LeanUniv.MoritaGen2
import URTM.CTSH10_7

namespace URTM.Univ.U10_7
open URTM URTM.CTSH URTM.Gen.K13_7 URTM.Univ.KToSpec URTM.Univ.NumGen URTM.Univ.MoritaGen
  URTM.Univ.MoritaGen2
open URTM.CTSH.U13_7 (nm13)
open URTM.CTSH.U10_7 (T10 RA10 RA10_length tapeList10 rep10 encC10 encC10_eq finList10 finCfg10 gSY
  urtm10_7_simulates_ctsh)

/-- **URTM(10,7) as a Spec table** (57 quintuples). -/
def U : List Quint := numT U13_7.num T10

/-- The witness is the numbering of the image of `T11` under `chg`, duplicates removed
    (pinned by `tests/check.sh`). -/
theorem U_def : U = numT U13_7.num (URTM.CTSH.U11_7.T11.flatMap URTM.CTSH.U10_7.chg).eraseDups := rfl

theorem U_length : U.length = 57 := by decide +kernel
/-- **Counts**: 10 states, 7 symbols. -/
theorem U_counts : Spec.NStates U = 10 ∧ Spec.NSyms U = 7 := by decide +kernel
theorem U_det : Spec.Deterministic U := by decide +kernel
theorem U_rev : Spec.Reversible U := by decide +kernel

/-- As for (13,7): the quintuples that enter a state without outgoing quintuples are exactly the two
    0-shift halting quintuples. -/
theorem U_halting :
    U.filter (fun r => decide (r.q ∉ U.map Quint.p)) = [⟨0, 0, 0, .Z, 13⟩, ⟨1, 0, 0, .Z, 14⟩] ∧
    ∀ r ∈ U, (r.d = .Z ↔ r.q ∉ U.map Quint.p) := by decide +kernel

theorem hls3 : ∀ c, U13_7.lo13 c ≠ Sy.s3 := by intro c; cases c <;> decide
theorem hlsN5 : ∀ c, URTM.CTSH.U11_7.loN c ≠ Sy.s5 := by intro c; cases c <;> decide
theorem hlsN3 : ∀ c, URTM.CTSH.U11_7.loN c ≠ Sy.s3 := by intro c; cases c <;> decide

theorem YNS_count3 {L : List Sy} (hL : ∀ x ∈ L, URTM.CTSH.U13_7.YNS nm13 x) : L.count Sy.s3 = 0 :=
  List.count_eq_zero.mpr fun h => by
    rcases hL _ h with h | h | h <;> simp [nm13] at h

theorem count_map_gSY_5 {L : List Sy} (hL : ∀ x ∈ L, URTM.CTSH.U13_7.YNS nm13 x) :
    (L.map gSY).count Sy.s5 = 0 :=
  List.count_eq_zero.mpr fun h => by
    obtain ⟨x, hx, hxe⟩ := List.mem_map.mp h
    rcases hL x hx with rfl | rfl | rfl <;> simp [gSY, nm13] at hxe

theorem count_map_gSY_3 {L : List Sy} (hL : ∀ x ∈ L, URTM.CTSH.U13_7.YNS nm13 x) :
    (L.map gSY).count Sy.s3 = L.count Sy.s5 := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    have ih := ih fun y hy => hL y (List.mem_cons_of_mem _ hy)
    rcases hL x (List.mem_cons_self ..) with rfl | rfl | rfl <;>
      simp [gSY, nm13, ih]

/-- The rule region at a CTSH step boundary holds as many separators `∗` or `Y` as the rule region of
    (13,7) holds `∗` (exactly `|C|`, `count_RA`). -/
theorem count_RA10 (C : CTSH) (m : ℕ) :
    (RA10 C m).count Sy.s5 + (RA10 C m).count Sy.s3 = (URTM.CTSH.U13_7.RA nm13 C m).count Sy.s5 := by
  have hHi : ∀ x ∈ URTM.CTSH.U13_7.Hi nm13 C m, URTM.CTSH.U13_7.YNS nm13 x :=
    Sim.Hi_mem URTM.CTSH.U13_7.lo_YNS (by simp [URTM.CTSH.U13_7.YNS]) C m
  have hLo : ∀ x ∈ URTM.CTSH.U13_7.Lo nm13 C m, URTM.CTSH.U13_7.YNS nm13 x :=
    Sim.Lo_mem URTM.CTSH.U13_7.lo_YNS (by simp [URTM.CTSH.U13_7.YNS]) C m
  have hP5 : ((prod C m).reverse.map (URTM.CTSH.U13_7.lo nm13)).count Sy.s5 = 0 :=
    count_lo U13_7.lo13 _ U13_7.hls _
  have hP3 : ((prod C m).reverse.map (URTM.CTSH.U13_7.lo nm13)).count Sy.s3 = 0 :=
    count_lo U13_7.lo13 _ hls3 _
  simp only [RA10, URTM.CTSH.U13_7.RA, Sim.RA, URTM.CTSH.U13_7.Hi, URTM.CTSH.U13_7.Lo,
    List.count_append, List.count_cons, count_map_gSY_5 hLo, count_map_gSY_3 hLo, YNS_count3 hHi,
    hP5, hP3]
  simp [nm13]

/-- **Body form**: the body of `IsUTMStrict U` for the encoder of (13,7) and the two-colour readout. -/
theorem body_U : DropGen.StrictBody U
    (ChainGen.cOf (encM (U13_7.num.st (.go .q0)) (U13_7.num.sym .s6) (U13_7.num.sym .s5)))
    (GenDec.dOf (readM2 (U13_7.num.st (.halt .h1)) (U13_7.num.sym .s5) (U13_7.num.sym .s3) 1)) := by
  refine strictBody_morita2 U13_7.num T10 U13_7.lo13 .s5 .s3 .s0 .s6 .q0 .h0 .h1 1
    (by decide) (by intro c; cases c <;> decide) U13_7.hls hls3 (by decide) (by decide) (by decide)
    encC10 finCfg10 (fun C w => ?_) urtm10_7_simulates_ctsh
    (fun C mf rm hm => ?_) (fun C v rm => ?_) (by decide +kernel) (by decide +kernel)
  · rw [encC10_eq]
    simp [URTM.CTSH.U13_7.encC, URTM.CTSH.U13_7.rep, URTM.CTSH.U13_7.tapeList, nm13, U13_7.lo13]
  · refine ⟨finList10 C [] mf rm, (URTM.CTSH.U13_7.RA nm13 C mf).length + 2 + rm.length, ?_, ?_, ?_⟩
    · simp [finList10, tapeList10, RA10_length]; omega
    · simp [finCfg10, nm13]
    · have h : (RA10 C mf).count Sy.s5 + (RA10 C mf).count Sy.s3 = C.length :=
        (count_RA10 C mf).trans (count_RA U13_7.lo13 Sy.s5 Sy.s0 U13_7.hls (by decide) C hm)
      simp only [finList10, tapeList10, List.map_nil, List.append_nil, List.count_cons,
        List.count_append]
      rw [show (rm.map (URTM.CTSH.U13_7.lo nm13)).count Sy.s5 = 0 from count_lo U13_7.lo13 _ U13_7.hls rm,
        show (rm.map (URTM.CTSH.U13_7.lo nm13)).count Sy.s3 = 0 from count_lo U13_7.lo13 _ hls3 rm]
      simp [nm13]
      omega
  · refine ⟨Sy.s0 :: URTM.CTSH.U13_7.RA nm13 C 0 ++ Sy.s3 :: rm.map URTM.CTSH.U11_7.loN, Sy.s6,
      (URTM.CTSH.U13_7.RA nm13 C 0).length, ?_, ?_, ?_, by decide, by decide, by decide⟩
    · simp; omega
    · simp [finCfg10, finList10, nm13, U13_7.lo13]
    · have h := count_RA U13_7.lo13 Sy.s5 Sy.s0 U13_7.hls (by decide) C (Nat.zero_le _)
      have h3 : (URTM.CTSH.U13_7.RA nm13 C 0).count Sy.s3 = 0 := by
        rw [URTM.CTSH.U13_7.RA, Sim.RA_zero, List.count_append]
        rw [YNS_count3 (Sim.Hi_mem URTM.CTSH.U13_7.lo_YNS (by simp [URTM.CTSH.U13_7.YNS]) C 0)]
        simp [nm13]
      simp only [List.count_cons, List.count_append, List.count_nil]
      rw [show (URTM.CTSH.U13_7.RA nm13 C 0).count Sy.s5 = C.length from h, h3,
        show (rm.map URTM.CTSH.U11_7.loN).count Sy.s5 = 0 from count_lo URTM.CTSH.U11_7.loN _ hlsN5 rm,
        show (rm.map URTM.CTSH.U11_7.loN).count Sy.s3 = 0 from count_lo URTM.CTSH.U11_7.loN _ hlsN3 rm]
      simp

/-- **URTM(10,7) is a UTM in the strict sense of Morita Def. 7.1.** -/
theorem isUTMStrict_U : Spec.IsUTMStrict U :=
  ChainGen.isUTMStrict_of_body_ctsh (encM_primrec _ _ _) (readM2_primrec _ _ _ _) body_U

/-- **Existence of URTM(10,7)** in the exact sense of Morita's Def. 7.1. No hypotheses. -/
theorem exists_urtm_10_7 :
    ∃ U : List Quint, Spec.Deterministic U ∧ Spec.Reversible U ∧ Spec.NStates U = 10 ∧
      Spec.NSyms U = 7 ∧ Spec.IsUTMStrict U :=
  ⟨U, U_det, U_rev, U_counts.1, U_counts.2, isUTMStrict_U⟩

end URTM.Univ.U10_7
