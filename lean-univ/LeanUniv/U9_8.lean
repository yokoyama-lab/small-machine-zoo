/-
  **URTM(9,8) as a Spec table, and its universality in the sense of Def. 7.1** (2026-11-05).

  `U = numT num T9`: URTM(10,7) (`URTM.CTSH.U10_7.T10`) with case_y_1 merged into copy_n_3 (the tag
  family L₁) and the symbols recoloured at the same time; the table is `URTM.CTSH.U9_8.T9`
  (lean/URTM/CTSH9_8.lean, 54 quintuples, the output of the joint search written in the state
  coordinates of (13,7)). Numbering: states `q0..q12 ↦ 0..12` (q6, q9, q10 and q12 do not occur in
  `T9`), pseudo-states `null ↦ 13`, `halt ↦ 14`, symbols `s0..s7 ↦ 0..7` (`b y n Y N ∗ $ T`; `N` is the
  colour `*_t3_t3` and `T` the colour `*_t2` of the found table).

  Final tapes (`URTM.CTSH.U9_8.finList9`): `(λ, m)`: `b · RA9(m) · $ · ϕ₁(rm)` in `null`, where `RA9(m)`
  is `RA(m)` with the separators `∗` after the phase marker written `Y` (as for (10,7)); `(Y v, 0)`:
  `b · RA(0) · Y · loN(rm) · $ · ϕ₁(v)` in `halt`. The readout is that of (10,7): `readM2 14 5 3 1`
  counts the separators `∗` and `Y` (one `Y` too many in `halt`, hence `e = 1`) and reads ϕ₁(v) after
  the last symbol that is not y or n, i.e. after the mark `$`.
-/
import LeanUniv.MoritaGen2
import URTM.CTSH9_8

namespace URTM.Univ.U9_8
open URTM URTM.CTSH URTM.Gen.K13_7 URTM.Univ.KToSpec URTM.Univ.NumGen URTM.Univ.MoritaGen
  URTM.Univ.MoritaGen2
open URTM.CTSH.U9_8 (Sy8 ss8 hS8 lo9 T9 RA9 RA9b RA9_length RA9_zero tapeList9 rep9 encC9 encC9_eq
  finList9 finCfg9 gSY YNS lo_YNS urtm9_8_simulates_ctsh)

/-- The numbering of URTM(9,8): states and pseudo-states as for (13,7), symbols `s0..s7 ↦ 0..7`. -/
def num : Numbering St Ps Sy8 :=
  numOf qs [.h0, .h1] ss8 hQ (by intro p; cases p <;> decide) hS8

/-- **URTM(9,8) as a Spec table** (54 quintuples). -/
def U : List Quint := numT num T9

/-- The witness is the numbering of the typed table `T9` (pinned by `tests/check.sh`). -/
theorem U_def : U = numT num URTM.CTSH.U9_8.T9 := rfl

theorem U_length : U.length = 54 := by decide +kernel
/-- **Counts**: 9 states, 8 symbols. -/
theorem U_counts : Spec.NStates U = 9 ∧ Spec.NSyms U = 8 := by decide +kernel
theorem U_det : Spec.Deterministic U := by decide +kernel
theorem U_rev : Spec.Reversible U := by decide +kernel

/-- As for (13,7) and (10,7): the quintuples that enter a state without outgoing quintuples are exactly
    the two 0-shift halting quintuples (`begin` into `null`, the merged state `M₂ = q1` into `halt`). -/
theorem U_halting :
    U.filter (fun r => decide (r.q ∉ U.map Quint.p)) = [⟨0, 0, 0, .Z, 13⟩, ⟨1, 0, 0, .Z, 14⟩] ∧
    ∀ r ∈ U, (r.d = .Z ↔ r.q ∉ U.map Quint.p) := by decide +kernel

theorem hls : ∀ c, lo9 c ≠ Sy8.s5 := by intro c; cases c <;> decide
theorem hls3 : ∀ c, lo9 c ≠ Sy8.s3 := by intro c; cases c <;> decide
theorem hlsN5 : ∀ c, URTM.CTSH.U9_8.loN c ≠ Sy8.s5 := by intro c; cases c <;> decide
theorem hlsN3 : ∀ c, URTM.CTSH.U9_8.loN c ≠ Sy8.s3 := by intro c; cases c <;> decide

theorem YNS_count3 {L : List Sy8} (hL : ∀ x ∈ L, YNS x) : L.count Sy8.s3 = 0 :=
  List.count_eq_zero.mpr fun h => by
    rcases hL _ h with h | h | h <;> simp at h

theorem count_map_gSY_5 {L : List Sy8} (hL : ∀ x ∈ L, YNS x) :
    (L.map gSY).count Sy8.s5 = 0 :=
  List.count_eq_zero.mpr fun h => by
    obtain ⟨x, hx, hxe⟩ := List.mem_map.mp h
    rcases hL x hx with rfl | rfl | rfl <;> simp [gSY] at hxe

theorem count_map_gSY_3 {L : List Sy8} (hL : ∀ x ∈ L, YNS x) :
    (L.map gSY).count Sy8.s3 = L.count Sy8.s5 := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    have ih := ih fun y hy => hL y (List.mem_cons_of_mem _ hy)
    rcases hL x (List.mem_cons_self ..) with rfl | rfl | rfl <;>
      simp [gSY, ih]

/-- The rule region at a CTSH step boundary holds as many separators `∗` or `Y` as the rule region of
    (13,7) holds `∗` (exactly `|C|`, `count_RA`). -/
theorem count_RA9 (C : CTSH) (m : ℕ) :
    (RA9 C m).count Sy8.s5 + (RA9 C m).count Sy8.s3 = (RA9b C m).count Sy8.s5 := by
  have hHi : ∀ x ∈ Sim.Hi lo9 Sy8.s5 C m, YNS x := Sim.Hi_mem lo_YNS (by simp [YNS]) C m
  have hLo : ∀ x ∈ Sim.Lo lo9 Sy8.s5 C m, YNS x := Sim.Lo_mem lo_YNS (by simp [YNS]) C m
  have hP5 : ((prod C m).reverse.map lo9).count Sy8.s5 = 0 := count_lo lo9 _ hls _
  have hP3 : ((prod C m).reverse.map lo9).count Sy8.s3 = 0 := count_lo lo9 _ hls3 _
  simp only [RA9, RA9b, URTM.CTSH.U9_8.Hi9, URTM.CTSH.U9_8.Lo9, Sim.RA, List.count_append,
    List.count_cons, count_map_gSY_5 hLo, count_map_gSY_3 hLo, YNS_count3 hHi, hP5, hP3]
  simp

/-- **Body form**: the body of `IsUTMStrict U` for the encoder of (13,7) and the two-colour readout. -/
theorem body_U : DropGen.StrictBody U
    (ChainGen.cOf (encM (num.st (.go .q0)) (num.sym .s6) (num.sym .s5)))
    (GenDec.dOf (readM2 (num.st (.halt .h1)) (num.sym .s5) (num.sym .s3) 1)) := by
  refine strictBody_morita2 num T9 lo9 .s5 .s3 .s0 .s6 .q0 .h0 .h1 1
    (by decide) (by intro c; cases c <;> decide) hls hls3 (by decide) (by decide) (by decide)
    encC9 finCfg9 (fun C w => ?_) urtm9_8_simulates_ctsh
    (fun C mf rm hm => ?_) (fun C v rm => ?_) (by decide +kernel) (by decide +kernel)
  · exact encC9_eq C w
  · refine ⟨finList9 C [] mf rm, (RA9b C mf).length + 2 + rm.length, ?_, ?_, ?_⟩
    · simp [finList9, tapeList9, RA9_length]; omega
    · simp [finCfg9]
    · have h : (RA9 C mf).count Sy8.s5 + (RA9 C mf).count Sy8.s3 = C.length :=
        (count_RA9 C mf).trans (count_RA lo9 Sy8.s5 Sy8.s0 hls (by decide) C hm)
      simp only [finList9, tapeList9, List.map_nil, List.append_nil, List.count_cons,
        List.count_append]
      rw [show (rm.map lo9).count Sy8.s5 = 0 from count_lo lo9 _ hls rm,
        show (rm.map lo9).count Sy8.s3 = 0 from count_lo lo9 _ hls3 rm]
      simp
      omega
  · refine ⟨Sy8.s0 :: RA9b C 0 ++ Sy8.s3 :: rm.map URTM.CTSH.U9_8.loN, Sy8.s6,
      (RA9b C 0).length, ?_, ?_, ?_, by decide, by decide, by decide⟩
    · simp; omega
    · simp [finCfg9, finList9]
    · have h := count_RA lo9 Sy8.s5 Sy8.s0 hls (by decide) C (Nat.zero_le _)
      have h3 : (RA9b C 0).count Sy8.s3 = 0 := by
        rw [RA9b, Sim.RA_zero, List.count_append]
        rw [YNS_count3 (Sim.Hi_mem lo_YNS (by simp [YNS]) C 0)]
        simp
      simp only [List.count_cons, List.count_append, List.count_nil]
      rw [show (RA9b C 0).count Sy8.s5 = C.length from h, h3,
        show (rm.map URTM.CTSH.U9_8.loN).count Sy8.s5 = 0 from
          count_lo URTM.CTSH.U9_8.loN _ hlsN5 rm,
        show (rm.map URTM.CTSH.U9_8.loN).count Sy8.s3 = 0 from
          count_lo URTM.CTSH.U9_8.loN _ hlsN3 rm]
      simp

/-- **URTM(9,8) is a UTM in the strict sense of Morita Def. 7.1.** -/
theorem isUTMStrict_U : Spec.IsUTMStrict U :=
  ChainGen.isUTMStrict_of_body_ctsh (encM_primrec _ _ _) (readM2_primrec _ _ _ _) body_U

/-- **Existence of URTM(9,8)** in the exact sense of Morita's Def. 7.1. No hypotheses. -/
theorem exists_urtm_9_8 :
    ∃ U : List Quint, Spec.Deterministic U ∧ Spec.Reversible U ∧ Spec.NStates U = 9 ∧
      Spec.NSyms U = 8 ∧ Spec.IsUTMStrict U :=
  ⟨U, U_det, U_rev, U_counts.1, U_counts.2, isUTMStrict_U⟩

end URTM.Univ.U9_8
