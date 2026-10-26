/-
  **URTM(92,2) from (24,4) as a Spec table, and its universality in the sense of Def. 7.1**.

  `U = numT num M`: the 2-symbol machine `URTM.Gen.FS92_2_24_4.M` (176 quintuples; the symbol
  reduction of docs/23 applied to Morita's (24,4), 2 bits per symbol `b 00`, `y 10`, `n 11`,
  `∗ 01`, record `results/fewsym/records/urtm24-4.92.merge.json`), numbered by
  `FewSymGen.numFS`. Not the machine (94,2) of `CTSH94_2Main.lean` (another record from (24,4)).

  Where (24,4) would apply its halting quintuple (`begin` or `case_y_2` reading the blank), `M`
  halts inside the block without writing (`hrunH`, `decide +kernel`): at once for `begin` (state 1),
  after one step to the right for `case_y_2` (state 39, head on the second bit). The readout
  `FewSymGen.readFS` moves the head back by one cell in the state 39, decodes the code in blocks
  of 2 bits and applies the (24,4) readout `MoritaGen.readM` in the state `halt` (25) for the
  state 39 and in `null` (24) otherwise. `isUTMStrict_U` by `FewSymGen.isUTMStrict_fewsym`.
-/
import LeanUniv.FewSymGen
import LeanUniv.U24_4
import URTM.CTSH92_2_24_4Main

namespace URTM.Univ.U92_2_24_4
open URTM URTM.CTSH URTM.Gen.K24_4 URTM.Univ.KToSpec URTM.Univ.NumGen URTM.Univ.MoritaGen
open URTM.Univ.FewSymGen
open URTM.KState (Tgt Cfg Machine HaltsIn)
open URTM.FewSym (enc pre hrun hfuel)
open URTM.Gen.FS92_2_24_4 (M E)
open URTM.CTSH.U92_2_24_4 (f24 urtm92_2_24_4_simulates_ctsh)
open URTM.CTSH.U24_4 (nm24 encC24 finCfg24 RA finList tapeList)
open URTM.Univ.U24_4 (lo24 hls)
open URTM.Univ.U10_8 (loN)

/-! ### Numbering and the Spec table -/

def pn : Ps → ℕ
  | .h0 => 0
  | .h1 => 1

/-- The numbering of URTM(92,2). -/
def num : Numbering ℕ Ps Bool :=
  numFS pn (by intro a b h; cases a <;> cases b <;> first | rfl | exact absurd h (by decide))
    (by intro h; cases h <;> decide)

/-- **URTM(92,2) from (24,4) as a Spec table** (176 quintuples). -/
def U : List Quint := numT num M

/-- **Counts** (Morita's convention): 92 states, 2 symbols. -/
theorem U_counts : Spec.NStates U = 92 ∧ Spec.NSyms U = 2 := by decide +kernel
theorem U_det : Spec.Deterministic U := by decide +kernel
theorem U_rev : Spec.Reversible U := by decide +kernel

/-- `U` has no halting quintuple and no pseudo-state. -/
theorem U_noPseudo : ∀ r ∈ U, r.q ∈ U.map Quint.p ∧ r.d ≠ .Z := by decide +kernel

/-! ### The code and the readout data -/

/-- The code of a (24,4) symbol number, as numbers. -/
def cf (a : ℕ) : List ℕ := [[0, 0], [1, 0], [1, 1], [0, 1]].getD a [0, 0]

/-- The symbol number of (24,4) with the code number `2·b₀ + b₁`. -/
def tab : List ℕ := [0, 3, 1, 2]

/-- The final states of `M`: `ρ begin = 1` (for `null`), `39` (for `halt`, one cell into the
    block of `ρ case_y_2`). -/
def fs : Ps → ℕ
  | .h0 => 1
  | .h1 => 39

def dd : Ps → ℕ
  | .h0 => 0
  | .h1 => 1

/-- The head offset in the final state `39 + 2 = 41`. -/
def off (q : ℕ) : ℕ := if q = 41 then 1 else 0

/-- The state of the (24,4) readout: `halt` (25) for the final state 41, `null` (24) otherwise. -/
def stm (q : ℕ) : ℕ := if q = 41 then 25 else 24

theorem cf_length (a : ℕ) : (cf a).length = 2 := by
  unfold cf
  rcases a with _ | _ | _ | _ | a <;> simp [List.getD]

theorem cf_mem (a b : ℕ) (h : b ∈ cf a) : b = 0 ∨ b = 1 := by
  unfold cf at h
  rcases a with _ | _ | _ | _ | a <;> simp [List.getD] at h <;> omega

open Primrec in
theorem cf_primrec : Primrec cf := (list_getD [0, 0]).comp (const _) .id

open Primrec in
theorem off_primrec : Primrec off :=
  (Primrec.ite (Primrec.eq.comp .id (const 41)) (const 1) (const 0)).of_eq fun _ => rfl

open Primrec in
theorem stm_primrec : Primrec stm :=
  (Primrec.ite (Primrec.eq.comp .id (const 41)) (const 25) (const 24)).of_eq fun _ => rfl

/-- Where (24,4) would apply a halting quintuple, `M` halts inside the block without writing. -/
theorem hrunH (h : Ps) :
    hrun M (hfuel E) ⟨E.ρ (f24 h), E.ce (f24 h), E.code Sy.s0⟩ =
      some ⟨fs h, dd h, E.code Sy.s0⟩ := by
  cases h <;> decide +kernel

/-! ### The base (24,4) -/

theorem hlo : ∀ c, U24_4.num.sym (lo24 c) = loN c := by intro c; cases c <;> decide

theorem henc (C : CTSH) (w : List Ch) :
    encC24 C w = ⟨.go .q0, (((Sim.RA lo24 .s3 .s0 C 0).length + 2 : ℕ) : ℤ),
      Sim.tp .s0 (Sy.s0 :: Sim.RA lo24 .s3 .s0 C 0 ++ Sy.s0 :: w.map lo24)⟩ := by
  simp [encC24, URTM.CTSH.U24_4.encC, URTM.CTSH.U24_4.rep, tapeList, RA, nm24, lo24]

theorem hnullfin (C : CTSH) (mf : ℕ) (rm : List Ch) (hm : mf ≤ C.length) :
    ∃ (L : List Sy) (p : ℕ), p ≤ L.length ∧
      finCfg24 C [] mf rm = ⟨.halt .h0, p, Sim.tp .s0 L⟩ ∧ L.count .s3 = C.length := by
  refine ⟨finList nm24 C [] mf rm, (RA nm24 C mf).length + 2 + rm.length, ?_, ?_, ?_⟩
  · simp [finList, tapeList]; omega
  · simp [finCfg24, URTM.CTSH.U24_4.finCfg, nm24]
  · have h := count_RA lo24 Sy.s3 Sy.s0 hls (by decide) C hm
    simp only [finList, tapeList, List.map_nil, List.append_nil, List.count_cons,
      List.count_append]
    rw [show (RA nm24 C mf).count Sy.s3 = C.length from h,
      show (rm.map (URTM.CTSH.U24_4.lo nm24)).count Sy.s3 = 0 from count_lo lo24 _ hls rm]
    simp [nm24]

theorem hhaltfin (C : CTSH) (v rm : List Ch) :
    ∃ (A : List Sy) (mk : Sy) (p : ℕ), p ≤ (A ++ mk :: v.map lo24).length ∧
      finCfg24 C (.Y :: v) 0 rm = ⟨.halt .h1, p, Sim.tp .s0 (A ++ mk :: v.map lo24)⟩ ∧
      (A ++ [mk]).count .s3 - 1 = C.length ∧ U24_4.num.sym mk ≠ 0 ∧ U24_4.num.sym mk ≠ 1 ∧
      U24_4.num.sym mk ≠ 2 := by
  refine ⟨Sy.s0 :: RA nm24 C 0 ++ Sy.s0 :: rm.map lo24, Sy.s3, (RA nm24 C 0).length,
    ?_, ?_, ?_, by decide, by decide, by decide⟩
  · simp; omega
  · simp [finCfg24, URTM.CTSH.U24_4.finCfg, finList, nm24, lo24]
  · have h := count_RA lo24 Sy.s3 Sy.s0 hls (by decide) C (Nat.zero_le _)
    simp only [List.count_cons, List.count_append, List.count_nil]
    rw [show (RA nm24 C 0).count Sy.s3 = C.length from h,
      show (rm.map lo24).count Sy.s3 = 0 from count_lo lo24 _ hls rm]
    simp

/-- The cell under the head of a final configuration of (24,4) is blank. -/
theorem head24 (C : CTSH) (vf : List Ch) (mf : ℕ) (rm : List Ch) (hf : Halting C (vf, mf)) :
    ∃ h, (finCfg24 C vf mf rm).st = .halt h ∧
      (finCfg24 C vf mf rm).tape (finCfg24 C vf mf rm).pos = Sy.s0 := by
  cases vf with
  | nil =>
    have e : finCfg24 C [] mf rm = ⟨.halt .h0,
        (((finList nm24 C [] mf rm).length : ℕ) : ℤ), Sim.tp .s0 (finList nm24 C [] mf rm)⟩ := by
      simp [finCfg24, URTM.CTSH.U24_4.finCfg, finList, tapeList, nm24]
      omega
    refine ⟨.h0, by rw [e], ?_⟩
    rw [e]
    simp only [Sim.tp_ofNat]
    rw [List.getD_eq_default _ _ (Nat.le_refl _)]
  | cons c v =>
    have hm : mf = 0 := by
      rcases hf.2 with ⟨v', -, h2⟩ | h
      · exact h2
      · simp at h
    subst hm
    have e : finCfg24 C (c :: v) 0 rm = ⟨.halt .h1,
        (((Sy.s0 :: Sim.Hi lo24 .s3 C 0).length : ℕ) : ℤ),
        Sim.tp .s0 ((Sy.s0 :: Sim.Hi lo24 .s3 C 0) ++ Sy.s0 ::
          (Sy.s0 :: rm.map lo24 ++ Sy.s3 :: v.map lo24))⟩ := by
      simp [finCfg24, URTM.CTSH.U24_4.finCfg, finList, RA, nm24, lo24, Sim.RA_zero]
    refine ⟨.h1, by rw [e], ?_⟩
    rw [e]
    exact Sim.tp_at _ _ _

/-! ### The main theorem -/

/-- **URTM(92,2) from (24,4) is a UTM in the strict sense of Morita Def. 7.1.** -/
theorem isUTMStrict_U : Spec.IsUTMStrict U :=
  isUTMStrict_fewsym U24_4.num Sy.s0 .q0 encC24 finCfg24
    (encM (U24_4.num.st (.go .q0)) (U24_4.num.sym .s0) (U24_4.num.sym .s3)) (encM_primrec _ _ _)
    (morita_hinit U24_4.num lo24 .s3 .s0 .s0 .q0 rfl hlo encC24 henc)
    (readM (U24_4.num.st (.halt .h1)) (U24_4.num.sym .s3) 1) (readM_primrec _ _ _)
    (fun _ _ _ h => readM_toID _ _ _ (by decide) h) (fun _ => Sy.s0)
    (fun h => U24_4.num.st (.halt h))
    (morita_hfinB U24_4.num lo24 .s3 .s0 .h0 .h1 1 rfl hlo hls (by decide)
      (fun h => U24_4.num.st (.halt h)) (by decide) finCfg24 hnullfin hhaltfin (fun _ => Sy.s0)
      head24)
    M E f24 num rfl (by decide)
    (fun s => by cases s <;> rfl) (fun i => by rcases i with _ | _ | i <;> rfl) rfl
    (fun C w => by
      obtain ⟨-, -, -, -, -, -, hF, -, hN⟩ := urtm92_2_24_4_simulates_ctsh C w
      exact ⟨hF, hN⟩)
    cf cf_primrec cf_length (fun s => by cases s <;> rfl) cf_mem tab rfl
    (fun s => by cases s <;> rfl) fs dd (fun _ => Sy.s0) (fun h => by cases h <;> decide) hrunH
    off (fun _ => cf 0) stm off_primrec (Primrec.const _) stm_primrec
    (fun h => by cases h <;> rfl) (fun _ => rfl) (fun h => by cases h <;> rfl)
    (by decide +kernel) (by decide +kernel)

end URTM.Univ.U92_2_24_4
