/-
  **URTM(108,2) from (15,6) as a Spec table, and its universality in the sense of Def. 7.1**.

  `U = numT num M`: the 2-symbol machine `URTM.Gen.FS108_2_15_6.M` (187 quintuples; the symbol
  reduction of docs/23 applied to Morita's (15,6), 3 bits per symbol `b 000`, `y 100`, `n 101`, `∗ 110`, `$ 111`, `yd 001`,
  record `results/fewsym/records/urtm15-6.108.merge.json`), numbered by `FewSymGen.numFS`.

  Where (15,6) would apply a halting quintuple, `M` halts inside the block (`hrunH`,
  `decide +kernel`): at once for `case_y_1` reading the blank (state 50, for `halt`), and
  after two steps to the right for `case_y_2` reading `$` (state 59, head on the third bit), having rewritten the block of `$` into the block of `n`. The readout `FewSymGen.readFS` moves the head back by two cells in the state 59 and
  reads that block as `$`, decodes the code in blocks of 3 bits and applies the (15,6) readout
  `MoritaGen.readM` in the state `halt` (15) for the state 50 and in `null` (16) otherwise.
  `isUTMStrict_U` by `FewSymGen.isUTMStrict_fewsym`.
-/
import LeanUniv.FewSymGen
import LeanUniv.Base15_6
import URTM.CTSH108_2_15_6Main

namespace URTM.Univ.U108_2_15_6
open URTM URTM.CTSH URTM.Gen.K15_6 URTM.Univ.KToSpec URTM.Univ.NumGen URTM.Univ.MoritaGen
open URTM.Univ.FewSymGen
open URTM.KState (Tgt Cfg Machine HaltsIn)
open URTM.FewSym (enc pre hrun hfuel)
open URTM.Gen.FS108_2_15_6 (M E)
open URTM.CTSH.U108_2_15_6 (f15 urtm108_2_15_6_simulates_ctsh)
open URTM.CTSH.U15_6 (nm15 encC15 finCfg15)
open URTM.CTSH.U17_5 (Core)
open URTM.Univ.U15_6 (lo15 hls)
open URTM.Univ.U10_8 (loN)

/-! ### Numbering and the Spec table -/

def pn : Ps → ℕ
  | .h0 => 0
  | .h1 => 1

/-- The numbering of URTM(108,2). -/
def num : Numbering ℕ Ps Bool :=
  numFS pn (by intro a b h; cases a <;> cases b <;> first | rfl | exact absurd h (by decide))
    (by intro h; cases h <;> decide)

/-- **URTM(108,2) from (15,6) as a Spec table** (187 quintuples). -/
def U : List Quint := numT num M

/-- **Counts** (Morita's convention): 108 states, 2 symbols. -/
theorem U_counts : Spec.NStates U = 108 ∧ Spec.NSyms U = 2 := by decide +kernel
theorem U_det : Spec.Deterministic U := by decide +kernel
theorem U_rev : Spec.Reversible U := by decide +kernel

/-- `U` has no halting quintuple and no pseudo-state. -/
theorem U_noPseudo : ∀ r ∈ U, r.q ∈ U.map Quint.p ∧ r.d ≠ .Z := by decide +kernel

/-! ### The code and the readout data -/

/-- The code of a (15,6) symbol number, as numbers. -/
def cf (a : ℕ) : List ℕ := [[0, 0, 0], [1, 0, 0], [1, 0, 1], [1, 1, 0], [1, 1, 1], [0, 0, 1]].getD a [0, 0, 0]

/-- The symbol number of (15,6) with the code number `4·b₀ + 2·b₁ + b₂`. -/
def tab : List ℕ := [0, 5, 0, 0, 1, 2, 3, 4]

/-- The symbol that the halting quintuple of each pseudo-state reads: `b` for `halt` (`h0`), `$` for
    `null` (`h1`). -/
def hs : Ps → Sy
  | .h0 => .s0
  | .h1 => .s4

/-- The final states of `M`: 50 (for `halt`) and 59 (for `null`). -/
def fs : Ps → ℕ
  | .h0 => 50
  | .h1 => 59

def dd : Ps → ℕ
  | .h0 => 0
  | .h1 => 2

/-- The block that `M` leaves under the head. -/
def ws : Ps → Sy
  | .h0 => .s0
  | .h1 => Sy.s2

/-- The head offset in the final state `59 + 2 = 61`. -/
def off (q : ℕ) : ℕ := if q = 61 then 2 else 0

/-- The code of the symbol read by the halting quintuple: `$` in the final state 61, `b` otherwise. -/
def fx (q : ℕ) : List ℕ := if q = 61 then [1, 1, 1] else [0, 0, 0]

/-- The state of the (15,6) readout: `halt` (15) for the final state `50 + 2 = 52`, `null`
    (16) otherwise. -/
def stm (q : ℕ) : ℕ := if q = 52 then 15 else 16

theorem cf_length (a : ℕ) : (cf a).length = 3 := by
  unfold cf
  rcases a with _ | _ | _ | _ | _ | _ | a <;> simp [List.getD]

theorem cf_mem (a b : ℕ) (h : b ∈ cf a) : b = 0 ∨ b = 1 := by
  unfold cf at h
  rcases a with _ | _ | _ | _ | _ | _ | a <;> simp [List.getD] at h <;> omega

open Primrec in
theorem cf_primrec : Primrec cf := (list_getD [0, 0, 0]).comp (const _) .id

open Primrec in
theorem off_primrec : Primrec off :=
  (Primrec.ite (Primrec.eq.comp .id (const 61)) (const 2) (const 0)).of_eq fun _ => rfl

open Primrec in
theorem fx_primrec : Primrec fx :=
  (Primrec.ite (Primrec.eq.comp .id (const 61)) (const [1, 1, 1]) (const [0, 0, 0])).of_eq
    fun _ => rfl

open Primrec in
theorem stm_primrec : Primrec stm :=
  (Primrec.ite (Primrec.eq.comp .id (const 52)) (const 15) (const 16)).of_eq fun _ => rfl

/-- Where (15,6) would apply a halting quintuple, `M` halts inside the block. -/
theorem hrunH (h : Ps) :
    hrun M (hfuel E) ⟨E.ρ (f15 h), E.ce (f15 h), E.code (hs h)⟩ =
      some ⟨fs h, dd h, E.code (ws h)⟩ := by
  cases h <;> decide +kernel

/-! ### The base (15,6) -/

/-- The cell under the head of a final configuration of (15,6): `$` for `null`, `b` for `halt`. -/
theorem head15 (C : CTSH) (vf : List Ch) (mf : ℕ) (rm : List Ch) (hf : Halting C (vf, mf)) :
    ∃ h, (finCfg15 C vf mf rm).st = .halt h ∧
      (finCfg15 C vf mf rm).tape (finCfg15 C vf mf rm).pos = hs h := by
  cases vf with
  | nil =>
    have e : finCfg15 C [] mf rm = ⟨.halt .h1,
        (((Sy.s0 :: Sim.RA lo15 .s3 .s0 C mf).length : ℕ) : ℤ),
        Sim.tp .s0 ((Sy.s0 :: Sim.RA lo15 .s3 .s0 C mf) ++ Sy.s4 :: (rm.map lo15 ++ [Sy.s4]))⟩ := by
      simp [finCfg15, URTM.CTSH.U15_6.finCfg, Core.finCfg, Core.finList, Core.tapeList, nm15, lo15]
    refine ⟨.h1, by rw [e], ?_⟩
    rw [e]
    exact Sim.tp_at _ _ _
  | cons c v =>
    have hm : mf = 0 := by
      rcases hf.2 with ⟨v', -, h2⟩ | h
      · exact h2
      · simp at h
    subst hm
    have e : finCfg15 C (c :: v) 0 rm = ⟨.halt .h0,
        (((Sy.s0 :: Sim.Hi lo15 .s3 C 0).length : ℕ) : ℤ),
        Sim.tp .s0 ((Sy.s0 :: Sim.Hi lo15 .s3 C 0) ++ Sy.s0 ::
          (Sy.s0 :: rm.map lo15 ++ Sy.s4 :: v.map lo15))⟩ := by
      simp [finCfg15, URTM.CTSH.U15_6.finCfg, Core.finCfg, Core.finList, nm15, lo15, Sim.RA_zero]
    refine ⟨.h0, by rw [e], ?_⟩
    rw [e]
    exact Sim.tp_at _ _ _

/-! ### The main theorem -/

/-- **URTM(108,2) from (15,6) is a UTM in the strict sense of Morita Def. 7.1.** -/
theorem isUTMStrict_U : Spec.IsUTMStrict U :=
  isUTMStrict_fewsym U15_6.num Sy.s0 .q0 encC15 finCfg15
    (encM (U15_6.num.st (.go .q0)) (U15_6.num.sym .s4) (U15_6.num.sym .s3)) (encM_primrec _ _ _)
    (morita_hinit U15_6.num lo15 .s3 .s0 .s4 .q0 rfl Base15_6.hlo encC15 Base15_6.henc)
    (readM (U15_6.num.st (.halt .h0)) (U15_6.num.sym .s3) 0) (readM_primrec _ _ _)
    (fun _ _ _ h => readM_toID _ _ _ (by decide) h) hs (fun h => U15_6.num.st (.halt h))
    (morita_hfinB U15_6.num lo15 .s3 .s0 .h1 .h0 0 rfl Base15_6.hlo hls (by decide)
      (fun h => U15_6.num.st (.halt h)) (by decide) finCfg15 Base15_6.hnullfin Base15_6.hhaltfin hs
      head15)
    M E f15 num rfl (by decide)
    (fun s => by cases s <;> rfl) (fun i => by rcases i with _ | _ | _ | i <;> rfl) rfl
    (fun C w => by
      obtain ⟨-, -, -, -, -, -, hF, -, hN⟩ := urtm108_2_15_6_simulates_ctsh C w
      exact ⟨hF, hN⟩)
    cf cf_primrec cf_length (fun s => by cases s <;> rfl) cf_mem tab rfl
    (fun s => by cases s <;> rfl) fs dd ws (fun h => by cases h <;> decide) hrunH
    off fx stm off_primrec fx_primrec stm_primrec
    (fun h => by cases h <;> rfl) (fun h => by cases h <;> rfl) (fun h => by cases h <;> rfl)
    (by decide +kernel) (by decide +kernel)

end URTM.Univ.U108_2_15_6
