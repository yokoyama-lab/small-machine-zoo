/-
  **URTM(115,2) from (17,5) as a Spec table, and its universality in the sense of Def. 7.1**.

  `U = numT num M`: the 2-symbol machine `URTM.Gen.FS115_2_17_5.M` (198 quintuples; the symbol
  reduction of docs/23 applied to Morita's (17,5), 3 bits per symbol `b 000`, `y 100`, `n 101`, `∗ 110`, `$ 111`,
  record `results/fewsym/records/urtm17-5.115.merge.json`), numbered by `FewSymGen.numFS`.

  Where (17,5) would apply a halting quintuple, `M` halts inside the block (`hrunH`,
  `decide +kernel`): at once for `case_y_1` reading the blank (state 54, for `halt`), and
  after two steps to the right without writing for `case_y_2` reading `$` (state 62, head on the third bit). The readout `FewSymGen.readFS` moves the head back by two cells in the state 62 and
  reads that block as `$`, decodes the code in blocks of 3 bits and applies the (17,5) readout
  `MoritaGen.readM` in the state `halt` (17) for the state 54 and in `null` (18) otherwise.
  `isUTMStrict_U` by `FewSymGen.isUTMStrict_fewsym`.
-/
import LeanUniv.FewSymGen
import LeanUniv.Base17_5
import URTM.CTSH115_2_17_5Main

namespace URTM.Univ.U115_2_17_5
open URTM URTM.CTSH URTM.Gen.K17_5 URTM.Univ.KToSpec URTM.Univ.NumGen URTM.Univ.MoritaGen
open URTM.Univ.FewSymGen
open URTM.KState (Tgt Cfg Machine HaltsIn)
open URTM.FewSym (enc pre hrun hfuel)
open URTM.Gen.FS115_2_17_5 (M E)
open URTM.CTSH.U115_2_17_5 (f17 urtm115_2_17_5_simulates_ctsh)
open URTM.CTSH.U17_5 (nm17 encC17 finCfg17)
open URTM.CTSH.U17_5 (Core)
open URTM.Univ.U17_5 (lo17 hls)
open URTM.Univ.U10_8 (loN)

/-! ### Numbering and the Spec table -/

def pn : Ps → ℕ
  | .h0 => 0
  | .h1 => 1

/-- The numbering of URTM(115,2). -/
def num : Numbering ℕ Ps Bool :=
  numFS pn (by intro a b h; cases a <;> cases b <;> first | rfl | exact absurd h (by decide))
    (by intro h; cases h <;> decide)

/-- **URTM(115,2) from (17,5) as a Spec table** (198 quintuples). -/
def U : List Quint := numT num M

/-- **Counts** (Morita's convention): 115 states, 2 symbols. -/
theorem U_counts : Spec.NStates U = 115 ∧ Spec.NSyms U = 2 := by decide +kernel
theorem U_det : Spec.Deterministic U := by decide +kernel
theorem U_rev : Spec.Reversible U := by decide +kernel

/-- `U` has no halting quintuple and no pseudo-state. -/
theorem U_noPseudo : ∀ r ∈ U, r.q ∈ U.map Quint.p ∧ r.d ≠ .Z := by decide +kernel

/-! ### The code and the readout data -/

/-- The code of a (17,5) symbol number, as numbers. -/
def cf (a : ℕ) : List ℕ := [[0, 0, 0], [1, 0, 0], [1, 0, 1], [1, 1, 0], [1, 1, 1]].getD a [0, 0, 0]

/-- The symbol number of (17,5) with the code number `4·b₀ + 2·b₁ + b₂`. -/
def tab : List ℕ := [0, 0, 0, 0, 1, 2, 3, 4]

/-- The symbol that the halting quintuple of each pseudo-state reads: `b` for `halt` (`h0`), `$` for
    `null` (`h1`). -/
def hs : Ps → Sy
  | .h0 => .s0
  | .h1 => .s4

/-- The final states of `M`: 54 (for `halt`) and 62 (for `null`). -/
def fs : Ps → ℕ
  | .h0 => 54
  | .h1 => 62

def dd : Ps → ℕ
  | .h0 => 0
  | .h1 => 2

/-- The block that `M` leaves under the head. -/
def ws : Ps → Sy
  | .h0 => .s0
  | .h1 => Sy.s4

/-- The head offset in the final state `62 + 2 = 64`. -/
def off (q : ℕ) : ℕ := if q = 64 then 2 else 0

/-- The code of the symbol read by the halting quintuple: `$` in the final state 64, `b` otherwise. -/
def fx (q : ℕ) : List ℕ := if q = 64 then [1, 1, 1] else [0, 0, 0]

/-- The state of the (17,5) readout: `halt` (17) for the final state `54 + 2 = 56`, `null`
    (18) otherwise. -/
def stm (q : ℕ) : ℕ := if q = 56 then 17 else 18

theorem cf_length (a : ℕ) : (cf a).length = 3 := by
  unfold cf
  rcases a with _ | _ | _ | _ | _ | a <;> simp [List.getD]

theorem cf_mem (a b : ℕ) (h : b ∈ cf a) : b = 0 ∨ b = 1 := by
  unfold cf at h
  rcases a with _ | _ | _ | _ | _ | a <;> simp [List.getD] at h <;> omega

open Primrec in
theorem cf_primrec : Primrec cf := (list_getD [0, 0, 0]).comp (const _) .id

open Primrec in
theorem off_primrec : Primrec off :=
  (Primrec.ite (Primrec.eq.comp .id (const 64)) (const 2) (const 0)).of_eq fun _ => rfl

open Primrec in
theorem fx_primrec : Primrec fx :=
  (Primrec.ite (Primrec.eq.comp .id (const 64)) (const [1, 1, 1]) (const [0, 0, 0])).of_eq
    fun _ => rfl

open Primrec in
theorem stm_primrec : Primrec stm :=
  (Primrec.ite (Primrec.eq.comp .id (const 56)) (const 17) (const 18)).of_eq fun _ => rfl

/-- Where (17,5) would apply a halting quintuple, `M` halts inside the block. -/
theorem hrunH (h : Ps) :
    hrun M (hfuel E) ⟨E.ρ (f17 h), E.ce (f17 h), E.code (hs h)⟩ =
      some ⟨fs h, dd h, E.code (ws h)⟩ := by
  cases h <;> decide +kernel

/-! ### The base (17,5) -/

/-- The cell under the head of a final configuration of (17,5): `$` for `null`, `b` for `halt`. -/
theorem head17 (C : CTSH) (vf : List Ch) (mf : ℕ) (rm : List Ch) (hf : Halting C (vf, mf)) :
    ∃ h, (finCfg17 C vf mf rm).st = .halt h ∧
      (finCfg17 C vf mf rm).tape (finCfg17 C vf mf rm).pos = hs h := by
  cases vf with
  | nil =>
    have e : finCfg17 C [] mf rm = ⟨.halt .h1,
        (((Sy.s0 :: Sim.RA lo17 .s3 .s0 C mf).length : ℕ) : ℤ),
        Sim.tp .s0 ((Sy.s0 :: Sim.RA lo17 .s3 .s0 C mf) ++ Sy.s4 :: (rm.map lo17 ++ [Sy.s4]))⟩ := by
      simp [finCfg17, URTM.CTSH.U17_5.finCfg, Core.finCfg, Core.finList, Core.tapeList, nm17, lo17]
    refine ⟨.h1, by rw [e], ?_⟩
    rw [e]
    exact Sim.tp_at _ _ _
  | cons c v =>
    have hm : mf = 0 := by
      rcases hf.2 with ⟨v', -, h2⟩ | h
      · exact h2
      · simp at h
    subst hm
    have e : finCfg17 C (c :: v) 0 rm = ⟨.halt .h0,
        (((Sy.s0 :: Sim.Hi lo17 .s3 C 0).length : ℕ) : ℤ),
        Sim.tp .s0 ((Sy.s0 :: Sim.Hi lo17 .s3 C 0) ++ Sy.s0 ::
          (Sy.s0 :: rm.map lo17 ++ Sy.s4 :: v.map lo17))⟩ := by
      simp [finCfg17, URTM.CTSH.U17_5.finCfg, Core.finCfg, Core.finList, nm17, lo17, Sim.RA_zero]
    refine ⟨.h0, by rw [e], ?_⟩
    rw [e]
    exact Sim.tp_at _ _ _

/-! ### The main theorem -/

/-- **URTM(115,2) from (17,5) is a UTM in the strict sense of Morita Def. 7.1.** -/
theorem isUTMStrict_U : Spec.IsUTMStrict U :=
  isUTMStrict_fewsym U17_5.num Sy.s0 .q0 encC17 finCfg17
    (encM (U17_5.num.st (.go .q0)) (U17_5.num.sym .s4) (U17_5.num.sym .s3)) (encM_primrec _ _ _)
    (morita_hinit U17_5.num lo17 .s3 .s0 .s4 .q0 rfl Base17_5.hlo encC17 Base17_5.henc)
    (readM (U17_5.num.st (.halt .h0)) (U17_5.num.sym .s3) 0) (readM_primrec _ _ _)
    (fun _ _ _ h => readM_toID _ _ _ (by decide) h) hs (fun h => U17_5.num.st (.halt h))
    (morita_hfinB U17_5.num lo17 .s3 .s0 .h1 .h0 0 rfl Base17_5.hlo hls (by decide)
      (fun h => U17_5.num.st (.halt h)) (by decide) finCfg17 Base17_5.hnullfin Base17_5.hhaltfin hs
      head17)
    M E f17 num rfl (by decide)
    (fun s => by cases s <;> rfl) (fun i => by rcases i with _ | _ | _ | i <;> rfl) rfl
    (fun C w => by
      obtain ⟨-, -, -, -, -, -, hF, -, hN⟩ := urtm115_2_17_5_simulates_ctsh C w
      exact ⟨hF, hN⟩)
    cf cf_primrec cf_length (fun s => by cases s <;> rfl) cf_mem tab rfl
    (fun s => by cases s <;> rfl) fs dd ws (fun h => by cases h <;> decide) hrunH
    off fx stm off_primrec fx_primrec stm_primrec
    (fun h => by cases h <;> rfl) (fun h => by cases h <;> rfl) (fun h => by cases h <;> rfl)
    (by decide +kernel) (by decide +kernel)

end URTM.Univ.U115_2_17_5
