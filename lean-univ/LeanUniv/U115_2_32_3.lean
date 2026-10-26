/-
  **URTM(115,2) from (32,3) as a Spec table, and its universality in the sense of Def. 7.1**.

  `U = numT num M`: the 2-symbol machine `URTM.Gen.FS115_2_32_3.M` (209 quintuples; the symbol
  reduction of docs/23 applied to Morita's (32,3), 2 bits per symbol `b 00`, `y 10`, `n 11`,
  record `results/fewsym/records/urtm32-3.115.merge.json`), numbered by `FewSymGen.numFS`
  (`go n ↦ n + 2`, pseudo-states `h0, h1 ↦ 0, 1`, which do not occur in `M`).

  Where (32,3) would apply its halting quintuple (`begin` or `case_y_2` reading the blank), `M`
  halts at once inside the block (`hrunH`, `decide +kernel`): the final tape is the 2-bit
  encoding of the final tape of (32,3). The readout `FewSymGen.readFS` decodes the code in blocks
  of 2 bits and applies the (32,3) readout `U32_3.readU` in the state `halt` (number 33) if `M`
  halts in the state `ρ case_y_2`, and in `null` otherwise. `isUTMStrict_U` by
  `FewSymGen.isUTMStrict_fewsym`.
-/
import LeanUniv.FewSymGen
import LeanUniv.U32_3
import URTM.CTSH115_2_32_3Main

namespace URTM.Univ.U115_2_32_3
open URTM URTM.CTSH URTM.Gen.K32_3 URTM.Univ.KToSpec URTM.Univ.NumGen URTM.Univ.FewSymGen
open URTM.KState (Tgt Cfg Machine HaltsIn)
open URTM.FewSym (enc pre hrun hfuel)
open URTM.Gen.FS115_2_32_3 (M E)
open URTM.CTSH.U115_2_32_3 (f32 urtm115_2_32_3_simulates_ctsh)
open URTM.CTSH.U32_3 (nm32 encC32 finCfg32 RA Hi Lo finList tapeList lo)
open URTM.Univ.U10_8 (loN)

/-! ### Numbering and the Spec table -/

def pn : Ps → ℕ
  | .h0 => 0
  | .h1 => 1

/-- The numbering of URTM(115,2). -/
def num : Numbering ℕ Ps Bool :=
  numFS pn (by intro a b h; cases a <;> cases b <;> first | rfl | exact absurd h (by decide))
    (by intro h; cases h <;> decide)

/-- **URTM(115,2) as a Spec table** (209 quintuples). -/
def U : List Quint := numT num M

/-- **Counts** (Morita's convention): 115 states, 2 symbols. -/
theorem U_counts : Spec.NStates U = 115 ∧ Spec.NSyms U = 2 := by decide +kernel
theorem U_det : Spec.Deterministic U := by decide +kernel
theorem U_rev : Spec.Reversible U := by decide +kernel

/-- `U` has no halting quintuple and no pseudo-state: every target state has outgoing
    quintuples, and no quintuple is a 0-shift. It halts where no quintuple applies. -/
theorem U_noPseudo : ∀ r ∈ U, r.q ∈ U.map Quint.p ∧ r.d ≠ .Z := by decide +kernel

/-! ### The code and the readout data -/

/-- The code of a (32,3) symbol number, as numbers. -/
def cf (a : ℕ) : List ℕ := [[0, 0], [1, 0], [1, 1]].getD a [0, 0]

/-- The symbol number of (32,3) with the code number `2·b₀ + b₁`. -/
def tab : List ℕ := [0, 0, 1, 2]

/-- The final states of `M`: `ρ begin = 1` (for `null`), `ρ case_y_2 = 47` (for `halt`). -/
def fs : Ps → ℕ
  | .h0 => 1
  | .h1 => 47

/-- The state of the (32,3) readout: `halt` (33) for the final state `47 + 2 = 49`, `null` (32)
    otherwise. -/
def stm (q : ℕ) : ℕ := if q = 49 then 33 else 32

theorem cf_length (a : ℕ) : (cf a).length = 2 := by
  unfold cf
  rcases a with _ | _ | _ | a <;> simp [List.getD]

theorem cf_mem (a b : ℕ) (h : b ∈ cf a) : b = 0 ∨ b = 1 := by
  unfold cf at h
  rcases a with _ | _ | _ | a <;> simp [List.getD] at h <;> omega

open Primrec in
theorem cf_primrec : Primrec cf := (list_getD [0, 0]).comp (const _) .id

open Primrec in
theorem stm_primrec : Primrec stm :=
  (Primrec.ite (Primrec.eq.comp .id (const 49)) (const 33) (const 32)).of_eq fun _ => rfl

/-- Where (32,3) would apply a halting quintuple, `M` halts at once inside the block. -/
theorem hrunH (h : Ps) :
    hrun M (hfuel E) ⟨E.ρ (f32 h), E.ce (f32 h), E.code Sy.s0⟩ = some ⟨fs h, 0, E.code Sy.s0⟩ := by
  cases h <;> decide +kernel

/-! ### The base (32,3) -/

theorem hinit (C : CTSH) (w : List Ch) : ∃ (L0 : List Sy) (P0 : ℕ), P0 ≤ L0.length ∧
    encC32 C w = ⟨.go .q0, (P0 : ℤ), Sim.tp .s0 L0⟩ ∧
    U32_3.encList C w = window (U32_3.num.st (.go .q0)) (L0.map U32_3.num.sym) P0 := by
  refine ⟨Sy.s0 :: RA nm32 C 0 ++ Sy.s0 :: w.map (lo nm32), (RA nm32 C 0).length + 2,
    by simp, ?_, ?_⟩
  · simp [encC32, URTM.CTSH.U32_3.encC, URTM.CTSH.U32_3.rep, tapeList, nm32]
  · have hL : Sy.s0 :: RA nm32 C 0 ++ Sy.s0 :: w.map (lo nm32) =
        (Sy.s0 :: RA nm32 C 0 ++ [Sy.s0]) ++ w.map (lo nm32) := by simp
    have hp : (RA nm32 C 0).length + 2 =
        ((Sy.s0 :: RA nm32 C 0 ++ [Sy.s0]).map U32_3.num.sym).length := by simp
    simp only [window]
    rw [hL, List.map_append, List.take_left' hp.symm, List.drop_left' hp.symm]
    simp only [U32_3.encList, U32_3.RA_zero, List.map_append, List.map_cons, List.map_nil,
      List.reverse_append, List.reverse_cons, List.reverse_nil, U32_3.Hi_zero_rev, U32_3.map_lo]
    rfl

/-- The final configurations of (32,3), head on the blank, read by `U32_3.readU`. -/
theorem hfinB (C : CTSH) (vf : List Ch) (mf : ℕ) (rm : List Ch) (hf : Halting C (vf, mf)) :
    ∃ (h : Ps) (A B : List Sy),
      finCfg32 C vf mf rm = ⟨.halt h, (A.length : ℤ), Sim.tp .s0 (A ++ Sy.s0 :: B)⟩ ∧
      U32_3.readU (U32_3.num.st (.halt h), (A.map U32_3.num.sym).reverse,
        U32_3.num.sym Sy.s0 :: B.map U32_3.num.sym) = some (C.length, vf.map loN) := by
  have hR : ∀ p g g', Spec.toID p g = Spec.toID p g' → U32_3.readU g = U32_3.readU g' :=
    fun _ _ _ h => U32_3.readU_toID h
  obtain ⟨hk, hv | hv⟩ := hf
  · obtain ⟨v, hv1, hv2⟩ := hv
    simp only at hv1 hv2
    subst hv1 hv2
    have e : finCfg32 C (Ch.Y :: v) 0 rm = ⟨.halt .h1, ((RA nm32 C 0).length : ℕ),
        Sim.tp .s0 (finList nm32 C (Ch.Y :: v) 0 rm)⟩ := by
      simp [finCfg32, URTM.CTSH.U32_3.finCfg, nm32]
    have hL : (finList nm32 C (Ch.Y :: v) 0 rm).map U32_3.num.sym =
        0 :: (RA nm32 C 0).map U32_3.num.sym ++ 0 :: (rm.map loN ++ 0 :: v.map loN) := by
      simp only [finList, List.map_append, List.map_cons, U32_3.map_lo]
      simp [nm32]
      rfl
    have hrd : U32_3.readU (window (U32_3.num.st (.halt .h1))
        ((finList nm32 C (Ch.Y :: v) 0 rm).map U32_3.num.sym) (RA nm32 C 0).length) =
        some (C.length, (Ch.Y :: v).map loN) := by
      simp only [U32_3.readU, window_whole, window_st, hL]
      exact congrArg some (U32_3.readL_halt C rm v)
    have hx : Sim.tp Sy.s0 (finList nm32 C (Ch.Y :: v) 0 rm) ((RA nm32 C 0).length : ℕ) =
        Sy.s0 := by
      have hA : finList nm32 C (Ch.Y :: v) 0 rm =
          (Sy.s0 :: Hi nm32 C 0 ++ URTM.CTSH.U32_3.E nm32 (prod C 0).reverse ++ [Sy.s2]) ++
            Sy.s0 :: (Sy.s0 :: rm.map (lo nm32) ++ Sy.s0 :: v.map (lo nm32)) := by
        simp [finList, RA, Lo, nm32]
      have hl : (RA nm32 C 0).length =
          (Sy.s0 :: Hi nm32 C 0 ++ URTM.CTSH.U32_3.E nm32 (prod C 0).reverse ++ [Sy.s2]).length := by
        simp [RA, Lo, nm32]; omega
      rw [hA, hl]
      exact Sim.tp_at _ _ _
    obtain ⟨A, B, h1, h2⟩ := fin_split U32_3.num Sy.s0 rfl U32_3.readU hR .h1 Sy.s0 _ _ _
      (by simp [finList]; omega) hx _ hrd
    exact ⟨.h1, A, B, e.trans h1, h2⟩
  · simp only at hv
    subst hv
    have hm : mf ≤ C.length := by simp [CTSH.k] at hk; omega
    have e : finCfg32 C [] mf rm = ⟨.halt .h0, (((RA nm32 C mf).length + 2 + rm.length : ℕ) : ℤ),
        Sim.tp .s0 (finList nm32 C [] mf rm)⟩ := by
      simp [finCfg32, URTM.CTSH.U32_3.finCfg, nm32]
    have hL : (finList nm32 C [] mf rm).map U32_3.num.sym =
        0 :: (RA nm32 C mf).map U32_3.num.sym ++ 0 :: rm.map loN := by
      simp only [finList, tapeList, List.map_append, List.map_cons, U32_3.map_lo, List.map_nil,
        List.append_nil]
      simp [nm32]
      rfl
    have hrd : U32_3.readU (window (U32_3.num.st (.halt .h0))
        ((finList nm32 C [] mf rm).map U32_3.num.sym) ((RA nm32 C mf).length + 2 + rm.length)) =
        some (C.length, ([] : List Ch).map loN) := by
      simp only [U32_3.readU, window_whole, window_st, hL]
      exact congrArg some (U32_3.readL_null C hm _ _ (by decide))
    have hlen : (finList nm32 C [] mf rm).length = (RA nm32 C mf).length + 2 + rm.length := by
      simp [finList, tapeList]; omega
    have hx : Sim.tp Sy.s0 (finList nm32 C [] mf rm)
        (((RA nm32 C mf).length + 2 + rm.length : ℕ) : ℤ) = Sy.s0 := by
      rw [Sim.tp_ofNat, List.getD_eq_default _ _ (by omega)]
    obtain ⟨A, B, h1, h2⟩ := fin_split U32_3.num Sy.s0 rfl U32_3.readU hR .h0 Sy.s0 _ _ _
      (by omega) hx _ hrd
    exact ⟨.h0, A, B, e.trans h1, h2⟩

/-! ### The main theorem -/

/-- **URTM(115,2) from (32,3) is a UTM in the strict sense of Morita Def. 7.1.** -/
theorem isUTMStrict_U : Spec.IsUTMStrict U :=
  isUTMStrict_fewsym U32_3.num Sy.s0 .q0 encC32 finCfg32 U32_3.encList U32_3.encList_primrec hinit
    U32_3.readU U32_3.readU_primrec (fun _ _ _ h => U32_3.readU_toID h) (fun _ => Sy.s0)
    (fun h => U32_3.num.st (.halt h)) hfinB M E f32 num rfl (by decide)
    (fun s => by cases s <;> rfl) (fun i => by rcases i with _ | _ | i <;> rfl) rfl
    (fun C w => by
      obtain ⟨-, -, -, -, -, -, hF, -, hN⟩ := urtm115_2_32_3_simulates_ctsh C w
      exact ⟨hF, hN⟩)
    cf cf_primrec cf_length (fun s => by cases s <;> rfl) cf_mem tab rfl
    (fun s => by cases s <;> rfl) fs (fun _ => 0) (fun _ => Sy.s0) (fun _ => by decide) hrunH
    (fun _ => 0) (fun _ => cf 0) stm (Primrec.const 0) (Primrec.const _) stm_primrec
    (fun _ => rfl) (fun _ => rfl) (fun h => by cases h <;> rfl) (by decide +kernel)
    (by decide +kernel)

end URTM.Univ.U115_2_32_3
