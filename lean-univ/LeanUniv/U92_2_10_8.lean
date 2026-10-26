/-
  **URTM(92,2) from (10,8) as a Spec table, and its universality in the sense of Def. 7.1**.

  `U = numT num M`: the 2-symbol machine `URTM.Gen.FS92_2_10_8.M` (169 quintuples; the symbol
  reduction of docs/23 applied to Morita's (10,8), 3 bits per symbol `b 000`, `y 011`, `n 101`,
  `nd 010`, `y1 001`, `n1 111`, `∗ 100`, `$ 110`, record
  `results/fewsym/records/urtm10-8.92.merge.json`), numbered by `FewSymGen.numFS`. Not the
  machine (92,2) of `CTSH92_2Main.lean` (from (13,7)).

  Where (10,8) would apply a halting quintuple (`begin` or `case_y_1` reading the blank), `M`
  halts inside the block after two steps to the right, in the same state 0 for both
  (`hrunH`, `decide +kernel`); for `begin` it has rewritten the blank block into the block of
  `nd`. The (10,8) readout `Base10_8.readN` does not depend on the state, so the readout
  `FewSymGen.readFS` moves the head back by two cells in the state 0, reads that block as the
  blank, decodes the code in blocks of 3 bits and applies `readN`.
  `isUTMStrict_U` by `FewSymGen.isUTMStrict_fewsym`.
-/
import LeanUniv.FewSymGen
import LeanUniv.Base10_8
import URTM.CTSH92_2_10_8Main

namespace URTM.Univ.U92_2_10_8
open URTM URTM.CTSH URTM.Gen.K10_8 URTM.Univ.KToSpec URTM.Univ.NumGen URTM.Univ.FewSymGen
open URTM.KState (Tgt Cfg Machine HaltsIn)
open URTM.FewSym (enc pre hrun hfuel)
open URTM.Gen.FS92_2_10_8 (M E)
open URTM.CTSH.U92_2_10_8 (f10 urtm92_2_10_8_simulates_ctsh)
open URTM.CTSH.U10_8 (lo up RA Hi tapeList tapeOf rep encC finCfg)
open URTM.Univ.U10_8 (loN num10_8 syN stN encList)

/-! ### Numbering and the Spec table -/

def pn : Ps → ℕ
  | .h0 => 0
  | .h1 => 1

/-- The numbering of URTM(92,2). -/
def num : Numbering ℕ Ps Bool :=
  numFS pn (by intro a b h; cases a <;> cases b <;> first | rfl | exact absurd h (by decide))
    (by intro h; cases h <;> decide)

/-- **URTM(92,2) from (10,8) as a Spec table** (169 quintuples). -/
def U : List Quint := numT num M

/-- **Counts** (Morita's convention): 92 states, 2 symbols. -/
theorem U_counts : Spec.NStates U = 92 ∧ Spec.NSyms U = 2 := by decide +kernel
theorem U_det : Spec.Deterministic U := by decide +kernel
theorem U_rev : Spec.Reversible U := by decide +kernel

/-- `U` has no halting quintuple and no pseudo-state. -/
theorem U_noPseudo : ∀ r ∈ U, r.q ∈ U.map Quint.p ∧ r.d ≠ .Z := by decide +kernel

/-! ### The code and the readout data -/

/-- The code of a (10,8) symbol number, as numbers. -/
def cf (a : ℕ) : List ℕ :=
  [[0, 0, 0], [0, 1, 1], [1, 0, 1], [0, 1, 0], [0, 0, 1], [1, 1, 1], [1, 0, 0], [1, 1, 0]].getD a
    [0, 0, 0]

/-- The symbol number of (10,8) with the code number `4·b₀ + 2·b₁ + b₂`. -/
def tab : List ℕ := [0, 4, 3, 1, 6, 2, 7, 5]

/-- The block that `M` leaves under the head: `nd` for `null` (`h0`), `b` for `halt` (`h1`). -/
def ws : Ps → Sy
  | .h0 => .s3
  | .h1 => .s0

/-- The head offset in the final state `0 + 2 = 2`. -/
def off (q : ℕ) : ℕ := if q = 2 then 2 else 0

/-- The state number given to `readN`, which does not read it (`Base10_8.hfin` with `k = 0`, no
    pseudo-state list). -/
def stn (h : Ps) : ℕ := 0 + ([] : List Ps).idxOf h

theorem cf_length (a : ℕ) : (cf a).length = 3 := by
  unfold cf
  rcases a with _ | _ | _ | _ | _ | _ | _ | _ | a <;> simp [List.getD]

theorem cf_mem (a b : ℕ) (h : b ∈ cf a) : b = 0 ∨ b = 1 := by
  unfold cf at h
  rcases a with _ | _ | _ | _ | _ | _ | _ | _ | a <;> simp [List.getD] at h <;> omega

open Primrec in
theorem cf_primrec : Primrec cf := (list_getD [0, 0, 0]).comp (const _) .id

open Primrec in
theorem off_primrec : Primrec off :=
  (Primrec.ite (Primrec.eq.comp .id (const 2)) (const 2) (const 0)).of_eq fun _ => rfl

/-- Where (10,8) would apply a halting quintuple, `M` halts inside the block after two steps, in
    the state 0. -/
theorem hrunH (h : Ps) :
    hrun M (hfuel E) ⟨E.ρ (f10 h), E.ce (f10 h), E.code Sy.s0⟩ = some ⟨0, 2, E.code (ws h)⟩ := by
  cases h <;> decide +kernel

/-! ### The base (10,8) -/

theorem hinit (C : CTSH) (w : List Ch) : ∃ (L0 : List Sy) (P0 : ℕ), P0 ≤ L0.length ∧
    encC C w = ⟨.go .q0, (P0 : ℤ), Sim.tp .s0 L0⟩ ∧
    encList C w = window (num10_8.st (.go .q0)) (L0.map num10_8.sym) P0 := by
  refine ⟨tapeList C 0 [] w, (RA C 0).length + 2 + ([] : List Ch).length,
    by simp [tapeList], by simp [encC, rep, tapeOf], ?_⟩
  have hL : tapeList C 0 [] w = (Sy.s0 :: RA C 0 ++ [Sy.s7]) ++ w.map lo := by simp [tapeList]
  have hp' : ((RA C 0).length + 2 + ([] : List Ch).length : ℕ) =
      ((Sy.s0 :: RA C 0 ++ [Sy.s7]).map num10_8.sym).length := by simp
  simp only [window]
  rw [hL, List.map_append, List.take_left' hp'.symm, List.drop_left' hp'.symm]
  simp only [encList, U10_8.RA_zero, num10_8, stN, List.map_append, List.map_cons, List.map_nil,
    List.reverse_append, List.reverse_cons, List.reverse_nil, List.map_map, U10_8.syN_comp_lo,
    U10_8.Hi_zero_rev]
  simp [syN]

/-- The cell under the head of a final configuration of (10,8) is blank. -/
theorem head10 (C : CTSH) (vf : List Ch) (mf : ℕ) (rm : List Ch) :
    ∃ h, (finCfg C vf mf rm).st = .halt h ∧
      (finCfg C vf mf rm).tape (finCfg C vf mf rm).pos = Sy.s0 := by
  cases vf with
  | nil =>
    have e : finCfg C [] mf rm = ⟨.halt .h0, (((tapeList C mf rm []).length : ℕ) : ℤ),
        Sim.tp .s0 (tapeList C mf rm [])⟩ := by
      simp [finCfg, tapeOf, tapeList]
      omega
    refine ⟨.h0, by rw [e], ?_⟩
    rw [e]
    simp only [Sim.tp_ofNat]
    rw [List.getD_eq_default _ _ (Nat.le_refl _)]
  | cons c v =>
    have e : finCfg C (c :: v) mf rm = ⟨.halt .h1, (((Sy.s0 :: Hi C 0).length : ℕ) : ℤ),
        Sim.tp .s0 ((Sy.s0 :: Hi C 0) ++ Sy.s0 :: (Sy.s7 :: rm.map up ++ (c :: v).map lo))⟩ := by
      simp [finCfg, tapeOf, tapeList, U10_8.RA_zero]
    refine ⟨.h1, by rw [e], ?_⟩
    rw [e]
    exact Sim.tp_at _ _ _

/-- The final configurations of (10,8) in the split form, read by `Base10_8.readN`. -/
theorem hfinB (C : CTSH) (vf : List Ch) (mf : ℕ) (rm : List Ch) (hf : Halting C (vf, mf)) :
    ∃ (h : Ps) (A B : List Sy),
      finCfg C vf mf rm = ⟨.halt h, (A.length : ℤ), Sim.tp .s0 (A ++ Sy.s0 :: B)⟩ ∧
      Base10_8.readN (stn h, (A.map num10_8.sym).reverse,
        num10_8.sym Sy.s0 :: B.map num10_8.sym) = some (C.length, vf.map loN) := by
  obtain ⟨h, L, p, hp, hfin, hrd⟩ := Base10_8.hfin 0 [] C vf mf rm hf
  obtain ⟨h', hst, htp⟩ := head10 C vf mf rm
  rw [hfin] at hst htp
  obtain rfl : h = h' := by injection hst
  obtain ⟨A, B, h1, h2⟩ := fin_split num10_8 Sy.s0 rfl Base10_8.readN
    (fun _ _ _ hg => Base10_8.readN_toID hg) h Sy.s0 (stn h) L p hp htp _ hrd
  exact ⟨h, A, B, hfin.trans h1, h2⟩

/-! ### The main theorem -/

/-- **URTM(92,2) from (10,8) is a UTM in the strict sense of Morita Def. 7.1.** -/
theorem isUTMStrict_U : Spec.IsUTMStrict U :=
  isUTMStrict_fewsym num10_8 Sy.s0 .q0 encC finCfg encList ComputableEnc.encList_primrec hinit
    Base10_8.readN Base10_8.readN_primrec (fun _ _ _ h => Base10_8.readN_toID h) (fun _ => Sy.s0)
    stn hfinB M E f10 num rfl (by decide)
    (fun s => by cases s <;> rfl) (fun i => by rcases i with _ | _ | _ | i <;> rfl) rfl
    (fun C w => by
      obtain ⟨-, -, -, -, -, -, hF, -, hN⟩ := urtm92_2_10_8_simulates_ctsh C w
      exact ⟨hF, hN⟩)
    cf cf_primrec cf_length (fun s => by cases s <;> rfl) cf_mem tab rfl
    (fun s => by cases s <;> rfl) (fun _ => 0) (fun _ => 2) ws (fun _ => by decide) hrunH
    off (fun _ => [0, 0, 0]) (fun _ => 0) off_primrec (Primrec.const _) (Primrec.const _)
    (fun _ => rfl) (fun _ => rfl) (fun h => by cases h <;> rfl)
    (by decide +kernel) (by decide +kernel)

end URTM.Univ.U92_2_10_8
