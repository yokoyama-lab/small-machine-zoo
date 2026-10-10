/-
  **The 2-symbol conversion of (13,7), step by step** (the materials of `FinalValues`; the values 169, 149,
  135 and 92 of the paper's table on the 3-state and 2-symbol conversions).

  * 169: Morita's conversion with 3-bit codes (`Conv54K.conv`) and Morita's code `numCode ss 3` (the symbols
    numbered in the order of the description file, `b, y, n, y1, n1, *, $` ↦ `000, 001, …, 110`).
  * 149: the same conversion with the code found by exhaustive search over the 5040 assignments
    (`results/fewsym/urtm13-7.morita.json`: `b 000, y 100, n 101, y1 001, n1 010, * 110, $ 111`).
  * 135: the table before merging of the record `results/fewsym/records/urtm13-7.2.merge.json` (the written
    values and the path types chosen by CP-SAT, `tools/fewsym3.py`), imported from the generator
    (`URTM.Gen.FS135_2`); the conversion with written values and path types is *not* a Lean function.
  * 92: the merged table of the same record (`URTM.Gen.FS92_2`, already proved to simulate every CTSH in
    `URTM.CTSH92_2Main`); `FS135_2` checks that it is the image of the 135-state table under a renaming of
    the states.

  Each table is shown to be deterministic and reversible and to pass the finite per-rule check `FewSym.certB`
  (kernel `decide`), so the general theorem `FewSym.fs_simulates`, composed with the CTSH simulation of (13,7)
  (`CTSH13_7Main.urtm13_7_simulates_ctsh`), gives the three halting clauses for every CTSH (`Sim13`).

  No `sorry`, no new axiom, no `native_decide`.
-/
import LeanUniv.Conv54K
import URTM.CTSH92_2Main
import URTM.Gen.FS135_2

set_option maxRecDepth 100000

namespace URTM.Univ.Values13_7

open URTM URTM.KState URTM.CTSH URTM.SimLemmas URTM.FewSym URTM.Gen.K13_7
open URTM.Univ.SymCount (nst dGo)
open URTM.Univ.Conv54K (KSt pRK pWK numCode)
open URTM.CTSH.U13_7 (encC13 finCfg13 urtm13_7_simulates_ctsh)
open URTM.CTSH.U92_2 (f13 hH13 finCfg13_pseudo)

/-- **Simulation of every CTSH through (13,7)** by a 2-symbol machine `M` with the block encoding `E`
    (the three halting clauses of `FewSym.fs_simulates`, from Morita's initial configuration of (13,7)). -/
def Sim13 {Q' : Type} [DecidableEq Q'] (M : Machine Q' Ps Bool) (E : Enc St Sy Q') : Prop :=
  ∀ (C : CTSH) (w : List Ch),
    (∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) →
      ∃ N rm, n ≤ N + 1 ∧ HaltsIn M N (enc E (encC13 C w)) (pre M E (unhalt f13 (finCfg13 C vf mf rm)))) ∧
    (∀ N e, HaltsIn M N (enc E (encC13 C w)) e →
      ∃ n vf mf rm, CHaltsIn C n (w, 0) (vf, mf) ∧ e = pre M E (unhalt f13 (finCfg13 C vf mf rm))) ∧
    ((∀ n f, ¬ CHaltsIn C n (w, 0) f) ↔ (∀ N e, ¬ HaltsIn M N (enc E (encC13 C w)) e))

theorem sim13 {Q' : Type} [DecidableEq Q'] {M : Machine Q' Ps Bool} {E : Enc St Sy Q'}
    {cost : Rule St Ps Sy → Nat} (H : FewSym.Hyp T M E cost ss) (hD' : Deterministic M) : Sim13 M E := by
  intro C w
  have h13 := urtm13_7_simulates_ctsh C w
  exact fs_simulates H hD hH13 hD' C w (encC13 C w) ⟨.q0, rfl⟩ (finCfg13 C) (finCfg13_pseudo C) ⟨h13.1, h13.2.1⟩

theorem hqs : qs.Nodup := by decide

/-- Every non-halting rule is simulated in `3k − 2 = 7` steps by the conversion of Theorem 5.4. -/
def cost7 (_ : Rule St Ps Sy) : Nat := 7

/-! ## 169: Morita's conversion, Morita's code -/

/-- Morita's code for (13,7): the 3-bit numeral of the position in `ss` (`b, y, n, y1, n1, *, $`). -/
def code169 : Sy → List Bool := numCode ss 3
def M169 : Machine (KSt St) Ps Bool := Conv54K.conv T code169 3 qs
def E169 : Enc St Sy (KSt St) := ⟨code169, 3, fun p => .r p [], fun _ => 0⟩

theorem code169_eq : code169 .s0 = [false, false, false] ∧ code169 .s1 = [false, false, true] ∧
    code169 .s2 = [false, true, false] ∧ code169 .s3 = [false, true, true] ∧
    code169 .s4 = [true, false, false] ∧ code169 .s5 = [true, false, true] ∧
    code169 .s6 = [true, true, false] := by decide +kernel
theorem hlen169 : ∀ s, (code169 s).length = 3 := by intro s; cases s <;> decide +kernel
theorem counts169 : (dGo T qs).length = 13 ∧ (pRK T code169 3).length = 65 ∧ (pWK T code169 3).length = 65 := by
  decide +kernel
theorem cert169 : certB T M169 E169 cost7 ss = true := by decide +kernel
theorem det169 : Deterministic M169 := by decide +kernel
theorem rev169 : Reversible M169 := by decide +kernel
theorem hyp169 : FewSym.Hyp T M169 E169 cost7 ss := ⟨by decide, hlen169, hS, cert169⟩

/-! ## 149: the same conversion, the code found by exhaustive search -/

/-- The code of `results/fewsym/urtm13-7.morita.json` (best of the 5040 assignments with the blank `000`). -/
def code149 : Sy → List Bool
  | .s0 => [false, false, false]
  | .s1 => [true, false, false]
  | .s2 => [true, false, true]
  | .s3 => [false, false, true]
  | .s4 => [false, true, false]
  | .s5 => [true, true, false]
  | .s6 => [true, true, true]
def M149 : Machine (KSt St) Ps Bool := Conv54K.conv T code149 3 qs
def E149 : Enc St Sy (KSt St) := ⟨code149, 3, fun p => .r p [], fun _ => 0⟩

theorem hlen149 : ∀ s, (code149 s).length = 3 := by intro s; cases s <;> rfl
theorem counts149 : (dGo T qs).length = 13 ∧ (pRK T code149 3).length = 55 ∧ (pWK T code149 3).length = 55 := by
  decide +kernel
theorem cert149 : certB T M149 E149 cost7 ss = true := by decide +kernel
theorem det149 : Deterministic M149 := by decide +kernel
theorem rev149 : Reversible M149 := by decide +kernel
theorem hyp149 : FewSym.Hyp T M149 E149 cost7 ss := ⟨by decide, hlen149, hS, cert149⟩

/-! ## 135 and 92: the record `urtm13-7.2` before and after merging -/

/-- The tables before and after merging use the code of 149. -/
theorem code135 : ∀ s, URTM.Gen.FS135_2.code s = code149 s ∧ URTM.Gen.FS92_2.code s = code149 s := by
  intro s; cases s <;> exact ⟨rfl, rfl⟩
theorem nst135 : nst URTM.Gen.FS135_2.M = 135 := by decide +kernel
theorem nst92 : nst URTM.Gen.FS92_2.M = 92 := by decide +kernel

end URTM.Univ.Values13_7
