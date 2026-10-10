/-
  **The full chain for Morita's URTM(10,8), up to computability** (docs/24 L5 and
  "Integration notes").

      tm n  →(L0, P1)  code level of tbl n  →(L1, P5)  TRM  →(L2, P4)  2-TS
            →(L3, P3)  CTSH  →(L4, P6/P7a)  U = URTM(10,8)

  * `c10_8 : ℕ × Code → Code` and `d10_8 : Code → Option Code` are ordinary (computable)
    definitions built from the layers' encoders and decoders.
  * `isUTMStrict_U10_8_of_computable`: `Computable c10_8 → Computable d10_8 →
    IsUTMStrict U10_8.U`. These two computability facts are the only hypotheses
    (Phase C2).
  * `exists_urtm_10_8_of_computable`: the final target
    `∃ U, Deterministic U ∧ Reversible U ∧ NStates U = 10 ∧ NSyms U = 8 ∧ IsUTMStrict U`
    from the same two facts.
-/
import LeanUniv.Finite
import LeanUniv.U10_8
import LeanUniv.PadInv

namespace URTM.Univ.Chain10_8
open URTM URTM.Spec Relation
open URTM.CTSH (CStep Halting)
open URTM.Univ.L0 (tbl)

/-! ### The encoder and the decoder -/

/-- The 2-TS productions for table `T` (P4's gadgets on P5's TRM program). -/
def tagOf (T : List Quint) : ℕ → Option (List ℕ) := TRMToTag.tagP (L1.prog T)

/-- The CTSH for table `T` (P3's `Ĉ` over the alphabet `[0, Sb T)`). -/
def ctshOf (T : List Quint) : URTM.CTSH.CTSH := TagToCTSH.ctsh (Fin.Sb T) (tagOf T)

/-- The initial CTSH string for table `T` and code `a`: ϕ(W(L1.enc T a)). -/
def wordOf (T : List Quint) (a : Code) : List URTM.CTSH.Ch :=
  TagToCTSH.phiW (Fin.Sb T) (tagOf T) (TRMToTag.enc (L1.enc T a))

/-- **Encoder** `c(n, a)`: U's initial ID (as a Spec code) for the CTSH of `tbl n` and the
    initial string of `a`. -/
def c10_8 (p : ℕ × Code) : Code := U10_8.encList (ctshOf (tbl p.1)) (wordOf (tbl p.1) p.2)

/-- The middle decoder on (number of CTSH productions, final CTSH string): ϕ⁻¹ with block
    length `(ℓ - 1) / 2 + 1`, then the 2-TS readback, then the TRM readback. -/
def decMid (ℓ : ℕ) (v : List URTM.CTSH.Ch) : Option Code :=
  (TRMToTag.dec (TagToCTSH.decWord ((ℓ - 1) / 2) v)).bind L1.dec

/-- **Decoder** `d(g)`: read `(|C|, (vf, mf))` from the window `g` of U's halting ID, then
    `decMid |C| vf`. Independent of `n`. -/
def d10_8 (g : Code) : Option Code := (U10_8.readU g).bind fun p => decMid p.1 p.2.1

/-- **The decoder sees only the ID**: two codes of one ID (trailing blanks aside) are decoded
    alike (`PadInv.readU_toID`). This is what the 2026-10-03 output clause of `IsUTMStrict`
    ("every code of the halting ID") needs. -/
theorem d10_8_toID (p : ℤ) (g g' : Code) (h : toID p g = toID p g') : d10_8 g = d10_8 g' := by
  simp only [d10_8, PadInv.readU_toID h]

theorem decM_eq (y : TagToCTSH.CID) : Fin.decM y = decMid y.1.length y.2.1 := rfl

/-! ### Exit layer on configurations that carry the CTSH -/

theorem reach_stepC {C : URTM.CTSH.CTSH} {s : URTM.CTSH.ID} {y : TagToCTSH.CID}
    (h : ReflTransGen TagToCTSH.stepC (C, s) y) : y.1 = C ∧ ReflTransGen (CStep C) s y.2 := by
  induction h with
  | refl => exact ⟨rfl, ReflTransGen.refl⟩
  | tail _ hst ih =>
    obtain ⟨h1, h2⟩ := ih
    obtain ⟨e, hs⟩ := hst
    refine ⟨e.trans h1, h2.tail ?_⟩
    rw [← h1]; exact hs

/-- The CTSH configurations that carry the CTSH simulate the plain ones exactly. -/
theorem runSim_carry (C : URTM.CTSH.CTSH) (s : URTM.CTSH.ID) :
    RunSim TagToCTSH.stepC TagToCTSH.haltC (CStep C) (Halting C) (fun y s' => y = (C, s'))
      (C, s) s := by
  refine ⟨fun y hy => ?_, fun hn hs => ?_⟩
  · obtain ⟨e, hr⟩ := reach_stepC hy.1
    obtain ⟨C', s'⟩ := y
    simp only at e hr
    subst e
    exact ⟨s', ⟨hr, hy.2⟩, rfl⟩
  · obtain ⟨f, hf, hh⟩ := hs
    exact hn ⟨(C, f), hf.lift (fun s => (C, s)) (fun _ _ h => ⟨rfl, h⟩), hh⟩

theorem encMid_eq (n : ℕ) (a : Code) :
    Fin.encMid (tbl n) a = (ctshOf (tbl n), (wordOf (tbl n) a, 0)) := rfl

/-- **The exit layer** in the shape of `hout` of `isUTMStrict_of_chain`. -/
theorem hout (n : ℕ) (a : Code) :
    RunSim TagToCTSH.stepC TagToCTSH.haltC (Spec.Step U10_8.U) (Halted U10_8.U)
      (fun y γ => ∃ g, toID γ.pos g = γ ∧ d10_8 g = Fin.decM y)
      (Fin.encMid (tbl n) a) (toID 0 (c10_8 (n, a))) := by
  rw [encMid_eq]
  have h := (runSim_carry (ctshOf (tbl n)) (wordOf (tbl n) a, 0)).trans
    (U10_8.runSim_U10_8 (ctshOf (tbl n)) (wordOf (tbl n) a))
  refine ⟨fun y hy => ?_, h.2⟩
  obtain ⟨γ, hγ, s', rfl, g, hg, hr⟩ := h.1 y hy
  exact ⟨γ, hγ, g, hg, by simp [d10_8, hr, decM_eq]⟩

/-! ### The main theorems -/

/-- **Body form** (docs/26): the body of `IsUTMStrict U10_8.U` for `c10_8` and `d10_8`. -/
theorem strictBody_U10_8 : DropGen.StrictBody U10_8.U c10_8 d10_8 :=
  strictBody_of_chain U10_8.U c10_8 d10_8
    (fun n => L0.CStep (tbl n)) (fun n => L0.CHalt (tbl n)) (fun n => Fin.Inv1 (tbl n))
    (fun _ => TagToCTSH.stepC) (fun _ => TagToCTSH.haltC)
    (fun n => Fin.encMid (tbl n)) Fin.decM
    (fun _ _ _ => U10_8.isIDOf_encList _ _)
    Fin.hin1
    (fun n => Fin.mid (tbl n))
    (fun n a _ => hout n a)
    d10_8_toID

/-- **URTM(10,8) is a UTM in the strict sense of Morita Def. 7.1, up to computability**:
    the only missing inputs are the computability of the concrete encoder `c10_8` and
    decoder `d10_8` (Phase C2). -/
theorem isUTMStrict_U10_8_of_computable (hc : Computable c10_8) (hd : Computable d10_8) :
    IsUTMStrict U10_8.U :=
  DropGen.isUTMStrict_of_body hc hd strictBody_U10_8

/-- **The final target for (10,8)**, from the two computability facts of Phase C2. -/
theorem exists_urtm_10_8_of_computable (hc : Computable c10_8) (hd : Computable d10_8) :
    ∃ U : List Quint, Deterministic U ∧ Reversible U ∧ NStates U = 10 ∧ NSyms U = 8 ∧
      IsUTMStrict U :=
  ⟨U10_8.U, U10_8.U_det, U10_8.U_rev, U10_8.U_counts.1, U10_8.U_counts.2,
    isUTMStrict_U10_8_of_computable hc hd⟩

end URTM.Univ.Chain10_8
