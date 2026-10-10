/-
  **The chain for an arbitrary machine that simulates every CTSH** (docs/24 P7a–P7d, P8, P9).

  The chain `tm n → TRM → 2-TS → CTSH` of `Chain10_8` does not depend on the record machine.
  For a Spec table `U` with
  * a list-level encoder `encList : CTSH → List Ch → Code` (primitive recursive),
  * a readout `readN : Code → Option (ℕ × List ℕ)` (primitive recursive, blind to trailing
    blanks),
  * `encList C w ∈ ID(U)`, and
  * the run-level simulation of every CTSH `C` from `(w, 0)` by `U` from `toID 0 (encList C w)`,
    whose halting ID has a code `g` with `readN g = some (|C|, ϕ₁(vf))`,
  `isUTMStrict_of_ctsh` gives `IsUTMStrict U` (Morita Def. 7.1) with
  `c = cOf encList`, `d = GenDec.dOf readN`. No other hypothesis.
-/
import LeanUniv.Chain10_8
import LeanUniv.ComputableEnc
import LeanUniv.GenDec

namespace URTM.Univ.ChainGen
open URTM URTM.Spec Relation
open URTM.CTSH (CStep Halting Ch CTSH)
open URTM.Univ.L0 (tbl)
open URTM.Univ.Chain10_8 (ctshOf wordOf decMid)

/-- **The encoder** `c(n, a)` built from a machine-specific list-level encoder: U's initial ID
    for the CTSH of `tbl n` and the initial string of `a`. -/
def cOf (encList : CTSH → List Ch → Code) (p : ℕ × Code) : Code :=
  encList (ctshOf (tbl p.1)) (wordOf (tbl p.1) p.2)

theorem cOf_computable {encList : CTSH → List Ch → Code} (h : Primrec₂ encList) :
    Computable (cOf encList) :=
  (h.comp (ComputableEnc.ctshOf_primrec.comp (ComputableEnc.tbl_primrec.comp Primrec.fst))
    (ComputableEnc.wordOf_primrec.comp (ComputableEnc.tbl_primrec.comp Primrec.fst)
      Primrec.snd)).to_comp

/-- The exit layer in the shape of `hout` of `isUTMStrict_of_chain`. -/
theorem hout {U : List Quint} {encList : CTSH → List Ch → Code}
    {readN : Code → Option (ℕ × List ℕ)}
    (hsim : ∀ C w, RunSim (CStep C) (Halting C) (Step U) (Halted U)
      (fun y γ => ∃ g, toID γ.pos g = γ ∧ readN g = some (C.length, y.1.map U10_8.loN))
      (w, 0) (toID 0 (encList C w)))
    (n : ℕ) (a : Code) :
    RunSim TagToCTSH.stepC TagToCTSH.haltC (Step U) (Halted U)
      (fun y γ => ∃ g, toID γ.pos g = γ ∧ GenDec.dOf readN g = Fin.decM y)
      (Fin.encMid (tbl n) a) (toID 0 (cOf encList (n, a))) := by
  rw [Chain10_8.encMid_eq]
  have h := (Chain10_8.runSim_carry (ctshOf (tbl n)) (wordOf (tbl n) a, 0)).trans
    (hsim (ctshOf (tbl n)) (wordOf (tbl n) a))
  refine ⟨fun y hy => ?_, h.2⟩
  obtain ⟨γ, hγ, s', rfl, g, hg, hr⟩ := h.1 y hy
  refine ⟨γ, hγ, g, hg, ?_⟩
  simp only [GenDec.dOf, hr, Option.bind_some, U10_8.chOf_loN, Chain10_8.decM_eq]

/-- **Body form** (docs/26) of `isUTMStrict_of_ctsh`: the body of `IsUTMStrict U` for the encoder
    `cOf encList` and the decoder `GenDec.dOf readN` (no computability needed). -/
theorem strictBody_of_ctsh (U : List Quint) (encList : CTSH → List Ch → Code)
    (readN : Code → Option (ℕ × List ℕ))
    (hID : ∀ C w, IsIDOf U (toID 0 (encList C w)))
    (hsim : ∀ C w, RunSim (CStep C) (Halting C) (Step U) (Halted U)
      (fun y γ => ∃ g, toID γ.pos g = γ ∧ readN g = some (C.length, y.1.map U10_8.loN))
      (w, 0) (toID 0 (encList C w)))
    (hinv : ∀ p g g', toID p g = toID p g' → readN g = readN g') :
    DropGen.StrictBody U (cOf encList) (GenDec.dOf readN) :=
  strictBody_of_chain U (cOf encList) (GenDec.dOf readN)
    (fun n => L0.CStep (tbl n)) (fun n => L0.CHalt (tbl n)) (fun n => Fin.Inv1 (tbl n))
    (fun _ => TagToCTSH.stepC) (fun _ => TagToCTSH.haltC)
    (fun n => Fin.encMid (tbl n)) Fin.decM
    (fun _ _ _ => hID _ _)
    Fin.hin1
    (fun n => Fin.mid (tbl n))
    (fun n a _ => hout hsim n a)
    (fun p g g' h => by simp only [GenDec.dOf, hinv p g g' h])

/-- The body form plus the primitive recursiveness of the encoder and the readout. -/
theorem isUTMStrict_of_body_ctsh {U : List Quint} {encList : CTSH → List Ch → Code}
    {readN : Code → Option (ℕ × List ℕ)} (henc : Primrec₂ encList) (hread : Primrec readN)
    (h : DropGen.StrictBody U (cOf encList) (GenDec.dOf readN)) : IsUTMStrict U :=
  DropGen.isUTMStrict_of_body (cOf_computable henc) (GenDec.dOf_computable hread) h

/-- **A machine that simulates every CTSH, with a primitive recursive encoder and a primitive
    recursive readout that is blind to trailing blanks, is a UTM in the strict sense of Morita
    Def. 7.1.** -/
theorem isUTMStrict_of_ctsh (U : List Quint) (encList : CTSH → List Ch → Code)
    (readN : Code → Option (ℕ × List ℕ))
    (henc : Primrec₂ encList) (hread : Primrec readN)
    (hID : ∀ C w, IsIDOf U (toID 0 (encList C w)))
    (hsim : ∀ C w, RunSim (CStep C) (Halting C) (Step U) (Halted U)
      (fun y γ => ∃ g, toID γ.pos g = γ ∧ readN g = some (C.length, y.1.map U10_8.loN))
      (w, 0) (toID 0 (encList C w)))
    (hinv : ∀ p g g', toID p g = toID p g' → readN g = readN g') :
    IsUTMStrict U :=
  isUTMStrict_of_body_ctsh henc hread (strictBody_of_ctsh U encList readN hID hsim hinv)

/-- **Removing the halting quintuples** (docs/26) from a machine of this exit layer: the table
    `dropT U H` is a UTM in the strict sense of Def. 7.1, with the encoder `cOf encList` and the
    decoder `fixD H (dOf readN)`, provided the removed quintuples are 0-shift quintuples into
    pseudo-states, the initial state `q0` is a state of `dropT U H` and no non-blank symbol is lost. -/
theorem isUTMStrict_drop_ctsh {U H : List Quint} {encList : CTSH → List Ch → Code}
    {readN : Code → Option (ℕ × List ℕ)} (henc : Primrec₂ encList) (hread : Primrec readN)
    (h : DropGen.StrictBody U (cOf encList) (GenDec.dOf readN))
    (hD : Deterministic U) (hH : DropGen.HaltQuints U H) (q0 : ℕ)
    (hq0 : ∀ C w, (encList C w).1 = q0) (hq0U : q0 ∈ states (DropGen.dropT U H))
    (hsym : ∀ x ∈ symbols U, x = 0 ∨ x ∈ symbols (DropGen.dropT U H)) :
    IsUTMStrict (DropGen.dropT U H) :=
  DropGen.isUTMStrict_drop (cOf_computable henc) (GenDec.dOf_computable hread) hD hH
    (fun n a _ => by simp only [cOf, hq0]; exact hq0U) hsym h

end URTM.Univ.ChainGen
