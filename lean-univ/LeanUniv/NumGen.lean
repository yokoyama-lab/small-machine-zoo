/-
  **Generic numbering and generic exit layer** (docs/24 P7a–P7d).

  * `numOf qs ps ss`: the numbering of a typed machine by position in enumerations of its
    states `qs`, pseudo-states `ps` (numbered after the real states) and symbols `ss`.
  * `runSim_of_sim`: the run-level simulation `RunSim` from the CTSH `(CStep C, Halting C)` to
    Spec's `(Step U, Halted U)`, `U = numT N T`, from the three facts every record machine's
    CTSH theorem provides: a halting CTSH run gives a halting run of `T` to a configuration of
    the final shape `Fin`; a non-halting CTSH gives a non-halting `T`; and the final shape is
    read back (`R`).
  * `read_of_tp`: a typed final configuration with a finite list tape has the window code.
  * `read_toID`: a readout that sees only the state and the whole window list, and ignores
    blanks appended on either side, does not depend on the code chosen for an ID
    (the hypothesis `hdinv` of `isUTMStrict_of_chain`).
-/
import LeanUniv.KToSpec
import LeanUniv.ExactSim
import LeanUniv.PadInv

namespace URTM.Univ.NumGen
open URTM URTM.CTSH URTM.Univ.KToSpec Relation
open URTM.KState (Tgt Cfg Machine Step StepN Halted HaltsIn)

/-! ### Numbering by position in an enumeration -/

section Num
variable {Q P S : Type} [DecidableEq Q] [DecidableEq P] [DecidableEq S]

/-- Real states by position in `qs`; pseudo-states after them, by position in `ps`. -/
def stOf (qs : List Q) (ps : List P) : Tgt Q P → ℕ
  | .go q => qs.idxOf q
  | .halt h => qs.length + ps.idxOf h

theorem stOf_inj (qs : List Q) (ps : List P) (hq : ∀ q, q ∈ qs) (hp : ∀ p, p ∈ ps) :
    Function.Injective (stOf qs ps) := by
  intro a b h
  cases a with
  | go a =>
    cases b with
    | go b => simp only [stOf] at h; rw [(List.idxOf_inj (hq a)).mp h]
    | halt b =>
      simp only [stOf] at h
      have := List.idxOf_lt_length_iff.mpr (hq a)
      omega
  | halt a =>
    cases b with
    | go b =>
      simp only [stOf] at h
      have := List.idxOf_lt_length_iff.mpr (hq b)
      omega
    | halt b =>
      simp only [stOf] at h
      have h' : ps.idxOf a = ps.idxOf b := by omega
      rw [(List.idxOf_inj (hp a)).mp h']

/-- **Numbering by enumeration**: states by position in `qs` (pseudo-states after them, by
    position in `ps`), symbols by position in `ss`. -/
def numOf (qs : List Q) (ps : List P) (ss : List S) (hq : ∀ q, q ∈ qs) (hp : ∀ p, p ∈ ps)
    (hs : ∀ s, s ∈ ss) : Numbering Q P S :=
  ⟨stOf qs ps, fun s => ss.idxOf s, stOf_inj qs ps hq hp,
    fun a _ h => (List.idxOf_inj (hs a)).mp h⟩

end Num

/-! ### The generic exit layer -/

/-- **Exit layer from a CTSH simulation theorem.** `T` started at `c₀` halts, at a configuration
    of the shape `Fin f`, whenever the CTSH `C` halts at `f` from `(w, 0)`; it does not halt when
    `C` does not; and the shape `Fin f` reads back to `f` (relation `R`). Then `numT N T` at
    `numCfg N δ c₀` run-level simulates `C` at `(w, 0)` with readback `R`. -/
theorem runSim_of_sim {Q P S : Type} (N : Numbering Q P S) (T : Machine Q P S) (δ : ℤ)
    (C : CTSH) (w : List Ch) (c₀ : Cfg Q P S) (Fin : CTSH.ID → Cfg Q P S → Prop)
    (R : CTSH.ID → Spec.ID → Prop)
    (hF : ∀ n f, CHaltsIn C n (w, 0) f → ∃ M e, HaltsIn T M c₀ e ∧ Fin f e)
    (hNH : (∀ n f, ¬ CHaltsIn C n (w, 0) f) → ∀ M e, ¬ HaltsIn T M c₀ e)
    (hR : ∀ f e, Halting C f → Fin f e → R f (numCfg N δ e)) :
    RunSim (CStep C) (Halting C) (Spec.Step (numT N T)) (Spec.Halted (numT N T)) R
      (w, 0) (numCfg N δ c₀) := by
  refine ⟨fun y hy => ?_, fun hn hU => ?_⟩
  · obtain ⟨n, hn⟩ := U10_8.cstepN_of_rtg hy.1
    obtain ⟨M, e, he, hfin⟩ := hF n y ⟨hn, hy.2⟩
    exact ⟨_, (haltsAt_numCfg_iff T δ _ _).mpr ⟨M, e, he, rfl⟩, hR y e hy.2 hfin⟩
  · obtain ⟨γ, hγ⟩ := hU
    obtain ⟨M, c', h, -⟩ := (haltsAt_numCfg_iff (N := N) T δ _ γ).mp hγ
    exact hNH (fun n f hc => hn ⟨f, U10_8.rtg_of_cstepN hc.1, hc.2⟩) M c' h

/-- The window code read as one list (left end first). -/
theorem window_whole (s : ℕ) (L : List ℕ) (p : ℕ) :
    (window s L p).2.1.reverse ++ (window s L p).2.2 = L := by simp [window]

theorem window_st (s : ℕ) (L : List ℕ) (p : ℕ) : (window s L p).1 = s := rfl

/-- A typed configuration with a finite list tape has its window as a code; a readout that is
    right on the window is right on some code of the numbered configuration. -/
theorem read_of_tp {Q P S α : Type} (N : Numbering Q P S) (bk : S) (hbk : N.sym bk = 0) (δ : ℤ)
    (q : Tgt Q P) (L : List S) (p : ℕ) (hp : p ≤ L.length) (readN : Spec.Code → Option α) (v : α)
    (h : readN (window (N.st q) (L.map N.sym) p) = some v) :
    ∃ g, Spec.toID (numCfg N δ ⟨q, p, CTSH.Sim.tp bk L⟩).pos g = numCfg N δ ⟨q, p, CTSH.Sim.tp bk L⟩ ∧
      readN g = some v :=
  ⟨_, (numCfg_tp bk hbk δ q L p hp).symm, h⟩

/-! ### Readouts that ignore trailing blanks -/

/-- **A readout of the state and the whole window list that ignores blanks appended on either
    side depends only on the ID.** -/
theorem read_toID {α : Type} (f : ℕ → List ℕ → α)
    (hl : ∀ s k L, f s (List.replicate k 0 ++ L) = f s L)
    (hr : ∀ s k L, f s (L ++ List.replicate k 0) = f s L)
    {p : ℤ} {g g' : Spec.Code} (h : Spec.toID p g = Spec.toID p g') :
    f g.1 (g.2.1.reverse ++ g.2.2) = f g'.1 (g'.2.1.reverse ++ g'.2.2) := by
  obtain ⟨hs, hl', hr'⟩ := Spec.CodePad.getD_of_toID h
  obtain ⟨m, k, k', e1, e2⟩ := Spec.CodePad.pad_of_getD _ _ hl'
  obtain ⟨m', j, j', e3, e4⟩ := Spec.CodePad.pad_of_getD _ _ hr'
  obtain ⟨s, l, r⟩ := g
  obtain ⟨s', l', r'⟩ := g'
  simp only at hs e1 e2 e3 e4
  subst hs e1 e2 e3 e4
  simp only [List.reverse_append, List.reverse_replicate, List.append_assoc]
  rw [hl, ← List.append_assoc, hr, hl, ← List.append_assoc, hr]

end URTM.Univ.NumGen
