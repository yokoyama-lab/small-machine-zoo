/-
  **Counts through an injective numbering** (for tables too large for `decide`).

  For a typed machine `T` and an injective numbering `N` (`KToSpec.Numbering`), the counts of the
  Spec table `numT N T` are the counts of `T`:

  * `nstates_numT`: `Spec.NStates (numT N T) = SymCount.nst T` (distinct current states);
  * `nsyms_numT`: `Spec.NSyms (numT N T) = SymCount.nsym T` (distinct read or written symbols),
    when some symbol `bk` of `T` is numbered `0` (Spec's blank, which `NSyms` always counts);
  * `symbols_numT`, `mem_states_numT`, `mem_symbols_numT`: the states and symbols of `numT N T`
    are the images of those of `T`.

  No hypothesis on the size of `T`: nothing here evaluates the table.
  No `sorry`, no new axiom, no `native_decide`.
-/
import LeanUniv.KToSpec
import LeanUniv.Strict
import LeanUniv.SymCount

namespace URTM.Univ.NumCount
open URTM URTM.Univ.KToSpec URTM.Univ.SymCount
open URTM.KState (Tgt Machine Rule)

variable {Q P S : Type}

/-- The symbols of the numbered table are the numbered symbols of the typed table. -/
theorem symbols_numT (N : Numbering Q P S) (T : Machine Q P S) :
    Spec.symbols (numT N T) = (syms T).map N.sym := by
  induction T with
  | nil => rfl
  | cons r T ih =>
    simp only [Spec.symbols, numT, syms, List.map_cons, List.flatMap_cons, List.map_append] at ih ⊢
    rw [ih]
    rfl

/-- The current states of the numbered table are the numbered current states. -/
theorem p_numT (N : Numbering Q P S) (T : Machine Q P S) :
    (numT N T).map Quint.p = (T.map (·.p)).map (fun q => N.st (.go q)) := by
  simp only [numT, List.map_map]
  rfl

/-- **The number of states** of a numbered table is that of the typed table. -/
theorem nstates_numT [DecidableEq Q] (N : Numbering Q P S) (T : Machine Q P S) :
    Spec.NStates (numT N T) = nst T := by
  unfold Spec.NStates nst
  rw [p_numT, List.dedup_map_of_injective (fun a b h => Tgt.go.inj (N.st_inj h)), List.length_map]

/-- **The number of symbols** of a numbered table is that of the typed table, when a symbol of
    the typed table is numbered `0` (the blank of Spec, always counted by `NSyms`). -/
theorem nsyms_numT [DecidableEq S] (N : Numbering Q P S) (T : Machine Q P S) (bk : S)
    (hbk : N.sym bk = 0) (hmem : bk ∈ syms T) : Spec.NSyms (numT N T) = nsym T := by
  unfold Spec.NSyms nsym
  rw [symbols_numT, List.dedup_cons_of_mem (hbk ▸ List.mem_map_of_mem hmem),
    List.dedup_map_of_injective N.sym_inj, List.length_map]

/-- A typed rule's current state is a state of the numbered table. -/
theorem mem_states_numT (N : Numbering Q P S) {T : Machine Q P S} {r : Rule Q P S} (hr : r ∈ T) :
    N.st (.go r.p) ∈ Spec.states (numT N T) :=
  List.mem_flatMap.2 ⟨numRule N r, List.mem_map_of_mem hr, by simp [numRule]⟩

/-- A typed rule's read symbol is a symbol of the numbered table. -/
theorem mem_symbols_numT (N : Numbering Q P S) {T : Machine Q P S} {r : Rule Q P S} (hr : r ∈ T) :
    N.sym r.s ∈ Spec.symbols (numT N T) :=
  List.mem_flatMap.2 ⟨numRule N r, List.mem_map_of_mem hr, by simp [numRule]⟩

end URTM.Univ.NumCount
