/-
  **Repeated quintuples do not matter** (results/symmerge-relaxed-2026-10-29).

  The symbol merges of results/symmerge-relaxed-2026-10-29 may send two quintuples of the block
  table to the same quintuple (the merge of the read symbols and of the written symbols makes the
  two rules coincide). The list `mapQ h UB` then has repeated entries; the table is the list with
  the repeats removed (`List.dedup`). Every notion of `Spec` and `Strict` reads a table only through
  membership (`Step`, `Halted`, `IsIDOf` through `states`/`symbols`, `Deterministic`), so two lists
  with the same members are interchangeable:

  * `isUTMStrict_congr`: `IsUTMStrict T ↔ IsUTMStrict T'` when `T` and `T'` have the same members.
  * `deterministic_congr`: the same for `Deterministic`.
  * `mem_dropT_congr`: removing the same quintuples `H` keeps the members equal.
-/
import LeanUniv.DropGen

namespace URTM.Univ.SymMergeDedup
open URTM URTM.Spec

variable {T T' : List Quint}

theorem step_eq (h : ∀ r, r ∈ T ↔ r ∈ T') : Step T = Step T' := by
  funext c c'
  apply propext
  simp only [Step, h]

theorem halted_eq (h : ∀ r, r ∈ T ↔ r ∈ T') : Halted T = Halted T' := by
  funext c
  apply propext
  simp only [Halted, h]

theorem isIDOf_eq (h : ∀ r, r ∈ T ↔ r ∈ T') : IsIDOf T = IsIDOf T' := by
  funext c
  apply propext
  simp only [IsIDOf, states, symbols, List.mem_flatMap, h]

theorem haltsAt_eq (h : ∀ r, r ∈ T ↔ r ∈ T') : HaltsAt T = HaltsAt T' := by
  funext c c'
  unfold HaltsAt
  rw [step_eq h, halted_eq h]

theorem halts_eq (h : ∀ r, r ∈ T ↔ r ∈ T') : Halts T = Halts T' := by
  funext c
  unfold Halts
  rw [haltsAt_eq h]

/-- **`IsUTMStrict` depends only on the members of the table.** -/
theorem isUTMStrict_congr (h : ∀ r, r ∈ T ↔ r ∈ T') : IsUTMStrict T ↔ IsUTMStrict T' := by
  unfold IsUTMStrict
  rw [isIDOf_eq h, haltsAt_eq h, halts_eq h]

/-- `Deterministic` depends only on the members of the table. -/
theorem deterministic_congr (h : ∀ r, r ∈ T ↔ r ∈ T') : Deterministic T ↔ Deterministic T' := by
  simp only [Deterministic, h]

/-- Removing the same quintuples from two tables with the same members. -/
theorem mem_dropT_congr (h : ∀ r, r ∈ T ↔ r ∈ T') (H : List Quint) :
    ∀ r, r ∈ DropGen.dropT T H ↔ r ∈ DropGen.dropT T' H := fun r => by
  simp only [DropGen.mem_dropT, h]

end URTM.Univ.SymMergeDedup
