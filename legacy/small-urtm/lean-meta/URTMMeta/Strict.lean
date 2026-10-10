/-
  **Morita Def. 7.1, strict form, and faithful state/symbol counts** (docs/24 §1).

  `Spec.IsUTM` (the copy in `LeanUniv/Spec.lean`, text-identical to
  `legacy/small-urtm/lean-meta/URTMMeta/Spec.lean`) drops Morita's requirement
  `c(n, α) ∈ ID(U)` (Def. 7.1: `c : ℕ × I → ID(U)`). That is the safe side for a
  non-existence theorem but the unsafe side for an existence theorem, so the positive
  theorems use `IsUTMStrict`, which restores it. The Spec text itself is unchanged.

  2026-10-03: the output clause of `IsUTMStrict` now quantifies over **all** codes of the
  halting ID (see the docstring; the old form is `IsUTMStrictWeak`). `Spec.IsUTM` keeps the weak
  `∃ g` form: it is only used as the conclusion of non-existence theorems, where weaker is the
  safe side.
-/
import URTMMeta.Spec

namespace URTM.Spec
open URTM

/-- **UTM (Morita Def. 7.1), strict**: as `IsUTM`, and in addition
    * the encoded initial ID `c(n, α)` is an ID of `U` (`c : ℕ × ID(T_n) → ID(U)` in Def. 7.1);
    * the output clause is about the halting **ID** `γ`, not about one chosen code of it:
      `γ` has a code, and **every** code `g` of `γ` (`toID γ.pos g = γ`) is decoded by `d` to a
      code of `β`.

    Why "every code" (audit of 2026-10-03, docs/24 末尾): `toID` reads both lists with the blank
    `0` as default, so one ID has infinitely many codes (append blanks). With `∃ g` (the form of
    `Spec.IsUTM`, kept below as `IsUTMStrictWeak`) a computable `d` that looks up an enumeration
    of codes by the *length* of `g` outputs any `β` from some padding of `g`, so the output
    clause says nothing (`StrictToy.weak_out_vacuous`). Morita's `d : ID(U) → ID(T)` is a map on
    IDs; requiring `d` to be right on all codes of `γ` is the faithful reading. The conjunct
    `∃ g, toID γ.pos g = γ` (γ is finite) keeps the strict form at least as strong as the weak
    one (`IsUTMStrict.weak`). -/
def IsUTMStrict (U : List Quint) : Prop :=
  ∃ (c : ℕ × Code → Code) (d : Code → Option Code), Computable c ∧ Computable d ∧
    ∀ n a, IsIDOf (tm n) (toID 0 a) →
      IsIDOf U (toID 0 (c (n, a))) ∧
      (∀ β, HaltsAt (tm n) (toID 0 a) β →
        ∃ γ, HaltsAt U (toID 0 (c (n, a))) γ ∧ (∃ g, toID γ.pos g = γ) ∧
          ∀ g, toID γ.pos g = γ → ∃ b, d g = some b ∧ toID β.pos b = β) ∧
      (¬ Halts (tm n) (toID 0 a) → ¬ Halts U (toID 0 (c (n, a))))

/-- **The pre-2026-10-03 strict form** (output read off *some* code `g` of the halting ID).
    Kept only to state `IsUTMStrict.weak`; its output clause is vacuous
    (`StrictToy.weak_out_vacuous`). -/
def IsUTMStrictWeak (U : List Quint) : Prop :=
  ∃ (c : ℕ × Code → Code) (d : Code → Option Code), Computable c ∧ Computable d ∧
    ∀ n a, IsIDOf (tm n) (toID 0 a) →
      IsIDOf U (toID 0 (c (n, a))) ∧
      (∀ β, HaltsAt (tm n) (toID 0 a) β →
        ∃ γ, HaltsAt U (toID 0 (c (n, a))) γ ∧
          ∃ g b, toID γ.pos g = γ ∧ d g = some b ∧ toID β.pos b = β) ∧
      (¬ Halts (tm n) (toID 0 a) → ¬ Halts U (toID 0 (c (n, a))))

/-- **New → old**: the strict form implies the pre-2026-10-03 form. -/
theorem IsUTMStrict.weak {U : List Quint} (h : IsUTMStrict U) : IsUTMStrictWeak U := by
  obtain ⟨c, d, hc, hd, h⟩ := h
  refine ⟨c, d, hc, hd, fun n a ha => ⟨(h n a ha).1, fun β hβ => ?_, (h n a ha).2.2⟩⟩
  obtain ⟨γ, hγ, ⟨g, hg⟩, hall⟩ := (h n a ha).2.1 β hβ
  obtain ⟨b, hb, hβb⟩ := hall g hg
  exact ⟨γ, hγ, g, b, hg, hb, hβb⟩

/-- The weak strict form implies Spec's `IsUTM` (it only adds a conjunct). -/
theorem IsUTMStrictWeak.isUTM {U : List Quint} (h : IsUTMStrictWeak U) : IsUTM U := by
  obtain ⟨c, d, hc, hd, h⟩ := h
  exact ⟨c, d, hc, hd, fun n a ha => (h n a ha).2⟩

/-- The strict form implies Spec's `IsUTM`. -/
theorem IsUTMStrict.isUTM {U : List Quint} (h : IsUTMStrict U) : IsUTM U := h.weak.isUTM

/-- **Number of states** in Morita's sense: the distinct *source* states of the quintuples.
    A state with no outgoing quintuple (a halting pseudo-state such as `halt`/`null`) is a
    target only and is not counted. -/
def NStates (U : List Quint) : ℕ := (U.map Quint.p).dedup.length

/-- **Number of symbols** in Morita's sense: the distinct symbols read or written by the
    quintuples, with the blank `0` always counted. -/
def NSyms (U : List Quint) : ℕ := (0 :: symbols U).dedup.length

/-! Sanity checks of the counts on a toy table (`decide` on the kernel). -/

section Examples

/-- Two real states 0, 1 and a pseudo halting state 2 (only a target). Symbols 1, 2, blank 0. -/
private def toy : List Quint :=
  [⟨0, 0, 1, .R, 1⟩, ⟨1, 0, 2, .L, 0⟩, ⟨1, 1, 1, .Z, 2⟩]

example : NStates toy = 2 := by decide
example : NSyms toy = 3 := by decide
/-- The blank is counted even when no quintuple mentions it. -/
example : NSyms [⟨0, 1, 1, .R, 0⟩] = 2 := by decide
example : NStates [] = 0 ∧ NSyms [] = 1 := by decide

end Examples

end URTM.Spec
