/-
  `IsUTM_MoritaOver` の**記号を空白と 1 つの記号に限った形**が空虚に偽でないこと。**手書き**。

  `MoritaOverSat.exists_moritaOver_of_strict` が示したのは、記号の条件を機械に現れるすべての記号
  （`symbols U`）とした形だった。ここでは、記号数が 2（`NSyms U = 2`、空白ともう 1 つ）の機械なら、
  現れる記号は 0 と 1 つの σ ≠ 0 に限られるので、単調性 `IsUTM_MoritaOver.mono` で `[σ]` の形へ移せることを示す。
  仮定は lean-univ の存在定理（例えば `URTM.Univ.Final85_2.exists_urtm_85_2`）の文の形そのもので、
  二つの lake 環境をまたぐ点は `exists_moritaOver_of_strict` と同じ（定義の写しの字句の一致に依る）。

  既存の定理の文は変えない（追加だけ）。
-/
import URTMMeta.ThreeStrict
import URTMMeta.MoritaOverSat

namespace URTM.Meta.Sat
open URTM URTM.Spec

/-- 記号数が 2 の表に現れる記号は、空白 0 と、0 でないある 1 つの記号 σ に限られる。 -/
theorem symbols_of_nsyms_two {U : List Quint} (h : NSyms U = 2) :
    ∃ σ : ℕ, σ ≠ 0 ∧ ∀ a ∈ symbols U, a = 0 ∨ a = σ := by
  have h' : (0 :: symbols U).dedup.length = 2 := h
  obtain ⟨x, y, hxy⟩ := List.length_eq_two.mp h'
  have hne : x ≠ y := by
    have hnd := List.nodup_dedup (0 :: symbols U)
    rw [hxy] at hnd
    simpa using hnd
  have hmem : ∀ a, a ∈ (0 :: symbols U) → a = x ∨ a = y := fun a ha => by
    have : a ∈ (0 :: symbols U).dedup := List.mem_dedup.mpr ha
    rw [hxy] at this
    simpa using this
  rcases hmem 0 (by simp) with h0 | h0
  · exact ⟨y, fun e => hne (h0.symm.trans e.symm),
      fun a ha => (hmem a (by simp [ha])).imp (fun e => e.trans h0.symm) id⟩
  · exact ⟨x, fun e => hne (e.trans h0),
      fun a ha => (hmem a (by simp [ha])).symm.imp (fun e => e.trans h0.symm) id⟩

/-- **系**: lean-univ の存在定理の形の仮定（記号数 2）から、記号の条件を空白と 1 つの記号 σ（σ ≠ 0、
    表に現れる記号は 0 と σ だけ）に限った `IsUTM_MoritaOver U [σ]` を満たす決定的・可逆な表が存在する。 -/
theorem exists_moritaOver_single_of_strict {m : ℕ}
    (h : ∃ U : List Quint, Spec.Deterministic U ∧ Reversible U ∧ NStates U = m ∧ NSyms U = 2 ∧
      IsUTMStrict U) :
    ∃ (U : List Quint) (σ : ℕ), Spec.Deterministic U ∧ Reversible U ∧ NStates U = m ∧
      NSyms U = 2 ∧ σ ≠ 0 ∧ (∀ a ∈ symbols U, a = 0 ∨ a = σ) ∧ IsUTM_MoritaOver U [σ] := by
  obtain ⟨U, h1, h2, h3, h4, h5⟩ := h
  obtain ⟨σ, hσ0, hσ⟩ := symbols_of_nsyms_two h4
  exact ⟨U, σ, h1, h2, h3, h4, hσ0, hσ, (IsUTMStrict.moritaOver h1 h5).mono fun a ha =>
    (hσ a ha).imp_right List.mem_singleton.mpr⟩

end URTM.Meta.Sat
