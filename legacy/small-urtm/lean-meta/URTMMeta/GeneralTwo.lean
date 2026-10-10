import URTMMeta.SpecThm

namespace URTM.Spec
open URTM URTM.Meta

def stayTable (T : List Quint) (q₀ q₁ : ℕ) : List Quint :=
  T.filter (fun r => decide (r.q = q₀ ∨ r.q = q₁))

theorem mem_stayTable {T : List Quint} {q₀ q₁ : ℕ} {r : Quint} :
    r ∈ stayTable T q₀ q₁ ↔ r ∈ T ∧ (r.q = q₀ ∨ r.q = q₁) := by
  simp [stayTable]

theorem stay_det {T : List Quint} {q₀ q₁ : ℕ} (h : Deterministic T) :
    Deterministic (stayTable T q₀ q₁) := by
  intro r₁ h₁ r₂ h₂ hp hs
  exact h r₁ (mem_stayTable.mp h₁).1 r₂ (mem_stayTable.mp h₂).1 hp hs

theorem stay_rev {T : List Quint} {q₀ q₁ : ℕ} (h : Reversible T) :
    Reversible (stayTable T q₀ q₁) := by
  intro r₁ h₁ r₂ h₂ hne hq
  exact h r₁ (mem_stayTable.mp h₁).1 r₂ (mem_stayTable.mp h₂).1 hne hq

theorem stay_step {T : List Quint} {q₀ q₁ : ℕ} {c c' : ID}
    (h : Step (stayTable T q₀ q₁) c c') : Step T c c' := by
  obtain ⟨r, hr, ha, he⟩ := h
  exact ⟨r, (mem_stayTable.mp hr).1, ha, he⟩

theorem stay_halted_of_halted {T : List Quint} {q₀ q₁ : ℕ} {c : ID}
    (h : Halted T c) : Halted (stayTable T q₀ q₁) c := by
  intro r hr
  exact h r (mem_stayTable.mp hr).1

theorem stay_step_of_not_halted {T : List Quint} {q₀ q₁ : ℕ} {c c' : ID}
    (hdet : Deterministic T) (hs : Step T c c')
    (hh : ¬ Halted (stayTable T q₀ q₁) c) :
    Step (stayTable T q₀ q₁) c c' := by
  classical
  obtain ⟨r, hr, ha, he⟩ := hs
  unfold Halted at hh
  push Not at hh
  obtain ⟨r', hr', ha'⟩ := hh
  change r'.p = c.st ∧ r'.s = c.tape c.pos at ha'
  change r.p = c.st ∧ r.s = c.tape c.pos at ha
  have heq := hdet r' (mem_stayTable.mp hr').1 r hr
    (ha'.1.trans ha.1.symm) (ha'.2.trans ha.2.symm)
  subst r'
  exact ⟨r, hr', ha, he⟩

theorem terminal_step_halted {T : List Quint} {q₀ q₁ : ℕ} {c c' : ID}
    (hsrc : ∀ r ∈ T, r.p = q₀ ∨ r.p = q₁)
    (hh : Halted (stayTable T q₀ q₁) c)
    (hs : Step T c c') : Halted T c' := by
  obtain ⟨r, hr, ha, rfl⟩ := hs
  have hq : ¬ (r.q = q₀ ∨ r.q = q₁) := by
    intro hq
    exact hh r (mem_stayTable.mpr ⟨hr, hq⟩) ha
  intro r' hr' ha'
  have hp := hsrc r' hr'
  simp only [Applicable, apply] at ha'
  exact hq (hp.elim (fun h => Or.inl (ha'.1.symm.trans h))
    (fun h => Or.inr (ha'.1.symm.trans h)))

theorem halts_iff_stay {T : List Quint} {q₀ q₁ : ℕ}
    (hdet : Deterministic T)
    (hsrc : ∀ r ∈ T, r.p = q₀ ∨ r.p = q₁) (c : ID) :
    Halts T c ↔ Halts (stayTable T q₀ q₁) c := by
  classical
  constructor
  · rintro ⟨c', hr, hh⟩
    induction hr using Relation.ReflTransGen.head_induction_on with
    | refl => exact ⟨c', Relation.ReflTransGen.refl, stay_halted_of_halted hh⟩
    | @head a b hs _ ih =>
      by_cases hc : Halted (stayTable T q₀ q₁) a
      · exact ⟨a, Relation.ReflTransGen.refl, hc⟩
      · obtain ⟨d, hd, hh'⟩ := ih
        exact ⟨d, Relation.ReflTransGen.head (stay_step_of_not_halted hdet hs hc) hd, hh'⟩
  · rintro ⟨c', hr, hh⟩
    have hreach : Relation.ReflTransGen (Step T) c c' := by
      induction hr using Relation.ReflTransGen.head_induction_on with
      | refl => exact Relation.ReflTransGen.refl
      | head hs _ ih => exact Relation.ReflTransGen.head (stay_step hs) ih
    by_cases hhalt : Halted T c'
    · exact ⟨c', hreach, hhalt⟩
    · unfold Halted at hhalt
      push Not at hhalt
      obtain ⟨r, hr', ha⟩ := hhalt
      let d := apply r c'
      have hs : Step T c' d := ⟨r, hr', ha, rfl⟩
      exact ⟨d, Relation.ReflTransGen.tail hreach hs,
        terminal_step_halted hsrc hh hs⟩

theorem stay_two_state {T : List Quint} {q₀ q₁ : ℕ}
    (hdet : Deterministic T) (hrev : Reversible T)
    (hne : q₀ ≠ q₁)
    (hsrc : ∀ r ∈ T, r.p = q₀ ∨ r.p = q₁) :
    TwoStateRTM (stayTable T q₀ q₁) q₀ q₁ (max q₀ q₁ + 1) where
  det := stay_det hdet
  rev := stay_rev hrev
  ne := hne
  f0 := by omega
  f1 := by omega
  src := by
    intro r hr
    exact hsrc r (mem_stayTable.mp hr).1
  dst := by
    intro r hr
    exact (mem_stayTable.mp hr).2.elim (fun h => Or.inl h) (fun h => Or.inr (Or.inl h))

theorem halting_decidable_general {T : List Quint} {q₀ q₁ : ℕ}
    (hdet : Deterministic T) (hrev : Reversible T)
    (hne : q₀ ≠ q₁)
    (hsrc : ∀ r ∈ T, r.p = q₀ ∨ r.p = q₁) :
    ComputablePred fun x : ℤ × Code => Halts T (toID x.1 x.2) := by
  have h := halting_decidable (stay_two_state hdet hrev hne hsrc)
  have heq : (fun x : ℤ × Code => Halts T (toID x.1 x.2)) =
      (fun x : ℤ × Code => Halts (stayTable T q₀ q₁) (toID x.1 x.2)) := by
    funext x
    exact propext (halts_iff_stay hdet hsrc _)
  rw [heq]
  exact h

theorem simulates_halting_computable_general {U T : List Quint} {q₀ q₁ : ℕ}
    (hdet : Deterministic U) (hrev : Reversible U)
    (hne : q₀ ≠ q₁)
    (hsrc : ∀ r ∈ U, r.p = q₀ ∨ r.p = q₁)
    (hs : Simulates U T) :
    ∃ f : Code → Bool, Computable f ∧
      ∀ a, IsIDOf T (toID 0 a) → (Halts T (toID 0 a) ↔ f a = true) := by
  obtain ⟨c, d, hc, -, h⟩ := hs
  obtain ⟨g, hg, hge⟩ := ComputablePred.computable_iff.mp
    (halting_decidable_general hdet hrev hne hsrc)
  refine ⟨fun a => g (0, c a), hg.comp (Computable.pair (Computable.const _) hc),
    fun a ha => ?_⟩
  have hiff : Halts T (toID 0 a) ↔ Halts U (toID 0 (c a)) := by
    constructor
    · rintro ⟨β, hβ⟩
      obtain ⟨γ, hγ, -⟩ := (h a ha).1 β hβ
      exact ⟨γ, hγ⟩
    · intro hU'; by_contra hn; exact (h a ha).2 hn hU'
  rw [hiff]
  exact iff_of_eq (congrFun hge (0, c a))

theorem no_two_state_URTM_general {U : List Quint} {q₀ q₁ : ℕ}
    (hdet : Deterministic U) (hrev : Reversible U)
    (hne : q₀ ≠ q₁)
    (hsrc : ∀ r ∈ U, r.p = q₀ ∨ r.p = q₁) : ¬ IsUTM U := by
  rintro ⟨c, d, hc, hd, h⟩
  have hs : Simulates U (tm (tmIndex URTM.Meta.tblU)) :=
    ⟨fun a => c (tmIndex URTM.Meta.tblU, a), d,
      hc.comp (Computable.pair (Computable.const _) Computable.id),
      hd, fun a ha => h (tmIndex URTM.Meta.tblU) a ha⟩
  rw [tm_tmIndex_tblU] at hs
  obtain ⟨f, hf, hfe⟩ := simulates_halting_computable_general hdet hrev hne hsrc hs
  apply URTM.Meta.tblU_undecidable
  refine ComputablePred.computable_iff.mpr
    ⟨fun x => f (URTM.Meta.zidU x), hf.comp URTM.Meta.zidU_primrec.to_comp, ?_⟩
  funext x
  apply propext
  rw [← halts_toID_iff tblU_det 0]
  exact hfe (URTM.Meta.zidU x) (isIDOf_of_IDOf (URTM.Meta.IDOf_tblU_zidU x) 0)

theorem two_sources_of_count {T : List Quint}
    (hcount : (T.map Quint.p).dedup.length = 2) :
    ∃ q₀ q₁ : ℕ, q₀ ≠ q₁ ∧ ∀ r ∈ T, r.p = q₀ ∨ r.p = q₁ := by
  classical
  obtain ⟨q₀, q₁, hqs⟩ := List.length_eq_two.mp hcount
  refine ⟨q₀, q₁, ?_, ?_⟩
  · have hn : [q₀, q₁].Nodup := hqs ▸ List.nodup_dedup (T.map Quint.p)
    exact (List.nodup_cons.mp hn).1 ∘ (by simp : q₀ = q₁ → q₀ ∈ [q₁])
  · intro r hr
    have hm : r.p ∈ (T.map Quint.p).dedup :=
      List.mem_dedup.mpr (List.mem_map.mpr ⟨r, hr, rfl⟩)
    rw [hqs] at hm
    simpa using hm

theorem no_two_state_URTM_count {U : List Quint}
    (hdet : Deterministic U) (hrev : Reversible U)
    (hcount : (U.map Quint.p).dedup.length = 2) : ¬ IsUTM U := by
  obtain ⟨q₀, q₁, hne, hsrc⟩ := two_sources_of_count hcount
  exact no_two_state_URTM_general hdet hrev hne hsrc

theorem halting_decidable_count {T : List Quint}
    (hdet : Deterministic T) (hrev : Reversible T)
    (hcount : (T.map Quint.p).dedup.length = 2) :
    ComputablePred fun x : ℤ × Code => Halts T (toID x.1 x.2) := by
  obtain ⟨q₀, q₁, hne, hsrc⟩ := two_sources_of_count hcount
  exact halting_decidable_general hdet hrev hne hsrc

/-- The theorem covers a table with two distinct terminal destinations. -/
example : ¬ IsUTM [⟨0, 0, 0, .R, 2⟩, ⟨1, 0, 0, .R, 3⟩] := by
  apply no_two_state_URTM_count
  · simp [Deterministic]
  · simp [Reversible]
  · decide

end URTM.Spec
