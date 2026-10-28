/-
  3 状態 2 記号の URTM の非存在を、**仕様の決定性と可逆性**（`Spec.Deterministic`・`Spec.Reversible`。
  Morita Def. 5.4 と同じく相異なる五つ組の対についての条件）の下で述べる。**手書き**。

  `no_three_two_URTMStrict_all` の仮定 `RTM32` は計算用の検査 `deterministic`・`reversible`
  （リストの異なる位置にある 2 項をすべて比べる）を使うので、同じ五つ組を 2 回並べた表を弾く。
  仕様（`Spec.lean`）では表の意味は `∈` だけを通して決まるので、重複は意味を持たない。
  ここでは表から重複を除き（`List.dedup`）、所属が同じ表は `Spec.IsUTMStrict` の真偽も同じであること
  （`isUTMStrict_congr_mem`）を使って、重複を許す形に移す。

  既存の定理の文は変えない（追加だけ）。
-/
import URTMMeta.ThreeStrictAll

namespace URTM.Meta
open URTM URTM.TwoState URTM.Three

/-! ### 所属が同じ表は同じ意味を持つ -/

section congr
variable {T T' : List Quint}

/-- 所属が同じ表は、1 歩も同じ。 -/
theorem step_congr_mem (h : ∀ r, r ∈ T ↔ r ∈ T') : Spec.Step T = Spec.Step T' := by
  funext c c'
  exact propext ⟨fun ⟨r, hr, hx⟩ => ⟨r, (h r).1 hr, hx⟩, fun ⟨r, hr, hx⟩ => ⟨r, (h r).2 hr, hx⟩⟩

/-- 所属が同じ表は、停止 ID も同じ。 -/
theorem halted_congr_mem (h : ∀ r, r ∈ T ↔ r ∈ T') : Spec.Halted T = Spec.Halted T' := by
  funext c
  exact propext ⟨fun hc r hr => hc r ((h r).2 hr), fun hc r hr => hc r ((h r).1 hr)⟩

theorem haltsAt_congr_mem (h : ∀ r, r ∈ T ↔ r ∈ T') : Spec.HaltsAt T = Spec.HaltsAt T' := by
  funext c c'
  simp only [Spec.HaltsAt, step_congr_mem h, halted_congr_mem h]

theorem halts_congr_mem (h : ∀ r, r ∈ T ↔ r ∈ T') : Spec.Halts T = Spec.Halts T' := by
  funext c
  simp only [Spec.Halts, haltsAt_congr_mem h]

theorem isIDOf_congr_mem (h : ∀ r, r ∈ T ↔ r ∈ T') : Spec.IsIDOf T = Spec.IsIDOf T' := by
  funext c
  simp only [Spec.IsIDOf, Spec.states, Spec.symbols, List.mem_flatMap, h]

/-- **所属が同じ表は、`IsUTMStrict` の真偽も同じ**。 -/
theorem isUTMStrict_congr_mem (h : ∀ r, r ∈ T ↔ r ∈ T') :
    Spec.IsUTMStrict T ↔ Spec.IsUTMStrict T' := by
  simp only [Spec.IsUTMStrict, haltsAt_congr_mem h, halts_congr_mem h, isIDOf_congr_mem h]

end congr

/-! ### 重複の無い列では，相異なる値の対についての条件が Bool の検査になる -/

theorem allPairs_true_iff_pairwise (f : Quint → Quint → Bool) (l : List Quint) :
    allPairs f l = true ↔ l.Pairwise (fun a b => f a b = true) := by
  induction l with
  | nil => simp [allPairs]
  | cons x xs ih => simp [allPairs, List.pairwise_cons, ih, List.all_eq_true]

theorem allPairs_true_of_nodup {f : Quint → Quint → Bool} {l : List Quint} (hl : l.Nodup)
    (h : ∀ a ∈ l, ∀ b ∈ l, a ≠ b → f a b = true) : allPairs f l = true :=
  (allPairs_true_iff_pairwise f l).mpr (hl.pairwise_of_forall_ne h)

/-! ### 主定理（重複を許す形） -/

/-- **主定理（重複を許す形）**: 仕様の意味で決定的かつ可逆で、遷移元が `q₀, q₁, q₂` のどれかで、
    `0` と `σ ≠ 0` だけを読み書きする表は、`IsUTMStrict` の意味で万能でない。
    同じ五つ組を重複して含む表も対象にする（`no_three_two_URTMStrict_all` との違いはそこだけ）。 -/
theorem no_three_two_URTMStrict_spec {U : List Quint} {q₀ q₁ q₂ σ : Nat}
    (hdet : Spec.Deterministic U) (hrev : Spec.Reversible U)
    (n01 : q₀ ≠ q₁) (n02 : q₀ ≠ q₂) (n12 : q₁ ≠ q₂)
    (src : ∀ r ∈ U, r.p = q₀ ∨ r.p = q₁ ∨ r.p = q₂) (sig : σ ≠ 0)
    (sym : ∀ r ∈ U, (r.s = 0 ∨ r.s = σ) ∧ (r.t = 0 ∨ r.t = σ)) :
    ¬ Spec.IsUTMStrict U := by
  have hm : ∀ r, r ∈ U.dedup ↔ r ∈ U := fun r => List.mem_dedup
  have H : RTM32 U.dedup q₀ q₁ q₂ σ :=
    { det := allPairs_true_of_nodup (List.nodup_dedup U) fun a ha b hb hab => by
        have hd := hdet a ((hm a).1 ha) b ((hm b).1 hb)
        by_cases hp : a.p = b.p
        · by_cases hs : a.s = b.s
          · exact absurd (hd hp hs) hab
          · simp [detPair, hs]
        · simp [detPair, hp]
      rev := allPairs_true_of_nodup (List.nodup_dedup U) fun a ha b hb hab => by
        have hr := hrev a ((hm a).1 ha) b ((hm b).1 hb) hab
        by_cases hq : a.q = b.q
        · obtain ⟨hd, ht⟩ := hr hq
          simp [revPair, hd, ht]
        · simp [revPair, hq]
      n01 := n01
      n02 := n02
      n12 := n12
      src := fun r hr => src r ((hm r).1 hr)
      sig := sig
      sym := fun r hr => sym r ((hm r).1 hr) }
  intro hU
  exact no_three_two_URTMStrict_all H ((isUTMStrict_congr_mem hm).2 hU)

end URTM.Meta
