/-
  Morita 2017 の Lemma 5.9（1WU-RTM 化、`Conv59`）と Lemma 5.10（3 状態化、`Conv510`）が
  **可逆性を保存する**ことの一般の証明。

  これまで URTM(3,36654) の可逆性は Lean に無く（決定性だけ `Conv59.conv_det`・`Conv510.conv_det`）、
  Python の検査器（層2）に頼っていた。ここで 2 段とも可逆性の保存を示し、(3,36654) の可逆性を
  (32,3) の可逆性（`Gen.K32_3.hR`、カーネルの `decide`）から導けるようにする。

  * `Conv59.conv_rev`  : T が可逆で、qp の状態にはどれも右移動で入る規則があるなら
                         T̂ も可逆（0 シフト・停止規則の有無は問わない）。
  * `Conv510.conv_rev` : T̂ が可逆で、規則の形が 1WU-RTM のもの、q_L 以外の番号が単射で 1 以上なら T† も可逆。

  mathlib 非依存。未証明の穴・新規公理・native_decide を使わない。
-/
import URTM.Conv59
import URTM.Conv510

namespace URTM.ConvRev

open URTM URTM.KState URTM.CTSH URTM.SimLemmas

/-! ## 1. Lemma 5.9 -/

section C59
open URTM.Conv59

variable {Q P S : Type} [DecidableEq Q] [DecidableEq S]

/-- 可逆な T で、同じ状態に入る 2 本の規則の方向は同じ（異なる規則なら可逆性から、同じ規則なら自明）。 -/
theorem same_dir {T : Machine Q P S} (hR : Reversible T) {r₁ r₂ : Rule Q P S} (h₁ : r₁ ∈ T) (h₂ : r₂ ∈ T)
    (hq : r₁.q = r₂.q) : r₁.d = r₂.d := by
  by_cases e : r₁ = r₂
  · rw [e]
  · exact (hR r₁ h₁ r₂ h₂ e hq).1

/-- 可逆な T で、同じ状態に同じ記号を書いて入る 2 本の規則は等しい。 -/
theorem same_rule {T : Machine Q P S} (hR : Reversible T) {r₁ r₂ : Rule Q P S} (h₁ : r₁ ∈ T) (h₂ : r₂ ∈ T)
    (hq : r₁.q = r₂.q) (ht : r₁.t = r₂.t) : r₁ = r₂ := by
  by_cases e : r₁ = r₂
  · exact e
  · exact absurd ht (hR r₁ h₁ r₂ h₂ e hq).2

/-- rule35 の形（左移動なら δ̂3/δ̂4、それ以外は δ̂5）。 -/
theorem rule35_cases (T : Machine Q P S) (r : Rule Q P S) (p' : Q) (s u : S) :
    (r.d = .L ∧ rule35 T r p' s u =
        ⟨.q s, .hp r.p r.s u, .hp p' s r.t, .R, .go (if has T p' s then .q u else .h u)⟩) ∨
    (r.d ≠ .L ∧ rule35 T r p' s u = ⟨.q s, .hp r.p r.s u, .pr s r.t, .R, .go (.qp p' u)⟩) := by
  unfold rule35
  by_cases h : r.d = .L
  · exact .inl ⟨h, by simp [h]⟩
  · exact .inr ⟨h, by simp [h]⟩

/-- δ̂6/δ̂7（現状態 q(p', u)）の p' は qp から来る。 -/
theorem qp_of_mem {T : Machine Q P S} {s0 : S} {ss : List S} {qs qp : List Q} {ρ : Rule (WSt Q S) P (WSym Q S)}
    (h : ρ ∈ Conv59.conv T s0 ss qs qp) {p' : Q} {u : S} (hp : ρ.p = .qp p' u) : p' ∈ qp := by
  unfold Conv59.conv at h
  simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_cons, List.not_mem_nil,
    or_false] at h
  rcases h with (((((((h | ⟨_, _, _, _, _, _, h⟩) | ⟨r, _, h⟩) | ⟨p₁, hp₁, _, _, _, _, _, _, h⟩) | ⟨_, _, h⟩) | h) |
    ⟨_, _, _, _, h⟩) | ⟨_, _, _, _, _, _, h⟩) | ⟨_, _, _, _, _, _, h⟩
  · subst h; cases hp
  · subst h; cases hp
  · simp only [ruleRules] at h
    split at h
    · simp only [List.mem_flatMap, List.mem_map] at h
      obtain ⟨s, _, u, _, h⟩ := h
      subst h; rw [rule35_p] at hp; cases hp
    · simp at h
  · subst h; simp only [WSt.qp.injEq] at hp; rw [← hp.1]; exact hp₁
  all_goals (subst h; cases hp)

/-- **Lemma 5.9 の可逆性の保存**。`hqp'` は「qp の状態には右移動で入る規則がある」（Hyp.hqp の逆向き）。 -/
theorem conv59_rev {T : Machine Q P S} {s0 : S} {ss : List S} {qs qp : List Q}
    (hR : Reversible T)
    (hqp' : ∀ p' ∈ qp, ∃ r ∈ T, r.q = .go p' ∧ r.d = .R) :
    Reversible (Conv59.conv T s0 ss qs qp) := by
  -- δ̂3/δ̂4 の行き先 p' は左移動で入る状態、δ̂6/δ̂7 の p' は右移動で入る状態なので衝突しない。
  have hLR : ∀ r ∈ T, ∀ p', r.q = .go p' → r.d = .L → p' ∉ qp := by
    intro r hr p' hq hd hp
    obtain ⟨r', hr', hq', hd'⟩ := hqp' p' hp
    have := same_dir hR hr hr' (hq.trans hq'.symm)
    rw [hd, hd'] at this; cases this
  intro ρ₁ h₁ ρ₂ h₂ hne hq
  rcases mem_conv h₁ with rfl | ⟨s, t, u, rfl⟩ | ⟨r, hr, p', hrq, s, u, rfl⟩ | ⟨p', u, s, t, rfl⟩ | ⟨s, rfl⟩ | rfl |
    ⟨s, t, rfl⟩ | ⟨p, s, t, rfl⟩ | ⟨s, t, u, rfl⟩ <;>
  rcases mem_conv h₂ with rfl | ⟨s₂, t₂, u₂, rfl⟩ | ⟨r₂, hr₂, p₂, hrq₂, s₂, u₂, rfl⟩ | ⟨p₂, u₂, s₂, t₂, rfl⟩ |
    ⟨s₂, rfl⟩ | rfl | ⟨s₂, t₂, rfl⟩ | ⟨p₂, s₂, t₂, rfl⟩ | ⟨s₂, t₂, u₂, rfl⟩
  all_goals (try (rcases rule35_cases T r p' s u with ⟨hd1, e1⟩ | ⟨hd1, e1⟩ <;> rw [e1] at hne hq ⊢))
  all_goals (try (rcases rule35_cases T r₂ p₂ s₂ u₂ with ⟨hd2, e2⟩ | ⟨hd2, e2⟩ <;> rw [e2] at hne hq ⊢))
  all_goals (try (split at hq))
  all_goals (try (split at hq))
  all_goals (simp only [Tgt.go.injEq, WSt.q.injEq, WSt.h.injEq, WSt.qp.injEq, reduceCtorEq, ne_eq,
    WSym.pr.injEq, WSym.hp.injEq, Rule.mk.injEq, true_and, and_true, not_and] at hq hne ⊢)
  all_goals (try simp_all)
  all_goals first
    | (intro hp hs ht; subst hp
       have e := same_rule hR hr hr₂ (hrq.trans hrq₂.symm) ht; subst e; exact hne hs rfl rfl rfl ht)
    | (intro hs ht; obtain ⟨hp, _⟩ := hq; subst hp
       have e := same_rule hR hr hr₂ (hrq.trans hrq₂.symm) ht; subst e; exact hne hs rfl rfl ht)
    | (intro hp _ _; subst hp; exact absurd (qp_of_mem h₂ rfl) (hLR r hr _ hrq hd1))
    | (intro hp _ _; subst hp; exact absurd (qp_of_mem h₁ rfl) (hLR r₂ hr₂ _ hrq₂ hd2))

end C59

/-! ## 2. Lemma 5.10 -/

section C510
open URTM.Conv510
open URTM.Conv55 (FSym)

variable {Q P S : Type} [DecidableEq Q] [DecidableEq S]

/-- **Lemma 5.10 の可逆性の保存**: T̂ が可逆で、規則の形が 1WU-RTM のもの、q_L 以外の番号が単射なら T† も可逆。 -/
theorem conv510_rev {T : Machine Q P S} {qL : Q} {s0 : S} {idx : Q → Nat} {m : Nat} {ss : List S}
    (hR : Reversible T) (hsh : ∀ r ∈ T, shapeOK qL s0 r = true)
    (hinj : ∀ p q, p ≠ qL → q ≠ qL → idx p = idx q → p = q) :
    Reversible (Conv510.conv T qL s0 idx m ss) := by
  -- 同じ状態に同じ記号を書いて入る T̂ の規則は等しいので、変換後の規則も等しい。
  have same : ∀ {r₁ r₂ : Rule Q P S} {ρ₁ ρ₂ : Rule TSt P (FSym S)}, r₁ ∈ T → r₂ ∈ T →
      convRule qL idx r₁ = some ρ₁ → convRule qL idx r₂ = some ρ₂ → r₁.q = r₂.q → r₁.t = r₂.t → ρ₁ = ρ₂ := by
    intro r₁ r₂ ρ₁ ρ₂ hr₁ hr₂ e₁ e₂ hq ht
    have e : r₁ = r₂ := by
      by_cases e : r₁ = r₂
      · exact e
      · exact absurd ht (hR r₁ hr₁ r₂ hr₂ e hq).2
    subst e; rw [e₁] at e₂; cases e₂; rfl
  intro ρ₁ h₁ ρ₂ h₂ hne hq
  rcases mem_conv h₁ with ⟨r₁, hr₁, e₁⟩ | ⟨u₁, _, h₁⟩ <;> rcases mem_conv h₂ with ⟨r₂, hr₂, e₂⟩ | ⟨u₂, _, h₂⟩
  · obtain ⟨q₁, hq₁, c₁⟩ := convRule_spec e₁
    obtain ⟨q₂, hq₂, c₂⟩ := convRule_spec e₂
    rcases c₁ with ⟨p₁, d₁, rfl⟩ | ⟨p₁, d₁, rfl⟩ | ⟨p₁, d₁, rfl⟩ <;>
      rcases c₂ with ⟨p₂, d₂, rfl⟩ | ⟨p₂, d₂, rfl⟩ | ⟨p₂, d₂, rfl⟩ <;>
      simp only [Tgt.go.injEq, reduceCtorEq, ne_eq, FSym.dn.injEq, FSym.pl.injEq, not_and, true_and] at hq ⊢
    -- 行き先 R0 どうし（δ1†, δ2†）: 書込 [t, idx q↓] が等しければ q も等しい（番号の単射性）。
    all_goals (try (intro ht hi
                    have hqq := hinj _ _ (shape_R (hsh r₁ hr₁) d₁ hq₁) (shape_R (hsh r₂ hr₂) d₂ hq₂) hi
                    subst hqq
                    exact hne (same hr₁ hr₂ e₁ e₂ (hq₁.trans hq₂.symm) ht)))
    -- 行き先 L どうし（δ7†）: どちらも q_L に入る。
    all_goals (try (intro ht
                    have a₁ := Tgt.go.inj (hq₁.symm.trans (shape_L (hsh r₁ hr₁) d₁ p₁).2)
                    have a₂ := Tgt.go.inj (hq₂.symm.trans (shape_L (hsh r₂ hr₂) d₂ p₂).2)
                    subst a₁ a₂
                    exact hne (same hr₁ hr₂ e₁ e₂ (hq₁.trans hq₂.symm) ht)))
  · obtain ⟨q₁, hq₁, c₁⟩ := convRule_spec e₁
    rcases c₁ with ⟨p₁, d₁, rfl⟩ | ⟨p₁, d₁, rfl⟩ | ⟨p₁, d₁, rfl⟩ <;>
      rcases sym_spec h₂ with rfl | rfl | ⟨hu, rfl⟩ | ⟨k, _, rfl | rfl⟩ <;>
      simp only [Tgt.go.injEq, reduceCtorEq, ne_eq, FSym.pl.injEq, true_and, not_false_eq_true] at hq ⊢
    intro ht; exact hu (ht ▸ (shape_L (hsh r₁ hr₁) d₁ p₁).1)
  · obtain ⟨q₂, hq₂, c₂⟩ := convRule_spec e₂
    rcases c₂ with ⟨p₂, d₂, rfl⟩ | ⟨p₂, d₂, rfl⟩ | ⟨p₂, d₂, rfl⟩ <;>
      rcases sym_spec h₁ with rfl | rfl | ⟨hu, rfl⟩ | ⟨k, _, rfl | rfl⟩ <;>
      simp only [Tgt.go.injEq, reduceCtorEq, ne_eq, FSym.pl.injEq, true_and, not_false_eq_true] at hq ⊢
    intro ht; exact hu (ht.symm ▸ (shape_L (hsh r₂ hr₂) d₂ p₂).1)
  · rcases sym_spec h₁ with rfl | rfl | ⟨_, rfl⟩ | ⟨k, _, rfl | rfl⟩ <;>
      rcases sym_spec h₂ with rfl | rfl | ⟨_, rfl⟩ | ⟨k', _, rfl | rfl⟩ <;>
      simp only [Tgt.go.injEq, reduceCtorEq, ne_eq, FSym.pl.injEq, FSym.up.injEq, FSym.dn.injEq, true_and,
        not_and, Rule.mk.injEq, and_true, not_false_eq_true] at hq hne ⊢
    all_goals first
      | (intro h; exact hne h h)
      | (intro h _; omega)
      | (intro h h'; exact hne ⟨h, by omega⟩ h h')

end C510

end URTM.ConvRev
