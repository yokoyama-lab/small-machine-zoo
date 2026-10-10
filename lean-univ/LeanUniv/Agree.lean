/-
  **2 つの URTM を直接比べる**（`IsUTMStrict` の系）。**手書き**。

  `IsUTMStrict U`（`LeanUniv/Strict.lean`、Morita Def. 7.1）は、各 URTM を TM の列挙 `tm n` と比べる定義である。
  ここでは、決定的な 2 つの URTM U₁, U₂ を直接比べる: 同じ `(n, a)` について、U₁ と U₂ は一緒に停止するか
  一緒に停止せず（その停止は `tm n` の停止と一致する）、両方が停止したなら、それぞれの停止 ID のどの符号を
  それぞれの復号器で読んでも、同じ ID β（`tm n` の停止 ID）の符号になる。一致するのは停止と復号した結果であって、
  符号化した入力・実行の過程・歩数は機械ごとに違う。符号化 c₁, c₂ と復号 d₁, d₂ は機械ごとに違ってよい
  （`IsUTMStrict` の存在量化をそのまま取り出す）。決定性は、U の停止 ID が 1 つに決まること（`haltsAt_unique`）に使う。

  文は `legacy/small-urtm/lean-meta/URTMMeta/StrictAgree.lean` の `URTM.Meta.Sat.isUTMStrict_agree` と同じ
  （名前空間だけが違う）。lean-meta の版は lean-univ の定義の写しの上で述べたもので、13 点の存在定理に当てるには
  二つの lake 環境をまたいでいた。この版は lean-univ の中にあるので、13 点の証人に環境をまたがずに当たる
  （`LeanUniv/FinalAgree.lean`）。停止 ID の一意性は、重い import（`BlockHalt.haltsAt_unique_spec`）を避けて
  ここで証明する。依存するのは `LeanUniv.Strict`（と、その下の `LeanUniv.Spec`）だけ。

  **Two URTMs compared directly** (a corollary of `IsUTMStrict`). Hand-written. For deterministic U₁, U₂ with
  `IsUTMStrict`, there are computable encoders c₁, c₂ and decoders d₁, d₂ such that, for every TM `tm n` of the
  enumeration and every finite ID `toID 0 a` of it, U₁ halts from `c₁ (n, a)` iff U₂ halts from `c₂ (n, a)` iff
  `tm n` halts from `a`, and when both halt, every code of either halting ID decodes to a code of the same ID β,
  the halting ID of `tm n`. Same statement as `URTM.Meta.Sat.isUTMStrict_agree` of lean-meta, here inside
  lean-univ, so that it applies to the 13 record machines without crossing lake environments.
-/
import LeanUniv.Strict

namespace URTM.Univ.Agree
open URTM URTM.Spec

/-! ### Uniqueness of the halting ID of a deterministic table -/

/-- One step of a deterministic table is a function. -/
theorem step_det {U : List Quint} (hdet : Deterministic U) {c c₁ c₂ : ID} (h₁ : Step U c c₁)
    (h₂ : Step U c c₂) : c₁ = c₂ := by
  obtain ⟨r₁, hr₁, ha₁, rfl⟩ := h₁
  obtain ⟨r₂, hr₂, ha₂, rfl⟩ := h₂
  rw [hdet r₁ hr₁ r₂ hr₂ (ha₁.1.trans ha₂.1.symm) (ha₁.2.trans ha₂.2.symm)]

/-- A halted ID makes no step. -/
theorem not_step_of_halted {U : List Quint} {c c' : ID} (h : Halted U c) : ¬ Step U c c' :=
  fun ⟨r, hr, ha, _⟩ => h r hr ha

/-- **The halting ID of a deterministic table is unique.** -/
theorem haltsAt_unique {U : List Quint} (hdet : Deterministic U) {ι γ₁ γ₂ : ID}
    (h₁ : HaltsAt U ι γ₁) (h₂ : HaltsAt U ι γ₂) : γ₁ = γ₂ := by
  obtain ⟨r₁, hh₁⟩ := h₁
  obtain ⟨r₂, hh₂⟩ := h₂
  induction r₁ using Relation.ReflTransGen.head_induction_on with
  | refl =>
    rcases Relation.ReflTransGen.cases_head r₂ with h | ⟨c, hc, -⟩
    · exact h
    · exact absurd hc (not_step_of_halted hh₁)
  | head hab _ ih =>
    rcases Relation.ReflTransGen.cases_head r₂ with rfl | ⟨c, hc, hc₂⟩
    · exact absurd hab (not_step_of_halted hh₂)
    · exact ih (step_det hdet hc hab ▸ hc₂)

/-! ### The corollary -/

/-- **U₁ and U₂ compute the same thing** (the conclusion of `isUTMStrict_agree`, as a definition, so that the
    statement over the 13 record machines in `FinalAgree` reads `Agrees (W i) (W j)`): there are computable
    encoders c₁, c₂ and decoders d₁, d₂ such that, for every TM `tm n` of the enumeration and every finite ID
    `toID 0 a` of it,
    (0) `c₁ (n, a)`, `c₂ (n, a)` are IDs of U₁, U₂;
    (1) U₁ halts from `c₁ (n, a)` ⇔ U₂ halts from `c₂ (n, a)`, and U₁ halts from `c₁ (n, a)` ⇔ `tm n` halts
        from `a`;
    (2) if U₁, U₂ reach halting IDs γ₁, γ₂, then γ₁ and γ₂ have codes, and there is a halting ID β of `tm n`
        from `a` such that every code of γ₁ read by d₁ and every code of γ₂ read by d₂ are codes of β. -/
def Agrees (U₁ U₂ : List Quint) : Prop :=
  ∃ (c₁ c₂ : ℕ × Code → Code) (d₁ d₂ : Code → Option Code),
    Computable c₁ ∧ Computable c₂ ∧ Computable d₁ ∧ Computable d₂ ∧
    ∀ n a, IsIDOf (tm n) (toID 0 a) →
      IsIDOf U₁ (toID 0 (c₁ (n, a))) ∧ IsIDOf U₂ (toID 0 (c₂ (n, a))) ∧
      (Halts U₁ (toID 0 (c₁ (n, a))) ↔ Halts U₂ (toID 0 (c₂ (n, a)))) ∧
      (Halts U₁ (toID 0 (c₁ (n, a))) ↔ Halts (tm n) (toID 0 a)) ∧
      ∀ γ₁ γ₂, HaltsAt U₁ (toID 0 (c₁ (n, a))) γ₁ → HaltsAt U₂ (toID 0 (c₂ (n, a))) γ₂ →
        (∃ g₁, toID γ₁.pos g₁ = γ₁) ∧ (∃ g₂, toID γ₂.pos g₂ = γ₂) ∧
        ∃ β, HaltsAt (tm n) (toID 0 a) β ∧
          ∀ g₁ g₂, toID γ₁.pos g₁ = γ₁ → toID γ₂.pos g₂ = γ₂ →
            ∃ b₁ b₂, d₁ g₁ = some b₁ ∧ d₂ g₂ = some b₂ ∧
              toID β.pos b₁ = β ∧ toID β.pos b₂ = β

/-- **2 つの URTM は同じ計算をする** / **two URTMs compute the same thing**: deterministic tables U₁, U₂ with
    `IsUTMStrict` have computable encoders c₁, c₂ and decoders d₁, d₂ such that, for every TM `tm n` of the
    enumeration and every finite ID `toID 0 a` of it,
    (0) `c₁ (n, a)`, `c₂ (n, a)` are IDs of U₁, U₂;
    (1) U₁ halts from `c₁ (n, a)` ⇔ U₂ halts from `c₂ (n, a)` ⇔ `tm n` halts from `a`;
    (2) if both halt, at γ₁ and γ₂, then γ₁ and γ₂ have codes, and there is a halting ID β of `tm n` such that
        every code of γ₁ read by d₁ and every code of γ₂ read by d₂ are codes of β.
    The statement is that of `URTM.Meta.Sat.isUTMStrict_agree` (lean-meta), stated inside lean-univ. -/
theorem isUTMStrict_agree {U₁ U₂ : List Quint}
    (hdet₁ : Deterministic U₁) (hdet₂ : Deterministic U₂)
    (hU₁ : IsUTMStrict U₁) (hU₂ : IsUTMStrict U₂) :
    ∃ (c₁ c₂ : ℕ × Code → Code) (d₁ d₂ : Code → Option Code),
      Computable c₁ ∧ Computable c₂ ∧ Computable d₁ ∧ Computable d₂ ∧
      ∀ n a, IsIDOf (tm n) (toID 0 a) →
        IsIDOf U₁ (toID 0 (c₁ (n, a))) ∧ IsIDOf U₂ (toID 0 (c₂ (n, a))) ∧
        (Halts U₁ (toID 0 (c₁ (n, a))) ↔ Halts U₂ (toID 0 (c₂ (n, a)))) ∧
        (Halts U₁ (toID 0 (c₁ (n, a))) ↔ Halts (tm n) (toID 0 a)) ∧
        ∀ γ₁ γ₂, HaltsAt U₁ (toID 0 (c₁ (n, a))) γ₁ → HaltsAt U₂ (toID 0 (c₂ (n, a))) γ₂ →
          (∃ g₁, toID γ₁.pos g₁ = γ₁) ∧ (∃ g₂, toID γ₂.pos g₂ = γ₂) ∧
          ∃ β, HaltsAt (tm n) (toID 0 a) β ∧
            ∀ g₁ g₂, toID γ₁.pos g₁ = γ₁ → toID γ₂.pos g₂ = γ₂ →
              ∃ b₁ b₂, d₁ g₁ = some b₁ ∧ d₂ g₂ = some b₂ ∧
                toID β.pos b₁ = β ∧ toID β.pos b₂ = β := by
  obtain ⟨c₁, d₁, hc₁, hd₁, H₁⟩ := hU₁
  obtain ⟨c₂, d₂, hc₂, hd₂, H₂⟩ := hU₂
  refine ⟨c₁, c₂, d₁, d₂, hc₁, hc₂, hd₁, hd₂, fun n a ha => ?_⟩
  obtain ⟨hi₁, hh₁, hn₁⟩ := H₁ n a ha
  obtain ⟨hi₂, hh₂, hn₂⟩ := H₂ n a ha
  have e₁ : Halts U₁ (toID 0 (c₁ (n, a))) ↔ Halts (tm n) (toID 0 a) :=
    ⟨fun h => Classical.byContradiction fun hc => hn₁ hc h,
      fun ⟨β, hβ⟩ => let ⟨γ, hγ, _⟩ := hh₁ β hβ; ⟨γ, hγ⟩⟩
  have e₂ : Halts U₂ (toID 0 (c₂ (n, a))) ↔ Halts (tm n) (toID 0 a) :=
    ⟨fun h => Classical.byContradiction fun hc => hn₂ hc h,
      fun ⟨β, hβ⟩ => let ⟨γ, hγ, _⟩ := hh₂ β hβ; ⟨γ, hγ⟩⟩
  refine ⟨hi₁, hi₂, e₁.trans e₂.symm, e₁, fun γ₁ γ₂ hγ₁ hγ₂ => ?_⟩
  obtain ⟨β, hβ⟩ := e₁.mp ⟨γ₁, hγ₁⟩
  obtain ⟨γ₁', hγ₁', hex₁, hall₁⟩ := hh₁ β hβ
  obtain ⟨γ₂', hγ₂', hex₂, hall₂⟩ := hh₂ β hβ
  obtain rfl := haltsAt_unique hdet₁ hγ₁' hγ₁
  obtain rfl := haltsAt_unique hdet₂ hγ₂' hγ₂
  refine ⟨hex₁, hex₂, β, hβ, fun g₁ g₂ hg₁ hg₂ => ?_⟩
  obtain ⟨b₁, hb₁, hb₁'⟩ := hall₁ g₁ hg₁
  obtain ⟨b₂, hb₂, hb₂'⟩ := hall₂ g₂ hg₂
  exact ⟨b₁, b₂, hb₁, hb₂, hb₁', hb₂'⟩

/-- The same, with the conclusion named `Agrees`. -/
theorem agree_of_isUTMStrict {U₁ U₂ : List Quint}
    (hdet₁ : Deterministic U₁) (hdet₂ : Deterministic U₂)
    (hU₁ : IsUTMStrict U₁) (hU₂ : IsUTMStrict U₂) : Agrees U₁ U₂ :=
  isUTMStrict_agree hdet₁ hdet₂ hU₁ hU₂

end URTM.Univ.Agree
