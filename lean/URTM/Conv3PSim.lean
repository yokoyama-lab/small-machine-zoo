/-
  改良版の 3 状態化（Conv3P.lean、↑ と ↓ をまとめた計数 `ct x k`）の**停止の 3 項の移送**
  （`Conv510.conv_simulates` と同じ形）。計数を刈り込まない場合、すなわち W のどの規則の行き先 q（q_L 以外）の
  番号も、どの記号の計数の上限にも収まる（`∀ x, idx q ≤ need x`）場合に示す。

  * `needOK_of_step`: そのとき W の任意の 1 ステップの行き先は `NeedOK` を満たす（行き先の状態は規則の行き先）。
    したがって W の普通の実行（`StepN`）は条件付きの実行（`GRun`）であり（`grun_of_stepN`）、`Conv3P.grun_sim` が
    そのまま使える（`stepN_sim`）。
  * `not_halted_L`: 1WU 機械の条件 2・3（q_L は空白でない記号の上では左へ、空白の上では右へ進む）から、W は q_L では
    止まらない。`Conv3P.halted_sim` の仮定 `p ≠ q_L` はこれで満たされる。
  * `conv_simulates`: 前向き（W の停止 → T† の停止）と、`SimLemmas.back_of_fwd` による逆向き
    （T† の停止 → W の停止。W が止まらないなら T† は W の各計算を同じ長さ以上で追うので止まらない）。

  mathlib 非依存。未証明の穴・新規公理・native_decide を使わない。
-/
import URTM.Conv3P

set_option linter.unusedSectionVars false

namespace URTM.Conv3P

open URTM URTM.KState URTM.SimLemmas URTM.Conv3Base
open URTM.Conv510 (TSt shape_spec)

variable {Q P S : Type} [DecidableEq Q] [DecidableEq S]
variable {W : Machine Q P S} {qL : Q} {s0 : S} {idx : Q → Nat} {need : S → Nat} {syms : List S}

/-- 計数を刈り込まない場合、W の 1 ステップの行き先はつねに `NeedOK`。 -/
theorem needOK_of_step (hsyms : ∀ s, s ∈ syms)
    (hfull : ∀ r ∈ W, ∀ q, r.q = .go q → q ≠ qL → ∀ x, idx q ≤ need x)
    {c c' : Cfg Q P S} (h : Step W c c') : NeedOK qL idx need syms c' := by
  obtain ⟨r, hr, _, _, rfl⟩ := h
  intro q hq hqL
  exact ⟨hfull r hr q hq hqL _, hsyms _⟩

/-- 各ステップの行き先が `NeedOK` なら、W の普通の実行は条件付きの実行。 -/
theorem grun_of_stepN (hN : ∀ {c c' : Cfg Q P S}, Step W c c' → NeedOK qL idx need syms c')
    {n : Nat} {a b : Cfg Q P S} (h : StepN W n a b) : GRun W (NeedOK qL idx need syms) n a b := by
  induction h with
  | refl => exact .refl _
  | cons h₁ _ ih => exact .cons h₁ (hN h₁) ih

/-- **実行の模倣**（刈り込まない場合）: W の n ステップの実行を、T† は n ステップ以上で。 -/
theorem stepN_sim (H : Hyp W qL s0 idx need syms)
    (hN : ∀ {c c' : Cfg Q P S}, Step W c c' → NeedOK qL idx need syms c')
    {n : Nat} {a b : Cfg Q P S} (h : StepN W n a b) :
    ∃ N, n ≤ N ∧ StepN (conv W qL s0 idx need syms) N (enc qL idx a) (enc qL idx b) :=
  grun_sim H (fun _ h => h) (grun_of_stepN hN h)

/-- W は q_L では止まらない（1WU 機械の条件 2・3）。 -/
theorem not_halted_L (hsyms : ∀ s, s ∈ syms)
    (hL : ∀ s ∈ syms, s ≠ s0 → (⟨qL, s, s, .L, .go qL⟩ : Rule Q P S) ∈ W)
    (hL0 : ∃ q, (⟨qL, s0, s0, .R, .go q⟩ : Rule Q P S) ∈ W)
    {c : Cfg Q P S} (hc : c.st = .go qL) : ¬ Halted W c := by
  intro hh
  obtain ⟨st, x, g⟩ := c
  simp only at hc; subst hc
  by_cases hs : g x = s0
  · obtain ⟨q, hq⟩ := hL0
    exact hh _ ⟨_, hq, rfl, hs, rfl⟩
  · exact hh _ ⟨_, hL (g x) (hsyms _) hs, rfl, rfl, rfl⟩

/-- **停止の 3 項の移送**（`Conv510.conv_simulates` と同じ形。計数を刈り込まない場合）。 -/
theorem conv_simulates {α : Type} (H : Hyp W qL s0 idx need syms) (hsyms : ∀ s, s ∈ syms)
    (hfull : ∀ r ∈ W, ∀ q, r.q = .go q → q ≠ qL → ∀ x, idx q ≤ need x)
    (hL : ∀ s ∈ syms, s ≠ s0 → (⟨qL, s, s, .L, .go qL⟩ : Rule Q P S) ∈ W)
    (hL0 : ∃ q, (⟨qL, s0, s0, .R, .go q⟩ : Rule Q P S) ∈ W)
    (hD : Deterministic (conv W qL s0 idx need syms))
    (Halts : α → Prop) (a : Cfg Q P S) (ha : ∃ q, a.st = .go q)
    (fin : α → Cfg Q P S)
    (hsim :
      (∀ x, Halts x → ∃ N, HaltsIn W N a (fin x)) ∧
      (∀ N e, HaltsIn W N a e → ∃ x, Halts x ∧ e = fin x)) :
    (∀ x, Halts x → ∃ N, HaltsIn (conv W qL s0 idx need syms) N (enc qL idx a) (enc qL idx (fin x))) ∧
    (∀ N e, HaltsIn (conv W qL s0 idx need syms) N (enc qL idx a) e → ∃ x, Halts x ∧ e = enc qL idx (fin x)) := by
  have hN : ∀ {c c' : Cfg Q P S}, Step W c c' → NeedOK qL idx need syms c' :=
    fun h => needOK_of_step hsyms hfull h
  have hG : ∀ r ∈ W, r.q.isGo = true := by
    intro r hr; obtain ⟨q, hq, _⟩ := shape_spec (H.hshape r hr); rw [hq]; rfl
  have haltsW : ∀ N e, HaltsIn W N a e →
      ∃ N', HaltsIn (conv W qL s0 idx need syms) N' (enc qL idx a) (enc qL idx e) := by
    intro N e ⟨hs, hh⟩
    obtain ⟨N', _, hs'⟩ := stepN_sim H hN hs
    obtain ⟨q, hq⟩ := StepN.go_of_allGo hG hs ha
    have hqL : q ≠ qL := fun e => not_halted_L hsyms hL hL0 (e ▸ hq) hh
    exact ⟨N', hs', halted_sim H hq hqL hh⟩
  refine ⟨fun x hx => let ⟨N, hh⟩ := hsim.1 x hx; haltsW N _ hh, fun N e he => ?_⟩
  obtain ⟨M, e₀, h₀, rfl⟩ := back_of_fwd hD (fun _ e => enc qL idx e) haltsW
    (fun _ _ _ hb => let ⟨N', hN', hs⟩ := stepN_sim H hN hb; ⟨N', hN', _, hs⟩) N e he
  obtain ⟨x, hx, rfl⟩ := hsim.2 M e₀ h₀
  exact ⟨x, hx, rfl⟩

end URTM.Conv3P
