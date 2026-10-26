/-
  Morita 2017, Lemma 5.10 の歩数（C14）。`Conv510.lean` の `step_sim` は T† のステップ数を `∃ N, … (N + 1)` で
  隠していたので、その値を式で述べる。

  * `step_sim_exact`: T̂ の 1 ステップ c → c' が右へ動いて状態 q_j（j = idx q）に入るなら、T† は enc c から
    ちょうど 2j + 1 ステップで enc c' へ。左へ動くなら（入るのは q_L）ちょうど 1 ステップ。
  * `step_sim_cost`: 同じことを、入った状態だけで決まる重み `cost`（q_L なら 1、q_j なら 2j + 1）で述べたもの。
  * `stepW_sim`・`haltsW_sim`: T̂ の n ステップの実行で入った状態の重みの和が w なら、T† はちょうど w ステップ
    （`StepW`、`StepW.lean`）。止まる実行ならちょうど w ステップで止まる。

  証明は `Conv510.step_sim` と同じ場合分けで、そこで作っていた長さの決まった連鎖（δ1†/δ2† → `cont`、δ7†・δ8† は
  1 ステップ）をそのまま使う。`Conv510.lean` を書き換えずに別ファイルにしたのは、Conv510 の olean を変えると
  3.8 万本の表の照合（`Gen/F3_36654`・`V3_36654`）と URTMSteps の区間の検査が建て直しになるため。

  mathlib 非依存。未証明の穴・新規公理・native_decide を使わない。
-/
import URTM.Conv510
import URTM.StepW

namespace URTM.Conv510

open URTM URTM.KState URTM.CTSH URTM.SimLemmas
open URTM.Conv55 (FSym upd_eq upd_ne upd_upd upd_comm upd3 upd_comp)

variable {Q P S : Type} [DecidableEq Q]

/-- T̂ の 1 ステップで状態 `st` に入るときの T† のステップ数（Lemma 5.10）: q_L に入る（左へ動く）なら 1、
    q_j（j = idx q。右へ動く）に入るなら 2j + 1。疑似状態には入らない（`Hyp.hshape`）ので最後の行は使われない。 -/
def cost (qL : Q) (idx : Q → Nat) : Tgt Q P → Nat
  | .go q => if q = qL then 1 else 2 * idx q + 1
  | .halt _ => 0

section Exact
variable [DecidableEq S] {T : Machine Q P S} {qL : Q} {s0 : S} {idx : Q → Nat} {m : Nat} {ss : List S}

/-- **1 ステップの模倣の歩数（重みの形）**: T̂ の 1 ステップ c → c' を、T† は enc c からちょうど
    `cost qL idx c'.st` ステップで enc c' へ。 -/
theorem step_sim_cost (H : Hyp T qL s0 idx m ss) {c c' : Cfg Q P S} (h : Step T c c') :
    StepN (conv T qL s0 idx m ss) (cost qL idx c'.st) (enc qL idx c) (enc qL idx c') := by
  obtain ⟨r, hr, hst, hsr, rfl⟩ := h
  obtain ⟨st, x, g⟩ := c
  simp only at hst hsr
  subst hst
  show StepN _ (cost qL idx r.q) _ _
  obtain ⟨q, hq, hsh⟩ := shape_spec (H.hshape r hr)
  rw [hq]
  rcases hsh with ⟨hp, hd, hqL, hst, hs0⟩ | ⟨hp, hd, hs, ht, hqL⟩ | ⟨hp, hd, ht, hqL⟩ | ⟨hp, hd, hs, ht, hqL⟩
  · -- (a) [q_L, s, s, −, q_L]: δ8†、1 ステップ
    subst hqL
    have hρ := mem_sym (T := T) (qL := q) (idx := idx) (m := m) (H.hS r.s)
      (ρ := ⟨.L, .pl r.s, .pl r.s, .L, .go .L⟩) (s0 := s0) (by simp [symRules, hs0])
    rw [show cost (P := P) q idx (.go q) = 1 by simp [cost]]
    refine .single ⟨_, hρ, ?_, ?_, ?_⟩
    · simp [enc, hp]
    · simp [enc, hp, hsr]
    · simp only [enc, fire, hq, hd, mv, hp, if_true]
      rw [← hst, upd_comp FSym.pl]
  · -- (b) [q_L, s0, s0, +, q]: δ1† → cont、2 idx q + 1 ステップ
    have hρ : (⟨.L, .pl r.s, .dn r.t (idx q), .R, .go .R0⟩ : Rule TSt P (FSym S)) ∈ conv T qL s0 idx m ss :=
      mem_rule hr (by simp [convRule, hq, hp, hd])
    have s1 : Step (conv T qL s0 idx m ss) (enc qL idx ⟨.go r.p, x, g⟩)
        { st := .go .R0, pos := x + 1, tape := upd (fun i => .pl (g i)) x (.dn r.t (idx q)) } := by
      refine ⟨_, hρ, ?_, ?_, ?_⟩
      · simp [enc, hp]
      · simp [enc, hp, hsr]
      · simp only [enc, fire, mv, hp, if_true]
    have s2 := cont H g x r.t hqL (idxOK_spec (H.hidx r hr) hq hqL)
    rw [show cost (P := P) qL idx (.go q) = 2 * idx q + 1 by simp [cost, hqL]]
    have := (StepN.single s1).trans s2
    rw [show 1 + 2 * idx q = 2 * idx q + 1 by omega] at this
    simpa [fire, hq, hd, mv] using this
  · -- (c) [q_i, s, t, +, q_j]: δ2† → cont、2 idx q + 1 ステップ
    have hρ : (⟨.R0, .up r.s (idx r.p), .dn r.t (idx q), .R, .go .R0⟩ : Rule TSt P (FSym S)) ∈
        conv T qL s0 idx m ss :=
      mem_rule hr (by simp [convRule, hq, hp, hd])
    have s1 : Step (conv T qL s0 idx m ss) (enc qL idx ⟨.go r.p, x, g⟩)
        { st := .go .R0, pos := x + 1, tape := upd (fun i => .pl (g i)) x (.dn r.t (idx q)) } := by
      refine ⟨_, hρ, ?_, ?_, ?_⟩
      · simp [enc, hp]
      · simp [enc, hp, hsr, upd_eq]
      · simp only [enc, fire, mv, hp, if_false]; rw [upd_upd]
    have s2 := cont H g x r.t hqL (idxOK_spec (H.hidx r hr) hq hqL)
    rw [show cost (P := P) qL idx (.go q) = 2 * idx q + 1 by simp [cost, hqL]]
    have := (StepN.single s1).trans s2
    rw [show 1 + 2 * idx q = 2 * idx q + 1 by omega] at this
    simpa [fire, hq, hd, mv] using this
  · -- (d) [q_i, s0, s0, −, q_L]: δ7†、1 ステップ
    subst hqL
    have hρ : (⟨.R0, .up r.s (idx r.p), .pl r.t, .L, .go .L⟩ : Rule TSt P (FSym S)) ∈ conv T q s0 idx m ss :=
      mem_rule hr (by simp [convRule, hq, hp, hd])
    rw [show cost (P := P) q idx (.go q) = 1 by simp [cost]]
    refine .single ⟨_, hρ, ?_, ?_, ?_⟩
    · simp [enc, hp]
    · simp [enc, hp, hsr, upd_eq]
    · simp only [enc, fire, hq, hd, mv, hp, if_false, if_true]
      rw [upd_upd, upd_comp FSym.pl]

/-- T̂ の 1 ステップは、右へ動いて q_L 以外の状態に入るか、左へ動いて q_L に入るか（1WU-RTM の規則の形）。 -/
theorem step_shape (H : Hyp T qL s0 idx m ss) {c c' : Cfg Q P S} (h : Step T c c') :
    (c'.pos = c.pos + 1 ∧ ∃ q, c'.st = .go q ∧ q ≠ qL) ∨ (c'.pos = c.pos - 1 ∧ c'.st = .go qL) := by
  obtain ⟨r, hr, _, _, rfl⟩ := h
  obtain ⟨q, hq, hsh⟩ := shape_spec (H.hshape r hr)
  simp only [fire, hq]
  rcases hsh with ⟨_, hd, hqL, _⟩ | ⟨_, hd, _, _, hqL⟩ | ⟨_, hd, _, hqL⟩ | ⟨_, hd, _, _, hqL⟩
  · right; rw [hd, hqL]; exact ⟨by simp [mv]; omega, rfl⟩
  · left; rw [hd]; exact ⟨by simp [mv], q, rfl, hqL⟩
  · left; rw [hd]; exact ⟨by simp [mv], q, rfl, hqL⟩
  · right; rw [hd, hqL]; exact ⟨by simp [mv]; omega, rfl⟩

/-- **Lemma 5.10 の歩数**: T̂ の 1 ステップ c → c' について、
    * 右へ動いて状態 q_j（j = idx q、q ≠ q_L）に入るなら、T† は enc c からちょうど 2j + 1 ステップで enc c' へ。
    * 左へ動くなら、入る状態は q_L で、T† はちょうど 1 ステップ。 -/
theorem step_sim_exact (H : Hyp T qL s0 idx m ss) {c c' : Cfg Q P S} (h : Step T c c') :
    (c'.pos = c.pos + 1 → ∃ q, c'.st = .go q ∧ q ≠ qL ∧
      StepN (conv T qL s0 idx m ss) (2 * idx q + 1) (enc qL idx c) (enc qL idx c')) ∧
    (c'.pos = c.pos - 1 → c'.st = .go qL ∧
      StepN (conv T qL s0 idx m ss) 1 (enc qL idx c) (enc qL idx c')) := by
  have hc := step_sim_cost H h
  rcases step_shape H h with ⟨hR, q, hq, hqL⟩ | ⟨hL, hq⟩
  · refine ⟨fun _ => ⟨q, hq, hqL, ?_⟩, fun h' => by omega⟩
    rw [hq] at hc; simpa [cost, hqL] using hc
  · refine ⟨fun h' => by omega, fun _ => ⟨hq, ?_⟩⟩
    rw [hq] at hc; simpa [cost] using hc

/-- **実行の歩数**: T̂ が a から b へ n ステップで、入った状態の重み `cost` の和が w なら、T† は enc a から
    ちょうど w ステップで enc b へ。 -/
theorem stepW_sim (H : Hyp T qL s0 idx m ss) {n w : Nat} {a b : Cfg Q P S}
    (h : StepW T (cost qL idx) n w a b) : StepN (conv T qL s0 idx m ss) w (enc qL idx a) (enc qL idx b) := by
  induction h with
  | refl => exact .refl _
  | cons hs _ ih => exact (step_sim_cost H hs).trans ih

/-- **止まる実行の歩数**: さらに b で T̂ が（実状態のまま）止まるなら、T† は enc a からちょうど w ステップで
    enc b に止まる。 -/
theorem haltsW_sim (H : Hyp T qL s0 idx m ss) {n w : Nat} {a b : Cfg Q P S}
    (h : StepW T (cost qL idx) n w a b) {p : Q} (hb : b.st = .go p) (hh : Halted T b) :
    HaltsIn (conv T qL s0 idx m ss) w (enc qL idx a) (enc qL idx b) :=
  ⟨stepW_sim H h, halted_sim H hb hh⟩

end Exact

end URTM.Conv510
