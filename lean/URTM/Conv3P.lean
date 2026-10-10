/-
  改良版の 3 状態化（docs/09_three_state_2026-09-26.md §2.1–2.2、`tools/threestate.py` の `ThreeState`、
  counter=pruned）の一般の模倣証明。Morita の Lemma 5.10（Conv510.lean）に 2 つの改良を入れたもの:

  (i)  計数記号の ↑ と ↓ を 1 種類 `ct x k` にまとめる（往復は右向きだけなので、L が読む計数は常に元のマス側、
       R0・R1 が読む計数は常に行き先側）。
  (ii) 記号 x の計数は k = 1..need x だけ用意する（刈り込み）。need と番号付け idx は引数。
       刈り込みの健全性は、1WU 機械 W の実行の各ステップの行き先で「idx q ≤ need (読む記号)」が成り立つこと
       （`NeedOK`）を仮定して示す。Conv1W.lean の掃引の補題がこれを `GRun` で運ぶ。

      δ1 : [L, s0, [s0, j], +, R0]              ([q_L, s0, s0, +, q_j] ∈ W)
      δ2 : [R0, [s, i], [t, j], +, R0]          ([q_i, s, t, +, q_j] ∈ W)
      δ3 : [R0, u, [u, 1], −, L]                (need u ≥ 1)
      δ4 : [L, [x, k], [x, k−1], +, R1]         (2 ≤ k ≤ need x)
      δ5 : [R1, [x, k], [x, k+1], −, L]         (1 ≤ k < need x)
      δ6 : [L, [x, 1], x, +, R0]                (need x ≥ 1)
      δ7 : [R0, [s0, i], s0, −, L]              ([q_i, s0, s0, −, q_L] ∈ W)
      δ8 : [L, x, x, −, L]                      (x ≠ s0)

  主定理: `step_sim`（W の 1 ステップを 1 または 2j+1 ステップで）、`grun_sim`、`halted_sim`、`conv_det`、`conv_rev`。

  mathlib 非依存。未証明の穴・新規公理・native_decide を使わない。
-/
import URTM.Conv3Base
import URTM.Conv510

set_option linter.unusedSectionVars false

namespace URTM.Conv3P

open URTM URTM.KState URTM.SimLemmas URTM.Conv3Base
open URTM.Conv55 (upd_eq upd_ne upd_upd upd_comm upd3 upd_comp)
open URTM.Conv510 (TSt shapeOK shape_spec shape_R shape_L)

/-- T† の記号: 素の記号と、計数（↑↓ の区別なし）。 -/
inductive CSym (S : Type) where
  | pl (s : S)
  | ct (s : S) (k : Nat)
  deriving DecidableEq, Repr

variable {Q P S : Type} [DecidableEq Q] [DecidableEq S]

/-- W の規則 1 本の変換（δ1, δ2, δ7）。q_L の左移動の規則は δ8 がまとめて担う。 -/
def convRule (qL : Q) (idx : Q → Nat) (r : Rule Q P S) : Option (Rule TSt P (CSym S)) :=
  match r.q with
  | .go q =>
    if r.p = qL then
      if r.d = .R then some ⟨.L, .pl r.s, .ct r.t (idx q), .R, .go .R0⟩ else none
    else if r.d = .R then some ⟨.R0, .ct r.s (idx r.p), .ct r.t (idx q), .R, .go .R0⟩
    else some ⟨.R0, .ct r.s (idx r.p), .pl r.t, .L, .go .L⟩
  | .halt _ => none

/-- 記号 x の計数の規則（δ4, δ5, δ6。`threestate.py` と同じ順）。 -/
def cntRules (need : S → Nat) (x : S) : List (Rule TSt P (CSym S)) :=
  (List.range (need x - 1)).map (fun k => ⟨.L, .ct x (k + 2), .ct x (k + 1), .R, .go .R1⟩) ++
  (List.range (need x - 1)).map (fun k => ⟨.R1, .ct x (k + 1), .ct x (k + 2), .L, .go .L⟩) ++
  (if 1 ≤ need x then [⟨.L, .ct x 1, .pl x, .R, .go .R0⟩] else [])

/-- **改良版の 3 状態化** T†。syms は W の記号の列挙（空白 s0 を含む）。 -/
def conv (W : Machine Q P S) (qL : Q) (s0 : S) (idx : Q → Nat) (need : S → Nat) (syms : List S) :
    Machine TSt P (CSym S) :=
  W.filterMap (convRule qL idx) ++
  syms.filterMap (fun u => if 1 ≤ need u then some ⟨.R0, .pl u, .ct u 1, .L, .go .L⟩ else none) ++
  syms.flatMap (cntRules need) ++
  syms.filterMap (fun x => if x = s0 then none else some ⟨.L, .pl x, .pl x, .L, .go .L⟩)

/-- T† の記号の全体: 素の記号と、計数 [x, 1..need x]。 -/
def univ (need : S → Nat) (syms : List S) : List (CSym S) :=
  syms.map .pl ++ syms.flatMap (fun x => (List.range (need x)).map (fun k => .ct x (k + 1)))

/-- 配置の符号化。 -/
def enc (qL : Q) (idx : Q → Nat) (c : Cfg Q P S) : Cfg TSt P (CSym S) :=
  match c.st with
  | .go p =>
    if p = qL then { st := .go .L, pos := c.pos, tape := fun i => .pl (c.tape i) }
    else { st := .go .R0, pos := c.pos,
           tape := upd (fun i => .pl (c.tape i)) c.pos (.ct (c.tape c.pos) (idx p)) }
  | .halt h => { st := .halt h, pos := c.pos, tape := fun i => .pl (c.tape i) }

/-- 計数の刈り込みが足りている配置（W の状態 q ≠ q_L が読む記号は記号の列挙にあり、その計数は idx q まである）。 -/
def NeedOK (qL : Q) (idx : Q → Nat) (need : S → Nat) (syms : List S) (c : Cfg Q P S) : Prop :=
  ∀ q, c.st = .go q → q ≠ qL → idx q ≤ need (c.tape c.pos) ∧ c.tape c.pos ∈ syms

/-- 仮定のまとめ。 -/
structure Hyp (W : Machine Q P S) (qL : Q) (s0 : S) (idx : Q → Nat) (need : S → Nat) (syms : List S) : Prop where
  /-- W の規則が読み書きする記号は列挙にある。 -/
  hS : ∀ r ∈ W, r.s ∈ syms ∧ r.t ∈ syms
  hshape : ∀ r ∈ W, shapeOK qL s0 r = true
  /-- 行き先の番号は 1 以上で、書く記号の計数はその番号まである。 -/
  hidx : ∀ r ∈ W, ∀ q, r.q = .go q → q ≠ qL → 1 ≤ idx q ∧ idx q ≤ need r.t
  hinj : ∀ p q, p ≠ qL → q ≠ qL → idx p = idx q → p = q

/-! ## 1. 規則の所属 -/

section Mem
variable {W : Machine Q P S} {qL : Q} {s0 : S} {idx : Q → Nat} {need : S → Nat} {syms : List S}

theorem mem_rule {r : Rule Q P S} (hr : r ∈ W) {ρ : Rule TSt P (CSym S)} (h : convRule qL idx r = some ρ) :
    ρ ∈ conv W qL s0 idx need syms := by
  unfold conv; simp only [List.mem_append, List.mem_filterMap]
  left; left; left; exact ⟨r, hr, h⟩

theorem mem_d3 {u : S} (hu : u ∈ syms) (h1 : 1 ≤ need u) :
    (⟨.R0, .pl u, .ct u 1, .L, .go .L⟩ : Rule TSt P (CSym S)) ∈ conv W qL s0 idx need syms := by
  unfold conv; simp only [List.mem_append, List.mem_filterMap]
  left; left; right; exact ⟨u, hu, by simp [h1]⟩

theorem mem_cnt {x : S} (hx : x ∈ syms) {ρ : Rule TSt P (CSym S)} (h : ρ ∈ cntRules need x) :
    ρ ∈ conv W qL s0 idx need syms := by
  unfold conv; simp only [List.mem_append, List.mem_flatMap]
  left; right; exact ⟨x, hx, h⟩

theorem mem_d4 {x : S} (hx : x ∈ syms) {k : Nat} (hk : k + 2 ≤ need x) :
    (⟨.L, .ct x (k + 2), .ct x (k + 1), .R, .go .R1⟩ : Rule TSt P (CSym S)) ∈ conv W qL s0 idx need syms :=
  mem_cnt hx (by unfold cntRules; simp only [List.mem_append, List.mem_map, List.mem_range]
                 left; left; exact ⟨k, by omega, rfl⟩)

theorem mem_d5 {x : S} (hx : x ∈ syms) {k : Nat} (hk : k + 2 ≤ need x) :
    (⟨.R1, .ct x (k + 1), .ct x (k + 2), .L, .go .L⟩ : Rule TSt P (CSym S)) ∈ conv W qL s0 idx need syms :=
  mem_cnt hx (by unfold cntRules; simp only [List.mem_append, List.mem_map, List.mem_range]
                 left; right; exact ⟨k, by omega, rfl⟩)

theorem mem_d6 {x : S} (hx : x ∈ syms) (h1 : 1 ≤ need x) :
    (⟨.L, .ct x 1, .pl x, .R, .go .R0⟩ : Rule TSt P (CSym S)) ∈ conv W qL s0 idx need syms :=
  mem_cnt hx (by unfold cntRules; simp [h1])

theorem mem_d8 {x : S} (hx : x ∈ syms) (h0 : x ≠ s0) :
    (⟨.L, .pl x, .pl x, .L, .go .L⟩ : Rule TSt P (CSym S)) ∈ conv W qL s0 idx need syms := by
  unfold conv; simp only [List.mem_append, List.mem_filterMap]
  right; exact ⟨x, hx, by simp [h0]⟩

end Mem

/-! ## 2. 1 ステップの模倣 -/

section Sim
variable {W : Machine Q P S} {qL : Q} {s0 : S} {idx : Q → Nat} {need : S → Nat} {syms : List S}

/-- 数え上げの途中: 位置 x に [t, j−k]、x+1 に [u, k+1] を置いた L の配置。 -/
def B (g : Int → CSym S) (x : Int) (t u : S) (j k : Nat) : Cfg TSt P (CSym S) :=
  { st := .go .L, pos := x, tape := upd (upd g x (.ct t (j - k))) (x + 1) (.ct u (k + 1)) }

theorem count (g : Int → CSym S) (x : Int) (t u : S) (j : Nat) (hts : t ∈ syms) (hus : u ∈ syms)
    (hjt : j ≤ need t) (hju : j ≤ need u) :
    ∀ k, k + 1 ≤ j → StepN (conv W qL s0 idx need syms) (2 * k) (B g x t u j 0) (B g x t u j k) := by
  intro k
  induction k with
  | zero => intro _; exact .refl _
  | succ k ih =>
    intro hk
    have h1 := ih (by omega)
    have hne : x + 1 ≠ x := by omega
    have s1 : Step (conv W qL s0 idx need syms) (B g x t u j k)
        { st := .go .R1, pos := x + 1, tape := upd (upd g x (.ct t (j - (k + 1)))) (x + 1) (.ct u (k + 1)) } := by
      have hρ := mem_d4 (W := W) (qL := qL) (s0 := s0) (idx := idx) (need := need) hts (k := j - k - 2) (by omega)
      refine ⟨_, hρ, rfl, ?_, ?_⟩
      · simp only [B]; rw [upd_ne _ _ (Ne.symm hne), upd_eq]; congr 1; omega
      · simp only [B, fire, mv]
        rw [upd3 _ (Ne.symm hne), show j - k - 2 + 1 = j - (k + 1) by omega]
    have s2 : Step (conv W qL s0 idx need syms)
        { st := .go .R1, pos := x + 1, tape := upd (upd g x (.ct t (j - (k + 1)))) (x + 1) (.ct u (k + 1)) }
        (B g x t u j (k + 1)) := by
      have hρ := mem_d5 (W := W) (qL := qL) (s0 := s0) (idx := idx) (need := need) hus (k := k) (by omega)
      refine ⟨_, hρ, rfl, ?_, ?_⟩
      · simp only; rw [upd_eq]
      · simp only [B, fire, mv]
        rw [upd_upd]; congr 1; omega
    have := h1.trans ((StepN.single s1).trans (StepN.single s2))
    rwa [show 2 * k + (1 + 1) = 2 * (k + 1) by omega] at this

/-- δ1 または δ2 で [t, j] を書いて右へ R0 に来た後: δ3 → 数え上げ → δ6 で enc (q_j の配置)。 -/
theorem cont (g : Int → S) (x : Int) (t : S) {q : Q} (hq : q ≠ qL) (hts : t ∈ syms) (hus : g (x + 1) ∈ syms)
    (h1 : 1 ≤ idx q) (hjt : idx q ≤ need t) (hju : idx q ≤ need (g (x + 1))) :
    StepN (conv W qL s0 idx need syms) (2 * idx q)
      { st := .go .R0, pos := x + 1, tape := upd (fun i => .pl (g i)) x (.ct t (idx q)) }
      (enc qL idx { st := .go q, pos := x + 1, tape := upd g x t }) := by
  have hne : x + 1 ≠ x := by omega
  have s1 : Step (conv W qL s0 idx need syms)
      { st := .go .R0, pos := x + 1, tape := upd (fun i => .pl (g i)) x (.ct t (idx q)) }
      (B (fun i => .pl (g i)) x t (g (x + 1)) (idx q) 0) := by
    have hρ := mem_d3 (W := W) (qL := qL) (s0 := s0) (idx := idx) (need := need) hus (by omega)
    refine ⟨_, hρ, rfl, ?_, ?_⟩
    · simp only; rw [upd_ne _ _ hne]
    · simp only [B, fire, mv, Nat.sub_zero]; congr 1; omega
  have s2 := count (W := W) (qL := qL) (s0 := s0) (idx := idx) (fun i => .pl (g i)) x t (g (x + 1))
    (idx q) hts hus hjt hju (idx q - 1) (by omega)
  have s3 : Step (conv W qL s0 idx need syms) (B (fun i => .pl (g i)) x t (g (x + 1)) (idx q) (idx q - 1))
      (enc qL idx { st := .go q, pos := x + 1, tape := upd g x t }) := by
    have hρ := mem_d6 (W := W) (qL := qL) (s0 := s0) (idx := idx) (need := need) hts (by omega)
    refine ⟨_, hρ, rfl, ?_, ?_⟩
    · simp only [B]; rw [upd_ne _ _ (Ne.symm hne), upd_eq]; congr 1; omega
    · simp only [B, enc, fire, mv, hq, if_false]
      rw [upd_comm _ _ _ (Ne.symm hne), upd_upd, upd_comm _ _ _ hne, ← upd_comp CSym.pl]
      congr 2
      · rw [upd_ne _ _ hne]; congr 1; omega
  have := (StepN.single s1).trans (s2.trans (StepN.single s3))
  rwa [show 1 + (2 * (idx q - 1) + 1) = 2 * idx q by omega] at this

/-- **1 ステップの模倣**: W の 1 ステップ c → c'（行き先の計数が足りている）を、T† は enc c から 1 ステップ以上で
    enc c' へ（q_L の左移動と δ7 は 1 ステップ、右移動は 2j + 1 ステップ）。 -/
theorem step_sim (H : Hyp W qL s0 idx need syms) {c c' : Cfg Q P S} (h : Step W c c')
    (hN : NeedOK qL idx need syms c') :
    ∃ N, StepN (conv W qL s0 idx need syms) (N + 1) (enc qL idx c) (enc qL idx c') := by
  obtain ⟨r, hr, hst, hsr, rfl⟩ := h
  obtain ⟨st, x, g⟩ := c
  simp only at hst hsr
  subst hst
  obtain ⟨q, hq, hsh⟩ := shape_spec (H.hshape r hr)
  rcases hsh with ⟨hp, hd, hqL, hst, hs0⟩ | ⟨hp, hd, hs, ht, hqL⟩ | ⟨hp, hd, ht, hqL⟩ | ⟨hp, hd, hs, ht, hqL⟩
  · -- [q_L, s, s, −, q_L]: δ8
    subst hqL
    have hρ := mem_d8 (W := W) (qL := q) (idx := idx) (need := need) (H.hS r hr).1 hs0
    refine ⟨0, .single ⟨_, hρ, ?_, ?_, ?_⟩⟩
    · simp [enc, hp]
    · simp [enc, hp, hsr]
    · simp only [enc, fire, hq, hd, mv, hp, if_true]
      rw [← hst, upd_comp CSym.pl]
  · -- [q_L, s0, s0, +, q]: δ1 → cont
    have hρ : (⟨.L, .pl r.s, .ct r.t (idx q), .R, .go .R0⟩ : Rule TSt P (CSym S)) ∈ conv W qL s0 idx need syms :=
      mem_rule hr (by simp [convRule, hq, hp, hd])
    have s1 : Step (conv W qL s0 idx need syms) (enc qL idx ⟨.go r.p, x, g⟩)
        { st := .go .R0, pos := x + 1, tape := upd (fun i => .pl (g i)) x (.ct r.t (idx q)) } := by
      refine ⟨_, hρ, ?_, ?_, ?_⟩
      · simp [enc, hp]
      · simp [enc, hp, hsr]
      · simp only [enc, fire, mv, hp, if_true]
    have hN' := hN q (by simp [fire, hq]) hqL
    simp only [fire, hd, mv] at hN'
    rw [upd_ne _ _ (by omega)] at hN'
    obtain ⟨h1, h2⟩ := H.hidx r hr q hq hqL
    have s2 := cont (W := W) (s0 := s0) g x r.t hqL (H.hS r hr).2 hN'.2 h1 h2 hN'.1
    refine ⟨2 * idx q, ?_⟩
    have := (StepN.single s1).trans s2
    rw [show 1 + 2 * idx q = 2 * idx q + 1 by omega] at this
    simpa [fire, hq, hd, mv] using this
  · -- [q_i, s, t, +, q_j]: δ2 → cont
    have hρ : (⟨.R0, .ct r.s (idx r.p), .ct r.t (idx q), .R, .go .R0⟩ : Rule TSt P (CSym S)) ∈
        conv W qL s0 idx need syms :=
      mem_rule hr (by simp [convRule, hq, hp, hd])
    have s1 : Step (conv W qL s0 idx need syms) (enc qL idx ⟨.go r.p, x, g⟩)
        { st := .go .R0, pos := x + 1, tape := upd (fun i => .pl (g i)) x (.ct r.t (idx q)) } := by
      refine ⟨_, hρ, ?_, ?_, ?_⟩
      · simp [enc, hp]
      · simp [enc, hp, hsr, upd_eq]
      · simp only [enc, fire, mv, hp, if_false]; rw [upd_upd]
    have hN' := hN q (by simp [fire, hq]) hqL
    simp only [fire, hd, mv] at hN'
    rw [upd_ne _ _ (by omega)] at hN'
    obtain ⟨h1, h2⟩ := H.hidx r hr q hq hqL
    have s2 := cont (W := W) (s0 := s0) g x r.t hqL (H.hS r hr).2 hN'.2 h1 h2 hN'.1
    refine ⟨2 * idx q, ?_⟩
    have := (StepN.single s1).trans s2
    rw [show 1 + 2 * idx q = 2 * idx q + 1 by omega] at this
    simpa [fire, hq, hd, mv] using this
  · -- [q_i, s0, s0, −, q_L]: δ7
    subst hqL
    have hρ : (⟨.R0, .ct r.s (idx r.p), .pl r.t, .L, .go .L⟩ : Rule TSt P (CSym S)) ∈ conv W q s0 idx need syms :=
      mem_rule hr (by simp [convRule, hq, hp, hd])
    refine ⟨0, .single ⟨_, hρ, ?_, ?_, ?_⟩⟩
    · simp [enc, hp]
    · simp [enc, hp, hsr, upd_eq]
    · simp only [enc, fire, hq, hd, mv, hp, if_false, if_true]
      rw [upd_upd, upd_comp CSym.pl]

/-- **実行の模倣**: 各ステップの行き先で計数が足りている W の実行を、T† は同じかそれ以上のステップ数で。 -/
theorem grun_sim (H : Hyp W qL s0 idx need syms) {G : Cfg Q P S → Prop} (hG : ∀ c, G c → NeedOK qL idx need syms c)
    {n : Nat} {a b : Cfg Q P S} (h : GRun W G n a b) :
    ∃ N, n ≤ N ∧ StepN (conv W qL s0 idx need syms) N (enc qL idx a) (enc qL idx b) := by
  induction h with
  | refl => exact ⟨0, Nat.le_refl _, .refl _⟩
  | cons h₁ hg _ ih =>
    obtain ⟨j, hj⟩ := step_sim H h₁ (hG _ hg)
    obtain ⟨N, hN, hs⟩ := ih
    exact ⟨j + 1 + N, by omega, hj.trans hs⟩

/-- W が q_L 以外の状態で止まる配置では T† も止まる。 -/
theorem halted_sim (H : Hyp W qL s0 idx need syms) {c : Cfg Q P S} {p : Q} (hc : c.st = .go p) (hp : p ≠ qL)
    (hh : Halted W c) : Halted (conv W qL s0 idx need syms) (enc qL idx c) := by
  obtain ⟨st, x, g⟩ := c
  simp only at hc; subst hc
  intro c' ⟨ρ, hρ, hst, hs, _⟩
  simp only [enc, hp, if_false, upd_eq] at hst hs
  unfold conv at hρ
  simp only [List.mem_append, List.mem_filterMap, List.mem_flatMap] at hρ
  rcases hρ with ((⟨r, hr, e⟩ | ⟨u, _, e⟩) | ⟨u, _, e⟩) | ⟨u, _, e⟩
  · unfold convRule at e
    split at e
    · split at e
      · split at e
        · cases e; cases hst
        · cases e
      · split at e
        · cases e
          simp only [CSym.ct.injEq] at hs
          have := H.hinj _ _ hp (by assumption) hs.2
          subst this
          exact hh _ ⟨r, hr, rfl, hs.1, rfl⟩
        · cases e
          simp only [CSym.ct.injEq] at hs
          have := H.hinj _ _ hp (by assumption) hs.2
          subst this
          exact hh _ ⟨r, hr, rfl, hs.1, rfl⟩
    · cases e
  · split at e
    · cases e; cases hs
    · cases e
  · unfold cntRules at e
    simp only [List.mem_append, List.mem_map, List.mem_range] at e
    rcases e with (⟨k, _, rfl⟩ | ⟨k, _, rfl⟩) | e
    · cases hst
    · cases hst
    · split at e
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at e; subst e; cases hst
      · cases e
  · split at e
    · cases e
    · cases e; cases hst

end Sim

/-! ## 3. 決定性と可逆性の保存 -/

section DetRev
variable {W : Machine Q P S} {qL : Q} {s0 : S} {idx : Q → Nat} {need : S → Nat} {syms : List S}

theorem mem_conv {ρ : Rule TSt P (CSym S)} (h : ρ ∈ conv W qL s0 idx need syms) :
    (∃ r ∈ W, convRule qL idx r = some ρ) ∨
    (∃ u, 1 ≤ need u ∧ ρ = ⟨.R0, .pl u, .ct u 1, .L, .go .L⟩) ∨
    (∃ x k, k + 2 ≤ need x ∧ ρ = ⟨.L, .ct x (k + 2), .ct x (k + 1), .R, .go .R1⟩) ∨
    (∃ x k, k + 2 ≤ need x ∧ ρ = ⟨.R1, .ct x (k + 1), .ct x (k + 2), .L, .go .L⟩) ∨
    (∃ x, 1 ≤ need x ∧ ρ = ⟨.L, .ct x 1, .pl x, .R, .go .R0⟩) ∨
    (∃ x, x ≠ s0 ∧ ρ = ⟨.L, .pl x, .pl x, .L, .go .L⟩) := by
  unfold conv at h
  simp only [List.mem_append, List.mem_filterMap, List.mem_flatMap] at h
  rcases h with ((⟨r, hr, e⟩ | ⟨u, _, e⟩) | ⟨x, _, e⟩) | ⟨x, _, e⟩
  · exact .inl ⟨r, hr, e⟩
  · split at e
    · rename_i h1; cases e; exact .inr (.inl ⟨u, h1, rfl⟩)
    · cases e
  · unfold cntRules at e
    simp only [List.mem_append, List.mem_map, List.mem_range] at e
    rcases e with (⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩) | e
    · exact .inr (.inr (.inl ⟨x, k, by omega, rfl⟩))
    · exact .inr (.inr (.inr (.inl ⟨x, k, by omega, rfl⟩)))
    · split at e
      · rename_i h1
        simp only [List.mem_cons, List.not_mem_nil, or_false] at e
        exact .inr (.inr (.inr (.inr (.inl ⟨x, h1, e⟩))))
      · cases e
  · split at e
    · cases e
    · rename_i h0; cases e; exact .inr (.inr (.inr (.inr (.inr ⟨x, h0, rfl⟩))))

omit [DecidableEq S] in
theorem convRule_spec {r : Rule Q P S} {ρ : Rule TSt P (CSym S)} (h : convRule qL idx r = some ρ) :
    ∃ q, r.q = .go q ∧
      ((r.p = qL ∧ r.d = .R ∧ ρ = ⟨.L, .pl r.s, .ct r.t (idx q), .R, .go .R0⟩) ∨
       (r.p ≠ qL ∧ r.d = .R ∧ ρ = ⟨.R0, .ct r.s (idx r.p), .ct r.t (idx q), .R, .go .R0⟩) ∨
       (r.p ≠ qL ∧ r.d ≠ .R ∧ ρ = ⟨.R0, .ct r.s (idx r.p), .pl r.t, .L, .go .L⟩)) := by
  unfold convRule at h
  cases hq : r.q with
  | halt _ => rw [hq] at h; cases h
  | go q =>
    rw [hq] at h
    refine ⟨q, rfl, ?_⟩
    by_cases hp : r.p = qL <;> by_cases hd : r.d = .R <;> simp only [hp, hd, if_true, if_false] at h
    · cases h; exact .inl ⟨hp, hd, rfl⟩
    · cases h
    · cases h; exact .inr (.inl ⟨hp, hd, rfl⟩)
    · cases h; exact .inr (.inr ⟨hp, hd, rfl⟩)

/-- **決定性の保存**: W が決定的で、規則の形が 1WU のもの、q_L 以外の状態の番号が単射なら T† も決定的。 -/
theorem conv_det (hT : Deterministic W) (hsh : ∀ r ∈ W, shapeOK qL s0 r = true)
    (hinj : ∀ p q, p ≠ qL → q ≠ qL → idx p = idx q → p = q) :
    Deterministic (conv W qL s0 idx need syms) := by
  intro ρ₁ h₁ ρ₂ h₂ hne hp hs
  rcases mem_conv h₁ with ⟨r₁, hr₁, e₁⟩ | h₁' <;> rcases mem_conv h₂ with ⟨r₂, hr₂, e₂⟩ | h₂'
  · obtain ⟨q₁, hq₁, c₁⟩ := convRule_spec e₁
    obtain ⟨q₂, hq₂, c₂⟩ := convRule_spec e₂
    have same : r₁.p = r₂.p → r₁.s = r₂.s → False := by
      intro hpp hss
      by_cases e : r₁ = r₂
      · subst e; rw [e₁] at e₂; cases e₂; exact hne rfl
      · exact hT r₁ hr₁ r₂ hr₂ e hpp hss
    rcases c₁ with ⟨p₁, _, rfl⟩ | ⟨p₁, _, rfl⟩ | ⟨p₁, _, rfl⟩ <;>
      rcases c₂ with ⟨p₂, _, rfl⟩ | ⟨p₂, _, rfl⟩ | ⟨p₂, _, rfl⟩ <;>
      simp only [CSym.pl.injEq, CSym.ct.injEq, reduceCtorEq] at hp hs
    · exact same (p₁.trans p₂.symm) hs
    · exact same (hinj _ _ p₁ p₂ hs.2) hs.1
    · exact same (hinj _ _ p₁ p₂ hs.2) hs.1
    · exact same (hinj _ _ p₁ p₂ hs.2) hs.1
    · exact same (hinj _ _ p₁ p₂ hs.2) hs.1
  · obtain ⟨q₁, hq₁, c₁⟩ := convRule_spec e₁
    obtain ⟨_, _, hsh₁⟩ := shape_spec (hsh r₁ hr₁)
    rcases c₁ with ⟨p₁, d₁, rfl⟩ | ⟨p₁, _, rfl⟩ | ⟨p₁, _, rfl⟩ <;>
      rcases h₂' with ⟨u, _, rfl⟩ | ⟨x, k, _, rfl⟩ | ⟨x, k, _, rfl⟩ | ⟨x, _, rfl⟩ | ⟨x, hx, rfl⟩ <;>
      simp only [CSym.pl.injEq, reduceCtorEq] at hp hs
    rcases hsh₁ with ⟨_, hd, _⟩ | ⟨_, _, hs0, _⟩ | ⟨hp', _⟩ | ⟨hp', _⟩
    · rw [d₁] at hd; cases hd
    · exact hx (hs ▸ hs0)
    · exact hp' p₁
    · exact hp' p₁
  · obtain ⟨q₂, hq₂, c₂⟩ := convRule_spec e₂
    obtain ⟨_, _, hsh₂⟩ := shape_spec (hsh r₂ hr₂)
    rcases c₂ with ⟨p₂, d₂, rfl⟩ | ⟨p₂, _, rfl⟩ | ⟨p₂, _, rfl⟩ <;>
      rcases h₁' with ⟨u, _, rfl⟩ | ⟨x, k, _, rfl⟩ | ⟨x, k, _, rfl⟩ | ⟨x, _, rfl⟩ | ⟨x, hx, rfl⟩ <;>
      simp only [CSym.pl.injEq, reduceCtorEq] at hp hs
    rcases hsh₂ with ⟨_, hd, _⟩ | ⟨_, _, hs0, _⟩ | ⟨hp', _⟩ | ⟨hp', _⟩
    · rw [d₂] at hd; cases hd
    · exact hx (hs.symm ▸ hs0)
    · exact hp' p₂
    · exact hp' p₂
  · rcases h₁' with ⟨u, _, rfl⟩ | ⟨x, k, _, rfl⟩ | ⟨x, k, _, rfl⟩ | ⟨x, _, rfl⟩ | ⟨x, _, rfl⟩ <;>
      rcases h₂' with ⟨u', _, rfl⟩ | ⟨x', k', _, rfl⟩ | ⟨x', k', _, rfl⟩ | ⟨x', _, rfl⟩ | ⟨x', _, rfl⟩ <;>
      simp only [CSym.pl.injEq, CSym.ct.injEq, reduceCtorEq] at hp hs <;>
      (try subst hs) <;> (try (obtain ⟨rfl, _⟩ := hs)) <;> (try omega) <;>
      (first
        | exact hne rfl
        | (have : k = k' := by omega
           subst this; exact hne rfl))

/-- **可逆性の保存**: W が可逆で、規則の形が 1WU のもの、q_L 以外の状態の番号が単射なら T† も可逆。 -/
theorem conv_rev (hR : Reversible W) (hsh : ∀ r ∈ W, shapeOK qL s0 r = true)
    (hinj : ∀ p q, p ≠ qL → q ≠ qL → idx p = idx q → p = q) :
    Reversible (conv W qL s0 idx need syms) := by
  intro ρ₁ h₁ ρ₂ h₂ hne hq
  rcases mem_conv h₁ with ⟨r₁, hr₁, e₁⟩ | h₁' <;> rcases mem_conv h₂ with ⟨r₂, hr₂, e₂⟩ | h₂'
  · obtain ⟨q₁, hq₁, c₁⟩ := convRule_spec e₁
    obtain ⟨q₂, hq₂, c₂⟩ := convRule_spec e₂
    have same : r₁.q = r₂.q → r₁.t = r₂.t → False := by
      intro hqq htt
      by_cases e : r₁ = r₂
      · subst e; rw [e₁] at e₂; cases e₂; exact hne rfl
      · exact (hR r₁ hr₁ r₂ hr₂ e hqq).2 htt
    rcases c₁ with ⟨p₁, d₁, rfl⟩ | ⟨p₁, d₁, rfl⟩ | ⟨p₁, d₁, rfl⟩ <;>
      rcases c₂ with ⟨p₂, d₂, rfl⟩ | ⟨p₂, d₂, rfl⟩ | ⟨p₂, d₂, rfl⟩ <;>
      simp only [Tgt.go.injEq, reduceCtorEq] at hq <;>
      refine ⟨rfl, fun ht => ?_⟩ <;>
      simp only [CSym.ct.injEq, CSym.pl.injEq, reduceCtorEq] at ht
    all_goals first
      | (have e := hinj _ _ (shape_R (hsh r₁ hr₁) d₁ hq₁) (shape_R (hsh r₂ hr₂) d₂ hq₂) ht.2
         subst e; exact same (by rw [hq₁, hq₂]) ht.1)
      | (have h1 := shape_L (hsh r₁ hr₁) d₁ p₁
         have h2 := shape_L (hsh r₂ hr₂) d₂ p₂
         exact same (by rw [h1.2, h2.2]) ht)
  · obtain ⟨q₁, hq₁, c₁⟩ := convRule_spec e₁
    rcases c₁ with ⟨p₁, d₁, rfl⟩ | ⟨p₁, d₁, rfl⟩ | ⟨p₁, d₁, rfl⟩ <;>
      rcases h₂' with ⟨u, _, rfl⟩ | ⟨x, k, _, rfl⟩ | ⟨x, k, _, rfl⟩ | ⟨x, _, rfl⟩ | ⟨x, hx, rfl⟩ <;>
      simp only [Tgt.go.injEq, reduceCtorEq] at hq <;>
      refine ⟨rfl, fun ht => ?_⟩ <;>
      simp only [CSym.pl.injEq, reduceCtorEq] at ht
    exact hx (ht ▸ (shape_L (hsh r₁ hr₁) d₁ p₁).1)
  · obtain ⟨q₂, hq₂, c₂⟩ := convRule_spec e₂
    rcases c₂ with ⟨p₂, d₂, rfl⟩ | ⟨p₂, d₂, rfl⟩ | ⟨p₂, d₂, rfl⟩ <;>
      rcases h₁' with ⟨u, _, rfl⟩ | ⟨x, k, _, rfl⟩ | ⟨x, k, _, rfl⟩ | ⟨x, _, rfl⟩ | ⟨x, hx, rfl⟩ <;>
      simp only [Tgt.go.injEq, reduceCtorEq] at hq <;>
      refine ⟨rfl, fun ht => ?_⟩ <;>
      simp only [CSym.pl.injEq, reduceCtorEq] at ht
    exact hx (ht.symm ▸ (shape_L (hsh r₂ hr₂) d₂ p₂).1)
  · rcases h₁' with ⟨u, _, rfl⟩ | ⟨x, k, _, rfl⟩ | ⟨x, k, _, rfl⟩ | ⟨x, _, rfl⟩ | ⟨x, _, rfl⟩ <;>
      rcases h₂' with ⟨u', _, rfl⟩ | ⟨x', k', _, rfl⟩ | ⟨x', k', _, rfl⟩ | ⟨x', _, rfl⟩ | ⟨x', _, rfl⟩ <;>
      simp only [Tgt.go.injEq, reduceCtorEq] at hq <;>
      refine ⟨rfl, fun ht => ?_⟩ <;>
      simp only [CSym.ct.injEq, CSym.pl.injEq, reduceCtorEq] at ht <;>
      (try subst ht) <;> (try (obtain ⟨rfl, _⟩ := ht)) <;> (try omega) <;>
      (first
        | exact hne rfl
        | (have : k = k' := by omega
           subst this; exact hne rfl))

end DetRev

/-! ## 4. 記号の範囲 -/

section Syms
variable {W : Machine Q P S} {qL : Q} {s0 : S} {idx : Q → Nat} {need : S → Nat} {syms : List S}

theorem pl_univ {x : S} (hx : x ∈ syms) : (CSym.pl x) ∈ univ need syms :=
  List.mem_append_left _ (List.mem_map.mpr ⟨x, hx, rfl⟩)

theorem ct_univ {x : S} (hx : x ∈ syms) {k : Nat} (h1 : 1 ≤ k) (h2 : k ≤ need x) : (CSym.ct x k) ∈ univ need syms :=
  List.mem_append_right _ (List.mem_flatMap.mpr ⟨x, hx, List.mem_map.mpr ⟨k - 1, List.mem_range.mpr (by omega),
    by congr 1; omega⟩⟩)

/-- **T† の規則が読み書きする記号はすべて `univ need syms` にある**（W の規則が読む記号の計数も足りていれば）。 -/
theorem conv_syms (hS : ∀ r ∈ W, r.s ∈ syms ∧ r.t ∈ syms) (hsh : ∀ r ∈ W, shapeOK qL s0 r = true)
    (hidx : ∀ r ∈ W, ∀ q, r.q = .go q → q ≠ qL → 1 ≤ idx q ∧ idx q ≤ need r.t)
    (hsrc : ∀ r ∈ W, r.p ≠ qL → 1 ≤ idx r.p ∧ idx r.p ≤ need r.s) :
    ∀ ρ ∈ conv W qL s0 idx need syms, ρ.s ∈ univ need syms ∧ ρ.t ∈ univ need syms := by
  intro ρ h
  unfold conv at h
  simp only [List.mem_append, List.mem_filterMap, List.mem_flatMap] at h
  rcases h with ((⟨r, hr, e⟩ | ⟨u, hu, e⟩) | ⟨x, hx, e⟩) | ⟨x, hx, e⟩
  · obtain ⟨q, hq, c⟩ := convRule_spec e
    rcases c with ⟨_, hd, rfl⟩ | ⟨hp, hd, rfl⟩ | ⟨hp, _, rfl⟩
    · have := hidx r hr q hq (shape_R (hsh r hr) hd hq)
      exact ⟨pl_univ (hS r hr).1, ct_univ (hS r hr).2 this.1 this.2⟩
    · have := hidx r hr q hq (shape_R (hsh r hr) hd hq)
      have h' := hsrc r hr hp
      exact ⟨ct_univ (hS r hr).1 h'.1 h'.2, ct_univ (hS r hr).2 this.1 this.2⟩
    · have h' := hsrc r hr hp
      exact ⟨ct_univ (hS r hr).1 h'.1 h'.2, pl_univ (hS r hr).2⟩
  · split at e
    · rename_i h1; cases e; exact ⟨pl_univ hu, ct_univ hu (Nat.le_refl _) h1⟩
    · cases e
  · unfold cntRules at e
    simp only [List.mem_append, List.mem_map, List.mem_range] at e
    rcases e with (⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩) | e
    · exact ⟨ct_univ hx (by omega) (by omega), ct_univ hx (by omega) (by omega)⟩
    · exact ⟨ct_univ hx (by omega) (by omega), ct_univ hx (by omega) (by omega)⟩
    · split at e
      · rename_i h1
        simp only [List.mem_cons, List.not_mem_nil, or_false] at e; subst e
        exact ⟨ct_univ hx (Nat.le_refl _) h1, pl_univ hx⟩
      · cases e
  · split at e
    · cases e
    · cases e; exact ⟨pl_univ hx, pl_univ hx⟩

end Syms

end URTM.Conv3P
