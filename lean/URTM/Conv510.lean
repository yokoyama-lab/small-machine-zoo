/-
  Morita 2017, Lemma 5.10（§5.3.5.2）: 1 方向更新の可逆 TM（1WU-RTM、Def. 5.20）T̂ を、3 状態 L R0 R1 の
  TM T† に変換する（Shannon の方法を右向きだけに使う）。その一般の模倣証明。

  T̂ の状態 q_i（i = idx q ≥ 1）と q_L（左へ戻る唯一の状態）。記号は Conv55 と同じ `pl s`・`up s i`・`dn s i`。

      δ1† : [L, s0, [s0, j↓], +, R0]            ([q_L, s0, s0, +, q_j] ∈ δ̂)
      δ2† : [R0, [s, i↑], [t, j↓], +, R0]       ([q_i, s, t, +, q_j] ∈ δ̂, q_i ≠ q_L)
      δ3† : [R0, u, [u, 1↑], −, L]
      δ4† : [L, [t, k↓], [t, (k−1)↓], +, R1]     (2 ≤ k ≤ m−1。原典の文面は t ≠ s0 だが、δ1† が [s0, j↓] を書くので
                                                 t = s0 も要る。記述ファイル urtm3-36654 も t = s0 を含む)
      δ5† : [R1, [u, k↑], [u, (k+1)↑], −, L]    (1 ≤ k ≤ m−2)
      δ6† : [L, [t, 1↓], t, +, R0]
      δ7† : [R0, [s0, i↑], s0, −, L]             ([q_i, s0, s0, −, q_L] ∈ δ̂)
      δ8† : [L, s, s, −, L]                      (s ≠ s0)

  T̂ の配置は、状態が q_L なら (L, テープそのまま)、q_i なら (R0, ヘッドの記号 s を [s, i↑] に) に対応する。

  主定理: `step_sim`（T̂ の 1 ステップを T† は 1 または 2j+1 ステップで）、`halted_sim`、`conv_simulates`
  （停止の 3 項の移送）、`conv_det`（決定性の保存）。

  mathlib 非依存。未証明の穴・新規公理・native_decide を使わない。
-/
import URTM.SimLemmas
import URTM.Conv55

namespace URTM.Conv510

open URTM URTM.KState URTM.CTSH URTM.SimLemmas
open URTM.Conv55 (FSym upd_eq upd_ne upd_upd upd_comm upd3 upd_comp)

/-- T† の 3 状態。 -/
inductive TSt where
  | L | R0 | R1
  deriving DecidableEq, Repr

variable {Q P S : Type} [DecidableEq Q]

/-- T̂ の規則 1 本の変換（δ1†, δ2†, δ7†）。q_L から左へ動く規則は δ8† がまとめて担う。 -/
def convRule (qL : Q) (idx : Q → Nat) (r : Rule Q P S) : Option (Rule TSt P (FSym S)) :=
  match r.q with
  | .go q =>
    if r.p = qL then
      if r.d = .R then some ⟨.L, .pl r.s, .dn r.t (idx q), .R, .go .R0⟩ else none
    else if r.d = .R then some ⟨.R0, .up r.s (idx r.p), .dn r.t (idx q), .R, .go .R0⟩
    else some ⟨.R0, .up r.s (idx r.p), .pl r.t, .L, .go .L⟩
  | .halt _ => none

/-- 記号 u についての δ3†..δ6†, δ8†。 -/
def symRules [DecidableEq S] (m : Nat) (s0 : S) (u : S) : List (Rule TSt P (FSym S)) :=
  [⟨.R0, .pl u, .up u 1, .L, .go .L⟩, ⟨.L, .dn u 1, .pl u, .R, .go .R0⟩] ++
  (if u = s0 then [] else [⟨.L, .pl u, .pl u, .L, .go .L⟩]) ++
  (List.range (m - 2)).flatMap (fun k =>
    [⟨.L, .dn u (k + 2), .dn u (k + 1), .R, .go .R1⟩, ⟨.R1, .up u (k + 1), .up u (k + 2), .L, .go .L⟩])

/-- **Lemma 5.10 の変換** T†。 -/
def conv [DecidableEq S] (T : Machine Q P S) (qL : Q) (s0 : S) (idx : Q → Nat) (m : Nat) (ss : List S) :
    Machine TSt P (FSym S) :=
  T.filterMap (convRule qL idx) ++ ss.flatMap (symRules m s0)

/-- 配置の符号化。 -/
def enc (qL : Q) (idx : Q → Nat) (c : Cfg Q P S) : Cfg TSt P (FSym S) :=
  match c.st with
  | .go p =>
    if p = qL then { st := .go .L, pos := c.pos, tape := fun i => .pl (c.tape i) }
    else { st := .go .R0, pos := c.pos,
           tape := upd (fun i => .pl (c.tape i)) c.pos (.up (c.tape c.pos) (idx p)) }
  | .halt h => { st := .halt h, pos := c.pos, tape := fun i => .pl (c.tape i) }

/-- T̂ の規則の形（1WU-RTM の条件 1, 4, 5 を規則ごとに述べたもの。`decide` 用の Bool 版）:
    (a) [q_L, s, s, −, q_L]（s ≠ s0）、(b) [q_L, s0, s0, +, q]（q ≠ q_L）、
    (c) [p, s, t, +, q]（p, q ≠ q_L, t ≠ s0）、(d) [p, s0, s0, −, q_L]（p ≠ q_L）。 -/
def shapeOK [DecidableEq S] (qL : Q) (s0 : S) (r : Rule Q P S) : Bool :=
  match r.q with
  | .go q =>
    if r.p = qL then
      (r.d == .L && q == qL && r.s == r.t && r.s != s0) || (r.d == .R && r.s == s0 && r.t == s0 && q != qL)
    else
      (r.d == .R && r.t != s0 && q != qL) || (r.d == .L && r.s == s0 && r.t == s0 && q == qL)
  | .halt _ => false

/-- 規則 r の行き先（q_L 以外）の番号が 1 以上 m 未満（`decide` 用の Bool 版）。 -/
def idxOK (qL : Q) (idx : Q → Nat) (m : Nat) (r : Rule Q P S) : Bool :=
  match r.q with
  | .go q => q == qL || (1 ≤ idx q && idx q < m)
  | .halt _ => true

theorem idxOK_spec {qL : Q} {idx : Q → Nat} {m : Nat} {r : Rule Q P S} (h : idxOK qL idx m r = true) {q : Q}
    (hq : r.q = .go q) (hqL : q ≠ qL) : 1 ≤ idx q ∧ idx q < m := by
  unfold idxOK at h; rw [hq] at h
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with h | h
  · exact absurd h hqL
  · exact h

/-- 仮定のまとめ。 -/
structure Hyp [DecidableEq S] (T : Machine Q P S) (qL : Q) (s0 : S) (idx : Q → Nat) (m : Nat) (ss : List S) :
    Prop where
  hS : ∀ s, s ∈ ss
  /-- 規則の行き先の状態（q_L 以外）の番号は 1 以上 m 未満。 -/
  hidx : ∀ r ∈ T, idxOK qL idx m r = true
  hinj : ∀ p q, p ≠ qL → q ≠ qL → idx p = idx q → p = q
  hshape : ∀ r ∈ T, shapeOK qL s0 r = true
  /-- 1WU-RTM の条件 2: q_L は空白でない記号の上では左へ進む。 -/
  hL : ∀ s ∈ ss, s ≠ s0 → (⟨qL, s, s, .L, .go qL⟩ : Rule Q P S) ∈ T
  /-- 1WU-RTM の条件 3: q_L は空白の上で右へ進んで Q+ の状態に入る。 -/
  hL0 : ∃ q, (⟨qL, s0, s0, .R, .go q⟩ : Rule Q P S) ∈ T

section Spec
variable [DecidableEq S] {qL : Q} {s0 : S}

theorem shape_spec {r : Rule Q P S} (h : shapeOK qL s0 r = true) :
    ∃ q, r.q = .go q ∧
      ((r.p = qL ∧ r.d = .L ∧ q = qL ∧ r.s = r.t ∧ r.s ≠ s0) ∨
       (r.p = qL ∧ r.d = .R ∧ r.s = s0 ∧ r.t = s0 ∧ q ≠ qL) ∨
       (r.p ≠ qL ∧ r.d = .R ∧ r.t ≠ s0 ∧ q ≠ qL) ∨
       (r.p ≠ qL ∧ r.d = .L ∧ r.s = s0 ∧ r.t = s0 ∧ q = qL)) := by
  unfold shapeOK at h
  split at h
  · rename_i q hq
    refine ⟨q, hq, ?_⟩
    split at h
    · rename_i hp
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
      rcases h with ⟨⟨⟨hd, hq'⟩, hst⟩, hs0⟩ | ⟨⟨⟨hd, hs⟩, ht⟩, hq'⟩
      · exact .inl ⟨hp, hd, hq', hst, hs0⟩
      · exact .inr (.inl ⟨hp, hd, hs, ht, hq'⟩)
    · rename_i hp
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
      rcases h with ⟨⟨hd, ht⟩, hq'⟩ | ⟨⟨⟨hd, hs⟩, ht⟩, hq'⟩
      · exact .inr (.inr (.inl ⟨hp, hd, ht, hq'⟩))
      · exact .inr (.inr (.inr ⟨hp, hd, hs, ht, hq'⟩))
  · cases h

theorem shape_R {r : Rule Q P S} (h : shapeOK qL s0 r = true) (hd : r.d = .R) {q : Q} (hq : r.q = .go q) :
    q ≠ qL := by
  obtain ⟨q', hq', hsh⟩ := shape_spec h
  rw [hq] at hq'; cases hq'
  rcases hsh with ⟨_, hd', _⟩ | ⟨_, _, _, _, h'⟩ | ⟨_, _, _, h'⟩ | ⟨_, hd', _⟩
  · rw [hd] at hd'; cases hd'
  · exact h'
  · exact h'
  · rw [hd] at hd'; cases hd'

theorem shape_L {r : Rule Q P S} (h : shapeOK qL s0 r = true) (hd : r.d ≠ .R) (hp : r.p ≠ qL) :
    r.t = s0 ∧ r.q = .go qL := by
  obtain ⟨q', hq', hsh⟩ := shape_spec h
  rcases hsh with ⟨hp', _⟩ | ⟨hp', _⟩ | ⟨_, hd', _⟩ | ⟨_, _, _, ht, hq''⟩
  · exact absurd hp' hp
  · exact absurd hp' hp
  · exact absurd hd' hd
  · exact ⟨ht, by rw [hq', hq'']⟩

end Spec

/-! ## 1. 1 ステップの模倣 -/

section Sim
variable [DecidableEq S] {T : Machine Q P S} {qL : Q} {s0 : S} {idx : Q → Nat} {m : Nat} {ss : List S}

theorem mem_sym {u : S} (hu : u ∈ ss) {ρ : Rule TSt P (FSym S)} (h : ρ ∈ symRules m s0 u) :
    ρ ∈ conv T qL s0 idx m ss :=
  List.mem_append_right _ (List.mem_flatMap.mpr ⟨u, hu, h⟩)

theorem mem_cnt {u : S} (hu : u ∈ ss) {k : Nat} (hk : k + 2 < m) {ρ : Rule TSt P (FSym S)}
    (h : ρ ∈ [(⟨.L, .dn u (k + 2), .dn u (k + 1), .R, .go .R1⟩ : Rule TSt P (FSym S)),
      ⟨.R1, .up u (k + 1), .up u (k + 2), .L, .go .L⟩]) :
    ρ ∈ conv T qL s0 idx m ss :=
  mem_sym hu (List.mem_append_right _ (List.mem_flatMap.mpr ⟨k, List.mem_range.mpr (by omega), h⟩))

theorem mem_rule {r : Rule Q P S} (hr : r ∈ T) {ρ : Rule TSt P (FSym S)} (h : convRule qL idx r = some ρ) :
    ρ ∈ conv T qL s0 idx m ss :=
  List.mem_append_left _ (List.mem_filterMap.mpr ⟨r, hr, h⟩)

/-- 数え上げの途中: 位置 x に [t, (j−k)↓]、x+1 に [u, (k+1)↑] を置いた L の配置。 -/
def B (g : Int → FSym S) (x : Int) (t u : S) (j k : Nat) : Cfg TSt P (FSym S) :=
  { st := .go .L, pos := x, tape := upd (upd g x (.dn t (j - k))) (x + 1) (.up u (k + 1)) }

theorem count (hS : ∀ s, s ∈ ss) (g : Int → FSym S) (x : Int) (t u : S) (j : Nat) (hj : j < m) :
    ∀ k, k + 1 ≤ j → StepN (conv T qL s0 idx m ss) (2 * k) (B g x t u j 0) (B g x t u j k) := by
  intro k
  induction k with
  | zero => intro _; exact .refl _
  | succ k ih =>
    intro hk
    have h1 := ih (by omega)
    have hne : x + 1 ≠ x := by omega
    have s1 : Step (conv T qL s0 idx m ss) (B g x t u j k)
        { st := .go .R1, pos := x + 1, tape := upd (upd g x (.dn t (j - (k + 1)))) (x + 1) (.up u (k + 1)) } := by
      have hρ := mem_cnt (T := T) (qL := qL) (s0 := s0) (idx := idx) (m := m) (hS t) (k := j - k - 2)
        (by omega) (u := t) (List.mem_cons_self ..)
      refine ⟨_, hρ, rfl, ?_, ?_⟩
      · simp only [B]; rw [upd_ne _ _ (Ne.symm hne), upd_eq]; congr 1; omega
      · simp only [B, fire, mv]
        rw [upd3 _ (Ne.symm hne), show j - k - 2 + 1 = j - (k + 1) by omega]
    have s2 : Step (conv T qL s0 idx m ss)
        { st := .go .R1, pos := x + 1, tape := upd (upd g x (.dn t (j - (k + 1)))) (x + 1) (.up u (k + 1)) }
        (B g x t u j (k + 1)) := by
      have hρ := mem_cnt (T := T) (qL := qL) (s0 := s0) (idx := idx) (m := m) (hS u) (k := k) (by omega)
        (u := u) (ρ := ⟨.R1, .up u (k + 1), .up u (k + 2), .L, .go .L⟩) (by simp)
      refine ⟨_, hρ, rfl, ?_, ?_⟩
      · simp only; rw [upd_eq]
      · simp only [B, fire, mv]
        rw [upd_upd]; congr 1; omega
    have := h1.trans ((StepN.single s1).trans (StepN.single s2))
    rwa [show 2 * k + (1 + 1) = 2 * (k + 1) by omega] at this

/-- δ1† または δ2† で [t, j↓] を書いて右へ R0 に来た後: δ3† → 数え上げ → δ6† で enc (q_j の配置)。 -/
theorem cont (H : Hyp T qL s0 idx m ss) (g : Int → S) (x : Int) (t : S) {q : Q} (hq : q ≠ qL)
    (hidx : 1 ≤ idx q ∧ idx q < m) :
    StepN (conv T qL s0 idx m ss) (2 * idx q)
      { st := .go .R0, pos := x + 1, tape := upd (fun i => .pl (g i)) x (.dn t (idx q)) }
      (enc qL idx { st := .go q, pos := x + 1, tape := upd g x t }) := by
  obtain ⟨h1, hm⟩ := hidx
  have hne : x + 1 ≠ x := by omega
  have s1 : Step (conv T qL s0 idx m ss)
      { st := .go .R0, pos := x + 1, tape := upd (fun i => .pl (g i)) x (.dn t (idx q)) }
      (B (fun i => .pl (g i)) x t (g (x + 1)) (idx q) 0) := by
    have hρ := mem_sym (T := T) (qL := qL) (idx := idx) (m := m) (H.hS (g (x + 1)))
      (ρ := ⟨.R0, .pl (g (x + 1)), .up (g (x + 1)) 1, .L, .go .L⟩) (s0 := s0) (by simp [symRules])
    refine ⟨_, hρ, rfl, ?_, ?_⟩
    · simp only; rw [upd_ne _ _ hne]
    · simp only [B, fire, mv, Nat.sub_zero]; congr 1; omega
  have s2 := count (T := T) (qL := qL) (s0 := s0) (idx := idx) H.hS (fun i => .pl (g i)) x t (g (x + 1))
    (idx q) hm (idx q - 1) (by omega)
  have s3 : Step (conv T qL s0 idx m ss) (B (fun i => .pl (g i)) x t (g (x + 1)) (idx q) (idx q - 1))
      (enc qL idx { st := .go q, pos := x + 1, tape := upd g x t }) := by
    have hρ := mem_sym (T := T) (qL := qL) (idx := idx) (m := m) (H.hS t)
      (ρ := ⟨.L, .dn t 1, .pl t, .R, .go .R0⟩) (s0 := s0) (by simp [symRules])
    refine ⟨_, hρ, rfl, ?_, ?_⟩
    · simp only [B]; rw [upd_ne _ _ (Ne.symm hne), upd_eq]; congr 1; omega
    · simp only [B, enc, fire, mv, hq, if_false]
      rw [upd_comm _ _ _ (Ne.symm hne), upd_upd, upd_comm _ _ _ hne, ← upd_comp FSym.pl]
      congr 2
      · rw [upd_ne _ _ hne]; congr 1; omega
  have := (StepN.single s1).trans (s2.trans (StepN.single s3))
  rwa [show 1 + (2 * (idx q - 1) + 1) = 2 * idx q by omega] at this

/-- **1 ステップの模倣**: T̂ の 1 ステップ c → c' を、T† は enc c から 1 ステップ以上で enc c' へ
    （q_L の左移動と δ7† は 1 ステップ、右移動は 2j + 1 ステップ）。 -/
theorem step_sim (H : Hyp T qL s0 idx m ss) {c c' : Cfg Q P S} (h : Step T c c') :
    ∃ N, StepN (conv T qL s0 idx m ss) (N + 1) (enc qL idx c) (enc qL idx c') := by
  obtain ⟨r, hr, hst, hsr, rfl⟩ := h
  obtain ⟨st, x, g⟩ := c
  simp only at hst hsr
  subst hst
  obtain ⟨q, hq, hsh⟩ := shape_spec (H.hshape r hr)
  rcases hsh with ⟨hp, hd, hqL, hst, hs0⟩ | ⟨hp, hd, hs, ht, hqL⟩ | ⟨hp, hd, ht, hqL⟩ | ⟨hp, hd, hs, ht, hqL⟩
  · -- (a) [q_L, s, s, −, q_L]: δ8†
    subst hqL
    have hρ := mem_sym (T := T) (qL := q) (idx := idx) (m := m) (H.hS r.s)
      (ρ := ⟨.L, .pl r.s, .pl r.s, .L, .go .L⟩) (s0 := s0) (by simp [symRules, hs0])
    refine ⟨0, .single ⟨_, hρ, ?_, ?_, ?_⟩⟩
    · simp [enc, hp]
    · simp [enc, hp, hsr]
    · simp only [enc, fire, hq, hd, mv, hp, if_true]
      rw [← hst, upd_comp FSym.pl]
  · -- (b) [q_L, s0, s0, +, q]: δ1† → cont
    have hρ : (⟨.L, .pl r.s, .dn r.t (idx q), .R, .go .R0⟩ : Rule TSt P (FSym S)) ∈ conv T qL s0 idx m ss :=
      mem_rule hr (by simp [convRule, hq, hp, hd])
    have s1 : Step (conv T qL s0 idx m ss) (enc qL idx ⟨.go r.p, x, g⟩)
        { st := .go .R0, pos := x + 1, tape := upd (fun i => .pl (g i)) x (.dn r.t (idx q)) } := by
      refine ⟨_, hρ, ?_, ?_, ?_⟩
      · simp [enc, hp]
      · simp [enc, hp, hsr]
      · simp only [enc, fire, mv, hp, if_true]
    have s2 := cont H g x r.t hqL (idxOK_spec (H.hidx r hr) hq hqL)
    refine ⟨2 * idx q, ?_⟩
    have := (StepN.single s1).trans s2
    rw [show 1 + 2 * idx q = 2 * idx q + 1 by omega] at this
    simpa [fire, hq, hd, mv] using this
  · -- (c) [q_i, s, t, +, q_j]: δ2† → cont
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
    refine ⟨2 * idx q, ?_⟩
    have := (StepN.single s1).trans s2
    rw [show 1 + 2 * idx q = 2 * idx q + 1 by omega] at this
    simpa [fire, hq, hd, mv] using this
  · -- (d) [q_i, s0, s0, −, q_L]: δ7†
    subst hqL
    have hρ : (⟨.R0, .up r.s (idx r.p), .pl r.t, .L, .go .L⟩ : Rule TSt P (FSym S)) ∈ conv T q s0 idx m ss :=
      mem_rule hr (by simp [convRule, hq, hp, hd])
    refine ⟨0, .single ⟨_, hρ, ?_, ?_, ?_⟩⟩
    · simp [enc, hp]
    · simp [enc, hp, hsr, upd_eq]
    · simp only [enc, fire, hq, hd, mv, hp, if_false, if_true]
      rw [upd_upd, upd_comp FSym.pl]

theorem stepN_sim (H : Hyp T qL s0 idx m ss) {n : Nat} {a b : Cfg Q P S} (h : StepN T n a b) :
    ∃ N, n ≤ N ∧ StepN (conv T qL s0 idx m ss) N (enc qL idx a) (enc qL idx b) :=
  stepN_sim_of_step _ (fun h₁ => let ⟨j, hj⟩ := step_sim H h₁; ⟨j + 1, by omega, hj⟩) h

/-- T̂ が止まる配置では T† も止まる。T̂ は q_L では止まらない（1WU-RTM の条件 2, 3）。 -/
theorem halted_sim (H : Hyp T qL s0 idx m ss) {c : Cfg Q P S} {p : Q} (hc : c.st = .go p)
    (hh : Halted T c) : Halted (conv T qL s0 idx m ss) (enc qL idx c) := by
  obtain ⟨st, x, g⟩ := c
  simp only at hc; subst hc
  by_cases hp : p = qL
  · subst hp
    exfalso
    by_cases hs : g x = s0
    · obtain ⟨q, hq⟩ := H.hL0
      exact hh _ ⟨_, hq, rfl, hs, rfl⟩
    · exact hh _ ⟨_, H.hL (g x) (H.hS _) hs, rfl, rfl, rfl⟩
  · intro c' ⟨ρ, hρ, hst, hs, _⟩
    simp only [enc, hp, if_false, upd_eq] at hst hs
    rcases List.mem_append.mp hρ with h | h
    · obtain ⟨r, hr, e⟩ := List.mem_filterMap.mp h
      unfold convRule at e
      split at e
      · split at e
        · split at e
          · cases e; cases hst
          · cases e
        · split at e
          · cases e
            simp only [FSym.up.injEq] at hs
            have := H.hinj _ _ hp (by assumption) hs.2
            subst this
            exact hh _ ⟨r, hr, rfl, hs.1, rfl⟩
          · cases e
            simp only [FSym.up.injEq] at hs
            have := H.hinj _ _ hp (by assumption) hs.2
            subst this
            exact hh _ ⟨r, hr, rfl, hs.1, rfl⟩
      · cases e
    · obtain ⟨u, _, hu⟩ := List.mem_flatMap.mp h
      simp only [symRules, List.mem_append, List.mem_cons, List.mem_flatMap, List.mem_range,
        List.not_mem_nil, or_false] at hu
      rcases hu with ((h1 | h1) | h1) | ⟨k, _, h2 | h2⟩
      · subst h1; cases hs
      · subst h1; cases hst
      · split at h1
        · cases h1
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at h1; subst h1; cases hst
      · subst h2; cases hst
      · subst h2; cases hst

end Sim

/-! ## 2. 停止の 3 項の移送と決定性の保存 -/

section Main
variable [DecidableEq S] {T : Machine Q P S} {qL : Q} {s0 : S} {idx : Q → Nat} {m : Nat} {ss : List S}

/-- **停止の 3 項の移送**（Conv55.conv_simulates と同じ形）。 -/
theorem conv_simulates {α : Type} (H : Hyp T qL s0 idx m ss) (hD : Deterministic (conv T qL s0 idx m ss))
    (Halts : α → Prop) (a : Cfg Q P S) (ha : ∃ q, a.st = .go q)
    (fin : α → Cfg Q P S)
    (hsim :
      (∀ x, Halts x → ∃ N, HaltsIn T N a (fin x)) ∧
      (∀ N e, HaltsIn T N a e → ∃ x, Halts x ∧ e = fin x)) :
    (∀ x, Halts x → ∃ N, HaltsIn (conv T qL s0 idx m ss) N (enc qL idx a) (enc qL idx (fin x))) ∧
    (∀ N e, HaltsIn (conv T qL s0 idx m ss) N (enc qL idx a) e → ∃ x, Halts x ∧ e = enc qL idx (fin x)) := by
  have hG : ∀ r ∈ T, r.q.isGo = true := by
    intro r hr; obtain ⟨q, hq, _⟩ := shape_spec (H.hshape r hr); rw [hq]; rfl
  have haltsT : ∀ N e, HaltsIn T N a e →
      ∃ N', HaltsIn (conv T qL s0 idx m ss) N' (enc qL idx a) (enc qL idx e) := by
    intro N e ⟨hs, hh⟩
    obtain ⟨N', _, hs'⟩ := stepN_sim H hs
    obtain ⟨q, hq⟩ := StepN.go_of_allGo hG hs ha
    exact ⟨N', hs', halted_sim H hq hh⟩
  refine ⟨fun x hx => let ⟨N, hh⟩ := hsim.1 x hx; haltsT N _ hh, fun N e he => ?_⟩
  obtain ⟨M, e₀, h₀, rfl⟩ := back_of_fwd hD (fun _ e => enc qL idx e) haltsT
    (fun _ _ _ hb => let ⟨N', hN', hs⟩ := stepN_sim H hb; ⟨N', hN', _, hs⟩) N e he
  obtain ⟨x, hx, rfl⟩ := hsim.2 M e₀ h₀
  exact ⟨x, hx, rfl⟩

theorem mem_conv {ρ : Rule TSt P (FSym S)} (h : ρ ∈ conv T qL s0 idx m ss) :
    (∃ r ∈ T, convRule qL idx r = some ρ) ∨ (∃ u ∈ ss, ρ ∈ symRules m s0 u) := by
  rcases List.mem_append.mp h with h | h
  · exact .inl (List.mem_filterMap.mp h)
  · exact .inr (List.mem_flatMap.mp h)

omit [DecidableEq S] in
theorem convRule_spec {r : Rule Q P S} {ρ : Rule TSt P (FSym S)} (h : convRule qL idx r = some ρ) :
    ∃ q, r.q = .go q ∧
      ((r.p = qL ∧ r.d = .R ∧ ρ = ⟨.L, .pl r.s, .dn r.t (idx q), .R, .go .R0⟩) ∨
       (r.p ≠ qL ∧ r.d = .R ∧ ρ = ⟨.R0, .up r.s (idx r.p), .dn r.t (idx q), .R, .go .R0⟩) ∨
       (r.p ≠ qL ∧ r.d ≠ .R ∧ ρ = ⟨.R0, .up r.s (idx r.p), .pl r.t, .L, .go .L⟩)) := by
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

theorem sym_spec {u : S} {ρ : Rule TSt P (FSym S)} (h : ρ ∈ symRules m s0 u) :
    ρ = ⟨.R0, .pl u, .up u 1, .L, .go .L⟩ ∨ ρ = ⟨.L, .dn u 1, .pl u, .R, .go .R0⟩ ∨
    (u ≠ s0 ∧ ρ = ⟨.L, .pl u, .pl u, .L, .go .L⟩) ∨
    ∃ k, k + 2 < m ∧ (ρ = ⟨.L, .dn u (k + 2), .dn u (k + 1), .R, .go .R1⟩ ∨
      ρ = ⟨.R1, .up u (k + 1), .up u (k + 2), .L, .go .L⟩) := by
  simp only [symRules, List.mem_append, List.mem_cons, List.mem_flatMap, List.mem_range,
    List.not_mem_nil, or_false] at h
  rcases h with ((h | h) | h) | ⟨k, hk, h⟩
  · exact .inl h
  · exact .inr (.inl h)
  · split at h
    · cases h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rename_i hu
      exact .inr (.inr (.inl ⟨hu, h⟩))
  · exact .inr (.inr (.inr ⟨k, by omega, h⟩))

/-- **決定性の保存**: T̂ が決定的で、規則の形が 1WU-RTM のもの、q_L 以外の状態の番号が単射なら T† も決定的。 -/
theorem conv_det (hT : Deterministic T) (hsh : ∀ r ∈ T, shapeOK qL s0 r = true)
    (hinj : ∀ p q, p ≠ qL → q ≠ qL → idx p = idx q → p = q) :
    Deterministic (conv T qL s0 idx m ss) := by
  intro ρ₁ h₁ ρ₂ h₂ hne hp hs
  rcases mem_conv h₁ with ⟨r₁, hr₁, e₁⟩ | ⟨u₁, _, h₁⟩ <;> rcases mem_conv h₂ with ⟨r₂, hr₂, e₂⟩ | ⟨u₂, _, h₂⟩
  · obtain ⟨q₁, hq₁, c₁⟩ := convRule_spec e₁
    obtain ⟨q₂, hq₂, c₂⟩ := convRule_spec e₂
    have same : r₁.p = r₂.p → r₁.s = r₂.s → False := by
      intro hpp hss
      by_cases e : r₁ = r₂
      · subst e; rw [e₁] at e₂; cases e₂; exact hne rfl
      · exact hT r₁ hr₁ r₂ hr₂ e hpp hss
    rcases c₁ with ⟨p₁, _, rfl⟩ | ⟨p₁, _, rfl⟩ | ⟨p₁, _, rfl⟩ <;>
      rcases c₂ with ⟨p₂, _, rfl⟩ | ⟨p₂, _, rfl⟩ | ⟨p₂, _, rfl⟩ <;>
      simp only [FSym.pl.injEq, FSym.up.injEq, reduceCtorEq] at hp hs
    · exact same (p₁.trans p₂.symm) hs
    · exact same (hinj _ _ p₁ p₂ hs.2) hs.1
    · exact same (hinj _ _ p₁ p₂ hs.2) hs.1
    · exact same (hinj _ _ p₁ p₂ hs.2) hs.1
    · exact same (hinj _ _ p₁ p₂ hs.2) hs.1
  · obtain ⟨q₁, hq₁, c₁⟩ := convRule_spec e₁
    obtain ⟨_, _, hsh₁⟩ := shape_spec (hsh r₁ hr₁)
    rcases c₁ with ⟨p₁, d₁, rfl⟩ | ⟨p₁, _, rfl⟩ | ⟨p₁, _, rfl⟩ <;>
      rcases sym_spec h₂ with rfl | rfl | ⟨hu, rfl⟩ | ⟨k, _, rfl | rfl⟩ <;>
      simp only [FSym.pl.injEq, reduceCtorEq] at hp hs
    rcases hsh₁ with ⟨_, hd, _⟩ | ⟨_, _, hs0, _⟩ | ⟨hp', _⟩ | ⟨hp', _⟩
    · rw [d₁] at hd; cases hd
    · exact hu (hs ▸ hs0)
    · exact hp' p₁
    · exact hp' p₁
  · obtain ⟨q₂, hq₂, c₂⟩ := convRule_spec e₂
    obtain ⟨_, _, hsh₂⟩ := shape_spec (hsh r₂ hr₂)
    rcases c₂ with ⟨p₂, d₂, rfl⟩ | ⟨p₂, _, rfl⟩ | ⟨p₂, _, rfl⟩ <;>
      rcases sym_spec h₁ with rfl | rfl | ⟨hu, rfl⟩ | ⟨k, _, rfl | rfl⟩ <;>
      simp only [FSym.pl.injEq, reduceCtorEq] at hp hs
    rcases hsh₂ with ⟨_, hd, _⟩ | ⟨_, _, hs0, _⟩ | ⟨hp', _⟩ | ⟨hp', _⟩
    · rw [d₂] at hd; cases hd
    · exact hu (hs.symm ▸ hs0)
    · exact hp' p₂
    · exact hp' p₂
  · rcases sym_spec h₁ with rfl | rfl | ⟨_, rfl⟩ | ⟨k, _, rfl | rfl⟩ <;>
      rcases sym_spec h₂ with rfl | rfl | ⟨_, rfl⟩ | ⟨k', _, rfl | rfl⟩ <;>
      simp only [FSym.pl.injEq, FSym.up.injEq, FSym.dn.injEq, reduceCtorEq] at hp hs <;>
      (try subst hs) <;> (try (obtain ⟨rfl, _⟩ := hs)) <;> (try omega) <;>
      (first
        | exact hne rfl
        | (have : k = k' := by omega
           subst this; exact hne rfl))

end Main

/-! ## 3. 規則の引き当て（大きな表を線形に照合するため） -/

section Lookup
variable [DecidableEq S] {T : Machine Q P S} {qL : Q} {s0 : S} {idx : Q → Nat} {m : Nat} {ss : List S}

/-- T† の規則を (状態, 記号) から引く。`hat` は T̂ の規則を (状態, 記号) から引く関数、`num` は番号から状態へ。 -/
def lookup (hat : Q → S → Option (Rule Q P S)) (qL : Q) (s0 : S) (idx : Q → Nat) (num : Nat → Q) (m : Nat) :
    TSt → FSym S → Option (Rule TSt P (FSym S))
  | .L, .pl s =>
    if s = s0 then (match hat qL s0 with
      | some r => if r.p = qL then convRule qL idx r else none
      | none => none)
    else some ⟨.L, .pl s, .pl s, .L, .go .L⟩
  | .L, .dn u k =>
    if k = 1 then some ⟨.L, .dn u 1, .pl u, .R, .go .R0⟩
    else if 2 ≤ k ∧ k < m then some ⟨.L, .dn u k, .dn u (k - 1), .R, .go .R1⟩ else none
  | .R0, .pl u => some ⟨.R0, .pl u, .up u 1, .L, .go .L⟩
  | .R0, .up s i =>
    match hat (num i) s with
    | some r => if r.p = qL then none else convRule qL idx r
    | none => none
  | .R1, .up u k => if 1 ≤ k ∧ k + 2 ≤ m then some ⟨.R1, .up u k, .up u (k + 1), .L, .go .L⟩ else none
  | _, _ => none

theorem lookup_sound (hS : ∀ s, s ∈ ss) {hat : Q → S → Option (Rule Q P S)}
    (hhat : ∀ p s r, hat p s = some r → r ∈ T) {num : Nat → Q} {p : TSt} {s : FSym S}
    {ρ : Rule TSt P (FSym S)} (h : lookup hat qL s0 idx num m p s = some ρ) :
    ρ ∈ conv T qL s0 idx m ss := by
  match p, s with
  | .L, .pl s =>
    simp only [lookup] at h
    split at h
    · split at h
      · rename_i r hr
        split at h
        · exact mem_rule (hhat _ _ _ hr) h
        · cases h
      · cases h
    · rename_i hs0; cases h
      exact mem_sym (hS s) (by simp [symRules, hs0])
  | .L, .dn u k =>
    simp only [lookup] at h
    split at h
    · cases h; subst_vars; exact mem_sym (hS u) (by simp [symRules])
    · split at h
      · cases h
        rename_i hk1 hk
        obtain ⟨k', rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
        exact mem_cnt (hS u) (k := k') (by omega) (by simp)
      · cases h
  | .R0, .pl u => simp only [lookup] at h; cases h; exact mem_sym (hS u) (by simp [symRules])
  | .R0, .up s i =>
    simp only [lookup] at h
    split at h
    · rename_i r hr
      split at h
      · cases h
      · exact mem_rule (hhat _ _ _ hr) h
    · cases h
  | .R1, .up u k =>
    simp only [lookup] at h
    split at h
    · cases h
      rename_i hk
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      exact mem_cnt (hS u) (k := k') (by omega) (ρ := ⟨.R1, .up u (k' + 1), .up u (k' + 2), .L, .go .L⟩) (by simp)
    · cases h
  | .L, .up _ _ => simp [lookup] at h
  | .R0, .dn _ _ => simp [lookup] at h
  | .R1, .pl _ => simp [lookup] at h
  | .R1, .dn _ _ => simp [lookup] at h

end Lookup

end URTM.Conv510
