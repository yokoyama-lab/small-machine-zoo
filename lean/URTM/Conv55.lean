/-
  Morita 2017, Theorem 5.5（§5.3.4）: 零シフト規則の無い 1 テープ可逆 TM T（m 状態 n 記号）を、
  4 状態 L0 L1 R0 R1・(2mn + n) 記号の TM T̃ に変換する（Shannon の方法の可逆版）。その一般の模倣証明。

  記号は T の記号 s（`pl s`）、[s, i↑]（`up s i`）、[s, i↓]（`dn s i`）。状態 p_i は番号 i = idx p_i で表し、
  T の配置 α p_i s β は T̃ の配置 α X [s, i↑] β（X は p_i に入る向きが + なら R0、そうでなければ L0）に対応する。

      δ̃1, δ̃2, δ̃1', δ̃2' : [X(p_i), [s, i↑], [t, j↓], d, (d = + なら R0、− なら L0)]   ([p_i, s, t, d, p_j] ∈ δ)
      δ̃3  : [R0, u, [u, 0↑], −, L0]        δ̃3' : [L0, u, [u, 0↑], +, R0]
      δ̃4  : [L0, [t, k↓], [t, (k−1)↓], +, R1]   δ̃4' : [R0, [t, k↓], [t, (k−1)↓], −, L1]   (1 ≤ k ≤ m−1)
      δ̃5  : [R1, [u, k↑], [u, (k+1)↑], −, L0]   δ̃5' : [L1, [u, k↑], [u, (k+1)↑], +, R0]   (0 ≤ k ≤ m−2)
      δ̃6  : [L0, [t, 0↓], t, +, R0]         δ̃6' : [R0, [t, 0↓], t, −, L0]

  主定理:
  * `step_sim` : T の 1 ステップ（p_i → p_j）を T̃ はちょうど 2j + 3 ステップで模倣する（原典 Fig. 5.10）。
  * `halted_sim` : T が止まる配置では T̃ も止まる（状態の番号が単射なら）。
  * `conv_simulates` : T の「停止の 3 項」（CTSH の模倣定理の形）は、符号化 `enc` を通して T̃ に移る
    （逆向きは T̃ の決定性を仮定。具体機械では `decide` で確かめる）。

  mathlib 非依存。未証明の穴・新規公理・native_decide を使わない。
-/
import URTM.SimLemmas

namespace URTM.Conv55

open URTM URTM.KState URTM.CTSH URTM.SimLemmas

/-- T̃ の 4 状態。 -/
inductive FSt where
  | L0 | L1 | R0 | R1
  deriving DecidableEq, Repr

/-- T̃ の記号: 元の記号 s、[s, i↑]、[s, i↓]。 -/
inductive FSym (S : Type) where
  | pl (s : S)
  | up (s : S) (i : Nat)
  | dn (s : S) (i : Nat)
  deriving DecidableEq, Repr

variable {Q P S : Type}

/-- 状態 p を表す T̃ の状態（p に入る向きが + なら R0、そうでなければ L0）。 -/
def X (side : Q → Bool) (p : Q) : FSt := if side p then .R0 else .L0

/-- 元の規則 1 本の変換（δ̃1, δ̃2, δ̃1', δ̃2'）。停止規則は変換しない。 -/
def convRule (idx : Q → Nat) (side : Q → Bool) (r : Rule Q P S) : Option (Rule FSt P (FSym S)) :=
  match r.q with
  | .go q => some ⟨X side r.p, .up r.s (idx r.p), .dn r.t (idx q), r.d,
                   .go (if r.d = .R then .R0 else .L0)⟩
  | .halt _ => none

/-- 記号 u についての δ̃3..δ̃6, δ̃3'..δ̃6'。 -/
def symRules (m : Nat) (u : S) : List (Rule FSt P (FSym S)) :=
  [⟨.R0, .pl u, .up u 0, .L, .go .L0⟩, ⟨.L0, .pl u, .up u 0, .R, .go .R0⟩,
   ⟨.L0, .dn u 0, .pl u, .R, .go .R0⟩, ⟨.R0, .dn u 0, .pl u, .L, .go .L0⟩] ++
  (List.range (m - 1)).flatMap (fun k =>
    [⟨.L0, .dn u (k + 1), .dn u k, .R, .go .R1⟩, ⟨.R0, .dn u (k + 1), .dn u k, .L, .go .L1⟩,
     ⟨.R1, .up u k, .up u (k + 1), .L, .go .L0⟩, ⟨.L1, .up u k, .up u (k + 1), .R, .go .R0⟩])

/-- **Theorem 5.5 の変換** T̃。 -/
def conv (T : Machine Q P S) (idx : Q → Nat) (m : Nat) (side : Q → Bool) (ss : List S) :
    Machine FSt P (FSym S) :=
  T.filterMap (convRule idx side) ++ ss.flatMap (symRules m)

/-- 配置の符号化: ヘッドの記号 s を [s, i↑]（i は現状態の番号）に、他の記号 u を u のままに。 -/
def enc (idx : Q → Nat) (side : Q → Bool) (c : Cfg Q P S) : Cfg FSt P (FSym S) :=
  match c.st with
  | .go p => { st := .go (X side p), pos := c.pos,
               tape := upd (fun i => .pl (c.tape i)) c.pos (.up (c.tape c.pos) (idx p)) }
  | .halt h => { st := .halt h, pos := c.pos, tape := fun i => .pl (c.tape i) }

/-! ## 1. 1 点更新の補題 -/

theorem upd_eq {α : Type} (f : Int → α) (i : Int) (v : α) : upd f i v i = v := by simp [upd]
theorem upd_ne {α : Type} (f : Int → α) {i j : Int} (v : α) (h : j ≠ i) : upd f i v j = f j := by
  simp [upd, h]
theorem upd_upd {α : Type} (f : Int → α) (i : Int) (a b : α) : upd (upd f i a) i b = upd f i b := by
  funext j; simp only [upd]; split <;> rfl
theorem upd_comm {α : Type} (f : Int → α) {i j : Int} (a b : α) (h : i ≠ j) :
    upd (upd f i a) j b = upd (upd f j b) i a := by
  funext k; simp only [upd]; split <;> split <;> first | rfl | (subst_vars; exact absurd rfl h)
theorem upd3 {α : Type} (f : Int → α) {i j : Int} (h : i ≠ j) (a b c : α) :
    upd (upd (upd f i a) j b) i c = upd (upd f i c) j b := by
  rw [upd_comm _ _ _ h, upd_upd, upd_comm _ _ _ (Ne.symm h)]
theorem upd_self {α : Type} (f : Int → α) (i : Int) : upd f i (f i) = f := by
  funext j; simp only [upd]; split <;> subst_vars <;> rfl
theorem upd_comp {α β : Type} (f : α → β) (g : Int → α) (i : Int) (t : α) :
    (fun k => f (upd g i t k)) = upd (fun k => f (g k)) i (f t) := by
  funext k; simp only [upd]; split <;> rfl

/-! ## 2. 1 ステップの模倣 -/

section Sim
variable {T : Machine Q P S} {idx : Q → Nat} {m : Nat} {side : Q → Bool} {ss : List S}

theorem mem_sym {u : S} (hu : u ∈ ss) {ρ : Rule FSt P (FSym S)} (h : ρ ∈ symRules m u) :
    ρ ∈ conv T idx m side ss :=
  List.mem_append_right _ (List.mem_flatMap.mpr ⟨u, hu, h⟩)

theorem mem_cnt {u : S} (hu : u ∈ ss) {k : Nat} (hk : k + 1 < m) {ρ : Rule FSt P (FSym S)}
    (h : ρ ∈ [(⟨.L0, .dn u (k + 1), .dn u k, .R, .go .R1⟩ : Rule FSt P (FSym S)),
      ⟨.R0, .dn u (k + 1), .dn u k, .L, .go .L1⟩,
      ⟨.R1, .up u k, .up u (k + 1), .L, .go .L0⟩, ⟨.L1, .up u k, .up u (k + 1), .R, .go .R0⟩]) :
    ρ ∈ conv T idx m side ss :=
  mem_sym hu (List.mem_append_right _ (List.mem_flatMap.mpr ⟨k, List.mem_range.mpr (by omega), h⟩))

/-- 右へ動く場合の数え上げ（原典 Fig. 5.10）: 位置 x に [t, (j−k)↓]、x+1 に [u, k↑] を置いた L0 の配置 B k から、
    2 ステップで B (k+1) へ。 -/
def BR (g : Int → FSym S) (x : Int) (t u : S) (j k : Nat) : Cfg FSt P (FSym S) :=
  { st := .go .L0, pos := x, tape := upd (upd g x (.dn t (j - k))) (x + 1) (.up u k) }

def BL (g : Int → FSym S) (x : Int) (t u : S) (j k : Nat) : Cfg FSt P (FSym S) :=
  { st := .go .R0, pos := x, tape := upd (upd g x (.dn t (j - k))) (x - 1) (.up u k) }

theorem countR (hS : ∀ s, s ∈ ss) (g : Int → FSym S) (x : Int) (t u : S) (j : Nat) (hj : j < m) :
    ∀ k, k ≤ j → StepN (conv T idx m side ss) (2 * k) (BR g x t u j 0) (BR g x t u j k) := by
  intro k
  induction k with
  | zero => intro _; exact .refl _
  | succ k ih =>
    intro hk
    have h1 := ih (by omega)
    have hne : x + 1 ≠ x := by omega
    -- L0 が [t, (j−k)↓] を [t, (j−k−1)↓] にして右へ
    have s1 : Step (conv T idx m side ss) (BR g x t u j k)
        { st := .go .R1, pos := x + 1,
          tape := upd (upd g x (.dn t (j - (k + 1)))) (x + 1) (.up u k) } := by
      have hρ := mem_cnt (T := T) (idx := idx) (m := m) (side := side) (hS t) (k := j - (k + 1)) (by omega)
        (u := t) (List.mem_cons_self ..)
      refine ⟨_, hρ, rfl, ?_, ?_⟩
      · simp only [BR]; rw [upd_ne _ _ (Ne.symm hne), upd_eq]; congr 1; omega
      · simp only [BR, fire, mv]
        rw [upd3 _ (Ne.symm hne)]
    -- R1 が [u, k↑] を [u, (k+1)↑] にして左へ
    have s2 : Step (conv T idx m side ss)
        { st := .go .R1, pos := x + 1,
          tape := upd (upd g x (.dn t (j - (k + 1)))) (x + 1) (.up u k) }
        (BR g x t u j (k + 1)) := by
      have hρ := mem_cnt (T := T) (idx := idx) (m := m) (side := side) (hS u) (k := k) (by omega)
        (u := u) (ρ := ⟨.R1, .up u k, .up u (k + 1), .L, .go .L0⟩) (by simp)
      refine ⟨_, hρ, rfl, ?_, ?_⟩
      · simp only; rw [upd_eq]
      · simp only [BR, fire, mv]
        rw [upd_upd]; congr 1; omega
    have := h1.trans ((StepN.single s1).trans (StepN.single s2))
    rwa [show 2 * k + (1 + 1) = 2 * (k + 1) by omega] at this

theorem countL (hS : ∀ s, s ∈ ss) (g : Int → FSym S) (x : Int) (t u : S) (j : Nat) (hj : j < m) :
    ∀ k, k ≤ j → StepN (conv T idx m side ss) (2 * k) (BL g x t u j 0) (BL g x t u j k) := by
  intro k
  induction k with
  | zero => intro _; exact .refl _
  | succ k ih =>
    intro hk
    have h1 := ih (by omega)
    have hne : x - 1 ≠ x := by omega
    have s1 : Step (conv T idx m side ss) (BL g x t u j k)
        { st := .go .L1, pos := x - 1,
          tape := upd (upd g x (.dn t (j - (k + 1)))) (x - 1) (.up u k) } := by
      have hρ := mem_cnt (T := T) (idx := idx) (m := m) (side := side) (hS t) (k := j - (k + 1)) (by omega)
        (u := t) (ρ := ⟨.R0, .dn t (j - (k + 1) + 1), .dn t (j - (k + 1)), .L, .go .L1⟩) (by simp)
      refine ⟨_, hρ, rfl, ?_, ?_⟩
      · simp only [BL]; rw [upd_ne _ _ (Ne.symm hne), upd_eq]; congr 1; omega
      · simp only [BL, fire, mv]
        rw [upd3 _ (Ne.symm hne), Int.sub_eq_add_neg]
    have s2 : Step (conv T idx m side ss)
        { st := .go .L1, pos := x - 1,
          tape := upd (upd g x (.dn t (j - (k + 1)))) (x - 1) (.up u k) }
        (BL g x t u j (k + 1)) := by
      have hρ := mem_cnt (T := T) (idx := idx) (m := m) (side := side) (hS u) (k := k) (by omega)
        (u := u) (ρ := ⟨.L1, .up u k, .up u (k + 1), .R, .go .R0⟩) (by simp)
      refine ⟨_, hρ, rfl, ?_, ?_⟩
      · simp only; rw [upd_eq]
      · simp only [BL, fire, mv]
        rw [upd_upd]; congr 1; omega
    have := h1.trans ((StepN.single s1).trans (StepN.single s2))
    rwa [show 2 * k + (1 + 1) = 2 * (k + 1) by omega] at this

/-- **1 ステップの模倣**。T の規則 [p_i, s, t, d, p_j]（d = ±）による c → c' を、T̃ は enc c から
    ちょうど 2j + 3 ステップで enc c' へ。 -/
theorem step_sim (hS : ∀ s, s ∈ ss) (hidx : ∀ q, idx q < m)
    (hside : ∀ r ∈ T, match r.q with
      | .go q => (r.d = .R → side q = true) ∧ (r.d = .L → side q = false) ∧ r.d ≠ .Z
      | .halt _ => True)
    {c c' : Cfg Q P S} (h : Step T c c') (hg : ∃ q, c'.st = .go q) :
    ∃ N, StepN (conv T idx m side ss) (N + 1) (enc idx side c) (enc idx side c') := by
  obtain ⟨r, hr, hst, hsr, rfl⟩ := h
  obtain ⟨q, hq⟩ := hg
  simp only [fire] at hq
  have hsd := hside r hr
  rw [hq] at hsd
  obtain ⟨hR, hL, hZ⟩ := hsd
  have hρ : (⟨X side r.p, .up r.s (idx r.p), .dn r.t (idx q), r.d,
      .go (if r.d = .R then .R0 else .L0)⟩ : Rule FSt P (FSym S)) ∈ conv T idx m side ss :=
    List.mem_append_left _ (List.mem_filterMap.mpr ⟨r, hr, by simp [convRule, hq]⟩)
  obtain ⟨st, x, g⟩ := c
  simp only at hst hsr
  subst hst
  have hjm : idx q < m := hidx q
  cases hd : r.d with
  | Z => exact absurd hd hZ
  | R =>
    have hside' := hR hd
    have hne : x + 1 ≠ x := by omega
    rw [hd] at hρ
    have s1 : Step (conv T idx m side ss) (enc idx side ⟨.go r.p, x, g⟩)
        { st := .go .R0, pos := x + 1, tape := upd (fun i => .pl (g i)) x (.dn r.t (idx q)) } := by
      refine ⟨_, hρ, rfl, ?_, ?_⟩
      · simp [enc, upd_eq, hsr]
      · simp only [enc, fire, mv, if_true]; rw [upd_upd]
    have s2 : Step (conv T idx m side ss)
        { st := .go .R0, pos := x + 1, tape := upd (fun i => .pl (g i)) x (.dn r.t (idx q)) }
        (BR (fun i => .pl (g i)) x r.t (g (x + 1)) (idx q) 0) := by
      have hρ3 := mem_sym (T := T) (idx := idx) (m := m) (side := side) (hS (g (x + 1)))
        (ρ := ⟨.R0, .pl (g (x + 1)), .up (g (x + 1)) 0, .L, .go .L0⟩) (by simp [symRules])
      refine ⟨_, hρ3, rfl, ?_, ?_⟩
      · simp only; rw [upd_ne _ _ hne]
      · simp only [BR, fire, mv, Nat.sub_zero]; congr 1; omega
    have s3 := countR (T := T) (idx := idx) (side := side) hS (fun i => .pl (g i)) x r.t (g (x + 1))
      (idx q) hjm (idx q) (Nat.le_refl _)
    have s4 : Step (conv T idx m side ss) (BR (fun i => .pl (g i)) x r.t (g (x + 1)) (idx q) (idx q))
        (enc idx side { st := .go q, pos := x + 1, tape := upd g x r.t }) := by
      have hρ6 := mem_sym (T := T) (idx := idx) (m := m) (side := side) (hS r.t)
        (ρ := ⟨.L0, .dn r.t 0, .pl r.t, .R, .go .R0⟩) (by simp [symRules])
      refine ⟨_, hρ6, rfl, ?_, ?_⟩
      · simp only [BR, Nat.sub_self]; rw [upd_ne _ _ (Ne.symm hne), upd_eq]
      · simp only [BR, enc, fire, mv, X, hside', if_true, Nat.sub_self]
        rw [upd_comm _ _ _ (Ne.symm hne), upd_upd, upd_comm _ _ _ hne, ← upd_comp FSym.pl]
        congr 2
        rw [upd_ne _ _ hne]
    refine ⟨1 + 2 * idx q + 1, ?_⟩
    have := ((StepN.single s1).trans (StepN.single s2)).trans (s3.trans (StepN.single s4))
    rw [show 1 + 1 + (2 * idx q + 1) = 1 + 2 * idx q + 1 + 1 by omega] at this
    simpa [fire, hq, hd, mv] using this
  | L =>
    have hside' := hL hd
    have hne : x - 1 ≠ x := by omega
    rw [hd] at hρ
    have s1 : Step (conv T idx m side ss) (enc idx side ⟨.go r.p, x, g⟩)
        { st := .go .L0, pos := x - 1, tape := upd (fun i => .pl (g i)) x (.dn r.t (idx q)) } := by
      refine ⟨_, hρ, rfl, ?_, ?_⟩
      · simp [enc, upd_eq, hsr]
      · simp only [enc, fire, mv, reduceCtorEq, if_false]; rw [upd_upd, Int.sub_eq_add_neg]
    have s2 : Step (conv T idx m side ss)
        { st := .go .L0, pos := x - 1, tape := upd (fun i => .pl (g i)) x (.dn r.t (idx q)) }
        (BL (fun i => .pl (g i)) x r.t (g (x - 1)) (idx q) 0) := by
      have hρ3 := mem_sym (T := T) (idx := idx) (m := m) (side := side) (hS (g (x - 1)))
        (ρ := ⟨.L0, .pl (g (x - 1)), .up (g (x - 1)) 0, .R, .go .R0⟩) (by simp [symRules])
      refine ⟨_, hρ3, rfl, ?_, ?_⟩
      · simp only; rw [upd_ne _ _ hne]
      · simp only [BL, fire, mv, Nat.sub_zero]; congr 1; omega
    have s3 := countL (T := T) (idx := idx) (side := side) hS (fun i => .pl (g i)) x r.t (g (x - 1))
      (idx q) hjm (idx q) (Nat.le_refl _)
    have s4 : Step (conv T idx m side ss) (BL (fun i => .pl (g i)) x r.t (g (x - 1)) (idx q) (idx q))
        (enc idx side { st := .go q, pos := x - 1, tape := upd g x r.t }) := by
      have hρ6 := mem_sym (T := T) (idx := idx) (m := m) (side := side) (hS r.t)
        (ρ := ⟨.R0, .dn r.t 0, .pl r.t, .L, .go .L0⟩) (by simp [symRules])
      refine ⟨_, hρ6, rfl, ?_, ?_⟩
      · simp only [BL, Nat.sub_self]; rw [upd_ne _ _ (Ne.symm hne), upd_eq]
      · simp only [BL, enc, fire, mv, X, hside', Nat.sub_self, Bool.false_eq_true, if_false]
        rw [upd_comm _ _ _ (Ne.symm hne), upd_upd, upd_comm _ _ _ hne, ← upd_comp FSym.pl]
        congr 2
        rw [upd_ne _ _ hne]
    refine ⟨1 + 2 * idx q + 1, ?_⟩
    have := ((StepN.single s1).trans (StepN.single s2)).trans (s3.trans (StepN.single s4))
    rw [show 1 + 1 + (2 * idx q + 1) = 1 + 2 * idx q + 1 + 1 by omega] at this
    have e : x + -1 = x - 1 := by omega
    simpa [fire, hq, hd, mv, e] using this

end Sim

/-! ## 3. 停止の対応と、停止の 3 項の移送 -/

section Main
variable {T : Machine Q P S} {idx : Q → Nat} {m : Nat} {side : Q → Bool} {ss : List S}

/-- T が実状態の配置 c で止まるなら、T̃ も enc c で止まる（状態の番号が単射なら）。 -/
theorem halted_sim (hinj : ∀ p q, idx p = idx q → p = q) {c : Cfg Q P S} {p : Q} (hc : c.st = .go p)
    (hh : Halted T c) : Halted (conv T idx m side ss) (enc idx side c) := by
  intro c' ⟨ρ, hρ, hst, hs, _⟩
  obtain ⟨st, x, g⟩ := c
  simp only at hc; subst hc
  simp only [enc, upd_eq] at hst hs
  rcases List.mem_append.mp hρ with h | h
  · obtain ⟨r, hr, hcr⟩ := List.mem_filterMap.mp h
    unfold convRule at hcr
    split at hcr
    · cases hcr
      simp only [FSym.up.injEq] at hs
      obtain ⟨hs1, hs2⟩ := hs
      have := hinj _ _ hs2
      subst this
      exact hh _ ⟨r, hr, rfl, hs1, rfl⟩
    · cases hcr
  · obtain ⟨u, _, hu⟩ := List.mem_flatMap.mp h
    simp only [symRules, List.mem_append, List.mem_cons, List.mem_flatMap, List.mem_range,
      List.not_mem_nil, or_false] at hu
    rcases hu with h1 | ⟨k, _, h2⟩
    · rcases h1 with rfl | rfl | rfl | rfl <;> simp at hs
    · rcases h2 with rfl | rfl | rfl | rfl
      · simp at hs
      · simp at hs
      · simp only [X] at hst; split at hst <;> cases hst
      · simp only [X] at hst; split at hst <;> cases hst

/-- 規則 r の向きが行き先の側と合い、0 シフトでない（`decide` 用の Bool 版）。 -/
def sideOK (side : Q → Bool) (r : Rule Q P S) : Bool :=
  match r.q with
  | .go q => match r.d with
    | .R => side q
    | .L => !side q
    | .Z => false
  | .halt _ => true

theorem sideOK_spec {side : Q → Bool} {r : Rule Q P S} (h : sideOK side r = true) :
    match r.q with
    | .go q => (r.d = .R → side q = true) ∧ (r.d = .L → side q = false) ∧ r.d ≠ .Z
    | .halt _ => True := by
  unfold sideOK at h
  split at h
  · split at h <;> rename_i hd <;> simp_all
  · trivial

/-- 仮定のまとめ: T の記号は ss に列挙され、状態の番号は m 未満で単射、T は停止規則を持たず、
    規則の向きは行き先の側 `side` と合っていて 0 シフトは無い。 -/
structure Hyp (T : Machine Q P S) (idx : Q → Nat) (m : Nat) (side : Q → Bool) (ss : List S) : Prop where
  hS : ∀ s, s ∈ ss
  hidx : ∀ q, idx q < m
  hinj : ∀ p q, idx p = idx q → p = q
  hG : ∀ r ∈ T, r.q.isGo = true
  hside : ∀ r ∈ T, sideOK side r = true

theorem stepN_sim (H : Hyp T idx m side ss) {n : Nat} {a b : Cfg Q P S} (h : StepN T n a b) :
    ∃ N, n ≤ N ∧ StepN (conv T idx m side ss) N (enc idx side a) (enc idx side b) :=
  stepN_sim_of_step _ (fun h₁ =>
    let ⟨j, hj⟩ := step_sim H.hS H.hidx (fun r hr => sideOK_spec (H.hside r hr)) h₁
      (StepN.go_of_allGo H.hG (.single h₁) (Step.go h₁))
    ⟨j + 1, by omega, hj⟩) h

/-- **停止の 3 項の移送**。T の実状態の配置 a から「停止の 3 項」（停止配置 fin はどれも実状態）が
    成り立つなら、T̃ = conv T（決定的と仮定）も enc a から、停止配置を enc ∘ fin として成り立つ。 -/
theorem conv_simulates (H : Hyp T idx m side ss) (hD : Deterministic (conv T idx m side ss))
    (C : CTSH) (w : List Ch) (a : Cfg Q P S) (ha : ∃ q, a.st = .go q)
    (fin : List Ch → Nat → List Ch → Cfg Q P S)
    (hsim :
      (∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) → ∃ N rm, n ≤ N + 1 ∧ HaltsIn T N a (fin vf mf rm)) ∧
      (∀ N e, HaltsIn T N a e → ∃ n vf mf rm, CHaltsIn C n (w, 0) (vf, mf) ∧ e = fin vf mf rm)) :
    (∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) →
      ∃ N rm, n ≤ N + 1 ∧ HaltsIn (conv T idx m side ss) N (enc idx side a) (enc idx side (fin vf mf rm))) ∧
    (∀ N e, HaltsIn (conv T idx m side ss) N (enc idx side a) e →
      ∃ n vf mf rm, CHaltsIn C n (w, 0) (vf, mf) ∧ e = enc idx side (fin vf mf rm)) ∧
    ((∀ n e, ¬ CHaltsIn C n (w, 0) e) ↔
      (∀ N e, ¬ HaltsIn (conv T idx m side ss) N (enc idx side a) e)) := by
  refine transfer3 hD (enc idx side) (fun N e ⟨hs, hh⟩ => ?_)
    (fun _ _ _ hb => let ⟨N', hN', hs⟩ := stepN_sim H hb; ⟨N', hN', _, hs⟩) C w fin hsim
  obtain ⟨N', hN', hs'⟩ := stepN_sim H hs
  obtain ⟨q, hq⟩ := StepN.go_of_allGo H.hG hs ha
  exact ⟨N', hN', hs', halted_sim H.hinj hq hh⟩

end Main

/-! ## 4. 決定性と可逆性の保存（原典 Theorem 5.5 の証明の後半） -/

section Pres
variable {T : Machine Q P S} {idx : Q → Nat} {m : Nat} {side : Q → Bool} {ss : List S}

theorem mem_conv {ρ : Rule FSt P (FSym S)} (h : ρ ∈ conv T idx m side ss) :
    (∃ r ∈ T, ∃ q, r.q = .go q ∧ ρ = ⟨X side r.p, .up r.s (idx r.p), .dn r.t (idx q), r.d,
      .go (if r.d = .R then .R0 else .L0)⟩) ∨
    (∃ u ∈ ss, ρ ∈ symRules m u) := by
  rcases List.mem_append.mp h with h | h
  · obtain ⟨r, hr, e⟩ := List.mem_filterMap.mp h
    unfold convRule at e
    split at e
    · rename_i q hq; cases e; exact .inl ⟨r, hr, q, hq, rfl⟩
    · cases e
  · obtain ⟨u, hu, h⟩ := List.mem_flatMap.mp h
    exact .inr ⟨u, hu, h⟩

theorem mem_symRules {u : S} {ρ : Rule FSt P (FSym S)} (h : ρ ∈ symRules m u) :
    ρ = ⟨.R0, .pl u, .up u 0, .L, .go .L0⟩ ∨ ρ = ⟨.L0, .pl u, .up u 0, .R, .go .R0⟩ ∨
    ρ = ⟨.L0, .dn u 0, .pl u, .R, .go .R0⟩ ∨ ρ = ⟨.R0, .dn u 0, .pl u, .L, .go .L0⟩ ∨
    ∃ k, k + 1 < m ∧ (ρ = ⟨.L0, .dn u (k + 1), .dn u k, .R, .go .R1⟩ ∨
      ρ = ⟨.R0, .dn u (k + 1), .dn u k, .L, .go .L1⟩ ∨
      ρ = ⟨.R1, .up u k, .up u (k + 1), .L, .go .L0⟩ ∨ ρ = ⟨.L1, .up u k, .up u (k + 1), .R, .go .R0⟩) := by
  simp only [symRules, List.mem_append, List.mem_cons, List.mem_flatMap, List.mem_range,
    List.not_mem_nil, or_false] at h
  rcases h with (h | h | h | h) | ⟨k, hk, h⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl h))
  · exact .inr (.inr (.inr (.inl h)))
  · exact .inr (.inr (.inr (.inr ⟨k, by omega, h⟩)))

theorem X_ne_R1 (p : Q) : X side p ≠ .R1 := by unfold X; split <;> nofun
theorem X_ne_L1 (p : Q) : X side p ≠ .L1 := by unfold X; split <;> nofun
theorem R1_ne_X (p : Q) : FSt.R1 ≠ X side p := fun h => X_ne_R1 p h.symm
theorem L1_ne_X (p : Q) : FSt.L1 ≠ X side p := fun h => X_ne_L1 p h.symm

/-- **決定性の保存**: T が決定的で状態の番号が単射なら T̃ も決定的。 -/
theorem conv_det (hT : Deterministic T) (hinj : ∀ p q, idx p = idx q → p = q) :
    Deterministic (conv T idx m side ss) := by
  intro ρ₁ h₁ ρ₂ h₂ hne hp hs
  rcases mem_conv h₁ with ⟨r₁, hr₁, q₁, hq₁, rfl⟩ | ⟨u₁, _, h₁⟩ <;>
  rcases mem_conv h₂ with ⟨r₂, hr₂, q₂, hq₂, rfl⟩ | ⟨u₂, _, h₂⟩
  · simp only [FSym.up.injEq] at hs
    obtain ⟨hs, hi⟩ := hs
    have hpp := hinj _ _ hi
    by_cases e : r₁ = r₂
    · subst e; rw [hq₁] at hq₂; cases hq₂; exact hne rfl
    · exact hT r₁ hr₁ r₂ hr₂ e hpp hs
  · rcases mem_symRules h₂ with rfl | rfl | rfl | rfl | ⟨k, _, rfl | rfl | rfl | rfl⟩ <;>
      simp_all [X_ne_R1, X_ne_L1]
  · rcases mem_symRules h₁ with rfl | rfl | rfl | rfl | ⟨k, _, rfl | rfl | rfl | rfl⟩ <;>
      simp_all [R1_ne_X, L1_ne_X]
  · rcases mem_symRules h₁ with rfl | rfl | rfl | rfl | ⟨k, _, rfl | rfl | rfl | rfl⟩ <;>
    rcases mem_symRules h₂ with rfl | rfl | rfl | rfl | ⟨k', _, rfl | rfl | rfl | rfl⟩ <;>
      simp_all

/-- **可逆性の保存**（原典 Theorem 5.5 の証明）: T が可逆で、状態の番号が単射、規則の向きが行き先の側と
    合っていて 0 シフトが無いなら T̃ も可逆。 -/
theorem conv_rev (hR : Reversible T) (hinj : ∀ p q, idx p = idx q → p = q)
    (hside : ∀ r ∈ T, sideOK side r = true) :
    Reversible (conv T idx m side ss) := by
  intro ρ₁ h₁ ρ₂ h₂ hne hq
  rcases mem_conv h₁ with ⟨r₁, hr₁, q₁, hq₁, rfl⟩ | ⟨u₁, _, h₁⟩ <;>
  rcases mem_conv h₂ with ⟨r₂, hr₂, q₂, hq₂, rfl⟩ | ⟨u₂, _, h₂⟩
  · have hs₁ := sideOK_spec (hside r₁ hr₁); rw [hq₁] at hs₁
    have hs₂ := sideOK_spec (hside r₂ hr₂); rw [hq₂] at hs₂
    have hd : r₁.d = r₂.d := by
      simp only [Tgt.go.injEq] at hq
      cases h₁d : r₁.d <;> cases h₂d : r₂.d <;> simp_all
    refine ⟨hd, ?_⟩
    simp only [ne_eq, FSym.dn.injEq, not_and]
    intro ht hi
    have e := hinj _ _ hi
    subst e
    by_cases e : r₁ = r₂
    · subst e; exact hne rfl
    · exact (hR r₁ hr₁ r₂ hr₂ e (hq₁.trans hq₂.symm)).2 ht
  · have hs₁ := sideOK_spec (hside r₁ hr₁); rw [hq₁] at hs₁
    rcases mem_symRules h₂ with rfl | rfl | rfl | rfl | ⟨k, _, rfl | rfl | rfl | rfl⟩ <;>
      cases h₁d : r₁.d <;> simp_all
  · have hs₂ := sideOK_spec (hside r₂ hr₂); rw [hq₂] at hs₂
    rcases mem_symRules h₁ with rfl | rfl | rfl | rfl | ⟨k, _, rfl | rfl | rfl | rfl⟩ <;>
      cases h₂d : r₂.d <;> simp_all
  · rcases mem_symRules h₁ with rfl | rfl | rfl | rfl | ⟨k, _, rfl | rfl | rfl | rfl⟩ <;>
    rcases mem_symRules h₂ with rfl | rfl | rfl | rfl | ⟨k', _, rfl | rfl | rfl | rfl⟩ <;>
      simp_all <;> omega

end Pres

end URTM.Conv55
