/-
  改良版の 1WU 化（docs/09_three_state_2026-09-26.md §3.2、`tools/threestate.py` の `SingleWU`）の一般の模倣証明。

  T（零シフト規則・停止規則の無い機械）を 1 方向更新の機械 W に変換する。Morita の Lemma 5.9（Conv59.lean）と違い、
  T の 2 マスを 1 マスに詰めない。T の 1 マスを W の 1 マスに置き、毎掃引でテープを 1 マス右へずらす。

  W の記号: 空白 `bl`（位置 0 と使う範囲の外）、素の記号 `pl s`（T の空白 b も `pl b`）、
  Q₋ の印 `mk p s`（T は状態 p、ヘッドはこのマス、中身 s）、Q₊ の印 `mkp p v`（T は状態 p、ヘッドは右隣、このマスの中身 v）。
  Q₊ は右移動で入る状態（`isPlus`）、Q₋ はそれ以外（`qm` に列挙）。
  W の状態: `L`（q_L）、`c s`（記号 s を運ぶ）、`e1` `e2`（右端）、`r q t`（(q, t) ∈ Rl。次のマスに Q₊ の印を置く）、
  `g p v`（(p, v) ∈ Gl。v を運び、今読むマスが T のヘッド）。

      [L, bl, bl, +, c b]                   [L, x, x, −, L]（x ≠ bl）
      [c s, pl x, pl s, +, c x]             [c s, bl, pl s, +, e1]
      [c s, mk p u, mk q s, +, c t]         (δ(p,u) = (t, −, q))
      [c s, mk p u, pl s, +, r q t]         (δ(p,u) = (t, +, q))
      [c s, mkp p v, pl s, +, g p v]
      [e1, bl, pl b, +, e2]                 [e2, bl, bl, −, L]
      [r p v, pl x, mkp p v, +, c x]
      [g p v, pl u, mk q v, +, c t]         (δ(p,u) = (t, −, q))
      [g p v, pl u, pl v, +, r q t]         (δ(p,u) = (t, +, q))

  配置の対応 `encV a n p x g`: W は L で位置 0（空白）を読み、位置 i = 1..n に T のマス a + i − 1 を置く
  （ヘッドの印は Q₋ ならマス x、Q₊ ならマス x − 1）。不変量 `Inv`: a + 1 ≤ x、x + 2 ≤ a + n、範囲の外は空白、
  Q₊ なら (p, g (x − 1)) ∈ Gl。W の 1 回の掃引が T の 1 ステップで、a は 1 減り n は 2 増える。

  掃引の各ステップの行き先は述語 `good` を満たす（`GRun`）。3 状態化（Conv3P.lean）の計数記号の刈り込みの健全性に使う。

  mathlib 非依存。未証明の穴・新規公理・native_decide を使わない。
-/
import URTM.Conv3Base
import URTM.Conv59

set_option linter.unusedSectionVars false

namespace URTM.Conv1W

open URTM URTM.KState URTM.SimLemmas URTM.Conv3Base
open URTM.Conv55 (upd_eq upd_ne upd_upd upd_comm)
open URTM.Conv59 (mix mix_lt mix_ge mix_step)

/-- W の状態。 -/
inductive VSt (Q S : Type) where
  | L
  | c (s : S)
  | e1
  | e2
  | r (p : Q) (v : S)
  | g (p : Q) (v : S)
  deriving DecidableEq, Repr

/-- W の記号。 -/
inductive VSym (Q S : Type) where
  | bl
  | pl (s : S)
  | mk (p : Q) (s : S)
  | mkp (p : Q) (v : S)
  deriving DecidableEq, Repr

variable {Q P S : Type} [DecidableEq Q] [DecidableEq S]

/-- 規則 r が状態 q へ右移動で入るか。 -/
def entersR (r : Rule Q P S) (q : Q) : Bool :=
  (match r.q with
   | .go q' => q' == q
   | .halt _ => false) && r.d == .R

/-- Q₊ の状態か（右移動で入る規則がある）。 -/
def isPlus (T : Machine Q P S) (q : Q) : Bool := T.any (fun r => entersR r q)

/-- T の規則を (状態, 記号) から引く。 -/
def look (T : Machine Q P S) (p : Q) (u : S) : Option (Rule Q P S) := T.find? (fun r => r.p == p && r.s == u)

/-- c s が Q₋ の印 mk p u を読む規則（T の規則 r = δ(p, u) から）。 -/
def headC (s : S) (p : Q) (u : S) (r : Rule Q P S) : Option (Rule (VSt Q S) P (VSym Q S)) :=
  match r.q with
  | .go q => some (if r.d = .L then ⟨.c s, .mk p u, .mk q s, .R, .go (.c r.t)⟩
      else ⟨.c s, .mk p u, .pl s, .R, .go (.r q r.t)⟩)
  | .halt _ => none

/-- g p v が素の記号 u を読む規則（T の規則 r = δ(p, u) から）。 -/
def headG (p : Q) (v u : S) (r : Rule Q P S) : Option (Rule (VSt Q S) P (VSym Q S)) :=
  match r.q with
  | .go q => some (if r.d = .L then ⟨.g p v, .pl u, .mk q v, .R, .go (.c r.t)⟩
      else ⟨.g p v, .pl u, .pl v, .R, .go (.r q r.t)⟩)
  | .halt _ => none

/-- W の空白以外の記号の列（`threestate.py` の `symbols[1:]` と同じ順）。 -/
def allSyms (ss : List S) (qm : List Q) (Gl : List (Q × S)) : List (VSym Q S) :=
  ss.map .pl ++ qm.flatMap (fun p => ss.map (.mk p)) ++ Gl.map (fun pv => .mkp pv.1 pv.2)

/-- c s の規則（`threestate.py` と同じ順）。 -/
def partC (T : Machine Q P S) (ss : List S) (qm : List Q) (Gl : List (Q × S)) (s : S) :
    List (Rule (VSt Q S) P (VSym Q S)) :=
  ss.map (fun x => ⟨.c s, .pl x, .pl s, .R, .go (.c x)⟩) ++
  [⟨.c s, .bl, .pl s, .R, .go .e1⟩] ++
  qm.flatMap (fun p => ss.filterMap (fun u => (look T p u).bind (headC s p u))) ++
  Gl.map (fun pv => ⟨.c s, .mkp pv.1 pv.2, .pl s, .R, .go (.g pv.1 pv.2)⟩)

/-- **改良版の 1WU 化** W。b は T の空白、ss は T の記号、qm は Q₋ の状態、Rl は右移動の行き先と書込記号の組、
    Gl ⊇ Rl は Q₊ の印の組。 -/
def conv (T : Machine Q P S) (b : S) (ss : List S) (qm : List Q) (Rl Gl : List (Q × S)) :
    Machine (VSt Q S) P (VSym Q S) :=
  [⟨.L, .bl, .bl, .R, .go (.c b)⟩] ++
  (allSyms ss qm Gl).map (fun x => ⟨.L, x, x, .L, .go .L⟩) ++
  ss.flatMap (partC T ss qm Gl) ++
  [⟨.e1, .bl, .pl b, .R, .go .e2⟩, ⟨.e2, .bl, .bl, .L, .go .L⟩] ++
  Rl.flatMap (fun pv => ss.map (fun x => ⟨.r pv.1 pv.2, .pl x, .mkp pv.1 pv.2, .R, .go (.c x)⟩)) ++
  Gl.flatMap (fun pv => ss.filterMap (fun u => (look T pv.1 u).bind (headG pv.1 pv.2 u)))

/-! ## 1. 符号化 -/

/-- 印を置く T のマス（Q₊ ならヘッドの 1 つ左）。 -/
def mpos (T : Machine Q P S) (p : Q) (x : Int) : Int := if isPlus T p then x - 1 else x

/-- 印の記号。 -/
def mark (T : Machine Q P S) (p : Q) (s : S) : VSym Q S := if isPlus T p then .mkp p s else .mk p s

/-- T のマス y の W での記号。 -/
def cell (T : Machine Q P S) (p : Q) (x : Int) (g : Int → S) (y : Int) : VSym Q S :=
  if y = mpos T p x then mark T p (g y) else .pl (g y)

/-- W のテープ: 位置 1..n に T のマス a..a+n−1。 -/
def packV (T : Machine Q P S) (a : Int) (n : Nat) (p : Q) (x : Int) (g : Int → S) (i : Int) : VSym Q S :=
  if 1 ≤ i ∧ i ≤ n then cell T p x g (a + i - 1) else .bl

/-- 掃引の始まり（L が位置 0 の空白を読む）の配置。 -/
def encV (T : Machine Q P S) (a : Int) (n : Nat) (p : Q) (x : Int) (g : Int → S) : Cfg (VSt Q S) P (VSym Q S) :=
  { st := .go .L, pos := 0, tape := packV T a n p x g }

/-- T が止まる配置（状態 p、ヘッド x）で W が止まる配置: 掃引がヘッドの印まで進み、
    Q₋ なら c (g (x−1)) が印を、Q₊ なら g p (g (x−1)) がヘッドのマスを読んで止まる。 -/
def haltV (T : Machine Q P S) (a : Int) (n : Nat) (p : Q) (x : Int) (g : Int → S) : Cfg (VSt Q S) P (VSym Q S) :=
  { st := .go (if isPlus T p then .g p (g (x - 1)) else .c (g (x - 1))), pos := x - a + 1,
    tape := mix (x - a + 1) (packV T (a - 1) n p x g) (packV T a n p x g) }

/-- 不変量。 -/
structure Inv (T : Machine Q P S) (b : S) (Gl : List (Q × S)) (a : Int) (n : Nat) (p : Q) (x : Int)
    (g : Int → S) : Prop where
  lo : a + 1 ≤ x
  hi : x + 2 ≤ a + n
  out : ∀ j, (j < a ∨ a + n ≤ j) → g j = b
  gl : isPlus T p = true → (p, g (x - 1)) ∈ Gl

/-- 行き先の配置が good を満たす（状態 q で読む記号について）。 -/
def Good (good : VSt Q S → VSym Q S → Prop) (c : Cfg (VSt Q S) P (VSym Q S)) : Prop :=
  ∀ q, c.st = .go q → good q (c.tape c.pos)

/-- 仮定のまとめ。 -/
structure Hyp (T : Machine Q P S) (b : S) (ss : List S) (qm : List Q) (Rl Gl : List (Q × S))
    (good : VSt Q S → VSym Q S → Prop) : Prop where
  hS : ∀ s, s ∈ ss
  /-- 規則はどれも実状態へ入り、左右どちらかへ動く。 -/
  hG : ∀ r ∈ T, r.q.isGo = true ∧ r.d ≠ .Z
  hD : Deterministic T
  /-- 左移動で入る状態は Q₋（可逆なら成り立つ。`hLm_of_rev`）。 -/
  hLm : ∀ r ∈ T, ∀ q, r.q = .go q → r.d = .L → isPlus T q = false
  hqm : ∀ q, isPlus T q = false → q ∈ qm
  hR : ∀ r ∈ T, ∀ q, r.q = .go q → r.d = .R → (q, r.t) ∈ Rl
  hRG : ∀ pv ∈ Rl, pv ∈ Gl
  good_c : ∀ s x, x ∈ (.bl :: allSyms ss qm Gl) → good (.c s) x
  good_r : ∀ pv ∈ Rl, ∀ x, good (.r pv.1 pv.2) (.pl x)
  good_g : ∀ pv ∈ Gl, ∀ u, good (.g pv.1 pv.2) (.pl u)
  good_e1 : good .e1 .bl
  good_e2 : good .e2 .bl
  good_L : ∀ x, good .L x

/-! ## 2. 基本の補題 -/

theorem isPlus_iff {T : Machine Q P S} {q : Q} : isPlus T q = true ↔ ∃ r ∈ T, r.q = .go q ∧ r.d = .R := by
  simp only [isPlus, List.any_eq_true, entersR, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨r, hr, h1, h2⟩
    refine ⟨r, hr, ?_, h2⟩
    revert h1; cases r.q <;> simp_all
  · rintro ⟨r, hr, h1, h2⟩
    exact ⟨r, hr, by rw [h1]; simp, h2⟩

theorem isPlus_of {T : Machine Q P S} {r : Rule Q P S} (hr : r ∈ T) {q : Q} (hq : r.q = .go q) (hd : r.d = .R) :
    isPlus T q = true := isPlus_iff.mpr ⟨r, hr, hq, hd⟩

omit [DecidableEq Q] [DecidableEq S] in
theorem hLm_of_rev_aux {T : Machine Q P S} (hR : Reversible T) {r r' : Rule Q P S} (hr : r ∈ T) (hr' : r' ∈ T)
    (hq : r.q = r'.q) (hd : r.d = .L) (hd' : r'.d = .R) : False := by
  by_cases e : r = r'
  · subst e; rw [hd] at hd'; cases hd'
  · have := (hR r hr r' hr' e hq).1; rw [hd, hd'] at this; cases this

theorem hLm_of_rev {T : Machine Q P S} (hR : Reversible T) :
    ∀ r ∈ T, ∀ q, r.q = .go q → r.d = .L → isPlus T q = false := by
  intro r hr q hq hd
  cases h : isPlus T q with
  | false => rfl
  | true =>
    obtain ⟨r', hr', hq', hd'⟩ := isPlus_iff.mp h
    exact (hLm_of_rev_aux hR hr hr' (by rw [hq, hq']) hd hd').elim

theorem look_some {T : Machine Q P S} {p : Q} {u : S} {r : Rule Q P S} (h : look T p u = some r) :
    r ∈ T ∧ r.p = p ∧ r.s = u := by
  refine ⟨List.mem_of_find?_eq_some h, ?_⟩
  have := List.find?_some h
  simpa using this

theorem look_of {T : Machine Q P S} (hD : Deterministic T) {r : Rule Q P S} (hr : r ∈ T) :
    look T r.p r.s = some r := by
  cases h : look T r.p r.s with
  | none =>
    have := List.find?_eq_none.mp h r hr
    simp at this
  | some r' =>
    obtain ⟨hr', hp, hs⟩ := look_some h
    by_cases e : r' = r
    · rw [e]
    · exact absurd hs (hD r' hr' r hr e hp)

/-! ### 規則の所属 -/

section Mem
variable {T : Machine Q P S} {b : S} {ss : List S} {qm : List Q} {Rl Gl : List (Q × S)}

theorem mem_L0 : (⟨.L, .bl, .bl, .R, .go (.c b)⟩ : Rule (VSt Q S) P (VSym Q S)) ∈ conv T b ss qm Rl Gl := by
  simp [conv]

theorem mem_LL {x : VSym Q S} (hx : x ∈ allSyms ss qm Gl) :
    (⟨.L, x, x, .L, .go .L⟩ : Rule (VSt Q S) P (VSym Q S)) ∈ conv T b ss qm Rl Gl := by
  unfold conv; simp only [List.mem_append, List.mem_map]
  left; left; left; left; right; exact ⟨x, hx, rfl⟩

theorem mem_partC {s : S} (hs : s ∈ ss) {ρ : Rule (VSt Q S) P (VSym Q S)} (h : ρ ∈ partC T ss qm Gl s) :
    ρ ∈ conv T b ss qm Rl Gl := by
  unfold conv; simp only [List.mem_append, List.mem_flatMap]
  left; left; left; right; exact ⟨s, hs, h⟩

theorem mem_shift (hS : ∀ s, s ∈ ss) (s x : S) :
    (⟨.c s, .pl x, .pl s, .R, .go (.c x)⟩ : Rule (VSt Q S) P (VSym Q S)) ∈ conv T b ss qm Rl Gl :=
  mem_partC (hS s) (by unfold partC; simp only [List.mem_append, List.mem_map]; left; left; left; exact ⟨x, hS x, rfl⟩)

theorem mem_ce1 (hS : ∀ s, s ∈ ss) (s : S) :
    (⟨.c s, .bl, .pl s, .R, .go .e1⟩ : Rule (VSt Q S) P (VSym Q S)) ∈ conv T b ss qm Rl Gl :=
  mem_partC (hS s) (by unfold partC; simp)

theorem mem_headC (hS : ∀ s, s ∈ ss) (s : S) {p : Q} (hp : p ∈ qm) (u : S) {ρ : Rule (VSt Q S) P (VSym Q S)}
    (h : (look T p u).bind (headC s p u) = some ρ) : ρ ∈ conv T b ss qm Rl Gl :=
  mem_partC (hS s) (by
    unfold partC; simp only [List.mem_append, List.mem_flatMap, List.mem_filterMap]
    left; right; exact ⟨p, hp, u, hS u, h⟩)

theorem mem_cg (hS : ∀ s, s ∈ ss) (s : S) {pv : Q × S} (hpv : pv ∈ Gl) :
    (⟨.c s, .mkp pv.1 pv.2, .pl s, .R, .go (.g pv.1 pv.2)⟩ : Rule (VSt Q S) P (VSym Q S)) ∈ conv T b ss qm Rl Gl :=
  mem_partC (hS s) (by
    unfold partC; simp only [List.mem_append, List.mem_map]
    right; exact ⟨pv, hpv, rfl⟩)

theorem mem_e1 : (⟨.e1, .bl, .pl b, .R, .go .e2⟩ : Rule (VSt Q S) P (VSym Q S)) ∈ conv T b ss qm Rl Gl := by
  unfold conv; simp only [List.mem_append, List.mem_cons]; left; left; right; simp

theorem mem_e2 : (⟨.e2, .bl, .bl, .L, .go .L⟩ : Rule (VSt Q S) P (VSym Q S)) ∈ conv T b ss qm Rl Gl := by
  unfold conv; simp only [List.mem_append, List.mem_cons]; left; left; right; simp

theorem mem_r (hS : ∀ s, s ∈ ss) {pv : Q × S} (hpv : pv ∈ Rl) (x : S) :
    (⟨.r pv.1 pv.2, .pl x, .mkp pv.1 pv.2, .R, .go (.c x)⟩ : Rule (VSt Q S) P (VSym Q S)) ∈ conv T b ss qm Rl Gl := by
  unfold conv; simp only [List.mem_append, List.mem_flatMap, List.mem_map]
  left; right; exact ⟨pv, hpv, x, hS x, rfl⟩

theorem mem_headG (hS : ∀ s, s ∈ ss) {pv : Q × S} (hpv : pv ∈ Gl) (u : S) {ρ : Rule (VSt Q S) P (VSym Q S)}
    (h : (look T pv.1 u).bind (headG pv.1 pv.2 u) = some ρ) : ρ ∈ conv T b ss qm Rl Gl := by
  unfold conv; simp only [List.mem_append, List.mem_flatMap, List.mem_filterMap]
  right; exact ⟨pv, hpv, u, hS u, h⟩

end Mem

/-! ### 符号化の補題 -/

theorem packV_out {T : Machine Q P S} {a : Int} {n : Nat} {p : Q} {x : Int} {g : Int → S} {i : Int}
    (h : i < 1 ∨ n < i) : packV T a n p x g i = .bl := by
  simp only [packV]; rw [if_neg (by omega)]

theorem packV_in {T : Machine Q P S} {a : Int} {n : Nat} {p : Q} {x : Int} {g : Int → S} {i : Int}
    (h1 : 1 ≤ i) (h2 : i ≤ n) : packV T a n p x g i = cell T p x g (a + i - 1) := by
  simp only [packV]; rw [if_pos ⟨h1, h2⟩]

theorem packV_pl {T : Machine Q P S} {a : Int} {n : Nat} {p : Q} {x : Int} {g : Int → S} {i : Int}
    (h1 : 1 ≤ i) (h2 : i ≤ n) (hm : a + i - 1 ≠ mpos T p x) : packV T a n p x g i = .pl (g (a + i - 1)) := by
  rw [packV_in h1 h2]; simp only [cell]; rw [if_neg hm]

theorem packV_mk {T : Machine Q P S} {a : Int} {n : Nat} {p : Q} {x : Int} {g : Int → S} {i : Int}
    (h1 : 1 ≤ i) (h2 : i ≤ n) (hm : a + i - 1 = mpos T p x) : packV T a n p x g i = mark T p (g (a + i - 1)) := by
  rw [packV_in h1 h2]; simp only [cell]; rw [if_pos hm]

theorem mpos_minus {T : Machine Q P S} {p : Q} (h : isPlus T p = false) (x : Int) : mpos T p x = x := by
  simp [mpos, h]
theorem mpos_plus {T : Machine Q P S} {p : Q} (h : isPlus T p = true) (x : Int) : mpos T p x = x - 1 := by
  simp [mpos, h]
theorem mark_minus {T : Machine Q P S} {p : Q} (h : isPlus T p = false) (s : S) : mark T p s = .mk p s := by
  simp [mark, h]
theorem mark_plus {T : Machine Q P S} {p : Q} (h : isPlus T p = true) (s : S) : mark T p s = .mkp p s := by
  simp [mark, h]

/-- 符号化のマスはどれも q_L の左移動の規則を持つ。 -/
theorem packV_allSyms {T : Machine Q P S} {b : S} {ss : List S} {qm : List Q} {Rl Gl : List (Q × S)}
    {good : VSt Q S → VSym Q S → Prop} (H : Hyp T b ss qm Rl Gl good)
    {a : Int} {n : Nat} {p : Q} {x : Int} {g : Int → S} (hI : Inv T b Gl a n p x g) {i : Int}
    (h1 : 1 ≤ i) (h2 : i ≤ n) : packV T a n p x g i ∈ allSyms ss qm Gl := by
  rw [packV_in h1 h2]; simp only [cell, allSyms, List.mem_append, List.mem_map, List.mem_flatMap]
  split
  · rename_i hm
    cases hp : isPlus T p with
    | false =>
      rw [mark_minus hp]; left; right; exact ⟨p, H.hqm p hp, _, H.hS _, rfl⟩
    | true =>
      rw [mark_plus hp]; right
      rw [mpos_plus hp] at hm
      exact ⟨_, hI.gl hp, by rw [hm]⟩
  · left; left; exact ⟨_, H.hS _, rfl⟩

theorem mv_R : mv Dir.R = 1 := rfl

theorem mpos_le (T : Machine Q P S) (p : Q) (x : Int) : x - 1 ≤ mpos T p x ∧ mpos T p x ≤ x := by
  unfold mpos; split <;> omega

theorem packV_mem {T : Machine Q P S} {b : S} {ss : List S} {qm : List Q} {Rl Gl : List (Q × S)}
    {good : VSt Q S → VSym Q S → Prop} (H : Hyp T b ss qm Rl Gl good)
    {a : Int} {n : Nat} {p : Q} {x : Int} {g : Int → S} (hI : Inv T b Gl a n p x g) (i : Int) :
    packV T a n p x g i ∈ (.bl :: allSyms ss qm Gl) := by
  by_cases h : 1 ≤ i ∧ i ≤ n
  · exact List.mem_cons_of_mem _ (packV_allSyms H hI h.1 h.2)
  · rw [packV_out (by omega)]; exact List.mem_cons_self ..

/-! ## 3. 掃引 -/

section Sweep
variable {T : Machine Q P S} {b : S} {ss : List S} {qm : List Q} {Rl Gl : List (Q × S)}
  {good : VSt Q S → VSym Q S → Prop}

theorem good_c' (H : Hyp T b ss qm Rl Gl good) (s : S) (i : Int) (F O : Int → VSym Q S)
    (hO : O i ∈ (.bl :: allSyms ss qm Gl)) :
    Good good ({ st := .go (.c s), pos := i, tape := mix i F O } : Cfg (VSt Q S) P (VSym Q S)) := by
  intro q hq; cases hq; simp only; rw [mix_ge (Int.le_refl _)]; exact H.good_c _ _ hO

theorem good_L' (H : Hyp T b ss qm Rl Gl good) (i : Int) (t : Int → VSym Q S) :
    Good good ({ st := .go .L, pos := i, tape := t } : Cfg (VSt Q S) P (VSym Q S)) := by
  intro q hq; cases hq; exact H.good_L _

/-- 右へずらす: 位置 i から k マス、古い記号 pl (G' (a+j−1)) を運んできた pl (G' (a+j−2)) に書き換える。 -/
theorem shift (H : Hyp T b ss qm Rl Gl good) (G' : Int → S) (a : Int) (F O : Int → VSym Q S)
    (hO : ∀ j, O j ∈ (.bl :: allSyms ss qm Gl)) :
    ∀ (k : Nat) (i : Int), (∀ j, i ≤ j → j < i + k →
      O j = .pl (G' (a + j - 1)) ∧ F j = .pl (G' (a + j - 2))) →
    GRun (conv T b ss qm Rl Gl) (Good good) k
      { st := .go (.c (G' (a + i - 2))), pos := i, tape := mix i F O }
      { st := .go (.c (G' (a + (i + k) - 2))), pos := i + k, tape := mix (i + k) F O } := by
  intro k
  induction k with
  | zero => intro i _; rw [show i + ((0 : Nat) : Int) = i by omega]; exact .refl _
  | succ k ih =>
    intro i hj
    obtain ⟨ho, hF⟩ := hj i (Int.le_refl _) (by omega)
    have s1 : Step (conv T b ss qm Rl Gl)
        { st := .go (.c (G' (a + i - 2))), pos := i, tape := mix i F O }
        { st := .go (.c (G' (a + (i + 1) - 2))), pos := i + 1, tape := mix (i + 1) F O } := by
      refine ⟨_, mem_shift H.hS (G' (a + i - 2)) (G' (a + i - 1)), rfl, ?_, ?_⟩
      · simp only; rw [mix_ge (Int.le_refl _), ho]
      · simp only [fire, mv]
        rw [show a + (i + 1) - 2 = a + i - 1 by omega, ← hF, mix_step]
    have := GRun.cons s1 (good_c' H _ _ _ _ (hO _)) (ih (i + 1) (fun j h1 h2 => hj j (by omega) (by omega)))
    rwa [show i + 1 + (k : Int) = i + ((k + 1 : Nat) : Int) by omega] at this

/-- 左への戻り: q_L が位置 k から空白でないマスを左へ越えて位置 0 まで。 -/
theorem sweepL (H : Hyp T b ss qm Rl Gl good) (F : Int → VSym Q S) :
    ∀ k : Nat, (∀ j : Int, 1 ≤ j → j ≤ k → F j ∈ allSyms ss qm Gl) →
    GRun (conv T b ss qm Rl Gl) (Good good) k { st := .go .L, pos := k, tape := F }
      { st := .go .L, pos := 0, tape := F } := by
  intro k
  induction k with
  | zero => intro _; exact .refl _
  | succ k ih =>
    intro hF
    have hx := hF (k + 1) (by omega) (Int.le_refl _)
    have s1 : Step (conv T b ss qm Rl Gl) { st := .go .L, pos := ((k + 1 : Nat) : Int), tape := F }
        { st := .go .L, pos := k, tape := F } := by
      refine ⟨_, mem_LL (b := b) (Rl := Rl) (T := T) hx, rfl, rfl, ?_⟩
      simp only [fire, mv]; congr 1
      · push_cast; omega
      · push_cast; rw [Conv55.upd_self]
    exact GRun.cons s1 (good_L' H _ _) (ih (fun j h1 h2 => hF j h1 (by omega)))

/-- 掃引の前半: 位置 0 の空白から、位置 1..i−1 をずらし、位置 i に c (g (a+i−2)) で来る。 -/
theorem prefix_ (H : Hyp T b ss qm Rl Gl good) {a : Int} {n : Nat} {p : Q} {x : Int} {g : Int → S}
    (hI : Inv T b Gl a n p x g) (F : Int → VSym Q S) (hF0 : ∀ j, j < 1 → F j = .bl)
    (i : Int) (hi1 : 1 ≤ i) (hi : i ≤ mpos T p x - a + 1)
    (hF : ∀ j, 1 ≤ j → j < i → F j = .pl (g (a + j - 2))) :
    GRun (conv T b ss qm Rl Gl) (Good good) (1 + (i - 1).toNat) (encV T a n p x g)
      { st := .go (.c (g (a + i - 2))), pos := i, tape := mix i F (packV T a n p x g) } := by
  have hlo := hI.lo; have hhi := hI.hi
  have hm := mpos_le T p x
  have s1 : Step (conv T b ss qm Rl Gl) (encV T a n p x g)
      { st := .go (.c (g (a + 1 - 2))), pos := 1, tape := mix 1 F (packV T a n p x g) } := by
    refine ⟨_, mem_L0, rfl, ?_, ?_⟩
    · simp only [encV]; exact packV_out (by omega)
    · simp only [encV, fire, mv]
      congr 1
      · rw [hI.out (a + 1 - 2) (by omega)]
      · funext j; simp only [upd, mix]
        by_cases h : j = 0
        · subst h; simp [hF0 0 (by omega)]
        · rw [if_neg h]; by_cases h' : j < 1
          · rw [if_pos h', hF0 j h', packV_out (by omega)]
          · rw [if_neg h']
  have s2 := shift (T := T) (b := b) (ss := ss) (qm := qm) (Rl := Rl) (Gl := Gl) H g a F
    (packV T a n p x g) (packV_mem H hI) (i - 1).toNat 1 (by
      intro j h1 h2
      refine ⟨packV_pl h1 (by omega) (by omega), hF j h1 (by omega)⟩)
  have := GRun.cons s1 (good_c' H _ _ _ _ (packV_mem H hI _)) s2
  rw [show (1 : Int) + ((i - 1).toNat : Int) = i by omega, Nat.add_comm] at this
  exact this

/-- 掃引の後半: 位置 i0..n をずらし、右端に運んだ記号と空白 pl b を足し、折り返して位置 0 へ戻る。 -/
theorem suffix (H : Hyp T b ss qm Rl Gl good) {a : Int} {n : Nat} (g' : Int → S) (O F : Int → VSym Q S)
    (hO : ∀ j, O j ∈ (.bl :: allSyms ss qm Gl))
    (i0 : Int) (_h0 : 1 ≤ i0) (h1 : i0 ≤ n + 1)
    (hmid : ∀ j, i0 ≤ j → j < n + 1 → O j = .pl (g' (a + j - 1)) ∧ F j = .pl (g' (a + j - 2)))
    (hOout : ∀ j : Int, (n : Int) + 1 ≤ j → O j = .bl)
    (hFn1 : F (n + 1) = .pl (g' (a + n - 1))) (hFn2 : F (n + 2) = .pl b)
    (hFout : ∀ j : Int, (n : Int) + 3 ≤ j → F j = .bl)
    (hFsym : ∀ j : Int, 1 ≤ j → j ≤ ((n + 2 : Nat) : Int) → F j ∈ allSyms ss qm Gl) :
    ∃ k, GRun (conv T b ss qm Rl Gl) (Good good) (k + 1)
      { st := .go (.c (g' (a + i0 - 2))), pos := i0, tape := mix i0 F O }
      { st := .go .L, pos := 0, tape := F } := by
  have s1 := shift (T := T) (b := b) (ss := ss) (qm := qm) (Rl := Rl) (Gl := Gl) H g' a F O hO
    (n + 1 - i0).toNat i0 (fun j h1 h2 => hmid j h1 (by omega))
  rw [show i0 + ((n + 1 - i0).toNat : Int) = n + 1 by omega,
    show a + ((n : Int) + 1) - 2 = a + n - 1 by omega] at s1
  have s2 : Step (conv T b ss qm Rl Gl)
      { st := .go (.c (g' (a + n - 1))), pos := (n : Int) + 1, tape := mix (n + 1) F O }
      { st := .go .e1, pos := n + 2, tape := mix (n + 2) F O } := by
    refine ⟨_, mem_ce1 H.hS _, rfl, ?_, ?_⟩
    · simp only; rw [mix_ge (Int.le_refl _), hOout _ (Int.le_refl _)]
    · simp only [fire, mv]; rw [← hFn1, mix_step, show (n : Int) + 1 + 1 = n + 2 by omega]
  have g2 : Good good ({ st := .go .e1, pos := n + 2, tape := mix (n + 2) F O } : Cfg (VSt Q S) P (VSym Q S)) := by
    intro q hq; cases hq; simp only; rw [mix_ge (Int.le_refl _), hOout _ (by omega)]; exact H.good_e1
  have s3 : Step (conv T b ss qm Rl Gl)
      { st := .go .e1, pos := (n : Int) + 2, tape := mix (n + 2) F O }
      { st := .go .e2, pos := n + 3, tape := mix (n + 3) F O } := by
    refine ⟨_, mem_e1, rfl, ?_, ?_⟩
    · simp only; rw [mix_ge (Int.le_refl _), hOout _ (by omega)]
    · simp only [fire, mv]; rw [← hFn2, mix_step, show (n : Int) + 2 + 1 = n + 3 by omega]
  have g3 : Good good ({ st := .go .e2, pos := n + 3, tape := mix (n + 3) F O } : Cfg (VSt Q S) P (VSym Q S)) := by
    intro q hq; cases hq; simp only; rw [mix_ge (Int.le_refl _), hOout _ (by omega)]; exact H.good_e2
  have s4 : Step (conv T b ss qm Rl Gl)
      { st := .go .e2, pos := (n : Int) + 3, tape := mix (n + 3) F O }
      { st := .go .L, pos := ((n + 2 : Nat) : Int), tape := F } := by
    refine ⟨_, mem_e2, rfl, ?_, ?_⟩
    · simp only; rw [mix_ge (Int.le_refl _), hOout _ (by omega)]
    · simp only [fire, mv]; congr 1
      · push_cast; omega
      · funext j; simp only [upd, mix]
        by_cases h : j = n + 3
        · subst h; rw [if_pos rfl, hFout _ (Int.le_refl _)]
        · rw [if_neg h]; by_cases h' : j < n + 3
          · rw [if_pos h']
          · rw [if_neg h', hOout _ (by omega), hFout _ (by omega)]
  have s5 := sweepL (T := T) (b := b) (Rl := Rl) H F (n + 2) hFsym
  refine ⟨(n + 1 - i0).toNat + 2 + (n + 2), ?_⟩
  have := s1.trans (GRun.cons s2 g2 (GRun.cons s3 g3 (GRun.cons s4 (good_L' H _ _) s5)))
  rwa [show (n + 1 - i0).toNat + (n + 2 + 1 + 1 + 1) = (n + 1 - i0).toNat + 2 + (n + 2) + 1 by omega] at this

end Sweep

/-! ## 4. 1 回の掃引で T の 1 ステップ -/

section Step
variable {T : Machine Q P S} {b : S} {ss : List S} {qm : List Q} {Rl Gl : List (Q × S)}
  {good : VSt Q S → VSym Q S → Prop}

/-- 掃引の 1 マス右移動: 境界 i の左は新しい列 F、右は古い列 O。O i を読んで F i を書く右移動の規則で、
    境界が 1 つ右へ進む。 -/
theorem mix_step_R {M : Machine (VSt Q S) P (VSym Q S)} {σ σ' : VSt Q S} (F O : Int → VSym Q S) {i : Int}
    {u w : VSym Q S} (hρ : (⟨σ, u, w, .R, .go σ'⟩ : Rule (VSt Q S) P (VSym Q S)) ∈ M) (hu : O i = u)
    (hw : F i = w) :
    Step M { st := .go σ, pos := i, tape := mix i F O } { st := .go σ', pos := i + 1, tape := mix (i + 1) F O } := by
  refine ⟨_, hρ, rfl, ?_, ?_⟩
  · simp only; rw [mix_ge (Int.le_refl _), hu]
  · simp only [fire, mv_R]; rw [← hw, mix_step]

theorem good_mix {σ : VSt Q S} {i : Int} (F O : Int → VSym Q S) (h : good σ (O i)) :
    Good good ({ st := .go σ, pos := i, tape := mix i F O } : Cfg (VSt Q S) P (VSym Q S)) := by
  intro q hq; cases hq; simp only; rw [mix_ge (Int.le_refl _)]; exact h

theorem mv_cases (H : Hyp T b ss qm Rl Gl good) {r : Rule Q P S} (hr : r ∈ T) :
    (r.d = .L ∧ mv r.d = -1) ∨ (r.d = .R ∧ mv r.d = 1) := by
  cases hd : r.d with
  | L => exact .inl ⟨rfl, rfl⟩
  | Z => exact absurd hd (H.hG r hr).2
  | R => exact .inr ⟨rfl, rfl⟩

theorem inv_step (H : Hyp T b ss qm Rl Gl good) {a : Int} {n : Nat} {p : Q} {x : Int} {g : Int → S}
    (hI : Inv T b Gl a n p x g) {r : Rule Q P S} (hr : r ∈ T) {q : Q} (hq : r.q = .go q) :
    Inv T b Gl (a - 1) (n + 2) q (x + mv r.d) (upd g x r.t) := by
  have hlo := hI.lo; have hhi := hI.hi
  have hmv := mv_cases H hr
  refine ⟨by omega, by push_cast; omega, fun j hj => ?_, fun hp => ?_⟩
  · push_cast at hj
    rw [upd_ne _ _ (by omega)]; exact hI.out j (by omega)
  · rcases hmv with ⟨hd, _⟩ | ⟨hd, hm⟩
    · rw [H.hLm r hr q hq hd] at hp; cases hp
    · rw [hm, show x + 1 - 1 = x by omega, upd_eq]; exact H.hRG _ (H.hR r hr q hq hd)

/-- 行き先の印の位置は x 以下。 -/
theorem mpos_new (H : Hyp T b ss qm Rl Gl good) {r : Rule Q P S} (hr : r ∈ T) {q : Q} (hq : r.q = .go q)
    (x : Int) : mpos T q (x + mv r.d) ≤ x ∧ x - 1 ≤ mpos T q (x + mv r.d) := by
  rcases mv_cases H hr with ⟨hd, hm⟩ | ⟨hd, hm⟩
  · rw [hm, mpos_minus (H.hLm r hr q hq hd)]; omega
  · rw [hm, mpos_plus (isPlus_of hr hq hd)]; omega

/-- **1 回の掃引で T の 1 ステップ**。T の規則 r = [p, g x, t, d, q] による配置の変化を、W は encV a n から
    1 ステップ以上で encV (a−1) (n+2) へ（各ステップの行き先は good を満たす）。 -/
theorem step_sim (H : Hyp T b ss qm Rl Gl good) {a : Int} {n : Nat} {p : Q} {x : Int} {g : Int → S}
    (hI : Inv T b Gl a n p x g) {r : Rule Q P S} (hr : r ∈ T) (hp : r.p = p) (hs : g x = r.s) {q : Q}
    (hq : r.q = .go q) :
    ∃ k, GRun (conv T b ss qm Rl Gl) (Good good) (k + 1) (encV T a n p x g)
      (encV T (a - 1) (n + 2) q (x + mv r.d) (upd g x r.t)) := by
  have hlo := hI.lo; have hhi := hI.hi
  have hI' := inv_step H hI hr hq
  have hlook : look T p (g x) = some r := by rw [hs, ← hp]; exact look_of H.hD hr
  have hmq := mpos_new H hr hq x
  have hFsym : ∀ j : Int, 1 ≤ j → j ≤ ((n + 2 : Nat) : Int) →
      packV T (a - 1) (n + 2) q (x + mv r.d) (upd g x r.t) j ∈ allSyms ss qm Gl :=
    fun j h1 h2 => packV_allSyms H hI' h1 h2
  have hFout : ∀ j : Int, (n : Int) + 3 ≤ j → packV T (a - 1) (n + 2) q (x + mv r.d) (upd g x r.t) j = .bl :=
    fun j h => packV_out (by push_cast; omega)
  have hF0 : ∀ j : Int, j < 1 → packV T (a - 1) (n + 2) q (x + mv r.d) (upd g x r.t) j = .bl :=
    fun j h => packV_out (by omega)
  have hOout : ∀ j : Int, (n : Int) + 1 ≤ j → packV T a n p x g j = .bl := fun j h => packV_out (by omega)
  have hFn1 : packV T (a - 1) (n + 2) q (x + mv r.d) (upd g x r.t) (n + 1) = .pl (upd g x r.t (a + n - 1)) := by
    rw [packV_pl (by omega) (by push_cast; omega) (by omega)]
    rw [show a - 1 + ((n : Int) + 1) - 1 = a + n - 1 by omega]
  have hFn2 : packV T (a - 1) (n + 2) q (x + mv r.d) (upd g x r.t) (n + 2) = .pl b := by
    rw [packV_pl (by omega) (by push_cast; omega) (by omega), upd_ne _ _ (by omega), hI.out _ (by omega)]
  -- F の、印より左（新しい印の位置 mpos q x' より左）の素のマス
  have hFl : ∀ j : Int, 1 ≤ j → a + j - 2 < mpos T q (x + mv r.d) →
      packV T (a - 1) (n + 2) q (x + mv r.d) (upd g x r.t) j = .pl (g (a + j - 2)) := by
    intro j h1 h2
    rw [packV_pl h1 (by push_cast; omega) (by omega), upd_ne _ _ (by omega),
      show a - 1 + j - 1 = a + j - 2 by omega]
  -- F の、新しい印より右の素のマス
  have hFr : ∀ j : Int, 1 ≤ j → j ≤ n + 2 → mpos T q (x + mv r.d) < a + j - 2 →
      packV T (a - 1) (n + 2) q (x + mv r.d) (upd g x r.t) j = .pl (upd g x r.t (a + j - 2)) := by
    intro j h1 h2 h3
    rw [packV_pl h1 (by push_cast; omega) (by omega), show a - 1 + j - 1 = a + j - 2 by omega]
  -- O の、印より右の素のマス（T の x より右）
  have hOr : ∀ j : Int, 1 ≤ j → j ≤ n → x < a + j - 1 →
      packV T a n p x g j = .pl (upd g x r.t (a + j - 1)) := by
    intro j h1 h2 h3
    have := mpos_le T p x
    rw [packV_pl h1 h2 (by omega), upd_ne _ _ (by omega)]
  cases hP : isPlus T p with
  | false =>
    have hmp : mpos T p x = x := mpos_minus hP x
    have hpre := prefix_ (b := b) (Rl := Rl) H hI (packV T (a - 1) (n + 2) q (x + mv r.d) (upd g x r.t)) hF0
      (x - a + 1) (by omega) (by omega) (fun j h1 h2 => hFl j h1 (by omega))
    rw [show a + (x - a + 1) - 2 = x - 1 by omega] at hpre
    have hO : packV T a n p x g (x - a + 1) = .mk p (g x) := by
      rw [packV_mk (by omega) (by omega) (by omega), mark_minus hP, show a + (x - a + 1) - 1 = x by omega]
    rcases mv_cases H hr with ⟨hd, hm⟩ | ⟨hd, hm⟩
    · -- Q₋ のヘッド、左へ: [c s, mk p u, mk q s, +, c t]
      have hQ : isPlus T q = false := H.hLm r hr q hq hd
      have hρ : (⟨.c (g (x - 1)), .mk p (g x), .mk q (g (x - 1)), .R, .go (.c r.t)⟩ :
          Rule (VSt Q S) P (VSym Q S)) ∈ conv T b ss qm Rl Gl :=
        mem_headC H.hS (g (x - 1)) (H.hqm p hP) (g x) (by rw [hlook]; simp [headC, hq, hd])
      have hFi : packV T (a - 1) (n + 2) q (x + mv r.d) (upd g x r.t) (x - a + 1) = .mk q (g (x - 1)) := by
        rw [packV_mk (by omega) (by push_cast; omega) (by rw [mpos_minus hQ, hm]; omega), mark_minus hQ,
          upd_ne _ _ (by omega), show a - 1 + (x - a + 1) - 1 = x - 1 by omega]
      have s1 := mix_step_R (M := conv T b ss qm Rl Gl) (σ := (.c (g (x - 1))))
        (σ' := (.c (upd g x r.t (a + (x - a + 1 + 1) - 2))))
        (packV T (a - 1) (n + 2) q (x + mv r.d) (upd g x r.t)) (packV T a n p x g)
        (by rw [show a + (x - a + 1 + 1) - 2 = x by omega, upd_eq]; exact hρ) hO hFi
      obtain ⟨k, hk⟩ := suffix (b := b) (Rl := Rl) H (upd g x r.t) (packV T a n p x g) _ (packV_mem H hI) (x - a + 1 + 1)
        (by omega) (by omega)
        (fun j h1 h2 => ⟨hOr j (by omega) (by omega) (by omega),
          hFr j (by omega) (by omega) (by rw [mpos_minus hQ, hm]; omega)⟩)
        hOout hFn1 hFn2 hFout hFsym
      have := hpre.trans (GRun.cons s1 (good_c' H _ _ _ _ (packV_mem H hI _)) hk)
      exact ⟨_, by rw [show 1 + (x - a + 1 - 1).toNat + (k + 1 + 1) =
        (1 + (x - a + 1 - 1).toNat + k + 1) + 1 by omega] at this; exact this⟩
    · -- Q₋ のヘッド、右へ: [c s, mk p u, pl s, +, r q t] → [r q t, pl x, mkp q t, +, c x]
      have hQ : isPlus T q = true := isPlus_of hr hq hd
      have hρ1 : (⟨.c (g (x - 1)), .mk p (g x), .pl (g (x - 1)), .R, .go (.r q r.t)⟩ :
          Rule (VSt Q S) P (VSym Q S)) ∈ conv T b ss qm Rl Gl :=
        mem_headC H.hS (g (x - 1)) (H.hqm p hP) (g x) (by rw [hlook]; simp [headC, hq, hd])
      have hρ2 : (⟨.r q r.t, .pl (g (x + 1)), .mkp q r.t, .R, .go (.c (g (x + 1)))⟩ :
          Rule (VSt Q S) P (VSym Q S)) ∈ conv T b ss qm Rl Gl :=
        mem_r (pv := (q, r.t)) H.hS (H.hR r hr q hq hd) (g (x + 1))
      have hFi : packV T (a - 1) (n + 2) q (x + mv r.d) (upd g x r.t) (x - a + 1) = .pl (g (x - 1)) := by
        rw [hFl _ (by omega) (by rw [mpos_plus hQ, hm]; omega), show a + (x - a + 1) - 2 = x - 1 by omega]
      have hFi1 : packV T (a - 1) (n + 2) q (x + mv r.d) (upd g x r.t) (x - a + 1 + 1) = .mkp q r.t := by
        rw [packV_mk (by omega) (by push_cast; omega) (by rw [mpos_plus hQ, hm]; omega), mark_plus hQ,
          show a - 1 + (x - a + 1 + 1) - 1 = x by omega, upd_eq]
      have hOi1 : packV T a n p x g (x - a + 1 + 1) = .pl (g (x + 1)) := by
        rw [packV_pl (by omega) (by omega) (by omega), show a + (x - a + 1 + 1) - 1 = x + 1 by omega]
      have s1 := mix_step_R (M := conv T b ss qm Rl Gl) (σ := (.c (g (x - 1))))
        (σ' := (.r q r.t))
        (packV T (a - 1) (n + 2) q (x + mv r.d) (upd g x r.t)) (packV T a n p x g)
        hρ1 hO hFi
      have g1 := good_mix (P := P) (σ := (.r q r.t)) (i := x - a + 1 + 1)
        (packV T (a - 1) (n + 2) q (x + mv r.d) (upd g x r.t)) (packV T a n p x g)
        (by rw [hOi1]; exact H.good_r (q, r.t) (H.hR r hr q hq hd) _)
      have s2 := mix_step_R (M := conv T b ss qm Rl Gl) (σ := (.r q r.t))
        (σ' := (.c (upd g x r.t (a + (x - a + 1 + 1 + 1) - 2))))
        (packV T (a - 1) (n + 2) q (x + mv r.d) (upd g x r.t)) (packV T a n p x g)
        (by rw [show a + (x - a + 1 + 1 + 1) - 2 = x + 1 by omega, upd_ne _ _ (by omega)]; exact hρ2) hOi1 hFi1
      obtain ⟨k, hk⟩ := suffix (b := b) (Rl := Rl) H (upd g x r.t) (packV T a n p x g) _ (packV_mem H hI) (x - a + 1 + 1 + 1)
        (by omega) (by omega)
        (fun j h1 h2 => ⟨hOr j (by omega) (by omega) (by omega),
          hFr j (by omega) (by omega) (by rw [mpos_plus hQ, hm]; omega)⟩)
        hOout hFn1 hFn2 hFout hFsym
      have := hpre.trans (GRun.cons s1 g1 (GRun.cons s2 (good_c' H _ _ _ _ (packV_mem H hI _)) hk))
      exact ⟨_, by rw [show 1 + (x - a + 1 - 1).toNat + (k + 1 + 1 + 1) =
        (1 + (x - a + 1 - 1).toNat + k + 2) + 1 by omega] at this; exact this⟩
  | true =>
    have hmp : mpos T p x = x - 1 := mpos_plus hP x
    have hpre := prefix_ (b := b) (Rl := Rl) H hI (packV T (a - 1) (n + 2) q (x + mv r.d) (upd g x r.t)) hF0
      (x - a) (by omega) (by omega) (fun j h1 h2 => hFl j h1 (by omega))
    rw [show a + (x - a) - 2 = x - 2 by omega] at hpre
    have hO : packV T a n p x g (x - a) = .mkp p (g (x - 1)) := by
      rw [packV_mk (by omega) (by omega) (by omega), mark_plus hP, show a + (x - a) - 1 = x - 1 by omega]
    have hOi1 : packV T a n p x g (x - a + 1) = .pl (g x) := by
      rw [packV_pl (by omega) (by omega) (by omega), show a + (x - a + 1) - 1 = x by omega]
    have hρ0 : (⟨.c (g (x - 2)), .mkp p (g (x - 1)), .pl (g (x - 2)), .R, .go (.g p (g (x - 1)))⟩ :
        Rule (VSt Q S) P (VSym Q S)) ∈ conv T b ss qm Rl Gl :=
      mem_cg (pv := (p, g (x - 1))) H.hS (g (x - 2)) (hI.gl hP)
    have hFi : packV T (a - 1) (n + 2) q (x + mv r.d) (upd g x r.t) (x - a) = .pl (g (x - 2)) := by
      rw [hFl _ (by omega) (by omega), show a + (x - a) - 2 = x - 2 by omega]
    have s0 := mix_step_R (M := conv T b ss qm Rl Gl) (σ := (.c (g (x - 2))))
      (σ' := (.g p (g (x - 1))))
      (packV T (a - 1) (n + 2) q (x + mv r.d) (upd g x r.t)) (packV T a n p x g)
      hρ0 hO hFi
    have g0 := good_mix (P := P) (σ := (.g p (g (x - 1)))) (i := x - a + 1)
      (packV T (a - 1) (n + 2) q (x + mv r.d) (upd g x r.t)) (packV T a n p x g)
      (by rw [hOi1]; exact H.good_g (p, g (x - 1)) (hI.gl hP) _)
    rcases mv_cases H hr with ⟨hd, hm⟩ | ⟨hd, hm⟩
    · -- Q₊ のヘッド、左へ: [g p v, pl u, mk q v, +, c t]
      have hQ : isPlus T q = false := H.hLm r hr q hq hd
      have hρ : (⟨.g p (g (x - 1)), .pl (g x), .mk q (g (x - 1)), .R, .go (.c r.t)⟩ :
          Rule (VSt Q S) P (VSym Q S)) ∈ conv T b ss qm Rl Gl :=
        mem_headG (pv := (p, g (x - 1))) H.hS (hI.gl hP) (g x) (by rw [hlook]; simp [headG, hq, hd])
      have hFi1 : packV T (a - 1) (n + 2) q (x + mv r.d) (upd g x r.t) (x - a + 1) = .mk q (g (x - 1)) := by
        rw [packV_mk (by omega) (by push_cast; omega) (by rw [mpos_minus hQ, hm]; omega), mark_minus hQ,
          upd_ne _ _ (by omega), show a - 1 + (x - a + 1) - 1 = x - 1 by omega]
      have s1 := mix_step_R (M := conv T b ss qm Rl Gl) (σ := (.g p (g (x - 1))))
        (σ' := (.c (upd g x r.t (a + (x - a + 1 + 1) - 2))))
        (packV T (a - 1) (n + 2) q (x + mv r.d) (upd g x r.t)) (packV T a n p x g)
        (by rw [show a + (x - a + 1 + 1) - 2 = x by omega, upd_eq]; exact hρ) hOi1 hFi1
      obtain ⟨k, hk⟩ := suffix (b := b) (Rl := Rl) H (upd g x r.t) (packV T a n p x g) _ (packV_mem H hI) (x - a + 1 + 1)
        (by omega) (by omega)
        (fun j h1 h2 => ⟨hOr j (by omega) (by omega) (by omega),
          hFr j (by omega) (by omega) (by rw [mpos_minus hQ, hm]; omega)⟩)
        hOout hFn1 hFn2 hFout hFsym
      have := hpre.trans (GRun.cons s0 g0 (GRun.cons s1 (good_c' H _ _ _ _ (packV_mem H hI _)) hk))
      exact ⟨_, by rw [show 1 + (x - a - 1).toNat + (k + 1 + 1 + 1) =
        (1 + (x - a - 1).toNat + k + 2) + 1 by omega] at this; exact this⟩
    · -- Q₊ のヘッド、右へ: [g p v, pl u, pl v, +, r q t] → [r q t, pl x, mkp q t, +, c x]
      have hQ : isPlus T q = true := isPlus_of hr hq hd
      have hρ1 : (⟨.g p (g (x - 1)), .pl (g x), .pl (g (x - 1)), .R, .go (.r q r.t)⟩ :
          Rule (VSt Q S) P (VSym Q S)) ∈ conv T b ss qm Rl Gl :=
        mem_headG (pv := (p, g (x - 1))) H.hS (hI.gl hP) (g x) (by rw [hlook]; simp [headG, hq, hd])
      have hρ2 : (⟨.r q r.t, .pl (g (x + 1)), .mkp q r.t, .R, .go (.c (g (x + 1)))⟩ :
          Rule (VSt Q S) P (VSym Q S)) ∈ conv T b ss qm Rl Gl :=
        mem_r (pv := (q, r.t)) H.hS (H.hR r hr q hq hd) (g (x + 1))
      have hFi1 : packV T (a - 1) (n + 2) q (x + mv r.d) (upd g x r.t) (x - a + 1) = .pl (g (x - 1)) := by
        rw [hFl _ (by omega) (by rw [mpos_plus hQ, hm]; omega), show a + (x - a + 1) - 2 = x - 1 by omega]
      have hFi2 : packV T (a - 1) (n + 2) q (x + mv r.d) (upd g x r.t) (x - a + 1 + 1) = .mkp q r.t := by
        rw [packV_mk (by omega) (by push_cast; omega) (by rw [mpos_plus hQ, hm]; omega), mark_plus hQ,
          show a - 1 + (x - a + 1 + 1) - 1 = x by omega, upd_eq]
      have hOi2 : packV T a n p x g (x - a + 1 + 1) = .pl (g (x + 1)) := by
        rw [packV_pl (by omega) (by omega) (by omega), show a + (x - a + 1 + 1) - 1 = x + 1 by omega]
      have s1 := mix_step_R (M := conv T b ss qm Rl Gl) (σ := (.g p (g (x - 1))))
        (σ' := (.r q r.t))
        (packV T (a - 1) (n + 2) q (x + mv r.d) (upd g x r.t)) (packV T a n p x g)
        hρ1 hOi1 hFi1
      have g1 := good_mix (P := P) (σ := (.r q r.t)) (i := x - a + 1 + 1)
        (packV T (a - 1) (n + 2) q (x + mv r.d) (upd g x r.t)) (packV T a n p x g)
        (by rw [hOi2]; exact H.good_r (q, r.t) (H.hR r hr q hq hd) _)
      have s2 := mix_step_R (M := conv T b ss qm Rl Gl) (σ := (.r q r.t))
        (σ' := (.c (upd g x r.t (a + (x - a + 1 + 1 + 1) - 2))))
        (packV T (a - 1) (n + 2) q (x + mv r.d) (upd g x r.t)) (packV T a n p x g)
        (by rw [show a + (x - a + 1 + 1 + 1) - 2 = x + 1 by omega, upd_ne _ _ (by omega)]; exact hρ2) hOi2 hFi2
      obtain ⟨k, hk⟩ := suffix (b := b) (Rl := Rl) H (upd g x r.t) (packV T a n p x g) _ (packV_mem H hI) (x - a + 1 + 1 + 1)
        (by omega) (by omega)
        (fun j h1 h2 => ⟨hOr j (by omega) (by omega) (by omega),
          hFr j (by omega) (by omega) (by rw [mpos_plus hQ, hm]; omega)⟩)
        hOout hFn1 hFn2 hFout hFsym
      have := hpre.trans (GRun.cons s0 g0 (GRun.cons s1 g1 (GRun.cons s2 (good_c' H _ _ _ _ (packV_mem H hI _)) hk)))
      exact ⟨_, by rw [show 1 + (x - a - 1).toNat + (k + 1 + 1 + 1 + 1) =
        (1 + (x - a - 1).toNat + k + 3) + 1 by omega] at this; exact this⟩

end Step

/-! ## 5. 規則の分類と停止 -/

section Spec
variable {T : Machine Q P S} {b : S} {ss : List S} {qm : List Q} {Rl Gl : List (Q × S)}

theorem mem_conv {ρ : Rule (VSt Q S) P (VSym Q S)} (h : ρ ∈ conv T b ss qm Rl Gl) :
    ρ = ⟨.L, .bl, .bl, .R, .go (.c b)⟩ ∨
    (∃ x ∈ allSyms ss qm Gl, ρ = ⟨.L, x, x, .L, .go .L⟩) ∨
    (∃ s x, ρ = ⟨.c s, .pl x, .pl s, .R, .go (.c x)⟩) ∨
    (∃ s, ρ = ⟨.c s, .bl, .pl s, .R, .go .e1⟩) ∨
    (∃ s p u, p ∈ qm ∧ (look T p u).bind (headC s p u) = some ρ) ∨
    (∃ s pv, pv ∈ Gl ∧ ρ = ⟨.c s, .mkp pv.1 pv.2, .pl s, .R, .go (.g pv.1 pv.2)⟩) ∨
    ρ = ⟨.e1, .bl, .pl b, .R, .go .e2⟩ ∨
    ρ = ⟨.e2, .bl, .bl, .L, .go .L⟩ ∨
    (∃ pv x, pv ∈ Rl ∧ ρ = ⟨.r pv.1 pv.2, .pl x, .mkp pv.1 pv.2, .R, .go (.c x)⟩) ∨
    (∃ pv u, pv ∈ Gl ∧ (look T pv.1 u).bind (headG pv.1 pv.2 u) = some ρ) := by
  unfold conv at h
  simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_cons, List.not_mem_nil,
    List.mem_filterMap, or_false] at h
  rcases h with ((((h | ⟨x, hx, h⟩) | ⟨s, _, h⟩) | (h | h)) | ⟨pv, hpv, x, _, h⟩) | ⟨pv, hpv, u, _, h⟩
  · exact .inl h
  · exact .inr (.inl ⟨x, hx, h.symm⟩)
  · unfold partC at h
    simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false,
      List.mem_flatMap, List.mem_filterMap] at h
    rcases h with ((⟨x, _, h⟩ | h) | ⟨p, hp, u, _, h⟩) | ⟨pv, hpv, h⟩
    · exact .inr (.inr (.inl ⟨s, x, h.symm⟩))
    · exact .inr (.inr (.inr (.inl ⟨s, h⟩)))
    · exact .inr (.inr (.inr (.inr (.inl ⟨s, p, u, hp, h⟩))))
    · exact .inr (.inr (.inr (.inr (.inr (.inl ⟨s, pv, hpv, h.symm⟩)))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inl h))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl h)))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨pv, x, hpv, h.symm⟩))))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr ⟨pv, u, hpv, h⟩))))))))

theorem headC_spec {s : S} {p : Q} {u : S} {ρ : Rule (VSt Q S) P (VSym Q S)}
    (h : (look T p u).bind (headC s p u) = some ρ) :
    ∃ r, look T p u = some r ∧ ∃ q, r.q = .go q ∧
      ((r.d = .L ∧ ρ = ⟨.c s, .mk p u, .mk q s, .R, .go (.c r.t)⟩) ∨
       (r.d ≠ .L ∧ ρ = ⟨.c s, .mk p u, .pl s, .R, .go (.r q r.t)⟩)) := by
  cases hl : look T p u with
  | none => rw [hl] at h; cases h
  | some r =>
    rw [hl] at h
    simp only [Option.bind_some, headC] at h
    cases hq : r.q with
    | halt _ => rw [hq] at h; cases h
    | go q =>
      rw [hq] at h; dsimp only at h
      refine ⟨r, rfl, q, hq, ?_⟩
      by_cases hd : r.d = .L
      · rw [if_pos hd] at h; cases h; exact .inl ⟨hd, rfl⟩
      · rw [if_neg hd] at h; cases h; exact .inr ⟨hd, rfl⟩

theorem headG_spec {p : Q} {v u : S} {ρ : Rule (VSt Q S) P (VSym Q S)}
    (h : (look T p u).bind (headG p v u) = some ρ) :
    ∃ r, look T p u = some r ∧ ∃ q, r.q = .go q ∧
      ((r.d = .L ∧ ρ = ⟨.g p v, .pl u, .mk q v, .R, .go (.c r.t)⟩) ∨
       (r.d ≠ .L ∧ ρ = ⟨.g p v, .pl u, .pl v, .R, .go (.r q r.t)⟩)) := by
  cases hl : look T p u with
  | none => rw [hl] at h; cases h
  | some r =>
    rw [hl] at h
    simp only [Option.bind_some, headG] at h
    cases hq : r.q with
    | halt _ => rw [hq] at h; cases h
    | go q =>
      rw [hq] at h; dsimp only at h
      refine ⟨r, rfl, q, hq, ?_⟩
      by_cases hd : r.d = .L
      · rw [if_pos hd] at h; cases h; exact .inl ⟨hd, rfl⟩
      · rw [if_neg hd] at h; cases h; exact .inr ⟨hd, rfl⟩

/-- W の規則を (状態, 読む記号) から引く。 -/
def wlook (T : Machine Q P S) (b : S) : VSt Q S → VSym Q S → Option (Rule (VSt Q S) P (VSym Q S))
  | .L, .bl => some ⟨.L, .bl, .bl, .R, .go (.c b)⟩
  | .L, x => some ⟨.L, x, x, .L, .go .L⟩
  | .c s, .pl x => some ⟨.c s, .pl x, .pl s, .R, .go (.c x)⟩
  | .c s, .bl => some ⟨.c s, .bl, .pl s, .R, .go .e1⟩
  | .c s, .mk p u => (look T p u).bind (headC s p u)
  | .c s, .mkp p v => some ⟨.c s, .mkp p v, .pl s, .R, .go (.g p v)⟩
  | .e1, .bl => some ⟨.e1, .bl, .pl b, .R, .go .e2⟩
  | .e2, .bl => some ⟨.e2, .bl, .bl, .L, .go .L⟩
  | .r p v, .pl x => some ⟨.r p v, .pl x, .mkp p v, .R, .go (.c x)⟩
  | .g p v, .pl u => (look T p u).bind (headG p v u)
  | _, _ => none

theorem allSyms_ne {x : VSym Q S} (h : x ∈ allSyms ss qm Gl) : x ≠ .bl := by
  simp only [allSyms, List.mem_append, List.mem_map, List.mem_flatMap] at h
  rcases h with (⟨_, _, rfl⟩ | ⟨_, _, _, _, rfl⟩) | ⟨_, _, rfl⟩ <;> nofun

theorem wlook_mem {ρ : Rule (VSt Q S) P (VSym Q S)} (h : ρ ∈ conv T b ss qm Rl Gl) :
    wlook T b ρ.p ρ.s = some ρ := by
  rcases mem_conv h with rfl | ⟨x, hx, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, rfl⟩ | ⟨s, p, u, _, e⟩ | ⟨_, _, _, rfl⟩ |
    rfl | rfl | ⟨_, _, _, rfl⟩ | ⟨pv, u, _, e⟩
  · rfl
  · have := allSyms_ne hx
    cases x with
    | bl => exact absurd rfl this
    | pl _ => rfl
    | mk _ _ => rfl
    | mkp _ _ => rfl
  · rfl
  · rfl
  · obtain ⟨r, _, q, _, hc⟩ := headC_spec e
    rcases hc with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> exact e
  · rfl
  · rfl
  · rfl
  · rfl
  · obtain ⟨r, _, q, _, hc⟩ := headG_spec e
    rcases hc with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> exact e

/-- `wlook` が引けない (状態, 記号) の配置では W は止まっている。 -/
theorem halted_of_wlook {q : VSt Q S} {i : Int} {t : Int → VSym Q S} (h : wlook T b q (t i) = none) :
    Halted (conv T b ss qm Rl Gl) ({ st := .go q, pos := i, tape := t } : Cfg (VSt Q S) P (VSym Q S)) := by
  intro c' ⟨ρ, hρ, hst, hs, _⟩
  injection hst with hst
  have := wlook_mem hρ
  rw [← hst, ← hs, h] at this
  cases this

end Spec

section Halt
variable {T : Machine Q P S} {b : S} {ss : List S} {qm : List Q} {Rl Gl : List (Q × S)}
  {good : VSt Q S → VSym Q S → Prop}

theorem good_at (H : Hyp T b ss qm Rl Gl good) {q : VSt Q S} {i : Int} {t : Int → VSym Q S}
    (h : good q (t i)) : Good good ({ st := .go q, pos := i, tape := t } : Cfg (VSt Q S) P (VSym Q S)) := by
  intro q' hq'; cases hq'; exact h

/-- **T が止まる配置では W も止まる**: 掃引がヘッドまで進んで止まる（`haltV`）。 -/
theorem halt_sim (H : Hyp T b ss qm Rl Gl good) {a : Int} {n : Nat} {p : Q} {x : Int} {g : Int → S}
    (hI : Inv T b Gl a n p x g) (hh : look T p (g x) = none) :
    ∃ k, GRun (conv T b ss qm Rl Gl) (Good good) k (encV T a n p x g) (haltV T a n p x g) ∧
      Halted (conv T b ss qm Rl Gl) (haltV T a n p x g) := by
  have hlo := hI.lo; have hhi := hI.hi
  have hF0 : ∀ j : Int, j < 1 → packV T (a - 1) n p x g j = .bl := fun j h => packV_out (by omega)
  cases hP : isPlus T p with
  | false =>
    have hmp : mpos T p x = x := mpos_minus hP x
    have hpre := prefix_ (b := b) (Rl := Rl) H hI (packV T (a - 1) n p x g) hF0 (x - a + 1) (by omega) (by omega)
      (fun j h1 h2 => by
        rw [packV_pl h1 (by omega) (by omega), show a - 1 + j - 1 = a + j - 2 by omega])
    rw [show a + (x - a + 1) - 2 = x - 1 by omega] at hpre
    have hE : haltV T a n p x g =
        { st := .go (.c (g (x - 1))), pos := x - a + 1,
          tape := mix (x - a + 1) (packV T (a - 1) n p x g) (packV T a n p x g) } := by
      simp [haltV, hP]
    refine ⟨_, hE ▸ hpre, hE ▸ halted_of_wlook ?_⟩
    rw [mix_ge (Int.le_refl _), packV_mk (by omega) (by omega) (by omega), mark_minus hP,
      show a + (x - a + 1) - 1 = x by omega]
    simp [wlook, hh]
  | true =>
    have hmp : mpos T p x = x - 1 := mpos_plus hP x
    have hpre := prefix_ (b := b) (Rl := Rl) H hI (packV T (a - 1) n p x g) hF0 (x - a) (by omega) (by omega)
      (fun j h1 h2 => by
        rw [packV_pl h1 (by omega) (by omega), show a - 1 + j - 1 = a + j - 2 by omega])
    rw [show a + (x - a) - 2 = x - 2 by omega] at hpre
    have hO : packV T a n p x g (x - a) = .mkp p (g (x - 1)) := by
      rw [packV_mk (by omega) (by omega) (by omega), mark_plus hP, show a + (x - a) - 1 = x - 1 by omega]
    have hOi1 : packV T a n p x g (x - a + 1) = .pl (g x) := by
      rw [packV_pl (by omega) (by omega) (by omega), show a + (x - a + 1) - 1 = x by omega]
    have hFi : packV T (a - 1) n p x g (x - a) = .pl (g (x - 2)) := by
      rw [packV_pl (by omega) (by omega) (by omega), show a - 1 + (x - a) - 1 = x - 2 by omega]
    have hE : haltV T a n p x g =
        { st := .go (.g p (g (x - 1))), pos := x - a + 1,
          tape := mix (x - a + 1) (packV T (a - 1) n p x g) (packV T a n p x g) } := by
      simp [haltV, hP]
    have s0 : Step (conv T b ss qm Rl Gl)
        { st := .go (.c (g (x - 2))), pos := x - a,
          tape := mix (x - a) (packV T (a - 1) n p x g) (packV T a n p x g) }
        { st := .go (.g p (g (x - 1))), pos := x - a + 1,
          tape := mix (x - a + 1) (packV T (a - 1) n p x g) (packV T a n p x g) } := by
      refine ⟨_, mem_cg (pv := (p, g (x - 1))) H.hS (g (x - 2)) (hI.gl hP), rfl, ?_, ?_⟩
      · simp only; rw [mix_ge (Int.le_refl _), hO]
      · simp only [fire, mv_R]; rw [← hFi, mix_step]
    refine ⟨_, hE ▸ hpre.trans (GRun.single s0 (good_at H (by
      rw [mix_ge (Int.le_refl _), hOi1]; exact H.good_g (p, g (x - 1)) (hI.gl hP) _))),
      hE ▸ halted_of_wlook ?_⟩
    rw [mix_ge (Int.le_refl _), hOi1]
    simp [wlook, hh]

end Halt

/-! ## 6. 計算過程の模倣 -/

section Run
variable {T : Machine Q P S} {b : S} {ss : List S} {qm : List Q} {Rl Gl : List (Q × S)}
  {good : VSt Q S → VSym Q S → Prop}

/-- T の配置 c を、N 回掃いた後の W の配置に（始まり a0 − N、長さ n0 + 2N）。 -/
def Wc (T : Machine Q P S) (a0 : Int) (n0 : Nat) (N : Nat) (c : Cfg Q P S) : Cfg (VSt Q S) P (VSym Q S) :=
  match c.st with
  | .go p => encV T (a0 - N) (n0 + 2 * N) p c.pos c.tape
  | .halt h => { st := .halt h, pos := 0, tape := fun _ => .bl }

/-- T が N ステップで止まった配置 e に対応する W の停止配置。 -/
def Ev (T : Machine Q P S) (a0 : Int) (n0 : Nat) (N : Nat) (e : Cfg Q P S) : Cfg (VSt Q S) P (VSym Q S) :=
  match e.st with
  | .go p => haltV T (a0 - N) (n0 + 2 * N) p e.pos e.tape
  | .halt h => { st := .halt h, pos := 0, tape := fun _ => .bl }

/-- **計算過程の模倣**: T が c0 から N ステップで c に達するなら、W は Wc 0 c0 から N ステップ以上で Wc N c に
    達し（各ステップの行き先は good を満たす）、不変量も保たれる。 -/
theorem run_sim (H : Hyp T b ss qm Rl Gl good) {a0 : Int} {n0 : Nat} {c0 : Cfg Q P S} {p0 : Q}
    (hc0 : c0.st = .go p0) (hI : Inv T b Gl a0 n0 p0 c0.pos c0.tape) :
    ∀ N {c : Cfg Q P S}, StepN T N c0 c →
      (∃ p, c.st = .go p ∧ Inv T b Gl (a0 - N) (n0 + 2 * N) p c.pos c.tape) ∧
      ∃ M, N ≤ M ∧ GRun (conv T b ss qm Rl Gl) (Good good) M (Wc T a0 n0 0 c0) (Wc T a0 n0 N c) := by
  intro N
  induction N with
  | zero =>
    intro c h
    cases h
    exact ⟨⟨p0, hc0, by simpa using hI⟩, 0, Nat.le_refl _, .refl _⟩
  | succ N ih =>
    intro c h
    obtain ⟨c₁, h₁, r, hr, hst, hs, rfl⟩ := StepN.last h
    obtain ⟨⟨p₁, hp₁, hI₁⟩, M₁, hM₁, hrun⟩ := ih h₁
    obtain ⟨q, hq⟩ : ∃ q, r.q = .go q := by
      have := (H.hG r hr).1
      cases hq : r.q with
      | go q => exact ⟨q, rfl⟩
      | halt _ => rw [hq] at this; cases this
    have hr' : r.p = p₁ := by rw [hp₁] at hst; injection hst with h; exact h.symm
    have hI' := inv_step H hI₁ hr hq
    obtain ⟨k, hk⟩ := step_sim H hI₁ hr hr' hs hq
    have hW : Wc T a0 n0 N c₁ = encV T (a0 - N) (n0 + 2 * N) p₁ c₁.pos c₁.tape := by simp [Wc, hp₁]
    have hW' : Wc T a0 n0 (N + 1) (fire r c₁) =
        encV T (a0 - N - 1) (n0 + 2 * N + 2) q (c₁.pos + mv r.d) (upd c₁.tape c₁.pos r.t) := by
      simp only [Wc, fire, hq]
      rw [show a0 - ((N + 1 : Nat) : Int) = a0 - (N : Int) - 1 by push_cast; omega,
        show n0 + 2 * (N + 1) = n0 + 2 * N + 2 by omega]
    refine ⟨⟨q, by simp [fire, hq], ?_⟩, M₁ + (k + 1), by omega, ?_⟩
    · simp only [fire]
      rw [show a0 - ((N + 1 : Nat) : Int) = a0 - (N : Int) - 1 by push_cast; omega,
        show n0 + 2 * (N + 1) = n0 + 2 * N + 2 by omega]
      exact hI'
    · rw [hW] at hrun; rw [hW']; exact hrun.trans hk

theorem look_none_of_halted (H : Hyp T b ss qm Rl Gl good) {e : Cfg Q P S} {p : Q} (hp : e.st = .go p)
    (hh : Halted T e) : look T p (e.tape e.pos) = none := by
  cases hl : look T p (e.tape e.pos) with
  | none => rfl
  | some r =>
    obtain ⟨hr, hrp, hrs⟩ := look_some hl
    exact (hh (fire r e) ⟨r, hr, by rw [hp, hrp], hrs.symm, rfl⟩).elim

/-- **T が N ステップで止まるなら W も止まり、停止配置は Ev N e**。 -/
theorem halts_sim (H : Hyp T b ss qm Rl Gl good) {a0 : Int} {n0 : Nat} {c0 : Cfg Q P S} {p0 : Q}
    (hc0 : c0.st = .go p0) (hI : Inv T b Gl a0 n0 p0 c0.pos c0.tape) {N : Nat} {e : Cfg Q P S}
    (h : HaltsIn T N c0 e) :
    ∃ M, N ≤ M ∧ GRun (conv T b ss qm Rl Gl) (Good good) M (Wc T a0 n0 0 c0) (Ev T a0 n0 N e) ∧
      Halted (conv T b ss qm Rl Gl) (Ev T a0 n0 N e) := by
  obtain ⟨⟨p, hp, hIe⟩, M, hM, hrun⟩ := run_sim H hc0 hI N h.1
  obtain ⟨k, hk, hH⟩ := halt_sim H hIe (look_none_of_halted H hp h.2)
  have hW : Wc T a0 n0 N e = encV T (a0 - N) (n0 + 2 * N) p e.pos e.tape := by simp [Wc, hp]
  have hE : Ev T a0 n0 N e = haltV T (a0 - N) (n0 + 2 * N) p e.pos e.tape := by simp [Ev, hp]
  rw [hW] at hrun
  exact ⟨M + k, by omega, hE ▸ hrun.trans hk, hE ▸ hH⟩

end Run

/-! ## 7. 決定性と可逆性の保存 -/

section DetRev
variable {T : Machine Q P S} {b : S} {ss : List S} {qm : List Q} {Rl Gl : List (Q × S)}

/-- **決定性**: W は（T に何の仮定も置かずに）決定的（T の規則は `look` で 1 本に決めて引くので）。 -/
theorem conv_det : Deterministic (conv T b ss qm Rl Gl) := by
  intro ρ₁ h₁ ρ₂ h₂ hne hp hs
  have e₁ := wlook_mem h₁
  rw [hp, hs, wlook_mem h₂] at e₁
  exact hne (Option.some.inj e₁).symm

/-- 行き先と書込記号が T の規則 r を決める（可逆性の検索）。 -/
def lookB (T : Machine Q P S) (q : Q) (t : S) : Option (Rule Q P S) :=
  T.find? (fun r => (match r.q with
    | .go q' => q' == q
    | .halt _ => false) && r.t == t)

theorem lookB_of (hR : Reversible T) {r : Rule Q P S} (hr : r ∈ T) {q : Q} (hq : r.q = .go q) :
    lookB T q r.t = some r := by
  cases h : lookB T q r.t with
  | none =>
    have := List.find?_eq_none.mp h r hr
    simp [hq] at this
  | some r' =>
    have hr' := List.mem_of_find?_eq_some h
    have hp := List.find?_some h
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    obtain ⟨hq', ht⟩ := hp
    have hq'' : r'.q = .go q := by
      revert hq'; cases r'.q <;> simp_all
    by_cases e : r' = r
    · rw [e]
    · exact absurd ht ((hR r' hr' r hr e (by rw [hq'', hq])).2)

/-- W の規則を (行き先, 書込記号) から引く。 -/
def wback (T : Machine Q P S) (b : S) : Tgt (VSt Q S) P → VSym Q S → Option (Rule (VSt Q S) P (VSym Q S))
  | .go .L, .bl => some ⟨.e2, .bl, .bl, .L, .go .L⟩
  | .go .L, x => some ⟨.L, x, x, .L, .go .L⟩
  | .go (.c x), .bl => if x = b then some ⟨.L, .bl, .bl, .R, .go (.c b)⟩ else none
  | .go (.c x), .pl s => some ⟨.c s, .pl x, .pl s, .R, .go (.c x)⟩
  | .go (.c x), .mk q s => (lookB T q x).bind (fun r =>
      if isPlus T r.p then some ⟨.g r.p s, .pl r.s, .mk q s, .R, .go (.c x)⟩
      else some ⟨.c s, .mk r.p r.s, .mk q s, .R, .go (.c x)⟩)
  | .go (.c x), .mkp p v => some ⟨.r p v, .pl x, .mkp p v, .R, .go (.c x)⟩
  | .go .e1, .pl s => some ⟨.c s, .bl, .pl s, .R, .go .e1⟩
  | .go .e2, .pl t => if t = b then some ⟨.e1, .bl, .pl b, .R, .go .e2⟩ else none
  | .go (.r q t), .pl s => (lookB T q t).bind (fun r =>
      if isPlus T r.p then some ⟨.g r.p s, .pl r.s, .pl s, .R, .go (.r q t)⟩
      else some ⟨.c s, .mk r.p r.s, .pl s, .R, .go (.r q t)⟩)
  | .go (.g p v), .pl s => some ⟨.c s, .mkp p v, .pl s, .R, .go (.g p v)⟩
  | _, _ => none

/-- 可逆性に使う仮定: T は可逆・決定的、qm は Q₋ の状態だけ、Gl は Q₊ の状態だけ。 -/
structure RevHyp (T : Machine Q P S) (qm : List Q) (Gl : List (Q × S)) : Prop where
  hR : Reversible T
  hD : Deterministic T
  hqm : ∀ p ∈ qm, isPlus T p = false
  hGl : ∀ pv ∈ Gl, isPlus T pv.1 = true

theorem wback_mem (RH : RevHyp T qm Gl) {ρ : Rule (VSt Q S) P (VSym Q S)} (h : ρ ∈ conv T b ss qm Rl Gl) :
    wback T b ρ.q ρ.t = some ρ := by
  rcases mem_conv h with rfl | ⟨x, hx, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, rfl⟩ | ⟨s, p, u, hp, e⟩ | ⟨_, _, _, rfl⟩ |
    rfl | rfl | ⟨_, _, _, rfl⟩ | ⟨pv, u, hpv, e⟩
  · simp [wback]
  · have := allSyms_ne hx
    cases x with
    | bl => exact absurd rfl this
    | pl _ => rfl
    | mk _ _ => rfl
    | mkp _ _ => rfl
  · rfl
  · rfl
  · obtain ⟨r, hl, q, hq, hc⟩ := headC_spec e
    obtain ⟨hr, hrp, hrs⟩ := look_some hl
    have hb := lookB_of RH.hR hr hq
    have hm := RH.hqm p hp
    rcases hc with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · simp only [wback, hb, Option.bind_some, hrp, hrs, hm]; rfl
    · simp only [wback, hb, Option.bind_some, hrp, hrs, hm]; rfl
  · rfl
  · simp [wback]
  · rfl
  · rfl
  · obtain ⟨r, hl, q, hq, hc⟩ := headG_spec e
    obtain ⟨hr, hrp, hrs⟩ := look_some hl
    have hb := lookB_of RH.hR hr hq
    have hm := RH.hGl pv hpv
    rcases hc with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · simp only [wback, hb, Option.bind_some, hrp, hrs, hm, if_true]
    · simp only [wback, hb, Option.bind_some, hrp, hrs, hm, if_true]

/-- 行き先から決まる方向（q_L へは左、それ以外は右）。 -/
def dirOf : Tgt (VSt Q S) P → Dir
  | .go .L => .L
  | _ => .R

/-- 左移動の規則はちょうど q_L へ入る規則。 -/
theorem dir_mem {ρ : Rule (VSt Q S) P (VSym Q S)} (h : ρ ∈ conv T b ss qm Rl Gl) :
    ρ.d = dirOf ρ.q := by
  rcases mem_conv h with rfl | ⟨x, hx, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, rfl⟩ | ⟨s, p, u, hp, e⟩ | ⟨_, _, _, rfl⟩ |
    rfl | rfl | ⟨_, _, _, rfl⟩ | ⟨pv, u, hpv, e⟩ <;> try rfl
  · obtain ⟨r, _, q, _, hc⟩ := headC_spec e
    rcases hc with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl
  · obtain ⟨r, _, q, _, hc⟩ := headG_spec e
    rcases hc with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl

/-- **可逆性の保存**: T が可逆・決定的で、qm が Q₋ の状態だけ、Gl が Q₊ の状態だけなら W も可逆。 -/
theorem conv_rev (RH : RevHyp T qm Gl) : Reversible (conv T b ss qm Rl Gl) := by
  intro ρ₁ h₁ ρ₂ h₂ hne hq
  refine ⟨by rw [dir_mem h₁, dir_mem h₂, hq], fun ht => hne ?_⟩
  have e₁ := wback_mem (b := b) RH h₁
  rw [hq, ht, wback_mem RH h₂] at e₁
  exact (Option.some.inj e₁).symm

end DetRev

end URTM.Conv1W
