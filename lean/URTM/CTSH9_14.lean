/-
  URTM(9,14) が任意の CTSH を模倣することの一般証明（2026-10-31）。

  機械 `T9` と表現 `rep9`・`finCfg9` は CTSH9_14Defs.lean。証明は CTSH10_8.lean（親 (10,8)）と同じ組み立てで、
  各掃引の書換えにタグの付け外しが加わる。掃引は 9 種類で、どれも記号ごとに一様（`g*` の写像）:

  | 状態（親の役） | 向き | 通る記号 → 書く記号 |
  |---|---|---|
  | q1（case_y_1） | 左 | Y, N → そのまま、$ → $′ |
  | q2（case_y_2） | 右 | $′ → $、Y, N → そのまま |
  | q3（case_y_n） | 左 | Y, N → Y′, N′、$ → $、∗′ → ∗ |
  | q5（copy_y_1） | 右 | $ → $′、他（∗, Y′, N′, y, n）はそのまま |
  | q1（copy_y_2） | 左 | $′ → $、他はそのまま |
  | q7（copy_n_1） | 右 | $ → $′、∗ → ∗′、Y′, N′ → Y, N、y, n はそのまま |
  | q8（copy_n_2） | 左 | 上の逆 |
  | q9（copy_end） | 右 | $ → $、∗ → ∗′、Y′, N′ → Y, N |
  | q0（begin、周の終わり） | 右 | Y′, N′ → y, n、∗ → ∗ |

  未証明の穴・新規公理・native_decide を使わない。
-/
import URTM.CTSH9_14Defs

set_option maxRecDepth 100000

namespace URTM.CTSH.U9_14

open URTM URTM.KState URTM.CTSH URTM.CTSH.Sim URTM.Gen.K10_8
open URTM.CTSH.U10_8 (up hd)

/-! ## 1. 記号の写像と、規則表からの通過の補題 -/

/-- タグ付き。 -/
def G (X : List Sy) : List TS := X.map (·, true)

/-- copy の相の `Lo`: 大文字にタグ、∗ にタグ無し。 -/
def tagUp (x : Sy) : TS := (x, x != .s6)

def cM1 (x : TS) : Bool := x == (.s4, false) || x == (.s5, false) || x == (.s7, false)
def gM1 (x : TS) : TS := if x = (.s7, false) then (.s7, true) else x

def cC2 (x : TS) : Bool := x == (.s4, false) || x == (.s5, false) || x == (.s7, true)
def gC2 (x : TS) : TS := if x = (.s7, true) then (.s7, false) else x

def cN3 (x : TS) : Bool :=
  x == (.s4, false) || x == (.s5, false) || x == (.s7, false) || x == (.s6, true)
def gN3 : TS → TS
  | (.s4, false) => (.s4, true)
  | (.s5, false) => (.s5, true)
  | (.s6, true) => (.s6, false)
  | x => x

/-- copy の掃引が通る記号（∗, $, Y′, N′, y, n。タグは往路と復路で付け外し）。 -/
def cCp (x : TS) : Bool :=
  x == (.s6, false) || x == (.s7, false) || x == (.s4, true) || x == (.s5, true) ||
  x == (.s1, false) || x == (.s2, false)
def gY5 (x : TS) : TS := if x = (.s7, false) then (.s7, true) else x
def cY6 (x : TS) : Bool :=
  x == (.s6, false) || x == (.s7, true) || x == (.s4, true) || x == (.s5, true) ||
  x == (.s1, false) || x == (.s2, false)
def gY6 (x : TS) : TS := if x = (.s7, true) then (.s7, false) else x

def gN7 : TS → TS
  | (.s7, false) => (.s7, true)
  | (.s6, false) => (.s6, true)
  | (.s4, true) => (.s4, false)
  | (.s5, true) => (.s5, false)
  | x => x
def cN8 (x : TS) : Bool :=
  x == (.s6, true) || x == (.s7, true) || x == (.s4, false) || x == (.s5, false) ||
  x == (.s1, false) || x == (.s2, false)
def gN8 : TS → TS
  | (.s7, true) => (.s7, false)
  | (.s6, true) => (.s6, false)
  | (.s4, false) => (.s4, true)
  | (.s5, false) => (.s5, true)
  | x => x

def cE9 (x : TS) : Bool :=
  x == (.s7, false) || x == (.s6, false) || x == (.s4, true) || x == (.s5, true)
def gE9 : TS → TS
  | (.s6, false) => (.s6, true)
  | (.s4, true) => (.s4, false)
  | (.s5, true) => (.s5, false)
  | x => x

def cB0 (x : TS) : Bool := x == (.s4, true) || x == (.s5, true) || x == (.s6, false)
def gB0 : TS → TS
  | (.s4, true) => (.s1, false)
  | (.s5, true) => (.s2, false)
  | x => x

theorem ofAll {c : TS → Bool} {P : TS → Prop} (hp : ∀ x, c x = true → P x) {X : List TS}
    (h : X.all c = true) : ∀ x ∈ X, P x :=
  fun x hx => hp x (List.all_eq_true.mp h x hx)

theorem p_M1 : ∀ x, cM1 x = true → (⟨.q1, x, gM1 x, .L, .go .q1⟩ : Rule St Ps TS) ∈ T9 := by
  intro ⟨s, b⟩; cases s <;> cases b <;> decide
theorem p_C2 : ∀ x, cC2 x = true → (⟨.q2, x, gC2 x, .R, .go .q2⟩ : Rule St Ps TS) ∈ T9 := by
  intro ⟨s, b⟩; cases s <;> cases b <;> decide
theorem p_N3 : ∀ x, cN3 x = true → (⟨.q3, x, gN3 x, .L, .go .q3⟩ : Rule St Ps TS) ∈ T9 := by
  intro ⟨s, b⟩; cases s <;> cases b <;> decide
theorem p_Y5 : ∀ x, cCp x = true → (⟨.q5, x, gY5 x, .R, .go .q5⟩ : Rule St Ps TS) ∈ T9 := by
  intro ⟨s, b⟩; cases s <;> cases b <;> decide
theorem p_Y6 : ∀ x, cY6 x = true → (⟨.q1, x, gY6 x, .L, .go .q1⟩ : Rule St Ps TS) ∈ T9 := by
  intro ⟨s, b⟩; cases s <;> cases b <;> decide
theorem p_N7 : ∀ x, cCp x = true → (⟨.q7, x, gN7 x, .R, .go .q7⟩ : Rule St Ps TS) ∈ T9 := by
  intro ⟨s, b⟩; cases s <;> cases b <;> decide
theorem p_N8 : ∀ x, cN8 x = true → (⟨.q8, x, gN8 x, .L, .go .q8⟩ : Rule St Ps TS) ∈ T9 := by
  intro ⟨s, b⟩; cases s <;> cases b <;> decide
theorem p_E9 : ∀ x, cE9 x = true → (⟨.q9, x, gE9 x, .R, .go .q9⟩ : Rule St Ps TS) ∈ T9 := by
  intro ⟨s, b⟩; cases s <;> cases b <;> decide
theorem p_B0 : ∀ x, cB0 x = true → (⟨.q0, x, gB0 x, .R, .go .q0⟩ : Rule St Ps TS) ∈ T9 := by
  intro ⟨s, b⟩; cases s <;> cases b <;> decide

/-- 往路と復路の合成は恒等（copy の 2 つの掃引）。 -/
theorem gY6_gY5 : ∀ x, cCp x = true → gY6 (gY5 x) = x := by
  intro ⟨s, b⟩; cases s <;> cases b <;> decide
theorem cY6_gY5 : ∀ x, cCp x = true → cY6 (gY5 x) = true := by
  intro ⟨s, b⟩; cases s <;> cases b <;> decide
theorem gN8_gN7 : ∀ x, cCp x = true → gN8 (gN7 x) = x := by
  intro ⟨s, b⟩; cases s <;> cases b <;> decide
theorem cN8_gN7 : ∀ x, cCp x = true → cN8 (gN7 x) = true := by
  intro ⟨s, b⟩; cases s <;> cases b <;> decide

/-! ## 2. 記号列の補題 -/

theorem all_un (f : TS → Bool) {X : List Sy} (h : ∀ x ∈ X, f (x, false) = true) :
    (un X).all f = true := by
  simp only [un, List.all_map, List.all_eq_true, Function.comp]; exact h
theorem all_G (f : TS → Bool) {X : List Sy} (h : ∀ x ∈ X, f (x, true) = true) :
    (G X).all f = true := by
  simp only [G, List.all_map, List.all_eq_true, Function.comp]; exact h

theorem up_mem {c : Ch} : up c = .s4 ∨ up c = .s5 := by cases c <;> simp [up]
theorem lo_mem {c : Ch} : lo c = .s1 ∨ lo c = .s2 := by cases c <;> simp [lo, U10_8.lo]

theorem mem_up {x : Sy} {u : List Ch} (h : x ∈ u.map up) : x = .s4 ∨ x = .s5 := by
  obtain ⟨c, _, rfl⟩ := List.mem_map.mp h; exact up_mem
theorem mem_lo {x : Sy} {u : List Ch} (h : x ∈ u.map lo) : x = .s1 ∨ x = .s2 := by
  obtain ⟨c, _, rfl⟩ := List.mem_map.mp h; exact lo_mem

theorem mem_LoCore {C : CTSH} {m : Nat} {x : Sy} (h : x ∈ U10_8.LoCore C m) :
    x = .s4 ∨ x = .s5 ∨ x = .s6 := by
  simp only [U10_8.LoCore, Sim.LoCore, List.mem_flatten, List.mem_map] at h
  obtain ⟨_, ⟨w, _, rfl⟩, hx⟩ := h
  simp only [List.mem_append, List.mem_singleton] at hx
  rcases hx with hx | hx
  · rw [List.map_reverse] at hx
    rcases mem_up (List.mem_reverse.mp hx) with h | h <;> simp [h]
  · simp [hx]

theorem mem_Lo {C : CTSH} {m : Nat} {x : Sy} (h : x ∈ U10_8.Lo C m) : x = .s4 ∨ x = .s5 ∨ x = .s6 := by
  unfold U10_8.Lo Sim.Lo at h; split at h
  · simp at h
  · simp only [List.mem_append, List.mem_singleton] at h
    rcases h with h | h
    · exact mem_LoCore h
    · simp [h]

theorem map_map_id {f g : TS → TS} {c : TS → Bool} (h : ∀ x, c x = true → g (f x) = x)
    {X : List TS} (hX : X.all c = true) : (X.map f).map g = X := by
  rw [List.map_map]
  refine (List.map_congr_left fun x hx => ?_).trans (List.map_id X)
  simpa using h x (List.all_eq_true.mp hX x hx)

theorem all_map_of {f : TS → TS} {c d : TS → Bool} (h : ∀ x, c x = true → d (f x) = true)
    {X : List TS} (hX : X.all c = true) : (X.map f).all d = true := by
  simp only [List.all_map, List.all_eq_true, Function.comp]
  exact fun x hx => h x (List.all_eq_true.mp hX x hx)

/-! ## 3. 表現と配置 -/

/-- copy の相の `Lo`。 -/
def LoC (C : CTSH) (m : Nat) : List TS := (U10_8.Lo C m).map tagUp

theorem RA9_length (C : CTSH) (m : Nat) : (RA9 C m).length = (U10_8.RA C m).length := by
  simp [RA9, U10_8.RA, un]

theorem rep9_eq (C : CTSH) (m : Nat) (rm v : List Ch) :
    rep9 C m rm v = zr bk (.go .q0) (bk :: RA9 C m ++ (.s7, false) :: un (rm.map up)).reverse
      (un (v.map lo)) := by
  rw [zr_eq]; simp only [rep9, tapeList9, un, List.map_append]
  congr 1
  · simp [RA9_length]; omega
  · simp [List.append_assoc]

/-! ## 4. コピー（copy_start が規則 1 文字を読み、右端まで行って戻る） -/

/-- 先頭が y（書き足す）: 右端の b に lo c を書き、戻って c の位置をタグ付きの大文字に。 -/
theorem copyY_one (c : Ch) {LL : List TS} (hLL : LL ≠ []) {R : List TS}
    (hR : R.all cCp = true) :
    Reach T9 (zc bk (.go .q4) LL (lo c, false) R)
      (zl bk (.go .q4) LL ((up c, true) :: R ++ [(lo c, false)])) := by
  rw [← zc_trail _ _ _ R, ← zl_trail]
  cases c with
  | Y =>
    refine (runRg (T := T9) (p := .q4) (q := .q5) (h := (.s1, false)) (t := (.s0, true)) (by decide) gY5
      (ofAll p_Y5 hR) LL bk []).trans ?_
    rw [zc_nil]
    refine (Reach.step (stepR (T := T9) (p := .q5) (h := bk) (t := (.s1, false)) (q := .go .q2)
      (by decide) _ bk [])).trans ?_
    have hX : ((Sy.s1, false) :: (R.map gY5).reverse).all cY6 = true := by
      simp only [List.all_cons, List.all_reverse]
      rw [all_map_of cY6_gY5 hR]; rfl
    refine (runLg (T := T9) (p := .q2) (q := .q1) (h := bk) (t := bk) (by decide) gY6
      (ofAll p_Y6 hX) (.s0, true) LL []).trans ?_
    refine (Reach.step (stepL' (T := T9) (p := .q1) (h := (.s0, true)) (t := (.s4, true))
      (q := .go .q4) (by decide) hLL _)).trans ?_
    apply Reach.of_eq
    simp only [List.map_cons, List.map_reverse, List.reverse_cons, List.reverse_reverse,
      map_map_id gY6_gY5 hR]
    simp [up, lo, U10_8.lo, gY6]
  | N =>
    refine (runRg (T := T9) (p := .q4) (q := .q7) (h := (.s2, false)) (t := (.s0, true)) (by decide) gN7
      (ofAll p_N7 hR) LL bk []).trans ?_
    rw [zc_nil]
    refine (Reach.step (stepR (T := T9) (p := .q7) (h := bk) (t := (.s2, false)) (q := .go .q9)
      (by decide) _ bk [])).trans ?_
    have hX : ((Sy.s2, false) :: (R.map gN7).reverse).all cN8 = true := by
      simp only [List.all_cons, List.all_reverse]
      rw [all_map_of cN8_gN7 hR]; rfl
    refine (runLg (T := T9) (p := .q9) (q := .q8) (h := bk) (t := bk) (by decide) gN8
      (ofAll p_N8 hX) (.s0, true) LL []).trans ?_
    refine (Reach.step (stepL' (T := T9) (p := .q8) (h := (.s0, true)) (t := (.s5, true))
      (q := .go .q4) (by decide) hLL _)).trans ?_
    apply Reach.of_eq
    simp only [List.map_cons, List.map_reverse, List.reverse_cons, List.reverse_reverse,
      map_map_id gN8_gN7 hR]
    simp [up, lo, U10_8.lo, gN8]

/-- 先頭が n′（書き足さない）: n′ で折り返し、戻って c の位置をタグ付きの大文字に。 -/
theorem copyN_one (c : Ch) {LL : List TS} (hLL : LL ≠ []) {X : List TS}
    (hX : X.all cCp = true) (S : List TS) :
    Reach T9 (zc bk (.go .q4) LL (lo c, false) (X ++ (.s3, false) :: S))
      (zl bk (.go .q4) LL ((up c, true) :: X ++ (.s3, false) :: S)) := by
  cases c with
  | Y =>
    refine (runRg (T := T9) (p := .q4) (q := .q5) (h := (.s1, false)) (t := (.s0, true)) (by decide) gY5
      (ofAll p_Y5 hX) LL (.s3, false) S).trans ?_
    have hX' : (X.map gY5).reverse.all cY6 = true := by
      rw [List.all_reverse]; exact all_map_of cY6_gY5 hX
    refine (runLg (T := T9) (p := .q5) (q := .q1) (h := (.s3, false)) (t := (.s3, false)) (by decide) gY6
      (ofAll p_Y6 hX') (.s0, true) LL S).trans ?_
    refine (Reach.step (stepL' (T := T9) (p := .q1) (h := (.s0, true)) (t := (.s4, true))
      (q := .go .q4) (by decide) hLL _)).trans ?_
    apply Reach.of_eq
    simp only [List.map_reverse, List.reverse_reverse, map_map_id gY6_gY5 hX]
    simp [up]
  | N =>
    refine (runRg (T := T9) (p := .q4) (q := .q7) (h := (.s2, false)) (t := (.s0, true)) (by decide) gN7
      (ofAll p_N7 hX) LL (.s3, false) S).trans ?_
    have hX' : (X.map gN7).reverse.all cN8 = true := by
      rw [List.all_reverse]; exact all_map_of cN8_gN7 hX
    refine (runLg (T := T9) (p := .q7) (q := .q8) (h := (.s3, false)) (t := (.s3, false)) (by decide) gN8
      (ofAll p_N8 hX') (.s0, true) LL S).trans ?_
    refine (Reach.step (stepL' (T := T9) (p := .q8) (h := (.s0, true)) (t := (.s5, true))
      (q := .go .q4) (by decide) hLL _)).trans ?_
    apply Reach.of_eq
    simp only [List.map_reverse, List.reverse_reverse, map_map_id gN8_gN7 hX]
    simp [up]

/-- 規則の文字のタグ無しの並び。 -/
def ul (Q : List Ch) : List TS := Q.map fun c => (lo c, false)
/-- 写し終えた文字のタグ付きの大文字の並び。 -/
def gu (P : List Ch) : List TS := P.map fun c => (up c, true)

theorem all_gu (P : List Ch) : (gu P).all cCp = true := by
  simp only [gu, List.all_map, List.all_eq_true, Function.comp]
  intro c _; cases c <;> rfl
theorem all_ul (P : List Ch) : (ul P).all cCp = true := by
  simp only [ul, List.all_map, List.all_eq_true, Function.comp]
  intro c _; cases c <;> rfl

theorem copyY_loop (Z : List TS) (hZ : Z ≠ []) (Mid : List TS) (hMid : Mid.all cCp = true) :
    ∀ (Q P : List Ch) (S : List TS), S.all cCp = true →
    Reach T9 (zl bk (.go .q4) (ul Q ++ Z) (gu P.reverse ++ (.s6, false) :: Mid ++ (.s1, false) :: S))
      (zl bk (.go .q4) Z (gu (P ++ Q).reverse ++ (.s6, false) :: Mid ++ (.s1, false) :: S ++ ul Q)) := by
  intro Q
  induction Q with
  | nil => intro P S _; exact Reach.of_eq (by simp [ul])
  | cons c Q ih =>
    intro P S hS
    have hR : (gu P.reverse ++ (.s6, false) :: Mid ++ (.s1, false) :: S).all cCp = true := by
      simp only [List.all_append, List.all_cons, all_gu, hMid, hS]; rfl
    have h1 := copyY_one c (LL := ul Q ++ Z) (by simp [hZ]) hR
    have h2 := ih (P ++ [c]) (S ++ [(lo c, false)]) (by simp [hS]; cases c <;> rfl)
    refine h1.trans (Eq.mpr ?_ h2)
    simp [ul, gu]

theorem copyN_loop (Z : List TS) (hZ : Z ≠ []) (Mid : List TS) (hMid : Mid.all cCp = true)
    (S : List TS) :
    ∀ (Q P : List Ch),
    Reach T9 (zl bk (.go .q4) (ul Q ++ Z) (gu P.reverse ++ (.s6, false) :: Mid ++ (.s3, false) :: S))
      (zl bk (.go .q4) Z (gu (P ++ Q).reverse ++ (.s6, false) :: Mid ++ (.s3, false) :: S)) := by
  intro Q
  induction Q with
  | nil => intro P; exact Reach.of_eq (by simp [ul])
  | cons c Q ih =>
    intro P
    have hX : (gu P.reverse ++ (.s6, false) :: Mid).all cCp = true := by
      simp only [List.all_append, List.all_cons, all_gu, hMid]; rfl
    have h1 := copyN_one c (LL := ul Q ++ Z) (by simp [hZ]) hX S
    have h2 := ih (P ++ [c])
    refine h1.trans (Eq.mpr ?_ h2)
    simp [ul, gu]

/-! ## 5. 記号列の写像の計算 -/

theorem un_up_map {f : TS → TS} (h4 : f (.s4, false) = (.s4, false)) (h5 : f (.s5, false) = (.s5, false))
    (u : List Ch) : (un (u.map up)).map f = un (u.map up) := by
  simp only [un, List.map_map]
  exact List.map_congr_left fun c _ => by cases c <;> simp [up, h4, h5]

theorem un_up_gN3 (u : List Ch) : (un (u.map up)).map gN3 = G (u.map up) := by
  simp only [un, G, List.map_map]
  exact List.map_congr_left fun c _ => by cases c <;> rfl

theorem G_up_gE9 (u : List Ch) : (G (u.map up)).map gE9 = un (u.map up) := by
  simp only [un, G, List.map_map]
  exact List.map_congr_left fun c _ => by cases c <;> rfl

theorem gu_gE9 (u : List Ch) : (gu u).map gE9 = un (u.map up) := by
  simp only [un, gu, List.map_map]
  exact List.map_congr_left fun c _ => by cases c <;> rfl

theorem tagSt_gN3 {X : List Sy} (h : ∀ x ∈ X, x = .s4 ∨ x = .s5 ∨ x = .s6) :
    (X.map tagSt).map gN3 = X.map tagUp := by
  rw [List.map_map]
  exact List.map_congr_left fun x hx => by rcases h x hx with rfl | rfl | rfl <;> rfl

theorem tagUp_gE9 {X : List Sy} (h : ∀ x ∈ X, x = .s4 ∨ x = .s5 ∨ x = .s6) :
    (X.map tagUp).map gE9 = X.map tagSt := by
  rw [List.map_map]
  exact List.map_congr_left fun x hx => by rcases h x hx with rfl | rfl | rfl <;> rfl

theorem tagUp_gB0 {X : List Sy} (h : ∀ x ∈ X, x = .s4 ∨ x = .s5 ∨ x = .s6) :
    (X.map tagUp).map gB0 = un (X.map U10_8.g0) := by
  simp only [un, List.map_map]
  exact List.map_congr_left fun x hx => by rcases h x hx with rfl | rfl | rfl <;> rfl

theorem gu_gB0 (u : List Ch) : (gu u).map gB0 = un (u.map lo) := by
  simp only [un, gu, List.map_map]
  exact List.map_congr_left fun c _ => by cases c <;> rfl

theorem all_un_up (f : TS → Bool) (h4 : f (.s4, false) = true) (h5 : f (.s5, false) = true)
    (u : List Ch) : (un (u.map up)).all f = true := by
  simp only [un, List.all_map, List.all_eq_true, Function.comp, List.map_map]
  intro c _; cases c <;> simp [up, h4, h5]

theorem all_G_up (f : TS → Bool) (h4 : f (.s4, true) = true) (h5 : f (.s5, true) = true)
    (u : List Ch) : (G (u.map up)).all f = true := by
  simp only [G, List.all_map, List.all_eq_true, Function.comp, List.map_map]
  intro c _; cases c <;> simp [up, h4, h5]

theorem all_un_lo (f : TS → Bool) (h1 : f (.s1, false) = true) (h2 : f (.s2, false) = true)
    (u : List Ch) : (un (u.map lo)).all f = true := by
  simp only [un, List.all_map, List.all_eq_true, Function.comp, List.map_map]
  intro c _; cases c <;> simp [lo, U10_8.lo, h1, h2]

theorem all_tag {g : Sy → TS} (f : TS → Bool) (h4 : f (g .s4) = true) (h5 : f (g .s5) = true)
    (h6 : f (g .s6) = true) {X : List Sy} (hX : ∀ x ∈ X, x = .s4 ∨ x = .s5 ∨ x = .s6) :
    (X.map g).all f = true := by
  simp only [List.all_map, List.all_eq_true, Function.comp]
  intro x hx; rcases hX x hx with rfl | rfl | rfl <;> assumption

theorem LoC_all_cCp (C : CTSH) (m : Nat) : (LoC C m).all cCp = true :=
  all_tag cCp rfl rfl rfl fun _ h => mem_Lo h

theorem Mid_all (C : CTSH) (m : Nat) (rm : List Ch) :
    (LoC C m ++ (.s7, false) :: G (rm.map up)).all cCp = true := by
  simp only [List.all_append, List.all_cons, LoC_all_cCp, all_G_up cCp rfl rfl]; rfl

theorem un_map_lo_append (v u : List Ch) : un ((v ++ u).map lo) = un (v.map lo) ++ ul u := by
  simp [un, ul, List.map_map, Function.comp_def]

/-! ## 6. 1 マクロステップ -/

theorem left_split (C : CTSH) (m : Nat) (rm : List Ch) :
    (bk :: RA9 C m ++ (Sy.s7, false) :: un (rm.map up)).reverse =
      ((un (rm.map up)).reverse ++ (Sy.s7, false) :: ((U10_8.Lo C m).map tagSt).reverse) ++
        bk :: (bk :: un (U10_8.Hi C m ++ (prod C m).reverse.map lo)).reverse := by
  simp [RA9]

theorem L0_eq (C : CTSH) (m : Nat) :
    (bk :: un (U10_8.Hi C m ++ (prod C m).reverse.map lo)).reverse =
      ul (prod C m) ++ (bk :: un (U10_8.Hi C m)).reverse := by
  simp [un, ul, List.map_reverse, Function.comp_def]

theorem rep9_cons (C : CTSH) (m : Nat) (rm : List Ch) (c : Ch) (v : List Ch) :
    rep9 C m rm (c :: v) = zc bk (.go .q0) (bk :: RA9 C m ++ (Sy.s7, false) :: un (rm.map up)).reverse
      (lo c, false) (un (v.map lo)) := by
  rw [rep9_eq]; simp [un, zr]

/-- 先頭が N（任意の相）: begin で n → n′、case_y_n で相マーカーまで左へ（Y, N にタグ、∗′ を ∗ に）、
    b を ∗ に → copy_start。 -/
theorem frontN (C : CTSH) (m : Nat) (rm v : List Ch) :
    Reach1 T9 (rep9 C m rm (.N :: v))
      (zl bk (.go .q4) (ul (prod C m) ++ (bk :: un (U10_8.Hi C m)).reverse)
        (gu ([] : List Ch).reverse ++ (.s6, false) :: (LoC C m ++ (.s7, false) :: G (rm.map up)) ++
          (.s3, false) :: un (v.map lo))) := by
  rw [rep9_cons, left_split]
  have hX : ((un (rm.map up)).reverse ++ (Sy.s7, false) :: ((U10_8.Lo C m).map tagSt).reverse).all cN3
      = true := by
    simp only [List.all_append, List.all_reverse, List.all_cons, all_un_up cN3 rfl rfl,
      all_tag (g := tagSt) cN3 rfl rfl rfl (fun _ h => mem_Lo h)]; rfl
  refine (runL1g (T := T9) (p := .q0) (q := .q3) (h := (.s2, false)) (t := (.s3, false)) (by decide) gN3
    (ofAll p_N3 hX) bk _ _).trans ?_
  refine (Reach.step (stepL' (T := T9) (p := .q3) (h := bk) (t := (.s6, false)) (q := .go .q4) (by decide)
    (L := (bk :: un (U10_8.Hi C m ++ (prod C m).reverse.map lo)).reverse) (by simp) _)).trans ?_
  apply Reach.of_eq
  rw [L0_eq]
  simp only [List.map_append, List.map_reverse, List.map_cons, List.reverse_append, List.reverse_reverse,
    List.reverse_cons, un_up_gN3, tagSt_gN3 (fun _ h => mem_Lo h), LoC, gu]
  simp [gN3]

/-- 先頭が Y、相 m ≥ 1: begin → case_y_1（$ を $′ に。区切り 0 の ∗′ で折り返す）→ case_y_2（$′ を $ に）→
    case_y_n（相マーカーまで左へ）→ copy_start。 -/
theorem frontY (C : CTSH) (m : Nat) (hm : m ≠ 0) (rm v : List Ch) :
    Reach1 T9 (rep9 C m rm (.Y :: v))
      (zl bk (.go .q4) (ul (prod C m) ++ (bk :: un (U10_8.Hi C m)).reverse)
        (gu ([] : List Ch).reverse ++ (.s6, false) :: (LoC C m ++ (.s7, false) :: G (rm.map up)) ++
          (.s1, false) :: un (v.map lo))) := by
  have e1 : (bk :: RA9 C m ++ (Sy.s7, false) :: un (rm.map up)).reverse =
      ((un (rm.map up)).reverse ++ [(Sy.s7, false)]) ++ (Sy.s6, true) ::
      (((U10_8.LoCore C m).map tagSt).reverse ++ bk :: (bk :: un (U10_8.Hi C m ++ (prod C m).reverse.map lo)).reverse) := by
    simp [RA9, U10_8.Lo_ne C m hm, tagSt]
  rw [rep9_cons, e1]
  have hX1 : ((un (rm.map up)).reverse ++ [(Sy.s7, false)]).all cM1 = true := by
    simp only [List.all_append, List.all_reverse, all_un_up cM1 rfl rfl]; rfl
  refine (runL1g (T := T9) (p := .q0) (q := .q1) (h := (.s1, false)) (t := (.s1, true)) (by decide) gM1
    (ofAll p_M1 hX1) (.s6, true) _ _).trans ?_
  have e2 : (((un (rm.map up)).reverse ++ [(Sy.s7, false)]).map gM1).reverse ++ (Sy.s1, true) :: un (v.map lo) =
      ((Sy.s7, true) :: un (rm.map up)) ++ (Sy.s1, true) :: un (v.map lo) := by
    simp only [List.map_append, List.map_reverse, List.reverse_append, List.reverse_reverse,
      un_up_map (f := gM1) rfl rfl]; simp [gM1]
  rw [e2]
  have hX2 : ((Sy.s7, true) :: un (rm.map up)).all cC2 = true := by
    simp only [List.all_cons, all_un_up cC2 rfl rfl]; rfl
  refine (runRg (T := T9) (p := .q1) (q := .q2) (h := (.s6, true)) (t := (.s6, true)) (by decide) gC2
    (ofAll p_C2 hX2) _ (.s1, true) _).trans ?_
  have e3 : (((Sy.s7, true) :: un (rm.map up)).map gC2).reverse ++ (Sy.s6, true) ::
      (((U10_8.LoCore C m).map tagSt).reverse ++ bk :: (bk :: un (U10_8.Hi C m ++ (prod C m).reverse.map lo)).reverse) =
      ((un (rm.map up)).reverse ++ (Sy.s7, false) :: (Sy.s6, true) :: ((U10_8.LoCore C m).map tagSt).reverse) ++
        bk :: (bk :: un (U10_8.Hi C m ++ (prod C m).reverse.map lo)).reverse := by
    simp only [List.map_cons, un_up_map (f := gC2) rfl rfl]; simp [gC2]
  rw [e3]
  have hX3 : ((un (rm.map up)).reverse ++ (Sy.s7, false) :: (Sy.s6, true) ::
      ((U10_8.LoCore C m).map tagSt).reverse).all cN3 = true := by
    simp only [List.all_append, List.all_reverse, List.all_cons, all_un_up cN3 rfl rfl,
      all_tag (g := tagSt) cN3 rfl rfl rfl (fun _ h => mem_LoCore h)]; rfl
  refine (runLg (T := T9) (p := .q2) (q := .q3) (h := (.s1, true)) (t := (.s1, false)) (by decide) gN3
    (ofAll p_N3 hX3) bk _ _).trans ?_
  refine (Reach.step (stepL' (T := T9) (p := .q3) (h := bk) (t := (.s6, false)) (q := .go .q4) (by decide)
    (L := (bk :: un (U10_8.Hi C m ++ (prod C m).reverse.map lo)).reverse) (by simp) _)).trans ?_
  apply Reach.of_eq
  rw [L0_eq, LoC, U10_8.Lo_ne C m hm]
  simp only [List.map_append, List.map_reverse, List.map_cons, List.reverse_append, List.reverse_reverse,
    List.reverse_cons, un_up_gN3, tagSt_gN3 (fun _ h => mem_LoCore h), gu]
  simp [gN3, tagUp]

theorem q9_hd9 (c : Ch) : (⟨.q9, (hd c, false), (up c, false), .R, .go .q0⟩ : Rule St Ps TS) ∈ T9 := by
  cases c <;> decide

/-- 相の終わり: 次の区切りを新しい相マーカーに（m = k−1 なら左端で折り返し、規則領域を小文字に戻して
    区切り 0 を相マーカーに）、copy_end で先頭まで右へ（タグを外し、∗ にタグ）、先頭を大文字にして begin。 -/
theorem finish (C : CTSH) (m : Nat) (hm : m ≤ C.length) (rm : List Ch) (c : Ch) (v : List Ch) :
    Reach T9 (zl bk (.go .q4) (bk :: un (U10_8.Hi C m)).reverse
        (gu (prod C m).reverse ++ (.s6, false) :: (LoC C m ++ (.s7, false) :: G (rm.map up)) ++
          (hd c, false) :: un (v.map lo)))
      (rep9 C ((m + 1) % C.k) (rm ++ [c]) v) := by
  rcases Nat.lt_or_ge m C.length with h | h
  · -- 次の区切り m+1 がある
    rw [Nat.mod_eq_of_lt (by simp [CTSH.k]; omega), rep9_eq, U10_8.Hi_step C m h]
    rw [show (bk :: un (U10_8.Hi C (m + 1) ++ (prod C (m + 1)).reverse.map lo ++ [Sy.s6])).reverse =
        (Sy.s6, false) :: (bk :: un (U10_8.Hi C (m + 1) ++ (prod C (m + 1)).reverse.map lo)).reverse by
      simp [un]]
    simp only [zl]
    have hX : (gu (prod C m).reverse ++ (Sy.s6, false) :: (LoC C m ++ (Sy.s7, false) :: G (rm.map up))).all cE9
        = true := by
      simp only [List.all_append, List.all_cons, all_G_up cE9 rfl rfl,
        all_tag (g := tagUp) cE9 rfl rfl rfl (fun _ h => mem_Lo h), LoC]
      simp only [gu, List.all_map, Function.comp_def]
      rw [List.all_eq_true.mpr (fun c _ => by cases c <;> rfl)]; rfl
    rw [show gu (prod C m).reverse ++ (Sy.s6, false) :: (LoC C m ++ (Sy.s7, false) :: G (rm.map up)) ++
          (hd c, false) :: un (v.map lo) =
        (gu (prod C m).reverse ++ (Sy.s6, false) :: (LoC C m ++ (Sy.s7, false) :: G (rm.map up))) ++
          (hd c, false) :: un (v.map lo) by simp]
    refine (runRg (T := T9) (p := .q4) (q := .q9) (h := (.s6, false)) (t := bk) (by decide) gE9
      (ofAll p_E9 hX) _ _ _).trans ?_
    refine (Reach.step (stepR' (q9_hd9 c) _ _)).trans ?_
    apply Reach.of_eq
    congr 1
    rw [RA9, U10_8.Lo_step C m hm]
    simp only [List.map_append, List.map_cons, gu_gE9, G_up_gE9, LoC, tagUp_gE9 (fun _ h => mem_Lo h)]
    simp [un, gE9, tagSt, List.map_reverse]
    intro a _; cases a <;> simp [up]
  · -- m = k − 1: 1 周の終わり
    have hmk : m = C.length := by omega
    subst hmk
    rw [show (C.length + 1) % C.k = 0 by simp [CTSH.k], rep9_eq, U10_8.Hi_len]
    simp only [un, List.map_nil, List.reverse_cons, List.reverse_nil, List.nil_append, zl]
    have hX : (gu (prod C C.length).reverse ++ (Sy.s6, false) :: LoC C C.length).all cB0 = true := by
      simp only [List.all_append, List.all_cons,
        all_tag (g := tagUp) cB0 rfl rfl rfl (fun _ h => mem_Lo h), LoC]
      simp only [gu, List.all_map, Function.comp_def]
      rw [List.all_eq_true.mpr (fun c _ => by cases c <;> rfl)]; rfl
    rw [show gu (prod C C.length).reverse ++ (Sy.s6, false) :: (LoC C C.length ++ (Sy.s7, false) :: G (rm.map up)) ++
          (hd c, false) :: (v.map lo).map (·, false) =
        (gu (prod C C.length).reverse ++ (Sy.s6, false) :: LoC C C.length) ++ (Sy.s7, false) ::
          (G (rm.map up) ++ (hd c, false) :: (v.map lo).map (·, false)) by simp]
    refine (runRg (T := T9) (p := .q4) (q := .q0) (h := bk) (t := bk) (by decide) gB0
      (ofAll p_B0 hX) [] (.s7, false) _).trans ?_
    have eB : (gu (prod C C.length).reverse ++ (Sy.s6, false) :: LoC C C.length).map gB0 =
        un (U10_8.Hi C 0) ++ [(Sy.s6, false)] := by
      have h2 := congrArg (List.map ((·, false) : Sy → TS)) (U10_8.Lo_full_g0 C)
      rw [U10_8.Lo_step C C.length (Nat.le_refl _)] at h2
      simp only [List.map_append, List.map_cons, List.map_map, List.map_reverse, List.map_nil] at h2
      simp only [List.map_append, List.map_cons, gu_gB0, LoC, tagUp_gB0 (fun _ h => mem_Lo h), un,
        List.map_map, List.map_reverse]
      rw [← h2]
      simp [Function.comp_def, gB0, U10_8.g0]
      intro a _; cases a <;> rfl
    rw [eB]
    rw [show (un (U10_8.Hi C 0) ++ [(Sy.s6, false)]).reverse ++ [bk] =
        (Sy.s6, false) :: ((un (U10_8.Hi C 0)).reverse ++ [bk]) by simp]
    refine (Reach.step (stepL (T := T9) (p := .q0) (h := (.s7, false)) (t := (.s7, false)) (q := .go .q4)
      (by decide) _ _ _)).trans ?_
    have hX2 : ((Sy.s7, false) :: G (rm.map up)).all cE9 = true := by
      simp only [List.all_cons, all_G_up cE9 rfl rfl]; rfl
    rw [show (Sy.s7, false) :: (G (rm.map up) ++ (hd c, false) :: (v.map lo).map (·, false)) =
        ((Sy.s7, false) :: G (rm.map up)) ++ (hd c, false) :: (v.map lo).map (·, false) by simp]
    refine (runRg (T := T9) (p := .q4) (q := .q9) (h := (.s6, false)) (t := bk) (by decide) gE9
      (ofAll p_E9 hX2) _ _ _).trans ?_
    refine (Reach.step (stepR' (q9_hd9 c) _ _)).trans ?_
    apply Reach.of_eq
    congr 1
    simp only [List.map_cons, G_up_gE9]
    simp [RA9, prod, U10_8.Lo_zero, un, gE9]

theorem macroY (C : CTSH) {m : Nat} (h0 : m ≠ 0) (hk : m < C.k) (rm v : List Ch) :
    Reach1 T9 (rep9 C m rm (.Y :: v)) (rep9 C ((m + 1) % C.k) (rm ++ [.Y]) (v ++ prod C m)) := by
  have hmk : m ≤ C.length := by simp [CTSH.k] at hk; omega
  refine (frontY C m h0 rm v).trans ?_
  have hZ : (bk :: un (U10_8.Hi C m)).reverse ≠ [] := by simp
  have hL := copyY_loop _ hZ _ (Mid_all C m rm) (prod C m) [] (un (v.map lo))
    (all_un_lo cCp rfl rfl v)
  refine hL.trans ?_
  have hf := finish C m hmk rm .Y (v ++ prod C m)
  rw [un_map_lo_append] at hf
  simp only [hd] at hf
  refine Eq.mpr ?_ hf
  simp

theorem macroN (C : CTSH) {m : Nat} (hk : m < C.k) (rm v : List Ch) :
    Reach1 T9 (rep9 C m rm (.N :: v)) (rep9 C ((m + 1) % C.k) (rm ++ [.N]) v) := by
  have hmk : m ≤ C.length := by simp [CTSH.k] at hk; omega
  refine (frontN C m rm v).trans ?_
  have hZ : (bk :: un (U10_8.Hi C m)).reverse ≠ [] := by simp
  have hL := copyN_loop _ hZ _ (Mid_all C m rm) (un (v.map lo)) (prod C m) []
  refine hL.trans ?_
  have hf := finish C m hmk rm .N v
  simp only [hd] at hf
  refine Eq.mpr ?_ hf
  simp

/-! ## 7. 停止 -/

theorem halt_null (C : CTSH) (m : Nat) (rm : List Ch) :
    Step T9 (rep9 C m rm []) (finCfg9 C [] m rm) := by
  rw [rep9_eq]
  simp only [List.map_nil, un, zr]
  refine (congrArg (Step T9 _) ?_).mp (stepZ (T := T9) (p := .q0) (h := bk) (t := (.s0, true))
    (q := .halt .h0) (by decide) _ [])
  simp only [zc, finCfg9, tapeList9, un, List.map_nil, List.append_nil]
  congr 1
  · simp [RA9_length]; omega
  · simp

theorem halt_Y (C : CTSH) (rm v : List Ch) :
    Reach1 T9 (rep9 C 0 rm (.Y :: v)) (finCfg9 C (.Y :: v) 0 rm) := by
  rw [rep9_cons]
  have e1 : (bk :: RA9 C 0 ++ (Sy.s7, false) :: un (rm.map up)).reverse =
      ((un (rm.map up)).reverse ++ [(Sy.s7, false)]) ++ bk :: (bk :: un (U10_8.Hi C 0)).reverse := by
    simp [RA9, prod, U10_8.Lo_zero, un]
  rw [e1]
  have hX1 : ((un (rm.map up)).reverse ++ [(Sy.s7, false)]).all cM1 = true := by
    simp only [List.all_append, List.all_reverse, all_un_up cM1 rfl rfl]; rfl
  refine (runL1g (T := T9) (p := .q0) (q := .q1) (h := (.s1, false)) (t := (.s1, true)) (by decide) gM1
    (ofAll p_M1 hX1) bk _ _).trans ?_
  refine (Reach.step (stepZ (T := T9) (p := .q1) (h := bk) (t := (.s0, true)) (q := .halt .h1)
    (by decide) _ _)).trans ?_
  apply Reach.of_eq
  simp only [zc, finCfg9]
  congr 1
  · simp [U10_8.RA, prod, U10_8.Lo_zero, un]
  · simp only [List.map_append, List.map_reverse, List.reverse_append, List.reverse_reverse,
      un_up_map (f := gM1) rfl rfl]
    simp [gM1, un]

theorem finCfg9_halted (C : CTSH) (vf : List Ch) (mf : Nat) (rm : List Ch) :
    Halted T9 (finCfg9 C vf mf rm) := by
  intro c' ⟨r, _, hst, _⟩
  cases vf <;> simp [finCfg9] at hst

/-! ## 8. 主定理 -/

/-- **主定理**（URTM(9,14) は任意の CTSH を模倣する）。`urtm10_8_simulates_ctsh` と同じ 3 項を、
    子の表 `T9`・初期配置 `encC9`・停止配置 `finCfg9` について。 -/
theorem urtm9_14_simulates_ctsh (C : CTSH) (w : List Ch) : SimStatement C w :=
  simulates_of_steps C (rep9 C) (finCfg9 C) hD9 (macroY C) (macroN C) (halt_Y C)
    (fun m rm => Reach1.of_step (halt_null C m rm) (Reach.refl _)) (finCfg9_halted C) w

end URTM.CTSH.U9_14
