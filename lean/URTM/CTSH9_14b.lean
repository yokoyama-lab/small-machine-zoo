/-
  URTM(9,14) の第 2 の表 t4b が任意の CTSH を模倣することの一般証明（2026-10-31）。

  機械 `T9b` と表現 `rep9b`・`finCfg9b` は CTSH9_14bDefs.lean。組み立ては t4a（CTSH9_14.lean）と同じで、
  掃引の写像が違う。t4a と違って、copy の相の規則領域の大文字と `∗` はタグ無しで、case の相で消去済みの
  大文字にタグが付く。左端の b のタグは周の偶奇（`eB`）で、周の終わりに copy_start が反転させる。

  | 状態（親の役） | 向き | 通る記号 → 書く記号 |
  |---|---|---|
  | q1（case_y_1） | 左 | Y, N, $ → Y′, N′, $′ |
  | q2（case_y_2） | 右 | Y′, N′, $′ → Y, N, $ |
  | q3（case_y_n） | 左 | ∗′ → ∗、Y, N, $ はそのまま |
  | q5（copy_y_1） | 右 | $, ∗, Y, N → $′, ∗′, Y′, N′、y, n はそのまま |
  | q6（copy_y_2） | 左 | 上の逆 |
  | q7（copy_n_1） | 右 | $, Y, N, y → $′, Y′, N′, y′、∗, n はそのまま |
  | q1（copy_n_2） | 左 | 上の逆 |
  | q9（copy_end） | 右 | ∗ → ∗′、$, Y, N はそのまま |
  | q0（begin、周の終わり） | 右 | Y, N → y, n、∗ はそのまま |

  未証明の穴・新規公理・native_decide を使わない。
-/
import URTM.CTSH9_14bDefs
import URTM.CTSH9_14

set_option maxRecDepth 100000

namespace URTM.CTSH.U9_14b

open URTM URTM.KState URTM.CTSH URTM.CTSH.Sim URTM.Gen.K10_8
open URTM.CTSH.U9_14 (TS bk un tagSt RA9 G ofAll all_un_up all_G_up all_un_lo all_tag mem_Lo mem_LoCore
  map_map_id all_map_of ul un_map_lo_append RA9_length L0_eq)
open URTM.CTSH.U10_8 (up hd)

/-! ## 1. 記号の写像と、規則表からの通過の補題 -/

def cM1 (x : TS) : Bool := x == (.s4, false) || x == (.s5, false) || x == (.s7, false)
def gM1 (x : TS) : TS := (x.1, true)

def cC2 (x : TS) : Bool := x == (.s4, true) || x == (.s5, true) || x == (.s7, true)
def gC2 (x : TS) : TS := (x.1, false)

def cN3 (x : TS) : Bool :=
  x == (.s4, false) || x == (.s5, false) || x == (.s7, false) || x == (.s6, true)
def gN3 (x : TS) : TS := (x.1, false)

/-- copy の掃引が往路で通る記号（∗, $, Y, N, y, n、どれもタグ無し）。 -/
def cCp (x : TS) : Bool :=
  x == (.s6, false) || x == (.s7, false) || x == (.s4, false) || x == (.s5, false) ||
  x == (.s1, false) || x == (.s2, false)
def gY5 (x : TS) : TS := (x.1, x.1 == .s6 || x.1 == .s7 || x.1 == .s4 || x.1 == .s5)
def cY6 (x : TS) : Bool :=
  x == (.s6, true) || x == (.s7, true) || x == (.s4, true) || x == (.s5, true) ||
  x == (.s1, false) || x == (.s2, false)
def gY6 (x : TS) : TS := (x.1, false)
def gN7 (x : TS) : TS := (x.1, x.1 == .s7 || x.1 == .s4 || x.1 == .s5 || x.1 == .s1)
def cN8 (x : TS) : Bool :=
  x == (.s6, false) || x == (.s7, true) || x == (.s4, true) || x == (.s5, true) ||
  x == (.s1, true) || x == (.s2, false)
def gN8 (x : TS) : TS := (x.1, false)

def cE9 (x : TS) : Bool :=
  x == (.s7, false) || x == (.s6, false) || x == (.s4, false) || x == (.s5, false)
def gE9 (x : TS) : TS := (x.1, x.1 == .s6)

def cB0 (x : TS) : Bool := x == (.s4, false) || x == (.s5, false) || x == (.s6, false)
def gB0 (x : TS) : TS := (U10_8.g0 x.1, false)

theorem p_M1 : ∀ x, cM1 x = true → (⟨.q1, x, gM1 x, .L, .go .q1⟩ : Rule St Ps TS) ∈ T9b := by
  intro ⟨s, b⟩; cases s <;> cases b <;> decide
theorem p_C2 : ∀ x, cC2 x = true → (⟨.q2, x, gC2 x, .R, .go .q2⟩ : Rule St Ps TS) ∈ T9b := by
  intro ⟨s, b⟩; cases s <;> cases b <;> decide
theorem p_N3 : ∀ x, cN3 x = true → (⟨.q3, x, gN3 x, .L, .go .q3⟩ : Rule St Ps TS) ∈ T9b := by
  intro ⟨s, b⟩; cases s <;> cases b <;> decide
theorem p_Y5 : ∀ x, cCp x = true → (⟨.q5, x, gY5 x, .R, .go .q5⟩ : Rule St Ps TS) ∈ T9b := by
  intro ⟨s, b⟩; cases s <;> cases b <;> decide
theorem p_Y6 : ∀ x, cY6 x = true → (⟨.q6, x, gY6 x, .L, .go .q6⟩ : Rule St Ps TS) ∈ T9b := by
  intro ⟨s, b⟩; cases s <;> cases b <;> decide
theorem p_N7 : ∀ x, cCp x = true → (⟨.q7, x, gN7 x, .R, .go .q7⟩ : Rule St Ps TS) ∈ T9b := by
  intro ⟨s, b⟩; cases s <;> cases b <;> decide
theorem p_N8 : ∀ x, cN8 x = true → (⟨.q1, x, gN8 x, .L, .go .q1⟩ : Rule St Ps TS) ∈ T9b := by
  intro ⟨s, b⟩; cases s <;> cases b <;> decide
theorem p_E9 : ∀ x, cE9 x = true → (⟨.q9, x, gE9 x, .R, .go .q9⟩ : Rule St Ps TS) ∈ T9b := by
  intro ⟨s, b⟩; cases s <;> cases b <;> decide
theorem p_B0 : ∀ x, cB0 x = true → (⟨.q0, x, gB0 x, .R, .go .q0⟩ : Rule St Ps TS) ∈ T9b := by
  intro ⟨s, b⟩; cases s <;> cases b <;> decide

theorem gY6_gY5 : ∀ x, cCp x = true → gY6 (gY5 x) = x := by
  intro ⟨s, b⟩; cases s <;> cases b <;> decide
theorem cY6_gY5 : ∀ x, cCp x = true → cY6 (gY5 x) = true := by
  intro ⟨s, b⟩; cases s <;> cases b <;> decide
theorem gN8_gN7 : ∀ x, cCp x = true → gN8 (gN7 x) = x := by
  intro ⟨s, b⟩; cases s <;> cases b <;> decide
theorem cN8_gN7 : ∀ x, cCp x = true → cN8 (gN7 x) = true := by
  intro ⟨s, b⟩; cases s <;> cases b <;> decide

/-- 周の終わりに copy_start が左端の b のタグを反転させる。 -/
theorem p_wrap (e : Bool) : (⟨.q4, (.s0, e), (.s0, !e), .R, .go .q0⟩ : Rule St Ps TS) ∈ T9b := by
  cases e <;> decide

theorem q9_hd9 (c : Ch) : (⟨.q9, (hd c, false), (up c, false), .R, .go .q0⟩ : Rule St Ps TS) ∈ T9b := by
  cases c <;> decide

/-! ## 2. 周の偶奇 -/

theorem eB_step (C : CTSH) {m : Nat} (h : m + 1 < C.k) (rm : List Ch) (c : Ch) :
    eB C (m + 1) (rm ++ [c]) = eB C m rm := by
  simp only [eB, List.length_append, List.length_singleton]
  rw [show rm.length + 1 + C.k - (m + 1) = rm.length + C.k - m by omega]

theorem eB_wrap (C : CTSH) (rm : List Ch) (c : Ch) :
    eB C 0 (rm ++ [c]) = !(eB C C.length rm) := by
  have hk : C.k = C.length + 1 := rfl
  simp only [eB, List.length_append, List.length_singleton]
  rw [show rm.length + 1 + C.k - 0 = (rm.length + 1) + C.k by omega,
    show rm.length + C.k - C.length = rm.length + 1 by omega,
    Nat.add_div_right _ (by omega : 0 < C.k)]
  rcases Nat.mod_two_eq_zero_or_one ((rm.length + 1) / C.k) with h | h <;>
    simp [Nat.add_mod, h]

/-! ## 3. 記号列 -/

/-- タグ無しの大文字（copy の相の写し終えた文字）。 -/
def uu (P : List Ch) : List TS := P.map fun c => (up c, false)

theorem all_uu (f : TS → Bool) (h4 : f (.s4, false) = true) (h5 : f (.s5, false) = true) (P : List Ch) :
    (uu P).all f = true := by
  simp only [uu, List.all_map, List.all_eq_true, Function.comp]
  intro c _; cases c <;> simp [up, h4, h5]

theorem all_ul (P : List Ch) : (ul P).all cCp = true := by
  simp only [ul, List.all_map, List.all_eq_true, Function.comp]
  intro c _; cases c <;> rfl

theorem un_up_gM1 (u : List Ch) : (un (u.map up)).map gM1 = G (u.map up) := by
  simp [un, G, gM1, Function.comp_def]
theorem G_up_gC2 (u : List Ch) : (G (u.map up)).map gC2 = un (u.map up) := by
  simp [un, G, gC2, Function.comp_def]
theorem un_gN3 (X : List Sy) : (un X).map gN3 = un X := by
  simp [un, gN3, Function.comp_def]
theorem tagSt_gN3 (X : List Sy) : (X.map tagSt).map gN3 = un X := by
  simp [un, tagSt, gN3, Function.comp_def]
theorem un_Lo_gE9 {X : List Sy} (h : ∀ x ∈ X, x = .s4 ∨ x = .s5 ∨ x = .s6) :
    (un X).map gE9 = X.map tagSt := by
  simp only [un, List.map_map]
  exact List.map_congr_left fun x hx => by rcases h x hx with rfl | rfl | rfl <;> rfl
theorem un_up_gE9 (u : List Ch) : (un (u.map up)).map gE9 = un (u.map up) := by
  simp only [un, List.map_map]
  exact List.map_congr_left fun c _ => by cases c <;> rfl
theorem uu_gE9 (u : List Ch) : (uu u).map gE9 = un (u.map up) := by
  simp only [un, uu, List.map_map]
  exact List.map_congr_left fun c _ => by cases c <;> rfl
theorem uu_gB0 (u : List Ch) : (uu u).map gB0 = un (u.map lo) := by
  simp only [un, uu, List.map_map]
  exact List.map_congr_left fun c _ => by cases c <;> rfl
theorem un_Lo_gB0 {X : List Sy} (h : ∀ x ∈ X, x = .s4 ∨ x = .s5 ∨ x = .s6) :
    (un X).map gB0 = un (X.map U10_8.g0) := by
  simp only [un, List.map_map]
  exact List.map_congr_left fun x hx => by rcases h x hx with rfl | rfl | rfl <;> rfl

theorem all_un_Lo (f : TS → Bool) (h4 : f (.s4, false) = true) (h5 : f (.s5, false) = true)
    (h6 : f (.s6, false) = true) (C : CTSH) (m : Nat) : (un (U10_8.Lo C m)).all f = true :=
  all_tag f h4 h5 h6 fun _ h => mem_Lo h

theorem Mid_all (C : CTSH) (m : Nat) (rm : List Ch) :
    (un (U10_8.Lo C m) ++ (.s7, false) :: un (rm.map up)).all cCp = true := by
  simp only [List.all_append, List.all_cons, all_un_Lo cCp rfl rfl rfl, all_un_up cCp rfl rfl]; rfl

/-! ## 4. 表現 -/

theorem rep9b_eq (C : CTSH) (m : Nat) (rm v : List Ch) :
    rep9b C m rm v = zr bk (.go .q0) ((Sy.s0, eB C m rm) :: RA9 C m ++ (.s7, false) :: un (rm.map up)).reverse
      (un (v.map lo)) := by
  rw [zr_eq]; simp only [rep9b, tapeList9b, un, List.map_append]
  congr 1
  · simp [RA9_length]; omega
  · simp [List.append_assoc]

theorem rep9b_cons (C : CTSH) (m : Nat) (rm : List Ch) (c : Ch) (v : List Ch) :
    rep9b C m rm (c :: v) = zc bk (.go .q0)
      ((Sy.s0, eB C m rm) :: RA9 C m ++ (Sy.s7, false) :: un (rm.map up)).reverse
      (lo c, false) (un (v.map lo)) := by
  rw [rep9b_eq]; simp [un, zr]

theorem L0b_eq (C : CTSH) (m : Nat) (e : Bool) :
    ((Sy.s0, e) :: un (U10_8.Hi C m ++ (prod C m).reverse.map lo)).reverse =
      ul (prod C m) ++ ((Sy.s0, e) :: un (U10_8.Hi C m)).reverse := by
  simp [un, ul, List.map_reverse, Function.comp_def]

/-! ## 5. コピー -/

theorem copyY_one (c : Ch) {LL : List TS} (hLL : LL ≠ []) {R : List TS}
    (hR : R.all cCp = true) :
    Reach T9b (zc bk (.go .q4) LL (lo c, false) R)
      (zl bk (.go .q4) LL ((up c, false) :: R ++ [(lo c, false)])) := by
  rw [← zc_trail _ _ _ R, ← zl_trail]
  cases c with
  | Y =>
    refine (runRg (T := T9b) (p := .q4) (q := .q5) (h := (.s1, false)) (t := (.s0, true)) (by decide) gY5
      (ofAll p_Y5 hR) LL bk []).trans ?_
    rw [zc_nil]
    refine (Reach.step (stepR (T := T9b) (p := .q5) (h := bk) (t := (.s1, false)) (q := .go .q2)
      (by decide) _ bk [])).trans ?_
    have hX : ((Sy.s1, false) :: (R.map gY5).reverse).all cY6 = true := by
      simp only [List.all_cons, List.all_reverse]
      rw [all_map_of cY6_gY5 hR]; rfl
    refine (runLg (T := T9b) (p := .q2) (q := .q6) (h := bk) (t := bk) (by decide) gY6
      (ofAll p_Y6 hX) (.s0, true) LL []).trans ?_
    refine (Reach.step (stepL' (T := T9b) (p := .q6) (h := (.s0, true)) (t := (.s4, false))
      (q := .go .q4) (by decide) hLL _)).trans ?_
    apply Reach.of_eq
    simp only [List.map_cons, List.map_reverse, List.reverse_cons, List.reverse_reverse,
      map_map_id gY6_gY5 hR]
    simp [up, lo, U10_8.lo, gY6]
  | N =>
    refine (runRg (T := T9b) (p := .q4) (q := .q7) (h := (.s2, false)) (t := (.s0, true)) (by decide) gN7
      (ofAll p_N7 hR) LL bk []).trans ?_
    rw [zc_nil]
    refine (Reach.step (stepR (T := T9b) (p := .q7) (h := bk) (t := (.s2, false)) (q := .go .q9)
      (by decide) _ bk [])).trans ?_
    have hX : ((Sy.s2, false) :: (R.map gN7).reverse).all cN8 = true := by
      simp only [List.all_cons, List.all_reverse]
      rw [all_map_of cN8_gN7 hR]; rfl
    refine (runLg (T := T9b) (p := .q9) (q := .q1) (h := bk) (t := bk) (by decide) gN8
      (ofAll p_N8 hX) (.s0, true) LL []).trans ?_
    refine (Reach.step (stepL' (T := T9b) (p := .q1) (h := (.s0, true)) (t := (.s5, false))
      (q := .go .q4) (by decide) hLL _)).trans ?_
    apply Reach.of_eq
    simp only [List.map_cons, List.map_reverse, List.reverse_cons, List.reverse_reverse,
      map_map_id gN8_gN7 hR]
    simp [up, lo, U10_8.lo, gN8]

theorem copyN_one (c : Ch) {LL : List TS} (hLL : LL ≠ []) {X : List TS}
    (hX : X.all cCp = true) (S : List TS) :
    Reach T9b (zc bk (.go .q4) LL (lo c, false) (X ++ (.s3, false) :: S))
      (zl bk (.go .q4) LL ((up c, false) :: X ++ (.s3, false) :: S)) := by
  cases c with
  | Y =>
    refine (runRg (T := T9b) (p := .q4) (q := .q5) (h := (.s1, false)) (t := (.s0, true)) (by decide) gY5
      (ofAll p_Y5 hX) LL (.s3, false) S).trans ?_
    have hX' : (X.map gY5).reverse.all cY6 = true := by
      rw [List.all_reverse]; exact all_map_of cY6_gY5 hX
    refine (runLg (T := T9b) (p := .q5) (q := .q6) (h := (.s3, false)) (t := (.s3, false)) (by decide) gY6
      (ofAll p_Y6 hX') (.s0, true) LL S).trans ?_
    refine (Reach.step (stepL' (T := T9b) (p := .q6) (h := (.s0, true)) (t := (.s4, false))
      (q := .go .q4) (by decide) hLL _)).trans ?_
    apply Reach.of_eq
    simp only [List.map_reverse, List.reverse_reverse, map_map_id gY6_gY5 hX]
    simp [up]
  | N =>
    refine (runRg (T := T9b) (p := .q4) (q := .q7) (h := (.s2, false)) (t := (.s0, true)) (by decide) gN7
      (ofAll p_N7 hX) LL (.s3, false) S).trans ?_
    have hX' : (X.map gN7).reverse.all cN8 = true := by
      rw [List.all_reverse]; exact all_map_of cN8_gN7 hX
    refine (runLg (T := T9b) (p := .q7) (q := .q1) (h := (.s3, false)) (t := (.s3, false)) (by decide) gN8
      (ofAll p_N8 hX') (.s0, true) LL S).trans ?_
    refine (Reach.step (stepL' (T := T9b) (p := .q1) (h := (.s0, true)) (t := (.s5, false))
      (q := .go .q4) (by decide) hLL _)).trans ?_
    apply Reach.of_eq
    simp only [List.map_reverse, List.reverse_reverse, map_map_id gN8_gN7 hX]
    simp [up]

theorem copyY_loop (Z : List TS) (hZ : Z ≠ []) (Mid : List TS) (hMid : Mid.all cCp = true) :
    ∀ (Q P : List Ch) (S : List TS), S.all cCp = true →
    Reach T9b (zl bk (.go .q4) (ul Q ++ Z) (uu P.reverse ++ (.s6, false) :: Mid ++ (.s1, false) :: S))
      (zl bk (.go .q4) Z (uu (P ++ Q).reverse ++ (.s6, false) :: Mid ++ (.s1, false) :: S ++ ul Q)) := by
  intro Q
  induction Q with
  | nil => intro P S _; exact Reach.of_eq (by simp [ul])
  | cons c Q ih =>
    intro P S hS
    have hR : (uu P.reverse ++ (.s6, false) :: Mid ++ (.s1, false) :: S).all cCp = true := by
      simp only [List.all_append, List.all_cons, all_uu cCp rfl rfl, hMid, hS]; rfl
    have h1 := copyY_one c (LL := ul Q ++ Z) (by simp [hZ]) hR
    have h2 := ih (P ++ [c]) (S ++ [(lo c, false)]) (by simp [hS]; cases c <;> rfl)
    refine h1.trans (Eq.mpr ?_ h2)
    simp [ul, uu]

theorem copyN_loop (Z : List TS) (hZ : Z ≠ []) (Mid : List TS) (hMid : Mid.all cCp = true)
    (S : List TS) :
    ∀ (Q P : List Ch),
    Reach T9b (zl bk (.go .q4) (ul Q ++ Z) (uu P.reverse ++ (.s6, false) :: Mid ++ (.s3, false) :: S))
      (zl bk (.go .q4) Z (uu (P ++ Q).reverse ++ (.s6, false) :: Mid ++ (.s3, false) :: S)) := by
  intro Q
  induction Q with
  | nil => intro P; exact Reach.of_eq (by simp [ul])
  | cons c Q ih =>
    intro P
    have hX : (uu P.reverse ++ (.s6, false) :: Mid).all cCp = true := by
      simp only [List.all_append, List.all_cons, all_uu cCp rfl rfl, hMid]; rfl
    have h1 := copyN_one c (LL := ul Q ++ Z) (by simp [hZ]) hX S
    have h2 := ih (P ++ [c])
    refine h1.trans (Eq.mpr ?_ h2)
    simp [ul, uu]

/-! ## 6. 先頭の処理 -/

theorem frontN (C : CTSH) (m : Nat) (rm v : List Ch) :
    Reach1 T9b (rep9b C m rm (.N :: v))
      (zl bk (.go .q4) (ul (prod C m) ++ ((Sy.s0, eB C m rm) :: un (U10_8.Hi C m)).reverse)
        (uu ([] : List Ch).reverse ++ (.s6, false) :: (un (U10_8.Lo C m) ++ (.s7, false) :: un (rm.map up)) ++
          (.s3, false) :: un (v.map lo))) := by
  rw [rep9b_cons]
  have e1 : ((Sy.s0, eB C m rm) :: RA9 C m ++ (Sy.s7, false) :: un (rm.map up)).reverse =
      ((un (rm.map up)).reverse ++ (Sy.s7, false) :: ((U10_8.Lo C m).map tagSt).reverse) ++
        bk :: ((Sy.s0, eB C m rm) :: un (U10_8.Hi C m ++ (prod C m).reverse.map lo)).reverse := by
    simp [RA9]
  rw [e1]
  have hX : ((un (rm.map up)).reverse ++ (Sy.s7, false) :: ((U10_8.Lo C m).map tagSt).reverse).all cN3
      = true := by
    simp only [List.all_append, List.all_reverse, List.all_cons, all_un_up cN3 rfl rfl,
      all_tag (g := tagSt) cN3 rfl rfl rfl (fun _ h => mem_Lo h)]; rfl
  refine (runL1g (T := T9b) (p := .q0) (q := .q3) (h := (.s2, false)) (t := (.s3, false)) (by decide) gN3
    (ofAll p_N3 hX) bk _ _).trans ?_
  refine (Reach.step (stepL' (T := T9b) (p := .q3) (h := bk) (t := (.s6, false)) (q := .go .q4) (by decide)
    (L := ((Sy.s0, eB C m rm) :: un (U10_8.Hi C m ++ (prod C m).reverse.map lo)).reverse) (by simp) _)).trans ?_
  apply Reach.of_eq
  rw [L0b_eq]
  simp only [List.map_append, List.map_reverse, List.map_cons, List.reverse_append, List.reverse_reverse,
    List.reverse_cons, un_gN3, tagSt_gN3, uu]
  simp [gN3]

theorem frontY (C : CTSH) (m : Nat) (hm : m ≠ 0) (rm v : List Ch) :
    Reach1 T9b (rep9b C m rm (.Y :: v))
      (zl bk (.go .q4) (ul (prod C m) ++ ((Sy.s0, eB C m rm) :: un (U10_8.Hi C m)).reverse)
        (uu ([] : List Ch).reverse ++ (.s6, false) :: (un (U10_8.Lo C m) ++ (.s7, false) :: un (rm.map up)) ++
          (.s1, false) :: un (v.map lo))) := by
  have e1 : ((Sy.s0, eB C m rm) :: RA9 C m ++ (Sy.s7, false) :: un (rm.map up)).reverse =
      ((un (rm.map up)).reverse ++ [(Sy.s7, false)]) ++ (Sy.s6, true) ::
      (((U10_8.LoCore C m).map tagSt).reverse ++ bk ::
        ((Sy.s0, eB C m rm) :: un (U10_8.Hi C m ++ (prod C m).reverse.map lo)).reverse) := by
    simp [RA9, U10_8.Lo_ne C m hm, tagSt]
  rw [rep9b_cons, e1]
  have hX1 : ((un (rm.map up)).reverse ++ [(Sy.s7, false)]).all cM1 = true := by
    simp only [List.all_append, List.all_reverse, all_un_up cM1 rfl rfl]; rfl
  refine (runL1g (T := T9b) (p := .q0) (q := .q1) (h := (.s1, false)) (t := (.s1, true)) (by decide) gM1
    (ofAll p_M1 hX1) (.s6, true) _ _).trans ?_
  have e2 : (((un (rm.map up)).reverse ++ [(Sy.s7, false)]).map gM1).reverse ++ (Sy.s1, true) :: un (v.map lo) =
      ((Sy.s7, true) :: G (rm.map up)) ++ (Sy.s1, true) :: un (v.map lo) := by
    simp only [List.map_append, List.map_reverse, List.reverse_append, List.reverse_reverse, un_up_gM1]
    simp [gM1]
  rw [e2]
  have hX2 : ((Sy.s7, true) :: G (rm.map up)).all cC2 = true := by
    simp only [List.all_cons, all_G_up cC2 rfl rfl]; rfl
  refine (runRg (T := T9b) (p := .q1) (q := .q2) (h := (.s6, true)) (t := (.s6, true)) (by decide) gC2
    (ofAll p_C2 hX2) _ (.s1, true) _).trans ?_
  have e3 : (((Sy.s7, true) :: G (rm.map up)).map gC2).reverse ++ (Sy.s6, true) ::
      (((U10_8.LoCore C m).map tagSt).reverse ++ bk ::
        ((Sy.s0, eB C m rm) :: un (U10_8.Hi C m ++ (prod C m).reverse.map lo)).reverse) =
      ((un (rm.map up)).reverse ++ (Sy.s7, false) :: (Sy.s6, true) :: ((U10_8.LoCore C m).map tagSt).reverse) ++
        bk :: ((Sy.s0, eB C m rm) :: un (U10_8.Hi C m ++ (prod C m).reverse.map lo)).reverse := by
    simp only [List.map_cons, G_up_gC2]; simp [gC2]
  rw [e3]
  have hX3 : ((un (rm.map up)).reverse ++ (Sy.s7, false) :: (Sy.s6, true) ::
      ((U10_8.LoCore C m).map tagSt).reverse).all cN3 = true := by
    simp only [List.all_append, List.all_reverse, List.all_cons, all_un_up cN3 rfl rfl,
      all_tag (g := tagSt) cN3 rfl rfl rfl (fun _ h => mem_LoCore h)]; rfl
  refine (runLg (T := T9b) (p := .q2) (q := .q3) (h := (.s1, true)) (t := (.s1, false)) (by decide) gN3
    (ofAll p_N3 hX3) bk _ _).trans ?_
  refine (Reach.step (stepL' (T := T9b) (p := .q3) (h := bk) (t := (.s6, false)) (q := .go .q4) (by decide)
    (L := ((Sy.s0, eB C m rm) :: un (U10_8.Hi C m ++ (prod C m).reverse.map lo)).reverse) (by simp) _)).trans ?_
  apply Reach.of_eq
  rw [L0b_eq, U10_8.Lo_ne C m hm]
  simp only [List.map_append, List.map_reverse, List.map_cons, List.reverse_append, List.reverse_reverse,
    List.reverse_cons, un_gN3, tagSt_gN3, uu]
  simp [gN3, un, tagSt]

/-! ## 7. 相の終わり -/

theorem finish (C : CTSH) (m : Nat) (hm : m ≤ C.length) (rm : List Ch) (c : Ch) (v : List Ch) :
    Reach T9b (zl bk (.go .q4) ((Sy.s0, eB C m rm) :: un (U10_8.Hi C m)).reverse
        (uu (prod C m).reverse ++ (.s6, false) :: (un (U10_8.Lo C m) ++ (.s7, false) :: un (rm.map up)) ++
          (hd c, false) :: un (v.map lo)))
      (rep9b C ((m + 1) % C.k) (rm ++ [c]) v) := by
  rcases Nat.lt_or_ge m C.length with h | h
  · -- 次の区切り m+1 がある
    have hk : m + 1 < C.k := by simp [CTSH.k]; omega
    rw [Nat.mod_eq_of_lt hk, rep9b_eq, eB_step C hk, U10_8.Hi_step C m h]
    rw [show ((Sy.s0, eB C m rm) :: un (U10_8.Hi C (m + 1) ++ (prod C (m + 1)).reverse.map lo ++ [Sy.s6])).reverse =
        (Sy.s6, false) :: ((Sy.s0, eB C m rm) :: un (U10_8.Hi C (m + 1) ++ (prod C (m + 1)).reverse.map lo)).reverse by
      simp [un]]
    simp only [zl]
    have hX : (uu (prod C m).reverse ++ (Sy.s6, false) :: (un (U10_8.Lo C m) ++ (Sy.s7, false) :: un (rm.map up))).all cE9
        = true := by
      simp only [List.all_append, List.all_cons, all_uu cE9 rfl rfl, all_un_Lo cE9 rfl rfl rfl,
        all_un_up cE9 rfl rfl]; rfl
    rw [show uu (prod C m).reverse ++ (Sy.s6, false) :: (un (U10_8.Lo C m) ++ (Sy.s7, false) :: un (rm.map up)) ++
          (hd c, false) :: un (v.map lo) =
        (uu (prod C m).reverse ++ (Sy.s6, false) :: (un (U10_8.Lo C m) ++ (Sy.s7, false) :: un (rm.map up))) ++
          (hd c, false) :: un (v.map lo) by simp]
    refine (runRg (T := T9b) (p := .q4) (q := .q9) (h := (.s6, false)) (t := bk) (by decide) gE9
      (ofAll p_E9 hX) _ _ _).trans ?_
    refine (Reach.step (stepR' (q9_hd9 c) _ _)).trans ?_
    apply Reach.of_eq
    congr 1
    rw [RA9, U10_8.Lo_step C m hm]
    simp only [List.map_append, List.map_cons, uu_gE9, un_up_gE9, un_Lo_gE9 (fun _ h => mem_Lo h)]
    simp [un, gE9, tagSt, List.map_reverse]
    intro a _; cases a <;> simp [up]
  · -- m = k − 1: 1 周の終わり
    have hmk : m = C.length := by omega
    subst hmk
    rw [show (C.length + 1) % C.k = 0 by simp [CTSH.k], rep9b_eq, eB_wrap, U10_8.Hi_len]
    simp only [un, List.map_nil, List.reverse_cons, List.reverse_nil, List.nil_append, zl]
    have hX : (uu (prod C C.length).reverse ++ (Sy.s6, false) ::
        (U10_8.Lo C C.length).map ((·, false) : Sy → TS)).all cB0 = true := by
      have := all_un_Lo cB0 rfl rfl rfl C C.length
      simp only [un] at this
      simp only [List.all_append, List.all_cons, all_uu cB0 rfl rfl, this]; rfl
    rw [show uu (prod C C.length).reverse ++ (Sy.s6, false) :: ((U10_8.Lo C C.length).map (·, false) ++
          (Sy.s7, false) :: (rm.map up).map (·, false)) ++ (hd c, false) :: (v.map lo).map (·, false) =
        (uu (prod C C.length).reverse ++ (Sy.s6, false) :: (U10_8.Lo C C.length).map ((·, false) : Sy → TS)) ++
          (Sy.s7, false) :: ((rm.map up).map (·, false) ++ (hd c, false) :: (v.map lo).map (·, false)) by simp]
    refine (runRg (T := T9b) (p := .q4) (q := .q0) (h := (.s0, eB C C.length rm))
      (t := (.s0, !eB C C.length rm)) (p_wrap _) gB0 (ofAll p_B0 hX) [] (.s7, false) _).trans ?_
    have eB0 : (uu (prod C C.length).reverse ++ (Sy.s6, false) ::
        (U10_8.Lo C C.length).map ((·, false) : Sy → TS)).map gB0 =
        un (U10_8.Hi C 0) ++ [(Sy.s6, false)] := by
      show (uu (prod C C.length).reverse ++ (Sy.s6, false) :: un (U10_8.Lo C C.length)).map gB0 = _
      have h2 := congrArg (List.map ((·, false) : Sy → TS)) (U10_8.Lo_full_g0 C)
      rw [U10_8.Lo_step C C.length (Nat.le_refl _)] at h2
      simp only [List.map_append, List.map_cons, List.map_map, List.map_reverse, List.map_nil] at h2
      simp only [List.map_append, List.map_cons, uu_gB0, un_Lo_gB0 (fun _ h => mem_Lo h), un,
        List.map_map, List.map_reverse]
      rw [← h2]
      simp [Function.comp_def, gB0, U10_8.g0]
      intro a _; cases a <;> rfl
    rw [eB0]
    rw [show (un (U10_8.Hi C 0) ++ [(Sy.s6, false)]).reverse ++ [((Sy.s0, !eB C C.length rm) : TS)] =
        (Sy.s6, false) :: ((un (U10_8.Hi C 0)).reverse ++ [(Sy.s0, !eB C C.length rm)]) by simp]
    refine (Reach.step (stepL (T := T9b) (p := .q0) (h := (.s7, false)) (t := (.s7, false)) (q := .go .q4)
      (by decide) _ _ _)).trans ?_
    have hX2 : ((Sy.s7, false) :: (rm.map up).map (·, false)).all cE9 = true := by
      simp only [List.all_cons]
      rw [show (rm.map up).map ((·, false) : Sy → TS) = un (rm.map up) from rfl, all_un_up cE9 rfl rfl]; rfl
    rw [show (Sy.s7, false) :: ((rm.map up).map (·, false) ++ (hd c, false) :: (v.map lo).map (·, false)) =
        ((Sy.s7, false) :: (rm.map up).map (·, false)) ++ (hd c, false) :: (v.map lo).map (·, false) by simp]
    refine (runRg (T := T9b) (p := .q4) (q := .q9) (h := (.s6, false)) (t := bk) (by decide) gE9
      (ofAll p_E9 hX2) _ _ _).trans ?_
    refine (Reach.step (stepR' (q9_hd9 c) _ _)).trans ?_
    apply Reach.of_eq
    congr 1
    simp only [List.map_cons]
    rw [show ((rm.map up).map ((·, false) : Sy → TS)).map gE9 = un (rm.map up) from un_up_gE9 rm]
    simp [RA9, prod, U10_8.Lo_zero, un, gE9]

/-! ## 8. 1 マクロステップと停止 -/

theorem macroY (C : CTSH) {m : Nat} (h0 : m ≠ 0) (hk : m < C.k) (rm v : List Ch) :
    Reach1 T9b (rep9b C m rm (.Y :: v)) (rep9b C ((m + 1) % C.k) (rm ++ [.Y]) (v ++ prod C m)) := by
  have hmk : m ≤ C.length := by simp [CTSH.k] at hk; omega
  refine (frontY C m h0 rm v).trans ?_
  have hZ : ((Sy.s0, eB C m rm) :: un (U10_8.Hi C m)).reverse ≠ [] := by simp
  have hL := copyY_loop _ hZ _ (Mid_all C m rm) (prod C m) [] (un (v.map lo))
    (all_un_lo cCp rfl rfl v)
  refine hL.trans ?_
  have hf := finish C m hmk rm .Y (v ++ prod C m)
  rw [un_map_lo_append] at hf
  simp only [hd] at hf
  refine Eq.mpr ?_ hf
  simp

theorem macroN (C : CTSH) {m : Nat} (hk : m < C.k) (rm v : List Ch) :
    Reach1 T9b (rep9b C m rm (.N :: v)) (rep9b C ((m + 1) % C.k) (rm ++ [.N]) v) := by
  have hmk : m ≤ C.length := by simp [CTSH.k] at hk; omega
  refine (frontN C m rm v).trans ?_
  have hZ : ((Sy.s0, eB C m rm) :: un (U10_8.Hi C m)).reverse ≠ [] := by simp
  have hL := copyN_loop _ hZ _ (Mid_all C m rm) (un (v.map lo)) (prod C m) []
  refine hL.trans ?_
  have hf := finish C m hmk rm .N v
  simp only [hd] at hf
  refine Eq.mpr ?_ hf
  simp

theorem halt_null (C : CTSH) (m : Nat) (rm : List Ch) :
    Step T9b (rep9b C m rm []) (finCfg9b C [] m rm) := by
  rw [rep9b_eq]
  simp only [List.map_nil, un, zr]
  refine (congrArg (Step T9b _) ?_).mp (stepZ (T := T9b) (p := .q0) (h := bk) (t := bk)
    (q := .halt .h0) (by decide) _ [])
  simp only [zc, finCfg9b, tapeList9b, un, List.map_nil, List.append_nil]
  congr 1
  · simp [RA9_length]; omega
  · rw [List.reverse_reverse]; exact tp_trail _

theorem halt_Y (C : CTSH) (rm v : List Ch) :
    Reach1 T9b (rep9b C 0 rm (.Y :: v)) (finCfg9b C (.Y :: v) 0 rm) := by
  rw [rep9b_cons]
  have e1 : ((Sy.s0, eB C 0 rm) :: RA9 C 0 ++ (Sy.s7, false) :: un (rm.map up)).reverse =
      ((un (rm.map up)).reverse ++ [(Sy.s7, false)]) ++ bk :: ((Sy.s0, eB C 0 rm) :: un (U10_8.Hi C 0)).reverse := by
    simp [RA9, prod, U10_8.Lo_zero, un]
  rw [e1]
  have hX1 : ((un (rm.map up)).reverse ++ [(Sy.s7, false)]).all cM1 = true := by
    simp only [List.all_append, List.all_reverse, all_un_up cM1 rfl rfl]; rfl
  refine (runL1g (T := T9b) (p := .q0) (q := .q1) (h := (.s1, false)) (t := (.s1, true)) (by decide) gM1
    (ofAll p_M1 hX1) bk _ _).trans ?_
  refine (Reach.step (stepZ (T := T9b) (p := .q1) (h := bk) (t := bk) (q := .halt .h1)
    (by decide) _ _)).trans ?_
  apply Reach.of_eq
  simp only [zc, finCfg9b]
  congr 1
  · simp [U10_8.RA, prod, U10_8.Lo_zero, un]
  · simp only [List.map_append, List.map_reverse, List.reverse_append, List.reverse_reverse, un_up_gM1]
    simp [gM1, un, G]

theorem finCfg9b_halted (C : CTSH) (vf : List Ch) (mf : Nat) (rm : List Ch) :
    Halted T9b (finCfg9b C vf mf rm) := by
  intro c' ⟨r, _, hst, _⟩
  cases vf <;> simp [finCfg9b] at hst

/-! ## 9. 主定理 -/

/-- **主定理**（URTM(9,14) の第 2 の表 t4b は任意の CTSH を模倣する）。 -/
theorem urtm9_14b_simulates_ctsh (C : CTSH) (w : List Ch) : SimStatementB C w :=
  simulates_of_steps C (rep9b C) (finCfg9b C) hD9b (macroY C) (macroN C) (halt_Y C)
    (fun m rm => Reach1.of_step (halt_null C m rm) (Reach.refl _)) (finCfg9b_halted C) w

end URTM.CTSH.U9_14b
