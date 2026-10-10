/-
  URTM(10,8)（Morita 2017, §7.3.2, Table 7.2）が任意の CTSH を模倣することの一般証明。

  機械は生成モジュール `URTM.Gen.K10_8` の `T`（記述ファイル urtm10-8.txt の五つ組そのもの。
  手で写していない）。記号・状態の対応（生成器のコメントより）:
    記号  s0=b s1=y s2=n s3=nd(n′) s4=y1(Y) s5=n1(N) s6=* s7=$
    状態  q0=begin q1=case_y_1 q2=case_y_2 q3=case_y_n q4=copy_start
          q5=copy_y_1 q6=copy_y_2 q7=copy_n_1 q8=copy_n_2 q9=copy_end
    疑似状態 h0=null h1=halt

  主定理 `urtm10_8_simulates_ctsh`（ファイル末尾）と、定理 A と合成した
  `urtm4_88_simulates_ctsh`。ジッパー・掃引（begin は書き換えつつ進むので `sweepRg` 等）と模倣の枠組み
  （`simulates_of`）は CTSHSim.lean。計画と補題の分解・検証の記録は docs/07_ctsh_lean_plan.md。

  生成モジュールに依存するので、`tools/gen_all_lean.sh`（CI）が書く `URTM.lean` 経由でビルドされる。
  未証明の穴・新規公理・native_decide を使わない。
-/
import URTM.CTSHSim
import URTM.Gen.K10_8

namespace URTM.CTSH.U10_8

open URTM URTM.KState URTM.CTSH URTM.CTSH.Sim URTM.Gen.K10_8

/-! ## 1. 規則表から読み取る通過集合（`decide` で T を直接検査） -/

/-- {Y, N, $}（case_y_1 が左へ、case_y_2 が右へ通過）。 -/
def c457 (x : Sy) : Bool := x == .s4 || x == .s5 || x == .s7
/-- {Y, N, ∗, $}（case_y_n が左へ、copy_end が右へ通過）。 -/
def c4567 (x : Sy) : Bool := x == .s4 || x == .s5 || x == .s6 || x == .s7
/-- b と n′ 以外（copy_y_1, copy_n_1 が右へ、copy_y_2, copy_n_2 が左へ通過）。 -/
def cNot03 (x : Sy) : Bool := x != .s0 && x != .s3
/-- {Y, N, ∗}（begin が右へ通過しつつ Y→y, N→n と小文字に戻す）。 -/
def c456 (x : Sy) : Bool := x == .s4 || x == .s5 || x == .s6

/-- begin の書換: Y→y, N→n、他はそのまま。 -/
def g0 : Sy → Sy
  | .s4 => .s1
  | .s5 => .s2
  | x => x

theorem ofAll {c : Sy → Bool} {P : Sy → Prop} (hp : ∀ x, c x = true → P x) {X : List Sy}
    (h : X.all c = true) : ∀ x ∈ X, P x :=
  fun x hx => hp x (List.all_eq_true.mp h x hx)

theorem p_q1 : ∀ x, c457 x = true → (⟨.q1, x, id x, .L, .go .q1⟩ : Rule St Ps Sy) ∈ T := by
  intro x; cases x <;> decide
theorem p_q2 : ∀ x, c457 x = true → (⟨.q2, x, id x, .R, .go .q2⟩ : Rule St Ps Sy) ∈ T := by
  intro x; cases x <;> decide
theorem p_q3 : ∀ x, c4567 x = true → (⟨.q3, x, id x, .L, .go .q3⟩ : Rule St Ps Sy) ∈ T := by
  intro x; cases x <;> decide
theorem p_q9 : ∀ x, c4567 x = true → (⟨.q9, x, id x, .R, .go .q9⟩ : Rule St Ps Sy) ∈ T := by
  intro x; cases x <;> decide
theorem p_q5 : ∀ x, cNot03 x = true → (⟨.q5, x, id x, .R, .go .q5⟩ : Rule St Ps Sy) ∈ T := by
  intro x; cases x <;> decide
theorem p_q7 : ∀ x, cNot03 x = true → (⟨.q7, x, id x, .R, .go .q7⟩ : Rule St Ps Sy) ∈ T := by
  intro x; cases x <;> decide
theorem p_q6 : ∀ x, cNot03 x = true → (⟨.q6, x, id x, .L, .go .q6⟩ : Rule St Ps Sy) ∈ T := by
  intro x; cases x <;> decide
theorem p_q8 : ∀ x, cNot03 x = true → (⟨.q8, x, id x, .L, .go .q8⟩ : Rule St Ps Sy) ∈ T := by
  intro x; cases x <;> decide
theorem p_q0 : ∀ x, c456 x = true → (⟨.q0, x, g0 x, .R, .go .q0⟩ : Rule St Ps Sy) ∈ T := by
  intro x; cases x <;> decide

/-! ## 2. CTSH の符号化（原典 p. 183, 186 の初期 ID と、相 m の不変量） -/

/-- ϕ₁: Y ↦ y, N ↦ n（現在の文字列と、小文字の規則）。 -/
def lo : Ch → Sy
  | .Y => .s1
  | .N => .s2

/-- 大文字: Y ↦ Y, N ↦ N（消去済みの記号と、コピー済みの規則）。 -/
def up : Ch → Sy
  | .Y => .s4
  | .N => .s5

/-- H(m) = ϕ₁(w^R_{k−1}) ∗ ⋯ ϕ₁(w^R_{m+1}) ∗（相マーカーより左の、小文字のままの規則）。 -/
abbrev Hi (C : CTSH) (m : Nat) : List Sy := Sim.Hi lo .s6 C m
/-- ϕ_up(w^R_{m−1}) ∗ ⋯ ϕ_up(w^R_1) ∗。 -/
abbrev LoCore (C : CTSH) (m : Nat) : List Sy := Sim.LoCore up .s6 C m
/-- Lo(m) = ϕ_up(w^R_{m−1}) ∗ ⋯ ϕ_up(w^R_1) ∗ ∗（最後の ∗ が区切り 0）。相 0 では空。 -/
abbrev Lo (C : CTSH) (m : Nat) : List Sy := Sim.Lo up .s6 C m

/-- 規則領域 RA(m) = H(m) · ϕ₁(w^R_m) · b · Lo(m)。b が相マーカー。 -/
def RA (C : CTSH) (m : Nat) : List Sy :=
  Hi C m ++ (prod C m).reverse.map lo ++ .s0 :: Lo C m

/-- テープの中身（左端が位置 0）: b · RA(m) · $ · ϕ_up(rm) · ϕ₁(v)。以降は b。 -/
def tapeList (C : CTSH) (m : Nat) (rm v : List Ch) : List Sy :=
  .s0 :: RA C m ++ .s7 :: rm.map up ++ v.map lo

def tapeOf (C : CTSH) (m : Nat) (rm v : List Ch) : Int → Sy := tp .s0 (tapeList C m rm v)

/-- CTSH の ID (v, m) と消去済みの記号列 rm を表す U10_8 の配置: 状態 begin、
    ヘッドは現在の文字列の先頭（v = λ なら直後の b）。 -/
def rep (C : CTSH) (m : Nat) (rm v : List Ch) : Cfg St Ps Sy :=
  { st := .go .q0, pos := (RA C m).length + 2 + rm.length, tape := tapeOf C m rm v }

/-- **Morita の符号化**: CTSH C と初期語 w から U10_8 の初期配置
    `b ϕ₁(w^R_{k−1}) ∗ ⋯ ∗ ϕ₁(w^R_1) ∗ b $ q_begin ϕ₁(w) b`。 -/
def encC (C : CTSH) (w : List Ch) : Cfg St Ps Sy := rep C 0 [] w

/-- 停止配置。最終 ID が (λ, m) なら null（begin が b を読んで 0 シフト）、
    (Y v, 0) なら halt（case_y_1 が区切り 0 の b を読んで 0 シフト）。いずれもテープは
    `tapeList C m rm vf`、すなわち消去済みの大文字列の直後に最終文字列 vf が小文字で並ぶ。 -/
def finCfg (C : CTSH) (vf : List Ch) (mf : Nat) (rm : List Ch) : Cfg St Ps Sy :=
  match vf with
  | [] => { st := .halt .h0, pos := (RA C mf).length + 2 + rm.length, tape := tapeOf C mf rm [] }
  | _ :: _ => { st := .halt .h1, pos := (RA C 0).length, tape := tapeOf C 0 rm vf }

/-! ### 規則領域の漸化式 -/

theorem Hi_step (C : CTSH) (m : Nat) (h : m < C.length) :
    Hi C m = Hi C (m + 1) ++ (prod C (m + 1)).reverse.map lo ++ [.s6] := Sim.Hi_step C m h
theorem Hi_len (C : CTSH) : Hi C C.length = [] := Sim.Hi_len C
theorem Lo_step (C : CTSH) (m : Nat) (h : m ≤ C.length) :
    Lo C (m + 1) = (prod C m).reverse.map up ++ .s6 :: Lo C m := Sim.Lo_step C m h
theorem Lo_ne (C : CTSH) (m : Nat) (h : m ≠ 0) : Lo C m = LoCore C m ++ [.s6] := Sim.Lo_ne C m h
theorem Lo_zero (C : CTSH) : Lo C 0 = [] := rfl

theorem g0_up (c : Ch) : g0 (up c) = lo c := by cases c <;> rfl

theorem Lo_full_g0 (C : CTSH) : (Lo C (C.length + 1)).map g0 = Hi C 0 ++ [.s6] := by
  simp only [Lo, Sim.Lo, Sim.LoCore, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel,
    List.take_length, Hi, Sim.Hi, List.drop_zero, List.map_append, List.map_flatten, List.map_map]
  congr 2
  · congr 1; funext w
    simp only [Function.comp_def, List.map_append, List.map_reverse, List.map_map, List.map_cons,
      List.map_nil]
    congr 2
    exact List.map_congr_left (fun c _ => g0_up c)

/-! ### 記号クラス -/

theorem all_up (f : Sy → Bool) (h4 : f .s4 = true) (h5 : f .s5 = true) (w : List Ch) :
    (w.map up).all f = true := by
  induction w with
  | nil => rfl
  | cons c w ih => cases c <;> simp_all [up]

theorem all_lo (f : Sy → Bool) (h1 : f .s1 = true) (h2 : f .s2 = true) (w : List Ch) :
    (w.map lo).all f = true := by
  induction w with
  | nil => rfl
  | cons c w ih => cases c <;> simp_all [lo]

theorem all_LoCore (f : Sy → Bool) (h4 : f .s4 = true) (h5 : f .s5 = true) (h6 : f .s6 = true)
    (C : CTSH) (m : Nat) : (LoCore C m).all f = true := by
  simp only [LoCore, Sim.LoCore, List.all_eq_true, List.mem_flatten, List.mem_map]
  rintro x ⟨_, ⟨w, _, rfl⟩, hx⟩
  simp only [List.mem_append] at hx
  rcases hx with hx | hx
  · rw [List.map_reverse] at hx
    exact List.all_eq_true.mp (all_up f h4 h5 w.reverse) x (by simpa using hx)
  · simp at hx; subst hx; exact h6

theorem all_Lo (f : Sy → Bool) (h4 : f .s4 = true) (h5 : f .s5 = true) (h6 : f .s6 = true)
    (C : CTSH) (m : Nat) : (Lo C m).all f = true := by
  unfold Lo Sim.Lo; split
  · rfl
  · simp [List.all_append, all_LoCore f h4 h5 h6, h6]

theorem all_imp {f g : Sy → Bool} (h : ∀ x, f x = true → g x = true) {X : List Sy}
    (hX : X.all f = true) : X.all g = true :=
  List.all_eq_true.mpr fun x hx => h x (List.all_eq_true.mp hX x hx)

theorem c4567_not03 : ∀ x, c4567 x = true → cNot03 x = true := by intro x; cases x <;> decide

/-! ## 3. 表現と配置 -/

theorem rep_eq (C : CTSH) (m : Nat) (rm v : List Ch) :
    rep C m rm v = zr .s0 (.go .q0) (.s0 :: RA C m ++ .s7 :: rm.map up).reverse (v.map lo) := by
  rw [zr_eq]; simp only [rep, tapeOf]; congr 1 <;> simp; omega

/-! ## 4. コピー（copy_start が規則 1 文字を読み、右端まで行って戻る） -/

/-- 先頭が y（書き足す）: c を右端の b に書き、戻って c の位置を大文字に。 -/
theorem copyY_one (c : Ch) {LL : List Sy} (hLL : LL ≠ []) {R : List Sy}
    (hR : R.all cNot03 = true) :
    Reach T (zc .s0 (.go .q4) LL (lo c) R) (zl .s0 (.go .q4) LL (up c :: R ++ [lo c])) := by
  rw [← zc_trail _ _ _ R, ← zl_trail]
  have hR' : ((R.map id).reverse).all cNot03 = true := by simpa using hR
  cases c with
  | Y =>
    refine (runRg (T := T) (p := .q4) (q := .q5) (h := .s1) (t := .s0) (by decide) id
      (ofAll p_q5 hR) LL .s0 []).trans ?_
    rw [zc_nil]
    refine (Reach.step (stepR (T := T) (p := .q5) (h := .s0) (t := .s1) (q := .go .q2) (by decide) _ .s0 [])).trans ?_
    refine (runLg (T := T) (p := .q2) (q := .q6) (h := .s0) (t := .s0) (by decide) id
      (X := .s1 :: (R.map id).reverse) (ofAll p_q6 (by simp only [List.all_cons, hR'] <;> decide)) .s0 LL []).trans ?_
    refine (Reach.step (stepL' (T := T) (p := .q6) (h := .s0) (t := .s4) (q := .go .q4) (by decide) hLL _)).trans ?_
    exact Reach.of_eq (by simp [up, lo])
  | N =>
    refine (runRg (T := T) (p := .q4) (q := .q7) (h := .s2) (t := .s0) (by decide) id
      (ofAll p_q7 hR) LL .s0 []).trans ?_
    rw [zc_nil]
    refine (Reach.step (stepR (T := T) (p := .q7) (h := .s0) (t := .s2) (q := .go .q9) (by decide) _ .s0 [])).trans ?_
    refine (runLg (T := T) (p := .q9) (q := .q8) (h := .s0) (t := .s0) (by decide) id
      (X := .s2 :: (R.map id).reverse) (ofAll p_q8 (by simp only [List.all_cons, hR'] <;> decide)) .s0 LL []).trans ?_
    refine (Reach.step (stepL' (T := T) (p := .q8) (h := .s0) (t := .s5) (q := .go .q4) (by decide) hLL _)).trans ?_
    exact Reach.of_eq (by simp [up, lo])

/-- 先頭が n′（書き足さない）: n′ で折り返し、戻って c の位置を大文字に。 -/
theorem copyN_one (c : Ch) {LL : List Sy} (hLL : LL ≠ []) {X : List Sy}
    (hX : X.all c4567 = true) (S : List Sy) :
    Reach T (zc .s0 (.go .q4) LL (lo c) (X ++ .s3 :: S)) (zl .s0 (.go .q4) LL (up c :: X ++ .s3 :: S)) := by
  have hX' : X.all cNot03 = true := all_imp c4567_not03 hX
  have hX'' : ((X.map id).reverse).all cNot03 = true := by simpa using hX'
  cases c with
  | Y =>
    refine (runRg (T := T) (p := .q4) (q := .q5) (h := .s1) (t := .s0) (by decide) id
      (ofAll p_q5 hX') LL .s3 S).trans ?_
    refine (runLg (T := T) (p := .q5) (q := .q6) (h := .s3) (t := .s3) (by decide) id
      (ofAll p_q6 hX'') .s0 LL S).trans ?_
    refine (Reach.step (stepL' (T := T) (p := .q6) (h := .s0) (t := .s4) (q := .go .q4) (by decide) hLL _)).trans ?_
    exact Reach.of_eq (by simp [up])
  | N =>
    refine (runRg (T := T) (p := .q4) (q := .q7) (h := .s2) (t := .s0) (by decide) id
      (ofAll p_q7 hX') LL .s3 S).trans ?_
    refine (runLg (T := T) (p := .q7) (q := .q8) (h := .s3) (t := .s3) (by decide) id
      (ofAll p_q8 hX'') .s0 LL S).trans ?_
    refine (Reach.step (stepL' (T := T) (p := .q8) (h := .s0) (t := .s5) (q := .go .q4) (by decide) hLL _)).trans ?_
    exact Reach.of_eq (by simp [up])

theorem copyY_loop (Z : List Sy) (hZ : Z ≠ []) (Mid : List Sy) (hMid : Mid.all c4567 = true) :
    ∀ (Q P : List Ch) (S : List Sy), S.all cNot03 = true →
    Reach T (zl .s0 (.go .q4) (Q.map lo ++ Z) (P.reverse.map up ++ .s6 :: Mid ++ .s1 :: S))
      (zl .s0 (.go .q4) Z ((P ++ Q).reverse.map up ++ .s6 :: Mid ++ .s1 :: S ++ Q.map lo)) := by
  intro Q
  induction Q with
  | nil => intro P S _; exact Reach.of_eq (by simp)
  | cons c Q ih =>
    intro P S hS
    have hR : (P.reverse.map up ++ .s6 :: Mid ++ .s1 :: S).all cNot03 = true := by
      simp only [List.all_append, List.all_cons, all_up cNot03 rfl rfl, all_imp c4567_not03 hMid, hS]
      rfl
    have h1 := copyY_one c (LL := Q.map lo ++ Z) (by simp [hZ]) hR
    have h2 := ih (P ++ [c]) (S ++ [lo c]) (by simp [hS]; cases c <;> rfl)
    refine h1.trans (Eq.mpr ?_ h2)
    simp

theorem copyN_loop (Z : List Sy) (hZ : Z ≠ []) (Mid : List Sy) (hMid : Mid.all c4567 = true)
    (S : List Sy) :
    ∀ (Q P : List Ch),
    Reach T (zl .s0 (.go .q4) (Q.map lo ++ Z) (P.reverse.map up ++ .s6 :: Mid ++ .s3 :: S))
      (zl .s0 (.go .q4) Z ((P ++ Q).reverse.map up ++ .s6 :: Mid ++ .s3 :: S)) := by
  intro Q
  induction Q with
  | nil => intro P; exact Reach.of_eq (by simp)
  | cons c Q ih =>
    intro P
    have hX : (P.reverse.map up ++ .s6 :: Mid).all c4567 = true := by
      simp only [List.all_append, List.all_cons, all_up c4567 rfl rfl, hMid]
      rfl
    have h1 := copyN_one c (LL := Q.map lo ++ Z) (by simp [hZ]) hX S
    have h2 := ih (P ++ [c])
    refine h1.trans (Eq.mpr ?_ h2)
    simp

/-! ## 5. 1 マクロステップ -/

/-- 先頭が Y、相 m ≥ 1: begin → case_y_1（$ の左の区切り 0 が ∗ なので続行）→ case_y_2 →
    case_y_n（相マーカー b まで左へ、b を ∗ に）→ copy_start。 -/
theorem frontY (C : CTSH) (m : Nat) (hm : m ≠ 0) (rm v : List Ch) :
    Reach1 T (rep C m rm (.Y :: v))
      (zl .s0 (.go .q4) ((prod C m).map lo ++ (.s0 :: Hi C m).reverse)
        (([] : List Ch).reverse.map up ++ .s6 :: (Lo C m ++ .s7 :: rm.map up) ++ .s1 :: v.map lo)) := by
  rw [rep_eq]
  simp only [List.map_cons, zr]
  have hU4 := all_up c4567 rfl rfl rm
  have hU := all_up c457 rfl rfl rm
  have hLC := all_LoCore c4567 rfl rfl rfl C m
  rw [show (Sy.s0 :: RA C m ++ .s7 :: rm.map up).reverse =
      ((rm.map up).reverse ++ [.s7]) ++ .s6 ::
        (Sy.s0 :: Hi C m ++ (prod C m).reverse.map lo ++ .s0 :: LoCore C m).reverse by
    simp [RA, Lo_ne C m hm]]
  refine (runL1g (T := T) (p := .q0) (q := .q1) (h := .s1) (t := .s1) (by decide) id
    (ofAll p_q1 (by simp [hU] <;> decide)) .s6 _ _).trans ?_
  rw [show (((rm.map up).reverse ++ [Sy.s7]).map id).reverse ++ .s1 :: v.map lo =
      (.s7 :: rm.map up) ++ .s1 :: v.map lo by simp]
  refine (runRg (T := T) (p := .q1) (q := .q2) (h := .s6) (t := .s6) (by decide) id
    (ofAll p_q2 (by simp [hU] <;> decide)) _ .s1 _).trans ?_
  rw [show ((Sy.s7 :: rm.map up).map id).reverse ++ .s6 ::
        (Sy.s0 :: Hi C m ++ (prod C m).reverse.map lo ++ .s0 :: LoCore C m).reverse =
      ((rm.map up).reverse ++ .s7 :: .s6 :: (LoCore C m).reverse) ++ .s0 ::
        (Sy.s0 :: Hi C m ++ (prod C m).reverse.map lo).reverse by simp]
  refine (runLg (T := T) (p := .q2) (q := .q3) (h := .s1) (t := .s1) (by decide) id
    (ofAll p_q3 (by simp [hU4, hLC] <;> decide)) .s0 _ _).trans ?_
  refine (Reach.step (stepL' (T := T) (p := .q3) (h := .s0) (t := .s6) (q := .go .q4) (by decide)
    (L := (Sy.s0 :: Hi C m ++ (prod C m).reverse.map lo).reverse) (by simp) _)).trans ?_
  exact Reach.of_eq (by simp [Lo_ne C m hm])

/-- 先頭が N（任意の相）: begin で n → n′、case_y_n で相マーカーまで左へ、b を ∗ に → copy_start。 -/
theorem frontN (C : CTSH) (m : Nat) (rm v : List Ch) :
    Reach1 T (rep C m rm (.N :: v))
      (zl .s0 (.go .q4) ((prod C m).map lo ++ (.s0 :: Hi C m).reverse)
        (([] : List Ch).reverse.map up ++ .s6 :: (Lo C m ++ .s7 :: rm.map up) ++ .s3 :: v.map lo)) := by
  rw [rep_eq]
  simp only [List.map_cons, zr]
  have hU4 := all_up c4567 rfl rfl rm
  have hL := all_Lo c4567 rfl rfl rfl C m
  rw [show (Sy.s0 :: RA C m ++ .s7 :: rm.map up).reverse =
      ((rm.map up).reverse ++ .s7 :: (Lo C m).reverse) ++ .s0 ::
        (Sy.s0 :: Hi C m ++ (prod C m).reverse.map lo).reverse by
    simp [RA]]
  refine (runL1g (T := T) (p := .q0) (q := .q3) (h := .s2) (t := .s3) (by decide) id
    (ofAll p_q3 (by simp [hU4, hL] <;> decide)) .s0 _ _).trans ?_
  refine (Reach.step (stepL' (T := T) (p := .q3) (h := .s0) (t := .s6) (q := .go .q4) (by decide)
    (L := (Sy.s0 :: Hi C m ++ (prod C m).reverse.map lo).reverse) (by simp) _)).trans ?_
  exact Reach.of_eq (by simp)

/-- 印をつけた先頭記号（y はそのまま、n は n′）。 -/
def hd : Ch → Sy
  | .Y => .s1
  | .N => .s3

theorem q9_hd (c : Ch) : (⟨.q9, hd c, up c, .R, .go .q0⟩ : Rule St Ps Sy) ∈ T := by
  cases c <;> decide

/-- 相の終わり: 次の区切りを新しい相マーカーに（m = k−1 なら左端で折り返し、規則領域を小文字に戻して
    区切り 0 を相マーカーに）、copy_end で先頭まで右へ、先頭を大文字にして begin。 -/
theorem finish (C : CTSH) (m : Nat) (hm : m ≤ C.length) (rm : List Ch) (c : Ch) (v : List Ch) :
    Reach T (zl .s0 (.go .q4) (.s0 :: Hi C m).reverse
        ((prod C m).reverse.map up ++ .s6 :: (Lo C m ++ .s7 :: rm.map up) ++ hd c :: v.map lo))
      (rep C ((m + 1) % C.k) (rm ++ [c]) v) := by
  have hU4 := all_up c4567 rfl rfl rm
  rcases Nat.lt_or_ge m C.length with h | h
  · -- 次の区切り m+1 がある
    rw [Nat.mod_eq_of_lt (by simp [CTSH.k]; omega), rep_eq, Hi_step C m h]
    rw [show (Sy.s0 :: (Hi C (m + 1) ++ (prod C (m + 1)).reverse.map lo ++ [.s6])).reverse =
        .s6 :: (Sy.s0 :: Hi C (m + 1) ++ (prod C (m + 1)).reverse.map lo).reverse by simp]
    simp only [zl]
    rw [show (prod C m).reverse.map up ++ .s6 :: (Lo C m ++ .s7 :: rm.map up) ++ hd c :: v.map lo =
        ((prod C m).reverse.map up ++ .s6 :: Lo C m ++ .s7 :: rm.map up) ++ hd c :: v.map lo by simp]
    refine (runRg (T := T) (p := .q4) (q := .q9) (h := .s6) (t := .s0) (by decide) id
      (ofAll p_q9 (by simp [all_up c4567 rfl rfl, all_Lo c4567 rfl rfl rfl] <;> decide)) _ _ _).trans ?_
    refine (Reach.step (stepR' (q9_hd c) _ _)).trans ?_
    apply Reach.of_eq
    congr 1
    simp [RA, Lo_step C m hm]
  · -- m = k − 1: 1 周の終わり
    have hmk : m = C.length := by omega
    subst hmk
    rw [show (C.length + 1) % C.k = 0 by simp [CTSH.k], rep_eq, Hi_len]
    simp only [zl, List.reverse_cons, List.reverse_nil, List.nil_append]
    rw [show (prod C C.length).reverse.map up ++ .s6 :: (Lo C C.length ++ .s7 :: rm.map up) ++
          hd c :: v.map lo =
        ((prod C C.length).reverse.map up ++ .s6 :: Lo C C.length) ++ .s7 ::
          (rm.map up ++ hd c :: v.map lo) by simp]
    refine (runRg (T := T) (p := .q4) (q := .q0) (h := .s0) (t := .s0) (by decide) g0
      (ofAll p_q0 (by simp [all_up c456 rfl rfl, all_Lo c456 rfl rfl rfl] <;> decide)) [] .s7 _).trans ?_
    rw [← Lo_step C C.length (Nat.le_refl _), Lo_full_g0]
    rw [show (Hi C 0 ++ [Sy.s6]).reverse ++ [Sy.s0] = .s6 :: ((Hi C 0).reverse ++ [.s0]) by simp]
    refine (Reach.step (stepL (T := T) (p := .q0) (h := .s7) (t := .s7) (q := .go .q4) (by decide) _ _ _)).trans ?_
    rw [show Sy.s7 :: (rm.map up ++ hd c :: v.map lo) = (.s7 :: rm.map up) ++ hd c :: v.map lo by simp]
    refine (runRg (T := T) (p := .q4) (q := .q9) (h := .s6) (t := .s0) (by decide) id
      (ofAll p_q9 (by simp [hU4] <;> decide)) _ _ _).trans ?_
    refine (Reach.step (stepR' (q9_hd c) _ _)).trans ?_
    apply Reach.of_eq
    congr 1
    simp [RA, prod, Lo_zero]

theorem macroY (C : CTSH) {m : Nat} (h0 : m ≠ 0) (hk : m < C.k) (rm v : List Ch) :
    Reach1 T (rep C m rm (.Y :: v)) (rep C ((m + 1) % C.k) (rm ++ [.Y]) (v ++ prod C m)) := by
  have hmk : m ≤ C.length := by simp [CTSH.k] at hk; omega
  refine (frontY C m h0 rm v).trans ?_
  have hZ : (Sy.s0 :: Hi C m).reverse ≠ [] := by simp
  have hL := copyY_loop _ hZ (Lo C m ++ .s7 :: rm.map up)
    (by simp [all_Lo c4567 rfl rfl rfl, all_up c4567 rfl rfl] <;> decide) (prod C m) [] (v.map lo)
    (all_lo cNot03 rfl rfl v)
  refine hL.trans ?_
  have hf := finish C m hmk rm .Y (v ++ prod C m)
  simp only [hd, List.map_append] at hf
  refine Eq.mpr ?_ hf
  simp

theorem macroN (C : CTSH) {m : Nat} (hk : m < C.k) (rm v : List Ch) :
    Reach1 T (rep C m rm (.N :: v)) (rep C ((m + 1) % C.k) (rm ++ [.N]) v) := by
  have hmk : m ≤ C.length := by simp [CTSH.k] at hk; omega
  refine (frontN C m rm v).trans ?_
  have hZ : (Sy.s0 :: Hi C m).reverse ≠ [] := by simp
  have hL := copyN_loop _ hZ (Lo C m ++ .s7 :: rm.map up)
    (by simp [all_Lo c4567 rfl rfl rfl, all_up c4567 rfl rfl] <;> decide) (v.map lo) (prod C m) []
  refine hL.trans ?_
  have hf := finish C m hmk rm .N v
  simp only [hd] at hf
  refine Eq.mpr ?_ hf
  simp

/-! ## 6. 停止 -/

theorem halt_null (C : CTSH) (m : Nat) (rm : List Ch) :
    Step T (rep C m rm []) (finCfg C [] m rm) := by
  rw [rep_eq]
  simp only [List.map_nil, zr]
  refine (congrArg (Step T _) ?_).mp (stepZ (T := T) (p := .q0) (h := .s0) (t := .s0) (q := .halt .h0)
    (by decide) _ [])
  simp only [zc, finCfg, tapeOf, tapeList, List.map_nil, List.append_nil]
  congr 1
  · simp; omega
  · rw [List.reverse_reverse]; exact tp_trail _

theorem halt_Y (C : CTSH) (rm v : List Ch) :
    Reach1 T (rep C 0 rm (.Y :: v)) (finCfg C (.Y :: v) 0 rm) := by
  rw [rep_eq]
  simp only [List.map_cons, zr]
  have hU := all_up c457 rfl rfl rm
  rw [show (Sy.s0 :: RA C 0 ++ .s7 :: rm.map up).reverse =
      ((rm.map up).reverse ++ [.s7]) ++ .s0 :: (Sy.s0 :: Hi C 0).reverse by
    simp [RA, prod, Lo_zero]]
  refine (runL1g (T := T) (p := .q0) (q := .q1) (h := .s1) (t := .s1) (by decide) id
    (ofAll p_q1 (by simp [hU] <;> decide)) .s0 _ _).trans ?_
  refine (Reach.step (stepZ (T := T) (p := .q1) (h := .s0) (t := .s0) (q := .halt .h1) (by decide) _ _)).trans ?_
  apply Reach.of_eq
  simp only [zc, finCfg, tapeOf, tapeList, List.map_cons]
  congr 1
  · simp [RA, prod, Lo_zero]
  · simp [RA, prod, Lo_zero, lo]

theorem finCfg_halted (C : CTSH) (vf : List Ch) (mf : Nat) (rm : List Ch) :
    Halted T (finCfg C vf mf rm) := by
  intro c' ⟨r, _, hst, _⟩
  cases vf <;> simp [finCfg] at hst

/-! ## 7. 主定理 -/

/-- **主定理**（URTM(10,8) は任意の CTSH を模倣する）。任意の CTSH C（周期 k = |C| + 1、
    生成規則 C = [w₁, …, w_{k−1}]）と任意の初期語 w について、U10_8 = `T` を
    Morita の初期配置 `encC C w` から動かすと:

    1. C が (w, 0) から n ステップで停止 ID (vf, mf) に達するなら、U10_8 は n ステップ以上で停止し、
       停止配置は `finCfg C vf mf rm`: vf = λ なら疑似状態 null、vf = Y v なら halt で、テープは
       `b · RA(mf) · $ · (消去済みの大文字列 rm) · ϕ₁(vf) · b b …`。
    2. 逆に U10_8 が `encC C w` から停止するなら、C も (w, 0) から停止し、停止配置は 1 の形。
    3. C が停止しない ⇔ U10_8 が停止しない。 -/
theorem urtm10_8_simulates_ctsh (C : CTSH) (w : List Ch) :
    (∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) →
      ∃ N rm, n ≤ N ∧ HaltsIn T N (encC C w) (finCfg C vf mf rm)) ∧
    (∀ N e, HaltsIn T N (encC C w) e →
      ∃ n vf mf rm, CHaltsIn C n (w, 0) (vf, mf) ∧ e = finCfg C vf mf rm) ∧
    ((∀ n f, ¬ CHaltsIn C n (w, 0) f) ↔ (∀ N e, ¬ HaltsIn T N (encC C w) e)) :=
  simulates_of_steps C (rep C) (finCfg C) hD (macroY C) (macroN C) (halt_Y C)
    (fun m rm => Reach1.of_step (halt_null C m rm) (Reach.refl _)) (finCfg_halted C) w

/-! ## 8. 系: URTM(4,88)（定理 A の変換 `conv T qs ss`）も任意の CTSH を模倣する -/

/-- **系**。T' = `conv T qs ss`（定理 A、4 状態・記号は 88 要素の `symUniverse 10 ss` に入る・決定的可逆）を
    符号化 `E = enc T (canonOff T qs)` を通して見ると、主定理と同じ主張が成り立つ。 -/
theorem urtm4_88_simulates_ctsh (C : CTSH) (w : List Ch) :
    let T' := conv T qs ss
    let E := enc T (canonOff T qs)
    Deterministic T' ∧ Reversible T' ∧
    (∀ ρ ∈ T', ρ.s ∈ symUniverse 10 ss ∧ ρ.t ∈ symUniverse 10 ss) ∧
    (symUniverse 10 ss).length = 88 ∧
    (∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) →
      ∃ N rm, n ≤ N ∧ HaltsIn T' N (E (encC C w)) (E (finCfg C vf mf rm))) ∧
    (∀ N e, HaltsIn T' N (E (encC C w)) e →
      ∃ n vf mf rm, CHaltsIn C n (w, 0) (vf, mf) ∧ e = E (finCfg C vf mf rm)) ∧
    ((∀ n f, ¬ CHaltsIn C n (w, 0) f) ↔ (∀ N e, ¬ HaltsIn T' N (E (encC C w)) e)) := by
  intro T' E
  obtain ⟨hDet, hRev, -, -, hF, hB, hDiv, hSy⟩ := conv_main hW hD hR hQ hS
  refine ⟨hDet, hRev, card.1 ▸ hSy, card.2.2.1, simulates_enc hF hB hDiv (urtm10_8_simulates_ctsh C w)⟩

end URTM.CTSH.U10_8
