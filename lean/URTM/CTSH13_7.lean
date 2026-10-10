/-
  URTM(13,7)（Morita 2017, §7.3.1, Table 7.1）が任意の CTSH を模倣することの一般証明。

  機械の**型に依存しない**形（CTSH17_5.lean と同じ設計）: 状態・記号・疑似状態の名前（`Names`）と、
  Table 7.1 の 59 本の五つ組（`rules`、停止の 2 本を含む）がすべて機械 T に含まれること（`hT`）、
  逆向きでは T の決定性だけを仮定する。`CTSH13_7Main.lean` で生成モジュール `URTM.Gen.K13_7` に
  具体化し、`rules` = T（集合として）を `decide` で確かめる。

  記号 b y n Y N ∗ $、状態 begin case_y_1 case_y_2 case_y_n copy_start copy_y_1..3 copy_n_1..3
  copy_end cycle_end、疑似状態 halt null（原典の名前）。

  不変量 `rep C m rm v`（CTSH の ID (v, m) と消去済みの記号列 rm）: 状態 begin、テープ

      b · RA(m) · $ · ϕ₁(rm) · ϕ₁(v) · b b …

  ヘッドは ϕ₁(v) の先頭（v = λ なら直後の b）。原典 p. 183 の初期 ID
  `b ϕ₁(w^R_{k−1}) ∗ ⋯ ∗ ϕ₁(w^R_1) ∗ b $ q_begin ϕ₁(v0) b` は `rep C 0 [] v0`。
  U13_7 では消去済みの記号は小文字のまま残り、処理中の先頭の記号だけが大文字 Y/N で印される
  （原典 p. 184「it is changed to the uppercase letter Y or N to indicate the leftmost position」）。
  先頭が N のときも copy_start は規則を 1 文字ずつ読むが、copy_*_1 が N に当たって引き返すので
  何も書き足されない（原典 p. 185, t = 315–316）。

  計画・補題の分解・検証の記録は docs/10_ctsh_all_lean_2026-09-26.md。mathlib 非依存。
  未証明の穴・新規公理・native_decide を使わない。
-/
import URTM.CTSHSim

namespace URTM.CTSH.U13_7

open URTM URTM.KState URTM.CTSH URTM.CTSH.Sim

/-! ## 0. 機械の名前と Table 7.1 -/

/-- U13_7 の記号・状態・疑似状態の名前。 -/
structure Names (St Ps Sy : Type) where
  b : Sy
  y : Sy
  n : Sy
  Y : Sy
  N : Sy
  st : Sy   -- ∗
  dl : Sy   -- $
  begin : St
  cy1 : St
  cy2 : St
  cyn : St
  cs : St
  cpy1 : St
  cpy2 : St
  cpy3 : St
  cpn1 : St
  cpn2 : St
  cpn3 : St
  ce : St
  cyc : St
  halt : Ps
  null : Ps

section
variable {St Ps Sy : Type} (nm : Names St Ps Sy)

/-- Table 7.1（urtm13-7.txt の五つ組を、記述ファイルの順に、名前で書いたもの）。
    `CTSH13_7Main.lean` で生成モジュールの表と集合として一致することを `decide` で確かめる。 -/
def rules : List (Rule St Ps Sy) :=
  let b := nm.b; let y := nm.y; let n := nm.n; let Y := nm.Y; let N := nm.N
  let s := nm.st; let d := nm.dl
  [ ⟨nm.begin, y, Y, .L, .go nm.cy1⟩,
    ⟨nm.begin, n, N, .L, .go nm.cyn⟩,
    ⟨nm.begin, b, b, .Z, .halt nm.null⟩,
    ⟨nm.cy1, y, y, .L, .go nm.cy1⟩,
    ⟨nm.cy1, n, n, .L, .go nm.cy1⟩,
    ⟨nm.cy1, d, d, .L, .go nm.cy1⟩,
    ⟨nm.cy1, s, s, .R, .go nm.cy2⟩,
    ⟨nm.cy1, b, b, .Z, .halt nm.halt⟩,
    ⟨nm.cy2, y, y, .R, .go nm.cy2⟩,
    ⟨nm.cy2, n, n, .R, .go nm.cy2⟩,
    ⟨nm.cy2, d, d, .R, .go nm.cy2⟩,
    ⟨nm.cy2, Y, Y, .L, .go nm.cyn⟩,
    ⟨nm.cyn, y, y, .L, .go nm.cyn⟩,
    ⟨nm.cyn, n, n, .L, .go nm.cyn⟩,
    ⟨nm.cyn, s, s, .L, .go nm.cyn⟩,
    ⟨nm.cyn, d, d, .L, .go nm.cyn⟩,
    ⟨nm.cyn, b, s, .L, .go nm.cs⟩,
    ⟨nm.cs, y, b, .R, .go nm.cpy1⟩,
    ⟨nm.cs, n, b, .R, .go nm.cpn1⟩,
    ⟨nm.cs, s, b, .R, .go nm.ce⟩,
    ⟨nm.cs, b, b, .R, .go nm.cyc⟩,
    ⟨nm.cpy1, y, y, .R, .go nm.cpy1⟩,
    ⟨nm.cpy1, n, n, .R, .go nm.cpy1⟩,
    ⟨nm.cpy1, s, s, .R, .go nm.cpy1⟩,
    ⟨nm.cpy1, Y, Y, .R, .go nm.cpy1⟩,
    ⟨nm.cpy1, N, N, .L, .go nm.cpy3⟩,
    ⟨nm.cpy1, d, d, .R, .go nm.cpy1⟩,
    ⟨nm.cpy1, b, y, .R, .go nm.cpy2⟩,
    ⟨nm.cpy2, b, b, .L, .go nm.cpy3⟩,
    ⟨nm.cpy3, y, y, .L, .go nm.cpy3⟩,
    ⟨nm.cpy3, n, n, .L, .go nm.cpy3⟩,
    ⟨nm.cpy3, s, s, .L, .go nm.cpy3⟩,
    ⟨nm.cpy3, Y, Y, .L, .go nm.cpy3⟩,
    ⟨nm.cpy3, d, d, .L, .go nm.cpy3⟩,
    ⟨nm.cpy3, b, y, .L, .go nm.cs⟩,
    ⟨nm.cpn1, y, y, .R, .go nm.cpn1⟩,
    ⟨nm.cpn1, n, n, .R, .go nm.cpn1⟩,
    ⟨nm.cpn1, s, s, .R, .go nm.cpn1⟩,
    ⟨nm.cpn1, Y, Y, .R, .go nm.cpn1⟩,
    ⟨nm.cpn1, N, N, .L, .go nm.cpn3⟩,
    ⟨nm.cpn1, d, d, .R, .go nm.cpn1⟩,
    ⟨nm.cpn1, b, n, .R, .go nm.cpn2⟩,
    ⟨nm.cpn2, b, b, .L, .go nm.cpn3⟩,
    ⟨nm.cpn3, y, y, .L, .go nm.cpn3⟩,
    ⟨nm.cpn3, n, n, .L, .go nm.cpn3⟩,
    ⟨nm.cpn3, s, s, .L, .go nm.cpn3⟩,
    ⟨nm.cpn3, Y, Y, .L, .go nm.cpn3⟩,
    ⟨nm.cpn3, d, d, .L, .go nm.cpn3⟩,
    ⟨nm.cpn3, b, n, .L, .go nm.cs⟩,
    ⟨nm.ce, y, y, .R, .go nm.ce⟩,
    ⟨nm.ce, n, n, .R, .go nm.ce⟩,
    ⟨nm.ce, s, s, .R, .go nm.ce⟩,
    ⟨nm.ce, d, d, .R, .go nm.ce⟩,
    ⟨nm.ce, Y, y, .R, .go nm.begin⟩,
    ⟨nm.ce, N, n, .R, .go nm.begin⟩,
    ⟨nm.cyc, y, y, .R, .go nm.cyc⟩,
    ⟨nm.cyc, n, n, .R, .go nm.cyc⟩,
    ⟨nm.cyc, s, s, .R, .go nm.cyc⟩,
    ⟨nm.cyc, d, d, .L, .go nm.cs⟩ ]

/-! ## 1. CTSH の符号化 -/

/-- ϕ₁: Y ↦ y, N ↦ n。 -/
def lo : Ch → Sy
  | .Y => nm.y
  | .N => nm.n

/-- 処理中の先頭の記号の印: Y ↦ Y, N ↦ N（大文字）。 -/
def up : Ch → Sy
  | .Y => nm.Y
  | .N => nm.N

/-- copy_c_1（右へ）・copy_c_2・copy_c_3（左へ）の状態。 -/
def c1 : Ch → St
  | .Y => nm.cpy1
  | .N => nm.cpn1
def c2 : Ch → St
  | .Y => nm.cpy2
  | .N => nm.cpn2
def c3 : Ch → St
  | .Y => nm.cpy3
  | .N => nm.cpn3

/-- 規則領域 RA(m) = H(m) · ϕ₁(w^R_m) · b · Lo(m)（b が相マーカー）。 -/
abbrev RA (C : CTSH) (m : Nat) : List Sy := Sim.RA (lo nm) nm.st nm.b C m
abbrev Hi (C : CTSH) (m : Nat) : List Sy := Sim.Hi (lo nm) nm.st C m
abbrev Lo (C : CTSH) (m : Nat) : List Sy := Sim.Lo (lo nm) nm.st C m
abbrev LoCore (C : CTSH) (m : Nat) : List Sy := Sim.LoCore (lo nm) nm.st C m

/-- テープの中身（左端が位置 0）: b · RA(m) · $ · ϕ₁(rm) · ϕ₁(v)。以降は b。 -/
def tapeList (C : CTSH) (m : Nat) (rm v : List Ch) : List Sy :=
  nm.b :: RA nm C m ++ nm.dl :: rm.map (lo nm) ++ v.map (lo nm)

/-- CTSH の ID (v, m) と消去済みの記号列 rm を表す配置: 状態 begin、ヘッドは v の先頭。 -/
def rep (C : CTSH) (m : Nat) (rm v : List Ch) : Cfg St Ps Sy :=
  { st := .go nm.begin, pos := (RA nm C m).length + 2 + rm.length, tape := tp nm.b (tapeList nm C m rm v) }

/-- **Morita の符号化**（原典 p. 183）: `b ϕ₁(w^R_{k−1}) ∗ ⋯ ∗ ϕ₁(w^R_1) ∗ b $ q_begin ϕ₁(w) b`。 -/
def encC (C : CTSH) (w : List Ch) : Cfg St Ps Sy := rep nm C 0 [] w

/-- 停止配置のテープ（リスト）。
    * 最終 ID (λ, m): begin が末尾の b を読んで null。テープは `rep` のまま `b · RA(m) · $ · ϕ₁(rm)`。
    * 最終 ID (Y v, 0): begin が先頭の y を Y に変え、case_y_1 が $ を越えて区切り 0 の b で halt。
      テープは `b · RA(0) · $ · ϕ₁(rm) · Y · ϕ₁(v)`（原典 p. 185「the final string YNY of Ĉ2 is obtained
      as a suffix … starting from the symbol Y」）。 -/
def finList (C : CTSH) (vf : List Ch) (mf : Nat) (rm : List Ch) : List Sy :=
  match vf with
  | [] => tapeList nm C mf rm []
  | _ :: v => nm.b :: RA nm C 0 ++ nm.dl :: rm.map (lo nm) ++ nm.Y :: v.map (lo nm)

/-- 停止配置。(λ, m) なら疑似状態 null でヘッドは末尾の b、(Y v, 0) なら halt でヘッドは区切り 0。 -/
def finCfg (C : CTSH) (vf : List Ch) (mf : Nat) (rm : List Ch) : Cfg St Ps Sy :=
  match vf with
  | [] => { st := .halt nm.null, pos := (RA nm C mf).length + 2 + rm.length,
            tape := tp nm.b (finList nm C [] mf rm) }
  | c :: v => { st := .halt nm.halt, pos := (RA nm C 0).length,
                tape := tp nm.b (finList nm C (c :: v) 0 rm) }

end

/-! ## 2. 記号クラス -/

section Sets
variable {St Ps Sy : Type} (nm : Names St Ps Sy)

/-- {y, n, $}（case_y_1・case_y_2 が通過する）。 -/
def YND (x : Sy) : Prop := x = nm.y ∨ x = nm.n ∨ x = nm.dl
/-- {y, n, ∗}（cycle_end が通過する）。 -/
def YNS (x : Sy) : Prop := x = nm.y ∨ x = nm.n ∨ x = nm.st
/-- {y, n, ∗, $}（case_y_n・copy_end が通過する）。 -/
def YNSD (x : Sy) : Prop := x = nm.y ∨ x = nm.n ∨ x = nm.st ∨ x = nm.dl
/-- {y, n, ∗, $, Y}（copy_*_1・copy_*_3 が通過する）。 -/
def YNSDY (x : Sy) : Prop := x = nm.y ∨ x = nm.n ∨ x = nm.st ∨ x = nm.dl ∨ x = nm.Y

variable {nm}

theorem lo_YND : ∀ c, YND nm (lo nm c) := by intro c; cases c <;> simp [YND, lo]
theorem lo_YNS : ∀ c, YNS nm (lo nm c) := by intro c; cases c <;> simp [YNS, lo]
theorem lo_YNSD : ∀ c, YNSD nm (lo nm c) := by intro c; cases c <;> simp [YNSD, lo]
theorem lo_YNSDY : ∀ c, YNSDY nm (lo nm c) := by intro c; cases c <;> simp [YNSDY, lo]

end Sets

/-! ## 3. 規則表から読み取る 1 ステップと掃引 -/

section Main
variable {St Ps Sy : Type} {nm : Names St Ps Sy} {T : Machine St Ps Sy}
  (hT : ∀ r ∈ rules nm, r ∈ T)
include hT

set_option hygiene false in
/-- 規則 `r` が Table 7.1 にあるので T にある。 -/
macro "rl" : tactic =>
  `(tactic| (apply hT; simp only [rules]; repeat (first | exact List.Mem.head _ | apply List.Mem.tail)))

theorem p_cy1 : ∀ x, YND nm x → (⟨nm.cy1, x, x, .L, .go nm.cy1⟩ : Rule St Ps Sy) ∈ T := by
  rintro x (rfl | rfl | rfl) <;> rl
theorem p_cy2 : ∀ x, YND nm x → (⟨nm.cy2, x, x, .R, .go nm.cy2⟩ : Rule St Ps Sy) ∈ T := by
  rintro x (rfl | rfl | rfl) <;> rl
theorem p_cyc : ∀ x, YNS nm x → (⟨nm.cyc, x, x, .R, .go nm.cyc⟩ : Rule St Ps Sy) ∈ T := by
  rintro x (rfl | rfl | rfl) <;> rl
theorem p_cyn : ∀ x, YNSD nm x → (⟨nm.cyn, x, x, .L, .go nm.cyn⟩ : Rule St Ps Sy) ∈ T := by
  rintro x (rfl | rfl | rfl | rfl) <;> rl
theorem p_ce : ∀ x, YNSD nm x → (⟨nm.ce, x, x, .R, .go nm.ce⟩ : Rule St Ps Sy) ∈ T := by
  rintro x (rfl | rfl | rfl | rfl) <;> rl
theorem p_cpy1 : ∀ x, YNSDY nm x → (⟨nm.cpy1, x, x, .R, .go nm.cpy1⟩ : Rule St Ps Sy) ∈ T := by
  rintro x (rfl | rfl | rfl | rfl | rfl) <;> rl
theorem p_cpy3 : ∀ x, YNSDY nm x → (⟨nm.cpy3, x, x, .L, .go nm.cpy3⟩ : Rule St Ps Sy) ∈ T := by
  rintro x (rfl | rfl | rfl | rfl | rfl) <;> rl
theorem p_cpn1 : ∀ x, YNSDY nm x → (⟨nm.cpn1, x, x, .R, .go nm.cpn1⟩ : Rule St Ps Sy) ∈ T := by
  rintro x (rfl | rfl | rfl | rfl | rfl) <;> rl
theorem p_cpn3 : ∀ x, YNSDY nm x → (⟨nm.cpn3, x, x, .L, .go nm.cpn3⟩ : Rule St Ps Sy) ∈ T := by
  rintro x (rfl | rfl | rfl | rfl | rfl) <;> rl

theorem r_cs (c : Ch) : (⟨nm.cs, lo nm c, nm.b, .R, .go (c1 nm c)⟩ : Rule St Ps Sy) ∈ T := by
  cases c <;> rl
theorem r_c1b (c : Ch) : (⟨c1 nm c, nm.b, lo nm c, .R, .go (c2 nm c)⟩ : Rule St Ps Sy) ∈ T := by
  cases c <;> rl
theorem r_c1N (c : Ch) : (⟨c1 nm c, nm.N, nm.N, .L, .go (c3 nm c)⟩ : Rule St Ps Sy) ∈ T := by
  cases c <;> rl
theorem r_c2 (c : Ch) : (⟨c2 nm c, nm.b, nm.b, .L, .go (c3 nm c)⟩ : Rule St Ps Sy) ∈ T := by
  cases c <;> rl
theorem r_c3 (c : Ch) : (⟨c3 nm c, nm.b, lo nm c, .L, .go nm.cs⟩ : Rule St Ps Sy) ∈ T := by
  cases c <;> rl
theorem p_c1 (c : Ch) : ∀ x, YNSDY nm x → (⟨c1 nm c, x, x, .R, .go (c1 nm c)⟩ : Rule St Ps Sy) ∈ T := by
  cases c
  · exact p_cpy1 hT
  · exact p_cpn1 hT
theorem p_c3 (c : Ch) : ∀ x, YNSDY nm x → (⟨c3 nm c, x, x, .L, .go (c3 nm c)⟩ : Rule St Ps Sy) ∈ T := by
  cases c
  · exact p_cpy3 hT
  · exact p_cpn3 hT
theorem r_ce (c : Ch) : (⟨nm.ce, up nm c, lo nm c, .R, .go nm.begin⟩ : Rule St Ps Sy) ∈ T := by
  cases c <;> rl

/-! ## 4. コピー -/

/-- 先頭が Y のとき（書き足す）: copy_start が規則の 1 文字 c を b で印し、copy_c_1 が右端の b まで行って
    c を書き、copy_c_2 が折り返し、copy_c_3 が印の b まで戻って c を書き戻す（原典 t = 35–56）。 -/
theorem copy_oneY (c : Ch) {LL : List Sy} (hLL : LL ≠ []) {R : List Sy}
    (hR : ∀ x ∈ R, YNSDY nm x) :
    Reach T (zc nm.b (.go nm.cs) LL (lo nm c) R)
      (zl nm.b (.go nm.cs) LL (lo nm c :: R ++ [lo nm c])) := by
  rw [← zc_trail _ _ _ R, ← zl_trail]
  have hR' : ∀ x ∈ R.reverse, YNSDY nm x := fa_rev hR
  refine (runR (r_cs hT c) (ofP (p_c1 hT c) hR) LL nm.b []).trans ?_
  rw [zc_nil]
  refine (Reach.step (stepR (r_c1b hT c) _ nm.b [])).trans ?_
  refine (Reach.step (stepL (r_c2 hT c) (lo nm c) _ [])).trans ?_
  refine (sweepL (X := lo nm c :: R.reverse)
    (ofP (p_c3 hT c) (fa_cons (lo_YNSDY c) hR')) nm.b LL [nm.b]).trans ?_
  refine (Reach.step (stepL' (r_c3 hT c) hLL _)).trans ?_
  exact Reach.of_eq (by simp)

/-- 先頭が N のとき（書き足さない）: copy_c_1 が N に当たって引き返し、copy_c_3 が印の b に c を書き戻す
    （原典 t = 303–316）。 -/
theorem copy_oneN (c : Ch) {LL : List Sy} (hLL : LL ≠ []) {R₁ : List Sy}
    (hR : ∀ x ∈ R₁, YNSDY nm x) (R₂ : List Sy) :
    Reach T (zc nm.b (.go nm.cs) LL (lo nm c) (R₁ ++ nm.N :: R₂))
      (zl nm.b (.go nm.cs) LL (lo nm c :: R₁ ++ nm.N :: R₂)) := by
  refine (runR (r_cs hT c) (ofP (p_c1 hT c) hR) LL nm.N R₂).trans ?_
  refine (Reach.step (stepL' (r_c1N hT c) (L := R₁.reverse ++ nm.b :: LL) (by simp) R₂)).trans ?_
  refine (sweepL (X := R₁.reverse) (ofP (p_c3 hT c) (fa_rev hR)) nm.b LL (nm.N :: R₂)).trans ?_
  refine (Reach.step (stepL' (r_c3 hT c) hLL _)).trans ?_
  exact Reach.of_eq (by simp)

theorem copy_loopY (Z : List Sy) (hZ : Z ≠ []) :
    ∀ (Q P : List Ch) (S : List Sy), (∀ x ∈ S, YNSDY nm x) →
    Reach T (zl nm.b (.go nm.cs) (Q.map (lo nm) ++ Z) (P.reverse.map (lo nm) ++ S))
      (zl nm.b (.go nm.cs) Z ((P ++ Q).reverse.map (lo nm) ++ S ++ Q.map (lo nm))) := by
  intro Q
  induction Q with
  | nil => intro P S _; exact Reach.of_eq (by simp)
  | cons c Q ih =>
    intro P S hS
    have hR : ∀ x ∈ P.reverse.map (lo nm) ++ S, YNSDY nm x := fa_app (fa_map lo_YNSDY _) hS
    have h1 := copy_oneY hT c (LL := Q.map (lo nm) ++ Z) (by simp [hZ]) hR
    have h2 := ih (P ++ [c]) (S ++ [lo nm c]) (fa_app hS (fa_cons (lo_YNSDY c) fa_nil))
    refine h1.trans (Eq.mpr ?_ h2)
    simp

theorem copy_loopN (Z : List Sy) (hZ : Z ≠ []) (S₂ : List Sy) :
    ∀ (Q P : List Ch) (S₁ : List Sy), (∀ x ∈ S₁, YNSDY nm x) →
    Reach T (zl nm.b (.go nm.cs) (Q.map (lo nm) ++ Z) (P.reverse.map (lo nm) ++ S₁ ++ nm.N :: S₂))
      (zl nm.b (.go nm.cs) Z ((P ++ Q).reverse.map (lo nm) ++ S₁ ++ nm.N :: S₂)) := by
  intro Q
  induction Q with
  | nil => intro P S₁ _; exact Reach.of_eq (by simp)
  | cons c Q ih =>
    intro P S₁ hS
    have hR : ∀ x ∈ P.reverse.map (lo nm) ++ S₁, YNSDY nm x := fa_app (fa_map lo_YNSDY _) hS
    have h1 := copy_oneN hT c (LL := Q.map (lo nm) ++ Z) (by simp [hZ]) hR S₂
    have h1' : Reach T
        (zl nm.b (.go nm.cs) ((c :: Q).map (lo nm) ++ Z) (P.reverse.map (lo nm) ++ S₁ ++ nm.N :: S₂))
        (zl nm.b (.go nm.cs) (Q.map (lo nm) ++ Z)
          ((P ++ [c]).reverse.map (lo nm) ++ S₁ ++ nm.N :: S₂)) := by
      refine Eq.mpr ?_ h1; simp [zl]
    have h2 := ih (P ++ [c]) S₁ hS
    refine h1'.trans (Eq.mpr ?_ h2)
    simp

/-! ## 5. 1 マクロステップ -/

omit hT in
theorem rep_eq (C : CTSH) (m : Nat) (rm v : List Ch) :
    rep nm C m rm v =
      zr nm.b (.go nm.begin) (nm.b :: RA nm C m ++ nm.dl :: rm.map (lo nm)).reverse (v.map (lo nm)) := by
  rw [zr_eq]; simp only [rep, tapeList]; congr 1 <;> simp; omega

/-- 先頭が Y、相 m ≥ 1（原典 t = 7–18）: begin が y を Y に、case_y_1 が $ を越えて区切り 0 の ∗ を見て
    case_y_2 で Y まで戻り、case_y_n が相マーカー b まで左へ行って ∗ に → copy_start。 -/
theorem frontY (C : CTSH) (m : Nat) (hm : m ≠ 0) (rm v : List Ch) :
    Reach1 T (rep nm C m rm (.Y :: v))
      (zl nm.b (.go nm.cs) ((prod C m).map (lo nm) ++ (nm.b :: Hi nm C m).reverse)
        (nm.st :: Lo nm C m ++ nm.dl :: rm.map (lo nm) ++ nm.Y :: v.map (lo nm))) := by
  rw [rep_eq]
  simp only [List.map_cons, zr, lo]
  rw [show (nm.b :: RA nm C m ++ nm.dl :: rm.map (lo nm)).reverse =
      ((rm.map (lo nm)).reverse ++ [nm.dl]) ++ nm.st :: ((LoCore nm C m).reverse ++ nm.b ::
        ((prod C m).map (lo nm) ++ (nm.b :: Hi nm C m).reverse)) by
    simp [RA, Sim.RA, Sim.Lo_ne C m hm]]
  refine (runL1 (p := nm.begin) (q := nm.cy1) (h := nm.y) (t := nm.Y) (by rl)
    (ofP (p_cy1 hT) (fa_app (fa_rev (fa_map lo_YND _)) (fa_cons (by simp [YND]) fa_nil)))
    nm.st _ _).trans ?_
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.reverse_reverse, List.cons_append]
  refine (runR (p := nm.cy1) (q := nm.cy2) (h := nm.st) (t := nm.st) (by rl)
    (X := nm.dl :: rm.map (lo nm))
    (ofP (p_cy2 hT) (fa_cons (by simp [YND]) (fa_map lo_YND _))) _ nm.Y _).trans ?_
  rw [show (nm.dl :: rm.map (lo nm)).reverse ++ nm.st :: ((LoCore nm C m).reverse ++ nm.b ::
        ((prod C m).map (lo nm) ++ ((Hi nm C m).reverse ++ [nm.b]))) =
      ((rm.map (lo nm)).reverse ++ nm.dl :: nm.st :: (LoCore nm C m).reverse) ++ nm.b ::
        ((prod C m).map (lo nm) ++ ((Hi nm C m).reverse ++ [nm.b])) by simp]
  refine (runL (p := nm.cy2) (q := nm.cyn) (h := nm.Y) (t := nm.Y) (by rl)
    (ofP (p_cyn hT) (fa_app (fa_rev (fa_map lo_YNSD _)) (fa_cons (by simp [YNSD])
      (fa_cons (by simp [YNSD]) (fa_rev (LoCore_mem lo_YNSD (by simp [YNSD]) C m))))))
    nm.b _ _).trans ?_
  refine (Reach.step (stepL' (p := nm.cyn) (h := nm.b) (t := nm.st) (q := .go nm.cs) (by rl)
    (L := (prod C m).map (lo nm) ++ ((Hi nm C m).reverse ++ [nm.b])) (by simp) _)).trans ?_
  exact Reach.of_eq (by simp [Sim.Lo_ne C m hm])

/-- 先頭が N（任意の相。原典 t = 0–7, 291–303）: begin が n を N に、case_y_n が相マーカー b まで左へ行って
    ∗ に → copy_start。 -/
theorem frontN (C : CTSH) (m : Nat) (rm v : List Ch) :
    Reach1 T (rep nm C m rm (.N :: v))
      (zl nm.b (.go nm.cs) ((prod C m).map (lo nm) ++ (nm.b :: Hi nm C m).reverse)
        (nm.st :: Lo nm C m ++ nm.dl :: rm.map (lo nm) ++ nm.N :: v.map (lo nm))) := by
  rw [rep_eq]
  simp only [List.map_cons, zr, lo]
  rw [show (nm.b :: RA nm C m ++ nm.dl :: rm.map (lo nm)).reverse =
      ((rm.map (lo nm)).reverse ++ nm.dl :: (Lo nm C m).reverse) ++ nm.b ::
        ((prod C m).map (lo nm) ++ (nm.b :: Hi nm C m).reverse) by simp [RA, Sim.RA]]
  refine (runL1 (p := nm.begin) (q := nm.cyn) (h := nm.n) (t := nm.N) (by rl)
    (ofP (p_cyn hT) (fa_app (fa_rev (fa_map lo_YNSD _)) (fa_cons (by simp [YNSD])
      (fa_rev (Lo_mem lo_YNSD (by simp [YNSD]) C m)))))
    nm.b _ _).trans ?_
  refine (Reach.step (stepL' (p := nm.cyn) (h := nm.b) (t := nm.st) (q := .go nm.cs) (by rl)
    (L := (prod C m).map (lo nm) ++ (nm.b :: Hi nm C m).reverse) (by simp) _)).trans ?_
  exact Reach.of_eq (by simp)

/-- 相の終わり（先頭が Y でも N でも同じ。原典 t = 56–64, 174–185）: copy_start が次の区切り ∗ を b
    （新しい相マーカー）にして copy_end が印の Y/N を小文字に戻して begin。m = k−1 なら左端の b で
    cycle_end に入り、$ で折り返して区切り 0 を相マーカーに。 -/
theorem finish (C : CTSH) (m : Nat) (hk : m ≤ C.length) (c : Ch) (rm v : List Ch) :
    Reach T (zl nm.b (.go nm.cs) (nm.b :: Hi nm C m).reverse
        ((prod C m).reverse.map (lo nm) ++ nm.st :: Lo nm C m ++ nm.dl :: rm.map (lo nm) ++
          up nm c :: v.map (lo nm)))
      (rep nm C ((m + 1) % C.k) (rm ++ [c]) v) := by
  rcases Nat.lt_or_ge m C.length with h | h
  · rw [Nat.mod_eq_of_lt (by simp [CTSH.k]; omega), rep_eq, Hi, Sim.Hi_step C m h]
    rw [show (nm.b :: (Sim.Hi (lo nm) nm.st C (m + 1) ++ (prod C (m + 1)).reverse.map (lo nm) ++
          [nm.st])).reverse =
        nm.st :: (nm.b :: Sim.Hi (lo nm) nm.st C (m + 1) ++ (prod C (m + 1)).reverse.map (lo nm)).reverse
        by simp]
    simp only [zl]
    rw [show (prod C m).reverse.map (lo nm) ++ nm.st :: Lo nm C m ++ nm.dl :: rm.map (lo nm) ++
          up nm c :: v.map (lo nm) =
        ((prod C m).reverse.map (lo nm) ++ nm.st :: Lo nm C m ++ nm.dl :: rm.map (lo nm)) ++
          up nm c :: v.map (lo nm) by simp]
    refine (runR (p := nm.cs) (q := nm.ce) (h := nm.st) (t := nm.b) (by rl)
      (ofP (p_ce hT) (fa_app (fa_app (fa_map lo_YNSD _) (fa_cons (by simp [YNSD])
        (Lo_mem lo_YNSD (by simp [YNSD]) C m))) (fa_cons (by simp [YNSD]) (fa_map lo_YNSD _))))
      _ _ _).trans ?_
    refine (Reach.step (stepR' (r_ce hT c) _ _)).trans ?_
    apply Reach.of_eq
    congr 1
    simp [RA, Sim.RA, Sim.Lo_step (lo := lo nm) (st := nm.st) C m hk]
  · have hmk : m = C.length := by omega
    subst hmk
    rw [show (C.length + 1) % C.k = 0 by simp [CTSH.k], rep_eq, Hi, Sim.Hi_len]
    simp only [zl, List.reverse_cons, List.reverse_nil, List.nil_append]
    have hLo := Sim.Lo_step (lo := lo nm) (st := nm.st) C C.length (Nat.le_refl _)
    rw [show (prod C C.length).reverse.map (lo nm) ++ nm.st :: Lo nm C C.length ++
          nm.dl :: rm.map (lo nm) ++ up nm c :: v.map (lo nm) =
        Lo nm C (C.length + 1) ++ nm.dl :: (rm.map (lo nm) ++ up nm c :: v.map (lo nm)) by
      simp [Lo, hLo]]
    refine (runR (p := nm.cs) (q := nm.cyc) (h := nm.b) (t := nm.b) (by rl)
      (ofP (p_cyc hT) (Lo_mem lo_YNS (by simp [YNS]) C _)) [] _ _).trans ?_
    rw [Sim.Lo_ne C (C.length + 1) (by omega)]
    rw [show (Sim.LoCore (lo nm) nm.st C (C.length + 1) ++ [nm.st]).reverse ++ [nm.b] =
        nm.st :: ((Sim.LoCore (lo nm) nm.st C (C.length + 1)).reverse ++ [nm.b]) by simp]
    refine (Reach.step (stepL (p := nm.cyc) (h := nm.dl) (t := nm.dl) (q := .go nm.cs) (by rl)
      _ _ _)).trans ?_
    rw [show nm.dl :: (rm.map (lo nm) ++ up nm c :: v.map (lo nm)) =
        (nm.dl :: rm.map (lo nm)) ++ up nm c :: v.map (lo nm) by simp]
    refine (runR (p := nm.cs) (q := nm.ce) (h := nm.st) (t := nm.b) (by rl)
      (ofP (p_ce hT) (fa_cons (by simp [YNSD]) (fa_map lo_YNSD _))) _ _ _).trans ?_
    refine (Reach.step (stepR' (r_ce hT c) _ _)).trans ?_
    apply Reach.of_eq
    congr 1
    simp [RA, Sim.RA, Sim.LoCore_full, lo, prod, Sim.Lo]

theorem macroY (C : CTSH) {m : Nat} (h0 : m ≠ 0) (hk : m < C.k) (rm v : List Ch) :
    Reach1 T (rep nm C m rm (.Y :: v)) (rep nm C ((m + 1) % C.k) (rm ++ [.Y]) (v ++ prod C m)) := by
  have hmk : m ≤ C.length := by simp [CTSH.k] at hk; omega
  refine (frontY hT C m h0 rm v).trans ?_
  have hS : ∀ x ∈ nm.st :: Lo nm C m ++ nm.dl :: rm.map (lo nm) ++ nm.Y :: v.map (lo nm),
      YNSDY nm x :=
    fa_app (fa_app (fa_cons (by simp [YNSDY]) (Lo_mem lo_YNSDY (by simp [YNSDY]) C m))
      (fa_cons (by simp [YNSDY]) (fa_map lo_YNSDY _)))
      (fa_cons (by simp [YNSDY]) (fa_map lo_YNSDY _))
  have hL := copy_loopY hT _ (by simp : (nm.b :: Hi nm C m).reverse ≠ []) (prod C m) [] _ hS
  refine hL.trans ?_
  have hf := finish hT C m hmk .Y rm (v ++ prod C m)
  refine Eq.mpr ?_ hf
  simp [up]

theorem macroN (C : CTSH) {m : Nat} (hk : m < C.k) (rm v : List Ch) :
    Reach1 T (rep nm C m rm (.N :: v)) (rep nm C ((m + 1) % C.k) (rm ++ [.N]) v) := by
  have hmk : m ≤ C.length := by simp [CTSH.k] at hk; omega
  refine (frontN hT C m rm v).trans ?_
  have hS : ∀ x ∈ nm.st :: Lo nm C m ++ nm.dl :: rm.map (lo nm), YNSDY nm x :=
    fa_app (fa_cons (by simp [YNSDY]) (Lo_mem lo_YNSDY (by simp [YNSDY]) C m))
      (fa_cons (by simp [YNSDY]) (fa_map lo_YNSDY _))
  have hL := copy_loopN hT _ (by simp : (nm.b :: Hi nm C m).reverse ≠ []) (v.map (lo nm))
    (prod C m) [] _ hS
  have hL' : Reach T
      (zl nm.b (.go nm.cs) ((prod C m).map (lo nm) ++ (nm.b :: Hi nm C m).reverse)
        (nm.st :: Lo nm C m ++ nm.dl :: rm.map (lo nm) ++ nm.N :: v.map (lo nm)))
      (zl nm.b (.go nm.cs) (nm.b :: Hi nm C m).reverse
        ((prod C m).reverse.map (lo nm) ++ nm.st :: Lo nm C m ++ nm.dl :: rm.map (lo nm) ++
          nm.N :: v.map (lo nm))) := by
    refine Eq.mpr ?_ hL; simp
  refine hL'.trans ?_
  have hf := finish hT C m hmk .N rm v
  refine Eq.mpr ?_ hf
  simp [up]

/-! ## 6. 停止 -/

/-- (λ, m): begin が末尾の b を読んで null（原典「If the read symbol is b, U13_7 halts」）。 -/
theorem halt_null (C : CTSH) (m : Nat) (rm : List Ch) :
    Reach1 T (rep nm C m rm []) (finCfg nm C [] m rm) := by
  rw [rep_eq]
  simp only [List.map_nil, zr]
  refine Reach1.of_step (stepZ (p := nm.begin) (h := nm.b) (t := nm.b) (q := .halt nm.null) (by rl)
    _ _) (Reach.of_eq ?_)
  simp only [zc, finCfg, finList, tapeList]
  congr 1
  · simp; omega
  · simpa using tp_trail (bk := nm.b) (nm.b :: (RA nm C m ++ nm.dl :: List.map (lo nm) rm))

/-- (Y v, 0): begin が y を Y に、case_y_1 が $ を越えて区切り 0 の b で halt（原典 t = 676）。 -/
theorem halt_Y (C : CTSH) (rm v : List Ch) :
    Reach1 T (rep nm C 0 rm (.Y :: v)) (finCfg nm C (.Y :: v) 0 rm) := by
  rw [rep_eq]
  simp only [List.map_cons, zr, lo]
  rw [show (nm.b :: RA nm C 0 ++ nm.dl :: rm.map (lo nm)).reverse =
      ((rm.map (lo nm)).reverse ++ [nm.dl]) ++ nm.b :: (nm.b :: Hi nm C 0).reverse by
    simp [RA, Sim.RA_zero]]
  refine (runL1 (p := nm.begin) (q := nm.cy1) (h := nm.y) (t := nm.Y) (by rl)
    (ofP (p_cy1 hT) (fa_app (fa_rev (fa_map lo_YND _)) (fa_cons (by simp [YND]) fa_nil)))
    nm.b _ _).trans ?_
  refine (Reach.step (stepZ (p := nm.cy1) (h := nm.b) (t := nm.b) (q := .halt nm.halt) (by rl)
    _ _)).trans ?_
  apply Reach.of_eq
  simp only [zc, finCfg, finList]
  congr 1
  · simp [RA, Sim.RA_zero]
  · simp [RA, Sim.RA_zero]

omit hT in
theorem finCfg_halted (C : CTSH) (vf : List Ch) (mf : Nat) (rm : List Ch) :
    Halted T (finCfg nm C vf mf rm) := by
  intro c' ⟨r, _, hst, _⟩
  cases vf <;> simp [finCfg] at hst

/-! ## 7. 主定理（機械の型に依らない形） -/

/-- **主定理（型に依らない形）**。Table 7.1 の 59 本を含む決定的な機械 T は、任意の CTSH C と
    初期語 w について、Morita の初期配置 `encC nm C w` から
    1. C が (w, 0) から n ステップで停止 ID (vf, mf) に達するなら n ステップ以上で停止し、停止配置は
       `finCfg nm C vf mf rm`（ある消去済み列 rm について）。
    2. 逆に停止するなら C も (w, 0) から停止し、停止配置は 1 の形。
    3. C が停止しない ⇔ T が停止しない。 -/
theorem simulates (hD : Deterministic T) (C : CTSH) (w : List Ch) :
    (∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) →
      ∃ N rm, n ≤ N ∧ HaltsIn T N (encC nm C w) (finCfg nm C vf mf rm)) ∧
    (∀ N e, HaltsIn T N (encC nm C w) e →
      ∃ n vf mf rm, CHaltsIn C n (w, 0) (vf, mf) ∧ e = finCfg nm C vf mf rm) ∧
    ((∀ n f, ¬ CHaltsIn C n (w, 0) f) ↔ (∀ N e, ¬ HaltsIn T N (encC nm C w) e)) :=
  simulates_of_steps C (rep nm C) (finCfg nm C) hD (macroY hT C) (macroN hT C) (halt_Y hT C)
    (halt_null hT C) (finCfg_halted C) w

end Main

end URTM.CTSH.U13_7
