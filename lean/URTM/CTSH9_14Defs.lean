/-
  URTM(9,14)（2026-10-31）の定義: Morita の URTM(10,8) の表 `T`（生成モジュール `URTM.Gen.K10_8`）から、
  状態 copy_y_2（q6）を case_y_1（q1）に併合し、区別をセルのタグに移した表。

  子の表 `T9` は親の 63 本の五つ組を 1 本ずつ写したもの（分割も欠落も無い）。写し方は
  * 状態: q6 を q1 に読み替える（`merge`）。
  * 記号: タグ付きの記号 `Sy × Bool`。親の規則 (p, s) について、読む記号のタグは `rt p s`、
    書く記号のタグは `wt p s`。19 組・21 組の集合（results/lockmerge-2026-10-31/t4a.json）。
  表そのものは書き写さない（zoo に五つ組の表を入れない約束）。

  マクロステップの境目の配置 `rep9` は、親の `rep` の各セルに、相マーカーと `$` の間の `∗`
  （`Lo` の中の `∗`）にだけタグを付けたもの（results/lockmerge-2026-10-31/README.md §3.1 の規則 R）。

  主定理 `urtm9_14_simulates_ctsh` は CTSH9_14.lean。
-/
import URTM.CTSHSim
import URTM.CTSH10_8
import URTM.Gen.K10_8

set_option maxRecDepth 100000

namespace URTM.CTSH.U9_14

open URTM URTM.KState URTM.CTSH URTM.CTSH.Sim URTM.Gen.K10_8
open URTM.CTSH.U10_8 (up Hi Lo LoCore RA)

abbrev lo : Ch → Sy := URTM.CTSH.U10_8.lo

/-! ## 1. 子の表 -/

/-- タグ付きの記号。`(x, true)` が x′。 -/
abbrev TS := Sy × Bool

/-- 状態の併合: copy_y_2（q6）を case_y_1（q1）に。 -/
def merge : St → St
  | .q6 => .q1
  | q => q

def mergeT : Tgt St Ps → Tgt St Ps
  | .go q => .go (merge q)
  | .halt h => .halt h

/-- 読む記号にタグが付く親の規則 (p, s)（19 組）。 -/
def rtL : List (St × Sy) :=
  [(.q0, .s4), (.q0, .s5), (.q1, .s6), (.q2, .s1), (.q2, .s7), (.q3, .s6), (.q5, .s4), (.q5, .s5),
   (.q6, .s0), (.q6, .s4), (.q6, .s5), (.q6, .s7), (.q7, .s4), (.q7, .s5), (.q8, .s0), (.q8, .s6),
   (.q8, .s7), (.q9, .s4), (.q9, .s5)]

/-- 書く記号にタグが付く親の規則 (p, s)（21 組）。 -/
def wtL : List (St × Sy) :=
  [(.q0, .s0), (.q0, .s1), (.q1, .s0), (.q1, .s6), (.q1, .s7), (.q3, .s4), (.q3, .s5), (.q4, .s1),
   (.q4, .s2), (.q5, .s4), (.q5, .s5), (.q5, .s7), (.q6, .s0), (.q6, .s4), (.q6, .s5), (.q7, .s6),
   (.q7, .s7), (.q8, .s0), (.q8, .s4), (.q8, .s5), (.q9, .s6)]

def rt (p : St) (s : Sy) : Bool := rtL.contains (p, s)
def wt (p : St) (s : Sy) : Bool := wtL.contains (p, s)

/-- 親の規則 1 本を子の規則に。 -/
def tagRule (ρ : Rule St Ps Sy) : Rule St Ps TS :=
  ⟨merge ρ.p, (ρ.s, rt ρ.p ρ.s), (ρ.t, wt ρ.p ρ.s), ρ.d, mergeT ρ.q⟩

/-- **URTM(9,14) の表**。 -/
def T9 : Machine St Ps TS := T.map tagRule

theorem T9_length : T9.length = 63 := by decide
theorem hD9 : Deterministic T9 := by decide
theorem hR9 : Reversible T9 := by decide
/-- 状態 q6 は子の表の規則の元の状態にも行き先にも現れない（状態は 9 個）。 -/
theorem q6_unused : ∀ ρ ∈ T9, ρ.p ≠ .q6 ∧ ρ.q ≠ .go .q6 := by decide

/-! ## 2. 境目の配置（規則 R） -/

/-- 空白 b（タグ無し）。 -/
abbrev bk : TS := (.s0, false)

/-- タグ無しの記号列。 -/
def un (X : List Sy) : List TS := X.map (·, false)

/-- `Lo` の `∗` にだけタグ。 -/
def tagSt (x : Sy) : TS := (x, x == .s6)

/-- 子の規則領域 RA'(m) = H(m) · ϕ₁(w^R_m) · b · Lo'(m)。 -/
def RA9 (C : CTSH) (m : Nat) : List TS :=
  un (Hi C m ++ (prod C m).reverse.map lo) ++ bk :: (Lo C m).map tagSt

/-- 子のテープの中身: b · RA'(m) · $ · ϕ_up(rm) · ϕ₁(v)。 -/
def tapeList9 (C : CTSH) (m : Nat) (rm v : List Ch) : List TS :=
  bk :: RA9 C m ++ (.s7, false) :: un (rm.map up ++ v.map lo)

/-- 境目の配置（状態 begin、ヘッドは現在の文字列の先頭）。 -/
def rep9 (C : CTSH) (m : Nat) (rm v : List Ch) : Cfg St Ps TS :=
  { st := .go .q0, pos := (RA C m).length + 2 + rm.length, tape := tp bk (tapeList9 C m rm v) }

/-- 初期配置（相 0 にはタグが無い）。 -/
def encC9 (C : CTSH) (w : List Ch) : Cfg St Ps TS := rep9 C 0 [] w

/-- 停止配置。null は `rep9` のテープでヘッドのセル（b）にタグ。halt は `$`・ヘッドのセル（区切り 0 の b）・
    最終文字列の先頭 y にタグ。 -/
def finCfg9 (C : CTSH) (vf : List Ch) (mf : Nat) (rm : List Ch) : Cfg St Ps TS :=
  match vf with
  | [] =>
    { st := .halt .h0, pos := (RA C mf).length + 2 + rm.length,
      tape := tp bk (tapeList9 C mf rm [] ++ [(.s0, true)]) }
  | _ :: v =>
    { st := .halt .h1, pos := (RA C 0).length,
      tape := tp bk (bk :: un (Hi C 0) ++ (.s0, true) :: (.s7, true) ::
        (un (rm.map up) ++ (.s1, true) :: un (v.map lo))) }

/-! ## 3. 主定理の文（証明は CTSH9_14.lean） -/

/-- CTSH9_14.lean が示す主定理の文（`urtm10_8_simulates_ctsh` と同じ 3 項）。 -/
def SimStatement (C : CTSH) (w : List Ch) : Prop :=
  (∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) →
    ∃ N rm, n ≤ N ∧ HaltsIn T9 N (encC9 C w) (finCfg9 C vf mf rm)) ∧
  (∀ N e, HaltsIn T9 N (encC9 C w) e →
    ∃ n vf mf rm, CHaltsIn C n (w, 0) (vf, mf) ∧ e = finCfg9 C vf mf rm) ∧
  ((∀ n f, ¬ CHaltsIn C n (w, 0) f) ↔ (∀ N e, ¬ HaltsIn T9 N (encC9 C w) e))

end URTM.CTSH.U9_14
