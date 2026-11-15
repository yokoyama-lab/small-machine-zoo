/-
  URTM(9,14) の第 2 の表 t4b（2026-10-31）の定義: Morita の URTM(10,8) の表 `T` から、状態 copy_n_2（q8）を
  case_y_1（q1）に併合し、区別をセルのタグに移した表。

  子の表 `T9b` は親の 63 本を 1 本ずつ写したもの（`tagRuleB`）に、copy_start がタグ付きの空白 b′ を読む 1 本
  `⟨q4, b′, b, R, begin⟩` を足した 64 本。親の規則 copy_start・b は子では b → b′ と書き、この 1 本が b′ → b と書く。
  左端の b のタグは、CTSH の生成規則を一巡するたびに反転する。

  境目の配置 `rep9b` は t4a の `rep9` の左端の b に、周の偶奇のタグ `eB C m rm` を付けたもの。
  `eB C m rm = ((|rm| + k − m) / k が偶数)`。相 m を 1 進めて rm に 1 文字足すとき、m が k−1 → 0 と一巡する場合だけ
  反転する（`eB_step`・`eB_wrap`）。初期配置（m = 0、rm = []）では偽（タグ無し）。

  主定理 `urtm9_14b_simulates_ctsh` は CTSH9_14b.lean。表そのものは書き写さない（タグの組の集合だけ）。
-/
import URTM.CTSH9_14Defs

set_option maxRecDepth 100000

namespace URTM.CTSH.U9_14b

open URTM URTM.KState URTM.CTSH URTM.CTSH.Sim URTM.Gen.K10_8
open URTM.CTSH.U9_14 (TS bk un tagSt RA9)

abbrev lo : Ch → Sy := URTM.CTSH.U10_8.lo
open URTM.CTSH.U10_8 (up)

/-! ## 1. 子の表 -/

/-- 状態の併合: copy_n_2（q8）を case_y_1（q1）に。 -/
def mergeB : St → St
  | .q8 => .q1
  | q => q

def mergeBT : Tgt St Ps → Tgt St Ps
  | .go q => .go (mergeB q)
  | .halt h => .halt h

/-- 読む記号にタグが付く親の規則 (p, s)（16 組。copy_start・b は含まない）。 -/
def rtLB : List (St × Sy) :=
  [(.q1, .s6), (.q2, .s1), (.q2, .s4), (.q2, .s5), (.q2, .s7), (.q3, .s6), (.q6, .s0), (.q6, .s4),
   (.q6, .s5), (.q6, .s6), (.q6, .s7), (.q8, .s0), (.q8, .s1), (.q8, .s4), (.q8, .s5), (.q8, .s7)]

/-- 書く記号にタグが付く親の規則 (p, s)（17 組）。 -/
def wtLB : List (St × Sy) :=
  [(.q0, .s1), (.q1, .s4), (.q1, .s5), (.q1, .s6), (.q1, .s7), (.q4, .s0), (.q4, .s1), (.q4, .s2),
   (.q5, .s4), (.q5, .s5), (.q5, .s6), (.q5, .s7), (.q7, .s1), (.q7, .s4), (.q7, .s5), (.q7, .s7),
   (.q9, .s6)]

def rtB (p : St) (s : Sy) : Bool := rtLB.contains (p, s)
def wtB (p : St) (s : Sy) : Bool := wtLB.contains (p, s)

def tagRuleB (ρ : Rule St Ps Sy) : Rule St Ps TS :=
  ⟨mergeB ρ.p, (ρ.s, rtB ρ.p ρ.s), (ρ.t, wtB ρ.p ρ.s), ρ.d, mergeBT ρ.q⟩

/-- **URTM(9,14) の第 2 の表**（64 本）。 -/
def T9b : Machine St Ps TS := T.map tagRuleB ++ [⟨.q4, (.s0, true), (.s0, false), .R, .go .q0⟩]

theorem T9b_length : T9b.length = 64 := by decide
theorem hD9b : Deterministic T9b := by decide
theorem hR9b : Reversible T9b := by decide
/-- 状態 q8 は子の表に現れない（状態は 9 個）。 -/
theorem q8_unused : ∀ ρ ∈ T9b, ρ.p ≠ .q8 ∧ ρ.q ≠ .go .q8 := by decide

/-! ## 2. 境目の配置 -/

/-- 左端の b のタグ: (|rm| + k − m) / k が偶数。 -/
def eB (C : CTSH) (m : Nat) (rm : List Ch) : Bool := (rm.length + C.k - m) / C.k % 2 == 0

def tapeList9b (C : CTSH) (m : Nat) (rm v : List Ch) : List TS :=
  (.s0, eB C m rm) :: RA9 C m ++ (.s7, false) :: un (rm.map up ++ v.map lo)

def rep9b (C : CTSH) (m : Nat) (rm v : List Ch) : Cfg St Ps TS :=
  { st := .go .q0, pos := (U10_8.RA C m).length + 2 + rm.length, tape := tp bk (tapeList9b C m rm v) }

def encC9b (C : CTSH) (w : List Ch) : Cfg St Ps TS := rep9b C 0 [] w

/-- 停止配置。null は `rep9b` のテープのまま。halt は `$`・規則の消去済みの大文字・最終文字列の先頭 y にタグ。 -/
def finCfg9b (C : CTSH) (vf : List Ch) (mf : Nat) (rm : List Ch) : Cfg St Ps TS :=
  match vf with
  | [] =>
    { st := .halt .h0, pos := (U10_8.RA C mf).length + 2 + rm.length, tape := tp bk (tapeList9b C mf rm []) }
  | _ :: v =>
    { st := .halt .h1, pos := (U10_8.RA C 0).length,
      tape := tp bk ((.s0, eB C 0 rm) :: un (U10_8.Hi C 0) ++ (.s0, false) :: (.s7, true) ::
        ((rm.map up).map (·, true) ++ (.s1, true) :: un (v.map lo))) }

def SimStatementB (C : CTSH) (w : List Ch) : Prop :=
  (∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) →
    ∃ N rm, n ≤ N ∧ HaltsIn T9b N (encC9b C w) (finCfg9b C vf mf rm)) ∧
  (∀ N e, HaltsIn T9b N (encC9b C w) e →
    ∃ n vf mf rm, CHaltsIn C n (w, 0) (vf, mf) ∧ e = finCfg9b C vf mf rm) ∧
  ((∀ n f, ¬ CHaltsIn C n (w, 0) f) ↔ (∀ N e, ¬ HaltsIn T9b N (encC9b C w) e))

end URTM.CTSH.U9_14b
