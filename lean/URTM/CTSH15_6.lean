/-
  URTM(15,6)（Morita 2017, §7.3.4, Table 7.4）が任意の CTSH を模倣することの一般証明。

  機械の**型に依存しない**形（CTSH17_5.lean と同じ設計）: 名前（`Names`）と Table 7.4 の 64 本の五つ組（原典の 62 本に停止の 2 本を加えたもの）
  （`rules`、停止の 2 本を含む）がすべて機械 T に含まれること（`hT`）、逆向きでは T の決定性だけを仮定する。
  `CTSH15_6Main.lean` で生成モジュール `URTM.Gen.K15_6` に具体化し、`rules` = T（集合として）を
  `decide` で確かめる。

  U15_6 の規則は、コピーの部分を除いて U17_5 と同一（begin・case_y_1・case_y_2・copy_end_1・copy_end_2・
  cycle_end・case_n_1..4 の規則が記号名まで一致）。コピーは copy_start が規則の文字 y を yd、n を b で印し、
  copy_y / copy_n が右端に書き足し、copy_next_1・copy_next_2 が共通の帰り道で、印 yd なら y、b なら n を書き戻す。
  したがって不変量・符号化・停止配置・コピー以外の補題は U17_5 と同じで、本ファイルは CTSH17_5.lean の
  共通部分（`U17_5.Core`・`U17_5.Core.simulates`）を使い、コピー 1 文字（`copy_one`）だけを示す。

  補題の docstring の「原典 t = …」は U17_5 のスナップショット（原典 p. 188–189）の時刻。原典 p. 190
  「The time for simulating a CTSH in U15_6 is exactly the same as that in U17_5」により U15_6 でも同じ時刻になる
  （U15_6 自身のスナップショットは t = 164–466 の一部だけが載っている）。

  記号 b y n ∗ $ yd（原典の y0 は記述ファイルでは yd）、状態 begin case_y_1 case_y_2 copy_start copy_y copy_n copy_next_1 copy_next_2
  copy_end_1 copy_end_2 cycle_end case_n_1..4、疑似状態 halt null（原典の名前）。

  不変量 `rep C m rm v`: 状態 begin、テープ `b · RA(m) · $ · ϕ₁(rm) · ϕ₁(v) · b b …`、ヘッドは ϕ₁(v) の先頭。

  検証の記録は docs/10_ctsh_all_lean_2026-09-26.md。mathlib 非依存。未証明の穴・新規公理・native_decide を使わない。
-/
import URTM.CTSH17_5

namespace URTM.CTSH.U15_6

open URTM URTM.KState URTM.CTSH URTM.CTSH.Sim
open URTM.CTSH.U17_5 (Core)

/-! ## 0. 機械の名前と規則表 -/

/-- U15_6 の記号・状態・疑似状態の名前（U17_5 と共通の `Core` に、印 yd とコピーの 4 状態を加えたもの）。 -/
structure Names (St Ps Sy : Type) extends Core St Ps Sy where
  yd : Sy
  cpy : St
  cpn : St
  cnx1 : St
  cnx2 : St

section
variable {St Ps Sy : Type} (nm : Names St Ps Sy)

/-- 規則表（urtm15-6.txt の五つ組を、記述ファイルの順に、名前で書いたもの）。
    `CTSH15_6Main.lean` で生成モジュールの表と集合として一致することを `decide` で確かめる。 -/
def rules : List (Rule St Ps Sy) :=
  let b := nm.b; let y := nm.y; let n := nm.n; let s := nm.st; let d := nm.dl; let yd := nm.yd
  [ ⟨nm.begin, y, d, .L, .go nm.cy1⟩,
    ⟨nm.begin, n, b, .L, .go nm.cn1⟩,
    ⟨nm.begin, b, d, .L, .go nm.cy2⟩,
    ⟨nm.cy1, y, y, .L, .go nm.cy1⟩,
    ⟨nm.cy1, n, n, .L, .go nm.cy1⟩,
    ⟨nm.cy1, d, b, .L, .go nm.cy1⟩,
    ⟨nm.cy1, s, s, .R, .go nm.begin⟩,
    ⟨nm.cy1, b, b, .Z, .halt nm.halt⟩,
    ⟨nm.cy2, y, y, .L, .go nm.cy2⟩,
    ⟨nm.cy2, n, n, .L, .go nm.cy2⟩,
    ⟨nm.cy2, s, s, .L, .go nm.cy2⟩,
    ⟨nm.cy2, d, d, .Z, .halt nm.null⟩,
    ⟨nm.cy2, b, s, .L, .go nm.cs⟩,
    ⟨nm.cs, y, yd, .R, .go nm.cpy⟩,
    ⟨nm.cs, n, b, .R, .go nm.cpn⟩,
    ⟨nm.cs, s, b, .R, .go nm.ce1⟩,
    ⟨nm.cs, b, b, .R, .go nm.cyc⟩,
    ⟨nm.cpy, y, y, .R, .go nm.cpy⟩,
    ⟨nm.cpy, n, n, .R, .go nm.cpy⟩,
    ⟨nm.cpy, s, s, .R, .go nm.cpy⟩,
    ⟨nm.cpy, d, d, .R, .go nm.cpy⟩,
    ⟨nm.cpy, b, y, .R, .go nm.cnx1⟩,
    ⟨nm.cpn, y, y, .R, .go nm.cpn⟩,
    ⟨nm.cpn, n, n, .R, .go nm.cpn⟩,
    ⟨nm.cpn, s, s, .R, .go nm.cpn⟩,
    ⟨nm.cpn, d, d, .R, .go nm.cpn⟩,
    ⟨nm.cpn, b, n, .R, .go nm.cnx1⟩,
    ⟨nm.cnx1, b, b, .L, .go nm.cnx2⟩,
    ⟨nm.cnx2, y, y, .L, .go nm.cnx2⟩,
    ⟨nm.cnx2, n, n, .L, .go nm.cnx2⟩,
    ⟨nm.cnx2, s, s, .L, .go nm.cnx2⟩,
    ⟨nm.cnx2, d, d, .L, .go nm.cnx2⟩,
    ⟨nm.cnx2, b, n, .L, .go nm.cs⟩,
    ⟨nm.cnx2, yd, y, .L, .go nm.cs⟩,
    ⟨nm.ce1, y, y, .R, .go nm.ce1⟩,
    ⟨nm.ce1, n, n, .R, .go nm.ce1⟩,
    ⟨nm.ce1, s, s, .R, .go nm.ce1⟩,
    ⟨nm.ce1, d, d, .R, .go nm.ce2⟩,
    ⟨nm.ce2, y, y, .R, .go nm.ce2⟩,
    ⟨nm.ce2, n, n, .R, .go nm.ce2⟩,
    ⟨nm.ce2, s, s, .R, .go nm.ce2⟩,
    ⟨nm.ce2, d, y, .R, .go nm.begin⟩,
    ⟨nm.cyc, y, y, .R, .go nm.cyc⟩,
    ⟨nm.cyc, n, n, .R, .go nm.cyc⟩,
    ⟨nm.cyc, s, s, .R, .go nm.cyc⟩,
    ⟨nm.cyc, d, d, .L, .go nm.cs⟩,
    ⟨nm.cn1, y, y, .L, .go nm.cn1⟩,
    ⟨nm.cn1, n, n, .L, .go nm.cn1⟩,
    ⟨nm.cn1, s, s, .L, .go nm.cn1⟩,
    ⟨nm.cn1, d, d, .L, .go nm.cn1⟩,
    ⟨nm.cn1, b, s, .L, .go nm.cn2⟩,
    ⟨nm.cn2, y, y, .L, .go nm.cn2⟩,
    ⟨nm.cn2, n, n, .L, .go nm.cn2⟩,
    ⟨nm.cn2, s, b, .R, .go nm.cn3⟩,
    ⟨nm.cn2, b, b, .R, .go nm.cn4⟩,
    ⟨nm.cn3, y, y, .R, .go nm.cn3⟩,
    ⟨nm.cn3, n, n, .R, .go nm.cn3⟩,
    ⟨nm.cn3, s, s, .R, .go nm.cn3⟩,
    ⟨nm.cn3, d, d, .R, .go nm.cn3⟩,
    ⟨nm.cn3, b, n, .R, .go nm.begin⟩,
    ⟨nm.cn4, y, y, .R, .go nm.cn4⟩,
    ⟨nm.cn4, n, n, .R, .go nm.cn4⟩,
    ⟨nm.cn4, s, s, .R, .go nm.cn4⟩,
    ⟨nm.cn4, d, d, .L, .go nm.cn2⟩ ]

/-- copy_start が規則の文字 c に付ける印（y ↦ yd, n ↦ b）と、書き足しに向かう状態。 -/
def mk : Ch → Sy
  | .Y => nm.yd
  | .N => nm.b
def cc : Ch → St
  | .Y => nm.cpy
  | .N => nm.cpn


/-! ## 1. CTSH の符号化（U17_5 と同じ。`U17_5.Core` のもの） -/

/-- ϕ₁: Y ↦ y, N ↦ n。 -/
def lo : Ch → Sy := Core.lo nm.toCore
/-- 規則領域 RA(m)。 -/
def RA (C : CTSH) (m : Nat) : List Sy := Core.RA nm.toCore C m
/-- テープの中身: b · RA(m) · $ · ϕ₁(rm) · ϕ₁(v)。 -/
def tapeList (C : CTSH) (m : Nat) (rm v : List Ch) : List Sy := Core.tapeList nm.toCore C m rm v
/-- CTSH の ID (v, m) と消去済みの記号列 rm を表す配置（`Core.rep`）。 -/
def rep (C : CTSH) (m : Nat) (rm v : List Ch) : Cfg St Ps Sy := Core.rep nm.toCore C m rm v

/-- **Morita の符号化**（原典 p. 190: U15_6 の初期 ID は U17_5 と同じ。U17_5 のは U13_7 と同じ（p. 188, 183））:
    `b ϕ₁(w^R_{k−1}) ∗ ⋯ ∗ ϕ₁(w^R_1) ∗ b $ q_begin ϕ₁(w) b`。 -/
def encC (C : CTSH) (w : List Ch) : Cfg St Ps Sy := rep nm C 0 [] w

/-- 停止配置のテープ（`Core.finList`。U17_5 と同じ形）。 -/
def finList (C : CTSH) (vf : List Ch) (mf : Nat) (rm : List Ch) : List Sy :=
  Core.finList nm.toCore C vf mf rm

/-- 停止配置（`Core.finCfg`）。(λ, m) なら疑似状態 null でヘッドは本来の $、(Y v, 0) なら halt で
    ヘッドは区切り 0。 -/
def finCfg (C : CTSH) (vf : List Ch) (mf : Nat) (rm : List Ch) : Cfg St Ps Sy :=
  Core.finCfg nm.toCore C vf mf rm

end

/-! ## 2. コピー（copy_start が規則 1 文字 c を印 yd / b にし、右端に書き足して戻る） -/

section Main
variable {St Ps Sy : Type} {nm : Names St Ps Sy} {T : Machine St Ps Sy}
  (hT : ∀ r ∈ rules nm, r ∈ T)
include hT

set_option hygiene false in
/-- 規則 `r` が規則表にあるので T にある。 -/
local macro "rl" : tactic =>
  `(tactic| (apply hT; simp only [rules]; repeat (first | exact List.Mem.head _ | apply List.Mem.tail)))

/-- コピー以外の 45 本（`U17_5.Core.rules`）は規則表に同じ順で含まれる。 -/
theorem core_sub : ∀ r ∈ Core.rules nm.toCore, r ∈ T := fun r h => hT r <| List.Sublist.subset (by
  simp only [Core.rules, rules]
  repeat (first | exact List.nil_sublist _ | apply List.Sublist.cons_cons | apply List.Sublist.cons)) h

theorem copy_one (c : Ch) {LL : List Sy} (hLL : LL ≠ []) {R : List Sy}
    (hR : ∀ x ∈ R, Core.YNSD nm.toCore x) :
    Reach T (zc nm.b (.go nm.cs) LL (lo nm c) R)
      (zl nm.b (.go nm.cs) LL (lo nm c :: R ++ [lo nm c])) := by
  rw [← zc_trail _ _ _ R, ← zl_trail]
  have r_cs : (⟨nm.cs, lo nm c, mk nm c, .R, .go (cc nm c)⟩ : Rule St Ps Sy) ∈ T := by
    cases c <;> rl
  have r_cc : (⟨cc nm c, nm.b, lo nm c, .R, .go nm.cnx1⟩ : Rule St Ps Sy) ∈ T := by
    cases c <;> rl
  have r_cnx2 : (⟨nm.cnx2, mk nm c, lo nm c, .L, .go nm.cs⟩ : Rule St Ps Sy) ∈ T := by
    cases c <;> rl
  have p_cc : ∀ x, Core.YNSD nm.toCore x → (⟨cc nm c, x, x, .R, .go (cc nm c)⟩ : Rule St Ps Sy) ∈ T := by
    cases c <;> rintro x (rfl | rfl | rfl | rfl) <;> rl
  have p_cnx2 : ∀ x, Core.YNSD nm.toCore x → (⟨nm.cnx2, x, x, .L, .go nm.cnx2⟩ : Rule St Ps Sy) ∈ T := by
    rintro x (rfl | rfl | rfl | rfl) <;> rl
  refine (runR r_cs (ofP p_cc hR) LL nm.b []).trans ?_
  rw [zc_nil]
  refine (Reach.step (stepR r_cc _ nm.b [])).trans ?_
  refine (Reach.step (stepL (p := nm.cnx1) (h := nm.b) (t := nm.b) (q := .go nm.cnx2) (by rl)
    (lo nm c) _ [])).trans ?_
  refine (sweepL (X := lo nm c :: R.reverse)
    (ofP p_cnx2 (fa_cons (Core.YNS_YNSD _ (Core.lo_YNS1 c)) (fa_rev hR))) (mk nm c) LL [nm.b]).trans ?_
  refine (Reach.step (stepL' r_cnx2 hLL _)).trans ?_
  exact Reach.of_eq (by simp)

/-! ## 3. 主定理（機械の型に依らない形） -/

/-- **主定理（型に依らない形）**。規則表の 64 本を含む決定的な機械 T は、任意の CTSH C と
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
  Core.simulates (core_sub hT) (fun c _ hLL _ hR => copy_one hT c hLL hR) hD C w

end Main

end URTM.CTSH.U15_6
