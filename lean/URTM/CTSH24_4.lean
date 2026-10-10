/-
  URTM(24,4)（Morita 2017, §7.3.5, Table 7.5）が任意の CTSH を模倣することの一般証明。

  機械の**型に依存しない**形（CTSH17_5.lean と同じ設計）: 名前（`Names`）と Table 7.5 の 84 本の五つ組
  （`rules`、原典の 82 本に停止の 2 本を加えたもの）がすべて機械 T に含まれること（`hT`）、逆向きでは
  T の決定性だけを仮定する。`CTSH24_4Main.lean` で生成モジュール `URTM.Gen.K24_4` に具体化し、
  `rules` = T（集合として）を `decide` で確かめる。

  記号 b y n ∗ の 4 個だけ。原典 p. 192: U17_5 の $ が使えないので、規則領域と消去済みの記号の区切りは
  b、現在の文字列の先頭の印は ∗ になる。初期 ID は

      b ϕ₁(w^R_{k−1}) ∗ ⋯ ∗ ϕ₁(w^R_1) ∗ b b q_begin ϕ₁(v0) b

  不変量 `rep C m rm v`: 状態 begin、テープ `b · RA(m) · b · ϕ₁(rm) · ϕ₁(v) · b b …`、ヘッドは ϕ₁(v) の先頭。
  RA(m) = H(m) · ϕ₁(w^R_m) · b · Lo(m)（b が相マーカー、U17_5 と同じ）。

  先頭が Y のとき（原典 t = 7–60）: begin が y を ∗ に、case_y_1 が区切りの b まで左へ、case_y_2 が区切り 0 を見て
  （∗ なら）case_n_5 で区切りの b まで戻って case_y_3 が相マーカー b まで左へ、b を ∗ にして copy_start。
  copy_c_1 が区切りの b まで、copy_c_2 が右端まで行って c を書き、copy_c_3 で折り返し、copy_c_4 が区切りの b まで、
  copy_c_5 が印の b まで戻って c を書き戻す。規則の終わり（∗）で copy_end_1 が区切りまで、copy_end_2 が
  印の ∗ を y に戻して begin。
  先頭が N のとき（t = 0–7）: begin が n を ∗ に、case_n_1 が区切りの b まで、case_n_2 が相マーカー b まで左へ行って
  ∗ にし、case_n_3 が w_m を越えて次の区切り ∗ を b（新しい相マーカー）に、case_n_4 が区切りの b まで、
  case_n_5 が印の ∗ を n に戻して begin。

  記号 b y n ∗、状態 begin case_y_1..3 copy_start copy_y_1..5 copy_n_1..5 copy_end_1 copy_end_2
  cycle_end case_n_1..6、疑似状態 halt null（原典の名前）。

  検証の記録は docs/10_ctsh_all_lean_2026-09-26.md。mathlib 非依存。未証明の穴・新規公理・native_decide を使わない。
-/
import URTM.CTSHSim

namespace URTM.CTSH.U24_4

open URTM URTM.KState URTM.CTSH URTM.CTSH.Sim

/-! ## 0. 機械の名前と Table 7.5 -/

/-- U24_4 の記号・状態・疑似状態の名前。 -/
structure Names (St Ps Sy : Type) where
  b : Sy
  y : Sy
  n : Sy
  st : Sy   -- ∗
  begin : St
  cy1 : St
  cy2 : St
  cy3 : St
  cs : St
  cpy1 : St
  cpy2 : St
  cpy3 : St
  cpy4 : St
  cpy5 : St
  cpn1 : St
  cpn2 : St
  cpn3 : St
  cpn4 : St
  cpn5 : St
  ce1 : St
  ce2 : St
  cyc : St
  cn1 : St
  cn2 : St
  cn3 : St
  cn4 : St
  cn5 : St
  cn6 : St
  halt : Ps
  null : Ps

section
variable {St Ps Sy : Type} (nm : Names St Ps Sy)

/-- Table 7.5（urtm24-4.txt の五つ組を、記述ファイルの順に、名前で書いたもの）。
    `CTSH24_4Main.lean` で生成モジュールの表と集合として一致することを `decide` で確かめる。 -/
def rules : List (Rule St Ps Sy) :=
  let b := nm.b; let y := nm.y; let n := nm.n; let s := nm.st
  [ ⟨nm.begin, y, s, .L, .go nm.cy1⟩,
    ⟨nm.begin, n, s, .L, .go nm.cn1⟩,
    ⟨nm.begin, b, b, .Z, .halt nm.null⟩,
    ⟨nm.cy1, y, y, .L, .go nm.cy1⟩,
    ⟨nm.cy1, n, n, .L, .go nm.cy1⟩,
    ⟨nm.cy1, b, b, .L, .go nm.cy2⟩,
    ⟨nm.cy2, s, s, .R, .go nm.cn5⟩,
    ⟨nm.cy2, b, b, .Z, .halt nm.halt⟩,
    ⟨nm.cy3, y, y, .L, .go nm.cy3⟩,
    ⟨nm.cy3, n, n, .L, .go nm.cy3⟩,
    ⟨nm.cy3, s, s, .L, .go nm.cy3⟩,
    ⟨nm.cy3, b, s, .L, .go nm.cs⟩,
    ⟨nm.cs, y, b, .R, .go nm.cpy1⟩,
    ⟨nm.cs, n, b, .R, .go nm.cpn1⟩,
    ⟨nm.cs, s, b, .R, .go nm.ce1⟩,
    ⟨nm.cs, b, b, .R, .go nm.cyc⟩,
    ⟨nm.cpy1, y, y, .R, .go nm.cpy1⟩,
    ⟨nm.cpy1, n, n, .R, .go nm.cpy1⟩,
    ⟨nm.cpy1, s, s, .R, .go nm.cpy1⟩,
    ⟨nm.cpy1, b, b, .R, .go nm.cpy2⟩,
    ⟨nm.cpy2, y, y, .R, .go nm.cpy2⟩,
    ⟨nm.cpy2, n, n, .R, .go nm.cpy2⟩,
    ⟨nm.cpy2, s, s, .R, .go nm.cpy2⟩,
    ⟨nm.cpy2, b, y, .R, .go nm.cpy3⟩,
    ⟨nm.cpy3, b, b, .L, .go nm.cpy4⟩,
    ⟨nm.cpy4, y, y, .L, .go nm.cpy4⟩,
    ⟨nm.cpy4, n, n, .L, .go nm.cpy4⟩,
    ⟨nm.cpy4, s, s, .L, .go nm.cpy4⟩,
    ⟨nm.cpy4, b, b, .L, .go nm.cpy5⟩,
    ⟨nm.cpy5, y, y, .L, .go nm.cpy5⟩,
    ⟨nm.cpy5, n, n, .L, .go nm.cpy5⟩,
    ⟨nm.cpy5, s, s, .L, .go nm.cpy5⟩,
    ⟨nm.cpy5, b, y, .L, .go nm.cs⟩,
    ⟨nm.cpn1, y, y, .R, .go nm.cpn1⟩,
    ⟨nm.cpn1, n, n, .R, .go nm.cpn1⟩,
    ⟨nm.cpn1, s, s, .R, .go nm.cpn1⟩,
    ⟨nm.cpn1, b, b, .R, .go nm.cpn2⟩,
    ⟨nm.cpn2, y, y, .R, .go nm.cpn2⟩,
    ⟨nm.cpn2, n, n, .R, .go nm.cpn2⟩,
    ⟨nm.cpn2, s, s, .R, .go nm.cpn2⟩,
    ⟨nm.cpn2, b, n, .R, .go nm.cpn3⟩,
    ⟨nm.cpn3, b, b, .L, .go nm.cpn4⟩,
    ⟨nm.cpn4, y, y, .L, .go nm.cpn4⟩,
    ⟨nm.cpn4, n, n, .L, .go nm.cpn4⟩,
    ⟨nm.cpn4, s, s, .L, .go nm.cpn4⟩,
    ⟨nm.cpn4, b, b, .L, .go nm.cpn5⟩,
    ⟨nm.cpn5, y, y, .L, .go nm.cpn5⟩,
    ⟨nm.cpn5, n, n, .L, .go nm.cpn5⟩,
    ⟨nm.cpn5, s, s, .L, .go nm.cpn5⟩,
    ⟨nm.cpn5, b, n, .L, .go nm.cs⟩,
    ⟨nm.ce1, y, y, .R, .go nm.ce1⟩,
    ⟨nm.ce1, n, n, .R, .go nm.ce1⟩,
    ⟨nm.ce1, s, s, .R, .go nm.ce1⟩,
    ⟨nm.ce1, b, b, .R, .go nm.ce2⟩,
    ⟨nm.ce2, y, y, .R, .go nm.ce2⟩,
    ⟨nm.ce2, n, n, .R, .go nm.ce2⟩,
    ⟨nm.ce2, s, y, .R, .go nm.begin⟩,
    ⟨nm.cyc, y, y, .R, .go nm.cyc⟩,
    ⟨nm.cyc, n, n, .R, .go nm.cyc⟩,
    ⟨nm.cyc, s, s, .R, .go nm.cyc⟩,
    ⟨nm.cyc, b, b, .L, .go nm.cs⟩,
    ⟨nm.cn1, y, y, .L, .go nm.cn1⟩,
    ⟨nm.cn1, n, n, .L, .go nm.cn1⟩,
    ⟨nm.cn1, b, b, .L, .go nm.cn2⟩,
    ⟨nm.cn2, y, y, .L, .go nm.cn2⟩,
    ⟨nm.cn2, n, n, .L, .go nm.cn2⟩,
    ⟨nm.cn2, s, s, .L, .go nm.cn2⟩,
    ⟨nm.cn2, b, s, .L, .go nm.cn3⟩,
    ⟨nm.cn3, y, y, .L, .go nm.cn3⟩,
    ⟨nm.cn3, n, n, .L, .go nm.cn3⟩,
    ⟨nm.cn3, s, b, .R, .go nm.cn4⟩,
    ⟨nm.cn3, b, b, .R, .go nm.cn6⟩,
    ⟨nm.cn4, y, y, .R, .go nm.cn4⟩,
    ⟨nm.cn4, n, n, .R, .go nm.cn4⟩,
    ⟨nm.cn4, s, s, .R, .go nm.cn4⟩,
    ⟨nm.cn4, b, b, .R, .go nm.cn5⟩,
    ⟨nm.cn5, y, y, .R, .go nm.cn5⟩,
    ⟨nm.cn5, n, n, .R, .go nm.cn5⟩,
    ⟨nm.cn5, s, n, .R, .go nm.begin⟩,
    ⟨nm.cn5, b, b, .L, .go nm.cy3⟩,
    ⟨nm.cn6, y, y, .R, .go nm.cn6⟩,
    ⟨nm.cn6, n, n, .R, .go nm.cn6⟩,
    ⟨nm.cn6, s, s, .R, .go nm.cn6⟩,
    ⟨nm.cn6, b, b, .L, .go nm.cn3⟩ ]

/-! ## 1. CTSH の符号化 -/

/-- ϕ₁: Y ↦ y, N ↦ n。 -/
def lo : Ch → Sy
  | .Y => nm.y
  | .N => nm.n

/-- copy_c_1..5 の状態。 -/
def k1 : Ch → St
  | .Y => nm.cpy1
  | .N => nm.cpn1
def k2 : Ch → St
  | .Y => nm.cpy2
  | .N => nm.cpn2
def k3 : Ch → St
  | .Y => nm.cpy3
  | .N => nm.cpn3
def k4 : Ch → St
  | .Y => nm.cpy4
  | .N => nm.cpn4
def k5 : Ch → St
  | .Y => nm.cpy5
  | .N => nm.cpn5

/-- 規則領域 RA(m) = H(m) · ϕ₁(w^R_m) · b · Lo(m)（CTSHSim の ϕ₁ 型、相マーカー b）。 -/
def RA (C : CTSH) (m : Nat) : List Sy := Sim.RA (lo nm) nm.st nm.b C m

/-- テープの中身（左端が位置 0）: b · RA(m) · b · ϕ₁(rm) · ϕ₁(v)。以降は b。 -/
def tapeList (C : CTSH) (m : Nat) (rm v : List Ch) : List Sy :=
  nm.b :: RA nm C m ++ nm.b :: rm.map (lo nm) ++ v.map (lo nm)

/-- CTSH の ID (v, m) と消去済みの記号列 rm を表す配置: 状態 begin、ヘッドは v の先頭。 -/
def rep (C : CTSH) (m : Nat) (rm v : List Ch) : Cfg St Ps Sy :=
  { st := .go nm.begin, pos := (RA nm C m).length + 2 + rm.length, tape := tp nm.b (tapeList nm C m rm v) }

/-- **Morita の符号化**（原典 p. 192）: `b ϕ₁(w^R_{k−1}) ∗ ⋯ ∗ ϕ₁(w^R_1) ∗ b b q_begin ϕ₁(w) b`。 -/
def encC (C : CTSH) (w : List Ch) : Cfg St Ps Sy := rep nm C 0 [] w

/-- 停止配置のテープ（リスト）。
    * 最終 ID (λ, m): begin が末尾の b を読んで null。テープは `rep` のまま `b · RA(m) · b · ϕ₁(rm)`。
    * 最終 ID (Y v, 0): begin が先頭の y を ∗ に変え、case_y_1 が区切りの b まで行き、case_y_2 が区切り 0 の
      b（相マーカー）で halt。テープは `b · RA(0) · b · ϕ₁(rm) · ∗ · ϕ₁(v)`
      （原典 p. 192, t = 466「the rightmost ∗ should be read as Y」）。 -/
def finList (C : CTSH) (vf : List Ch) (mf : Nat) (rm : List Ch) : List Sy :=
  match vf with
  | [] => tapeList nm C mf rm []
  | _ :: v => nm.b :: RA nm C 0 ++ nm.b :: rm.map (lo nm) ++ nm.st :: v.map (lo nm)

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

/-- {y, n}。 -/
def YN (x : Sy) : Prop := x = nm.y ∨ x = nm.n
/-- {y, n, ∗}。 -/
def YNS (x : Sy) : Prop := x = nm.y ∨ x = nm.n ∨ x = nm.st

variable {nm}

theorem lo_YN : ∀ c, YN nm (lo nm c) := by intro c; cases c <;> simp [YN, lo]
theorem lo_YNS : ∀ c, YNS nm (lo nm c) := by intro c; cases c <;> simp [YNS, lo]
theorem YNS_st : YNS nm nm.st := by simp [YNS]

theorem Lo_YNS (C : CTSH) (m : Nat) : ∀ x ∈ Sim.Lo (lo nm) nm.st C m, YNS nm x :=
  Lo_mem lo_YNS YNS_st C m
theorem LoCore_YNS (C : CTSH) (m : Nat) : ∀ x ∈ Sim.LoCore (lo nm) nm.st C m, YNS nm x :=
  LoCore_mem lo_YNS YNS_st C m

end Sets

/-! ## 3. 規則表から読み取る 1 ステップと掃引 -/

section Main
variable {St Ps Sy : Type} {nm : Names St Ps Sy} {T : Machine St Ps Sy}
  (hT : ∀ r ∈ rules nm, r ∈ T)
include hT

set_option hygiene false in
/-- 規則 `r` が Table 7.5 にあるので T にある。 -/
macro "rl" : tactic =>
  `(tactic| (apply hT; simp only [rules]; repeat (first | exact List.Mem.head _ | apply List.Mem.tail)))

set_option hygiene false in
/-- 状態 q が集合 {y, n} / {y, n, ∗} を書き換えずに dir 向きに通過する。 -/
macro "pass2" : tactic => `(tactic| (rintro x (rfl | rfl) <;> rl))
set_option hygiene false in
macro "pass3" : tactic => `(tactic| (rintro x (rfl | rfl | rfl) <;> rl))

theorem p_cy1 : ∀ x, YN nm x → (⟨nm.cy1, x, x, .L, .go nm.cy1⟩ : Rule St Ps Sy) ∈ T := by pass2
theorem p_cn1 : ∀ x, YN nm x → (⟨nm.cn1, x, x, .L, .go nm.cn1⟩ : Rule St Ps Sy) ∈ T := by pass2
theorem p_cn3 : ∀ x, YN nm x → (⟨nm.cn3, x, x, .L, .go nm.cn3⟩ : Rule St Ps Sy) ∈ T := by pass2
theorem p_cn5 : ∀ x, YN nm x → (⟨nm.cn5, x, x, .R, .go nm.cn5⟩ : Rule St Ps Sy) ∈ T := by pass2
theorem p_ce2 : ∀ x, YN nm x → (⟨nm.ce2, x, x, .R, .go nm.ce2⟩ : Rule St Ps Sy) ∈ T := by pass2
theorem p_cy3 : ∀ x, YNS nm x → (⟨nm.cy3, x, x, .L, .go nm.cy3⟩ : Rule St Ps Sy) ∈ T := by pass3
theorem p_cn2 : ∀ x, YNS nm x → (⟨nm.cn2, x, x, .L, .go nm.cn2⟩ : Rule St Ps Sy) ∈ T := by pass3
theorem p_cn4 : ∀ x, YNS nm x → (⟨nm.cn4, x, x, .R, .go nm.cn4⟩ : Rule St Ps Sy) ∈ T := by pass3
theorem p_cn6 : ∀ x, YNS nm x → (⟨nm.cn6, x, x, .R, .go nm.cn6⟩ : Rule St Ps Sy) ∈ T := by pass3
theorem p_ce1 : ∀ x, YNS nm x → (⟨nm.ce1, x, x, .R, .go nm.ce1⟩ : Rule St Ps Sy) ∈ T := by pass3
theorem p_cyc : ∀ x, YNS nm x → (⟨nm.cyc, x, x, .R, .go nm.cyc⟩ : Rule St Ps Sy) ∈ T := by pass3
theorem p_k1 (c : Ch) : ∀ x, YNS nm x → (⟨k1 nm c, x, x, .R, .go (k1 nm c)⟩ : Rule St Ps Sy) ∈ T := by
  cases c <;> pass3
theorem p_k2 (c : Ch) : ∀ x, YNS nm x → (⟨k2 nm c, x, x, .R, .go (k2 nm c)⟩ : Rule St Ps Sy) ∈ T := by
  cases c <;> pass3
theorem p_k4 (c : Ch) : ∀ x, YNS nm x → (⟨k4 nm c, x, x, .L, .go (k4 nm c)⟩ : Rule St Ps Sy) ∈ T := by
  cases c <;> pass3
theorem p_k5 (c : Ch) : ∀ x, YNS nm x → (⟨k5 nm c, x, x, .L, .go (k5 nm c)⟩ : Rule St Ps Sy) ∈ T := by
  cases c <;> pass3
theorem r_cs (c : Ch) : (⟨nm.cs, lo nm c, nm.b, .R, .go (k1 nm c)⟩ : Rule St Ps Sy) ∈ T := by
  cases c <;> rl
theorem r_k1 (c : Ch) : (⟨k1 nm c, nm.b, nm.b, .R, .go (k2 nm c)⟩ : Rule St Ps Sy) ∈ T := by
  cases c <;> rl
theorem r_k2 (c : Ch) : (⟨k2 nm c, nm.b, lo nm c, .R, .go (k3 nm c)⟩ : Rule St Ps Sy) ∈ T := by
  cases c <;> rl
theorem r_k3 (c : Ch) : (⟨k3 nm c, nm.b, nm.b, .L, .go (k4 nm c)⟩ : Rule St Ps Sy) ∈ T := by
  cases c <;> rl
theorem r_k4 (c : Ch) : (⟨k4 nm c, nm.b, nm.b, .L, .go (k5 nm c)⟩ : Rule St Ps Sy) ∈ T := by
  cases c <;> rl
theorem r_k5 (c : Ch) : (⟨k5 nm c, nm.b, lo nm c, .L, .go nm.cs⟩ : Rule St Ps Sy) ∈ T := by
  cases c <;> rl

/-! ## 4. コピー（先頭が Y のときだけ使う） -/

/-- copy_start が規則の 1 文字 c を b で印し、copy_c_1 が区切りの b まで、copy_c_2 が右端の b まで行って c を書き、
    copy_c_3 が折り返し、copy_c_4 が区切りの b まで、copy_c_5 が印の b まで戻って c を書き戻す
    （原典 t = 14–52）。R₁ は印と区切りの間、R₂ は区切りと右端の間。 -/
theorem copy_one (c : Ch) {LL : List Sy} (hLL : LL ≠ []) {R₁ R₂ : List Sy}
    (h₁ : ∀ x ∈ R₁, YNS nm x) (h₂ : ∀ x ∈ R₂, YNS nm x) :
    Reach T (zc nm.b (.go nm.cs) LL (lo nm c) (R₁ ++ nm.b :: R₂))
      (zl nm.b (.go nm.cs) LL (lo nm c :: R₁ ++ nm.b :: (R₂ ++ [lo nm c]))) := by
  rw [← zc_trail _ _ _ (R₁ ++ nm.b :: R₂), ← zl_trail]
  rw [show R₁ ++ nm.b :: R₂ ++ [nm.b] = R₁ ++ nm.b :: (R₂ ++ [nm.b]) by simp]
  refine (runR (r_cs hT c) (ofP (p_k1 hT c) h₁) LL nm.b _).trans ?_
  refine (runR (r_k1 hT c) (ofP (p_k2 hT c) h₂) _ nm.b []).trans ?_
  rw [zc_nil]
  refine (Reach.step (stepR (r_k2 hT c) _ nm.b [])).trans ?_
  refine (Reach.step (stepL (r_k3 hT c) (lo nm c) _ [])).trans ?_
  refine (sweepL (X := lo nm c :: R₂.reverse)
    (ofP (p_k4 hT c) (fa_cons (lo_YNS c) (fa_rev h₂))) nm.b _ [nm.b]).trans ?_
  refine (runL (r_k4 hT c) (X := R₁.reverse) (ofP (p_k5 hT c) (fa_rev h₁)) nm.b LL _).trans ?_
  refine (Reach.step (stepL' (r_k5 hT c) hLL _)).trans ?_
  exact Reach.of_eq (by simp)

theorem copy_loop (Z : List Sy) (hZ : Z ≠ []) :
    ∀ (Q P : List Ch) (S₁ S₂ : List Sy), (∀ x ∈ S₁, YNS nm x) → (∀ x ∈ S₂, YNS nm x) →
    Reach T (zl nm.b (.go nm.cs) (Q.map (lo nm) ++ Z) (P.reverse.map (lo nm) ++ S₁ ++ nm.b :: S₂))
      (zl nm.b (.go nm.cs) Z ((P ++ Q).reverse.map (lo nm) ++ S₁ ++ nm.b :: (S₂ ++ Q.map (lo nm)))) := by
  intro Q
  induction Q with
  | nil => intro P S₁ S₂ _ _; exact Reach.of_eq (by simp)
  | cons c Q ih =>
    intro P S₁ S₂ hS₁ hS₂
    have hR : ∀ x ∈ P.reverse.map (lo nm) ++ S₁, YNS nm x := fa_app (fa_map lo_YNS _) hS₁
    have h1 := copy_one hT c (LL := Q.map (lo nm) ++ Z) (by simp [hZ]) hR hS₂
    have h1' : Reach T
        (zl nm.b (.go nm.cs) ((c :: Q).map (lo nm) ++ Z) (P.reverse.map (lo nm) ++ S₁ ++ nm.b :: S₂))
        (zl nm.b (.go nm.cs) (Q.map (lo nm) ++ Z)
          ((P ++ [c]).reverse.map (lo nm) ++ S₁ ++ nm.b :: (S₂ ++ [lo nm c]))) := by
      refine Eq.mpr ?_ h1; simp [zl]
    have h2 := ih (P ++ [c]) S₁ (S₂ ++ [lo nm c]) hS₁ (fa_app hS₂ (fa_cons (lo_YNS c) fa_nil))
    refine h1'.trans (Eq.mpr ?_ h2)
    simp

/-! ## 5. 1 マクロステップ -/

omit hT in
theorem rep_eq (C : CTSH) (m : Nat) (rm v : List Ch) :
    rep nm C m rm v =
      zr nm.b (.go nm.begin) (nm.b :: RA nm C m ++ nm.b :: rm.map (lo nm)).reverse (v.map (lo nm)) := by
  rw [zr_eq]; simp only [rep, tapeList]; congr 1 <;> simp; omega

/-- 相マーカーより左（近い順）: ϕ₁(w_m) · (b · H(m))^R。 -/
abbrev Zl (nm : Names St Ps Sy) (C : CTSH) (m : Nat) : List Sy :=
  (prod C m).map (lo nm) ++ (nm.b :: Sim.Hi (lo nm) nm.st C m).reverse

omit hT in
theorem left_eq (C : CTSH) (m : Nat) (rm : List Ch) :
    (nm.b :: RA nm C m ++ nm.b :: rm.map (lo nm)).reverse =
      (rm.map (lo nm)).reverse ++ nm.b :: (Sim.Lo (lo nm) nm.st C m).reverse ++ nm.b :: Zl nm C m := by
  simp [RA, Sim.RA]

/-- 先頭が Y、相 m ≥ 1（原典 t = 7–14）: begin が y を ∗ に、case_y_1 が区切りの b まで左へ、case_y_2 が区切り 0 の
    ∗ を見て case_n_5 で区切りへ戻り、case_y_3 が相マーカー b まで左へ行って ∗ に → copy_start。 -/
theorem frontY (C : CTSH) (m : Nat) (hm : m ≠ 0) (rm v : List Ch) :
    Reach1 T (rep nm C m rm (.Y :: v))
      (zl nm.b (.go nm.cs) (Zl nm C m)
        (nm.st :: Sim.Lo (lo nm) nm.st C m ++ nm.b :: rm.map (lo nm) ++ nm.st :: v.map (lo nm))) := by
  rw [rep_eq, left_eq, Sim.Lo_ne C m hm]
  simp only [List.map_cons, zr, lo]
  rw [show (rm.map (lo nm)).reverse ++ nm.b ::
        (Sim.LoCore (lo nm) nm.st C m ++ [nm.st]).reverse ++ nm.b :: Zl nm C m =
      (rm.map (lo nm)).reverse ++ nm.b ::
        (nm.st :: ((Sim.LoCore (lo nm) nm.st C m).reverse ++ nm.b :: Zl nm C m)) by simp]
  refine (runL1 (p := nm.begin) (q := nm.cy1) (h := nm.y) (t := nm.st) (by rl)
    (ofP (p_cy1 hT) (fa_rev (fa_map lo_YN _))) nm.b _ _).trans ?_
  refine (Reach.step (stepL (p := nm.cy1) (h := nm.b) (t := nm.b) (q := .go nm.cy2) (by rl)
    nm.st _ _)).trans ?_
  refine (Reach.step (stepR (p := nm.cy2) (h := nm.st) (t := nm.st) (q := .go nm.cn5) (by rl)
    _ nm.b _)).trans ?_
  refine (Reach.step (stepL (p := nm.cn5) (h := nm.b) (t := nm.b) (q := .go nm.cy3) (by rl)
    nm.st _ _)).trans ?_
  refine (sweepL (q := nm.cy3) (X := nm.st :: (Sim.LoCore (lo nm) nm.st C m).reverse)
    (ofP (p_cy3 hT) (fa_cons YNS_st (fa_rev (LoCore_YNS C m)))) nm.b (Zl nm C m) _).trans ?_
  refine (Reach.step (stepL' (p := nm.cy3) (h := nm.b) (t := nm.st) (q := .go nm.cs) (by rl)
    (L := Zl nm C m) (by simp) _)).trans ?_
  exact Reach.of_eq (by simp)

/-- 先頭が Y の相の終わり（原典 t = 52–60, 164–175）: copy_start が次の区切り ∗ を b（新しい相マーカー）にして
    copy_end_1 が区切りの b まで、copy_end_2 が印の ∗ を y に戻して begin。m = k−1 なら左端の b で cycle_end に入り、
    区切りの b で折り返して区切り 0 を相マーカーに。 -/
theorem finishY (C : CTSH) (m : Nat) (hk : m ≤ C.length) (rm v : List Ch) :
    Reach T (zl nm.b (.go nm.cs) (nm.b :: Sim.Hi (lo nm) nm.st C m).reverse
        ((prod C m).reverse.map (lo nm) ++ nm.st :: Sim.Lo (lo nm) nm.st C m ++ nm.b ::
          (rm.map (lo nm) ++ nm.st :: v.map (lo nm))))
      (rep nm C ((m + 1) % C.k) (rm ++ [.Y]) v) := by
  have hLs : ∀ x ∈ (prod C m).reverse.map (lo nm) ++ nm.st :: Sim.Lo (lo nm) nm.st C m, YNS nm x :=
    fa_app (fa_map lo_YNS _) (fa_cons YNS_st (Lo_YNS C m))
  rcases Nat.lt_or_ge m C.length with h | h
  · rw [Nat.mod_eq_of_lt (by simp [CTSH.k]; omega), rep_eq, Sim.Hi_step C m h]
    rw [show (nm.b :: (Sim.Hi (lo nm) nm.st C (m + 1) ++ (prod C (m + 1)).reverse.map (lo nm) ++
          [nm.st])).reverse =
        nm.st :: (nm.b :: Sim.Hi (lo nm) nm.st C (m + 1) ++
          (prod C (m + 1)).reverse.map (lo nm)).reverse by simp]
    simp only [zl]
    refine (runR (p := nm.cs) (q := nm.ce1) (h := nm.st) (t := nm.b) (by rl)
      (ofP (p_ce1 hT) hLs) _ _ _).trans ?_
    refine (runR (p := nm.ce1) (q := nm.ce2) (h := nm.b) (t := nm.b) (by rl)
      (ofP (p_ce2 hT) (fa_map lo_YN _)) _ _ _).trans ?_
    refine (Reach.step (stepR' (p := nm.ce2) (h := nm.st) (t := nm.y) (q := .go nm.begin) (by rl)
      _ _)).trans ?_
    apply Reach.of_eq
    congr 1
    simp [RA, Sim.RA, Sim.Lo_step (lo := lo nm) (st := nm.st) C m hk, lo]
  · have hmk : m = C.length := by omega
    subst hmk
    rw [show (C.length + 1) % C.k = 0 by simp [CTSH.k], rep_eq, Sim.Hi_len]
    simp only [zl, List.reverse_cons, List.reverse_nil, List.nil_append]
    rw [← Sim.Lo_step (lo := lo nm) (st := nm.st) C C.length (Nat.le_refl _)] at hLs ⊢
    refine (runR (p := nm.cs) (q := nm.cyc) (h := nm.b) (t := nm.b) (by rl)
      (ofP (p_cyc hT) hLs) [] _ _).trans ?_
    rw [Sim.Lo_ne C (C.length + 1) (by omega)]
    rw [show (Sim.LoCore (lo nm) nm.st C (C.length + 1) ++ [nm.st]).reverse ++ [nm.b] =
        nm.st :: ((Sim.LoCore (lo nm) nm.st C (C.length + 1)).reverse ++ [nm.b]) by simp]
    refine (Reach.step (stepL (p := nm.cyc) (h := nm.b) (t := nm.b) (q := .go nm.cs) (by rl)
      _ _ _)).trans ?_
    refine (runR (p := nm.cs) (q := nm.ce1) (h := nm.st) (t := nm.b) (by rl) (X := [])
      (fun _ h => nomatch h) _ _ _).trans ?_
    refine (runR (p := nm.ce1) (q := nm.ce2) (h := nm.b) (t := nm.b) (by rl)
      (ofP (p_ce2 hT) (fa_map lo_YN _)) _ _ _).trans ?_
    refine (Reach.step (stepR' (p := nm.ce2) (h := nm.st) (t := nm.y) (q := .go nm.begin) (by rl)
      _ _)).trans ?_
    apply Reach.of_eq
    congr 1
    simp [RA, Sim.RA, Sim.LoCore_full, lo, prod, Sim.Lo]

theorem macroY (C : CTSH) {m : Nat} (h0 : m ≠ 0) (hk : m < C.k) (rm v : List Ch) :
    Reach1 T (rep nm C m rm (.Y :: v)) (rep nm C ((m + 1) % C.k) (rm ++ [.Y]) (v ++ prod C m)) := by
  have hmk : m ≤ C.length := by simp [CTSH.k] at hk; omega
  refine (frontY hT C m h0 rm v).trans ?_
  have hL := copy_loop hT _ (by simp : (nm.b :: Sim.Hi (lo nm) nm.st C m).reverse ≠ []) (prod C m) []
    (nm.st :: Sim.Lo (lo nm) nm.st C m) (rm.map (lo nm) ++ nm.st :: v.map (lo nm))
    (fa_cons YNS_st (Lo_YNS C m)) (fa_app (fa_map lo_YNS _) (fa_cons YNS_st (fa_map lo_YNS _)))
  have hL' : Reach T
      (zl nm.b (.go nm.cs) (Zl nm C m)
        (nm.st :: Sim.Lo (lo nm) nm.st C m ++ nm.b :: rm.map (lo nm) ++ nm.st :: v.map (lo nm)))
      (zl nm.b (.go nm.cs) (nm.b :: Sim.Hi (lo nm) nm.st C m).reverse
        ((prod C m).reverse.map (lo nm) ++ nm.st :: Sim.Lo (lo nm) nm.st C m ++ nm.b ::
          (rm.map (lo nm) ++ nm.st :: (v ++ prod C m).map (lo nm)))) := by
    refine Eq.mpr ?_ hL; simp [Zl]
  exact hL'.trans (finishY hT C m hmk rm (v ++ prod C m))



/-- 先頭が N（任意の相。原典 t = 0–7）: begin が n を ∗ に、case_n_1 が区切りの b まで左へ、case_n_2 が
    相マーカー b まで左へ行って ∗ に → case_n_3。 -/
theorem frontN (C : CTSH) (m : Nat) (rm v : List Ch) :
    Reach1 T (rep nm C m rm (.N :: v))
      (zl nm.b (.go nm.cn3) (Zl nm C m)
        (nm.st :: Sim.Lo (lo nm) nm.st C m ++ nm.b :: (rm.map (lo nm) ++ nm.st :: v.map (lo nm)))) := by
  rw [rep_eq, left_eq]
  simp only [List.map_cons, zr, lo]
  rw [show (rm.map (lo nm)).reverse ++ nm.b :: (Sim.Lo (lo nm) nm.st C m).reverse ++ nm.b :: Zl nm C m =
      (rm.map (lo nm)).reverse ++ nm.b :: ((Sim.Lo (lo nm) nm.st C m).reverse ++ nm.b :: Zl nm C m) by simp]
  refine (runL1 (p := nm.begin) (q := nm.cn1) (h := nm.n) (t := nm.st) (by rl)
    (ofP (p_cn1 hT) (fa_rev (fa_map lo_YN _))) nm.b _ _).trans ?_
  refine (runL (p := nm.cn1) (q := nm.cn2) (h := nm.b) (t := nm.b) (by rl)
    (ofP (p_cn2 hT) (fa_rev (Lo_YNS C m))) nm.b _ _).trans ?_
  refine (Reach.step (stepL' (p := nm.cn2) (h := nm.b) (t := nm.st) (q := .go nm.cn3) (by rl)
    (L := Zl nm C m) (by simp) _)).trans ?_
  exact Reach.of_eq (by simp)

/-- 先頭が N の後半（原典 t = 1–7）: case_n_3 が w_m を左へ越えて次の区切り ∗ を b（新しい相マーカー）に、
    case_n_4 が区切りの b まで、case_n_5 が印の ∗ を n に戻して begin。m = k−1 なら左端の b で case_n_6 に入り、
    区切りの b で折り返して区切り 0 を相マーカーに。 -/
theorem finishN (C : CTSH) (m : Nat) (hk : m ≤ C.length) (rm v : List Ch) :
    Reach T (zl nm.b (.go nm.cn3) (Zl nm C m)
        (nm.st :: Sim.Lo (lo nm) nm.st C m ++ nm.b :: (rm.map (lo nm) ++ nm.st :: v.map (lo nm))))
      (rep nm C ((m + 1) % C.k) (rm ++ [.N]) v) := by
  rcases Nat.lt_or_ge m C.length with h | h
  · rw [Nat.mod_eq_of_lt (by simp [CTSH.k]; omega), rep_eq, Zl, Sim.Hi_step C m h]
    rw [show (prod C m).map (lo nm) ++ (nm.b :: (Sim.Hi (lo nm) nm.st C (m + 1) ++
          (prod C (m + 1)).reverse.map (lo nm) ++ [nm.st])).reverse =
        (prod C m).map (lo nm) ++ nm.st ::
          (nm.b :: Sim.Hi (lo nm) nm.st C (m + 1) ++ (prod C (m + 1)).reverse.map (lo nm)).reverse
        by simp]
    have hS : ∀ x ∈ ((prod C m).map (lo nm)).reverse ++ nm.st :: Sim.Lo (lo nm) nm.st C m, YNS nm x :=
      fa_app (fa_rev (fa_map lo_YNS _)) (fa_cons YNS_st (Lo_YNS C m))
    refine (sweepL (q := nm.cn3) (X := (prod C m).map (lo nm)) (ofP (p_cn3 hT) (fa_map lo_YN _))
      nm.st _ _).trans ?_
    rw [show ((prod C m).map (lo nm)).reverse ++ (nm.st :: Sim.Lo (lo nm) nm.st C m ++
          nm.b :: (rm.map (lo nm) ++ nm.st :: v.map (lo nm))) =
        (((prod C m).map (lo nm)).reverse ++ nm.st :: Sim.Lo (lo nm) nm.st C m) ++
          nm.b :: (rm.map (lo nm) ++ nm.st :: v.map (lo nm)) by simp]
    refine (runR (p := nm.cn3) (q := nm.cn4) (h := nm.st) (t := nm.b) (by rl)
      (ofP (p_cn4 hT) hS) _ _ _).trans ?_
    refine (runR (p := nm.cn4) (q := nm.cn5) (h := nm.b) (t := nm.b) (by rl)
      (ofP (p_cn5 hT) (fa_map lo_YN _)) _ _ _).trans ?_
    refine (Reach.step (stepR' (p := nm.cn5) (h := nm.st) (t := nm.n) (q := .go nm.begin) (by rl)
      _ _)).trans ?_
    apply Reach.of_eq
    congr 1
    simp [RA, Sim.RA, Sim.Lo_step (lo := lo nm) (st := nm.st) C m hk, lo]
  · have hmk : m = C.length := by omega
    subst hmk
    rw [show (C.length + 1) % C.k = 0 by simp [CTSH.k], rep_eq, Zl, Sim.Hi_len]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
    refine (sweepL (q := nm.cn3) (X := (prod C C.length).map (lo nm)) (ofP (p_cn3 hT) (fa_map lo_YN _))
      nm.b [] _).trans ?_
    have hLo := Sim.Lo_step (lo := lo nm) (st := nm.st) C C.length (Nat.le_refl _)
    rw [show ((prod C C.length).map (lo nm)).reverse ++ (nm.st :: Sim.Lo (lo nm) nm.st C C.length ++
          nm.b :: (rm.map (lo nm) ++ nm.st :: v.map (lo nm))) =
        Sim.Lo (lo nm) nm.st C (C.length + 1) ++ nm.b :: (rm.map (lo nm) ++ nm.st :: v.map (lo nm)) by
      simp [hLo]]
    refine (runR (p := nm.cn3) (q := nm.cn6) (h := nm.b) (t := nm.b) (by rl)
      (ofP (p_cn6 hT) (Lo_YNS C _)) [] _ _).trans ?_
    rw [Sim.Lo_ne C (C.length + 1) (by omega)]
    rw [show (Sim.LoCore (lo nm) nm.st C (C.length + 1) ++ [nm.st]).reverse ++ [nm.b] =
        nm.st :: ((Sim.LoCore (lo nm) nm.st C (C.length + 1)).reverse ++ [nm.b]) by simp]
    refine (Reach.step (stepL (p := nm.cn6) (h := nm.b) (t := nm.b) (q := .go nm.cn3) (by rl)
      _ _ _)).trans ?_
    refine (runR (p := nm.cn3) (q := nm.cn4) (h := nm.st) (t := nm.b) (by rl) (X := [])
      (fun _ h => nomatch h) _ _ _).trans ?_
    refine (runR (p := nm.cn4) (q := nm.cn5) (h := nm.b) (t := nm.b) (by rl)
      (ofP (p_cn5 hT) (fa_map lo_YN _)) _ _ _).trans ?_
    refine (Reach.step (stepR' (p := nm.cn5) (h := nm.st) (t := nm.n) (q := .go nm.begin) (by rl)
      _ _)).trans ?_
    apply Reach.of_eq
    congr 1
    simp [RA, Sim.RA, Sim.LoCore_full, lo, prod, Sim.Lo]

theorem macroN (C : CTSH) {m : Nat} (hk : m < C.k) (rm v : List Ch) :
    Reach1 T (rep nm C m rm (.N :: v)) (rep nm C ((m + 1) % C.k) (rm ++ [.N]) v) := by
  have hmk : m ≤ C.length := by simp [CTSH.k] at hk; omega
  exact (frontN hT C m rm v).trans (finishN hT C m hmk rm v)

/-! ## 6. 停止 -/

/-- (λ, m): begin が末尾の b を読んで null。 -/
theorem halt_null (C : CTSH) (m : Nat) (rm : List Ch) :
    Reach1 T (rep nm C m rm []) (finCfg nm C [] m rm) := by
  rw [rep_eq]
  simp only [List.map_nil, zr]
  refine Reach1.of_step (stepZ (p := nm.begin) (h := nm.b) (t := nm.b) (q := .halt nm.null) (by rl)
    _ _) (Reach.of_eq ?_)
  simp only [zc, finCfg, finList, tapeList]
  congr 1
  · simp; omega
  · simpa using tp_trail (bk := nm.b) (nm.b :: (RA nm C m ++ nm.b :: List.map (lo nm) rm))

/-- (Y v, 0): begin が y を ∗ に、case_y_1 が区切りの b まで、case_y_2 が区切り 0 の b で halt（原典 t = 466）。 -/
theorem halt_Y (C : CTSH) (rm v : List Ch) :
    Reach1 T (rep nm C 0 rm (.Y :: v)) (finCfg nm C (.Y :: v) 0 rm) := by
  rw [rep_eq]
  simp only [List.map_cons, zr, lo]
  rw [show (nm.b :: RA nm C 0 ++ nm.b :: rm.map (lo nm)).reverse =
      (rm.map (lo nm)).reverse ++ nm.b :: nm.b :: (nm.b :: Sim.Hi (lo nm) nm.st C 0).reverse by
    simp [RA, Sim.RA_zero]]
  refine (runL1 (p := nm.begin) (q := nm.cy1) (h := nm.y) (t := nm.st) (by rl)
    (ofP (p_cy1 hT) (fa_rev (fa_map lo_YN _))) nm.b _ _).trans ?_
  refine (Reach.step (stepL (p := nm.cy1) (h := nm.b) (t := nm.b) (q := .go nm.cy2) (by rl)
    nm.b _ _)).trans ?_
  refine (Reach.step (stepZ (p := nm.cy2) (h := nm.b) (t := nm.b) (q := .halt nm.halt) (by rl)
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

/-- **主定理（型に依らない形）**。Table 7.5 の 84 本を含む決定的な機械 T は、任意の CTSH C と
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

end URTM.CTSH.U24_4
