/-
  URTM(17,5)（Morita 2017, §7.3.3, Table 7.3。Morita–Yamaguchi 2007 の機械）が
  任意の CTSH を模倣することの一般証明。

  この証明は機械の**型に依存しない**: 状態・記号・疑似状態の型は任意で、それらの名前
  （`Names`）と、Table 7.3 の 69 本の五つ組（`rules`、停止の 2 本を含む）がすべて機械 T に
  含まれること（`hT`）だけを仮定する。逆向き（U17_5 の停止 ⇒ CTSH の停止）では T の決定性も使う。
  生成モジュール `URTM.Gen.K17_5`（(17,5) そのもの）と、定理 B の入力になる
  `URTM.Gen.K17_5_b21` / `K17_5_b22`（同じ記述ファイルから生成されるが型が別）に、
  同じ証明を `CTSH17_5Main.lean` で具体化する。仮定 `hT` と `rules` = T（集合として）は
  そこで `decide` により記述ファイルの表そのものと照合する。

  記号 b y n ∗ $、状態 begin case_y_1 case_y_2 copy_start copy_y_1..3 copy_n_1..3
  copy_end_1 copy_end_2 cycle_end case_n_1..4、疑似状態 halt null（原典の名前）。

  不変量 `rep C m rm v`（CTSH の ID (v, m) と消去済みの記号列 rm）: 状態 begin、テープ

      b · RA(m) · $ · ϕ₁(rm) · ϕ₁(v) · b b …

  ヘッドは ϕ₁(v) の先頭（v = λ なら直後の b）。U17_5 では規則も消去済みの記号も小文字のまま
  （原典 p. 188「the leftmost symbol of the current string is indicated by the symbol $ or b」）。
  RA(m) = H(m) · ϕ₁(w^R_m) · b · Lo(m) で、b が相マーカー（区切り m）。

  U15_6（CTSH15_6.lean）はコピー以外の規則が U17_5 と記号名まで一致するので、コピー以外の名前
  （`Core`）・規則（`Core.rules`、45 本）・不変量と、コピー 1 文字の補題を仮定とする模倣の証明
  （`Core.simulates`）をここに置き、両機械で共有する。ジッパーと模倣の枠組みは CTSHSim.lean。

  計画・補題の分解・検証の記録は docs/08_ctsh17_lean_2026-09-26.md。mathlib 非依存。
  未証明の穴・新規公理・native_decide を使わない。
-/
import URTM.CTSHSim

namespace URTM.CTSH.U17_5

open URTM URTM.KState URTM.CTSH URTM.CTSH.Sim

/-! ## 0. 機械の名前 -/

/-- U17_5 と U15_6 に共通の、コピー以外の記号・状態・疑似状態の名前。 -/
structure Core (St Ps Sy : Type) where
  b : Sy
  y : Sy
  n : Sy
  st : Sy   -- ∗
  dl : Sy   -- $
  begin : St
  cy1 : St
  cy2 : St
  cs : St
  ce1 : St
  ce2 : St
  cyc : St
  cn1 : St
  cn2 : St
  cn3 : St
  cn4 : St
  halt : Ps
  null : Ps

/-- U17_5 の記号・状態・疑似状態の名前（`Core` にコピーの 6 状態を加えたもの）。 -/
structure Names (St Ps Sy : Type) extends Core St Ps Sy where
  cpy1 : St
  cpy2 : St
  cpy3 : St
  cpn1 : St
  cpn2 : St
  cpn3 : St

/-! ## 1. 共通部分: 符号化・規則・模倣（U17_5 と U15_6 で共有） -/

namespace Core

section
variable {St Ps Sy : Type} (nm : Core St Ps Sy)

/-- ϕ₁: Y ↦ y, N ↦ n。 -/
def lo : Ch → Sy
  | .Y => nm.y
  | .N => nm.n

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

/-- 停止配置のテープ（リスト）。
    * 最終 ID (λ, m): begin が末尾の b を $ に変え、case_y_2 が $ まで左へ戻って null。
      テープは `b · RA(m) · $ · ϕ₁(rm) · $`。
    * 最終 ID (Y v, 0): begin が先頭の y を $ に変え、case_y_1 が本来の $ を b に変えて
      区切り 0 の b で halt。テープは `b · RA(0) · b · ϕ₁(rm) · $ · ϕ₁(v)`
      （原典 p. 189「$ should be read as Y」: 最終文字列 Y v の Y が $ で書かれている）。 -/
def finList (C : CTSH) (vf : List Ch) (mf : Nat) (rm : List Ch) : List Sy :=
  match vf with
  | [] => tapeList nm C mf rm [] ++ [nm.dl]
  | _ :: v => nm.b :: RA nm C 0 ++ nm.b :: rm.map (lo nm) ++ nm.dl :: v.map (lo nm)

/-- 停止配置。(λ, m) なら疑似状態 null でヘッドは本来の $、(Y v, 0) なら halt でヘッドは区切り 0。 -/
def finCfg (C : CTSH) (vf : List Ch) (mf : Nat) (rm : List Ch) : Cfg St Ps Sy :=
  match vf with
  | [] => { st := .halt nm.null, pos := (RA nm C mf).length + 1, tape := tp nm.b (finList nm C [] mf rm) }
  | c :: v => { st := .halt nm.halt, pos := (RA nm C 0).length, tape := tp nm.b (finList nm C (c :: v) 0 rm) }

/-- コピー以外の 45 本（Table 7.3 の該当行を同じ順に）。 -/
def rules : List (Rule St Ps Sy) :=
  let b := nm.b; let y := nm.y; let n := nm.n; let s := nm.st; let d := nm.dl
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
    ⟨nm.cs, s, b, .R, .go nm.ce1⟩,
    ⟨nm.cs, b, b, .R, .go nm.cyc⟩,
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

/-- {y, n}。 -/
def YN (x : Sy) : Prop := x = nm.y ∨ x = nm.n
/-- {y, n, ∗}。 -/
def YNS (x : Sy) : Prop := x = nm.y ∨ x = nm.n ∨ x = nm.st
/-- {y, n, ∗, $}。 -/
def YNSD (x : Sy) : Prop := x = nm.y ∨ x = nm.n ∨ x = nm.st ∨ x = nm.dl

end

/-! ### 記号クラスと規則領域の漸化式 -/

section Sets
variable {St Ps Sy : Type} {nm : Core St Ps Sy}

theorem YN_YNS : ∀ x, YN nm x → YNS nm x := by
  rintro x (h | h) <;> simp [YNS, h]
theorem YNS_YNSD : ∀ x, YNS nm x → YNSD nm x := by
  rintro x (h | h | h) <;> simp [YNSD, h]

theorem lo_YN1 (c : Ch) : YN nm (lo nm c) := by cases c <;> simp [YN, lo]
theorem lo_YNS1 (c : Ch) : YNS nm (lo nm c) := YN_YNS _ (lo_YN1 c)
theorem lo_YN (w : List Ch) : ∀ x ∈ w.map (lo nm), YN nm x := fa_map lo_YN1 w
theorem lo_YNS (w : List Ch) : ∀ x ∈ w.map (lo nm), YNS nm x := ofP YN_YNS (lo_YN w)
theorem lo_YNSD (w : List Ch) : ∀ x ∈ w.map (lo nm), YNSD nm x := ofP YNS_YNSD (lo_YNS w)

theorem YNS_st : YNS nm nm.st := by simp [YNS]
theorem YNSD_st : YNSD nm nm.st := by simp [YNSD]
theorem YNSD_dl : YNSD nm nm.dl := by simp [YNSD]

theorem Hi_YNS (C : CTSH) (m : Nat) : ∀ x ∈ Hi nm C m, YNS nm x := Hi_mem lo_YNS1 YNS_st C m
theorem LoCore_YNS (C : CTSH) (m : Nat) : ∀ x ∈ LoCore nm C m, YNS nm x :=
  LoCore_mem lo_YNS1 YNS_st C m
theorem Lo_YNS (C : CTSH) (m : Nat) : ∀ x ∈ Lo nm C m, YNS nm x := Lo_mem lo_YNS1 YNS_st C m
theorem Lo_YNSD (C : CTSH) (m : Nat) : ∀ x ∈ Lo nm C m, YNSD nm x := ofP YNS_YNSD (Lo_YNS C m)

theorem Hi_step (C : CTSH) (m : Nat) (h : m < C.length) :
    Hi nm C m = Hi nm C (m + 1) ++ (prod C (m + 1)).reverse.map (lo nm) ++ [nm.st] :=
  Sim.Hi_step C m h
theorem Hi_len (C : CTSH) : Hi nm C C.length = [] := Sim.Hi_len C
theorem Lo_step (C : CTSH) (m : Nat) (h : m ≤ C.length) :
    Lo nm C (m + 1) = (prod C m).reverse.map (lo nm) ++ nm.st :: Lo nm C m := Sim.Lo_step C m h
theorem Lo_ne (C : CTSH) (m : Nat) (h : m ≠ 0) : Lo nm C m = LoCore nm C m ++ [nm.st] :=
  Sim.Lo_ne C m h
theorem LoCore_full (C : CTSH) : LoCore nm C (C.length + 1) = Hi nm C 0 := Sim.LoCore_full C

theorem rep_eq (C : CTSH) (m : Nat) (rm v : List Ch) :
    rep nm C m rm v =
      zr nm.b (.go nm.begin) (nm.b :: RA nm C m ++ nm.dl :: rm.map (lo nm)).reverse (v.map (lo nm)) := by
  rw [zr_eq]; simp only [rep, tapeList]; congr 1 <;> simp; omega

end Sets

/-- `∀ x ∈ X, P x`（P は YN / YNS / YNSD）を、X の連結・cons・反転に沿って分解して閉じる。 -/
local macro "fa" : tactic =>
  `(tactic| (repeat (first
    | exact fa_nil | exact lo_YN _ | exact lo_YNS _ | exact lo_YNSD _
    | exact Lo_YNS _ _ | exact Lo_YNSD _ _ | exact LoCore_YNS _ _ | exact Hi_YNS _ _
    | exact YNS_st | exact YNSD_st | exact YNSD_dl
    | apply fa_app | apply fa_cons | apply fa_rev)))

/-! ### 規則表から読み取る掃引 -/

section Main
variable {St Ps Sy : Type} {nm : Core St Ps Sy} {T : Machine St Ps Sy}
  (hT : ∀ r ∈ rules nm, r ∈ T)
include hT

set_option hygiene false in
/-- 規則 `r` がコピー以外の 45 本にあるので T にある。 -/
local macro "rl" : tactic =>
  `(tactic| (apply hT; simp only [rules]; repeat (first | exact List.Mem.head _ | apply List.Mem.tail)))

theorem p_cy1 : ∀ x, YN nm x → (⟨nm.cy1, x, x, .L, .go nm.cy1⟩ : Rule St Ps Sy) ∈ T := by
  rintro x (rfl | rfl) <;> rl
theorem p_cn2 : ∀ x, YN nm x → (⟨nm.cn2, x, x, .L, .go nm.cn2⟩ : Rule St Ps Sy) ∈ T := by
  rintro x (rfl | rfl) <;> rl
theorem p_cy2 : ∀ x, YNS nm x → (⟨nm.cy2, x, x, .L, .go nm.cy2⟩ : Rule St Ps Sy) ∈ T := by
  rintro x (rfl | rfl | rfl) <;> rl
theorem p_ce1 : ∀ x, YNS nm x → (⟨nm.ce1, x, x, .R, .go nm.ce1⟩ : Rule St Ps Sy) ∈ T := by
  rintro x (rfl | rfl | rfl) <;> rl
theorem p_ce2 : ∀ x, YNS nm x → (⟨nm.ce2, x, x, .R, .go nm.ce2⟩ : Rule St Ps Sy) ∈ T := by
  rintro x (rfl | rfl | rfl) <;> rl
theorem p_cyc : ∀ x, YNS nm x → (⟨nm.cyc, x, x, .R, .go nm.cyc⟩ : Rule St Ps Sy) ∈ T := by
  rintro x (rfl | rfl | rfl) <;> rl
theorem p_cn4 : ∀ x, YNS nm x → (⟨nm.cn4, x, x, .R, .go nm.cn4⟩ : Rule St Ps Sy) ∈ T := by
  rintro x (rfl | rfl | rfl) <;> rl
theorem p_cn1 : ∀ x, YNSD nm x → (⟨nm.cn1, x, x, .L, .go nm.cn1⟩ : Rule St Ps Sy) ∈ T := by
  rintro x (rfl | rfl | rfl | rfl) <;> rl
theorem p_cn3 : ∀ x, YNSD nm x → (⟨nm.cn3, x, x, .R, .go nm.cn3⟩ : Rule St Ps Sy) ∈ T := by
  rintro x (rfl | rfl | rfl | rfl) <;> rl

/-! ### コピー（1 文字のコピー `hcp` は機械ごとに示す） -/

omit hT in
/-- 規則を 1 文字ずつ右端に書き足す繰り返し。1 文字のコピー `hcp`（copy_start が規則の文字 c を
    印し、右端に c を書き足して印まで戻る）から得る。 -/
theorem copy_loop
    (hcp : ∀ (c : Ch) {LL : List Sy}, LL ≠ [] → ∀ {R : List Sy}, (∀ x ∈ R, YNSD nm x) →
      Reach T (zc nm.b (.go nm.cs) LL (lo nm c) R) (zl nm.b (.go nm.cs) LL (lo nm c :: R ++ [lo nm c])))
    (Z : List Sy) (hZ : Z ≠ []) :
    ∀ (Q P : List Ch) (S : List Sy), (∀ x ∈ S, YNSD nm x) →
    Reach T (zl nm.b (.go nm.cs) (Q.map (lo nm) ++ Z) (P.reverse.map (lo nm) ++ S))
      (zl nm.b (.go nm.cs) Z ((P ++ Q).reverse.map (lo nm) ++ S ++ Q.map (lo nm))) := by
  intro Q
  induction Q with
  | nil => intro P S _; exact Reach.of_eq (by simp)
  | cons c Q ih =>
    intro P S hS
    have h1 := hcp c (LL := Q.map (lo nm) ++ Z) (by simp [hZ]) (R := P.reverse.map (lo nm) ++ S)
      (fa_app (lo_YNSD _) hS)
    have h2 := ih (P ++ [c]) (S ++ [lo nm c]) (fa_app hS (fa_cons (YNS_YNSD _ (lo_YNS1 c)) fa_nil))
    refine h1.trans (Eq.mpr ?_ h2)
    simp

/-! ### 1 マクロステップ -/

/-- 先頭が Y、相 m ≥ 1（原典 t = 7–14）: begin が y を $ に、case_y_1 が本来の $ まで左へ
    （そこを一旦 b に）、区切り 0 が ∗ なので begin へ戻って $ を書き直し、case_y_2 が相マーカー b
    まで左へ行って ∗ に → copy_start。 -/
theorem frontY (C : CTSH) (m : Nat) (hm : m ≠ 0) (rm v : List Ch) :
    Reach1 T (rep nm C m rm (.Y :: v))
      (zl nm.b (.go nm.cs) ((prod C m).map (lo nm) ++ (nm.b :: Hi nm C m).reverse)
        (nm.st :: Lo nm C m ++ nm.dl :: rm.map (lo nm) ++ nm.dl :: v.map (lo nm))) := by
  rw [rep_eq]
  simp only [List.map_cons, zr, lo]
  rw [show (nm.b :: RA nm C m ++ nm.dl :: rm.map (lo nm)).reverse =
      (rm.map (lo nm)).reverse ++ nm.dl :: nm.st :: ((LoCore nm C m).reverse ++ nm.b ::
        (nm.b :: Hi nm C m ++ (prod C m).reverse.map (lo nm)).reverse) by
    simp [RA, Sim.RA, Lo_ne C m hm]]
  refine (runL1 (p := nm.begin) (q := nm.cy1) (h := nm.y) (t := nm.dl) (by rl)
    (ofP (p_cy1 hT) (fa_rev (lo_YN _))) nm.dl _ _).trans ?_
  refine (Reach.step (stepL (p := nm.cy1) (h := nm.dl) (t := nm.b) (q := .go nm.cy1) (by rl)
    nm.st _ _)).trans ?_
  refine (Reach.step (stepR (p := nm.cy1) (h := nm.st) (t := nm.st) (q := .go nm.begin) (by rl)
    _ nm.b _)).trans ?_
  refine (Reach.step (stepL (p := nm.begin) (h := nm.b) (t := nm.dl) (q := .go nm.cy2) (by rl)
    nm.st _ _)).trans ?_
  refine (sweepL (q := nm.cy2) (X := nm.st :: (LoCore nm C m).reverse)
    (ofP (p_cy2 hT) (fa_cons YNS_st (fa_rev (LoCore_YNS C m)))) nm.b _ _).trans ?_
  refine (Reach.step (stepL' (p := nm.cy2) (h := nm.b) (t := nm.st) (q := .go nm.cs) (by rl)
    (L := (nm.b :: Hi nm C m ++ (prod C m).reverse.map (lo nm)).reverse) (by simp) _)).trans ?_
  exact Reach.of_eq (by simp [Lo_ne C m hm])

/-- 先頭が Y の相の終わり（原典 t = 52–60, 164–175）: copy_start が次の区切り ∗ を b（新しい相マーカー）に
    して copy_end_1 → copy_end_2 が印の $ を y に戻して begin。m = k−1 なら左端の b で cycle_end に入り、
    $ で折り返して区切り 0 を相マーカーに。 -/
theorem finishY (C : CTSH) (m : Nat) (hm : m ≠ 0) (hk : m ≤ C.length) (rm v : List Ch) :
    Reach T (zl nm.b (.go nm.cs) (nm.b :: Hi nm C m).reverse
        ((prod C m).reverse.map (lo nm) ++ nm.st :: Lo nm C m ++ nm.dl :: rm.map (lo nm) ++
          nm.dl :: v.map (lo nm)))
      (rep nm C ((m + 1) % C.k) (rm ++ [.Y]) v) := by
  have hLs : ∀ x ∈ (prod C m).reverse.map (lo nm) ++ nm.st :: Lo nm C m, YNS nm x :=
    fa_app (lo_YNS _) (fa_cons YNS_st (Lo_YNS C m))
  rcases Nat.lt_or_ge m C.length with h | h
  · rw [Nat.mod_eq_of_lt (by simp [CTSH.k]; omega), rep_eq, Hi_step C m h]
    rw [show (nm.b :: (Hi nm C (m + 1) ++ (prod C (m + 1)).reverse.map (lo nm) ++ [nm.st])).reverse =
        nm.st :: (nm.b :: Hi nm C (m + 1) ++ (prod C (m + 1)).reverse.map (lo nm)).reverse by simp]
    simp only [zl]
    rw [show (prod C m).reverse.map (lo nm) ++ nm.st :: Lo nm C m ++ nm.dl :: rm.map (lo nm) ++
          nm.dl :: v.map (lo nm) =
        ((prod C m).reverse.map (lo nm) ++ nm.st :: Lo nm C m) ++ nm.dl ::
          (rm.map (lo nm) ++ nm.dl :: v.map (lo nm)) by simp]
    refine (runR (p := nm.cs) (q := nm.ce1) (h := nm.st) (t := nm.b) (by rl)
      (ofP (p_ce1 hT) hLs) _ _ _).trans ?_
    refine (runR (p := nm.ce1) (q := nm.ce2) (h := nm.dl) (t := nm.dl) (by rl)
      (ofP (p_ce2 hT) (lo_YNS _)) _ _ _).trans ?_
    refine (Reach.step (stepR' (p := nm.ce2) (h := nm.dl) (t := nm.y) (q := .go nm.begin) (by rl)
      _ _)).trans ?_
    apply Reach.of_eq
    congr 1
    simp [RA, Sim.RA, Lo_step (nm := nm) C m hk, lo]
  · have hmk : m = C.length := by omega
    subst hmk
    rw [show (C.length + 1) % C.k = 0 by simp [CTSH.k], rep_eq, Hi_len]
    simp only [zl, List.reverse_cons, List.reverse_nil, List.nil_append]
    rw [← Lo_step (nm := nm) C C.length (Nat.le_refl _)] at hLs ⊢
    rw [show Lo nm C (C.length + 1) ++ nm.dl :: rm.map (lo nm) ++ nm.dl :: v.map (lo nm) =
        Lo nm C (C.length + 1) ++ nm.dl :: (rm.map (lo nm) ++ nm.dl :: v.map (lo nm)) by simp]
    refine (runR (p := nm.cs) (q := nm.cyc) (h := nm.b) (t := nm.b) (by rl)
      (ofP (p_cyc hT) hLs) [] _ _).trans ?_
    rw [Lo_ne C (C.length + 1) (by omega)]
    rw [show (LoCore nm C (C.length + 1) ++ [nm.st]).reverse ++ [nm.b] =
        nm.st :: ((LoCore nm C (C.length + 1)).reverse ++ [nm.b]) by simp]
    refine (Reach.step (stepL (p := nm.cyc) (h := nm.dl) (t := nm.dl) (q := .go nm.cs) (by rl)
      _ _ _)).trans ?_
    refine (Reach.step (stepR (p := nm.cs) (h := nm.st) (t := nm.b) (q := .go nm.ce1) (by rl)
      _ _ _)).trans ?_
    refine (runR (p := nm.ce1) (q := nm.ce2) (h := nm.dl) (t := nm.dl) (by rl)
      (X := rm.map (lo nm)) (ofP (p_ce2 hT) (lo_YNS _)) _ _ _).trans ?_
    refine (Reach.step (stepR' (p := nm.ce2) (h := nm.dl) (t := nm.y) (q := .go nm.begin) (by rl)
      _ _)).trans ?_
    apply Reach.of_eq
    congr 1
    simp [RA, Sim.RA, LoCore_full, lo, prod, Sim.Lo]

/-- 先頭が N（任意の相。原典 t = 0–7）: begin が n を b（印）に、case_n_1 が相マーカー b まで左へ行って ∗ に。 -/
theorem frontN (C : CTSH) (m : Nat) (rm v : List Ch) :
    Reach1 T (rep nm C m rm (.N :: v))
      (zc nm.b (.go nm.cn1) (nm.b :: Hi nm C m ++ (prod C m).reverse.map (lo nm)).reverse nm.b
        (Lo nm C m ++ nm.dl :: rm.map (lo nm) ++ nm.b :: v.map (lo nm))) := by
  rw [rep_eq]
  simp only [List.map_cons, zr, lo]
  rw [show (nm.b :: RA nm C m ++ nm.dl :: rm.map (lo nm)).reverse =
      ((rm.map (lo nm)).reverse ++ nm.dl :: (Lo nm C m).reverse) ++ nm.b ::
        (nm.b :: Hi nm C m ++ (prod C m).reverse.map (lo nm)).reverse by simp [RA, Sim.RA]]
  refine (runL1 (p := nm.begin) (q := nm.cn1) (h := nm.n) (t := nm.b) (by rl)
    (ofP (p_cn1 hT) (fa_app (fa_rev (lo_YNSD _)) (fa_cons YNSD_dl (fa_rev (Lo_YNSD C m)))))
    nm.b _ _).trans ?_
  exact Reach.of_eq (by simp)

/-- 先頭が N の後半（原典 t = 1–7）: case_n_2 が w_m を左へ越えて次の区切り ∗ を b（新しい相マーカー）に、
    case_n_3 が印の b を n に戻して begin。m = k−1 なら左端の b で case_n_4 に入り、$ で折り返して
    区切り 0 を相マーカーに。 -/
theorem finishN (C : CTSH) (m : Nat) (hk : m ≤ C.length) (rm v : List Ch) :
    Reach T (zc nm.b (.go nm.cn1) (nm.b :: Hi nm C m ++ (prod C m).reverse.map (lo nm)).reverse nm.b
        (Lo nm C m ++ nm.dl :: rm.map (lo nm) ++ nm.b :: v.map (lo nm)))
      (rep nm C ((m + 1) % C.k) (rm ++ [.N]) v) := by
  rcases Nat.lt_or_ge m C.length with h | h
  · rw [Nat.mod_eq_of_lt (by simp [CTSH.k]; omega), rep_eq, Hi_step C m h]
    rw [show (nm.b :: (Hi nm C (m + 1) ++ (prod C (m + 1)).reverse.map (lo nm) ++ [nm.st]) ++
          (prod C m).reverse.map (lo nm)).reverse =
        (prod C m).map (lo nm) ++ nm.st ::
          (nm.b :: Hi nm C (m + 1) ++ (prod C (m + 1)).reverse.map (lo nm)).reverse by simp]
    refine (runL (p := nm.cn1) (q := nm.cn2) (h := nm.b) (t := nm.st) (by rl)
      (ofP (p_cn2 hT) (lo_YN _)) nm.st _ _).trans ?_
    rw [show ((prod C m).map (lo nm)).reverse ++ nm.st ::
          (Lo nm C m ++ nm.dl :: rm.map (lo nm) ++ nm.b :: v.map (lo nm)) =
        (((prod C m).map (lo nm)).reverse ++ nm.st :: (Lo nm C m ++ nm.dl :: rm.map (lo nm))) ++
          nm.b :: v.map (lo nm) by simp]
    refine (runR (p := nm.cn2) (q := nm.cn3) (h := nm.st) (t := nm.b) (by rl)
      (ofP (p_cn3 hT) (by fa)) _ _ _).trans ?_
    refine (Reach.step (stepR' (p := nm.cn3) (h := nm.b) (t := nm.n) (q := .go nm.begin) (by rl)
      _ _)).trans ?_
    apply Reach.of_eq
    congr 1
    simp [RA, Sim.RA, Lo_step (nm := nm) C m hk, lo]
  · have hmk : m = C.length := by omega
    subst hmk
    rw [show (C.length + 1) % C.k = 0 by simp [CTSH.k], rep_eq, Hi_len]
    rw [show ([nm.b] ++ (prod C C.length).reverse.map (lo nm)).reverse =
        (prod C C.length).map (lo nm) ++ nm.b :: [] by simp]
    refine (runL (p := nm.cn1) (q := nm.cn2) (h := nm.b) (t := nm.st) (by rl)
      (ofP (p_cn2 hT) (lo_YN _)) nm.b [] _).trans ?_
    rw [show ((prod C C.length).map (lo nm)).reverse ++ nm.st ::
          (Lo nm C C.length ++ nm.dl :: rm.map (lo nm) ++ nm.b :: v.map (lo nm)) =
        Lo nm C (C.length + 1) ++ nm.dl :: (rm.map (lo nm) ++ nm.b :: v.map (lo nm)) by
      rw [Lo_step (nm := nm) C C.length (Nat.le_refl _)]; simp]
    refine (runR (p := nm.cn2) (q := nm.cn4) (h := nm.b) (t := nm.b) (by rl)
      (ofP (p_cn4 hT) (Lo_YNS C _)) [] _ _).trans ?_
    rw [Lo_ne C (C.length + 1) (by omega)]
    rw [show (LoCore nm C (C.length + 1) ++ [nm.st]).reverse ++ [nm.b] =
        nm.st :: ((LoCore nm C (C.length + 1)).reverse ++ [nm.b]) by simp]
    refine (Reach.step (stepL (p := nm.cn4) (h := nm.dl) (t := nm.dl) (q := .go nm.cn2) (by rl)
      _ _ _)).trans ?_
    rw [show nm.dl :: (rm.map (lo nm) ++ nm.b :: v.map (lo nm)) =
        (nm.dl :: rm.map (lo nm)) ++ nm.b :: v.map (lo nm) by simp]
    refine (runR (p := nm.cn2) (q := nm.cn3) (h := nm.st) (t := nm.b) (by rl)
      (ofP (p_cn3 hT) (fa_cons YNSD_dl (lo_YNSD _))) _ _ _).trans ?_
    refine (Reach.step (stepR' (p := nm.cn3) (h := nm.b) (t := nm.n) (q := .go nm.begin) (by rl)
      _ _)).trans ?_
    apply Reach.of_eq
    congr 1
    simp [RA, Sim.RA, LoCore_full, lo, prod, Sim.Lo]

/-! ### 停止 -/

/-- (λ, m): begin が末尾の b を $ に、case_y_2 が本来の $ まで左へ戻って null（原典 urtm17-5.txt の
    「Halts when the string becomes null」）。 -/
theorem halt_null (C : CTSH) (m : Nat) (rm : List Ch) :
    Reach1 T (rep nm C m rm []) (finCfg nm C [] m rm) := by
  rw [rep_eq]
  simp only [List.map_nil, zr]
  rw [show (nm.b :: RA nm C m ++ nm.dl :: rm.map (lo nm)).reverse =
      (rm.map (lo nm)).reverse ++ nm.dl :: (nm.b :: RA nm C m).reverse by simp]
  refine (runL1 (p := nm.begin) (q := nm.cy2) (h := nm.b) (t := nm.dl) (by rl)
    (ofP (p_cy2 hT) (fa_rev (lo_YNS _))) nm.dl _ _).trans ?_
  refine (Reach.step (stepZ (p := nm.cy2) (h := nm.dl) (t := nm.dl) (q := .halt nm.null) (by rl)
    _ _)).trans ?_
  apply Reach.of_eq
  simp only [zc, finCfg, finList, tapeList]
  congr 1
  · simp <;> omega
  · simp

/-- (Y v, 0): begin が y を $ に、case_y_1 が本来の $ を b にして、区切り 0 の b で halt（原典 t = 466）。 -/
theorem halt_Y (C : CTSH) (rm v : List Ch) :
    Reach1 T (rep nm C 0 rm (.Y :: v)) (finCfg nm C (.Y :: v) 0 rm) := by
  rw [rep_eq]
  simp only [List.map_cons, zr, lo]
  rw [show (nm.b :: RA nm C 0 ++ nm.dl :: rm.map (lo nm)).reverse =
      (rm.map (lo nm)).reverse ++ nm.dl :: nm.b :: (nm.b :: Hi nm C 0).reverse by
    simp [RA, Sim.RA_zero]]
  refine (runL1 (p := nm.begin) (q := nm.cy1) (h := nm.y) (t := nm.dl) (by rl)
    (ofP (p_cy1 hT) (fa_rev (lo_YN _))) nm.dl _ _).trans ?_
  refine (Reach.step (stepL (p := nm.cy1) (h := nm.dl) (t := nm.b) (q := .go nm.cy1) (by rl)
    nm.b _ _)).trans ?_
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

/-- **共通部分の模倣**: コピー以外の 45 本を含む決定的な機械 T が 1 文字のコピー `hcp` もできるなら、
    `rep nm C 0 [] w` から (10,8) 版と同じ 3 項が成り立つ（`simulates_of`）。 -/
theorem simulates
    (hcp : ∀ (c : Ch) {LL : List Sy}, LL ≠ [] → ∀ {R : List Sy}, (∀ x ∈ R, YNSD nm x) →
      Reach T (zc nm.b (.go nm.cs) LL (lo nm c) R) (zl nm.b (.go nm.cs) LL (lo nm c :: R ++ [lo nm c])))
    (hD : Deterministic T) (C : CTSH) (w : List Ch) :
    (∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) →
      ∃ N rm, n ≤ N ∧ HaltsIn T N (rep nm C 0 [] w) (finCfg nm C vf mf rm)) ∧
    (∀ N e, HaltsIn T N (rep nm C 0 [] w) e →
      ∃ n vf mf rm, CHaltsIn C n (w, 0) (vf, mf) ∧ e = finCfg nm C vf mf rm) ∧
    ((∀ n f, ¬ CHaltsIn C n (w, 0) f) ↔ (∀ N e, ¬ HaltsIn T N (rep nm C 0 [] w) e)) := by
  refine simulates_of_steps C (rep nm C) (finCfg nm C) hD (fun {m} h0 hk rm v => ?_)
    (fun {m} hk rm v => ?_) (halt_Y hT C) (halt_null hT C) (finCfg_halted C) w
  · -- 先頭が Y: 前半 → コピー → 後半
    have hmk : m ≤ C.length := by simp [CTSH.k] at hk; omega
    refine (frontY hT C m h0 rm v).trans ?_
    have hS : ∀ x ∈ nm.st :: Lo nm C m ++ nm.dl :: rm.map (lo nm) ++ nm.dl :: v.map (lo nm),
        YNSD nm x := by fa
    refine (copy_loop hcp _ (by simp : (nm.b :: Hi nm C m).reverse ≠ []) (prod C m) [] _ hS).trans ?_
    exact Eq.mpr (by simp) (finishY hT C m h0 hmk rm (v ++ prod C m))
  · have hmk : m ≤ C.length := by simp [CTSH.k] at hk; omega
    exact (frontN hT C m rm v).trans (finishN hT C m hmk rm v)

end Main

end Core

/-! ## 2. U17_5 の規則表と符号化 -/

section
variable {St Ps Sy : Type} (nm : Names St Ps Sy)

/-- Table 7.3（urtm17-5.txt の五つ組を、記述ファイルの順に、名前で書いたもの）。
    `CTSH17_5Main.lean` で生成モジュールの表と集合として一致することを `decide` で確かめる。 -/
def rules : List (Rule St Ps Sy) :=
  let b := nm.b; let y := nm.y; let n := nm.n; let s := nm.st; let d := nm.dl
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
    ⟨nm.cs, y, b, .R, .go nm.cpy1⟩,
    ⟨nm.cs, n, b, .R, .go nm.cpn1⟩,
    ⟨nm.cs, s, b, .R, .go nm.ce1⟩,
    ⟨nm.cs, b, b, .R, .go nm.cyc⟩,
    ⟨nm.cpy1, y, y, .R, .go nm.cpy1⟩,
    ⟨nm.cpy1, n, n, .R, .go nm.cpy1⟩,
    ⟨nm.cpy1, s, s, .R, .go nm.cpy1⟩,
    ⟨nm.cpy1, d, d, .R, .go nm.cpy1⟩,
    ⟨nm.cpy1, b, y, .R, .go nm.cpy2⟩,
    ⟨nm.cpy2, b, b, .L, .go nm.cpy3⟩,
    ⟨nm.cpy3, y, y, .L, .go nm.cpy3⟩,
    ⟨nm.cpy3, n, n, .L, .go nm.cpy3⟩,
    ⟨nm.cpy3, s, s, .L, .go nm.cpy3⟩,
    ⟨nm.cpy3, d, d, .L, .go nm.cpy3⟩,
    ⟨nm.cpy3, b, y, .L, .go nm.cs⟩,
    ⟨nm.cpn1, y, y, .R, .go nm.cpn1⟩,
    ⟨nm.cpn1, n, n, .R, .go nm.cpn1⟩,
    ⟨nm.cpn1, s, s, .R, .go nm.cpn1⟩,
    ⟨nm.cpn1, d, d, .R, .go nm.cpn1⟩,
    ⟨nm.cpn1, b, n, .R, .go nm.cpn2⟩,
    ⟨nm.cpn2, b, b, .L, .go nm.cpn3⟩,
    ⟨nm.cpn3, y, y, .L, .go nm.cpn3⟩,
    ⟨nm.cpn3, n, n, .L, .go nm.cpn3⟩,
    ⟨nm.cpn3, s, s, .L, .go nm.cpn3⟩,
    ⟨nm.cpn3, d, d, .L, .go nm.cpn3⟩,
    ⟨nm.cpn3, b, n, .L, .go nm.cs⟩,
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

/-- ϕ₁: Y ↦ y, N ↦ n。 -/
def lo : Ch → Sy := Core.lo nm.toCore
/-- 規則領域 RA(m)。 -/
def RA (C : CTSH) (m : Nat) : List Sy := Core.RA nm.toCore C m
/-- テープの中身: b · RA(m) · $ · ϕ₁(rm) · ϕ₁(v)。 -/
def tapeList (C : CTSH) (m : Nat) (rm v : List Ch) : List Sy := Core.tapeList nm.toCore C m rm v
/-- CTSH の ID (v, m) と消去済みの記号列 rm を表す配置（`Core.rep`）。 -/
def rep (C : CTSH) (m : Nat) (rm v : List Ch) : Cfg St Ps Sy := Core.rep nm.toCore C m rm v

/-- **Morita の符号化**（原典 p. 183, 188: U17_5 の初期 ID は U13_7 と同じ）:
    `b ϕ₁(w^R_{k−1}) ∗ ⋯ ∗ ϕ₁(w^R_1) ∗ b $ q_begin ϕ₁(w) b`。 -/
def encC (C : CTSH) (w : List Ch) : Cfg St Ps Sy := rep nm C 0 [] w

/-- 停止配置のテープ（`Core.finList`）。 -/
def finList (C : CTSH) (vf : List Ch) (mf : Nat) (rm : List Ch) : List Sy :=
  Core.finList nm.toCore C vf mf rm

/-- 停止配置（`Core.finCfg`）。(λ, m) なら疑似状態 null でヘッドは本来の $、(Y v, 0) なら halt で
    ヘッドは区切り 0。 -/
def finCfg (C : CTSH) (vf : List Ch) (mf : Nat) (rm : List Ch) : Cfg St Ps Sy :=
  Core.finCfg nm.toCore C vf mf rm

end

/-! ## 3. コピー（copy_start が規則 1 文字を b で印し、右端に書き足して戻る） -/

section Main
variable {St Ps Sy : Type} {nm : Names St Ps Sy} {T : Machine St Ps Sy}
  (hT : ∀ r ∈ rules nm, r ∈ T)
include hT

set_option hygiene false in
/-- 規則 `r` が Table 7.3 にあるので T にある。 -/
local macro "rl" : tactic =>
  `(tactic| (apply hT; simp only [rules]; repeat (first | exact List.Mem.head _ | apply List.Mem.tail)))

/-- コピー以外の 45 本は Table 7.3 に同じ順で含まれる。 -/
theorem core_sub : ∀ r ∈ Core.rules nm.toCore, r ∈ T := fun r h => hT r <| List.Sublist.subset (by
  simp only [Core.rules, rules]
  repeat (first | exact List.nil_sublist _ | apply List.Sublist.cons_cons | apply List.Sublist.cons)) h

theorem copy_one (c : Ch) {LL : List Sy} (hLL : LL ≠ []) {R : List Sy}
    (hR : ∀ x ∈ R, Core.YNSD nm.toCore x) :
    Reach T (zc nm.b (.go nm.cs) LL (lo nm c) R) (zl nm.b (.go nm.cs) LL (lo nm c :: R ++ [lo nm c])) := by
  rw [← zc_trail _ _ _ R, ← zl_trail]
  have hp : ∀ q d, (∀ x, Core.YNSD nm.toCore x → (⟨q, x, x, d, .go q⟩ : Rule St Ps Sy) ∈ T) →
      ∀ x ∈ R.reverse, (⟨q, x, x, d, .go q⟩ : Rule St Ps Sy) ∈ T := fun q d h => ofP h (fa_rev hR)
  cases c with
  | Y =>
    refine (runR (p := nm.cs) (q := nm.cpy1) (h := nm.y) (t := nm.b) (by rl)
      (ofP (by rintro x (rfl | rfl | rfl | rfl) <;> rl) hR) LL nm.b []).trans ?_
    rw [zc_nil]
    refine (Reach.step (stepR (p := nm.cpy1) (h := nm.b) (t := nm.y) (q := .go nm.cpy2) (by rl)
      _ nm.b [])).trans ?_
    refine (Reach.step (stepL (p := nm.cpy2) (h := nm.b) (t := nm.b) (q := .go nm.cpy3) (by rl)
      nm.y _ [])).trans ?_
    refine (sweepL (q := nm.cpy3) (X := nm.y :: R.reverse)
      (fa_cons (by rl) (hp _ _ (by rintro x (rfl | rfl | rfl | rfl) <;> rl))) nm.b LL [nm.b]).trans ?_
    refine (Reach.step (stepL' (p := nm.cpy3) (h := nm.b) (t := nm.y) (q := .go nm.cs) (by rl)
      hLL _)).trans ?_
    exact Reach.of_eq (by simp [lo, Core.lo])
  | N =>
    refine (runR (p := nm.cs) (q := nm.cpn1) (h := nm.n) (t := nm.b) (by rl)
      (ofP (by rintro x (rfl | rfl | rfl | rfl) <;> rl) hR) LL nm.b []).trans ?_
    rw [zc_nil]
    refine (Reach.step (stepR (p := nm.cpn1) (h := nm.b) (t := nm.n) (q := .go nm.cpn2) (by rl)
      _ nm.b [])).trans ?_
    refine (Reach.step (stepL (p := nm.cpn2) (h := nm.b) (t := nm.b) (q := .go nm.cpn3) (by rl)
      nm.n _ [])).trans ?_
    refine (sweepL (q := nm.cpn3) (X := nm.n :: R.reverse)
      (fa_cons (by rl) (hp _ _ (by rintro x (rfl | rfl | rfl | rfl) <;> rl))) nm.b LL [nm.b]).trans ?_
    refine (Reach.step (stepL' (p := nm.cpn3) (h := nm.b) (t := nm.n) (q := .go nm.cs) (by rl)
      hLL _)).trans ?_
    exact Reach.of_eq (by simp [lo, Core.lo])

/-! ## 4. 主定理（機械の型に依らない形） -/

/-- **主定理（型に依らない形）**。Table 7.3 の 69 本を含む決定的な機械 T は、任意の CTSH C と
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

end URTM.CTSH.U17_5
