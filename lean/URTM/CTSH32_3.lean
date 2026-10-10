/-
  URTM(32,3)（Morita 2017, §7.3.6, Table 7.6）が任意の CTSH を模倣することの一般証明。

  機械の**型に依存しない**形（CTSH17_5.lean と同じ設計）: 名前（`Names`）と Table 7.6 の 84 本の五つ組
  （`rules`、原典の 82 本に停止の 2 本を加えたもの）がすべて機械 T に含まれること（`hT`）、逆向きでは
  T の決定性だけを仮定する。`CTSH32_3Main.lean` で生成モジュール `URTM.Gen.K32_3` に具体化し、
  `rules` = T（集合として）を `decide` で確かめる。

  記号は b y n の 3 個。原典 p. 194: 規則の記号 y, n, ∗ を 2 マスの ϕ₂(Y) = yy, ϕ₂(N) = ny, nn で書き、
  相マーカーは nn の右を b に変えた nb。初期 ID は

      b ϕ₂(w^R_{k−1}) nn ⋯ nn ϕ₂(w^R_1) nn nb b q_begin ϕ₁(v0) b

  規則領域と消去済みの記号の区切りは b、処理中の先頭の記号の印も b（begin が y / n を b に変える）。

  不変量 `rep C m rm v`: 状態 begin、テープ `b · RA(m) · b · ϕ₁(rm) · ϕ₁(v) · b b …`、ヘッドは ϕ₁(v) の先頭。
  RA(m) = H(m) · ϕ₂(w^R_m) · n b · Lo(m)（2 マス単位。Lo(m) の最後の nn が区切り 0）。

  先頭が Y（原典 t = 9–88）: begin y→b、case_y_1 が区切りの b まで、case_y_2 が区切り 0 の右のマス n を見て
  case_y_3 → case_y_4 が印の b まで右へ、case_y_5 が区切りまで、case_y_6 が相マーカーの b まで左へ行って n に戻し、
  case_y_7 → copy_start_1。copy_start_1 が規則の記号の右のマス y を b で印し、copy_start_2 が左のマスで y / n を見分け、
  copy_c_1..4 が右端に c を書き、copy_next_1..4 が戻って印を y に戻し、case_y_7 → copy_start_1 で次の記号へ。
  規則の終わり（nn）で copy_start_1 が右のマスを b に（新しい相マーカー nb）、copy_end_1・copy_end_2 が印の b を y に。
  先頭が N（t = 0–9）: begin n→b、case_n_1 が区切りまで、case_n_2 が相マーカー nb を nn に戻し、
  case_n_3・case_n_4 が 2 マスずつ左へ進んで次の nn を nb にし、case_n_5・case_n_6 が印の b を n に。

  検証の記録は docs/10_ctsh_all_lean_2026-09-26.md。mathlib 非依存。未証明の穴・新規公理・native_decide を使わない。
-/
import URTM.CTSHSim

namespace URTM.CTSH.U32_3

open URTM URTM.KState URTM.CTSH URTM.CTSH.Sim

/-! ## 0. 機械の名前と Table 7.6 -/

/-- U32_3 の記号・状態・疑似状態の名前。 -/
structure Names (St Ps Sy : Type) where
  b : Sy
  y : Sy
  n : Sy
  begin : St
  cy1 : St
  cy2 : St
  cy3 : St
  cy4 : St
  cy5 : St
  cy6 : St
  cy7 : St
  cs1 : St
  cs2 : St
  cpy1 : St
  cpy2 : St
  cpy3 : St
  cpy4 : St
  cnx1 : St
  cnx2 : St
  cnx3 : St
  cnx4 : St
  cpn1 : St
  cpn2 : St
  cpn3 : St
  cpn4 : St
  ce1 : St
  ce2 : St
  cyc : St
  cn1 : St
  cn2 : St
  cn3 : St
  cn4 : St
  cn5 : St
  cn6 : St
  cn7 : St
  halt : Ps
  null : Ps

section
variable {St Ps Sy : Type} (nm : Names St Ps Sy)

/-- Table 7.6（urtm32-3.txt の五つ組を、記述ファイルの順に、名前で書いたもの）。
    `CTSH32_3Main.lean` で生成モジュールの表と集合として一致することを `decide` で確かめる。 -/
def rules : List (Rule St Ps Sy) :=
  let b := nm.b; let y := nm.y; let n := nm.n
  [ ⟨nm.begin, y, b, .L, .go nm.cy1⟩,
    ⟨nm.begin, n, b, .L, .go nm.cn1⟩,
    ⟨nm.begin, b, b, .Z, .halt nm.null⟩,
    ⟨nm.cy1, y, y, .L, .go nm.cy1⟩,
    ⟨nm.cy1, n, n, .L, .go nm.cy1⟩,
    ⟨nm.cy1, b, b, .L, .go nm.cy2⟩,
    ⟨nm.cy2, n, n, .R, .go nm.cy3⟩,
    ⟨nm.cy2, b, b, .Z, .halt nm.halt⟩,
    ⟨nm.cy3, b, b, .R, .go nm.cy4⟩,
    ⟨nm.cy4, y, y, .R, .go nm.cy4⟩,
    ⟨nm.cy4, n, n, .R, .go nm.cy4⟩,
    ⟨nm.cy4, b, b, .L, .go nm.cy5⟩,
    ⟨nm.cy5, y, y, .L, .go nm.cy5⟩,
    ⟨nm.cy5, n, n, .L, .go nm.cy5⟩,
    ⟨nm.cy5, b, b, .L, .go nm.cy6⟩,
    ⟨nm.cy6, y, y, .L, .go nm.cy6⟩,
    ⟨nm.cy6, n, n, .L, .go nm.cy6⟩,
    ⟨nm.cy6, b, n, .L, .go nm.cy7⟩,
    ⟨nm.cy7, y, y, .L, .go nm.cs1⟩,
    ⟨nm.cy7, n, n, .L, .go nm.cs1⟩,
    ⟨nm.cs1, y, b, .L, .go nm.cs2⟩,
    ⟨nm.cs1, n, b, .R, .go nm.ce1⟩,
    ⟨nm.cs1, b, b, .R, .go nm.cyc⟩,
    ⟨nm.cs2, y, y, .R, .go nm.cpy1⟩,
    ⟨nm.cs2, n, n, .R, .go nm.cpn1⟩,
    ⟨nm.cpy1, b, b, .R, .go nm.cpy2⟩,
    ⟨nm.cpy2, y, y, .R, .go nm.cpy2⟩,
    ⟨nm.cpy2, n, n, .R, .go nm.cpy2⟩,
    ⟨nm.cpy2, b, b, .R, .go nm.cpy3⟩,
    ⟨nm.cpy3, y, y, .R, .go nm.cpy3⟩,
    ⟨nm.cpy3, n, n, .R, .go nm.cpy3⟩,
    ⟨nm.cpy3, b, b, .R, .go nm.cpy4⟩,
    ⟨nm.cpy4, y, y, .R, .go nm.cpy4⟩,
    ⟨nm.cpy4, n, n, .R, .go nm.cpy4⟩,
    ⟨nm.cpy4, b, y, .R, .go nm.cnx1⟩,
    ⟨nm.cnx1, b, b, .L, .go nm.cnx2⟩,
    ⟨nm.cnx2, y, y, .L, .go nm.cnx2⟩,
    ⟨nm.cnx2, n, n, .L, .go nm.cnx2⟩,
    ⟨nm.cnx2, b, b, .L, .go nm.cnx3⟩,
    ⟨nm.cnx3, y, y, .L, .go nm.cnx3⟩,
    ⟨nm.cnx3, n, n, .L, .go nm.cnx3⟩,
    ⟨nm.cnx3, b, b, .L, .go nm.cnx4⟩,
    ⟨nm.cnx4, y, y, .L, .go nm.cnx4⟩,
    ⟨nm.cnx4, n, n, .L, .go nm.cnx4⟩,
    ⟨nm.cnx4, b, y, .L, .go nm.cy7⟩,
    ⟨nm.cpn1, b, b, .R, .go nm.cpn2⟩,
    ⟨nm.cpn2, y, y, .R, .go nm.cpn2⟩,
    ⟨nm.cpn2, n, n, .R, .go nm.cpn2⟩,
    ⟨nm.cpn2, b, b, .R, .go nm.cpn3⟩,
    ⟨nm.cpn3, y, y, .R, .go nm.cpn3⟩,
    ⟨nm.cpn3, n, n, .R, .go nm.cpn3⟩,
    ⟨nm.cpn3, b, b, .R, .go nm.cpn4⟩,
    ⟨nm.cpn4, y, y, .R, .go nm.cpn4⟩,
    ⟨nm.cpn4, n, n, .R, .go nm.cpn4⟩,
    ⟨nm.cpn4, b, n, .R, .go nm.cnx1⟩,
    ⟨nm.ce1, y, y, .R, .go nm.ce1⟩,
    ⟨nm.ce1, n, n, .R, .go nm.ce1⟩,
    ⟨nm.ce1, b, b, .R, .go nm.ce2⟩,
    ⟨nm.ce2, y, y, .R, .go nm.ce2⟩,
    ⟨nm.ce2, n, n, .R, .go nm.ce2⟩,
    ⟨nm.ce2, b, y, .R, .go nm.begin⟩,
    ⟨nm.cyc, y, y, .R, .go nm.cyc⟩,
    ⟨nm.cyc, n, n, .R, .go nm.cyc⟩,
    ⟨nm.cyc, b, b, .L, .go nm.cs1⟩,
    ⟨nm.cn1, y, y, .L, .go nm.cn1⟩,
    ⟨nm.cn1, n, n, .L, .go nm.cn1⟩,
    ⟨nm.cn1, b, b, .L, .go nm.cn2⟩,
    ⟨nm.cn2, y, y, .L, .go nm.cn2⟩,
    ⟨nm.cn2, n, n, .L, .go nm.cn2⟩,
    ⟨nm.cn2, b, n, .L, .go nm.cn4⟩,
    ⟨nm.cn3, y, y, .L, .go nm.cn4⟩,
    ⟨nm.cn3, n, b, .R, .go nm.cn5⟩,
    ⟨nm.cn3, b, b, .R, .go nm.cn7⟩,
    ⟨nm.cn4, y, y, .L, .go nm.cn3⟩,
    ⟨nm.cn4, n, n, .L, .go nm.cn3⟩,
    ⟨nm.cn5, y, y, .R, .go nm.cn5⟩,
    ⟨nm.cn5, n, n, .R, .go nm.cn5⟩,
    ⟨nm.cn5, b, b, .R, .go nm.cn6⟩,
    ⟨nm.cn6, y, y, .R, .go nm.cn6⟩,
    ⟨nm.cn6, n, n, .R, .go nm.cn6⟩,
    ⟨nm.cn6, b, n, .R, .go nm.begin⟩,
    ⟨nm.cn7, y, y, .R, .go nm.cn7⟩,
    ⟨nm.cn7, n, n, .R, .go nm.cn7⟩,
    ⟨nm.cn7, b, b, .L, .go nm.cn3⟩ ]

/-! ## 1. CTSH の符号化 -/

/-- ϕ₁: Y ↦ y, N ↦ n（現在の文字列と消去済みの記号）。 -/
def lo : Ch → Sy
  | .Y => nm.y
  | .N => nm.n

/-- ϕ₂: Y ↦ yy, N ↦ ny（規則の記号、2 マス）。 -/
def p2 : Ch → List Sy
  | .Y => [nm.y, nm.y]
  | .N => [nm.n, nm.y]

/-- 2 マスの左のマス（Y ↦ y, N ↦ n）。右のマスは常に y。 -/
def xc : Ch → Sy
  | .Y => nm.y
  | .N => nm.n

/-- ϕ₂ を語に（2 マスずつ並べる）。 -/
def E (w : List Ch) : List Sy := (w.map (p2 nm)).flatten

/-- 1 つの規則のブロック ϕ₂(w^R) nn。 -/
def blk (w : List Ch) : List Sy := E nm w.reverse ++ [nm.n, nm.n]

/-- H(m) = ϕ₂(w^R_{k−1}) nn ⋯ ϕ₂(w^R_{m+1}) nn。 -/
def Hi (C : CTSH) (m : Nat) : List Sy := ((C.drop m).reverse.map (blk nm)).flatten

/-- ϕ₂(w^R_{m−1}) nn ⋯ ϕ₂(w^R_1) nn。 -/
def LoCore (C : CTSH) (m : Nat) : List Sy := ((C.take (m - 1)).reverse.map (blk nm)).flatten

/-- Lo(m) = ϕ₂(w^R_{m−1}) nn ⋯ ϕ₂(w^R_1) nn nn（最後の nn が区切り 0）。相 0 では空。 -/
def Lo (C : CTSH) (m : Nat) : List Sy := if m = 0 then [] else LoCore nm C m ++ [nm.n, nm.n]

/-- 規則領域 RA(m) = H(m) · ϕ₂(w^R_m) · n b · Lo(m)（nb が相マーカー）。 -/
def RA (C : CTSH) (m : Nat) : List Sy := Hi nm C m ++ E nm (prod C m).reverse ++ nm.n :: nm.b :: Lo nm C m

/-- テープの中身（左端が位置 0）: b · RA(m) · b · ϕ₁(rm) · ϕ₁(v)。以降は b。 -/
def tapeList (C : CTSH) (m : Nat) (rm v : List Ch) : List Sy :=
  nm.b :: RA nm C m ++ nm.b :: rm.map (lo nm) ++ v.map (lo nm)

/-- CTSH の ID (v, m) と消去済みの記号列 rm を表す配置: 状態 begin、ヘッドは v の先頭。 -/
def rep (C : CTSH) (m : Nat) (rm v : List Ch) : Cfg St Ps Sy :=
  { st := .go nm.begin, pos := (RA nm C m).length + 2 + rm.length, tape := tp nm.b (tapeList nm C m rm v) }

/-- **Morita の符号化**（原典 p. 194）: `b ϕ₂(w^R_{k−1}) nn ⋯ nn ϕ₂(w^R_1) nn nb b q_begin ϕ₁(w) b`。 -/
def encC (C : CTSH) (w : List Ch) : Cfg St Ps Sy := rep nm C 0 [] w

/-- 停止配置のテープ（リスト）。
    * 最終 ID (λ, m): begin が末尾の b を読んで null。テープは `rep` のまま。
    * 最終 ID (Y v, 0): begin が先頭の y を b に変え、case_y_1 が区切りの b まで行き、case_y_2 が区切り 0 の
      右のマス b（相 0 のマーカー nb）で halt。テープは `b · RA(0) · b · ϕ₁(rm) · b · ϕ₁(v)`
      （原典 p. 194, t = 664「bny should be read as YNY」）。 -/
def finList (C : CTSH) (vf : List Ch) (mf : Nat) (rm : List Ch) : List Sy :=
  match vf with
  | [] => tapeList nm C mf rm []
  | _ :: v => nm.b :: RA nm C 0 ++ nm.b :: rm.map (lo nm) ++ nm.b :: v.map (lo nm)

/-- 停止配置。(λ, m) なら疑似状態 null でヘッドは末尾の b、(Y v, 0) なら halt でヘッドは相マーカーの b。 -/
def finCfg (C : CTSH) (vf : List Ch) (mf : Nat) (rm : List Ch) : Cfg St Ps Sy :=
  match vf with
  | [] => { st := .halt nm.null, pos := (RA nm C mf).length + 2 + rm.length,
            tape := tp nm.b (finList nm C [] mf rm) }
  | c :: v => { st := .halt nm.halt, pos := (RA nm C 0).length,
                tape := tp nm.b (finList nm C (c :: v) 0 rm) }

/-- copy_c_1..4 の状態。 -/
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

end

/-! ## 2. 記号クラスと規則領域の漸化式 -/

section Rec
variable {St Ps Sy : Type} {nm : Names St Ps Sy}

/-- {y, n}（規則領域・消去済みの記号・現在の文字列のマスはすべてこれ）。 -/
def YN (nm : Names St Ps Sy) (x : Sy) : Prop := x = nm.y ∨ x = nm.n

theorem p2_eq (c : Ch) : p2 nm c = [xc nm c, nm.y] := by cases c <;> rfl

theorem E_nil : E nm [] = [] := rfl
theorem E_cons (c : Ch) (w : List Ch) : E nm (c :: w) = xc nm c :: nm.y :: E nm w := by
  simp [E, p2_eq]
theorem E_append (a b : List Ch) : E nm (a ++ b) = E nm a ++ E nm b := by simp [E]

/-- ϕ₂(w^R) を右から読むと、各記号が y, (y / n) の順に現れる。 -/
theorem E_rev_rev (w : List Ch) :
    (E nm w.reverse).reverse = (w.map (fun c => [nm.y, xc nm c])).flatten := by
  induction w with
  | nil => rfl
  | cons c w ih => simp [E_append, E_cons, E_nil, ih]

theorem lo_YN (c : Ch) : YN nm (lo nm c) := by cases c <;> simp [YN, lo]
theorem xc_YN (c : Ch) : YN nm (xc nm c) := by cases c <;> simp [YN, xc]
theorem y_YN : YN nm nm.y := .inl rfl
theorem n_YN : YN nm nm.n := .inr rfl

theorem E_YN (w : List Ch) : ∀ x ∈ E nm w, YN nm x := by
  induction w with
  | nil => exact fa_nil
  | cons c w ih => rw [E_cons]; exact fa_cons (xc_YN c) (fa_cons y_YN ih)

theorem blk_YN (L : List (List Ch)) : ∀ x ∈ (L.map (blk nm)).flatten, YN nm x := by
  refine fa_flatten ?_
  intro A hA
  obtain ⟨w, _, rfl⟩ := List.mem_map.mp hA
  exact fa_app (E_YN _) (fa_cons n_YN (fa_cons n_YN fa_nil))

theorem LoCore_YN (C : CTSH) (m : Nat) : ∀ x ∈ LoCore nm C m, YN nm x := blk_YN _
theorem Lo_YN (C : CTSH) (m : Nat) : ∀ x ∈ Lo nm C m, YN nm x := by
  unfold Lo; split
  · exact fa_nil
  · exact fa_app (LoCore_YN C m) (fa_cons n_YN (fa_cons n_YN fa_nil))
theorem lo_map_YN (w : List Ch) : ∀ x ∈ w.map (lo nm), YN nm x := fa_map lo_YN w

theorem Hi_step (C : CTSH) (m : Nat) (h : m < C.length) :
    Hi nm C m = Hi nm C (m + 1) ++ E nm (prod C (m + 1)).reverse ++ [nm.n, nm.n] := by
  rw [prod_succ C m h]
  unfold Hi
  rw [List.drop_eq_getElem_cons h]
  simp only [List.reverse_cons, List.map_append, List.flatten_append, List.map_cons, List.map_nil,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc, blk]

theorem Hi_len (C : CTSH) : Hi nm C C.length = [] := by simp [Hi]

theorem Lo_step (C : CTSH) (m : Nat) (h : m ≤ C.length) :
    Lo nm C (m + 1) = E nm (prod C m).reverse ++ nm.n :: nm.n :: Lo nm C m := by
  cases m with
  | zero => simp [Lo, LoCore, prod, E]
  | succ m =>
    rw [prod_succ C m (by omega)]
    simp only [Lo, LoCore, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
    rw [List.take_add_one, List.getElem?_eq_getElem (by omega)]
    simp only [Option.toList_some, List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.map_cons, List.flatten_cons, List.append_assoc, List.cons_append, blk]

theorem Lo_ne (C : CTSH) (m : Nat) (h : m ≠ 0) : Lo nm C m = LoCore nm C m ++ [nm.n, nm.n] := by
  simp [Lo, h]

theorem LoCore_full (C : CTSH) : LoCore nm C (C.length + 1) = Hi nm C 0 := by
  simp [LoCore, Hi]

theorem rep_eq (C : CTSH) (m : Nat) (rm v : List Ch) :
    rep nm C m rm v =
      zr nm.b (.go nm.begin) (nm.b :: RA nm C m ++ nm.b :: rm.map (lo nm)).reverse (v.map (lo nm)) := by
  rw [zr_eq]; simp only [rep, tapeList]; congr 1 <;> simp; omega

/-- 相マーカーより左（近い順）: 右から読んだ ϕ₂(w_m) と (b · H(m))^R。 -/
def Zq (nm : Names St Ps Sy) (C : CTSH) (m : Nat) : List Sy :=
  ((prod C m).map (fun c => [nm.y, xc nm c])).flatten ++ (nm.b :: Hi nm C m).reverse

theorem left_eq (C : CTSH) (m : Nat) (rm : List Ch) :
    (nm.b :: RA nm C m ++ nm.b :: rm.map (lo nm)).reverse =
      (rm.map (lo nm)).reverse ++ nm.b :: ((Lo nm C m).reverse ++ nm.b :: nm.n :: Zq nm C m) := by
  simp [RA, Zq, E_rev_rev]

theorem Zq_ne (C : CTSH) (m : Nat) : Zq nm C m ≠ [] := by simp [Zq]

end Rec

/-! ## 3. 規則表から読み取る 1 ステップと掃引 -/

section Main
variable {St Ps Sy : Type} {nm : Names St Ps Sy} {T : Machine St Ps Sy}
  (hT : ∀ r ∈ rules nm, r ∈ T)
include hT

set_option hygiene false in
/-- 規則 `r` が Table 7.6 にあるので T にある。 -/
macro "rl" : tactic =>
  `(tactic| (apply hT; simp only [rules]; repeat (first | exact List.Mem.head _ | apply List.Mem.tail)))

set_option hygiene false in
/-- 状態が {y, n} を書き換えずに通過する。 -/
macro "pass" : tactic => `(tactic| (rintro x (rfl | rfl) <;> rl))

theorem pL {q : St} (hq : q = nm.cy1 ∨ q = nm.cy5 ∨ q = nm.cy6 ∨ q = nm.cnx2 ∨ q = nm.cnx3 ∨
    q = nm.cnx4 ∨ q = nm.cn1 ∨ q = nm.cn2) :
    ∀ x, YN nm x → (⟨q, x, x, .L, .go q⟩ : Rule St Ps Sy) ∈ T := by
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> pass

theorem pR {q : St} (hq : q = nm.cy4 ∨ q = nm.cpy2 ∨ q = nm.cpy3 ∨ q = nm.cpy4 ∨ q = nm.cpn2 ∨
    q = nm.cpn3 ∨ q = nm.cpn4 ∨ q = nm.ce1 ∨ q = nm.ce2 ∨ q = nm.cyc ∨ q = nm.cn5 ∨ q = nm.cn6 ∨
    q = nm.cn7) :
    ∀ x, YN nm x → (⟨q, x, x, .R, .go q⟩ : Rule St Ps Sy) ∈ T := by
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> pass

theorem p_k2 (c : Ch) : ∀ x, YN nm x → (⟨k2 nm c, x, x, .R, .go (k2 nm c)⟩ : Rule St Ps Sy) ∈ T := by
  cases c <;> pass
theorem p_k3 (c : Ch) : ∀ x, YN nm x → (⟨k3 nm c, x, x, .R, .go (k3 nm c)⟩ : Rule St Ps Sy) ∈ T := by
  cases c <;> pass
theorem p_k4 (c : Ch) : ∀ x, YN nm x → (⟨k4 nm c, x, x, .R, .go (k4 nm c)⟩ : Rule St Ps Sy) ∈ T := by
  cases c <;> pass
theorem r_cs2 (c : Ch) : (⟨nm.cs2, xc nm c, xc nm c, .R, .go (k1 nm c)⟩ : Rule St Ps Sy) ∈ T := by
  cases c <;> rl
theorem r_k1 (c : Ch) : (⟨k1 nm c, nm.b, nm.b, .R, .go (k2 nm c)⟩ : Rule St Ps Sy) ∈ T := by
  cases c <;> rl
theorem r_k2 (c : Ch) : (⟨k2 nm c, nm.b, nm.b, .R, .go (k3 nm c)⟩ : Rule St Ps Sy) ∈ T := by
  cases c <;> rl
theorem r_k3 (c : Ch) : (⟨k3 nm c, nm.b, nm.b, .R, .go (k4 nm c)⟩ : Rule St Ps Sy) ∈ T := by
  cases c <;> rl
theorem r_k4 (c : Ch) : (⟨k4 nm c, nm.b, lo nm c, .R, .go nm.cnx1⟩ : Rule St Ps Sy) ∈ T := by
  cases c <;> rl
theorem r_cy7 (c : Ch) : (⟨nm.cy7, xc nm c, xc nm c, .L, .go nm.cs1⟩ : Rule St Ps Sy) ∈ T := by
  cases c <;> rl
theorem r_cn4 (c : Ch) : (⟨nm.cn4, xc nm c, xc nm c, .L, .go nm.cn3⟩ : Rule St Ps Sy) ∈ T := by
  cases c <;> rl

/-! ## 4. コピー（先頭が Y のときだけ使う）と、N のときの読み飛ばし -/

/-- 原典 t = 22–46: copy_start_1 が規則の記号 c の右のマス y を b で印し、copy_start_2 が左のマスで c を見分け、
    copy_c_1 が印を越え、copy_c_2 が区切りの b まで、copy_c_3 が現在の文字列の印 b まで、copy_c_4 が右端の b まで
    行って c を書き、copy_next_1 が折り返し、copy_next_2..4 が 3 つの b を越えて印の b を y に戻し、
    case_y_7 が左のマスを越えて copy_start_1。R₁ は印と区切りの間、R₂ は区切りと先頭の印の間、R₃ はその右。 -/
theorem copy_one (c : Ch) {LL : List Sy} (hLL : LL ≠ []) {R₁ R₂ R₃ : List Sy}
    (h₁ : ∀ x ∈ R₁, YN nm x) (h₂ : ∀ x ∈ R₂, YN nm x) (h₃ : ∀ x ∈ R₃, YN nm x) :
    Reach T (zl nm.b (.go nm.cs1) (nm.y :: xc nm c :: LL) (R₁ ++ nm.b :: R₂ ++ nm.b :: R₃))
      (zl nm.b (.go nm.cs1) LL (xc nm c :: nm.y :: R₁ ++ nm.b :: R₂ ++ nm.b :: (R₃ ++ [lo nm c]))) := by
  rw [← zl_trail _ (nm.y :: xc nm c :: LL) (R₁ ++ nm.b :: R₂ ++ nm.b :: R₃), ← zl_trail _ LL]
  rw [show R₁ ++ nm.b :: R₂ ++ nm.b :: R₃ ++ [nm.b] = R₁ ++ nm.b :: (R₂ ++ nm.b :: (R₃ ++ [nm.b])) by simp]
  show Reach T (zc nm.b (.go nm.cs1) (xc nm c :: LL) nm.y (R₁ ++ nm.b :: (R₂ ++ nm.b :: (R₃ ++ [nm.b])))) _
  refine (Reach.step (stepL (p := nm.cs1) (h := nm.y) (t := nm.b) (q := .go nm.cs2) (by rl)
    (xc nm c) LL _)).trans ?_
  refine (Reach.step (stepR (r_cs2 hT c) LL nm.b _)).trans ?_
  refine (runR (r_k1 hT c) (ofP (p_k2 hT c) h₁) _ nm.b _).trans ?_
  refine (runR (r_k2 hT c) (ofP (p_k3 hT c) h₂) _ nm.b _).trans ?_
  refine (runR (r_k3 hT c) (ofP (p_k4 hT c) h₃) _ nm.b []).trans ?_
  rw [zc_nil]
  refine (Reach.step (stepR (r_k4 hT c) _ nm.b [])).trans ?_
  refine (Reach.step (stepL (p := nm.cnx1) (h := nm.b) (t := nm.b) (q := .go nm.cnx2) (by rl)
    (lo nm c) _ [])).trans ?_
  refine (sweepL (X := lo nm c :: R₃.reverse)
    (ofP (pL hT (by simp)) (fa_cons (lo_YN c) (fa_rev h₃))) nm.b _ [nm.b]).trans ?_
  refine (runL (p := nm.cnx2) (q := nm.cnx3) (h := nm.b) (t := nm.b) (by rl) (X := R₂.reverse)
    (ofP (pL hT (by simp)) (fa_rev h₂)) nm.b _ _).trans ?_
  refine (runL (p := nm.cnx3) (q := nm.cnx4) (h := nm.b) (t := nm.b) (by rl) (X := R₁.reverse)
    (ofP (pL hT (by simp)) (fa_rev h₁)) nm.b _ _).trans ?_
  refine (Reach.step (stepL (p := nm.cnx4) (h := nm.b) (t := nm.y) (q := .go nm.cy7) (by rl)
    (xc nm c) LL _)).trans ?_
  refine (Reach.step (stepL' (r_cy7 hT c) hLL _)).trans ?_
  exact Reach.of_eq (by simp)

theorem copy_loop (Z : List Sy) (hZ : Z ≠ []) :
    ∀ (Q P : List Ch) (R₁ R₂ R₃ : List Sy), (∀ x ∈ R₁, YN nm x) → (∀ x ∈ R₂, YN nm x) →
      (∀ x ∈ R₃, YN nm x) →
    Reach T (zl nm.b (.go nm.cs1) ((Q.map (fun c => [nm.y, xc nm c])).flatten ++ Z)
        (E nm P.reverse ++ R₁ ++ nm.b :: R₂ ++ nm.b :: R₃))
      (zl nm.b (.go nm.cs1) Z
        (E nm (P ++ Q).reverse ++ R₁ ++ nm.b :: R₂ ++ nm.b :: (R₃ ++ Q.map (lo nm)))) := by
  intro Q
  induction Q with
  | nil => intro P R₁ R₂ R₃ _ _ _; exact Reach.of_eq (by simp)
  | cons c Q ih =>
    intro P R₁ R₂ R₃ h₁ h₂ h₃
    have h1 := copy_one hT c (LL := (Q.map (fun c => [nm.y, xc nm c])).flatten ++ Z) (by simp [hZ])
      (R₁ := E nm P.reverse ++ R₁) (fa_app (E_YN _) h₁) h₂ h₃
    have h1' : Reach T
        (zl nm.b (.go nm.cs1) (((c :: Q).map (fun c => [nm.y, xc nm c])).flatten ++ Z)
          (E nm P.reverse ++ R₁ ++ nm.b :: R₂ ++ nm.b :: R₃))
        (zl nm.b (.go nm.cs1) ((Q.map (fun c => [nm.y, xc nm c])).flatten ++ Z)
          (E nm (P ++ [c]).reverse ++ R₁ ++ nm.b :: R₂ ++ nm.b :: (R₃ ++ [lo nm c]))) := by
      refine Eq.mpr ?_ h1; simp [E_cons]
    have h2 := ih (P ++ [c]) R₁ R₂ (R₃ ++ [lo nm c]) h₁ h₂ (fa_app h₃ (fa_cons (lo_YN c) fa_nil))
    refine h1'.trans (Eq.mpr ?_ h2)
    simp

/-- 先頭が N（原典 t = 1–9）: case_n_3・case_n_4 が規則の記号を 2 マスずつ左へ読み飛ばす。 -/
theorem skipN (Z : List Sy) (hZ : Z ≠ []) :
    ∀ (Q : List Ch) (S : List Sy),
    Reach T (zl nm.b (.go nm.cn3) ((Q.map (fun c => [nm.y, xc nm c])).flatten ++ Z) S)
      (zl nm.b (.go nm.cn3) Z (E nm Q.reverse ++ S)) := by
  intro Q
  induction Q with
  | nil => intro S; exact Reach.of_eq (by simp [E])
  | cons c Q ih =>
    intro S
    simp only [List.map_cons, List.flatten_cons, List.cons_append, List.nil_append]
    rw [show zl nm.b (.go nm.cn3) (nm.y :: xc nm c :: ((Q.map (fun c => [nm.y, xc nm c])).flatten ++ Z)) S =
      zc nm.b (.go nm.cn3) (xc nm c :: ((Q.map (fun c => [nm.y, xc nm c])).flatten ++ Z)) nm.y S from rfl]
    refine (Reach.step (stepL (p := nm.cn3) (h := nm.y) (t := nm.y) (q := .go nm.cn4) (by rl)
      (xc nm c) _ S)).trans ?_
    refine (Reach.step (stepL' (r_cn4 hT c) (L := (Q.map (fun c => [nm.y, xc nm c])).flatten ++ Z)
      (by simp [hZ]) _)).trans ?_
    refine (ih _).trans (Reach.of_eq ?_)
    simp [E_append, E_cons, E_nil]

/-! ## 5. 1 マクロステップ -/

/-- 先頭が Y、相 m ≥ 1（原典 t = 9–22）。 -/
theorem frontY (C : CTSH) (m : Nat) (hm : m ≠ 0) (rm v : List Ch) :
    Reach1 T (rep nm C m rm (.Y :: v))
      (zl nm.b (.go nm.cs1) (Zq nm C m)
        (nm.n :: nm.n :: Lo nm C m ++ nm.b :: rm.map (lo nm) ++ nm.b :: v.map (lo nm))) := by
  rw [rep_eq, left_eq, Lo_ne C m hm]
  simp only [List.map_cons, zr, lo]
  rw [show (LoCore nm C m ++ [nm.n, nm.n]).reverse ++ nm.b :: nm.n :: Zq nm C m =
      nm.n :: (nm.n :: ((LoCore nm C m).reverse ++ nm.b :: nm.n :: Zq nm C m)) by simp]
  refine (runL1 (p := nm.begin) (q := nm.cy1) (h := nm.y) (t := nm.b) (by rl)
    (ofP (pL hT (by simp)) (fa_rev (lo_map_YN _))) nm.b _ _).trans ?_
  refine (Reach.step (stepL (p := nm.cy1) (h := nm.b) (t := nm.b) (q := .go nm.cy2) (by rl)
    nm.n _ _)).trans ?_
  refine (Reach.step (stepR (p := nm.cy2) (h := nm.n) (t := nm.n) (q := .go nm.cy3) (by rl)
    _ nm.b _)).trans ?_
  simp only [List.reverse_reverse]
  refine (runR (p := nm.cy3) (q := nm.cy4) (h := nm.b) (t := nm.b) (by rl)
    (ofP (pR hT (by simp)) (lo_map_YN _)) _ nm.b _).trans ?_
  refine (runL (p := nm.cy4) (q := nm.cy5) (h := nm.b) (t := nm.b) (by rl)
    (ofP (pL hT (by simp)) (fa_rev (lo_map_YN _))) nm.b _ _).trans ?_
  rw [show nm.n :: nm.n :: ((LoCore nm C m).reverse ++ nm.b :: nm.n :: Zq nm C m) =
      (nm.n :: nm.n :: (LoCore nm C m).reverse) ++ nm.b :: nm.n :: Zq nm C m by simp]
  refine (runL (p := nm.cy5) (q := nm.cy6) (h := nm.b) (t := nm.b) (by rl)
    (ofP (pL hT (by simp)) (fa_cons n_YN (fa_cons n_YN (fa_rev (LoCore_YN C m))))) nm.b _ _).trans ?_
  refine (Reach.step (stepL (p := nm.cy6) (h := nm.b) (t := nm.n) (q := .go nm.cy7) (by rl)
    nm.n _ _)).trans ?_
  refine (Reach.step (stepL' (p := nm.cy7) (h := nm.n) (t := nm.n) (q := .go nm.cs1) (by rl)
    (Zq_ne C m) _)).trans ?_
  exact Reach.of_eq (by simp)

/-- 先頭が Y の相の終わり（原典 t = 76–88, 248–267）: copy_start_1 が次の区切り nn の右を b に（新しい相マーカー）、
    copy_end_1 が区切りの b まで、copy_end_2 が印の b を y に戻して begin。m = k−1 なら左端の b で cycle_end に入り、
    区切りの b で折り返して区切り 0 を相マーカーに。 -/
theorem finishY (C : CTSH) (m : Nat) (hk : m ≤ C.length) (rm v : List Ch) :
    Reach T (zl nm.b (.go nm.cs1) (nm.b :: Hi nm C m).reverse
        (E nm (prod C m).reverse ++ nm.n :: nm.n :: Lo nm C m ++ nm.b ::
          (rm.map (lo nm) ++ nm.b :: v.map (lo nm))))
      (rep nm C ((m + 1) % C.k) (rm ++ [.Y]) v) := by
  have hLs : ∀ x ∈ E nm (prod C m).reverse ++ nm.n :: nm.n :: Lo nm C m, YN nm x :=
    fa_app (E_YN _) (fa_cons n_YN (fa_cons n_YN (Lo_YN C m)))
  rcases Nat.lt_or_ge m C.length with h | h
  · rw [Nat.mod_eq_of_lt (by simp [CTSH.k]; omega), rep_eq, Hi_step C m h]
    rw [show (nm.b :: (Hi nm C (m + 1) ++ E nm (prod C (m + 1)).reverse ++ [nm.n, nm.n])).reverse =
        nm.n :: nm.n :: (nm.b :: Hi nm C (m + 1) ++ E nm (prod C (m + 1)).reverse).reverse by simp]
    simp only [zl]
    refine (runR (p := nm.cs1) (q := nm.ce1) (h := nm.n) (t := nm.b) (by rl)
      (ofP (pR hT (by simp)) hLs) _ _ _).trans ?_
    refine (runR (p := nm.ce1) (q := nm.ce2) (h := nm.b) (t := nm.b) (by rl)
      (ofP (pR hT (by simp)) (lo_map_YN _)) _ _ _).trans ?_
    refine (Reach.step (stepR' (p := nm.ce2) (h := nm.b) (t := nm.y) (q := .go nm.begin) (by rl)
      _ _)).trans ?_
    apply Reach.of_eq
    congr 1
    simp [RA, Lo_step C m hk, lo]
  · have hmk : m = C.length := by omega
    subst hmk
    rw [show (C.length + 1) % C.k = 0 by simp [CTSH.k], rep_eq, Hi_len]
    simp only [zl, List.reverse_cons, List.reverse_nil, List.nil_append]
    rw [show E nm (prod C C.length).reverse ++ nm.n :: nm.n :: Lo nm C C.length ++ nm.b ::
          (rm.map (lo nm) ++ nm.b :: v.map (lo nm)) =
        Lo nm C (C.length + 1) ++ nm.b :: (rm.map (lo nm) ++ nm.b :: v.map (lo nm)) by
      simp [Lo_step C C.length (Nat.le_refl _)]]
    refine (runR (p := nm.cs1) (q := nm.cyc) (h := nm.b) (t := nm.b) (by rl)
      (ofP (pR hT (by simp)) (Lo_YN C _)) [] _ _).trans ?_
    rw [Lo_ne C (C.length + 1) (by omega)]
    rw [show (LoCore nm C (C.length + 1) ++ [nm.n, nm.n]).reverse ++ [nm.b] =
        nm.n :: (nm.n :: (LoCore nm C (C.length + 1)).reverse ++ [nm.b]) by simp]
    refine (Reach.step (stepL (p := nm.cyc) (h := nm.b) (t := nm.b) (q := .go nm.cs1) (by rl)
      _ _ _)).trans ?_
    refine (runR (p := nm.cs1) (q := nm.ce1) (h := nm.n) (t := nm.b) (by rl) (X := [])
      (fun _ h => nomatch h) _ _ _).trans ?_
    refine (runR (p := nm.ce1) (q := nm.ce2) (h := nm.b) (t := nm.b) (by rl)
      (ofP (pR hT (by simp)) (lo_map_YN _)) _ _ _).trans ?_
    refine (Reach.step (stepR' (p := nm.ce2) (h := nm.b) (t := nm.y) (q := .go nm.begin) (by rl)
      _ _)).trans ?_
    apply Reach.of_eq
    congr 1
    simp [RA, LoCore_full, lo, prod, Lo, E]

theorem macroY (C : CTSH) {m : Nat} (h0 : m ≠ 0) (hk : m < C.k) (rm v : List Ch) :
    Reach1 T (rep nm C m rm (.Y :: v)) (rep nm C ((m + 1) % C.k) (rm ++ [.Y]) (v ++ prod C m)) := by
  have hmk : m ≤ C.length := by simp [CTSH.k] at hk; omega
  refine (frontY hT C m h0 rm v).trans ?_
  have hL := copy_loop hT _ (by simp : (nm.b :: Hi nm C m).reverse ≠ []) (prod C m) []
    (nm.n :: nm.n :: Lo nm C m) (rm.map (lo nm)) (v.map (lo nm))
    (fa_cons n_YN (fa_cons n_YN (Lo_YN C m))) (lo_map_YN _) (lo_map_YN _)
  have hL' : Reach T
      (zl nm.b (.go nm.cs1) (Zq nm C m)
        (nm.n :: nm.n :: Lo nm C m ++ nm.b :: rm.map (lo nm) ++ nm.b :: v.map (lo nm)))
      (zl nm.b (.go nm.cs1) (nm.b :: Hi nm C m).reverse
        (E nm (prod C m).reverse ++ nm.n :: nm.n :: Lo nm C m ++ nm.b ::
          (rm.map (lo nm) ++ nm.b :: (v ++ prod C m).map (lo nm)))) := by
    refine Eq.mpr ?_ hL; simp [Zq, E]
  exact hL'.trans (finishY hT C m hmk rm (v ++ prod C m))

/-- 先頭が N（任意の相。原典 t = 0–1）: begin が n を b に、case_n_1 が区切りの b まで左へ、case_n_2 が
    相マーカー nb を nn に戻し、case_n_4 が左のマスを越えて case_n_3 へ。 -/
theorem frontN (C : CTSH) (m : Nat) (rm v : List Ch) :
    Reach1 T (rep nm C m rm (.N :: v))
      (zl nm.b (.go nm.cn3) (Zq nm C m)
        (nm.n :: nm.n :: Lo nm C m ++ nm.b :: (rm.map (lo nm) ++ nm.b :: v.map (lo nm)))) := by
  rw [rep_eq, left_eq]
  simp only [List.map_cons, zr, lo]
  refine (runL1 (p := nm.begin) (q := nm.cn1) (h := nm.n) (t := nm.b) (by rl)
    (ofP (pL hT (by simp)) (fa_rev (lo_map_YN _))) nm.b _ _).trans ?_
  refine (runL (p := nm.cn1) (q := nm.cn2) (h := nm.b) (t := nm.b) (by rl)
    (ofP (pL hT (by simp)) (fa_rev (Lo_YN C m))) nm.b _ _).trans ?_
  refine (Reach.step (stepL (p := nm.cn2) (h := nm.b) (t := nm.n) (q := .go nm.cn4) (by rl)
    nm.n _ _)).trans ?_
  refine (Reach.step (stepL' (p := nm.cn4) (h := nm.n) (t := nm.n) (q := .go nm.cn3) (by rl)
    (Zq_ne C m) _)).trans ?_
  exact Reach.of_eq (by simp)

/-- 先頭が N の後半（原典 t = 1–9）: 規則 w_m を読み飛ばし、case_n_3 が次の区切り nn の右を b に（新しい相マーカー）、
    case_n_5 が区切りの b まで、case_n_6 が印の b を n に戻して begin。m = k−1 なら左端の b で case_n_7 に入り、
    区切りの b で折り返して区切り 0 を相マーカーに。 -/
theorem finishN (C : CTSH) (m : Nat) (hk : m ≤ C.length) (rm v : List Ch) :
    Reach T (zl nm.b (.go nm.cn3) (Zq nm C m)
        (nm.n :: nm.n :: Lo nm C m ++ nm.b :: (rm.map (lo nm) ++ nm.b :: v.map (lo nm))))
      (rep nm C ((m + 1) % C.k) (rm ++ [.N]) v) := by
  refine (skipN hT _ (by simp) (prod C m) _).trans ?_
  have hLs : ∀ x ∈ E nm (prod C m).reverse ++ nm.n :: nm.n :: Lo nm C m, YN nm x :=
    fa_app (E_YN _) (fa_cons n_YN (fa_cons n_YN (Lo_YN C m)))
  rw [show E nm (prod C m).reverse ++ (nm.n :: nm.n :: Lo nm C m ++ nm.b ::
        (rm.map (lo nm) ++ nm.b :: v.map (lo nm))) =
      (E nm (prod C m).reverse ++ nm.n :: nm.n :: Lo nm C m) ++ nm.b ::
        (rm.map (lo nm) ++ nm.b :: v.map (lo nm)) by simp]
  rcases Nat.lt_or_ge m C.length with h | h
  · rw [Nat.mod_eq_of_lt (by simp [CTSH.k]; omega), rep_eq, Hi_step C m h]
    rw [show (nm.b :: (Hi nm C (m + 1) ++ E nm (prod C (m + 1)).reverse ++ [nm.n, nm.n])).reverse =
        nm.n :: nm.n :: (nm.b :: Hi nm C (m + 1) ++ E nm (prod C (m + 1)).reverse).reverse by simp]
    simp only [zl]
    refine (runR (p := nm.cn3) (q := nm.cn5) (h := nm.n) (t := nm.b) (by rl)
      (ofP (pR hT (by simp)) hLs) _ _ _).trans ?_
    refine (runR (p := nm.cn5) (q := nm.cn6) (h := nm.b) (t := nm.b) (by rl)
      (ofP (pR hT (by simp)) (lo_map_YN _)) _ _ _).trans ?_
    refine (Reach.step (stepR' (p := nm.cn6) (h := nm.b) (t := nm.n) (q := .go nm.begin) (by rl)
      _ _)).trans ?_
    apply Reach.of_eq
    congr 1
    simp [RA, Lo_step C m hk, lo]
  · have hmk : m = C.length := by omega
    subst hmk
    rw [show (C.length + 1) % C.k = 0 by simp [CTSH.k], rep_eq, Hi_len]
    simp only [zl, List.reverse_cons, List.reverse_nil, List.nil_append]
    rw [← Lo_step C C.length (Nat.le_refl _)] at hLs ⊢
    refine (runR (p := nm.cn3) (q := nm.cn7) (h := nm.b) (t := nm.b) (by rl)
      (ofP (pR hT (by simp)) hLs) [] _ _).trans ?_
    rw [Lo_ne C (C.length + 1) (by omega)]
    rw [show (LoCore nm C (C.length + 1) ++ [nm.n, nm.n]).reverse ++ [nm.b] =
        nm.n :: (nm.n :: (LoCore nm C (C.length + 1)).reverse ++ [nm.b]) by simp]
    refine (Reach.step (stepL (p := nm.cn7) (h := nm.b) (t := nm.b) (q := .go nm.cn3) (by rl)
      _ _ _)).trans ?_
    refine (runR (p := nm.cn3) (q := nm.cn5) (h := nm.n) (t := nm.b) (by rl) (X := [])
      (fun _ h => nomatch h) _ _ _).trans ?_
    refine (runR (p := nm.cn5) (q := nm.cn6) (h := nm.b) (t := nm.b) (by rl)
      (ofP (pR hT (by simp)) (lo_map_YN _)) _ _ _).trans ?_
    refine (Reach.step (stepR' (p := nm.cn6) (h := nm.b) (t := nm.n) (q := .go nm.begin) (by rl)
      _ _)).trans ?_
    apply Reach.of_eq
    congr 1
    simp [RA, LoCore_full, lo, prod, Lo, E]

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

/-- (Y v, 0): begin が y を b に、case_y_1 が区切りの b まで、case_y_2 が相 0 のマーカー nb の b で halt（原典 t = 664）。 -/
theorem halt_Y (C : CTSH) (rm v : List Ch) :
    Reach1 T (rep nm C 0 rm (.Y :: v)) (finCfg nm C (.Y :: v) 0 rm) := by
  rw [rep_eq]
  simp only [List.map_cons, zr, lo]
  rw [show (nm.b :: RA nm C 0 ++ nm.b :: rm.map (lo nm)).reverse =
      (rm.map (lo nm)).reverse ++ nm.b :: nm.b :: nm.n :: (nm.b :: Hi nm C 0).reverse by
    simp [RA, prod, Lo, E]]
  refine (runL1 (p := nm.begin) (q := nm.cy1) (h := nm.y) (t := nm.b) (by rl)
    (ofP (pL hT (by simp)) (fa_rev (lo_map_YN _))) nm.b _ _).trans ?_
  refine (Reach.step (stepL (p := nm.cy1) (h := nm.b) (t := nm.b) (q := .go nm.cy2) (by rl)
    nm.b _ _)).trans ?_
  refine (Reach.step (stepZ (p := nm.cy2) (h := nm.b) (t := nm.b) (q := .halt nm.halt) (by rl)
    _ _)).trans ?_
  apply Reach.of_eq
  simp only [zc, finCfg, finList]
  congr 1
  · simp [RA, prod, Lo, E]; omega
  · simp [RA, prod, Lo, E]

omit hT in
theorem finCfg_halted (C : CTSH) (vf : List Ch) (mf : Nat) (rm : List Ch) :
    Halted T (finCfg nm C vf mf rm) := by
  intro c' ⟨r, _, hst, _⟩
  cases vf <;> simp [finCfg] at hst

/-! ## 7. 主定理（機械の型に依らない形） -/

/-- **主定理（型に依らない形）**。Table 7.6 の 84 本を含む決定的な機械 T は、任意の CTSH C と
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

end URTM.CTSH.U32_3
