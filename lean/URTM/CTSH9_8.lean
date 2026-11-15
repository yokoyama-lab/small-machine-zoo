/-
  **URTM(9,8)**（2026-11-05、層 1 の候補）: URTM(10,7)（`URTM.CTSH.U10_7.T10`）に「タグで 2 状態を併合（case_y_1 と
  copy_n_3）と記号の併合を同時に」当てた表（結合探索の出力。54 本、9 状態、8 記号）が、任意の CTSH を模倣すること。

  記号は 8 つ `Sy8`（s0 = b、s1 = y、s2 = n、s3 = Y、s4 = N、s5 = ∗、s6 = $、s7 = T）。b y n ∗ $ は (13,7) のままの意味、
  Y は見つかった表の `y1`、N は `*_t3_t3`（タグ付きの y を吸収した色）、T は `*_t2`（タグ付きの n を吸収した色）。
  状態は (13,7) の `St` の座で書く（9 個）: begin = q0、M₂ = q1（case_y_1 と copy_n_3 の併合）、
  M = q2（case_y_2・copy_y_2・cycle_end の併合、(10,7) と同じ）、case_y_n = q3、copy_start = q4、copy_y_1 = q5、
  copy_y_3 = q7、copy_n_1 = q8、E = q11（copy_end と copy_n_2 の併合、(11,7) と同じ）。q6・q9・q10・q12 は現れない。
  子の表 `T9 = (T10.flatMap chg).eraseDups` は親 (10,7) の 57 本をそれぞれ 1 本か 2 本に写した像（集合として）。
  `mu` は状態の併合（copy_n_3 (q10) → M₂ = case_y_1 の座 q1）、`chgSym` は読む記号・書く記号の書き換え（親の 4 本は、
  通る時のタグが 2 通りあるので子の 2 本に写る。結合探索の出力 9-8n の表と親を並走させて規則の対応を取った。T28）。
  像の 61 本のうち 7 本が同じ五つ組になり、子は 54 本。表は書き写していない（記述ファイルは tools/gen_child_desc.py が
  `mu`・`chgSym` から作り直し、材料の表と md5 で一致する。照合は報告書）。

  子の動きは (13,7)・(10,7) と 1 歩ずつ同じで、違いはセルの色だけ。CTSH の 1 歩の境目（状態 begin）では (10,7) と同じく
  相 m の規則領域の Lo(m) の区切り ∗ が Y になっている（`gSY`）ほかは (13,7) と同じ（`rep9`）。掃引ごとの書き換え:
  * M₂（左へ、case_y_1 の役）: y ↦ N、n ↦ T、$ ↦ Y（`gM2`）。M（右へ）: Y ↦ $、N ↦ y、T ↦ n、y ↦ ∗（`gM`）。
  * case_y_n（左へ）: y ↦ N、n ↦ T、Y ↦ y、$ ↦ n（`gcyn`）。copy_start に入るとき Lo(m) は `gL`（∗ ↦ y、y ↦ N、n ↦ T）の形、
    消去済みの列 ϕ₁(rm) は `loN`（y ↦ N、n ↦ T）の形、印 $ は n、先頭の印 Y/N は Y/∗（`mk`）。
  * copy_y_1（`gc1`）と copy_y_3（`hc1`）、copy_n_1（`gn1`）と M₂（copy_n_3 の役、`gM2`）は互いに逆。消した印は y か T（`er`）、
    右端の b に書く印は N か ∗（`wr`）、書き戻しは N か T（`loN`）、右端に書き足すのは親と同じ ϕ₁(c)。
  * E（右へ、copy_end の役）: T ↦ n、N ↦ y、y ↦ Y、n ↦ $（`gce`）で、境目の形に戻る。
  停止配置は、null は `rep9` のまま、halt は M₂ の掃引のあと `b · RA(0) · Y · loN(rm) · $ · ϕ₁(v)`（`finCfg9`）。
  読み戻しは (10,7) と同じ（lean-univ の `U9_8`・`MoritaGen2.readM2`: 区切りは ∗ と Y の両方を数える）。

  証明の組み立ては CTSH10_7.lean と同じ（`simulates_of_steps`）。掃引は CTSHSim の写像つきの補題
  （`runRg`・`runL1g`・`runLg`・`sweepLg`）で書く。規則が表にあることは `decide`。
-/
import URTM.CTSH10_7

namespace URTM.CTSH.U9_8

open URTM URTM.KState URTM.CTSH URTM.CTSH.Sim URTM.Gen.K13_7
open URTM.CTSH.U10_7 (T10)

/-! ## 0. 記号と ϕ₁ -/

/-- 8 記号: s0 = b、s1 = y、s2 = n、s3 = Y（`y1`）、s4 = N（`*_t3_t3`）、s5 = ∗、s6 = $、s7 = T（`*_t2`）。 -/
inductive Sy8 where
  | s0 | s1 | s2 | s3 | s4 | s5 | s6 | s7
  deriving DecidableEq, Repr

def ss8 : List Sy8 := [Sy8.s0, Sy8.s1, Sy8.s2, Sy8.s3, Sy8.s4, Sy8.s5, Sy8.s6, Sy8.s7]
theorem hS8 : ∀ s, s ∈ ss8 := by intro s; cases s <;> decide

/-- ϕ₁: Y ↦ y、N ↦ n。 -/
def lo9 : Ch → Sy8
  | .Y => Sy8.s1
  | .N => Sy8.s2

/-- (13,7) の形の規則領域とその部分（色を付ける前）。区切りは ∗、相マーカーは b。 -/
abbrev Hi9 (C : CTSH) (m : Nat) : List Sy8 := Sim.Hi lo9 Sy8.s5 C m
abbrev Lo9 (C : CTSH) (m : Nat) : List Sy8 := Sim.Lo lo9 Sy8.s5 C m
abbrev LoCore9 (C : CTSH) (m : Nat) : List Sy8 := Sim.LoCore lo9 Sy8.s5 C m
abbrev RA9b (C : CTSH) (m : Nat) : List Sy8 := Sim.RA lo9 Sy8.s5 Sy8.s0 C m

/-! ## 1. 子の表（親 (10,7) の表の像） -/

/-- 親 (10,7) の 7 色の埋め込み。 -/
def cv : Sy → Sy8
  | .s0 => .s0
  | .s1 => .s1
  | .s2 => .s2
  | .s3 => .s3
  | .s4 => .s4
  | .s5 => .s5
  | .s6 => .s6


/-! ## 1. 子の表（親 (10,7) の表の像） -/

/-- 状態の併合（親の状態 → 子の状態）: copy_n_3（q10）→ M′（q1 = case_y_1 の座）。 -/
def mu : St → St
  | .q10 => .q1
  | q => q

def muT : Tgt St Ps → Tgt St Ps
  | .go q => .go (mu q)
  | .halt h => .halt h

/-- 書き換える規則（親 (10,7) の (状態, 読む記号) → 子の (読む記号, 書く記号) の列。2 本に写るものが 4 つ）。
    書いていない組は色の埋め込みそのまま `[(cv s, cv t)]`。 -/
def chgSym (p : St) (s t : Sy) : List (Sy8 × Sy8) :=
  match p, s with
  | .q0, .s2 => [(.s2, .s5)]
  | .q1, .s2 => [(.s2, .s7)]
  | .q2, .s5 => [(.s2, .s2)]
  | .q2, .s2 => [(.s7, .s2)]
  | .q3, .s6 => [(.s6, .s2)]
  | .q3, .s2 => [(.s2, .s7)]
  | .q4, .s2 => [(.s2, .s7)]
  | .q4, .s1 => [(.s1, .s1)]
  | .q5, .s6 => [(.s5, .s5)]
  | .q5, .s5 => [(.s2, .s7)]
  | .q5, .s2 => [(.s7, .s5), (.s2, .s7)]
  | .q7, .s5 => [(.s5, .s7), (.s7, .s2)]
  | .q7, .s0 => [(.s1, .s4)]
  | .q7, .s2 => [(.s7, .s2)]
  | .q8, .s6 => [(.s5, .s5)]
  | .q8, .s5 => [(.s2, .s5)]
  | .q8, .s4 => [(.s4, .s1)]
  | .q8, .s3 => [(.s3, .s6)]
  | .q8, .s0 => [(.s0, .s5)]
  | .q8, .s2 => [(.s7, .s2), (.s2, .s5)]
  | .q8, .s1 => [(.s1, .s4)]
  | .q10, .s6 => [(.s5, .s2)]
  | .q10, .s5 => [(.s6, .s3)]
  | .q10, .s4 => [(.s5, .s2), (.s2, .s7)]
  | .q10, .s3 => [(.s7, .s7)]
  | .q10, .s0 => [(.s1, .s4)]
  | .q10, .s1 => [(.s4, .s1)]
  | .q11, .s6 => [(.s5, .s2)]
  | .q11, .s5 => [(.s2, .s6)]
  | .q11, .s2 => [(.s7, .s2)]
  | _, _ => [(cv s, cv t)]

/-- 親の規則 1 本の像（1 本か 2 本）。 -/
def chg (r : Rule St Ps Sy) : List (Rule St Ps Sy8) :=
  (chgSym r.p r.s r.t).map fun st => ⟨mu r.p, st.1, st.2, r.d, muT r.q⟩

/-- **URTM(9,8) の表**（54 本）: 親の 57 本の像（61 本）から重複を除いたもの。 -/
def T9 : Machine St Ps Sy8 := (T10.flatMap chg).eraseDups

theorem T9_length : T9.length = 54 := by decide
theorem hD9 : Deterministic T9 := by decide
theorem hR9 : Reversible T9 := by decide
/-- 状態 q6・q9・q10・q12 は子の表に現れない（状態は 9 個）。 -/
theorem unused_states : ∀ ρ ∈ T9, ρ.p ≠ .q6 ∧ ρ.p ≠ .q9 ∧ ρ.p ≠ .q10 ∧ ρ.p ≠ .q12 ∧
    ρ.q ≠ .go .q6 ∧ ρ.q ≠ .go .q9 ∧ ρ.q ≠ .go .q10 ∧ ρ.q ≠ .go .q12 := by decide

/-! ## 2. 掃引の書き換え -/

/-- M₂（左へ）: y ↦ N、n ↦ T、$ ↦ Y、∗ ↦ n、N ↦ y。case_y_1 の役では {y, n, $} を、copy_n_3 の役では `gn1` の像を通る。 -/
def gM2 : Sy8 → Sy8
  | Sy8.s1 => Sy8.s4
  | Sy8.s2 => Sy8.s7
  | Sy8.s6 => Sy8.s3
  | Sy8.s5 => Sy8.s2
  | Sy8.s4 => Sy8.s1
  | x => x
/-- M（右へ）: Y ↦ $、N ↦ y、T ↦ n、y ↦ ∗。 -/
def gM : Sy8 → Sy8
  | Sy8.s3 => Sy8.s6
  | Sy8.s4 => Sy8.s1
  | Sy8.s7 => Sy8.s2
  | Sy8.s1 => Sy8.s5
  | x => x
/-- case_y_n（左へ）: y ↦ N、n ↦ T、Y ↦ y、$ ↦ n。 -/
def gcyn : Sy8 → Sy8
  | Sy8.s1 => Sy8.s4
  | Sy8.s2 => Sy8.s7
  | Sy8.s3 => Sy8.s1
  | Sy8.s6 => Sy8.s2
  | x => x
/-- 境目での Lo(m) の形: ∗ ↦ Y。 -/
def gSY : Sy8 → Sy8
  | Sy8.s5 => Sy8.s3
  | x => x
/-- コピーの間の Lo(m) の形: ∗ ↦ y、y ↦ N、n ↦ T。 -/
def gL : Sy8 → Sy8
  | Sy8.s5 => Sy8.s1
  | Sy8.s1 => Sy8.s4
  | Sy8.s2 => Sy8.s7
  | x => x
/-- copy_y_1（右へ）: T ↦ ∗、N ↦ $、n ↦ T、y ↦ N（Y はそのまま）。 -/
def gc1 : Sy8 → Sy8
  | Sy8.s7 => Sy8.s5
  | Sy8.s4 => Sy8.s6
  | Sy8.s2 => Sy8.s7
  | Sy8.s1 => Sy8.s4
  | x => x
/-- copy_y_3（左へ）: ∗ ↦ T、$ ↦ N、T ↦ n、N ↦ y（`gc1` の逆）。 -/
def hc1 : Sy8 → Sy8
  | Sy8.s5 => Sy8.s7
  | Sy8.s6 => Sy8.s4
  | Sy8.s7 => Sy8.s2
  | Sy8.s4 => Sy8.s1
  | x => x
/-- copy_n_1（右へ）: T ↦ n、N ↦ y、y ↦ N、n ↦ ∗、Y ↦ $（M₂ の `gM2` が逆）。 -/
def gn1 : Sy8 → Sy8
  | Sy8.s7 => Sy8.s2
  | Sy8.s4 => Sy8.s1
  | Sy8.s1 => Sy8.s4
  | Sy8.s2 => Sy8.s5
  | Sy8.s3 => Sy8.s6
  | x => x
/-- E（右へ、copy_end の役）: T ↦ n、N ↦ y、y ↦ Y、n ↦ $。 -/
def gce : Sy8 → Sy8
  | Sy8.s7 => Sy8.s2
  | Sy8.s4 => Sy8.s1
  | Sy8.s1 => Sy8.s3
  | Sy8.s2 => Sy8.s6
  | x => x

/-- copy_c_1 の書き換えと copy_c_3 の書き換え（copy_n_3 の役は M₂）。 -/
def gc : Ch → Sy8 → Sy8
  | .Y => gc1
  | .N => gn1
def hc : Ch → Sy8 → Sy8
  | .Y => hc1
  | .N => gM2

/-- copy_c_1 の座: copy_y_1 = q5、copy_n_1 = q8。 -/
def c1 : Ch → St
  | .Y => .q5
  | .N => .q8
/-- copy_c_3 の座: copy_y_3 = q7、copy_n_3 → M₂ = q1。 -/
def c3 : Ch → St
  | .Y => .q7
  | .N => .q1
/-- copy_c_2 の座: copy_y_2 → M = q2、copy_n_2 → E = q11。 -/
def c2' : Ch → St
  | .Y => .q2
  | .N => .q11
/-- copy_start が規則の 1 文字を消した印: y は y のまま、n は T。 -/
def er : Ch → Sy8
  | .Y => Sy8.s1
  | .N => Sy8.s7
/-- copy_c_1 が右端の b に書く印: y は N、n は ∗。copy_c_3 がこれを ϕ₁(c) に戻す。 -/
def wr : Ch → Sy8
  | .Y => Sy8.s4
  | .N => Sy8.s5
/-- 消去済みの記号の色（M₂ の掃引のあと）。copy_c_3 が印に書き戻す記号でもある: Y ↦ N、N ↦ T。 -/
def loN : Ch → Sy8
  | .Y => Sy8.s4
  | .N => Sy8.s7
/-- 処理中の先頭の記号の印: Y は Y、N は ∗。 -/
def mk : Ch → Sy8
  | .Y => Sy8.s3
  | .N => Sy8.s5

/-- {y, n, ∗}（(13,7) の形の規則領域の記号）。 -/
def YNS (x : Sy8) : Prop := x = Sy8.s1 ∨ x = Sy8.s2 ∨ x = Sy8.s5
/-- {y, n, $}（M₂ が case_y_1 の役で通過する）。 -/
def YND (x : Sy8) : Prop := x = Sy8.s1 ∨ x = Sy8.s2 ∨ x = Sy8.s6
/-- {Y, N, T}（M が case_y_2 の役で通過する）。 -/
def YNT (x : Sy8) : Prop := x = Sy8.s3 ∨ x = Sy8.s4 ∨ x = Sy8.s7
/-- {y, N, T}（M が cycle_end の役で通過する）。 -/
def yNT (x : Sy8) : Prop := x = Sy8.s1 ∨ x = Sy8.s4 ∨ x = Sy8.s7
/-- {y, n, Y, $}（case_y_n が通過する）。 -/
def YNYD (x : Sy8) : Prop := x = Sy8.s1 ∨ x = Sy8.s2 ∨ x = Sy8.s3 ∨ x = Sy8.s6
/-- {y, n, T, N, Y}（copy_*_1・copy_*_3 が通過する）。 -/
def YNTNY (x : Sy8) : Prop := x = Sy8.s1 ∨ x = Sy8.s2 ∨ x = Sy8.s7 ∨ x = Sy8.s4 ∨ x = Sy8.s3
/-- {y, n, T, N}（E が copy_end の役で通過する）。 -/
def YNTN (x : Sy8) : Prop := x = Sy8.s1 ∨ x = Sy8.s2 ∨ x = Sy8.s7 ∨ x = Sy8.s4

theorem lo_YNS : ∀ c, YNS (lo9 c) := by intro c; cases c <;> simp [YNS, lo9]
theorem lo_YND : ∀ c, YND (lo9 c) := by intro c; cases c <;> simp [YND, lo9]
theorem lo_YNYD : ∀ c, YNYD (lo9 c) := by intro c; cases c <;> simp [YNYD, lo9]
theorem lo_YNTNY : ∀ c, YNTNY (lo9 c) := by intro c; cases c <;> simp [YNTNY, lo9]
theorem loN_YNTNY : ∀ c, YNTNY (loN c) := by intro c; cases c <;> simp [YNTNY, loN]
theorem loN_YNTN : ∀ c, YNTN (loN c) := by intro c; cases c <;> simp [YNTN, loN]
theorem loN_YNT : ∀ c, YNT (loN c) := by intro c; cases c <;> simp [YNT, loN]
theorem loN_yNT : ∀ c, yNT (loN c) := by intro c; cases c <;> simp [yNT, loN]
theorem gSY_YNYD : ∀ x, YNS x → YNYD (gSY x) := by
  rintro x (rfl | rfl | rfl) <;> simp [YNYD, gSY]
theorem gL_YNTNY : ∀ x, YNS x → YNTNY (gL x) := by
  rintro x (rfl | rfl | rfl) <;> simp [YNTNY, gL]
theorem gL_YNTN : ∀ x, YNS x → YNTN (gL x) := by
  rintro x (rfl | rfl | rfl) <;> simp [YNTN, gL]
theorem gL_yNT : ∀ x, YNS x → yNT (gL x) := by
  rintro x (rfl | rfl | rfl) <;> simp [yNT, gL]

theorem fa_map_of {P R : Sy8 → Prop} {f : Sy8 → Sy8} (hf : ∀ x, P x → R (f x)) {L : List Sy8}
    (hL : ∀ x ∈ L, P x) : ∀ y ∈ L.map f, R y := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
  exact hf x (hL x hx)

/-- 写像の合成（`List.map_map` のあとに使う）。 -/
theorem gM2_lo : gM2 ∘ lo9 = loN := by funext c; cases c <;> rfl
theorem gcyn_lo : gcyn ∘ lo9 = loN := by funext c; cases c <;> rfl
theorem gM_loN : gM ∘ loN = lo9 := by funext c; cases c <;> rfl
theorem gce_loN : gce ∘ loN = lo9 := by funext c; cases c <;> rfl
theorem gSY_lo : gSY ∘ lo9 = lo9 := by funext c; cases c <;> rfl
theorem gM2_dl : gM2 Sy8.s6 = Sy8.s3 := rfl
theorem gcyn_dl : gcyn Sy8.s6 = Sy8.s2 := rfl
theorem gcyn_Y : gcyn Sy8.s3 = Sy8.s1 := rfl
theorem gM_Y : gM Sy8.s3 = Sy8.s6 := rfl
theorem gM_y : gM Sy8.s1 = Sy8.s5 := rfl
theorem gce_y : gce Sy8.s1 = Sy8.s3 := rfl
theorem gce_n : gce Sy8.s2 = Sy8.s6 := rfl
theorem gSY_st : gSY Sy8.s5 = Sy8.s3 := rfl
theorem gL_st : gL Sy8.s5 = Sy8.s1 := rfl

theorem map_gcyn_gSY {L : List Sy8} (hL : ∀ x ∈ L, YNS x) : L.map (gcyn ∘ gSY) = L.map gL :=
  List.map_congr_left fun x hx => by rcases hL x hx with rfl | rfl | rfl <;> rfl
theorem map_gce_gL {L : List Sy8} (hL : ∀ x ∈ L, YNS x) : L.map (gce ∘ gL) = L.map gSY :=
  List.map_congr_left fun x hx => by rcases hL x hx with rfl | rfl | rfl <;> rfl
theorem map_gM_gL {L : List Sy8} (hL : ∀ x ∈ L, YNS x) : L.map (gM ∘ gL) = L :=
  List.map_congr_left (fun x hx => by rcases hL x hx with rfl | rfl | rfl <;> rfl) |>.trans (List.map_id L)

theorem hcgc (c : Ch) : ∀ x, YNTNY x → hc c (gc c x) = x := by
  cases c <;> rintro x (rfl | rfl | rfl | rfl | rfl) <;> rfl
theorem hc_wr (c : Ch) : hc c (wr c) = lo9 c := by cases c <;> rfl

theorem map_hc_gc (c : Ch) {R : List Sy8} (hR : ∀ x ∈ R, YNTNY x) :
    (R.map (gc c)).map (hc c) = R := by
  induction R with
  | nil => rfl
  | cons x R ih =>
    simp only [List.map_cons, hcgc c x (hR x (List.mem_cons_self ..)),
      ih (fun y hy => hR y (List.mem_cons_of_mem _ hy))]

/-! ## 3. 規則が表にあること -/

theorem pcy1 : ∀ x, YND x → (⟨.q1, x, gM2 x, .L, .go .q1⟩ : Rule St Ps Sy8) ∈ T9 := by
  rintro x (rfl | rfl | rfl) <;> decide
theorem pM1 : ∀ x, YNT x → (⟨.q2, x, gM x, .R, .go .q2⟩ : Rule St Ps Sy8) ∈ T9 := by
  rintro x (rfl | rfl | rfl) <;> decide
theorem pM2 : ∀ x, yNT x → (⟨.q2, x, gM x, .R, .go .q2⟩ : Rule St Ps Sy8) ∈ T9 := by
  rintro x (rfl | rfl | rfl) <;> decide
theorem pcyn : ∀ x, YNYD x → (⟨.q3, x, gcyn x, .L, .go .q3⟩ : Rule St Ps Sy8) ∈ T9 := by
  rintro x (rfl | rfl | rfl | rfl) <;> decide
theorem pce : ∀ x, YNTN x → (⟨.q11, x, gce x, .R, .go .q11⟩ : Rule St Ps Sy8) ∈ T9 := by
  rintro x (rfl | rfl | rfl | rfl) <;> decide

theorem rcs (c : Ch) : (⟨.q4, lo9 c, er c, .R, .go (c1 c)⟩ : Rule St Ps Sy8) ∈ T9 := by
  cases c <;> decide
theorem rc1b (c : Ch) : (⟨c1 c, Sy8.s0, wr c, .R, .go (c2' c)⟩ : Rule St Ps Sy8) ∈ T9 := by
  cases c <;> decide
theorem rc1N (c : Ch) : (⟨c1 c, Sy8.s5, Sy8.s5, .L, .go (c3 c)⟩ : Rule St Ps Sy8) ∈ T9 := by
  cases c <;> decide
theorem rc2 (c : Ch) : (⟨c2' c, Sy8.s0, Sy8.s0, .L, .go (c3 c)⟩ : Rule St Ps Sy8) ∈ T9 := by
  cases c <;> decide
theorem rc3 (c : Ch) : (⟨c3 c, er c, loN c, .L, .go .q4⟩ : Rule St Ps Sy8) ∈ T9 := by
  cases c <;> decide
theorem pc1 (c : Ch) : ∀ x, YNTNY x →
    (⟨c1 c, x, gc c x, .R, .go (c1 c)⟩ : Rule St Ps Sy8) ∈ T9 := by
  cases c <;> rintro x (rfl | rfl | rfl | rfl | rfl) <;> decide
theorem pc3 (c : Ch) : ∀ x, YNTNY x →
    (⟨c3 c, gc c x, hc c (gc c x), .L, .go (c3 c)⟩ : Rule St Ps Sy8) ∈ T9 := by
  cases c <;> rintro x (rfl | rfl | rfl | rfl | rfl) <;> decide
theorem rce (c : Ch) : (⟨.q11, mk c, lo9 c, .R, .go .q0⟩ : Rule St Ps Sy8) ∈ T9 := by
  cases c <;> decide

/-- copy_c_3 が通る列 (gc c)(R)ᴿ の各記号について、hc c で書き戻す規則がある。 -/
theorem pc3_list (c : Ch) {R : List Sy8} (hR : ∀ x ∈ R, YNTNY x) :
    ∀ y ∈ (R.map (gc c)).reverse, (⟨c3 c, y, hc c y, .L, .go (c3 c)⟩ : Rule St Ps Sy8) ∈ T9 := by
  intro y hy
  rw [List.mem_reverse, List.mem_map] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  exact pc3 c x (hR x hx)

theorem pc3_wr (c : Ch) : (⟨c3 c, wr c, hc c (wr c), .L, .go (c3 c)⟩ : Rule St Ps Sy8) ∈ T9 := by
  cases c <;> decide

/-! ## 4. コピー -/

/-- 先頭が Y のとき（書き足す）。親の copy_oneY と同じ道筋。copy_start が印 `er c` を置き、copy_c_1 が
    `gc c` で書き換えつつ右端へ行って `wr c` を書き、copy_c_2 が折り返し、copy_c_3 が `hc c` で戻しつつ印まで戻って
    `loN c` を書く。 -/
theorem copy_oneY (c : Ch) {LL : List Sy8} (hLL : LL ≠ []) {R : List Sy8}
    (hR : ∀ x ∈ R, YNTNY x) :
    Reach T9 (zc Sy8.s0 (.go .q4) LL (lo9 c) R)
      (zl Sy8.s0 (.go .q4) LL (loN c :: R ++ [lo9 c])) := by
  rw [← zc_trail _ _ _ R, ← zl_trail]
  refine (runRg (rcs c) (gc c) (fun x hx => pc1 c x (hR x hx)) LL Sy8.s0 []).trans ?_
  rw [zc_nil]
  refine (Reach.step (stepR (rc1b c) _ Sy8.s0 [])).trans ?_
  refine (Reach.step (stepL (rc2 c) (wr c) _ [])).trans ?_
  have hX : ∀ y ∈ wr c :: (R.map (gc c)).reverse,
      (⟨c3 c, y, hc c y, .L, .go (c3 c)⟩ : Rule St Ps Sy8) ∈ T9 := by
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact pc3_wr c
    · exact pc3_list c hR y hy
  refine (sweepLg (hc c) hX (er c) LL [Sy8.s0]).trans ?_
  refine (Reach.step (stepL' (rc3 c) hLL _)).trans ?_
  apply Reach.of_eq
  have hm := map_hc_gc c hR
  simp only [List.map_cons, List.map_reverse, hm, hc_wr, List.reverse_cons, List.reverse_reverse]
  simp

/-- 先頭が N のとき（書き足さない）: copy_c_1 が印の ∗ に当たって引き返す。 -/
theorem copy_oneN (c : Ch) {LL : List Sy8} (hLL : LL ≠ []) {R₁ : List Sy8}
    (hR : ∀ x ∈ R₁, YNTNY x) (R₂ : List Sy8) :
    Reach T9 (zc Sy8.s0 (.go .q4) LL (lo9 c) (R₁ ++ Sy8.s5 :: R₂))
      (zl Sy8.s0 (.go .q4) LL (loN c :: R₁ ++ Sy8.s5 :: R₂)) := by
  refine (runRg (rcs c) (gc c) (fun x hx => pc1 c x (hR x hx)) LL Sy8.s5 R₂).trans ?_
  refine (Reach.step (stepL' (rc1N c) (L := (R₁.map (gc c)).reverse ++ er c :: LL) (by simp) R₂)).trans ?_
  refine (sweepLg (hc c) (pc3_list c hR) (er c) LL (Sy8.s5 :: R₂)).trans ?_
  refine (Reach.step (stepL' (rc3 c) hLL _)).trans ?_
  apply Reach.of_eq
  have hm := map_hc_gc c hR
  simp only [List.map_reverse, hm, List.reverse_reverse]
  simp

theorem copy_loopY (Z : List Sy8) (hZ : Z ≠ []) :
    ∀ (Q P : List Ch) (S : List Sy8), (∀ x ∈ S, YNTNY x) →
    Reach T9 (zl Sy8.s0 (.go .q4) (Q.map lo9 ++ Z) (P.reverse.map loN ++ S))
      (zl Sy8.s0 (.go .q4) Z ((P ++ Q).reverse.map loN ++ S ++ Q.map lo9)) := by
  intro Q
  induction Q with
  | nil => intro P S _; exact Reach.of_eq (by simp)
  | cons c Q ih =>
    intro P S hS
    have hR : ∀ x ∈ P.reverse.map loN ++ S, YNTNY x := fa_app (fa_map loN_YNTNY _) hS
    have h1 := copy_oneY c (LL := Q.map lo9 ++ Z) (by simp [hZ]) hR
    have h2 := ih (P ++ [c]) (S ++ [lo9 c]) (fa_app hS (fa_cons (lo_YNTNY c) fa_nil))
    refine h1.trans (Eq.mpr ?_ h2)
    simp

theorem copy_loopN (Z : List Sy8) (hZ : Z ≠ []) (S₂ : List Sy8) :
    ∀ (Q P : List Ch) (S₁ : List Sy8), (∀ x ∈ S₁, YNTNY x) →
    Reach T9 (zl Sy8.s0 (.go .q4) (Q.map lo9 ++ Z) (P.reverse.map loN ++ S₁ ++ Sy8.s5 :: S₂))
      (zl Sy8.s0 (.go .q4) Z ((P ++ Q).reverse.map loN ++ S₁ ++ Sy8.s5 :: S₂)) := by
  intro Q
  induction Q with
  | nil => intro P S₁ _; exact Reach.of_eq (by simp)
  | cons c Q ih =>
    intro P S₁ hS
    have hR : ∀ x ∈ P.reverse.map loN ++ S₁, YNTNY x := fa_app (fa_map loN_YNTNY _) hS
    have h1 := copy_oneN c (LL := Q.map lo9 ++ Z) (by simp [hZ]) hR S₂
    have h1' : Reach T9
        (zl Sy8.s0 (.go .q4) ((c :: Q).map lo9 ++ Z) (P.reverse.map loN ++ S₁ ++ Sy8.s5 :: S₂))
        (zl Sy8.s0 (.go .q4) (Q.map lo9 ++ Z)
          ((P ++ [c]).reverse.map loN ++ S₁ ++ Sy8.s5 :: S₂)) := by
      refine Eq.mpr ?_ h1; simp [zl]
    have h2 := ih (P ++ [c]) S₁ hS
    refine h1'.trans (Eq.mpr ?_ h2)
    simp

/-! ## 5. 境目の配置と 1 マクロステップ -/

/-- 境目（状態 begin）での規則領域: (13,7) の RA(m) の Lo(m) の区切り ∗ を Y にしたもの（(10,7) の `RA10` と同じ形）。 -/
def RA9 (C : CTSH) (m : Nat) : List Sy8 :=
  Hi9 C m ++ (prod C m).reverse.map lo9 ++ Sy8.s0 :: (Lo9 C m).map gSY

theorem RA9_length (C : CTSH) (m : Nat) : (RA9 C m).length = (RA9b C m).length := by
  simp [RA9, Sim.RA]

/-- 境目のテープ: b · RA9(m) · $ · ϕ₁(rm) · ϕ₁(v)。 -/
def tapeList9 (C : CTSH) (m : Nat) (rm v : List Ch) : List Sy8 :=
  Sy8.s0 :: RA9 C m ++ Sy8.s6 :: rm.map lo9 ++ v.map lo9

/-- CTSH の ID (v, m) と消去済みの記号列 rm を表す配置。状態・ヘッドの位置は (13,7) と同じ。 -/
def rep9 (C : CTSH) (m : Nat) (rm v : List Ch) : Cfg St Ps Sy8 :=
  { st := .go .q0, pos := (RA9b C m).length + 2 + rm.length,
    tape := tp Sy8.s0 (tapeList9 C m rm v) }

theorem rep9_eq (C : CTSH) (m : Nat) (rm v : List Ch) :
    rep9 C m rm v =
      zr Sy8.s0 (.go .q0) (Sy8.s0 :: RA9 C m ++ Sy8.s6 :: rm.map lo9).reverse (v.map lo9) := by
  rw [zr_eq]; simp only [rep9, tapeList9]; congr 1 <;> simp [RA9_length]; omega

/-- M₂ が case_y_1 の役で通る列の各記号について規則がある。 -/
theorem pcy1_list {X : List Sy8} (hX : ∀ x ∈ X, YND x) :
    ∀ x ∈ X, (⟨.q1, x, gM2 x, .L, .go .q1⟩ : Rule St Ps Sy8) ∈ T9 := fun x hx => pcy1 x (hX x hx)

/-- M（case_y_2 の役）が通る列 Y · loN(rm) の各記号について規則がある。 -/
theorem pM1_list (rm : List Ch) :
    ∀ x ∈ Sy8.s3 :: rm.map loN, (⟨.q2, x, gM x, .R, .go .q2⟩ : Rule St Ps Sy8) ∈ T9 :=
  fun x hx => pM1 x ((fa_cons (by simp [YNT]) (fa_map loN_YNT _)) x hx)

/-- 先頭が Y、相 m ≥ 1: begin が y を $ に、M₂ が y ↦ N・n ↦ T・$ ↦ Y と書き換えつつ Lo(m) の末尾の Y まで、
    M が Y ↦ $・N ↦ y・T ↦ n と戻しつつ印 $ まで（印を Y に）、case_y_n が y ↦ N・n ↦ T・Y ↦ y・$ ↦ n と
    書き換えつつ相マーカー b まで（b を y に）→ copy_start。 -/
theorem frontY (C : CTSH) (m : Nat) (hm : m ≠ 0) (rm v : List Ch) :
    Reach1 T9 (rep9 C m rm (.Y :: v))
      (zl Sy8.s0 (.go .q4) ((prod C m).map lo9 ++ (Sy8.s0 :: Hi9 C m).reverse)
        (Sy8.s1 :: (Lo9 C m).map gL ++ Sy8.s2 :: rm.map loN ++ Sy8.s3 :: v.map lo9)) := by
  have hLc : ∀ x ∈ LoCore9 C m, YNS x := LoCore_mem lo_YNS (by simp [YNS]) C m
  rw [rep9_eq]
  simp only [List.map_cons, zr, lo9]
  rw [show (Sy8.s0 :: RA9 C m ++ Sy8.s6 :: rm.map lo9).reverse =
      ((rm.map lo9).reverse ++ [Sy8.s6]) ++ Sy8.s3 :: (((LoCore9 C m).map gSY).reverse ++ Sy8.s0 ::
        ((prod C m).map lo9 ++ (Sy8.s0 :: Hi9 C m).reverse)) by
    simp [RA9, Sim.Lo_ne C m hm, gSY_st]]
  refine (runL1g (p := St.q0) (q := St.q1) (h := Sy8.s1) (t := Sy8.s6) (by decide) gM2
    (pcy1_list (fa_app (fa_rev (fa_map lo_YND _)) (fa_cons (by simp [YND]) fa_nil)))
    Sy8.s3 _ _).trans ?_
  rw [show (((rm.map lo9).reverse ++ [Sy8.s6]).map gM2).reverse = Sy8.s3 :: rm.map loN by
    simp [List.map_reverse, List.map_map, gM2_lo, gM2_dl]]
  refine (runRg (p := St.q1) (q := St.q2) (h := Sy8.s3) (t := Sy8.s3) (by decide) gM
    (X := Sy8.s3 :: rm.map loN) (pM1_list rm) _ Sy8.s6 _).trans ?_
  rw [show ((Sy8.s3 :: rm.map loN).map gM) = Sy8.s6 :: rm.map lo9 by
    simp [List.map_map, gM_loN, gM_Y]]
  rw [show (Sy8.s6 :: rm.map lo9).reverse ++ Sy8.s3 :: (((LoCore9 C m).map gSY).reverse ++ Sy8.s0 ::
        ((prod C m).map lo9 ++ (Sy8.s0 :: Hi9 C m).reverse)) =
      ((rm.map lo9).reverse ++ Sy8.s6 :: Sy8.s3 :: ((LoCore9 C m).map gSY).reverse) ++ Sy8.s0 ::
        ((prod C m).map lo9 ++ (Sy8.s0 :: Hi9 C m).reverse) by simp]
  refine (runLg (p := St.q2) (q := St.q3) (h := Sy8.s6) (t := Sy8.s3) (by decide) gcyn
    (fun x hx => pcyn x ((fa_app (fa_rev (fa_map lo_YNYD _)) (fa_cons (by simp [YNYD])
      (fa_cons (by simp [YNYD]) (fa_rev (fa_map_of gSY_YNYD hLc)))))
      x hx))
    Sy8.s0 _ _).trans ?_
  refine (Reach.step (stepL' (p := St.q3) (h := Sy8.s0) (t := Sy8.s1) (q := .go St.q4) (by decide)
    (L := (prod C m).map lo9 ++ (Sy8.s0 :: Hi9 C m).reverse) (by simp) _)).trans ?_
  apply Reach.of_eq
  simp only [List.map_append, List.map_cons, List.map_reverse, List.map_map, gcyn_lo, gcyn_dl, gcyn_Y,
    map_gcyn_gSY hLc, List.reverse_append, List.reverse_cons,
    List.reverse_reverse, Sim.Lo_ne C m hm]
  simp [gL_st]

/-- 先頭が N（任意の相）: begin が n を ∗ に、case_y_n が書き換えつつ相マーカー b まで → copy_start。 -/
theorem frontN (C : CTSH) (m : Nat) (rm v : List Ch) :
    Reach1 T9 (rep9 C m rm (.N :: v))
      (zl Sy8.s0 (.go .q4) ((prod C m).map lo9 ++ (Sy8.s0 :: Hi9 C m).reverse)
        (Sy8.s1 :: (Lo9 C m).map gL ++ Sy8.s2 :: rm.map loN ++ Sy8.s5 :: v.map lo9)) := by
  rw [rep9_eq]
  simp only [List.map_cons, zr, lo9]
  rw [show (Sy8.s0 :: RA9 C m ++ Sy8.s6 :: rm.map lo9).reverse =
      ((rm.map lo9).reverse ++ Sy8.s6 :: ((Lo9 C m).map gSY).reverse) ++ Sy8.s0 ::
        ((prod C m).map lo9 ++ (Sy8.s0 :: Hi9 C m).reverse) by simp [RA9]]
  have hLoS : ∀ x ∈ Lo9 C m, YNS x := Lo_mem lo_YNS (by simp [YNS]) C m
  refine (runL1g (p := St.q0) (q := St.q3) (h := Sy8.s2) (t := Sy8.s5) (by decide) gcyn
    (fun x hx => pcyn x ((fa_app (fa_rev (fa_map lo_YNYD _)) (fa_cons (by simp [YNYD])
      (fa_rev (fa_map_of gSY_YNYD hLoS)))) x hx))
    Sy8.s0 _ _).trans ?_
  refine (Reach.step (stepL' (p := St.q3) (h := Sy8.s0) (t := Sy8.s1) (q := .go St.q4) (by decide)
    (L := (prod C m).map lo9 ++ (Sy8.s0 :: Hi9 C m).reverse) (by simp) _)).trans ?_
  apply Reach.of_eq
  simp only [List.map_append, List.map_cons, List.map_reverse, List.map_map, gcyn_lo, gcyn_dl,
    map_gcyn_gSY hLoS, List.reverse_append, List.reverse_cons, List.reverse_reverse]
  simp

/-- E が copy_end の役で通る列の各記号について規則がある。 -/
theorem pce_list {X : List Sy8} (hX : ∀ x ∈ X, YNTN x) :
    ∀ x ∈ X, (⟨.q11, x, gce x, .R, .go .q11⟩ : Rule St Ps Sy8) ∈ T9 := fun x hx => pce x (hX x hx)

/-- 相の終わり: copy_start が次の区切り ∗ を b（新しい相マーカー）にして E が `gce` で境目の形に
    戻しつつ印まで行き、印を小文字に戻して begin。m = k−1 なら左端の b で M（cycle_end の役）に入り、
    `gM` で規則を小文字に戻しつつ印 n の手前の ∗ で折り返して copy_start、その ∗ を相マーカーに。 -/
theorem finish (C : CTSH) (m : Nat) (hk : m ≤ C.length) (c : Ch) (rm v : List Ch) :
    Reach T9 (zl Sy8.s0 (.go .q4) (Sy8.s0 :: Hi9 C m).reverse
        ((prod C m).reverse.map loN ++ Sy8.s1 :: (Lo9 C m).map gL ++ Sy8.s2 :: rm.map loN ++
          mk c :: v.map lo9))
      (rep9 C ((m + 1) % C.k) (rm ++ [c]) v) := by
  have hLoS : ∀ x ∈ Lo9 C m, YNS x := Lo_mem lo_YNS (by simp [YNS]) C m
  rcases Nat.lt_or_ge m C.length with h | h
  · rw [Nat.mod_eq_of_lt (by simp [CTSH.k]; omega), rep9_eq, Hi9, Sim.Hi_step C m h]
    rw [show (Sy8.s0 :: (Sim.Hi lo9 Sy8.s5 C (m + 1) ++ (prod C (m + 1)).reverse.map lo9 ++
          [Sy8.s5])).reverse =
        Sy8.s5 :: (Sy8.s0 :: Sim.Hi lo9 Sy8.s5 C (m + 1) ++ (prod C (m + 1)).reverse.map lo9).reverse
        by simp]
    simp only [zl]
    rw [show (prod C m).reverse.map loN ++ Sy8.s1 :: (Lo9 C m).map gL ++ Sy8.s2 :: rm.map loN ++
          mk c :: v.map lo9 =
        ((prod C m).reverse.map loN ++ Sy8.s1 :: (Lo9 C m).map gL ++ Sy8.s2 :: rm.map loN) ++
          mk c :: v.map lo9 by simp]
    refine (runRg (p := St.q4) (q := St.q11) (h := Sy8.s5) (t := Sy8.s0) (by decide) gce
      (pce_list (fa_app (fa_app (fa_map loN_YNTN _) (fa_cons (by simp [YNTN])
        (fa_map_of gL_YNTN hLoS))) (fa_cons (by simp [YNTN]) (fa_map loN_YNTN _))))
      _ _ _).trans ?_
    refine (Reach.step (stepR' (rce c) _ _)).trans ?_
    apply Reach.of_eq
    congr 1
    simp only [List.map_append, List.map_cons, List.map_map, gce_loN, gce_y, gce_n,
      map_gce_gL hLoS]
    simp [RA9, Sim.Lo_step (lo := lo9) (st := Sy8.s5) C m hk, List.map_map, gSY_lo, gSY_st]
  · have hmk : m = C.length := by omega
    subst hmk
    rw [show (C.length + 1) % C.k = 0 by simp [CTSH.k], rep9_eq, Hi9, Sim.Hi_len]
    simp only [zl, List.reverse_cons, List.reverse_nil, List.nil_append]
    have hLo := Sim.Lo_step (lo := lo9) (st := Sy8.s5) C C.length (Nat.le_refl _)
    rw [show (prod C C.length).reverse.map loN ++ Sy8.s1 :: (Lo9 C C.length).map gL ++
          Sy8.s2 :: rm.map loN ++ mk c :: v.map lo9 =
        ((prod C C.length).reverse.map loN ++ Sy8.s1 :: (Lo9 C C.length).map gL) ++
          Sy8.s2 :: (rm.map loN ++ mk c :: v.map lo9) by simp]
    refine (runRg (p := St.q4) (q := St.q2) (h := Sy8.s0) (t := Sy8.s0) (by decide) gM
      (fun x hx => pM2 x ((fa_app (fa_map loN_yNT _) (fa_cons (by simp [yNT]) (fa_map_of gL_yNT hLoS)))
        x hx)) [] _ _).trans ?_
    have hX : ((prod C C.length).reverse.map loN ++ Sy8.s1 :: (Lo9 C C.length).map gL).map gM =
        Sim.LoCore lo9 Sy8.s5 C (C.length + 1) ++ [Sy8.s5] := by
      simp only [List.map_append, List.map_cons, List.map_map, gM_loN, gM_y, map_gM_gL hLoS]
      rw [← Sim.Lo_ne C (C.length + 1) (by omega), hLo]
    rw [hX]
    rw [show (Sim.LoCore lo9 Sy8.s5 C (C.length + 1) ++ [Sy8.s5]).reverse ++ [Sy8.s0] =
        Sy8.s5 :: ((Sim.LoCore lo9 Sy8.s5 C (C.length + 1)).reverse ++ [Sy8.s0]) by simp]
    refine (Reach.step (stepL (p := St.q2) (h := Sy8.s2) (t := Sy8.s2) (q := .go St.q4) (by decide)
      _ _ _)).trans ?_
    rw [show Sy8.s2 :: (rm.map loN ++ mk c :: v.map lo9) =
        (Sy8.s2 :: rm.map loN) ++ mk c :: v.map lo9 by simp]
    refine (runRg (p := St.q4) (q := St.q11) (h := Sy8.s5) (t := Sy8.s0) (by decide) gce
      (pce_list (fa_cons (by simp [YNTN]) (fa_map loN_YNTN _))) _ _ _).trans ?_
    refine (Reach.step (stepR' (rce c) _ _)).trans ?_
    apply Reach.of_eq
    congr 1
    simp only [List.map_cons, List.map_map, gce_loN, gce_n]
    simp [RA9, Sim.LoCore_full, lo9, prod, Sim.Lo]

theorem macroY (C : CTSH) {m : Nat} (h0 : m ≠ 0) (hk : m < C.k) (rm v : List Ch) :
    Reach1 T9 (rep9 C m rm (.Y :: v)) (rep9 C ((m + 1) % C.k) (rm ++ [.Y]) (v ++ prod C m)) := by
  have hmk : m ≤ C.length := by simp [CTSH.k] at hk; omega
  refine (frontY C m h0 rm v).trans ?_
  have hS : ∀ x ∈ Sy8.s1 :: (Lo9 C m).map gL ++ Sy8.s2 :: rm.map loN ++ Sy8.s3 :: v.map lo9,
      YNTNY x :=
    fa_app (fa_app (fa_cons (by simp [YNTNY]) (fa_map_of gL_YNTNY (Lo_mem lo_YNS (by simp [YNS]) C m)))
      (fa_cons (by simp [YNTNY]) (fa_map loN_YNTNY _)))
      (fa_cons (by simp [YNTNY]) (fa_map lo_YNTNY _))
  have hL := copy_loopY _ (by simp : (Sy8.s0 :: Hi9 C m).reverse ≠ []) (prod C m) [] _ hS
  refine hL.trans ?_
  have hf := finish C m hmk .Y rm (v ++ prod C m)
  refine Eq.mpr ?_ hf
  simp [mk]

theorem macroN (C : CTSH) {m : Nat} (hk : m < C.k) (rm v : List Ch) :
    Reach1 T9 (rep9 C m rm (.N :: v)) (rep9 C ((m + 1) % C.k) (rm ++ [.N]) v) := by
  have hmk : m ≤ C.length := by simp [CTSH.k] at hk; omega
  refine (frontN C m rm v).trans ?_
  have hS : ∀ x ∈ Sy8.s1 :: (Lo9 C m).map gL ++ Sy8.s2 :: rm.map loN, YNTNY x :=
    fa_app (fa_cons (by simp [YNTNY]) (fa_map_of gL_YNTNY (Lo_mem lo_YNS (by simp [YNS]) C m)))
      (fa_cons (by simp [YNTNY]) (fa_map loN_YNTNY _))
  have hL := copy_loopN _ (by simp : (Sy8.s0 :: Hi9 C m).reverse ≠ []) (v.map lo9)
    (prod C m) [] _ hS
  have hL' : Reach T9
      (zl Sy8.s0 (.go .q4) ((prod C m).map lo9 ++ (Sy8.s0 :: Hi9 C m).reverse)
        (Sy8.s1 :: (Lo9 C m).map gL ++ Sy8.s2 :: rm.map loN ++ Sy8.s5 :: v.map lo9))
      (zl Sy8.s0 (.go .q4) (Sy8.s0 :: Hi9 C m).reverse
        ((prod C m).reverse.map loN ++ Sy8.s1 :: (Lo9 C m).map gL ++ Sy8.s2 :: rm.map loN ++
          Sy8.s5 :: v.map lo9)) := by
    refine Eq.mpr ?_ hL; simp
  refine hL'.trans ?_
  have hf := finish C m hmk .N rm v
  refine Eq.mpr ?_ hf
  simp [mk]

/-! ## 6. 停止 -/

/-- 停止配置のテープ（リスト）。(λ, m) は境目のまま。(Y v, 0) は begin が y を $ に、M₂ が
    y ↦ N・n ↦ T・$ ↦ Y と書き換えつつ相マーカー b まで行って halt: `b · RA(0) · Y · loN(rm) · $ · ϕ₁(v)`。 -/
def finList9 (C : CTSH) (vf : List Ch) (mf : Nat) (rm : List Ch) : List Sy8 :=
  match vf with
  | [] => tapeList9 C mf rm []
  | _ :: v => Sy8.s0 :: RA9b C 0 ++ Sy8.s3 :: rm.map loN ++ Sy8.s6 :: v.map lo9

/-- 停止配置。状態とヘッドの位置は (13,7)・(10,7) と同じ。 -/
def finCfg9 (C : CTSH) (vf : List Ch) (mf : Nat) (rm : List Ch) : Cfg St Ps Sy8 :=
  match vf with
  | [] => { st := .halt .h0, pos := (RA9b C mf).length + 2 + rm.length,
            tape := tp Sy8.s0 (finList9 C [] mf rm) }
  | c :: v => { st := .halt .h1, pos := (RA9b C 0).length,
                tape := tp Sy8.s0 (finList9 C (c :: v) 0 rm) }

theorem halt_null (C : CTSH) (m : Nat) (rm : List Ch) :
    Reach1 T9 (rep9 C m rm []) (finCfg9 C [] m rm) := by
  rw [rep9_eq]
  simp only [List.map_nil, zr]
  refine Reach1.of_step (stepZ (p := St.q0) (h := Sy8.s0) (t := Sy8.s0) (q := Tgt.halt Ps.h0) (by decide)
    _ _) (Reach.of_eq ?_)
  simp only [zc, finCfg9, finList9, tapeList9]
  congr 1
  · simp [RA9_length]; omega
  · simpa using tp_trail (bk := Sy8.s0) (Sy8.s0 :: (RA9 C m ++ Sy8.s6 :: List.map lo9 rm))

theorem halt_Y (C : CTSH) (rm v : List Ch) :
    Reach1 T9 (rep9 C 0 rm (.Y :: v)) (finCfg9 C (.Y :: v) 0 rm) := by
  rw [rep9_eq]
  simp only [List.map_cons, zr, lo9]
  rw [show (Sy8.s0 :: RA9 C 0 ++ Sy8.s6 :: rm.map lo9).reverse =
      ((rm.map lo9).reverse ++ [Sy8.s6]) ++ Sy8.s0 :: (Sy8.s0 :: Hi9 C 0).reverse by
    simp [RA9, prod, Sim.Lo]]
  refine (runL1g (p := St.q0) (q := St.q1) (h := Sy8.s1) (t := Sy8.s6) (by decide) gM2
    (pcy1_list (fa_app (fa_rev (fa_map lo_YND _)) (fa_cons (by simp [YND]) fa_nil)))
    Sy8.s0 _ _).trans ?_
  refine (Reach.step (stepZ (p := St.q1) (h := Sy8.s0) (t := Sy8.s0) (q := Tgt.halt Ps.h1) (by decide)
    _ _)).trans ?_
  apply Reach.of_eq
  simp only [zc, finCfg9, finList9]
  congr 1
  · simp [Sim.RA_zero]
  · simp [Sim.RA_zero, List.map_reverse, List.map_map, gM2_lo, gM2_dl]

theorem finCfg9_halted (C : CTSH) (vf : List Ch) (mf : Nat) (rm : List Ch) :
    Halted T9 (finCfg9 C vf mf rm) := by
  intro c' ⟨r, _, hst, _⟩
  cases vf <;> simp [finCfg9] at hst

/-! ## 7. 主定理 -/

/-- 初期配置は (13,7) の符号化そのもの（相 0 では Lo(0) = λ なので RA9(0) は (13,7) の RA(0)）。 -/
def encC9 (C : CTSH) (w : List Ch) : Cfg St Ps Sy8 := rep9 C 0 [] w

theorem RA9_zero (C : CTSH) : RA9 C 0 = RA9b C 0 := by
  simp [RA9, Sim.RA, Sim.Lo]

theorem encC9_eq (C : CTSH) (w : List Ch) :
    encC9 C w = ⟨.go .q0, (((RA9b C 0).length + 2 : Nat) : Int),
      tp Sy8.s0 (Sy8.s0 :: RA9b C 0 ++ Sy8.s6 :: w.map lo9)⟩ := by
  simp [encC9, rep9, tapeList9, RA9_zero]

/-- **主定理（URTM(9,8) は任意の CTSH を模倣する）**。`urtm10_7_simulates_ctsh` と同じ 3 項で、
    表は `T9`、停止配置は `finCfg9`。 -/
theorem urtm9_8_simulates_ctsh (C : CTSH) (w : List Ch) :
    (∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) →
      ∃ N rm, n ≤ N ∧ HaltsIn T9 N (encC9 C w) (finCfg9 C vf mf rm)) ∧
    (∀ N e, HaltsIn T9 N (encC9 C w) e →
      ∃ n vf mf rm, CHaltsIn C n (w, 0) (vf, mf) ∧ e = finCfg9 C vf mf rm) ∧
    ((∀ n f, ¬ CHaltsIn C n (w, 0) f) ↔ (∀ N e, ¬ HaltsIn T9 N (encC9 C w) e)) :=
  simulates_of_steps C (rep9 C) (finCfg9 C) hD9 (macroY C) (macroN C) (halt_Y C)
    (halt_null C) (finCfg9_halted C) w

end URTM.CTSH.U9_8
