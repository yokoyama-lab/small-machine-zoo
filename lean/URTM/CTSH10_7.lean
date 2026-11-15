/-
  **URTM(10,7)**（2026-11-02、層 1 の候補）: URTM(11,7)（`URTM.CTSH.U11_7.T11`）に「タグで 2 状態を併合（族 L₁）と
  記号の併合を同時に」当てた表が、任意の CTSH を模倣すること。

  子の表 `T10 = (T11.flatMap chg).eraseDups` は親の 59 本をそれぞれ 1 本か 2 本に写した像（集合として）。
  `mu` は状態の併合（cycle_end → M = case_y_2 の座、q12 → q2）、`chgSym` は読む記号・書く記号の書き換え
  （親の 4 本は、通る時のタグが 2 通りあるので子の 2 本に写る。生成器 `tools/gen_tagchain_lean.py --multi` の出力）。
  像の 63 本のうち 6 本が同じ五つ組になり、子は 57 本。記号は親と同じ 7 つ（b y n Y N ∗ $）だが、意味が違う:
  子の N（`*_t3`）は親の N ではなく、タグ付きの y などを吸収した色。表は書き写していない。

  子の動きは親と 1 歩ずつ同じで、違いはセルの色だけ。CTSH の 1 歩の境目（状態 begin）では
  相 m の規則領域の Lo(m) の区切り ∗ が Y になっている（`gSY`）ほかは親と同じ（`rep10`）。掃引ごとの書き換え:
  * case_y_1（左へ）: y ↦ N、$ ↦ Y（`gcy1`）。M（右へ）: Y ↦ $、N ↦ y、y ↦ ∗（`gM`）。
  * case_y_n（左へ）: y ↦ N、Y ↦ y、$ ↦ ∗（`gcyn`）。copy_start に入るとき Lo(m) は `gL`（∗ ↦ y、y ↦ N）の形、
    消去済みの列 ϕ₁(rm) は `loN`（y ↦ N）の形、$ は ∗、先頭の印 Y/N は Y/$（`mk`）。
  * copy_y_1・copy_y_3（`gc1`・`hc1`）、copy_n_1・copy_n_3（`gn1`・`hn1`）は互いに逆。消した印は b か Y（`er`）、
    書き戻しは N か n（`loE`）、右端に書き足すのは親と同じ ϕ₁(c)。
  * copy_end（右へ）: N ↦ y、y ↦ Y、∗ ↦ $（`gce`）で、境目の形に戻る。
  停止配置は、null は `rep10` のまま、halt は case_y_1 の掃引のあと `b · RA(0) · Y · loN(rm) · $ · ϕ₁(v)`（`finCfg10`）。
  読み戻しは停止状態で変わる（lean-univ の `U10_7`・`MoritaGen2`: 区切りは ∗ と Y の両方を数える）。

  証明の組み立ては CTSH11_7.lean と同じ（`simulates_of_steps`）。掃引は CTSHSim の写像つきの補題
  （`runRg`・`runL1g`・`runLg`・`sweepLg`）で書く。規則が表にあることは `decide`。
-/
import URTM.CTSH11_7

namespace URTM.CTSH.U10_7

open URTM URTM.KState URTM.CTSH URTM.CTSH.Sim URTM.Gen.K13_7
open URTM.CTSH.U13_7 (lo up c1 c3 RA Hi Lo LoCore YND YNS YNSD YNSDY lo_YND lo_YNS lo_YNSD lo_YNSDY nm13)
open URTM.CTSH.U11_7 (T11 loN)

/-! ## 1. 子の表（生成器 tools/gen_tagchain_lean.py --multi の出力） -/

/-- 状態の併合（親の状態 → 子の状態）: cycle_end（q12）→ M（q2 = m_case_y_2_copy_y_2_ の座）。 -/
def mu : St → St
  | .q12 => .q2
  | q => q

def muT : Tgt St Ps → Tgt St Ps
  | .go q => .go (mu q)
  | .halt h => .halt h

/-- 書き換える規則（親 (11,7) の (状態, 読む記号) → 子の (読む記号, 書く記号) の列。2 本に写るものが 4 つ）。 -/
def chgSym (p : St) (s t : Sy) : List (Sy × Sy) :=
  match p, s with
  | .q0, .s1 => [(.s1, .s6)]
  | .q0, .s2 => [(.s2, .s6)]
  | .q1, .s5 => [(.s3, .s3)]
  | .q1, .s6 => [(.s6, .s3)]
  | .q2, .s3 => [(.s6, .s3)]
  | .q2, .s6 => [(.s3, .s6)]
  | .q3, .s0 => [(.s0, .s1)]
  | .q3, .s1 => [(.s1, .s4)]
  | .q3, .s5 => [(.s3, .s1)]
  | .q3, .s6 => [(.s6, .s5)]
  | .q4, .s2 => [(.s2, .s3)]
  | .q5, .s1 => [(.s4, .s6), (.s1, .s4)]
  | .q5, .s2 => [(.s2, .s5)]
  | .q5, .s4 => [(.s6, .s6)]
  | .q5, .s5 => [(.s1, .s4)]
  | .q5, .s6 => [(.s5, .s2)]
  | .q7, .s0 => [(.s0, .s4)]
  | .q7, .s2 => [(.s5, .s2)]
  | .q7, .s4 => [(.s6, .s4), (.s4, .s1)]
  | .q7, .s5 => [(.s4, .s1)]
  | .q7, .s6 => [(.s2, .s5)]
  | .q8, .s1 => [(.s4, .s0), (.s1, .s1)]
  | .q8, .s3 => [(.s3, .s5)]
  | .q8, .s4 => [(.s6, .s6)]
  | .q8, .s5 => [(.s1, .s1)]
  | .q8, .s6 => [(.s5, .s6)]
  | .q10, .s0 => [(.s3, .s2)]
  | .q10, .s1 => [(.s0, .s4), (.s1, .s1)]
  | .q10, .s3 => [(.s5, .s3)]
  | .q10, .s5 => [(.s1, .s1)]
  | .q10, .s6 => [(.s6, .s5)]
  | .q11, .s1 => [(.s4, .s1)]
  | .q11, .s4 => [(.s6, .s2)]
  | .q11, .s5 => [(.s1, .s3)]
  | .q11, .s6 => [(.s5, .s6)]
  | .q12, .s1 => [(.s4, .s1)]
  | .q12, .s5 => [(.s1, .s5)]
  | .q12, .s6 => [(.s5, .s5)]
  | _, _ => [(s, t)]

/-- 親の規則 1 本の像（1 本か 2 本）。 -/
def chg (r : Rule St Ps Sy) : List (Rule St Ps Sy) :=
  (chgSym r.p r.s r.t).map fun st => ⟨mu r.p, st.1, st.2, r.d, muT r.q⟩

/-- **URTM(10,7) の表**（57 本）: 親の 59 本の像（63 本）から重複を除いたもの。 -/
def T10 : Machine St Ps Sy := (T11.flatMap chg).eraseDups

theorem T10_length : T10.length = 57 := by decide
theorem hD10 : Deterministic T10 := by decide
theorem hR10 : Reversible T10 := by decide
/-- 状態 q6・q9・q12 は子の表に現れない（状態は 10 個）。 -/
theorem unused_states : ∀ ρ ∈ T10, ρ.p ≠ .q6 ∧ ρ.p ≠ .q9 ∧ ρ.p ≠ .q12 ∧
    ρ.q ≠ .go .q6 ∧ ρ.q ≠ .go .q9 ∧ ρ.q ≠ .go .q12 := by decide

/-! ## 2. 掃引の書き換え -/

/-- case_y_1（左へ）: y ↦ N、$ ↦ Y。 -/
def gcy1 : Sy → Sy
  | .s1 => .s4
  | .s6 => .s3
  | x => x
/-- M（右へ）: Y ↦ $、N ↦ y、y ↦ ∗。 -/
def gM : Sy → Sy
  | .s3 => .s6
  | .s4 => .s1
  | .s1 => .s5
  | x => x
/-- case_y_n（左へ）: y ↦ N、Y ↦ y、$ ↦ ∗。 -/
def gcyn : Sy → Sy
  | .s1 => .s4
  | .s3 => .s1
  | .s6 => .s5
  | x => x
/-- 境目での Lo(m) の形: ∗ ↦ Y。 -/
def gSY : Sy → Sy
  | .s5 => .s3
  | x => x
/-- コピーの間の Lo(m) の形: ∗ ↦ y、y ↦ N。 -/
def gL : Sy → Sy
  | .s5 => .s1
  | .s1 => .s4
  | x => x
/-- copy_y_1（右へ）: N ↦ $、n ↦ ∗、y ↦ N、∗ ↦ n。 -/
def gc1 : Sy → Sy
  | .s4 => .s6
  | .s2 => .s5
  | .s1 => .s4
  | .s5 => .s2
  | x => x
/-- copy_y_3（左へ）: $ ↦ N、∗ ↦ n、N ↦ y、n ↦ ∗（`gc1` の逆）。 -/
def hc1 : Sy → Sy
  | .s6 => .s4
  | .s5 => .s2
  | .s4 => .s1
  | .s2 => .s5
  | x => x
/-- copy_n_1（右へ）: ∗ ↦ $、N ↦ b、n ↦ N、Y ↦ ∗。 -/
def gn1 : Sy → Sy
  | .s5 => .s6
  | .s4 => .s0
  | .s2 => .s4
  | .s3 => .s5
  | x => x
/-- copy_n_3（左へ）: $ ↦ ∗、∗ ↦ Y、N ↦ n、b ↦ N（`gn1` の逆）。 -/
def hn1 : Sy → Sy
  | .s6 => .s5
  | .s5 => .s3
  | .s4 => .s2
  | .s0 => .s4
  | x => x
/-- copy_end（右へ）: N ↦ y、y ↦ Y、∗ ↦ $。 -/
def gce : Sy → Sy
  | .s4 => .s1
  | .s1 => .s3
  | .s5 => .s6
  | x => x

/-- copy_c_1 の書き換えと copy_c_3 の書き換え。 -/
def gc : Ch → Sy → Sy
  | .Y => gc1
  | .N => gn1
def hc : Ch → Sy → Sy
  | .Y => hc1
  | .N => hn1

/-- copy_c_2 の座: copy_y_2 → M（q2）、copy_n_2 → copy_end（q11）。 -/
def c2' : Ch → St
  | .Y => .q2
  | .N => .q11
/-- copy_start が規則の 1 文字を消した印: y は b、n は Y。 -/
def er : Ch → Sy
  | .Y => .s0
  | .N => .s3
/-- copy_c_3 が印に書き戻す記号: y の代わりに N、n は n。 -/
def loE : Ch → Sy
  | .Y => .s4
  | .N => .s2
/-- 処理中の先頭の記号の印: Y は Y、N は $。 -/
def mk : Ch → Sy
  | .Y => .s3
  | .N => .s6

/-- {y, n, ∗, N, Y}（copy_*_1・copy_*_3 が通過する）。 -/
def YNSNY (x : Sy) : Prop := x = nm13.y ∨ x = nm13.n ∨ x = nm13.st ∨ x = nm13.N ∨ x = nm13.Y
/-- {y, n, Y, $}（case_y_n が通過する）。 -/
def YNYD (x : Sy) : Prop := x = nm13.y ∨ x = nm13.n ∨ x = nm13.Y ∨ x = nm13.dl
/-- {y, n, ∗, N}（copy_end が通過する）。 -/
def YNSN (x : Sy) : Prop := x = nm13.y ∨ x = nm13.n ∨ x = nm13.st ∨ x = nm13.N
/-- {y, n, N}（M が cycle_end の役で通過する）。 -/
def YNN (x : Sy) : Prop := x = nm13.y ∨ x = nm13.n ∨ x = nm13.N
/-- {Y, N, n}（M が case_y_2 の役で通過する）。 -/
def YNn (x : Sy) : Prop := x = nm13.Y ∨ x = nm13.N ∨ x = nm13.n

theorem lo_YNSNY : ∀ c, YNSNY (lo nm13 c) := by intro c; cases c <;> simp [YNSNY, U13_7.lo, nm13]
theorem loE_YNSNY : ∀ c, YNSNY (loE c) := by intro c; cases c <;> simp [YNSNY, loE, nm13]
theorem loN_YNSNY : ∀ c, YNSNY (loN c) := by intro c; cases c <;> simp [YNSNY, loN, U11_7.gYN, U13_7.lo, nm13]
theorem loN_YNSN : ∀ c, YNSN (loN c) := by intro c; cases c <;> simp [YNSN, loN, U11_7.gYN, U13_7.lo, nm13]
theorem loN_YNn : ∀ c, YNn (loN c) := by intro c; cases c <;> simp [YNn, loN, U11_7.gYN, U13_7.lo, nm13]
theorem loE_YNSN : ∀ c, YNSN (loE c) := by intro c; cases c <;> simp [YNSN, loE, nm13]
theorem loE_YNN : ∀ c, YNN (loE c) := by intro c; cases c <;> simp [YNN, loE, nm13]
theorem gSY_YNYD : ∀ x, YNS nm13 x → YNYD (gSY x) := by
  rintro x (rfl | rfl | rfl) <;> simp [YNYD, gSY, nm13]
theorem gL_YNSNY : ∀ x, YNS nm13 x → YNSNY (gL x) := by
  rintro x (rfl | rfl | rfl) <;> simp [YNSNY, gL, nm13]
theorem gL_YNSN : ∀ x, YNS nm13 x → YNSN (gL x) := by
  rintro x (rfl | rfl | rfl) <;> simp [YNSN, gL, nm13]
theorem gL_YNN : ∀ x, YNS nm13 x → YNN (gL x) := by
  rintro x (rfl | rfl | rfl) <;> simp [YNN, gL, nm13]

theorem fa_map_of {P R : Sy → Prop} {f : Sy → Sy} (hf : ∀ x, P x → R (f x)) {L : List Sy}
    (hL : ∀ x ∈ L, P x) : ∀ y ∈ L.map f, R y := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
  exact hf x (hL x hx)

/-- 写像の合成（`List.map_map` のあとに使う）。 -/
theorem gcy1_lo : gcy1 ∘ lo nm13 = loN := by funext c; cases c <;> rfl
theorem gcyn_lo : gcyn ∘ lo nm13 = loN := by funext c; cases c <;> rfl
theorem gM_loN : gM ∘ loN = lo nm13 := by funext c; cases c <;> rfl
theorem gce_loN : gce ∘ loN = lo nm13 := by funext c; cases c <;> rfl
theorem gce_loE : gce ∘ loE = lo nm13 := by funext c; cases c <;> rfl
theorem gM_loE : gM ∘ loE = lo nm13 := by funext c; cases c <;> rfl
theorem gSY_lo : gSY ∘ lo nm13 = lo nm13 := by funext c; cases c <;> rfl
theorem gcy1_dl : gcy1 nm13.dl = nm13.Y := rfl
theorem gcyn_dl : gcyn nm13.dl = nm13.st := rfl
theorem gcyn_Y : gcyn nm13.Y = nm13.y := rfl
theorem gM_Y : gM nm13.Y = nm13.dl := rfl
theorem gM_y : gM nm13.y = nm13.st := rfl
theorem gce_y : gce nm13.y = nm13.Y := rfl
theorem gce_st : gce nm13.st = nm13.dl := rfl
theorem gSY_st : gSY nm13.st = nm13.Y := rfl
theorem gL_st : gL nm13.st = nm13.y := rfl

theorem map_gcyn_gSY {L : List Sy} (hL : ∀ x ∈ L, YNS nm13 x) : L.map (gcyn ∘ gSY) = L.map gL :=
  List.map_congr_left fun x hx => by rcases hL x hx with rfl | rfl | rfl <;> rfl
theorem map_gce_gL {L : List Sy} (hL : ∀ x ∈ L, YNS nm13 x) : L.map (gce ∘ gL) = L.map gSY :=
  List.map_congr_left fun x hx => by rcases hL x hx with rfl | rfl | rfl <;> rfl
theorem map_gM_gL {L : List Sy} (hL : ∀ x ∈ L, YNS nm13 x) : L.map (gM ∘ gL) = L :=
  List.map_congr_left (fun x hx => by rcases hL x hx with rfl | rfl | rfl <;> rfl) |>.trans (List.map_id L)

theorem hcgc (c : Ch) : ∀ x, YNSNY x → hc c (gc c x) = x := by
  cases c <;> rintro x (rfl | rfl | rfl | rfl | rfl) <;> rfl
theorem hc_N (c : Ch) : hc c .s4 = lo nm13 c := by cases c <;> rfl

theorem map_hc_gc (c : Ch) {R : List Sy} (hR : ∀ x ∈ R, YNSNY x) :
    (R.map (gc c)).map (hc c) = R := by
  induction R with
  | nil => rfl
  | cons x R ih =>
    simp only [List.map_cons, hcgc c x (hR x (List.mem_cons_self ..)),
      ih (fun y hy => hR y (List.mem_cons_of_mem _ hy))]

/-! ## 3. 規則が表にあること -/

theorem pcy1 : ∀ x, YND nm13 x → (⟨.q1, x, gcy1 x, .L, .go .q1⟩ : Rule St Ps Sy) ∈ T10 := by
  rintro x (rfl | rfl | rfl) <;> decide
theorem pM1 : ∀ x, YNn x → (⟨.q2, x, gM x, .R, .go .q2⟩ : Rule St Ps Sy) ∈ T10 := by
  rintro x (rfl | rfl | rfl) <;> decide
theorem pM2 : ∀ x, YNN x → (⟨.q2, x, gM x, .R, .go .q2⟩ : Rule St Ps Sy) ∈ T10 := by
  rintro x (rfl | rfl | rfl) <;> decide
theorem pcyn : ∀ x, YNYD x → (⟨.q3, x, gcyn x, .L, .go .q3⟩ : Rule St Ps Sy) ∈ T10 := by
  rintro x (rfl | rfl | rfl | rfl) <;> decide
theorem pce : ∀ x, YNSN x → (⟨.q11, x, gce x, .R, .go .q11⟩ : Rule St Ps Sy) ∈ T10 := by
  rintro x (rfl | rfl | rfl | rfl) <;> decide

theorem rcs (c : Ch) : (⟨.q4, lo nm13 c, er c, .R, .go (c1 nm13 c)⟩ : Rule St Ps Sy) ∈ T10 := by
  cases c <;> decide
theorem rc1b (c : Ch) : (⟨c1 nm13 c, .s0, .s4, .R, .go (c2' c)⟩ : Rule St Ps Sy) ∈ T10 := by
  cases c <;> decide
theorem rc1N (c : Ch) : (⟨c1 nm13 c, .s6, .s6, .L, .go (c3 nm13 c)⟩ : Rule St Ps Sy) ∈ T10 := by
  cases c <;> decide
theorem rc2 (c : Ch) : (⟨c2' c, .s0, .s0, .L, .go (c3 nm13 c)⟩ : Rule St Ps Sy) ∈ T10 := by
  cases c <;> decide
theorem rc3 (c : Ch) : (⟨c3 nm13 c, er c, loE c, .L, .go .q4⟩ : Rule St Ps Sy) ∈ T10 := by
  cases c <;> decide
theorem pc1 (c : Ch) : ∀ x, YNSNY x →
    (⟨c1 nm13 c, x, gc c x, .R, .go (c1 nm13 c)⟩ : Rule St Ps Sy) ∈ T10 := by
  cases c <;> rintro x (rfl | rfl | rfl | rfl | rfl) <;> decide
theorem pc3 (c : Ch) : ∀ x, YNSNY x →
    (⟨c3 nm13 c, gc c x, hc c (gc c x), .L, .go (c3 nm13 c)⟩ : Rule St Ps Sy) ∈ T10 := by
  cases c <;> rintro x (rfl | rfl | rfl | rfl | rfl) <;> decide
theorem rce (c : Ch) : (⟨.q11, mk c, lo nm13 c, .R, .go .q0⟩ : Rule St Ps Sy) ∈ T10 := by
  cases c <;> decide

/-- copy_c_3 が通る列 (gc c)(R)ᴿ の各記号について、hc c で書き戻す規則がある。 -/
theorem pc3_list (c : Ch) {R : List Sy} (hR : ∀ x ∈ R, YNSNY x) :
    ∀ y ∈ (R.map (gc c)).reverse, (⟨c3 nm13 c, y, hc c y, .L, .go (c3 nm13 c)⟩ : Rule St Ps Sy) ∈ T10 := by
  intro y hy
  rw [List.mem_reverse, List.mem_map] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  exact pc3 c x (hR x hx)

theorem pc3_N (c : Ch) : (⟨c3 nm13 c, .s4, hc c .s4, .L, .go (c3 nm13 c)⟩ : Rule St Ps Sy) ∈ T10 := by
  cases c <;> decide

/-! ## 4. コピー -/

/-- 先頭が Y のとき（書き足す）。親の copy_oneY と同じ道筋。copy_start が印 `er c` を置き、copy_c_1 が
    `gc c` で書き換えつつ右端へ行って N を書き、copy_c_2 が折り返し、copy_c_3 が `hc c` で戻しつつ印まで戻って
    `loE c` を書く。 -/
theorem copy_oneY (c : Ch) {LL : List Sy} (hLL : LL ≠ []) {R : List Sy}
    (hR : ∀ x ∈ R, YNSNY x) :
    Reach T10 (zc nm13.b (.go .q4) LL (lo nm13 c) R)
      (zl nm13.b (.go .q4) LL (loE c :: R ++ [lo nm13 c])) := by
  rw [← zc_trail _ _ _ R, ← zl_trail]
  refine (runRg (rcs c) (gc c) (fun x hx => pc1 c x (hR x hx)) LL nm13.b []).trans ?_
  rw [zc_nil]
  refine (Reach.step (stepR (rc1b c) _ nm13.b [])).trans ?_
  refine (Reach.step (stepL (rc2 c) .s4 _ [])).trans ?_
  have hX : ∀ y ∈ .s4 :: (R.map (gc c)).reverse,
      (⟨c3 nm13 c, y, hc c y, .L, .go (c3 nm13 c)⟩ : Rule St Ps Sy) ∈ T10 := by
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact pc3_N c
    · exact pc3_list c hR y hy
  refine (sweepLg (hc c) hX (er c) LL [nm13.b]).trans ?_
  refine (Reach.step (stepL' (rc3 c) hLL _)).trans ?_
  apply Reach.of_eq
  have hm := map_hc_gc c hR
  simp only [List.map_cons, List.map_reverse, hm, hc_N, List.reverse_cons, List.reverse_reverse]
  simp

/-- 先頭が N のとき（書き足さない）: copy_c_1 が印の $ に当たって引き返す。 -/
theorem copy_oneN (c : Ch) {LL : List Sy} (hLL : LL ≠ []) {R₁ : List Sy}
    (hR : ∀ x ∈ R₁, YNSNY x) (R₂ : List Sy) :
    Reach T10 (zc nm13.b (.go .q4) LL (lo nm13 c) (R₁ ++ nm13.dl :: R₂))
      (zl nm13.b (.go .q4) LL (loE c :: R₁ ++ nm13.dl :: R₂)) := by
  refine (runRg (rcs c) (gc c) (fun x hx => pc1 c x (hR x hx)) LL nm13.dl R₂).trans ?_
  refine (Reach.step (stepL' (rc1N c) (L := (R₁.map (gc c)).reverse ++ er c :: LL) (by simp) R₂)).trans ?_
  refine (sweepLg (hc c) (pc3_list c hR) (er c) LL (nm13.dl :: R₂)).trans ?_
  refine (Reach.step (stepL' (rc3 c) hLL _)).trans ?_
  apply Reach.of_eq
  have hm := map_hc_gc c hR
  simp only [List.map_reverse, hm, List.reverse_reverse]
  simp

theorem copy_loopY (Z : List Sy) (hZ : Z ≠ []) :
    ∀ (Q P : List Ch) (S : List Sy), (∀ x ∈ S, YNSNY x) →
    Reach T10 (zl nm13.b (.go .q4) (Q.map (lo nm13) ++ Z) (P.reverse.map loE ++ S))
      (zl nm13.b (.go .q4) Z ((P ++ Q).reverse.map loE ++ S ++ Q.map (lo nm13))) := by
  intro Q
  induction Q with
  | nil => intro P S _; exact Reach.of_eq (by simp)
  | cons c Q ih =>
    intro P S hS
    have hR : ∀ x ∈ P.reverse.map loE ++ S, YNSNY x := fa_app (fa_map loE_YNSNY _) hS
    have h1 := copy_oneY c (LL := Q.map (lo nm13) ++ Z) (by simp [hZ]) hR
    have h2 := ih (P ++ [c]) (S ++ [lo nm13 c]) (fa_app hS (fa_cons (lo_YNSNY c) fa_nil))
    refine h1.trans (Eq.mpr ?_ h2)
    simp

theorem copy_loopN (Z : List Sy) (hZ : Z ≠ []) (S₂ : List Sy) :
    ∀ (Q P : List Ch) (S₁ : List Sy), (∀ x ∈ S₁, YNSNY x) →
    Reach T10 (zl nm13.b (.go .q4) (Q.map (lo nm13) ++ Z) (P.reverse.map loE ++ S₁ ++ nm13.dl :: S₂))
      (zl nm13.b (.go .q4) Z ((P ++ Q).reverse.map loE ++ S₁ ++ nm13.dl :: S₂)) := by
  intro Q
  induction Q with
  | nil => intro P S₁ _; exact Reach.of_eq (by simp)
  | cons c Q ih =>
    intro P S₁ hS
    have hR : ∀ x ∈ P.reverse.map loE ++ S₁, YNSNY x := fa_app (fa_map loE_YNSNY _) hS
    have h1 := copy_oneN c (LL := Q.map (lo nm13) ++ Z) (by simp [hZ]) hR S₂
    have h1' : Reach T10
        (zl nm13.b (.go .q4) ((c :: Q).map (lo nm13) ++ Z) (P.reverse.map loE ++ S₁ ++ nm13.dl :: S₂))
        (zl nm13.b (.go .q4) (Q.map (lo nm13) ++ Z)
          ((P ++ [c]).reverse.map loE ++ S₁ ++ nm13.dl :: S₂)) := by
      refine Eq.mpr ?_ h1; simp [zl]
    have h2 := ih (P ++ [c]) S₁ hS
    refine h1'.trans (Eq.mpr ?_ h2)
    simp

/-! ## 5. 境目の配置と 1 マクロステップ -/

/-- 境目（状態 begin）での規則領域: 親の RA(m) の Lo(m) の区切り ∗ を Y にしたもの。 -/
def RA10 (C : CTSH) (m : Nat) : List Sy :=
  Hi nm13 C m ++ (prod C m).reverse.map (lo nm13) ++ nm13.b :: (Lo nm13 C m).map gSY

theorem RA10_length (C : CTSH) (m : Nat) : (RA10 C m).length = (RA nm13 C m).length := by
  simp [RA10, U13_7.RA, Sim.RA]

/-- 境目のテープ: b · RA10(m) · $ · ϕ₁(rm) · ϕ₁(v)。 -/
def tapeList10 (C : CTSH) (m : Nat) (rm v : List Ch) : List Sy :=
  nm13.b :: RA10 C m ++ nm13.dl :: rm.map (lo nm13) ++ v.map (lo nm13)

/-- CTSH の ID (v, m) と消去済みの記号列 rm を表す配置。状態・ヘッドの位置は親と同じ。 -/
def rep10 (C : CTSH) (m : Nat) (rm v : List Ch) : Cfg St Ps Sy :=
  { st := .go nm13.begin, pos := (RA nm13 C m).length + 2 + rm.length,
    tape := tp nm13.b (tapeList10 C m rm v) }

theorem rep10_eq (C : CTSH) (m : Nat) (rm v : List Ch) :
    rep10 C m rm v =
      zr nm13.b (.go nm13.begin) (nm13.b :: RA10 C m ++ nm13.dl :: rm.map (lo nm13)).reverse
        (v.map (lo nm13)) := by
  rw [zr_eq]; simp only [rep10, tapeList10]; congr 1 <;> simp [RA10_length]; omega

/-- case_y_1 が通る列の各記号について規則がある。 -/
theorem pcy1_list {X : List Sy} (hX : ∀ x ∈ X, YND nm13 x) :
    ∀ x ∈ X, (⟨.q1, x, gcy1 x, .L, .go .q1⟩ : Rule St Ps Sy) ∈ T10 := fun x hx => pcy1 x (hX x hx)

/-- M（case_y_2 の役）が通る列 Y · loN(rm) の各記号について規則がある。 -/
theorem pM1_list (rm : List Ch) :
    ∀ x ∈ nm13.Y :: rm.map loN, (⟨.q2, x, gM x, .R, .go .q2⟩ : Rule St Ps Sy) ∈ T10 :=
  fun x hx => pM1 x ((fa_cons (by simp [YNn]) (fa_map loN_YNn _)) x hx)

/-- 先頭が Y、相 m ≥ 1: begin が y を $ に、case_y_1 が y ↦ N・$ ↦ Y と書き換えつつ Lo(m) の末尾の Y まで、
    M が Y ↦ $・N ↦ y と戻しつつ印 $ まで（印を Y に）、case_y_n が y ↦ N・Y ↦ y・$ ↦ ∗ と書き換えつつ
    相マーカー b まで（b を y に）→ copy_start。 -/
theorem frontY (C : CTSH) (m : Nat) (hm : m ≠ 0) (rm v : List Ch) :
    Reach1 T10 (rep10 C m rm (.Y :: v))
      (zl nm13.b (.go .q4) ((prod C m).map (lo nm13) ++ (nm13.b :: Hi nm13 C m).reverse)
        (nm13.y :: (Lo nm13 C m).map gL ++ nm13.st :: rm.map loN ++ nm13.Y :: v.map (lo nm13))) := by
  have hLc : ∀ x ∈ LoCore nm13 C m, YNS nm13 x := LoCore_mem lo_YNS (by simp [YNS]) C m
  rw [rep10_eq]
  simp only [List.map_cons, zr, U13_7.lo]
  rw [show (nm13.b :: RA10 C m ++ nm13.dl :: rm.map (lo nm13)).reverse =
      ((rm.map (lo nm13)).reverse ++ [nm13.dl]) ++ nm13.Y :: (((LoCore nm13 C m).map gSY).reverse ++ nm13.b ::
        ((prod C m).map (lo nm13) ++ (nm13.b :: Hi nm13 C m).reverse)) by
    simp [RA10, Sim.Lo_ne C m hm, gSY_st]]
  refine (runL1g (p := St.q0) (q := St.q1) (h := nm13.y) (t := nm13.dl) (by decide) gcy1
    (pcy1_list (fa_app (fa_rev (fa_map lo_YND _)) (fa_cons (by simp [YND]) fa_nil)))
    nm13.Y _ _).trans ?_
  rw [show (((rm.map (lo nm13)).reverse ++ [nm13.dl]).map gcy1).reverse = nm13.Y :: rm.map loN by
    simp [List.map_reverse, List.map_map, gcy1_lo, gcy1_dl]]
  refine (runRg (p := St.q1) (q := St.q2) (h := nm13.Y) (t := nm13.Y) (by decide) gM
    (X := nm13.Y :: rm.map loN) (pM1_list rm) _ nm13.dl _).trans ?_
  rw [show ((nm13.Y :: rm.map loN).map gM) = nm13.dl :: rm.map (lo nm13) by
    simp [List.map_map, gM_loN, gM_Y]]
  rw [show (nm13.dl :: rm.map (lo nm13)).reverse ++ nm13.Y :: (((LoCore nm13 C m).map gSY).reverse ++ nm13.b ::
        ((prod C m).map (lo nm13) ++ (nm13.b :: Hi nm13 C m).reverse)) =
      ((rm.map (lo nm13)).reverse ++ nm13.dl :: nm13.Y :: ((LoCore nm13 C m).map gSY).reverse) ++ nm13.b ::
        ((prod C m).map (lo nm13) ++ (nm13.b :: Hi nm13 C m).reverse) by simp]
  refine (runLg (p := St.q2) (q := St.q3) (h := nm13.dl) (t := nm13.Y) (by decide) gcyn
    (fun x hx => pcyn x ((fa_app (fa_rev (fa_map lo_YND' _)) (fa_cons (by simp [YNYD])
      (fa_cons (by simp [YNYD]) (fa_rev (fa_map_of gSY_YNYD hLc)))))
      x hx))
    nm13.b _ _).trans ?_
  refine (Reach.step (stepL' (p := St.q3) (h := nm13.b) (t := nm13.y) (q := .go St.q4) (by decide)
    (L := (prod C m).map (lo nm13) ++ (nm13.b :: Hi nm13 C m).reverse) (by simp) _)).trans ?_
  apply Reach.of_eq
  simp only [List.map_append, List.map_cons, List.map_reverse, List.map_map, gcyn_lo, gcyn_dl, gcyn_Y,
    map_gcyn_gSY hLc, List.reverse_append, List.reverse_cons,
    List.reverse_reverse, Sim.Lo_ne C m hm]
  simp [gL_st]
where
  lo_YND' : ∀ c, YNYD (lo nm13 c) := by intro c; cases c <;> simp [YNYD, U13_7.lo, nm13]

/-- 先頭が N（任意の相）: begin が n を $ に、case_y_n が書き換えつつ相マーカー b まで → copy_start。 -/
theorem frontN (C : CTSH) (m : Nat) (rm v : List Ch) :
    Reach1 T10 (rep10 C m rm (.N :: v))
      (zl nm13.b (.go .q4) ((prod C m).map (lo nm13) ++ (nm13.b :: Hi nm13 C m).reverse)
        (nm13.y :: (Lo nm13 C m).map gL ++ nm13.st :: rm.map loN ++ nm13.dl :: v.map (lo nm13))) := by
  rw [rep10_eq]
  simp only [List.map_cons, zr, U13_7.lo]
  rw [show (nm13.b :: RA10 C m ++ nm13.dl :: rm.map (lo nm13)).reverse =
      ((rm.map (lo nm13)).reverse ++ nm13.dl :: ((Lo nm13 C m).map gSY).reverse) ++ nm13.b ::
        ((prod C m).map (lo nm13) ++ (nm13.b :: Hi nm13 C m).reverse) by simp [RA10]]
  have hLoS : ∀ x ∈ Lo nm13 C m, YNS nm13 x := Lo_mem lo_YNS (by simp [YNS]) C m
  refine (runL1g (p := St.q0) (q := St.q3) (h := nm13.n) (t := nm13.dl) (by decide) gcyn
    (fun x hx => pcyn x ((fa_app (fa_rev (fa_map frontY.lo_YND' _)) (fa_cons (by simp [YNYD])
      (fa_rev (fa_map_of gSY_YNYD hLoS)))) x hx))
    nm13.b _ _).trans ?_
  refine (Reach.step (stepL' (p := St.q3) (h := nm13.b) (t := nm13.y) (q := .go St.q4) (by decide)
    (L := (prod C m).map (lo nm13) ++ (nm13.b :: Hi nm13 C m).reverse) (by simp) _)).trans ?_
  apply Reach.of_eq
  simp only [List.map_append, List.map_cons, List.map_reverse, List.map_map, gcyn_lo, gcyn_dl,
    map_gcyn_gSY hLoS, List.reverse_append, List.reverse_cons, List.reverse_reverse]
  simp

/-- copy_end が通る列の各記号について規則がある。 -/
theorem pce_list {X : List Sy} (hX : ∀ x ∈ X, YNSN x) :
    ∀ x ∈ X, (⟨.q11, x, gce x, .R, .go .q11⟩ : Rule St Ps Sy) ∈ T10 := fun x hx => pce x (hX x hx)

/-- 相の終わり: copy_start が次の区切り ∗ を b（新しい相マーカー）にして copy_end が `gce` で境目の形に
    戻しつつ印まで行き、印を小文字に戻して begin。m = k−1 なら左端の b で M（cycle_end の役）に入り、
    `gM` で規則を小文字に戻しつつ $ の手前の ∗ で折り返して copy_start、その ∗ を相マーカーに。 -/
theorem finish (C : CTSH) (m : Nat) (hk : m ≤ C.length) (c : Ch) (rm v : List Ch) :
    Reach T10 (zl nm13.b (.go .q4) (nm13.b :: Hi nm13 C m).reverse
        ((prod C m).reverse.map loE ++ nm13.y :: (Lo nm13 C m).map gL ++ nm13.st :: rm.map loN ++
          mk c :: v.map (lo nm13)))
      (rep10 C ((m + 1) % C.k) (rm ++ [c]) v) := by
  have hLoS : ∀ x ∈ Lo nm13 C m, YNS nm13 x := Lo_mem lo_YNS (by simp [YNS]) C m
  rcases Nat.lt_or_ge m C.length with h | h
  · rw [Nat.mod_eq_of_lt (by simp [CTSH.k]; omega), rep10_eq, U13_7.Hi, Sim.Hi_step C m h]
    rw [show (nm13.b :: (Sim.Hi (lo nm13) nm13.st C (m + 1) ++ (prod C (m + 1)).reverse.map (lo nm13) ++
          [nm13.st])).reverse =
        nm13.st :: (nm13.b :: Sim.Hi (lo nm13) nm13.st C (m + 1) ++ (prod C (m + 1)).reverse.map (lo nm13)).reverse
        by simp]
    simp only [zl]
    rw [show (prod C m).reverse.map loE ++ nm13.y :: (Lo nm13 C m).map gL ++ nm13.st :: rm.map loN ++
          mk c :: v.map (lo nm13) =
        ((prod C m).reverse.map loE ++ nm13.y :: (Lo nm13 C m).map gL ++ nm13.st :: rm.map loN) ++
          mk c :: v.map (lo nm13) by simp]
    refine (runRg (p := St.q4) (q := St.q11) (h := nm13.st) (t := nm13.b) (by decide) gce
      (pce_list (fa_app (fa_app (fa_map loE_YNSN _) (fa_cons (by simp [YNSN])
        (fa_map_of gL_YNSN hLoS))) (fa_cons (by simp [YNSN]) (fa_map loN_YNSN _))))
      _ _ _).trans ?_
    refine (Reach.step (stepR' (rce c) _ _)).trans ?_
    apply Reach.of_eq
    congr 1
    simp only [List.map_append, List.map_cons, List.map_map, gce_loE, gce_loN, gce_y, gce_st,
      map_gce_gL hLoS]
    simp [RA10, Sim.Lo_step (lo := lo nm13) (st := nm13.st) C m hk, List.map_map, gSY_lo, gSY_st]
  · have hmk : m = C.length := by omega
    subst hmk
    rw [show (C.length + 1) % C.k = 0 by simp [CTSH.k], rep10_eq, U13_7.Hi, Sim.Hi_len]
    simp only [zl, List.reverse_cons, List.reverse_nil, List.nil_append]
    have hLo := Sim.Lo_step (lo := lo nm13) (st := nm13.st) C C.length (Nat.le_refl _)
    rw [show (prod C C.length).reverse.map loE ++ nm13.y :: (Lo nm13 C C.length).map gL ++
          nm13.st :: rm.map loN ++ mk c :: v.map (lo nm13) =
        ((prod C C.length).reverse.map loE ++ nm13.y :: (Lo nm13 C C.length).map gL) ++
          nm13.st :: (rm.map loN ++ mk c :: v.map (lo nm13)) by simp]
    refine (runRg (p := St.q4) (q := St.q2) (h := nm13.b) (t := nm13.b) (by decide) gM
      (fun x hx => pM2 x ((fa_app (fa_map loE_YNN _) (fa_cons (by simp [YNN]) (fa_map_of gL_YNN hLoS)))
        x hx)) [] _ _).trans ?_
    have hX : ((prod C C.length).reverse.map loE ++ nm13.y :: (Lo nm13 C C.length).map gL).map gM =
        Sim.LoCore (lo nm13) nm13.st C (C.length + 1) ++ [nm13.st] := by
      simp only [List.map_append, List.map_cons, List.map_map, gM_loE, gM_y, map_gM_gL hLoS]
      rw [← Sim.Lo_ne C (C.length + 1) (by omega), hLo]
    rw [hX]
    rw [show (Sim.LoCore (lo nm13) nm13.st C (C.length + 1) ++ [nm13.st]).reverse ++ [nm13.b] =
        nm13.st :: ((Sim.LoCore (lo nm13) nm13.st C (C.length + 1)).reverse ++ [nm13.b]) by simp]
    refine (Reach.step (stepL (p := St.q2) (h := nm13.st) (t := nm13.st) (q := .go St.q4) (by decide)
      _ _ _)).trans ?_
    rw [show nm13.st :: (rm.map loN ++ mk c :: v.map (lo nm13)) =
        (nm13.st :: rm.map loN) ++ mk c :: v.map (lo nm13) by simp]
    refine (runRg (p := St.q4) (q := St.q11) (h := nm13.st) (t := nm13.b) (by decide) gce
      (pce_list (fa_cons (by simp [YNSN]) (fa_map loN_YNSN _))) _ _ _).trans ?_
    refine (Reach.step (stepR' (rce c) _ _)).trans ?_
    apply Reach.of_eq
    congr 1
    simp only [List.map_cons, List.map_map, gce_loN, gce_st]
    simp [RA10, Sim.LoCore_full, U13_7.lo, prod, Sim.Lo]

theorem macroY (C : CTSH) {m : Nat} (h0 : m ≠ 0) (hk : m < C.k) (rm v : List Ch) :
    Reach1 T10 (rep10 C m rm (.Y :: v)) (rep10 C ((m + 1) % C.k) (rm ++ [.Y]) (v ++ prod C m)) := by
  have hmk : m ≤ C.length := by simp [CTSH.k] at hk; omega
  refine (frontY C m h0 rm v).trans ?_
  have hS : ∀ x ∈ nm13.y :: (Lo nm13 C m).map gL ++ nm13.st :: rm.map loN ++ nm13.Y :: v.map (lo nm13),
      YNSNY x :=
    fa_app (fa_app (fa_cons (by simp [YNSNY]) (fa_map_of gL_YNSNY (Lo_mem lo_YNS (by simp [YNS]) C m)))
      (fa_cons (by simp [YNSNY]) (fa_map loN_YNSNY _)))
      (fa_cons (by simp [YNSNY]) (fa_map lo_YNSNY _))
  have hL := copy_loopY _ (by simp : (nm13.b :: Hi nm13 C m).reverse ≠ []) (prod C m) [] _ hS
  refine hL.trans ?_
  have hf := finish C m hmk .Y rm (v ++ prod C m)
  refine Eq.mpr ?_ hf
  simp [mk, nm13]

theorem macroN (C : CTSH) {m : Nat} (hk : m < C.k) (rm v : List Ch) :
    Reach1 T10 (rep10 C m rm (.N :: v)) (rep10 C ((m + 1) % C.k) (rm ++ [.N]) v) := by
  have hmk : m ≤ C.length := by simp [CTSH.k] at hk; omega
  refine (frontN C m rm v).trans ?_
  have hS : ∀ x ∈ nm13.y :: (Lo nm13 C m).map gL ++ nm13.st :: rm.map loN, YNSNY x :=
    fa_app (fa_cons (by simp [YNSNY]) (fa_map_of gL_YNSNY (Lo_mem lo_YNS (by simp [YNS]) C m)))
      (fa_cons (by simp [YNSNY]) (fa_map loN_YNSNY _))
  have hL := copy_loopN _ (by simp : (nm13.b :: Hi nm13 C m).reverse ≠ []) (v.map (lo nm13))
    (prod C m) [] _ hS
  have hL' : Reach T10
      (zl nm13.b (.go .q4) ((prod C m).map (lo nm13) ++ (nm13.b :: Hi nm13 C m).reverse)
        (nm13.y :: (Lo nm13 C m).map gL ++ nm13.st :: rm.map loN ++ nm13.dl :: v.map (lo nm13)))
      (zl nm13.b (.go .q4) (nm13.b :: Hi nm13 C m).reverse
        ((prod C m).reverse.map loE ++ nm13.y :: (Lo nm13 C m).map gL ++ nm13.st :: rm.map loN ++
          nm13.dl :: v.map (lo nm13))) := by
    refine Eq.mpr ?_ hL; simp
  refine hL'.trans ?_
  have hf := finish C m hmk .N rm v
  refine Eq.mpr ?_ hf
  simp [mk, nm13]

/-! ## 6. 停止 -/

/-- 停止配置のテープ（リスト）。(λ, m) は境目のまま。(Y v, 0) は begin が y を $ に、case_y_1 が
    y ↦ N・$ ↦ Y と書き換えつつ相マーカー b まで行って halt: `b · RA(0) · Y · loN(rm) · $ · ϕ₁(v)`。 -/
def finList10 (C : CTSH) (vf : List Ch) (mf : Nat) (rm : List Ch) : List Sy :=
  match vf with
  | [] => tapeList10 C mf rm []
  | _ :: v => nm13.b :: RA nm13 C 0 ++ nm13.Y :: rm.map loN ++ nm13.dl :: v.map (lo nm13)

/-- 停止配置。状態とヘッドの位置は親（`U13_7.finCfg`）と同じ。 -/
def finCfg10 (C : CTSH) (vf : List Ch) (mf : Nat) (rm : List Ch) : Cfg St Ps Sy :=
  match vf with
  | [] => { st := .halt nm13.null, pos := (RA nm13 C mf).length + 2 + rm.length,
            tape := tp nm13.b (finList10 C [] mf rm) }
  | c :: v => { st := .halt nm13.halt, pos := (RA nm13 C 0).length,
                tape := tp nm13.b (finList10 C (c :: v) 0 rm) }

theorem halt_null (C : CTSH) (m : Nat) (rm : List Ch) :
    Reach1 T10 (rep10 C m rm []) (finCfg10 C [] m rm) := by
  rw [rep10_eq]
  simp only [List.map_nil, zr]
  refine Reach1.of_step (stepZ (p := St.q0) (h := nm13.b) (t := nm13.b) (q := Tgt.halt nm13.null) (by decide)
    _ _) (Reach.of_eq ?_)
  simp only [zc, finCfg10, finList10, tapeList10]
  congr 1
  · simp [RA10_length]; omega
  · simpa using tp_trail (bk := nm13.b) (nm13.b :: (RA10 C m ++ nm13.dl :: List.map (lo nm13) rm))

theorem halt_Y (C : CTSH) (rm v : List Ch) :
    Reach1 T10 (rep10 C 0 rm (.Y :: v)) (finCfg10 C (.Y :: v) 0 rm) := by
  rw [rep10_eq]
  simp only [List.map_cons, zr, U13_7.lo]
  rw [show (nm13.b :: RA10 C 0 ++ nm13.dl :: rm.map (lo nm13)).reverse =
      ((rm.map (lo nm13)).reverse ++ [nm13.dl]) ++ nm13.b :: (nm13.b :: Hi nm13 C 0).reverse by
    simp [RA10, prod, Sim.Lo]]
  refine (runL1g (p := St.q0) (q := St.q1) (h := nm13.y) (t := nm13.dl) (by decide) gcy1
    (pcy1_list (fa_app (fa_rev (fa_map lo_YND _)) (fa_cons (by simp [YND]) fa_nil)))
    nm13.b _ _).trans ?_
  refine (Reach.step (stepZ (p := St.q1) (h := nm13.b) (t := nm13.b) (q := Tgt.halt nm13.halt) (by decide)
    _ _)).trans ?_
  apply Reach.of_eq
  simp only [zc, finCfg10, finList10]
  congr 1
  · simp [U13_7.RA, Sim.RA_zero]
  · simp [U13_7.RA, U13_7.Hi, Sim.RA_zero, List.map_reverse, List.map_map, gcy1_lo, gcy1_dl]

theorem finCfg10_halted (C : CTSH) (vf : List Ch) (mf : Nat) (rm : List Ch) :
    Halted T10 (finCfg10 C vf mf rm) := by
  intro c' ⟨r, _, hst, _⟩
  cases vf <;> simp [finCfg10] at hst

/-! ## 7. 主定理 -/

/-- 初期配置は親と同じ（Morita の (13,7) の符号化。相 0 では Lo(0) = λ なので RA10(0) = RA(0)）。 -/
def encC10 (C : CTSH) (w : List Ch) : Cfg St Ps Sy := rep10 C 0 [] w

theorem encC10_eq (C : CTSH) (w : List Ch) : encC10 C w = U13_7.encC nm13 C w := by
  simp [encC10, rep10, tapeList10, RA10, U13_7.encC, U13_7.rep, U13_7.tapeList, U13_7.RA, Sim.RA, Sim.Lo]

/-- **主定理（URTM(10,7) は任意の CTSH を模倣する）**。`urtm11_7_simulates_ctsh` と同じ 3 項で、
    表は `T10`、停止配置は `finCfg10`。 -/
theorem urtm10_7_simulates_ctsh (C : CTSH) (w : List Ch) :
    (∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) →
      ∃ N rm, n ≤ N ∧ HaltsIn T10 N (encC10 C w) (finCfg10 C vf mf rm)) ∧
    (∀ N e, HaltsIn T10 N (encC10 C w) e →
      ∃ n vf mf rm, CHaltsIn C n (w, 0) (vf, mf) ∧ e = finCfg10 C vf mf rm) ∧
    ((∀ n f, ¬ CHaltsIn C n (w, 0) f) ↔ (∀ N e, ¬ HaltsIn T10 N (encC10 C w) e)) :=
  simulates_of_steps C (rep10 C) (finCfg10 C) hD10 (macroY C) (macroN C) (halt_Y C)
    (halt_null C) (finCfg10_halted C) w

end URTM.CTSH.U10_7
