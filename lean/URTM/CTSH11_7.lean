/-
  **URTM(11,7)**（2026-11-01、層 1 へ）: Morita の URTM(13,7)（`URTM.Gen.K13_7.T`）に「タグで 2 状態を併合 →
  タグ付きの写しを他の記号と併合」を 2 回当てた表が、任意の CTSH を模倣すること。

  子の表 `T11 = T.map chg` は親の 59 本を 1 本ずつ写したもの。`mu` は状態の併合（copy_y_2 → case_y_2、
  copy_n_2 → copy_end）、`chgSym` は読む記号・書く記号を書き換える 8 本（生成器 `tools/gen_tagchain_lean.py` の出力）。
  記号は親と同じ 7 つ（b y n Y N ∗ $）で、タグはすべて N に吸収されている。表は書き写していない。

  子の動きは親と 1 歩ずつ同じで、違いは掃引の書き換えだけ:
  * case_y_1（左へ）は y を N に、case_y_2（右へ）は N を y に戻す（`gYN`・`gNY`）。
  * copy_c_1（右へ）は lo c を N に、copy_c_3（左へ）は N を lo c に戻す。書き足す記号も lo c でなく N（`gc`・`hc`）。
  CTSH の 1 歩の境目では子のテープは親と同じ（不変量は `U13_7.rep` のまま）。停止配置は、null は親と同じ、
  halt は case_y_1 の掃引の途中で止まるので、消去済みの文字列 ϕ₁(rm) の y が N のまま（`finCfg11`）。

  証明の組み立ては CTSH13_7.lean と同じ（`simulates_of_steps`）。書き換えのある掃引は CTSHSim の写像つきの
  補題（`runRg`・`runL1g`・`sweepLg`）で書く。規則が表にあることは `decide`。
-/
import URTM.CTSH13_7Main

namespace URTM.CTSH.U11_7

open URTM URTM.KState URTM.CTSH URTM.CTSH.Sim URTM.Gen.K13_7
open URTM.CTSH.U13_7 (Names rules lo up c1 c3 RA Hi Lo LoCore tapeList rep encC finCfg finList rep_eq
  YND YNS YNSD YNSDY lo_YND lo_YNS lo_YNSD lo_YNSDY nm13)

/-! ## 1. 子の表（生成器 tools/gen_tagchain_lean.py の出力） -/

/-- 状態の併合（親の状態 → 子の状態）: copy_y_2（q6）→ case_y_2（q2）、copy_n_2（q9）→ copy_end（q11）。 -/
def mu : St → St
  | .q6 => .q2
  | .q9 => .q11
  | q => q

def muT : Tgt St Ps → Tgt St Ps
  | .go q => .go (mu q)
  | .halt h => .halt h

/-- 書き換える規則（親の (状態, 読む記号) → 子の (読む記号, 書く記号)）。 -/
def chgSym (p : St) (s t : Sy) : Sy × Sy :=
  match p, s with
  | .q1, .s1 => (.s1, .s4)
  | .q2, .s1 => (.s4, .s1)
  | .q8, .s0 => (.s0, .s4)
  | .q8, .s2 => (.s2, .s4)
  | .q10, .s2 => (.s4, .s2)
  | .q5, .s0 => (.s0, .s4)
  | .q5, .s1 => (.s1, .s4)
  | .q7, .s1 => (.s4, .s1)
  | _, _ => (s, t)

def chg (r : Rule St Ps Sy) : Rule St Ps Sy :=
  ⟨mu r.p, (chgSym r.p r.s r.t).1, (chgSym r.p r.s r.t).2, r.d, muT r.q⟩

/-- **URTM(11,7) の表**（59 本）。 -/
def T11 : Machine St Ps Sy := T.map chg

theorem T11_length : T11.length = 59 := by decide
theorem hD11 : Deterministic T11 := by decide
theorem hR11 : Reversible T11 := by decide
/-- 状態 q6・q9 は子の表に現れない（状態は 11 個）。 -/
theorem q6_q9_unused : ∀ ρ ∈ T11, ρ.p ≠ .q6 ∧ ρ.p ≠ .q9 ∧ ρ.q ≠ .go .q6 ∧ ρ.q ≠ .go .q9 := by decide

/-! ## 2. 掃引の書き換え -/

/-- case_y_1・copy_y_1: y ↦ N。 -/
def gYN : Sy → Sy
  | .s1 => .s4
  | x => x
/-- case_y_2・copy_y_3: N ↦ y。 -/
def gNY : Sy → Sy
  | .s4 => .s1
  | x => x
/-- copy_n_1: n ↦ N。 -/
def gnN : Sy → Sy
  | .s2 => .s4
  | x => x
/-- copy_n_3: N ↦ n。 -/
def gNn : Sy → Sy
  | .s4 => .s2
  | x => x

/-- copy_c_1 の書き換え（lo c ↦ N）と copy_c_3 の書き換え（N ↦ lo c）。 -/
def gc : Ch → Sy → Sy
  | .Y => gYN
  | .N => gnN
def hc : Ch → Sy → Sy
  | .Y => gNY
  | .N => gNn

/-- copy_c_2 の状態（併合後）: copy_y_2 → case_y_2（q2）、copy_n_2 → copy_end（q11）。 -/
def c2' : Ch → St
  | .Y => .q2
  | .N => .q11

/-- case_y_1 の掃引のあとの消去済みの記号: Y ↦ N、N ↦ n。 -/
def loN (c : Ch) : Sy := gYN (lo nm13 c)

theorem hcgc (c : Ch) : ∀ x, YNSDY nm13 x → hc c (gc c x) = x := by
  cases c <;> rintro x (rfl | rfl | rfl | rfl | rfl) <;> rfl
theorem gc_lo (c : Ch) : gc c (lo nm13 c) = .s4 := by cases c <;> rfl
theorem hc_N (c : Ch) : hc c .s4 = lo nm13 c := by cases c <;> rfl
theorem gNY_loN (c : Ch) : gNY (loN c) = lo nm13 c := by cases c <;> rfl

theorem map_hc_gc (c : Ch) {R : List Sy} (hR : ∀ x ∈ R, YNSDY nm13 x) :
    (R.map (gc c)).map (hc c) = R := by
  induction R with
  | nil => rfl
  | cons x R ih =>
    simp only [List.map_cons, hcgc c x (hR x (List.mem_cons_self ..)),
      ih (fun y hy => hR y (List.mem_cons_of_mem _ hy))]

theorem map_loN (rm : List Ch) : (rm.map (lo nm13)).map gYN = rm.map loN := by
  rw [List.map_map]; rfl

theorem map_gNY_loN (rm : List Ch) : (rm.map loN).map gNY = rm.map (lo nm13) := by
  rw [List.map_map]
  exact List.map_congr_left (fun c _ => gNY_loN c)

/-! ## 3. 規則が表にあること -/

theorem pcy1 : ∀ x, YND nm13 x → (⟨.q1, x, gYN x, .L, .go .q1⟩ : Rule St Ps Sy) ∈ T11 := by
  rintro x (rfl | rfl | rfl) <;> decide
theorem pcy2 : ∀ x, YND nm13 x → (⟨.q2, gYN x, gNY (gYN x), .R, .go .q2⟩ : Rule St Ps Sy) ∈ T11 := by
  rintro x (rfl | rfl | rfl) <;> decide
theorem pcyc : ∀ x, YNS nm13 x → (⟨.q12, x, x, .R, .go .q12⟩ : Rule St Ps Sy) ∈ T11 := by
  rintro x (rfl | rfl | rfl) <;> decide
theorem pcyn : ∀ x, YNSD nm13 x → (⟨.q3, x, x, .L, .go .q3⟩ : Rule St Ps Sy) ∈ T11 := by
  rintro x (rfl | rfl | rfl | rfl) <;> decide
theorem pce : ∀ x, YNSD nm13 x → (⟨.q11, x, x, .R, .go .q11⟩ : Rule St Ps Sy) ∈ T11 := by
  rintro x (rfl | rfl | rfl | rfl) <;> decide

theorem rcs (c : Ch) : (⟨.q4, lo nm13 c, .s0, .R, .go (c1 nm13 c)⟩ : Rule St Ps Sy) ∈ T11 := by
  cases c <;> decide
theorem rc1b (c : Ch) : (⟨c1 nm13 c, .s0, .s4, .R, .go (c2' c)⟩ : Rule St Ps Sy) ∈ T11 := by
  cases c <;> decide
theorem rc1N (c : Ch) : (⟨c1 nm13 c, .s4, .s4, .L, .go (c3 nm13 c)⟩ : Rule St Ps Sy) ∈ T11 := by
  cases c <;> decide
theorem rc2 (c : Ch) : (⟨c2' c, .s0, .s0, .L, .go (c3 nm13 c)⟩ : Rule St Ps Sy) ∈ T11 := by
  cases c <;> decide
theorem rc3 (c : Ch) : (⟨c3 nm13 c, .s0, lo nm13 c, .L, .go .q4⟩ : Rule St Ps Sy) ∈ T11 := by
  cases c <;> decide
theorem pc1 (c : Ch) : ∀ x, YNSDY nm13 x →
    (⟨c1 nm13 c, x, gc c x, .R, .go (c1 nm13 c)⟩ : Rule St Ps Sy) ∈ T11 := by
  cases c <;> rintro x (rfl | rfl | rfl | rfl | rfl) <;> decide
theorem pc3 (c : Ch) : ∀ x, YNSDY nm13 x →
    (⟨c3 nm13 c, gc c x, hc c (gc c x), .L, .go (c3 nm13 c)⟩ : Rule St Ps Sy) ∈ T11 := by
  cases c <;> rintro x (rfl | rfl | rfl | rfl | rfl) <;> decide
theorem rce (c : Ch) : (⟨.q11, up nm13 c, lo nm13 c, .R, .go .q0⟩ : Rule St Ps Sy) ∈ T11 := by
  cases c <;> decide

/-- copy_c_3 が通る列 N · (gc c)(R)ᴿ の各記号について、hc c で書き戻す規則がある。 -/
theorem pc3_list (c : Ch) {R : List Sy} (hR : ∀ x ∈ R, YNSDY nm13 x) :
    ∀ y ∈ (R.map (gc c)).reverse, (⟨c3 nm13 c, y, hc c y, .L, .go (c3 nm13 c)⟩ : Rule St Ps Sy) ∈ T11 := by
  intro y hy
  rw [List.mem_reverse, List.mem_map] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  exact pc3 c x (hR x hx)

theorem pc3_N (c : Ch) : (⟨c3 nm13 c, .s4, hc c .s4, .L, .go (c3 nm13 c)⟩ : Rule St Ps Sy) ∈ T11 := by
  cases c <;> decide

/-! ## 4. コピー -/

/-- 先頭が Y のとき（書き足す）。親の copy_oneY と同じ道筋で、copy_c_1 が通った lo c を N にし、
    右端に N を書き、copy_c_3 が N を lo c に戻す。 -/
theorem copy_oneY (c : Ch) {LL : List Sy} (hLL : LL ≠ []) {R : List Sy}
    (hR : ∀ x ∈ R, YNSDY nm13 x) :
    Reach T11 (zc nm13.b (.go .q4) LL (lo nm13 c) R)
      (zl nm13.b (.go .q4) LL (lo nm13 c :: R ++ [lo nm13 c])) := by
  rw [← zc_trail _ _ _ R, ← zl_trail]
  refine (runRg (rcs c) (gc c) (fun x hx => pc1 c x (hR x hx)) LL nm13.b []).trans ?_
  rw [zc_nil]
  refine (Reach.step (stepR (rc1b c) _ nm13.b [])).trans ?_
  refine (Reach.step (stepL (rc2 c) .s4 _ [])).trans ?_
  have hX : ∀ y ∈ .s4 :: (R.map (gc c)).reverse,
      (⟨c3 nm13 c, y, hc c y, .L, .go (c3 nm13 c)⟩ : Rule St Ps Sy) ∈ T11 := by
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact pc3_N c
    · exact pc3_list c hR y hy
  refine (sweepLg (hc c) hX nm13.b LL [nm13.b]).trans ?_
  refine (Reach.step (stepL' (rc3 c) hLL _)).trans ?_
  apply Reach.of_eq
  have hm := map_hc_gc c hR
  simp only [List.map_cons, List.map_reverse, hm, hc_N, List.reverse_cons, List.reverse_reverse]
  simp

/-- 先頭が N のとき（書き足さない）: copy_c_1 が印の N に当たって引き返す。 -/
theorem copy_oneN (c : Ch) {LL : List Sy} (hLL : LL ≠ []) {R₁ : List Sy}
    (hR : ∀ x ∈ R₁, YNSDY nm13 x) (R₂ : List Sy) :
    Reach T11 (zc nm13.b (.go .q4) LL (lo nm13 c) (R₁ ++ nm13.N :: R₂))
      (zl nm13.b (.go .q4) LL (lo nm13 c :: R₁ ++ nm13.N :: R₂)) := by
  refine (runRg (rcs c) (gc c) (fun x hx => pc1 c x (hR x hx)) LL nm13.N R₂).trans ?_
  refine (Reach.step (stepL' (rc1N c) (L := (R₁.map (gc c)).reverse ++ nm13.b :: LL) (by simp) R₂)).trans ?_
  refine (sweepLg (hc c) (pc3_list c hR) nm13.b LL (nm13.N :: R₂)).trans ?_
  refine (Reach.step (stepL' (rc3 c) hLL _)).trans ?_
  apply Reach.of_eq
  have hm := map_hc_gc c hR
  simp only [List.map_reverse, hm, List.reverse_reverse]
  simp

theorem copy_loopY (Z : List Sy) (hZ : Z ≠ []) :
    ∀ (Q P : List Ch) (S : List Sy), (∀ x ∈ S, YNSDY nm13 x) →
    Reach T11 (zl nm13.b (.go .q4) (Q.map (lo nm13) ++ Z) (P.reverse.map (lo nm13) ++ S))
      (zl nm13.b (.go .q4) Z ((P ++ Q).reverse.map (lo nm13) ++ S ++ Q.map (lo nm13))) := by
  intro Q
  induction Q with
  | nil => intro P S _; exact Reach.of_eq (by simp)
  | cons c Q ih =>
    intro P S hS
    have hR : ∀ x ∈ P.reverse.map (lo nm13) ++ S, YNSDY nm13 x := fa_app (fa_map lo_YNSDY _) hS
    have h1 := copy_oneY c (LL := Q.map (lo nm13) ++ Z) (by simp [hZ]) hR
    have h2 := ih (P ++ [c]) (S ++ [lo nm13 c]) (fa_app hS (fa_cons (lo_YNSDY c) fa_nil))
    refine h1.trans (Eq.mpr ?_ h2)
    simp

theorem copy_loopN (Z : List Sy) (hZ : Z ≠ []) (S₂ : List Sy) :
    ∀ (Q P : List Ch) (S₁ : List Sy), (∀ x ∈ S₁, YNSDY nm13 x) →
    Reach T11 (zl nm13.b (.go .q4) (Q.map (lo nm13) ++ Z) (P.reverse.map (lo nm13) ++ S₁ ++ nm13.N :: S₂))
      (zl nm13.b (.go .q4) Z ((P ++ Q).reverse.map (lo nm13) ++ S₁ ++ nm13.N :: S₂)) := by
  intro Q
  induction Q with
  | nil => intro P S₁ _; exact Reach.of_eq (by simp)
  | cons c Q ih =>
    intro P S₁ hS
    have hR : ∀ x ∈ P.reverse.map (lo nm13) ++ S₁, YNSDY nm13 x := fa_app (fa_map lo_YNSDY _) hS
    have h1 := copy_oneN c (LL := Q.map (lo nm13) ++ Z) (by simp [hZ]) hR S₂
    have h1' : Reach T11
        (zl nm13.b (.go .q4) ((c :: Q).map (lo nm13) ++ Z) (P.reverse.map (lo nm13) ++ S₁ ++ nm13.N :: S₂))
        (zl nm13.b (.go .q4) (Q.map (lo nm13) ++ Z)
          ((P ++ [c]).reverse.map (lo nm13) ++ S₁ ++ nm13.N :: S₂)) := by
      refine Eq.mpr ?_ h1; simp [zl]
    have h2 := ih (P ++ [c]) S₁ hS
    refine h1'.trans (Eq.mpr ?_ h2)
    simp

/-! ## 5. 1 マクロステップ -/

theorem gYN_dl : gYN nm13.dl = nm13.dl := rfl
theorem comp_loN : (gYN ∘ U13_7.lo nm13) = loN := rfl
theorem gNY_dl : gNY nm13.dl = nm13.dl := rfl

/-- case_y_1 が通る列の各記号について、y を N にする規則がある。 -/
theorem pcy1_list {X : List Sy} (hX : ∀ x ∈ X, YND nm13 x) :
    ∀ x ∈ X, (⟨.q1, x, gYN x, .L, .go .q1⟩ : Rule St Ps Sy) ∈ T11 := fun x hx => pcy1 x (hX x hx)

/-- case_y_2 が通る列 $ · loN(rm) の各記号について、N を y に戻す規則がある。 -/
theorem pcy2_list (rm : List Ch) :
    ∀ x ∈ nm13.dl :: rm.map loN, (⟨.q2, x, gNY x, .R, .go .q2⟩ : Rule St Ps Sy) ∈ T11 := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact pcy2 nm13.dl (by simp [YND])
  · rw [List.mem_map] at hx
    obtain ⟨c, -, rfl⟩ := hx
    exact pcy2 (lo nm13 c) (lo_YND c)

/-- 先頭が Y、相 m ≥ 1: 親の frontY と同じ道筋。case_y_1 は ϕ₁(rm) の y を N にし、case_y_2 が戻す。 -/
theorem frontY (C : CTSH) (m : Nat) (hm : m ≠ 0) (rm v : List Ch) :
    Reach1 T11 (rep nm13 C m rm (.Y :: v))
      (zl nm13.b (.go .q4) ((prod C m).map (lo nm13) ++ (nm13.b :: U13_7.Hi nm13 C m).reverse)
        (nm13.st :: U13_7.Lo nm13 C m ++ nm13.dl :: rm.map (lo nm13) ++ nm13.Y :: v.map (lo nm13))) := by
  rw [rep_eq]
  simp only [List.map_cons, zr, U13_7.lo]
  rw [show (nm13.b :: U13_7.RA nm13 C m ++ nm13.dl :: rm.map (lo nm13)).reverse =
      ((rm.map (lo nm13)).reverse ++ [nm13.dl]) ++ nm13.st :: ((U13_7.LoCore nm13 C m).reverse ++ nm13.b ::
        ((prod C m).map (lo nm13) ++ (nm13.b :: U13_7.Hi nm13 C m).reverse)) by
    simp [U13_7.RA, Sim.RA, Sim.Lo_ne C m hm]]
  refine (runL1g (p := St.q0) (q := St.q1) (h := nm13.y) (t := nm13.Y) (by decide) gYN
    (pcy1_list (fa_app (fa_rev (fa_map lo_YND _)) (fa_cons (by simp [YND]) fa_nil)))
    nm13.st _ _).trans ?_
  rw [show (((rm.map (lo nm13)).reverse ++ [nm13.dl]).map gYN).reverse = nm13.dl :: rm.map loN by
    simp [List.map_reverse, loN, gYN_dl]]
  refine (runRg (p := St.q1) (q := St.q2) (h := nm13.st) (t := nm13.st) (by decide) gNY
    (X := nm13.dl :: rm.map loN) (pcy2_list rm) _ nm13.Y _).trans ?_
  rw [show ((nm13.dl :: rm.map loN).map gNY) = nm13.dl :: rm.map (lo nm13) by
    simp [gNY_loN, gNY_dl]]
  rw [show (nm13.dl :: rm.map (U13_7.lo nm13)).reverse ++ nm13.st :: ((U13_7.LoCore nm13 C m).reverse ++ nm13.b ::
        ((prod C m).map (U13_7.lo nm13) ++ (nm13.b :: U13_7.Hi nm13 C m).reverse)) =
      ((rm.map (U13_7.lo nm13)).reverse ++ nm13.dl :: nm13.st :: (U13_7.LoCore nm13 C m).reverse) ++ nm13.b ::
        ((prod C m).map (U13_7.lo nm13) ++ (nm13.b :: U13_7.Hi nm13 C m).reverse) by simp]
  refine (runL (p := St.q2) (q := St.q3) (h := nm13.Y) (t := nm13.Y) (by decide)
    (fun x hx => pcyn x ((fa_app (fa_rev (fa_map lo_YNSD _)) (fa_cons (by simp [YNSD])
      (fa_cons (by simp [YNSD]) (fa_rev (LoCore_mem lo_YNSD (by simp [YNSD]) C m))))) x hx))
    nm13.b _ _).trans ?_
  refine (Reach.step (stepL' (p := St.q3) (h := nm13.b) (t := nm13.st) (q := .go St.q4) (by decide)
    (L := (prod C m).map (lo nm13) ++ (nm13.b :: U13_7.Hi nm13 C m).reverse) (by simp) _)).trans ?_
  exact Reach.of_eq (by simp [Sim.Lo_ne C m hm])

/-- 先頭が N（任意の相）: 親と同じ規則だけを使う。 -/
theorem frontN (C : CTSH) (m : Nat) (rm v : List Ch) :
    Reach1 T11 (rep nm13 C m rm (.N :: v))
      (zl nm13.b (.go .q4) ((prod C m).map (lo nm13) ++ (nm13.b :: U13_7.Hi nm13 C m).reverse)
        (nm13.st :: U13_7.Lo nm13 C m ++ nm13.dl :: rm.map (lo nm13) ++ nm13.N :: v.map (lo nm13))) := by
  rw [rep_eq]
  simp only [List.map_cons, zr, U13_7.lo]
  rw [show (nm13.b :: U13_7.RA nm13 C m ++ nm13.dl :: rm.map (lo nm13)).reverse =
      ((rm.map (lo nm13)).reverse ++ nm13.dl :: (U13_7.Lo nm13 C m).reverse) ++ nm13.b ::
        ((prod C m).map (lo nm13) ++ (nm13.b :: U13_7.Hi nm13 C m).reverse) by simp [U13_7.RA, Sim.RA]]
  refine (runL1 (p := St.q0) (q := St.q3) (h := nm13.n) (t := nm13.N) (by decide)
    (fun x hx => pcyn x ((fa_app (fa_rev (fa_map lo_YNSD _)) (fa_cons (by simp [YNSD])
      (fa_rev (Lo_mem lo_YNSD (by simp [YNSD]) C m)))) x hx))
    nm13.b _ _).trans ?_
  refine (Reach.step (stepL' (p := St.q3) (h := nm13.b) (t := nm13.st) (q := .go St.q4) (by decide)
    (L := (prod C m).map (lo nm13) ++ (nm13.b :: U13_7.Hi nm13 C m).reverse) (by simp) _)).trans ?_
  exact Reach.of_eq (by simp)

/-- 相の終わり: 親と同じ規則だけを使う。 -/
theorem finish (C : CTSH) (m : Nat) (hk : m ≤ C.length) (c : Ch) (rm v : List Ch) :
    Reach T11 (zl nm13.b (.go .q4) (nm13.b :: U13_7.Hi nm13 C m).reverse
        ((prod C m).reverse.map (lo nm13) ++ nm13.st :: U13_7.Lo nm13 C m ++ nm13.dl :: rm.map (lo nm13) ++
          up nm13 c :: v.map (lo nm13)))
      (rep nm13 C ((m + 1) % C.k) (rm ++ [c]) v) := by
  rcases Nat.lt_or_ge m C.length with h | h
  · rw [Nat.mod_eq_of_lt (by simp [CTSH.k]; omega), rep_eq, U13_7.Hi, Sim.Hi_step C m h]
    rw [show (nm13.b :: (Sim.Hi (lo nm13) nm13.st C (m + 1) ++ (prod C (m + 1)).reverse.map (lo nm13) ++
          [nm13.st])).reverse =
        nm13.st :: (nm13.b :: Sim.Hi (lo nm13) nm13.st C (m + 1) ++ (prod C (m + 1)).reverse.map (lo nm13)).reverse
        by simp]
    simp only [zl]
    rw [show (prod C m).reverse.map (lo nm13) ++ nm13.st :: U13_7.Lo nm13 C m ++ nm13.dl :: rm.map (lo nm13) ++
          up nm13 c :: v.map (lo nm13) =
        ((prod C m).reverse.map (lo nm13) ++ nm13.st :: U13_7.Lo nm13 C m ++ nm13.dl :: rm.map (lo nm13)) ++
          up nm13 c :: v.map (lo nm13) by simp]
    refine (runR (p := St.q4) (q := St.q11) (h := nm13.st) (t := nm13.b) (by decide)
      (fun x hx => pce x ((fa_app (fa_app (fa_map lo_YNSD _) (fa_cons (by simp [YNSD])
        (Lo_mem lo_YNSD (by simp [YNSD]) C m))) (fa_cons (by simp [YNSD]) (fa_map lo_YNSD _))) x hx))
      _ _ _).trans ?_
    refine (Reach.step (stepR' (rce c) _ _)).trans ?_
    apply Reach.of_eq
    congr 1
    simp [U13_7.RA, Sim.RA, Sim.Lo_step (lo := lo nm13) (st := nm13.st) C m hk]
  · have hmk : m = C.length := by omega
    subst hmk
    rw [show (C.length + 1) % C.k = 0 by simp [CTSH.k], rep_eq, U13_7.Hi, Sim.Hi_len]
    simp only [zl, List.reverse_cons, List.reverse_nil, List.nil_append]
    have hLo := Sim.Lo_step (lo := lo nm13) (st := nm13.st) C C.length (Nat.le_refl _)
    rw [show (prod C C.length).reverse.map (lo nm13) ++ nm13.st :: U13_7.Lo nm13 C C.length ++
          nm13.dl :: rm.map (lo nm13) ++ up nm13 c :: v.map (lo nm13) =
        U13_7.Lo nm13 C (C.length + 1) ++ nm13.dl :: (rm.map (lo nm13) ++ up nm13 c :: v.map (lo nm13)) by
      simp [U13_7.Lo, hLo]]
    refine (runR (p := St.q4) (q := St.q12) (h := nm13.b) (t := nm13.b) (by decide)
      (fun x hx => pcyc x ((Lo_mem lo_YNS (by simp [YNS]) C _) x hx)) [] _ _).trans ?_
    rw [Sim.Lo_ne C (C.length + 1) (by omega)]
    rw [show (Sim.LoCore (lo nm13) nm13.st C (C.length + 1) ++ [nm13.st]).reverse ++ [nm13.b] =
        nm13.st :: ((Sim.LoCore (lo nm13) nm13.st C (C.length + 1)).reverse ++ [nm13.b]) by simp]
    refine (Reach.step (stepL (p := St.q12) (h := nm13.dl) (t := nm13.dl) (q := .go St.q4) (by decide)
      _ _ _)).trans ?_
    rw [show nm13.dl :: (rm.map (lo nm13) ++ up nm13 c :: v.map (lo nm13)) =
        (nm13.dl :: rm.map (lo nm13)) ++ up nm13 c :: v.map (lo nm13) by simp]
    refine (runR (p := St.q4) (q := St.q11) (h := nm13.st) (t := nm13.b) (by decide)
      (fun x hx => pce x ((fa_cons (by simp [YNSD]) (fa_map lo_YNSD _)) x hx)) _ _ _).trans ?_
    refine (Reach.step (stepR' (rce c) _ _)).trans ?_
    apply Reach.of_eq
    congr 1
    simp [U13_7.RA, Sim.RA, Sim.LoCore_full, U13_7.lo, prod, Sim.Lo]

theorem macroY (C : CTSH) {m : Nat} (h0 : m ≠ 0) (hk : m < C.k) (rm v : List Ch) :
    Reach1 T11 (rep nm13 C m rm (.Y :: v)) (rep nm13 C ((m + 1) % C.k) (rm ++ [.Y]) (v ++ prod C m)) := by
  have hmk : m ≤ C.length := by simp [CTSH.k] at hk; omega
  refine (frontY C m h0 rm v).trans ?_
  have hS : ∀ x ∈ nm13.st :: U13_7.Lo nm13 C m ++ nm13.dl :: rm.map (lo nm13) ++ nm13.Y :: v.map (lo nm13),
      YNSDY nm13 x :=
    fa_app (fa_app (fa_cons (by simp [YNSDY]) (Lo_mem lo_YNSDY (by simp [YNSDY]) C m))
      (fa_cons (by simp [YNSDY]) (fa_map lo_YNSDY _)))
      (fa_cons (by simp [YNSDY]) (fa_map lo_YNSDY _))
  have hL := copy_loopY _ (by simp : (nm13.b :: U13_7.Hi nm13 C m).reverse ≠ []) (prod C m) [] _ hS
  refine hL.trans ?_
  have hf := finish C m hmk .Y rm (v ++ prod C m)
  refine Eq.mpr ?_ hf
  simp [up]

theorem macroN (C : CTSH) {m : Nat} (hk : m < C.k) (rm v : List Ch) :
    Reach1 T11 (rep nm13 C m rm (.N :: v)) (rep nm13 C ((m + 1) % C.k) (rm ++ [.N]) v) := by
  have hmk : m ≤ C.length := by simp [CTSH.k] at hk; omega
  refine (frontN C m rm v).trans ?_
  have hS : ∀ x ∈ nm13.st :: U13_7.Lo nm13 C m ++ nm13.dl :: rm.map (lo nm13), YNSDY nm13 x :=
    fa_app (fa_cons (by simp [YNSDY]) (Lo_mem lo_YNSDY (by simp [YNSDY]) C m))
      (fa_cons (by simp [YNSDY]) (fa_map lo_YNSDY _))
  have hL := copy_loopN _ (by simp : (nm13.b :: U13_7.Hi nm13 C m).reverse ≠ []) (v.map (lo nm13))
    (prod C m) [] _ hS
  have hL' : Reach T11
      (zl nm13.b (.go .q4) ((prod C m).map (lo nm13) ++ (nm13.b :: U13_7.Hi nm13 C m).reverse)
        (nm13.st :: U13_7.Lo nm13 C m ++ nm13.dl :: rm.map (lo nm13) ++ nm13.N :: v.map (lo nm13)))
      (zl nm13.b (.go .q4) (nm13.b :: U13_7.Hi nm13 C m).reverse
        ((prod C m).reverse.map (lo nm13) ++ nm13.st :: U13_7.Lo nm13 C m ++ nm13.dl :: rm.map (lo nm13) ++
          nm13.N :: v.map (lo nm13))) := by
    refine Eq.mpr ?_ hL; simp
  refine hL'.trans ?_
  have hf := finish C m hmk .N rm v
  refine Eq.mpr ?_ hf
  simp [up]

/-! ## 6. 停止 -/

/-- 停止配置のテープ（リスト）。(λ, m) は親と同じ。(Y v, 0) は case_y_1 の掃引の途中で止まるので、
    消去済みの文字列 ϕ₁(rm) の y が N のまま（`loN`）。 -/
def finList11 (C : CTSH) (vf : List Ch) (mf : Nat) (rm : List Ch) : List Sy :=
  match vf with
  | [] => tapeList nm13 C mf rm []
  | _ :: v => nm13.b :: U13_7.RA nm13 C 0 ++ nm13.dl :: rm.map loN ++ nm13.Y :: v.map (lo nm13)

/-- 停止配置。状態とヘッドの位置は親（`U13_7.finCfg`）と同じ。 -/
def finCfg11 (C : CTSH) (vf : List Ch) (mf : Nat) (rm : List Ch) : Cfg St Ps Sy :=
  match vf with
  | [] => { st := .halt nm13.null, pos := (U13_7.RA nm13 C mf).length + 2 + rm.length,
            tape := tp nm13.b (finList11 C [] mf rm) }
  | c :: v => { st := .halt nm13.halt, pos := (U13_7.RA nm13 C 0).length,
                tape := tp nm13.b (finList11 C (c :: v) 0 rm) }

theorem halt_null (C : CTSH) (m : Nat) (rm : List Ch) :
    Reach1 T11 (rep nm13 C m rm []) (finCfg11 C [] m rm) := by
  rw [rep_eq]
  simp only [List.map_nil, zr]
  refine Reach1.of_step (stepZ (p := St.q0) (h := nm13.b) (t := nm13.b) (q := Tgt.halt nm13.null) (by decide)
    _ _) (Reach.of_eq ?_)
  simp only [zc, finCfg11, finList11, tapeList]
  congr 1
  · simp; omega
  · simpa using tp_trail (bk := nm13.b) (nm13.b :: (U13_7.RA nm13 C m ++ nm13.dl :: List.map (lo nm13) rm))

theorem halt_Y (C : CTSH) (rm v : List Ch) :
    Reach1 T11 (rep nm13 C 0 rm (.Y :: v)) (finCfg11 C (.Y :: v) 0 rm) := by
  rw [rep_eq]
  simp only [List.map_cons, zr, U13_7.lo]
  rw [show (nm13.b :: U13_7.RA nm13 C 0 ++ nm13.dl :: rm.map (lo nm13)).reverse =
      ((rm.map (lo nm13)).reverse ++ [nm13.dl]) ++ nm13.b :: (nm13.b :: U13_7.Hi nm13 C 0).reverse by
    simp [U13_7.RA, Sim.RA_zero]]
  refine (runL1g (p := St.q0) (q := St.q1) (h := nm13.y) (t := nm13.Y) (by decide) gYN
    (pcy1_list (fa_app (fa_rev (fa_map lo_YND _)) (fa_cons (by simp [YND]) fa_nil)))
    nm13.b _ _).trans ?_
  refine (Reach.step (stepZ (p := St.q1) (h := nm13.b) (t := nm13.b) (q := Tgt.halt nm13.halt) (by decide)
    _ _)).trans ?_
  apply Reach.of_eq
  simp only [zc, finCfg11, finList11]
  congr 1
  · simp [U13_7.RA, Sim.RA_zero]
  · simp [U13_7.RA, U13_7.Hi, Sim.RA_zero, List.map_reverse, comp_loN, gYN_dl]

theorem finCfg11_halted (C : CTSH) (vf : List Ch) (mf : Nat) (rm : List Ch) :
    Halted T11 (finCfg11 C vf mf rm) := by
  intro c' ⟨r, _, hst, _⟩
  cases vf <;> simp [finCfg11] at hst

/-! ## 7. 主定理 -/

/-- 初期配置は親と同じ（Morita の (13,7) の符号化）。 -/
def encC11 (C : CTSH) (w : List Ch) : Cfg St Ps Sy := encC nm13 C w

/-- **主定理（URTM(11,7) は任意の CTSH を模倣する）**。`urtm13_7_simulates_ctsh` と同じ 3 項で、
    表は `T11`、停止配置は `finCfg11`。 -/
theorem urtm11_7_simulates_ctsh (C : CTSH) (w : List Ch) :
    (∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) →
      ∃ N rm, n ≤ N ∧ HaltsIn T11 N (encC11 C w) (finCfg11 C vf mf rm)) ∧
    (∀ N e, HaltsIn T11 N (encC11 C w) e →
      ∃ n vf mf rm, CHaltsIn C n (w, 0) (vf, mf) ∧ e = finCfg11 C vf mf rm) ∧
    ((∀ n f, ¬ CHaltsIn C n (w, 0) f) ↔ (∀ N e, ¬ HaltsIn T11 N (encC11 C w) e)) :=
  simulates_of_steps C (rep nm13 C) (finCfg11 C) hD11 (macroY C) (macroN C) (halt_Y C)
    (halt_null C) (finCfg11_halted C) w

end URTM.CTSH.U11_7
