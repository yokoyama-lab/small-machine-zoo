/-
  k 状態化変換「定理 A」（docs/03_kstate_2026-09-23.md §2）の一般の模倣証明。

  * T は任意の 1 テープ五つ組機械（状態型 `Q`・記号型 `S` は任意。状態は有限で
    `qs : List Q` に列挙され、記号も `ss : List S` に列挙される）。
  * 可逆性条件は Morita 2017, Def. 5.4 を「規則の集合」として述べたもの。
  * 疑似状態（Morita の `halt`, `null` など）は任意の型 `P` の値 `.halt h` で、複数持てる。
    可逆性は「同じ次状態（同じ疑似状態を含む）」についてだけ要求する。
  * 変換 `conv T qs ss` は 4 状態 `Hp Hm Ap Am`（と T と同じ疑似状態）、
    記号は素の `pl s` と計数 `ctr i s` の機械を返す**関数**。
  * テープは両側無限（`Int → S`）。左端から落ちる事象は無い（`Basic.lean` の片側テープとの差）。

  主定理（ファイル末尾）:
  * `conv_det_rev`       : T が決定的・可逆 ⇒ T' も決定的・可逆            (a)
  * `conv_simulates`     : T の 1 ステップ c → c' を T' が enc c から
                           ちょうど `cost c'` = 3 + 2Δ（停止規則は 1）ステップで enc c' へ   (b)
  * `conv_halted_iff`    : T が c で止まる ⇔ T' が enc c で止まる             (b)
  * `conv_haltsIn`       : T が n ステップで停止配置 cf ⇒ T' が N ステップで enc cf（n ≤ N）(c ⇒)
  * `conv_haltsIn_rev`   : T' が enc c から停止 ⇒ T も c から停止し、停止配置は enc で対応 (c ⇐)
  * `conv_diverges_iff`  : 停止しないことの保存                                (c)
  * `conv_main`          : 以上と記号の範囲のまとめ（具体機械への適用用。`tools/gen_kstate_lean.py`）

  未証明の穴・新規公理なし（検査は docs/05 を参照）。mathlib 非依存。
-/
import URTM.Basic

namespace URTM.KState

open URTM (Dir)

/-! ## 1. 一般の五つ組機械 -/

/-- 次状態。`halt` は疑似状態（そこから出る規則は無い）。 -/
inductive Tgt (Q P : Type) where
  | go (q : Q)
  | halt (h : P)
  deriving DecidableEq

/-- 行き先が実状態か。 -/
def Tgt.isGo {Q P : Type} : Tgt Q P → Bool
  | .go _ => true
  | .halt _ => false

/-- 五つ組 `[p, s, t, d, q]`。 -/
structure Rule (Q P S : Type) where
  p : Q
  s : S
  t : S
  d : Dir
  q : Tgt Q P
  deriving DecidableEq

/-- 機械 = 規則のリスト（集合として扱う。重複は意味を持たない）。 -/
abbrev Machine (Q P S : Type) := List (Rule Q P S)

variable {Q P S : Type}

/-- 決定性（相異なる規則で現状態が同じなら読込記号が相異なる）。 -/
def Deterministic (T : Machine Q P S) : Prop :=
  ∀ r₁ ∈ T, ∀ r₂ ∈ T, r₁ ≠ r₂ → r₁.p = r₂.p → r₁.s ≠ r₂.s

/-- 可逆性条件（Morita 2017, Def. 5.4）: 相異なる規則で次状態が同じなら、
    方向は同じで書込記号は相異なる。 -/
def Reversible (T : Machine Q P S) : Prop :=
  ∀ r₁ ∈ T, ∀ r₂ ∈ T, r₁ ≠ r₂ → r₁.q = r₂.q → r₁.d = r₂.d ∧ r₁.t ≠ r₂.t

/-- 0 シフト規則は疑似状態 `halt` にしか入らない（Morita の記述ファイルの約束）。 -/
def ZeroShiftHalts (T : Machine Q P S) : Prop :=
  ∀ r ∈ T, r.d = .Z → r.q.isGo = false

instance [DecidableEq Q] [DecidableEq P] [DecidableEq S] (T : Machine Q P S) :
    Decidable (Deterministic T) := by unfold Deterministic; infer_instance
instance [DecidableEq Q] [DecidableEq P] [DecidableEq S] (T : Machine Q P S) :
    Decidable (Reversible T) := by unfold Reversible; infer_instance
instance (T : Machine Q P S) : Decidable (ZeroShiftHalts T) := by
  unfold ZeroShiftHalts; infer_instance

/-- 実状態へ入る規則は左右どちらかに動く（0 シフトは疑似状態にしか入らない）。 -/
theorem go_dir_LR {T : Machine Q P S} (hW : ZeroShiftHalts T) {r : Rule Q P S} (hr : r ∈ T)
    (hq : r.q.isGo = true) : r.d = .L ∨ r.d = .R := by
  cases hd : r.d with
  | L => exact .inl rfl
  | R => exact .inr rfl
  | Z => have := hW r hr hd; rw [hq] at this; cases this

/-- ヘッドの移動量。 -/
def mv : Dir → Int
  | .L => -1
  | .Z => 0
  | .R => 1

/-- 逆方向。 -/
def opp : Dir → Dir
  | .L => .R
  | .R => .L
  | .Z => .Z

theorem opp_inj {d e : Dir} (h : opp d = opp e) : d = e := by
  cases d <;> cases e <;> first | rfl | cases h

/-- 配置。テープは両側無限。 -/
structure Cfg (Q P S : Type) where
  st : Tgt Q P
  pos : Int
  tape : Int → S

/-- 1 点更新。 -/
def upd {α : Type} (f : Int → α) (i : Int) (v : α) : Int → α :=
  fun j => if j = i then v else f j

/-- 規則 `r` を配置 `c` に適用した結果。 -/
def fire (r : Rule Q P S) (c : Cfg Q P S) : Cfg Q P S :=
  { st := r.q, pos := c.pos + mv r.d, tape := upd c.tape c.pos r.t }

/-- 1 ステップ（関係）。 -/
def Step (T : Machine Q P S) (c c' : Cfg Q P S) : Prop :=
  ∃ r ∈ T, c.st = .go r.p ∧ c.tape c.pos = r.s ∧ c' = fire r c

/-- ちょうど `n` ステップ。 -/
inductive StepN (T : Machine Q P S) : Nat → Cfg Q P S → Cfg Q P S → Prop
  | refl (c : Cfg Q P S) : StepN T 0 c c
  | cons {n : Nat} {c c' c'' : Cfg Q P S} : Step T c c' → StepN T n c' c'' → StepN T (n + 1) c c''

/-- 停止配置（どの規則も適用できない。状態が `halt` の場合と、規則が無い場合の両方）。 -/
def Halted (T : Machine Q P S) (c : Cfg Q P S) : Prop :=
  ∀ c', ¬ Step T c c'

/-- ちょうど `n` ステップで停止配置 `e` に達する。 -/
def HaltsIn (T : Machine Q P S) (n : Nat) (c e : Cfg Q P S) : Prop :=
  StepN T n c e ∧ Halted T e

/-! ### ステップの一般的な性質 -/

theorem StepN.trans {T : Machine Q P S} {n m : Nat} {a b c : Cfg Q P S}
    (h₁ : StepN T n a b) (h₂ : StepN T m b c) : StepN T (n + m) a c := by
  induction h₁ with
  | refl => simpa using h₂
  | cons h _ ih =>
    have := StepN.cons h (ih h₂)
    rwa [show ∀ k l : Nat, k + 1 + l = k + l + 1 from fun k l => by omega]

theorem StepN.first {T : Machine Q P S} {k : Nat} {a b : Cfg Q P S} (h : StepN T k a b)
    (hk : 1 ≤ k) : ∃ x, Step T a x := by
  cases h with
  | refl => omega
  | cons h₁ _ => exact ⟨_, h₁⟩

theorem StepN.single {T : Machine Q P S} {a b : Cfg Q P S} (h : Step T a b) : StepN T 1 a b :=
  StepN.cons h (StepN.refl b)

theorem step_func {T : Machine Q P S} (hD : Deterministic T) {c c₁ c₂ : Cfg Q P S}
    (h₁ : Step T c c₁) (h₂ : Step T c c₂) : c₁ = c₂ := by
  obtain ⟨r₁, hr₁, hst₁, hs₁, rfl⟩ := h₁
  obtain ⟨r₂, hr₂, hst₂, hs₂, rfl⟩ := h₂
  by_cases h : r₁ = r₂
  · subst h; rfl
  · rw [hst₁] at hst₂
    injection hst₂ with hp
    exact absurd (hs₁.symm.trans hs₂) (hD r₁ hr₁ r₂ hr₂ h hp)

/-- 決定的な機械では、停止配置へ向かう経路の途中の配置はすべてその経路上にある。 -/
theorem stepN_prefix {T : Machine Q P S} (hD : Deterministic T) :
    ∀ {k n : Nat} {a b e : Cfg Q P S}, StepN T n a b → Halted T b → StepN T k a e →
      k ≤ n ∧ StepN T (n - k) e b := by
  intro k
  induction k with
  | zero =>
    intro n a b e hab _ hae
    cases hae
    exact ⟨Nat.zero_le _, by simpa using hab⟩
  | succ k ih =>
    intro n a b e hab hb hae
    cases hae with
    | cons h₁ h₂ =>
      cases hab with
      | refl => exact absurd h₁ (hb _)
      | cons h₃ h₄ =>
        have := step_func hD h₁ h₃
        subst this
        obtain ⟨hk, hr⟩ := ih h₄ hb h₂
        refine ⟨by omega, ?_⟩
        rwa [show ∀ x y : Nat, x + 1 - (y + 1) = x - y from fun x y => by omega]

theorem stepN_from_halted {T : Machine Q P S} {n : Nat} {a e : Cfg Q P S}
    (ha : Halted T a) (h : StepN T n a e) : n = 0 ∧ e = a := by
  cases h with
  | refl => exact ⟨rfl, rfl⟩
  | cons h₁ _ => exact absurd h₁ (ha _)

theorem exists_step_of_not_halted {T : Machine Q P S} {c : Cfg Q P S} (h : ¬ Halted T c) :
    ∃ c', Step T c c' :=
  Classical.byContradiction fun h' => h fun c' hc => h' ⟨c', hc⟩

/-! ### 1 ステップの模倣から多ステップへ（機械の型に依らない）

  T の各ステップ c → c' を T' が `cost c'`（≥ 1）ステップで E c → E c' と模倣し、T の停止配置を
  E が T' の停止配置に移すなら、停止する実行の前向きの対応と（T' が決定的なら）逆向きの対応が従う。
  前向きは、模倣の仮定を「その後 `ok` な停止配置に達するステップ」にだけ要求する。
  逆向きは、ステップで保たれる不変量 `Inv` の下で要求する。 -/

section Multi
variable {Q' P' S' : Type} {T : Machine Q P S} {T' : Machine Q' P' S'}
  (E : Cfg Q P S → Cfg Q' P' S') (cost : Cfg Q P S → Nat)

theorem haltsIn_of_sim (ok : Cfg Q P S → Prop) (hpos : ∀ c, 1 ≤ cost c)
    (hsim : ∀ {c c' n cf}, Step T c c' → HaltsIn T n c' cf → ok cf → StepN T' (cost c') (E c) (E c'))
    (hhalt : ∀ {c}, Halted T c → ok c → Halted T' (E c)) :
    ∀ {n c cf}, HaltsIn T n c cf → ok cf → ∃ N, n ≤ N ∧ HaltsIn T' N (E c) (E cf) := by
  intro n
  induction n with
  | zero => intro c cf ⟨h, hH⟩ hf; cases h; exact ⟨0, Nat.le_refl _, .refl _, hhalt hH hf⟩
  | succ n ih =>
    intro c cf ⟨h, hH⟩ hf
    cases h with
    | cons h₁ h₂ =>
      rename_i c₁
      obtain ⟨N, hN, hs, hH'⟩ := ih ⟨h₂, hH⟩ hf
      exact ⟨_, by have := hpos c₁; omega, (hsim h₁ ⟨h₂, hH⟩ hf).trans hs, hH'⟩

theorem haltsIn_rev_of_sim (Inv : Cfg Q P S → Prop) (hD' : Deterministic T') (hpos : ∀ c, 1 ≤ cost c)
    (hInv : ∀ {c c'}, Inv c → Step T c c' → Inv c')
    (hsim : ∀ {c c'}, Inv c → Step T c c' → StepN T' (cost c') (E c) (E c'))
    (hhalt : ∀ {c}, Inv c → Halted T c → Halted T' (E c)) :
    ∀ (N : Nat) {c e}, Inv c → HaltsIn T' N (E c) e → ∃ n cf, HaltsIn T n c cf ∧ e = E cf := by
  intro N
  induction N using Nat.strongRecOn with
  | _ N ih =>
    intro c e hI ⟨hs, hH⟩
    by_cases hc : Halted T c
    · obtain ⟨rfl, rfl⟩ := stepN_from_halted (hhalt hI hc) hs
      exact ⟨0, c, ⟨.refl _, hc⟩, rfl⟩
    · obtain ⟨c₁, h₁⟩ := exists_step_of_not_halted hc
      obtain ⟨hk, hrest⟩ := stepN_prefix hD' hs hH (hsim hI h₁)
      have := hpos c₁
      obtain ⟨n, cf, ⟨hn, hcf⟩, rfl⟩ := ih (N - cost c₁) (by omega) (hInv hI h₁) ⟨hrest, hH⟩
      exact ⟨n + 1, cf, ⟨.cons h₁ hn, hcf⟩, rfl⟩

/-- 停止の前向き・逆向きの対応から、停止しないことの対応。 -/
theorem diverges_iff_of {c : Cfg Q P S} {c' : Cfg Q' P' S'}
    (fwd : ∀ n cf, HaltsIn T n c cf → ∃ N e, HaltsIn T' N c' e)
    (bwd : ∀ N e, HaltsIn T' N c' e → ∃ n cf, HaltsIn T n c cf) :
    (∀ n cf, ¬ HaltsIn T n c cf) ↔ (∀ N e, ¬ HaltsIn T' N c' e) :=
  ⟨fun h N e he => let ⟨n, cf, hn⟩ := bwd N e he; h n cf hn,
   fun h n cf hn => let ⟨N, e, hN⟩ := fwd n cf hn; h N e hN⟩

end Multi

/-! ## 2. 入る方向 `dir` と番号付け -/

section Dir
variable [DecidableEq Q] [DecidableEq P]

/-- 状態 `q` に入る規則の方向。`L` で入る規則があれば `L`、無ければ `R`
    （一度も入られない状態は Q₊ に置く約束）。 -/
def dir (T : Machine Q P S) (q : Q) : Dir :=
  if ∃ r ∈ T, r.q = .go q ∧ r.d = .L then .L else .R

theorem dir_cases (T : Machine Q P S) (q : Q) : dir T q = .L ∨ dir T q = .R := by
  unfold dir; split
  · exact .inl rfl
  · exact .inr rfl

/-- 可逆な T では、q に入る規則の方向は `dir T q` に一致する。 -/
theorem dir_eq {T : Machine Q P S} (hW : ZeroShiftHalts T) (hR : Reversible T)
    {r : Rule Q P S} (hr : r ∈ T) {q : Q} (hq : r.q = .go q) : dir T q = r.d := by
  unfold dir
  split
  · rename_i h
    obtain ⟨r', hr', hq', hd'⟩ := h
    by_cases e : r = r'
    · subst e; exact hd'.symm
    · rw [(hR r hr r' hr' e (hq.trans hq'.symm)).1, hd']
  · rename_i h
    cases hd : r.d with
    | L => exact absurd ⟨r, hr, hq, hd⟩ h
    | Z => have := hW r hr hd; simp [hq, Tgt.isGo] at this
    | R => rfl

end Dir

/-! ## 3. 変換 T ↦ T' -/

/-- T' の状態。`H` 系は安定配置、`A` 系は往復中。添字はその状態に入る方向。 -/
inductive KSt where
  | Hp
  | Hm
  | Ap
  | Am
  deriving DecidableEq, Repr

/-- T' の記号: 素の記号と計数記号 `[i, s]`。 -/
inductive KSym (S : Type) where
  | pl (s : S)
  | ctr (i : Nat) (s : S)
  deriving DecidableEq

def H : Dir → KSt
  | .L => .Hm
  | _ => .Hp

def A : Dir → KSt
  | .L => .Am
  | _ => .Ap

@[simp] theorem H_L : H .L = .Hm := rfl
@[simp] theorem H_R : H .R = .Hp := rfl
@[simp] theorem A_L : A .L = .Am := rfl
@[simp] theorem A_R : A .R = .Ap := rfl
@[simp] theorem opp_L : opp .L = .R := rfl
@[simp] theorem opp_R : opp .R = .L := rfl

@[simp] theorem H_ne_A (x y : Dir) : H x ≠ A y := by cases x <;> cases y <;> simp [H, A]
@[simp] theorem H_ne_Ap (x : Dir) : H x ≠ .Ap := by cases x <;> simp [H]
@[simp] theorem H_ne_Am (x : Dir) : H x ≠ .Am := by cases x <;> simp [H]
@[simp] theorem Ap_ne_H (x : Dir) : KSt.Ap ≠ H x := by cases x <;> simp [H]
@[simp] theorem Am_ne_H (x : Dir) : KSt.Am ≠ H x := by cases x <;> simp [H]

/-- 番号範囲: Q₊ は `{1..mp}`、Q₋ は `{mp+1..mp+mm}`。 -/
def lo (mp : Nat) : Dir → Nat
  | .L => mp + 1
  | _ => 1

def hi (mp mm : Nat) : Dir → Nat
  | .L => mp + mm
  | _ => mp

@[simp] theorem lo_L (mp : Nat) : lo mp .L = mp + 1 := rfl
@[simp] theorem lo_R (mp : Nat) : lo mp .R = 1 := rfl
@[simp] theorem hi_L (mp mm : Nat) : hi mp mm .L = mp + mm := rfl
@[simp] theorem hi_R (mp mm : Nat) : hi mp mm .R = mp := rfl

section Conv
variable [DecidableEq Q] [DecidableEq P]

/-- R1 / R1'（T の規則 1 本の実行）。 -/
def rule1 (T : Machine Q P S) (off : Q → Nat) (r : Rule Q P S) : Rule KSt P (KSym S) :=
  match r.q with
  | .go q => ⟨H (dir T r.p), .ctr (off r.p) r.s, .ctr (off q) r.t, r.d, .go (H r.d)⟩
  | .halt h => ⟨H (dir T r.p), .ctr (off r.p) r.s, .pl r.t, r.d, .halt h⟩

/-- 方向 `d` の往復（R2〜R5）。範囲が空（その方向に入る状態が無い）なら規則を作らない。 -/
def shuttle (mp mm : Nat) (ss : List S) (d : Dir) : List (Rule KSt P (KSym S)) :=
  if lo mp d ≤ hi mp mm d then
    ss.map (fun s₂ => ⟨H d, .pl s₂, .ctr (lo mp d) s₂, opp d, .go (A (opp d))⟩) ++
    (List.range' (lo mp d + 1) (hi mp mm d - lo mp d)).flatMap
      (fun i => ss.map (fun t => ⟨A (opp d), .ctr i t, .ctr (i - 1) t, d, .go (A d)⟩)) ++
    ss.map (fun t => ⟨A (opp d), .ctr (lo mp d) t, .pl t, d, .go (H d)⟩) ++
    (List.range' (lo mp d) (hi mp mm d - lo mp d)).flatMap
      (fun j => ss.map (fun s₂ => ⟨A d, .ctr j s₂, .ctr (j + 1) s₂, opp d, .go (A (opp d))⟩))
  else []

/-- 番号付け `off` と範囲 `mp, mm` を与えた変換。 -/
def convWith (T : Machine Q P S) (off : Q → Nat) (mp mm : Nat) (ss : List S) :
    Machine KSt P (KSym S) :=
  T.map (rule1 T off) ++ shuttle mp mm ss .R ++ shuttle mp mm ss .L

/-- リスト内の最初の位置。 -/
def ix (a : Q) : List Q → Nat
  | [] => 0
  | x :: xs => if x = a then 0 else ix a xs + 1

/-- Q₊（`R` で入る、または入られない状態）の列挙。 -/
def plusList (T : Machine Q P S) (qs : List Q) : List Q := qs.filter (fun q => decide (dir T q = .R))
/-- Q₋ の列挙。 -/
def minusList (T : Machine Q P S) (qs : List Q) : List Q := qs.filter (fun q => decide (dir T q = .L))

/-- 標準の番号付け: Q₊ に `1..m₊`、Q₋ に `m₊+1..m`。 -/
def canonOff (T : Machine Q P S) (qs : List Q) (q : Q) : Nat :=
  if dir T q = .R then ix q (plusList T qs) + 1
  else (plusList T qs).length + ix q (minusList T qs) + 1

/-- **定理 A の変換**（関数）。`qs` は T の状態の列挙、`ss` は記号の列挙。 -/
def conv (T : Machine Q P S) (qs : List Q) (ss : List S) : Machine KSt P (KSym S) :=
  convWith T (canonOff T qs) (plusList T qs).length (minusList T qs).length ss

/-- 配置の符号化。安定配置: 状態 `H (dir p)`、ヘッド上のセルだけ計数記号 `[off p, s]`。 -/
def enc (T : Machine Q P S) (off : Q → Nat) (c : Cfg Q P S) : Cfg KSt P (KSym S) :=
  match c.st with
  | .go p => ⟨.go (H (dir T p)), c.pos,
      fun j => if j = c.pos then .ctr (off p) (c.tape j) else .pl (c.tape j)⟩
  | .halt h => ⟨.halt h, c.pos, fun j => .pl (c.tape j)⟩

/-- T の 1 ステップ（行き先配置 `c'`）に要する T' のステップ数。
    Δ = off(q) − lo(dir q)。停止規則は 1。 -/
def cost (T : Machine Q P S) (off : Q → Nat) (mp : Nat) (c' : Cfg Q P S) : Nat :=
  match c'.st with
  | .go q => 3 + 2 * (off q - lo mp (dir T q))
  | .halt _ => 1

/-- 番号付けの条件。 -/
structure GoodNum (T : Machine Q P S) (off : Q → Nat) (mp mm : Nat) : Prop where
  inj : ∀ a b, off a = off b → a = b
  rngR : ∀ q, dir T q = .R → 1 ≤ off q ∧ off q ≤ mp
  rngL : ∀ q, dir T q = .L → mp + 1 ≤ off q ∧ off q ≤ mp + mm

/-! ### 規則の分類 -/

/-- T' の規則の 6 種類（R1, R1', R2〜R5）。 -/
inductive Kind (T : Machine Q P S) (off : Q → Nat) (mp mm : Nat) : Rule KSt P (KSym S) → Prop
  | r1go (p : Q) (s t : S) (d : Dir) (q : Q) :
      (⟨p, s, t, d, .go q⟩ : Rule Q P S) ∈ T → (d = .L ∨ d = .R) →
      Kind T off mp mm ⟨H (dir T p), .ctr (off p) s, .ctr (off q) t, d, .go (H d)⟩
  | r1halt (p : Q) (s t : S) (d : Dir) (h : P) :
      (⟨p, s, t, d, .halt h⟩ : Rule Q P S) ∈ T →
      Kind T off mp mm ⟨H (dir T p), .ctr (off p) s, .pl t, d, .halt h⟩
  | r2 (d : Dir) (s₂ : S) : (d = .L ∨ d = .R) → lo mp d ≤ hi mp mm d →
      Kind T off mp mm ⟨H d, .pl s₂, .ctr (lo mp d) s₂, opp d, .go (A (opp d))⟩
  | r3 (d : Dir) (i : Nat) (t : S) : (d = .L ∨ d = .R) → lo mp d < i → i ≤ hi mp mm d →
      Kind T off mp mm ⟨A (opp d), .ctr i t, .ctr (i - 1) t, d, .go (A d)⟩
  | r4 (d : Dir) (t : S) : (d = .L ∨ d = .R) → lo mp d ≤ hi mp mm d →
      Kind T off mp mm ⟨A (opp d), .ctr (lo mp d) t, .pl t, d, .go (H d)⟩
  | r5 (d : Dir) (j : Nat) (s₂ : S) : (d = .L ∨ d = .R) → lo mp d ≤ j → j < hi mp mm d →
      Kind T off mp mm ⟨A d, .ctr j s₂, .ctr (j + 1) s₂, opp d, .go (A (opp d))⟩

variable {T : Machine Q P S} {off : Q → Nat} {mp mm : Nat} {ss : List S}

theorem mem_shuttle {d : Dir} (hd : d = .L ∨ d = .R) {ρ : Rule KSt P (KSym S)}
    (h : ρ ∈ shuttle mp mm ss d) : Kind T off mp mm ρ := by
  unfold shuttle at h
  split at h
  · rename_i hlh
    simp only [List.mem_append, List.mem_map, List.mem_flatMap, List.mem_range'_1] at h
    rcases h with ((⟨s₂, _, rfl⟩ | ⟨i, ⟨h1, h2⟩, t, _, rfl⟩) | ⟨t, _, rfl⟩) | ⟨j, ⟨h1, h2⟩, s₂, _, rfl⟩
    · exact Kind.r2 d s₂ hd hlh
    · exact Kind.r3 d i t hd (by omega) (by omega)
    · exact Kind.r4 d t hd hlh
    · exact Kind.r5 d j s₂ hd h1 (by omega)
  · simp at h

theorem kind_of_mem (hW : ZeroShiftHalts T) {ρ : Rule KSt P (KSym S)}
    (h : ρ ∈ convWith T off mp mm ss) : Kind T off mp mm ρ := by
  unfold convWith at h
  simp only [List.mem_append, List.mem_map] at h
  rcases h with (⟨r, hr, rfl⟩ | h) | h
  · obtain ⟨p, s, t, d, q⟩ := r
    cases q with
    | go q =>
      have hd : d = .L ∨ d = .R := go_dir_LR hW hr rfl
      exact Kind.r1go p s t d q hr hd
    | halt h => exact Kind.r1halt p s t d h hr
  · exact mem_shuttle (.inr rfl) h
  · exact mem_shuttle (.inl rfl) h

theorem mem_of_kind (hS : ∀ s, s ∈ ss) {ρ : Rule KSt P (KSym S)}
    (h : Kind T off mp mm ρ) : ρ ∈ convWith T off mp mm ss := by
  unfold convWith
  simp only [List.mem_append]
  have hsh : ∀ d, (d = .L ∨ d = .R) → ρ ∈ shuttle mp mm ss d →
      (ρ ∈ T.map (rule1 T off) ∨ ρ ∈ shuttle mp mm ss .R) ∨ ρ ∈ shuttle mp mm ss .L := by
    rintro d (rfl | rfl) h
    · exact .inr h
    · exact .inl (.inr h)
  cases h with
  | r1go p s t d q hr _ =>
    refine .inl (.inl (List.mem_map.2 ⟨_, hr, ?_⟩))
    simp [rule1]
  | r1halt p s t d h hr =>
    refine .inl (.inl (List.mem_map.2 ⟨_, hr, ?_⟩))
    simp [rule1]
  | r2 d s₂ hd hlh =>
    apply hsh d hd
    unfold shuttle; rw [if_pos hlh]
    simp only [List.mem_append, List.mem_map]
    exact .inl (.inl (.inl ⟨s₂, hS _, rfl⟩))
  | r3 d i t hd h1 h2 =>
    apply hsh d hd
    unfold shuttle; rw [if_pos (by omega)]
    simp only [List.mem_append, List.mem_map, List.mem_flatMap, List.mem_range'_1]
    exact .inl (.inl (.inr ⟨i, ⟨by omega, by omega⟩, t, hS _, rfl⟩))
  | r4 d t hd hlh =>
    apply hsh d hd
    unfold shuttle; rw [if_pos hlh]
    simp only [List.mem_append, List.mem_map]
    exact .inl (.inr ⟨t, hS _, rfl⟩)
  | r5 d j s₂ hd h1 h2 =>
    apply hsh d hd
    unfold shuttle; rw [if_pos (by omega)]
    simp only [List.mem_append, List.mem_map, List.mem_flatMap, List.mem_range'_1]
    exact .inr ⟨j, ⟨h1, by omega⟩, s₂, hS _, rfl⟩

/-! ## 4. (a) 決定性と可逆性の保存 -/

omit [DecidableEq Q] [DecidableEq P] in
theorem detT_eq (hD : Deterministic T) {r r' : Rule Q P S} (hr : r ∈ T) (hr' : r' ∈ T)
    (hp : r.p = r'.p) (hs : r.s = r'.s) : r = r' := by
  by_cases h : r = r'
  · exact h
  · exact absurd hs (hD r hr r' hr' h hp)

omit [DecidableEq Q] [DecidableEq P] in
theorem revT_eq (hR : Reversible T) {r r' : Rule Q P S} (hr : r ∈ T) (hr' : r' ∈ T)
    (hq : r.q = r'.q) (ht : r.t = r'.t) : r = r' := by
  by_cases h : r = r'
  · exact h
  · exact absurd ht (hR r hr r' hr' h hq).2

theorem convWith_det (hW : ZeroShiftHalts T) (hD : Deterministic T)
    (hinj : ∀ a b, off a = off b → a = b) : Deterministic (convWith T off mp mm ss) := by
  intro a ha b hb hne hp hs
  have ka := kind_of_mem hW ha
  have kb := kind_of_mem hW hb
  clear ha hb
  rcases ka with ⟨p, s, t, d, q, hr, (rfl | rfl)⟩ | ⟨p, s, t, d, ph, hr⟩ | ⟨d, s₂, (rfl | rfl), hlh⟩ |
      ⟨d, i, t, (rfl | rfl), h1, h2⟩ | ⟨d, t, (rfl | rfl), hlh⟩ | ⟨d, j, s₂, (rfl | rfl), h1, h2⟩ <;>
  rcases kb with ⟨p', s', t', d', q', hr', (rfl | rfl)⟩ | ⟨p', s', t', d', ph', hr'⟩ |
      ⟨d', s₂', (rfl | rfl), hlh'⟩ | ⟨d', i', t', (rfl | rfl), h1', h2'⟩ | ⟨d', t', (rfl | rfl), hlh'⟩ |
      ⟨d', j', s₂', (rfl | rfl), h1', h2'⟩
  all_goals first
    | (simp only [KSym.ctr.injEq] at hs
       obtain ⟨h1, rfl⟩ := hs
       obtain rfl := hinj _ _ h1
       have := detT_eq hD hr hr' rfl rfl
       simp_all)
    | (simp_all; done)
    | (simp_all; omega)

theorem convWith_rev (hW : ZeroShiftHalts T) (hR : Reversible T)
    (hinj : ∀ a b, off a = off b → a = b) : Reversible (convWith T off mp mm ss) := by
  intro a ha b hb hne hq
  have ka := kind_of_mem hW ha
  have kb := kind_of_mem hW hb
  clear ha hb
  rcases ka with ⟨p, s, t, d, q, hr, (rfl | rfl)⟩ | ⟨p, s, t, d, ph, hr⟩ | ⟨d, s₂, (rfl | rfl), hlh⟩ |
      ⟨d, i, t, (rfl | rfl), h1, h2⟩ | ⟨d, t, (rfl | rfl), hlh⟩ | ⟨d, j, s₂, (rfl | rfl), h1, h2⟩ <;>
  rcases kb with ⟨p', s', t', d', q', hr', (rfl | rfl)⟩ | ⟨p', s', t', d', ph', hr'⟩ |
      ⟨d', s₂', (rfl | rfl), hlh'⟩ | ⟨d', i', t', (rfl | rfl), h1', h2'⟩ | ⟨d', t', (rfl | rfl), hlh'⟩ |
      ⟨d', j', s₂', (rfl | rfl), h1', h2'⟩
  all_goals first
    | -- R1 と R1（行き先が実状態）: T の可逆性
      (refine ⟨by simp_all [H], ?_⟩
       intro ht
       simp only [KSym.ctr.injEq] at ht
       obtain ⟨h1, rfl⟩ := ht
       obtain rfl := hinj _ _ h1
       have := revT_eq hR hr hr' rfl rfl
       simp_all)
    | -- R1' と R1'（行き先が halt）: T の可逆性
      (have hh : ph = ph' := by simpa using hq
       subst hh
       have hne' : (⟨p, s, t, d, .halt ph⟩ : Rule Q P S) ≠ ⟨p', s', t', d', .halt ph⟩ := by
         intro e; simp_all
       have := hR _ hr _ hr' hne' rfl
       simp_all)
    | (simp_all; done)
    | (simp_all; omega)
    | (simp_all; intros; omega)
    | (simp_all; intro h3; exact hne (by omega))

/-! ## 5. (b) 1 ステップの模倣 -/

/-- 往復中のテープ: 元セル `pos` に `α`、行き先 `pos + δ` に `β`、他は素の記号。 -/
def tp (pos δ : Int) (tape : Int → S) (α β : KSym S) : Int → KSym S :=
  fun j => if j = pos then α else if j = pos + δ then β else .pl (tape j)

theorem upd_tp_src {pos δ : Int} {tape : Int → S} {α β : KSym S} (α' : KSym S) :
    upd (tp pos δ tape α β) pos α' = tp pos δ tape α' β := by
  funext j; simp only [upd, tp]; by_cases h : j = pos <;> simp [h]

theorem upd_tp_dst {pos δ : Int} (hδ : δ ≠ 0) {tape : Int → S} {α β : KSym S} (β' : KSym S) :
    upd (tp pos δ tape α β) (pos + δ) β' = tp pos δ tape α β' := by
  funext j; simp only [upd, tp]
  by_cases h : j = pos + δ
  · subst h
    have : pos + δ ≠ pos := by omega
    simp [this]
  · simp [h]

theorem tp_src {pos δ : Int} {tape : Int → S} {α β : KSym S} : tp pos δ tape α β pos = α := by
  simp [tp]

theorem tp_dst {pos δ : Int} (hδ : δ ≠ 0) {tape : Int → S} {α β : KSym S} :
    tp pos δ tape α β (pos + δ) = β := by
  have : pos + δ ≠ pos := by omega
  simp [tp, this]

theorem mv_ne_zero {d : Dir} (hd : d = .L ∨ d = .R) : mv d ≠ 0 := by
  rcases hd with rfl | rfl <;> simp [mv]

theorem mv_opp {d : Dir} : mv (opp d) = - mv d := by
  cases d <;> simp [mv, opp]

omit [DecidableEq Q] [DecidableEq P] in
theorem step_of {T : Machine Q P S} {c c' : Cfg Q P S} {ρ : Rule Q P S} (hρ : ρ ∈ T)
    (hst : c.st = .go ρ.p) (hs : c.tape c.pos = ρ.s) (h1 : c'.st = ρ.q)
    (h2 : c'.pos = c.pos + mv ρ.d) (h3 : c'.tape = upd c.tape c.pos ρ.t) : Step T c c' := by
  refine ⟨ρ, hρ, hst, hs, ?_⟩
  obtain ⟨_, _, _⟩ := c'
  simp only at h1 h2 h3
  subst h1 h2 h3
  rfl

omit [DecidableEq Q] [DecidableEq P] in
/-- **往復の一般形**（定理 A・B とその疎版で共通）。状態 a₀（元セル側）・a₁（行き先側）について、
    R3ᵢ = [a₀, [i,t], [i-1,t], d, a₁]（lo < i ≤ lo+k）と R5ⱼ = [a₁, [j,s₂], [j+1,s₂], opp d, a₀]（b ≤ j < b+k）が
    M にあれば、元セル −1・行き先 +1 を k 回、2k ステップ。 -/
theorem loop_gen {St : Type} {M : Machine St P (KSym S)} {d : Dir} (hd : d = .L ∨ d = .R) (a₀ a₁ : St)
    (pos : Int) (tape : Int → S) (t s₂ : S) (lo : Nat) :
    ∀ k b, (∀ i, lo < i → i ≤ lo + k → (⟨a₀, .ctr i t, .ctr (i - 1) t, d, .go a₁⟩ : Rule St P (KSym S)) ∈ M) →
      (∀ j, b ≤ j → j < b + k → (⟨a₁, .ctr j s₂, .ctr (j + 1) s₂, opp d, .go a₀⟩ : Rule St P (KSym S)) ∈ M) →
      StepN M (2 * k) ⟨.go a₀, pos, tp pos (mv d) tape (.ctr (lo + k) t) (.ctr b s₂)⟩
        ⟨.go a₀, pos, tp pos (mv d) tape (.ctr lo t) (.ctr (b + k) s₂)⟩ := by
  have hδ := mv_ne_zero hd
  intro k
  induction k with
  | zero => intro b _ _; simpa using StepN.refl _
  | succ k ih =>
    intro b h3 h5
    -- R3: 元セル [lo+k+1, t] → [lo+k, t]、方向 d、状態 a₁
    have s1 : Step M ⟨.go a₀, pos, tp pos (mv d) tape (.ctr (lo + (k + 1)) t) (.ctr b s₂)⟩
        ⟨.go a₁, pos + mv d, tp pos (mv d) tape (.ctr (lo + k) t) (.ctr b s₂)⟩ := by
      refine step_of (h3 _ (by omega) (Nat.le_refl _)) rfl (by simp [tp_src]) rfl rfl ?_
      simp only [upd_tp_src]
      congr 2
    -- R5: 行き先 [b, s₂] → [b+1, s₂]、方向 opp d、状態 a₀
    have s2 : Step M ⟨.go a₁, pos + mv d, tp pos (mv d) tape (.ctr (lo + k) t) (.ctr b s₂)⟩
        ⟨.go a₀, pos, tp pos (mv d) tape (.ctr (lo + k) t) (.ctr (b + 1) s₂)⟩ := by
      refine step_of (h5 b (Nat.le_refl _) (by omega)) rfl (by simp [tp_dst hδ]) rfl ?_ ?_
      · simp only [mv_opp]; omega
      · simp only [upd_tp_dst hδ]
    have := StepN.cons s1 (StepN.cons s2 (ih (b + 1) (fun i h1 h2 => h3 i h1 (by omega))
      (fun j h1 h2 => h5 j (by omega) (by omega))))
    rwa [show b + 1 + k = b + (k + 1) by omega, show 2 * k + 1 + 1 = 2 * (k + 1) by omega] at this

omit [DecidableEq Q] [DecidableEq P] in
/-- **実状態へ移る規則 1 本の模倣の一般形**（R1 → R2 → 往復 → R4、3 + 2(c₁ − lo) ステップ）。
    安定状態 h₀ でヘッドに計数記号 [c₀, s]、行き先の安定状態 h₁ で行き先に [c₁, s₂]（lo ≤ c₁）。
    必要な規則は R1・R2・R4 と、往復の R3ᵢ（lo < i ≤ c₁）・R5ⱼ（lo ≤ j < c₁）だけ。 -/
theorem sim_go_gen {St : Type} {M : Machine St P (KSym S)} {d : Dir} (hd : d = .L ∨ d = .R)
    {h₀ h₁ a₀ a₁ : St} {lo c₀ c₁ : Nat} (hlo : lo ≤ c₁) {pos : Int} {tape : Int → S} {t : S}
    (r1 : (⟨h₀, .ctr c₀ (tape pos), .ctr c₁ t, d, .go h₁⟩ : Rule St P (KSym S)) ∈ M)
    (r2 : (⟨h₁, .pl (tape (pos + mv d)), .ctr lo (tape (pos + mv d)), opp d, .go a₀⟩ :
      Rule St P (KSym S)) ∈ M)
    (r3 : ∀ i, lo < i → i ≤ c₁ → (⟨a₀, .ctr i t, .ctr (i - 1) t, d, .go a₁⟩ : Rule St P (KSym S)) ∈ M)
    (r5 : ∀ j, lo ≤ j → j < c₁ → (⟨a₁, .ctr j (tape (pos + mv d)), .ctr (j + 1) (tape (pos + mv d)),
      opp d, .go a₀⟩ : Rule St P (KSym S)) ∈ M)
    (r4 : (⟨a₀, .ctr lo t, .pl t, d, .go h₁⟩ : Rule St P (KSym S)) ∈ M) :
    StepN M (3 + 2 * (c₁ - lo))
      ⟨.go h₀, pos, fun j => if j = pos then .ctr c₀ (tape j) else .pl (tape j)⟩
      ⟨.go h₁, pos + mv d,
        fun j => if j = pos + mv d then .ctr c₁ (upd tape pos t j) else .pl (upd tape pos t j)⟩ := by
  have hδ := mv_ne_zero hd
  generalize hs₂ : tape (pos + mv d) = s₂ at r2 r5
  have e0 : (fun j => if j = pos then KSym.ctr c₀ (tape j) else .pl (tape j)) =
      tp pos (mv d) tape (.ctr c₀ (tape pos)) (.pl s₂) := by
    funext j; simp only [tp]
    by_cases h : j = pos
    · subst h; simp
    · by_cases h' : j = pos + mv d
      · subst h'; simp [h, hs₂]
      · simp [h, h']
  have e1 : (fun j => if j = pos + mv d then KSym.ctr c₁ (upd tape pos t j) else .pl (upd tape pos t j)) =
      tp pos (mv d) tape (.pl t) (.ctr c₁ s₂) := by
    funext j; simp only [tp, upd]
    by_cases h : j = pos + mv d
    · have : j ≠ pos := by omega
      subst h; simp [this, hs₂]
    · by_cases h' : j = pos
      · subst h'; simp [h]
      · simp [h, h']
  rw [e0, e1]
  obtain ⟨k, rfl⟩ : ∃ k, c₁ = lo + k := ⟨c₁ - lo, by omega⟩
  rw [show lo + k - lo = k by omega]
  -- R1: [c₀, s] → [c₁, t]、方向 d、h₁ へ
  have s1 : Step M ⟨.go h₀, pos, tp pos (mv d) tape (.ctr c₀ (tape pos)) (.pl s₂)⟩
      ⟨.go h₁, pos + mv d, tp pos (mv d) tape (.ctr (lo + k) t) (.pl s₂)⟩ :=
    step_of r1 rfl (by simp [tp_src]) rfl rfl (by simp only [upd_tp_src])
  -- R2: 行き先の素の s₂ → [lo, s₂]、方向 opp d、a₀ へ
  have s2 : Step M ⟨.go h₁, pos + mv d, tp pos (mv d) tape (.ctr (lo + k) t) (.pl s₂)⟩
      ⟨.go a₀, pos, tp pos (mv d) tape (.ctr (lo + k) t) (.ctr lo s₂)⟩ :=
    step_of r2 rfl (by simp [tp_dst hδ]) rfl (by simp only [mv_opp]; omega) (by simp only [upd_tp_dst hδ])
  -- 往復 k 回
  have s3 := loop_gen hd a₀ a₁ pos tape t s₂ lo k lo r3 (fun j h1 h2 => r5 j h1 (by omega))
  -- R4: 元セル [lo, t] → t、方向 d、h₁ へ
  have s4 : Step M ⟨.go a₀, pos, tp pos (mv d) tape (.ctr lo t) (.ctr (lo + k) s₂)⟩
      ⟨.go h₁, pos + mv d, tp pos (mv d) tape (.pl t) (.ctr (lo + k) s₂)⟩ :=
    step_of r4 rfl (by simp [tp_src]) rfl rfl (by simp only [upd_tp_src])
  have := StepN.cons s1 (StepN.cons s2 (s3.trans (StepN.single s4)))
  rwa [show 2 * k + 1 + 1 + 1 = 3 + 2 * k by omega] at this

theorem enc_go (p : Q) (pos : Int) (tape : Int → S) (T : Machine Q P S) (off : Q → Nat) :
    enc T off ⟨.go p, pos, tape⟩ =
      ⟨.go (H (dir T p)), pos, fun j => if j = pos then .ctr (off p) (tape j) else .pl (tape j)⟩ :=
  rfl

/-- 実状態へ移る規則 1 本の模倣。3 + 2Δ ステップ。 -/
theorem sim_go (hW : ZeroShiftHalts T) (hR : Reversible T) (hN : GoodNum T off mp mm)
    (hS : ∀ s, s ∈ ss) {p q : Q} {s t : S} {d : Dir}
    (hr : (⟨p, s, t, d, .go q⟩ : Rule Q P S) ∈ T) (pos : Int) (tape : Int → S)
    (hs : tape pos = s) :
    StepN (convWith T off mp mm ss) (3 + 2 * (off q - lo mp (dir T q)))
      (enc T off ⟨.go p, pos, tape⟩) (enc T off ⟨.go q, pos + mv d, upd tape pos t⟩) := by
  have hdq : dir T q = d := dir_eq hW hR hr rfl
  have hd : d = .L ∨ d = .R := go_dir_LR hW hr rfl
  have hrng : lo mp d ≤ off q ∧ off q ≤ hi mp mm d := by
    rcases hd with rfl | rfl
    · have := hN.rngL q hdq; simp; omega
    · have := hN.rngR q hdq; simp; omega
  subst hs
  rw [enc_go, enc_go, hdq]
  exact sim_go_gen hd hrng.1 (mem_of_kind hS (.r1go p _ t d q hr hd)) (mem_of_kind hS (.r2 d _ hd (by omega)))
    (fun i h1 h2 => mem_of_kind hS (.r3 d i t hd h1 (by omega)))
    (fun j h1 h2 => mem_of_kind hS (.r5 d j _ hd h1 (by omega))) (mem_of_kind hS (.r4 d t hd (by omega)))

/-- 停止規則（行き先が `halt`）1 本の模倣。1 ステップ。 -/
theorem sim_halt (hS : ∀ s, s ∈ ss) {p : Q} {s t : S} {d : Dir} {h : P}
    (hr : (⟨p, s, t, d, .halt h⟩ : Rule Q P S) ∈ T) (pos : Int) (tape : Int → S)
    (hs : tape pos = s) :
    StepN (convWith T off mp mm ss) 1
      (enc T off ⟨.go p, pos, tape⟩) (enc T off ⟨.halt h, pos + mv d, upd tape pos t⟩) := by
  have hk := Kind.r1halt (T := T) (off := off) (mp := mp) (mm := mm) p s t d h hr
  refine StepN.single (step_of (mem_of_kind hS hk) rfl (by simp [enc, hs]) rfl rfl ?_)
  funext j; simp only [enc, upd]
  by_cases h : j = pos <;> simp [h]

/-- (b) 模倣: T の任意のステップ c → c' に対し、T' は enc c から
    ちょうど `cost c'` ステップで enc c' に達する。 -/
theorem convWith_simulates (hW : ZeroShiftHalts T) (hR : Reversible T) (hN : GoodNum T off mp mm)
    (hS : ∀ s, s ∈ ss) {c c' : Cfg Q P S} (h : Step T c c') :
    StepN (convWith T off mp mm ss) (cost T off mp c') (enc T off c) (enc T off c') := by
  obtain ⟨⟨p, s, t, d, q⟩, hr, hst, hs, rfl⟩ := h
  obtain ⟨st, pos, tape⟩ := c
  simp only at hst hs
  subst hst
  cases q with
  | go q => exact sim_go hW hR hN hS hr pos tape hs
  | halt h => exact sim_halt hS hr pos tape hs

/-- T が c で止まっているなら、T' も enc c で止まっている。 -/
theorem convWith_halted (hW : ZeroShiftHalts T) (hinj : ∀ a b, off a = off b → a = b)
    {c : Cfg Q P S} (hH : Halted T c) : Halted (convWith T off mp mm ss) (enc T off c) := by
  intro c'' ⟨ρ, hρ, hst, hs, _⟩
  obtain ⟨st, pos, tape⟩ := c
  cases st with
  | halt h => simp [enc] at hst
  | go p =>
    rw [enc_go] at hst hs
    simp at hst hs
    rcases kind_of_mem hW hρ with ⟨p', s', t', d', q', hr, _⟩ | ⟨p', s', t', d', ph', hr⟩ |
        ⟨d', s₂', hd, _⟩ | ⟨d', i', t', hd, _, _⟩ | ⟨d', t', hd, _⟩ | ⟨d', j', s₂', hd, _, _⟩
    · simp only [KSym.ctr.injEq] at hs
      obtain ⟨h1, rfl⟩ := hs
      obtain rfl := hinj _ _ h1
      exact hH _ ⟨_, hr, rfl, rfl, rfl⟩
    · simp only [KSym.ctr.injEq] at hs
      obtain ⟨h1, rfl⟩ := hs
      obtain rfl := hinj _ _ h1
      exact hH _ ⟨_, hr, rfl, rfl, rfl⟩
    · simp at hs
    · simp at hst
    · simp at hst
    · simp at hst

theorem cost_pos {c' : Cfg Q P S} : 1 ≤ cost T off mp c' := by
  unfold cost; split <;> omega

/-! ## 6. (c) 多ステップ -/

theorem convWith_haltsIn (hW : ZeroShiftHalts T) (hR : Reversible T) (hN : GoodNum T off mp mm)
    (hS : ∀ s, s ∈ ss) :
    ∀ {n : Nat} {c cf : Cfg Q P S}, HaltsIn T n c cf →
      ∃ N, n ≤ N ∧ HaltsIn (convWith T off mp mm ss) N (enc T off c) (enc T off cf) :=
  fun h => haltsIn_of_sim _ _ (fun _ => True) (fun _ => cost_pos)
    (fun h₁ _ _ => convWith_simulates hW hR hN hS h₁) (fun hH _ => convWith_halted hW hN.inj hH) h trivial

theorem convWith_haltsIn_rev (hW : ZeroShiftHalts T) (hD : Deterministic T) (hR : Reversible T)
    (hN : GoodNum T off mp mm) (hS : ∀ s, s ∈ ss) :
    ∀ (N : Nat) {c : Cfg Q P S} {e : Cfg KSt P (KSym S)},
      HaltsIn (convWith T off mp mm ss) N (enc T off c) e →
      ∃ n cf, HaltsIn T n c cf ∧ e = enc T off cf :=
  fun N _ _ h => haltsIn_rev_of_sim _ _ (fun _ => True) (convWith_det hW hD hN.inj) (fun _ => cost_pos)
    (fun _ _ => trivial) (fun _ h₁ => convWith_simulates hW hR hN hS h₁)
    (fun _ hH => convWith_halted hW hN.inj hH) N trivial h

/-! ## 7. 標準の番号付けが条件を満たすこと -/

theorem ix_lt {a : Q} : ∀ {l : List Q}, a ∈ l → ix a l < l.length
  | [], h => by cases h
  | x :: xs, h => by
    simp only [ix, List.length_cons]
    by_cases hx : x = a
    · simp [hx]
    · simp only [hx, if_false]
      have : a ∈ xs := by
        cases h with
        | head => exact absurd rfl hx
        | tail _ h => exact h
      have := ix_lt this
      omega

theorem ix_inj {a b : Q} : ∀ {l : List Q}, a ∈ l → b ∈ l → ix a l = ix b l → a = b
  | [], h, _, _ => by cases h
  | x :: xs, ha, hb, h => by
    simp only [ix] at h
    by_cases hxa : x = a <;> by_cases hxb : x = b
    · exact hxa.symm.trans hxb
    · simp [hxa] at h
      all_goals first | exact h | exact h.symm
    · simp [hxb] at h
      all_goals first | exact h | exact h.symm
    · simp only [hxa, hxb, if_false] at h
      have ha' : a ∈ xs := by
        cases ha with
        | head => exact absurd rfl hxa
        | tail _ h => exact h
      have hb' : b ∈ xs := by
        cases hb with
        | head => exact absurd rfl hxb
        | tail _ h => exact h
      exact ix_inj ha' hb' (by omega)

theorem canon_good {qs : List Q} (hQ : ∀ q, q ∈ qs) :
    GoodNum T (canonOff T qs) (plusList T qs).length (minusList T qs).length := by
  have memP : ∀ q, dir T q = .R → q ∈ plusList T qs := fun q h => by
    simp [plusList, List.mem_filter, hQ q, h]
  have memM : ∀ q, dir T q = .L → q ∈ minusList T qs := fun q h => by
    simp [minusList, List.mem_filter, hQ q, h]
  refine ⟨?_, ?_, ?_⟩
  · intro a b h
    unfold canonOff at h
    rcases dir_cases T a with ha | ha <;> rcases dir_cases T b with hb | hb <;>
      simp only [ha, hb, reduceCtorEq, if_false, if_true] at h
    · exact ix_inj (memM a ha) (memM b hb) (by omega)
    · have := ix_lt (memP b hb); omega
    · have := ix_lt (memP a ha); omega
    · exact ix_inj (memP a ha) (memP b hb) (by omega)
  · intro q h
    have := ix_lt (memP q h)
    simp only [canonOff, h, if_true]; omega
  · intro q h
    have := ix_lt (memM q h)
    simp only [canonOff, h, reduceCtorEq, if_false]; omega

theorem plus_minus_length (qs : List Q) :
    (plusList T qs).length + (minusList T qs).length = qs.length := by
  induction qs with
  | nil => rfl
  | cons x xs ih =>
    simp only [plusList, minusList, List.filter_cons] at *
    rcases dir_cases T x with h | h <;> simp [h] <;> omega

/-- T' の記号はすべて素の `pl s` か、`1 ≤ i ≤ m` の計数 `ctr i s`（したがって (m+1)n 記号）。 -/
theorem convWith_symbols (hW : ZeroShiftHalts T) (hN : GoodNum T off mp mm)
    {ρ : Rule KSt P (KSym S)} (hρ : ρ ∈ convWith T off mp mm ss) :
    ∀ σ ∈ [ρ.s, ρ.t], (∃ x, σ = .pl x) ∨ (∃ i x, σ = .ctr i x ∧ 1 ≤ i ∧ i ≤ mp + mm) := by
  have hoff : ∀ q, 1 ≤ off q ∧ off q ≤ mp + mm := fun q => by
    rcases dir_cases T q with h | h
    · have := hN.rngL q h; omega
    · have := hN.rngR q h; omega
  rcases kind_of_mem hW hρ with ⟨p, s, t, d, q, _, _⟩ | ⟨p, s, t, d, ph, _⟩ |
      ⟨d, s₂, (rfl | rfl), hlh⟩ | ⟨d, i, t, (rfl | rfl), h1, h2⟩ | ⟨d, t, (rfl | rfl), hlh⟩ |
      ⟨d, j, s₂, (rfl | rfl), h1, h2⟩ <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] <;> rintro σ (rfl | rfl) <;>
    simp_all [lo, hi] <;> omega

/-! ## 8. 主定理（標準の番号付け） -/

section Main
variable {qs : List Q}

/-- (a) T が決定的かつ可逆 ⇒ T' = conv T qs ss も決定的かつ可逆。 -/
theorem conv_det_rev (hW : ZeroShiftHalts T) (hD : Deterministic T) (hR : Reversible T)
    (hQ : ∀ q, q ∈ qs) :
    Deterministic (conv T qs ss) ∧ Reversible (conv T qs ss) :=
  ⟨convWith_det hW hD (canon_good hQ).inj, convWith_rev hW hR (canon_good hQ).inj⟩

/-- (b) 1 ステップの模倣。Δ = off q − lo(dir q)、実状態へのステップは 3 + 2Δ。 -/
theorem conv_simulates (hW : ZeroShiftHalts T) (hR : Reversible T)
    (hQ : ∀ q, q ∈ qs) (hS : ∀ s, s ∈ ss) {c c' : Cfg Q P S} (h : Step T c c') :
    StepN (conv T qs ss) (cost T (canonOff T qs) (plusList T qs).length c')
      (enc T (canonOff T qs) c) (enc T (canonOff T qs) c') :=
  convWith_simulates hW hR (canon_good hQ) hS h

/-- (b) 停止の対応: T が c で止まる ⇔ T' が enc c で止まる。 -/
theorem conv_halted_iff (hW : ZeroShiftHalts T) (hR : Reversible T)
    (hQ : ∀ q, q ∈ qs) (hS : ∀ s, s ∈ ss) (c : Cfg Q P S) :
    Halted T c ↔ Halted (conv T qs ss) (enc T (canonOff T qs) c) := by
  constructor
  · exact convWith_halted hW (canon_good hQ).inj
  · intro h c' hs
    have := conv_simulates hW hR hQ hS hs
    have hp := cost_pos (T := T) (off := canonOff T qs) (mp := (plusList T qs).length) (c' := c')
    obtain ⟨x, hx⟩ := StepN.first this hp
    exact h x hx

/-- 実状態へのステップの Δ は `m_{dir q} − 1` 以下（Δ ≤ max(m₊, m₋) − 1）。 -/
theorem conv_delta_bound (hQ : ∀ q, q ∈ qs) (q : Q) :
    canonOff T qs q - lo (plusList T qs).length (dir T q) + 1 ≤
      (if dir T q = .R then (plusList T qs).length else (minusList T qs).length) := by
  have hN := canon_good (T := T) hQ
  rcases dir_cases T q with h | h
  · have := hN.rngL q h; simp [h, lo]; omega
  · have := hN.rngR q h; simp [h, lo]; omega

/-- (c ⇒) T が n ステップで停止配置 cf に達するなら、T' は enc c から
    N ≥ n ステップで停止配置 enc cf に達する。 -/
theorem conv_haltsIn (hW : ZeroShiftHalts T) (hR : Reversible T)
    (hQ : ∀ q, q ∈ qs) (hS : ∀ s, s ∈ ss) {n : Nat} {c cf : Cfg Q P S} (h : HaltsIn T n c cf) :
    ∃ N, n ≤ N ∧ HaltsIn (conv T qs ss) N (enc T (canonOff T qs) c) (enc T (canonOff T qs) cf) :=
  convWith_haltsIn hW hR (canon_good hQ) hS h

/-- (c ⇐) T' が enc c から停止配置 e に達するなら、T も c から停止し、e はその符号化。 -/
theorem conv_haltsIn_rev (hW : ZeroShiftHalts T) (hD : Deterministic T) (hR : Reversible T)
    (hQ : ∀ q, q ∈ qs) (hS : ∀ s, s ∈ ss) {N : Nat} {c : Cfg Q P S} {e : Cfg KSt P (KSym S)}
    (h : HaltsIn (conv T qs ss) N (enc T (canonOff T qs) c) e) :
    ∃ n cf, HaltsIn T n c cf ∧ e = enc T (canonOff T qs) cf :=
  convWith_haltsIn_rev hW hD hR (canon_good hQ) hS N h

/-- (c) 停止しないことの保存。 -/
theorem conv_diverges_iff (hW : ZeroShiftHalts T) (hD : Deterministic T) (hR : Reversible T)
    (hQ : ∀ q, q ∈ qs) (hS : ∀ s, s ∈ ss) (c : Cfg Q P S) :
    (∀ n cf, ¬ HaltsIn T n c cf) ↔
      (∀ N e, ¬ HaltsIn (conv T qs ss) N (enc T (canonOff T qs) c) e) :=
  diverges_iff_of (fun _ _ hn => let ⟨N, _, hN⟩ := conv_haltsIn hW hR hQ hS hn; ⟨N, _, hN⟩)
    (fun _ _ he => let ⟨n, cf, hn, _⟩ := conv_haltsIn_rev hW hD hR hQ hS he; ⟨n, cf, hn⟩)

/-- 記号数: T' の記号は素の記号か `1 ≤ i ≤ |qs|` の計数記号（(m+1)n 記号）。 -/
theorem conv_symbols (hW : ZeroShiftHalts T) (hQ : ∀ q, q ∈ qs)
    {ρ : Rule KSt P (KSym S)} (hρ : ρ ∈ conv T qs ss) :
    ∀ σ ∈ [ρ.s, ρ.t], (∃ x, σ = .pl x) ∨ (∃ i x, σ = .ctr i x ∧ 1 ≤ i ∧ i ≤ qs.length) := by
  rw [← plus_minus_length (T := T) qs]
  exact convWith_symbols hW (canon_good hQ) hρ

/-- 記号の全体: 素の記号 n 個と、`1 ≤ i ≤ m` の計数記号 mn 個。 -/
def ctrs (ss : List S) : Nat → List (KSym S)
  | 0 => []
  | m + 1 => ctrs ss m ++ ss.map (.ctr (m + 1))

def symUniverse (m : Nat) (ss : List S) : List (KSym S) := ss.map .pl ++ ctrs ss m

omit [DecidableEq Q] [DecidableEq P] in
theorem symUniverse_length (m : Nat) (ss : List S) :
    (symUniverse m ss).length = (m + 1) * ss.length := by
  unfold symUniverse
  induction m with
  | zero => simp [ctrs]
  | succ m ih => simp only [ctrs, List.length_append, List.length_map] at *; rw [Nat.succ_mul]; omega

omit [DecidableEq Q] [DecidableEq P] in
theorem mem_ctrs {ss : List S} {i : Nat} {x : S} (hx : x ∈ ss) :
    ∀ {m : Nat}, 1 ≤ i → i ≤ m → KSym.ctr i x ∈ ctrs ss m
  | 0, _, h => by omega
  | m + 1, h1, h2 => by
    simp only [ctrs, List.mem_append, List.mem_map]
    by_cases h : i = m + 1
    · exact .inr ⟨x, hx, by rw [h]⟩
    · exact .inl (mem_ctrs hx h1 (by omega))

/-- 記号数: T' の規則に現れる記号はすべて `symUniverse |qs| ss`（(|qs|+1)·|ss| 要素）に入る。 -/
theorem conv_symbols_mem (hW : ZeroShiftHalts T) (hQ : ∀ q, q ∈ qs) (hS : ∀ s, s ∈ ss)
    {ρ : Rule KSt P (KSym S)} (hρ : ρ ∈ conv T qs ss) :
    ρ.s ∈ symUniverse qs.length ss ∧ ρ.t ∈ symUniverse qs.length ss := by
  have h := conv_symbols hW hQ hρ
  have key : ∀ σ ∈ [ρ.s, ρ.t], σ ∈ symUniverse qs.length ss := by
    intro σ hσ
    unfold symUniverse
    rcases h σ hσ with ⟨x, rfl⟩ | ⟨i, x, rfl, h1, h2⟩
    · exact List.mem_append.2 (.inl (List.mem_map.2 ⟨x, hS x, rfl⟩))
    · exact List.mem_append.2 (.inr (mem_ctrs (hS x) h1 h2))
  exact ⟨key _ (by simp), key _ (by simp)⟩

/-- 状態は 4 つ。 -/
theorem KSt_all (x : KSt) : x ∈ [KSt.Hp, .Hm, .Ap, .Am] := by cases x <;> simp

/-- 主定理のまとめ（具体機械への適用用）。 -/
theorem conv_main (hW : ZeroShiftHalts T) (hD : Deterministic T) (hR : Reversible T)
    (hQ : ∀ q, q ∈ qs) (hS : ∀ s, s ∈ ss) :
    Deterministic (conv T qs ss) ∧ Reversible (conv T qs ss) ∧
    (∀ c c' : Cfg Q P S, Step T c c' →
      StepN (conv T qs ss) (cost T (canonOff T qs) (plusList T qs).length c')
        (enc T (canonOff T qs) c) (enc T (canonOff T qs) c')) ∧
    (∀ c : Cfg Q P S, Halted T c ↔ Halted (conv T qs ss) (enc T (canonOff T qs) c)) ∧
    (∀ (n : Nat) (c cf : Cfg Q P S), HaltsIn T n c cf →
      ∃ N, n ≤ N ∧ HaltsIn (conv T qs ss) N (enc T (canonOff T qs) c) (enc T (canonOff T qs) cf)) ∧
    (∀ (N : Nat) (c : Cfg Q P S) (e : Cfg KSt P (KSym S)),
      HaltsIn (conv T qs ss) N (enc T (canonOff T qs) c) e →
      ∃ n cf, HaltsIn T n c cf ∧ e = enc T (canonOff T qs) cf) ∧
    (∀ c : Cfg Q P S, (∀ n cf, ¬ HaltsIn T n c cf) ↔
      (∀ N e, ¬ HaltsIn (conv T qs ss) N (enc T (canonOff T qs) c) e)) ∧
    (∀ ρ ∈ conv T qs ss, ρ.s ∈ symUniverse qs.length ss ∧ ρ.t ∈ symUniverse qs.length ss) :=
  ⟨(conv_det_rev hW hD hR hQ).1, (conv_det_rev hW hD hR hQ).2,
   fun _ _ h => conv_simulates hW hR hQ hS h,
   fun c => conv_halted_iff hW hR hQ hS c,
   fun _ _ _ h => conv_haltsIn hW hR hQ hS h,
   fun _ _ _ h => conv_haltsIn_rev hW hD hR hQ hS h,
   fun c => conv_diverges_iff hW hD hR hQ hS c,
   fun _ h => conv_symbols_mem hW hQ hS h⟩

end Main

end Conv

/-! ## 9. 仮定が空でないことの確認（具体例）

  2 状態・2 記号の小さな決定的可逆機械で、主定理の仮定がすべて成り立つことを `decide` で確かめ、
  生成された T' の決定性・可逆性も `decide` で独立に確かめる（主定理の帰結と一致すること）。 -/

namespace Example

/-- `false` で `false` を読めば `true` を書いて右へ・状態 `true` へ。
    `true` で `false` を読めば `false` を書いて左へ・状態 `false` へ。
    `true` で `true` を読めば 0 シフトで停止。 -/
def T0 : Machine Bool Unit Bool :=
  [⟨false, false, true, .R, .go true⟩,
   ⟨true, false, false, .L, .go false⟩,
   ⟨true, true, true, .Z, .halt ()⟩]

theorem T0_wf : ZeroShiftHalts T0 := by decide
theorem T0_det : Deterministic T0 := by decide
theorem T0_rev : Reversible T0 := by decide

/-- 主定理 (a) の適用。 -/
theorem T0'_det_rev : Deterministic (conv T0 [false, true] [false, true]) ∧
    Reversible (conv T0 [false, true] [false, true]) :=
  conv_det_rev T0_wf T0_det T0_rev (by decide)

/-- 同じ結論をカーネルの `decide` で直接（主定理とは独立に）。 -/
theorem T0'_det_rev_decide : Deterministic (conv T0 [false, true] [false, true]) ∧
    Reversible (conv T0 [false, true] [false, true]) := by
  constructor <;> decide

end Example

end URTM.KState
