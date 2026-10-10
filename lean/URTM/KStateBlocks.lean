/-
  ε 逆向きの計数をブロック分けと役割の任意の併合に広げた変換（docs/22_eps_blocks_2026-09-28.md）の
  一般の模倣証明。`tools/kstate_blocks.py` の `Gen` を関数として書いたもの。

  * T の状態 q は入る向き `dir T q` と、ブロック番号 `blk q` を持つ。ブロック (dir, b) は 3 つの役割
    H・O・D を持ち、役割の併合は写像 `cls : Role → Dir → Nat → Fin k`（同じ値 = 同じ状態）で与える。
    T' の状態は `Fin k`（k 状態以下）。
  * 各状態 q は計数値 `v q` を、各ブロックは番兵 `sg (dir) (b)` を持つ。数える向き ε は
    v q と σ の大小で決まる（v ≥ σ なら ε = +1、v < σ なら ε = −1）。状態ごとに決まるので、
    ブロックの全状態が σ の同じ側にあることも要求しない（Python の表はそうなっている）。
  * 規則（d = dir q、e = opp d、σ = σ_{blk q}、H/O/D は q のブロックの役割の類）:
      R1  [H_{blk p}, [v p, s], [v q, t], d, H_{blk q}]（行き先が疑似状態なら [.., [v p, s], t, d, halt h]）
      R2  [H, s₂, [σ, s₂], e, O]                       s₂ は q が読む記号
      R5  [D, [j, s₂], [j+ε, s₂], e, O]                j は σ から v q の手前まで
      R4  [O, [σ, t], t, d, H]                          t は q に入る規則が書く記号
      R3  [O, [i, t], [i−ε, t], d, D]                  i は σ の次から v q まで
    完全に同じ規則は 1 本にまとめる（`dedupL`、最初の出現を残す）。
  * 衝突の無さは一般には証明しない。**T' が決定的であること**を仮定に置き（具体機械では
    `decide +kernel`）、模倣の各ステップで発火する規則が表にあることを構文的に示す。
    前向き（1 ステップの模倣と停止の前向き）は決定性すら使わない。

  主定理 `bconv_main`（T はゼロシフトが疑似状態にだけ入る可逆機械、T' は決定的）:
  * T の 1 ステップ c → c' は、c' が生きていれば `bcost c'` = 3 + 2|v(q) − σ_{blk q}|（停止規則は 1）
    ステップで benc c → benc c' と模倣される
  * 疑似状態で止まる実行は、同じ停止配置の符号化で止まる（前向き）
  * `NoStuck T c` なら、T' の停止は T の停止に対応し（逆向き）、停止しないことも対応する

  未証明の穴・新規公理・native_decide を使わない。mathlib 非依存。
-/
import URTM.KStateEps

namespace URTM.KStateBlocks

set_option linter.unusedSectionVars false

open URTM (Dir)
open URTM.KState
open URTM.KStateSparse (Live NoStuck live_of_stepN nostuck_step live_of_nostuck)
open URTM.KStateEps (readB writeB readB_of writeB_of readB_next loop_rev sim_go_rev)

variable {Q P S : Type} [DecidableEq Q] [DecidableEq P] [DecidableEq S]

/-! ## 1. 定義 -/

/-- ブロックの役割: H（安定）、O（元セル側の往復）、D（行き先側の往復）。 -/
inductive Role where
  | h
  | o
  | d
  deriving DecidableEq, Repr

/-- ブロック分け・計数値・番兵・役割の併合。 -/
structure BSpec (Q : Type) (k : Nat) where
  blk : Q → Nat
  v : Q → Nat
  sg : Dir → Nat → Nat
  cls : Role → Dir → Nat → Fin k

variable {k : Nat}

/-- q のブロックの役割 r の状態。 -/
def rst (T : Machine Q P S) (sp : BSpec Q k) (r : Role) (q : Q) : Fin k :=
  sp.cls r (dir T q) (sp.blk q)

/-- q のブロックの番兵。 -/
def sgq (T : Machine Q P S) (sp : BSpec Q k) (q : Q) : Nat :=
  sp.sg (dir T q) (sp.blk q)

/-- a から b へ（a を含み b を含まない）。Python の `between(a, b, closed_b=False)`。 -/
def path (a b : Nat) : List Nat :=
  if a ≤ b then List.range' a (b - a) else (List.range' (b + 1) (a - b)).reverse

/-- a の次から b まで（b を含む）。Python の `between(a, b)` から先頭を除いたもの。 -/
def path1 (a b : Nat) : List Nat :=
  if a ≤ b then List.range' (a + 1) (b - a) else (List.range' b (a - b)).reverse

/-- 行き先側の 1 歩（j + ε）。 -/
def fwdv (a b j : Nat) : Nat := if a ≤ b then j + 1 else j - 1

/-- 元セル側の 1 歩（i − ε）。 -/
def bwdv (a b i : Nat) : Nat := if a ≤ b then i - 1 else i + 1

/-- R1 / R1'（T の規則 1 本の実行）。 -/
def brule1 (T : Machine Q P S) (sp : BSpec Q k) (r : Rule Q P S) : Rule (Fin k) P (KSym S) :=
  match r.q with
  | .go q => ⟨rst T sp .h r.p, .ctr (sp.v r.p) r.s, .ctr (sp.v q) r.t, r.d, .go (rst T sp .h q)⟩
  | .halt h => ⟨rst T sp .h r.p, .ctr (sp.v r.p) r.s, .pl r.t, r.d, .halt h⟩

/-- 状態 q へ入るための往復の規則（R2・R5 を読む記号ごとに、R4・R3 を書く記号ごとに）。 -/
def shut (T : Machine Q P S) (sp : BSpec Q k) (ss : List S) (q : Q) : List (Rule (Fin k) P (KSym S)) :=
  (ss.filter (readB T q)).flatMap (fun s₂ =>
    ⟨rst T sp .h q, .pl s₂, .ctr (sgq T sp q) s₂, opp (dir T q), .go (rst T sp .o q)⟩ ::
    (path (sgq T sp q) (sp.v q)).map (fun j =>
      ⟨rst T sp .d q, .ctr j s₂, .ctr (fwdv (sgq T sp q) (sp.v q) j) s₂, opp (dir T q), .go (rst T sp .o q)⟩)) ++
  (ss.filter (writeB T q)).flatMap (fun t =>
    ⟨rst T sp .o q, .ctr (sgq T sp q) t, .pl t, dir T q, .go (rst T sp .h q)⟩ ::
    (path1 (sgq T sp q) (sp.v q)).map (fun i =>
      ⟨rst T sp .o q, .ctr i t, .ctr (bwdv (sgq T sp q) (sp.v q) i) t, dir T q, .go (rst T sp .d q)⟩))

/-- 重複を除く（最初の出現を残す）。 -/
def dedupL {α : Type} [DecidableEq α] : List α → List α
  | [] => []
  | x :: xs => x :: (dedupL xs).filter (fun y => decide (y ≠ x))

/-- **ブロック分け・役割の併合・ε の変換**（関数）。`qs` は往復の規則を置く順の状態の並び、
    `ss` は記号を回る順。 -/
def bconv (T : Machine Q P S) (sp : BSpec Q k) (qs : List Q) (ss : List S) : Machine (Fin k) P (KSym S) :=
  dedupL (T.map (brule1 T sp) ++ qs.flatMap (shut T sp ss))

/-- 配置の符号化。安定配置: 状態 H_{blk p}、ヘッド上のセルだけ計数記号 `[v p, s]`。 -/
def benc (T : Machine Q P S) (sp : BSpec Q k) (c : Cfg Q P S) : Cfg (Fin k) P (KSym S) :=
  match c.st with
  | .go p => ⟨.go (rst T sp .h p), c.pos,
      fun j => if j = c.pos then .ctr (sp.v p) (c.tape j) else .pl (c.tape j)⟩
  | .halt h => ⟨.halt h, c.pos, fun j => .pl (c.tape j)⟩

/-- T の 1 ステップ（行き先配置 `c'`）に要する T' のステップ数: 3 + 2|v q − σ_{blk q}|、停止規則は 1。 -/
def bcost (T : Machine Q P S) (sp : BSpec Q k) (c' : Cfg Q P S) : Nat :=
  match c'.st with
  | .go q => 3 + 2 * ((sp.v q - sgq T sp q) + (sgq T sp q - sp.v q))
  | .halt _ => 1

/-! ## 2. 表に入っている規則 -/

theorem mem_dedupL {α : Type} [DecidableEq α] {a : α} : ∀ {l : List α}, a ∈ dedupL l ↔ a ∈ l
  | [] => by simp [dedupL]
  | x :: xs => by
    simp only [dedupL, List.mem_cons, List.mem_filter, mem_dedupL (l := xs)]
    by_cases h : a = x <;> simp [h]

theorem mem_path_le {a b j : Nat} (h : a ≤ b) : j ∈ path a b ↔ a ≤ j ∧ j < b := by
  unfold path; rw [if_pos h, List.mem_range'_1]; omega

theorem mem_path_gt {a b j : Nat} (h : b < a) : j ∈ path a b ↔ b < j ∧ j ≤ a := by
  unfold path; rw [if_neg (by omega), List.mem_reverse, List.mem_range'_1]; omega

theorem mem_path1_le {a b i : Nat} (h : a ≤ b) : i ∈ path1 a b ↔ a < i ∧ i ≤ b := by
  unfold path1; rw [if_pos h, List.mem_range'_1]; omega

theorem mem_path1_gt {a b i : Nat} (h : b < a) : i ∈ path1 a b ↔ b ≤ i ∧ i < a := by
  unfold path1; rw [if_neg (by omega), List.mem_reverse, List.mem_range'_1]; omega

variable {T : Machine Q P S} {sp : BSpec Q k} {qs : List Q} {ss : List S}

theorem mem_brule1 {r : Rule Q P S} (hr : r ∈ T) : brule1 T sp r ∈ bconv T sp qs ss :=
  mem_dedupL.2 (List.mem_append.2 (.inl (List.mem_map.2 ⟨r, hr, rfl⟩)))

theorem mem_shut (hQ : ∀ q, q ∈ qs) {q : Q} {ρ : Rule (Fin k) P (KSym S)} (h : ρ ∈ shut T sp ss q) :
    ρ ∈ bconv T sp qs ss :=
  mem_dedupL.2 (List.mem_append.2 (.inr (List.mem_flatMap.2 ⟨q, hQ q, h⟩)))

section Shut
variable (hS : ∀ s, s ∈ ss) {q : Q}
include hS

theorem shut_r2 {s₂ : S} (hr : readB T q s₂ = true) :
    (⟨rst T sp .h q, .pl s₂, .ctr (sgq T sp q) s₂, opp (dir T q), .go (rst T sp .o q)⟩ :
      Rule (Fin k) P (KSym S)) ∈ shut T sp ss q := by
  unfold shut
  refine List.mem_append.2 (.inl (List.mem_flatMap.2 ⟨s₂, List.mem_filter.2 ⟨hS s₂, hr⟩, ?_⟩))
  exact List.mem_cons_self

theorem shut_r5 {s₂ : S} (hr : readB T q s₂ = true) {j : Nat} (hj : j ∈ path (sgq T sp q) (sp.v q)) :
    (⟨rst T sp .d q, .ctr j s₂, .ctr (fwdv (sgq T sp q) (sp.v q) j) s₂, opp (dir T q), .go (rst T sp .o q)⟩ :
      Rule (Fin k) P (KSym S)) ∈ shut T sp ss q := by
  unfold shut
  refine List.mem_append.2 (.inl (List.mem_flatMap.2 ⟨s₂, List.mem_filter.2 ⟨hS s₂, hr⟩, ?_⟩))
  exact List.mem_cons_of_mem _ (List.mem_map.2 ⟨j, hj, rfl⟩)

theorem shut_r4 {t : S} (hw : writeB T q t = true) :
    (⟨rst T sp .o q, .ctr (sgq T sp q) t, .pl t, dir T q, .go (rst T sp .h q)⟩ :
      Rule (Fin k) P (KSym S)) ∈ shut T sp ss q := by
  unfold shut
  refine List.mem_append.2 (.inr (List.mem_flatMap.2 ⟨t, List.mem_filter.2 ⟨hS t, hw⟩, ?_⟩))
  exact List.mem_cons_self

theorem shut_r3 {t : S} (hw : writeB T q t = true) {i : Nat} (hi : i ∈ path1 (sgq T sp q) (sp.v q)) :
    (⟨rst T sp .o q, .ctr i t, .ctr (bwdv (sgq T sp q) (sp.v q) i) t, dir T q, .go (rst T sp .d q)⟩ :
      Rule (Fin k) P (KSym S)) ∈ shut T sp ss q := by
  unfold shut
  refine List.mem_append.2 (.inr (List.mem_flatMap.2 ⟨t, List.mem_filter.2 ⟨hS t, hw⟩, ?_⟩))
  exact List.mem_cons_of_mem _ (List.mem_map.2 ⟨i, hi, rfl⟩)

end Shut

/-! ## 3. 1 ステップの模倣 -/

/-- 実状態へ移る規則 1 本の模倣。3 + 2|v q − σ| ステップ。 -/
theorem bsim_go (hW : ZeroShiftHalts T) (hR : Reversible T) (hQ : ∀ q, q ∈ qs) (hS : ∀ s, s ∈ ss)
    {p q : Q} {s t : S} {d : Dir}
    (hr : (⟨p, s, t, d, .go q⟩ : Rule Q P S) ∈ T) (pos : Int) (tape : Int → S)
    (hs : tape pos = s) (hrd : readB T q (tape (pos + mv d)) = true) :
    StepN (bconv T sp qs ss) (bcost T sp ⟨.go q, pos + mv d, upd tape pos t⟩)
      (benc T sp ⟨.go p, pos, tape⟩) (benc T sp ⟨.go q, pos + mv d, upd tape pos t⟩) := by
  have hdq : dir T q = d := dir_eq hW hR hr rfl
  have hd : d = .L ∨ d = .R := go_dir_LR hW hr rfl
  have hw : writeB T q t = true := writeB_of hr
  have r1 : brule1 T sp ⟨p, s, t, d, .go q⟩ ∈ bconv T sp qs ss := mem_brule1 hr
  simp only [brule1] at r1
  subst hs
  have r2 := mem_shut hQ (shut_r2 (sp := sp) hS hrd)
  have r4 := mem_shut hQ (shut_r4 (sp := sp) hS hw)
  have r5 := fun j (hj : j ∈ path (sgq T sp q) (sp.v q)) => mem_shut hQ (shut_r5 (sp := sp) hS hrd hj)
  have r3 := fun i (hi : i ∈ path1 (sgq T sp q) (sp.v q)) => mem_shut hQ (shut_r3 (sp := sp) hS hw hi)
  rw [hdq] at r2 r4 r3 r5
  show StepN _ (3 + 2 * ((sp.v q - sgq T sp q) + (sgq T sp q - sp.v q))) _ _
  by_cases hle : sgq T sp q ≤ sp.v q
  · rw [show sp.v q - sgq T sp q + (sgq T sp q - sp.v q) = sp.v q - sgq T sp q by omega]
    exact sim_go_gen (a₀ := rst T sp .o q) (a₁ := rst T sp .d q) hd hle r1 r2
      (fun i h1 h2 => by
        have := r3 i ((mem_path1_le hle).2 ⟨h1, h2⟩); simpa [bwdv, hle] using this)
      (fun j h1 h2 => by
        have := r5 j ((mem_path_le hle).2 ⟨h1, h2⟩); simpa [fwdv, hle] using this)
      r4
  · have hlt : sp.v q < sgq T sp q := by omega
    rw [show sp.v q - sgq T sp q + (sgq T sp q - sp.v q) = sgq T sp q - sp.v q by omega]
    exact sim_go_rev (a₀ := rst T sp .o q) (a₁ := rst T sp .d q) hd (Nat.le_of_lt hlt) r1 r2
      (fun i h1 h2 => by
        have := r3 i ((mem_path1_gt hlt).2 ⟨h1, h2⟩); simpa [bwdv, hle] using this)
      (fun j h1 h2 => by
        have := r5 j ((mem_path_gt hlt).2 ⟨h1, h2⟩); simpa [fwdv, hle] using this)
      r4

/-- 停止規則（行き先が `halt`）1 本の模倣。1 ステップ。 -/
theorem bsim_halt {p : Q} {s t : S} {d : Dir} {h : P}
    (hr : (⟨p, s, t, d, .halt h⟩ : Rule Q P S) ∈ T) (pos : Int) (tape : Int → S)
    (hs : tape pos = s) :
    StepN (bconv T sp qs ss) 1
      (benc T sp ⟨.go p, pos, tape⟩) (benc T sp ⟨.halt h, pos + mv d, upd tape pos t⟩) := by
  have r1 : brule1 T sp ⟨p, s, t, d, .halt h⟩ ∈ bconv T sp qs ss := mem_brule1 hr
  simp only [brule1] at r1
  refine StepN.single (step_of r1 rfl (by simp [benc, hs]) rfl rfl ?_)
  funext j; simp only [benc, upd]
  by_cases h : j = pos <;> simp [h]

/-- 模倣: T のステップ c → c' で c' が生きているなら、T' は benc c からちょうど `bcost c'` ステップで
    benc c' に達する。 -/
theorem bconv_simulates (hW : ZeroShiftHalts T) (hR : Reversible T) (hQ : ∀ q, q ∈ qs)
    (hS : ∀ s, s ∈ ss) {c c' : Cfg Q P S} (h : Step T c c') (hl : Live T c') :
    StepN (bconv T sp qs ss) (bcost T sp c') (benc T sp c) (benc T sp c') := by
  obtain ⟨⟨p, s, t, d, q⟩, hr, hst, hs, rfl⟩ := h
  obtain ⟨st, pos, tape⟩ := c
  simp only at hst hs
  subst hst
  cases q with
  | go q => exact bsim_go hW hR hQ hS hr pos tape hs (readB_next hW hr hl)
  | halt h => exact bsim_halt hr pos tape hs

/-- 疑似状態の配置の符号化は、どの機械でも止まっている。 -/
theorem benc_halted {M : Machine (Fin k) P (KSym S)} {c : Cfg Q P S} (hc : ∃ h, c.st = .halt h) :
    Halted M (benc T sp c) := by
  obtain ⟨h, hh⟩ := hc
  intro c'' ⟨ρ, _, hst, _⟩
  obtain ⟨st, pos, tape⟩ := c
  simp only at hh
  subst hh
  simp [benc] at hst

theorem bcost_pos {c' : Cfg Q P S} : 1 ≤ bcost T sp c' := by
  unfold bcost; split <;> omega

/-! ## 4. 多ステップ -/

theorem bconv_haltsIn (hW : ZeroShiftHalts T) (hR : Reversible T) (hQ : ∀ q, q ∈ qs)
    (hS : ∀ s, s ∈ ss) :
    ∀ {n : Nat} {c cf : Cfg Q P S}, HaltsIn T n c cf → (∃ h, cf.st = .halt h) →
      ∃ N, n ≤ N ∧ HaltsIn (bconv T sp qs ss) N (benc T sp c) (benc T sp cf) :=
  haltsIn_of_sim _ _ _ (fun _ => bcost_pos)
    (fun h₁ hH hf => bconv_simulates hW hR hQ hS h₁ (live_of_stepN hH.1 hf))
    (fun _ hf => benc_halted hf)

theorem bconv_haltsIn_rev (hW : ZeroShiftHalts T) (hR : Reversible T) (hQ : ∀ q, q ∈ qs)
    (hS : ∀ s, s ∈ ss) (hD' : Deterministic (bconv T sp qs ss)) :
    ∀ (N : Nat) {c : Cfg Q P S} {e : Cfg (Fin k) P (KSym S)}, NoStuck T c →
      HaltsIn (bconv T sp qs ss) N (benc T sp c) e →
      ∃ n cf, HaltsIn T n c cf ∧ e = benc T sp cf :=
  haltsIn_rev_of_sim _ _ (NoStuck T) hD'
    (fun _ => bcost_pos) nostuck_step
    (fun hns h₁ => bconv_simulates hW hR hQ hS h₁ (live_of_nostuck (nostuck_step hns h₁)))
    (fun hns hH => benc_halted (hns 0 _ ⟨.refl _, hH⟩))

/-! ## 5. 主定理 -/

/-- **ブロック分け・役割の併合・ε の変換の主定理**（具体機械への適用用）。E = benc T sp。
    T はゼロシフトが疑似状態にだけ入る可逆機械、`qs`・`ss` は状態・記号を尽くす並び。
    仮定 `hD'`（T' が決定的）は具体機械ではカーネルの `decide` で確かめる。
    1. 生きている行き先への 1 ステップは `bcost` = 3 + 2|v(q) − σ_{blk q}| ステップで模倣
    2. 疑似状態で止まる実行は、E で対応する配置で止まる（前向き）
    3. `NoStuck T c` なら、T' の停止は T の停止に対応（逆向き）
    4. `NoStuck T c` なら、停止しないことが対応 -/
theorem bconv_main (hW : ZeroShiftHalts T) (hR : Reversible T) (hQ : ∀ q, q ∈ qs)
    (hS : ∀ s, s ∈ ss) (hD' : Deterministic (bconv T sp qs ss)) :
    (∀ c c' : Cfg Q P S, Step T c c' → Live T c' →
      StepN (bconv T sp qs ss) (bcost T sp c') (benc T sp c) (benc T sp c')) ∧
    (∀ (n : Nat) (c cf : Cfg Q P S), HaltsIn T n c cf → (∃ h, cf.st = .halt h) →
      ∃ N, n ≤ N ∧ HaltsIn (bconv T sp qs ss) N (benc T sp c) (benc T sp cf)) ∧
    (∀ (N : Nat) (c : Cfg Q P S) (e : Cfg (Fin k) P (KSym S)), NoStuck T c →
      HaltsIn (bconv T sp qs ss) N (benc T sp c) e →
      ∃ n cf, HaltsIn T n c cf ∧ e = benc T sp cf) ∧
    (∀ c : Cfg Q P S, NoStuck T c → ((∀ n cf, ¬ HaltsIn T n c cf) ↔
      (∀ N e, ¬ HaltsIn (bconv T sp qs ss) N (benc T sp c) e))) := by
  refine ⟨fun _ _ h hl => bconv_simulates hW hR hQ hS h hl,
    fun _ _ _ h hf => bconv_haltsIn hW hR hQ hS h hf,
    fun N _ _ hns h => bconv_haltsIn_rev hW hR hQ hS hD' N hns h, ?_⟩
  intro c hns
  exact diverges_iff_of
    (fun n cf hn => let ⟨N, _, hN'⟩ := bconv_haltsIn (sp := sp) hW hR hQ hS hn (hns n cf hn); ⟨N, _, hN'⟩)
    (fun N e he => let ⟨n, cf, hn, _⟩ := bconv_haltsIn_rev hW hR hQ hS hD' N hns he; ⟨n, cf, hn⟩)

end URTM.KStateBlocks
