/-
  「ε 逆向き」の 4 状態化（docs/20_five_state_2026-09-28.md §3）の一般の模倣証明。

  定理 A（`KState.lean` の `conv`）と同じ 4 状態 `Hp Hm Ap Am` と計数記号 `[i, s]` を使うが、
  2 方向の計数を**逆向きに**数える（ε₊ = +1, ε₋ = −1）。番兵は σ₊ = 1（最小）、σ₋ = M（最大）、
  計数値は両方向とも共有の範囲 1..M（M = max(m₊, m₋)）に置く。

  * R1  [H (dir p), [v p, s], [v q, t], d, H d]（行き先が疑似状態なら [H (dir p), [v p, s], t, d, halt h]）
  * R2⁺ [Hp, s, [1, s], L, Am]        R2⁻ [Hm, s, [M, s], R, Ap]
  * R4⁺ [Am, [1, t], t, R, Hp]        R4⁻ [Ap, [M, t], t, L, Hm]
  * dec [Am, [i, x], [i−1, x], R, Ap]（2 ≤ i ≤ M）= R3⁺（O⁺ の減算）= R5⁻（D⁻ の減算）
  * inc [Ap, [j, x], [j+1, x], L, Am]（1 ≤ j < M）= R5⁺（D⁺ の加算）= R3⁻（O⁻ の加算）
  逆向きに数えるので O⁺ と D⁻（D⁺ と O⁻）の規則が**同じ規則**になり、範囲を分けずに済む。
  記号は (M+1)·n（(10,8) では 6·8 = 48）。

  規則は、仮定 `nd : Slot → S → Bool` が真のものだけを置く（`econvWith`）。標準の `econv T qs ss` は
  構文的に要るもの（`tools/kstate5.py` の k4・ε₋ = −1 と同じ基準）だけを置く疎な版で、
  模倣は T の実行が疑似状態以外で止まらない（`NoStuck`）ことを仮定する（`KStateSparse` と同じ形）。

  主定理 `econv_main`:
  * 決定的・可逆
  * T の 1 ステップ c → c' は、c' が生きていれば `ecost c'` = 3 + 2|v(q) − σ_{dir q}|（停止規則は 1）
    ステップで enc c → enc c' と模倣される
  * 疑似状態で止まる実行は、同じ停止配置の符号化で止まる（前向き）
  * `NoStuck T c` なら、T' の停止は T の停止に対応し（逆向き）、停止しないことも対応する
  * 規則の記号は `symUniverse (emax T qs) ss`（長さ (max(m₊, m₋) + 1)·|ss|）に入る

  未証明の穴・新規公理・native_decide を使わない。mathlib 非依存。
-/
import URTM.KStateSparse

namespace URTM.KStateEps

set_option linter.unusedSectionVars false

open URTM (Dir)
open URTM.KState
open URTM.KStateSparse (Live NoStuck live_of_stepN nostuck_step live_of_nostuck)

variable {Q P S : Type} [DecidableEq Q] [DecidableEq P] [DecidableEq S]

/-! ## 1. 定義 -/

/-- 往復の規則の種類（記号ごとに 1 本）。 -/
inductive Slot where
  | r2p
  | r2m
  | r4p
  | r4m
  | dec (i : Nat)
  | inc (j : Nat)
  deriving DecidableEq, Repr

/-- 種類 `k` の、記号 `x` についての規則。 -/
def slotRule (M : Nat) : Slot → S → Rule KSt P (KSym S)
  | .r2p, x => ⟨.Hp, .pl x, .ctr 1 x, .L, .go .Am⟩
  | .r2m, x => ⟨.Hm, .pl x, .ctr M x, .R, .go .Ap⟩
  | .r4p, x => ⟨.Am, .ctr 1 x, .pl x, .R, .go .Hp⟩
  | .r4m, x => ⟨.Ap, .ctr M x, .pl x, .L, .go .Hm⟩
  | .dec i, x => ⟨.Am, .ctr i x, .ctr (i - 1) x, .R, .go .Ap⟩
  | .inc j, x => ⟨.Ap, .ctr j x, .ctr (j + 1) x, .L, .go .Am⟩

/-- 種類の並び（M = 0 なら往復の規則は置かない）。 -/
def slots (M : Nat) : List Slot :=
  if M = 0 then []
  else [.r2p, .r2m, .r4p, .r4m] ++ (List.range' 2 (M - 1)).map .dec ++ (List.range' 1 (M - 1)).map .inc

/-- 番号付け `off`・計数の最大値 `M`・残す規則の選択 `nd` を与えた変換。 -/
def econvWith (T : Machine Q P S) (off : Q → Nat) (M : Nat) (ss : List S) (nd : Slot → S → Bool) :
    Machine KSt P (KSym S) :=
  T.map (rule1 T off) ++ (slots M).flatMap (fun k => (ss.filter (nd k)).map (slotRule M k))

/-- q で s を読む規則がある。 -/
def readB (T : Machine Q P S) (q : Q) (s : S) : Bool :=
  T.any (fun r => decide (r.p = q) && decide (r.s = s))

/-- q に入る規則が t を書く。 -/
def writeB (T : Machine Q P S) (q : Q) (t : S) : Bool :=
  T.any (fun r => decide (r.q = .go q) && decide (r.t = t))

/-- 構文的に要る規則（`tools/kstate5.py` の R2〜R5 の基準。dec・inc は 2 つの役割のどちらかで要れば置く）。 -/
def enb (T : Machine Q P S) (off : Q → Nat) (qs : List Q) : Slot → S → Bool
  | .r2p, x => qs.any (fun q => decide (dir T q = .R) && readB T q x)
  | .r2m, x => qs.any (fun q => decide (dir T q = .L) && readB T q x)
  | .r4p, x => qs.any (fun q => decide (dir T q = .R) && writeB T q x)
  | .r4m, x => qs.any (fun q => decide (dir T q = .L) && writeB T q x)
  | .dec i, x => qs.any (fun q =>
      (decide (dir T q = .R) && decide (i ≤ off q) && writeB T q x) ||
      (decide (dir T q = .L) && decide (off q < i) && readB T q x))
  | .inc j, x => qs.any (fun q =>
      (decide (dir T q = .R) && decide (j < off q) && readB T q x) ||
      (decide (dir T q = .L) && decide (off q ≤ j) && writeB T q x))

/-- 計数の最大値 M = max(m₊, m₋)。 -/
def emax (T : Machine Q P S) (qs : List Q) : Nat :=
  max (plusList T qs).length (minusList T qs).length

/-- 標準の番号付け: Q₊ は `1, 2, …, m₊`（下から）、Q₋ は `M, M−1, …, M−m₋+1`（上から）。 -/
def ecanonOff (T : Machine Q P S) (qs : List Q) (q : Q) : Nat :=
  if dir T q = .R then ix q (plusList T qs) + 1 else emax T qs - ix q (minusList T qs)

/-- **ε 逆向きの 4 状態化**（構文的に要る規則だけを置く版、関数）。 -/
def econv (T : Machine Q P S) (qs : List Q) (ss : List S) : Machine KSt P (KSym S) :=
  econvWith T (ecanonOff T qs) (emax T qs) ss (enb T (ecanonOff T qs) qs)

/-- T の 1 ステップ（行き先配置 `c'`）に要する T' のステップ数。
    Q₊ へ: 3 + 2(v q − 1)、Q₋ へ: 3 + 2(M − v q)、停止規則は 1。 -/
def ecost (T : Machine Q P S) (off : Q → Nat) (M : Nat) (c' : Cfg Q P S) : Nat :=
  match c'.st with
  | .go q => if dir T q = .R then 3 + 2 * (off q - 1) else 3 + 2 * (M - off q)
  | .halt _ => 1

/-- 番号付けの条件（向きごとに単射、値は 1..M）。 -/
structure EGood (T : Machine Q P S) (off : Q → Nat) (M : Nat) : Prop where
  inj : ∀ a b, dir T a = dir T b → off a = off b → a = b
  rng : ∀ q, 1 ≤ off q ∧ off q ≤ M

/-! ## 2. 規則の分類 -/

inductive EKind (T : Machine Q P S) (off : Q → Nat) (M : Nat) : Rule KSt P (KSym S) → Prop
  | r1go (p : Q) (s t : S) (d : Dir) (q : Q) :
      (⟨p, s, t, d, .go q⟩ : Rule Q P S) ∈ T → (d = .L ∨ d = .R) → dir T q = d →
      EKind T off M ⟨H (dir T p), .ctr (off p) s, .ctr (off q) t, d, .go (H d)⟩
  | r1halt (p : Q) (s t : S) (d : Dir) (h : P) :
      (⟨p, s, t, d, .halt h⟩ : Rule Q P S) ∈ T →
      EKind T off M ⟨H (dir T p), .ctr (off p) s, .pl t, d, .halt h⟩
  | r2p (x : S) : 1 ≤ M → EKind T off M ⟨.Hp, .pl x, .ctr 1 x, .L, .go .Am⟩
  | r2m (x : S) : 1 ≤ M → EKind T off M ⟨.Hm, .pl x, .ctr M x, .R, .go .Ap⟩
  | r4p (x : S) : 1 ≤ M → EKind T off M ⟨.Am, .ctr 1 x, .pl x, .R, .go .Hp⟩
  | r4m (x : S) : 1 ≤ M → EKind T off M ⟨.Ap, .ctr M x, .pl x, .L, .go .Hm⟩
  | dec (i : Nat) (x : S) : 2 ≤ i → i ≤ M → EKind T off M ⟨.Am, .ctr i x, .ctr (i - 1) x, .R, .go .Ap⟩
  | inc (j : Nat) (x : S) : 1 ≤ j → j < M → EKind T off M ⟨.Ap, .ctr j x, .ctr (j + 1) x, .L, .go .Am⟩

/-- 種類 `k` が並びに入っている条件。 -/
def SlotOK (M : Nat) : Slot → Prop
  | .dec i => 2 ≤ i ∧ i ≤ M
  | .inc j => 1 ≤ j ∧ j < M
  | _ => 1 ≤ M

theorem mem_slots {M : Nat} {k : Slot} : k ∈ slots M ↔ SlotOK M k := by
  unfold slots
  by_cases hM : M = 0
  · subst hM; cases k <;> simp [SlotOK] <;> omega
  · rw [if_neg hM]
    cases k <;> simp [SlotOK, List.mem_range'_1] <;> omega

variable {T : Machine Q P S} {off : Q → Nat} {M : Nat} {ss : List S} {nd : Slot → S → Bool}

theorem ekind_slot {k : Slot} (hk : SlotOK M k) (x : S) : EKind T off M (slotRule M k x) := by
  cases k with
  | r2p => exact .r2p x hk
  | r2m => exact .r2m x hk
  | r4p => exact .r4p x hk
  | r4m => exact .r4m x hk
  | dec i => exact .dec i x hk.1 hk.2
  | inc j => exact .inc j x hk.1 hk.2

theorem ekind_of_mem (hW : ZeroShiftHalts T) (hR : Reversible T) {ρ : Rule KSt P (KSym S)}
    (h : ρ ∈ econvWith T off M ss nd) : EKind T off M ρ := by
  unfold econvWith at h
  simp only [List.mem_append, List.mem_map, List.mem_flatMap, List.mem_filter] at h
  rcases h with ⟨r, hr, rfl⟩ | ⟨k, hk, x, _, rfl⟩
  · obtain ⟨p, s, t, d, q⟩ := r
    cases q with
    | go q =>
      have hd : d = .L ∨ d = .R := go_dir_LR hW hr rfl
      exact EKind.r1go p s t d q hr hd (dir_eq hW hR hr rfl)
    | halt h => exact EKind.r1halt p s t d h hr
  · exact ekind_slot (mem_slots.1 hk) x

theorem mem_rule1 {r : Rule Q P S} (hr : r ∈ T) : rule1 T off r ∈ econvWith T off M ss nd :=
  List.mem_append.2 (.inl (List.mem_map.2 ⟨r, hr, rfl⟩))

theorem mem_slot (hS : ∀ s, s ∈ ss) {k : Slot} (hk : SlotOK M k) {x : S} (hx : nd k x = true) :
    slotRule M k x ∈ econvWith T off M ss nd := by
  unfold econvWith
  refine List.mem_append.2 (.inr (List.mem_flatMap.2 ⟨k, mem_slots.2 hk, ?_⟩))
  exact List.mem_map.2 ⟨x, List.mem_filter.2 ⟨hS x, hx⟩, rfl⟩

/-! ## 3. 決定性と可逆性 -/

theorem H_dir_inj {a b : Q} (h : H (dir T a) = H (dir T b)) : dir T a = dir T b := by
  rcases dir_cases T a with ha | ha <;> rcases dir_cases T b with hb | hb <;>
    rw [ha, hb] at h ⊢ <;> first | rfl | cases h

theorem econvWith_det (hW : ZeroShiftHalts T) (hD : Deterministic T) (hR : Reversible T)
    (hinj : ∀ a b, dir T a = dir T b → off a = off b → a = b) :
    Deterministic (econvWith T off M ss nd) := by
  intro a ha b hb hne hp hs
  have ka := ekind_of_mem hW hR ha
  have kb := ekind_of_mem hW hR hb
  clear ha hb
  rcases ka with ⟨p, s, t, d, q, hr, (rfl | rfl), hq⟩ | ⟨p, s, t, d, ph, hr⟩ | ⟨x, hM⟩ | ⟨x, hM⟩ |
      ⟨x, hM⟩ | ⟨x, hM⟩ | ⟨i, x, h1, h2⟩ | ⟨j, x, h1, h2⟩ <;>
  rcases kb with ⟨p', s', t', d', q', hr', (rfl | rfl), hq'⟩ | ⟨p', s', t', d', ph', hr'⟩ | ⟨x', hM'⟩ |
      ⟨x', hM'⟩ | ⟨x', hM'⟩ | ⟨x', hM'⟩ | ⟨i', x', h1', h2'⟩ | ⟨j', x', h1', h2'⟩
  all_goals first
    | (simp only [KSym.ctr.injEq] at hs
       obtain ⟨h1, rfl⟩ := hs
       obtain rfl := hinj _ _ (H_dir_inj hp) h1
       have := detT_eq hD hr hr' rfl rfl
       simp_all)
    | (simp_all; done)
    | (simp_all; omega)
    | (simp_all [H]; done)
    | (revert hp; rcases dir_cases T p with h | h <;> simp [h, H])
    | (revert hp; rcases dir_cases T p' with h | h <;> simp [h, H])

theorem econvWith_rev (hW : ZeroShiftHalts T) (hR : Reversible T)
    (hinj : ∀ a b, dir T a = dir T b → off a = off b → a = b) :
    Reversible (econvWith T off M ss nd) := by
  intro a ha b hb hne hq
  have ka := ekind_of_mem hW hR ha
  have kb := ekind_of_mem hW hR hb
  clear ha hb
  rcases ka with ⟨p, s, t, d, q, hr, (rfl | rfl), hdq⟩ | ⟨p, s, t, d, ph, hr⟩ | ⟨x, hM⟩ | ⟨x, hM⟩ |
      ⟨x, hM⟩ | ⟨x, hM⟩ | ⟨i, x, h1, h2⟩ | ⟨j, x, h1, h2⟩ <;>
  rcases kb with ⟨p', s', t', d', q', hr', (rfl | rfl), hdq'⟩ | ⟨p', s', t', d', ph', hr'⟩ | ⟨x', hM'⟩ |
      ⟨x', hM'⟩ | ⟨x', hM'⟩ | ⟨x', hM'⟩ | ⟨i', x', h1', h2'⟩ | ⟨j', x', h1', h2'⟩
  all_goals first
    | -- R1 と R1（行き先が実状態、同じ方向）: T の可逆性
      (refine ⟨rfl, ?_⟩
       intro ht
       simp only [KSym.ctr.injEq] at ht
       obtain ⟨h1, rfl⟩ := ht
       obtain rfl := hinj _ _ (hdq.trans hdq'.symm) h1
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

/-! ## 4. 1 ステップの模倣 -/

omit [DecidableEq Q] [DecidableEq P] [DecidableEq S] in
/-- **往復の逆向き版**（元セルを x から x+k へ +1 ずつ、行き先を b+k から b へ −1 ずつ、2k ステップ）。
    R3ᵢ = [a₀, [i,t], [i+1,t], d, a₁]（x ≤ i < x+k）、R5ⱼ = [a₁, [j,s₂], [j−1,s₂], opp d, a₀]（b < j ≤ b+k）。 -/
theorem loop_rev {St : Type} {Mc : Machine St P (KSym S)} {d : Dir} (hd : d = .L ∨ d = .R) (a₀ a₁ : St)
    (pos : Int) (tape : Int → S) (t s₂ : S) :
    ∀ k x b, (∀ i, x ≤ i → i < x + k → (⟨a₀, .ctr i t, .ctr (i + 1) t, d, .go a₁⟩ : Rule St P (KSym S)) ∈ Mc) →
      (∀ j, b < j → j ≤ b + k → (⟨a₁, .ctr j s₂, .ctr (j - 1) s₂, opp d, .go a₀⟩ : Rule St P (KSym S)) ∈ Mc) →
      StepN Mc (2 * k) ⟨.go a₀, pos, tp pos (mv d) tape (.ctr x t) (.ctr (b + k) s₂)⟩
        ⟨.go a₀, pos, tp pos (mv d) tape (.ctr (x + k) t) (.ctr b s₂)⟩ := by
  have hδ := mv_ne_zero hd
  intro k
  induction k with
  | zero => intro x b _ _; simpa using StepN.refl _
  | succ k ih =>
    intro x b h3 h5
    have s1 : Step Mc ⟨.go a₀, pos, tp pos (mv d) tape (.ctr x t) (.ctr (b + (k + 1)) s₂)⟩
        ⟨.go a₁, pos + mv d, tp pos (mv d) tape (.ctr (x + 1) t) (.ctr (b + (k + 1)) s₂)⟩ := by
      refine step_of (h3 x (Nat.le_refl _) (by omega)) rfl (by simp [tp_src]) rfl rfl ?_
      simp only [upd_tp_src]
    have s2 : Step Mc ⟨.go a₁, pos + mv d, tp pos (mv d) tape (.ctr (x + 1) t) (.ctr (b + (k + 1)) s₂)⟩
        ⟨.go a₀, pos, tp pos (mv d) tape (.ctr (x + 1) t) (.ctr (b + k) s₂)⟩ := by
      refine step_of (h5 (b + (k + 1)) (by omega) (Nat.le_refl _)) rfl (by simp [tp_dst hδ]) rfl ?_ ?_
      · simp only [mv_opp]; omega
      · simp only [upd_tp_dst hδ]
        congr 2
    have := StepN.cons s1 (StepN.cons s2 (ih (x + 1) b (fun i h1 h2 => h3 i (by omega) (by omega))
      (fun j h1 h2 => h5 j h1 (by omega))))
    rwa [show x + 1 + k = x + (k + 1) by omega, show 2 * k + 1 + 1 = 2 * (k + 1) by omega] at this

omit [DecidableEq Q] [DecidableEq P] [DecidableEq S] in
/-- **実状態へ移る規則 1 本の模倣の逆向き版**（R1 → R2 → 往復 → R4、3 + 2(hi − c₁) ステップ）。
    番兵は hi（最大）、行き先の計数 c₁ ≤ hi。 -/
theorem sim_go_rev {St : Type} {Mc : Machine St P (KSym S)} {d : Dir} (hd : d = .L ∨ d = .R)
    {h₀ h₁ a₀ a₁ : St} {hi c₀ c₁ : Nat} (hle : c₁ ≤ hi) {pos : Int} {tape : Int → S} {t : S}
    (r1 : (⟨h₀, .ctr c₀ (tape pos), .ctr c₁ t, d, .go h₁⟩ : Rule St P (KSym S)) ∈ Mc)
    (r2 : (⟨h₁, .pl (tape (pos + mv d)), .ctr hi (tape (pos + mv d)), opp d, .go a₀⟩ :
      Rule St P (KSym S)) ∈ Mc)
    (r3 : ∀ i, c₁ ≤ i → i < hi → (⟨a₀, .ctr i t, .ctr (i + 1) t, d, .go a₁⟩ : Rule St P (KSym S)) ∈ Mc)
    (r5 : ∀ j, c₁ < j → j ≤ hi → (⟨a₁, .ctr j (tape (pos + mv d)), .ctr (j - 1) (tape (pos + mv d)),
      opp d, .go a₀⟩ : Rule St P (KSym S)) ∈ Mc)
    (r4 : (⟨a₀, .ctr hi t, .pl t, d, .go h₁⟩ : Rule St P (KSym S)) ∈ Mc) :
    StepN Mc (3 + 2 * (hi - c₁))
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
  obtain ⟨k, rfl⟩ : ∃ k, hi = c₁ + k := ⟨hi - c₁, by omega⟩
  rw [show c₁ + k - c₁ = k by omega]
  have s1 : Step Mc ⟨.go h₀, pos, tp pos (mv d) tape (.ctr c₀ (tape pos)) (.pl s₂)⟩
      ⟨.go h₁, pos + mv d, tp pos (mv d) tape (.ctr c₁ t) (.pl s₂)⟩ :=
    step_of r1 rfl (by simp [tp_src]) rfl rfl (by simp only [upd_tp_src])
  have s2 : Step Mc ⟨.go h₁, pos + mv d, tp pos (mv d) tape (.ctr c₁ t) (.pl s₂)⟩
      ⟨.go a₀, pos, tp pos (mv d) tape (.ctr c₁ t) (.ctr (c₁ + k) s₂)⟩ :=
    step_of r2 rfl (by simp [tp_dst hδ]) rfl (by simp only [mv_opp]; omega) (by simp only [upd_tp_dst hδ])
  have s3 := loop_rev hd a₀ a₁ pos tape t s₂ k c₁ c₁ r3 r5
  have s4 : Step Mc ⟨.go a₀, pos, tp pos (mv d) tape (.ctr (c₁ + k) t) (.ctr c₁ s₂)⟩
      ⟨.go h₁, pos + mv d, tp pos (mv d) tape (.pl t) (.ctr c₁ s₂)⟩ :=
    step_of r4 rfl (by simp [tp_src]) rfl rfl (by simp only [upd_tp_src])
  have := StepN.cons s1 (StepN.cons s2 (s3.trans (StepN.single s4)))
  rwa [show 2 * k + 1 + 1 + 1 = 3 + 2 * k by omega] at this

/-- 実状態 q へ移るステップの模倣に要る規則が残っていること（行き先で読む記号 s₂、書く記号 t）。 -/
def Kept (nd : Slot → S → Bool) (T : Machine Q P S) (off : Q → Nat) (M : Nat) (q : Q) (t s₂ : S) : Prop :=
  if dir T q = .R then
    nd .r2p s₂ = true ∧ nd .r4p t = true ∧ (∀ i, 2 ≤ i → i ≤ off q → nd (.dec i) t = true) ∧
      (∀ j, 1 ≤ j → j < off q → nd (.inc j) s₂ = true)
  else
    nd .r2m s₂ = true ∧ nd .r4m t = true ∧ (∀ j, off q ≤ j → j < M → nd (.inc j) t = true) ∧
      (∀ i, off q < i → i ≤ M → nd (.dec i) s₂ = true)

/-- 実状態へ移る規則 1 本の模倣。 -/
theorem esim_go (hW : ZeroShiftHalts T) (hR : Reversible T) (hN : EGood T off M)
    (hS : ∀ s, s ∈ ss) {p q : Q} {s t : S} {d : Dir}
    (hr : (⟨p, s, t, d, .go q⟩ : Rule Q P S) ∈ T) (pos : Int) (tape : Int → S)
    (hs : tape pos = s) (hk : Kept nd T off M q t (tape (pos + mv d))) :
    StepN (econvWith T off M ss nd) (ecost T off M ⟨.go q, pos + mv d, upd tape pos t⟩)
      (enc T off ⟨.go p, pos, tape⟩) (enc T off ⟨.go q, pos + mv d, upd tape pos t⟩) := by
  have hdq : dir T q = d := dir_eq hW hR hr rfl
  have hd : d = .L ∨ d = .R := go_dir_LR hW hr rfl
  have hrng := hN.rng q
  have r1 : rule1 T off ⟨p, s, t, d, .go q⟩ ∈ econvWith T off M ss nd := mem_rule1 hr
  simp only [rule1] at r1
  subst hs
  unfold Kept at hk
  rw [hdq] at hk
  rw [enc_go, enc_go, hdq]
  simp only [ecost, hdq]
  rcases hd with rfl | rfl
  · -- Q₋ へ: 番兵は M、a₀ = Ap（O⁻）、a₁ = Am（D⁻）
    simp only [reduceCtorEq, if_false] at hk ⊢
    obtain ⟨k2, k4, k3, k5⟩ := hk
    exact sim_go_rev (a₀ := KSt.Ap) (a₁ := KSt.Am) (.inl rfl) hrng.2 r1
      (mem_slot (k := .r2m) hS (by show 1 ≤ M; omega) k2)
      (fun i h1 h2 => mem_slot (k := .inc i) hS (by show 1 ≤ i ∧ i < M; omega) (k3 i h1 h2))
      (fun j h1 h2 => mem_slot (k := .dec j) hS (by show 2 ≤ j ∧ j ≤ M; omega) (k5 j h1 h2))
      (mem_slot (k := .r4m) hS (by show 1 ≤ M; omega) k4)
  · -- Q₊ へ: 番兵は 1、a₀ = Am（O⁺）、a₁ = Ap（D⁺）
    simp only [if_true] at hk ⊢
    obtain ⟨k2, k4, k3, k5⟩ := hk
    exact sim_go_gen (a₀ := KSt.Am) (a₁ := KSt.Ap) (.inr rfl) hrng.1 r1
      (mem_slot (k := .r2p) hS (by show 1 ≤ M; omega) k2)
      (fun i h1 h2 => mem_slot (k := .dec i) hS (by show 2 ≤ i ∧ i ≤ M; omega) (k3 i (by omega) h2))
      (fun j h1 h2 => mem_slot (k := .inc j) hS (by show 1 ≤ j ∧ j < M; omega) (k5 j h1 h2))
      (mem_slot (k := .r4p) hS (by show 1 ≤ M; omega) k4)

/-- 停止規則（行き先が `halt`）1 本の模倣。1 ステップ。 -/
theorem esim_halt {p : Q} {s t : S} {d : Dir} {h : P}
    (hr : (⟨p, s, t, d, .halt h⟩ : Rule Q P S) ∈ T) (pos : Int) (tape : Int → S)
    (hs : tape pos = s) :
    StepN (econvWith T off M ss nd) 1
      (enc T off ⟨.go p, pos, tape⟩) (enc T off ⟨.halt h, pos + mv d, upd tape pos t⟩) := by
  have r1 : rule1 T off ⟨p, s, t, d, .halt h⟩ ∈ econvWith T off M ss nd := mem_rule1 hr
  simp only [rule1] at r1
  refine StepN.single (step_of r1 rfl (by simp [enc, hs]) rfl rfl ?_)
  funext j; simp only [enc, upd]
  by_cases h : j = pos <;> simp [h]

theorem readB_of {r : Rule Q P S} (hr : r ∈ T) : readB T r.p r.s = true := by
  unfold readB; rw [List.any_eq_true]; exact ⟨_, hr, by simp⟩

theorem writeB_of {p q : Q} {s t : S} {d : Dir}
    (hr : (⟨p, s, t, d, .go q⟩ : Rule Q P S) ∈ T) : writeB T q t = true := by
  unfold writeB; rw [List.any_eq_true]; exact ⟨_, hr, by simp⟩

/-- 行き先が生きているなら、行き先の記号は行き先の状態で読まれる。 -/
theorem readB_next (hW : ZeroShiftHalts T) {p q : Q} {s t : S} {d : Dir}
    (hr : (⟨p, s, t, d, .go q⟩ : Rule Q P S) ∈ T) {pos : Int} {tape : Int → S}
    (hl : Live T ⟨.go q, pos + mv d, upd tape pos t⟩) : readB T q (tape (pos + mv d)) = true := by
  have hδ : mv d ≠ 0 := mv_ne_zero (go_dir_LR hW hr rfl)
  rcases hl with ⟨_, hh⟩ | ⟨_, r', hr', hst', hs', _⟩
  · cases hh
  · dsimp only at hst' hs'
    injection hst' with e
    have hu : upd tape pos t (pos + mv d) = tape (pos + mv d) := by
      simp only [upd]; rw [if_neg (by omega)]
    rw [← hu, hs', e]
    exact readB_of hr'

/-- 模倣: T のステップ c → c' で c' が生きていて、要る規則が残っているなら、
    T' は enc c からちょうど `ecost c'` ステップで enc c' に達する。 -/
theorem econvWith_simulates (hW : ZeroShiftHalts T) (hR : Reversible T) (hN : EGood T off M)
    (hS : ∀ s, s ∈ ss)
    (hK : ∀ q t s₂, writeB T q t = true → readB T q s₂ = true → Kept nd T off M q t s₂)
    {c c' : Cfg Q P S} (h : Step T c c') (hl : Live T c') :
    StepN (econvWith T off M ss nd) (ecost T off M c') (enc T off c) (enc T off c') := by
  obtain ⟨⟨p, s, t, d, q⟩, hr, hst, hs, rfl⟩ := h
  obtain ⟨st, pos, tape⟩ := c
  simp only at hst hs
  subst hst
  cases q with
  | go q => exact esim_go hW hR hN hS hr pos tape hs (hK q t _ (writeB_of hr) (readB_next hW hr hl))
  | halt h => exact esim_halt hr pos tape hs

/-- T が c で止まっているなら、T' も enc c で止まっている。 -/
theorem econvWith_halted (hW : ZeroShiftHalts T) (hR : Reversible T)
    (hinj : ∀ a b, dir T a = dir T b → off a = off b → a = b)
    {c : Cfg Q P S} (hH : Halted T c) : Halted (econvWith T off M ss nd) (enc T off c) := by
  intro c'' ⟨ρ, hρ, hst, hs, _⟩
  obtain ⟨st, pos, tape⟩ := c
  cases st with
  | halt h => simp [enc] at hst
  | go p =>
    rw [enc_go] at hst hs
    simp at hst hs
    rcases ekind_of_mem hW hR hρ with ⟨p', s', t', d', q', hr, _⟩ | ⟨p', s', t', d', ph', hr⟩ |
        ⟨x, _⟩ | ⟨x, _⟩ | ⟨x, _⟩ | ⟨x, _⟩ | ⟨i, x, _⟩ | ⟨j, x, _⟩
    · simp only [KSym.ctr.injEq] at hs
      obtain ⟨h1, rfl⟩ := hs
      obtain rfl := hinj _ _ (H_dir_inj hst) h1
      exact hH _ ⟨_, hr, rfl, rfl, rfl⟩
    · simp only [KSym.ctr.injEq] at hs
      obtain ⟨h1, rfl⟩ := hs
      obtain rfl := hinj _ _ (H_dir_inj hst) h1
      exact hH _ ⟨_, hr, rfl, rfl, rfl⟩
    · simp at hs
    · simp at hs
    · revert hst; rcases dir_cases T p with h | h <;> simp [h, H]
    · revert hst; rcases dir_cases T p with h | h <;> simp [h, H]
    · revert hst; rcases dir_cases T p with h | h <;> simp [h, H]
    · revert hst; rcases dir_cases T p with h | h <;> simp [h, H]

theorem ecost_pos {c' : Cfg Q P S} : 1 ≤ ecost T off M c' := by
  unfold ecost; split
  · split <;> omega
  · omega

/-! ## 5. 多ステップ -/

theorem econvWith_haltsIn (hW : ZeroShiftHalts T) (hR : Reversible T) (hN : EGood T off M)
    (hS : ∀ s, s ∈ ss)
    (hK : ∀ q t s₂, writeB T q t = true → readB T q s₂ = true → Kept nd T off M q t s₂) :
    ∀ {n : Nat} {c cf : Cfg Q P S}, HaltsIn T n c cf → (∃ h, cf.st = .halt h) →
      ∃ N, n ≤ N ∧ HaltsIn (econvWith T off M ss nd) N (enc T off c) (enc T off cf) :=
  haltsIn_of_sim _ _ _ (fun _ => ecost_pos)
    (fun h₁ hH hf => econvWith_simulates hW hR hN hS hK h₁ (live_of_stepN hH.1 hf))
    (fun hH _ => econvWith_halted hW hR hN.inj hH)

theorem econvWith_haltsIn_rev (hW : ZeroShiftHalts T) (hD : Deterministic T) (hR : Reversible T)
    (hN : EGood T off M) (hS : ∀ s, s ∈ ss)
    (hK : ∀ q t s₂, writeB T q t = true → readB T q s₂ = true → Kept nd T off M q t s₂) :
    ∀ (N : Nat) {c : Cfg Q P S} {e : Cfg KSt P (KSym S)}, NoStuck T c →
      HaltsIn (econvWith T off M ss nd) N (enc T off c) e →
      ∃ n cf, HaltsIn T n c cf ∧ e = enc T off cf :=
  haltsIn_rev_of_sim _ _ (NoStuck T) (econvWith_det hW hD hR hN.inj)
    (fun _ => ecost_pos) nostuck_step
    (fun hns h₁ => econvWith_simulates hW hR hN hS hK h₁ (live_of_nostuck (nostuck_step hns h₁)))
    (fun _ hH => econvWith_halted hW hR hN.inj hH)

/-- 記号: 素の記号か、1 ≤ i ≤ M の計数記号。 -/
theorem econvWith_symbols (hW : ZeroShiftHalts T) (hR : Reversible T) (hN : EGood T off M)
    {ρ : Rule KSt P (KSym S)} (hρ : ρ ∈ econvWith T off M ss nd) :
    ∀ σ ∈ [ρ.s, ρ.t], (∃ x, σ = .pl x) ∨ (∃ i x, σ = .ctr i x ∧ 1 ≤ i ∧ i ≤ M) := by
  have hoff := hN.rng
  rcases ekind_of_mem hW hR hρ with ⟨p, s, t, d, q, _, _⟩ | ⟨p, s, t, d, ph, _⟩ |
      ⟨x, hM⟩ | ⟨x, hM⟩ | ⟨x, hM⟩ | ⟨x, hM⟩ | ⟨i, x, h1, h2⟩ | ⟨j, x, h1, h2⟩ <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] <;> rintro σ (rfl | rfl) <;>
    simp_all <;> first | omega | (have := hoff p; omega) | (have := hoff q; omega)

theorem econvWith_symbols_mem (hW : ZeroShiftHalts T) (hR : Reversible T) (hN : EGood T off M)
    (hS : ∀ s, s ∈ ss) {ρ : Rule KSt P (KSym S)} (hρ : ρ ∈ econvWith T off M ss nd) :
    ρ.s ∈ symUniverse M ss ∧ ρ.t ∈ symUniverse M ss := by
  have h := econvWith_symbols hW hR hN hρ
  have key : ∀ σ ∈ [ρ.s, ρ.t], σ ∈ symUniverse M ss := by
    intro σ hσ
    unfold symUniverse
    rcases h σ hσ with ⟨x, rfl⟩ | ⟨i, x, rfl, h1, h2⟩
    · exact List.mem_append.2 (.inl (List.mem_map.2 ⟨x, hS x, rfl⟩))
    · exact List.mem_append.2 (.inr (mem_ctrs (hS x) h1 h2))
  exact ⟨key _ (by simp), key _ (by simp)⟩

/-! ## 6. 標準の番号付けと、構文的に要る規則の選択 -/

section Canon
variable {qs : List Q}

theorem ecanon_good (hQ : ∀ q, q ∈ qs) : EGood T (ecanonOff T qs) (emax T qs) := by
  have memP : ∀ q, dir T q = .R → q ∈ plusList T qs := fun q h => by
    simp [plusList, List.mem_filter, hQ q, h]
  have memM : ∀ q, dir T q = .L → q ∈ minusList T qs := fun q h => by
    simp [minusList, List.mem_filter, hQ q, h]
  have hmx1 : (plusList T qs).length ≤ emax T qs := Nat.le_max_left _ _
  have hmx2 : (minusList T qs).length ≤ emax T qs := Nat.le_max_right _ _
  refine ⟨?_, ?_⟩
  · intro a b hab h
    unfold ecanonOff at h
    rcases dir_cases T a with ha | ha
    · have hb : dir T b = .L := hab ▸ ha
      have := ix_lt (memM a ha); have := ix_lt (memM b hb)
      simp only [ha, hb, reduceCtorEq, if_false] at h
      exact ix_inj (memM a ha) (memM b hb) (by omega)
    · have hb : dir T b = .R := hab ▸ ha
      simp only [ha, hb, if_true] at h
      exact ix_inj (memP a ha) (memP b hb) (by omega)
  · intro q
    unfold ecanonOff
    rcases dir_cases T q with h | h
    · have := ix_lt (memM q h); simp only [h, reduceCtorEq, if_false]; omega
    · have := ix_lt (memP q h); simp only [h, if_true]; omega

theorem any_of_mem {l : List Q} {f : Q → Bool} {q : Q} (hq : q ∈ l) (h : f q = true) : l.any f = true :=
  List.any_eq_true.2 ⟨q, hq, h⟩

/-- 構文的に要る規則の選択 `enb` は、模倣に要る規則を残している。 -/
theorem enb_kept (hQ : ∀ q, q ∈ qs) {off : Q → Nat} {M : Nat} :
    ∀ q t s₂, writeB T q t = true → readB T q s₂ = true → Kept (enb T off qs) T off M q t s₂ := by
  intro q t s₂ hw hrd
  unfold Kept
  rcases dir_cases T q with h | h
  · simp only [h, reduceCtorEq, if_false]
    refine ⟨any_of_mem (hQ q) (by simp [h, hrd]), any_of_mem (hQ q) (by simp [h, hw]),
      fun j h1 _ => any_of_mem (hQ q) ?_, fun i h1 _ => any_of_mem (hQ q) ?_⟩
    · simp [h, hw, h1]
    · simp [h, hrd, h1]
  · simp only [h, if_true]
    refine ⟨any_of_mem (hQ q) (by simp [h, hrd]), any_of_mem (hQ q) (by simp [h, hw]),
      fun i _ h2 => any_of_mem (hQ q) ?_, fun j _ h2 => any_of_mem (hQ q) ?_⟩
    · simp [h, hw, h2]
    · simp [h, hrd, h2]

theorem symUniverse_emax_length (qs : List Q) (ss : List S) :
    (symUniverse (emax T qs) ss).length =
      (max (plusList T qs).length (minusList T qs).length + 1) * ss.length :=
  symUniverse_length _ _

/-! ## 7. 主定理 -/

/-- **ε 逆向きの 4 状態化の主定理**（具体機械への適用用）。E = enc T (ecanonOff T qs)。
    1. 決定的・可逆
    2. 生きている行き先への 1 ステップは `ecost` = 3 + 2|v(q) − σ_{dir q}| ステップで模倣
    3. 疑似状態で止まる実行は、E で対応する配置で止まる（前向き）
    4. `NoStuck T c` なら、T' の停止は T の停止に対応（逆向き）
    5. `NoStuck T c` なら、停止しないことが対応
    6. 規則の記号は `symUniverse (emax T qs) ss`（長さ (max(m₊, m₋) + 1)·|ss|）に入る -/
theorem econv_main (hW : ZeroShiftHalts T) (hD : Deterministic T) (hR : Reversible T)
    (hQ : ∀ q, q ∈ qs) (hS : ∀ s, s ∈ ss) :
    Deterministic (econv T qs ss) ∧ Reversible (econv T qs ss) ∧
    (∀ c c' : Cfg Q P S, Step T c c' → Live T c' →
      StepN (econv T qs ss) (ecost T (ecanonOff T qs) (emax T qs) c')
        (enc T (ecanonOff T qs) c) (enc T (ecanonOff T qs) c')) ∧
    (∀ (n : Nat) (c cf : Cfg Q P S), HaltsIn T n c cf → (∃ h, cf.st = .halt h) →
      ∃ N, n ≤ N ∧ HaltsIn (econv T qs ss) N (enc T (ecanonOff T qs) c) (enc T (ecanonOff T qs) cf)) ∧
    (∀ (N : Nat) (c : Cfg Q P S) (e : Cfg KSt P (KSym S)), NoStuck T c →
      HaltsIn (econv T qs ss) N (enc T (ecanonOff T qs) c) e →
      ∃ n cf, HaltsIn T n c cf ∧ e = enc T (ecanonOff T qs) cf) ∧
    (∀ c : Cfg Q P S, NoStuck T c → ((∀ n cf, ¬ HaltsIn T n c cf) ↔
      (∀ N e, ¬ HaltsIn (econv T qs ss) N (enc T (ecanonOff T qs) c) e))) ∧
    (∀ ρ ∈ econv T qs ss, ρ.s ∈ symUniverse (emax T qs) ss ∧ ρ.t ∈ symUniverse (emax T qs) ss) ∧
    (symUniverse (emax T qs) ss).length =
      (max (plusList T qs).length (minusList T qs).length + 1) * ss.length := by
  have hN := ecanon_good (T := T) hQ
  have hK := enb_kept (T := T) (off := ecanonOff T qs) (M := emax T qs) hQ
  refine ⟨econvWith_det hW hD hR hN.inj, econvWith_rev hW hR hN.inj,
    fun _ _ h hl => econvWith_simulates hW hR hN hS hK h hl,
    fun _ _ _ h hf => econvWith_haltsIn hW hR hN hS hK h hf,
    fun N _ _ hns h => econvWith_haltsIn_rev hW hD hR hN hS hK N hns h, ?_,
    fun _ h => econvWith_symbols_mem hW hR hN hS h, symUniverse_emax_length qs ss⟩
  intro c hns
  exact diverges_iff_of
    (fun n cf hn => let ⟨N, _, hN'⟩ := econvWith_haltsIn hW hR hN hS hK hn (hns n cf hn); ⟨N, _, hN'⟩)
    (fun N e he => let ⟨n, cf, hn, _⟩ := econvWith_haltsIn_rev hW hD hR hN hS hK N hns he; ⟨n, cf, hn⟩)

end Canon

/-! ## 8. 仮定が空でないことの確認（KState.lean の例 T0） -/

namespace Example
open URTM.KState.Example

/-- 決定性・可逆性をカーネルの `decide` で直接確かめる（主定理とは独立）。 -/
theorem T0e_det_rev_decide : Deterministic (econv T0 [false, true] [false, true]) ∧
    Reversible (econv T0 [false, true] [false, true]) := by
  constructor <;> decide

end Example

end URTM.KStateEps
