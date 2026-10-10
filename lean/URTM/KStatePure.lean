/-
  「1 ブロック 3 状態」の変換（旧リポ `kstate_convert.py --mode pure`、docs/15 §6）とその疎版の
  一般の模倣証明。zoo の定式化（`KState.lean` の `Machine`/`Cfg`）で書き直したもの。

  * T の状態をブロックに分ける。同じブロックの状態はすべて同じ方向 d（= `dir T q`）から入られる
    （pure）。ブロック b の状態は 3 つ: 安定状態 `z d b`（r0_b / l0_b）、往復用の `z (opp d) b` と
    `o d b`（r1_b / l1_b）。計数記号 `[i, s]` の i はブロック内の位置 `loc q`（0 から）で、
    全ブロックが共有する。ブロック分け `Layout`（blk・loc・ブロック数・各ブロックの方向と大きさ）は
    引数で、`Good` を満たせば何でもよい（`tools/kstate_sparse_pure.py` が選んだものを渡す）。
  * 規則（Python の A〜E と同じ）:
      A  [z (dir p) (blk p), [loc p, s], [loc q, t], d, z d (blk q)]   T の規則 [p, s, t, d, q]
      A' [z (dir p) (blk p), [loc p, s], t,          d, halt h]        T の規則 [p, s, t, d, halt h]
      B  [z d b,       s,      [0, s],     opp d, z (opp d) b]   行き先の初期化
      C  [z (opp d) b, [j, s], [j-1, s],   d,     o d b]         元セルの減算（1 ≤ j < size b）
      D  [o d b,       [e, s], [e+1, s],   opp d, z (opp d) b]   行き先の加算（e + 1 < size b）
      E  [z (opp d) b, [0, s], s,          d,     z d b]         転送完了
    A' は 0 シフト停止規則も含む（Python の旧生成器は疑似状態行きの規則を落としていた。
    zoo では定理 A（`KState.lean` の R1'）と同じく 1 ステップで疑似状態へ写す）。
  * 疎版 `spconv T L qs ss := (pconv T L ss).filter (pkeepRule T L qs)`: 計数記号 `[c, s]` は
    ∃ q ∈ qs, c ≤ loc q ∧ s ∈ need(q) のときだけ残す（`needB` は KStateSparse.lean と同じ）。
    `tools/kstate_sparse_pure.py` の keep と同じ定義。

  主定理 `spconv_main`（`KStateSparse.sconv_main` と同じ形）:
  * 決定的・可逆（密な版 `pconv` が決定的・可逆で、疎版はその部分集合）
  * T の 1 ステップ c → c' は、c' が生きているなら `pcost c'` = 3 + 2·loc q（停止規則は 1）ステップで
    penc c → penc c' と模倣される
  * 疑似状態で止まる実行は、同じ停止配置の符号化で止まる（前向き）
  * `NoStuck T c` なら、疎版の停止は T の停止に対応し（逆向き）、停止しないことも対応する

  未証明の穴・新規公理・native_decide を使わない。mathlib 非依存。
-/
import URTM.KStateSparse

namespace URTM.KStatePure

set_option linter.unusedSectionVars false

open URTM (Dir)
open URTM.KState
open URTM.KStateSparse (needB needB_read' needB_write needB_next Live NoStuck live_of_stepN nostuck_step
  live_of_nostuck)
open URTM.SimLemmas (Deterministic.mono Reversible.mono Halted.mono)

variable {Q P S : Type} [DecidableEq Q] [DecidableEq P] [DecidableEq S]

/-! ## 1. 定義 -/

/-- 変換後の状態。`z d b` は r0_b（d = R）/ l0_b（d = L）、`o d b` は r1_b / l1_b。 -/
inductive PSt where
  | z (d : Dir) (b : Nat)
  | o (d : Dir) (b : Nat)
  deriving DecidableEq, Repr

/-- ブロック分け: 状態のブロック番号とブロック内の位置、ブロック数、各ブロックの方向と大きさ。 -/
structure Layout (Q : Type) where
  blk : Q → Nat
  loc : Q → Nat
  nb : Nat
  bd : Nat → Dir
  bs : Nat → Nat

/-- ブロック分けの条件。 -/
structure Good (T : Machine Q P S) (L : Layout Q) : Prop where
  inj : ∀ a b, L.blk a = L.blk b → L.loc a = L.loc b → a = b
  pure : ∀ q, L.bd (L.blk q) = dir T q
  rng : ∀ q, L.loc q < L.bs (L.blk q)
  nbq : ∀ q, L.blk q < L.nb
  bdir : ∀ b, b < L.nb → L.bd b = .L ∨ L.bd b = .R

/-- 規則 A / A'（T の規則 1 本の実行）。 -/
def ruleA (T : Machine Q P S) (L : Layout Q) (r : Rule Q P S) : Rule PSt P (KSym S) :=
  match r.q with
  | .go q => ⟨.z (dir T r.p) (L.blk r.p), .ctr (L.loc r.p) r.s, .ctr (L.loc q) r.t, r.d,
      .go (.z r.d (L.blk q))⟩
  | .halt h => ⟨.z (dir T r.p) (L.blk r.p), .ctr (L.loc r.p) r.s, .pl r.t, r.d, .halt h⟩

/-- ブロック b（方向 d・大きさ n）の往復の規則 B・C・D・E（Python と同じ並び）。 -/
def shut (ss : List S) (d : Dir) (n b : Nat) : List (Rule PSt P (KSym S)) :=
  ss.map (fun s => ⟨.z d b, .pl s, .ctr 0 s, opp d, .go (.z (opp d) b)⟩) ++
  (List.range' 1 (n - 1)).flatMap (fun j =>
    ss.map (fun s => ⟨.z (opp d) b, .ctr j s, .ctr (j - 1) s, d, .go (.o d b)⟩)) ++
  (List.range (n - 1)).flatMap (fun e =>
    ss.map (fun s => ⟨.o d b, .ctr e s, .ctr (e + 1) s, opp d, .go (.z (opp d) b)⟩)) ++
  ss.map (fun s => ⟨.z (opp d) b, .ctr 0 s, .pl s, d, .go (.z d b)⟩)

/-- **1 ブロック 3 状態の変換**（密な版、関数）。 -/
def pconv (T : Machine Q P S) (L : Layout Q) (ss : List S) : Machine PSt P (KSym S) :=
  T.map (ruleA T L) ++ (List.range L.nb).flatMap (fun b => shut ss (L.bd b) (L.bs b) b)

/-- 残す記号: 素の記号はすべて、計数記号 `[c, s]` は c ≤ loc q かつ s ∈ need(q) の q があるとき。 -/
def pkeepSym (T : Machine Q P S) (L : Layout Q) (qs : List Q) : KSym S → Bool
  | .pl _ => true
  | .ctr c s => qs.any (fun q => decide (c ≤ L.loc q) && needB T q s)

/-- 残す規則: 読む記号と書く記号の両方が残るもの。 -/
def pkeepRule (T : Machine Q P S) (L : Layout Q) (qs : List Q) (ρ : Rule PSt P (KSym S)) : Bool :=
  pkeepSym T L qs ρ.s && pkeepSym T L qs ρ.t

/-- **疎版**（関数）。 -/
def spconv (T : Machine Q P S) (L : Layout Q) (qs : List Q) (ss : List S) :
    Machine PSt P (KSym S) :=
  (pconv T L ss).filter (pkeepRule T L qs)

/-- 配置の符号化。安定配置: 状態 `z (dir p) (blk p)`、ヘッド上のセルだけ計数記号 `[loc p, s]`。 -/
def penc (T : Machine Q P S) (L : Layout Q) (c : Cfg Q P S) : Cfg PSt P (KSym S) :=
  match c.st with
  | .go p => ⟨.go (.z (dir T p) (L.blk p)), c.pos,
      fun j => if j = c.pos then .ctr (L.loc p) (c.tape j) else .pl (c.tape j)⟩
  | .halt h => ⟨.halt h, c.pos, fun j => .pl (c.tape j)⟩

/-- T の 1 ステップ（行き先配置 `c'`）に要するステップ数。停止規則は 1。 -/
def pcost (L : Layout Q) (c' : Cfg Q P S) : Nat :=
  match c'.st with
  | .go q => 3 + 2 * L.loc q
  | .halt _ => 1

/-- 行き先が実状態なら `l` に入っている（状態数の検査用）。 -/
def tgtIn (l : List PSt) : Tgt PSt P → Bool
  | .go x => decide (x ∈ l)
  | .halt _ => true

/-- 生成表の検査（記号・状態がリストに入る）を主定理の形（現状態と行き先の状態・読み書きの記号）に分ける。 -/
theorem sts_syms_of {M : Machine PSt P (KSym S)} {A : List (KSym S)} {B : List PSt}
    (h : ∀ ρ ∈ M, ρ.s ∈ A ∧ ρ.t ∈ A ∧ ρ.p ∈ B ∧ tgtIn B ρ.q = true) :
    (∀ ρ ∈ M, ρ.p ∈ B ∧ ∀ x, ρ.q = .go x → x ∈ B) ∧ (∀ ρ ∈ M, ρ.s ∈ A ∧ ρ.t ∈ A) :=
  ⟨fun ρ hρ => ⟨(h ρ hρ).2.2.1, fun x hx => by simpa [tgtIn, hx] using (h ρ hρ).2.2.2⟩,
   fun ρ hρ => ⟨(h ρ hρ).1, (h ρ hρ).2.1⟩⟩

/-! ### ブロックのリストから作るブロック分け -/

/-- `q` を含む最初のブロックの番号。 -/
def bIdx (q : Q) : List (List Q) → Nat
  | [] => 0
  | l :: ls => if q ∈ l then 0 else bIdx q ls + 1

/-- ブロックのリスト（Python の `blocks`）からブロック分けを作る。方向は先頭の状態の `dir`。 -/
def layoutOf (T : Machine Q P S) (bl : List (List Q)) : Layout Q where
  blk q := bIdx q bl
  loc q := ix q (bl.getD (bIdx q bl) [])
  nb := bl.length
  bd b := match bl.getD b [] with
    | [] => .R
    | q :: _ => dir T q
  bs b := (bl.getD b []).length

/-- `Good` を状態のリスト上の有限の検査に落としたもの（具体機械では `decide` で示す）。 -/
def GoodL (T : Machine Q P S) (L : Layout Q) (qs : List Q) : Prop :=
  (∀ a ∈ qs, ∀ b ∈ qs, L.blk a = L.blk b → L.loc a = L.loc b → a = b) ∧
  (∀ q ∈ qs, L.bd (L.blk q) = dir T q ∧ L.loc q < L.bs (L.blk q) ∧ L.blk q < L.nb) ∧
  (∀ b, b < L.nb → L.bd b = .L ∨ L.bd b = .R)

instance (T : Machine Q P S) (L : Layout Q) (qs : List Q) : Decidable (GoodL T L qs) := by
  unfold GoodL; infer_instance

theorem good_of_L {T : Machine Q P S} {L : Layout Q} {qs : List Q} (hQ : ∀ q, q ∈ qs)
    (h : GoodL T L qs) : Good T L :=
  ⟨fun a b => h.1 a (hQ a) b (hQ b), fun q => (h.2.1 q (hQ q)).1, fun q => (h.2.1 q (hQ q)).2.1,
    fun q => (h.2.1 q (hQ q)).2.2, h.2.2⟩

/-! ## 2. 規則の分類 -/

/-- 変換後の規則の 6 種類（A, A', B, C, D, E）。 -/
inductive PKind (T : Machine Q P S) (L : Layout Q) : Rule PSt P (KSym S) → Prop
  | ago (p : Q) (s t : S) (d : Dir) (q : Q) :
      (⟨p, s, t, d, .go q⟩ : Rule Q P S) ∈ T → (d = .L ∨ d = .R) →
      PKind T L ⟨.z (dir T p) (L.blk p), .ctr (L.loc p) s, .ctr (L.loc q) t, d, .go (.z d (L.blk q))⟩
  | ahalt (p : Q) (s t : S) (d : Dir) (h : P) :
      (⟨p, s, t, d, .halt h⟩ : Rule Q P S) ∈ T →
      PKind T L ⟨.z (dir T p) (L.blk p), .ctr (L.loc p) s, .pl t, d, .halt h⟩
  | rb (b : Nat) (d : Dir) (s : S) : b < L.nb → L.bd b = d →
      PKind T L ⟨.z d b, .pl s, .ctr 0 s, opp d, .go (.z (opp d) b)⟩
  | rc (b : Nat) (d : Dir) (j : Nat) (s : S) : b < L.nb → L.bd b = d → 1 ≤ j → j < L.bs b →
      PKind T L ⟨.z (opp d) b, .ctr j s, .ctr (j - 1) s, d, .go (.o d b)⟩
  | rd (b : Nat) (d : Dir) (e : Nat) (s : S) : b < L.nb → L.bd b = d → e + 1 < L.bs b →
      PKind T L ⟨.o d b, .ctr e s, .ctr (e + 1) s, opp d, .go (.z (opp d) b)⟩
  | re (b : Nat) (d : Dir) (s : S) : b < L.nb → L.bd b = d →
      PKind T L ⟨.z (opp d) b, .ctr 0 s, .pl s, d, .go (.z d b)⟩

section Kind
variable {T : Machine Q P S} {L : Layout Q} {ss : List S}

theorem pkind_of_mem (hW : ZeroShiftHalts T) {ρ : Rule PSt P (KSym S)}
    (h : ρ ∈ pconv T L ss) : PKind T L ρ := by
  unfold pconv at h
  simp only [List.mem_append, List.mem_map, List.mem_flatMap, List.mem_range] at h
  rcases h with ⟨r, hr, rfl⟩ | ⟨b, hb, h⟩
  · obtain ⟨p, s, t, d, q⟩ := r
    cases q with
    | go q =>
      have hd : d = .L ∨ d = .R := go_dir_LR hW hr rfl
      exact PKind.ago p s t d q hr hd
    | halt h => exact PKind.ahalt p s t d h hr
  · unfold shut at h
    simp only [List.mem_append, List.mem_map, List.mem_flatMap, List.mem_range'_1,
      List.mem_range] at h
    rcases h with ((⟨s, _, rfl⟩ | ⟨j, ⟨h1, h2⟩, s, _, rfl⟩) | ⟨e, h1, s, _, rfl⟩) | ⟨s, _, rfl⟩
    · exact PKind.rb b _ s hb rfl
    · exact PKind.rc b _ j s hb rfl h1 (by omega)
    · exact PKind.rd b _ e s hb rfl (by omega)
    · exact PKind.re b _ s hb rfl

theorem mem_of_pkind (hS : ∀ s, s ∈ ss) {ρ : Rule PSt P (KSym S)} (h : PKind T L ρ) :
    ρ ∈ pconv T L ss := by
  unfold pconv
  simp only [List.mem_append, List.mem_map, List.mem_flatMap, List.mem_range]
  cases h with
  | ago p s t d q hr _ =>
    exact .inl ⟨_, hr, by simp [ruleA]⟩
  | ahalt p s t d h hr =>
    exact .inl ⟨_, hr, by simp [ruleA]⟩
  | rb b d s hb hbd =>
    subst hbd
    refine .inr ⟨b, hb, ?_⟩
    unfold shut
    simp only [List.mem_append, List.mem_map]
    exact .inl (.inl (.inl ⟨s, hS s, rfl⟩))
  | rc b d j s hb hbd h1 h2 =>
    subst hbd
    refine .inr ⟨b, hb, ?_⟩
    unfold shut
    simp only [List.mem_append, List.mem_map, List.mem_flatMap, List.mem_range'_1]
    exact .inl (.inl (.inr ⟨j, ⟨h1, by omega⟩, s, hS s, rfl⟩))
  | rd b d e s hb hbd h1 =>
    subst hbd
    refine .inr ⟨b, hb, ?_⟩
    unfold shut
    simp only [List.mem_append, List.mem_map, List.mem_flatMap, List.mem_range]
    exact .inl (.inr ⟨e, by omega, s, hS s, rfl⟩)
  | re b d s hb hbd =>
    subst hbd
    refine .inr ⟨b, hb, ?_⟩
    unfold shut
    simp only [List.mem_append, List.mem_map]
    exact .inr ⟨s, hS s, rfl⟩

end Kind

/-! ## 3. 決定性と可逆性 -/

theorem opp_ne {d : Dir} (h : d = .L ∨ d = .R) : opp d ≠ d := by
  rcases h with rfl | rfl <;> simp [opp]

section DetRev
variable {T : Machine Q P S} {L : Layout Q} {ss : List S}

/-- 安定状態は往復用の状態 `z (opp d) b` と一致しない。 -/
theorem stable_ne (hG : Good T L) {p : Q} {b : Nat} {d : Dir} (hbd : L.bd b = d)
    (h1 : dir T p = opp d) (h2 : L.blk p = b) : False := by
  have hp := hG.pure p
  rw [h2, hbd] at hp
  rw [← hp] at h1
  exact opp_ne (dir_cases T p) (by rw [← hp] at *; exact h1.symm)

theorem pconv_det (hW : ZeroShiftHalts T) (hD : Deterministic T) (hG : Good T L) :
    Deterministic (pconv T L ss) := by
  intro a ha b hb hne hp hs
  have ka := pkind_of_mem hW ha
  have kb := pkind_of_mem hW hb
  clear ha hb
  rcases ka with ⟨p, s, t, d, q, hr, hd⟩ | ⟨p, s, t, d, h, hr⟩ | ⟨b, d, s, hb, hbd⟩ |
      ⟨b, d, j, s, hb, hbd, h1, h2⟩ | ⟨b, d, e, s, hb, hbd, h1⟩ | ⟨b, d, s, hb, hbd⟩ <;>
  rcases kb with ⟨p', s', t', d', q', hr', hd'⟩ | ⟨p', s', t', d', h', hr'⟩ | ⟨b', d', s', hb', hbd'⟩ |
      ⟨b', d', j', s', hb', hbd', h1', h2'⟩ | ⟨b', d', e', s', hb', hbd', h1'⟩ | ⟨b', d', s', hb', hbd'⟩ <;>
  simp only [PSt.z.injEq, PSt.o.injEq, KSym.ctr.injEq, reduceCtorEq] at hp hs <;>
  simp only [ne_eq, Rule.mk.injEq, not_and] at hne
  -- A と A / A'
  all_goals first
    | (obtain ⟨h0, rfl⟩ := hp
       have e : d = d' := hbd.symm.trans hbd'
       subst e
       clear h0
       simp_all; done)
    | (obtain ⟨_, h2⟩ := hp
       obtain ⟨h3, rfl⟩ := hs
       obtain rfl := hG.inj _ _ h2 h3
       have := detT_eq hD hr hr' rfl rfl
       simp only [Rule.mk.injEq, Tgt.go.injEq, reduceCtorEq] at this
       simp_all)
    | (obtain ⟨h1, h2⟩ := hp
       exact (stable_ne hG hbd' h1 h2).elim)
    | (obtain ⟨h1, h2⟩ := hp
       exact (stable_ne hG hbd h1.symm h2.symm).elim)
    | (obtain ⟨rfl, rfl⟩ := hp
       subst hs
       exact hne rfl rfl rfl rfl rfl)
    | (obtain ⟨h1, rfl⟩ := hp
       obtain ⟨rfl, rfl⟩ := hs
       subst hbd hbd'
       exact hne rfl rfl rfl rfl rfl)
    | (obtain ⟨h1, rfl⟩ := hp
       obtain ⟨rfl, rfl⟩ := hs
       omega)
    | (obtain ⟨h1, rfl⟩ := hp
       obtain ⟨h3, rfl⟩ := hs
       omega)
    | (obtain ⟨h1, rfl⟩ := hp
       subst hbd hbd'
       exact opp_ne (hG.bdir _ hb) h1.symm)
    | (obtain ⟨h1, rfl⟩ := hp
       subst hbd hbd'
       exact opp_ne (hG.bdir _ hb) h1)

theorem pconv_rev (hW : ZeroShiftHalts T) (hR : Reversible T) (hG : Good T L) :
    Reversible (pconv T L ss) := by
  intro a ha b hb hne hq
  have ka := pkind_of_mem hW ha
  have kb := pkind_of_mem hW hb
  clear ha hb
  rcases ka with ⟨p, s, t, d, q, hr, hd⟩ | ⟨p, s, t, d, h, hr⟩ | ⟨b, d, s, hb, hbd⟩ |
      ⟨b, d, j, s, hb, hbd, h1, h2⟩ | ⟨b, d, e, s, hb, hbd, h1⟩ | ⟨b, d, s, hb, hbd⟩ <;>
  rcases kb with ⟨p', s', t', d', q', hr', hd'⟩ | ⟨p', s', t', d', h', hr'⟩ | ⟨b', d', s', hb', hbd'⟩ |
      ⟨b', d', j', s', hb', hbd', h1', h2'⟩ | ⟨b', d', e', s', hb', hbd', h1'⟩ | ⟨b', d', s', hb', hbd'⟩ <;>
  simp only [Tgt.go.injEq, Tgt.halt.injEq, PSt.z.injEq, PSt.o.injEq, reduceCtorEq] at hq <;>
  simp only [ne_eq, Rule.mk.injEq, not_and] at hne <;>
  simp only [ne_eq, KSym.ctr.injEq, reduceCtorEq, not_false_eq_true, and_true, true_and]
  all_goals first
    | (obtain ⟨h0, rfl⟩ := hq
       have e : d = d' := hbd.symm.trans hbd'
       subst e
       have hdd : d = .L ∨ d = .R := hbd ▸ hG.bdir _ hb
       first
         | exact (opp_ne hdd h0).elim
         | exact (opp_ne hdd h0.symm).elim
         | (clear h0; simp_all; done)
         | (refine ⟨rfl, ?_⟩
            rintro ⟨h3, rfl⟩
            have : j = j' := by omega
            subst this; simp_all)
         | (refine ⟨rfl, ?_⟩
            rintro ⟨h3, rfl⟩
            have : e = e' := by omega
            subst this; simp_all))
    | -- A と A（行き先が実状態）: T の可逆性
      (obtain ⟨rfl, h2⟩ := hq
       refine ⟨rfl, ?_⟩
       rintro ⟨h3, rfl⟩
       have hdq := dir_eq hW hR hr rfl
       have hdq' := dir_eq hW hR hr' rfl
       obtain rfl := hG.inj _ _ h2 h3
       have := revT_eq hR hr hr' rfl rfl
       simp only [Rule.mk.injEq] at this
       simp_all)
    | -- A' と A'（行き先が同じ疑似状態）: T の可逆性
      (subst hq
       by_cases e : (⟨p, s, t, d, .halt h⟩ : Rule Q P S) = ⟨p', s', t', d', .halt h⟩
       · simp only [Rule.mk.injEq] at e
         obtain ⟨rfl, rfl, rfl, rfl, -⟩ := e
         exact absurd rfl (hne rfl rfl rfl rfl)
       · have := hR _ hr _ hr' e rfl
         simp only [KSym.pl.injEq]
         exact this)
    | -- A と B / D（z (opp d) b への入り口は A からは来ない）
      (obtain ⟨h1, h2⟩ := hq
       have hdq := dir_eq hW hR hr rfl
       rw [h1] at hdq
       exact (stable_ne hG hbd' hdq h2).elim)
    | (obtain ⟨h1, h2⟩ := hq
       have hdq := dir_eq hW hR hr' rfl
       rw [← h1] at hdq
       exact (stable_ne hG hbd hdq h2.symm).elim)
    | -- A と E: 同じ方向で、書く記号は計数と素で異なる
      (obtain ⟨h1, h2⟩ := hq
       have hdq := dir_eq hW hR hr rfl
       exact h1)
    | (obtain ⟨h1, h2⟩ := hq
       exact h1)
    | (obtain ⟨h1, h2⟩ := hq
       exact h1.symm)
    | (obtain ⟨h1, rfl⟩ := hq
       subst hbd hbd'
       refine ⟨opp_inj h1, ?_⟩
       omega)
    | (obtain ⟨h1, rfl⟩ := hq
       subst hbd hbd'
       refine ⟨rfl, ?_⟩
       rintro rfl
       exact hne rfl rfl rfl rfl rfl)
    | (obtain ⟨h1, rfl⟩ := hq
       subst hbd hbd'
       refine ⟨rfl, ?_⟩
       intro h3
       exact hne rfl (by omega) (by omega) rfl rfl)
    | (obtain ⟨h1, rfl⟩ := hq
       subst hbd hbd'
       exact (opp_ne (hG.bdir _ hb) h1).elim)
    | (obtain ⟨h1, rfl⟩ := hq
       subst hbd hbd'
       exact (opp_ne (hG.bdir _ hb) h1.symm).elim)

end DetRev

/-! ## 4. 1 ステップの模倣（疎版） -/

section Sim
variable {T : Machine Q P S} {L : Layout Q} {ss : List S} {qs : List Q}

theorem pkeep_ctr {q : Q} (hq : q ∈ qs) {c : Nat} {s : S} (h1 : c ≤ L.loc q)
    (h2 : needB T q s = true) : pkeepSym T L qs (.ctr c s) = true := by
  unfold pkeepSym; rw [List.any_eq_true]; exact ⟨q, hq, by simp [h1, h2]⟩

theorem pkeep_pl (x : S) : pkeepSym T L qs (.pl x) = true := rfl

theorem spconv_sub {ρ : Rule PSt P (KSym S)} (h : ρ ∈ spconv T L qs ss) : ρ ∈ pconv T L ss :=
  (List.mem_filter.1 h).1

theorem mem_spconv (hS : ∀ s, s ∈ ss) {ρ : Rule PSt P (KSym S)} (hk : PKind T L ρ)
    (h1 : pkeepSym T L qs ρ.s = true) (h2 : pkeepSym T L qs ρ.t = true) :
    ρ ∈ spconv T L qs ss :=
  List.mem_filter.2 ⟨mem_of_pkind hS hk, by simp [pkeepRule, h1, h2]⟩

theorem penc_go (p : Q) (pos : Int) (tape : Int → S) :
    penc T L ⟨.go p, pos, tape⟩ = ⟨.go (.z (dir T p) (L.blk p)), pos,
      fun j => if j = pos then .ctr (L.loc p) (tape j) else .pl (tape j)⟩ := rfl

/-- 実状態へ移る規則 1 本の模倣（疎版）。行き先の記号が q の need に入っていること。
    A → B → 往復（C・D を loc q 回）→ E。往復で使う計数記号はどれも値が loc q 以下で need(q) に入る。 -/
theorem psim_go (hW : ZeroShiftHalts T) (hR : Reversible T) (hG : Good T L)
    (hS : ∀ s, s ∈ ss) (hQ : ∀ q, q ∈ qs) {p q : Q} {s t : S} {d : Dir}
    (hr : (⟨p, s, t, d, .go q⟩ : Rule Q P S) ∈ T) (pos : Int) (tape : Int → S)
    (hs : tape pos = s) (hnext : needB T q (tape (pos + mv d)) = true) :
    StepN (spconv T L qs ss) (3 + 2 * L.loc q)
      (penc T L ⟨.go p, pos, tape⟩) (penc T L ⟨.go q, pos + mv d, upd tape pos t⟩) := by
  have hdq : dir T q = d := dir_eq hW hR hr rfl
  have hd : d = .L ∨ d = .R := go_dir_LR hW hr rfl
  have hbd : L.bd (L.blk q) = d := (hG.pure q).trans hdq
  have hnb : L.blk q < L.nb := hG.nbq q
  have hrng : L.loc q < L.bs (L.blk q) := hG.rng q
  have ht := needB_write hr
  subst hs
  rw [penc_go, penc_go, hdq]
  have := sim_go_gen (lo := 0) hd (Nat.zero_le _)
    (mem_spconv hS (.ago p _ t d q hr hd) (pkeep_ctr (hQ p) (Nat.le_refl _) (needB_read' hr))
      (pkeep_ctr (hQ q) (Nat.le_refl _) ht))
    (mem_spconv hS (.rb _ d _ hnb hbd) (pkeep_pl _) (pkeep_ctr (hQ q) (Nat.zero_le _) hnext))
    (fun i h1 h2 => mem_spconv hS (.rc _ d i t hnb hbd h1 (by omega)) (pkeep_ctr (hQ q) h2 ht)
      (pkeep_ctr (hQ q) (by omega) ht))
    (fun j _ h2 => mem_spconv hS (.rd _ d j _ hnb hbd (by omega)) (pkeep_ctr (hQ q) (by omega) hnext)
      (pkeep_ctr (hQ q) (by omega) hnext))
    (mem_spconv hS (.re _ d t hnb hbd) (pkeep_ctr (hQ q) (Nat.zero_le _) ht) (pkeep_pl t))
  rwa [Nat.sub_zero] at this

/-- 停止規則 1 本の模倣（疎版）。 -/
theorem psim_halt (hS : ∀ s, s ∈ ss) (hQ : ∀ q, q ∈ qs)
    {p : Q} {s t : S} {d : Dir} {h : P}
    (hr : (⟨p, s, t, d, .halt h⟩ : Rule Q P S) ∈ T) (pos : Int) (tape : Int → S)
    (hs : tape pos = s) :
    StepN (spconv T L qs ss) 1
      (penc T L ⟨.go p, pos, tape⟩) (penc T L ⟨.halt h, pos + mv d, upd tape pos t⟩) := by
  have hk := PKind.ahalt (L := L) p s t d h hr
  have kp : pkeepSym T L qs (.ctr (L.loc p) s) = true :=
    pkeep_ctr (hQ p) (Nat.le_refl _) (needB_read' hr)
  refine StepN.single (step_of (mem_spconv hS hk kp (pkeep_pl t)) rfl (by simp [penc, hs]) rfl rfl ?_)
  funext j; simp only [penc, upd]
  by_cases h : j = pos <;> simp [h]

/-- 模倣（疎版）: T のステップ c → c' で c' が生きているなら、疎版は penc c から
    ちょうど `pcost c'` ステップで penc c' に達する。 -/
theorem spconv_simulates (hW : ZeroShiftHalts T) (hR : Reversible T) (hG : Good T L)
    (hS : ∀ s, s ∈ ss) (hQ : ∀ q, q ∈ qs) {c c' : Cfg Q P S} (h : Step T c c') (hl : Live T c') :
    StepN (spconv T L qs ss) (pcost L c') (penc T L c) (penc T L c') := by
  obtain ⟨⟨p, s, t, d, q⟩, hr, hst, hs, rfl⟩ := h
  obtain ⟨st, pos, tape⟩ := c
  simp only at hst hs
  subst hst
  cases q with
  | go q =>
    exact psim_go hW hR hG hS hQ hr pos tape hs (needB_next hW hr hl)
  | halt h => exact psim_halt hS hQ hr pos tape hs

/-- T が c で止まっているなら、密な版も penc c で止まっている。 -/
theorem pconv_halted (hW : ZeroShiftHalts T) (hG : Good T L) {c : Cfg Q P S} (hH : Halted T c) :
    Halted (pconv T L ss) (penc T L c) := by
  intro c' ⟨ρ, hρ, hst, hs, _⟩
  obtain ⟨st, pos, tape⟩ := c
  cases st with
  | halt h => simp [penc] at hst
  | go p =>
    simp only [penc, if_pos] at hst hs
    simp only [Tgt.go.injEq] at hst hs
    rcases pkind_of_mem hW hρ with ⟨p', s', t', d', q', hr, hd⟩ | ⟨p', s', t', d', h', hr⟩ |
        ⟨b, d, s, hb, hbd⟩ | ⟨b, d, j, s, hb, hbd, h1, h2⟩ | ⟨b, d, e, s, hb, hbd, h1⟩ |
        ⟨b, d, s, hb, hbd⟩ <;>
    simp only [PSt.z.injEq, KSym.ctr.injEq, reduceCtorEq] at hst hs
    · obtain ⟨_, h2⟩ := hst
      obtain ⟨h3, h4⟩ := hs
      obtain rfl := hG.inj _ _ h2 h3
      exact hH _ ⟨_, hr, rfl, h4, rfl⟩
    · obtain ⟨_, h2⟩ := hst
      obtain ⟨h3, h4⟩ := hs
      obtain rfl := hG.inj _ _ h2 h3
      exact hH _ ⟨_, hr, rfl, h4, rfl⟩
    · obtain ⟨h1, h2⟩ := hst
      exact stable_ne hG hbd h1 h2
    · obtain ⟨h1, h2⟩ := hst
      exact stable_ne hG hbd h1 h2

theorem spconv_halted (hW : ZeroShiftHalts T) (hG : Good T L) {c : Cfg Q P S} (hH : Halted T c) :
    Halted (spconv T L qs ss) (penc T L c) :=
  Halted.mono (fun _ h => spconv_sub h) (pconv_halted hW hG hH)

theorem pcost_pos {c' : Cfg Q P S} : 1 ≤ pcost L c' := by
  unfold pcost; split <;> omega

/-! ## 5. 多ステップ -/

/-- (前向き) T が n ステップで疑似状態の停止配置 cf に達するなら、疎版は penc c から
    N ≥ n ステップで penc cf に達して止まる。 -/
theorem spconv_haltsIn (hW : ZeroShiftHalts T) (hR : Reversible T) (hG : Good T L)
    (hS : ∀ s, s ∈ ss) (hQ : ∀ q, q ∈ qs) :
    ∀ {n : Nat} {c cf : Cfg Q P S}, HaltsIn T n c cf → (∃ h, cf.st = .halt h) →
      ∃ N, n ≤ N ∧ HaltsIn (spconv T L qs ss) N (penc T L c) (penc T L cf) :=
  haltsIn_of_sim _ _ _ (fun _ => pcost_pos)
    (fun h₁ hH hf => spconv_simulates hW hR hG hS hQ h₁ (live_of_stepN hH.1 hf))
    (fun hH _ => spconv_halted hW hG hH)

/-- (逆向き) T の c からの実行が疑似状態以外で止まらないなら、疎版が penc c から止まるとき
    T も c から止まり、停止配置は符号化で対応する。 -/
theorem spconv_haltsIn_rev (hW : ZeroShiftHalts T) (hD : Deterministic T) (hR : Reversible T)
    (hG : Good T L) (hS : ∀ s, s ∈ ss) (hQ : ∀ q, q ∈ qs) :
    ∀ (N : Nat) {c : Cfg Q P S} {e : Cfg PSt P (KSym S)}, NoStuck T c →
      HaltsIn (spconv T L qs ss) N (penc T L c) e →
      ∃ n cf, HaltsIn T n c cf ∧ e = penc T L cf :=
  haltsIn_rev_of_sim _ _ (NoStuck T) (Deterministic.mono (fun _ h => spconv_sub h) (pconv_det hW hD hG))
    (fun _ => pcost_pos) nostuck_step
    (fun hns h₁ => spconv_simulates hW hR hG hS hQ h₁ (live_of_nostuck (nostuck_step hns h₁)))
    (fun _ hH => spconv_halted hW hG hH)

end Sim

/-! ## 6. 主定理 -/

section Main
variable {T : Machine Q P S} {L : Layout Q} {qs : List Q} {ss : List S}

/-- **1 ブロック 3 状態の変換の疎版の主定理**（具体機械への適用用）。E = penc T L。
    1. 決定的・可逆
    2. 生きている行き先への 1 ステップは `pcost` ステップで模倣
    3. 疑似状態で止まる実行は、E で対応する配置で止まる（前向き）
    4. `NoStuck T c` なら、疎版の停止は T の停止に対応（逆向き）
    5. `NoStuck T c` なら、停止しないことが対応 -/
theorem spconv_main (hW : ZeroShiftHalts T) (hD : Deterministic T) (hR : Reversible T)
    (hQ : ∀ q, q ∈ qs) (hS : ∀ s, s ∈ ss) (hG : Good T L) :
    Deterministic (spconv T L qs ss) ∧ Reversible (spconv T L qs ss) ∧
    (∀ c c' : Cfg Q P S, Step T c c' → Live T c' →
      StepN (spconv T L qs ss) (pcost L c') (penc T L c) (penc T L c')) ∧
    (∀ (n : Nat) (c cf : Cfg Q P S), HaltsIn T n c cf → (∃ h, cf.st = .halt h) →
      ∃ N, n ≤ N ∧ HaltsIn (spconv T L qs ss) N (penc T L c) (penc T L cf)) ∧
    (∀ (N : Nat) (c : Cfg Q P S) (e : Cfg PSt P (KSym S)), NoStuck T c →
      HaltsIn (spconv T L qs ss) N (penc T L c) e →
      ∃ n cf, HaltsIn T n c cf ∧ e = penc T L cf) ∧
    (∀ c : Cfg Q P S, NoStuck T c → ((∀ n cf, ¬ HaltsIn T n c cf) ↔
      (∀ N e, ¬ HaltsIn (spconv T L qs ss) N (penc T L c) e))) := by
  refine ⟨Deterministic.mono (fun _ h => spconv_sub h) (pconv_det hW hD hG),
    Reversible.mono (fun _ h => spconv_sub h) (pconv_rev hW hR hG),
    fun _ _ h hl => spconv_simulates hW hR hG hS hQ h hl,
    fun _ _ _ h hf => spconv_haltsIn hW hR hG hS hQ h hf,
    fun N _ _ hns h => spconv_haltsIn_rev hW hD hR hG hS hQ N hns h, ?_⟩
  intro c hns
  exact diverges_iff_of
    (fun n cf hn => let ⟨N, _, hN'⟩ := spconv_haltsIn hW hR hG hS hQ hn (hns n cf hn); ⟨N, _, hN'⟩)
    (fun N e he => let ⟨n, cf, hn, _⟩ := spconv_haltsIn_rev hW hD hR hG hS hQ N hns he; ⟨n, cf, hn⟩)

end Main

/-! ## 7. 仮定が空でないことの確認（KState.lean の例 T0） -/

namespace Example
open URTM.KState.Example

/-- T0 の状態を 1 個ずつのブロックに分けたもの。 -/
def L0 : Layout Bool := layoutOf T0 [[false], [true]]

theorem L0_good : GoodL T0 L0 [false, true] := by decide

/-- 疎版の決定性・可逆性をカーネルの `decide` で直接確かめる（主定理とは独立）。 -/
theorem T0p_det_rev_decide : Deterministic (spconv T0 L0 [false, true] [false, true]) ∧
    Reversible (spconv T0 L0 [false, true] [false, true]) := by
  constructor <;> decide

end Example

end URTM.KStatePure
