/-
  定理 A の疎版（docs/15_sparse_counters_2026-09-27.md）の一般の模倣証明。

  `conv T qs ss`（KState.lean）の計数記号 `[i, s]` のうち、

      ∃ q ∈ qs, lo(dir q) ≤ i ≤ off(q) ∧ s ∈ need(q)
      need(q) = {q で読む記号} ∪ {q に入る規則が書く記号}

  を満たすものだけを残し（`keepSym`）、読む記号か書く記号が落ちた規則を落とした機械
  `sconv T qs ss := (conv T qs ss).filter keepRule` を扱う。番号は `canonOff T qs`
  （状態リスト `qs` の並び順で決まる）なので、疎になる並びは `qs` の並べ替えで選ぶ。
  `tools/kstate_sparse_k4.py` の `Sparse` と同じ定義（記号の条件 lo ≤ i ≤ off(q) と need）。

  主定理（ファイル末尾 `sconv_main`）:
  * 決定性・可逆性（密な版の部分集合なので自動）
  * T の 1 ステップ c → c' は、c' が「生きている」（疑似状態か、次の規則がある）なら
    密な版と同じ `cost c'` ステップで enc c → enc c' と模倣される
  * 停止配置が疑似状態 halt/null の実行は、同じ停止配置の符号化で止まる（前向き）
  * T の c からの実行が「疑似状態以外で止まらない」（`NoStuck T c`）なら、
    疎版の停止は T の停止に対応し（逆向き）、停止しないことも対応する
  * 規則に現れる記号は `sparseUniverse T qs ss`（`symUniverse` を `keepSym` で絞ったもの）に入る

  模倣が崩れうるのは、T が規則の無い組 (q, s) に出会うとき（行き先の計数が途中で止まる）だけで、
  それは `NoStuck` / `Live` の仮定で排除される。

  未証明の穴・新規公理・native_decide を使わない。mathlib 非依存。
-/
import URTM.SimLemmas

namespace URTM.KStateSparse

set_option linter.unusedSectionVars false

open URTM (Dir)
open URTM.KState
open URTM.SimLemmas (Deterministic.mono Reversible.mono Halted.mono)

variable {Q P S : Type} [DecidableEq Q] [DecidableEq P] [DecidableEq S]

/-! ## 1. 定義 -/

/-- need(q) ∋ s: q で s を読む規則があるか、q に入る規則が s を書く。 -/
def needB (T : Machine Q P S) (q : Q) (s : S) : Bool :=
  T.any (fun r => (decide (r.p = q) && decide (r.s = s)) || (decide (r.q = .go q) && decide (r.t = s)))

/-- 残す記号: 素の記号はすべて、計数記号 `[i, s]` は lo(dir q) ≤ i ≤ off q かつ s ∈ need(q) の q があるとき。 -/
def keepSym (T : Machine Q P S) (off : Q → Nat) (mp : Nat) (qs : List Q) : KSym S → Bool
  | .pl _ => true
  | .ctr i s => qs.any (fun q => decide (lo mp (dir T q) ≤ i) && decide (i ≤ off q) && needB T q s)

/-- 残す規則: 読む記号と書く記号の両方が残るもの。 -/
def keepRule (T : Machine Q P S) (off : Q → Nat) (mp : Nat) (qs : List Q)
    (ρ : Rule KSt P (KSym S)) : Bool :=
  keepSym T off mp qs ρ.s && keepSym T off mp qs ρ.t

/-- 番号付け `off` を与えた疎版。 -/
def sconvWith (T : Machine Q P S) (off : Q → Nat) (mp mm : Nat) (ss : List S) (qs : List Q) :
    Machine KSt P (KSym S) :=
  (convWith T off mp mm ss).filter (keepRule T off mp qs)

/-- **定理 A の疎版**（関数）。番号は `canonOff T qs`。 -/
def sconv (T : Machine Q P S) (qs : List Q) (ss : List S) : Machine KSt P (KSym S) :=
  sconvWith T (canonOff T qs) (plusList T qs).length (minusList T qs).length ss qs

/-- 疎版の記号の全体。 -/
def sparseUniverse (T : Machine Q P S) (qs : List Q) (ss : List S) : List (KSym S) :=
  (symUniverse qs.length ss).filter (keepSym T (canonOff T qs) (plusList T qs).length qs)

/-- 配置が「生きている」: 疑似状態にいるか、次に適用できる規則がある。 -/
def Live (T : Machine Q P S) (c : Cfg Q P S) : Prop :=
  (∃ h, c.st = .halt h) ∨ ∃ c', Step T c c'

/-- c からの実行は疑似状態以外で止まらない（規則の無い組 (q, s) に出会わない）。 -/
def NoStuck (T : Machine Q P S) (c : Cfg Q P S) : Prop :=
  ∀ n e, HaltsIn T n c e → ∃ h, e.st = .halt h

/-! ## 2. 基本の補題 -/

section Basic
variable {T : Machine Q P S}

theorem needB_read' {r : Rule Q P S} (hr : r ∈ T) : needB T r.p r.s = true := by
  unfold needB; rw [List.any_eq_true]; exact ⟨_, hr, by simp⟩

theorem needB_write {p q : Q} {s t : S} {d : Dir}
    (hr : (⟨p, s, t, d, .go q⟩ : Rule Q P S) ∈ T) : needB T q t = true := by
  unfold needB; rw [List.any_eq_true]; exact ⟨_, hr, by simp⟩

variable {off : Q → Nat} {mp mm : Nat} {ss : List S} {qs : List Q}

theorem keep_ctr {q : Q} (hq : q ∈ qs) {i : Nat} {s : S} (h1 : lo mp (dir T q) ≤ i) (h2 : i ≤ off q)
    (h3 : needB T q s = true) : keepSym T off mp qs (.ctr i s) = true := by
  unfold keepSym; rw [List.any_eq_true]; exact ⟨q, hq, by simp [h1, h2, h3]⟩

theorem keep_pl (x : S) : keepSym T off mp qs (.pl x) = true := rfl

theorem sconv_sub {ρ : Rule KSt P (KSym S)} (h : ρ ∈ sconvWith T off mp mm ss qs) :
    ρ ∈ convWith T off mp mm ss :=
  (List.mem_filter.1 h).1

theorem mem_sconv (hS : ∀ s, s ∈ ss) {ρ : Rule KSt P (KSym S)} (hk : Kind T off mp mm ρ)
    (h1 : keepSym T off mp qs ρ.s = true) (h2 : keepSym T off mp qs ρ.t = true) :
    ρ ∈ sconvWith T off mp mm ss qs :=
  List.mem_filter.2 ⟨mem_of_kind hS hk, by simp [keepRule, h1, h2]⟩

theorem off_ge_lo (hN : GoodNum T off mp mm) (q : Q) : lo mp (dir T q) ≤ off q := by
  rcases dir_cases T q with h | h
  · have := hN.rngL q h; rw [h]; simp; omega
  · have := hN.rngR q h; rw [h]; simp; omega

end Basic

/-! ## 3. 1 ステップの模倣 -/

/-- 実状態へ移るステップの行き先が生きているなら、行き先の記号は行き先の状態の need に入る。 -/
theorem needB_next {T : Machine Q P S} (hW : ZeroShiftHalts T) {p q : Q} {s t : S} {d : Dir}
    (hr : (⟨p, s, t, d, .go q⟩ : Rule Q P S) ∈ T) {pos : Int} {tape : Int → S}
    (hl : Live T ⟨.go q, pos + mv d, upd tape pos t⟩) : needB T q (tape (pos + mv d)) = true := by
  have hδ : mv d ≠ 0 := mv_ne_zero (go_dir_LR hW hr rfl)
  rcases hl with ⟨_, hh⟩ | ⟨_, r', hr', hst', hs', _⟩
  · cases hh
  · dsimp only at hst' hs'
    injection hst' with e
    have hu : upd tape pos t (pos + mv d) = tape (pos + mv d) := by
      simp only [upd]; rw [if_neg (by omega)]
    rw [← hu, hs', e]
    exact needB_read' hr'


section Sim
variable {T : Machine Q P S} {off : Q → Nat} {mp mm : Nat} {ss : List S} {qs : List Q}

/-- 実状態へ移る規則 1 本の模倣（疎版）。行き先の記号が q の need に入っていること。
    往復で使う計数記号 [i, t]・[j, s₂] はどれも lo(dir q) ≤ i ≤ off q で need(q) に入るので残っている。 -/
theorem ssim_go (hW : ZeroShiftHalts T) (hR : Reversible T) (hN : GoodNum T off mp mm)
    (hS : ∀ s, s ∈ ss) (hQ : ∀ q, q ∈ qs) {p q : Q} {s t : S} {d : Dir}
    (hr : (⟨p, s, t, d, .go q⟩ : Rule Q P S) ∈ T) (pos : Int) (tape : Int → S)
    (hs : tape pos = s) (hnext : needB T q (tape (pos + mv d)) = true) :
    StepN (sconvWith T off mp mm ss qs) (3 + 2 * (off q - lo mp (dir T q)))
      (enc T off ⟨.go p, pos, tape⟩) (enc T off ⟨.go q, pos + mv d, upd tape pos t⟩) := by
  have hdq : dir T q = d := dir_eq hW hR hr rfl
  have hd : d = .L ∨ d = .R := go_dir_LR hW hr rfl
  have hrng : lo mp d ≤ off q ∧ off q ≤ hi mp mm d := by
    rcases hd with rfl | rfl
    · have := hN.rngL q hdq; simp; omega
    · have := hN.rngR q hdq; simp; omega
  have kc : ∀ {i x}, lo mp d ≤ i → i ≤ off q → needB T q x = true → keepSym T off mp qs (.ctr i x) = true :=
    fun h1 h2 h3 => keep_ctr (hQ q) (by rw [hdq]; exact h1) h2 h3
  have ht := needB_write hr
  subst hs
  rw [enc_go, enc_go, hdq]
  exact sim_go_gen hd hrng.1
    (mem_sconv hS (.r1go p _ t d q hr hd) (keep_ctr (hQ p) (off_ge_lo hN p) (Nat.le_refl _) (needB_read' hr))
      (kc hrng.1 (Nat.le_refl _) ht))
    (mem_sconv hS (.r2 d _ hd (by omega)) (keep_pl _) (kc (Nat.le_refl _) hrng.1 hnext))
    (fun i h1 h2 => mem_sconv hS (.r3 d i t hd h1 (by omega)) (kc (by omega) h2 ht) (kc (by omega) (by omega) ht))
    (fun j h1 h2 => mem_sconv hS (.r5 d j _ hd h1 (by omega)) (kc h1 (by omega) hnext)
      (kc (by omega) (by omega) hnext))
    (mem_sconv hS (.r4 d t hd (by omega)) (kc (Nat.le_refl _) hrng.1 ht) (keep_pl t))

/-- 停止規則 1 本の模倣（疎版）。 -/
theorem ssim_halt (hN : GoodNum T off mp mm) (hS : ∀ s, s ∈ ss) (hQ : ∀ q, q ∈ qs)
    {p : Q} {s t : S} {d : Dir} {h : P}
    (hr : (⟨p, s, t, d, .halt h⟩ : Rule Q P S) ∈ T) (pos : Int) (tape : Int → S)
    (hs : tape pos = s) :
    StepN (sconvWith T off mp mm ss qs) 1
      (enc T off ⟨.go p, pos, tape⟩) (enc T off ⟨.halt h, pos + mv d, upd tape pos t⟩) := by
  have hk := Kind.r1halt (T := T) (off := off) (mp := mp) (mm := mm) p s t d h hr
  have kp : keepSym T off mp qs (.ctr (off p) s) = true :=
    keep_ctr (hQ p) (off_ge_lo hN p) (Nat.le_refl _) (needB_read' hr)
  refine StepN.single (step_of (mem_sconv hS hk kp (keep_pl t)) rfl (by simp [enc, hs]) rfl rfl ?_)
  funext j; simp only [enc, upd]
  by_cases h : j = pos <;> simp [h]

/-- 模倣（疎版）: T のステップ c → c' で c' が生きているなら、疎版は enc c から
    ちょうど `cost c'` ステップで enc c' に達する。 -/
theorem sconvWith_simulates (hW : ZeroShiftHalts T) (hR : Reversible T) (hN : GoodNum T off mp mm)
    (hS : ∀ s, s ∈ ss) (hQ : ∀ q, q ∈ qs) {c c' : Cfg Q P S} (h : Step T c c') (hl : Live T c') :
    StepN (sconvWith T off mp mm ss qs) (cost T off mp c') (enc T off c) (enc T off c') := by
  obtain ⟨⟨p, s, t, d, q⟩, hr, hst, hs, rfl⟩ := h
  obtain ⟨st, pos, tape⟩ := c
  simp only at hst hs
  subst hst
  cases q with
  | go q =>
    exact ssim_go hW hR hN hS hQ hr pos tape hs (needB_next hW hr hl)
  | halt h => exact ssim_halt hN hS hQ hr pos tape hs

theorem sconvWith_halted (hW : ZeroShiftHalts T) (hinj : ∀ a b, off a = off b → a = b)
    {c : Cfg Q P S} (hH : Halted T c) : Halted (sconvWith T off mp mm ss qs) (enc T off c) :=
  Halted.mono (fun _ h => sconv_sub h) (convWith_halted hW hinj hH)

theorem live_of_stepN {n : Nat} {c cf : Cfg Q P S} (h : StepN T n c cf) (hf : ∃ h, cf.st = .halt h) :
    Live T c := by
  cases h with
  | refl => exact .inl hf
  | cons h₁ _ => exact .inr ⟨_, h₁⟩

theorem nostuck_step {c c₁ : Cfg Q P S} (h : NoStuck T c) (h₁ : Step T c c₁) : NoStuck T c₁ :=
  fun n e ⟨hs, hH⟩ => h (n + 1) e ⟨StepN.cons h₁ hs, hH⟩

theorem live_of_nostuck {c : Cfg Q P S} (h : NoStuck T c) : Live T c := by
  by_cases hc : Halted T c
  · exact .inl (h 0 c ⟨StepN.refl _, hc⟩)
  · exact .inr (exists_step_of_not_halted hc)

/-! ## 4. 多ステップ -/

/-- (前向き) T が n ステップで疑似状態の停止配置 cf に達するなら、疎版は enc c から
    N ≥ n ステップで enc cf に達して止まる。 -/
theorem sconvWith_haltsIn (hW : ZeroShiftHalts T) (hR : Reversible T) (hN : GoodNum T off mp mm)
    (hS : ∀ s, s ∈ ss) (hQ : ∀ q, q ∈ qs) :
    ∀ {n : Nat} {c cf : Cfg Q P S}, HaltsIn T n c cf → (∃ h, cf.st = .halt h) →
      ∃ N, n ≤ N ∧ HaltsIn (sconvWith T off mp mm ss qs) N (enc T off c) (enc T off cf) :=
  haltsIn_of_sim _ _ _ (fun _ => cost_pos)
    (fun h₁ hH hf => sconvWith_simulates hW hR hN hS hQ h₁ (live_of_stepN hH.1 hf))
    (fun hH _ => sconvWith_halted hW hN.inj hH)

/-- (逆向き) T の c からの実行が疑似状態以外で止まらないなら、疎版が enc c から止まるとき
    T も c から止まり、停止配置は符号化で対応する。 -/
theorem sconvWith_haltsIn_rev (hW : ZeroShiftHalts T) (hD : Deterministic T) (hR : Reversible T)
    (hN : GoodNum T off mp mm) (hS : ∀ s, s ∈ ss) (hQ : ∀ q, q ∈ qs) :
    ∀ (N : Nat) {c : Cfg Q P S} {e : Cfg KSt P (KSym S)}, NoStuck T c →
      HaltsIn (sconvWith T off mp mm ss qs) N (enc T off c) e →
      ∃ n cf, HaltsIn T n c cf ∧ e = enc T off cf :=
  haltsIn_rev_of_sim _ _ (NoStuck T) (Deterministic.mono (fun _ h => sconv_sub h) (convWith_det hW hD hN.inj))
    (fun _ => cost_pos) nostuck_step
    (fun hns h₁ => sconvWith_simulates hW hR hN hS hQ h₁ (live_of_nostuck (nostuck_step hns h₁)))
    (fun _ hH => sconvWith_halted hW hN.inj hH)

end Sim

/-! ## 5. 主定理（標準の番号付け `canonOff T qs`） -/

section Main
variable {T : Machine Q P S} {qs : List Q} {ss : List S}

/-- 疎版は密な版の部分集合。 -/
theorem sconv_sub_conv {ρ : Rule KSt P (KSym S)} (h : ρ ∈ sconv T qs ss) : ρ ∈ conv T qs ss :=
  sconv_sub h

theorem sconv_symbols_mem (hW : ZeroShiftHalts T) (hQ : ∀ q, q ∈ qs) (hS : ∀ s, s ∈ ss)
    {ρ : Rule KSt P (KSym S)} (hρ : ρ ∈ sconv T qs ss) :
    ρ.s ∈ sparseUniverse T qs ss ∧ ρ.t ∈ sparseUniverse T qs ss := by
  have hc := conv_symbols_mem hW hQ hS (sconv_sub_conv hρ)
  have hk := (List.mem_filter.1 hρ).2
  simp only [keepRule, Bool.and_eq_true] at hk
  exact ⟨List.mem_filter.2 ⟨hc.1, hk.1⟩, List.mem_filter.2 ⟨hc.2, hk.2⟩⟩

/-- **定理 A の疎版の主定理**（具体機械への適用用）。E = enc T (canonOff T qs)。
    1. 決定的・可逆
    2. 生きている行き先への 1 ステップは密な版と同じステップ数で模倣
    3. 疑似状態で止まる実行は、E で対応する配置で止まる（前向き）
    4. `NoStuck T c` なら、疎版の停止は T の停止に対応（逆向き）
    5. `NoStuck T c` なら、停止しないことが対応
    6. 規則の記号は `sparseUniverse T qs ss` に入る -/
theorem sconv_main (hW : ZeroShiftHalts T) (hD : Deterministic T) (hR : Reversible T)
    (hQ : ∀ q, q ∈ qs) (hS : ∀ s, s ∈ ss) :
    Deterministic (sconv T qs ss) ∧ Reversible (sconv T qs ss) ∧
    (∀ c c' : Cfg Q P S, Step T c c' → Live T c' →
      StepN (sconv T qs ss) (cost T (canonOff T qs) (plusList T qs).length c')
        (enc T (canonOff T qs) c) (enc T (canonOff T qs) c')) ∧
    (∀ (n : Nat) (c cf : Cfg Q P S), HaltsIn T n c cf → (∃ h, cf.st = .halt h) →
      ∃ N, n ≤ N ∧ HaltsIn (sconv T qs ss) N (enc T (canonOff T qs) c) (enc T (canonOff T qs) cf)) ∧
    (∀ (N : Nat) (c : Cfg Q P S) (e : Cfg KSt P (KSym S)), NoStuck T c →
      HaltsIn (sconv T qs ss) N (enc T (canonOff T qs) c) e →
      ∃ n cf, HaltsIn T n c cf ∧ e = enc T (canonOff T qs) cf) ∧
    (∀ c : Cfg Q P S, NoStuck T c → ((∀ n cf, ¬ HaltsIn T n c cf) ↔
      (∀ N e, ¬ HaltsIn (sconv T qs ss) N (enc T (canonOff T qs) c) e))) ∧
    (∀ ρ ∈ sconv T qs ss, ρ.s ∈ sparseUniverse T qs ss ∧ ρ.t ∈ sparseUniverse T qs ss) := by
  have hN := canon_good (T := T) hQ
  have hdr := conv_det_rev (ss := ss) hW hD hR hQ
  refine ⟨Deterministic.mono (fun _ h => sconv_sub_conv h) hdr.1,
    Reversible.mono (fun _ h => sconv_sub_conv h) hdr.2,
    fun _ _ h hl => sconvWith_simulates hW hR hN hS hQ h hl,
    fun _ _ _ h hf => sconvWith_haltsIn hW hR hN hS hQ h hf,
    fun N _ _ hns h => sconvWith_haltsIn_rev hW hD hR hN hS hQ N hns h, ?_,
    fun _ h => sconv_symbols_mem hW hQ hS h⟩
  intro c hns
  exact diverges_iff_of
    (fun n cf hn => let ⟨N, _, hN'⟩ := sconvWith_haltsIn hW hR hN hS hQ hn (hns n cf hn); ⟨N, _, hN'⟩)
    (fun N e he => let ⟨n, cf, hn, _⟩ := sconvWith_haltsIn_rev hW hD hR hN hS hQ N hns he; ⟨n, cf, hn⟩)

open URTM.CTSH (CTSH Ch CHaltsIn) in
/-- **CTSH 模倣の合成**。元機械 T の CTSH 模倣（停止配置 fin はどれも疑似状態、初期配置 a から疑似状態以外で
    止まらない）を、変換 T'（符号化 E）の主定理の 3 項（前向き・`NoStuck` の下の逆向きと非停止）に通すと、
    T' の CTSH 模倣（停止配置は E ∘ fin）が得られる。 -/
theorem compose_ctsh {Q' S' : Type} {T' : Machine Q' P S'} (E : Cfg Q P S → Cfg Q' P S')
    {C : CTSH} {w : List Ch} {a : Cfg Q P S} {fin : List Ch → Nat → List Ch → Cfg Q P S}
    (hfin : ∀ vf mf rm, ∃ h, (fin vf mf rm).st = .halt h) (hns : NoStuck T a)
    (hu : (∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) → ∃ N rm, n ≤ N ∧ HaltsIn T N a (fin vf mf rm)) ∧
      (∀ N e, HaltsIn T N a e → ∃ n vf mf rm, CHaltsIn C n (w, 0) (vf, mf) ∧ e = fin vf mf rm) ∧
      ((∀ n f, ¬ CHaltsIn C n (w, 0) f) ↔ (∀ N e, ¬ HaltsIn T N a e)))
    (fwd : ∀ (n : Nat) (c cf : Cfg Q P S), HaltsIn T n c cf → (∃ h, cf.st = .halt h) →
      ∃ N, n ≤ N ∧ HaltsIn T' N (E c) (E cf))
    (bwd : ∀ (N : Nat) (c : Cfg Q P S) (e : Cfg Q' P S'), NoStuck T c → HaltsIn T' N (E c) e →
      ∃ n cf, HaltsIn T n c cf ∧ e = E cf)
    (div : ∀ c : Cfg Q P S, NoStuck T c → ((∀ n cf, ¬ HaltsIn T n c cf) ↔ (∀ N e, ¬ HaltsIn T' N (E c) e))) :
    (∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) → ∃ N rm, n ≤ N ∧ HaltsIn T' N (E a) (E (fin vf mf rm))) ∧
    (∀ N e, HaltsIn T' N (E a) e → ∃ n vf mf rm, CHaltsIn C n (w, 0) (vf, mf) ∧ e = E (fin vf mf rm)) ∧
    ((∀ n f, ¬ CHaltsIn C n (w, 0) f) ↔ (∀ N e, ¬ HaltsIn T' N (E a) e)) := by
  refine ⟨fun n vf mf h => ?_, fun N e he => ?_, hu.2.2.trans (div a hns)⟩
  · obtain ⟨N, rm, hN, hh⟩ := hu.1 n vf mf h
    obtain ⟨N', hN', hh'⟩ := fwd N _ _ hh (hfin vf mf rm)
    exact ⟨N', rm, by omega, hh'⟩
  · obtain ⟨n, cf, hcf, rfl⟩ := bwd N _ e hns he
    obtain ⟨k, vf, mf, rm, hk, rfl⟩ := hu.2.1 n cf hcf
    exact ⟨k, vf, mf, rm, hk, rfl⟩

end Main

/-! ## 6. 仮定が空でないことの確認（KState.lean の例 T0） -/

namespace Example
open URTM.KState.Example

/-- 疎版の決定性・可逆性をカーネルの `decide` で直接確かめる（主定理とは独立）。 -/
theorem T0s_det_rev_decide : Deterministic (sconv T0 [false, true] [false, true]) ∧
    Reversible (sconv T0 [false, true] [false, true]) := by
  constructor <;> decide

end Example

end URTM.KStateSparse
