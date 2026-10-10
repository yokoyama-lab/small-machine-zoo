/-
  記号を減らす変換（Morita 2017 Thm 5.4 の改良、docs/23）で作った 2 記号機械の一般の模倣定理。

  T の記号 s を長さ k のビット列 `code s` に置き、T の配置 (p, x, g) を
  T̃ の配置 (ρ p, k·x + ce p, bits g) に対応させる（`enc`）。ρ p は「p を読み始める状態」
  （併合した機械では併合後の名前）、ce p はブロックの中でヘッドが居る桁（左端 0 か右端 k−1）。

  ここでは変換そのもの（符号・先書き v・経路の型・向き・状態の併合）を関数として書くのではなく、
  **出来上がった表 M について、T の規則ごとの有限の検査**（`certB`、具体機械ではカーネルの `decide`）から
  模倣を導く:

  * 規則 r = [p, s, t, d, q]（d = R / L）と、d の側の隣のブロックの記号 u のすべてについて、
    2 ブロックの窓 `code s ++ code u`（L なら `code u ++ code s`）の上で M を `cost r` ステップ動かすと、
    窓から出ずに、窓 `code t ++ code u`（L なら `code u ++ code t`）・状態 ρ q・桁 ce q に着く（`stepCert`）。
  * T の停止規則 [p, s, s, 0, halt] の読み (p, s) では、1 ブロックの窓 `code s` の上で M が窓から出ずに
    止まる（`hrun`）。

  M の 1 ステップは読んだ 1 マスと規則表だけで決まるので、窓の上の実行は、窓の外が何であっても
  両側無限のテープの上の実行になる（`lrun_sound`・`hrun_sound`）。符号・先書き・経路の型・向き・併合は
  どれも「どの表ができるか」にしか効かないので、この検査が通る限り一般の定理に入る。

  併合した機械は、T が規則の無い配置（停止規則でもない）で止まる場合の停止を保存しない（未定義の読みを
  相手の規則で埋めるため）。主定理 `fs_simulates` はそれを、T の CTSH 模倣の逆向き（停止配置はどれも
  疑似状態）から「T の実行は停止規則の読みでしか止まらない」を導いて回避する（NoStuck と同じ内容）。

  主定理:
  * `step_sim`   : T の停止しない規則による 1 ステップを、M は enc から enc へちょうど `cost r` ステップで模倣する。
  * `halt_sim`   : T が停止規則を適用する配置 c では、M は enc c から `pre c` に達して止まる。
  * `fs_simulates` : T の CTSH 模倣（停止の 3 項）を M に移す（M の決定性を仮定。具体機械では `decide`）。

  mathlib 非依存。未証明の穴・新規公理・native_decide を使わない。
-/
import URTM.SimLemmas
import URTM.Conv55

namespace URTM.FewSym

open URTM URTM.KState URTM.CTSH URTM.SimLemmas
open URTM.Conv55 (upd_eq upd_ne upd_self)

variable {Q P S Q' : Type}

/-! ## 1. 有限の窓の上の実行 -/

/-- 窓の上の配置: 状態・窓の中のヘッドの位置・窓の中身。 -/
structure LCfg (Q' : Type) where
  st : Q'
  pos : Nat
  w : List Bool
  deriving DecidableEq

section Local
variable [DecidableEq Q']

/-- 表引き（先頭から最初に一致する規則）。 -/
def look (M : Machine Q' P Bool) (q : Q') (b : Bool) : Option (Rule Q' P Bool) :=
  M.find? (fun r => decide (r.p = q) && decide (r.s = b))

/-- 窓の上の 1 ステップ。規則が無い・疑似状態へ入る・窓から出る場合は `none`。 -/
def lstep (M : Machine Q' P Bool) (c : LCfg Q') : Option (LCfg Q') :=
  match c.w[c.pos]? with
  | none => none
  | some b =>
    match look M c.st b with
    | none => none
    | some r =>
      match r.q, r.d with
      | .go q', .L => if c.pos = 0 then none else some ⟨q', c.pos - 1, c.w.set c.pos r.t⟩
      | .go q', .R =>
        if c.pos + 1 < c.w.length then some ⟨q', c.pos + 1, c.w.set c.pos r.t⟩ else none
      | _, _ => none

/-- 窓の上でちょうど n ステップ。 -/
def lrun (M : Machine Q' P Bool) : Nat → LCfg Q' → Option (LCfg Q')
  | 0, c => some c
  | n + 1, c =>
    match lstep M c with
    | none => none
    | some c' => lrun M n c'

/-- 窓の中を読んでいて、適用できる規則が無い。 -/
def lhalt (M : Machine Q' P Bool) (c : LCfg Q') : Bool :=
  match c.w[c.pos]? with
  | none => false
  | some b => (look M c.st b).isNone

/-- 止まるまで（高々 n ステップ）窓の上で動かす。窓から出る・疑似状態へ入るなら `none`。 -/
def hrun (M : Machine Q' P Bool) : Nat → LCfg Q' → Option (LCfg Q')
  | 0, c => if lhalt M c then some c else none
  | n + 1, c =>
    if lhalt M c then some c else
    match lstep M c with
    | none => none
    | some c' => hrun M n c'

end Local

/-! ## 2. 窓を両側無限のテープに埋める -/

/-- テープ g の位置 base から窓 w を上書きしたもの。 -/
def ovl (g : Int → Bool) (base : Int) (w : List Bool) : Int → Bool :=
  fun i => if base ≤ i ∧ i < base + w.length then w.getD (i - base).toNat false else g i

/-- 窓の上の配置を、テープ g の位置 base に置いた配置。 -/
def glob (base : Int) (g : Int → Bool) (c : LCfg Q') : Cfg Q' P Bool :=
  ⟨.go c.st, base + c.pos, ovl g base c.w⟩

theorem ovl_at {g : Int → Bool} {base : Int} {w : List Bool} {p : Nat} {b : Bool}
    (hb : w[p]? = some b) : ovl g base w (base + p) = b := by
  have hp : p < w.length := by
    rcases Nat.lt_or_ge p w.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hb; cases hb
  simp only [ovl]
  rw [if_pos (by omega), show (base + (p : Int) - base).toNat = p by omega, List.getD_eq_getElem?_getD, hb]
  rfl

theorem ovl_set {g : Int → Bool} {base : Int} {w : List Bool} {p : Nat} (hp : p < w.length) (t : Bool) :
    upd (ovl g base w) (base + p) t = ovl g base (w.set p t) := by
  funext i
  simp only [upd, ovl, List.length_set]
  by_cases hi : i = base + p
  · subst hi
    rw [if_pos rfl, if_pos (by omega), show (base + (p : Int) - base).toNat = p by omega,
      List.getD_eq_getElem?_getD, List.getElem?_set_self hp]
    rfl
  · rw [if_neg hi]
    by_cases hin : base ≤ i ∧ i < base + w.length
    · rw [if_pos hin, if_pos hin, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_set_ne (by omega)]
    · rw [if_neg hin, if_neg hin]

theorem ovl_append (g : Int → Bool) (base : Int) (w₁ w₂ : List Bool) :
    ovl g base (w₁ ++ w₂) = ovl (ovl g base w₁) (base + w₁.length) w₂ := by
  funext i
  simp only [ovl, List.length_append]
  by_cases h₁ : base ≤ i ∧ i < base + w₁.length
  · rw [if_pos (by omega), if_neg (by omega), if_pos h₁, List.getD_eq_getElem?_getD,
      List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega)]
  · by_cases h₂ : base + w₁.length ≤ i ∧ i < base + w₁.length + w₂.length
    · rw [if_pos (by push_cast; omega), if_pos (by push_cast; omega), List.getD_eq_getElem?_getD,
        List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
      congr 2; omega
    · rw [if_neg (by push_cast; omega), if_neg (by push_cast; omega), if_neg h₁]

section LocalSound
variable [DecidableEq Q'] {M : Machine Q' P Bool}

theorem look_some {q : Q'} {b : Bool} {r : Rule Q' P Bool} (h : look M q b = some r) :
    r ∈ M ∧ r.p = q ∧ r.s = b := by
  have hm := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  exact ⟨hm, hp⟩

theorem look_none {q : Q'} {b : Bool} (h : look M q b = none) : ∀ r ∈ M, ¬ (r.p = q ∧ r.s = b) := by
  intro r hr hc
  have := List.find?_eq_none.mp h r hr
  simp [hc.1, hc.2] at this

/-- 窓の上の 1 ステップは、窓の外が何であってもテープの上の 1 ステップ。 -/
theorem lstep_sound {c c' : LCfg Q'} (h : lstep M c = some c') (base : Int) (g : Int → Bool) :
    Step M (glob base g c) (glob base g c' : Cfg Q' P Bool) := by
  obtain ⟨st, p, w⟩ := c
  unfold lstep at h
  simp only at h
  split at h
  · cases h
  rename_i b hb
  split at h
  · cases h
  rename_i r hr
  obtain ⟨hrM, hrp, hrs⟩ := look_some hr
  have hp : p < w.length := by
    rcases Nat.lt_or_ge p w.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hb; cases hb
  have hread : ovl g base w (base + p) = r.s := by rw [ovl_at hb, hrs]
  split at h
  · rename_i q' hq hd
    split at h
    · cases h
    · rename_i h0
      cases h
      refine ⟨r, hrM, by simp [glob, hrp], hread, ?_⟩
      simp only [glob, fire, hq, hd, mv]
      rw [← ovl_set hp]
      congr 1
      omega
  · rename_i q' hq hd
    split at h
    · cases h
      refine ⟨r, hrM, by simp [glob, hrp], hread, ?_⟩
      simp only [glob, fire, hq, hd, mv]
      rw [← ovl_set hp]
      congr 1
      omega
    · cases h
  · cases h

theorem lrun_sound : ∀ {n : Nat} {c c' : LCfg Q'}, lrun M n c = some c' → ∀ (base : Int) (g : Int → Bool),
    StepN M n (glob base g c) (glob base g c' : Cfg Q' P Bool)
  | 0, c, c', h, base, g => by
    simp only [lrun, Option.some.injEq] at h; subst h; exact .refl _
  | n + 1, c, c', h, base, g => by
    simp only [lrun] at h
    split at h
    · cases h
    · rename_i c₁ h₁
      exact .cons (lstep_sound h₁ base g) (lrun_sound h base g)

theorem lhalt_sound {c : LCfg Q'} (h : lhalt M c = true) (base : Int) (g : Int → Bool) :
    Halted M (glob base g c : Cfg Q' P Bool) := by
  obtain ⟨st, p, w⟩ := c
  unfold lhalt at h
  simp only at h
  split at h
  · cases h
  rename_i b hb
  intro c' ⟨r, hr, hst, hs, _⟩
  simp only [glob, Tgt.go.injEq] at hst hs
  rw [ovl_at hb] at hs
  have hn : look M st b = none := by
    cases e : look M st b with
    | none => rfl
    | some _ => rw [e] at h; cases h
  exact look_none hn r hr ⟨hst.symm, hs.symm⟩

theorem hrun_sound : ∀ {n : Nat} {c c' : LCfg Q'}, hrun M n c = some c' → ∀ (base : Int) (g : Int → Bool),
    (∃ j, StepN M j (glob base g c) (glob base g c' : Cfg Q' P Bool)) ∧ Halted M (glob base g c' : Cfg Q' P Bool)
  | 0, c, c', h, base, g => by
    simp only [hrun] at h
    split at h
    · rename_i hh; cases h; exact ⟨⟨0, .refl _⟩, lhalt_sound hh base g⟩
    · cases h
  | n + 1, c, c', h, base, g => by
    simp only [hrun] at h
    split at h
    · rename_i hh; cases h; exact ⟨⟨0, .refl _⟩, lhalt_sound hh base g⟩
    · split at h
      · cases h
      · rename_i c₁ h₁
        obtain ⟨⟨j, hj⟩, hH⟩ := hrun_sound h base g
        exact ⟨⟨j + 1, .cons (lstep_sound h₁ base g) hj⟩, hH⟩

end LocalSound

/-! ## 3. ブロックの符号化 -/

/-- テープの符号化: マス i には、ブロック i / k の記号の符号の i % k 桁目。 -/
def bits (code : S → List Bool) (k : Nat) (g : Int → S) (i : Int) : Bool :=
  (code (g (i / k))).getD (i % k).toNat false

theorem divmod_of {k : Nat} (hk : 0 < k) {x i : Int} (h₁ : (k : Int) * x ≤ i) (h₂ : i < k * x + k) :
    i / k = x ∧ i % k = i - k * x :=
  (Int.ediv_emod_unique (by omega)).mpr ⟨by omega, by omega, by omega⟩

theorem div_ne_of {k : Nat} (hk : 0 < k) {x i : Int} (h : ¬ ((k : Int) * x ≤ i ∧ i < k * x + k)) :
    i / k ≠ x := by
  intro e
  have h1 := Int.mul_ediv_add_emod i k
  have h2 := Int.emod_nonneg i (b := k) (by omega)
  have h3 := Int.emod_lt_of_pos i (b := k) (by omega)
  rw [e] at h1
  omega

/-- 1 ブロックの窓: ブロック x の符号を a の符号で上書きしたテープは、a を書いたテープの符号化。 -/
theorem ovl_block {code : S → List Bool} {k : Nat} (hk : 0 < k) (hlen : ∀ s, (code s).length = k)
    (g : Int → S) (x : Int) (a : S) :
    ovl (bits code k g) (k * x) (code a) = bits code k (upd g x a) := by
  funext i
  simp only [ovl, bits, upd, hlen]
  by_cases hin : (k : Int) * x ≤ i ∧ i < k * x + k
  · obtain ⟨hd, hm⟩ := divmod_of hk hin.1 hin.2
    rw [if_pos hin, hd, if_pos rfl, hm]
  · rw [if_neg hin, if_neg (div_ne_of hk hin)]

/-- 2 ブロックの窓。 -/
theorem ovl_block2 {code : S → List Bool} {k : Nat} (hk : 0 < k) (hlen : ∀ s, (code s).length = k)
    (g : Int → S) (x : Int) (a b : S) :
    ovl (bits code k g) (k * x) (code a ++ code b) = bits code k (upd (upd g x a) (x + 1) b) := by
  rw [ovl_append, ovl_block hk hlen, hlen, show (k : Int) * x + k = k * (x + 1) by
    rw [Int.mul_add, Int.mul_one], ovl_block hk hlen]

/-- 符号化の約束: 符号・ブロック長・「読み始める状態」ρ・ブロック内の桁 ce。 -/
structure Enc (Q S Q' : Type) where
  code : S → List Bool
  k : Nat
  ρ : Q → Q'
  ce : Q → Nat

/-- 配置の符号化。 -/
def enc (E : Enc Q S Q') (c : Cfg Q P S) : Cfg Q' P Bool :=
  match c.st with
  | .go p => ⟨.go (E.ρ p), E.k * c.pos + E.ce p, bits E.code E.k c.tape⟩
  | .halt h => ⟨.halt h, E.k * c.pos, bits E.code E.k c.tape⟩

/-! ## 4. 規則ごとの有限の検査 -/

section Cert
variable [DecidableEq Q']

/-- 規則 r（停止しない）と、動く側の隣のブロックの記号 u についての検査。 -/
def stepCert (M : Machine Q' P Bool) (E : Enc Q S Q') (cost : Rule Q P S → Nat) (r : Rule Q P S) (u : S) :
    Bool :=
  decide (1 ≤ cost r) &&
  match r.q, r.d with
  | .go q, .R => decide (lrun M (cost r) ⟨E.ρ r.p, E.ce r.p, E.code r.s ++ E.code u⟩ =
      some ⟨E.ρ q, E.k + E.ce q, E.code r.t ++ E.code u⟩)
  | .go q, .L => decide (lrun M (cost r) ⟨E.ρ r.p, E.k + E.ce r.p, E.code u ++ E.code r.s⟩ =
      some ⟨E.ρ q, E.ce q, E.code u ++ E.code r.t⟩)
  | _, _ => false

/-- 停止の読みで止まるまでの歩数の上限。 -/
def hfuel (E : Enc Q S Q') : Nat := 3 * E.k + 2

/-- 表全体の検査（具体機械ではカーネルの `decide`）。 -/
def certB (T : Machine Q P S) (M : Machine Q' P Bool) (E : Enc Q S Q') (cost : Rule Q P S → Nat)
    (ss : List S) : Bool :=
  T.all fun r =>
    match r.q with
    | .go _ => ss.all (stepCert M E cost r)
    | .halt _ => (hrun M (hfuel E) ⟨E.ρ r.p, E.ce r.p, E.code r.s⟩).isSome

/-- 仮定のまとめ。 -/
structure Hyp (T : Machine Q P S) (M : Machine Q' P Bool) (E : Enc Q S Q') (cost : Rule Q P S → Nat)
    (ss : List S) : Prop where
  hk : 0 < E.k
  hlen : ∀ s, (E.code s).length = E.k
  hS : ∀ s, s ∈ ss
  hC : certB T M E cost ss = true

/-- T が停止規則を適用する配置 c に対応する M の停止配置（ブロックの中で止まるまで進めたもの）。 -/
def pre (M : Machine Q' P Bool) (E : Enc Q S Q') (c : Cfg Q P S) : Cfg Q' P Bool :=
  match c.st with
  | .go p =>
    match hrun M (hfuel E) ⟨E.ρ p, E.ce p, E.code (c.tape c.pos)⟩ with
    | some c' => glob (E.k * c.pos) (bits E.code E.k c.tape) c'
    | none => enc E c
  | .halt _ => enc E c

end Cert

/-! ## 5. 1 ステップの模倣と停止 -/

section Sim
variable [DecidableEq Q'] {T : Machine Q P S} {M : Machine Q' P Bool} {E : Enc Q S Q'}
  {cost : Rule Q P S → Nat} {ss : List S}

theorem cert_step (H : Hyp T M E cost ss) {r : Rule Q P S} (hr : r ∈ T) {q : Q} (hq : r.q = .go q) (u : S) :
    stepCert M E cost r u = true := by
  have := List.all_eq_true.mp H.hC r hr
  rw [hq] at this
  exact List.all_eq_true.mp this u (H.hS u)

/-- **1 ステップの模倣**: T の停止しない規則 r による c → c' を、M は enc c から enc c' へ
    ちょうど `cost r` ステップで。 -/
theorem step_sim (H : Hyp T M E cost ss) {r : Rule Q P S} (hr : r ∈ T) {q : Q} (hq : r.q = .go q)
    {c : Cfg Q P S} (hst : c.st = .go r.p) (hs : c.tape c.pos = r.s) :
    StepN M (cost r) (enc E c) (enc E (fire r c)) := by
  obtain ⟨st, x, g⟩ := c
  simp only at hst hs
  subst hst
  have hc := cert_step H hr hq (g (x + mv r.d))
  unfold stepCert at hc
  rw [hq] at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨-, hc⟩ := hc
  have hk := H.hk
  have hlen := H.hlen
  cases hd : r.d with
  | Z => rw [hd] at hc; simp at hc
  | R =>
    rw [hd] at hc
    simp only [decide_eq_true_eq, mv] at hc
    have := lrun_sound hc (E.k * x) (bits E.code E.k g)
    simp only [glob] at this
    rw [ovl_block2 hk hlen, ← hs, upd_self, upd_self, ovl_block2 hk hlen] at this
    have e1 : upd (upd g x r.t) (x + 1) (g (x + 1)) = upd g x r.t := by
      rw [show g (x + 1) = upd g x r.t (x + 1) from (upd_ne _ _ (by omega)).symm, upd_self]
    rw [e1] at this
    simp only [enc, fire, hq, hd, mv]
    have hp : (E.k : Int) * x + ((E.k + E.ce q : Nat) : Int) = E.k * (x + 1) + E.ce q := by
      rw [Int.mul_add, Int.mul_one]; push_cast; omega
    rw [hp] at this
    exact this
  | L =>
    rw [hd] at hc
    simp only [decide_eq_true_eq, mv] at hc
    have := lrun_sound hc (E.k * (x - 1)) (bits E.code E.k g)
    simp only [glob] at this
    rw [ovl_block2 hk hlen, ovl_block2 hk hlen, show x - 1 + 1 = x by omega] at this
    have e0 : upd (upd g (x - 1) (g (x + -1))) x r.s = g := by
      rw [show x + -1 = x - 1 by omega, upd_self, ← hs, upd_self]
    have e1 : upd (upd g (x - 1) (g (x + -1))) x r.t = upd g x r.t := by
      rw [show x + -1 = x - 1 by omega, upd_self]
    rw [e0, e1] at this
    simp only [enc, fire, hq, hd, mv]
    have hp : E.k * (x - 1) + ((E.k + E.ce r.p : Nat) : Int) = E.k * x + E.ce r.p := by
      rw [Int.mul_sub, Int.mul_one]; push_cast; omega
    rw [hp] at this
    rw [show x + -1 = x - 1 by omega]
    exact this

/-- **停止の模倣**: T が停止規則 r を適用する配置 c では、M は enc c から `pre c` に達して止まる。 -/
theorem halt_sim (H : Hyp T M E cost ss) {r : Rule Q P S} (hr : r ∈ T) (hq : r.q.isGo = false)
    {c : Cfg Q P S} (hst : c.st = .go r.p) (hs : c.tape c.pos = r.s) :
    ∃ j, HaltsIn M j (enc E c) (pre M E c) := by
  obtain ⟨st, x, g⟩ := c
  simp only at hst hs
  subst hst
  have hc := List.all_eq_true.mp H.hC r hr
  have hc' : (hrun M (hfuel E) ⟨E.ρ r.p, E.ce r.p, E.code (g x)⟩).isSome = true := by
    cases h : r.q with
    | go _ => rw [h] at hq; cases hq
    | halt _ => rw [h] at hc; rw [hs]; exact hc
  obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp hc'
  have hpre : pre M E ⟨.go r.p, x, g⟩ = glob (E.k * x) (bits E.code E.k g) c' := by
    simp only [pre, hc']
  rw [hpre]
  obtain ⟨⟨j, hj⟩, hH⟩ := hrun_sound hc' (E.k * x) (bits E.code E.k g)
  refine ⟨j, ?_, hH⟩
  simp only [glob] at hj
  rw [ovl_block H.hk H.hlen, upd_self] at hj
  exact hj

end Sim

/-! ## 6. CTSH の模倣の移送 -/

section Main
variable [DecidableEq Q'] {T : Machine Q P S} {M : Machine Q' P Bool} {E : Enc Q S Q'}
  {cost : Rule Q P S → Nat} {ss : List S}

theorem step_sim' (H : Hyp T M E cost ss) {c c' : Cfg Q P S} (h : Step (dropHalt T) c c') :
    ∃ N, 1 ≤ N ∧ StepN M N (enc E c) (enc E c') := by
  obtain ⟨r, hr, hst, hs, rfl⟩ := h
  obtain ⟨hrT, hg⟩ := mem_dropHalt.mp hr
  cases hq : r.q with
  | halt _ => rw [hq] at hg; cases hg
  | go q =>
    have h1 : 1 ≤ cost r := by
      have hc := cert_step H hrT hq (c.tape c.pos)
      unfold stepCert at hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      exact hc.1
    exact ⟨cost r, h1, step_sim H hrT hq hst hs⟩

/-- **主定理（一般形）**。T（決定的、停止規則はどれも 0 シフトで読んだ記号をそのまま書き、疑似状態 h へ
    入る規則の現状態は f h）の実状態の配置 a から CTSH C の停止の 3 項が成り立ち（停止配置 fin はどれも
    疑似状態）、M が決定的で `certB` の検査に通るなら、M も enc a から停止の 3 項を満たす。停止配置は
    `pre ∘ unhalt f ∘ fin`（T の停止規則の直前の配置を、M がブロックの中で止まるまで進めたもの）。 -/
theorem fs_simulates [DecidableEq Q] (H : Hyp T M E cost ss) (hD : Deterministic T) {f : P → Q}
    (hH : HaltRulesId T f) (hD' : Deterministic M)
    (C : CTSH) (w : List Ch) (a : Cfg Q P S) (ha : ∃ q, a.st = .go q)
    (fin : List Ch → Nat → List Ch → Cfg Q P S) (hfin : ∀ vf mf rm, ∃ h, (fin vf mf rm).st = .halt h)
    (hsim :
      (∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) → ∃ N rm, n ≤ N ∧ HaltsIn T N a (fin vf mf rm)) ∧
      (∀ N e, HaltsIn T N a e → ∃ n vf mf rm, CHaltsIn C n (w, 0) (vf, mf) ∧ e = fin vf mf rm)) :
    (∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) →
      ∃ N rm, n ≤ N + 1 ∧ HaltsIn M N (enc E a) (pre M E (unhalt f (fin vf mf rm)))) ∧
    (∀ N e, HaltsIn M N (enc E a) e →
      ∃ n vf mf rm, CHaltsIn C n (w, 0) (vf, mf) ∧ e = pre M E (unhalt f (fin vf mf rm))) ∧
    ((∀ n e, ¬ CHaltsIn C n (w, 0) e) ↔ (∀ N e, ¬ HaltsIn M N (enc E a) e)) := by
  have hd := drop_simulates hD hH C w a ha fin hfin hsim
  have simN : ∀ {n : Nat} {b c : Cfg Q P S}, StepN (dropHalt T) n b c →
      ∃ N, n ≤ N ∧ StepN M N (enc E b) (enc E c) :=
    stepN_sim_of_step (T := dropHalt T) (T' := M) (enc E) (fun h => step_sim' H h)
  refine transfer3 hD' (pre M E) (fun N e ⟨hs, hh⟩ => ?_)
    (fun _ N _ hb => let ⟨M', hM', h'⟩ := simN hb; ⟨M', hM', _, h'⟩) C w
    (fun vf mf rm => unhalt f (fin vf mf rm)) ⟨hd.1, hd.2.1⟩
  -- T の実行は停止規則の読みでしか止まらない（NoStuck）
  have hsT := StepN.of_drop hs
  obtain ⟨q, hq⟩ := StepN.drop_go hs ha
  by_cases hT : Halted T e
  · obtain ⟨_, vf, mf, rm, _, rfl⟩ := hsim.2 N e ⟨hsT, hT⟩
    obtain ⟨h, hfh⟩ := hfin vf mf rm
    rw [hq] at hfh; cases hfh
  · obtain ⟨c', r, hr, hst, hsr, rfl⟩ := exists_step_of_not_halted hT
    cases hrq : r.q with
    | go q' =>
      exact absurd (Step.to_drop ⟨r, hr, hst, hsr, rfl⟩ ⟨q', by simp [fire, hrq]⟩) (hh _)
    | halt h =>
      obtain ⟨j, hj⟩ := halt_sim H hr (by rw [hrq]; rfl) hst hsr
      obtain ⟨N', hN', hs'⟩ := simN hs
      exact ⟨N' + j, by omega, hs'.trans hj.1, hj.2⟩

end Main

end URTM.FewSym
