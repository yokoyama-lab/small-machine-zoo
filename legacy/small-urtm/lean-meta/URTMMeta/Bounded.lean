/-
  2 状態 RTM の有界停止: 止まるなら計算できる歩数 `bnd` 以内に止まる。

  本体の `decide2_correct` / `decide2_halt_correct` は「`decide2` が停止を正しく判定する」を言う。
  ここではそれを「実行を `bnd nsym a b` 歩回して止まっているか」という 1 つの形に揃える
  （場合分け (iii)・右単調・左単調のどれでも同じ上界で済むように 3 つの上界を足す）。
  計算可能性の議論（`Computable.lean`）はこの形だけを使う。mathlib には依存しない。
-/
import URTM.TSDHaltState

namespace URTM.Meta
open URTM URTM.TwoState

/-- 3 つの場合の上界の和。 -/
def bnd (nsym : Nat) (a b : Int) : Nat :=
  haltBound nsym a b + monoBound nsym a b + monoBound nsym (-b) (-a)

/-- `decide2` が true なら、実際に `bnd` 歩で止まっている（`decide2_correct` と同じ場合分け）。 -/
theorem decide2_true_bound (tbl : List Quint) (hrev : reversible tbl = true) (q₀ q₁ : Nat)
    (hne : q₀ ≠ q₁) (hstates : ∀ r ∈ tbl, r.q = q₀ ∨ r.q = q₁) (nsym : Nat)
    (a b : Int) (c : QConf) (hst : c.st = q₀ ∨ c.st = q₁)
    (h : decide2 tbl q₀ q₁ nsym a b c = true) : qrun tbl (bnd nsym a b) c = none := by
  unfold decide2 at h
  cases hL : tbl.find? (fun r => r.d == Dir.L) with
  | none =>
    rw [hL] at h
    unfold decideMono at h
    have h0 : qrun tbl (monoBound nsym a b) c = none := by
      cases hr : qrun tbl (monoBound nsym a b) c with
      | none => rfl
      | some _ => rw [hr] at h; simp at h
    exact qrun_none_mono tbl c _ _ h0 (by unfold bnd; omega)
  | some rl =>
    rw [hL] at h
    have hrl := List.mem_of_find?_eq_some hL
    have hrld : rl.d = Dir.L := by have := List.find?_some hL; simpa using this
    simp only at h
    by_cases hR : tbl.any (fun r => r.d == Dir.R) = true
    · rw [if_pos hR] at h
      obtain ⟨rr, hrr, hrrd⟩ := List.any_eq_true.mp hR
      have hrrd' : rr.d = Dir.R := by simpa using hrrd
      let qL := rl.q
      let qR := if rl.q = q₀ then q₁ else q₀
      have hqLmem := hstates rl hrl
      have hneLR : qL ≠ qR := by
        show rl.q ≠ (if rl.q = q₀ then q₁ else q₀)
        by_cases h : rl.q = q₀
        · rw [if_pos h, h]; exact hne
        · rw [if_neg h]; exact h
      have hmemLR : ∀ q, (q = q₀ ∨ q = q₁) → (q = qL ∨ q = qR) := by
        intro q hq
        show q = rl.q ∨ q = (if rl.q = q₀ then q₁ else q₀)
        by_cases h : rl.q = q₀
        · rw [if_pos h]; rcases hq with hq | hq
          · left; rw [hq, h]
          · right; exact hq
        · rw [if_neg h]; rcases hq with hq | hq
          · right; exact hq
          · left; rcases hqLmem with h' | h'
            · exact absurd h' h
            · rw [hq, h']
      have hrrq : rr.q = qR := by
        rcases hmemLR rr.q (hstates rr hrr) with h | h
        · exfalso
          have := same_next_state_same_dir hrev hrr hrl h
          rw [hrrd', hrld] at this; exact Dir.noConfusion this
        · exact h
      have h3 : Case3 tbl qL qR :=
        ⟨hrev, hneLR, fun r hr => hmemLR r.q (hstates r hr), ⟨rl, hrl, rfl, hrld⟩,
          ⟨rr, hrr, hrrq, hrrd'⟩⟩
      unfold decideHalt at h
      have h0 : run2 (ruleOf tbl qL qR) (haltBound nsym a b) (toC2 qL c) = none := by
        cases hr : run2 (ruleOf tbl qL qR) (haltBound nsym a b) (toC2 qL c) with
        | none => rfl
        | some _ => rw [hr] at h; simp at h
      have h1 := (qrun_iff_run2 h3 (haltBound nsym a b) c (hmemLR c.st hst)).mpr h0
      exact qrun_none_mono tbl c _ _ h1 (by unfold bnd; omega)
    · rw [if_neg hR] at h
      unfold decideMono at h
      have h0 : qrun (mirT tbl) (monoBound nsym (-b) (-a)) (mirQ c) = none := by
        cases hr : qrun (mirT tbl) (monoBound nsym (-b) (-a)) (mirQ c) with
        | none => rfl
        | some _ => rw [hr] at h; simp at h
      rw [qrun_mir] at h0
      have h1 : qrun tbl (monoBound nsym (-b) (-a)) c = none := by
        cases hr : qrun tbl (monoBound nsym (-b) (-a)) c with
        | none => rfl
        | some _ => rw [hr] at h0; simp at h0
      exact qrun_none_mono tbl c _ _ h1 (by unfold bnd; omega)

/-- 疑似停止状態を除いた表で止まれば、元の表では 1 歩多く回せば止まる
    （本体 `QHalts_drop_iff` の証明の中の補題を取り出したもの）。 -/
theorem qrun_drop_succ {tbl : List Quint} {qf : Nat} (hdet : deterministic tbl = true)
    (hno : ∀ r ∈ tbl, r.p ≠ qf) :
    ∀ n (c : QConf), c.st ≠ qf → qrun (dropInto qf tbl) n c = none →
      qrun tbl (n + 1) c = none := by
  intro n
  induction n with
  | zero => intro c _ h; simp [qrun] at h
  | succ n ih =>
    intro c hc h
    rcases qstep_drop hdet hno c with ⟨_, hB | ⟨c', hc', hq⟩⟩ | ⟨c', hA, hB, hq⟩
    · exact qrun_succ_none tbl _ hB
    · rw [qrun_succ_some tbl _ hc']
      exact qrun_succ_none tbl _ (qstep_qf hno c' hq)
    · rw [qrun_succ_some _ n hA] at h
      rw [qrun_succ_some tbl _ hB]
      exact ih c' hq h

/-- **2 状態 RTM**（Morita Def. 5.1/5.3/5.4）。状態は q₀, q₁ の 2 つ（規則はこの 2 つから出る）、
    加えて出ていく規則の無い停止用の状態 qf へ入ってよい（qf へ入る規則が無い表も含む）。
    決定性と可逆性は Morita の定義の字義（本体の `deterministic`・`reversible`）。 -/
structure TwoStateRTM (tbl : List Quint) (q₀ q₁ qf : Nat) : Prop where
  det : deterministic tbl = true
  rev : reversible tbl = true
  ne : q₀ ≠ q₁
  f0 : qf ≠ q₀
  f1 : qf ≠ q₁
  src : ∀ r ∈ tbl, r.p = q₀ ∨ r.p = q₁
  dst : ∀ r ∈ tbl, r.q = q₀ ∨ r.q = q₁ ∨ r.q = qf

/-- **有界停止**: 2 状態 RTM が有限配置（窓 [a,b] の外は空白、記号は nsym 未満）から止まるなら、
    `bnd nsym a b + 1` 歩で止まっている。**始状態は任意**（q₀, q₁ 以外なら 1 歩目で止まる）。 -/
theorem bounded_halting {tbl : List Quint} {q₀ q₁ qf : Nat} (hT : TwoStateRTM tbl q₀ q₁ qf)
    (nsym : Nat) (hcl : QClosed tbl nsym) (a b : Int) (c : QConf)
    (hinit : ∀ x, c.tape x < nsym) (hab : a ≤ b) (ha : a ≤ c.pos) (hb : c.pos ≤ b)
    (hsupp : ∀ x, (x < a ∨ b < x) → c.tape x = 0) :
    QHalts tbl c ↔ qrun tbl (bnd nsym a b + 1) c = none := by
  constructor
  · intro hH
    have hno : ∀ r ∈ tbl, r.p ≠ qf := by
      intro r hr e
      rcases hT.src r hr with h | h
      · exact hT.f0 (e ▸ h)
      · exact hT.f1 (e ▸ h)
    by_cases hst : c.st = q₀ ∨ c.st = q₁
    · have hd := (decide2_halt_correct tbl hT.det hT.rev q₀ q₁ qf hT.ne hT.f0 hT.f1 hT.dst hno
        nsym hcl a b c hst hinit hab ha hb hsupp).mpr hH
      have hdst : ∀ r ∈ dropInto qf tbl, r.q = q₀ ∨ r.q = q₁ := by
        intro r hr
        obtain ⟨hr1, hr2⟩ := List.mem_filter.mp hr
        have : r.q ≠ qf := by simpa using hr2
        rcases hT.dst r hr1 with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd h this
      have h0 := decide2_true_bound (dropInto qf tbl) (allPairs_filter _ _ _ hT.rev) q₀ q₁ hT.ne
        hdst nsym a b c hst hd
      have hc : c.st ≠ qf := by
        rcases hst with h | h <;> rw [h]
        · exact fun e => hT.f0 e.symm
        · exact fun e => hT.f1 e.symm
      exact qrun_drop_succ hT.det hno _ c hc h0
    · -- 始状態から出る規則が無いので 1 歩目で止まる
      have hs : qstep tbl c = none := by
        unfold qstep
        cases h : find? tbl c.st (c.tape c.pos) with
        | none => rfl
        | some r =>
          obtain ⟨hr, hrp, _⟩ := find?_spec h
          exact absurd (hrp ▸ hT.src r hr) hst
      exact qrun_succ_none tbl _ hs
  · intro h; exact ⟨_, h⟩

end URTM.Meta
