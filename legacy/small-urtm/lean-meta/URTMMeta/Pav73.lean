/-
  **Pavlotskaya 1973 定理 4 の可逆版**（Mat. Zametki 13(6):899–909）。

  Pavlotskaya の定理 4: 2 記号の TM で、左へ動く命令（左頂点）か右へ動く命令（右頂点）が 1 つだけなら、
  停止問題は判定可能。ここではその可逆版を示す:

  * `URTM.Spec.no_URTM_oneL`: 決定的かつ可逆（Morita Def. 5.4）で、左へ動く五つ組が**高々 1 本** ℓ、
    0 シフトの五つ組で ℓ の出発状態 ℓ.p に入るものが無い表は、`IsUTM` でない。**記号の数・状態の数は任意**。
  * `URTM.Spec.no_URTM_oneR`: 右について同じ（鏡像 `mirT` で左の場合に帰着。Pavlotskaya の注意 1）。
  * `URTM.Spec.no_URTM_pav73_left` / `_right`: 依頼の形（記号 0, 1 だけ、ちょうど 1 本、0 シフト無し）。

  紙の証明（Pavlotskaya の議論のどこが可逆性で消えるか）:
  * (F1) 可逆性: 同じ状態に入る相異なる五つ組は向きが同じ。ℓ の行き先 ℓ.q に入るのは ℓ だけ。
  * 場合 B（ℓ.q = ℓ.p。Pavlotskaya の「左の閉路 = 自己ループ」で、彼女の証明の本体の場合）:
    ℓ.p に入るのは ℓ だけなので、左への掃引は最初の 1 回しか起こらない。その後は左へ動かない。
    彼女の剰余（rest）の議論（掃引が何度も起こる場合）は要らない。
  * 場合 A（ℓ.q ≠ ℓ.p）: ℓ.p に入る五つ組は向きが揃っていて、L でなく、仮定により 0 シフトでもないので R。
    よって左への 1 歩は直前の右への 1 歩と対になり、ヘッドは過去の位置より 2 つ以上左へ行かない（くぼみ ≤ 1）。
  * くぼみ ≤ 1 の実行の停止は判定できる（`dip_bound`）: 入力の右の空白に新しく着いたときの (状態, 1 つ左の記号) が
    2 度同じなら、複製補題（`qescape_dip`）で永久に繰り返す。だから止まる実行はヘッドが有界な窓に収まり、
    窓の配置の数が歩数を抑える。

  2 記号は Pavlotskaya の場合分け（左頂点の符号を 0L1 に絞る）にだけ要り、可逆版では使わない。
  0 シフトで ℓ.p に入る五つ組があると、ℓ → 0 シフト → ℓ … と左へ何セルでも進めるので、くぼみの上界が崩れる
  （例: (p,1,1,L,q) と (q,1,1,Z,p)）。この場合は示していない（仮定に明記）。
-/
import URTMMeta.GeneralTwo
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace URTM.Pav73
open URTM URTM.TwoState URTM.Meta URTM.Spec

/-! ## 1. 実行の 1 歩 -/

theorem move_cases (d : Dir) (p : ℤ) :
    (d = .L ∧ move d p = p - 1) ∨ (d = .Z ∧ move d p = p) ∨ (d = .R ∧ move d p = p + 1) := by
  cases d
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · exact Or.inr (Or.inr ⟨rfl, rfl⟩)

theorem qconf_ext : ∀ {c₁ c₂ : QConf}, c₁.st = c₂.st → c₁.pos = c₂.pos →
    (∀ x, c₁.tape x = c₂.tape x) → c₁ = c₂
  | ⟨s1, p1, t1⟩, ⟨s2, p2, t2⟩, h1, h2, h3 => by
    change s1 = s2 at h1
    change p1 = p2 at h2
    change ∀ x, t1 x = t2 x at h3
    subst h1; subst h2
    rw [show t1 = t2 from funext h3]

/-- 決定的な表で、五つ組 `r` が当てはまる配置の 1 歩。 -/
theorem qstep_rule {U : List Quint} (hdet : Deterministic U) {r : Quint} (hr : r ∈ U) {c : QConf}
    (hp : c.st = r.p) (hs : c.tape c.pos = r.s) :
    qstep U c = some ⟨r.q, move r.d c.pos, write c.tape c.pos r.t⟩ := by
  unfold qstep
  cases hf : find? U c.st (c.tape c.pos) with
  | none =>
    exfalso
    unfold find? at hf
    rw [List.find?_eq_none] at hf
    have := hf r hr
    simp [hp, hs] at this
  | some r' =>
    obtain ⟨hr', hp', hs'⟩ := find?_spec hf
    have e : r' = r := hdet r' hr' r hr (hp'.trans hp) (hs'.trans hs)
    subst e; rfl

section Run
variable {tbl : List Quint} {c : QConf} {T : ℕ}

/-- 止まる実行の時刻 `t` の 1 歩に使われた五つ組。 -/
theorem rstep (hR : QHaltRun tbl c T) (t : ℕ) (ht : t < T) :
    ∃ r ∈ tbl, r.p = (qtr tbl c t).st ∧ r.s = (qtr tbl c t).tape (QP tbl c t) ∧
      (qtr tbl c (t + 1)).st = r.q ∧ QP tbl c (t + 1) = move r.d (QP tbl c t) ∧
      qtr tbl c (t + 1) = ⟨r.q, move r.d (QP tbl c t), write (qtr tbl c t).tape (QP tbl c t) r.t⟩ := by
  obtain ⟨r, hr, hf, e⟩ := qstep_some (hR.step t ht)
  obtain ⟨_, hp, hs⟩ := find?_spec hf
  refine ⟨r, hr, hp, hs, by rw [e], ?_, e⟩
  show (qtr tbl c (t + 1)).pos = _
  rw [e]

theorem step_pos (hR : QHaltRun tbl c T) (t : ℕ) (ht : t < T) :
    QP tbl c (t + 1) = QP tbl c t - 1 ∨ QP tbl c (t + 1) = QP tbl c t ∨
      QP tbl c (t + 1) = QP tbl c t + 1 := by
  obtain ⟨r, -, -, -, -, hm, -⟩ := rstep hR t ht
  rcases move_cases r.d (QP tbl c t) with ⟨-, hmv⟩ | ⟨-, hmv⟩ | ⟨-, hmv⟩ <;> rw [hmv] at hm <;> omega

theorem noL_step (hR : QHaltRun tbl c T) (t : ℕ) (ht : t < T)
    (h : ∀ r ∈ tbl, r.p = (qtr tbl c t).st → r.s = (qtr tbl c t).tape (QP tbl c t) → r.d ≠ .L) :
    QP tbl c t ≤ QP tbl c (t + 1) := by
  obtain ⟨r, hr, hp, hs, -, hm, -⟩ := rstep hR t ht
  rcases move_cases r.d (QP tbl c t) with ⟨hd, -⟩ | ⟨-, hmv⟩ | ⟨-, hmv⟩
  · exact absurd hd (h r hr hp hs)
  · rw [hmv] at hm; omega
  · rw [hmv] at hm; omega

theorem run_st_mem (hR : QHaltRun tbl c T) {Qs : Finset ℕ} (h0 : c.st ∈ Qs)
    (hQ : ∀ r ∈ tbl, r.q ∈ Qs) : ∀ t, t ≤ T → (qtr tbl c t).st ∈ Qs := by
  intro t
  induction t with
  | zero => intro _; exact h0
  | succ t _ =>
    intro ht
    obtain ⟨r, hr, -, -, hst, -, -⟩ := rstep hR t (by omega)
    rw [hst]; exact hQ r hr

theorem run_tape_lt (hR : QHaltRun tbl c T) {K : ℕ} (hK : ∀ r ∈ tbl, r.t < K)
    (h0 : ∀ x, c.tape x < K) : ∀ t, t ≤ T → ∀ x, (qtr tbl c t).tape x < K := by
  intro t
  induction t with
  | zero => intro _ x; exact h0 x
  | succ t ih =>
    intro ht x
    obtain ⟨r, hr, -, -, -, -, e⟩ := rstep hR t (by omega)
    rw [e]
    show write _ _ r.t x < K
    unfold write; split
    · exact hK r hr
    · exact ih (by omega) x

/-- 初めて `M` 以上に着く時刻。そこではちょうど `M` にいて、それより前は `M` 未満。 -/
theorem run_first_arrival (hR : QHaltRun tbl c T) {M : ℤ} (hM : c.pos < M) {t₀ : ℕ}
    (ht₀ : t₀ ≤ T) (hge : M ≤ QP tbl c t₀) :
    ∃ f, f ≤ t₀ ∧ QP tbl c f = M ∧ ∀ u, u < f → QP tbl c u < M := by
  classical
  have hex : ∃ u, M ≤ QP tbl c u := ⟨t₀, hge⟩
  obtain ⟨f, hf, hfle, hlt⟩ : ∃ f, M ≤ QP tbl c f ∧ f ≤ t₀ ∧ ∀ u, u < f → QP tbl c u < M :=
    ⟨Nat.find hex, Nat.find_spec hex, Nat.find_min' hex hge,
      fun u hu => not_le.mp (Nat.find_min hex hu)⟩
  refine ⟨f, hfle, ?_, hlt⟩
  rcases Nat.eq_zero_or_pos f with h0 | hpos
  · subst h0
    have : QP tbl c 0 = c.pos := rfl
    omega
  · obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    have h1 := hlt g (by omega)
    rcases step_pos hR g (by omega) with h | h | h <;> omega

theorem haltRun_tail (hR : QHaltRun tbl c T) (hT : 1 ≤ T) :
    QHaltRun tbl (qtr tbl c 1) (T - 1) := by
  refine ⟨?_, ?_⟩
  · rw [hR.run_mid 1 (T - 1) (by omega)]; simp
  · have := hR.run_from 1 (by omega)
    rwa [show T + 1 - 1 = T - 1 + 1 by omega] at this

end Run

/-! ## 2. 複製補題（くぼみつき）

  Margenstern の複製補題（docs/35 の H6）の形。`c` から `Δ` 歩で、状態が同じで `δ ≥ 1` だけ右へずれた `c'` に着き、
  その間ヘッドは `κ` 以上にいて、`c'` の `[κ+δ, ∞)` が `c` の `[κ, ∞)` をずらしたものなら、永久に止まらない。
  既存の `qescape` は右単調（左へ動かない）な表に限っていた。 -/

/-- `[k, ∞)` のテープと、状態・位置が一致。 -/
def AgR (k : ℤ) (c₁ c₂ : QConf) : Prop :=
  c₁.st = c₂.st ∧ c₁.pos = c₂.pos ∧ ∀ x, k ≤ x → c₁.tape x = c₂.tape x

theorem qstep_agR (tbl : List Quint) {k : ℤ} {c₁ c₂ : QConf} (H : AgR k c₁ c₂) (hk : k ≤ c₁.pos) :
    (qstep tbl c₁ = none ∧ qstep tbl c₂ = none) ∨
    ∃ d₁ d₂, qstep tbl c₁ = some d₁ ∧ qstep tbl c₂ = some d₂ ∧ AgR k d₁ d₂ := by
  obtain ⟨hs, hp, ht⟩ := H
  have hread : c₂.tape c₂.pos = c₁.tape c₁.pos := by rw [← hp]; exact (ht _ hk).symm
  unfold qstep
  rw [hread, ← hs]
  cases hf : find? tbl c₁.st (c₁.tape c₁.pos) with
  | none => left; exact ⟨rfl, rfl⟩
  | some r =>
    right
    refine ⟨_, _, rfl, rfl, rfl, by rw [hp], ?_⟩
    intro x hx
    show write c₁.tape c₁.pos r.t x = write c₂.tape c₂.pos r.t x
    unfold write; rw [← hp]
    by_cases he : x = c₁.pos
    · simp [he]
    · simp [he, ht x hx]

theorem qrun_agR (tbl : List Quint) {k : ℤ} :
    ∀ (n : ℕ) (c₁ c₂ : QConf), AgR k c₁ c₂ →
      (∀ u, u < n → ∀ d, qrun tbl u c₁ = some d → k ≤ d.pos) →
      (qrun tbl n c₁ = none ∧ qrun tbl n c₂ = none) ∨
      ∃ d₁ d₂, qrun tbl n c₁ = some d₁ ∧ qrun tbl n c₂ = some d₂ ∧ AgR k d₁ d₂ := by
  intro n
  induction n with
  | zero => intro c₁ c₂ H _; exact Or.inr ⟨c₁, c₂, rfl, rfl, H⟩
  | succ n ih =>
    intro c₁ c₂ H hstay
    have hk : k ≤ c₁.pos := hstay 0 (by omega) c₁ rfl
    rcases qstep_agR tbl H hk with ⟨e1, e2⟩ | ⟨d₁, d₂, e1, e2, H'⟩
    · left; exact ⟨qrun_succ_none tbl n e1, qrun_succ_none tbl n e2⟩
    · rw [qrun_succ_some tbl n e1, qrun_succ_some tbl n e2]
      exact ih d₁ d₂ H' fun u hu d hd =>
        hstay (u + 1) (by omega) d (by rw [qrun_succ_some tbl u e1]; exact hd)

/-- **複製補題（くぼみつき）**。 -/
theorem qescape_dip {tbl : List Quint} (c c' : QConf) (Δ : ℕ) (δ κ : ℤ) (hδ : 1 ≤ δ)
    (hrun : qrun tbl Δ c = some c') (hst : c'.st = c.st) (hpos : c'.pos = c.pos + δ)
    (hstay : ∀ u, u < Δ → ∀ d, qrun tbl u c = some d → κ ≤ d.pos)
    (htape : ∀ x, κ + δ ≤ x → c'.tape x = c.tape (x - δ)) :
    ∀ n, qrun tbl n c ≠ none := by
  have hΔ : 1 ≤ Δ := by
    rcases Nat.eq_zero_or_pos Δ with h | h
    · subst h
      have : c = c' := Option.some.inj hrun
      rw [this] at hpos; omega
    · exact h
  have iter : ∀ j : ℕ, ∃ cj, qrun tbl (j * Δ) c = some cj ∧
      AgR (κ + j * δ) (shiftQ c (j * δ)) cj := by
    intro j
    induction j with
    | zero =>
      refine ⟨c, by rw [Nat.zero_mul]; rfl, rfl, ?_, fun x _ => ?_⟩
      · show c.pos + ((0 : ℕ) : ℤ) * δ = c.pos; simp
      · show c.tape (x - ((0 : ℕ) : ℤ) * δ) = c.tape x; simp
    | succ j ih =>
      obtain ⟨cj, hcj, hag⟩ := ih
      have hsh : qrun tbl Δ (shiftQ c (j * δ)) = some (shiftQ c' (j * δ)) := by
        rw [qrun_shift, hrun]; rfl
      have hstay' : ∀ u, u < Δ → ∀ d, qrun tbl u (shiftQ c (j * δ)) = some d →
          κ + j * δ ≤ d.pos := by
        intro u hu d hd
        rw [qrun_shift] at hd
        cases hq : qrun tbl u c with
        | none => rw [hq] at hd; exact absurd hd (by simp)
        | some d₀ =>
          rw [hq] at hd
          have e : shiftQ d₀ (j * δ) = d := Option.some.inj hd
          rw [← e]
          show κ + j * δ ≤ d₀.pos + j * δ
          have := hstay u hu d₀ hq; omega
      rcases qrun_agR tbl Δ _ _ hag hstay' with ⟨h1, _⟩ | ⟨d₁, d₂, h1, h2, hag2⟩
      · rw [hsh] at h1; exact absurd h1 (by simp)
      · rw [hsh] at h1
        have e := Option.some.inj h1
        subst e
        have e1 : ((j + 1 : ℕ) : ℤ) * δ = (j : ℤ) * δ + δ := by push_cast; ring
        refine ⟨d₂, by rw [Nat.succ_mul, qrun_add, hcj]; exact h2, ?_, ?_, ?_⟩
        · show c.st = d₂.st
          rw [← hag2.1]; exact hst.symm
        · show c.pos + ((j + 1 : ℕ) : ℤ) * δ = d₂.pos
          rw [← hag2.2.1, e1]
          show _ = c'.pos + j * δ
          rw [hpos]; ring
        · intro x hx
          rw [e1] at hx
          have hx' : κ + (j : ℤ) * δ ≤ x := by linarith
          rw [← hag2.2.2 x hx']
          show c.tape (x - ((j + 1 : ℕ) : ℤ) * δ) = c'.tape (x - j * δ)
          rw [htape (x - j * δ) (by linarith), e1]
          congr 1; ring
  intro n hn
  obtain ⟨cj, hcj, _⟩ := iter n
  have hle : n ≤ n * Δ := by have := Nat.mul_le_mul_left n hΔ; simpa using this
  rw [qrun_none_mono tbl c n (n * Δ) hn hle] at hcj
  exact absurd hcj (by simp)

/-! ## 3. くぼみ ≤ 1 の実行の歩数の上界 -/

/-- 歩数の上界（状態数の上界 `S`、記号数の上界 `K`、入力の台の幅 `w`）。 -/
def dipBnd (S K w : ℕ) : ℕ := S * ((w + 3 + S * K) * K ^ (w + 3 + S * K))

theorem dipBnd_mono {S K w w' : ℕ} (hK : 1 ≤ K) (h : w ≤ w') : dipBnd S K w ≤ dipBnd S K w' := by
  unfold dipBnd
  exact Nat.mul_le_mul_left S (Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right hK (by omega)))

section Dip
variable {tbl : List Quint} {c : QConf} {T : ℕ}

theorem dip_of_mono (hm : ∀ t, t < T → QP tbl c t ≤ QP tbl c (t + 1)) :
    ∀ u t, u ≤ t → t ≤ T → QP tbl c u ≤ QP tbl c t + 1 := by
  have key : ∀ u k, u + k ≤ T → QP tbl c u ≤ QP tbl c (u + k) := by
    intro u k
    induction k with
    | zero => intro _; exact le_refl _
    | succ k ih =>
      intro h
      have h1 := hm (u + k) (by omega)
      have h2 := ih (by omega)
      rw [← Nat.add_assoc]; omega
  intro u t hut ht
  have := key u (t - u) (by omega)
  rw [show u + (t - u) = t by omega] at this
  omega

/-- 左への 1 歩が（最初の 1 歩を除き）直前の右への 1 歩と対になるなら、くぼみは 1 以下。 -/
theorem dip_of_preceded (hR : QHaltRun tbl c T)
    (hpre : ∀ t, 1 ≤ t → t < T → QP tbl c (t + 1) = QP tbl c t - 1 →
      QP tbl c t = QP tbl c (t - 1) + 1) :
    ∀ u t, u ≤ t → t ≤ T → QP tbl c u ≤ QP tbl c t + 1 := by
  have key : ∀ t, t ≤ T → ∀ u, u ≤ t → QP tbl c u ≤ QP tbl c t + 1 := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      intro htT u hut
      rcases Nat.eq_zero_or_pos t with h0 | hpos
      · subst h0
        have : u = 0 := by omega
        subst this; omega
      · obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
        rcases Nat.lt_or_ge u (s + 1) with hu | hu
        · rcases step_pos hR s (by omega) with h | h | h
          · rcases Nat.eq_zero_or_pos s with hs0 | hs0
            · subst hs0
              have : u = 0 := by omega
              subst this; omega
            · have hp := hpre s hs0 (by omega) h
              rcases Nat.lt_or_ge u s with hu' | hu'
              · have := ih (s - 1) (by omega) (by omega) u (by omega); omega
              · have : u = s := by omega
                subst this; omega
          · have := ih s (by omega) (by omega) u (by omega); omega
          · have := ih s (by omega) (by omega) u (by omega); omega
        · have : u = s + 1 := by omega
          subst this; omega
  intro u t hut ht
  exact key t ht u hut

/-- **くぼみ ≤ 1 の止まる実行は `dipBnd` 歩未満で止まる**。 -/
theorem dip_bound (hR : QHaltRun tbl c T)
    (hdip : ∀ u t, u ≤ t → t ≤ T → QP tbl c u ≤ QP tbl c t + 1)
    {Qs : Finset ℕ} (hst0 : c.st ∈ Qs) (hQ : ∀ r ∈ tbl, r.q ∈ Qs) {S K : ℕ} (hS : Qs.card ≤ S)
    (hK : ∀ r ∈ tbl, r.t < K) (hK0 : ∀ x, c.tape x < K)
    {a b : ℤ} (ha : a ≤ c.pos) (hb : c.pos ≤ b) (hsupp : ∀ x, (x < a ∨ b < x) → c.tape x = 0) :
    T + 1 ≤ dipBnd S K (b - a).toNat := by
  classical
  obtain ⟨N, hN⟩ : ∃ N, N = S * K := ⟨_, rfl⟩
  have hst := run_st_mem hR hst0 hQ
  have htp := run_tape_lt hR hK hK0
  have h00 : QP tbl c 0 = c.pos := rfl
  -- 下界
  have hlow : ∀ t, t ≤ T → a - 1 ≤ QP tbl c t := fun t ht => by
    have := hdip 0 t (Nat.zero_le _) ht
    omega
  -- 訪れていないセルは初めのまま
  have frozen : ∀ t, t ≤ T → ∀ x, (∀ u, u < t → QP tbl c u ≠ x) →
      (qtr tbl c t).tape x = c.tape x := by
    intro t ht x hx
    have := hR.cell_frozen x 0 t (by omega) (fun u _ h2 => hx u (by omega))
    rwa [Nat.zero_add] at this
  -- 上界（複製補題と鳩の巣）
  have hhigh : ∀ t, t ≤ T → QP tbl c t ≤ b + 1 + N := by
    intro t₀ ht₀
    by_contra hc
    replace hc := not_le.mp hc
    have harr : ∀ i : ℕ, ∃ f : ℕ, i ≤ N →
        (f ≤ t₀ ∧ QP tbl c f = b + 1 + i ∧ ∀ u, u < f → QP tbl c u < b + 1 + i) := by
      intro i
      by_cases hi : i ≤ N
      · obtain ⟨f, h1, h2, h3⟩ := run_first_arrival hR (M := b + 1 + i) (by omega) ht₀ (by omega)
        exact ⟨f, fun _ => ⟨h1, h2, h3⟩⟩
      · exact ⟨0, fun h => absurd h hi⟩
    choose f hf using harr
    have hblank : ∀ i, i ≤ N → ∀ x, b + 1 + i ≤ x → (qtr tbl c (f i)).tape x = 0 := by
      intro i hi x hx
      obtain ⟨h1, -, h3⟩ := hf i hi
      rw [frozen (f i) (by omega) x (fun u hu => by have := h3 u hu; omega)]
      exact hsupp x (Or.inr (by omega))
    have key : ∀ i j, i < j → j ≤ N →
        ((qtr tbl c (f i)).st, (qtr tbl c (f i)).tape (b + i)) ≠
          ((qtr tbl c (f j)).st, (qtr tbl c (f j)).tape (b + j)) := by
      intro i j hij hjN he
      obtain ⟨hi1, hi2, hi3⟩ := hf i (by omega)
      obtain ⟨hj1, hj2, hj3⟩ := hf j hjN
      have hfij : f i < f j := by
        rcases Nat.lt_or_ge (f i) (f j) with h | h
        · exact h
        · exfalso
          rcases Nat.eq_or_lt_of_le h with h' | h'
          · rw [h'] at hj2; omega
          · have := hi3 (f j) h'; omega
      obtain ⟨est, etp⟩ := Prod.mk.inj he
      have hesc := qescape_dip (tbl := tbl) (qtr tbl c (f i)) (qtr tbl c (f j)) (f j - f i)
        ((j : ℤ) - i) (b + i) (by omega)
        (by
          have := hR.run_mid (f i) (f j - f i) (by omega)
          rwa [show f i + (f j - f i) = f j by omega] at this)
        est.symm
        (by show QP tbl c (f j) = QP tbl c (f i) + ((j : ℤ) - i); omega)
        (fun u hu d hd => by
          have h1 := hR.run_mid (f i) u (by omega)
          rw [hd] at h1
          rw [Option.some.inj h1]
          have := hdip (f i) (f i + u) (by omega) (by omega)
          show b + i ≤ QP tbl c (f i + u)
          omega)
        (fun x hx => by
          by_cases hxe : x = b + j
          · rw [hxe, show b + (j : ℤ) - ((j : ℤ) - i) = b + i by ring]
            exact etp.symm
          · rw [hblank j hjN x (by omega), hblank i (by omega) (x - ((j : ℤ) - i)) (by omega)])
      exact hesc (T + 1 - f i) (hR.run_from (f i) (by omega))
    let sig : ℕ → ℕ × ℕ := fun i => ((qtr tbl c (f i)).st, (qtr tbl c (f i)).tape (b + i))
    have hmaps : ∀ i ∈ Finset.range (N + 1), sig i ∈ Qs ×ˢ Finset.range K := by
      intro i hi
      rw [Finset.mem_range] at hi
      obtain ⟨h1, -, -⟩ := hf i (by omega)
      rw [Finset.mem_product, Finset.mem_range]
      exact ⟨hst (f i) (by omega), htp (f i) (by omega) _⟩
    have hcard : (Qs ×ˢ Finset.range K).card < (Finset.range (N + 1)).card := by
      rw [Finset.card_product, Finset.card_range, Finset.card_range]
      have : Qs.card * K ≤ S * K := Nat.mul_le_mul_right K hS
      omega
    obtain ⟨i, hi, j, hj, hne, he⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
    rw [Finset.mem_range] at hi hj
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact key i j h (by omega) he
    · exact key j i h (by omega) he.symm
  -- 窓の配置の数（鳩の巣）
  obtain ⟨W, hWdef⟩ : ∃ W : ℕ, (W : ℤ) = b - a + 3 + N := ⟨(b - a + 3 + N).toNat, by omega⟩
  have hout : ∀ t, t ≤ T → ∀ x, (x < a - 1 ∨ a - 1 + W ≤ x) → (qtr tbl c t).tape x = c.tape x := by
    intro t ht x hx
    exact frozen t ht x (fun u hu he => by
      have := hlow u (by omega); have := hhigh u (by omega); omega)
  let g : Fin (T + 1) → {q // q ∈ Qs} × Fin W × (Fin W → Fin K) := fun t =>
    (⟨(qtr tbl c t).st, hst t (Nat.lt_succ_iff.mp t.2)⟩,
     ⟨(QP tbl c t - (a - 1)).toNat, by
        have := hlow t (Nat.lt_succ_iff.mp t.2); have := hhigh t (Nat.lt_succ_iff.mp t.2); omega⟩,
     fun i => ⟨(qtr tbl c t).tape (a - 1 + (i.val : ℤ)), htp t (Nat.lt_succ_iff.mp t.2) _⟩)
  have hg : Function.Injective g := by
    intro t₁ t₂ he
    have e1 : (qtr tbl c t₁).st = (qtr tbl c t₂).st := congrArg (fun p => p.1.val) he
    have e2 : (QP tbl c t₁ - (a - 1)).toNat = (QP tbl c t₂ - (a - 1)).toNat :=
      congrArg (fun p => p.2.1.val) he
    have e3 : ∀ n (hn : n < W), (qtr tbl c t₁).tape (a - 1 + (n : ℤ)) =
        (qtr tbl c t₂).tape (a - 1 + (n : ℤ)) :=
      fun n hn => congrArg (fun p => (p.2.2 ⟨n, hn⟩).val) he
    have ht₁ := Nat.lt_succ_iff.mp t₁.2
    have ht₂ := Nat.lt_succ_iff.mp t₂.2
    have l1 := hlow t₁ ht₁
    have l2 := hlow t₂ ht₂
    have epos : QP tbl c t₁ = QP tbl c t₂ := by omega
    have etape : ∀ x, (qtr tbl c t₁).tape x = (qtr tbl c t₂).tape x := by
      intro x
      by_cases hx : x < a - 1 ∨ a - 1 + W ≤ x
      · rw [hout t₁ ht₁ x hx, hout t₂ ht₂ x hx]
      · have := e3 (x - (a - 1)).toNat (by omega)
        rwa [show a - 1 + (((x - (a - 1)).toNat : ℕ) : ℤ) = x by omega] at this
    have econf : qtr tbl c t₁ = qtr tbl c t₂ := qconf_ext e1 epos etape
    apply Fin.ext
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact hR.no_repeat t₁ t₂ h ht₂ econf
    · exact hR.no_repeat t₂ t₁ h ht₁ econf.symm
  have hc := Fintype.card_le_of_injective g hg
  simp only [Fintype.card_fin, Fintype.card_prod, Fintype.card_fun, Fintype.card_coe] at hc
  have hWeq : (b - a).toNat + 3 + S * K = W := by omega
  unfold dipBnd
  rw [hWeq]
  calc T + 1 ≤ Qs.card * (W * K ^ W) := hc
    _ ≤ S * (W * K ^ W) := Nat.mul_le_mul_right _ hS

end Dip

/-! ## 4. 左へ動く五つ組が高々 1 本の表 -/

/-- 場合 A（ℓ.q ≠ ℓ.p）: 左への 1 歩は（最初を除き）直前の右への 1 歩と対になる。可逆性は使わない。 -/
theorem preceded_caseA {U : List Quint} (hL : ∀ r₁ ∈ U, ∀ r₂ ∈ U, r₁.d = .L → r₂.d = .L → r₁ = r₂)
    {ℓ : Quint} (hℓ : ℓ ∈ U) (hℓd : ℓ.d = .L) (hqp : ℓ.q ≠ ℓ.p)
    (hZ : ∀ r ∈ U, r.d = .Z → r.q ≠ ℓ.p) {c : QConf} {T : ℕ} (hR : QHaltRun U c T) :
    ∀ t, 1 ≤ t → t < T → QP U c (t + 1) = QP U c t - 1 → QP U c t = QP U c (t - 1) + 1 := by
  intro t ht1 htT hLs
  obtain ⟨r, hr, hrp, -, -, hm, -⟩ := rstep hR t htT
  have hrd : r.d = .L := by
    rcases move_cases r.d (QP U c t) with ⟨hd, -⟩ | ⟨-, hmv⟩ | ⟨-, hmv⟩
    · exact hd
    · exfalso; rw [hmv] at hm; omega
    · exfalso; rw [hmv] at hm; omega
  have hpℓ : (qtr U c t).st = ℓ.p := by rw [← hrp, hL r hr ℓ hℓ hrd hℓd]
  obtain ⟨r', hr', -, -, hst', hm', -⟩ := rstep hR (t - 1) (by omega)
  rw [show t - 1 + 1 = t by omega] at hst' hm'
  have hq' : r'.q = ℓ.p := by rw [← hst', hpℓ]
  rcases move_cases r'.d (QP U c (t - 1)) with ⟨hd, -⟩ | ⟨hd, -⟩ | ⟨-, hmv⟩
  · exfalso
    have := hL r' hr' ℓ hℓ hd hℓd
    rw [this] at hq'; exact hqp hq'
  · exact absurd hq' (hZ r' hr' hd)
  · rw [hmv] at hm'; omega

/-- 場合 B（ℓ.q = ℓ.p）: 初めに ℓ が当てはまらないなら、以後 ℓ は使われず、ヘッドは左へ動かない。 -/
theorem caseB_mono {U : List Quint} (hrev : Reversible U)
    (hL : ∀ r₁ ∈ U, ∀ r₂ ∈ U, r₁.d = .L → r₂.d = .L → r₁ = r₂)
    {ℓ : Quint} (hℓ : ℓ ∈ U) (hℓd : ℓ.d = .L) (hqp : ℓ.q = ℓ.p)
    {c : QConf} {T : ℕ} (hR : QHaltRun U c T) (h0 : ¬ (c.st = ℓ.p ∧ c.tape c.pos = ℓ.s)) :
    ∀ t, t < T → QP U c t ≤ QP U c (t + 1) := by
  -- (F1) ℓ.p に入る五つ組は ℓ だけ
  have honly : ∀ r ∈ U, r.q = ℓ.p → r = ℓ := by
    intro r hr hq
    by_contra hne
    have hd := (hrev r hr ℓ hℓ hne (by rw [hq, hqp])).1
    exact hne (hL r hr ℓ hℓ (hd.trans hℓd) hℓd)
  have inv : ∀ t, t ≤ T → ¬ ((qtr U c t).st = ℓ.p ∧ (qtr U c t).tape (QP U c t) = ℓ.s) := by
    intro t
    induction t with
    | zero => intro _; exact h0
    | succ t ih =>
      intro ht ⟨hp, _⟩
      obtain ⟨r, hr, hrp, hrs, hst, -, -⟩ := rstep hR t (by omega)
      have hrℓ : r ≠ ℓ := by
        intro e
        rw [e] at hrp hrs
        exact ih (by omega) ⟨hrp.symm, hrs.symm⟩
      exact hrℓ (honly r hr (hst.symm.trans hp))
  intro t ht
  apply noL_step hR t ht
  intro r hr hp hs hd
  have e := hL r hr ℓ hℓ hd hℓd
  exact inv t (by omega) ⟨by rw [← hp, e], by rw [← hs, e]⟩

/-- 場合 B で `ℓ = (p, 0, t, L, p)` が空白の左半直線の上にあると、永久に左へ進む。 -/
theorem caseB_forever {U : List Quint} (hdet : Deterministic U) {ℓ : Quint} (hℓ : ℓ ∈ U)
    (hℓd : ℓ.d = .L) (hqp : ℓ.q = ℓ.p) (hs0 : ℓ.s = 0) :
    ∀ (n : ℕ) (c : QConf), c.st = ℓ.p → (∀ x, x ≤ c.pos → c.tape x = 0) → qrun U n c ≠ none := by
  intro n
  induction n with
  | zero => intro c _ _; exact Option.some_ne_none c
  | succ n ih =>
    intro c hst hz
    have hs : qstep U c = some ⟨ℓ.q, move ℓ.d c.pos, write c.tape c.pos ℓ.t⟩ :=
      qstep_rule hdet hℓ hst (by rw [hz c.pos le_rfl, hs0])
    rw [qrun_succ_some U n hs]
    apply ih
    · exact hqp
    · intro x hx
      change x ≤ move ℓ.d c.pos at hx
      rw [hℓd] at hx
      change x ≤ c.pos - 1 at hx
      show write c.tape c.pos ℓ.t x = 0
      rw [write_off _ _ _ (by omega : x ≠ c.pos)]
      exact hz x (by omega)

/-- 場合 B の歩数の上界。`n` は第 1 相（ℓ の掃引）の残りの長さの上界。 -/
theorem caseB_bound {U : List Quint} (hdet : Deterministic U) (hrev : Reversible U)
    (hL : ∀ r₁ ∈ U, ∀ r₂ ∈ U, r₁.d = .L → r₂.d = .L → r₁ = r₂)
    {ℓ : Quint} (hℓ : ℓ ∈ U) (hℓd : ℓ.d = .L) (hqp : ℓ.q = ℓ.p)
    {Qs : Finset ℕ} (hQ : ∀ r ∈ U, r.q ∈ Qs) {S K : ℕ} (hS : Qs.card ≤ S)
    (hK : ∀ r ∈ U, r.t < K) {a b : ℤ} (hab : a ≤ b) :
    ∀ (n : ℕ) (c : QConf) (T : ℕ), QHaltRun U c T → c.st ∈ Qs → (∀ x, c.tape x < K) →
      a - 1 ≤ c.pos → c.pos ≤ b → (∀ x, (x < a ∨ b < x) → c.tape x = 0) →
      c.pos - (a - 1) = n → T + 1 ≤ n + dipBnd S K ((b - a).toNat + 1) := by
  have hw : (b - (a - 1)).toNat = (b - a).toNat + 1 := by omega
  have hnoL : ∀ (c : QConf) (T : ℕ), QHaltRun U c T → c.st ∈ Qs → (∀ x, c.tape x < K) →
      a - 1 ≤ c.pos → c.pos ≤ b → (∀ x, (x < a ∨ b < x) → c.tape x = 0) →
      ¬ (c.st = ℓ.p ∧ c.tape c.pos = ℓ.s) → T + 1 ≤ dipBnd S K ((b - a).toNat + 1) := by
    intro c T hR hst hK0 ha hb hsupp h0
    have := dip_bound hR (dip_of_mono (caseB_mono hrev hL hℓ hℓd hqp hR h0)) hst hQ hS hK hK0
      (a := a - 1) (b := b) ha hb (fun x hx => hsupp x (by omega))
    rwa [hw] at this
  intro n
  induction n with
  | zero =>
    intro c T hR hst hK0 ha hb hsupp hn
    by_cases h0 : c.st = ℓ.p ∧ c.tape c.pos = ℓ.s
    · exfalso
      have hz : ∀ x, x ≤ c.pos → c.tape x = 0 := fun x hx => hsupp x (Or.inl (by omega))
      have hs0 : ℓ.s = 0 := by rw [← h0.2]; exact hz c.pos le_rfl
      exact caseB_forever hdet hℓ hℓd hqp hs0 (T + 1) c h0.1 hz hR.dead
    · have := hnoL c T hR hst hK0 ha hb hsupp h0; omega
  | succ n ih =>
    intro c T hR hst hK0 ha hb hsupp hn
    by_cases h0 : c.st = ℓ.p ∧ c.tape c.pos = ℓ.s
    · have hstep := qstep_rule hdet hℓ h0.1 h0.2
      have hT : 1 ≤ T := by
        rcases Nat.eq_zero_or_pos T with h | h
        · exfalso
          have hd := hR.dead
          rw [h, qrun_succ_some U 0 hstep] at hd
          exact Option.some_ne_none _ hd
        · exact h
      have hq1 : qtr U c 1 = ⟨ℓ.q, move ℓ.d c.pos, write c.tape c.pos ℓ.t⟩ := by
        have h1 := hR.step 0 hT
        rw [show qtr U c 0 = c from rfl, hstep] at h1
        exact (Option.some.inj h1).symm
      have hR1 := haltRun_tail hR hT
      rw [hq1] at hR1
      have hmv : move ℓ.d c.pos = c.pos - 1 := by rw [hℓd]; rfl
      have := ih ⟨ℓ.q, move ℓ.d c.pos, write c.tape c.pos ℓ.t⟩ (T - 1) hR1 (hQ ℓ hℓ)
        (fun x => by
          show write c.tape c.pos ℓ.t x < K
          unfold write; split
          · exact hK ℓ hℓ
          · exact hK0 x)
        (by show a - 1 ≤ move ℓ.d c.pos; rw [hmv]; omega)
        (by show move ℓ.d c.pos ≤ b; rw [hmv]; omega)
        (fun x hx => by
          show write c.tape c.pos ℓ.t x = 0
          rw [write_off _ _ _ (by omega : x ≠ c.pos)]
          exact hsupp x hx)
        (by show move ℓ.d c.pos - (a - 1) = ((n : ℕ) : ℤ); rw [hmv]; omega)
      omega
    · have := hnoL c T hR hst hK0 ha hb hsupp h0; omega

/-- **左へ動く五つ組が高々 1 本の表の、止まる実行の歩数の上界**。 -/
theorem oneL_bound {U : List Quint} (hdet : Deterministic U) (hrev : Reversible U)
    (hL : ∀ r₁ ∈ U, ∀ r₂ ∈ U, r₁.d = .L → r₂.d = .L → r₁ = r₂)
    (hZ : ∀ ℓ ∈ U, ℓ.d = .L → ∀ r ∈ U, r.d = .Z → r.q ≠ ℓ.p)
    {c : QConf} {T : ℕ} (hR : QHaltRun U c T)
    {Qs : Finset ℕ} (hst0 : c.st ∈ Qs) (hQ : ∀ r ∈ U, r.q ∈ Qs) {S K : ℕ} (hS : Qs.card ≤ S)
    (hK : ∀ r ∈ U, r.t < K) (hK0 : ∀ x, c.tape x < K)
    {a b : ℤ} (ha : a ≤ c.pos) (hb : c.pos ≤ b) (hsupp : ∀ x, (x < a ∨ b < x) → c.tape x = 0) :
    T + 1 ≤ (b - a).toNat + 2 + dipBnd S K ((b - a).toNat + 1) := by
  have hK1 : 1 ≤ K := by have := hK0 0; omega
  have hmono : dipBnd S K (b - a).toNat ≤ dipBnd S K ((b - a).toNat + 1) :=
    dipBnd_mono hK1 (by omega)
  by_cases hex : ∃ ℓ ∈ U, ℓ.d = .L
  · obtain ⟨ℓ, hℓ, hℓd⟩ := hex
    by_cases hqp : ℓ.q = ℓ.p
    · -- 場合 B
      have := caseB_bound hdet hrev hL hℓ hℓd hqp hQ hS hK (by omega : a ≤ b)
        (c.pos - (a - 1)).toNat c T hR hst0 hK0 (by omega) hb hsupp (by omega)
      omega
    · -- 場合 A
      have hdip := dip_of_preceded hR (preceded_caseA hL hℓ hℓd hqp (hZ ℓ hℓ hℓd) hR)
      have := dip_bound hR hdip hst0 hQ hS hK hK0 ha hb hsupp
      omega
  · -- 左へ動く五つ組が無い
    push Not at hex
    have hdip := dip_of_mono (fun t ht => noL_step hR t ht (fun r hr _ _ => hex r hr))
    have := dip_bound hR hdip hst0 hQ hS hK hK0 ha hb hsupp
    omega

/-! ## 5. 鏡像: 右へ動く五つ組が高々 1 本の表（Pavlotskaya の注意 1） -/

theorem flipD_eq_L {d : Dir} : flipD d = .L ↔ d = .R := by cases d <;> simp [flipD]
theorem flipD_eq_Z {d : Dir} : flipD d = .Z ↔ d = .Z := by cases d <;> simp [flipD]

theorem mir_det {U : List Quint} (h : Deterministic U) : Deterministic (mirT U) := by
  intro r₁ h₁ r₂ h₂ hp hs
  obtain ⟨a₁, ha₁, rfl⟩ := mem_mirT h₁
  obtain ⟨a₂, ha₂, rfl⟩ := mem_mirT h₂
  rw [h a₁ ha₁ a₂ ha₂ hp hs]

theorem mir_rev {U : List Quint} (h : Reversible U) : Reversible (mirT U) := by
  intro r₁ h₁ r₂ h₂ hne hq
  obtain ⟨a₁, ha₁, rfl⟩ := mem_mirT h₁
  obtain ⟨a₂, ha₂, rfl⟩ := mem_mirT h₂
  have hne' : a₁ ≠ a₂ := fun e => hne (by rw [e])
  obtain ⟨hd, ht⟩ := h a₁ ha₁ a₂ ha₂ hne' hq
  exact ⟨show flipD a₁.d = flipD a₂.d by rw [hd], ht⟩

theorem haltRun_mir {tbl : List Quint} {c : QConf} {T : ℕ} (hR : QHaltRun tbl c T) :
    QHaltRun (mirT tbl) (mirQ c) T := by
  refine ⟨?_, ?_⟩
  · rw [qrun_mir]
    cases e : qrun tbl T c with
    | none => exact absurd e hR.alive
    | some x => simp
  · rw [qrun_mir, hR.dead]; rfl

theorem oneR_bound {U : List Quint} (hdet : Deterministic U) (hrev : Reversible U)
    (hR1 : ∀ r₁ ∈ U, ∀ r₂ ∈ U, r₁.d = .R → r₂.d = .R → r₁ = r₂)
    (hZ : ∀ ρ ∈ U, ρ.d = .R → ∀ r ∈ U, r.d = .Z → r.q ≠ ρ.p)
    {c : QConf} {T : ℕ} (hR : QHaltRun U c T)
    {Qs : Finset ℕ} (hst0 : c.st ∈ Qs) (hQ : ∀ r ∈ U, r.q ∈ Qs) {S K : ℕ} (hS : Qs.card ≤ S)
    (hK : ∀ r ∈ U, r.t < K) (hK0 : ∀ x, c.tape x < K)
    {a b : ℤ} (ha : a ≤ c.pos) (hb : c.pos ≤ b) (hsupp : ∀ x, (x < a ∨ b < x) → c.tape x = 0) :
    T + 1 ≤ (b - a).toNat + 2 + dipBnd S K ((b - a).toNat + 1) := by
  have h := oneL_bound (U := mirT U) (mir_det hdet) (mir_rev hrev)
    (fun r₁ h₁ r₂ h₂ hd₁ hd₂ => by
      obtain ⟨a₁, ha₁, rfl⟩ := mem_mirT h₁
      obtain ⟨a₂, ha₂, rfl⟩ := mem_mirT h₂
      rw [hR1 a₁ ha₁ a₂ ha₂ (flipD_eq_L.mp hd₁) (flipD_eq_L.mp hd₂)])
    (fun ℓ hℓ hℓd r hr hrd => by
      obtain ⟨a₁, ha₁, rfl⟩ := mem_mirT hℓ
      obtain ⟨a₂, ha₂, rfl⟩ := mem_mirT hr
      exact hZ a₁ ha₁ (flipD_eq_L.mp hℓd) a₂ ha₂ (flipD_eq_Z.mp hrd))
    (haltRun_mir hR) (Qs := Qs) hst0
    (fun r hr => by obtain ⟨a₀, ha₀, rfl⟩ := mem_mirT hr; exact hQ a₀ ha₀) hS
    (fun r hr => by obtain ⟨a₀, ha₀, rfl⟩ := mem_mirT hr; exact hK a₀ ha₀)
    (fun x => hK0 (-x)) (a := -b) (b := -a)
    (by show -b ≤ -c.pos; omega) (by show -c.pos ≤ -a; omega)
    (fun x hx => by show c.tape (-x) = 0; exact hsupp (-x) (by omega))
  rwa [show -a - -b = b - a by ring] at h

/-! ## 6. 有限 ID（zipper）の上の判定関数 -/

/-- 判定に回す歩数（表と符号から計算できる）。 -/
def pbound (tbl : List Quint) (z : ZID) : ℕ :=
  (z.2.1.length + z.2.2.length) + 2 +
    dipBnd (tbl.length + 1) (nsymOf tbl z) (z.2.1.length + z.2.2.length + 1)

def pdecide (tbl : List Quint) (z : ZID) : Bool := (zrun tbl (pbound tbl z) z).isNone

theorem pbound_primrec (tbl : List Quint) : Primrec (pbound tbl) := by
  have zL := (Primrec.fst.comp Primrec.snd : Primrec fun z : ZID => z.2.1)
  have zR := (Primrec.snd.comp Primrec.snd : Primrec fun z : ZID => z.2.2)
  have hn : Primrec (nsymOf tbl) :=
    Primrec.nat_max.comp (Primrec.const _)
      (Primrec.nat_add.comp (lmax_primrec.comp (Primrec.list_append.comp zL zR)) (Primrec.const 1))
  have hw : Primrec fun z : ZID => z.2.1.length + z.2.2.length :=
    Primrec.nat_add.comp (Primrec.list_length.comp zL) (Primrec.list_length.comp zR)
  have hS : Primrec fun _ : ZID => tbl.length + 1 := Primrec.const _
  have hW : Primrec fun z : ZID =>
      z.2.1.length + z.2.2.length + 1 + 3 + (tbl.length + 1) * nsymOf tbl z :=
    Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.nat_add.comp hw (Primrec.const 1))
      (Primrec.const 3)) (Primrec.nat_mul.comp hS hn)
  have hB := Primrec.nat_add.comp (Primrec.nat_add.comp hw (Primrec.const 2))
    (Primrec.nat_mul.comp hS (Primrec.nat_mul.comp hW (pow_primrec.comp hn hW)))
  exact hB.of_eq fun z => rfl

theorem pdecide_primrec (tbl : List Quint) : Primrec (pdecide tbl) := by
  have hr : Primrec fun z : ZID => zrun tbl (pbound tbl z) z := by
    have := Primrec.nat_iterate (pbound_primrec tbl) (Primrec.option_some)
      ((Primrec.option_bind Primrec.snd ((zstep_primrec tbl).comp Primrec.snd).to₂).to₂ :
        Primrec₂ fun (_ : ZID) (o : Option ZID) => o.bind (zstep tbl))
    exact this.of_eq fun z => (zrun_eq_iter tbl _ z).symm
  exact (Primrec.not.comp (Primrec.option_isSome.comp hr)).of_eq fun z => by
    unfold pdecide; cases zrun tbl (pbound tbl z) z <;> rfl

/-- 歩数の上界の定理（`oneL_bound` / `oneR_bound` の形）から、zipper の上の有界停止を得る。 -/
theorem zhalts_iff_pbound {U : List Quint}
    (hbound : ∀ (c : QConf) (T : ℕ), QHaltRun U c T → ∀ (Qs : Finset ℕ), c.st ∈ Qs →
      (∀ r ∈ U, r.q ∈ Qs) → ∀ (S K : ℕ), Qs.card ≤ S → (∀ r ∈ U, r.t < K) →
      (∀ x, c.tape x < K) → ∀ (a b : ℤ), a ≤ c.pos → c.pos ≤ b →
      (∀ x, (x < a ∨ b < x) → c.tape x = 0) →
      T + 1 ≤ (b - a).toNat + 2 + dipBnd S K ((b - a).toNat + 1))
    (z : ZID) : ZHalts U z ↔ zrun U (pbound U z) z = none := by
  obtain ⟨st, L, R⟩ := z
  constructor
  · intro h
    rw [ZHalts_iff] at h
    obtain ⟨T, hR⟩ := qhalts_haltRun h
    have hL := lmax_append_left L R
    have hRm := lmax_append_right L R
    have hT := hbound _ T hR (insert st (U.map Quint.q).toFinset) (Finset.mem_insert_self _ _)
      (fun r hr => Finset.mem_insert_of_mem (List.mem_toFinset.mpr (List.mem_map.mpr ⟨r, hr, rfl⟩)))
      (U.length + 1) (nsymOf U (st, L, R))
      (by
        calc (insert st (U.map Quint.q).toFinset).card
            ≤ (U.map Quint.q).toFinset.card + 1 := Finset.card_insert_le _ _
          _ ≤ (U.map Quint.q).length + 1 := Nat.add_le_add_right (List.toFinset_card_le _) 1
          _ = U.length + 1 := by rw [List.length_map])
      (fun r hr => by have := t_le_tmax hr; unfold nsymOf; omega)
      (fun x => by
        show tapeOf 0 L R x < max (tmax U + 1) (lmax (L ++ R) + 1)
        unfold tapeOf
        split
        · have := getD_le_lmax R (x - 0).toNat; omega
        · have := getD_le_lmax L (0 - 1 - x).toNat; omega)
      (-(L.length : ℤ)) (R.length : ℤ) (by show -(L.length : ℤ) ≤ 0; omega)
      (by show (0 : ℤ) ≤ R.length; omega)
      (fun x hx => by
        show tapeOf 0 L R x = 0
        unfold tapeOf
        split
        · exact getD_len R _ (by omega)
        · exact getD_len L _ (by omega))
    rw [← qrun_realize U _ 0]
    apply qrun_none_mono U _ (T + 1) _ hR.dead
    have e : ((R.length : ℤ) - -(L.length : ℤ)).toNat = L.length + R.length := by omega
    rw [e] at hT
    exact hT
  · intro h; exact ⟨_, h⟩

theorem zhalts_computable_of {U : List Quint}
    (hiff : ∀ z, ZHalts U z ↔ zrun U (pbound U z) z = none) : ComputablePred (ZHalts U) := by
  refine ComputablePred.computable_iff.mpr ⟨pdecide U, (pdecide_primrec U).to_comp, ?_⟩
  funext z
  apply propext
  rw [hiff z]
  unfold pdecide
  cases zrun U (pbound U z) z <;> simp

theorem dec_of_zhalts {U : List Quint} (hdet : Deterministic U) (h : ComputablePred (ZHalts U)) :
    ComputablePred fun x : ℤ × Code => Halts U (toID x.1 x.2) := by
  obtain ⟨f, hf, hfe⟩ := ComputablePred.computable_iff.mp h
  refine ComputablePred.computable_iff.mpr ⟨fun x => f x.2, hf.comp Computable.snd, ?_⟩
  funext x
  apply propext
  rw [halts_toID_iff hdet]
  exact iff_of_eq (congrFun hfe x.2)

end URTM.Pav73

/-! ## 7. 主定理（`Spec.lean` の言葉だけで述べる） -/

namespace URTM.Spec
open URTM URTM.TwoState URTM.Meta

/-- 有限 ID からの停止が計算可能に判定できる表は、万能でない（`no_two_state_URTM_general` と同じ議論）。 -/
theorem not_isUTM_of_decidable {U : List Quint}
    (h : ComputablePred fun x : ℤ × Code => Halts U (toID x.1 x.2)) : ¬ IsUTM U := by
  rintro ⟨c, d, hc, hd, h'⟩
  obtain ⟨g, hg, hge⟩ := ComputablePred.computable_iff.mp h
  apply URTM.Meta.tblU_undecidable
  refine ComputablePred.computable_iff.mpr
    ⟨fun x => g (0, c (tmIndex tblU, zidU x)),
      hg.comp (Computable.pair (Computable.const _)
        (hc.comp (Computable.pair (Computable.const _) zidU_primrec.to_comp))), ?_⟩
  funext x
  apply propext
  rw [← halts_toID_iff tblU_det 0]
  have ha := h' (tmIndex tblU) (zidU x)
    (by rw [tm_tmIndex_tblU]; exact isIDOf_of_IDOf (IDOf_tblU_zidU x) 0)
  rw [tm_tmIndex_tblU] at ha
  have hiff : Halts tblU (toID 0 (zidU x)) ↔ Halts U (toID 0 (c (tmIndex tblU, zidU x))) := by
    constructor
    · rintro ⟨β, hβ⟩
      obtain ⟨γ, hγ, -⟩ := ha.1 β hβ
      exact ⟨γ, hγ⟩
    · intro hU'; by_contra hn; exact ha.2 hn hU'
  rw [hiff]
  exact iff_of_eq (congrFun hge (0, c (tmIndex tblU, zidU x)))

/-- **定理（停止の判定可能性、左）**: 決定的かつ可逆で、左へ動く五つ組が高々 1 本 ℓ、
    0 シフトの五つ組で ℓ.p に入るものが無い表では、有限 ID からの停止が計算可能に判定できる。
    記号の数・状態の数は任意。 -/
theorem halting_decidable_oneL {U : List Quint} (hdet : Deterministic U) (hrev : Reversible U)
    (hL : ∀ r₁ ∈ U, ∀ r₂ ∈ U, r₁.d = .L → r₂.d = .L → r₁ = r₂)
    (hZ : ∀ ℓ ∈ U, ℓ.d = .L → ∀ r ∈ U, r.d = .Z → r.q ≠ ℓ.p) :
    ComputablePred fun x : ℤ × Code => Halts U (toID x.1 x.2) :=
  URTM.Pav73.dec_of_zhalts hdet (URTM.Pav73.zhalts_computable_of
    (URTM.Pav73.zhalts_iff_pbound fun _ _ hR _ hst0 hQ _ _ hS hK hK0 _ _ ha hb hsupp =>
      URTM.Pav73.oneL_bound hdet hrev hL hZ hR hst0 hQ hS hK hK0 ha hb hsupp))

/-- **定理（停止の判定可能性、右）**: 右へ動く五つ組が高々 1 本 ρ で、0 シフトの五つ組で ρ.p に入るものが無い場合。 -/
theorem halting_decidable_oneR {U : List Quint} (hdet : Deterministic U) (hrev : Reversible U)
    (hR : ∀ r₁ ∈ U, ∀ r₂ ∈ U, r₁.d = .R → r₂.d = .R → r₁ = r₂)
    (hZ : ∀ ρ ∈ U, ρ.d = .R → ∀ r ∈ U, r.d = .Z → r.q ≠ ρ.p) :
    ComputablePred fun x : ℤ × Code => Halts U (toID x.1 x.2) :=
  URTM.Pav73.dec_of_zhalts hdet (URTM.Pav73.zhalts_computable_of
    (URTM.Pav73.zhalts_iff_pbound fun _ _ hRun _ hst0 hQ _ _ hS hK hK0 _ _ ha hb hsupp =>
      URTM.Pav73.oneR_bound hdet hrev hR hZ hRun hst0 hQ hS hK hK0 ha hb hsupp))

/-- **定理（Pavlotskaya 1973 定理 4 の可逆版、左）**: 決定的かつ可逆で、左へ動く五つ組が高々 1 本 ℓ、
    0 シフトの五つ組で ℓ.p に入るものが無い表は、万能でない。記号の数・状態の数は任意。 -/
theorem no_URTM_oneL {U : List Quint} (hdet : Deterministic U) (hrev : Reversible U)
    (hL : ∀ r₁ ∈ U, ∀ r₂ ∈ U, r₁.d = .L → r₂.d = .L → r₁ = r₂)
    (hZ : ∀ ℓ ∈ U, ℓ.d = .L → ∀ r ∈ U, r.d = .Z → r.q ≠ ℓ.p) : ¬ IsUTM U :=
  not_isUTM_of_decidable (halting_decidable_oneL hdet hrev hL hZ)

/-- **定理（同、右）**。 -/
theorem no_URTM_oneR {U : List Quint} (hdet : Deterministic U) (hrev : Reversible U)
    (hR : ∀ r₁ ∈ U, ∀ r₂ ∈ U, r₁.d = .R → r₂.d = .R → r₁ = r₂)
    (hZ : ∀ ρ ∈ U, ρ.d = .R → ∀ r ∈ U, r.d = .Z → r.q ≠ ρ.p) : ¬ IsUTM U :=
  not_isUTM_of_decidable (halting_decidable_oneR hdet hrev hR hZ)

/-- **系（依頼の形、左）**: 記号は 0, 1 だけ、左へ動く五つ組がちょうど 1 本、0 シフトの五つ組が無い
    決定的かつ可逆な表は、万能でない。2 記号の仮定 `_hbin` は証明に使わない（`no_URTM_oneL` は記号の数を問わない）。 -/
theorem no_URTM_pav73_left {U : List Quint} (hdet : Deterministic U) (hrev : Reversible U)
    (_hbin : ∀ r ∈ U, r.s ≤ 1 ∧ r.t ≤ 1)
    (hL : ∃ ℓ ∈ U, ℓ.d = .L ∧ ∀ r ∈ U, r.d = .L → r = ℓ)
    (hnoZ : ∀ r ∈ U, r.d ≠ .Z) : ¬ IsUTM U := by
  obtain ⟨ℓ, -, -, hu⟩ := hL
  exact no_URTM_oneL hdet hrev (fun r₁ h₁ r₂ h₂ hd₁ hd₂ => (hu r₁ h₁ hd₁).trans (hu r₂ h₂ hd₂).symm)
    (fun _ _ _ r hr hrd => absurd hrd (hnoZ r hr))

/-- **系（依頼の形、右）**。 -/
theorem no_URTM_pav73_right {U : List Quint} (hdet : Deterministic U) (hrev : Reversible U)
    (_hbin : ∀ r ∈ U, r.s ≤ 1 ∧ r.t ≤ 1)
    (hR : ∃ ρ ∈ U, ρ.d = .R ∧ ∀ r ∈ U, r.d = .R → r = ρ)
    (hnoZ : ∀ r ∈ U, r.d ≠ .Z) : ¬ IsUTM U := by
  obtain ⟨ρ, -, -, hu⟩ := hR
  exact no_URTM_oneR hdet hrev (fun r₁ h₁ r₂ h₂ hd₁ hd₂ => (hu r₁ h₁ hd₁).trans (hu r₂ h₂ hd₂).symm)
    (fun _ _ _ r hr hrd => absurd hrd (hnoZ r hr))

/-! 仮定が空虚でないこと（具体的な表で、`decide` を kernel で）。 -/

/-- 場合 A（ℓ = (0,1,0,L,1)、ℓ.q ≠ ℓ.p）、3 状態・2 記号・0 シフト無し。 -/
example : ¬ IsUTM [⟨0, 1, 0, .L, 1⟩, ⟨1, 0, 1, .R, 0⟩, ⟨1, 1, 1, .R, 2⟩, ⟨2, 0, 0, .R, 0⟩] := by
  apply no_URTM_pav73_left
  · unfold Deterministic; decide
  · unfold Reversible; decide
  · decide
  · decide
  · decide

/-- 場合 B（ℓ = (0,1,1,L,0)、自己ループ）、3 状態・2 記号・0 シフト無し。 -/
example : ¬ IsUTM [⟨0, 1, 1, .L, 0⟩, ⟨0, 0, 1, .R, 1⟩, ⟨1, 0, 0, .R, 2⟩, ⟨1, 1, 0, .R, 1⟩] := by
  apply no_URTM_pav73_left
  · unfold Deterministic; decide
  · unfold Reversible; decide
  · decide
  · decide
  · decide

/-- 0 シフトを含む表（0 シフトの行き先 2 は ℓ.p = 0 でない）。 -/
example : ¬ IsUTM [⟨0, 1, 0, .L, 1⟩, ⟨1, 0, 1, .R, 0⟩, ⟨1, 1, 1, .Z, 2⟩, ⟨2, 1, 0, .R, 0⟩] := by
  apply no_URTM_oneL
  · unfold Deterministic; decide
  · unfold Reversible; decide
  · decide
  · decide

/-- 右の場合（右へ動く五つ組が 1 本）。 -/
example : ¬ IsUTM [⟨0, 1, 0, .R, 1⟩, ⟨1, 0, 1, .L, 0⟩, ⟨1, 1, 1, .L, 2⟩, ⟨2, 0, 0, .L, 0⟩] := by
  apply no_URTM_pav73_right
  · unfold Deterministic; decide
  · unfold Reversible; decide
  · decide
  · decide
  · decide

end URTM.Spec
