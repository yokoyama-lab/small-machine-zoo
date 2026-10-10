/-
  **非存在の小さな隅**: 出発状態が 2 種類以下の RTM と、記号が空白だけの TM は万能でない。

  主定理（`Spec.lean` の `Deterministic`・`Reversible`・`IsUTM` と `Strict.lean` の `NStates`・`NSyms`・
  `IsUTMStrict` だけで述べる）:
  * `no_le_two_state_URTM` : 決定的かつ可逆で `NStates U ≤ 2`（出発状態が 0・1・2 種類）なら `¬ IsUTM U`。
    出発状態が 1 種類以下のときは、使われない状態を足して 2 状態の形にし、既存の
    `no_two_state_URTM_general`（`GeneralTwo.lean`）に帰着する。
  * `no_one_symbol_UTM` : 決定的で `NSyms U ≤ 1`（記号は空白 0 だけ）なら `¬ IsUTM U`。可逆性は仮定しない。
    五つ組はどれも 0 を読んで 0 を書くので、テープは書き換わらず、機械はテープの上を状態だけで決まる
    向きに歩き、空白でないセルに着くか規則の無い状態に入ると止まる。状態の列は表の長さ以内に周期に入るので、
    周期ごとの変位が 0 なら同じ所を回り続け、0 でなければ有限の非空白部分から離れていく。
    よって止まるなら `(W + k + 1)(k + 1)` 歩以内に止まる（`k` = 表の長さ、`W` = 符号の左右の長さの和。
    `qrun_blank_bound`）。停止が決定可能なので万能でない（`not_isUTM_of_halting_decidable`）。
  * 両方の `IsUTMStrict` 版（`IsUTMStrict.isUTM` による系）。

  既存の定義と定理は変えない（このファイルは追加だけ）。
-/
import URTMMeta.Uniform
import URTMMeta.Strict

namespace URTM.Spec
open URTM URTM.TwoState URTM.Meta

/-! ### 停止が決定可能な表は万能でない -/

/-- **停止が決定可能な表は万能でない**: 位置と符号の組からの停止が計算可能に判定できる表 `U` は、
    停止問題が決定不能な TM `tblU` を模倣できない。 -/
theorem not_isUTM_of_halting_decidable {U : List Quint}
    (h : ComputablePred fun x : ℤ × Code => Halts U (toID x.1 x.2)) : ¬ IsUTM U := by
  rintro ⟨c, d, hc, -, hU⟩
  obtain ⟨g, hg, hge⟩ := ComputablePred.computable_iff.mp h
  apply tblU_undecidable
  refine ComputablePred.computable_iff.mpr
    ⟨fun x => g (0, c (tmIndex tblU, zidU x)), ?_, ?_⟩
  · exact hg.comp (Computable.pair (Computable.const (0 : ℤ))
      (hc.comp (Computable.pair (Computable.const _) zidU_primrec.to_comp)))
  · funext x
    apply propext
    have ha : IsIDOf (tm (tmIndex tblU)) (toID 0 (zidU x)) := by
      rw [tm_tmIndex_tblU]; exact isIDOf_of_IDOf (IDOf_tblU_zidU x) 0
    have hiff : Halts tblU (toID 0 (zidU x)) ↔ Halts U (toID 0 (c (tmIndex tblU, zidU x))) := by
      have hh := hU (tmIndex tblU) (zidU x) ha
      rw [tm_tmIndex_tblU] at hh
      constructor
      · rintro ⟨β, hβ⟩
        obtain ⟨γ, hγ, -⟩ := hh.1 β hβ
        exact ⟨γ, hγ⟩
      · intro hU'; by_contra hn; exact hh.2 hn hU'
    rw [← halts_toID_iff tblU_det 0, hiff]
    exact iff_of_eq (congrFun hge (0, c (tmIndex tblU, zidU x)))

/-! ### 出発状態が 2 種類以下 -/

/-- 出発状態が高々 2 種類なら、相異なる 2 状態 `q₀ ≠ q₁` で出発状態をすべて覆える
    （0 種類・1 種類のときは使われない状態で埋める）。 -/
theorem sources_cover_of_le_two {U : List Quint} (h : (U.map Quint.p).dedup.length ≤ 2) :
    ∃ q₀ q₁ : ℕ, q₀ ≠ q₁ ∧ ∀ r ∈ U, r.p = q₀ ∨ r.p = q₁ := by
  have hmem : ∀ r ∈ U, r.p ∈ (U.map Quint.p).dedup := fun r hr =>
    List.mem_dedup.mpr (List.mem_map.mpr ⟨r, hr, rfl⟩)
  have hnd := List.nodup_dedup (U.map Quint.p)
  generalize (U.map Quint.p).dedup = l at h hmem hnd
  match l, h, hmem, hnd with
  | [], _, hmem, _ =>
    exact ⟨0, 1, by decide, fun r hr => by have := hmem r hr; simp at this⟩
  | [a], _, hmem, _ =>
    exact ⟨a, a + 1, by omega, fun r hr => Or.inl (by simpa using hmem r hr)⟩
  | [a, b], _, hmem, hnd =>
    exact ⟨a, b, by simpa using hnd, fun r hr => by simpa using hmem r hr⟩
  | _ :: _ :: _ :: _, h, _, _ => simp only [List.length_cons] at h; omega

/-- 出発状態が高々 2 種類の決定的かつ可逆な表では、停止が決定可能である。 -/
theorem halting_decidable_le_two {T : List Quint}
    (hdet : Deterministic T) (hrev : Reversible T) (hn : NStates T ≤ 2) :
    ComputablePred fun x : ℤ × Code => Halts T (toID x.1 x.2) := by
  obtain ⟨q₀, q₁, hne, hsrc⟩ := sources_cover_of_le_two (U := T) hn
  exact halting_decidable_general hdet hrev hne hsrc

/-- **出発状態が 2 種類以下の URTM は存在しない**（出発状態の種類数で述べた形）。 -/
theorem no_le_two_state_URTM_count {U : List Quint}
    (hdet : Deterministic U) (hrev : Reversible U)
    (hcount : (U.map Quint.p).dedup.length ≤ 2) : ¬ IsUTM U := by
  obtain ⟨q₀, q₁, hne, hsrc⟩ := sources_cover_of_le_two hcount
  exact no_two_state_URTM_general hdet hrev hne hsrc

/-- **出発状態が 2 種類以下の URTM は存在しない**（`NStates` で述べた形。0・1・2 種類を含む）。 -/
theorem no_le_two_state_URTM {U : List Quint}
    (hdet : Deterministic U) (hrev : Reversible U) (hn : NStates U ≤ 2) : ¬ IsUTM U :=
  no_le_two_state_URTM_count hdet hrev hn

/-- 系: 出発状態が 2 種類以下の決定的かつ可逆な表は、厳密な万能性 `IsUTMStrict` も持たない。 -/
theorem no_le_two_state_URTMStrict {U : List Quint}
    (hdet : Deterministic U) (hrev : Reversible U) (hn : NStates U ≤ 2) : ¬ IsUTMStrict U :=
  fun h => no_le_two_state_URTM hdet hrev hn h.isUTM

/-! ### 記号が空白だけの表: 1 歩・テープの不変・並進 -/

/-- 記号が空白だけ（`NSyms U ≤ 1`）なら、五つ組はどれも 0 を読んで 0 を書く。 -/
theorem blank_only_of_nsyms {U : List Quint} (h : NSyms U ≤ 1) : ∀ r ∈ U, r.s = 0 ∧ r.t = 0 := by
  have key : ∀ x ∈ symbols U, x = 0 := by
    intro x hx
    have h0 : (0 : ℕ) ∈ (0 :: symbols U).dedup := List.mem_dedup.mpr (by simp)
    have hx' : x ∈ (0 :: symbols U).dedup := List.mem_dedup.mpr (by simp [hx])
    unfold NSyms at h
    generalize (0 :: symbols U).dedup = l at h h0 hx'
    match l, h, h0, hx' with
    | [], _, h0, _ => simp at h0
    | [a], _, h0, hx' => simp at h0 hx'; omega
    | _ :: _ :: _, h, _, _ => simp only [List.length_cons] at h; omega
  intro r hr
  exact ⟨key r.s (by simp only [symbols, List.mem_flatMap]; exact ⟨r, hr, by simp⟩),
    key r.t (by simp only [symbols, List.mem_flatMap]; exact ⟨r, hr, by simp⟩)⟩

section BlankOnly
variable {U : List Quint}

/-- 記号が空白だけの表の 1 歩: 読む記号が 0 なら、状態だけで決まる五つ組で動き、テープは変わらない。
    0 でなければ止まる。 -/
theorem qstep_blank (hb : ∀ r ∈ U, r.s = 0 ∧ r.t = 0) (c : QConf) :
    qstep U c = if c.tape c.pos = 0 then
      (find? U c.st 0).map (fun r => (⟨r.q, move r.d c.pos, c.tape⟩ : QConf)) else none := by
  unfold qstep
  by_cases h0 : c.tape c.pos = 0
  · rw [if_pos h0, h0]
    cases hf : find? U c.st 0 with
    | none => rfl
    | some r =>
      have ht : r.t = 0 := (hb r (find?_spec hf).1).2
      have hw : write c.tape c.pos r.t = c.tape := by
        funext i
        by_cases he : i = c.pos
        · subst he; simp [write, h0, ht]
        · simp [write, he]
      simp [hw]
  · rw [if_neg h0]
    cases hf : find? U c.st (c.tape c.pos) with
    | none => rfl
    | some r =>
      have := (find?_spec hf).2.2
      rw [(hb r (find?_spec hf).1).1] at this
      exact absurd this.symm h0

theorem move_sub (d : Dir) (p : ℤ) : p - 1 ≤ move d p ∧ move d p ≤ p + 1 := by
  cases d <;> simp only [move] <;> omega

theorem move_trans (d : Dir) (p p' : ℤ) : move d p' - move d p = p' - p := by
  cases d <;> simp only [move] <;> omega

/-- 実行の途中でテープは変わらず、ヘッドは 1 歩に高々 1 しか動かない。 -/
theorem qrun_blank_inv (hb : ∀ r ∈ U, r.s = 0 ∧ r.t = 0) :
    ∀ (n : ℕ) (c d : QConf), qrun U n c = some d →
      d.tape = c.tape ∧ c.pos - n ≤ d.pos ∧ d.pos ≤ c.pos + n := by
  intro n
  induction n with
  | zero =>
    intro c d h
    simp only [qrun, Option.some.injEq] at h
    subst h; simp
  | succ n ih =>
    intro c d h
    cases hs : qstep U c with
    | none => rw [qrun_succ_none U n hs] at h; exact absurd h (by simp)
    | some c' =>
      rw [qrun_succ_some U n hs] at h
      obtain ⟨h1, h2, h3⟩ := ih c' d h
      rw [qstep_blank hb] at hs
      split at hs
      · cases hf : find? U c.st 0 with
        | none => rw [hf] at hs; exact absurd hs (by simp)
        | some r =>
          rw [hf] at hs
          simp only [Option.map, Option.some.injEq] at hs
          subst hs
          have hm := move_sub r.d c.pos
          have h2' : move r.d c.pos - (n : ℤ) ≤ d.pos := h2
          have h3' : d.pos ≤ move r.d c.pos + (n : ℤ) := h3
          refine ⟨h1, ?_, ?_⟩ <;> omega
      · exact absurd hs (by simp)

/-- **並進**: 状態とテープが同じで位置だけ違う 2 つの配置は、両方が生きているあいだ、
    同じ状態を通り、位置の差を保つ。 -/
theorem qrun_blank_trans (hb : ∀ r ∈ U, r.s = 0 ∧ r.t = 0) :
    ∀ (n : ℕ) (c₁ c₂ d₁ d₂ : QConf), c₁.st = c₂.st → c₁.tape = c₂.tape →
      qrun U n c₁ = some d₁ → qrun U n c₂ = some d₂ →
      d₁.st = d₂.st ∧ d₁.tape = d₂.tape ∧ d₂.pos - d₁.pos = c₂.pos - c₁.pos := by
  intro n
  induction n with
  | zero =>
    intro c₁ c₂ d₁ d₂ hst htp h₁ h₂
    simp only [qrun, Option.some.injEq] at h₁ h₂
    subst h₁ h₂
    exact ⟨hst, htp, rfl⟩
  | succ n ih =>
    intro c₁ c₂ d₁ d₂ hst htp h₁ h₂
    cases hs₁ : qstep U c₁ with
    | none => rw [qrun_succ_none U n hs₁] at h₁; exact absurd h₁ (by simp)
    | some c₁' =>
      cases hs₂ : qstep U c₂ with
      | none => rw [qrun_succ_none U n hs₂] at h₂; exact absurd h₂ (by simp)
      | some c₂' =>
        rw [qrun_succ_some U n hs₁] at h₁
        rw [qrun_succ_some U n hs₂] at h₂
        rw [qstep_blank hb] at hs₁ hs₂
        split at hs₁
        · split at hs₂
          · rw [← hst] at hs₂
            cases hf : find? U c₁.st 0 with
            | none => rw [hf] at hs₁; exact absurd hs₁ (by simp)
            | some r =>
              rw [hf] at hs₁ hs₂
              simp only [Option.map, Option.some.injEq] at hs₁ hs₂
              subst hs₁ hs₂
              obtain ⟨e1, e2, e3⟩ := ih ⟨r.q, move r.d c₁.pos, c₁.tape⟩ ⟨r.q, move r.d c₂.pos, c₂.tape⟩
                d₁ d₂ rfl htp h₁ h₂
              refine ⟨e1, e2, ?_⟩
              rw [e3]; exact move_trans r.d c₁.pos c₂.pos
          · exact absurd hs₂ (by simp)
        · exact absurd hs₁ (by simp)

theorem qrun_alive_of_le {c : QConf} {n m : ℕ} (h : qrun U m c ≠ none) (hnm : n ≤ m) :
    ∃ d, qrun U n c = some d := by
  cases hn : qrun U n c with
  | none => exact absurd (qrun_none_mono U c n m hn hnm) h
  | some d => exact ⟨d, rfl⟩

/-- 生きている配置から 1 歩進めるなら、読む記号は 0 で、その状態には規則がある。 -/
theorem qrun_blank_step (hb : ∀ r ∈ U, r.s = 0 ∧ r.t = 0) {c d : QConf} {t : ℕ}
    (hd : qrun U t c = some d) (h : qrun U (t + 1) c ≠ none) :
    d.tape d.pos = 0 ∧ ∃ r, r ∈ U ∧ r.p = d.st ∧ find? U d.st 0 = some r := by
  rw [qrun_succ_right, hd] at h
  change qstep U d ≠ none at h
  rw [qstep_blank hb] at h
  split at h
  · next h0 =>
    cases hf : find? U d.st 0 with
    | none => rw [hf] at h; exact absurd rfl h
    | some r => exact ⟨h0, r, (find?_spec hf).1, (find?_spec hf).2.1, rfl⟩
  · exact absurd rfl h

/-! ### 記号が空白だけの表: 停止までの歩数の上界 -/

/-- **停止までの歩数の上界**: 記号が空白だけの表 `U`（長さ `k`）が、テープの非空白部分が
    ヘッドから距離 `W` 以内にある配置から止まるなら、`(W + k + 1)(k + 1)` 歩で止まっている。 -/
theorem qrun_blank_bound (hb : ∀ r ∈ U, r.s = 0 ∧ r.t = 0) (c : QConf) (W : ℕ)
    (hsupp : ∀ x, c.tape x ≠ 0 → c.pos - W ≤ x ∧ x ≤ c.pos + W)
    (n : ℕ) (hn : qrun U n c = none) :
    qrun U ((W + U.length + 1) * (U.length + 1)) c = none := by
  classical
  set k := U.length with hk
  obtain ⟨T, halive, hdead⟩ := qhalts_haltRun (tbl := U) ⟨n, hn⟩
  by_cases hT : T + 1 ≤ (W + k + 1) * (k + 1)
  · exact qrun_none_mono U c _ _ hdead hT
  exfalso
  have hNk : 1 * (k + 1) ≤ (W + k + 1) * (k + 1) := Nat.mul_le_mul (by omega) (le_refl _)
  -- 0..k 歩目の状態はどれも規則を持つ（k+1 歩目まで生きている）
  obtain ⟨st, hst⟩ : ∃ f : ℕ → ℕ, ∀ t, f t = ((qrun U t c).getD c).st := ⟨_, fun _ => rfl⟩
  have hst_mem : ∀ t ∈ Finset.range (k + 1), st t ∈ (U.map Quint.p).toFinset := by
    intro t ht
    have ht' : t < k + 1 := Finset.mem_range.mp ht
    obtain ⟨d, hd⟩ := qrun_alive_of_le halive (show t ≤ T by omega)
    obtain ⟨-, r, hr, hrp, -⟩ := qrun_blank_step hb hd
      (fun e => halive (qrun_none_mono U c _ _ e (by omega)))
    rw [hst, hd, Option.getD_some, List.mem_toFinset, List.mem_map]
    exact ⟨r, hr, hrp⟩
  have hcard : (U.map Quint.p).toFinset.card < (Finset.range (k + 1)).card := by
    have := List.toFinset_card_le (U.map Quint.p)
    rw [List.length_map] at this
    rw [Finset.card_range]
    omega
  obtain ⟨x, hx, y, hy, hxy, hfxy⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard (f := st) hst_mem
  -- i < j ≤ k で状態が同じ
  obtain ⟨i, j, hij, hjk, hsij⟩ : ∃ i j, i < j ∧ j ≤ k ∧ st i = st j := by
    have hx' := Finset.mem_range.mp hx
    have hy' := Finset.mem_range.mp hy
    rcases Nat.lt_or_gt_of_ne hxy with h | h
    · exact ⟨x, y, h, by omega, hfxy⟩
    · exact ⟨y, x, h, by omega, hfxy.symm⟩
  obtain ⟨ci, hci⟩ := qrun_alive_of_le halive (show i ≤ T by omega)
  obtain ⟨cj, hcj⟩ := qrun_alive_of_le halive (show j ≤ T by omega)
  have hcicj : ci.st = cj.st := by
    have := hsij
    simp only [hst, hci, hcj, Option.getD_some] at this
    exact this
  have hcit := (qrun_blank_inv hb i c ci hci).1
  have hcjt := (qrun_blank_inv hb j c cj hcj).1
  obtain ⟨P, hP⟩ : ∃ P, P = j - i := ⟨_, rfl⟩
  obtain ⟨δ, hδ⟩ : ∃ δ : ℤ, δ = cj.pos - ci.pos := ⟨_, rfl⟩
  -- 周期: j + m 歩目は i + m 歩目を δ だけずらしたもの
  have hper : ∀ m D', qrun U (j + m) c = some D' →
      ∃ D, qrun U (i + m) c = some D ∧ D.st = D'.st ∧ D.tape = D'.tape ∧ D'.pos - D.pos = δ := by
    intro m D' hD'
    obtain ⟨D, hD⟩ := qrun_alive_of_le (c := c) (n := i + m) (m := j + m)
      (by rw [hD']; simp) (by omega)
    refine ⟨D, hD, ?_⟩
    rw [qrun_add, hci] at hD
    rw [qrun_add, hcj] at hD'
    rw [hδ]
    exact qrun_blank_trans hb m ci cj D D' hcicj (hcit.trans hcjt.symm) hD hD'
  have hiter : ∀ q r D, qrun U (i + q * P + r) c = some D →
      ∃ D₀, qrun U (i + r) c = some D₀ ∧ D₀.st = D.st ∧ D₀.tape = D.tape ∧
        D.pos - D₀.pos = (q : ℤ) * δ := by
    intro q
    induction q with
    | zero => intro r D hD; exact ⟨D, by simpa using hD, rfl, rfl, by simp⟩
    | succ q ih =>
      intro r D hD
      have e : i + (q + 1) * P + r = j + (q * P + r) := by rw [Nat.add_mul, Nat.one_mul]; omega
      rw [e] at hD
      obtain ⟨D₁, hD₁, s1, t1, p1⟩ := hper _ D hD
      rw [show i + (q * P + r) = i + q * P + r by omega] at hD₁
      obtain ⟨D₀, hD₀, s0, t0, p0⟩ := ih r D₁ hD₁
      refine ⟨D₀, hD₀, s0.trans s1, t0.trans t1, ?_⟩
      push_cast
      rw [Int.add_mul, Int.one_mul]
      omega
  -- 止まる直前の T 歩目を周期で戻す
  obtain ⟨D, hDT⟩ := qrun_alive_of_le halive (le_refl T)
  have hPpos : 0 < P := by omega
  obtain ⟨q, r, hrP, hTe⟩ : ∃ q r, r < P ∧ T = i + q * P + r :=
    ⟨(T - i) / P, (T - i) % P, Nat.mod_lt _ hPpos, by
      have := Nat.div_add_mod (T - i) P
      rw [Nat.mul_comm] at this
      omega⟩
  have hD := hDT
  rw [hTe] at hD
  obtain ⟨D₀, hD₀, s0, t0, p0⟩ := hiter q r D hD
  -- i + r 歩目は 1 歩進む（i + r + 1 ≤ j ≤ T）
  obtain ⟨h0, r₀, -, -, hf₀⟩ := qrun_blank_step hb hD₀
    (fun e => halive (qrun_none_mono U c _ _ e (by omega)))
  -- T 歩目では止まる
  have hstop : qstep U D = none := by
    have := hdead
    rw [qrun_succ_right, hDT] at this
    exact this
  rw [qstep_blank hb] at hstop
  have hDt : D.tape D.pos ≠ 0 := by
    intro hz
    rw [if_pos hz, ← s0, hf₀] at hstop
    exact absurd hstop (by simp)
  have hDtape : D.tape = c.tape := (qrun_blank_inv hb _ c D hDT).1
  have hD₀pos := qrun_blank_inv hb _ c D₀ hD₀
  have hin := hsupp D.pos (by rw [← hDtape]; exact hDt)
  -- 変位 δ が 0 なら、T 歩目の位置は i + r 歩目と同じで、そこは空白
  by_cases hδ0 : δ = 0
  · rw [hδ0, Int.mul_zero, sub_eq_zero] at p0
    exact hDt (by rw [p0, ← t0]; exact h0)
  -- 変位が 0 でなければ、q 周期で |q δ| ≥ q だけ離れるので q ≤ W + i + r
  have hqb : (q : ℤ) ≤ W + (i + r) := by
    have hpos := hD₀pos.2
    rcases lt_or_gt_of_ne hδ0 with hlt | hgt
    · have hm : (q : ℤ) * δ ≤ (q : ℤ) * (-1) :=
        Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
      generalize (q : ℤ) * δ = X at p0 hm
      omega
    · have hm : (q : ℤ) * 1 ≤ (q : ℤ) * δ :=
        Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
      generalize (q : ℤ) * δ = X at p0 hm
      omega
  have hq' : q ≤ W + k := by omega
  have hPk : P ≤ k := by omega
  have hqP : q * P ≤ (W + k) * k := Nat.mul_le_mul hq' hPk
  have hexp : (W + k + 1) * (k + 1) = (W + k) * k + W + 2 * k + 1 := by
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
    omega
  omega

end BlankOnly

/-! ### 記号が空白だけの表は万能でない -/

/-- 停止の判定に回す歩数（表と符号から計算できる）。 -/
def blankBound (U : List Quint) (z : Code) : ℕ :=
  (z.2.1.length + z.2.2.length + U.length + 1) * (U.length + 1)

theorem blankBound_primrec : Primrec₂ blankBound := by
  have zL := (Primrec.fst.comp (Primrec.snd.comp Primrec.snd) :
    Primrec fun x : List Quint × Code => x.2.2.1)
  have zR := (Primrec.snd.comp (Primrec.snd.comp Primrec.snd) :
    Primrec fun x : List Quint × Code => x.2.2.2)
  have hU := (Primrec.list_length.comp Primrec.fst : Primrec fun x : List Quint × Code => x.1.length)
  exact (Primrec.nat_mul.comp
    (Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.nat_add.comp
      (Primrec.list_length.comp zL) (Primrec.list_length.comp zR)) hU) (Primrec.const 1))
    (Primrec.nat_add.comp hU (Primrec.const 1))).of_eq fun _ => rfl

/-- 記号が空白だけの決定的な表では、符号からの停止は `blankBound` 歩の実行で決まる。 -/
theorem halts_iff_blankBound {T : List Quint} (hdet : Deterministic T) (hsym : NSyms T ≤ 1)
    (p : ℤ) (z : Code) : Halts T (toID p z) ↔ zrun T (blankBound T z) z = none := by
  rw [halts_toID_iff hdet p z]
  constructor
  · rintro ⟨n, hn⟩
    rw [← qrun_realize T n 0 z] at hn
    rw [← qrun_realize T _ 0 z]
    obtain ⟨st, L, R⟩ := z
    refine qrun_blank_bound (blank_only_of_nsyms hsym) (realize 0 (st, L, R)) (L.length + R.length)
      ?_ n hn
    intro x hx
    change tapeOf 0 L R x ≠ 0 at hx
    show (0 : ℤ) - ((L.length + R.length : ℕ) : ℤ) ≤ x ∧ x ≤ 0 + ((L.length + R.length : ℕ) : ℤ)
    unfold tapeOf at hx
    split at hx
    · have : ¬ R.length ≤ (x - 0).toNat := fun h => hx (getD_len R _ h)
      push_cast; omega
    · have : ¬ L.length ≤ (0 - 1 - x).toNat := fun h => hx (getD_len L _ h)
      push_cast; omega
  · intro h; exact ⟨_, h⟩

/-- **記号が空白だけの表の停止問題は、表も入力に含めて決定可能である**（一様版）。 -/
theorem halting_decidable_one_symbol_uniform :
    ∃ f : List Quint × ℤ × Code → Bool, Computable f ∧
      ∀ T : List Quint, Deterministic T → NSyms T ≤ 1 →
        ∀ (p : ℤ) (z : Code), f (T, p, z) = true ↔ Halts T (toID p z) := by
  refine ⟨fun x => (zrun x.1 (blankBound x.1 x.2.2) x.2.2).isNone, ?_, ?_⟩
  · have hr : Primrec fun x : List Quint × ℤ × Code => zrun x.1 (blankBound x.1 x.2.2) x.2.2 :=
      zrun_primrec_uniform.comp (Primrec.pair Primrec.fst
        (Primrec.pair (blankBound_primrec.comp Primrec.fst (Primrec.snd.comp Primrec.snd))
          (Primrec.snd.comp Primrec.snd)))
    exact (Primrec.not.comp (Primrec.option_isSome.comp hr)).to_comp.of_eq fun x => by
      cases zrun x.1 (blankBound x.1 x.2.2) x.2.2 <;> rfl
  · intro T hdet hsym p z
    show (zrun T (blankBound T z) z).isNone = true ↔ _
    rw [halts_iff_blankBound hdet hsym p z]
    cases zrun T (blankBound T z) z <;> simp

/-- **記号が空白だけの決定的な表では、停止が決定可能である。** -/
theorem halting_decidable_one_symbol {T : List Quint} (hdet : Deterministic T) (hsym : NSyms T ≤ 1) :
    ComputablePred fun x : ℤ × Code => Halts T (toID x.1 x.2) := by
  obtain ⟨f, hf, hfe⟩ := halting_decidable_one_symbol_uniform
  refine ComputablePred.computable_iff.mpr ⟨fun x => f (T, x),
    hf.comp (Computable.pair (Computable.const T) Computable.id), ?_⟩
  funext x
  exact propext (hfe T hdet hsym x.1 x.2).symm

/-- **記号が空白だけの UTM は存在しない**: 決定的で `NSyms U ≤ 1` の表は万能でない（可逆性は仮定しない）。 -/
theorem no_one_symbol_UTM {U : List Quint} (hdet : Deterministic U) (hsym : NSyms U ≤ 1) :
    ¬ IsUTM U :=
  not_isUTM_of_halting_decidable (halting_decidable_one_symbol hdet hsym)

/-- 系: 記号が空白だけの決定的な表は、厳密な万能性 `IsUTMStrict` も持たない。 -/
theorem no_one_symbol_UTMStrict {U : List Quint} (hdet : Deterministic U) (hsym : NSyms U ≤ 1) :
    ¬ IsUTMStrict U :=
  fun h => no_one_symbol_UTM hdet hsym h.isUTM

/-! ### 仮定が空虚でないことの確認（kernel の `decide`） -/

section Examples

/-- 出発状態が 0 種類（空の表）。 -/
example : Deterministic [] ∧ Reversible [] ∧ NStates [] ≤ 2 :=
  ⟨by unfold Deterministic; decide, by unfold Reversible; decide, by decide⟩

example : ¬ IsUTM [] := no_le_two_state_URTM (by unfold Deterministic; decide)
  (by unfold Reversible; decide) (by decide)

/-- 出発状態が 1 種類で、行き先が出発状態でない表（使われない状態で埋める場合）。 -/
example : NStates [⟨0, 0, 1, .R, 0⟩, ⟨0, 1, 0, .L, 5⟩] = 1 := by decide

example : ¬ IsUTM [⟨0, 0, 1, .R, 0⟩, ⟨0, 1, 0, .L, 5⟩] :=
  no_le_two_state_URTM (by unfold Deterministic; decide) (by unfold Reversible; decide) (by decide)

/-- 記号が空白だけで 3 状態・非可逆（状態 0 と 2 がともに 1 へ入り、向きが違う）。 -/
example : ¬ Reversible [⟨0, 0, 0, .R, 1⟩, ⟨1, 0, 0, .L, 2⟩, ⟨2, 0, 0, .L, 1⟩] := by
  unfold Reversible; decide

example : NSyms [⟨0, 0, 0, .R, 1⟩, ⟨1, 0, 0, .L, 2⟩, ⟨2, 0, 0, .L, 1⟩] = 1 ∧
    NStates [⟨0, 0, 0, .R, 1⟩, ⟨1, 0, 0, .L, 2⟩, ⟨2, 0, 0, .L, 1⟩] = 3 := by decide

example : ¬ IsUTMStrict [⟨0, 0, 0, .R, 1⟩, ⟨1, 0, 0, .L, 2⟩, ⟨2, 0, 0, .L, 1⟩] :=
  no_one_symbol_UTMStrict (by unfold Deterministic; decide) (by decide)

end Examples

end URTM.Spec
