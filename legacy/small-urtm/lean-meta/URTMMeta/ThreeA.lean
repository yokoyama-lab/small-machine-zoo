/-
  3 状態 2 記号の URTM（段階 2b）その 2: **群 A（入る規則の無い状態がある表）**。**手書き**。

  正規形の表に、入る規則が 1 本も無い状態 e があるとする。e に居られるのは初めの 1 歩だけで、
  以後は残りの 2 状態の RTM（`dropFrom e`）として動く。2 状態の有界停止 `bounded_halting` から、
  止まるなら `1 + (bndN 2 (幅 + 2) + 1)` 歩以内に止まる（`noEntry_bound`）。

  主定理 `no_three_two_URTM_A`: 段階 2a の例外（`isExc`）のうち、入る規則の無い状態がある表（`grpA`）を
  例外から外す（`isExcA es D = isExc es D && !grpA es D`）。

    * `halting_computable_of_bound` : 正規形の表の停止が「窓の幅だけで決まる歩数」で決まるなら、
      元の表の停止は U の ID の上で計算可能（`three_halting_computable` の組み立ての一般形）
    * `not_UTM_of_halting_computable` : U の ID の上の停止が計算可能なら Def. 7.1 の意味で万能でない
-/
import URTMMeta.Three
import URTMMeta.ThreeRed

namespace URTM.Meta
open URTM URTM.TwoState URTM.Three

/-! ### 組み立ての一般形 -/

/-- 正規形の表の停止が「窓の幅 m + n だけで決まる歩数 `B (m + n)`」で決まるなら、元の表の停止は
    U の ID（記号は 0 と sg）の上で計算可能。 -/
theorem halting_computable_of_bound {tbl : List Quint} {q₀ q₁ q₂ sg : Nat} (H : RTM32 tbl q₀ q₁ q₂ sg)
    {B : ℕ → ℕ} (hB : Primrec B)
    (hb : ∀ (c : QConf) (m n : ℕ), -(m : ℤ) ≤ c.pos → c.pos ≤ (n : ℤ) →
      (∀ x, (x < -(m : ℤ) ∨ (n : ℤ) < x) → c.tape x = 0) → (∀ x, c.tape x < 2) →
      (QHalts (normT (tbl := tbl) (q₀ := q₀) (q₁ := q₁) (q₂ := q₂) (σ := sg)) c ↔
        qrun (normT (tbl := tbl) (q₀ := q₀) (q₁ := q₁) (q₂ := q₂) (σ := sg)) (B (m + n)) c = none)) :
    ∃ f : ZID → Bool, Computable f ∧
      ∀ z, (∀ a ∈ z.2.1 ++ z.2.2, a = 0 ∨ a ∈ [sg]) → (ZHalts tbl z ↔ f z = true) := by
  -- 判定関数: 正規形の配置を `B (幅)` 歩回して止まっているか
  let T' := normT (tbl := tbl) (q₀ := q₀) (q₁ := q₁) (q₂ := q₂) (σ := sg)
  refine ⟨fun z => (zrun T' (B ((nz q₀ q₁ q₂ sg z).2.1.length + (nz q₀ q₁ q₂ sg z).2.2.length))
    (nz q₀ q₁ q₂ sg z)).isNone, ?_, ?_⟩
  · -- 計算可能性
    have hz := nz_primrec q₀ q₁ q₂ sg
    have hw : Primrec fun z : ZID => (nz q₀ q₁ q₂ sg z).2.1.length + (nz q₀ q₁ q₂ sg z).2.2.length :=
      Primrec.nat_add.comp (Primrec.list_length.comp (Primrec.fst.comp (Primrec.snd.comp hz)))
        (Primrec.list_length.comp (Primrec.snd.comp (Primrec.snd.comp hz)))
    have hBz : Primrec fun z : ZID =>
        B ((nz q₀ q₁ q₂ sg z).2.1.length + (nz q₀ q₁ q₂ sg z).2.2.length) := hB.comp hw
    have hr : Primrec fun z : ZID => zrun T' (B ((nz q₀ q₁ q₂ sg z).2.1.length +
        (nz q₀ q₁ q₂ sg z).2.2.length)) (nz q₀ q₁ q₂ sg z) := by
      have := Primrec.nat_iterate hBz (Primrec.option_some.comp hz)
        ((Primrec.option_bind Primrec.snd ((zstep_primrec T').comp Primrec.snd).to₂).to₂ :
          Primrec₂ fun (_ : ZID) (o : Option ZID) => o.bind (zstep T'))
      exact this.of_eq fun z => (zrun_eq_iter T' _ _).symm
    refine (Primrec.not.comp (Primrec.option_isSome.comp hr)).to_comp.of_eq fun z => ?_
    cases zrun T' _ _ <;> rfl
  · -- 正しさ
    intro z hz
    obtain ⟨st, L, R⟩ := z
    have htape : ∀ x, (realize 0 (st, L, R)).tape x = 0 ∨ (realize 0 (st, L, R)).tape x = sg := by
      intro x
      show tapeOf 0 L R x = 0 ∨ tapeOf 0 L R x = sg
      unfold tapeOf
      have hmem : ∀ (l : List ℕ) (k : ℕ), (∀ a ∈ l, a = 0 ∨ a ∈ [sg]) →
          l.getD k 0 = 0 ∨ l.getD k 0 = sg := by
        intro l k hl
        rw [List.getD_eq_getElem?_getD]
        cases h : l[k]? with
        | none => left; rfl
        | some a =>
          have := hl a (List.mem_of_getElem? h)
          simpa using this
      split
      · exact hmem R _ fun a ha => hz a (List.mem_append_right _ ha)
      · exact hmem L _ fun a ha => hz a (List.mem_append_left _ ha)
    rw [ZHalts_iff, halts_norm H _ htape]
    have hnc : normC q₀ q₁ q₂ sg (realize 0 (st, L, R)) = realize 0 (nz q₀ q₁ q₂ sg (st, L, R)) := by
      unfold normC realize nz
      simp only
      rw [tapeOf_map sg 0 L R H.sig]
    rw [hnc]
    simp only [Option.isNone_iff_eq_none]
    rw [← qrun_realize T' _ 0]
    have hlen : (nz q₀ q₁ q₂ sg (st, L, R)).2.1.length = L.length := by simp [nz]
    have hlen' : (nz q₀ q₁ q₂ sg (st, L, R)).2.2.length = R.length := by simp [nz]
    rw [hlen, hlen']
    apply hb
    · show -(L.length : Int) ≤ 0; omega
    · show (0 : Int) ≤ R.length; omega
    · intro x hx
      show tapeOf 0 (L.map (URTM.Three.symN sg)) (R.map (URTM.Three.symN sg)) x = 0
      unfold tapeOf
      split
      · exact getD_len _ _ (by simp; omega)
      · exact getD_len _ _ (by simp; omega)
    · intro x
      show tapeOf 0 (L.map (URTM.Three.symN sg)) (R.map (URTM.Three.symN sg)) x < 2
      rw [← tapeOf_map sg 0 L R H.sig]
      exact symN_lt H (htape x)

/-- U の ID（記号は 0 か Γ の元）の上の停止が計算可能な表は、Def. 7.1（U の記号集合の上の符号化）の
    意味で万能でない（`no_three_two_URTM` の後半と同じ議論）。 -/
theorem not_UTM_of_halting_computable {tbl : List Quint} {Γ : List Nat}
    (h : ∃ f : ZID → Bool, Computable f ∧
      ∀ z, (∀ a ∈ z.2.1 ++ z.2.2, a = 0 ∨ a ∈ Γ) → (ZHalts tbl z ↔ f z = true)) :
    ¬ IsUTM_MoritaOver tbl Γ := by
  rintro ⟨c, d, hc, _, hsim⟩
  obtain ⟨f, hf, hfe⟩ := h
  apply tm_halting_undecidable
  refine ⟨fun p => f (c p), hf.comp hc, fun p hp => ?_⟩
  obtain ⟨hsym, hh, hn⟩ := hsim p.1 p.2 hp
  have hiff : ZHalts (tmOf p.1) p.2 ↔ ZHalts tbl (c (p.1, p.2)) := by
    constructor
    · intro hH
      obtain ⟨β, hβ⟩ := hH.exists_at
      obtain ⟨γ, hγ, _⟩ := hh β hβ
      exact ZHalts_of_at hγ
    · intro hU
      exact Classical.byContradiction fun hno => hn hno hU
  rw [hiff]
  exact hfe _ hsym

/-! ### 群 A: 入る規則の無い状態 -/

/-- 状態 e へ入る規則が無い。 -/
def noEntry (tbl : List Quint) (e : Nat) : Bool := tbl.all fun r => r.q != e

theorem noEntry_spec {tbl : List Quint} {e : Nat} (h : noEntry tbl e = true) : ∀ r ∈ tbl, r.q ≠ e := by
  intro r hr
  unfold noEntry at h
  simpa using List.all_eq_true.mp h r hr

/-- **群 A の有界停止**（`QConf` の上）: 状態 e へ入る規則が無く、e から出る規則を除いた表が 2 状態の RTM
    なら、窓 [a, b] の外が空白の配置から止まる実行は `1 + (bnd nsym (a − 1) (b + 1) + 1)` 歩以内に止まる。
    1 歩目の後は e に居ない（始状態は任意）。 -/
theorem halts_noEntry {tbl : List Quint} {e qa qb : Nat} (hT : TwoStateRTM (dropFrom e tbl) qa qb e)
    (hno : ∀ r ∈ tbl, r.q ≠ e) {nsym : Nat} (hcl : QClosed tbl nsym) (a b : Int) (c : QConf)
    (hinit : ∀ x, c.tape x < nsym) (ha : a ≤ c.pos) (hb : c.pos ≤ b)
    (hsupp : ∀ x, (x < a ∨ b < x) → c.tape x = 0) :
    QHalts tbl c ↔ qrun tbl (1 + (bnd nsym (a - 1) (b + 1) + 1)) c = none := by
  have hso : SelfOnly tbl e := fun r hr hq => absurd hq (hno r hr)
  constructor
  · intro hH
    cases hs : qstep tbl c with
    | none => exact qrun_none_mono tbl c 1 _ (qrun_succ_none tbl 0 hs) (by omega)
    | some c' =>
      obtain ⟨r, hr, _, he⟩ := qstep_some hs
      have hc' : c'.st ≠ e := by rw [he]; exact hno r hr
      have hk : qrun tbl 1 c = some c' := by rw [qrun_succ_some tbl 0 hs]; rfl
      exact halts_tail hT hso hcl hk hc' (Nat.le_refl 1) hinit ha hb hsupp hH
  · intro h; exact ⟨_, h⟩

section
variable {tbl : List Quint} {q₀ q₁ q₂ sg : Nat}

/-- 窓の幅だけで書いた群 A の上界。 -/
def bndA (w : Nat) : Nat := 1 + (bndN 2 (w + 2) + 1)

theorem bndA_primrec : Primrec bndA :=
  Primrec.nat_add.comp (Primrec.const 1)
    (Primrec.nat_add.comp
      (bndN_primrec.comp (Primrec.const 2) (Primrec.nat_add.comp Primrec.id (Primrec.const 2)))
      (Primrec.const 1))

/-- **群 A の有界停止**（正規形の表）。 -/
theorem noEntry_bound (H : RTM32 tbl q₀ q₁ q₂ sg) {e : Nat} (he : e < 3)
    (hno : noEntry (normT (tbl := tbl) (q₀ := q₀) (q₁ := q₁) (q₂ := q₂) (σ := sg)) e = true)
    (c : QConf) (m n : ℕ) (ha : -(m : ℤ) ≤ c.pos) (hb : c.pos ≤ (n : ℤ))
    (hz : ∀ x, (x < -(m : ℤ) ∨ (n : ℤ) < x) → c.tape x = 0) (h2 : ∀ x, c.tape x < 2) :
    QHalts (normT (tbl := tbl) (q₀ := q₀) (q₁ := q₁) (q₂ := q₂) (σ := sg)) c ↔
      qrun (normT (tbl := tbl) (q₀ := q₀) (q₁ := q₁) (q₂ := q₂) (σ := sg)) (bndA (m + n)) c = none := by
  obtain ⟨qa, qb, hT⟩ := normT_twoState H he
  have h := halts_noEntry hT (noEntry_spec hno) (realize_closed _ _) (-(m : ℤ)) (n : ℤ) c h2 ha hb hz
  have e1 : -(m : ℤ) - 1 = -((m + 1 : ℕ) : ℤ) := by omega
  have e2 : (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) := by omega
  have e3 : m + 1 + (n + 1) = m + n + 2 := by omega
  rw [e1, e2, bnd_eq, e3] at h
  exact h

/-- 正規形の表 (es, D) に、入る規則の無い状態がある（群 A）。 -/
def grpA (es : List Nat) (D : List Dir) : Bool := (List.range 3).any fun e => noEntry (URTM.Three.realize es D) e

/-- 段階 2b（群 A まで）の例外: 段階 2a の例外のうち、入る規則の無い状態を持たない表。 -/
def isExcA (es : List Nat) (D : List Dir) : Bool := isExc es D && !grpA es D

/-- **3 状態 2 記号の RTM の停止問題は、U の ID の上で計算可能**（`isExcA` の表を除く）。 -/
theorem three_halting_computable_A (H : RTM32 tbl q₀ q₁ q₂ sg)
    (hne : isExcA (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl) = false) :
    ∃ f : ZID → Bool, Computable f ∧
      ∀ z, (∀ a ∈ z.2.1 ++ z.2.2, a = 0 ∨ a ∈ [sg]) → (ZHalts tbl z ↔ f z = true) := by
  cases hexc : isExc (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl) with
  | false => exact three_halting_computable H hexc
  | true =>
    have hA : grpA (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl) = true := by
      unfold isExcA at hne
      rw [hexc] at hne
      simpa using hne
    obtain ⟨e, he, hno⟩ := List.any_eq_true.mp hA
    exact halting_computable_of_bound H bndA_primrec (noEntry_bound H (List.mem_range.mp he) hno)

/-- **定理（段階 2b、群 A）: `isExcA` の表を除き、3 状態 2 記号の URTM は存在しない**（Morita Def. 7.1、
    U の記号集合 {0, sg} の上の ID への符号化）。 -/
theorem no_three_two_URTM_A (H : RTM32 tbl q₀ q₁ q₂ sg)
    (hne : isExcA (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl) = false) :
    ¬ IsUTM_MoritaOver tbl [sg] :=
  not_UTM_of_halting_computable (three_halting_computable_A H hne)

end

end URTM.Meta
