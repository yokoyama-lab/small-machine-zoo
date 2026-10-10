/-
  **3 状態 2 記号の URTM（段階 1）**: 例外の表を除き、3 状態 2 記号の RTM は Morita Def. 7.1 の意味で
  万能でない。

  定義 `IsUTM_MoritaOver tbl Γ` は `IsUTM_Morita`（`Morita.lean`）に、Def. 5.8/7.1 の字義どおり
  「符号化 c の値は U の ID（テープの記号は U の記号集合 {0} ∪ Γ の元）」という条件を足したもの。
  `IsUTM_Morita` より強い要求なので（`IsUTM_MoritaOver.toMorita`）、その否定は `IsUTM_Morita` の否定より
  弱い。2 状態の定理（`no_two_state_URTM_Morita`）は条件の無い `IsUTM_Morita` の否定であり、そのまま残す。

  主定理 `no_three_two_URTM`: `RTM32 tbl q₀ q₁ q₂ σ`（働く状態 3 つ、記号は空白 0 と σ）で、
  正規形の表の鍵が例外の一覧 `excKeys` に無いなら、`¬ IsUTM_MoritaOver tbl [σ]`。
  証明: 停止問題が U の ID の上で計算可能（`three_halting_computable`）なので、Tₙ の停止が計算可能になり
  `tm_halting_undecidable` と矛盾する。
-/
import URTMMeta.Morita
import URTM.ThreeCover
import URTM.ThreeNorm

namespace URTM.Meta
open URTM URTM.TwoState URTM.Three

/-- **模倣（Def. 7.1、U の ID の上で）**: `SimulatesEnum` に「c の値のテープの記号は 0 か Γ の元」を足したもの。 -/
def SimulatesEnumOver (tbl : List Quint) (Γ : List Nat) (E : ℕ → List Quint) : Prop :=
  ∃ (c : ℕ × ZID → ZID) (d : ZID → Option ZID), Computable c ∧ Computable d ∧
    ∀ n α, IDOf (E n) α →
      (∀ a ∈ (c (n, α)).2.1 ++ (c (n, α)).2.2, a = 0 ∨ a ∈ Γ) ∧
      (∀ β, ZHaltsAt (E n) α β →
          ∃ γ, ZHaltsAt tbl (c (n, α)) γ ∧ ∃ β', d γ = some β' ∧ ZSame β' β) ∧
      (¬ ZHalts (E n) α → ¬ ZHalts tbl (c (n, α)))

/-- **UTM（Def. 7.1、記号集合 {0} ∪ Γ の U）**。 -/
def IsUTM_MoritaOver (tbl : List Quint) (Γ : List Nat) : Prop := SimulatesEnumOver tbl Γ tmOf

theorem IsUTM_MoritaOver.toMorita {tbl : List Quint} {Γ : List Nat} (h : IsUTM_MoritaOver tbl Γ) :
    IsUTM_Morita tbl :=
  let ⟨c, d, hc, hd, h⟩ := h
  ⟨c, d, hc, hd, fun n α hα => (h n α hα).2⟩

/-! ### 正規形の配置（zipper の上） -/

section
variable (q₀ q₁ q₂ sg : Nat)

def nz (z : ZID) : ZID := (URTM.Three.stN q₀ q₁ q₂ z.1, z.2.1.map (URTM.Three.symN sg), z.2.2.map (URTM.Three.symN sg))

theorem stN_primrec : Primrec (URTM.Three.stN q₀ q₁ q₂) := by
  unfold URTM.Three.stN
  refine Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const _)) (Primrec.const 0) ?_
  refine Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const _)) (Primrec.const 1) ?_
  exact Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const _)) (Primrec.const 2) (Primrec.const 3)

theorem symN_primrec : Primrec (URTM.Three.symN sg) := by
  unfold URTM.Three.symN
  exact Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const _)) (Primrec.const 1) Primrec.id

theorem nz_primrec : Primrec (nz q₀ q₁ q₂ sg) := by
  have hs : Primrec fun l : List ℕ => l.map (URTM.Three.symN sg) :=
    Primrec.list_map Primrec.id ((symN_primrec sg).comp Primrec.snd).to₂
  exact Primrec.pair ((stN_primrec q₀ q₁ q₂).comp Primrec.fst)
    (Primrec.pair (hs.comp (Primrec.fst.comp Primrec.snd)) (hs.comp (Primrec.snd.comp Primrec.snd)))

end

theorem tapeOf_map (sg : ℕ) (p : ℤ) (L R : List ℕ) (hsg : sg ≠ 0) :
    (fun x => URTM.Three.symN sg (tapeOf p L R x)) = tapeOf p (L.map (URTM.Three.symN sg)) (R.map (URTM.Three.symN sg)) := by
  have h0 : URTM.Three.symN sg 0 = 0 := by unfold URTM.Three.symN; simp [Ne.symm hsg]
  funext x
  unfold tapeOf
  split
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases R[(x - p).toNat]? <;> simp [h0]
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases L[(p - 1 - x).toNat]? <;> simp [h0]

/-- 窓の幅だけで書いた上界。 -/
def bnd3N (MR ML w : Nat) : Nat := csize 2 (w + MR + ML + 1) + 1

theorem bound3_eq (MR ML m n : Nat) :
    bound3 MR ML (-(m : Int)) (n : Int) = bnd3N MR ML (m + n) := by
  unfold bound3 bnd3N
  congr 2
  omega

/-! ### 停止問題の計算可能性 -/

theorem fresh_of {pre : List ℕ} {c : ℕ} (h : c = 0 ∨ ∀ x ∈ pre, x ≠ c) : fresh pre c = true := by
  unfold fresh
  rcases h with h | h
  · simp [h]
  · cases hc : pre.contains c
    · simp
    · exact absurd rfl (h c (List.contains_iff_mem.mp hc))

/-- 符号の並びは全列挙の枝刈りの条件（重ならない）を満たす。 -/
theorem absCodes_fresh {tbl : List Quint} {q₀ q₁ q₂ sg : Nat} (H : RTM32 tbl q₀ q₁ q₂ sg) :
    fresh [codeOf q₀ q₁ q₂ sg tbl 0 0] (codeOf q₀ q₁ q₂ sg tbl 0 1) = true ∧
    fresh [codeOf q₀ q₁ q₂ sg tbl 0 0, codeOf q₀ q₁ q₂ sg tbl 0 1] (codeOf q₀ q₁ q₂ sg tbl 1 0) = true ∧
    fresh [codeOf q₀ q₁ q₂ sg tbl 0 0, codeOf q₀ q₁ q₂ sg tbl 0 1, codeOf q₀ q₁ q₂ sg tbl 1 0]
      (codeOf q₀ q₁ q₂ sg tbl 1 1) = true ∧
    fresh [codeOf q₀ q₁ q₂ sg tbl 0 0, codeOf q₀ q₁ q₂ sg tbl 0 1, codeOf q₀ q₁ q₂ sg tbl 1 0,
      codeOf q₀ q₁ q₂ sg tbl 1 1] (codeOf q₀ q₁ q₂ sg tbl 2 0) = true ∧
    fresh [codeOf q₀ q₁ q₂ sg tbl 0 0, codeOf q₀ q₁ q₂ sg tbl 0 1, codeOf q₀ q₁ q₂ sg tbl 1 0,
      codeOf q₀ q₁ q₂ sg tbl 1 1, codeOf q₀ q₁ q₂ sg tbl 2 0] (codeOf q₀ q₁ q₂ sg tbl 2 1) = true := by
  -- 欄 (i, s) の符号が 0 でなければ、それより前の欄 (i', s') の符号とは異なる
  have key : ∀ i s, i < 3 → s < 2 → ∀ (pre : List (ℕ × ℕ)),
      (∀ p ∈ pre, p.1 < 3 ∧ p.2 < 2 ∧ (p.1 ≠ i ∨ p.2 ≠ s)) →
      fresh (pre.map fun p => codeOf q₀ q₁ q₂ sg tbl p.1 p.2) (codeOf q₀ q₁ q₂ sg tbl i s) = true := by
    intro i s hi hs pre hpre
    refine fresh_of ?_
    by_cases h0 : codeOf q₀ q₁ q₂ sg tbl i s = 0
    · exact Or.inl h0
    · refine Or.inr fun x hx heq => ?_
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
      obtain ⟨h1, h2, h3⟩ := hpre p hp
      obtain ⟨e1, e2⟩ := codeOf_inj H hi hs h1 h2 h0 heq.symm
      rcases h3 with h3 | h3 <;> [exact h3 e1.symm; exact h3 e2.symm]
  refine ⟨key 0 1 (by decide) (by decide) [(0, 0)] (by decide),
    key 1 0 (by decide) (by decide) [(0, 0), (0, 1)] (by decide),
    key 1 1 (by decide) (by decide) [(0, 0), (0, 1), (1, 0)] (by decide),
    key 2 0 (by decide) (by decide) [(0, 0), (0, 1), (1, 0), (1, 1)] (by decide),
    key 2 1 (by decide) (by decide) [(0, 0), (0, 1), (1, 0), (1, 1), (2, 0)] (by decide)⟩

/-- **3 状態 2 記号の RTM の停止問題は、U の ID の上で計算可能**（例外の表を除く）。 -/
theorem three_halting_computable {tbl : List Quint} {q₀ q₁ q₂ sg : Nat} (H : RTM32 tbl q₀ q₁ q₂ sg)
    (hne : isExc (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl) = false) :
    ∃ f : ZID → Bool, Computable f ∧
      ∀ z, (∀ a ∈ z.2.1 ++ z.2.2, a = 0 ∨ a ∈ [sg]) → (ZHalts tbl z ↔ f z = true) := by
  -- 正規形の表は全列挙に載り、証明書が立つ
  have hlt := absCodes_lt H
  obtain ⟨f1, f2, f3, f4, f5⟩ := absCodes_fresh H
  have hcov : cov (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl) = true := by
    unfold absCodes absDirs
    unfold absCodes at hlt
    exact lvl0_sound lvl0_cov (hlt _ (by simp)) (hlt _ (by simp)) (hlt _ (by simp)) (hlt _ (by simp))
      (hlt _ (by simp)) (hlt _ (by simp)) f1 f2 f3 f4 f5 _ _ _
  have hok : tableOK (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl) = true := by
    unfold cov at hcov; rw [hne, Bool.or_false] at hcov; exact hcov
  have hlt' := hlt
  unfold absCodes at hok hlt'
  obtain ⟨MR, ML, hb⟩ := tableOK_bound (absDirs q₀ q₁ q₂ tbl) hlt' hok
  -- 判定関数: 正規形の配置を `bnd3N` 歩回して止まっているか
  let T' := normT (tbl := tbl) (q₀ := q₀) (q₁ := q₁) (q₂ := q₂) (σ := sg)
  refine ⟨fun z => (zrun T' (bnd3N MR ML ((nz q₀ q₁ q₂ sg z).2.1.length + (nz q₀ q₁ q₂ sg z).2.2.length))
    (nz q₀ q₁ q₂ sg z)).isNone, ?_, ?_⟩
  · -- 計算可能性
    have hz := nz_primrec q₀ q₁ q₂ sg
    have hw : Primrec fun z : ZID => (nz q₀ q₁ q₂ sg z).2.1.length + (nz q₀ q₁ q₂ sg z).2.2.length :=
      Primrec.nat_add.comp (Primrec.list_length.comp (Primrec.fst.comp (Primrec.snd.comp hz)))
        (Primrec.list_length.comp (Primrec.snd.comp (Primrec.snd.comp hz)))
    have hB : Primrec fun z : ZID => bnd3N MR ML ((nz q₀ q₁ q₂ sg z).2.1.length + (nz q₀ q₁ q₂ sg z).2.2.length) := by
      have := Primrec.nat_add.comp (csize_primrec.comp (Primrec.const 2)
        (Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.nat_add.comp hw (Primrec.const MR))
          (Primrec.const ML)) (Primrec.const 1))) (Primrec.const 1)
      exact this.of_eq fun z => rfl
    have hr : Primrec fun z : ZID => zrun T' (bnd3N MR ML ((nz q₀ q₁ q₂ sg z).2.1.length +
        (nz q₀ q₁ q₂ sg z).2.2.length)) (nz q₀ q₁ q₂ sg z) := by
      have := Primrec.nat_iterate hB (Primrec.option_some.comp hz)
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
      have hmem : ∀ (l : List ℕ) (k : ℕ), (∀ a ∈ l, a = 0 ∨ a ∈ [sg]) → l.getD k 0 = 0 ∨ l.getD k 0 = sg := by
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
    rw [hlen, hlen', ← bound3_eq]
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

/-- **定理（段階 1）: 例外の表を除き、3 状態 2 記号の URTM は存在しない**（Morita Def. 7.1、
    U の記号集合 {0, sg} の上の ID への符号化）。 -/
theorem no_three_two_URTM {tbl : List Quint} {q₀ q₁ q₂ sg : Nat} (H : RTM32 tbl q₀ q₁ q₂ sg)
    (hne : isExc (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl) = false) :
    ¬ IsUTM_MoritaOver tbl [sg] := by
  rintro ⟨c, d, hc, _, h⟩
  obtain ⟨f, hf, hfe⟩ := three_halting_computable H hne
  apply tm_halting_undecidable
  refine ⟨fun p => f (c p), hf.comp hc, fun p hp => ?_⟩
  obtain ⟨hsym, hh, hn⟩ := h p.1 p.2 hp
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

end URTM.Meta
