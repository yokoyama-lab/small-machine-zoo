/-
  `Spec.lean` の言葉で述べた主定理と、その証明（既存の定理への橋渡し）。
  主定理はファイル末尾の「主定理」節にある。
-/
import URTMMeta.Spec
import URTMMeta.Morita
import Mathlib.Data.Int.Interval
import Mathlib.Data.Set.Finite.Lattice

namespace URTM.Spec
open URTM URTM.TwoState URTM.Meta

/-! ### 仕様の ID と本体の `QConf` -/

def toQ (c : ID) : QConf := ⟨c.st, c.pos, c.tape⟩
def ofQ (c : QConf) : ID := ⟨c.st, c.pos, c.tape⟩

@[simp] theorem toQ_ofQ (c : QConf) : toQ (ofQ c) = c := rfl
@[simp] theorem ofQ_toQ (c : ID) : ofQ (toQ c) = c := rfl

theorem move_eq (d : Dir) (p : ℤ) : move d p = p + shift d := by
  cases d <;> simp [move, shift] <;> omega

theorem write_eq (t : ℤ → ℕ) (p : ℤ) (v : ℕ) : write t p v = Function.update t p v := by
  funext i; simp [write, Function.update_apply]

theorem toQ_apply (r : Quint) (c : ID) : toQ (apply r c) = ⟨r.q, move r.d c.pos, write c.tape c.pos r.t⟩ := by
  simp [toQ, apply, move_eq, write_eq]

theorem find?_none_iff (T : List Quint) (c : ID) :
    find? T c.st (c.tape c.pos) = none ↔ Halted T c := by
  unfold find? Halted Applicable
  rw [List.find?_eq_none]
  simp [Bool.and_eq_true, beq_iff_eq]

theorem qstep_none_iff (T : List Quint) (c : ID) : qstep T (toQ c) = none ↔ Halted T c := by
  rw [← find?_none_iff]
  unfold qstep; simp only [toQ]
  cases find? T c.st (c.tape c.pos) <;> simp

theorem step_of_qstep (T : List Quint) (c : ID) (q : QConf) (h : qstep T (toQ c) = some q) :
    Step T c (ofQ q) := by
  unfold qstep at h; simp only [toQ] at h
  cases hf : find? T c.st (c.tape c.pos) with
  | none => rw [hf] at h; cases h
  | some r =>
    rw [hf] at h; cases h
    obtain ⟨hr, hp, hs⟩ := find?_spec hf
    refine ⟨r, hr, ⟨hp, hs⟩, ?_⟩
    simp [ofQ, apply, move_eq, write_eq]

theorem qstep_of_step {T : List Quint} (hdet : Deterministic T) {c c' : ID} (h : Step T c c') :
    qstep T (toQ c) = some (toQ c') := by
  obtain ⟨r, hr, ⟨hp, hs⟩, rfl⟩ := h
  cases hf : find? T c.st (c.tape c.pos) with
  | none => exact absurd ⟨hp, hs⟩ ((find?_none_iff T c).mp hf r hr)
  | some r' =>
    obtain ⟨hr', hp', hs'⟩ := find?_spec hf
    obtain rfl : r' = r := hdet r' hr' r hr (hp'.trans hp.symm) (hs'.trans hs.symm)
    unfold qstep; simp only [toQ] at hf ⊢; rw [hf]; simp [apply, move_eq, write_eq]

/-- 決定的な表では、仕様の停止と本体の停止（先頭一致の実行）は一致する。 -/
theorem halts_iff_qhalts {T : List Quint} (hdet : Deterministic T) (c : ID) :
    Halts T c ↔ QHalts T (toQ c) := by
  constructor
  · rintro ⟨c', hr, hh⟩
    induction hr using Relation.ReflTransGen.head_induction_on with
    | refl => exact ⟨1, by simp [qrun, (qstep_none_iff T c').mpr hh]⟩
    | head hs _ ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, by simp only [qrun, qstep_of_step hdet hs]; exact hn⟩
  · rintro ⟨n, hn⟩
    induction n generalizing c with
    | zero => simp [qrun] at hn
    | succ n ih =>
      cases hq : qstep T (toQ c) with
      | none => exact ⟨c, Relation.ReflTransGen.refl, (qstep_none_iff T c).mp hq⟩
      | some q =>
        simp only [qrun, hq] at hn
        obtain ⟨c', hr, hh⟩ := ih (ofQ q) (by simpa using hn)
        exact ⟨c', Relation.ReflTransGen.head (step_of_qstep T c q hq) hr, hh⟩

theorem toQ_toID (p : ℤ) (z : Code) : toQ (toID p z) = realize p z := rfl

/-- 決定的な表では、符号 `z` を位置 `p` に置いた ID からの停止は本体の `ZHalts` と一致する。 -/
theorem halts_toID_iff {T : List Quint} (hdet : Deterministic T) (p : ℤ) (z : Code) :
    Halts T (toID p z) ↔ ZHalts T z := by
  rw [halts_iff_qhalts hdet, toQ_toID]
  exact exists_congr fun n => qrun_realize T n p z

/-! ### 重複を除いた列と Bool の検査 -/

theorem step_dedup (T : List Quint) (c c' : ID) : Step T.dedup c c' ↔ Step T c c' := by
  simp [Step, List.mem_dedup]

theorem halted_dedup (T : List Quint) (c : ID) : Halted T.dedup c ↔ Halted T c := by
  simp [Halted, List.mem_dedup]

theorem halts_dedup (T : List Quint) (c : ID) : Halts T.dedup c ↔ Halts T c := by
  have hs : Step T.dedup = Step T := by funext c c'; exact propext (step_dedup T c c')
  simp only [Halts, HaltsAt, hs, halted_dedup]

theorem det_dedup {T : List Quint} (h : Deterministic T) : Deterministic T.dedup := by
  intro r₁ h₁ r₂ h₂; exact h r₁ (List.mem_dedup.mp h₁) r₂ (List.mem_dedup.mp h₂)

theorem allPairs_of {f : Quint → Quint → Bool} :
    ∀ {l : List Quint}, l.Nodup → (∀ a ∈ l, ∀ b ∈ l, a ≠ b → f a b = true) → allPairs f l = true
  | [], _, _ => rfl
  | x :: xs, hn, h => by
    rw [List.nodup_cons] at hn
    simp only [allPairs, Bool.and_eq_true, List.all_eq_true]
    refine ⟨fun y hy => h x (by simp) y (by simp [hy]) (fun e => hn.1 (e ▸ hy)),
      allPairs_of hn.2 fun a ha b hb => h a (by simp [ha]) b (by simp [hb])⟩

/-- 仕様の 2 状態 RTM から、本体（Bool の検査）の 2 状態 RTM を得る（重複を除いた列で）。 -/
theorem meta_of_spec {T : List Quint} {q₀ q₁ qf : ℕ} (hT : TwoStateRTM T q₀ q₁ qf) :
    URTM.Meta.TwoStateRTM T.dedup q₀ q₁ qf where
  det := allPairs_of (List.nodup_dedup T) fun a ha b hb hab => by
    have := hT.det a (List.mem_dedup.mp ha) b (List.mem_dedup.mp hb)
    unfold detPair
    by_cases hp : a.p = b.p <;> by_cases hs : a.s = b.s <;> simp_all
  rev := allPairs_of (List.nodup_dedup T) fun a ha b hb hab => by
    have := hT.rev a (List.mem_dedup.mp ha) b (List.mem_dedup.mp hb) hab
    unfold revPair
    by_cases hq : a.q = b.q <;> simp_all
  ne := hT.ne
  f0 := hT.f0
  f1 := hT.f1
  src := fun r hr => hT.src r (List.mem_dedup.mp hr)
  dst := fun r hr => hT.dst r (List.mem_dedup.mp hr)

/-! ### 有限 ID と符号 -/

theorem getD_eq_zero_of_le (l : List ℕ) (n : ℕ) (h : l.length ≤ n) : l.getD n 0 = 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem toID_finite (p : ℤ) (z : Code) : (toID p z).Finite := by
  apply (Set.finite_Icc (p - z.2.1.length) (p + z.2.2.length)).subset
  intro x hx
  simp only [Set.mem_setOf_eq, toID] at hx
  simp only [Set.mem_Icc]
  split_ifs at hx with h
  · refine ⟨by omega, ?_⟩
    by_contra hc
    exact hx (getD_eq_zero_of_le _ _ (by omega))
  · refine ⟨?_, by omega⟩
    by_contra hc
    exact hx (getD_eq_zero_of_le _ _ (by omega))

/-- **有限 ID はすべて符号で表せる**（ヘッドの位置に置いた符号から戻る）。 -/
theorem toID_complete (c : ID) (hc : c.Finite) : ∃ z : Code, toID c.pos z = c := by
  obtain ⟨st, pos, tape⟩ := c
  obtain ⟨M, hM⟩ := (hc.image fun x => (x - pos).natAbs).bddAbove
  have hN : ∀ x, tape x ≠ 0 → (x - pos).natAbs ≤ M := fun x hx => hM ⟨x, hx, rfl⟩
  refine ⟨(st, (List.range (M + 1)).map (fun i : ℕ => tape (pos - 1 - (i : ℤ))),
    (List.range (M + 1)).map (fun i : ℕ => tape (pos + (i : ℤ)))), ?_⟩
  simp only [toID, ID.mk.injEq, true_and]
  funext x
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  split_ifs with h
  · by_cases hx : (x - pos).toNat < M + 1
    · rw [List.getElem?_range hx]; simp only [Option.map_some, Option.getD_some]; congr 1; omega
    · rw [List.getElem?_eq_none (by simp only [List.length_range]; omega)]
      simp only [Option.map_none, Option.getD_none]
      by_contra hne; have := hN x (Ne.symm hne); omega
  · by_cases hx : (pos - 1 - x).toNat < M + 1
    · rw [List.getElem?_range hx]; simp only [Option.map_some, Option.getD_some]; congr 1; omega
    · rw [List.getElem?_eq_none (by simp only [List.length_range]; omega)]
      simp only [Option.map_none, Option.getD_none]
      by_contra hne; have := hN x (Ne.symm hne); omega

/-! ### 万能性の部分 -/

theorem quintOfNat_tupleOf (r : Quint) : quintOfNat (tupleOf r) = r := by
  obtain ⟨p, s, t, d, q⟩ := r; cases d <;> rfl

theorem tblU_det : Deterministic tblU := by
  intro r₁ h₁ r₂ h₂ hp hs
  obtain ⟨q, hq, a, o, ho, rfl⟩ := mem_tblOf.mp h₁
  obtain ⟨q', hq', a', o', ho', rfl⟩ := mem_tblOf.mp h₂
  rw [mkQ_p, mkQ_p] at hp; rw [mkQ_s, mkQ_s] at hs
  obtain rfl := stN_inj hq hp
  obtain rfl := symN_inj hs
  rw [ho] at ho'; cases ho'; rfl

theorem tm_tmIndex_tblU : tm (tmIndex tblU) = tblU := by
  have e : (Denumerable.ofNat (List (ℕ × ℕ × ℕ × ℕ × ℕ)) (tmIndex tblU)).map quintOfNat = tblU := by
    have : (quintOfNat ∘ tupleOf) = id := funext quintOfNat_tupleOf
    rw [tmIndex, Denumerable.ofNat_encode, List.map_map, this, List.map_id]
  unfold tm
  dsimp only
  split_ifs with h
  · exact e
  · rw [e] at h; exact absurd tblU_det h

theorem isIDOf_of_IDOf {T : List Quint} {z : Code} (h : IDOf T z) (p : ℤ) : IsIDOf T (toID p z) := by
  refine ⟨toID_finite p z, h.1, fun x => ?_⟩
  simp only [toID]
  have key : ∀ (l : List ℕ) (n : ℕ), (∀ a ∈ l, a = 0 ∨ a ∈ symsOf T) →
      l.getD n 0 = 0 ∨ l.getD n 0 ∈ symbols T := by
    intro l n hl
    rw [List.getD_eq_getElem?_getD]
    cases hn : l[n]? with
    | none => left; rfl
    | some a => exact hl a (List.mem_of_getElem? hn)
  split_ifs
  · exact key _ _ fun a ha => h.2 a (List.mem_append_right _ ha)
  · exact key _ _ fun a ha => h.2 a (List.mem_append_left _ ha)

/-- 2 状態 RTM が模倣する TM の停止は、その有限 ID の上で計算可能に判定できる。 -/
theorem simulates_halting_computable {U T : List Quint} {q₀ q₁ qf : ℕ}
    (hU : TwoStateRTM U q₀ q₁ qf) (hs : Simulates U T) :
    ∃ f : Code → Bool, Computable f ∧
      ∀ a, IsIDOf T (toID 0 a) → (Halts T (toID 0 a) ↔ f a = true) := by
  obtain ⟨c, d, hc, -, h⟩ := hs
  obtain ⟨g, hg, hge⟩ := ComputablePred.computable_iff.mp (halting_computable (meta_of_spec hU))
  refine ⟨fun a => g (c a), hg.comp hc, fun a ha => ?_⟩
  have hiff : Halts T (toID 0 a) ↔ Halts U (toID 0 (c a)) := by
    constructor
    · rintro ⟨β, hβ⟩
      obtain ⟨γ, hγ, -⟩ := (h a ha).1 β hβ
      exact ⟨γ, hγ⟩
    · intro hU'; by_contra hn; exact (h a ha).2 hn hU'
  rw [hiff, ← halts_dedup, halts_toID_iff (det_dedup hU.det)]
  exact iff_of_eq (congrFun hge (c a))

/-! ## 主定理（`Spec.lean` の言葉だけで述べる） -/

/-- **定理 1 前半**: 2 状態の RTM では、有限 ID から停止するかが決定可能である
    （符号 `z` をヘッドの位置 `p` に置いた ID について。`toID_complete` により、
    有限 ID はすべてこの形で表せる）。 -/
theorem halting_decidable {T : List Quint} {q₀ q₁ qf : ℕ} (hT : TwoStateRTM T q₀ q₁ qf) :
    ComputablePred fun x : ℤ × Code => Halts T (toID x.1 x.2) := by
  obtain ⟨f, hf, hfe⟩ := ComputablePred.computable_iff.mp (halting_computable (meta_of_spec hT))
  refine ComputablePred.computable_iff.mpr ⟨fun x => f x.2, hf.comp Computable.snd, ?_⟩
  funext x
  apply propext
  rw [← halts_dedup, halts_toID_iff (det_dedup hT.det)]
  exact iff_of_eq (congrFun hfe x.2)

/-- **定理 1 後半（Morita B3 の否定的解決）**: 2 状態の URTM は存在しない。 -/
theorem no_two_state_URTM {U : List Quint} {q₀ q₁ qf : ℕ} (hU : TwoStateRTM U q₀ q₁ qf) :
    ¬ IsUTM U := by
  rintro ⟨c, d, hc, hd, h⟩
  have hs : Simulates U (tm (tmIndex tblU)) :=
    ⟨fun a => c (tmIndex tblU, a), d, hc.comp (Computable.pair (Computable.const _) Computable.id),
      hd, fun a ha => h (tmIndex tblU) a ha⟩
  rw [tm_tmIndex_tblU] at hs
  obtain ⟨f, hf, hfe⟩ := simulates_halting_computable hU hs
  apply tblU_undecidable
  refine ComputablePred.computable_iff.mpr ⟨fun x => f (zidU x), hf.comp zidU_primrec.to_comp, ?_⟩
  funext x
  apply propext
  rw [← halts_toID_iff tblU_det 0]
  exact hfe (zidU x) (isIDOf_of_IDOf (IDOf_tblU_zidU x) 0)

/-- **系（Morita B2 の否定的解決）**: 列挙のある TM は、どの 2 状態の RTM にも模倣されない。 -/
theorem two_state_class_not_universal :
    ∃ n, ∀ (U : List Quint) (q₀ q₁ qf : ℕ), TwoStateRTM U q₀ q₁ qf → ¬ Simulates U (tm n) := by
  refine ⟨tmIndex tblU, fun U q₀ q₁ qf hU hs => ?_⟩
  rw [tm_tmIndex_tblU] at hs
  obtain ⟨f, hf, hfe⟩ := simulates_halting_computable hU hs
  apply tblU_undecidable
  refine ComputablePred.computable_iff.mpr ⟨fun x => f (zidU x), hf.comp zidU_primrec.to_comp, ?_⟩
  funext x
  apply propext
  rw [← halts_toID_iff tblU_det 0]
  exact hfe (zidU x) (isIDOf_of_IDOf (IDOf_tblU_zidU x) 0)

end URTM.Spec
