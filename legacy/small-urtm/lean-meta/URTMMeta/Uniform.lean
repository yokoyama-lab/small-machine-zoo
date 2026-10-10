/-
  **一様な決定可能性**: 2 状態 RTM の停止問題は、表と有限 ID の組を入力とする**1 つの**
  計算可能な関数で判定できる。

  `Computable.lean` の `halting_computable` は表 `tbl` を固定した形（機械ごと）だけを述べる
  （`zdecide_primrec tbl` は表を定数として扱う）。ここでは表も入力に含めて、判定関数
  `zdecide` が (表, ID) の 2 引数について原始再帰的（`Primrec₂`）であることを示す。
  そのために五つ組 `Quint`（向き `Dir` を含む）を `Primcodable` にし、
  `look`・`zstep`・`zrun`・`nsymOf`・`zbound` を表についても原始再帰的と示す。

  判定の正しさ（`zdecide` の値と停止の同値）は既存の `zhalts_iff_bound`（`Zipper.lean`）と
  `SpecThm.lean`・`GeneralTwo.lean` の橋渡しをそのまま使う。新しいのは計算可能性だけである。
  既存の定義と定理は変えない（このファイルは追加だけ）。
-/
import URTMMeta.Computable
import URTMMeta.GeneralTwo
import Mathlib.Computability.Primrec.List

namespace URTM.Meta
open URTM URTM.TwoState

/-! ### 五つ組の符号化（`Primcodable`） -/

/-- `Dir ≃ Fin 3`（`L` = 0、`Z` = 1、`R` = 2。`dnum` と同じ番号）。 -/
def dirEquiv : Dir ≃ Fin 3 where
  toFun | .L => 0 | .Z => 1 | .R => 2
  invFun i := if i.val = 0 then .L else if i.val = 1 then .Z else .R
  left_inv d := by cases d <;> rfl
  right_inv
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
    | ⟨2, _⟩ => rfl

instance instPrimcodableDir : Primcodable Dir := Primcodable.ofEquiv _ dirEquiv

/-- `Quint ≃ ℕ × ℕ × ℕ × Dir × ℕ`（欄 `p, s, t, d, q` の順）。 -/
def quintEquiv : Quint ≃ ℕ × ℕ × ℕ × Dir × ℕ where
  toFun r := (r.p, r.s, r.t, r.d, r.q)
  invFun x := ⟨x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance instPrimcodableQuint : Primcodable Quint := Primcodable.ofEquiv _ quintEquiv

theorem quintEquiv_primrec : Primrec quintEquiv := Primrec.of_equiv

theorem quint_p_primrec : Primrec Quint.p :=
  (Primrec.fst.comp quintEquiv_primrec).of_eq fun _ => rfl

theorem quint_s_primrec : Primrec Quint.s :=
  (Primrec.fst.comp (Primrec.snd.comp quintEquiv_primrec)).of_eq fun _ => rfl

theorem quint_t_primrec : Primrec Quint.t :=
  (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp quintEquiv_primrec))).of_eq fun _ => rfl

theorem quint_d_primrec : Primrec Quint.d :=
  (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp quintEquiv_primrec)))).of_eq
    fun _ => rfl

theorem quint_q_primrec : Primrec Quint.q :=
  (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp quintEquiv_primrec)))).of_eq
    fun _ => rfl

theorem dnum_primrec : Primrec dnum :=
  (Primrec.fin_val.comp (Primrec.of_equiv (e := dirEquiv))).of_eq fun d => by cases d <;> rfl

theorem rhs_primrec : Primrec rhs :=
  (Primrec.pair quint_t_primrec (Primrec.pair (dnum_primrec.comp quint_d_primrec) quint_q_primrec)).of_eq
    fun _ => rfl

/-! ### 表についても原始再帰的な表引き・1 歩・反復・上界 -/

theorem look_eq_foldr (tbl : List Quint) (q s : ℕ) :
    look tbl q s = tbl.foldr (fun r acc => if r.p = q ∧ r.s = s then some (rhs r) else acc) none := by
  induction tbl with
  | nil => rfl
  | cons r tbl ih => simp only [look, List.foldr_cons, ih]

/-- 表引きは (表, 状態, 記号) の 3 引数について原始再帰的。 -/
theorem look_primrec_uniform : Primrec fun x : List Quint × ℕ × ℕ => look x.1 x.2.1 x.2.2 := by
  have hc : PrimrecPred fun a : (List Quint × ℕ × ℕ) × Quint × Option (ℕ × ℕ × ℕ) =>
      a.2.1.p = a.1.2.1 ∧ a.2.1.s = a.1.2.2 :=
    PrimrecPred.and
      (Primrec.eq.comp (quint_p_primrec.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
      (Primrec.eq.comp (quint_s_primrec.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
  have hh : Primrec₂ fun (x : List Quint × ℕ × ℕ) (a : Quint × Option (ℕ × ℕ × ℕ)) =>
      if a.1.p = x.2.1 ∧ a.1.s = x.2.2 then some (rhs a.1) else a.2 :=
    Primrec.ite hc (Primrec.option_some.comp (rhs_primrec.comp (Primrec.fst.comp Primrec.snd)))
      (Primrec.snd.comp Primrec.snd)
  exact (Primrec.list_foldr Primrec.fst (Primrec.const none) hh).of_eq
    fun x => (look_eq_foldr _ _ _).symm

/-- 1 歩は (表, ID) の 2 引数について原始再帰的。 -/
theorem zstep_primrec₂ : Primrec₂ zstep := by
  have hl : Primrec fun x : List Quint × ZID => look x.1 x.2.1 (x.2.2.2.headD 0) :=
    look_primrec_uniform.comp (Primrec.pair Primrec.fst
      (Primrec.pair (Primrec.fst.comp Primrec.snd)
        (headD_primrec.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))
  have hm : Primrec₂ fun (x : List Quint × ZID) (o : ℕ × ℕ × ℕ) => mv o x.2 :=
    mv_primrec.comp Primrec.snd (Primrec.snd.comp Primrec.fst)
  exact (Primrec.option_map hl hm).of_eq fun _ => rfl

/-- 反復の実行は (表, 歩数, ID) の 3 引数について原始再帰的。 -/
theorem zrun_primrec_uniform : Primrec fun x : List Quint × ℕ × ZID => zrun x.1 x.2.1 x.2.2 := by
  have := Primrec.nat_iterate (Primrec.fst.comp Primrec.snd) (Primrec.option_some.comp
      (Primrec.snd.comp Primrec.snd))
    ((Primrec.option_bind Primrec.snd
        (zstep_primrec₂.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd).to₂).to₂ :
      Primrec₂ fun (x : List Quint × ℕ × ZID) (o : Option ZID) => o.bind (zstep x.1))
  exact this.of_eq fun x => (zrun_eq_iter x.1 x.2.1 x.2.2).symm

theorem tmax_primrec : Primrec tmax :=
  (lmax_primrec.comp (Primrec.list_map Primrec.id (quint_t_primrec.comp Primrec.snd).to₂)).of_eq
    fun _ => rfl

theorem nsymOf_primrec₂ : Primrec₂ nsymOf := by
  have zL := (Primrec.fst.comp (Primrec.snd.comp Primrec.snd) :
    Primrec fun x : List Quint × ZID => x.2.2.1)
  have zR := (Primrec.snd.comp (Primrec.snd.comp Primrec.snd) :
    Primrec fun x : List Quint × ZID => x.2.2.2)
  exact (Primrec.nat_max.comp (Primrec.nat_add.comp (tmax_primrec.comp Primrec.fst) (Primrec.const 1))
    (Primrec.nat_add.comp (lmax_primrec.comp (Primrec.list_append.comp zL zR)) (Primrec.const 1))).of_eq
    fun _ => rfl

/-- 上界 `zbound` は (表, ID) の 2 引数について原始再帰的。 -/
theorem zbound_primrec₂ : Primrec₂ zbound := by
  have zL := (Primrec.fst.comp (Primrec.snd.comp Primrec.snd) :
    Primrec fun x : List Quint × ZID => x.2.2.1)
  have zR := (Primrec.snd.comp (Primrec.snd.comp Primrec.snd) :
    Primrec fun x : List Quint × ZID => x.2.2.2)
  have h := Primrec.nat_add.comp (bndN_primrec.comp nsymOf_primrec₂
    (Primrec.nat_add.comp (Primrec.list_length.comp zL) (Primrec.list_length.comp zR)))
    (Primrec.const 1)
  refine h.of_eq fun x => ?_
  show _ = zbound x.1 x.2
  unfold zbound
  rw [bnd_eq]

/-! ### 判定関数の一様な計算可能性と主定理（ZID 版） -/

/-- **判定関数 `zdecide` は (表, ID) の 2 引数について原始再帰的。** -/
theorem zdecide_primrec₂ : Primrec₂ zdecide := by
  have hr : Primrec fun x : List Quint × ZID => zrun x.1 (zbound x.1 x.2) x.2 :=
    zrun_primrec_uniform.comp (Primrec.pair Primrec.fst (Primrec.pair zbound_primrec₂ Primrec.snd))
  exact (Primrec.not.comp (Primrec.option_isSome.comp hr)).of_eq fun x => by
    show _ = zdecide x.1 x.2
    unfold zdecide; cases zrun x.1 (zbound x.1 x.2) x.2 <;> rfl

theorem zdecide_computable₂ : Computable₂ zdecide := zdecide_primrec₂.to_comp

/-- 判定の正しさ（既存の `zhalts_iff_bound` の言い換え）。 -/
theorem zdecide_iff {tbl : List Quint} {q₀ q₁ qf : ℕ} (hT : TwoStateRTM tbl q₀ q₁ qf) (z : ZID) :
    zdecide tbl z = true ↔ ZHalts tbl z := by
  rw [zhalts_iff_bound hT]
  unfold zdecide
  cases zrun tbl (zbound tbl z) z <;> simp

/-- **2 状態 RTM の停止問題は一様に決定可能**（有限 ID 上、表も入力に含めて）:
    1 つの計算可能な関数 `f` が、どの 2 状態 RTM の表 `tbl` とどの有限 ID `z` についても、
    `tbl` が `z` から止まるかを答える。 -/
theorem halting_computable_uniform :
    ∃ f : List Quint × ZID → Bool, Computable f ∧
      ∀ (tbl : List Quint) (q₀ q₁ qf : ℕ), TwoStateRTM tbl q₀ q₁ qf →
        ∀ z : ZID, f (tbl, z) = true ↔ ZHalts tbl z := by
  refine ⟨fun x => zdecide x.1 x.2, ?_, ?_⟩
  · exact zdecide_computable₂
  · intro tbl q₀ q₁ qf hT z
    exact zdecide_iff hT z

/-! ### 重複の除去は原始再帰的 -/

theorem list_dedup_primrec {α : Type} [Primcodable α] [DecidableEq α] :
    Primrec (List.dedup : List α → List α) := by
  have hc : PrimrecPred fun a : List α × α × List α => ∀ y ∈ a.2.2, a.2.1 ≠ y := by
    have h : PrimrecRel fun (L : List α) (b : α) => ∀ a ∈ L, ¬ a = b :=
      PrimrecRel.forall_mem_list (Primrec.eq (α := α)).not
    exact (h.comp (Primrec.snd.comp Primrec.snd) (Primrec.fst.comp Primrec.snd)).of_eq fun a => by
      constructor
      · intro hh y hy e; exact hh y hy e.symm
      · intro hh y hy e; exact hh y hy e.symm
  have hh : Primrec₂ fun (_ : List α) (a : α × List α) =>
      if ∀ y ∈ a.2, a.1 ≠ y then a.1 :: a.2 else a.2 :=
    Primrec.ite hc (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)
  exact (Primrec.list_foldr Primrec.id (Primrec.const []) hh).of_eq fun _ => rfl

end URTM.Meta

namespace URTM.Spec
open URTM URTM.Meta

/-! ### 主定理（`Spec.lean` の言葉で。一様版） -/

/-- **定理 1 前半の一様版**: 2 状態の RTM の停止問題は、表も入力に含めて決定可能である。
    1 つの計算可能な関数 `f` が、どの 2 状態 RTM `T`、どの位置 `p`、どの符号 `z` についても、
    `T` が有限 ID `toID p z` から停止するかを答える（`toID_complete` により、
    有限 ID はすべてこの形で表せる）。非一様版は `halting_decidable`。 -/
theorem halting_decidable_uniform :
    ∃ f : List Quint × ℤ × Code → Bool, Computable f ∧
      ∀ (T : List Quint) (q₀ q₁ qf : ℕ), TwoStateRTM T q₀ q₁ qf →
        ∀ (p : ℤ) (z : Code), f (T, p, z) = true ↔ Halts T (toID p z) := by
  refine ⟨fun x => zdecide x.1.dedup x.2.2, ?_, ?_⟩
  · exact (zdecide_primrec₂.comp (list_dedup_primrec.comp Primrec.fst)
      (Primrec.snd.comp Primrec.snd)).to_comp
  · intro T q₀ q₁ qf hT p z
    rw [zdecide_iff (meta_of_spec hT), ← halts_dedup, halts_toID_iff (det_dedup hT.det)]

/-- 出発状態に入る五つ組だけを残した表（出発状態がちょうど 2 つなら `stayTable` に一致）。 -/
def staySrc (T : List Quint) : List Quint := T.filter fun r => decide (r.q ∈ T.map Quint.p)

theorem staySrc_primrec : Primrec staySrc := by
  have hmem : PrimrecRel fun (r : Quint) (L : List ℕ) => r.q ∈ L := by
    have h : PrimrecRel fun (L : List ℕ) (b : ℕ) => ∃ a ∈ L, a = b :=
      PrimrecRel.exists_mem_list (Primrec.eq (α := ℕ))
    exact (h.comp Primrec.snd (quint_q_primrec.comp Primrec.fst)).of_eq fun x => by simp
  exact ((PrimrecRel.listFilter hmem).comp Primrec.id
    (Primrec.list_map Primrec.id (quint_p_primrec.comp Primrec.snd).to₂)).of_eq fun T => by
      simp [staySrc]

theorem staySrc_eq {T : List Quint} {q₀ q₁ : ℕ} (hqs : (T.map Quint.p).dedup = [q₀, q₁]) :
    staySrc T = stayTable T q₀ q₁ := by
  unfold staySrc stayTable
  apply List.filter_congr
  intro r _
  have h : r.q ∈ T.map Quint.p ↔ r.q = q₀ ∨ r.q = q₁ := by
    rw [← List.mem_dedup, hqs]; simp
  exact decide_eq_decide.mpr h

/-- **定理 1 前半の一様版（出発状態の種類数が 2 の形）**: 決定的かつ可逆で、
    五つ組の出発状態がちょうど 2 種類の表について、停止問題は表も入力に含めて決定可能である。
    非一様版は `halting_decidable_count`。帰着（行き先が出発状態でない五つ組を落とす）も
    計算可能に書ける（`staySrc`）。 -/
theorem halting_decidable_count_uniform :
    ∃ f : List Quint × ℤ × Code → Bool, Computable f ∧
      ∀ T : List Quint, Deterministic T → Reversible T → (T.map Quint.p).dedup.length = 2 →
        ∀ (p : ℤ) (z : Code), f (T, p, z) = true ↔ Halts T (toID p z) := by
  obtain ⟨g, hg, hge⟩ := halting_decidable_uniform
  refine ⟨fun x => g (staySrc x.1, x.2), ?_, ?_⟩
  · exact hg.comp (Computable.pair (staySrc_primrec.to_comp.comp Computable.fst) Computable.snd)
  · intro T hdet hrev hcount p z
    obtain ⟨q₀, q₁, hqs⟩ := List.length_eq_two.mp hcount
    have hne : q₀ ≠ q₁ := by
      have hn : [q₀, q₁].Nodup := hqs ▸ List.nodup_dedup (T.map Quint.p)
      exact (List.nodup_cons.mp hn).1 ∘ (by simp : q₀ = q₁ → q₀ ∈ [q₁])
    have hsrc : ∀ r ∈ T, r.p = q₀ ∨ r.p = q₁ := by
      intro r hr
      have hm : r.p ∈ (T.map Quint.p).dedup :=
        List.mem_dedup.mpr (List.mem_map.mpr ⟨r, hr, rfl⟩)
      rw [hqs] at hm
      simpa using hm
    show g (staySrc T, p, z) = true ↔ _
    rw [staySrc_eq hqs, hge _ q₀ q₁ _ (stay_two_state hdet hrev hne hsrc) p z]
    exact (halts_iff_stay hdet hsrc _).symm

end URTM.Spec
