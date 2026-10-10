/-
  **Morita Def. 7.1 をそのまま述べた UTM の定義**と、それに対する 2 状態 URTM の非存在（B3）。

  `NoURTM.lean` の `IsUTM` は、模倣される側を部分再帰関数のコード（`Nat.Partrec.Code`）で置いていた。
  ここでは Def. 7.1 の字義どおり、模倣される側を **TM の実効的な列挙 T₀, T₁, …** とその **有限 ID α**
  にする:
    * TM は五つ組 [p, s, t, d, q]（d ∈ {−, 0, +}）の有限表、テープは両側無限、空白は 0
      （本体の `Quint` と zipper `ZID`）。
    * 列挙 `tmOf n` は ℕ の 5 つ組のリストの標準の符号化（`Denumerable`）を復号したもの。
      全射で（`tmOf_index`）、万能の 1 歩関数 (n, α) ↦ T_n の 1 歩は原始再帰的（`tmStep_primrec`）。
    * c : ℕ × ID → ID(U)、d : ID(U) → ID ∪ {⊥}（⊥ = `none`）は全域計算可能（Mathlib `Computable`）。
    * Tₙ が α から止まって β に着くなら、U は c(n, α) から止まり、その停止 ID γ で d(γ) = β
      （ID の同一視は両端の空白の付け外しを除いて。`ZSame`）。
      Tₙ が α から止まらないなら U も c(n, α) から止まらない。

  証明: 2 状態 RTM の停止は計算可能（`halting_computable`）なので、U がそうなら
  列挙上の停止 (n, α) ↦ [Tₙ が α から止まる] が計算可能になる。ところが列挙には停止が決定不能な
  表 `tblU`（`UnivTable.lean`）が現れる。
-/
import URTMMeta.UnivTable
import URTMMeta.Demo

namespace URTM.Meta
open URTM URTM.TwoState

/-! ### TM の実効的な列挙 -/

/-- 方向の復号（0 = −, 1 = 0, それ以外 = +）。 -/
def dirOf : ℕ → Dir
  | 0 => .L
  | 1 => .Z
  | _ => .R

/-- 数の 5 つ組 (p, s, t, d, q) を五つ組に。 -/
def quintOf (x : ℕ × ℕ × ℕ × ℕ × ℕ) : Quint :=
  ⟨x.1, x.2.1, x.2.2.1, dirOf x.2.2.2.1, x.2.2.2.2⟩

def tupleOf (r : Quint) : ℕ × ℕ × ℕ × ℕ × ℕ := (r.p, r.s, r.t, dnum r.d, r.q)

theorem quintOf_tupleOf (r : Quint) : quintOf (tupleOf r) = r := by
  obtain ⟨p, s, t, d, q⟩ := r; cases d <;> rfl

/-- **TM の列挙 Tₙ**。 -/
def tmOf (n : ℕ) : List Quint := (Denumerable.ofNat (List (ℕ × ℕ × ℕ × ℕ × ℕ)) n).map quintOf

/-- 表の番号。 -/
def tmIndex (tbl : List Quint) : ℕ := Encodable.encode (tbl.map tupleOf)

/-- 列挙はすべての五つ組表を尽くす。 -/
theorem tmOf_index (tbl : List Quint) : tmOf (tmIndex tbl) = tbl := by
  unfold tmOf tmIndex
  rw [Denumerable.ofNat_encode, List.map_map]
  conv => rhs; rw [← List.map_id tbl]
  exact List.map_congr_left fun r _ => quintOf_tupleOf r

/-- 表引きを数の 5 つ組のまま行う。 -/
def lookT (l : List (ℕ × ℕ × ℕ × ℕ × ℕ)) (q s : ℕ) : Option (ℕ × ℕ × ℕ) :=
  l.foldr (fun x acc => if x.1 = q ∧ x.2.1 = s then
    some (x.2.2.1, dnum (dirOf x.2.2.2.1), x.2.2.2.2) else acc) none

theorem look_map (l : List (ℕ × ℕ × ℕ × ℕ × ℕ)) (q s : ℕ) :
    look (l.map quintOf) q s = lookT l q s := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.map_cons, look, lookT, List.foldr_cons] at ih ⊢
    rw [ih]; rfl

theorem dnum_dirOf_primrec : Primrec fun d : ℕ => dnum (dirOf d) := by
  have h := Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 0)) (Primrec.const 0)
    (Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 1)) (Primrec.const 1) (Primrec.const 2))
  refine h.of_eq fun d => ?_
  match d with
  | 0 => rfl
  | 1 => rfl
  | d + 2 => simp [dirOf, dnum]

theorem lookT_primrec :
    Primrec fun a : List (ℕ × ℕ × ℕ × ℕ × ℕ) × ℕ × ℕ => lookT a.1 a.2.1 a.2.2 := by
  have x := (Primrec.fst.comp Primrec.snd :
    Primrec fun p : (List (ℕ × ℕ × ℕ × ℕ × ℕ) × ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ × ℕ) ×
      Option (ℕ × ℕ × ℕ) => p.2.1)
  have acc := (Primrec.snd.comp Primrec.snd :
    Primrec fun p : (List (ℕ × ℕ × ℕ × ℕ × ℕ) × ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ × ℕ) ×
      Option (ℕ × ℕ × ℕ) => p.2.2)
  have q := (Primrec.fst.comp (Primrec.snd.comp Primrec.fst) :
    Primrec fun p : (List (ℕ × ℕ × ℕ × ℕ × ℕ) × ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ × ℕ) ×
      Option (ℕ × ℕ × ℕ) => p.1.2.1)
  have s := (Primrec.snd.comp (Primrec.snd.comp Primrec.fst) :
    Primrec fun p : (List (ℕ × ℕ × ℕ × ℕ × ℕ) × ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ × ℕ) ×
      Option (ℕ × ℕ × ℕ) => p.1.2.2)
  have x1 := Primrec.fst.comp x
  have x2 := Primrec.fst.comp (Primrec.snd.comp x)
  have x3 := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp x))
  have x4 := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp x)))
  have x5 := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp x)))
  have hh := Primrec.ite (PrimrecPred.and (Primrec.eq.comp x1 q) (Primrec.eq.comp x2 s))
    (Primrec.option_some.comp (Primrec.pair x3 (Primrec.pair (dnum_dirOf_primrec.comp x4) x5)))
    acc
  exact (Primrec.list_foldr Primrec.fst (Primrec.const none) hh.to₂).of_eq fun a => rfl

/-- 列挙の n 番目の TM の 1 歩（zipper）。 -/
def tmStep (n : ℕ) (z : ZID) : Option ZID := zstep (tmOf n) z

/-- **列挙は実効的**: 万能の 1 歩関数 (n, α) ↦ Tₙ の 1 歩 は原始再帰的。 -/
theorem tmStep_primrec : Primrec₂ tmStep := by
  have hl : Primrec fun p : ℕ × ZID =>
      lookT (Denumerable.ofNat (List (ℕ × ℕ × ℕ × ℕ × ℕ)) p.1) p.2.1 (p.2.2.2.headD 0) :=
    lookT_primrec.comp (Primrec.pair ((Primrec.ofNat _).comp Primrec.fst)
      (Primrec.pair (Primrec.fst.comp Primrec.snd)
        (headD_primrec.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))
  have hm : Primrec₂ fun (p : ℕ × ZID) (o : ℕ × ℕ × ℕ) => mv o p.2 :=
    mv_primrec.comp Primrec.snd (Primrec.snd.comp Primrec.fst)
  refine (Primrec.option_map hl hm).of_eq fun p => ?_
  show _ = zstep (tmOf p.1) p.2
  unfold zstep tmOf
  rw [look_map]

/-! ### T の ID（Morita Def. 5.5）

Def. 7.1 が量化するのは α ∈ ID(Tₙ) だけで、Def. 5.5 の ID(T) は **T 自身の状態と記号**からなる語である。
五つ組表には状態集合・記号集合の宣言が無いので、**表に現れるもの**を T の状態・記号とする:
  * 状態 = 五つ組の現状態 p と次状態 q に現れる番号（表には始状態の指定が無いので、始状態も
    この中にあるとみなす。Morita の TM の状態集合 Q はこれを含む）。
  * 記号 = 空白 0 と、五つ組の読込記号 s・書込記号 t に現れる番号（記号集合 S はこれを含む）。
これは Morita の ID(T) の**部分集合**（Q・S をどれだけ大きく取っても含まれる）なので、
ここでの「模倣する」は Def. 7.1 の要求**以下**、したがって「模倣しない」は Def. 7.1 の意味で
模倣しないことを**含意する**。判定可能（`DecidablePred`）。 -/

/-- 表に現れる状態（五つ組の p と q）。 -/
def statesOf (T : List Quint) : List Nat := T.flatMap fun r => [r.p, r.q]

/-- 表に現れる記号（五つ組の s と t）。空白 0 は別に許す。 -/
def symsOf (T : List Quint) : List Nat := T.flatMap fun r => [r.s, r.t]

/-- **α ∈ ID(T)**（Def. 5.5）: 状態は T の状態、テープの記号は空白か T の記号。 -/
def IDOf (T : List Quint) (z : ZID) : Prop :=
  z.1 ∈ statesOf T ∧ ∀ a ∈ z.2.1 ++ z.2.2, a = 0 ∨ a ∈ symsOf T

instance (T : List Quint) : DecidablePred (IDOf T) := fun z => by
  unfold IDOf; infer_instance

/-- 両端に空白を足しても T の ID のまま（ID は両端の空白を除いて同一視する。`ZSame` と整合）。 -/
theorem IDOf.pad {T : List Quint} {z : ZID} (h : IDOf T z) (k m : ℕ) :
    IDOf T (z.1, z.2.1 ++ List.replicate k 0, z.2.2 ++ List.replicate m 0) := by
  refine ⟨h.1, fun a ha => ?_⟩
  simp only [List.mem_append, List.mem_replicate] at ha
  rcases ha with (ha | ⟨_, rfl⟩) | (ha | ⟨_, rfl⟩)
  · exact h.2 a (List.mem_append_left _ ha)
  · exact Or.inl rfl
  · exact h.2 a (List.mem_append_right _ ha)
  · exact Or.inl rfl

/-- 制限は自明でない: 表に無い状態・記号を使う ID は外れる。 -/
example : IDOf haltTbl (0, [], [1, 0]) ∧ ¬ IDOf haltTbl (2, [], []) ∧
    ¬ IDOf haltTbl (0, [], [5]) := by decide

/-- `tblU` の始状態 `stN S0 default` では、どの記号にも規則がある（`TM1to0.tr` は `some` 状態で全域）。 -/
theorem M0_default_some (a : Γ₁) : ∃ o, M0 default a = some o := ⟨_, rfl⟩

theorem mem_tblU_default (a : Γ₁) : ∃ r ∈ tblU, r.p = stN S0 default ∧ r.s = symN a := by
  obtain ⟨o, ho⟩ := M0_default_some a
  exact ⟨mkQ S0 default a o, mem_tblOf.mpr ⟨default, M0_supports.1, a, o, ho, rfl⟩,
    mkQ_p .., mkQ_s ..⟩

theorem symN_mem_symsOf_tblU (a : Γ₁) : symN a ∈ symsOf tblU := by
  obtain ⟨r, hr, -, hs⟩ := mem_tblU_default a
  exact List.mem_flatMap.mpr ⟨r, hr, by simp [hs]⟩

/-- **入力の符号化 `zidU x` は `tblU` の ID**（`tblU` の始状態と `tblU` の記号だけを使う）。 -/
theorem IDOf_tblU_zidU (x : ℕ) : IDOf tblU (zidU x) := by
  refine ⟨?_, fun a ha => Or.inr ?_⟩
  · obtain ⟨r, hr, hp, -⟩ := mem_tblU_default (default : Γ₁)
    exact List.mem_flatMap.mpr ⟨r, hr, by simp [hp, zidU]⟩
  · simp only [zidU, List.nil_append, List.mem_cons, binU, List.mem_map] at ha
    rcases ha with rfl | ⟨b, -, rfl⟩
    · exact symN_mem_symsOf_tblU _
    · exact symN_mem_symsOf_tblU _

/-! ### Def. 7.1（α ∈ ID(Tₙ) に制限した、字義どおりの形）

c : ℕ × ID → ID(U) と d : ID(U) → ID ∪ {⊥}（⊥ = `none`）は、ここでは全域の `ZID` 上の計算可能関数
として置く。`IDOf` は判定可能なので、ID(Tₙ)・ID(U) 上だけで計算可能な c, d は既定値で全域に
計算可能に延長でき、この置き方は Def. 7.1 と同値。c(n, α) ∈ ID(U) は要求しない（要求を弱める側）。 -/

/-- 有限 ID の同一視（状態が同じで、テープの中身が両端の空白を除いて同じ）。 -/
def ZSame (z z' : ZID) : Prop :=
  z.1 = z'.1 ∧ (∀ i, z.2.1.getD i 0 = z'.2.1.getD i 0) ∧ (∀ i, z.2.2.getD i 0 = z'.2.2.getD i 0)

/-- **Morita Def. 5.8 を TM どうしで**: 表 tbl の機械 U が、TM `T` を ID(T) の各 α について模倣する。 -/
def SimulatesTM (tbl T : List Quint) : Prop :=
  ∃ (c : ZID → ZID) (d : ZID → Option ZID), Computable c ∧ Computable d ∧
    ∀ α, IDOf T α → (∀ β, ZHaltsAt T α β →
        ∃ γ, ZHaltsAt tbl (c α) γ ∧ ∃ β', d γ = some β' ∧ ZSame β' β) ∧
      (¬ ZHalts T α → ¬ ZHalts tbl (c α))

/-- 列挙 E の TM をすべて（番号つきで、α ∈ ID(E n) について）模倣する。 -/
def SimulatesEnum (tbl : List Quint) (E : ℕ → List Quint) : Prop :=
  ∃ (c : ℕ × ZID → ZID) (d : ZID → Option ZID), Computable c ∧ Computable d ∧
    ∀ n α, IDOf (E n) α → (∀ β, ZHaltsAt (E n) α β →
        ∃ γ, ZHaltsAt tbl (c (n, α)) γ ∧ ∃ β', d γ = some β' ∧ ZSame β' β) ∧
      (¬ ZHalts (E n) α → ¬ ZHalts tbl (c (n, α)))

/-- **Morita Def. 7.1（UTM）**: TM の実効的な列挙 Tₙ（`tmOf`）のすべてを、各 α ∈ ID(Tₙ) で模倣する。 -/
def IsUTM_Morita (tbl : List Quint) : Prop := SimulatesEnum tbl tmOf

theorem SimulatesEnum.halts_iff {tbl : List Quint} {E : ℕ → List Quint}
    {c : ℕ × ZID → ZID} {d : ZID → Option ZID}
    (h : ∀ n α, IDOf (E n) α → (∀ β, ZHaltsAt (E n) α β →
        ∃ γ, ZHaltsAt tbl (c (n, α)) γ ∧ ∃ β', d γ = some β' ∧ ZSame β' β) ∧
      (¬ ZHalts (E n) α → ¬ ZHalts tbl (c (n, α)))) (n : ℕ) (α : ZID) (hα : IDOf (E n) α) :
    ZHalts (E n) α ↔ ZHalts tbl (c (n, α)) := by
  constructor
  · intro hH
    obtain ⟨β, hβ⟩ := hH.exists_at
    obtain ⟨γ, hγ, _⟩ := (h n α hα).1 β hβ
    exact ZHalts_of_at hγ
  · intro hU
    by_contra hn
    exact (h n α hα).2 hn hU

/-- 2 状態 RTM が列挙 E を模倣するなら、E の停止 (n, α) は **α ∈ ID(E n) の上で**計算可能に判定できる。 -/
theorem enum_halting_computable {tbl : List Quint} {q₀ q₁ qf : Nat}
    (hT : TwoStateRTM tbl q₀ q₁ qf) {E : ℕ → List Quint} (hs : SimulatesEnum tbl E) :
    ∃ f : ℕ × ZID → Bool, Computable f ∧
      ∀ p : ℕ × ZID, IDOf (E p.1) p.2 → (ZHalts (E p.1) p.2 ↔ f p = true) := by
  obtain ⟨c, d, hc, _, h⟩ := hs
  obtain ⟨f, hf, hfe⟩ := ComputablePred.computable_iff.mp (halting_computable hT)
  refine ⟨fun p => f (c p), hf.comp hc, fun p hp => ?_⟩
  rw [SimulatesEnum.halts_iff h p.1 p.2 hp]
  exact iff_of_eq (congrFun hfe (c p))

/-- **列挙 Tₙ 上の停止問題は、α ∈ ID(Tₙ) に制限しても決定不能**
    （列挙に `tblU` が現れ、その入力 `zidU x` は `tblU` の ID なので）。 -/
theorem tm_halting_undecidable :
    ¬ ∃ f : ℕ × ZID → Bool, Computable f ∧
      ∀ p : ℕ × ZID, IDOf (tmOf p.1) p.2 → (ZHalts (tmOf p.1) p.2 ↔ f p = true) := by
  rintro ⟨f, hf, hfe⟩
  apply tblU_undecidable
  refine ComputablePred.computable_iff.mpr
    ⟨fun x => f (tmIndex tblU, zidU x),
      hf.comp (Computable.pair (Computable.const _) zidU_primrec.to_comp), ?_⟩
  funext x
  have hid : IDOf (tmOf (tmIndex tblU)) (zidU x) := by
    rw [tmOf_index]; exact IDOf_tblU_zidU x
  have := hfe (tmIndex tblU, zidU x) hid
  simp only [tmOf_index] at this
  exact propext this

/-- **定理（Morita B3 の否定的解決、Def. 7.1 の字義どおりの形）: 2 状態 URTM は存在しない。**
    q₀, q₁ の 2 状態（加えて停止用の疑似状態 qf）の決定的・可逆な 1 テープ五つ組 TM は、
    TM の実効的な列挙 Tₙ とその ID α ∈ ID(Tₙ) を Def. 7.1 の意味で模倣できない。 -/
theorem no_two_state_URTM_Morita (tbl : List Quint) (q₀ q₁ qf : Nat)
    (hT : TwoStateRTM tbl q₀ q₁ qf) : ¬ IsUTM_Morita tbl :=
  fun hU => tm_halting_undecidable (enum_halting_computable hT hU)

/-- **定理（Morita B2 の否定的解決、Def. 5.8/5.9 の TM どうしの形）: 1 テープ 2 状態 RTM のクラスは
    計算万能でない。** ある 1 テープ TM（列挙の番号 n の `tmOf n`）は、どの 2 状態 RTM にも
    （その ID の上で）模倣されない。 -/
theorem two_state_class_not_universal_Morita :
    ∃ n : ℕ, ∀ (tbl : List Quint) (q₀ q₁ qf : Nat), TwoStateRTM tbl q₀ q₁ qf →
      ¬ SimulatesTM tbl (tmOf n) := by
  refine ⟨tmIndex tblU, fun tbl q₀ q₁ qf hT hs => ?_⟩
  rw [tmOf_index] at hs
  obtain ⟨c, d, hc, hd, h⟩ := hs
  -- 定数列挙に持ち上げて `enum_halting_computable` を使う
  have hE : SimulatesEnum tbl (fun _ => tblU) :=
    ⟨fun p => c p.2, d, hc.comp Computable.snd, hd, fun _ α hα => h α hα⟩
  obtain ⟨f, hf, hfe⟩ := enum_halting_computable hT hE
  apply tblU_undecidable
  refine ComputablePred.computable_iff.mpr
    ⟨fun x => f (0, zidU x), hf.comp (Computable.pair (Computable.const 0) zidU_primrec.to_comp), ?_⟩
  funext x
  exact propext (hfe (0, zidU x) (IDOf_tblU_zidU x))

/-! ### 旧版（全 ID 版、`_allID`）

2026-09-29 までの定義は α を**すべての**有限 ID（Tₙ の記号・状態の外のものを含む）で量化していた。
これは Def. 7.1 より強い要求なので、その否定は Def. 7.1 の否定より弱い。比較のため残し、
新しい（制限した）定理からの系として示す。論文が引くのは上の制限版。 -/

def SimulatesTM_allID (tbl T : List Quint) : Prop :=
  ∃ (c : ZID → ZID) (d : ZID → Option ZID), Computable c ∧ Computable d ∧
    ∀ α, (∀ β, ZHaltsAt T α β →
        ∃ γ, ZHaltsAt tbl (c α) γ ∧ ∃ β', d γ = some β' ∧ ZSame β' β) ∧
      (¬ ZHalts T α → ¬ ZHalts tbl (c α))

def SimulatesEnum_allID (tbl : List Quint) (E : ℕ → List Quint) : Prop :=
  ∃ (c : ℕ × ZID → ZID) (d : ZID → Option ZID), Computable c ∧ Computable d ∧
    ∀ n α, (∀ β, ZHaltsAt (E n) α β →
        ∃ γ, ZHaltsAt tbl (c (n, α)) γ ∧ ∃ β', d γ = some β' ∧ ZSame β' β) ∧
      (¬ ZHalts (E n) α → ¬ ZHalts tbl (c (n, α)))

def IsUTM_Morita_allID (tbl : List Quint) : Prop := SimulatesEnum_allID tbl tmOf

theorem SimulatesTM_allID.restrict {tbl T : List Quint} (h : SimulatesTM_allID tbl T) :
    SimulatesTM tbl T :=
  let ⟨c, d, hc, hd, h⟩ := h
  ⟨c, d, hc, hd, fun α _ => h α⟩

theorem SimulatesEnum_allID.restrict {tbl : List Quint} {E : ℕ → List Quint}
    (h : SimulatesEnum_allID tbl E) : SimulatesEnum tbl E :=
  let ⟨c, d, hc, hd, h⟩ := h
  ⟨c, d, hc, hd, fun n α _ => h n α⟩

theorem no_two_state_URTM_Morita_allID (tbl : List Quint) (q₀ q₁ qf : Nat)
    (hT : TwoStateRTM tbl q₀ q₁ qf) : ¬ IsUTM_Morita_allID tbl :=
  fun hU => no_two_state_URTM_Morita tbl q₀ q₁ qf hT (SimulatesEnum_allID.restrict hU)

theorem two_state_class_not_universal_Morita_allID :
    ∃ n : ℕ, ∀ (tbl : List Quint) (q₀ q₁ qf : Nat), TwoStateRTM tbl q₀ q₁ qf →
      ¬ SimulatesTM_allID tbl (tmOf n) :=
  let ⟨n, hn⟩ := two_state_class_not_universal_Morita
  ⟨n, fun tbl q₀ q₁ qf hT hs => hn tbl q₀ q₁ qf hT (SimulatesTM_allID.restrict hs)⟩

/-! ### 空虚でないこと -/

theorem ZSame.refl (z : ZID) : ZSame z z := ⟨rfl, fun _ => rfl, fun _ => rfl⟩

/-- どの TM も自分自身を（c = 恒等、d = some で）模倣する。`SimulatesTM` の 2 条件は両立する。 -/
theorem simulatesTM_self (T : List Quint) : SimulatesTM T T := by
  refine ⟨id, some, Computable.id, Computable.option_some, fun α _ => ⟨?_, fun h => h⟩⟩
  intro β hβ
  exact ⟨β, hβ, β, rfl, ZSame.refl β⟩

/-- 定数列挙（1 台だけ）なら、その TM 自身が「万能」になる。`SimulatesEnum` は充足可能。 -/
theorem simulatesEnum_const (T : List Quint) : SimulatesEnum T (fun _ => T) := by
  refine ⟨Prod.snd, some, Computable.snd, Computable.option_some, fun n α _ => ⟨?_, fun h => h⟩⟩
  intro β hβ
  exact ⟨β, hβ, β, rfl, ZSame.refl β⟩

/-- 2 状態 RTM でも、停止が決定可能な列挙なら模倣できる（`haltTbl` の定数列挙）。
    非存在は「2 状態」ではなく「列挙の停止の決定不能性」から来ている。 -/
theorem two_state_simulates_const : SimulatesEnum haltTbl (fun _ => haltTbl) :=
  simulatesEnum_const haltTbl

end URTM.Meta
