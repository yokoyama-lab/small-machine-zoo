/-
  **Spec の両側無限テープの ID と、原典の文字列上の ID（αqβ）の対応**（docs/28）。

  `Spec.IsUTMStrict U`（ID = ヘッド位置つきの両側無限テープ `ℤ → ℕ`、関係 `Step`、列挙 `tm`）から、
  legacy lean-meta の文字列上の Def. 7.1 `Meta.IsUTM_Morita U`（ID = `ZID`（αqβ の α を逆順に持つ）、
  関数 `zstep`（表の先頭一致）、列挙 `tmOf`（決定的でない表も含む））を導く。U が決定的であることを仮定する
  （主定理の証人はすべて決定的）。

  * (a) `zstep_eq`・`haltsAt_iff`・`halts_iff`: 決定的な表で、Spec の停止と `zrun` の停止が `toID` で対応する。
  * (b) `detT`: 数の 5 つ組の表を、状態番号 < `topT l + 1` の ID の上で先頭一致の動きを変えずに
    決定的な表にする（2 本目以降の (p, s) の五つ組を、到達しない新しい状態から出す）。
    `tm (encode (detT l)) = (detT l).map quintOf`（`tm_detT`）なので、`tmOf n` の模倣を `tm` の模倣に帰着できる。
    番号の写し `idx` は原始再帰的（`idx_primrec`）。
  * (c) `isUTM_MoritaStrict`・`isUTM_Morita`: `Deterministic U → IsUTMStrict U → IsUTM_MoritaStrict U`、
    そこから `IsUTM_Morita U`。
-/
import LeanUniv.MoritaDefs
import LeanUniv.L0Zipper
import LeanUniv.KToSpec
import LeanUniv.CodePad

namespace URTM.Univ.StringID
open URTM URTM.Spec Relation
open URTM.Meta (ZID zrun ZHalts ZHaltsAt IDOf ZSame tmOf statesOf symsOf quintOf dirOf
  SimulatesEnum IsUTM_Morita)

/-! ### (a) 文字列側の 1 歩は L0 の zipper の 1 歩と同じ。Spec の停止との対応 -/

theorem dnum_eq (d : Dir) : Meta.dnum d = L0.dnum d := by cases d <;> rfl

theorem rhs_eq (r : Quint) : Meta.rhs r = L0.rhs r := by
  simp only [Meta.rhs, L0.rhs, dnum_eq]

theorem look_eq (T : List Quint) (q s : ℕ) : Meta.look T q s = L0.look T q s := by
  induction T with
  | nil => rfl
  | cons r T ih => simp only [Meta.look, L0.look, rhs_eq, ih]

theorem zstep_eq (T : List Quint) (z : ZID) : Meta.zstep T z = L0.zstep T z := by
  simp only [Meta.zstep, L0.zstep, look_eq]; rfl

theorem zrun_succ (T : List Quint) :
    ∀ (n : ℕ) (z : ZID), zrun T (n + 1) z = (zrun T n z).bind (Meta.zstep T)
  | 0, z => by
    simp only [zrun, Option.bind_some]
    cases Meta.zstep T z <;> rfl
  | n + 1, z => by
    conv_lhs => unfold zrun
    conv_rhs => unfold zrun
    cases Meta.zstep T z with
    | none => rfl
    | some z' => exact zrun_succ T n z'

/-- `ZHaltsAt` through the run only. -/
theorem zhaltsAt_iff (T : List Quint) (x z : ZID) :
    ZHaltsAt T x z ↔ ∃ n, zrun T n x = some z ∧ zrun T (n + 1) x = none := by
  constructor
  · rintro ⟨n, h1, h2⟩
    exact ⟨n, h1, by rw [zrun_succ, h1, Option.bind_some, h2]⟩
  · rintro ⟨n, h1, h2⟩
    refine ⟨n, h1, ?_⟩
    rw [zrun_succ, h1, Option.bind_some] at h2
    exact h2

theorem zhalts_exists_at (T : List Quint) :
    ∀ (n : ℕ) (x : ZID), zrun T n x = none → ∃ z, ZHaltsAt T x z
  | 0, x, h => by simp [zrun] at h
  | n + 1, x, h => by
    unfold zrun at h
    cases hs : Meta.zstep T x with
    | none => exact ⟨x, 0, rfl, hs⟩
    | some x' =>
      rw [hs] at h
      obtain ⟨z, m, h1, h2⟩ := zhalts_exists_at T n x' h
      exact ⟨z, m + 1, by simp only [zrun, hs]; exact h1, h2⟩

theorem zhalts_iff (T : List Quint) (x : ZID) : ZHalts T x ↔ ∃ z, ZHaltsAt T x z := by
  constructor
  · rintro ⟨n, hn⟩; exact zhalts_exists_at T n x hn
  · rintro ⟨z, h⟩
    obtain ⟨n, -, h2⟩ := (zhaltsAt_iff T x z).mp h
    exact ⟨n + 1, h2⟩

theorem rtg_of_zrun (T : List Quint) :
    ∀ (n : ℕ) (x z : ZID), zrun T n x = some z →
      ∀ p : ℤ, ∃ p', ReflTransGen (L0.PStep T) (p, x) (p', z)
  | 0, x, z, h, p => by
    simp only [zrun, Option.some.injEq] at h
    exact ⟨p, h ▸ ReflTransGen.refl⟩
  | n + 1, x, z, h, p => by
    unfold zrun at h
    cases hs : Meta.zstep T x with
    | none => rw [hs] at h; cases h
    | some x' =>
      rw [hs] at h
      have hp : (L0.pstep T (p, x)).map Prod.snd = some x' := by
        rw [L0.pstep_snd, ← zstep_eq, hs]
      obtain ⟨b, hb, hb2⟩ := Option.map_eq_some_iff.mp hp
      obtain ⟨p', hr⟩ := rtg_of_zrun T n x' z h b.1
      refine ⟨p', ReflTransGen.head (b := b) hb ?_⟩
      rw [← hb2] at hr
      exact hr

theorem zrun_of_rtg (T : List Quint) {a b : ℤ × ZID} (h : ReflTransGen (L0.PStep T) a b) :
    ∃ n, zrun T n a.2 = some b.2 := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | tail _ hs ih =>
    rename_i b c _
    obtain ⟨n, hn⟩ := ih
    refine ⟨n + 1, ?_⟩
    have : Meta.zstep T b.2 = some c.2 := by
      have := congrArg (Option.map Prod.snd) hs
      rw [show b = (b.1, b.2) from rfl, L0.pstep_snd] at this
      rw [zstep_eq]; exact this
    rw [zrun_succ, hn, Option.bind_some, this]

/-- **(a) 停止の対応（Spec → 文字列）**: 決定的な表で、Spec が `toID 0 x` から停止 ID `γ` に着くなら、
    文字列側の実行が `x` から停止 ID `z` に着き、`γ = toID p z`。 -/
theorem zhaltsAt_of_haltsAt {T : List Quint} (hdet : Deterministic T) {x : ZID} {γ : ID}
    (h : HaltsAt T (toID 0 x) γ) : ∃ p z, γ = toID p z ∧ ZHaltsAt T x z := by
  obtain ⟨p', z', hr, hn, rfl⟩ := (L0.haltsAt_toID_iff hdet 0 x γ).mp h
  obtain ⟨n, hz⟩ := zrun_of_rtg T hr
  exact ⟨p', z', rfl, n, hz, by rw [zstep_eq]; exact hn⟩

/-- **(a) 停止の対応（文字列 → Spec）**: どの表でも、文字列側の実行が `x` から停止 ID `z` に着くなら、
    Spec は `toID 0 x` からある位置 `p` の `toID p z` に着いて止まる。 -/
theorem haltsAt_of_zhaltsAt {T : List Quint} {x z : ZID} (h : ZHaltsAt T x z) :
    ∃ p, HaltsAt T (toID 0 x) (toID p z) := by
  obtain ⟨n, hz, hn⟩ := h
  obtain ⟨p', hr⟩ := rtg_of_zrun T n x z hz 0
  refine ⟨p', ?_, L0.halted_of_zstep (by rw [← zstep_eq]; exact hn) p'⟩
  suffices ∀ b, ReflTransGen (L0.PStep T) (0, x) b → ReflTransGen (Step T) (toID 0 x) (toID b.1 b.2)
    from this _ hr
  intro b hb
  induction hb with
  | refl => exact ReflTransGen.refl
  | tail _ hs ih =>
    rename_i b c _
    unfold L0.PStep L0.pstep at hs
    cases hl : L0.look T b.2.1 (b.2.2.2.headD 0) with
    | none => rw [hl] at hs; cases hs
    | some o =>
      rw [hl] at hs; cases hs
      exact ih.tail (L0.step_of_look hl b.1)

/-- **(a) 停止するかどうかの対応**: 決定的な表で、Spec が `toID 0 x` から停止することと、
    文字列側の実行が `x` から停止することは同値。 -/
theorem halts_iff {T : List Quint} (hdet : Deterministic T) (x : ZID) :
    Halts T (toID 0 x) ↔ ZHalts T x := by
  rw [zhalts_iff]
  constructor
  · rintro ⟨γ, h⟩
    obtain ⟨p, z, -, hz⟩ := zhaltsAt_of_haltsAt hdet h
    exact ⟨z, hz⟩
  · rintro ⟨z, hz⟩
    obtain ⟨p, h⟩ := haltsAt_of_zhaltsAt hz
    exact ⟨_, h⟩

/-! ### (b) 決定的でない表の決定化 `detT` -/

/-- 数の 5 つ組 (p, s, t, d, q)。 -/
abbrev Tup := ℕ × ℕ × ℕ × ℕ × ℕ

/-- 表 `l` で (p, s) に先頭一致する 5 つ組。 -/
def firstT (l : List Tup) (p s : ℕ) : Option Tup :=
  l.foldr (fun y acc => if y.1 = p ∧ y.2.1 = s then some y else acc) none

/-- 表に現れる状態番号（p と q）の最大値。 -/
def topT (l : List Tup) : ℕ := l.foldr (fun y m => max (max y.1 y.2.2.2.2) m) 0

/-- 先頭一致でない 5 つ組は、状態を `topT l + 1 + encode (t, d, q)`（表に現れない番号）に付け替える。 -/
def relabel (l : List Tup) (x : Tup) : Tup :=
  if firstT l x.1 x.2.1 = some x then x else (topT l + 1 + Encodable.encode x.2.2, x.2)

/-- **決定化**: 各 5 つ組を `relabel` する。 -/
def detT (l : List Tup) : List Tup := l.map (relabel l)

theorem firstT_some {l : List Tup} {p s : ℕ} {y : Tup} (h : firstT l p s = some y) :
    y ∈ l ∧ y.1 = p ∧ y.2.1 = s := by
  induction l with
  | nil => simp [firstT] at h
  | cons a l ih =>
    simp only [firstT, List.foldr_cons] at h
    split_ifs at h with ha
    · cases h; exact ⟨List.mem_cons_self .., ha.1, ha.2⟩
    · obtain ⟨h1, h2, h3⟩ := ih h
      exact ⟨List.mem_cons_of_mem _ h1, h2, h3⟩

theorem firstT_exists {l : List Tup} {x : Tup} (hx : x ∈ l) :
    ∃ y, firstT l x.1 x.2.1 = some y := by
  induction l with
  | nil => simp at hx
  | cons a l ih =>
    simp only [firstT, List.foldr_cons]
    split_ifs with ha
    · exact ⟨a, rfl⟩
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact absurd ⟨rfl, rfl⟩ ha
      · exact ih hx

theorem le_topT {l : List Tup} {x : Tup} (hx : x ∈ l) : x.1 ≤ topT l ∧ x.2.2.2.2 ≤ topT l := by
  induction l with
  | nil => simp at hx
  | cons a l ih =>
    simp only [topT, List.foldr_cons] at ih ⊢
    rcases List.mem_cons.mp hx with rfl | hx
    · omega
    · have := ih hx; omega

theorem relabel_snd (l : List Tup) (x : Tup) : (relabel l x).2 = x.2 := by
  unfold relabel; split_ifs <;> rfl

theorem relabel_of_first {l : List Tup} {x : Tup} (h : firstT l x.1 x.2.1 = some x) :
    relabel l x = x := by
  unfold relabel; rw [if_pos h]

theorem relabel_fst {l : List Tup} {x : Tup} (h : ¬ firstT l x.1 x.2.1 = some x) :
    (relabel l x).1 = topT l + 1 + Encodable.encode x.2.2 := by
  unfold relabel; rw [if_neg h]

/-- `relabel` は (p, s) に一致しない 5 つ組を一致させない（状態 `st ≤ topT l0` のとき）。 -/
theorem relabel_nomatch {l0 : List Tup} {y : Tup} {st s : ℕ} (hst : st ≤ topT l0)
    (hy : ¬ (y.1 = st ∧ y.2.1 = s)) : ¬ ((relabel l0 y).1 = st ∧ (relabel l0 y).2.1 = s) := by
  by_cases h : firstT l0 y.1 y.2.1 = some y
  · rw [relabel_of_first h]; exact hy
  · rw [relabel_fst h]; omega

theorem look_detT_aux (l0 : List Tup) (st s : ℕ) (hst : st ≤ topT l0) :
    ∀ l : List Tup, firstT l0 st s = firstT l st s →
      Meta.look ((l.map (relabel l0)).map quintOf) st s = Meta.look (l.map quintOf) st s
  | [], _ => rfl
  | y :: l, h => by
    simp only [List.map_cons, Meta.look]
    by_cases hy : y.1 = st ∧ y.2.1 = s
    · have hf : firstT (y :: l) st s = some y := by
        simp only [firstT, List.foldr_cons, if_pos hy]
      obtain ⟨h1, h2⟩ := hy
      subst h1 h2
      rw [relabel_of_first (h.trans hf), if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, rfl⟩]
    · have hf : firstT (y :: l) st s = firstT l st s := by
        simp only [firstT, List.foldr_cons, if_neg hy]
      have hq : ¬ ((quintOf (relabel l0 y)).p = st ∧ (quintOf (relabel l0 y)).s = s) :=
        relabel_nomatch hst hy
      have hq' : ¬ ((quintOf y).p = st ∧ (quintOf y).s = s) := hy
      rw [if_neg hq, if_neg hq', look_detT_aux l0 st s hst l (h.trans hf)]

/-- **先頭一致の一致**: 状態 `st ≤ topT l` では、決定化した表の表引きは元の表の表引きと同じ。 -/
theorem look_detT (l : List Tup) {st : ℕ} (hst : st ≤ topT l) (s : ℕ) :
    Meta.look ((detT l).map quintOf) st s = Meta.look (l.map quintOf) st s :=
  look_detT_aux l st s hst l rfl

theorem look_mem {T : List Quint} {q s : ℕ} {o : ℕ × ℕ × ℕ} (h : Meta.look T q s = some o) :
    ∃ r ∈ T, o.2.2 = r.q := by
  rw [look_eq] at h
  obtain ⟨r, hr, -, -, rfl⟩ := L0.look_some h
  exact ⟨r, hr, rfl⟩

theorem mv_fst (o : ℕ × ℕ × ℕ) (z : ZID) : (Meta.mv o z).1 = o.2.2 := by
  unfold Meta.mv; split_ifs <;> rfl

/-- 元の表の 1 歩は状態番号を `topT l` 以下に保つ。 -/
theorem zstep_top {l : List Tup} {z z' : ZID} (h : Meta.zstep (l.map quintOf) z = some z') :
    z'.1 ≤ topT l := by
  unfold Meta.zstep at h
  obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨r, hr, hq⟩ := look_mem ho
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
  rw [mv_fst, hq]
  exact (le_topT hx).2

theorem zstep_detT (l : List Tup) {z : ZID} (hz : z.1 ≤ topT l) :
    Meta.zstep ((detT l).map quintOf) z = Meta.zstep (l.map quintOf) z := by
  unfold Meta.zstep; rw [look_detT l hz]

/-- **実行の一致**: 状態 `≤ topT l` の ID から、決定化した表と元の表の実行は同じ。 -/
theorem zrun_detT (l : List Tup) :
    ∀ (n : ℕ) (z : ZID), z.1 ≤ topT l → zrun ((detT l).map quintOf) n z = zrun (l.map quintOf) n z
  | 0, _, _ => rfl
  | n + 1, z, hz => by
    simp only [zrun]
    rw [zstep_detT l hz]
    cases h : Meta.zstep (l.map quintOf) z with
    | none => rfl
    | some z' => exact zrun_detT l n z' (zstep_top h)

theorem zhaltsAt_detT (l : List Tup) {x : ZID} (hx : x.1 ≤ topT l) (z : ZID) :
    ZHaltsAt ((detT l).map quintOf) x z ↔ ZHaltsAt (l.map quintOf) x z := by
  simp only [zhaltsAt_iff, zrun_detT l _ x hx]

theorem zhalts_detT (l : List Tup) {x : ZID} (hx : x.1 ≤ topT l) :
    ZHalts ((detT l).map quintOf) x ↔ ZHalts (l.map quintOf) x := by
  simp only [ZHalts, zrun_detT l _ x hx]

/-- **決定化した表は決定的**（Spec の `Deterministic`）。 -/
theorem det_detT (l : List Tup) : Deterministic ((detT l).map quintOf) := by
  intro r₁ h₁ r₂ h₂ hp hs
  obtain ⟨y₁, hy₁, rfl⟩ := List.mem_map.mp h₁
  obtain ⟨y₂, hy₂, rfl⟩ := List.mem_map.mp h₂
  obtain ⟨x₁, hx₁, rfl⟩ := List.mem_map.mp hy₁
  obtain ⟨x₂, hx₂, rfl⟩ := List.mem_map.mp hy₂
  change (relabel l x₁).1 = (relabel l x₂).1 at hp
  change (relabel l x₁).2.1 = (relabel l x₂).2.1 at hs
  rw [relabel_snd, relabel_snd] at hs
  have t₁ := (le_topT hx₁).1
  have t₂ := (le_topT hx₂).1
  by_cases f₁ : firstT l x₁.1 x₁.2.1 = some x₁ <;> by_cases f₂ : firstT l x₂.1 x₂.2.1 = some x₂
  · rw [relabel_of_first f₁, relabel_of_first f₂] at hp ⊢
    rw [hp, hs, f₂] at f₁
    rw [Option.some.inj f₁]
  · rw [relabel_of_first f₁, relabel_fst f₂] at hp; omega
  · rw [relabel_fst f₁, relabel_of_first f₂] at hp; omega
  · rw [relabel_fst f₁, relabel_fst f₂] at hp
    have he : x₁.2.2 = x₂.2.2 := Encodable.encode_injective (by omega)
    have : relabel l x₁ = relabel l x₂ := by
      unfold relabel; rw [if_neg f₁, if_neg f₂]
      have : x₁.2 = x₂.2 := Prod.ext hs he
      rw [this]
    rw [this]

/-- 状態は増えるだけ。 -/
theorem states_detT {l : List Tup} {st : ℕ} (h : st ∈ statesOf (l.map quintOf)) :
    st ∈ states ((detT l).map quintOf) := by
  simp only [statesOf, List.mem_flatMap, List.mem_map, List.mem_cons, List.mem_nil_iff,
    or_false] at h
  obtain ⟨_, ⟨x, hx, rfl⟩, hst⟩ := h
  simp only [states, List.mem_flatMap, List.mem_map, List.mem_cons, List.mem_nil_iff, or_false,
    detT]
  rcases hst with rfl | rfl
  · obtain ⟨y, hy⟩ := firstT_exists hx
    obtain ⟨hyl, h1, h2⟩ := firstT_some hy
    refine ⟨quintOf (relabel l y), ⟨relabel l y, ⟨y, hyl, rfl⟩, rfl⟩, Or.inl ?_⟩
    have : firstT l y.1 y.2.1 = some y := by rw [h1, h2]; exact hy
    rw [relabel_of_first this]; exact h1.symm
  · refine ⟨quintOf (relabel l x), ⟨relabel l x, ⟨x, hx, rfl⟩, rfl⟩, Or.inr ?_⟩
    change x.2.2.2.2 = (relabel l x).2.2.2.2
    rw [relabel_snd]

/-- 記号は同じ。 -/
theorem symbols_detT {l : List Tup} {a : ℕ} (h : a ∈ symsOf (l.map quintOf)) :
    a ∈ symbols ((detT l).map quintOf) := by
  simp only [symsOf, List.mem_flatMap, List.mem_map, List.mem_cons, List.mem_nil_iff,
    or_false] at h
  obtain ⟨_, ⟨x, hx, rfl⟩, ha⟩ := h
  simp only [symbols, List.mem_flatMap, List.mem_map, List.mem_cons, List.mem_nil_iff, or_false,
    detT]
  refine ⟨quintOf (relabel l x), ⟨relabel l x, ⟨x, hx, rfl⟩, rfl⟩, ?_⟩
  change a = (relabel l x).2.1 ∨ a = (relabel l x).2.2.1
  rw [relabel_snd]; exact ha

theorem quintOfNat_eq_quintOf : quintOfNat = quintOf := by
  funext x
  obtain ⟨a, b, c, d, e⟩ := x
  rcases d with _ | _ | d <;> rfl

/-- **Spec の列挙での番号**: 決定化した表の番号を `tm` で引くと決定化した表そのもの。 -/
theorem tm_detT (l : List Tup) : tm (Encodable.encode (detT l)) = (detT l).map quintOf := by
  have h : (Denumerable.ofNat (List Tup) (Encodable.encode (detT l))).map quintOfNat =
      (detT l).map quintOf := by
    rw [Denumerable.ofNat_encode, quintOfNat_eq_quintOf]
  unfold tm
  dsimp only
  rw [h, if_pos (det_detT l)]

/-- 番号の写し: `tmOf n` を決定化した表の、Spec の列挙 `tm` での番号。 -/
def idx (n : ℕ) : ℕ := Encodable.encode (detT (Denumerable.ofNat (List Tup) n))

theorem tm_idx (n : ℕ) :
    tm (idx n) = (detT (Denumerable.ofNat (List Tup) n)).map quintOf := tm_detT _

theorem firstT_primrec : Primrec fun a : List Tup × ℕ × ℕ => firstT a.1 a.2.1 a.2.2 := by
  have y := (Primrec.fst.comp Primrec.snd :
    Primrec fun p : (List Tup × ℕ × ℕ) × Tup × Option Tup => p.2.1)
  have acc := (Primrec.snd.comp Primrec.snd :
    Primrec fun p : (List Tup × ℕ × ℕ) × Tup × Option Tup => p.2.2)
  have q := (Primrec.fst.comp (Primrec.snd.comp Primrec.fst) :
    Primrec fun p : (List Tup × ℕ × ℕ) × Tup × Option Tup => p.1.2.1)
  have s := (Primrec.snd.comp (Primrec.snd.comp Primrec.fst) :
    Primrec fun p : (List Tup × ℕ × ℕ) × Tup × Option Tup => p.1.2.2)
  have hh := Primrec.ite
    (PrimrecPred.and (Primrec.eq.comp (Primrec.fst.comp y) q)
      (Primrec.eq.comp (Primrec.fst.comp (Primrec.snd.comp y)) s))
    (Primrec.option_some.comp y) acc
  exact (Primrec.list_foldr Primrec.fst (Primrec.const none) hh.to₂).of_eq fun a => rfl

theorem topT_primrec : Primrec topT := by
  have y := (Primrec.fst.comp Primrec.snd : Primrec fun p : List Tup × Tup × ℕ => p.2.1)
  have m := (Primrec.snd.comp Primrec.snd : Primrec fun p : List Tup × Tup × ℕ => p.2.2)
  have hh := Primrec.nat_max.comp
    (Primrec.nat_max.comp (Primrec.fst.comp y)
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp y))))) m
  exact (Primrec.list_foldr Primrec.id (Primrec.const 0) hh.to₂).of_eq fun _ => rfl

theorem relabel_primrec : Primrec₂ relabel := by
  have l := (Primrec.fst : Primrec fun p : List Tup × Tup => p.1)
  have x := (Primrec.snd : Primrec fun p : List Tup × Tup => p.2)
  have hf := firstT_primrec.comp (Primrec.pair l
    (Primrec.pair (Primrec.fst.comp x) (Primrec.fst.comp (Primrec.snd.comp x))))
  have hnew := Primrec.pair
    (Primrec.nat_add.comp (Primrec.nat_add.comp (topT_primrec.comp l) (Primrec.const 1))
      (Primrec.encode.comp (Primrec.snd.comp (Primrec.snd.comp x))))
    (Primrec.snd.comp x)
  exact (Primrec.ite (Primrec.eq.comp hf (Primrec.option_some.comp x)) x hnew).of_eq
    fun p => rfl

theorem detT_primrec : Primrec detT :=
  (Primrec.list_map Primrec.id relabel_primrec).of_eq fun _ => rfl

theorem idx_primrec : Primrec idx :=
  (Primrec.encode.comp (detT_primrec.comp (Primrec.ofNat (List Tup)))).of_eq fun _ => rfl

/-! ### ID の同一視と ID(T) -/

/-- 同じ位置に置いた二つの符号が同じ ID を表すことは、文字列側の同一視 `ZSame` と同値。 -/
theorem toID_eq_iff (p : ℤ) (b b' : ZID) : toID p b = toID p b' ↔ ZSame b b' := by
  constructor
  · intro h; exact CodePad.getD_of_toID h
  · rintro ⟨h1, hl, hr⟩
    simp only [toID, h1, hl, hr]

theorem zsame_refl (z : ZID) : ZSame z z := ⟨rfl, fun _ => rfl, fun _ => rfl⟩

/-- 文字列側の ID(T) から Spec の ID(T') へ（状態と記号が `T'` にもあれば）。 -/
theorem isIDOf_of_IDOf {T : List Quint} {T' : List Quint} {α : ZID} (h : IDOf T α)
    (hst : ∀ q ∈ statesOf T, q ∈ states T') (hsym : ∀ a ∈ symsOf T, a ∈ symbols T') :
    IsIDOf T' (toID 0 α) :=
  KToSpec.isIDOf_toID T' 0 α (hst _ h.1) fun a ha => (h.2 a ha).imp_right (hsym a)

/-- Spec の ID(U) から文字列側の ID(U) へ。 -/
theorem IDOf_of_isIDOf {U : List Quint} {x : ZID} (h : IsIDOf U (toID 0 x)) : IDOf U x :=
  ⟨h.2.1, L0.syms_of_isIDOf h⟩

/-! ### (c) Def. 7.1: 両側無限テープの形から文字列の形へ -/

/-- **文字列上の ID の Def. 7.1、強い形**: `IsUTM_Morita` に加えて、
    * `c(n, α) ∈ ID(U)`（Def. 7.1 の `c : ℕ × ID(Tₙ) → ID(U)`）;
    * 復号は文字列としての ID の上の関数: 停止 ID `γ` と `ZSame` な（両端の空白だけが違う）
      **どの** `γ'` についても `d γ'` が `β` と `ZSame` な ID を返す。 -/
def IsUTM_MoritaStrict (U : List Quint) : Prop :=
  ∃ (c : ℕ × ZID → ZID) (d : ZID → Option ZID), Computable c ∧ Computable d ∧
    ∀ n α, IDOf (tmOf n) α →
      IDOf U (c (n, α)) ∧
      (∀ β, ZHaltsAt (tmOf n) α β →
        ∃ γ, ZHaltsAt U (c (n, α)) γ ∧
          ∀ γ', ZSame γ' γ → ∃ β', d γ' = some β' ∧ ZSame β' β) ∧
      (¬ ZHalts (tmOf n) α → ¬ ZHalts U (c (n, α)))

/-- 強い形は `IsUTM_Morita`（legacy の `Morita.lean` の定義の写し）を含意する。 -/
theorem IsUTM_MoritaStrict.morita {U : List Quint} (h : IsUTM_MoritaStrict U) :
    IsUTM_Morita U := by
  obtain ⟨c, d, hc, hd, h⟩ := h
  refine ⟨c, d, hc, hd, fun n α hα => ⟨fun β hβ => ?_, (h n α hα).2.2⟩⟩
  obtain ⟨γ, hγ, hall⟩ := (h n α hα).2.1 β hβ
  exact ⟨γ, hγ, hall γ (zsame_refl γ)⟩

/-- **主定理（(c)）**: 決定的な表 `U` が Spec の意味で（両側無限テープの ID で）万能なら、
    原典の文字列上の ID の意味でも万能（強い形）。 -/
theorem isUTM_MoritaStrict {U : List Quint} (hdet : Deterministic U) (hU : IsUTMStrict U) :
    IsUTM_MoritaStrict U := by
  obtain ⟨c', d', hc', hd', h⟩ := hU
  refine ⟨fun p => c' (idx p.1, p.2), d',
    hc'.comp (Computable.pair (idx_primrec.to_comp.comp Computable.fst) Computable.snd), hd',
    fun n α hα => ?_⟩
  set l := Denumerable.ofNat (List Tup) n with hl
  have hT : tmOf n = l.map quintOf := rfl
  rw [hT] at hα ⊢
  have htop : α.1 ≤ topT l := by
    have := hα.1
    simp only [statesOf, List.mem_flatMap, List.mem_map, List.mem_cons, List.mem_nil_iff,
      or_false] at this
    obtain ⟨_, ⟨x, hx, rfl⟩, h1 | h1⟩ := this
    · rw [h1]; exact (le_topT hx).1
    · rw [h1]; exact (le_topT hx).2
  have hα' : IsIDOf (tm (idx n)) (toID 0 α) := by
    rw [tm_idx]
    exact isIDOf_of_IDOf hα (fun _ => states_detT) (fun _ => symbols_detT)
  obtain ⟨hid, hhalt, hnon⟩ := h (idx n) α hα'
  rw [tm_idx] at hhalt hnon
  refine ⟨IDOf_of_isIDOf hid, fun β hβ => ?_, fun hn hz => ?_⟩
  · rw [← zhaltsAt_detT l htop] at hβ
    obtain ⟨pβ, hβs⟩ := haltsAt_of_zhaltsAt hβ
    obtain ⟨γs, hγs, -, hall⟩ := hhalt _ hβs
    obtain ⟨pγ, z, rfl, hz⟩ := zhaltsAt_of_haltsAt hdet hγs
    refine ⟨z, hz, fun γ' hγ' => ?_⟩
    obtain ⟨b, hb, hbβ⟩ := hall γ' ((toID_eq_iff pγ γ' z).mpr hγ')
    exact ⟨b, hb, (toID_eq_iff pβ b β).mp hbβ⟩
  · refine hnon ?_ ((halts_iff hdet _).mpr hz)
    rw [halts_iff (det_detT l), zhalts_detT l htop]
    exact hn

/-- **系**: 決定的な表 `U` が Spec の意味で万能なら、legacy の文字列上の Def. 7.1 `IsUTM_Morita` を満たす。 -/
theorem isUTM_Morita {U : List Quint} (hdet : Deterministic U) (hU : IsUTMStrict U) :
    IsUTM_Morita U :=
  (isUTM_MoritaStrict hdet hU).morita

end URTM.Univ.StringID
