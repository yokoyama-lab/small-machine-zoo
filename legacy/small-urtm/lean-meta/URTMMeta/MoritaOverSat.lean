/-
  **`IsUTM_MoritaOver` は空虚に偽ではない**（段階 1 から未確認だった点。2026-10-04）。

  `Three.lean` の `IsUTM_MoritaOver tbl Γ`（Morita Def. 7.1 を zipper の上で、c の値の記号を {0} ∪ Γ に
  制限したもの）を満たす表があることを、lean-univ の存在定理（`exists_urtm_10_8` など。結論は
  `Spec.IsUTMStrict U`）からの橋渡しで示す。

  主定理 `IsUTMStrict.moritaOver`: 決定的な表 U が `IsUTMStrict U` を満たすなら
  `IsUTM_MoritaOver U (symbols U)`。

  `IsUTMStrict` の定義は `URTMMeta/Strict.lean`（lean-univ の `LeanUniv/Strict.lean` の写し。違いは
  import の 1 行だけ。`lean-univ/tests/check.sh` が検査する）。lean-univ と lean-meta は同名のパッケージ
  `urtm`（別の実体）に依存するので 1 つの環境に読み込めない。したがって「`IsUTM_MoritaOver` を満たす表が
  存在する」は、この定理と lean-univ の `exists_urtm_10_8`（`Deterministic U ∧ … ∧ IsUTMStrict U`）を
  定義の文面の一致（`Spec.lean` はバイト一致、`Strict.lean` は import 行を除いて一致、`URTM.Basic` は
  ヘッダ注釈を除いて一致）を介して合わせたもので、1 つの kernel の中で閉じた証明ではない。

  2 つの定義の違いと、その埋め方:
  * 列挙: `Spec.tm n` は決定的でない表を空の表にする。`Meta.tmOf n` は決定的でない表も先頭一致の
    意味で動かす。そこで符号化 c は、`tmOf n` を「先頭一致で同じに動く決定的な表」`detify` に計算可能に
    直してから lean-univ の c に渡す。`detify` は先に同じ (状態, 記号) の規則がある規則を、使われない
    新しい状態から出る規則（`dummy`）に置き換える（書く記号と次の状態を残すので、表に現れる状態・記号は
    減らない。したがって `tmOf n` の ID は `detify` の表の ID でもある）。
  * 機械の意味: 仕様は関係（`Step`）、ここは zipper の関数（`zstep`）。決定的な表では一致する
    （`SpecThm.lean` の `qstep_realize`・`step_of_qstep`・`halts_toID_iff` を使う）。
  * 出力: `IsUTMStrict` は停止 ID の**どの**符号でも d が正しいことを要求するので、zipper の停止配置
    そのものを符号として渡せる。
-/
import URTMMeta.SpecThm
import URTMMeta.Strict
import URTMMeta.Three

namespace URTM.Meta.Sat
open URTM URTM.TwoState URTM.Meta URTM.Spec

/-- 数の 5 つ組（列挙の生の形）。 -/
abbrev Raw := ℕ × ℕ × ℕ × ℕ × ℕ

/-- 規則の鍵（状態, 読む記号）。 -/
def key (x : Raw) : ℕ × ℕ := (x.1, x.2.1)

/-- 置き換えの規則: 新しい状態 `F + encode x` から、記号 0 を読んで x と同じものを書き同じ状態へ入る。 -/
def dummy (F : ℕ) (x : Raw) : Raw := (F + Encodable.encode x, 0, x.2.2.1, x.2.2.2.1, x.2.2.2.2)

/-- 表に現れる状態の番号の和（どの状態もこれ以下）。 -/
def bigS (l : List Raw) : ℕ := l.foldr (fun x acc => x.1 + x.2.2.2.2 + acc) 0

/-- 先に同じ鍵の規則がある規則を `dummy` に置き換える（`seen` = それまでに残した鍵）。 -/
def detAux (F : ℕ) : List (ℕ × ℕ) → List Raw → List Raw
  | _, [] => []
  | seen, x :: l => if key x ∈ seen then dummy F x :: detAux F seen l
      else x :: detAux F (key x :: seen) l

/-- `detAux` を左畳み込みで書いたもの（計算可能性の証明に使う）。 -/
def stepF (F : ℕ) (st : List (ℕ × ℕ) × List Raw) (x : Raw) : List (ℕ × ℕ) × List Raw :=
  if @List.idxOf _ instBEqOfDecidableEq (key x) st.1 < st.1.length then (st.1, st.2 ++ [dummy F x])
  else (key x :: st.1, st.2 ++ [x])

/-- **先頭一致で同じに動く決定的な表**。 -/
def detify (l : List Raw) : List Raw := (l.foldl (stepF (bigS l + 1)) ([], [])).2

theorem foldl_stepF (F : ℕ) : ∀ (l : List Raw) (seen : List (ℕ × ℕ)) (out : List Raw),
    (l.foldl (stepF F) (seen, out)).2 = out ++ detAux F seen l
  | [], _, out => by simp [detAux]
  | x :: l, seen, out => by
    rw [List.foldl_cons]
    by_cases h : key x ∈ seen
    · have e : stepF F (seen, out) x = (seen, out ++ [dummy F x]) := by
        have hi : @List.idxOf _ instBEqOfDecidableEq (key x) seen < seen.length :=
          (@List.idxOf_lt_length_iff (ℕ × ℕ) instBEqOfDecidableEq _ seen (key x)).mpr h
        unfold stepF; dsimp only; rw [if_pos hi]
      rw [e, foldl_stepF F l]; simp [detAux, h]
    · have e : stepF F (seen, out) x = (key x :: seen, out ++ [x]) := by
        have hi : ¬ @List.idxOf _ instBEqOfDecidableEq (key x) seen < seen.length :=
          fun h' => h ((@List.idxOf_lt_length_iff (ℕ × ℕ) instBEqOfDecidableEq _ seen (key x)).mp h')
        unfold stepF; dsimp only; rw [if_neg hi]
      rw [e, foldl_stepF F l]; simp [detAux, h]

theorem detify_eq (l : List Raw) : detify l = detAux (bigS l + 1) [] l := by
  unfold detify; rw [foldl_stepF]; simp

theorem le_bigS : ∀ {l : List Raw} {x : Raw}, x ∈ l → x.1 + x.2.2.2.2 ≤ bigS l
  | [], _, h => by simp at h
  | y :: l, x, h => by
    unfold bigS; rw [List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := le_bigS h; unfold bigS at this; omega

/-! ### 列挙の 2 つの読み方は同じ -/

theorem quintOfNat_eq : quintOfNat = quintOf := by
  funext x
  obtain ⟨a, b, c, d, e⟩ := x
  rcases d with _ | _ | d <;> rfl

/-- 生の表を五つ組の表に。 -/
abbrev Q (l : List Raw) : List Quint := l.map quintOf

/-! ### 先頭一致の表引きは変わらない -/

theorem look_detAux (F : ℕ) (q s : ℕ) (hq : q < F) :
    ∀ (l : List Raw) (seen : List (ℕ × ℕ)), (q, s) ∉ seen →
      look (Q (detAux F seen l)) q s = look (Q l) q s
  | [], _, _ => rfl
  | x :: l, seen, hs => by
    unfold detAux
    by_cases h : key x ∈ seen
    · rw [if_pos h]
      simp only [List.map_cons, look]
      have hd : ¬ ((quintOf (dummy F x)).p = q ∧ (quintOf (dummy F x)).s = s) := by
        rintro ⟨h1, -⟩; simp only [quintOf, dummy] at h1; omega
      have hx : ¬ ((quintOf x).p = q ∧ (quintOf x).s = s) := by
        rintro ⟨h1, h2⟩; apply hs; simp only [quintOf] at h1 h2
        have : key x = (q, s) := by simp [key, h1, h2]
        rw [← this]; exact h
      rw [if_neg hd, if_neg hx]
      exact look_detAux F q s hq l seen hs
    · rw [if_neg h]
      simp only [List.map_cons, look]
      by_cases hx : (quintOf x).p = q ∧ (quintOf x).s = s
      · rw [if_pos hx, if_pos hx]
      · rw [if_neg hx, if_neg hx]
        refine look_detAux F q s hq l _ ?_
        intro hm
        rcases List.mem_cons.mp hm with he | he
        · apply hx; simp only [key, Prod.mk.injEq] at he; exact ⟨he.1.symm, he.2.symm⟩
        · exact hs he

/-! ### 決定的 -/

theorem mem_detAux (F : ℕ) : ∀ (l : List Raw) (seen : List (ℕ × ℕ)) (z : Raw), z ∈ detAux F seen l →
    (z ∈ l ∧ key z ∉ seen) ∨ ∃ x ∈ l, z = dummy F x
  | [], _, _, h => by simp [detAux] at h
  | x :: l, seen, z, h => by
    unfold detAux at h
    by_cases hk : key x ∈ seen
    · rw [if_pos hk] at h
      rcases List.mem_cons.mp h with rfl | h
      · exact Or.inr ⟨x, List.mem_cons_self .., rfl⟩
      · rcases mem_detAux F l seen z h with ⟨h1, h2⟩ | ⟨y, hy, rfl⟩
        · exact Or.inl ⟨List.mem_cons_of_mem _ h1, h2⟩
        · exact Or.inr ⟨y, List.mem_cons_of_mem _ hy, rfl⟩
    · rw [if_neg hk] at h
      rcases List.mem_cons.mp h with rfl | h
      · exact Or.inl ⟨List.mem_cons_self .., hk⟩
      · rcases mem_detAux F l _ z h with ⟨h1, h2⟩ | ⟨y, hy, rfl⟩
        · exact Or.inl ⟨List.mem_cons_of_mem _ h1, fun h3 => h2 (List.mem_cons_of_mem _ h3)⟩
        · exact Or.inr ⟨y, List.mem_cons_of_mem _ hy, rfl⟩

/-- 鍵が同じなら同じ規則。 -/
def KeyDet (a b : Raw) : Prop := a.1 = b.1 → a.2.1 = b.2.1 → a = b

instance : Std.Symm KeyDet := ⟨fun _ _ h h1 h2 => (h h1.symm h2.symm).symm⟩

theorem pairwise_detAux (F : ℕ) : ∀ (l : List Raw) (seen : List (ℕ × ℕ)), (∀ x ∈ l, x.1 < F) →
    (detAux F seen l).Pairwise KeyDet
  | [], _, _ => by simp [detAux]
  | x :: l, seen, hl => by
    have hl' : ∀ y ∈ l, y.1 < F := fun y hy => hl y (List.mem_cons_of_mem _ hy)
    have hx : x.1 < F := hl x (List.mem_cons_self ..)
    unfold detAux
    by_cases hk : key x ∈ seen
    · rw [if_pos hk]
      refine List.Pairwise.cons (fun z hz => ?_) (pairwise_detAux F l seen hl')
      intro h1 _
      rcases mem_detAux F l seen z hz with ⟨hz1, -⟩ | ⟨y, -, rfl⟩
      · have := hl' z hz1; simp only [dummy] at h1; omega
      · simp only [dummy] at h1
        have : x = y := Encodable.encode_injective (by omega)
        rw [this]
    · rw [if_neg hk]
      refine List.Pairwise.cons (fun z hz => ?_) (pairwise_detAux F l _ hl')
      intro h1 h2
      rcases mem_detAux F l _ z hz with ⟨-, hz2⟩ | ⟨y, -, rfl⟩
      · exact absurd (List.mem_cons.mpr (Or.inl (by simp [key, h1, h2]))) hz2
      · simp only [dummy] at h1; omega

theorem det_Q_detify (l : List Raw) : Spec.Deterministic (Q (detify l)) := by
  have hp := pairwise_detAux (bigS l + 1) l [] fun x hx => by have := le_bigS hx; omega
  rw [← detify_eq] at hp
  intro r₁ h₁ r₂ h₂ hp' hs'
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp h₁
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp h₂
  by_cases hab : a = b
  · rw [hab]
  · exact congrArg quintOf (hp.forall ha hb hab hp' hs')

/-! ### 状態と記号は減らない -/

theorem cover_detAux (F : ℕ) : ∀ (l : List Raw) (seen : List (ℕ × ℕ)) (x : Raw), x ∈ l →
    x ∈ detAux F seen l ∨ (dummy F x ∈ detAux F seen l ∧
      (key x ∈ seen ∨ ∃ y ∈ detAux F seen l, key y = key x))
  | [], _, _, h => by simp at h
  | z :: l, seen, x, h => by
    unfold detAux
    by_cases hk : key z ∈ seen
    · rw [if_pos hk]
      rcases List.mem_cons.mp h with rfl | h
      · exact Or.inr ⟨List.mem_cons_self .., Or.inl hk⟩
      · rcases cover_detAux F l seen x h with h1 | ⟨h1, h2 | ⟨y, hy, hy'⟩⟩
        · exact Or.inl (List.mem_cons_of_mem _ h1)
        · exact Or.inr ⟨List.mem_cons_of_mem _ h1, Or.inl h2⟩
        · exact Or.inr ⟨List.mem_cons_of_mem _ h1, Or.inr ⟨y, List.mem_cons_of_mem _ hy, hy'⟩⟩
    · rw [if_neg hk]
      rcases List.mem_cons.mp h with rfl | h
      · exact Or.inl (List.mem_cons_self ..)
      · rcases cover_detAux F l _ x h with h1 | ⟨h1, h2 | ⟨y, hy, hy'⟩⟩
        · exact Or.inl (List.mem_cons_of_mem _ h1)
        · rcases List.mem_cons.mp h2 with h2 | h2
          · exact Or.inr ⟨List.mem_cons_of_mem _ h1, Or.inr ⟨z, List.mem_cons_self .., h2.symm⟩⟩
          · exact Or.inr ⟨List.mem_cons_of_mem _ h1, Or.inl h2⟩
        · exact Or.inr ⟨List.mem_cons_of_mem _ h1, Or.inr ⟨y, List.mem_cons_of_mem _ hy, hy'⟩⟩

theorem cover_detify (l : List Raw) (x : Raw) (hx : x ∈ l) :
    x ∈ detify l ∨ (dummy (bigS l + 1) x ∈ detify l ∧ ∃ y ∈ detify l, key y = key x) := by
  rw [detify_eq]
  rcases cover_detAux _ l [] x hx with h | ⟨h1, h2 | h2⟩
  · exact Or.inl h
  · simp at h2
  · exact Or.inr ⟨h1, h2⟩

theorem mem_statesOf {l : List Raw} {x : Raw} (hx : x ∈ l) {v : ℕ}
    (hv : v = x.1 ∨ v = x.2.2.2.2) : v ∈ statesOf (Q l) :=
  List.mem_flatMap.mpr ⟨quintOf x, List.mem_map_of_mem hx, by rcases hv with rfl | rfl <;> simp [quintOf]⟩

theorem mem_symsOf {l : List Raw} {x : Raw} (hx : x ∈ l) {v : ℕ}
    (hv : v = x.2.1 ∨ v = x.2.2.1) : v ∈ symsOf (Q l) :=
  List.mem_flatMap.mpr ⟨quintOf x, List.mem_map_of_mem hx, by rcases hv with rfl | rfl <;> simp [quintOf]⟩

theorem statesOf_detify (l : List Raw) : ∀ v ∈ statesOf (Q l), v ∈ statesOf (Q (detify l)) := by
  intro v hv
  obtain ⟨r, hr, hv⟩ := List.mem_flatMap.mp hv
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
  have hv' : v = x.1 ∨ v = x.2.2.2.2 := by simpa [quintOf] using hv
  rcases cover_detify l x hx with h | ⟨h1, y, hy, hk⟩
  · exact mem_statesOf h hv'
  · simp only [key, Prod.mk.injEq] at hk
    rcases hv' with rfl | rfl
    · exact mem_statesOf hy (Or.inl hk.1.symm)
    · exact mem_statesOf h1 (Or.inr rfl)

theorem symsOf_detify (l : List Raw) : ∀ v ∈ symsOf (Q l), v ∈ symsOf (Q (detify l)) := by
  intro v hv
  obtain ⟨r, hr, hv⟩ := List.mem_flatMap.mp hv
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
  have hv' : v = x.2.1 ∨ v = x.2.2.1 := by simpa [quintOf] using hv
  rcases cover_detify l x hx with h | ⟨h1, y, hy, hk⟩
  · exact mem_symsOf h hv'
  · simp only [key, Prod.mk.injEq] at hk
    rcases hv' with rfl | rfl
    · exact mem_symsOf hy (Or.inl hk.2.symm)
    · exact mem_symsOf h1 (Or.inr rfl)

theorem IDOf_detify {l : List Raw} {z : ZID} (h : IDOf (Q l) z) : IDOf (Q (detify l)) z :=
  ⟨statesOf_detify l _ h.1, fun a ha => (h.2 a ha).imp id (symsOf_detify l a)⟩

/-! ### 実行は変わらない（状態が `bigS l + 1` 未満の配置から） -/

theorem look_lt (F : ℕ) : ∀ (l : List Raw), (∀ x ∈ l, x.2.2.2.2 < F) →
    ∀ q s o, look (Q l) q s = some o → o.2.2 < F
  | [], _, _, _, _, h => by simp [look] at h
  | x :: l, hl, q, s, o, h => by
    simp only [List.map_cons, look] at h
    split_ifs at h
    · cases h; simp only [rhs, quintOf]; exact hl x (List.mem_cons_self ..)
    · exact look_lt F l (fun y hy => hl y (List.mem_cons_of_mem _ hy)) q s o h

theorem mv_fst (o : ℕ × ℕ × ℕ) (z : ZID) : (mv o z).1 = o.2.2 := by
  unfold mv; split_ifs <;> rfl

section run
variable (l : List Raw)

theorem zstep_detify (z : ZID) (hz : z.1 < bigS l + 1) : zstep (Q (detify l)) z = zstep (Q l) z := by
  unfold zstep; rw [detify_eq, look_detAux _ _ _ hz l [] (by simp)]

theorem zstep_lt {z z' : ZID} (h : zstep (Q l) z = some z') : z'.1 < bigS l + 1 := by
  unfold zstep at h
  cases ho : look (Q l) z.1 (z.2.2.headD 0) with
  | none => rw [ho] at h; cases h
  | some o =>
    rw [ho] at h; cases h
    rw [mv_fst]
    exact look_lt _ l (fun x hx => by have := le_bigS hx; omega) _ _ o ho

theorem zrun_detify : ∀ (k : ℕ) (z : ZID), z.1 < bigS l + 1 →
    zrun (Q (detify l)) k z = zrun (Q l) k z
  | 0, _, _ => rfl
  | k + 1, z, hz => by
    have hD := zstep_detify l z hz
    cases h : zstep (Q l) z with
    | none => simp [zrun, hD, h]
    | some z' => simp [zrun, hD, h, zrun_detify k z' (zstep_lt l h)]

theorem zrun_lt : ∀ (k : ℕ) (z z' : ZID), z.1 < bigS l + 1 → zrun (Q l) k z = some z' →
    z'.1 < bigS l + 1
  | 0, z, z', hz, h => by simp [zrun] at h; rw [← h]; exact hz
  | k + 1, z, z', hz, h => by
    cases hs : zstep (Q l) z with
    | none => simp [zrun, hs] at h
    | some z₁ =>
      simp only [zrun, hs] at h
      exact zrun_lt k z₁ z' (zstep_lt l hs) h

theorem ZHaltsAt_detify {z β : ZID} (hz : z.1 < bigS l + 1) (h : ZHaltsAt (Q l) z β) :
    ZHaltsAt (Q (detify l)) z β := by
  obtain ⟨n, h1, h2⟩ := h
  refine ⟨n, by rw [zrun_detify l n z hz]; exact h1, ?_⟩
  rw [zstep_detify l β (zrun_lt l n z β hz h1)]; exact h2

theorem ZHalts_detify {z : ZID} (hz : z.1 < bigS l + 1) :
    ZHalts (Q (detify l)) z ↔ ZHalts (Q l) z := by
  unfold ZHalts; exact exists_congr fun n => by rw [zrun_detify l n z hz]

end run

theorem lt_of_statesOf {l : List Raw} {v : ℕ} (h : v ∈ statesOf (Q l)) : v < bigS l + 1 := by
  obtain ⟨r, hr, hv⟩ := List.mem_flatMap.mp h
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
  have := le_bigS hx
  have hv' : v = x.1 ∨ v = x.2.2.2.2 := by simpa [quintOf] using hv
  omega

/-! ### 列挙の番号の付け替え -/

/-- `tmOf n` を直した表の、仕様の列挙 `tm` での番号。 -/
def reidx (n : ℕ) : ℕ := Encodable.encode (detify (Denumerable.ofNat (List Raw) n))

theorem tm_reidx (n : ℕ) : tm (reidx n) = Q (detify (Denumerable.ofNat (List Raw) n)) := by
  unfold tm reidx
  rw [Denumerable.ofNat_encode, quintOfNat_eq]
  dsimp only
  rw [if_pos (det_Q_detify _)]

theorem tmOf_eq (n : ℕ) : tmOf n = Q (Denumerable.ofNat (List Raw) n) := rfl

/-! ### 計算可能性 -/

theorem bigS_primrec : Primrec bigS := by
  have hh : Primrec₂ fun (_ : List Raw) (p : Raw × ℕ) => p.1.1 + p.1.2.2.2.2 + p.2 :=
    (Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
        (Primrec.fst.comp Primrec.snd))))))
      (Primrec.snd.comp Primrec.snd)).to₂
  exact (Primrec.list_foldr Primrec.id (Primrec.const 0) hh).of_eq fun l => rfl

theorem key_primrec : Primrec key :=
  Primrec.pair Primrec.fst (Primrec.fst.comp Primrec.snd)

theorem dummy_primrec : Primrec₂ dummy := by
  have x := (Primrec.snd : Primrec fun p : ℕ × Raw => p.2)
  refine (Primrec.pair (Primrec.nat_add.comp Primrec.fst (Primrec.encode.comp x))
    (Primrec.pair (Primrec.const 0) (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp x)))
      (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp x))))
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp x)))))))).to₂.of_eq
    fun F x => rfl

theorem detify_primrec : Primrec detify := by
  -- 入力 q = (l, (st, x))
  let A := List Raw × ((List (ℕ × ℕ) × List Raw) × Raw)
  have hl : Primrec fun q : A => q.1 := Primrec.fst
  have hseen : Primrec fun q : A => q.2.1.1 := Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
  have hout : Primrec fun q : A => q.2.1.2 := Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
  have hx : Primrec fun q : A => q.2.2 := Primrec.snd.comp Primrec.snd
  have hk : Primrec fun q : A => key q.2.2 := key_primrec.comp hx
  have hF : Primrec fun q : A => bigS q.1 + 1 := Primrec.succ.comp (bigS_primrec.comp hl)
  have hc : PrimrecPred fun q : A => @List.idxOf _ instBEqOfDecidableEq (key q.2.2) q.2.1.1 < q.2.1.1.length :=
    Primrec.nat_lt.comp (Primrec.list_idxOf.comp hk hseen) (Primrec.list_length.comp hseen)
  have h1 : Primrec fun q : A => (q.2.1.1, q.2.1.2 ++ [dummy (bigS q.1 + 1) q.2.2]) :=
    Primrec.pair hseen (Primrec.list_concat.comp hout (dummy_primrec.comp hF hx))
  have h2 : Primrec fun q : A => (key q.2.2 :: q.2.1.1, q.2.1.2 ++ [q.2.2]) :=
    Primrec.pair (Primrec.list_cons.comp hk hseen) (Primrec.list_concat.comp hout hx)
  have hh : Primrec₂ fun (l : List Raw) (p : (List (ℕ × ℕ) × List Raw) × Raw) =>
      stepF (bigS l + 1) p.1 p.2 :=
    (Primrec.ite hc h1 h2).to₂.of_eq fun l p => by unfold stepF; rfl
  exact (Primrec.snd.comp (Primrec.list_foldl Primrec.id (Primrec.const ([], [])) hh)).of_eq
    fun l => rfl

theorem reidx_primrec : Primrec reidx :=
  Primrec.encode.comp (detify_primrec.comp (Primrec.ofNat _))

/-! ### 仕様の実行と zipper の実行 -/

theorem toID_step {T : List Quint} {z z' : ZID} (p : ℤ) (h : zstep T z = some z') :
    ∃ p', Step T (toID p z) (toID p' z') := by
  obtain ⟨p', hp'⟩ := (qstep_realize T p z).2 z' h
  exact ⟨p', step_of_qstep T (toID p z) (realize p' z') hp'⟩

theorem toID_halted {T : List Quint} {z : ZID} (p : ℤ) (h : zstep T z = none) :
    Halted T (toID p z) :=
  (qstep_none_iff T (toID p z)).mp ((qstep_realize T p z).1 h)

theorem zrun_reach (T : List Quint) : ∀ (n : ℕ) (p : ℤ) (z z' : ZID), zrun T n z = some z' →
    ∃ p', Relation.ReflTransGen (Step T) (toID p z) (toID p' z')
  | 0, p, z, z', h => by simp [zrun] at h; subst h; exact ⟨p, Relation.ReflTransGen.refl⟩
  | n + 1, p, z, z', h => by
    cases hs : zstep T z with
    | none => simp [zrun, hs] at h
    | some z₁ =>
      simp only [zrun, hs] at h
      obtain ⟨p₁, hp₁⟩ := toID_step p hs
      obtain ⟨p', hp'⟩ := zrun_reach T n p₁ z₁ z' h
      exact ⟨p', Relation.ReflTransGen.head hp₁ hp'⟩

theorem haltsAt_of_ZHaltsAt {T : List Quint} {z β : ZID} (h : ZHaltsAt T z β) :
    ∃ p, HaltsAt T (toID 0 z) (toID p β) := by
  obtain ⟨n, h1, h2⟩ := h
  obtain ⟨p, hp⟩ := zrun_reach T n 0 z β h1
  exact ⟨p, hp, toID_halted p h2⟩

theorem step_det {T : List Quint} (hdet : Spec.Deterministic T) {c a b : ID}
    (ha : Step T c a) (hb : Step T c b) : a = b := by
  obtain ⟨r₁, h₁, ⟨p₁, s₁⟩, rfl⟩ := ha
  obtain ⟨r₂, h₂, ⟨p₂, s₂⟩, rfl⟩ := hb
  rw [hdet r₁ h₁ r₂ h₂ (p₁.trans p₂.symm) (s₁.trans s₂.symm)]

theorem not_step_of_halted {T : List Quint} {c c' : ID} (hh : Halted T c) (hs : Step T c c') : False := by
  obtain ⟨r, hr, ha, -⟩ := hs
  exact hh r hr ha

/-- 決定的な表では停止 ID は 1 つ。 -/
theorem haltsAt_unique {T : List Quint} (hdet : Spec.Deterministic T) {c c₁ c₂ : ID}
    (h₁ : HaltsAt T c c₁) (h₂ : HaltsAt T c c₂) : c₁ = c₂ := by
  obtain ⟨r₁, hh₁⟩ := h₁
  obtain ⟨r₂, hh₂⟩ := h₂
  induction r₁ using Relation.ReflTransGen.head_induction_on generalizing c₂ with
  | refl =>
    rcases Relation.ReflTransGen.cases_head r₂ with rfl | ⟨c', hs, -⟩
    · rfl
    · exact (not_step_of_halted hh₁ hs).elim
  | head hs _ ih =>
    rcases Relation.ReflTransGen.cases_head r₂ with rfl | ⟨c', hs', r'⟩
    · exact (not_step_of_halted hh₂ hs).elim
    · rw [step_det hdet hs hs'] at ih
      exact ih r' hh₂

theorem ZSame_of_toID {p : ℤ} {a b : ZID} (h : toID p a = toID p b) : ZSame a b := by
  have hst := congrArg ID.st h
  have ht := congrArg ID.tape h
  refine ⟨hst, fun i => ?_, fun i => ?_⟩
  · have := congrFun ht (p - 1 - i)
    simp only [toID] at this
    rw [if_neg (by omega), if_neg (by omega)] at this
    have e : (p - 1 - (p - 1 - (i : ℤ))).toNat = i := by omega
    rwa [e] at this
  · have := congrFun ht (p + i)
    simp only [toID] at this
    rw [if_pos (by omega), if_pos (by omega)] at this
    have e : (p + (i : ℤ) - p).toNat = i := by omega
    rwa [e] at this

/-- `toID 0 z` の記号が `symbols U` に入るなら、z の列の記号も入る。 -/
theorem syms_of_isIDOf {U : List Quint} {z : ZID} (h : IsIDOf U (toID 0 z)) :
    ∀ a ∈ z.2.1 ++ z.2.2, a = 0 ∨ a ∈ symbols U := by
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
    have := h.2.2 (-1 - i)
    simp only [toID] at this
    rw [if_neg (by omega)] at this
    have e : (0 - 1 - (-1 - (i : ℤ))).toNat = i := by omega
    rw [e, List.getD_eq_getElem _ _ hi] at this
    exact this
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
    have := h.2.2 i
    simp only [toID] at this
    rw [if_pos (by omega)] at this
    have e : ((i : ℤ) - 0).toNat = i := by omega
    rw [e, List.getD_eq_getElem _ _ hi] at this
    exact this

/-! ## 主定理 -/

/-- **`IsUTMStrict`（lean-univ の存在定理の結論）を満たす決定的な表は `IsUTM_MoritaOver` を満たす**
    （記号集合 Γ = U に現れる記号）。 -/
theorem IsUTMStrict.moritaOver {U : List Quint} (hdet : Spec.Deterministic U) (hU : IsUTMStrict U) :
    IsUTM_MoritaOver U (symbols U) := by
  obtain ⟨c, d, hc, hd, h⟩ := hU
  refine ⟨fun p => c (reidx p.1, p.2), d,
    hc.comp (Computable.pair (reidx_primrec.to_comp.comp Computable.fst) Computable.snd), hd, ?_⟩
  intro n α hα
  -- 直した表 D と、その仕様の番号
  set l := Denumerable.ofNat (List Raw) n with hl
  have hT : tmOf n = Q l := tmOf_eq n
  rw [hT] at hα
  have hDet := det_Q_detify l
  have hz : α.1 < bigS l + 1 := lt_of_statesOf hα.1
  have hα' : IsIDOf (tm (reidx n)) (toID 0 α) := by
    rw [tm_reidx]; exact isIDOf_of_IDOf (IDOf_detify hα) 0
  obtain ⟨hcU, hhalt, hnon⟩ := h (reidx n) α hα'
  rw [tm_reidx] at hhalt hnon
  refine ⟨syms_of_isIDOf hcU, fun β hβ => ?_, fun hn hU' => ?_⟩
  · -- 止まる場合
    rw [hT] at hβ
    obtain ⟨p, hp⟩ := haltsAt_of_ZHaltsAt (ZHaltsAt_detify l hz hβ)
    obtain ⟨γs, hγs, -, hall⟩ := hhalt _ hp
    -- U の zipper の停止配置
    have hUh : ZHalts U (c (reidx n, α)) := (halts_toID_iff hdet 0 _).mp ⟨γs, hγs⟩
    obtain ⟨γ, hγ⟩ := hUh.exists_at
    obtain ⟨p', hp'⟩ := haltsAt_of_ZHaltsAt hγ
    have e : toID p' γ = γs := haltsAt_unique hdet hp' hγs
    obtain ⟨b, hb, hbβ⟩ := hall γ (by rw [← e]; rfl)
    exact ⟨γ, hγ, b, hb, ZSame_of_toID hbβ⟩
  · -- 止まらない場合
    rw [hT] at hn
    apply hnon
    · rw [halts_toID_iff hDet 0 α, ZHalts_detify l hz]; exact hn
    · exact (halts_toID_iff hdet 0 _).mpr hU'

/-- **系**: lean-univ の存在定理の形の仮定から、`IsUTM_MoritaOver` を満たす 10 状態 8 記号の
    決定的・可逆な表が存在する（仮定は lean-univ の `URTM.Univ.Final10_8.exists_urtm_10_8` の文そのもの）。 -/
theorem exists_moritaOver_of_strict {m k : ℕ}
    (h : ∃ U : List Quint, Spec.Deterministic U ∧ Reversible U ∧ NStates U = m ∧ NSyms U = k ∧
      IsUTMStrict U) :
    ∃ U : List Quint, Spec.Deterministic U ∧ Reversible U ∧ NStates U = m ∧ NSyms U = k ∧
      IsUTM_MoritaOver U (symbols U) :=
  let ⟨U, h1, h2, h3, h4, h5⟩ := h
  ⟨U, h1, h2, h3, h4, IsUTMStrict.moritaOver h1 h5⟩

end URTM.Meta.Sat
