/-
  記号準同型（記号併合）による模倣の一般定理。キュー S1 の Lean 側の土台。

  主張の形:
    元の機械 tbl と記号写像 h について、有限個の Bool 検査
    （coherent / symBoundB / coverB / domB。すべて `native_decide` で落とせる）が
    通れば、**任意の配置 c**（記号が nsym 未満のもの）について

      haltsIn (dedupT (mapTable h tbl)) (h blank) n (mapConf h c) = haltsIn tbl blank n c

    すなわち h で書き換えた機械は、元の機械の任意の実行をステップ数まで込みで
    再現する。とくに「任意の CTSH の初期配置」は h を通して構成できる
    （mapConf h ∘ 元の符号化）。これがキュー S1 の中核。

  設計メモ（2026-08-16 改稿）:
  * 08-15 版は盲目実装で `lake build` が赤（Quotient.olean が生成されなかった）。
    ログが読めない環境だったので、机上で危うい箇所を潰した:
    - core の補題名に賭ける箇所（`List.find?_cons_of_pos` の引数の明示性、
      `Array.set!` の展開形、`Option.map_some'` の名前）は自前の補題か
      `first | … | …` の代替並列で吸収する。
    - `show … match …` で `step`/`haltsIn` の内部 matcher と defeq を取る箇所を
      やめ、`step_of_find?_none/some`・`haltsIn_succ_none/some` の等式補題に置換。
    - `OptRel`（Prop 値の match）をやめ、1 ステップ模倣を素朴な `∨`/`∃` で述べる。
    - `dedupT` は整礎再帰をやめ構造再帰 `x :: dropEq x (dedupT xs)`（同じ
      先頭優先の重複除去）。
  * テープの同一視は配列の同一性ではなく `readAt` の外延（TapeRel）。
    これで writeAt の配列パディングの詳細が少数の補題に閉じる。
  * dedupT: 併合後の表は同一規則が重複する（同じキーに潰れた規則は
    coherent により**同一の五つ組**になる）。重複除去は find? を変えない
    （find?_dedupT）ので、重複除去後の表でも同じ模倣が成り立つ。
-/
import URTM.Basic

namespace URTM

/-! ## 記号写像と表の書き換え -/

/-- 五つ組の記号成分だけを h で書き換える（状態・方向は保つ）。 -/
def mapQuint (h : Nat → Nat) (r : Quint) : Quint :=
  ⟨r.p, h r.s, h r.t, r.d, r.q⟩

/-- 表全体の書き換え。重複はここでは除去しない（`dedupT` を参照）。 -/
def mapTable (h : Nat → Nat) (tbl : List Quint) : List Quint :=
  tbl.map (mapQuint h)

/-- 配置の書き換え。 -/
def mapConf (h : Nat → Nat) (c : Conf) : Conf :=
  ⟨c.st, c.pos, c.tape.map h⟩

/-- 配列で与えた記号写像（範囲外は 0）。インスタンス側（M3Q 等）は h として
    `hOf hArr` を渡す。08-18: `hf s := hArr.getD s 0` をインスタンス側で定義すると
    native_decide の評価で hf がインタプリタ経由の閉包になり、coherent の
    7×10⁸ 対の評価が律速した。この定義は本モジュール側にあるので、
    `precompileModules` で lib URTM をネイティブ化すれば h の呼出も native になる。 -/
def hOf (A : Array Nat) (s : Nat) : Nat := A.getD s 0

/-! ## Bool 検査（native_decide で落とす側） -/

/-- 条件(1)(2)の well-definedness:
    同じ状態・同じ h-クラスを読む 2 規則は、h-クラスの書込・方向・次状態が一致する。 -/
def coherentPair (h : Nat → Nat) (a b : Quint) : Bool :=
  decide (a.p = b.p → h a.s = h b.s → (h a.t = h b.t ∧ a.d = b.d ∧ a.q = b.q))

def coherent (h : Nat → Nat) (tbl : List Quint) : Bool :=
  allPairs (fun a b => coherentPair h a b && coherentPair h b a) tbl

/-- 表の記号（読み・書き）がすべて nsym 未満。 -/
def symBoundB (nsym : Nat) (tbl : List Quint) : Bool :=
  tbl.all fun r => decide (r.s < nsym ∧ r.t < nsym)

/-- 表に現れる現状態がすべて sl に載っている。 -/
def coverB (sl : List Nat) (tbl : List Quint) : Bool :=
  tbl.all fun r => decide (r.p ∈ sl)

/-- 定義域の閉性: 各状態 p と各記号 s について、(p,s) に規則があることと
    (p, rep (h s))（s のクラスの代表）に規則があることが一致する。
    これで「h s = h s' なら定義域が一致」が出る（両者とも代表と比較すればよい）。 -/
def domB (h rep : Nat → Nat) (sl : List Nat) (nsym : Nat) (tbl : List Quint) : Bool :=
  sl.all fun p => (List.range nsym).all fun s =>
    decide ((find? tbl p s).isSome = (find? tbl p (rep (h s))).isSome)

/-! ## 検査の健全性 -/

/-- `Bool.and_eq_true` が Eq か Iff かに依存しない自前版。 -/
theorem and_true_split {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> first | exact ⟨rfl, rfl⟩ | cases h | simp at h

/-- `List.all_eq_true` の向きに依存しない自前版。 -/
theorem all_true_mem {α : Type} {p : α → Bool} :
    ∀ {l : List α}, l.all p = true → ∀ {a : α}, a ∈ l → p a = true := by
  intro l
  induction l with
  | nil =>
    intro _ a ha
    first | cases ha | simp at ha
  | cons x xs ih =>
    intro H a ha
    have H0 : (p x && xs.all p) = true := by
      first | exact H | (simpa [List.all_cons] using H) | (simpa using H)
    obtain ⟨h1, h2⟩ := and_true_split H0
    rcases List.mem_cons.mp ha with rfl | ha'
    · exact h1
    · exact ih h2 ha'

theorem allPairs_sound {f : Quint → Quint → Bool} :
    ∀ {l : List Quint}, allPairs f l = true →
      ∀ {a b : Quint}, a ∈ l → b ∈ l → a = b ∨ f a b = true ∨ f b a = true := by
  intro l
  induction l with
  | nil =>
    intro _ a b ha _
    first | cases ha | simp at ha
  | cons x xs ih =>
    intro hall a b ha hb
    have hall0 : (xs.all (f x) && allPairs f xs) = true := hall
    have hall' : (xs.all (f x)) = true ∧ allPairs f xs = true := and_true_split hall0
    rcases List.mem_cons.mp ha with rfl | ha' <;>
      rcases List.mem_cons.mp hb with rfl | hb'
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ((all_true_mem hall'.1) hb'))
    · exact Or.inr (Or.inr ((all_true_mem hall'.1) ha'))
    · exact ih hall'.2 ha' hb'

/-- coherent から取り出す実用形: 表の任意の 2 規則（同一でもよい）について。 -/
theorem coherent_sound {h : Nat → Nat} {tbl : List Quint}
    (H : coherent h tbl = true) {a b : Quint} (ha : a ∈ tbl) (hb : b ∈ tbl)
    (hp : a.p = b.p) (hs : h a.s = h b.s) :
    h a.t = h b.t ∧ a.d = b.d ∧ a.q = b.q := by
  rcases allPairs_sound H ha hb with rfl | hf | hf
  · exact ⟨rfl, rfl, rfl⟩
  · have hf2 : (coherentPair h a b && coherentPair h b a) = true := hf
    have hab := (and_true_split hf2).1
    unfold coherentPair at hab
    exact of_decide_eq_true hab hp hs
  · have hf2 : (coherentPair h b a && coherentPair h a b) = true := hf
    have hab := (and_true_split hf2).2
    unfold coherentPair at hab
    exact of_decide_eq_true hab hp hs

theorem symBoundB_sound {nsym : Nat} {tbl : List Quint}
    (H : symBoundB nsym tbl = true) {r : Quint} (hr : r ∈ tbl) :
    r.s < nsym ∧ r.t < nsym := by
  have h1 : decide (r.s < nsym ∧ r.t < nsym) = true := (all_true_mem H) hr
  exact of_decide_eq_true h1

theorem coverB_sound {sl : List Nat} {tbl : List Quint}
    (H : coverB sl tbl = true) {r : Quint} (hr : r ∈ tbl) : r.p ∈ sl := by
  have h1 : decide (r.p ∈ sl) = true := (all_true_mem H) hr
  exact of_decide_eq_true h1

theorem domB_sound {h rep : Nat → Nat} {sl : List Nat} {nsym : Nat} {tbl : List Quint}
    (H : domB h rep sl nsym tbl = true) {p s : Nat} (hp : p ∈ sl) (hs : s < nsym) :
    (find? tbl p s).isSome = (find? tbl p (rep (h s))).isSome := by
  have h1 : ((List.range nsym).all fun s =>
      decide ((find? tbl p s).isSome = (find? tbl p (rep (h s))).isSome)) = true :=
    (all_true_mem H) hp
  have h2 : decide ((find? tbl p s).isSome = (find? tbl p (rep (h s))).isSome) = true :=
    (all_true_mem h1) (List.mem_range.mpr hs)
  exact of_decide_eq_true h2

/-! ## List.find? の小補題（core の補題名・引数の明示性に依存しない自前版） -/

theorem find?_cons_pos (p : Quint → Bool) (x : Quint) (l : List Quint) (hx : p x = true) :
    List.find? p (x :: l) = some x := by
  -- 08-17: 複数行の代替（`show … \n rw`）は 2 行目の列がずれて parse error になった。
  -- 代替はすべて 1 行に収める。
  first
  | (simp only [List.find?, hx]; done)
  | (rw [List.find?_cons, hx]; done)
  | (simp [List.find?, hx]; done)
  | (simp [hx]; done)
  | (unfold List.find?; rw [hx]; try rfl)

theorem find?_cons_neg (p : Quint → Bool) (x : Quint) (l : List Quint) (hx : p x = false) :
    List.find? p (x :: l) = List.find? p l := by
  first
  | (simp only [List.find?, hx]; done)
  | (rw [List.find?_cons, hx]; done)
  | (simp [List.find?, hx]; done)
  | (simp [hx]; done)
  | (unfold List.find?; rw [hx]; try rfl)

theorem find?_isSome_of_pred {p : Quint → Bool} :
    ∀ {l : List Quint} {a : Quint}, a ∈ l → p a = true → (l.find? p).isSome = true := by
  intro l
  induction l with
  | nil =>
    intro a ha _
    first | cases ha | simp at ha
  | cons x xs ih =>
    intro a ha hp
    cases hx : p x with
    | true =>
      rw [find?_cons_pos p x xs hx]
      all_goals first | rfl | (simp; done)
    | false =>
      rw [find?_cons_neg p x xs hx]
      rcases List.mem_cons.mp ha with rfl | ha'
      · first | (rw [hp] at hx; cases hx) | (simp [hx] at hp) | (simp [hp] at hx)
      · exact ih ha' hp

theorem find?_mapTable (h : Nat → Nat) (tbl : List Quint) (p σ : Nat) :
    find? (mapTable h tbl) p σ
      = (tbl.find? (fun r => r.p == p && h r.s == σ)).map (mapQuint h) := by
  induction tbl with
  | nil => rfl
  | cons x xs ih =>
    show List.find? (fun r => r.p == p && r.s == σ) (mapQuint h x :: mapTable h xs)
        = (List.find? (fun r => r.p == p && h r.s == σ) (x :: xs)).map (mapQuint h)
    cases hx : (x.p == p && h x.s == σ) with
    | true =>
      have hx2 : (fun r : Quint => r.p == p && r.s == σ) (mapQuint h x) = true := hx
      rw [find?_cons_pos (fun r => r.p == p && r.s == σ) (mapQuint h x) (mapTable h xs) hx2,
          find?_cons_pos (fun r => r.p == p && h r.s == σ) x xs hx]
      all_goals first | rfl | (simp; done)
    | false =>
      have hx2 : (fun r : Quint => r.p == p && r.s == σ) (mapQuint h x) = false := hx
      rw [find?_cons_neg (fun r => r.p == p && r.s == σ) (mapQuint h x) (mapTable h xs) hx2,
          find?_cons_neg (fun r => r.p == p && h r.s == σ) x xs hx]
      exact ih

theorem find?_mapTable_eq_none {h : Nat → Nat} {tbl : List Quint} {p σ : Nat}
    (hf : tbl.find? (fun r => r.p == p && h r.s == σ) = none) :
    find? (mapTable h tbl) p σ = none := by
  rw [find?_mapTable, hf]
  all_goals first | rfl | (simp; done)

theorem find?_mapTable_eq_some {h : Nat → Nat} {tbl : List Quint} {p σ : Nat} {r : Quint}
    (hf : tbl.find? (fun r => r.p == p && h r.s == σ) = some r) :
    find? (mapTable h tbl) p σ = some (mapQuint h r) := by
  rw [find?_mapTable, hf]
  all_goals first | rfl | (simp; done)

/-! ## テープの補題（配列の詳細をここに閉じ込める） -/

theorem readAt_push (bl : Nat) (A : Array Nat) (j : Nat) :
    readAt bl (A.push bl) j = readAt bl A j := by
  unfold readAt
  by_cases hj : j < A.size
  · have hj' : j < (A.push bl).size := by rw [Array.size_push]; omega
    rw [dif_pos hj', dif_pos hj]
    first
    | exact Array.getElem_push_lt hj
    | exact Array.getElem_push_lt A bl j hj
    | (simp [Array.getElem_push, hj]; done)
    | (simp [hj]; done)
  · by_cases hj2 : j < (A.push bl).size
    · have hje : j = A.size := by rw [Array.size_push] at hj2; omega
      rw [dif_pos hj2, dif_neg hj]
      subst hje
      first
      | exact Array.getElem_push_eq A bl
      | exact Array.getElem_push_eq
      | (simp [Array.getElem_push]; done)
      | (simp; done)
    · rw [dif_neg hj2, dif_neg hj]

/-- foldl の 1 段展開（`List.range` の補題名に依存しないよう、任意のリストで示す）。 -/
theorem foldpad_cons (bl : Nat) (a : Nat) (l : List Nat) (t : Array Nat) :
    (a :: l).foldl (fun acc _ => acc.push bl) t
      = l.foldl (fun acc _ => acc.push bl) (t.push bl) := by
  first | rfl | (simp only [List.foldl_cons]; done) | (rw [List.foldl_cons]; done)

theorem readAt_foldpad_list (bl : Nat) (j : Nat) :
    ∀ (l : List Nat) (t : Array Nat),
      readAt bl (l.foldl (fun acc _ => acc.push bl) t) j = readAt bl t j := by
  intro l
  induction l with
  | nil => intro t; rfl
  | cons a l ih =>
    intro t
    rw [foldpad_cons, ih, readAt_push]

theorem readAt_foldpad (bl : Nat) (t : Array Nat) (k : Nat) (j : Nat) :
    readAt bl ((List.range k).foldl (fun acc _ => acc.push bl) t) j = readAt bl t j :=
  readAt_foldpad_list bl j (List.range k) t

theorem foldpad_size_list (bl : Nat) :
    ∀ (l : List Nat) (t : Array Nat),
      (l.foldl (fun acc _ => acc.push bl) t).size = t.size + l.length := by
  intro l
  induction l with
  | nil => intro t; rfl
  | cons a l ih =>
    intro t
    rw [foldpad_cons, ih, Array.size_push, List.length_cons]
    all_goals omega

theorem foldpad_size (bl : Nat) (t : Array Nat) (k : Nat) :
    ((List.range k).foldl (fun acc _ => acc.push bl) t).size = t.size + k := by
  first
  | (rw [foldpad_size_list, List.length_range]; done)
  | (rw [foldpad_size_list]; simp; done)
  | (simp [foldpad_size_list]; done)

theorem size_set! (a : Array Nat) (i : Nat) (v : Nat) : (a.set! i v).size = a.size := by
  first
  | (simp [Array.set!]; done)
  | (simp [Array.set!, Array.setIfInBounds]; done)
  | (simp; done)
  | (unfold Array.set! Array.setIfInBounds; split <;> simp)

theorem readAt_set!_self (bl : Nat) (a : Array Nat) (i v : Nat) (h : i < a.size) :
    readAt bl (a.set! i v) i = v := by
  unfold readAt
  have h' : i < (a.set! i v).size := by rw [size_set!]; exact h
  rw [dif_pos h']
  first
  | (simp [Array.set!, Array.setIfInBounds, h]; done)
  | (simp [Array.set!, h]; done)
  | (simp [h]; done)
  | (unfold Array.set! Array.setIfInBounds; rw [dif_pos h]; simp)

theorem readAt_set!_other (bl : Nat) (a : Array Nat) (i v j : Nat) (hj : j ≠ i) :
    readAt bl (a.set! i v) j = readAt bl a j := by
  unfold readAt
  have hij : ¬ (i = j) := fun hh => hj hh.symm
  by_cases hjs : j < a.size
  · have h' : j < (a.set! i v).size := by rw [size_set!]; exact hjs
    rw [dif_pos h', dif_pos hjs]
    -- 08-17 のログ: `set!` を展開すると `(if h : i < a.size then a.set i v h else a)[j]`
    -- になり、その下で `rw [dif_pos hi]` は getElem の証明項に依存して motive が壊れる。
    -- `readAt_set!_self` は `h : i < a.size` を simp に渡すことで通っているので、
    -- ここも i < a.size で場合分けして simp に条件を渡す（rw は使わない）。
    by_cases hi : i < a.size
    · first
      | (simp [Array.set!, Array.setIfInBounds, hi, hij, hj]; done)
      | (simp [Array.set!, Array.setIfInBounds, Array.getElem_set, hi, hij, hj]; done)
      | (simp [Array.set!, Array.setIfInBounds, Array.getElem_set_ne, hi, hij, hj]; done)
      | (simp only [Array.set!, Array.setIfInBounds, dif_pos hi]; simp [Array.getElem_set, hij, hj]; done)
      | (simp only [Array.set!, Array.setIfInBounds]; split <;> simp [Array.getElem_set, hij, hj])
    · first
      | (simp [Array.set!, Array.setIfInBounds, hi]; done)
      | (simp only [Array.set!, Array.setIfInBounds, dif_neg hi]; done)
      | (simp only [Array.set!, Array.setIfInBounds]; split <;> simp_all)
  · have h' : ¬ j < (a.set! i v).size := by rw [size_set!]; exact hjs
    rw [dif_neg h', dif_neg hjs]

theorem writeAt_of_lt (bl : Nat) (t : Array Nat) (i v : Nat) (hi : i < t.size) :
    writeAt bl t i v = t.set! i v := by
  first
  | (simp only [writeAt, if_pos hi]; done)
  | (unfold writeAt; simp only [if_pos hi]; done)
  | (simp [writeAt, hi]; done)

theorem writeAt_of_ge (bl : Nat) (t : Array Nat) (i v : Nat) (hi : ¬ i < t.size) :
    writeAt bl t i v
      = ((List.range (i + 1 - t.size)).foldl (fun acc _ => acc.push bl) t).set! i v := by
  first
  | (simp only [writeAt, if_neg hi]; done)
  | (unfold writeAt; simp only [if_neg hi]; done)
  | (simp [writeAt, hi]; done)

theorem readAt_writeAt_self (bl : Nat) (t : Array Nat) (i v : Nat) :
    readAt bl (writeAt bl t i v) i = v := by
  by_cases hi : i < t.size
  · rw [writeAt_of_lt bl t i v hi]
    exact readAt_set!_self bl t i v hi
  · rw [writeAt_of_ge bl t i v hi]
    apply readAt_set!_self
    rw [foldpad_size]
    omega

theorem readAt_writeAt_other (bl : Nat) (t : Array Nat) (i v j : Nat) (hj : j ≠ i) :
    readAt bl (writeAt bl t i v) j = readAt bl t j := by
  by_cases hi : i < t.size
  · rw [writeAt_of_lt bl t i v hi]
    exact readAt_set!_other bl t i v j hj
  · rw [writeAt_of_ge bl t i v hi]
    rw [readAt_set!_other bl _ i v j hj]
    exact readAt_foldpad bl t (i + 1 - t.size) j

/-! ## テープ・配置の関係 -/

/-- 「h で書き換えたテープ」の外延的表現。読み出しがすべて h を通る。 -/
def TapeRel (h : Nat → Nat) (bl : Nat) (t t' : Array Nat) : Prop :=
  ∀ i, readAt (h bl) t' i = h (readAt bl t i)

/-- テープの記号がすべて nsym 未満（空白も含めて）。 -/
def TapeBounded (nsym bl : Nat) (t : Array Nat) : Prop :=
  ∀ i, readAt bl t i < nsym

theorem tapeRel_map (h : Nat → Nat) (bl : Nat) (t : Array Nat) :
    TapeRel h bl t (t.map h) := by
  intro i
  unfold readAt
  by_cases hi : i < t.size
  · have hi' : i < (t.map h).size := by rw [Array.size_map]; exact hi
    rw [dif_pos hi', dif_pos hi]
    first
    | exact Array.getElem_map h t i hi'
    | (simp [Array.getElem_map]; done)
    | (simp; done)
  · have hi' : ¬ i < (t.map h).size := by rw [Array.size_map]; exact hi
    rw [dif_neg hi', dif_neg hi]

/-- 具体配置の有界性は `native_decide` 可能な ∀ i < size から出す
    （`Nat.decidableBallLT` が効く形）。 -/
theorem tapeBounded_of_forall {nsym bl : Nat} {t : Array Nat}
    (hbl : bl < nsym) (ht : ∀ i, (hi : i < t.size) → t[i] < nsym) :
    TapeBounded nsym bl t := by
  intro i
  unfold readAt
  by_cases hi : i < t.size
  · rw [dif_pos hi]; exact ht i hi
  · rw [dif_neg hi]; exact hbl

/-! ## step の等式補題（Basic.step の内部 matcher に触れずに済ませる） -/

/-- `step` の「規則 r が見つかったとき」の本体。`Basic.step` の some 分岐と字面を揃える。 -/
def stepRule (bl : Nat) (c : Conf) (r : Quint) : Option Conf :=
  match r.d with
  | Dir.L => if c.pos = 0 then none
             else some { st := r.q, pos := c.pos - 1, tape := writeAt bl c.tape c.pos r.t }
  | Dir.Z => some { st := r.q, pos := c.pos, tape := writeAt bl c.tape c.pos r.t }
  | Dir.R => some { st := r.q, pos := c.pos + 1, tape := writeAt bl c.tape c.pos r.t }

theorem step_of_find?_none {tbl : List Quint} {bl : Nat} {c : Conf}
    (hf : find? tbl c.st (readAt bl c.tape c.pos) = none) : step tbl bl c = none := by
  first
  | (unfold step; rw [hf]; done)
  | (unfold step; rw [hf]; rfl)
  | (simp only [step, hf]; done)
  | (simp [step, hf]; done)

theorem step_of_find?_some {tbl : List Quint} {bl : Nat} {c : Conf} {r : Quint}
    (hf : find? tbl c.st (readAt bl c.tape c.pos) = some r) :
    step tbl bl c = stepRule bl c r := by
  first
  | (unfold step; rw [hf]; done)
  | (unfold step; rw [hf]; rfl)
  | (unfold step stepRule; rw [hf]; done)
  | (unfold step stepRule; rw [hf]; rfl)
  | (unfold step stepRule; rw [hf]; cases r.d <;> rfl)
  | (simp only [step, stepRule, hf]; done)
  | (simp [step, stepRule, hf]; done)

theorem stepRule_L (bl : Nat) (c : Conf) (r : Quint) (hd : r.d = Dir.L) :
    stepRule bl c r = if c.pos = 0 then none
      else some { st := r.q, pos := c.pos - 1, tape := writeAt bl c.tape c.pos r.t } := by
  first
  | (unfold stepRule; rw [hd]; done)
  | (unfold stepRule; rw [hd]; rfl)
  | (simp only [stepRule, hd]; done)
  | (simp [stepRule, hd]; done)

theorem stepRule_Z (bl : Nat) (c : Conf) (r : Quint) (hd : r.d = Dir.Z) :
    stepRule bl c r = some { st := r.q, pos := c.pos, tape := writeAt bl c.tape c.pos r.t } := by
  first
  | (unfold stepRule; rw [hd]; done)
  | (unfold stepRule; rw [hd]; rfl)
  | (simp only [stepRule, hd]; done)
  | (simp [stepRule, hd]; done)

theorem stepRule_R (bl : Nat) (c : Conf) (r : Quint) (hd : r.d = Dir.R) :
    stepRule bl c r = some { st := r.q, pos := c.pos + 1, tape := writeAt bl c.tape c.pos r.t } := by
  first
  | (unfold stepRule; rw [hd]; done)
  | (unfold stepRule; rw [hd]; rfl)
  | (simp only [stepRule, hd]; done)
  | (simp [stepRule, hd]; done)

/-! ## 1 ステップの模倣 -/

/-- ステップ模倣の主補題。関係（状態一致・位置一致・TapeRel・有界）が 1 ステップ保存される。
    停止（規則なし・左端落ち）も両側で一致する。 -/
theorem step_sim {h rep : Nat → Nat} {sl : List Nat} {nsym : Nat} {tbl : List Quint} {bl : Nat}
    (Hcoh : coherent h tbl = true)
    (Hsym : symBoundB nsym tbl = true)
    (Hcov : coverB sl tbl = true)
    (Hdom : domB h rep sl nsym tbl = true)
    {c c' : Conf} (Hst : c'.st = c.st) (Hpos : c'.pos = c.pos)
    (Htape : TapeRel h bl c.tape c'.tape) (Hb : TapeBounded nsym bl c.tape) :
    (step tbl bl c = none ∧ step (mapTable h tbl) (h bl) c' = none) ∨
    ∃ d d' : Conf, step tbl bl c = some d ∧ step (mapTable h tbl) (h bl) c' = some d' ∧
      d'.st = d.st ∧ d'.pos = d.pos ∧
      TapeRel h bl d.tape d'.tape ∧ TapeBounded nsym bl d.tape := by
  have hread : readAt (h bl) c'.tape c'.pos = h (readAt bl c.tape c.pos) := by
    rw [Hpos]; exact Htape c.pos
  have hs2 : readAt bl c.tape c.pos < nsym := Hb c.pos
  cases hf : find? tbl c.st (readAt bl c.tape c.pos) with
  | none =>
    cases hf' : tbl.find? (fun q => q.p == c.st && h q.s == h (readAt bl c.tape c.pos)) with
    | none =>
      have e1 : step tbl bl c = none := step_of_find?_none hf
      have e2 : step (mapTable h tbl) (h bl) c' = none := by
        apply step_of_find?_none
        rw [Hst, hread]
        exact find?_mapTable_eq_none (h := h) (p := c.st) (σ := h (readAt bl c.tape c.pos)) hf'
      exact Or.inl ⟨e1, e2⟩
    | some r₁ =>
      exfalso
      have hmem : r₁ ∈ tbl := List.mem_of_find?_eq_some hf'
      -- 08-17: 期待型を先に与えると `?p ?a` の高階単一化が `?p := (r₁.p == c.st).and` に
      -- 誤って落ちる（ログ 480 行）。型注釈なしで取り、defeq（β）で付け替える。
      have hpred0 := List.find?_some hf'
      have hpred : (r₁.p == c.st && h r₁.s == h (readAt bl c.tape c.pos)) = true := hpred0
      have hps : r₁.p = c.st := eq_of_beq (and_true_split hpred).1
      have hclass : h r₁.s = h (readAt bl c.tape c.pos) :=
        eq_of_beq (and_true_split hpred).2
      have hsl : c.st ∈ sl := by
        have hh := coverB_sound Hcov hmem
        rw [hps] at hh
        exact hh
      have hs1 : r₁.s < nsym := (symBoundB_sound Hsym hmem).1
      -- r₁ 側: (c.st, r₁.s) には規則がある → 代表側にもある
      have hsome1 : (find? tbl c.st r₁.s).isSome = true := by
        show (tbl.find? (fun q => q.p == c.st && q.s == r₁.s)).isSome = true
        apply find?_isSome_of_pred hmem
        simp [hps]
      have hrep1 : (find? tbl c.st (rep (h r₁.s))).isSome = true := by
        rw [← domB_sound Hdom hsl hs1]; exact hsome1
      -- 読んだ記号側: (c.st, s) に規則が無い → 代表側にも無い（矛盾）
      have hdom2 := domB_sound Hdom hsl hs2
      rw [hclass] at hrep1
      rw [← hdom2] at hrep1
      rw [hf] at hrep1
      first | (simp at hrep1) | exact absurd hrep1 (by decide) | cases hrep1
  | some r =>
    have hf0 : tbl.find? (fun q => q.p == c.st && q.s == readAt bl c.tape c.pos) = some r := hf
    have hmem : r ∈ tbl := List.mem_of_find?_eq_some hf0
    have hpred0 := List.find?_some hf0
    have hpred : (r.p == c.st && r.s == readAt bl c.tape c.pos) = true := hpred0
    have hrp : r.p = c.st := eq_of_beq (and_true_split hpred).1
    have hrs : r.s = readAt bl c.tape c.pos := eq_of_beq (and_true_split hpred).2
    -- 併合側の find? は空でない（r 自身がマッチする）
    have hsome : (tbl.find?
        (fun q => q.p == c.st && h q.s == h (readAt bl c.tape c.pos))).isSome = true := by
      apply find?_isSome_of_pred hmem
      simp [hrp, hrs]
    obtain ⟨r₁, hf'⟩ : ∃ r₁, tbl.find?
        (fun q => q.p == c.st && h q.s == h (readAt bl c.tape c.pos)) = some r₁ := by
      first
      | exact Option.isSome_iff_exists.mp hsome
      | (revert hsome; cases tbl.find? (fun q => q.p == c.st && h q.s == h (readAt bl c.tape c.pos)) <;> simp)
    have hmem1 : r₁ ∈ tbl := List.mem_of_find?_eq_some hf'
    have hpred10 := List.find?_some hf'
    have hpred1 : (r₁.p == c.st && h r₁.s == h (readAt bl c.tape c.pos)) = true := hpred10
    have hp1 : r₁.p = c.st := eq_of_beq (and_true_split hpred1).1
    have hs1 : h r₁.s = h (readAt bl c.tape c.pos) :=
      eq_of_beq (and_true_split hpred1).2
    obtain ⟨hw, hd, hq⟩ :=
      coherent_sound Hcoh hmem1 hmem (by rw [hp1, hrp]) (by rw [hs1, hrs])
    -- 書込後のテープの関係
    have htape' : TapeRel h bl (writeAt bl c.tape c.pos r.t)
        (writeAt (h bl) c'.tape c'.pos (h r₁.t)) := by
      intro j
      rw [Hpos]
      by_cases hj : j = c.pos
      · subst hj
        rw [readAt_writeAt_self, readAt_writeAt_self, hw]
      · rw [readAt_writeAt_other _ _ _ _ _ hj, readAt_writeAt_other _ _ _ _ _ hj]
        exact Htape j
    have hbound' : TapeBounded nsym bl (writeAt bl c.tape c.pos r.t) := by
      intro j
      by_cases hj : j = c.pos
      · subst hj
        rw [readAt_writeAt_self]
        exact (symBoundB_sound Hsym hmem).2
      · rw [readAt_writeAt_other _ _ _ _ _ hj]
        exact Hb j
    -- 両側の step を stepRule に落とす
    have e1 : step tbl bl c = stepRule bl c r := step_of_find?_some hf
    have e2 : step (mapTable h tbl) (h bl) c' = stepRule (h bl) c' (mapQuint h r₁) := by
      apply step_of_find?_some
      rw [Hst, hread]
      exact find?_mapTable_eq_some (h := h) (p := c.st) (σ := h (readAt bl c.tape c.pos)) hf'
    have hd' : (mapQuint h r₁).d = r.d := hd
    have hq' : (mapQuint h r₁).q = r.q := hq
    have hpos1 : c'.pos - 1 = c.pos - 1 := by rw [Hpos]
    have hpos2 : c'.pos + 1 = c.pos + 1 := by rw [Hpos]
    cases hdir : r.d with
    | L =>
      rw [stepRule_L bl c r hdir] at e1
      rw [stepRule_L (h bl) c' (mapQuint h r₁) (hd'.trans hdir)] at e2
      by_cases hz : c.pos = 0
      · have hz' : c'.pos = 0 := by rw [Hpos]; exact hz
        rw [if_pos hz] at e1
        rw [if_pos hz'] at e2
        exact Or.inl ⟨e1, e2⟩
      · have hz' : ¬ c'.pos = 0 := by rw [Hpos]; exact hz
        rw [if_neg hz] at e1
        rw [if_neg hz'] at e2
        refine Or.inr ⟨_, _, e1, e2, ?_, ?_, ?_, ?_⟩
        · exact hq'
        · exact hpos1
        · exact htape'
        · exact hbound'
    | Z =>
      rw [stepRule_Z bl c r hdir] at e1
      rw [stepRule_Z (h bl) c' (mapQuint h r₁) (hd'.trans hdir)] at e2
      refine Or.inr ⟨_, _, e1, e2, ?_, ?_, ?_, ?_⟩
      · exact hq'
      · exact Hpos
      · exact htape'
      · exact hbound'
    | R =>
      rw [stepRule_R bl c r hdir] at e1
      rw [stepRule_R (h bl) c' (mapQuint h r₁) (hd'.trans hdir)] at e2
      refine Or.inr ⟨_, _, e1, e2, ?_, ?_, ?_, ?_⟩
      · exact hq'
      · exact hpos2
      · exact htape'
      · exact hbound'

/-! ## 実行全体の模倣 -/

theorem haltsIn_succ_none {tbl : List Quint} {bl n : Nat} {c : Conf}
    (e : step tbl bl c = none) : haltsIn tbl bl (n + 1) c = some 0 := by
  -- 08-17: 複数行の `show … match …` 代替は parse error（列ずれ）。1 行代替のみに。
  first
  | (simp only [haltsIn, e]; done)
  | (rw [haltsIn, e]; done)
  | (unfold haltsIn; rw [e]; done)
  | (simp [haltsIn, e]; done)
  | (rw [haltsIn.eq_2, e]; done)
  | (unfold haltsIn; simp [e]; done)

theorem haltsIn_succ_some {tbl : List Quint} {bl n : Nat} {c d : Conf}
    (e : step tbl bl c = some d) :
    haltsIn tbl bl (n + 1) c = (haltsIn tbl bl n d).map (· + 1) := by
  first
  | (simp only [haltsIn, e]; done)
  | (rw [haltsIn, e]; done)
  | (unfold haltsIn; rw [e]; done)
  | (simp [haltsIn, e]; done)
  | (rw [haltsIn.eq_2, e]; done)
  | (unfold haltsIn; simp [e]; done)

theorem haltsIn_sim {h rep : Nat → Nat} {sl : List Nat} {nsym : Nat} {tbl : List Quint} {bl : Nat}
    (Hcoh : coherent h tbl = true)
    (Hsym : symBoundB nsym tbl = true)
    (Hcov : coverB sl tbl = true)
    (Hdom : domB h rep sl nsym tbl = true) :
    ∀ (n : Nat) {c c' : Conf}, c'.st = c.st → c'.pos = c.pos →
      TapeRel h bl c.tape c'.tape → TapeBounded nsym bl c.tape →
      haltsIn (mapTable h tbl) (h bl) n c' = haltsIn tbl bl n c := by
  intro n
  induction n with
  | zero => intro c c' _ _ _ _; rfl
  | succ n ih =>
    intro c c' Hst Hpos Htape Hb
    rcases step_sim Hcoh Hsym Hcov Hdom Hst Hpos Htape Hb with
      ⟨e1, e2⟩ | ⟨d, d', e1, e2, h3, h4, h5, h6⟩
    · rw [haltsIn_succ_none e2, haltsIn_succ_none e1]
    · rw [haltsIn_succ_some e2, haltsIn_succ_some e1, ih h3 h4 h5 h6]

/-- 主定理: h で書き換えた機械は、元の機械の任意の（記号有界な）配置からの実行を
    ステップ数込みで再現する。初期配置は `mapConf h` で構成すればよい。 -/
theorem haltsIn_map {h rep : Nat → Nat} {sl : List Nat} {nsym : Nat} {tbl : List Quint} {bl : Nat}
    (Hcoh : coherent h tbl = true)
    (Hsym : symBoundB nsym tbl = true)
    (Hcov : coverB sl tbl = true)
    (Hdom : domB h rep sl nsym tbl = true)
    (c : Conf) (Hb : TapeBounded nsym bl c.tape) (n : Nat) :
    haltsIn (mapTable h tbl) (h bl) n (mapConf h c) = haltsIn tbl bl n c :=
  haltsIn_sim Hcoh Hsym Hcov Hdom n rfl rfl (tapeRel_map h bl c.tape) Hb

/-! ## 重複除去（併合後の表の正規形） -/

/-- x と等しい要素を落とす。 -/
def dropEq (x : Quint) : List Quint → List Quint
  | [] => []
  | y :: ys => if y = x then dropEq x ys else y :: dropEq x ys

/-- 先頭優先の重複除去（構造再帰）。coherent な表の h-像では、同じキーに潰れた規則は
    同一の五つ組になるので、これで Morita 形式の併合表が得られる。 -/
def dedupT : List Quint → List Quint
  | [] => []
  | x :: xs => x :: dropEq x (dedupT xs)

theorem dropEq_cons_pos (x y : Quint) (ys : List Quint) (hy : y = x) :
    dropEq x (y :: ys) = dropEq x ys := by
  first
  | (simp only [dropEq, if_pos hy]; done)
  | (unfold dropEq; rw [if_pos hy]; done)
  | (rw [dropEq, if_pos hy]; done)
  | (simp [dropEq, hy]; done)

theorem dropEq_cons_neg (x y : Quint) (ys : List Quint) (hy : ¬ y = x) :
    dropEq x (y :: ys) = y :: dropEq x ys := by
  first
  | (simp only [dropEq, if_neg hy]; done)
  | (unfold dropEq; rw [if_neg hy]; done)
  | (rw [dropEq, if_neg hy]; done)
  | (simp [dropEq, hy]; done)

theorem find?_dropEq {p : Quint → Bool} {x : Quint} (hx : p x = false) :
    ∀ (l : List Quint), (dropEq x l).find? p = l.find? p := by
  intro l
  induction l with
  | nil => rfl
  | cons z zs ih =>
    by_cases hz : z = x
    · rw [dropEq_cons_pos x z zs hz, ih, find?_cons_neg p z zs (by rw [hz]; exact hx)]
    · rw [dropEq_cons_neg x z zs hz]
      cases hpz : p z with
      | true => rw [find?_cons_pos p z (dropEq x zs) hpz, find?_cons_pos p z zs hpz]
      | false =>
        rw [find?_cons_neg p z (dropEq x zs) hpz, find?_cons_neg p z zs hpz]
        exact ih

theorem dedupT_cons (x : Quint) (xs : List Quint) :
    dedupT (x :: xs) = x :: dropEq x (dedupT xs) := by
  first | rfl | (simp only [dedupT]; done) | (unfold dedupT; done)

theorem find?_dedupT (p : Quint → Bool) :
    ∀ (l : List Quint), (dedupT l).find? p = l.find? p := by
  intro l
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [dedupT_cons]
    cases hx : p x with
    | true => rw [find?_cons_pos p x (dropEq x (dedupT xs)) hx, find?_cons_pos p x xs hx]
    | false =>
      rw [find?_cons_neg p x (dropEq x (dedupT xs)) hx, find?_cons_neg p x xs hx,
          find?_dropEq hx (dedupT xs), ih]

theorem find?_dedupT' (l : List Quint) (p s : Nat) :
    find? (dedupT l) p s = find? l p s :=
  find?_dedupT (fun r => r.p == p && r.s == s) l

theorem step_congr_table {t1 t2 : List Quint}
    (hfind : ∀ p s, find? t1 p s = find? t2 p s) (bl : Nat) (c : Conf) :
    step t1 bl c = step t2 bl c := by
  first
  | (unfold step; rw [hfind]; done)
  | (simp only [step, hfind]; done)
  | (unfold step; rw [hfind]; rfl)

theorem haltsIn_congr_table {t1 t2 : List Quint}
    (hfind : ∀ p s, find? t1 p s = find? t2 p s) (bl : Nat) :
    ∀ (n : Nat) (c : Conf), haltsIn t1 bl n c = haltsIn t2 bl n c := by
  intro n
  induction n with
  | zero => intro c; rfl
  | succ n ih =>
    intro c
    have hs := step_congr_table hfind bl c
    cases e : step t2 bl c with
    | none => rw [haltsIn_succ_none (hs.trans e), haltsIn_succ_none e]
    | some c' => rw [haltsIn_succ_some (hs.trans e), haltsIn_succ_some e, ih]

/-- 重複除去つきの主定理。`dedupT (mapTable h tbl)` が Morita 形式の併合機械。 -/
theorem haltsIn_dedup_map {h rep : Nat → Nat} {sl : List Nat} {nsym : Nat}
    {tbl : List Quint} {bl : Nat}
    (Hcoh : coherent h tbl = true)
    (Hsym : symBoundB nsym tbl = true)
    (Hcov : coverB sl tbl = true)
    (Hdom : domB h rep sl nsym tbl = true)
    (c : Conf) (Hb : TapeBounded nsym bl c.tape) (n : Nat) :
    haltsIn (dedupT (mapTable h tbl)) (h bl) n (mapConf h c) = haltsIn tbl bl n c := by
  rw [haltsIn_congr_table (find?_dedupT' (mapTable h tbl))]
  exact haltsIn_map Hcoh Hsym Hcov Hdom c Hb n

end URTM
