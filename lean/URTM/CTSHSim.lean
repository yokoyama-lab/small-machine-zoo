/-
  CTSH を模倣する URTM の証明に共通の道具（機械の型にも記号の名前にも依らない）。

  * ジッパーによるテープ表現（空白記号 `bk` を引数に取る）と、1 ステップ・掃引の補題。
    もとは CTSH17_5.lean の §1・§3 にあったものを、空白記号を引数にして切り出した。
  * 模倣の枠組み `simulates_of`: 不変量 `rep`（CTSH の ID (v, m) と消去済みの記号列 rm を表す配置）が
    (i) CTSH の 1 ステップを 1 ステップ以上で模倣し、(ii) CTSH の停止 ID から停止配置 `fin` へ
    1 ステップ以上で進み、(iii) `fin` がどれも停止配置であるなら、決定的な機械は
    `rep C 0 [] w` から (10,8)・(17,5) 版と同じ 3 項（停止の順方向・逆方向・非停止の同値）を満たす。

  各機械のファイル（CTSH13_7.lean など）は (i)–(iii) だけを示し、ここから主定理を得る。
  mathlib 非依存。未証明の穴・新規公理・native_decide を使わない。
-/
import URTM.KState
import URTM.CTSH

namespace URTM.CTSH.Sim

open URTM URTM.KState URTM.CTSH

/-! ## 1. ジッパーによるテープ表現（空白は `bk`） -/

section Tape
variable {St Ps Sy : Type} (bk : Sy)

/-- 有限リストを両側無限テープに（範囲外は bk）。位置 0 がリストの先頭。 -/
def tp (L : List Sy) : Int → Sy
  | .ofNat i => L.getD i bk
  | .negSucc _ => bk

/-- ジッパー: `l` はヘッドより左を近い順、`h` はヘッドの記号、`r` は右側。位置は `l.length`。 -/
def zc (q : Tgt St Ps) (l : List Sy) (h : Sy) (r : List Sy) : Cfg St Ps Sy :=
  { st := q, pos := l.length, tape := tp bk (l.reverse ++ h :: r) }

/-- 右側リストの先頭をヘッドに（空なら bk）。 -/
def zr (q : Tgt St Ps) (l : List Sy) : List Sy → Cfg St Ps Sy
  | h :: r => zc bk q l h r
  | [] => zc bk q l bk []

/-- 左側リストの先頭をヘッドに（空なら bk。使わない）。 -/
def zl (q : Tgt St Ps) : List Sy → List Sy → Cfg St Ps Sy
  | h :: l, r => zc bk q l h r
  | [], r => zc bk q [] bk r

end Tape

section Zip
variable {St Ps Sy : Type} {bk : Sy}

theorem tp_ofNat (L : List Sy) (i : Nat) : tp bk L (i : Int) = L.getD i bk := rfl

theorem tp_trail (L : List Sy) : tp bk (L ++ [bk]) = tp bk L := by
  funext i
  cases i with
  | negSucc => rfl
  | ofNat j =>
    simp only [tp, List.getD_eq_getElem?_getD]
    by_cases h : j < L.length
    · rw [List.getElem?_append_left h]
    · rw [List.getElem?_append_right (by omega), List.getElem?_eq_none (l := L) (by omega)]
      obtain ⟨t, ht⟩ : ∃ t, j - L.length = t := ⟨_, rfl⟩
      rw [ht]; cases t <;> rfl

theorem zc_trail (q : Tgt St Ps) (l : List Sy) (h : Sy) (r : List Sy) :
    zc bk q l h (r ++ [bk]) = zc bk q l h r := by
  simp only [zc]
  rw [show l.reverse ++ h :: (r ++ [bk]) = (l.reverse ++ h :: r) ++ [bk] by simp, tp_trail]

theorem zl_trail (q : Tgt St Ps) (L r : List Sy) : zl bk q L (r ++ [bk]) = zl bk q L r := by
  cases L <;> simp only [zl, zc_trail]

theorem zc_nil (q : Tgt St Ps) (l : List Sy) (h : Sy) : zc bk q l h [] = zc bk q l h [bk] :=
  (zc_trail q l h []).symm

/-- 左から並べたリスト A ++ V でヘッドが V の先頭（V = [] なら直後の bk）の配置は、ジッパーで書ける。 -/
theorem zr_eq (q : Tgt St Ps) (A V : List Sy) :
    zr bk q A.reverse V = { st := q, pos := A.length, tape := tp bk (A ++ V) } := by
  cases V with
  | nil => simp only [zr, zc, List.reverse_reverse, List.length_reverse, tp_trail, List.append_nil]
  | cons h r => simp only [zr, zc, List.reverse_reverse, List.length_reverse]

theorem tp_at (A r : List Sy) (h : Sy) : tp bk (A ++ h :: r) (A.length : Int) = h := by
  rw [tp_ofNat]; simp

theorem tp_upd (A B : List Sy) (x t : Sy) :
    upd (tp bk (A ++ x :: B)) (A.length : Int) t = tp bk (A ++ t :: B) := by
  funext i
  unfold upd
  cases i with
  | negSucc k => simp [tp]
  | ofNat j =>
    by_cases hn : j = A.length
    · subst hn; rw [if_pos (by simp)]; exact (tp_at A B t).symm
    · rw [if_neg (by intro e; simp only [Int.ofNat_eq_natCast] at e; omega)]
      simp only [tp, List.getD_eq_getElem?_getD]
      by_cases hl : j < A.length
      · rw [List.getElem?_append_left hl, List.getElem?_append_left hl]
      · rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
        obtain ⟨t', ht⟩ : ∃ t', j - A.length = t' + 1 := ⟨j - A.length - 1, by omega⟩
        rw [ht]; rfl

theorem zc_read (q : Tgt St Ps) (l : List Sy) (h : Sy) (r : List Sy) :
    (zc bk q l h r).tape (zc bk q l h r).pos = h := by
  simp only [zc]
  rw [show (l.length : Int) = (l.reverse.length : Int) by simp]
  exact tp_at _ _ _

variable {T : Machine St Ps Sy}

theorem stepR {p : St} {h t : Sy} {q : Tgt St Ps} (hr : ⟨p, h, t, .R, q⟩ ∈ T)
    (l : List Sy) (y : Sy) (r : List Sy) :
    Step T (zc bk (.go p) l h (y :: r)) (zc bk q (t :: l) y r) := by
  refine ⟨_, hr, rfl, zc_read _ _ _ _, ?_⟩
  simp only [fire, zc, mv]
  congr 1
  rw [show (l.length : Int) = (l.reverse.length : Int) by simp, tp_upd]; simp

theorem stepL {p : St} {h t : Sy} {q : Tgt St Ps} (hr : ⟨p, h, t, .L, q⟩ ∈ T)
    (y : Sy) (l : List Sy) (r : List Sy) :
    Step T (zc bk (.go p) (y :: l) h r) (zc bk q l y (t :: r)) := by
  refine ⟨_, hr, rfl, zc_read _ _ _ _, ?_⟩
  simp only [fire, zc, mv]
  congr 1
  · simp; omega
  · rw [show ((y :: l).length : Int) = ((y :: l).reverse.length : Int) by simp, tp_upd]; simp

theorem stepZ {p : St} {h t : Sy} {q : Tgt St Ps} (hr : ⟨p, h, t, .Z, q⟩ ∈ T)
    (l : List Sy) (r : List Sy) :
    Step T (zc bk (.go p) l h r) (zc bk q l t r) := by
  refine ⟨_, hr, rfl, zc_read _ _ _ _, ?_⟩
  simp only [fire, zc, mv]
  congr 1
  rw [show (l.length : Int) = (l.reverse.length : Int) by simp, tp_upd]

theorem stepR' {p : St} {h t : Sy} {q : Tgt St Ps} (hr : ⟨p, h, t, .R, q⟩ ∈ T)
    (l : List Sy) (R : List Sy) :
    Step T (zc bk (.go p) l h R) (zr bk q (t :: l) R) := by
  cases R with
  | nil => rw [zc_nil]; exact stepR hr l bk []
  | cons y r => exact stepR hr l y r

theorem stepL' {p : St} {h t : Sy} {q : Tgt St Ps} (hr : ⟨p, h, t, .L, q⟩ ∈ T)
    {L : List Sy} (hL : L ≠ []) (r : List Sy) :
    Step T (zc bk (.go p) L h r) (zl bk q L (t :: r)) := by
  cases L with
  | nil => exact absurd rfl hL
  | cons y l => exact stepL hr y l r

/-! ### 到達可能性 -/

variable (T) in
/-- 何ステップかで到達する。 -/
def Reach (a b : Cfg St Ps Sy) : Prop := ∃ n, StepN T n a b

variable (T) in
/-- 1 ステップ以上で到達する。 -/
def Reach1 (a b : Cfg St Ps Sy) : Prop := ∃ n, StepN T (n + 1) a b

theorem Reach.refl (a : Cfg St Ps Sy) : Reach T a a := ⟨0, .refl a⟩

theorem Reach.trans {a b c : Cfg St Ps Sy} (h₁ : Reach T a b) (h₂ : Reach T b c) : Reach T a c :=
  let ⟨_, h₁⟩ := h₁; let ⟨_, h₂⟩ := h₂; ⟨_, h₁.trans h₂⟩

theorem Reach.step {a b : Cfg St Ps Sy} (h : Step T a b) : Reach T a b := ⟨1, .single h⟩

theorem Reach.of_eq {a b : Cfg St Ps Sy} (h : a = b) : Reach T a b := h ▸ Reach.refl a

theorem Reach1.trans {a b c : Cfg St Ps Sy} (h₁ : Reach1 T a b) (h₂ : Reach T b c) :
    Reach1 T a c := by
  obtain ⟨n, h₁⟩ := h₁; obtain ⟨k, h₂⟩ := h₂
  exact ⟨n + k, by have := h₁.trans h₂; rwa [show n + 1 + k = n + k + 1 by omega] at this⟩

theorem Reach1.of_step {a b c : Cfg St Ps Sy} (h₁ : Step T a b) (h₂ : Reach T b c) :
    Reach1 T a c :=
  let ⟨k, h₂⟩ := h₂; ⟨k, by have := (StepN.single h₁).trans h₂; rwa [Nat.add_comm] at this⟩

theorem Reach1.reach {a b : Cfg St Ps Sy} (h : Reach1 T a b) : Reach T a b :=
  let ⟨n, h⟩ := h; ⟨n + 1, h⟩

/-! ### 掃引（状態 q が記号 x を g x に書き換えつつ同じ向きに進み続ける。g = id なら書き換えない） -/

theorem sweepRg {q : St} (g : Sy → Sy) {X : List Sy}
    (hX : ∀ x ∈ X, (⟨q, x, g x, .R, .go q⟩ : Rule St Ps Sy) ∈ T) (l : List Sy) (z : Sy) (r : List Sy) :
    Reach T (zr bk (.go q) l (X ++ z :: r)) (zc bk (.go q) ((X.map g).reverse ++ l) z r) := by
  induction X generalizing l with
  | nil => exact Reach.refl _
  | cons x X ih =>
    have h1 := stepR' (bk := bk) (hX x (List.mem_cons_self ..)) l (X ++ z :: r)
    have h2 := ih (fun y hy => hX y (List.mem_cons_of_mem _ hy)) (g x :: l)
    simp only [List.map_cons, List.reverse_cons, List.append_assoc, List.singleton_append] at h2 ⊢
    exact (Reach.step h1).trans h2

theorem sweepLg {q : St} (g : Sy → Sy) {X : List Sy}
    (hX : ∀ x ∈ X, (⟨q, x, g x, .L, .go q⟩ : Rule St Ps Sy) ∈ T) (z : Sy) (l : List Sy) (r : List Sy) :
    Reach T (zl bk (.go q) (X ++ z :: l) r) (zc bk (.go q) l z ((X.map g).reverse ++ r)) := by
  induction X generalizing r with
  | nil => exact Reach.refl _
  | cons x X ih =>
    have h1 := stepL' (bk := bk) (hX x (List.mem_cons_self ..)) (L := X ++ z :: l) (by simp) r
    have h2 := ih (fun y hy => hX y (List.mem_cons_of_mem _ hy)) (g x :: r)
    simp only [List.map_cons, List.reverse_cons, List.append_assoc, List.singleton_append] at h2 ⊢
    exact (Reach.step h1).trans h2

theorem sweepR {q : St} {X : List Sy}
    (hX : ∀ x ∈ X, (⟨q, x, x, .R, .go q⟩ : Rule St Ps Sy) ∈ T) (l : List Sy) (z : Sy) (r : List Sy) :
    Reach T (zr bk (.go q) l (X ++ z :: r)) (zc bk (.go q) (X.reverse ++ l) z r) := by
  simpa using sweepRg id hX l z r

theorem sweepL {q : St} {X : List Sy}
    (hX : ∀ x ∈ X, (⟨q, x, x, .L, .go q⟩ : Rule St Ps Sy) ∈ T) (z : Sy) (l : List Sy) (r : List Sy) :
    Reach T (zl bk (.go q) (X ++ z :: l) r) (zc bk (.go q) l z (X.reverse ++ r)) := by
  simpa using sweepLg id hX z l r

/-- 1 ステップ（右へ、状態 p → q）に続けて q で書き換えつつ掃引。 -/
theorem runRg {p q : St} {h t : Sy} (hr : ⟨p, h, t, .R, .go q⟩ ∈ T) (g : Sy → Sy) {X : List Sy}
    (hX : ∀ x ∈ X, (⟨q, x, g x, .R, .go q⟩ : Rule St Ps Sy) ∈ T) (l : List Sy) (z : Sy) (r : List Sy) :
    Reach T (zc bk (.go p) l h (X ++ z :: r)) (zc bk (.go q) ((X.map g).reverse ++ t :: l) z r) :=
  (Reach.step (stepR' hr l _)).trans (sweepRg g hX _ z r)

theorem runL1g {p q : St} {h t : Sy} (hr : ⟨p, h, t, .L, .go q⟩ ∈ T) (g : Sy → Sy) {X : List Sy}
    (hX : ∀ x ∈ X, (⟨q, x, g x, .L, .go q⟩ : Rule St Ps Sy) ∈ T) (z : Sy) (l : List Sy) (r : List Sy) :
    Reach1 T (zc bk (.go p) (X ++ z :: l) h r) (zc bk (.go q) l z ((X.map g).reverse ++ t :: r)) :=
  Reach1.of_step (stepL' hr (by simp) r) (sweepLg g hX z l _)

theorem runLg {p q : St} {h t : Sy} (hr : ⟨p, h, t, .L, .go q⟩ ∈ T) (g : Sy → Sy) {X : List Sy}
    (hX : ∀ x ∈ X, (⟨q, x, g x, .L, .go q⟩ : Rule St Ps Sy) ∈ T) (z : Sy) (l : List Sy) (r : List Sy) :
    Reach T (zc bk (.go p) (X ++ z :: l) h r) (zc bk (.go q) l z ((X.map g).reverse ++ t :: r)) :=
  (Reach.step (stepL' hr (by simp) r)).trans (sweepLg g hX z l _)

/-- 1 ステップ（右へ、状態 p → q）に続けて q で掃引。 -/
theorem runR {p q : St} {h t : Sy} (hr : ⟨p, h, t, .R, .go q⟩ ∈ T) {X : List Sy}
    (hX : ∀ x ∈ X, (⟨q, x, x, .R, .go q⟩ : Rule St Ps Sy) ∈ T) (l : List Sy) (z : Sy) (r : List Sy) :
    Reach T (zc bk (.go p) l h (X ++ z :: r)) (zc bk (.go q) (X.reverse ++ t :: l) z r) :=
  (Reach.step (stepR' hr l _)).trans (sweepR hX _ z r)

theorem runL1 {p q : St} {h t : Sy} (hr : ⟨p, h, t, .L, .go q⟩ ∈ T) {X : List Sy}
    (hX : ∀ x ∈ X, (⟨q, x, x, .L, .go q⟩ : Rule St Ps Sy) ∈ T) (z : Sy) (l : List Sy) (r : List Sy) :
    Reach1 T (zc bk (.go p) (X ++ z :: l) h r) (zc bk (.go q) l z (X.reverse ++ t :: r)) :=
  Reach1.of_step (stepL' hr (by simp) r) (sweepL hX z l _)

theorem runL {p q : St} {h t : Sy} (hr : ⟨p, h, t, .L, .go q⟩ ∈ T) {X : List Sy}
    (hX : ∀ x ∈ X, (⟨q, x, x, .L, .go q⟩ : Rule St Ps Sy) ∈ T) (z : Sy) (l : List Sy) (r : List Sy) :
    Reach T (zc bk (.go p) (X ++ z :: l) h r) (zc bk (.go q) l z (X.reverse ++ t :: r)) :=
  (Reach.step (stepL' hr (by simp) r)).trans (sweepL hX z l _)

end Zip

/-! ## 2. 記号列の所属（`∀ x ∈ X, P x` の分解） -/

section Mem
variable {Sy : Type}

theorem fa_app {P : Sy → Prop} {A B : List Sy} (hA : ∀ x ∈ A, P x) (hB : ∀ x ∈ B, P x) :
    ∀ x ∈ A ++ B, P x := by
  intro x hx; rcases List.mem_append.mp hx with h | h
  · exact hA x h
  · exact hB x h

theorem fa_cons {P : Sy → Prop} {a : Sy} {A : List Sy} (ha : P a) (hA : ∀ x ∈ A, P x) :
    ∀ x ∈ a :: A, P x := by
  intro x hx; rcases List.mem_cons.mp hx with h | h
  · exact h ▸ ha
  · exact hA x h

theorem fa_rev {P : Sy → Prop} {A : List Sy} (hA : ∀ x ∈ A, P x) : ∀ x ∈ A.reverse, P x :=
  fun x hx => hA x (List.mem_reverse.mp hx)

theorem fa_nil {P : Sy → Prop} : ∀ x ∈ ([] : List Sy), P x := fun _ h => nomatch h

theorem fa_map {α : Type} {P : Sy → Prop} {f : α → Sy} (hf : ∀ a, P (f a)) (A : List α) :
    ∀ x ∈ A.map f, P x := by
  intro x hx; obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx; exact hf a

theorem fa_flatten {P : Sy → Prop} {L : List (List Sy)} (h : ∀ A ∈ L, ∀ x ∈ A, P x) :
    ∀ x ∈ L.flatten, P x := by
  intro x hx
  obtain ⟨A, hA, hx⟩ := List.mem_flatten.mp hx
  exact h A hA x hx

theorem ofP {P R : Sy → Prop} (hp : ∀ x, P x → R x) {X : List Sy} (h : ∀ x ∈ X, P x) :
    ∀ x ∈ X, R x := fun x hx => hp x (h x hx)

end Mem


/-! ## 3. 規則領域（ϕ₁ 型の符号化: 各記号を 1 マスに、規則は逆順、区切りは ∗、相マーカー 1 個） -/

section Area
variable {Sy : Type} (lo : Ch → Sy) (st bm : Sy)

/-- H(m) = ϕ(w^R_{k−1}) ∗ ⋯ ϕ(w^R_{m+1}) ∗（相マーカーより左の規則）。 -/
def Hi (C : CTSH) (m : Nat) : List Sy :=
  ((C.drop m).reverse.map (fun w => w.reverse.map lo ++ [st])).flatten

/-- ϕ(w^R_{m−1}) ∗ ⋯ ϕ(w^R_1) ∗。 -/
def LoCore (C : CTSH) (m : Nat) : List Sy :=
  ((C.take (m - 1)).reverse.map (fun w => w.reverse.map lo ++ [st])).flatten

/-- Lo(m) = ϕ(w^R_{m−1}) ∗ ⋯ ϕ(w^R_1) ∗ ∗（最後の ∗ が区切り 0）。相 0 では空。 -/
def Lo (C : CTSH) (m : Nat) : List Sy :=
  if m = 0 then [] else LoCore lo st C m ++ [st]

/-- 規則領域 RA(m) = H(m) · ϕ(w^R_m) · bm · Lo(m)。bm が相マーカー。 -/
def RA (C : CTSH) (m : Nat) : List Sy :=
  Hi lo st C m ++ (prod C m).reverse.map lo ++ bm :: Lo lo st C m

variable {lo st}

theorem prod_succ (C : CTSH) (m : Nat) (h : m < C.length) : prod C (m + 1) = C[m] := by
  simp [prod, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem Hi_step (C : CTSH) (m : Nat) (h : m < C.length) :
    Hi lo st C m = Hi lo st C (m + 1) ++ (prod C (m + 1)).reverse.map lo ++ [st] := by
  rw [prod_succ C m h]
  unfold Hi
  rw [List.drop_eq_getElem_cons h]
  simp only [List.reverse_cons, List.map_append, List.flatten_append, List.map_cons, List.map_nil,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc]

theorem Hi_len (C : CTSH) : Hi lo st C C.length = [] := by simp [Hi]

theorem Lo_step (C : CTSH) (m : Nat) (h : m ≤ C.length) :
    Lo lo st C (m + 1) = (prod C m).reverse.map lo ++ st :: Lo lo st C m := by
  cases m with
  | zero => simp [Lo, LoCore, prod]
  | succ m =>
    rw [prod_succ C m (by omega)]
    simp only [Lo, LoCore, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
    rw [List.take_add_one, List.getElem?_eq_getElem (by omega)]
    simp only [Option.toList_some, List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.map_cons, List.flatten_cons, List.append_assoc,
      List.cons_append]

theorem Lo_ne (C : CTSH) (m : Nat) (h : m ≠ 0) : Lo lo st C m = LoCore lo st C m ++ [st] := by
  simp [Lo, h]

theorem LoCore_full (C : CTSH) : LoCore lo st C (C.length + 1) = Hi lo st C 0 := by
  simp [LoCore, Hi]

theorem RA_zero (C : CTSH) : RA lo st bm C 0 = Hi lo st C 0 ++ [bm] := by
  simp [RA, prod, Lo]

theorem blk_mem {P : Sy → Prop} (hl : ∀ c, P (lo c)) (hs : P st) (L : List (List Ch)) :
    ∀ x ∈ (L.map (fun w => w.reverse.map lo ++ [st])).flatten, P x := by
  refine fa_flatten ?_
  intro A hA
  obtain ⟨w, _, rfl⟩ := List.mem_map.mp hA
  exact fa_app (fa_map hl _) (fa_cons hs fa_nil)

theorem Hi_mem {P : Sy → Prop} (hl : ∀ c, P (lo c)) (hs : P st) (C : CTSH) (m : Nat) :
    ∀ x ∈ Hi lo st C m, P x := blk_mem hl hs _
theorem LoCore_mem {P : Sy → Prop} (hl : ∀ c, P (lo c)) (hs : P st) (C : CTSH) (m : Nat) :
    ∀ x ∈ LoCore lo st C m, P x := blk_mem hl hs _
theorem Lo_mem {P : Sy → Prop} (hl : ∀ c, P (lo c)) (hs : P st) (C : CTSH) (m : Nat) :
    ∀ x ∈ Lo lo st C m, P x := by
  unfold Lo; split
  · exact fa_nil
  · exact fa_app (LoCore_mem hl hs C m) (fa_cons hs fa_nil)

end Area

/-! ## 4. 模倣の枠組み -/

section Frame
variable {St Ps Sy : Type} {T : Machine St Ps Sy}

theorem halts_unique (hD : Deterministic T) {N N' : Nat} {a e e' : Cfg St Ps Sy}
    (h : HaltsIn T N a e) (h' : HaltsIn T N' a e') : e = e' := by
  obtain ⟨_, h₂⟩ := stepN_prefix hD h.1 h.2 h'.1
  exact (stepN_from_halted h'.2 h₂).2

variable (C : CTSH) (rep : Nat → List Ch → List Ch → Cfg St Ps Sy)
  (fin : List Ch → Nat → List Ch → Cfg St Ps Sy)

theorem sim_steps
    (hmac : ∀ s s', CStep C s s' → ∀ rm, ∃ c, Reach1 T (rep s.2 rm s.1) (rep s'.2 (rm ++ [c]) s'.1))
    {n : Nat} {s f : ID} (h : CStepN C n s f) (rm : List Ch) :
    ∃ rm' N, n ≤ N ∧ StepN T N (rep s.2 rm s.1) (rep f.2 rm' f.1) := by
  induction h generalizing rm with
  | refl s => exact ⟨rm, 0, Nat.le_refl _, .refl _⟩
  | cons h₁ _ ih =>
    obtain ⟨c, k, hk⟩ := hmac _ _ h₁ rm
    obtain ⟨rm', N, hN, hs⟩ := ih (rm ++ [c])
    exact ⟨rm', k + 1 + N, by omega, hk.trans hs⟩

/-- **模倣の枠組み**。決定的な機械 T と、CTSH の ID を表す配置 `rep m rm v` について、
    (i) `hmac`: CTSH の 1 ステップ (v, m) ⇒ (v', m') を `rep m rm v` から 1 ステップ以上で
        `rep m' (rm ++ [c]) v'` へ模倣し、
    (ii) `hhalt`: 停止 ID (vf, mf) では `rep mf rm vf` から 1 ステップ以上で `fin vf mf rm` に達し、
    (iii) `hfin`: `fin` はどれも停止配置
    であれば、`rep 0 [] w` から (10,8)・(17,5) 版と同じ 3 項が成り立つ。 -/
theorem simulates_of (hD : Deterministic T)
    (hmac : ∀ s s', CStep C s s' → ∀ rm, ∃ c, Reach1 T (rep s.2 rm s.1) (rep s'.2 (rm ++ [c]) s'.1))
    (hhalt : ∀ vf mf, Halting C (vf, mf) → ∀ rm, Reach1 T (rep mf rm vf) (fin vf mf rm))
    (hfin : ∀ vf mf rm, Halted T (fin vf mf rm)) (w : List Ch) :
    (∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) →
      ∃ N rm, n ≤ N ∧ HaltsIn T N (rep 0 [] w) (fin vf mf rm)) ∧
    (∀ N e, HaltsIn T N (rep 0 [] w) e →
      ∃ n vf mf rm, CHaltsIn C n (w, 0) (vf, mf) ∧ e = fin vf mf rm) ∧
    ((∀ n f, ¬ CHaltsIn C n (w, 0) f) ↔ (∀ N e, ¬ HaltsIn T N (rep 0 [] w) e)) := by
  have forward : ∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) →
      ∃ N rm, n ≤ N ∧ HaltsIn T N (rep 0 [] w) (fin vf mf rm) := by
    intro n vf mf h
    obtain ⟨rm, N₁, hN₁, h₁⟩ := sim_steps C rep hmac h.1 []
    obtain ⟨k, h₂⟩ := hhalt vf mf h.2 rm
    exact ⟨N₁ + (k + 1), rm, by omega, h₁.trans h₂, hfin vf mf rm⟩
  have back : ∀ N e, HaltsIn T N (rep 0 [] w) e →
      ∃ n vf mf rm, CHaltsIn C n (w, 0) (vf, mf) ∧ e = fin vf mf rm := by
    intro N e he
    by_cases hc : ∃ n f, CHaltsIn C n (w, 0) f
    · obtain ⟨n, ⟨vf, mf⟩, hf⟩ := hc
      obtain ⟨N', rm, _, hN'⟩ := forward n vf mf hf
      exact ⟨n, vf, mf, rm, hf, halts_unique hD he hN'⟩
    · have hn : ∀ n f, ¬ CHaltsIn C n (w, 0) f := fun n f h => hc ⟨n, f, h⟩
      obtain ⟨f, hf⟩ := run_of_not_halts (s := (w, 0)) (by simp [CTSH.k]) hn (N + 1)
      obtain ⟨rm', N', hN', hs⟩ := sim_steps C rep hmac hf []
      have := (stepN_prefix hD he.1 he.2 hs).1
      omega
  refine ⟨forward, back, ?_⟩
  constructor
  · intro hn N e he
    obtain ⟨n, vf, mf, _, hf, _⟩ := back N e he
    exact hn n _ hf
  · intro hu n f hf
    obtain ⟨vf, mf⟩ := f
    obtain ⟨N, rm, _, hN⟩ := forward n vf mf hf
    exact hu N _ hN

/-- `simulates_of` の (i)(ii) を、先頭が Y・N のマクロステップ `hY`・`hN` と、停止 ID (Y v, 0)・(λ, m)
    からの停止 `hhY`・`hhN` に分けた形。 -/
theorem simulates_of_steps (hD : Deterministic T)
    (hY : ∀ {m : Nat}, m ≠ 0 → m < C.k → ∀ rm v,
      Reach1 T (rep m rm (.Y :: v)) (rep ((m + 1) % C.k) (rm ++ [.Y]) (v ++ prod C m)))
    (hN : ∀ {m : Nat}, m < C.k → ∀ rm v,
      Reach1 T (rep m rm (.N :: v)) (rep ((m + 1) % C.k) (rm ++ [.N]) v))
    (hhY : ∀ rm v, Reach1 T (rep 0 rm (.Y :: v)) (fin (.Y :: v) 0 rm))
    (hhN : ∀ m rm, Reach1 T (rep m rm []) (fin [] m rm))
    (hfin : ∀ vf mf rm, Halted T (fin vf mf rm)) (w : List Ch) :
    (∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) →
      ∃ N rm, n ≤ N ∧ HaltsIn T N (rep 0 [] w) (fin vf mf rm)) ∧
    (∀ N e, HaltsIn T N (rep 0 [] w) e →
      ∃ n vf mf rm, CHaltsIn C n (w, 0) (vf, mf) ∧ e = fin vf mf rm) ∧
    ((∀ n f, ¬ CHaltsIn C n (w, 0) f) ↔ (∀ N e, ¬ HaltsIn T N (rep 0 [] w) e)) := by
  refine simulates_of C rep fin hD (fun s s' h rm => ?_) ?_ hfin w
  · cases h with
    | y h0 hk => exact ⟨_, hY h0 hk rm _⟩
    | n hk => exact ⟨_, hN hk rm _⟩
  · rintro vf mf ⟨-, ⟨v, rfl, rfl⟩ | rfl⟩ rm
    · exact hhY rm v
    · exact hhN mf rm

omit C rep fin in
/-- 模倣の 3 項（初期配置 a、停止配置 fin）を、停止の順方向 `hF`・逆方向 `hB`・非停止 `hDiv` を保つ
    符号化 E を通して別の機械 T' へ移す（定理 A/B の系）。 -/
theorem simulates_enc {St' Sy' : Type} {T' : Machine St' Ps Sy'} {E : Cfg St Ps Sy → Cfg St' Ps Sy'}
    (hF : ∀ (n : Nat) (c cf : Cfg St Ps Sy), HaltsIn T n c cf → ∃ N, n ≤ N ∧ HaltsIn T' N (E c) (E cf))
    (hB : ∀ (N : Nat) (c : Cfg St Ps Sy) (e : Cfg St' Ps Sy'),
      HaltsIn T' N (E c) e → ∃ n cf, HaltsIn T n c cf ∧ e = E cf)
    (hDiv : ∀ c, (∀ n cf, ¬ HaltsIn T n c cf) ↔ (∀ N e, ¬ HaltsIn T' N (E c) e))
    {C : CTSH} {w : List Ch} {a : Cfg St Ps Sy} {fin : List Ch → Nat → List Ch → Cfg St Ps Sy}
    (hu : (∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) → ∃ N rm, n ≤ N ∧ HaltsIn T N a (fin vf mf rm)) ∧
      (∀ N e, HaltsIn T N a e → ∃ n vf mf rm, CHaltsIn C n (w, 0) (vf, mf) ∧ e = fin vf mf rm) ∧
      ((∀ n f, ¬ CHaltsIn C n (w, 0) f) ↔ (∀ N e, ¬ HaltsIn T N a e))) :
    (∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) → ∃ N rm, n ≤ N ∧ HaltsIn T' N (E a) (E (fin vf mf rm))) ∧
    (∀ N e, HaltsIn T' N (E a) e → ∃ n vf mf rm, CHaltsIn C n (w, 0) (vf, mf) ∧ e = E (fin vf mf rm)) ∧
    ((∀ n f, ¬ CHaltsIn C n (w, 0) f) ↔ (∀ N e, ¬ HaltsIn T' N (E a) e)) := by
  refine ⟨fun n vf mf h => ?_, fun N e he => ?_, hu.2.2.trans (hDiv a)⟩
  · obtain ⟨N, rm, hN, hh⟩ := hu.1 n vf mf h
    obtain ⟨N', hN', hh'⟩ := hF N _ _ hh
    exact ⟨N', rm, by omega, hh'⟩
  · obtain ⟨n, cf, hcf, rfl⟩ := hB N _ e he
    obtain ⟨k, vf, mf, rm, hk, rfl⟩ := hu.2.1 n cf hcf
    exact ⟨k, vf, mf, rm, hk, rfl⟩

end Frame

end URTM.CTSH.Sim
