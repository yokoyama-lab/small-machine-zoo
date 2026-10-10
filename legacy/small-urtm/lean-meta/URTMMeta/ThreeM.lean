/-
  3 状態 2 記号の URTM（段階 2e の 9）: **群 D の残り 2 類（class 20, 26、24 表。P' 型）**。**手書き**。

  向き: 開いている側を右にそろえる。状態は z（左へ動いて入る状態）と要求の状態 r1, r2。規則（`CellPP`）:
  L1 = (z, f') → (0, L, z)、R3 = (z, 1−f') → (f', R, r2)、(r1, 0) → (1, L, z)、(r1, 1) → (1−f', R, r1)、
  (r2, 1) → (f', R, r1)、(r2, 0) は規則無し（止まる）。
  セルの変換器: 0 に r1 → 1（吸収）、0 に r2 → 止まる、1 に r2 → 0（r1 を 1 つ送る）、1 に r1 → 0（r1 を送り、
  z が戻って 1−f' を読むと R3 で r2 も送る。出力は「r1 r2」）。カスケードの 1 歩は `cpp`。
  窓: z は f' の上を 0 にしながら左へ進み、1−f' に会うと R3 で r2 を右へ送る。その右のセルは掃引で 0 になって
  いるので、その場で止まる。よって窓から右への訪問は高々 2 回（初めの状態が要求ならその訪問と、z が初めに
  1−f' の上に居たときの 1 回）。止まる実行のヘッドは [a−2, b+4] に収まる（`bnd_mainPP`）。
  Pavlotskaya (1978) は補題 4 の最初の場合（「𝒫L1^k x3 が右でなければ L1-掃引は有限」）で済ませていて、証明が無い。
-/
import URTMMeta.ThreeL

namespace URTM.Meta
open URTM URTM.TwoState URTM.Three

/-- P' 型の規則（上の説明）。 -/
structure CellPP (tbl : List Quint) (z r1 r2 f' : Nat) : Prop where
  hZ : find? tbl z f' = some ⟨z, f', 0, Dir.L, z⟩
  hS : find? tbl z (1 - f') = some ⟨z, 1 - f', f', Dir.R, r2⟩
  hA : find? tbl r1 0 = some ⟨r1, 0, 1, Dir.L, z⟩
  hF1 : find? tbl r1 1 = some ⟨r1, 1, 1 - f', Dir.R, r1⟩
  hF2 : find? tbl r2 1 = some ⟨r2, 1, f', Dir.R, r1⟩
  hH : find? tbl r2 0 = none
  hf2 : f' < 2
  hperm : ∀ q, q < 3 → q = z ∨ q = r1 ∨ q = r2

/-! ### カスケード -/

/-- 戻れば止まる（2 つ目の要求 r2 が 0 に当たる）。 -/
def COut.thenHalt : COut → COut
  | .ret _ => .halt
  | .halt => .halt
  | .div => .div

/-- 戻ったら続ける。 -/
def COut.bindR (o : COut) (g : List Nat → COut) : COut :=
  match o with
  | .ret cs => g cs
  | .halt => .halt
  | .div => .div

/-- 中身の列 cs のカスケードに要求 a（true = r1）を 1 つ送った結果。 -/
def cpp : List Nat → Bool → COut
  | [], true => .ret [1]
  | [], false => .halt
  | x :: t, false => if x = 0 then .halt else (cpp t true).cons0
  | [x], true => if x = 0 then .ret [1] else .ret [0, 0, 1]
  | x :: (t@(y :: u)), true =>
    if x = 0 then .ret (1 :: t) else if y = 0 then (cpp u true).cons0.cons0 else (cpp t true).thenHalt

theorem cpp_nil_t : cpp [] true = .ret [1] := by first | rfl | simp only [cpp]
theorem cpp_nil_f : cpp [] false = .halt := by first | rfl | simp only [cpp]
theorem cpp_cons_f (x : Nat) (t : List Nat) :
    cpp (x :: t) false = if x = 0 then .halt else (cpp t true).cons0 := by first | rfl | simp only [cpp]
theorem cpp_one_t (x : Nat) : cpp [x] true = if x = 0 then .ret [1] else .ret [0, 0, 1] := by
  first | rfl | simp only [cpp]
theorem cpp_two_t (x y : Nat) (u : List Nat) :
    cpp (x :: y :: u) true =
      if x = 0 then .ret (1 :: y :: u) else if y = 0 then (cpp u true).cons0.cons0 else (cpp (y :: u) true).thenHalt := by
  first | rfl | simp only [cpp]

theorem cpp_zero_t (u : List Nat) : cpp (0 :: u) true = .ret (1 :: u) := by
  cases u with
  | nil => rw [cpp_one_t, if_pos rfl]
  | cons y w => rw [cpp_two_t, if_pos rfl]

/-- 中身 1 のセルに r1 を送って戻れば、そのセルは 0。 -/
theorem cpp_head0 {y : Nat} (hy : y ≠ 0) (u cs1 : List Nat) (h : cpp (y :: u) true = .ret cs1) :
    ∃ w, cs1 = 0 :: w := by
  cases u with
  | nil =>
    rw [cpp_one_t, if_neg hy] at h
    cases h; exact ⟨[0, 1], rfl⟩
  | cons y' u' =>
    rw [cpp_two_t, if_neg hy] at h
    by_cases hy' : y' = 0
    · rw [if_pos hy'] at h
      obtain ⟨c1, _, rfl⟩ := cons0_eq_ret h
      exact ⟨c1, rfl⟩
    · rw [if_neg hy'] at h
      cases hc : cpp (y' :: u') true <;> rw [hc] at h <;> simp [COut.thenHalt] at h

/-- **中身 1 のセルに r1**: 右へ r1 を送り、戻れば r2 も送る。 -/
theorem cpp_one_bind (x : Nat) (hx : x ≠ 0) (tl : List Nat) :
    cpp (x :: tl) true = (cpp tl true).bindR fun cs1 => (cpp cs1 false).cons0 := by
  cases tl with
  | nil =>
    rw [cpp_one_t, if_neg hx, cpp_nil_t]
    show COut.ret [0, 0, 1] = (cpp [1] false).cons0
    rw [cpp_cons_f, if_neg Nat.one_ne_zero, cpp_nil_t]; rfl
  | cons y u =>
    rw [cpp_two_t, if_neg hx]
    by_cases hy : y = 0
    · subst hy
      rw [if_pos rfl, cpp_zero_t]
      show (cpp u true).cons0.cons0 = (cpp (1 :: u) false).cons0
      rw [cpp_cons_f, if_neg Nat.one_ne_zero]
    · rw [if_neg hy]
      cases hc : cpp (y :: u) true with
      | ret cs1 =>
        obtain ⟨w, rfl⟩ := cpp_head0 hy u cs1 hc
        show COut.halt = (cpp (0 :: w) false).cons0
        rw [cpp_cons_f, if_pos rfl]; rfl
      | halt => rfl
      | div => rfl

/-- r1 の訪問が中身 1 で始まる列を返すのは、空白か 0 で始まる列に吸収したときだけ。 -/
theorem cpp_t_ret1 {tl : List Nat} {y : Nat} {w : List Nat} (h : cpp tl true = .ret (y :: w)) :
    y = 0 ∨ (y = 1 ∧ ((tl = [] ∧ w = []) ∨ tl = 0 :: w)) := by
  cases tl with
  | nil => rw [cpp_nil_t] at h; cases h; exact Or.inr ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
  | cons x u =>
    by_cases hx : x = 0
    · subst hx
      rw [cpp_zero_t] at h; cases h; exact Or.inr ⟨rfl, Or.inr rfl⟩
    · obtain ⟨w', hw⟩ := cpp_head0 hx u _ h
      cases hw; exact Or.inl rfl

theorem cpp_len : ∀ (cs : List Nat) (a : Bool) (cs' : List Nat), cpp cs a = .ret cs' → cs'.length ≤ cs.length + 2
  | [], true, cs', h => by rw [cpp_nil_t] at h; cases h; simp
  | [], false, cs', h => by rw [cpp_nil_f] at h; cases h
  | x :: t, false, cs', h => by
    rw [cpp_cons_f] at h
    by_cases hx : x = 0
    · rw [if_pos hx] at h; cases h
    · rw [if_neg hx] at h
      obtain ⟨c1, h1, rfl⟩ := cons0_eq_ret h
      have := cpp_len t true c1 h1
      simp only [List.length_cons]; omega
  | [x], true, cs', h => by
    rw [cpp_one_t] at h
    by_cases hx : x = 0
    · rw [if_pos hx] at h; cases h; simp
    · rw [if_neg hx] at h; cases h; simp
  | x :: y :: u, true, cs', h => by
    rw [cpp_two_t] at h
    by_cases hx : x = 0
    · rw [if_pos hx] at h; cases h; simp
    · rw [if_neg hx] at h
      by_cases hy : y = 0
      · rw [if_pos hy] at h
        obtain ⟨c1, h1, rfl⟩ := cons0_eq_ret h
        obtain ⟨c2, h2, rfl⟩ := cons0_eq_ret h1
        have := cpp_len u true c2 h2
        simp only [List.length_cons]; omega
      · rw [if_neg hy] at h
        cases hc : cpp (y :: u) true <;> rw [hc] at h <;> simp [COut.thenHalt] at h

theorem cpp_bin : ∀ (cs : List Nat) (a : Bool) (cs' : List Nat), Bin cs → cpp cs a = .ret cs' → Bin cs'
  | [], true, cs', _, h => by
    rw [cpp_nil_t] at h; cases h
    intro k; rcases k with _ | k <;> simp
  | [], false, cs', _, h => by rw [cpp_nil_f] at h; cases h
  | x :: t, false, cs', hb, h => by
    have hbt : Bin t := fun k => by have := hb (k + 1); rwa [List.getD_cons_succ] at this
    rw [cpp_cons_f] at h
    by_cases hx : x = 0
    · rw [if_pos hx] at h; cases h
    · rw [if_neg hx] at h
      obtain ⟨c1, h1, rfl⟩ := cons0_eq_ret h
      have := cpp_bin t true c1 hbt h1
      intro k; cases k with
      | zero => simp
      | succ k => rw [List.getD_cons_succ]; exact this k
  | [x], true, cs', _, h => by
    rw [cpp_one_t] at h
    by_cases hx : x = 0
    · rw [if_pos hx] at h; cases h
      intro k; rcases k with _ | k <;> simp
    · rw [if_neg hx] at h; cases h
      intro k; rcases k with _ | _ | _ | k <;> simp
  | x :: y :: u, true, cs', hb, h => by
    have hbu : Bin u := fun k => by have := hb (k + 2); rwa [List.getD_cons_succ, List.getD_cons_succ] at this
    rw [cpp_two_t] at h
    by_cases hx : x = 0
    · rw [if_pos hx] at h; cases h
      intro k; cases k with
      | zero => simp
      | succ k => rw [List.getD_cons_succ]; have := hb (k + 1); rwa [List.getD_cons_succ] at this
    · rw [if_neg hx] at h
      by_cases hy : y = 0
      · rw [if_pos hy] at h
        obtain ⟨c1, h1, rfl⟩ := cons0_eq_ret h
        obtain ⟨c2, h2, rfl⟩ := cons0_eq_ret h1
        have := cpp_bin u true c2 hbu h2
        intro k; rcases k with _ | _ | k
        · simp
        · simp
        · rw [List.getD_cons_succ, List.getD_cons_succ]; exact this k
      · rw [if_neg hy] at h
        cases hc : cpp (y :: u) true <;> rw [hc] at h <;> simp [COut.thenHalt] at h

/-! ### 訪問 -/

section visitPP
variable {tbl : List Quint} {z r1 r2 f' : Nat} (H : CellPP tbl z r1 r2 f')
include H

/-- **中身 1 のセルに r1**: r1 の訪問（結果 o1）のあと、z が 1−f' を読んで R3 で r2 を送る（結果 g cs1）。 -/
theorem vis_two {b : Int} {tp : Int → Nat} (hx : tp (b + 1) = 1) {up : Int} (hup : b + 1 ≤ up) {o1 : COut}
    (h1 : VSpec tbl z (b + 1) (write tp (b + 1) (1 - f')) ⟨r1, b + 1 + 1, write tp (b + 1) (1 - f')⟩ up o1)
    {g : List Nat → COut}
    (h2 : ∀ cs1 tp2, o1 = .ret cs1 → RepQ (b + 1) tp2 cs1 →
      VSpec tbl z (b + 1) (write tp2 (b + 1) f') ⟨r2, b + 1 + 1, write tp2 (b + 1) f'⟩ up (g cs1)) :
    VSpec tbl z b tp ⟨r1, b + 1, tp⟩ up (o1.bindR fun cs1 => (g cs1).cons0) := by
  have e1 : qrun tbl 1 ⟨r1, b + 1, tp⟩ = some ⟨r1, b + 1 + 1, write tp (b + 1) (1 - f')⟩ := step_R hx H.hF1
  cases o1 with
  | ret cs1 =>
    obtain ⟨k1, tp2, hv, hrun, hag, hrep⟩ := h1
    have htp2 : tp2 (b + 1) = 1 - f' := by rw [hag _ le_rfl]; simp [write]
    have hin := vspec_fwd' H.hZ htp2 H.hS hup (h2 cs1 tp2 rfl hrep)
    exact vspec_pre (k := 1 + k1) (by rw [qrun_add, e1, Option.bind_some, hrun])
      (VB_cat (VB_one le_rfl hup) e1 (VB_mono hv (by omega) le_rfl))
      (fun x hx' => by rw [hag x (by omega), write_off _ _ _ (by omega)]) hin
  | halt =>
    obtain ⟨k1, hv, hrun⟩ := h1
    exact ⟨1 + k1, VB_cat (VB_one le_rfl hup) e1 (VB_mono hv (by omega) le_rfl),
      by rw [qrun_add, e1, Option.bind_some, hrun]⟩
  | div =>
    intro n hn
    cases n with
    | zero => simp [qrun] at hn
    | succ n =>
      rw [show n + 1 = 1 + n by omega, qrun_add, e1, Option.bind_some] at hn
      exact h1 n hn

/-- **カスケードの訪問**: 右の中身が cs を表すとき、要求 a で b+1 に入った訪問の結果は `cpp cs a`。
    訪問中のヘッドは b+1 から b+2+|cs|。 -/
theorem visitPP : ∀ (n : Nat) (cs : List Nat), cs.length = n → ∀ (b : Int) (tp : Int → Nat), Bin cs →
    RepQ b tp cs → ∀ a : Bool, VSpec tbl z b tp ⟨sP r1 r2 a, b + 1, tp⟩ (b + 2 + cs.length) (cpp cs a) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro cs hn b tp hb hr a
  cases cs with
  | nil =>
    have h0 : tp (b + 1) = 0 := hr.zero _ le_rfl
    have hup : b + 1 ≤ b + 2 + (([] : List Nat).length : Int) := by simp
    cases a with
    | true =>
      rw [cpp_nil_t]
      exact vspec_ab' h0 H.hA (RepQ.of_zero (fun x hx => hr.zero x (by omega))) hup
    | false => rw [cpp_nil_f]; exact vspec_ht' h0 H.hH hup
  | cons x tl =>
    have hx := hr.head
    have hx2 : x < 2 := by have := hb 0; rwa [List.getD_cons_zero] at this
    have hbt : Bin tl := fun k => by have := hb (k + 1); rwa [List.getD_cons_succ] at this
    have hlen : tl.length < n := by rw [← hn]; simp
    have hup : b + 1 ≤ b + 2 + ((x :: tl).length : Int) := by simp; omega
    have hmono : b + 1 + 2 + (tl.length : Int) ≤ b + 2 + ((x :: tl).length : Int) := by
      simp only [List.length_cons]; push_cast; omega
    rcases (by omega : x = 0 ∨ x = 1) with rfl | rfl
    · cases a with
      | true => rw [cpp_zero_t]; exact vspec_ab' hx H.hA hr.shift hup
      | false => rw [cpp_cons_f, if_pos rfl]; exact vspec_ht' hx H.hH hup
    · cases a with
      | false =>
        rw [cpp_cons_f, if_neg Nat.one_ne_zero]
        apply vspec_fwd' H.hZ hx H.hF2 hup
        exact VSpec.mono hmono (ih tl.length hlen tl rfl (b + 1) _ hbt (hr.shift.write_le le_rfl f') true)
      | true =>
        rw [cpp_one_bind 1 (by decide)]
        refine vis_two H hx hup
          (VSpec.mono hmono (ih tl.length hlen tl rfl (b + 1) _ hbt (hr.shift.write_le le_rfl (1 - f')) true)) ?_
        intro cs1 tp2 hc hrep
        cases cs1 with
        | nil =>
          rw [cpp_nil_f]
          exact vspec_ht' (by rw [write_off _ _ _ (by omega)]; exact hrep.zero _ le_rfl) H.hH (by omega)
        | cons y w =>
          have hy := hrep.head
          rcases cpp_t_ret1 hc with h0 | ⟨rfl, htl⟩
          · subst h0
            rw [cpp_cons_f, if_pos rfl]
            exact vspec_ht' (by rw [write_off _ _ _ (by omega)]; exact hy) H.hH (by omega)
          · rw [cpp_cons_f, if_neg Nat.one_ne_zero]
            have hy' : write tp2 (b + 1) f' (b + 1 + 1) = 1 := by rw [write_off _ _ _ (by omega)]; exact hy
            apply vspec_fwd' H.hZ hy' H.hF2 (by omega)
            have hrw : RepQ (b + 1 + 1) (write (write tp2 (b + 1) f') (b + 1 + 1) f') w :=
              (hrep.write_le (by omega) f').shift.write_le le_rfl f'
            rcases htl with ⟨rfl, rfl⟩ | rfl
            · rw [cpp_nil_t]
              exact vspec_ab' (hrw.zero _ le_rfl) H.hA (RepQ.of_zero (fun x hx => hrw.zero x (by omega)))
                (by simp only [List.length_cons, List.length_nil]; push_cast; omega)
            · have hbw : Bin w := fun k => by have := hbt (k + 1); rwa [List.getD_cons_succ] at this
              refine VSpec.mono ?_ (ih w.length (by rw [← hn]; simp only [List.length_cons]; omega) w rfl
                (b + 1 + 1) _ hbw hrw true)
              simp only [List.length_cons]; push_cast; omega

end visitPP

/-! ### 窓 -/

section windowPP
variable {tbl : List Quint} {z r1 r2 f' : Nat} (H : CellPP tbl z r1 r2 f')
include H

/-- 掃引が c に着いたあと: R3 で r2 を c+1 へ送り、c+1 が 0 なのでそこで止まる。 -/
theorem sweep_end {c : Int} {tp : Int → Nat} (hc : tp c = 1 - f') (h0 : tp (c + 1) = 0) {lo up : Int}
    (hl : lo ≤ c) (hu : c + 1 ≤ up) : AB tbl ⟨z, c, tp⟩ lo up := by
  have e1 : qrun tbl 1 ⟨z, c, tp⟩ = some ⟨r2, c + 1, write tp c f'⟩ := step_R hc H.hS
  have e2 : qrun tbl 1 ⟨r2, c + 1, write tp c f'⟩ = none :=
    step_none (by rw [write_off _ _ _ (by omega)]; exact h0) H.hH
  exact AB_cat (VB_one hl (by omega)) e1 (AB_halt (VB_one (by omega) hu) e2)

/-- L1 で y から左へ出たあと（y は 0 に、y−1 から掃引）: 止まる実行は [a−2, y] にある。 -/
theorem after_L1 (a y : Int) (tp : Int → Nat) (hy0 : tp y = 0) (h2 : ∀ x, tp x < 2)
    (hcl : ∀ c, c < y → (∀ x, c < x → x < y → tp x = f') → tp c = 1 - f' → a - 2 ≤ c)
    (n : Nat) (hn : qrun tbl n ⟨z, y - 1, tp⟩ = none) : AB tbl ⟨z, y - 1, tp⟩ (a - 2) y := by
  obtain ⟨c, k, tp', hcy, hrun, hvb, hc, hfx, hzero, hag⟩ := sweep_run H.hZ H.hf2 n (y - 1) tp h2 hn
  have hca : a - 2 ≤ c := hcl c (by omega) (fun x h1 h2x => hfx x h1 (by omega)) hc
  have h0 : tp' (c + 1) = 0 := by
    by_cases hcy' : c + 1 ≤ y - 1
    · exact hzero _ (by omega) hcy'
    · rw [hag _ (Or.inr (by omega)), show c + 1 = y by omega, hy0]
  have htc : tp' c = 1 - f' := by rw [hag c (Or.inl le_rfl), hc]
  exact AB_cat (VB_mono hvb hca (by omega)) hrun (sweep_end H htc h0 hca (by omega))

/-- **z から**: z が y（a−1 ≤ y ≤ b）に居て、中身が [a, b+2] の外で 0 なら、止まる実行のヘッドは [a−2, b+4] にある。 -/
theorem from_zPP (a b y : Int) (tp : Int → Nat) (hy1 : a - 1 ≤ y) (hy2 : y ≤ b) (h2 : ∀ x, tp x < 2)
    (hlo : ∀ x, x < a → tp x = 0) (hhi : ∀ x, b + 2 < x → tp x = 0)
    (n : Nat) (hn : qrun tbl n ⟨z, y, tp⟩ = none) : AB tbl ⟨z, y, tp⟩ (a - 2) (b + 4) := by
  have hf2 := H.hf2
  by_cases hyf : tp y = f'
  · -- L1 で左へ
    have e1 : qrun tbl 1 ⟨z, y, tp⟩ = some ⟨z, y - 1, write tp y 0⟩ := step_Lm hyf H.hZ
    obtain ⟨_, hn'⟩ := run_split e1 hn
    have h2' : ∀ x, write tp y 0 x < 2 := fun x => by
      unfold write; by_cases h : x = y
      · rw [if_pos h]; omega
      · rw [if_neg h]; exact h2 x
    have hab := after_L1 H a y (write tp y 0) (by simp [write]) h2' (fun c hcy hfx hc => by
      by_contra hlt
      rcases (by omega : f' = 0 ∨ f' = 1) with h0 | h1
      · rw [write_off _ _ _ (by omega), hlo c (by omega), h0] at hc; omega
      · by_cases hya : y < a
        · rw [hlo y hya, h1] at hyf; omega
        · have := hfx (a - 1) (by omega) (by omega)
          rw [write_off _ _ _ (by omega), hlo (a - 1) (by omega), h1] at this; omega) _ hn'
    exact AB_cat (VB_one (by omega) (by omega)) e1 (AB_mono hab le_rfl (by omega))
  · -- R3 で右へ r2 を送る
    have hyx : tp y = 1 - f' := by have := h2 y; omega
    have e1 : qrun tbl 1 ⟨z, y, tp⟩ = some ⟨r2, y + 1, write tp y f'⟩ := step_R hyx H.hS
    obtain ⟨len, hl⟩ : ∃ len : Nat, (len : Int) = b + 2 - y := ⟨(b + 2 - y).toNat, by omega⟩
    have hrep : RepQ y (write tp y f') (listOf (fun i => tp (y + 1 + i)) len) := by
      intro i
      rw [listOf_getD, write_off _ _ _ (by omega)]
      by_cases hi : i < len
      · rw [if_pos hi]
      · rw [if_neg hi]; exact hhi _ (by omega)
    have hbin : Bin (listOf (fun i => tp (y + 1 + i)) len) := by
      intro i
      rw [listOf_getD]
      by_cases hi : i < len
      · rw [if_pos hi]; exact h2 _
      · rw [if_neg hi]; omega
    have hv := visitPP H _ _ rfl y (write tp y f') hbin hrep false
    rw [listOf_length] at hv
    obtain ⟨_, hn1⟩ := run_split e1 hn
    cases ho : cpp (listOf (fun i => tp (y + 1 + i)) len) false with
    | ret cs' =>
      rw [ho] at hv
      obtain ⟨k, tp2, hvb, hrun, hag, hrep'⟩ := hv
      obtain ⟨_, hn2⟩ := run_split hrun hn1
      have htp2 : tp2 y = f' := by rw [hag y le_rfl]; simp [write]
      have e2 : qrun tbl 1 ⟨z, y, tp2⟩ = some ⟨z, y - 1, write tp2 y 0⟩ := step_Lm htp2 H.hZ
      obtain ⟨_, hn3⟩ := run_split e2 hn2
      have h22 : ∀ x, write tp2 y 0 x < 2 := by
        intro x
        unfold write
        by_cases h : x = y
        · rw [if_pos h]; omega
        · rw [if_neg h]
          by_cases hx : x ≤ y
          · rw [hag x hx, write_off _ _ _ h]; exact h2 x
          · have := hrep' (x - (y + 1)).toNat
            rw [show y + 1 + ((x - (y + 1)).toNat : Int) = x by omega] at this
            rw [this]; exact cpp_bin _ _ _ hbin ho _
      have hab := after_L1 H a y (write tp2 y 0) (by simp [write]) h22 (fun c hcy hfx hc => by
        by_contra hlt
        rcases (by omega : f' = 0 ∨ f' = 1) with h0 | h1
        · rw [write_off _ _ _ (by omega), hag c (by omega), write_off _ _ _ (by omega), hlo c (by omega), h0] at hc
          omega
        · have := hfx (a - 2) (by omega) (by omega)
          rw [write_off _ _ _ (by omega), hag _ (by omega), write_off _ _ _ (by omega), hlo _ (by omega), h1] at this
          omega) _ hn3
      refine AB_cat (VB_one (by omega) (by omega)) e1 (AB_cat (VB_mono hvb (by omega) (by omega)) hrun ?_)
      exact AB_cat (VB_one (by omega) (by omega)) e2 (AB_mono hab le_rfl (by omega))
    | halt =>
      rw [ho] at hv
      obtain ⟨k, hvb, hrun⟩ := hv
      exact AB_cat (VB_one (by omega) (by omega)) e1 (AB_halt (VB_mono hvb (by omega) (by omega)) hrun)
    | div =>
      rw [ho] at hv
      exact absurd hn1 (hv _)

/-- **止まる実行は [a−2, b+4] に収まる**（初めの状態で場合を分ける）。 -/
theorem bnd_mainPP (hsrc : Src3 tbl) (c0 : QConf) (a b : Int) (ha : a ≤ c0.pos) (hb : c0.pos ≤ b)
    (hz : ∀ x, (x < a ∨ b < x) → c0.tape x = 0) (h2 : ∀ x, c0.tape x < 2) (n : Nat)
    (hn : qrun tbl n c0 = none) : AB tbl c0 (a - 2) (b + 4) := by
  obtain ⟨q, p, t⟩ := c0
  simp only at ha hb hz h2
  have hvis : ∀ aa : Bool, qrun tbl n ⟨sP r1 r2 aa, p, t⟩ = none → AB tbl ⟨sP r1 r2 aa, p, t⟩ (a - 2) (b + 4) := by
    intro aa hn
    obtain ⟨len, hl⟩ : ∃ len : Nat, (len : Int) = b - p + 1 := ⟨(b - p + 1).toNat, by omega⟩
    have hrep : RepQ (p - 1) t (listOf (fun i => t (p + i)) len) := by
      intro i
      rw [listOf_getD]
      by_cases hi : i < len
      · rw [if_pos hi]; congr 1; omega
      · rw [if_neg hi]; exact hz _ (Or.inr (by omega))
    have hbin : Bin (listOf (fun i => t (p + i)) len) := by
      intro i
      rw [listOf_getD]
      by_cases hi : i < len
      · rw [if_pos hi]; exact h2 _
      · rw [if_neg hi]; omega
    have hv := visitPP H _ _ rfl (p - 1) t hbin hrep aa
    rw [show p - 1 + 1 = p by omega, listOf_length] at hv
    cases ho : cpp (listOf (fun i => t (p + i)) len) aa with
    | ret cs' =>
      rw [ho] at hv
      obtain ⟨k, t1, hvb, hrun, hag, hrep'⟩ := hv
      obtain ⟨_, hn'⟩ := run_split hrun hn
      have hl' := cpp_len _ _ _ ho
      rw [listOf_length] at hl'
      have hb' := cpp_bin _ _ _ hbin ho
      have h21 : ∀ x, t1 x < 2 := by
        intro x
        by_cases hx : x ≤ p - 1
        · rw [hag x hx]; exact h2 x
        · have := hrep' (x - (p - 1 + 1)).toNat
          rw [show p - 1 + 1 + ((x - (p - 1 + 1)).toNat : Int) = x by omega] at this
          rw [this]; exact hb' _
      have hab := from_zPP H a b (p - 1) t1 (by omega) (by omega) h21
        (fun x hx => by rw [hag x (by omega)]; exact hz x (Or.inl hx))
        (fun x hx => by
          have := hrep' (x - (p - 1 + 1)).toNat
          rw [show p - 1 + 1 + ((x - (p - 1 + 1)).toNat : Int) = x by omega] at this
          rw [this, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl) _ hn'
      exact AB_cat (VB_mono hvb (by omega) (by omega)) hrun hab
    | halt =>
      rw [ho] at hv
      obtain ⟨k, hvb, hrun⟩ := hv
      exact AB_halt (VB_mono hvb (by omega) (by omega)) hrun
    | div =>
      rw [ho] at hv
      exact absurd hn (hv n)
  by_cases hq3 : q < 3
  · rcases H.hperm q hq3 with rfl | rfl | rfl
    · exact AB_mono (from_zPP H a b p t (by omega) hb h2 (fun x hx => hz x (Or.inl hx))
        (fun x hx => hz x (Or.inr (by omega))) n hn) le_rfl le_rfl
    · exact hvis true hn
    · exact hvis false hn
  · have hf : ∀ x, find? tbl q x = none := by
      intro x
      cases h : find? tbl q x with
      | none => rfl
      | some r =>
        obtain ⟨hr, hp, _⟩ := find?_spec h
        exact absurd (hp ▸ hsrc r hr) hq3
    exact AB_halt (VB_one (lo := a - 2) (up := b + 4) (by omega) (by omega)) (step_none rfl (hf (t p)))

end windowPP

/-- **有界停止**（P' 型の表。左右の上界は 2 と 6）。 -/
theorem halts_iff_boundM {tbl : List Quint} (hsrc : Src3 tbl) (hcl : QClosed tbl 2)
    {z r1 r2 f' : Nat} (H : CellPP tbl z r1 r2 f')
    (c : QConf) (a b : Int) (ha : a ≤ c.pos) (hb : c.pos ≤ b)
    (hz : ∀ x, (x < a ∨ b < x) → c.tape x = 0) (h2 : ∀ x, c.tape x < 2) :
    QHalts tbl c ↔ qrun tbl (bound3 6 2 a b) c = none := by
  constructor
  · intro hH
    obtain ⟨T, hR⟩ := qhalts_haltRun hH
    have hab := bnd_mainPP H hsrc c a b ha hb hz h2 (T + 1) hR.dead
    refine bound_of_window hsrc hcl hR 6 2 a b hz h2 ?_ ?_
    · intro t ht; have := (hab t _ (hR.run t ht)).1; push_cast; omega
    · intro t ht; have := (hab t _ (hR.run t ht)).2; push_cast; omega
  · intro h; exact ⟨_, h⟩

/-! ### Bool の検査 -/

/-- P' 型の規則が、役割 (z, r1, r2) と f' で立つ。 -/
def cellPPWith (tbl : List Quint) (z r1 r2 f' : Nat) : Bool :=
  decide (find? tbl z f' = some ⟨z, f', 0, Dir.L, z⟩) &&
  decide (find? tbl z (1 - f') = some ⟨z, 1 - f', f', Dir.R, r2⟩) &&
  decide (find? tbl r1 0 = some ⟨r1, 0, 1, Dir.L, z⟩) &&
  decide (find? tbl r1 1 = some ⟨r1, 1, 1 - f', Dir.R, r1⟩) &&
  decide (find? tbl r2 1 = some ⟨r2, 1, f', Dir.R, r1⟩) &&
  decide (find? tbl r2 0 = none) && decide (f' < 2) && permOK z r1 r2

theorem cellPPWith_spec {tbl : List Quint} {z r1 r2 f' : Nat} (h : cellPPWith tbl z r1 r2 f' = true) :
    CellPP tbl z r1 r2 f' := by
  unfold cellPPWith at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, permOK_spec h8⟩

/-- (z, r1, r2) の 6 通りと f'。 -/
def sidePP (tbl : List Quint) : Bool :=
  cell2Roles.any fun r => [0, 1].any fun f' => cellPPWith tbl r.1 r.2.1 r.2.2 f'

theorem sidePP_bound {tbl : List Quint} (hsrc : Src3 tbl) (hcl : QClosed tbl 2) (h : sidePP tbl = true) :
    ∀ (c : QConf) (a b : Int), a ≤ c.pos → c.pos ≤ b →
      (∀ x, (x < a ∨ b < x) → c.tape x = 0) → (∀ x, c.tape x < 2) →
      (QHalts tbl c ↔ qrun tbl (bound3 6 2 a b) c = none) := by
  unfold sidePP at h
  simp only [List.any_eq_true] at h
  obtain ⟨r, -, f', -, hw⟩ := h
  exact halts_iff_boundM hsrc hcl (cellPPWith_spec hw)

theorem sidePP_mir_bound {tbl : List Quint} (hsrc : Src3 tbl) (hcl : QClosed tbl 2)
    (h : sidePP (mirTbl tbl) = true) :
    ∀ (c : QConf) (a b : Int), a ≤ c.pos → c.pos ≤ b →
      (∀ x, (x < a ∨ b < x) → c.tape x = 0) → (∀ x, c.tape x < 2) →
      (QHalts tbl c ↔ qrun tbl (bound3 6 2 a b) c = none) := by
  rw [mirTbl_eq] at h
  have hb := sidePP_bound (src3_mir hsrc) (closed_mir hcl) h
  intro c a b ha hb' hz h2
  have := hb (mirQ c) (-b) (-a) (by show -b ≤ -c.pos; omega) (by show -c.pos ≤ -a; omega)
    (fun x hx => by show c.tape (-x) = 0; exact hz (-x) (by omega)) (fun x => h2 (-x))
  rw [QHalts_mir, qrun_mir] at this
  have e : bound3 6 2 (-b) (-a) = bound3 6 2 a b := by
    unfold bound3; congr 2; omega
  rw [e] at this
  rw [this]
  cases qrun tbl (bound3 6 2 a b) c <;> simp

/-- **群 D の P' 型の 2 類の検査**: 表か、その鏡像が `sidePP`。 -/
def grpM (es : List Nat) (D : List Dir) : Bool :=
  sidePP (URTM.Three.realize es D) || sidePP (mirTbl (URTM.Three.realize es D))

/-- 段階 2e の 9 の例外: `isExcL` の表のうち、この 2 類に当たらない表。 -/
def isExcM (es : List Nat) (D : List Dir) : Bool := isExcL es D && !grpM es D

/-- 窓の幅で書いた上界。 -/
def bndM (w : Nat) : Nat := bnd3N 6 2 w

theorem bndM_primrec : Primrec bndM :=
  (Primrec.nat_add.comp (csize_primrec.comp (Primrec.const 2)
    (Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.nat_add.comp Primrec.id (Primrec.const 6))
      (Primrec.const 2)) (Primrec.const 1))) (Primrec.const 1)).of_eq fun w => rfl

section
variable {tbl : List Quint} {q₀ q₁ q₂ sg : Nat}

/-- **2 類の有界停止**（任意の表の正規形）。 -/
theorem okM_bound (H : RTM32 tbl q₀ q₁ q₂ sg)
    (hok : grpM (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl) = true) :
    ∀ (c : QConf) (m n : ℕ), -(m : ℤ) ≤ c.pos → c.pos ≤ (n : ℤ) →
      (∀ x, (x < -(m : ℤ) ∨ (n : ℤ) < x) → c.tape x = 0) → (∀ x, c.tape x < 2) →
      (QHalts (normT (tbl := tbl) (q₀ := q₀) (q₁ := q₁) (q₂ := q₂) (σ := sg)) c ↔
        qrun (normT (tbl := tbl) (q₀ := q₀) (q₁ := q₁) (q₂ := q₂) (σ := sg)) (bndM (m + n)) c
          = none) := by
  have hsrc := realize_src3 (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl)
  have hcl := realize_closed (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl)
  unfold grpM at hok
  have hb : ∀ (c : QConf) (a b : Int), a ≤ c.pos → c.pos ≤ b →
      (∀ x, (x < a ∨ b < x) → c.tape x = 0) → (∀ x, c.tape x < 2) →
      (QHalts (URTM.Three.realize (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl)) c ↔
        qrun (URTM.Three.realize (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl))
          (bound3 6 2 a b) c = none) := by
    rcases Bool.or_eq_true_iff.mp hok with h | h
    · exact sidePP_bound hsrc hcl h
    · exact sidePP_mir_bound hsrc hcl h
  intro c m n ha hb' hz h2
  unfold bndM
  rw [← bound3_eq]
  exact hb c _ _ ha hb' hz h2

/-- **3 状態 2 記号の RTM の停止問題は、U の ID の上で計算可能**（`isExcM` の表を除く）。 -/
theorem three_halting_computable_M (H : RTM32 tbl q₀ q₁ q₂ sg)
    (hne : isExcM (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl) = false) :
    ∃ f : ZID → Bool, Computable f ∧
      ∀ z, (∀ a ∈ z.2.1 ++ z.2.2, a = 0 ∨ a ∈ [sg]) → (ZHalts tbl z ↔ f z = true) := by
  cases hL : isExcL (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl) with
  | false => exact three_halting_computable_L H hL
  | true =>
    have hM : grpM (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl) = true := by
      unfold isExcM at hne; rw [hL] at hne; simpa using hne
    exact halting_computable_of_bound H bndM_primrec (okM_bound H hM)

/-- **定理（段階 2e の 9）: `isExcM` の表を除き、3 状態 2 記号の URTM は存在しない**（Morita Def. 7.1、
    U の記号集合 {0, sg} の上の ID への符号化）。 -/
theorem no_three_two_URTM_M (H : RTM32 tbl q₀ q₁ q₂ sg)
    (hne : isExcM (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl) = false) :
    ¬ IsUTM_MoritaOver tbl [sg] :=
  not_UTM_of_halting_computable (three_halting_computable_M H hne)

end

/-! ### 残る例外の数

段階 2e の 8 の例外の上界 24 表（`excLKeys`）は、すべて `grpM` に当たる（kernel）。よって `isExcM` の表は無い。 -/

theorem excL_grpM : excLKeys.all (fun k => grpM (unkey k).1 (unkey k).2) = true := by decide +kernel

/-- 段階 2e の 9 の例外の鍵（の上界）。 -/
def excMKeys : List Nat := excLKeys.filter fun k => !grpM (unkey k).1 (unkey k).2

/-- **段階 2e の 9 の例外は 0 表**（kernel の評価）。 -/
theorem excMKeys_length : excMKeys.length = 0 := by decide +kernel

/-- **`isExcM` の表は無い**（符号 6 つ・向き 3 つの表について）。 -/
theorem isExcM_false {es : List Nat} {D : List Dir} (h : ValidKey es D) : isExcM es D = false := by
  cases hx : isExcM es D with
  | false => rfl
  | true =>
    exfalso
    unfold isExcM at hx
    obtain ⟨hL, hM⟩ := Bool.and_eq_true_iff.mp hx
    obtain ⟨k, hk, he⟩ := List.mem_map.mp (mem_excLTables h hL)
    have := List.all_eq_true.mp excL_grpM k hk
    rw [he] at this
    simp only [this, Bool.not_true] at hM
    exact Bool.false_ne_true hM

section
variable {tbl : List Quint} {q₀ q₁ q₂ sg : Nat}

/-- 正規形の表の鍵は符号 6 つ（各 7 未満）と向き 3 つ。 -/
theorem absKey_valid (H : RTM32 tbl q₀ q₁ q₂ sg) : ValidKey (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl) :=
  ⟨rfl, absCodes_lt H, rfl⟩

/-- **定理（段階 2e の 9 の系）: 3 状態 2 記号の URTM は存在しない**（Morita Def. 7.1、U の記号集合 {0, sg} の上の
    ID への符号化）。例外の仮定が外れる表は無い（`isExcM_false`）。 -/
theorem no_three_two_URTM_all (H : RTM32 tbl q₀ q₁ q₂ sg) : ¬ IsUTM_MoritaOver tbl [sg] :=
  no_three_two_URTM_M H (isExcM_false (absKey_valid H))

end

end URTM.Meta
