/-
  3 状態 2 記号の URTM（段階 2e の 2）: **群 D のうち「2 進カウンタと戻らない入り口」の 8 類**（96 表）。**手書き**。

  右側の向きで書く。入り口は e と z、戻りは r（`ZRules`）。
    e: 2 進カウンタ（§12.9.3 と同じ 3 本）(e, 1) → (w, R, e)、(e, 0) → (1, L, r)、(r, w) → (0, L, r)
    z: (z, h) は規則無し、(z, 1 − h) → (1 − w, R, e)、(r, 1 − w) → (y', R, z)
  e の訪問は中身に 1 を足して r で戻る（`visit_cnt`）。z の訪問は窓へ戻らない: z の位置の記号が h なら止まり、
  そうでなければ 1 つ右から e の訪問をして戻り、1 つ右の z に移る（`zmacro`、2j+3 歩）。
  z の位置から右を下位桁が先の 2 進数 N と読むと（`bval`）、z の 1 歩で N ↦ ⌊N/2⌋ + 1（`zmstep`）。
  ⌊N/2⌋ + 1 < N でないのは N ≤ 2 のときだけで、N = 0 なら次の 1 歩で止まり、N ∈ {1, 2}（⌊N/2⌋ + 1 = N）なら
  止まらない（`znohalt`）。よって z の訪問は、止まるなら (N + 2)(2L + 3) 歩以内に止まる（`zhbound`）。N < 2^L。
  `RSide` に載せる（`z_rside`）: 類は 1 つ（m = 1）、e は r で戻り、z は戻らない。g L = (2^(L+1) + 1)(2L + 5)。
  検査 `grpF es D`（Bool）、主定理 `no_three_two_URTM_F`（`isExcF = isExcE && !grpF`）。例外は高々 576 表。
-/
import URTMMeta.ThreeE

namespace URTM.Meta
open URTM URTM.TwoState URTM.Three

/-! ### 1 歩の補題 -/

theorem qrun_oneR {tbl : List Quint} {st s : Nat} {pos : Int} {tape : Int → Nat} {t' q : Nat}
    (hs : tape pos = s) (h : find? tbl st s = some ⟨st, s, t', Dir.R, q⟩) :
    qrun tbl 1 ⟨st, pos, tape⟩ = some ⟨q, pos + 1, write tape pos t'⟩ := by
  rw [qrun_succ_some tbl 0 (qstep_of_find (c := ⟨st, pos, tape⟩) (by simp only; rw [hs]; exact h))]; rfl

theorem qrun_comp {tbl : List Quint} {a b : Nat} {x y z : QConf} (h1 : qrun tbl a x = some y)
    (h2 : qrun tbl b y = some z) : qrun tbl (a + b) x = some z := by
  rw [qrun_add, h1]; exact h2

theorem exists_first_zero (t : Int → Nat) (p : Int) (L : Nat) (h2 : ∀ x, t x < 2) (hL : t (p + L) = 0) :
    ∃ j, j ≤ L ∧ (∀ k : Nat, k < j → t (p + k) = 1) ∧ t (p + j) = 0 := by
  classical
  have hex : ∃ j : Nat, t (p + j) = 0 := ⟨L, hL⟩
  refine ⟨Nat.find hex, Nat.find_min' hex hL, fun k hk => ?_, Nat.find_spec hex⟩
  have h1 := Nat.find_min hex hk
  have h3 := h2 (p + k)
  omega

theorem lead1_spec {P : Nat → Nat} {L : Nat} (h2 : ∀ k, P k < 2) (hL : P L = 0) :
    lead1 P ≤ L ∧ (∀ k, k < lead1 P → P k = 1) ∧ P (lead1 P) = 0 := by
  classical
  have hex : ∃ j, P j ≠ 1 := ⟨L, by rw [hL]; decide⟩
  have e : lead1 P = Nat.find hex := by unfold lead1; rw [dif_pos hex]
  rw [e]
  refine ⟨Nat.find_min' hex (by rw [hL]; decide), fun k hk => ?_, ?_⟩
  · have := Nat.find_min hex hk
    simpa using this
  · have h1 := Nat.find_spec hex
    have h3 := h2 (Nat.find hex)
    omega

/-! ### e の訪問（2 進カウンタ） -/

/-- 中身に 1 を足す: pos から j マスの 1 を 0 に、pos + j を 1 に。 -/
def incT (t : Int → Nat) (pos : Int) (j : Nat) (x : Int) : Nat :=
  if pos ≤ x ∧ x < pos + j then 0 else if x = pos + j then 1 else t x

/-- **e の訪問**: 中身 1^j 0 … に e で入ると、2j+1 歩で r・位置 pos − 1 に戻り、中身は 0^j 1 …。 -/
theorem visit_cnt {tbl : List Quint} {e r w : Nat} (h1 : find? tbl e 1 = some ⟨e, 1, w, Dir.R, e⟩)
    (h0 : find? tbl e 0 = some ⟨e, 0, 1, Dir.L, r⟩) (hr : find? tbl r w = some ⟨r, w, 0, Dir.L, r⟩)
    (pos : Int) (tape : Int → Nat) (j : Nat)
    (h1s : ∀ k : Nat, k < j → tape (pos + k) = 1) (h0s : tape (pos + j) = 0) :
    qrun tbl (2 * j + 1) ⟨e, pos, tape⟩ = some ⟨r, pos - 1, incT tape pos j⟩ := by
  rw [show 2 * j + 1 = j + (j + 1) by omega, qrun_add, sweepR h1 pos tape j h1s]
  simp only [Option.bind_some]
  have hread : (if pos ≤ pos + (j : Int) ∧ pos + (j : Int) < pos + j then w else tape (pos + j)) = 0 := by
    rw [if_neg (by omega)]; exact h0s
  rw [qrun_succ_some tbl _ (qstep_of_find (by simp only; rw [hread]; exact h0))]
  simp only [move]
  rw [sweepL hr (pos + j - 1) _ j (fun k hk => by simp only [write]; split_ifs <;> first | rfl | omega)]
  simp only [Option.some.injEq, QConf.mk.injEq, true_and]
  refine ⟨by omega, ?_⟩
  funext x; simp only [write, incT]; split_ifs <;> first | rfl | omega

/-! ### 2 進数として読む -/

/-- 位置 c から右 L マスを、下位桁が先の 2 進数として読む。 -/
def bval (t : Int → Nat) (c : Int) : Nat → Nat
  | 0 => 0
  | L + 1 => t c + 2 * bval t (c + 1) L

theorem bval_congr {t t' : Int → Nat} : ∀ (L : Nat) (c c' : Int),
    (∀ k : Nat, k < L → t (c + k) = t' (c' + k)) → bval t c L = bval t' c' L
  | 0, _, _, _ => rfl
  | L + 1, c, c', h => by
    show t c + 2 * bval t (c + 1) L = t' c' + 2 * bval t' (c' + 1) L
    have h0 : t c = t' c' := by simpa using h 0 (by omega)
    rw [h0, bval_congr L (c + 1) (c' + 1) (fun k hk => by
      have := h (k + 1) (by omega)
      rw [show c + 1 + (k : Int) = c + ((k + 1 : Nat) : Int) by push_cast; omega,
        show c' + 1 + (k : Int) = c' + ((k + 1 : Nat) : Int) by push_cast; omega]
      exact this)]

theorem bval_zero_top {t : Int → Nat} : ∀ (L : Nat) (c : Int), t (c + L) = 0 → bval t c (L + 1) = bval t c L
  | 0, c, h => by
    show t c + 2 * 0 = 0
    have : t c = 0 := by simpa using h
    omega
  | L + 1, c, h => by
    show t c + 2 * bval t (c + 1) (L + 1) = t c + 2 * bval t (c + 1) L
    rw [bval_zero_top L (c + 1) (by
      rw [show c + 1 + (L : Int) = c + ((L + 1 : Nat) : Int) by push_cast; omega]; exact h)]

theorem bval_lt {t : Int → Nat} (h2 : ∀ x, t x < 2) : ∀ (L : Nat) (c : Int), bval t c L < 2 ^ L
  | 0, _ => by show 0 < 2 ^ 0; simp
  | L + 1, c => by
    show t c + 2 * bval t (c + 1) L < 2 ^ (L + 1)
    have h1 := bval_lt h2 L (c + 1)
    have h3 := h2 c
    rw [Nat.pow_succ]; generalize 2 ^ L = P at h1 ⊢; omega

theorem bval_mod {t : Int → Nat} {c : Int} {L : Nat} (h2 : t c < 2) :
    bval t c (L + 1) % 2 = t c ∧ bval t c (L + 1) / 2 = bval t (c + 1) L := by
  show (t c + 2 * bval t (c + 1) L) % 2 = t c ∧ (t c + 2 * bval t (c + 1) L) / 2 = bval t (c + 1) L
  omega

/-- **1 を足すと値は 1 増える**。 -/
theorem bval_inc {t : Int → Nat} : ∀ (j L : Nat) (c : Int), j < L → (∀ k : Nat, k < j → t (c + k) = 1) →
    t (c + j) = 0 → bval (incT t c j) c L = bval t c L + 1
  | 0, L + 1, c, _, _, h0 => by
    show incT t c 0 c + 2 * bval (incT t c 0) (c + 1) L = t c + 2 * bval t (c + 1) L + 1
    have ht0 : t c = 0 := by simpa using h0
    have hi : incT t c 0 c = 1 := by unfold incT; simp
    rw [hi, ht0, bval_congr L (c + 1) (c + 1) (fun k _ => by
      unfold incT; rw [if_neg (by omega), if_neg (by omega)])]
    omega
  | j + 1, L + 1, c, hjL, h1s, h0 => by
    show incT t c (j + 1) c + 2 * bval (incT t c (j + 1)) (c + 1) L = t c + 2 * bval t (c + 1) L + 1
    have ht1 : t c = 1 := by simpa using h1s 0 (by omega)
    have hi : incT t c (j + 1) c = 0 := by unfold incT; rw [if_pos (by omega)]
    have hcg : bval (incT t c (j + 1)) (c + 1) L = bval (incT t (c + 1) j) (c + 1) L :=
      bval_congr L (c + 1) (c + 1) (fun k _ => by
        unfold incT; split_ifs <;> first | rfl | omega)
    rw [hi, ht1, hcg, bval_inc j L (c + 1) (by omega) (fun k hk => by
        rw [show c + 1 + (k : Int) = c + ((k + 1 : Nat) : Int) by push_cast; omega]
        exact h1s (k + 1) (by omega))
      (by rw [show c + 1 + (j : Int) = c + ((j + 1 : Nat) : Int) by push_cast; omega]; exact h0)]
    omega
  | _, 0, _, h, _, _ => absurd h (Nat.not_lt_zero _)

/-! ### z の訪問 -/

/-- 右側の規則: 2 進カウンタ e（戻り r）と、戻らない入り口 z。 -/
structure ZRules (tbl : List Quint) (e z r w h y' : Nat) : Prop where
  h1 : find? tbl e 1 = some ⟨e, 1, w, Dir.R, e⟩
  h0 : find? tbl e 0 = some ⟨e, 0, 1, Dir.L, r⟩
  hr : find? tbl r w = some ⟨r, w, 0, Dir.L, r⟩
  hzh : find? tbl z h = none
  hz : find? tbl z (1 - h) = some ⟨z, 1 - h, 1 - w, Dir.R, e⟩
  hry : find? tbl r (1 - w) = some ⟨r, 1 - w, y', Dir.R, z⟩
  hent : ∀ ρ ∈ tbl, ρ.d = Dir.R → ρ.q ∈ [e, z]
  hh : h < 2
  hy : y' < 2

section zrun
variable {tbl : List Quint} {e z r w h y' : Nat} (Z : ZRules tbl e z r w h y')
include Z

/-- **z の 1 歩**: z の位置の記号が 1 − h なら、2j+3 歩で 1 つ右の z に移り、右の中身に 1 を足す。 -/
theorem zmacro (c : Int) (t : Int → Nat) (j : Nat)
    (hx : t c = 1 - h) (h1s : ∀ k : Nat, k < j → t (c + 1 + k) = 1) (h0s : t (c + 1 + j) = 0) :
    qrun tbl (2 * j + 3) ⟨z, c, t⟩ =
      some ⟨z, c + 1, write (incT (write t c (1 - w)) (c + 1) j) c y'⟩ := by
  have hs1 := qrun_oneR (tape := t) (pos := c) hx Z.hz
  have hv := visit_cnt Z.h1 Z.h0 Z.hr (c + 1) (write t c (1 - w)) j
    (fun k hk => by simp only [write]; rw [if_neg (by omega)]; exact h1s k hk)
    (by simp only [write]; rw [if_neg (by omega)]; exact h0s)
  have hread : incT (write t c (1 - w)) (c + 1) j (c + 1 - 1) = 1 - w := by
    unfold incT; rw [if_neg (by omega), if_neg (by omega)]; simp only [write]; rw [if_pos (by omega)]
  have hs3 := qrun_oneR (tape := incT (write t c (1 - w)) (c + 1) j) (pos := c + 1 - 1) hread Z.hry
  have := qrun_comp (qrun_comp hs1 hv) hs3
  rw [show c + 1 - 1 = c by omega] at this
  rw [show 2 * j + 3 = 1 + (2 * j + 1) + 1 by omega]
  exact this

/-- z の 1 歩の後: 中身の長さは L のまま、値は ⌊N/2⌋ + 1。 -/
theorem zmstep {c : Int} {t : Int → Nat} {L : Nat} (hL : 1 ≤ L) (h2 : ∀ x, t x < 2)
    (hs : ∀ k : Nat, L ≤ k → t (c + k) = 0) (hx : t c = 1 - h) :
    ∃ j t', j + 1 ≤ L ∧ qrun tbl (2 * j + 3) ⟨z, c, t⟩ = some ⟨z, c + 1, t'⟩ ∧ (∀ x, t' x < 2) ∧
      (∀ k : Nat, L ≤ k → t' (c + 1 + k) = 0) ∧ bval t' (c + 1) L = bval t c L / 2 + 1 := by
  obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
  have htop : t (c + 1 + L') = 0 := by
    rw [show c + 1 + (L' : Int) = c + ((L' + 1 : Nat) : Int) by push_cast; omega]; exact hs _ le_rfl
  obtain ⟨j, hjL, h1s, h0s⟩ := exists_first_zero t (c + 1) L' h2 htop
  refine ⟨j, write (incT (write t c (1 - w)) (c + 1) j) c y', by omega, zmacro Z c t j hx h1s h0s, ?_, ?_, ?_⟩
  · intro x; simp only [write, incT]; split_ifs <;> first | omega | exact Z.hy | exact h2 x
  · intro k hk
    simp only [write, incT]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    rw [show c + 1 + (k : Int) = c + ((k + 1 : Nat) : Int) by push_cast; omega]; exact hs _ (by omega)
  · have hcg : bval (write (incT (write t c (1 - w)) (c + 1) j) c y') (c + 1) (L' + 1) =
        bval (incT t (c + 1) j) (c + 1) (L' + 1) :=
      bval_congr _ _ _ (fun k _ => by simp only [write, incT]; split_ifs <;> first | rfl | omega)
    rw [hcg, bval_inc j (L' + 1) (c + 1) (by omega) h1s h0s, bval_zero_top L' (c + 1) htop,
      (bval_mod (L := L') (h2 c)).2]

/-- **不動点では止まらない**: ⌊N/2⌋ + 1 = N で N の偶奇が 1 − h なら、z の訪問は止まらない。 -/
theorem znohalt {L N : Nat} (hL : 1 ≤ L) (hfix : N / 2 + 1 = N) (hpar : N % 2 = 1 - h) :
    ∀ (n : Nat) (c : Int) (t : Int → Nat), (∀ x, t x < 2) → (∀ k : Nat, L ≤ k → t (c + k) = 0) →
      bval t c L = N → qrun tbl n ⟨z, c, t⟩ ≠ none := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro c t h2 hs hv
    obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
    have hx : t c = 1 - h := by have := (bval_mod (L := L') (h2 c)).1; omega
    obtain ⟨j, t', -, hrun, h2', hs', hv'⟩ := zmstep Z hL h2 hs hx
    by_cases hn : n ≤ 2 * j + 3
    · intro hnone
      have := qrun_none_mono tbl _ _ _ hnone hn
      rw [hrun] at this; cases this
    · obtain ⟨m, rfl⟩ : ∃ m, n = 2 * j + 3 + m := ⟨n - (2 * j + 3), by omega⟩
      rw [qrun_add, hrun]
      exact ih m (by omega) (c + 1) t' h2' hs' (by rw [hv', hv, hfix])

/-- **z の訪問は、止まるなら (N + 2)(2L + 3) 歩以内に止まる**（N は z の位置から右の値）。 -/
theorem zhbound {L : Nat} (hL : 1 ≤ L) :
    ∀ (N : Nat) (c : Int) (t : Int → Nat), (∀ x, t x < 2) → (∀ k : Nat, L ≤ k → t (c + k) = 0) →
      bval t c L = N → QHalts tbl ⟨z, c, t⟩ → qrun tbl ((N + 2) * (2 * L + 3)) ⟨z, c, t⟩ = none := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro c t h2 hs hv hH
    have hb1 : 0 < (N + 2) * (2 * L + 3) := Nat.mul_pos (by omega) (by omega)
    by_cases hxh : t c = h
    · exact qrun_none_mono tbl _ 1 _ (qrun_succ_none tbl 0 (qstep_none_at hxh Z.hzh)) hb1
    · have hx : t c = 1 - h := by have := h2 c; have := Z.hh; omega
      obtain ⟨j, t', hj, hrun, h2', hs', hv'⟩ := zmstep Z hL h2 hs hx
      have hH' : QHalts tbl ⟨z, c + 1, t'⟩ := by
        obtain ⟨n, hn⟩ := hH
        by_cases hn' : n ≤ 2 * j + 3
        · have := qrun_none_mono tbl _ _ _ hn hn'; rw [hrun] at this; cases this
        · obtain ⟨m, rfl⟩ : ∃ m, n = 2 * j + 3 + m := ⟨n - (2 * j + 3), by omega⟩
          refine ⟨m, ?_⟩
          rw [qrun_add, hrun] at hn; exact hn
      have hN' : bval t' (c + 1) L = N / 2 + 1 := by rw [hv', hv]
      by_cases hlt : N / 2 + 1 < N
      · have hrec := ih (N / 2 + 1) hlt (c + 1) t' h2' hs' hN' hH'
        have hle : (N / 2 + 1 + 2) * (2 * L + 3) ≤ (N + 1) * (2 * L + 3) := Nat.mul_le_mul_right _ (by omega)
        have hsplit : (N + 2) * (2 * L + 3) = (N + 1) * (2 * L + 3) + (2 * L + 3) := by
          rw [show N + 2 = (N + 1) + 1 by omega, Nat.add_mul, Nat.one_mul]
        have hrun2 : qrun tbl (2 * j + 3 + (N / 2 + 1 + 2) * (2 * L + 3)) ⟨z, c, t⟩ = none := by
          rw [qrun_add, hrun]; exact hrec
        exact qrun_none_mono tbl _ _ _ hrun2 (by omega)
      · obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
        have hm := (bval_mod (L := L') (h2 c)).1
        by_cases hfix : N / 2 + 1 = N
        · exfalso
          have hpar : N % 2 = 1 - h := by omega
          obtain ⟨n, hn⟩ := hH
          exact znohalt Z hL hfix hpar n c t h2 hs hv hn
        · -- N = 0: 次の 1 歩で止まる
          have hN0 : N = 0 := by omega
          subst hN0
          have hh1 : h = 1 := by have := Z.hh; omega
          have ht1 : t' (c + 1) = h := by have := (bval_mod (L := L') (h2' (c + 1))).1; omega
          have hrun2 : qrun tbl (2 * j + 3 + 1) ⟨z, c, t⟩ = none := by
            rw [qrun_add, hrun]; exact qrun_succ_none tbl 0 (qstep_none_at ht1 Z.hzh)
          exact qrun_none_mono tbl _ _ _ hrun2 (by omega)

end zrun

/-! ### `RSide` に載せる -/

/-- 行き先: e なら r で戻る（類は 1 つ）、z なら戻らない。 -/
def zout (e r e' _a : Nat) : Option (Nat × Nat) := if e' = e then some (r, 0) else none

/-- 戻る訪問の歩数（e なら 2j+1）。 -/
noncomputable def zvl (e e' : Nat) (P : Nat → Nat) : Nat := if e' = e then 2 * lead1 P + 1 else 0

def zg (L : Nat) : Nat := (2 ^ (L + 1) + 1) * (2 * L + 5)

theorem zg_mono (i j : Nat) (h : i ≤ j) : zg i ≤ zg j := by
  unfold zg
  have : 2 ^ (i + 1) ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  exact Nat.mul_le_mul (Nat.add_le_add_right this 1) (by omega)

/-- **2 進カウンタと戻らない入り口は `RSide`**。 -/
theorem z_rside {tbl : List Quint} {e z r w h y' : Nat} (Z : ZRules tbl e z r w h y') :
    RSide tbl [e, z] (fun _ => True) (fun _ => 0) 1 (zvl e) (zout e r) zg where
  hent := Z.hent
  inv0 := trivial
  cls_lt := fun _ _ => by omega
  gmono := zg_mono
  ret := by
    intro e' _ b t L q a' ho _ hsupp h2
    by_cases hee : e' = e
    · rw [hee] at ho ⊢
      have ho' : ∀ a, zout e r e a = some (r, 0) := fun a => by unfold zout; rw [if_pos rfl]
      rw [ho'] at ho
      obtain ⟨hq, ha⟩ := Prod.mk.inj (Option.some.inj ho)
      rw [← hq, ← ha]
      have hP2 : ∀ k, rpart b t k < 2 := fun k => h2 _
      obtain ⟨hjL, h1s, h0s⟩ := lead1_spec hP2 (hsupp L le_rfl)
      have hvl : zvl e e (rpart b t) = 2 * lead1 (rpart b t) + 1 := by unfold zvl; rw [if_pos rfl]
      rw [hvl]
      refine ⟨?_, incT t (b + 1) (lead1 (rpart b t)), ?_, ?_, trivial, rfl, ?_⟩
      · unfold zg
        have := Nat.mul_le_mul (Nat.le_add_left 1 (2 ^ (L + 1))) (le_refl (2 * L + 5))
        generalize (2 ^ (L + 1) + 1) * (2 * L + 5) = X at this ⊢
        omega
      · rw [visit_cnt Z.h1 Z.h0 Z.hr (b + 1) t _ h1s h0s, show b + 1 - 1 = b by omega]
      · intro x hx; unfold incT; rw [if_neg (by omega), if_neg (by omega)]
      · intro k hk
        show incT t (b + 1) (lead1 (rpart b t)) (b + 1 + k) = 0
        unfold incT; rw [if_neg (by omega), if_neg (by omega)]; exact hsupp k (by omega)
    · exfalso
      unfold zout at ho; rw [if_neg hee] at ho; cases ho
  fin := by
    intro e' he' b t L ho _ hsupp h2 hH
    have hee : e' ≠ e := by intro h; rw [h] at ho; unfold zout at ho; rw [if_pos rfl] at ho; cases ho
    have hez : e' = z := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he'
      rcases he' with h | h
      · exact absurd h hee
      · exact h
    rw [hez] at hH ⊢
    have hb := zhbound Z (L := L + 1) (by omega) (bval t (b + 1) (L + 1)) (b + 1) t h2
      (fun k hk => hsupp k (by omega)) rfl hH
    have hlt := bval_lt h2 (L + 1) (b + 1)
    refine qrun_none_mono tbl _ _ _ hb ?_
    unfold zg
    generalize 2 ^ (L + 1) = P at hlt ⊢
    exact Nat.mul_le_mul (by omega) (by omega)

/-! ### Bool の検査 -/

/-- 右側の規則（Bool）。 -/
def zcR (tbl : List Quint) (e z r w h y' : Nat) : Bool :=
  find? tbl e 1 == some ⟨e, 1, w, Dir.R, e⟩ && find? tbl e 0 == some ⟨e, 0, 1, Dir.L, r⟩ &&
  find? tbl r w == some ⟨r, w, 0, Dir.L, r⟩ && find? tbl z h == none &&
  find? tbl z (1 - h) == some ⟨z, 1 - h, 1 - w, Dir.R, e⟩ &&
  find? tbl r (1 - w) == some ⟨r, 1 - w, y', Dir.R, z⟩ &&
  (entR tbl).all (fun q => q == e || q == z)

theorem zcR_spec {tbl : List Quint} {e z r w h y' : Nat} (hh : h < 2) (hy : y' < 2)
    (hc : zcR tbl e z r w h y' = true) : ZRules tbl e z r w h y' := by
  unfold zcR at hc
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨h1, h0⟩, hr⟩, hzh⟩, hz⟩, hry⟩, hent⟩ := hc
  refine ⟨h1, h0, hr, hzh, hz, hry, fun ρ hρ hd => ?_, hh, hy⟩
  have := hent ρ.q (mem_entR hρ hd)
  simpa using this

/-- 右が 2 進カウンタと戻らない入り口で、左に段階 1 の証明書が立つ。 -/
def sideF (tbl : List Quint) : Bool := checkR (mirTbl tbl) &&
  (List.range 3).any fun e => (List.range 3).any fun z => (List.range 3).any fun r =>
    (List.range 2).any fun w => (List.range 2).any fun h => (List.range 2).any fun y' =>
      zcR tbl e z r w h y'

/-- **群 D の「2 進カウンタと戻らない入り口」8 類の検査**: 表か、その鏡像が `sideF`。 -/
def grpF (es : List Nat) (D : List Dir) : Bool :=
  sideF (URTM.Three.realize es D) || sideF (mirTbl (URTM.Three.realize es D))

/-- 段階 2e の 2 の例外: `isExcE` の表のうち、この 8 類に当たらない表。 -/
def isExcF (es : List Nat) (D : List Dir) : Bool := isExcE es D && !grpF es D

theorem sideF_bound {tbl : List Quint} (hsrc : Src3 tbl) (hcl : QClosed tbl 2) (hdir : DirConsistent tbl)
    (h : sideF tbl = true) :
    ∃ ML : Nat, ∀ (c : QConf) (a b : Int), a ≤ c.pos → c.pos ≤ b →
      (∀ x, (x < a ∨ b < x) → c.tape x = 0) → (∀ x, c.tape x < 2) →
      (QHalts tbl c ↔ qrun tbl (boundE 1 zg ML a b) c = none) := by
  unfold sideF at h
  obtain ⟨hL, hc⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨CL, ML, hLc⟩ := checkR_spec hL
  obtain ⟨e, -, hc⟩ := List.any_eq_true.mp hc
  obtain ⟨z, -, hc⟩ := List.any_eq_true.mp hc
  obtain ⟨r, -, hc⟩ := List.any_eq_true.mp hc
  obtain ⟨w, -, hc⟩ := List.any_eq_true.mp hc
  obtain ⟨h, hh, hc⟩ := List.any_eq_true.mp hc
  obtain ⟨y', hy, hc⟩ := List.any_eq_true.mp hc
  exact ⟨ML, fun c a b ha hb hz h2 => halts_iff_boundE hsrc hcl hdir
    (z_rside (zcR_spec (List.mem_range.mp hh) (List.mem_range.mp hy) hc)) hLc c a b ha hb hz h2⟩

theorem sideF_mir_bound {tbl : List Quint} (hsrc : Src3 tbl) (hcl : QClosed tbl 2) (hdir : DirConsistent tbl)
    (h : sideF (mirTbl tbl) = true) :
    ∃ ML : Nat, ∀ (c : QConf) (a b : Int), a ≤ c.pos → c.pos ≤ b →
      (∀ x, (x < a ∨ b < x) → c.tape x = 0) → (∀ x, c.tape x < 2) →
      (QHalts tbl c ↔ qrun tbl (boundE 1 zg ML a b) c = none) := by
  rw [mirTbl_eq] at h
  obtain ⟨ML, hb⟩ := sideF_bound (src3_mir hsrc) (closed_mir hcl) (dirConsistent_mir hdir) h
  refine ⟨ML, fun c a b ha hb' hz h2 => ?_⟩
  have := hb (mirQ c) (-b) (-a) (by show -b ≤ -c.pos; omega) (by show -c.pos ≤ -a; omega)
    (fun x hx => by show c.tape (-x) = 0; exact hz (-x) (by omega)) (fun x => h2 (-x))
  rw [QHalts_mir, qrun_mir] at this
  have e : boundE 1 zg ML (-b) (-a) = boundE 1 zg ML a b := by
    unfold boundE; rw [show -a - (-b - (ML : Int)) + 1 = b - (a - ML) + 1 by omega]
  rw [e] at this
  rw [this]
  cases qrun tbl (boundE 1 zg ML a b) c <;> simp

/-- 窓の幅で書いた上界。 -/
def bndF (ML w : Nat) : Nat :=
  csize 2 (w + ML + 1) * 1 * (zg (csize 2 (w + ML + 1) * 1) + 2) + zg (csize 2 (w + ML + 1) * 1) + 1

theorem zg_primrec : Primrec zg := by
  have h := Primrec.nat_mul.comp
    (Primrec.nat_add.comp (pow_primrec.comp (Primrec.const 2)
      (Primrec.nat_add.comp Primrec.id (Primrec.const 1))) (Primrec.const 1))
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id) (Primrec.const 5))
  exact h.of_eq fun L => rfl

theorem bndF_primrec (ML : Nat) : Primrec (bndF ML) := by
  have hK : Primrec fun w => csize 2 (w + ML + 1) * 1 :=
    Primrec.nat_mul.comp (csize_primrec.comp (Primrec.const 2)
      (Primrec.nat_add.comp (Primrec.nat_add.comp Primrec.id (Primrec.const ML)) (Primrec.const 1)))
      (Primrec.const 1)
  have hg : Primrec fun w => zg (csize 2 (w + ML + 1) * 1) := zg_primrec.comp hK
  exact (Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.nat_mul.comp hK
    (Primrec.nat_add.comp hg (Primrec.const 2))) hg) (Primrec.const 1)).of_eq fun w => rfl

theorem boundF_eq (ML m n : Nat) : boundE 1 zg ML (-(m : Int)) (n : Int) = bndF ML (m + n) := by
  unfold boundE bndF
  rw [show ((n : Int) - (-(m : Int) - ML) + 1).toNat = m + n + ML + 1 by omega]

section
variable {tbl : List Quint} {q₀ q₁ q₂ sg : Nat}

/-- **8 類の有界停止**（任意の表の正規形）。 -/
theorem okF_bound (H : RTM32 tbl q₀ q₁ q₂ sg)
    (hok : grpF (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl) = true) :
    ∃ ML : Nat, ∀ (c : QConf) (m n : ℕ), -(m : ℤ) ≤ c.pos → c.pos ≤ (n : ℤ) →
      (∀ x, (x < -(m : ℤ) ∨ (n : ℤ) < x) → c.tape x = 0) → (∀ x, c.tape x < 2) →
      (QHalts (normT (tbl := tbl) (q₀ := q₀) (q₁ := q₁) (q₂ := q₂) (σ := sg)) c ↔
        qrun (normT (tbl := tbl) (q₀ := q₀) (q₁ := q₁) (q₂ := q₂) (σ := sg)) (bndF ML (m + n)) c = none) := by
  have hsrc := realize_src3 (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl)
  have hcl := realize_closed (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl)
  have hdir := realize_dir (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl)
  unfold grpF at hok
  obtain ⟨ML, hb⟩ : ∃ ML : Nat, ∀ (c : QConf) (a b : Int), a ≤ c.pos → c.pos ≤ b →
      (∀ x, (x < a ∨ b < x) → c.tape x = 0) → (∀ x, c.tape x < 2) →
      (QHalts (URTM.Three.realize (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl)) c ↔
        qrun (URTM.Three.realize (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl)) (boundE 1 zg ML a b) c
          = none) := by
    rcases Bool.or_eq_true_iff.mp hok with h | h
    · exact sideF_bound hsrc hcl hdir h
    · exact sideF_mir_bound hsrc hcl hdir h
  refine ⟨ML, fun c m n ha hb' hz h2 => ?_⟩
  rw [← boundF_eq]
  exact hb c _ _ ha hb' hz h2

/-- **3 状態 2 記号の RTM の停止問題は、U の ID の上で計算可能**（`isExcF` の表を除く）。 -/
theorem three_halting_computable_F (H : RTM32 tbl q₀ q₁ q₂ sg)
    (hne : isExcF (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl) = false) :
    ∃ f : ZID → Bool, Computable f ∧
      ∀ z, (∀ a ∈ z.2.1 ++ z.2.2, a = 0 ∨ a ∈ [sg]) → (ZHalts tbl z ↔ f z = true) := by
  cases hE : isExcE (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl) with
  | false => exact three_halting_computable_E H hE
  | true =>
    have hF : grpF (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl) = true := by
      unfold isExcF at hne; rw [hE] at hne; simpa using hne
    obtain ⟨ML, hb⟩ := okF_bound H hF
    exact halting_computable_of_bound H (bndF_primrec ML) hb

/-- **定理（段階 2e の 2）: `isExcF` の表を除き、3 状態 2 記号の URTM は存在しない**（Morita Def. 7.1、
    U の記号集合 {0, sg} の上の ID への符号化）。 -/
theorem no_three_two_URTM_F (H : RTM32 tbl q₀ q₁ q₂ sg)
    (hne : isExcF (absCodes q₀ q₁ q₂ sg tbl) (absDirs q₀ q₁ q₂ tbl) = false) :
    ¬ IsUTM_MoritaOver tbl [sg] :=
  not_UTM_of_halting_computable (three_halting_computable_F H hne)

end

/-! ### 残る例外の数

段階 2e の例外の上界 672 表（`excEKeys`）のうち、`grpF` に当たる 96 表（8 類）の鍵を一覧 `f96Keys` に書き、
それらが `grpF` に当たることを kernel で確かめる。残る例外はその外の 576 表に**含まれる**（上界）。 -/

/-- `grpF` に当たる 96 表の鍵（Python で類から生成。下の `f96_grpF` が kernel で検査する）。 -/
def f96Keys : List Nat := [
  243983, 243984, 246065, 246072, 287201, 287202, 303689, 303696, 324451, 324458, 326215, 326222,
  341197, 341198, 342667, 342668, 709587, 709636, 712569, 712912, 723993, 724042, 741381, 741724,
  800029, 800065, 800372, 800408, 817423, 817453, 817472, 817502, 971331, 971355, 988138, 988162,
  1003729, 1004317, 1020536, 1021124, 1029297, 1029315, 1031698, 1031716, 1032499, 1032793, 1034900, 1035194,
  2147821, 2147845, 2164628, 2164652, 2180219, 2180807, 2197026, 2197614, 2205787, 2205805, 2208188, 2208206,
  2208989, 2209283, 2211390, 2211684, 2356673, 2356722, 2359655, 2359998, 2371079, 2371128, 2388467, 2388810,
  2447115, 2447151, 2447458, 2447494, 2464509, 2464539, 2464558, 2464588, 2832261, 2832262, 2834343, 2834350,
  2875479, 2875480, 2891967, 2891974, 2912729, 2912736, 2914493, 2914500, 2929475, 2929476, 2930945, 2930946
]

theorem f96_grpF : f96Keys.all (fun k => grpF (unkey k).1 (unkey k).2) = true := by decide +kernel

theorem f96_sub : f96Keys.all (fun k => excEKeys.contains k) = true := by decide +kernel

/-- 段階 2e の 2 の例外の鍵（の上界）。 -/
def excFKeys : List Nat := excEKeys.filter fun k => !f96Keys.contains k

/-- **段階 2e の 2 の例外の表（の上界）の一覧**。 -/
def excFTables : List (List Nat × List Dir) := excFKeys.map unkey

/-- **主定理の仮定が外れる表は一覧に載る**（符号 6 つ・向き 3 つの表について）。 -/
theorem mem_excFTables {es : List Nat} {D : List Dir} (h : ValidKey es D) (hx : isExcF es D = true) :
    (es, D) ∈ excFTables := by
  unfold isExcF at hx
  obtain ⟨hE, hF⟩ := Bool.and_eq_true_iff.mp hx
  obtain ⟨k, hk, he⟩ := List.mem_map.mp (mem_excETables h hE)
  refine List.mem_map.mpr ⟨k, List.mem_filter.mpr ⟨hk, ?_⟩, he⟩
  cases hc : f96Keys.contains k
  · rfl
  · exfalso
    have := List.all_eq_true.mp f96_grpF k (List.contains_iff_mem.mp hc)
    rw [he] at this
    simp only [this, Bool.not_true] at hF
    exact Bool.false_ne_true hF

/-- **段階 2e の 2 の例外は高々 576 表**（672 − 96。kernel の評価）。 -/
theorem excFKeys_length : excFKeys.length = 576 := by decide +kernel

theorem excFTables_length : excFTables.length = 576 := by
  unfold excFTables; rw [List.length_map, excFKeys_length]

end URTM.Meta
