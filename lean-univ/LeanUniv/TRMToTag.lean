/-
  **TRM → 2-TS** (docs/24 §2 L2, piece P4): a Cocke–Minsky-style simulation of the
  two-register machine (`LeanUniv/TRM.lean`) by a 2-tag system (`LeanUniv/Tag2.lean`), as an
  instance of the `ExactSim` calculus.

  * Symbols. Fillers `x = 0`, `y = 1`, `z = 2`; the symbol of kind `κ < 18` for label `i` is
    `sym i κ = 3 + 18·i + κ`. (docs/24 says "`2 + 16·i + κ` for 16 kinds κ, plus fillers x, y,
    z"; that text is inconsistent — three fillers do not fit below 2, and `half1` needs
    4 + 14 = 18 kinds — so the numbering here is the closest consistent reading.)
    Kinds: `A 0, a 1, B 2, b 3`; for `half1`: `G 4, h 5, K 6, L 7, c 8, d 9, P 10, Q 11, r 12,
    s 13, k 14, e 15, l 16, f 17`; for `half2`: `G 4, g 5, K 6, h 7, P 8, Q 9, r 10, s 11,
    k₁ 12, k₂ 13, t 14, u 15`.
  * Canonical word `W i X Y = A_i x (a_i x)^X B_i x (b_i x)^Y` (the encoder `enc`).
  * Productions `tagP prog`: the gadget table of docs/24 §2 L2, verbatim.
  * Decoder `dec`: reads the label from the first symbol, the registers by counting, and
    checks that the word is canonical.

  Main results: the four gadget lemmas (`gadget_dbl1`, `gadget_dbl2`, `gadget_half1`,
  `gadget_half2`, each as a chain of `Tag2.pass'` sweeps, in the length-≥3 relation `LStep`),
  `exactSim : ExactSim …`, and the length invariant `reach_length` (every word reachable from
  a canonical word has length ≥ 3; hence `noShort`, the hypothesis of P3's CTSH layer).
-/
import LeanUniv.TRM
import LeanUniv.Tag2
import LeanUniv.ExactSim

namespace URTM.Univ.TRMToTag
open Relation TRM Tag2

/-! ### Symbols, productions, canonical words -/

/-- Filler symbols. -/
def xS : ℕ := 0
def yS : ℕ := 1
def zS : ℕ := 2

/-- The symbol of kind `κ` (`κ < 18`) for label `i`. -/
def sym (i κ : ℕ) : ℕ := 3 + 18 * i + κ

/-- The productions of the label-`i` symbols of kind `κ`, for the instruction at label `i`
    (docs/24 §2 L2 table). -/
def prodOf (i : ℕ) : Op → ℕ → Option (List ℕ)
  | .dbl1 b j, κ => match κ with
    | 0 => some ([sym j 0, xS] ++ rp b.toNat (sym j 1) xS)
    | 1 => some [sym j 1, xS, sym j 1, xS]
    | 2 => some [sym j 2, xS]
    | 3 => some [sym j 3, xS]
    | _ => none
  | .dbl2 b j, κ => match κ with
    | 0 => some [sym j 0, xS]
    | 1 => some [sym j 1, xS]
    | 2 => some ([sym j 2, xS] ++ rp b.toNat (sym j 3) xS)
    | 3 => some [sym j 3, xS, sym j 3, xS]
    | _ => none
  | .half1 j₀ j₁, κ => match κ with
    -- pass 1: A→G, a→h, B→K L, b→c d
    | 0 => some [sym i 4]
    | 1 => some [sym i 5]
    | 2 => some [sym i 6, sym i 7]
    | 3 => some [sym i 8, sym i 9]
    -- pass 2: G→P Q, h→r s, K→k y, c→e y, L→y l y, d→f y
    | 4 => some [sym i 10, sym i 11]
    | 5 => some [sym i 12, sym i 13]
    | 6 => some [sym i 14, yS]
    | 8 => some [sym i 15, yS]
    | 7 => some [yS, sym i 16, yS]
    | 9 => some [sym i 17, yS]
    -- pass 3: P→A_{j₁}x, Q→A_{j₀}x, r→a_{j₁}x, s→a_{j₀}x, k→B_{j₁}x, e→b_{j₁}x,
    --         l→B_{j₀}x, f→b_{j₀}x
    | 10 => some [sym j₁ 0, xS]
    | 11 => some [sym j₀ 0, xS]
    | 12 => some [sym j₁ 1, xS]
    | 13 => some [sym j₀ 1, xS]
    | 14 => some [sym j₁ 2, xS]
    | 15 => some [sym j₁ 3, xS]
    | 16 => some [sym j₀ 2, xS]
    | 17 => some [sym j₀ 3, xS]
    | _ => none
  | .half2 j₀ j₁, κ => match κ with
    -- pass 1: A→G y, a→g y, B→K, b→h
    | 0 => some [sym i 4, yS]
    | 1 => some [sym i 5, yS]
    | 2 => some [sym i 6]
    | 3 => some [sym i 7]
    -- pass 2: G→P Q, g→r s, K→k₁ k₂, h→t u
    | 4 => some [sym i 8, sym i 9]
    | 5 => some [sym i 10, sym i 11]
    | 6 => some [sym i 12, sym i 13]
    | 7 => some [sym i 14, sym i 15]
    -- pass 3: P→A_{j₁}x, r→a_{j₁}x, k₁→B_{j₁}x, t→b_{j₁}x,
    --         Q→z A_{j₀}x, s→a_{j₀}x, k₂→B_{j₀}x, u→b_{j₀}x
    | 8 => some [sym j₁ 0, xS]
    | 10 => some [sym j₁ 1, xS]
    | 12 => some [sym j₁ 2, xS]
    | 14 => some [sym j₁ 3, xS]
    | 9 => some [zS, sym j₀ 0, xS]
    | 11 => some [sym j₀ 1, xS]
    | 13 => some [sym j₀ 2, xS]
    | 15 => some [sym j₀ 3, xS]
    | _ => none

/-- The 2-TS productions of the TRM program `prog`. Fillers, symbols of halt labels and
    unused kinds are halting symbols. -/
def tagP (prog : ℕ → Option Op) (n : ℕ) : Option (List ℕ) :=
  if n < 3 then none
  else (prog ((n - 3) / 18)).bind fun op => prodOf ((n - 3) / 18) op ((n - 3) % 18)

theorem tagP_sym (prog : ℕ → Option Op) (i κ : ℕ) (hκ : κ < 18) :
    tagP prog (sym i κ) = (prog i).bind fun op => prodOf i op κ := by
  have h1 : (sym i κ - 3) / 18 = i := by unfold sym; omega
  have h2 : (sym i κ - 3) % 18 = κ := by unfold sym; omega
  have h3 : ¬ sym i κ < 3 := by unfold sym; omega
  simp only [tagP, h1, h2, h3, if_false]

/-- **Canonical word** `W i X Y = A_i x (a_i x)^X B_i x (b_i x)^Y`. -/
def W (i X Y : ℕ) : List ℕ :=
  sym i 0 :: xS :: (rp X (sym i 1) xS ++ sym i 2 :: xS :: rp Y (sym i 3) xS)

@[simp] theorem length_W (i X Y : ℕ) : (W i X Y).length = 2 * (X + Y + 1 + 1) := by
  simp [W]; omega

/-- **Encoder**: TRM configuration ↦ canonical word. -/
def enc (c : Cfg) : List ℕ := W c.1 c.2.1 c.2.2

/-- **Decoder** (exact readback): label from the first symbol, registers by counting, and a
    check that the word is canonical. -/
def dec : List ℕ → Option Cfg
  | [] => none
  | a :: w =>
    let i := (a - 3) / 18
    let X := (a :: w).count (sym i 1)
    let Y := (a :: w).count (sym i 3)
    if W i X Y = a :: w then some (i, X, Y) else none

theorem dec_W (i X Y : ℕ) : dec (W i X Y) = some (i, X, Y) := by
  have hi : (sym i 0 - 3) / 18 = i := by unfold sym; omega
  have hX : (W i X Y).count (sym i 1) = X := by
    simp only [W, List.count_cons, List.count_append, count_rp]
    simp [sym, xS]
  have hY : (W i X Y).count (sym i 3) = Y := by
    simp only [W, List.count_cons, List.count_append, count_rp]
    simp [sym, xS]
  unfold W at hX hY ⊢
  simp only [dec, hi, hX, hY]
  exact if_pos rfl

theorem dec_enc (c : Cfg) : dec (enc c) = some c := dec_W _ _ _

/-! ### The gadgets -/

section Gadgets
variable {prog : ℕ → Option Op} {i : ℕ}

/-- The four sweeps of the `half1` gadget, `X` even. -/
theorem gadget_half1_even {j₀ j₁ : ℕ} (hp : prog i = some (.half1 j₀ j₁)) (m Y : ℕ) :
    TransGen (LStep (tagP prog)) (W i (2 * m) Y) (W j₀ m Y) := by
  have hP : ∀ κ, κ < 18 → tagP prog (sym i κ) = prodOf i (.half1 j₀ j₁) κ := by
    intro κ hκ; rw [tagP_sym prog i κ hκ, hp]; rfl
  -- sweep 1: A x (a x)^{2m} B x (b x)^Y  ⇒  G h^{2m} K L (c d)^Y
  have s1 : TransGen (LStep (tagP prog)) (W i (2 * m) Y)
      (sym i 4 :: (List.replicate (2 * m) (sym i 5) ++
        sym i 6 :: sym i 7 :: rp Y (sym i 8) (sym i 9))) :=
    passAll (2 * m + Y + 1) (by simp)
      (e := sym i 0 :: (List.replicate (2 * m) (sym i 1) ++ sym i 2 ::
        List.replicate Y (sym i 3)))
      (by simp [W, xS])
      (by simp [hP, prodOf, List.mem_replicate]; aesop)
      (by simp [hP, prodOf]) (by simp; omega)
  -- sweep 2 reads G h^m: ⇒ L (c d)^Y P Q (r s)^m
  have s2 : TransGen (LStep (tagP prog))
      (sym i 4 :: (List.replicate (2 * m) (sym i 5) ++
        sym i 6 :: sym i 7 :: rp Y (sym i 8) (sym i 9)))
      (sym i 7 :: (rp Y (sym i 8) (sym i 9) ++ sym i 10 :: sym i 11 ::
        rp m (sym i 12) (sym i 13))) :=
    pass' (u := sym i 4 :: (List.replicate (2 * m) (sym i 5) ++ [sym i 6]))
      (v := sym i 7 :: rp Y (sym i 8) (sym i 9)) m (by simp) (by simp; omega)
      (e := sym i 4 :: List.replicate m (sym i 5))
      (by simp [odds_rep2_append])
      (by simp [hP, prodOf, List.mem_replicate])
      (by simp [hP, prodOf]) (by simp; omega)
  -- sweep 3 reads L d^Y: ⇒ Q (r s)^m y l y (f y)^Y
  have s3 : TransGen (LStep (tagP prog))
      (sym i 7 :: (rp Y (sym i 8) (sym i 9) ++ sym i 10 :: sym i 11 ::
        rp m (sym i 12) (sym i 13)))
      (sym i 11 :: (rp m (sym i 12) (sym i 13) ++ yS :: sym i 16 :: yS ::
        rp Y (sym i 17) yS)) :=
    pass' (u := sym i 7 :: (rp Y (sym i 8) (sym i 9) ++ [sym i 10]))
      (v := sym i 11 :: rp m (sym i 12) (sym i 13)) Y (by simp) (by simp; omega)
      (e := sym i 7 :: List.replicate Y (sym i 9))
      (by simp)
      (by simp [hP, prodOf, List.mem_replicate])
      (by simp [hP, prodOf]) (by simp; omega)
  -- sweep 4 reads Q s^m l f^Y: ⇒ A_{j₀} x (a_{j₀} x)^m B_{j₀} x (b_{j₀} x)^Y
  have s4 : TransGen (LStep (tagP prog))
      (sym i 11 :: (rp m (sym i 12) (sym i 13) ++ yS :: sym i 16 :: yS ::
        rp Y (sym i 17) yS)) (W j₀ m Y) :=
    passAll (m + Y + 1) (by simp; omega)
      (e := sym i 11 :: (List.replicate m (sym i 13) ++ sym i 16 ::
        List.replicate Y (sym i 17)))
      (by simp)
      (by simp [hP, prodOf, List.mem_replicate]; aesop)
      (by simp [hP, prodOf, W]) (by simp; omega)
  exact ((s1.trans s2).trans s3).trans s4

/-- The two sweeps of the `half1` gadget, `X` odd. -/
theorem gadget_half1_odd {j₀ j₁ : ℕ} (hp : prog i = some (.half1 j₀ j₁)) (m Y : ℕ) :
    TransGen (LStep (tagP prog)) (W i (2 * m + 1) Y) (W j₁ m Y) := by
  have hP : ∀ κ, κ < 18 → tagP prog (sym i κ) = prodOf i (.half1 j₀ j₁) κ := by
    intro κ hκ; rw [tagP_sym prog i κ hκ, hp]; rfl
  -- sweep 1: ⇒ G h^{2m+1} K L (c d)^Y
  have s1 : TransGen (LStep (tagP prog)) (W i (2 * m + 1) Y)
      (sym i 4 :: (List.replicate (2 * m + 1) (sym i 5) ++
        sym i 6 :: sym i 7 :: rp Y (sym i 8) (sym i 9))) :=
    passAll (2 * m + 1 + Y + 1) (by simp)
      (e := sym i 0 :: (List.replicate (2 * m + 1) (sym i 1) ++ sym i 2 ::
        List.replicate Y (sym i 3)))
      (by simp [W, xS])
      (by simp [hP, prodOf, List.mem_replicate])
      (by simp [hP, prodOf]) (by simp; omega)
  -- sweep 2 reads G h^m K c^Y: ⇒ P Q (r s)^m k y (e y)^Y
  have s2 : TransGen (LStep (tagP prog))
      (sym i 4 :: (List.replicate (2 * m + 1) (sym i 5) ++
        sym i 6 :: sym i 7 :: rp Y (sym i 8) (sym i 9)))
      (sym i 10 :: sym i 11 :: (rp m (sym i 12) (sym i 13) ++ sym i 14 :: yS ::
        rp Y (sym i 15) yS)) :=
    passAll (m + Y + 1) (by simp; omega)
      (e := sym i 4 :: (List.replicate m (sym i 5) ++ sym i 6 :: List.replicate Y (sym i 8)))
      (by simp [odds_rep2_succ_append])
      (by simp [hP, prodOf, List.mem_replicate]; aesop)
      (by simp [hP, prodOf]) (by simp; omega)
  -- sweep 3 reads P r^m k e^Y: ⇒ W j₁ m Y
  have s3 : TransGen (LStep (tagP prog))
      (sym i 10 :: sym i 11 :: (rp m (sym i 12) (sym i 13) ++ sym i 14 :: yS ::
        rp Y (sym i 15) yS)) (W j₁ m Y) :=
    passAll (m + Y + 1) (by simp; omega)
      (e := sym i 10 :: (List.replicate m (sym i 12) ++ sym i 14 ::
        List.replicate Y (sym i 15)))
      (by simp)
      (by simp [hP, prodOf, List.mem_replicate]; aesop)
      (by simp [hP, prodOf, W]) (by simp; omega)
  exact (s1.trans s2).trans s3

/-- The five sweeps of the `half2` gadget, `Y` even. -/
theorem gadget_half2_even {j₀ j₁ : ℕ} (hp : prog i = some (.half2 j₀ j₁)) (X m : ℕ) :
    TransGen (LStep (tagP prog)) (W i X (2 * m)) (W j₀ X m) := by
  have hP : ∀ κ, κ < 18 → tagP prog (sym i κ) = prodOf i (.half2 j₀ j₁) κ := by
    intro κ hκ; rw [tagP_sym prog i κ hκ, hp]; rfl
  -- sweep 1: ⇒ G y (g y)^X K h^{2m}
  have s1 : TransGen (LStep (tagP prog)) (W i X (2 * m))
      (sym i 4 :: yS :: (rp X (sym i 5) yS ++ sym i 6 :: List.replicate (2 * m) (sym i 7))) :=
    passAll (X + 2 * m + 1) (by simp)
      (e := sym i 0 :: (List.replicate X (sym i 1) ++ sym i 2 ::
        List.replicate (2 * m) (sym i 3)))
      (by simp [W, xS])
      (by simp [hP, prodOf, List.mem_replicate]; aesop)
      (by simp [hP, prodOf]) (by simp; omega)
  -- sweep 2 reads G g^X: ⇒ K h^{2m} P Q (r s)^X
  have s2 : TransGen (LStep (tagP prog))
      (sym i 4 :: yS :: (rp X (sym i 5) yS ++ sym i 6 :: List.replicate (2 * m) (sym i 7)))
      (sym i 6 :: (List.replicate (2 * m) (sym i 7) ++ sym i 8 :: sym i 9 ::
        rp X (sym i 10) (sym i 11))) :=
    pass' (u := sym i 4 :: yS :: rp X (sym i 5) yS)
      (v := sym i 6 :: List.replicate (2 * m) (sym i 7)) X (by simp) (by simp; omega)
      (e := sym i 4 :: List.replicate X (sym i 5))
      (by simp)
      (by simp [hP, prodOf, List.mem_replicate])
      (by simp [hP, prodOf]) (by simp; omega)
  -- sweep 3 reads K h^m: ⇒ Q (r s)^X k₁ k₂ (t u)^m
  have s3 : TransGen (LStep (tagP prog))
      (sym i 6 :: (List.replicate (2 * m) (sym i 7) ++ sym i 8 :: sym i 9 ::
        rp X (sym i 10) (sym i 11)))
      (sym i 9 :: (rp X (sym i 10) (sym i 11) ++ sym i 12 :: sym i 13 ::
        rp m (sym i 14) (sym i 15))) :=
    pass' (u := sym i 6 :: (List.replicate (2 * m) (sym i 7) ++ [sym i 8]))
      (v := sym i 9 :: rp X (sym i 10) (sym i 11)) m (by simp) (by simp; omega)
      (e := sym i 6 :: List.replicate m (sym i 7))
      (by simp [odds_rep2_append])
      (by simp [hP, prodOf, List.mem_replicate])
      (by simp [hP, prodOf]) (by simp; omega)
  -- sweep 4 reads Q s^X: ⇒ k₂ (t u)^m z A_{j₀} x (a_{j₀} x)^X
  have s4 : TransGen (LStep (tagP prog))
      (sym i 9 :: (rp X (sym i 10) (sym i 11) ++ sym i 12 :: sym i 13 ::
        rp m (sym i 14) (sym i 15)))
      (sym i 13 :: (rp m (sym i 14) (sym i 15) ++ zS :: sym j₀ 0 :: xS ::
        rp X (sym j₀ 1) xS)) :=
    pass' (u := sym i 9 :: (rp X (sym i 10) (sym i 11) ++ [sym i 12]))
      (v := sym i 13 :: rp m (sym i 14) (sym i 15)) X (by simp) (by simp; omega)
      (e := sym i 9 :: List.replicate X (sym i 11))
      (by simp)
      (by simp [hP, prodOf, List.mem_replicate])
      (by simp [hP, prodOf]) (by simp; omega)
  -- sweep 5 reads k₂ u^m (z is skipped): ⇒ W j₀ X m
  have s5 : TransGen (LStep (tagP prog))
      (sym i 13 :: (rp m (sym i 14) (sym i 15) ++ zS :: sym j₀ 0 :: xS ::
        rp X (sym j₀ 1) xS)) (W j₀ X m) :=
    pass' (u := sym i 13 :: (rp m (sym i 14) (sym i 15) ++ [zS]))
      (v := sym j₀ 0 :: xS :: rp X (sym j₀ 1) xS) m (by simp) (by simp; omega)
      (e := sym i 13 :: List.replicate m (sym i 15))
      (by simp)
      (by simp [hP, prodOf, List.mem_replicate])
      (by simp [hP, prodOf, W]) (by simp; omega)
  exact (((s1.trans s2).trans s3).trans s4).trans s5

/-- The three sweeps of the `half2` gadget, `Y` odd. -/
theorem gadget_half2_odd {j₀ j₁ : ℕ} (hp : prog i = some (.half2 j₀ j₁)) (X m : ℕ) :
    TransGen (LStep (tagP prog)) (W i X (2 * m + 1)) (W j₁ X m) := by
  have hP : ∀ κ, κ < 18 → tagP prog (sym i κ) = prodOf i (.half2 j₀ j₁) κ := by
    intro κ hκ; rw [tagP_sym prog i κ hκ, hp]; rfl
  -- sweep 1: ⇒ G y (g y)^X K h^{2m+1}
  have s1 : TransGen (LStep (tagP prog)) (W i X (2 * m + 1))
      (sym i 4 :: yS :: (rp X (sym i 5) yS ++ sym i 6 ::
        List.replicate (2 * m + 1) (sym i 7))) :=
    passAll (X + (2 * m + 1) + 1) (by simp)
      (e := sym i 0 :: (List.replicate X (sym i 1) ++ sym i 2 ::
        List.replicate (2 * m + 1) (sym i 3)))
      (by simp [W, xS])
      (by simp [hP, prodOf, List.mem_replicate]; aesop)
      (by simp [hP, prodOf]) (by simp; omega)
  -- sweep 2 reads G g^X K h^m: ⇒ P Q (r s)^X k₁ k₂ (t u)^m
  have s2 : TransGen (LStep (tagP prog))
      (sym i 4 :: yS :: (rp X (sym i 5) yS ++ sym i 6 ::
        List.replicate (2 * m + 1) (sym i 7)))
      (sym i 8 :: sym i 9 :: (rp X (sym i 10) (sym i 11) ++ sym i 12 :: sym i 13 ::
        rp m (sym i 14) (sym i 15))) :=
    passAll (X + m + 1) (by simp; omega)
      (e := sym i 4 :: (List.replicate X (sym i 5) ++ sym i 6 :: List.replicate m (sym i 7)))
      (by simp)
      (by simp [hP, prodOf, List.mem_replicate]; aesop)
      (by simp [hP, prodOf]) (by simp; omega)
  -- sweep 3 reads P r^X k₁ t^m: ⇒ W j₁ X m
  have s3 : TransGen (LStep (tagP prog))
      (sym i 8 :: sym i 9 :: (rp X (sym i 10) (sym i 11) ++ sym i 12 :: sym i 13 ::
        rp m (sym i 14) (sym i 15))) (W j₁ X m) :=
    passAll (X + m + 1) (by simp; omega)
      (e := sym i 8 :: (List.replicate X (sym i 10) ++ sym i 12 ::
        List.replicate m (sym i 14)))
      (by simp)
      (by simp [hP, prodOf, List.mem_replicate]; aesop)
      (by simp [hP, prodOf, W]) (by simp; omega)
  exact (s1.trans s2).trans s3

/-- The one-sweep `dbl1` gadget. -/
theorem gadget_dbl1 {b : Bool} {j : ℕ} (hp : prog i = some (.dbl1 b j)) (X Y : ℕ) :
    TransGen (LStep (tagP prog)) (W i X Y) (W j (2 * X + b.toNat) Y) := by
  have hP : ∀ κ, κ < 18 → tagP prog (sym i κ) = prodOf i (.dbl1 b j) κ := by
    intro κ hκ; rw [tagP_sym prog i κ hκ, hp]; rfl
  refine passAll (X + Y + 1) (by simp)
    (e := sym i 0 :: (List.replicate X (sym i 1) ++ sym i 2 :: List.replicate Y (sym i 3)))
    (by simp [W, xS])
    (by simp [hP, prodOf, List.mem_replicate]; aesop) ?_ (by simp; omega)
  cases b <;> simp [hP, prodOf, W, rp_succ]

/-- The one-sweep `dbl2` gadget. -/
theorem gadget_dbl2 {b : Bool} {j : ℕ} (hp : prog i = some (.dbl2 b j)) (X Y : ℕ) :
    TransGen (LStep (tagP prog)) (W i X Y) (W j X (2 * Y + b.toNat)) := by
  have hP : ∀ κ, κ < 18 → tagP prog (sym i κ) = prodOf i (.dbl2 b j) κ := by
    intro κ hκ; rw [tagP_sym prog i κ hκ, hp]; rfl
  refine passAll (X + Y + 1) (by simp)
    (e := sym i 0 :: (List.replicate X (sym i 1) ++ sym i 2 :: List.replicate Y (sym i 3)))
    (by simp [W, xS])
    (by simp [hP, prodOf, List.mem_replicate]; aesop) ?_ (by simp; omega)
  cases b <;> simp [hP, prodOf, W, rp_succ]

theorem gadget_half1 {j₀ j₁ : ℕ} (hp : prog i = some (.half1 j₀ j₁)) (X Y : ℕ) :
    TransGen (LStep (tagP prog)) (W i X Y) (W (if X % 2 = 0 then j₀ else j₁) (X / 2) Y) := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' X
  · have h1 : 2 * m % 2 = 0 := by omega
    have h2 : 2 * m / 2 = m := by omega
    rw [if_pos h1, h2]; exact gadget_half1_even hp m Y
  · have h1 : ¬ (2 * m + 1) % 2 = 0 := by omega
    have h2 : (2 * m + 1) / 2 = m := by omega
    rw [if_neg h1, h2]; exact gadget_half1_odd hp m Y

theorem gadget_half2 {j₀ j₁ : ℕ} (hp : prog i = some (.half2 j₀ j₁)) (X Y : ℕ) :
    TransGen (LStep (tagP prog)) (W i X Y) (W (if Y % 2 = 0 then j₀ else j₁) X (Y / 2)) := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' Y
  · have h1 : 2 * m % 2 = 0 := by omega
    have h2 : 2 * m / 2 = m := by omega
    rw [if_pos h1, h2]; exact gadget_half2_even hp X m
  · have h1 : ¬ (2 * m + 1) % 2 = 0 := by omega
    have h2 : (2 * m + 1) / 2 = m := by omega
    rw [if_neg h1, h2]; exact gadget_half2_odd hp X m

/-- **One TRM step is simulated** by ≥ 1 2-TS step, through words of length ≥ 3. -/
theorem fwd_L {c c' : Cfg} (h : TRM.Step prog c c') :
    TransGen (LStep (tagP prog)) (enc c) (enc c') := by
  obtain ⟨i, X, Y⟩ := c
  obtain ⟨op, hp, rfl⟩ := step_iff.mp h
  cases op with
  | dbl1 b j => exact gadget_dbl1 hp X Y
  | dbl2 b j => exact gadget_dbl2 hp X Y
  | half1 j₀ j₁ => exact gadget_half1 hp X Y
  | half2 j₀ j₁ => exact gadget_half2 hp X Y

end Gadgets

/-! ### Halting and the `ExactSim` -/

theorem halt_W {prog : ℕ → Option Op} {i : ℕ} (h : prog i = none) (X Y : ℕ) :
    Tag.Halt (tagP prog) (W i X Y) := by
  simp only [W, Tag.Halt, tagP_sym prog i 0 (by omega), h, Option.bind_none]

/-- **TRM → 2-TS is an exact simulation** (docs/24 §2 L2), on all TRM configurations. -/
theorem exactSim (prog : ℕ → Option Op) :
    ExactSim (fun _ => True) (TRM.Step prog) (TRM.Halt prog)
      (Tag.Step (tagP prog)) (Tag.Halt (tagP prog)) enc dec where
  inv_step _ _ _ _ := trivial
  prog c _ := TRM.halt_or_step prog c
  fwd _ _ _ h := (fwd_L h).mono fun _ _ h => h.step
  halt c _ hh := ⟨enc c, ReflTransGen.refl, halt_W hh _ _, dec_enc c⟩
  detY _ _ _ h₁ h₂ := Tag.step_det h₁ h₂
  stuckY _ _ hh := halt_not_step hh

/-! ### Length invariant (the |α| < 2 case of Morita Thm 7.2; docs/24 §2 L2–L3) -/

section Reach
variable {α β : Type*}

/-- On a deterministic system, a run of length `n` from `a` either is empty, or ends in a
    `G`-configuration, or passes the end `b` of a `G`-guarded path from `a`. -/
theorem nrel_along {r : β → β → Prop} (hdet : Det r) {G : β → Prop} {a b : β}
    (hab : TransGen (fun u v => r u v ∧ G v) a b) :
    ∀ {n y}, NRel r n a y → (n = 0 ∧ y = a) ∨ G y ∨ ∃ m < n, NRel r m b y := by
  induction hab using TransGen.head_induction_on with
  | single h =>
    intro n y hn
    cases n with
    | zero => exact .inl ⟨rfl, hn.symm⟩
    | succ k =>
      obtain ⟨c, hc, hk⟩ := hn
      exact .inr (.inr ⟨k, by omega, hdet _ _ _ hc h.1 ▸ hk⟩)
  | head h _ ih =>
    intro n y hn
    cases n with
    | zero => exact .inl ⟨rfl, hn.symm⟩
    | succ k =>
      obtain ⟨c, hc, hk⟩ := hn
      rcases ih (hdet _ _ _ hc h.1 ▸ hk) with ⟨rfl, rfl⟩ | hG | ⟨m, hm, hm'⟩
      · exact .inr (.inl h.2)
      · exact .inr (.inl hG)
      · exact .inr (.inr ⟨m, by omega, hm'⟩)

/-- Every configuration reachable from an image `enc x` satisfies `G`, if images satisfy `G`,
    and each image is stuck or reaches the next image along a `G`-guarded path. -/
theorem reach_good {r : β → β → Prop} (hdet : Det r) (G : β → Prop) (enc' : α → β)
    (hG : ∀ x, G (enc' x))
    (hnext : ∀ x, (∀ y, ¬ r (enc' x) y) ∨
      ∃ x', TransGen (fun u v => r u v ∧ G v) (enc' x) (enc' x'))
    (x : α) (y : β) (h : ReflTransGen r (enc' x) y) : G y := by
  obtain ⟨n, hn⟩ := NRel.of_reflTransGen h
  clear h
  induction n using Nat.strong_induction_on generalizing x with
  | _ n ih =>
    rcases hnext x with hst | ⟨x', hx'⟩
    · cases n with
      | zero => exact hn ▸ hG x
      | succ k => obtain ⟨c, hc, -⟩ := hn; exact absurd hc (hst c)
    · rcases nrel_along hdet hx' hn with ⟨-, rfl⟩ | hGy | ⟨m, hm, hm'⟩
      · exact hG x
      · exact hGy
      · exact ih m hm x' hm'

end Reach

/-- **Length invariant**: every word reachable from a canonical word has length ≥ 3. -/
theorem reach_length (prog : ℕ → Option Op) (c : Cfg) (w : List ℕ)
    (h : ReflTransGen (Tag.Step (tagP prog)) (enc c) w) : 3 ≤ w.length := by
  refine reach_good (r := Tag.Step (tagP prog)) (fun _ _ _ h₁ h₂ => Tag.step_det h₁ h₂) (fun w => 3 ≤ w.length) enc
    (fun c => by obtain ⟨i, X, Y⟩ := c; simp [enc]; omega) (fun c => ?_) c w h
  rcases TRM.halt_or_step prog c with hh | ⟨c', hc'⟩
  · exact .inl fun y => halt_not_step (halt_W hh _ _)
  · exact .inr ⟨c', fwd_L hc'⟩

/-- No word reachable from a canonical word is a one-letter word (in P3's vocabulary: the
    canonical words satisfy `NoShort`). -/
theorem reach_not_short (prog : ℕ → Option Op) (c : Cfg) (w : List ℕ)
    (h : ReflTransGen (Tag.Step (tagP prog)) (enc c) w) : ∀ a, w ≠ [a] := by
  intro a ha; have := reach_length prog c w h; simp [ha] at this

end URTM.Univ.TRMToTag
