/-
  **Finiteness of the middle chain** (integration of P3–P5; docs/24 "Integration notes").

  P3's 2-TS → CTSH layer (`TagToCTSH`) needs a finite alphabet `[0, S)`: the symbols of the
  initial word and of every production that can fire must be `< S`. P4's 2-TS (`TRMToTag`)
  numbers the symbol of kind `κ` of TRM label `i` as `sym i κ = 3 + 18 i + κ`, and P5's TRM
  program `L1.prog T` (`TMToTRM`) is defined for **every** label (its labels are `Nat.pair`
  codes). So the alphabet is finite only on the labels that can actually occur.

  * `Good T i`: the labels that can occur for table `T` — read labels `lRd m q j acc`
    (`m ≤ 1`, `q ≤ Qm T`, `j ≤ width T`, `acc < 2^j`), push labels
    `lPush r v k (lRd m q 0 0)` (`r ≤ 2`, `v < 2^width T`, `k ≤ width T`), and the
    normalisation labels `lNrm q`, `lNrm' q` (`q ≤ Qm T`), where `Qm T` is the largest state
    number of `T`.
  * `good_closed`: every jump target (both branches) of the instruction at a `Good` label is
    `Good`. `good_lt`: every `Good` label is `< Nb T`, an explicit (computable) bound built
    from `Qm T` and `2^width T` with `Nat.pair`.
  * `Alph T y := y < 3 ∨ Good T ((y - 3) / 18)`: the 2-TS symbols of `Good` labels and the
    fillers. `alph_lt`: they are `< Sb T := 3 + 18 · Nb T`. `alph_closed`: productions of
    `Alph` symbols are `Alph` words. (Symbols outside `Alph`, in particular all symbols
    `≥ Sb T`, are never reached; their productions may leave `[0, Sb T)`, which is why P3's
    `exactSim` was generalised to `exactSim_mem` over a sub-alphabet.)
  * The three layers with these invariants: `sim1` (L1 with the state bound `Inv1`),
    `sim2` (L2 on `Good` labels), `sim3` (L3 on `Alph` words without short words), and the
    composite `mid : ExactSim (Inv1 T) (CStep T) (CHalt T) stepC haltC (encMid T) decM`.
-/
import LeanUniv.TMToTRM
import LeanUniv.TRMToTag
import LeanUniv.TagToCTSH

namespace URTM.Univ.Fin
open URTM URTM.Spec URTM.Univ.L0 URTM.Univ.L1 Relation
open URTM.Univ.TRM (Op Cfg)

/-! ### L1 with a state bound -/

/-- The largest state number of `T`. -/
def Qm (T : List Quint) : ℕ := lmax (states T)

/-- L1's invariant plus the state bound. -/
def Inv1 (T : List Quint) (z : Code) : Prop := Inv T z ∧ z.1 ≤ Qm T

theorem q_le_Qm {T : List Quint} {r : Quint} (hr : r ∈ T) : r.q ≤ Qm T :=
  le_lmax (by simp only [states, List.mem_flatMap]; exact ⟨r, hr, by simp⟩)

theorem cstep_state {T : List Quint} {z z' : Code} (h : CStep T z z') (hz : z.1 ≤ Qm T) :
    z'.1 ≤ Qm T := by
  unfold CStep cstep at h
  split_ifs at h with hn
  · cases hs : zstep T z with
    | none => rw [hs] at h; cases h
    | some z'' =>
      rw [hs] at h; cases h
      unfold zstep at hs
      cases hl : look T z.1 (z.2.2.headD 0) with
      | none => rw [hl] at hs; cases hs
      | some o =>
        rw [hl] at hs; cases hs
        obtain ⟨r, hr, -, -, rfl⟩ := look_some hl
        have e : (mv (rhs r) z).1 = r.q := by unfold mv; split_ifs <;> rfl
        simp only [norm, e]
        exact q_le_Qm hr
  · cases h; exact hz

/-- **L1 with the state bound.** -/
theorem sim1 (T : List Quint) :
    ExactSim (Inv1 T) (CStep T) (CHalt T) (TRM.Step (prog T)) (TRM.Halt (prog T)) (enc T) dec :=
  (sim T).restrict (Inv1 T) (fun _ h => h.1)
    (fun z z' h hs => ⟨(sim T).inv_step z z' h.1 hs, cstep_state hs h.2⟩)

/-- **Entry with the state bound** (the bridge hypothesis `hin` with `InvX n := Inv1 (tbl n)`). -/
theorem hin1 (n : ℕ) (a : Code) (h : IsIDOf (tm n) (toID 0 a)) :
    Inv1 (tbl n) a ∧ RunSim (Spec.Step (tm n)) (Halted (tm n)) (CStep (tbl n)) (CHalt (tbl n))
      (fun β z => toID β.pos z = β) (toID 0 a) a := by
  obtain ⟨hi, hr⟩ := hin n a h
  refine ⟨⟨hi, ?_⟩, hr⟩
  obtain ⟨he, -⟩ := tm_eq_tbl (tm_ne_nil_of_isIDOf h)
  have hs : a.1 ∈ states (tm n) := h.2.1
  rw [he] at hs
  exact le_lmax hs

/-! ### Reachable labels -/

/-- The labels that can occur in a run of `prog T` from an image of L1. -/
def Good (T : List Quint) (i : ℕ) : Prop :=
  (∃ m q j acc, m ≤ 1 ∧ q ≤ Qm T ∧ j ≤ width T ∧ acc < 2 ^ j ∧ i = lRd m q j acc) ∨
  (∃ r v k m q, r ≤ 2 ∧ v < 2 ^ width T ∧ k ≤ width T ∧ m ≤ 1 ∧ q ≤ Qm T ∧
      i = lPush r v k (lRd m q 0 0)) ∨
  (∃ q, q ≤ Qm T ∧ (i = lNrm q ∨ i = lNrm' q))

/-- The jump targets of an instruction (both branches of a halving). -/
def targets : Op → List ℕ
  | .dbl1 _ j => [j]
  | .dbl2 _ j => [j]
  | .half1 j₀ j₁ => [j₀, j₁]
  | .half2 j₀ j₁ => [j₀, j₁]

theorem exec_mem_targets (op : Op) (X Y : ℕ) : (op.exec X Y).1 ∈ targets op := by
  cases op <;> simp only [Op.exec, targets] <;> (try split_ifs) <;> simp

theorem good_rd0 {T : List Quint} {m q : ℕ} (hm : m ≤ 1) (hq : q ≤ Qm T) :
    Good T (lRd m q 0 0) :=
  .inl ⟨m, q, 0, 0, hm, hq, Nat.zero_le _, by simp, rfl⟩

theorem targets_pushOp (r v k c : ℕ) :
    targets (pushOp r v k c) = [if k ≤ 1 then c else lPush r v (k - 1) c] := by
  unfold pushOp; split_ifs <;> rfl

theorem good_pushOp {T : List Quint} {r v k m q : ℕ} (hr : r ≤ 2) (hv : v < 2 ^ width T)
    (hk : k ≤ width T) (hm : m ≤ 1) (hq : q ≤ Qm T) :
    ∀ j ∈ targets (pushOp r v k (lRd m q 0 0)), Good T j := by
  intro j hj
  rw [targets_pushOp, List.mem_singleton] at hj
  subst hj
  split_ifs
  · exact good_rd0 hm hq
  · exact .inr (.inl ⟨r, v, k - 1, m, q, hr, hv, by omega, hm, hq, rfl⟩)

/-- **Closure of the reachable labels**: every jump target of the instruction at a `Good`
    label is `Good`. -/
theorem good_closed {T : List Quint} {i : ℕ} {op : Op} (hi : Good T i) (hp : prog T i = some op) :
    ∀ j ∈ targets op, Good T j := by
  unfold prog at hp
  rcases hi with ⟨m, q, j, acc, hm, hq, hj, hacc, rfl⟩ |
    ⟨r, v, k, m, q, hr, hv, hk, hm, hq, rfl⟩ | ⟨q, hq, rfl | rfl⟩
  · have hacc1 : acc < 2 ^ (j + 1) := by rw [pow_succ]; omega
    have hacc2 : acc + 2 ^ j < 2 ^ (j + 1) := by rw [pow_succ]; omega
    rcases Nat.lt_or_ge j (width T) with hjw | hjw
    · rcases (show m = 0 ∨ m = 1 by omega) with rfl | rfl
      · rw [progW_rd0_lt hjw] at hp
        cases hp
        intro j' hj'
        simp only [targets, List.mem_cons, List.not_mem_nil, or_false] at hj'
        rcases hj' with rfl | rfl
        · exact .inl ⟨0, q, j + 1, acc, le_rfl.trans (Nat.zero_le _), hq, hjw, hacc1, rfl⟩
        · exact .inl ⟨0, q, j + 1, acc + 2 ^ j, Nat.zero_le _, hq, hjw, hacc2, rfl⟩
      · rw [progW_rd1_lt hjw] at hp
        cases hp
        intro j' hj'
        simp only [targets, List.mem_cons, List.not_mem_nil, or_false] at hj'
        rcases hj' with rfl | rfl
        · exact .inl ⟨1, q, j + 1, acc, le_rfl, hq, hjw, hacc1, rfl⟩
        · exact .inl ⟨1, q, j + 1, acc + 2 ^ j, le_rfl, hq, hjw, hacc2, rfl⟩
    · obtain rfl : j = width T := le_antisymm hj hjw
      rcases (show m = 0 ∨ m = 1 by omega) with rfl | rfl
      · rw [progW_rd0_w] at hp
        cases hl : look T q acc with
        | none => rw [hl] at hp; cases hp
        | some o =>
          rw [hl] at hp
          cases hp
          obtain ⟨r, hr, -, -, rfl⟩ := look_some hl
          have ht : r.t < 2 ^ width T := lt_width (mem_symbols hr)
          have hq' := q_le_Qm hr
          simp only [act, rhs]
          split_ifs
          · exact good_pushOp (by norm_num) ht le_rfl le_rfl hq'
          · exact good_pushOp (by norm_num) ht le_rfl (Nat.zero_le _) hq'
          · exact good_pushOp (by norm_num) ht le_rfl (Nat.zero_le _) hq'
      · rw [progW_rd1_w] at hp
        cases hp
        exact good_pushOp (by norm_num) hacc le_rfl (Nat.zero_le _) hq
  · rw [progW_push] at hp
    cases hp
    exact good_pushOp hr hv hk hm hq
  · rw [progW_nrm] at hp
    cases hp
    intro j hj
    simp only [targets, List.mem_singleton] at hj
    subst hj
    exact .inr (.inr ⟨q, hq, .inr rfl⟩)
  · rw [progW_nrm'] at hp
    cases hp
    intro j hj
    simp only [targets, List.mem_cons, List.not_mem_nil, or_false, or_self] at hj
    subst hj
    exact good_rd0 (Nat.zero_le _) hq

/-! ### The bound on reachable labels -/

theorem pair_le_pair {a a' b b' : ℕ} (ha : a ≤ a') (hb : b ≤ b') :
    Nat.pair a b ≤ Nat.pair a' b' := by
  have h1 : Nat.pair a b ≤ Nat.pair a' b := by
    rcases ha.lt_or_eq with h | rfl
    · exact (Nat.pair_lt_pair_left b h).le
    · exact le_rfl
  have h2 : Nat.pair a' b ≤ Nat.pair a' b' := by
    rcases hb.lt_or_eq with h | rfl
    · exact (Nat.pair_lt_pair_right a' h).le
    · exact le_rfl
  exact h1.trans h2

/-- A number above every component of a `Good` label. -/
def Kb (T : List Quint) : ℕ := Qm T + 2 ^ width T + 3

/-- Bound for read labels. -/
def Rb (K : ℕ) : ℕ := Nat.pair K (Nat.pair K (Nat.pair K (Nat.pair K K)))

/-- **The bound on reachable labels** (computable from the table). -/
def Nb (T : List Quint) : ℕ :=
  Nat.pair (Kb T) (Nat.pair (Kb T) (Nat.pair (Kb T) (Nat.pair (Kb T) (Rb (Kb T))))) + 1

theorem rd_le {T : List Quint} {m q j acc : ℕ} (hm : m ≤ 1) (hq : q ≤ Qm T) (hj : j ≤ width T)
    (hacc : acc < 2 ^ j) : lRd m q j acc ≤ Rb (Kb T) := by
  have hw : width T < 2 ^ width T := Nat.lt_two_pow_self
  have hpj : 2 ^ j ≤ 2 ^ width T := Nat.pow_le_pow_right (by norm_num) hj
  unfold lRd Rb Kb
  exact pair_le_pair (Nat.zero_le _) (pair_le_pair (by omega)
    (pair_le_pair (by omega) (pair_le_pair (by omega) (by omega))))

/-- **Every reachable label is `< Nb T`.** -/
theorem good_lt {T : List Quint} {i : ℕ} (hi : Good T i) : i < Nb T := by
  have hw : width T < 2 ^ width T := Nat.lt_two_pow_self
  have hKR : Kb T ≤ Rb (Kb T) := Nat.left_le_pair _ _
  have hbig : Rb (Kb T) ≤
      Nat.pair (Kb T) (Nat.pair (Kb T) (Nat.pair (Kb T) (Nat.pair (Kb T) (Rb (Kb T))))) :=
    pair_le_pair le_rfl (pair_le_pair le_rfl (pair_le_pair le_rfl (pair_le_pair le_rfl hKR)))
  unfold Nb
  apply Nat.lt_succ_of_le
  rcases hi with ⟨m, q, j, acc, hm, hq, hj, hacc, rfl⟩ |
    ⟨r, v, k, m, q, hr, hv, hk, hm, hq, rfl⟩ | ⟨q, hq, rfl | rfl⟩
  · exact (rd_le hm hq hj hacc).trans hbig
  · unfold lPush
    have hc := rd_le (T := T) (j := 0) (acc := 0) hm hq (Nat.zero_le _) (by simp)
    exact pair_le_pair (by unfold Kb; omega) (pair_le_pair (by unfold Kb; omega)
      (pair_le_pair (by unfold Kb; omega) (pair_le_pair (by unfold Kb; omega) hc)))
  · unfold lNrm
    exact pair_le_pair (by unfold Kb; omega)
      ((show q ≤ Kb T by unfold Kb; omega).trans (Nat.left_le_pair _ _))
  · unfold lNrm'
    exact pair_le_pair (by unfold Kb; omega)
      ((show q ≤ Kb T by unfold Kb; omega).trans (Nat.left_le_pair _ _))

/-! ### L2 on reachable labels -/

/-- **L2 on `Good` labels.** -/
theorem sim2 (T : List Quint) :
    ExactSim (fun c : Cfg => Good T c.1) (TRM.Step (prog T)) (TRM.Halt (prog T))
      (Tag.Step (TRMToTag.tagP (prog T))) (Tag.Halt (TRMToTag.tagP (prog T)))
      TRMToTag.enc TRMToTag.dec :=
  (TRMToTag.exactSim (prog T)).restrict _ (fun _ _ => trivial) (fun c c' hc hs => by
    obtain ⟨i, X, Y⟩ := c
    obtain ⟨op, hp, rfl⟩ := TRM.step_iff.mp hs
    exact good_closed hc hp _ (exec_mem_targets op X Y))

theorem enc1_good {T : List Quint} {z : Code} (h : Inv1 T z) : Good T (enc T z).1 := by
  unfold enc
  split_ifs
  · exact good_rd0 (Nat.zero_le _) h.2
  · exact .inr (.inr ⟨z.1, h.2, .inl rfl⟩)

/-! ### The finite alphabet of the 2-TS -/

/-- The 2-TS symbols that can occur: fillers and the symbols of `Good` labels. -/
def Alph (T : List Quint) (y : ℕ) : Prop := y < 3 ∨ Good T ((y - 3) / 18)

/-- **The alphabet size** `S := 3 + 18 · Nb T`. -/
def Sb (T : List Quint) : ℕ := 3 + 18 * Nb T

theorem alph_lt {T : List Quint} {y : ℕ} (h : Alph T y) : y < Sb T := by
  unfold Sb
  rcases h with h | h
  · omega
  · have := good_lt h; omega

theorem mem_rp_iff {a b y n : ℕ} : y ∈ Tag2.rp n a b ↔ 0 < n ∧ (y = a ∨ y = b) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Tag2.rp_succ]
    simp only [List.mem_cons, ih]
    constructor
    · rintro (h | h | ⟨-, h⟩)
      · exact ⟨by omega, .inl h⟩
      · exact ⟨by omega, .inr h⟩
      · exact ⟨by omega, h⟩
    · rintro ⟨-, h | h⟩
      · exact .inl h
      · exact .inr (.inl h)

/-- The symbols in a production of label `i` belong to `i`, to a jump target, or are fillers. -/
theorem prodOf_mem {i : ℕ} {op : Op} {κ : ℕ} {w : List ℕ} (h : TRMToTag.prodOf i op κ = some w)
    {y : ℕ} (hy : y ∈ w) : y < 3 ∨ (y - 3) / 18 = i ∨ (y - 3) / 18 ∈ targets op := by
  cases op <;> simp only [TRMToTag.prodOf] at h <;> split at h <;>
    simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    simp only [targets, TRMToTag.sym, TRMToTag.xS, TRMToTag.yS, TRMToTag.zS, List.mem_cons,
      List.not_mem_nil, mem_rp_iff, or_false, List.cons_append,
      List.nil_append] at hy ⊢ <;>
    omega

/-- **Closure of the alphabet under the productions.** -/
theorem alph_closed {T : List Quint} {a : ℕ} {w : List ℕ} (ha : Alph T a)
    (hP : TRMToTag.tagP (prog T) a = some w) : ∀ y ∈ w, Alph T y := by
  intro y hy
  unfold TRMToTag.tagP at hP
  split_ifs at hP with h3
  have hG : Good T ((a - 3) / 18) := ha.resolve_left h3
  cases hp : prog T ((a - 3) / 18) with
  | none => rw [hp] at hP; cases hP
  | some op =>
    rw [hp, Option.bind_some] at hP
    rcases prodOf_mem hP hy with h | h | h
    · exact .inl h
    · exact .inr (h ▸ hG)
    · exact .inr (good_closed hG hp _ h)

theorem enc_alph {T : List Quint} {c : Cfg} (hc : Good T c.1) :
    ∀ y ∈ TRMToTag.enc c, Alph T y := by
  obtain ⟨i, X, Y⟩ := c
  intro y hy
  simp only [TRMToTag.enc, TRMToTag.W, TRMToTag.sym, TRMToTag.xS, List.mem_cons,
    List.mem_append, mem_rp_iff] at hy
  have : y < 3 ∨ (y - 3) / 18 = i := by omega
  rcases this with h | h
  · exact .inl h
  · exact .inr (h ▸ hc)

/-! ### L3 on the finite alphabet, and the composite middle layer -/

/-- **L3 on `Alph` words without short words.** -/
theorem sim3 (T : List Quint) :
    ExactSim (fun x => (∀ y ∈ x, Alph T y) ∧ Tag.NoShort (TRMToTag.tagP (prog T)) x)
      (Tag.Step (TRMToTag.tagP (prog T))) (Tag.Halt (TRMToTag.tagP (prog T)))
      TagToCTSH.stepC TagToCTSH.haltC (TagToCTSH.enc (Sb T) (TRMToTag.tagP (prog T)))
      TagToCTSH.dec :=
  TagToCTSH.exactSim_mem (Alph T) (fun _ h => alph_lt h) (fun _ ha _ hP => alph_closed ha hP)
    (Tag.NoShort _) (fun _ _ h hs => h.step hs) (fun _ h => h.not_short)

/-- The middle encoder: code ↦ TRM configuration ↦ canonical 2-TS word ↦ (Ĉ, (ϕ(word), 0)). -/
def encMid (T : List Quint) : Code → TagToCTSH.CID :=
  TagToCTSH.enc (Sb T) (TRMToTag.tagP (prog T)) ∘ (TRMToTag.enc ∘ enc T)

/-- The middle decoder (independent of the table). -/
def decM (y : TagToCTSH.CID) : Option Code :=
  (TagToCTSH.dec y).bind fun x => (TRMToTag.dec x).bind dec

/-- **The middle chain L1–L3 as one `ExactSim`** (code level of `T` → CTSH configurations). -/
theorem mid (T : List Quint) :
    ExactSim (Inv1 T) (CStep T) (CHalt T) TagToCTSH.stepC TagToCTSH.haltC (encMid T) decM :=
  ((sim1 T).trans (sim2 T) (fun _ h => enc1_good h)).trans (sim3 T) (fun z h =>
    ⟨enc_alph (enc1_good h), fun y hy ⟨a, _, hya, _⟩ =>
      TRMToTag.reach_not_short (prog T) (enc T z) y hy a hya⟩)

end URTM.Univ.Fin
