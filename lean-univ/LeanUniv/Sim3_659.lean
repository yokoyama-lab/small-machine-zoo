/-
  **The 3-state machine with 659 symbols (the improved 3-state conversion of (32,3), not mirrored) simulates
  every CTSH.** The same composition as `CTSH3_600Main.urtm3_600_simulates_ctsh`, without the mirror:

    `U32_3.urtm32_3_simulates_ctsh` → `SimLemmas.drop_simulates` (the halting rules removed) → `Conv3S.conv_main`.

  The table `T3py` of `URTM.Gen.T3_659` is the value of the general conversion `Conv3S.conv` on (32,3) without its
  halting rules (`URTM.Gen.T3_659.conv_eq_py`). Initial configuration: Morita's initial configuration `encC32 C w` of (32,3), with
  the window starting at `0` of length `len + 3` (`len` the length of the initial tape); the initial state `begin`
  is entered by right moves, and every pair `(begin, x)` is a mark of `G`, so the invariant holds.

  No `sorry`, no new axiom, no `native_decide`.
-/
import URTM.CTSH3_600Main
import URTM.Gen.T3_659

set_option maxRecDepth 100000

namespace URTM.Univ.Sim3_659

open URTM URTM.KState URTM.CTSH URTM.SimLemmas URTM.Conv3Base URTM.Gen.K32_3 URTM.Gen.T3_659
open URTM.Conv1W (VSt VSym isPlus)
open URTM.Conv3P (CSym)
open URTM.Conv510 (TSt)
open URTM.CTSH.U32_3 (encC32 finCfg32 urtm32_3_simulates_ctsh nm32)
open URTM.CTSH.U3_600 (f32 hH32 len32 len32_eq)

/-- The window of the initial configuration: start `0`, length `len + 3`. -/
def n0 (C : CTSH) (w : List Ch) : Nat := len32 C w + 3

/-- **The initial configuration of the 659-symbol machine**: Morita's initial configuration `encC32 C w` of
    (32,3), encoded (`Conv3S.enc`). -/
def E659 (C : CTSH) (w : List Ch) : Cfg TSt Ps (CSym (VSym St Sy)) :=
  Conv3S.enc T' idx 0 (n0 C w) (encC32 C w)

/-- **The halting configuration**: the halting configuration of U32_3 with its halting rule undone (`unhalt f32`),
    reached by `T'` in `N` steps, encoded. -/
def fin659 (C : CTSH) (w : List Ch) (vf : List Ch) (mf : Nat) (rm : List Ch) (N : Nat) :
    Cfg TSt Ps (CSym (VSym St Sy)) :=
  Conv3S.fin T' idx 0 (n0 C w) N (unhalt f32 (finCfg32 C vf mf rm))

/-- Every pair `(begin, x)` is a mark of `G` (`begin` is entered by right moves). -/
theorem begin_G : ∀ x, (St.q0, x) ∈ Gl := by intro x; cases x <;> decide +kernel

/-- The initial configuration satisfies the invariant of the 1WU conversion. -/
theorem inv0 (C : CTSH) (w : List Ch) :
    Conv1W.Inv T' Sy.s0 Gl 0 (n0 C w) St.q0 (encC32 C w).pos (encC32 C w).tape := by
  have hl := len32_eq C w
  have hl2 : (URTM.CTSH.U32_3.tapeList nm32 C 0 [] w).length = len32 C w := rfl
  simp only [encC32, URTM.CTSH.U32_3.encC, URTM.CTSH.U32_3.rep, List.length_nil, n0]
  refine ⟨by omega, by omega, fun j hj => ?_, fun _ => begin_G _⟩
  rcases hj with hj | hj
  · obtain ⟨k, hk⟩ : ∃ k : Nat, j = Int.negSucc k := ⟨(-j - 1).toNat, by omega⟩
    rw [hk]; rfl
  · obtain ⟨k, hk⟩ : ∃ k : Nat, j = (k : Int) := ⟨j.toNat, by omega⟩
    rw [hk, URTM.CTSH.Sim.tp_ofNat, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl

/-- **The 659-symbol machine simulates every CTSH** (the form of `urtm3_600_simulates_ctsh`). `T3py`
    (the value of `Conv3S.conv` on (32,3) without its halting rules) is deterministic and reversible, its rules
    read and write the 659 duplicate-free symbols of `sym3py`, and for every CTSH `C` and word `w`, from
    `E659 C w`:

    1. if `C` halts from `(w, 0)` in `n` steps at `(vf, mf)`, then `T'` halts from `encC32 C w` in `N` steps
       (`n ≤ N + 1`) at `unhalt f32 (finCfg32 C vf mf rm)` and `T3py` halts at `fin659 C w vf mf rm N`;
    2. if `T3py` halts, so does `C`, at a configuration of the form 1;
    3. `C` does not halt iff `T3py` does not halt. -/
theorem urtm3_659_simulates_ctsh (C : CTSH) (w : List Ch) :
    Deterministic T3py ∧ Reversible T3py ∧
    (∀ ρ ∈ T3py, ρ.s ∈ sym3py ∧ ρ.t ∈ sym3py) ∧ sym3py.length = 659 ∧ sym3py.Nodup ∧ T3py.length = 1757 ∧
    Conv3S.conv T' Sy.s0 ss qm Rl Gl idx need = T3py ∧
    (∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) →
      ∃ N M rm, n ≤ N + 1 ∧ HaltsIn T' N (encC32 C w) (unhalt f32 (finCfg32 C vf mf rm)) ∧
        HaltsIn T3py M (E659 C w) (fin659 C w vf mf rm N)) ∧
    (∀ M e, HaltsIn T3py M (E659 C w) e →
      ∃ n vf mf rm N, CHaltsIn C n (w, 0) (vf, mf) ∧
        HaltsIn T' N (encC32 C w) (unhalt f32 (finCfg32 C vf mf rm)) ∧ e = fin659 C w vf mf rm N) ∧
    ((∀ n f, ¬ CHaltsIn C n (w, 0) f) ↔ (∀ M e, ¬ HaltsIn T3py M (E659 C w) e)) := by
  have h32 := urtm32_3_simulates_ctsh C w
  have hfin : ∀ vf mf rm, ∃ h, (finCfg32 C vf mf rm).st = .halt h := by
    intro vf mf rm; cases vf <;> exact ⟨_, rfl⟩
  have hd := drop_simulates hD hH32 C w (encC32 C w) ⟨.q0, rfl⟩ (finCfg32 C) hfin ⟨h32.1, h32.2.1⟩
  have hm := Conv3S.conv_main hyp (c0 := encC32 C w) rfl (inv0 C w)
  rw [URTM.Gen.T3_659.conv_eq_py] at hm
  obtain ⟨hD3, hR3, hf, hb⟩ := hm
  have hsyms : ∀ ρ ∈ Conv3S.conv T' Sy.s0 ss qm Rl Gl idx need,
      ρ.s ∈ Conv3P.univ need (Conv3S.wsyms ss qm Gl) ∧ ρ.t ∈ Conv3P.univ need (Conv3S.wsyms ss qm Gl) :=
    Conv3P.conv_syms (fun _ h => Conv3S.w_syms hyp h) (fun _ h => Conv3S.w_shape h) hyp.hidx hsrc
  rw [URTM.Gen.T3_659.conv_eq_py, univ_eq_py] at hsyms
  have fwd : ∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) →
      ∃ N M rm, n ≤ N + 1 ∧ HaltsIn T' N (encC32 C w) (unhalt f32 (finCfg32 C vf mf rm)) ∧
        HaltsIn T3py M (E659 C w) (fin659 C w vf mf rm N) := by
    intro n vf mf hc
    obtain ⟨N, rm, hN, hh⟩ := hd.1 n vf mf hc
    obtain ⟨M, _, hM⟩ := hf N _ hh
    exact ⟨N, M, rm, hN, hh, hM⟩
  have bwd : ∀ M e, HaltsIn T3py M (E659 C w) e →
      ∃ n vf mf rm N, CHaltsIn C n (w, 0) (vf, mf) ∧
        HaltsIn T' N (encC32 C w) (unhalt f32 (finCfg32 C vf mf rm)) ∧ e = fin659 C w vf mf rm N := by
    intro M e he
    obtain ⟨N, e₀, h₀, rfl⟩ := hb M e he
    obtain ⟨n, vf, mf, rm, hc, rfl⟩ := hd.2.1 N e₀ h₀
    exact ⟨n, vf, mf, rm, N, hc, h₀, rfl⟩
  refine ⟨hD3, hR3, hsyms, card3.1, sym3py_nodup, card3.2, URTM.Gen.T3_659.conv_eq_py, fwd, bwd, ?_⟩
  constructor
  · intro hn M e he
    obtain ⟨n, vf, mf, rm, N, hc, _⟩ := bwd M e he
    exact hn n _ hc
  · intro hu n ⟨vf, mf⟩ hc
    obtain ⟨N, M, rm, _, _, hM⟩ := fwd n vf mf hc
    exact hu M _ hM

end URTM.Univ.Sim3_659
