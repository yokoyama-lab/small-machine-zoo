/-
  **Exact simulation calculus** (docs/24 §2, piece P2).

  Each layer of the chain `tm n → TRM → 2-TS → CTSH → U` is a *Def-5.8 simulation with
  exact readback*, `ExactSim`: every source step becomes ≥ 1 target step, every halting
  source configuration is reached by a halting target configuration that decodes back to it,
  and the target is deterministic with halting configurations stuck.

  Relation to Spec (`LeanUniv/Spec.lean`, `LeanUniv/Strict.lean`):
  * Spec's `Simulates`/`IsUTM`/`IsUTMStrict` speak about *runs*: a halting source run is
    matched by a halting target run whose halting ID reads back to the source's, and a
    non-halting source is matched by a non-halting target. That run-level shape is `RunSim`
    below, with `RHaltsAt (Step T) (Halted T) = HaltsAt T` and `RHalts … = Halts T` by `rfl`
    (`haltsAt_eq`, `halts_eq`).
  * `ExactSim` is the step-level, compositional form. `ExactSim.runSim` turns it into a
    `RunSim` (the non-halting direction is the "free" one: `ExactSim.not_halts`), and
    `ExactSim.trans` composes layers (encoders by `∘`, decoders by `Option.bind`, so the
    composite decoder is `Computable` whenever both are, `trans_dec_computable`).
  * `isUTMStrict_of_chain` is the bridge: a run-level entry layer (Spec ID of `tm n` → code;
    this is L0/P1), one `ExactSim` family for the middle (the composite of L1–L3), and a
    run-level exit layer (L4: the record machine `U`), together with computability of `c`
    and `d`, give `IsUTMStrict U`.

  Everything here is `Prop`-level; computability is only required of the final `c` and `d`.
-/
import LeanUniv.Strict
import LeanUniv.DropGen
import Mathlib.Computability.Primrec.Basic

namespace URTM.Univ
open Relation

variable {X Y Z : Type*}

/-! ### Generic halting notions -/

/-- `a` reaches the halting configuration `b`. -/
def RHaltsAt (step : X → X → Prop) (halt : X → Prop) (a b : X) : Prop :=
  ReflTransGen step a b ∧ halt b

/-- `a` halts. -/
def RHalts (step : X → X → Prop) (halt : X → Prop) (a : X) : Prop :=
  ∃ b, RHaltsAt step halt a b

theorem haltsAt_eq (T : List URTM.Quint) :
    Spec.HaltsAt T = RHaltsAt (Spec.Step T) (Spec.Halted T) := rfl

theorem halts_eq (T : List URTM.Quint) :
    Spec.Halts T = RHalts (Spec.Step T) (Spec.Halted T) := rfl

/-! ### Step counting and determinism -/

/-- Exactly `n` steps. -/
def NRel (r : X → X → Prop) : ℕ → X → X → Prop
  | 0, a, b => a = b
  | n + 1, a, b => ∃ c, r a c ∧ NRel r n c b

theorem NRel.of_reflTransGen {r : X → X → Prop} {a b : X} (h : ReflTransGen r a b) :
    ∃ n, NRel r n a b := by
  induction h using ReflTransGen.head_induction_on with
  | refl => exact ⟨0, rfl⟩
  | head hac _ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, _, hac, hn⟩

/-- Deterministic step relation. -/
def Det (r : X → X → Prop) : Prop := ∀ a b₁ b₂, r a b₁ → r a b₂ → b₁ = b₂

/-- In a deterministic system, a step from `a` stays on the unique path from `a` to a stuck
    configuration `z`, one step closer. -/
theorem NRel.step_toward {r : X → X → Prop} (hdet : Det r) {z : X} (hz : ∀ z', ¬ r z z')
    {n : ℕ} {a a' : X} (hn : NRel r n a z) (ha : r a a') : ∃ m, n = m + 1 ∧ NRel r m a' z := by
  cases n with
  | zero =>
    simp only [NRel] at hn
    subst hn
    exact absurd ha (hz _)
  | succ m =>
    obtain ⟨c, hc, hm⟩ := hn
    exact ⟨m, rfl, hdet _ _ _ ha hc ▸ hm⟩

theorem NRel.transGen_toward {r : X → X → Prop} (hdet : Det r) {z : X} (hz : ∀ z', ¬ r z z')
    {a a' : X} (h : TransGen r a a') : ∀ {n}, NRel r n a z → ∃ m < n, NRel r m a' z := by
  induction h with
  | single hab =>
    intro n hn
    obtain ⟨m, rfl, hm⟩ := NRel.step_toward hdet hz hn hab
    exact ⟨m, Nat.lt_succ_self m, hm⟩
  | tail _ hbc ih =>
    intro n hn
    obtain ⟨m, hmn, hm⟩ := ih hn
    obtain ⟨k, rfl, hk⟩ := NRel.step_toward hdet hz hm hbc
    exact ⟨k, by omega, hk⟩

/-- In a deterministic system, if `a` reaches a stuck `z` and also reaches `b`, then `b`
    reaches `z`. -/
theorem reflTransGen_to_stuck {r : X → X → Prop} (hdet : Det r) {z : X}
    (hz : ∀ z', ¬ r z z') {a b : X} (haz : ReflTransGen r a z) (hab : ReflTransGen r a b) :
    ReflTransGen r b z := by
  induction hab with
  | refl => exact haz
  | tail _ hcd ih =>
    rcases ReflTransGen.cases_head ih with rfl | ⟨e, hce, hez⟩
    · exact absurd hcd (hz _)
    · exact hdet _ _ _ hcd hce ▸ hez

/-- Halting configurations of a deterministic system with stuck halting configurations are
    unique. -/
theorem haltsAt_unique {r : X → X → Prop} {halt : X → Prop} (hdet : Det r)
    (hstuck : ∀ y y', halt y → ¬ r y y') {a b₁ b₂ : X}
    (h₁ : RHaltsAt r halt a b₁) (h₂ : RHaltsAt r halt a b₂) : b₁ = b₂ := by
  have h := reflTransGen_to_stuck hdet (fun z' => hstuck _ z' h₂.2) h₂.1 h₁.1
  rcases ReflTransGen.cases_head h with h | ⟨c, hc, -⟩
  · exact h
  · exact absurd hc (hstuck _ _ h₁.2)

/-! ### Run-level simulation (the shape of Spec's `Simulates`) -/

/-- **Run-level exact simulation** of the source configuration `x₀` by the target
    configuration `y₀`, with readback relation `R`: every halting source run from `x₀` is
    matched by a halting target run from `y₀` whose halting configuration is `R`-related to
    the source's, and a non-halting source gives a non-halting target. -/
def RunSim (stepX : X → X → Prop) (haltX : X → Prop) (stepY : Y → Y → Prop)
    (haltY : Y → Prop) (R : X → Y → Prop) (x₀ : X) (y₀ : Y) : Prop :=
  (∀ x, RHaltsAt stepX haltX x₀ x → ∃ y, RHaltsAt stepY haltY y₀ y ∧ R x y) ∧
  (¬ RHalts stepX haltX x₀ → ¬ RHalts stepY haltY y₀)

theorem RunSim.mono {stepX : X → X → Prop} {haltX : X → Prop} {stepY : Y → Y → Prop}
    {haltY : Y → Prop} {R R' : X → Y → Prop} {x₀ : X} {y₀ : Y}
    (h : RunSim stepX haltX stepY haltY R x₀ y₀) (hR : ∀ x y, R x y → R' x y) :
    RunSim stepX haltX stepY haltY R' x₀ y₀ :=
  ⟨fun x hx => (h.1 x hx).imp fun _ hy => ⟨hy.1, hR _ _ hy.2⟩, h.2⟩

/-- Run-level simulations compose; the readback relations compose relationally. -/
theorem RunSim.trans {stepX : X → X → Prop} {haltX : X → Prop} {stepY : Y → Y → Prop}
    {haltY : Y → Prop} {stepZ : Z → Z → Prop} {haltZ : Z → Prop}
    {R₁ : X → Y → Prop} {R₂ : Y → Z → Prop} {x₀ : X} {y₀ : Y} {z₀ : Z}
    (h₁ : RunSim stepX haltX stepY haltY R₁ x₀ y₀)
    (h₂ : RunSim stepY haltY stepZ haltZ R₂ y₀ z₀) :
    RunSim stepX haltX stepZ haltZ (fun x z => ∃ y, R₁ x y ∧ R₂ y z) x₀ z₀ := by
  refine ⟨fun x hx => ?_, fun hx => h₂.2 (h₁.2 hx)⟩
  obtain ⟨y, hy, hxy⟩ := h₁.1 x hx
  obtain ⟨z, hz, hyz⟩ := h₂.1 y hy
  exact ⟨z, hz, y, hxy, hyz⟩

/-! ### Step-level exact simulation -/

/-- **Exact simulation** (docs/24 §2) of the source system `(stepX, haltX)` by the target
    system `(stepY, haltY)` on the source configurations satisfying `Inv`, with encoder `enc`
    and decoder `dec`:
    * `inv_step`: `Inv` is closed under source steps;
    * `prog`: an `Inv` source configuration halts or steps (true for any TM whose halting
      is "no applicable rule");
    * `fwd`: each source step is simulated by ≥ 1 target step between the images;
    * `halt`: a halting source configuration `x` is reached from `enc x` by a halting target
      configuration that decodes back to `x` (exact readback);
    * `detY`, `stuckY`: the target is deterministic and its halting configurations are stuck.

    The converse directions (target halts ⇒ source halts, with the same readback; source
    does not halt ⇒ target does not halt) follow: `ExactSim.not_halts`,
    `ExactSim.haltsAt_of_target`, `ExactSim.runSim`. -/
structure ExactSim (Inv : X → Prop) (stepX : X → X → Prop) (haltX : X → Prop)
    (stepY : Y → Y → Prop) (haltY : Y → Prop) (enc : X → Y) (dec : Y → Option X) : Prop where
  inv_step : ∀ x x', Inv x → stepX x x' → Inv x'
  prog : ∀ x, Inv x → haltX x ∨ ∃ x', stepX x x'
  fwd : ∀ x x', Inv x → stepX x x' → TransGen stepY (enc x) (enc x')
  halt : ∀ x, Inv x → haltX x → ∃ y, ReflTransGen stepY (enc x) y ∧ haltY y ∧ dec y = some x
  detY : Det stepY
  stuckY : ∀ y y', haltY y → ¬ stepY y y'

namespace ExactSim

variable {Inv : X → Prop} {stepX : X → X → Prop} {haltX : X → Prop}
  {stepY : Y → Y → Prop} {haltY : Y → Prop} {enc : X → Y} {dec : Y → Option X}

theorem inv_reach (S : ExactSim Inv stepX haltX stepY haltY enc dec) {x x' : X}
    (hx : Inv x) (h : ReflTransGen stepX x x') : Inv x' := by
  induction h with
  | refl => exact hx
  | tail _ h ih => exact S.inv_step _ _ ih h

/-- Source runs lift to target runs between the images. -/
theorem lift (S : ExactSim Inv stepX haltX stepY haltY enc dec) {x x' : X}
    (hx : Inv x) (h : ReflTransGen stepX x x') : ReflTransGen stepY (enc x) (enc x') := by
  induction h with
  | refl => exact ReflTransGen.refl
  | tail hxb hbc ih => exact ih.trans (S.fwd _ _ (S.inv_reach hx hxb) hbc).to_reflTransGen

/-- **The free non-halting direction**: a source configuration that does not halt has an
    image that does not halt (the source has runs of every length, hence so does the
    deterministic target, which therefore cannot reach a stuck configuration). -/
theorem not_halts (S : ExactSim Inv stepX haltX stepY haltY enc dec) {x₀ : X}
    (hx₀ : Inv x₀) (hn : ¬ RHalts stepX haltX x₀) : ¬ RHalts stepY haltY (enc x₀) := by
  rintro ⟨y, hy, hhy⟩
  obtain ⟨n, hn'⟩ := NRel.of_reflTransGen hy
  have hz : ∀ z', ¬ stepY y z' := fun z' => S.stuckY _ z' hhy
  -- strong induction on the distance to the stuck `y`
  suffices ∀ n x, Inv x → ¬ RHalts stepX haltX x → NRel stepY n (enc x) y → False from
    this n x₀ hx₀ hn hn'
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x hx hnx hxn
    rcases S.prog x hx with hh | ⟨x', hxx'⟩
    · exact hnx ⟨x, ReflTransGen.refl, hh⟩
    · obtain ⟨m, hmn, hm⟩ := NRel.transGen_toward S.detY hz (S.fwd _ _ hx hxx') hxn
      refine ih m hmn x' (S.inv_step _ _ hx hxx') ?_ hm
      rintro ⟨b, hb, hhb⟩
      exact hnx ⟨b, ReflTransGen.head hxx' hb, hhb⟩

/-- Forward halting direction at run level. -/
theorem haltsAt (S : ExactSim Inv stepX haltX stepY haltY enc dec) {x₀ x : X}
    (hx₀ : Inv x₀) (h : RHaltsAt stepX haltX x₀ x) :
    ∃ y, RHaltsAt stepY haltY (enc x₀) y ∧ dec y = some x := by
  obtain ⟨y, hy, hhy, hd⟩ := S.halt x (S.inv_reach hx₀ h.1) h.2
  exact ⟨y, ⟨(S.lift hx₀ h.1).trans hy, hhy⟩, hd⟩

/-- **Backward direction**: if the image halts at `y`, the source halts at a configuration
    that `y` decodes to. -/
theorem haltsAt_of_target (S : ExactSim Inv stepX haltX stepY haltY enc dec) {x₀ : X}
    {y : Y} (hx₀ : Inv x₀) (h : RHaltsAt stepY haltY (enc x₀) y) :
    ∃ x, RHaltsAt stepX haltX x₀ x ∧ dec y = some x := by
  by_contra hne
  by_cases hs : RHalts stepX haltX x₀
  · obtain ⟨x, hx⟩ := hs
    obtain ⟨y', hy', hd⟩ := S.haltsAt hx₀ hx
    exact hne ⟨x, hx, haltsAt_unique S.detY S.stuckY h hy' ▸ hd⟩
  · exact S.not_halts hx₀ hs ⟨y, h⟩

/-- `ExactSim` gives the run-level simulation of Spec's shape, with readback `dec y = some x`. -/
theorem runSim (S : ExactSim Inv stepX haltX stepY haltY enc dec) {x₀ : X} (hx₀ : Inv x₀) :
    RunSim stepX haltX stepY haltY (fun x y => dec y = some x) x₀ (enc x₀) :=
  ⟨fun _ h => S.haltsAt hx₀ h, S.not_halts hx₀⟩

/-- **Composition** of exact simulations: encoders compose by `∘`, decoders by
    `Option.bind`. The intermediate invariant must hold on the images of the first encoder. -/
theorem trans {InvY : Y → Prop} {stepZ : Z → Z → Prop} {haltZ : Z → Prop}
    {enc₂ : Y → Z} {dec₂ : Z → Option Y}
    (S₁ : ExactSim Inv stepX haltX stepY haltY enc dec)
    (S₂ : ExactSim InvY stepY haltY stepZ haltZ enc₂ dec₂)
    (hinv : ∀ x, Inv x → InvY (enc x)) :
    ExactSim Inv stepX haltX stepZ haltZ (enc₂ ∘ enc) (fun z => (dec₂ z).bind dec) where
  inv_step := S₁.inv_step
  prog := S₁.prog
  fwd x x' hx h := by
    have hY := S₁.fwd x x' hx h
    have key : ∀ {b}, TransGen stepY (enc x) b → TransGen stepZ (enc₂ (enc x)) (enc₂ b) := by
      intro b hb
      induction hb with
      | single h => exact S₂.fwd _ _ (hinv x hx) h
      | tail hab hbc ih =>
        exact ih.trans (S₂.fwd _ _ (S₂.inv_reach (hinv x hx) hab.to_reflTransGen) hbc)
    exact key hY
  halt x hx hh := by
    obtain ⟨y, hy, hhy, hd⟩ := S₁.halt x hx hh
    obtain ⟨z, hz, hhz, hd₂⟩ := S₂.halt y (S₂.inv_reach (hinv x hx) hy) hhy
    exact ⟨z, (S₂.lift (hinv x hx) hy).trans hz, hhz, by simp [hd₂, hd]⟩
  detY := S₂.detY
  stuckY := S₂.stuckY

/-- **Restriction** to a smaller invariant that is still closed under source steps
    (integration: used to add the label / state bounds of the finiteness lemmas). -/
theorem restrict (S : ExactSim Inv stepX haltX stepY haltY enc dec) (Inv' : X → Prop)
    (hsub : ∀ x, Inv' x → Inv x) (hstep : ∀ x x', Inv' x → stepX x x' → Inv' x') :
    ExactSim Inv' stepX haltX stepY haltY enc dec where
  inv_step := hstep
  prog x hx := S.prog x (hsub x hx)
  fwd x x' hx h := S.fwd x x' (hsub x hx) h
  halt x hx hh := S.halt x (hsub x hx) hh
  detY := S.detY
  stuckY := S.stuckY

/-- The composite decoder of `trans` is computable when both decoders are. -/
theorem trans_dec_computable {X Y Z : Type*} [Primcodable X] [Primcodable Y] [Primcodable Z]
    {dec : Y → Option X} {dec₂ : Z → Option Y} (h : Computable dec) (h₂ : Computable dec₂) :
    Computable fun z => (dec₂ z).bind dec :=
  Computable.option_bind h₂ (h.comp Computable.snd).to₂

end ExactSim

/-! ### Bridge to `IsUTMStrict` -/

open Spec in
/-- **Bridge, body form** (docs/26): the body `StrictBody U c d` of `IsUTMStrict U` for the
    given `c` and `d`, from the hypotheses of `isUTMStrict_of_chain` other than computability.
    `isUTMStrict_of_chain` below is this plus computability. -/
theorem strictBody_of_chain {Y : Type*} (U : List URTM.Quint)
    (c : ℕ × Code → Code) (d : Code → Option Code)
    (stepX : ℕ → Code → Code → Prop) (haltX : ℕ → Code → Prop) (InvX : ℕ → Code → Prop)
    (stepY : ℕ → Y → Y → Prop) (haltY : ℕ → Y → Prop)
    (encM : ℕ → Code → Y) (decM : Y → Option Code)
    (hID : ∀ n a, IsIDOf (tm n) (toID 0 a) → IsIDOf U (toID 0 (c (n, a))))
    (hin : ∀ n a, IsIDOf (tm n) (toID 0 a) → InvX n a ∧
      RunSim (Step (tm n)) (Halted (tm n)) (stepX n) (haltX n)
        (fun β z => toID β.pos z = β) (toID 0 a) a)
    (hmid : ∀ n, ExactSim (InvX n) (stepX n) (haltX n) (stepY n) (haltY n) (encM n) decM)
    (hout : ∀ n a, IsIDOf (tm n) (toID 0 a) →
      RunSim (stepY n) (haltY n) (Step U) (Halted U)
        (fun y γ => ∃ g, toID γ.pos g = γ ∧ d g = decM y) (encM n a) (toID 0 (c (n, a))))
    (hdinv : ∀ p g g', toID p g = toID p g' → d g = d g') :
    DropGen.StrictBody U c d := by
  intro n a ha
  refine ⟨hID n a ha, ?_⟩
  obtain ⟨hinv, hent⟩ := hin n a ha
  have h := (hent.trans ((hmid n).runSim hinv)).trans (hout n a ha)
  refine ⟨fun β hβ => ?_, h.2⟩
  obtain ⟨γ, hγ, y, ⟨z, hz, hyz⟩, g, hg, hdg⟩ := h.1 β hβ
  refine ⟨γ, hγ, ⟨g, hg⟩, fun g' hg' => ⟨z, ?_, hz⟩⟩
  rw [hdinv _ g' g (hg'.trans hg.symm)]
  exact hdg.trans hyz

open Spec in
/-- **Bridge** (docs/24 §2, L5): `IsUTMStrict U` from
    * computable `c` and `d`, and `c(n, a) ∈ ID(U)`;
    * an **entry** layer (L0, P1): Spec's run of `tm n` from `toID 0 a` is run-level
      simulated by a code-level system `(stepX n, haltX n)` from the code `a` itself, with
      readback `toID β.pos z = β`, and `a` satisfies the invariant;
    * a **middle** family of `ExactSim`s (the composite of L1–L3 via `ExactSim.trans`) with an
      `n`-independent decoder `decM`;
    * an **exit** layer (L4): the image `encM n a` is run-level simulated by `U` from
      `toID 0 (c (n, a))`, and some window `g` of the halting ID satisfies `d g = decM y`;
    * `d` sees only the ID, not the code chosen for it (`hdinv`; needed since 2026-10-03, when
      the output clause of `IsUTMStrict` became "every code of the halting ID"). -/
theorem isUTMStrict_of_chain {Y : Type*} (U : List URTM.Quint)
    (c : ℕ × Code → Code) (d : Code → Option Code) (hc : Computable c) (hd : Computable d)
    (stepX : ℕ → Code → Code → Prop) (haltX : ℕ → Code → Prop) (InvX : ℕ → Code → Prop)
    (stepY : ℕ → Y → Y → Prop) (haltY : ℕ → Y → Prop)
    (encM : ℕ → Code → Y) (decM : Y → Option Code)
    (hID : ∀ n a, IsIDOf (tm n) (toID 0 a) → IsIDOf U (toID 0 (c (n, a))))
    (hin : ∀ n a, IsIDOf (tm n) (toID 0 a) → InvX n a ∧
      RunSim (Step (tm n)) (Halted (tm n)) (stepX n) (haltX n)
        (fun β z => toID β.pos z = β) (toID 0 a) a)
    (hmid : ∀ n, ExactSim (InvX n) (stepX n) (haltX n) (stepY n) (haltY n) (encM n) decM)
    (hout : ∀ n a, IsIDOf (tm n) (toID 0 a) →
      RunSim (stepY n) (haltY n) (Step U) (Halted U)
        (fun y γ => ∃ g, toID γ.pos g = γ ∧ d g = decM y) (encM n a) (toID 0 (c (n, a))))
    (hdinv : ∀ p g g', toID p g = toID p g' → d g = d g') :
    IsUTMStrict U :=
  DropGen.isUTMStrict_of_body hc hd (strictBody_of_chain U c d stepX haltX InvX stepY haltY encM decM
    hID hin hmid hout hdinv)

end URTM.Univ
