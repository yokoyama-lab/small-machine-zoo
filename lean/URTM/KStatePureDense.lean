/-
  「1 ブロック 3 状態」の変換の**密な版** `pconv`（計数記号を刈り込まないもの。旧リポ
  `kstate_convert.py --mode pure` の URTM(6,48)・(9,40) の系統）の主定理。

  疎版の主定理 `KStatePure.spconv_main` は `spconv ⊆ pconv` の部分集合について述べる。
  密な版は、疎版の実行がそのまま密な版の実行であること（`StepN.mono`）と、
  * 密な版も決定的・可逆（`pconv_det`・`pconv_rev`）
  * T が止まる配置では密な版も止まる（`pconv_halted`。疑似状態の配置は規則が無いので自明）
  から、同じ 3 項（前向きの停止・逆向きの停止・非停止の対応）を導く。逆向きは、決定性から
  「密な版の実行は疎版の実行と一致する」ことを使う（疎版が止まらないなら、密な版も同じ長さだけ進む）。

  疎版の定理を再利用するため、刈り込みの状態リスト `qs` を引数に取る（結論は `qs` に依らない）。
  未証明の穴・新規公理・native_decide を使わない。mathlib 非依存。
-/
import URTM.KStatePure
import URTM.SimLemmas

namespace URTM.KStatePure

set_option linter.unusedSectionVars false

open URTM (Dir)
open URTM.KState
open URTM.KStateSparse (NoStuck)
open URTM.SimLemmas (run_forever halts_unique StepN.mono halted_of_halt back_of_fwd)

variable {Q P S : Type} [DecidableEq Q] [DecidableEq P] [DecidableEq S]
variable {T : Machine Q P S} {L : Layout Q} {qs : List Q} {ss : List S}

/-- **密な版の主定理**。E = penc T L。
    1. 決定的・可逆
    2. 疑似状態で止まる実行は、E で対応する配置で止まる（前向き）
    3. `NoStuck T c` なら、密な版の停止は T の停止に対応（逆向き）
    4. `NoStuck T c` なら、停止しないことが対応 -/
theorem pconv_main (hW : ZeroShiftHalts T) (hD : Deterministic T) (hR : Reversible T)
    (hQ : ∀ q, q ∈ qs) (hS : ∀ s, s ∈ ss) (hG : Good T L) :
    Deterministic (pconv T L ss) ∧ Reversible (pconv T L ss) ∧
    (∀ (n : Nat) (c cf : Cfg Q P S), HaltsIn T n c cf → (∃ h, cf.st = .halt h) →
      ∃ N, n ≤ N ∧ HaltsIn (pconv T L ss) N (penc T L c) (penc T L cf)) ∧
    (∀ (N : Nat) (c : Cfg Q P S) (e : Cfg PSt P (KSym S)), NoStuck T c →
      HaltsIn (pconv T L ss) N (penc T L c) e →
      ∃ n cf, HaltsIn T n c cf ∧ e = penc T L cf) ∧
    (∀ c : Cfg Q P S, NoStuck T c → ((∀ n cf, ¬ HaltsIn T n c cf) ↔
      (∀ N e, ¬ HaltsIn (pconv T L ss) N (penc T L c) e))) := by
  obtain ⟨-, -, -, hF, -, hI⟩ := spconv_main (qs := qs) (ss := ss) hW hD hR hQ hS hG
  have hDp : Deterministic (pconv T L ss) := pconv_det hW hD hG
  have hsub : ∀ ρ ∈ spconv T L qs ss, ρ ∈ pconv T L ss := fun _ h => spconv_sub h
  -- 前向き: 疎版の停止実行は密な版の実行で、行き着く先は疑似状態なので密な版でも止まっている。
  have fwd : ∀ (n : Nat) (c cf : Cfg Q P S), HaltsIn T n c cf → (∃ h, cf.st = .halt h) →
      ∃ N, n ≤ N ∧ HaltsIn (pconv T L ss) N (penc T L c) (penc T L cf) := by
    intro n c cf h hf
    obtain ⟨N, hN, hs⟩ := hF n c cf h hf
    obtain ⟨hh, hst⟩ := hf
    refine ⟨N, hN, StepN.mono hsub hs.1, halted_of_halt (h := hh) ?_⟩
    simp [penc, hst]
  -- 逆向き: T が止まらなければ疎版は止まらず、密な版も同じだけ進む。
  have bwd : ∀ (N : Nat) (c : Cfg Q P S) (e : Cfg PSt P (KSym S)), NoStuck T c →
      HaltsIn (pconv T L ss) N (penc T L c) e → ∃ n cf, HaltsIn T n c cf ∧ e = penc T L cf :=
    fun N c e hns => back_of_fwd hDp (fun _ cf => penc T L cf)
      (fun n cf h => let ⟨N, _, hN⟩ := fwd n c cf h (hns n cf h); ⟨N, hN⟩)
      (fun hno N _ _ => let ⟨b, hb⟩ := run_forever ((hI c hns).1 hno) N
        ⟨N, Nat.le_refl _, b, StepN.mono hsub hb⟩) N e
  refine ⟨hDp, pconv_rev hW hR hG, fwd, bwd, fun c hns => diverges_iff_of
    (fun n cf hn => let ⟨N, _, hN'⟩ := fwd n c cf hn (hns n cf hn); ⟨N, _, hN'⟩)
    (fun N e he => let ⟨n, cf, hn, _⟩ := bwd N c e hns he; ⟨n, cf, hn⟩)⟩

end URTM.KStatePure
