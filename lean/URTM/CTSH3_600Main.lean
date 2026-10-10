/-
  URTM(3,600)（改良版の 3 状態化の反転版 ∘ (32,3)、docs/09_three_state_2026-09-26.md）が任意の CTSH を模倣すること。

  * 一般定理 `Conv3S.convM_main`（Conv3S.lean。Conv1W.lean の 1WU 化・Conv3P.lean の 3 状態化・Conv3Base.lean の
    左右反転の合成）は、任意の（停止規則を除いた）決定的・可逆な T について、反転してから変換し反転し直した機械が
    T を模倣し、決定的・可逆であることを与える。
  * 具体の機械は生成モジュール `URTM.Gen.T3_600`（tools/gen_threestate_lean.py）にあり、`Conv3S.convM` の値が
    Python（tools/threestate.py convert --mirror）の表 `T3py` と規則の並びまで一致し、記号は重複の無い 600 個、
    規則は 1572 本（いずれも `decide +kernel`）。一般定理の仮定（番号付け・刈り込み）も同じ所で有限検査している。
  * 合成: `U32_3.urtm32_3_simulates_ctsh`（(32,3) の CTSH 模倣）→ `SimLemmas.drop_simulates`（停止規則の除去）
    → `Conv3S.convM_main`。

  初期配置: U32_3 の Morita の初期配置 `encC32 C w` を、テープの長さ len から決まる窓（始まり −len−1、長さ len+3）で
  符号化したもの（`E600`）。テープは両側無限で、記述ファイルの有限の切り出し（左に詰めた空白）には依存しない。
  停止配置は T' のステップ数 N に依る（毎掃引でテープが 1 マスずれるので）。

  生成モジュールに依存するので、`tools/gen_all_lean.sh`（CI）が書く `URTM.lean` 経由でビルドされる。
  未証明の穴・新規公理・native_decide を使わない。
-/
import URTM.CTSH32_3Main
import URTM.Gen.T3_600

set_option maxRecDepth 100000

namespace URTM.CTSH.U3_600

open URTM URTM.KState URTM.CTSH URTM.SimLemmas URTM.Conv3Base URTM.Gen.K32_3 URTM.Gen.T3_600
open URTM.Conv1W (VSt VSym isPlus)
open URTM.Conv3P (CSym)
open URTM.Conv510 (TSt)
open URTM.CTSH.U32_3 (encC32 finCfg32 urtm32_3_simulates_ctsh nm32)

/-- 疑似状態へ入る規則の現状態: null ← begin（q0）、halt ← case_y_2（q2）。 -/
def f32 : Ps → St
  | .h0 => .q0
  | .h1 => .q2

theorem hH32 : HaltRulesId T f32 := by decide

/-- U32_3 の初期テープの長さ。 -/
def len32 (C : CTSH) (w : List Ch) : Nat := (URTM.CTSH.U32_3.tapeList nm32 C 0 [] w).length

/-- 反転した T' の窓の始まりと長さ。 -/
def a0 (C : CTSH) (w : List Ch) : Int := -((len32 C w : Nat) : Int) - 1
def n0 (C : CTSH) (w : List Ch) : Nat := len32 C w + 3

/-- **URTM(3,600) の初期配置**: Morita の (32,3) の初期配置 `encC32 C w` の符号化（`Conv3S.encM`）。 -/
def E600 (C : CTSH) (w : List Ch) : Cfg TSt Ps (CSym (VSym St Sy)) :=
  Conv3S.encM T' idx (a0 C w) (n0 C w) (encC32 C w)

/-- **停止配置**: U32_3 の停止配置から停止規則を戻し（`unhalt f32`）、T' が N ステップで達したときの符号化。 -/
def fin600 (C : CTSH) (w : List Ch) (vf : List Ch) (mf : Nat) (rm : List Ch) (N : Nat) :
    Cfg TSt Ps (CSym (VSym St Sy)) :=
  Conv3S.finM T' idx (a0 C w) (n0 C w) N (unhalt f32 (finCfg32 C vf mf rm))

theorem q0_minus : isPlus TR St.q0 = false := by decide +kernel

theorem len32_eq (C : CTSH) (w : List Ch) :
    len32 C w = (URTM.CTSH.U32_3.RA nm32 C 0).length + 2 + w.length := by
  simp [len32, URTM.CTSH.U32_3.tapeList]; omega

/-- 初期配置（を折り返したもの）は不変量を満たす。 -/
theorem inv0 (C : CTSH) (w : List Ch) :
    Conv1W.Inv TR Sy.s0 GlR (a0 C w) (n0 C w) St.q0 (-(encC32 C w).pos) (fun i => (encC32 C w).tape (-i)) := by
  have hl := len32_eq C w
  have hl2 : (URTM.CTSH.U32_3.tapeList nm32 C 0 [] w).length = len32 C w := rfl
  simp only [encC32, URTM.CTSH.U32_3.encC, URTM.CTSH.U32_3.rep, List.length_nil, a0, n0]
  refine ⟨by omega, by omega, fun j hj => ?_, fun h => by rw [q0_minus] at h; cases h⟩
  rcases hj with hj | hj
  · obtain ⟨k, hk⟩ : ∃ k : Nat, -j = (k : Int) := ⟨(-j).toNat, by omega⟩
    rw [hk, URTM.CTSH.Sim.tp_ofNat, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl
  · obtain ⟨k, hk⟩ : ∃ k : Nat, -j = Int.negSucc k := ⟨(j - 1).toNat, by omega⟩
    rw [hk]; rfl

/-- **主定理（URTM(3,600) は任意の CTSH を模倣する）**。U3_600 = `T3py`（`tools/threestate.py convert --mirror` の
    1572 本。一般の変換 `Conv3S.convM` を (32,3) から停止規則を除いた T' に適用した値と一致）は決定的・可逆で、
    状態は 3 個、記号は重複の無い 600 個の `sym3py` に入る。任意の CTSH C と初期語 w について、初期配置 `E600 C w` から:

    1. C が (w, 0) から n ステップで停止 ID (vf, mf) に達するなら、T' は `encC32 C w` から N ステップ（n ≤ N + 1）で
       `unhalt f32 (finCfg32 C vf mf rm)` に止まり、U3_600 は `fin600 C w vf mf rm N` で止まる。
    2. 逆に U3_600 が止まるなら C も止まり、停止配置は 1 の形。
    3. C が停止しない ⇔ U3_600 が停止しない。 -/
theorem urtm3_600_simulates_ctsh (C : CTSH) (w : List Ch) :
    Deterministic T3py ∧ Reversible T3py ∧
    (∀ x : TSt, x ∈ [TSt.L, .R0, .R1]) ∧
    (∀ ρ ∈ T3py, ρ.s ∈ sym3py ∧ ρ.t ∈ sym3py) ∧ sym3py.length = 600 ∧ sym3py.Nodup ∧ T3py.length = 1572 ∧
    Conv3S.convM T' Sy.s0 ss qmR RlR GlR idx need = T3py ∧
    (∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) →
      ∃ N M rm, n ≤ N + 1 ∧ HaltsIn T' N (encC32 C w) (unhalt f32 (finCfg32 C vf mf rm)) ∧
        HaltsIn T3py M (E600 C w) (fin600 C w vf mf rm N)) ∧
    (∀ M e, HaltsIn T3py M (E600 C w) e →
      ∃ n vf mf rm N, CHaltsIn C n (w, 0) (vf, mf) ∧
        HaltsIn T' N (encC32 C w) (unhalt f32 (finCfg32 C vf mf rm)) ∧ e = fin600 C w vf mf rm N) ∧
    ((∀ n f, ¬ CHaltsIn C n (w, 0) f) ↔ (∀ M e, ¬ HaltsIn T3py M (E600 C w) e)) := by
  have h32 := urtm32_3_simulates_ctsh C w
  have hfin : ∀ vf mf rm, ∃ h, (finCfg32 C vf mf rm).st = .halt h := by
    intro vf mf rm; cases vf <;> exact ⟨_, rfl⟩
  have hd := drop_simulates hD hH32 C w (encC32 C w) ⟨.q0, rfl⟩ (finCfg32 C) hfin ⟨h32.1, h32.2.1⟩
  have hm := Conv3S.convM_main hyp (c0 := encC32 C w) rfl (inv0 C w)
  rw [convM_eq_py] at hm
  obtain ⟨hD3, hR3, hf, hb⟩ := hm
  have hsyms := Conv3S.convM_syms hyp hsrc
  rw [convM_eq_py, univ_eq_py] at hsyms
  have fwd : ∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) →
      ∃ N M rm, n ≤ N + 1 ∧ HaltsIn T' N (encC32 C w) (unhalt f32 (finCfg32 C vf mf rm)) ∧
        HaltsIn T3py M (E600 C w) (fin600 C w vf mf rm N) := by
    intro n vf mf hc
    obtain ⟨N, rm, hN, hh⟩ := hd.1 n vf mf hc
    obtain ⟨M, _, hM⟩ := hf N _ hh
    exact ⟨N, M, rm, hN, hh, hM⟩
  have bwd : ∀ M e, HaltsIn T3py M (E600 C w) e →
      ∃ n vf mf rm N, CHaltsIn C n (w, 0) (vf, mf) ∧
        HaltsIn T' N (encC32 C w) (unhalt f32 (finCfg32 C vf mf rm)) ∧ e = fin600 C w vf mf rm N := by
    intro M e he
    obtain ⟨N, e₀, h₀, rfl⟩ := hb M e he
    obtain ⟨n, vf, mf, rm, hc, rfl⟩ := hd.2.1 N e₀ h₀
    exact ⟨n, vf, mf, rm, N, hc, h₀, rfl⟩
  refine ⟨hD3, hR3, fun x => by cases x <;> simp, hsyms, card3.1, sym3py_nodup, card3.2, convM_eq_py, fwd, bwd, ?_⟩
  constructor
  · intro hn M e he
    obtain ⟨n, vf, mf, rm, N, hc, _⟩ := bwd M e he
    exact hn n _ hc
  · intro hu n ⟨vf, mf⟩ hc
    obtain ⟨N, M, rm, _, _, hM⟩ := fwd n vf mf hc
    exact hu M _ hM

end URTM.CTSH.U3_600
