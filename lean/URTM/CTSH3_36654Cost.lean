/-
  URTM(3,36654) の試験例のステップ数を、表 T3（T†）を回さずに、Lemma 5.9・5.10 の歩数の式と (32,3) の実行から
  出すための道具（C14）。具体例は生成モジュール `URTM.Gen.W3_36654`（`tools/gen_cost36654_lean.py`）。

  道筋（`CTSH3_36654Steps.lean` の、T† そのものをカーネルで回す道筋とは独立）:
  1. (32,3) から停止規則を除いた T32' を `encC32 C w` から回す（`KRun.check`。数百ステップ）。
  2. **Lemma 5.9 の歩数**（`Conv59.halts_sim_exact`）: T32' が N + 1 ステップで止まるなら、T̂ は
     N (2 n0 + N + 3) + (n0 + N + 1) ステップで止まる（`hat_of_run32`）。T̂ を回さずに T̂ のステップ数が出る。
  3. **Lemma 5.10 の歩数**（`Conv510.stepW_sim`）: T̂ の実行に沿って、入った状態の重み `cost3`（q_L なら 1、
     q_j なら 2j + 1）を足した和が T† のステップ数（`dag_of_hat`）。T̂ の実行は `Conv59.hatLookup` で規則を引く
     重みつきの検査器 `freachW`（`KRunW.lean`）をカーネルで評価する（T̂ の 1 ステップは T† の数ステップ〜百数十ステップ）。
  4. 表 T3 は T† と集合として一致する（`sub3`・`sup3`）ので、T3 のステップ数。

  T̂ の初期配置・停止配置は主定理の `Conv59.W 0 n0 0 (encC32 C w)`・`Conv59.E .s0 0 n0 N (unhalt f32 (finCfg32 …))`
  （`E3`・`fin3` はこれらを Lemma 5.10 で符号化したもの）。ジッパーとの一致は窓の中を具体例で `decide` し、
  窓の外の空白は詰め方の定義（`Conv59.pack_out`）から示す（`W0_eq_zip`・`E_eq_zip`）。

  mathlib 非依存。未証明の穴・新規公理・native_decide を使わない。
-/
import URTM.CTSH3_36654Thm
import URTM.Conv59Exact
import URTM.Conv510Exact
import URTM.KRunW

set_option maxRecDepth 100000

namespace URTM.CTSH.U3_36654

open URTM URTM.KState URTM.CTSH URTM.SimLemmas URTM.Gen.K32_3 URTM.Gen.F3_36654 URTM.Gen.V3_36654
open URTM.KState.Run URTM.KState.RunF
open URTM.Conv55 (FSym)
open URTM.Conv59 (WSt WSym)
open URTM.Conv510 (TSt)
open URTM.CTSH.U32_3 (encC32 finCfg32 nm32)

/-- T̂ の空白（Lemma 5.9 の b）。 -/
abbrev bkh : WSym St Sy := .bl

/-- T̂ の規則の引き当て（`Conv59.hatLookup`）。 -/
def lookH : WSt St Sy → WSym St Sy → Option (Rule (WSt St Sy) Ps (WSym St Sy)) :=
  Conv59.hatLookup T32' .s0 qp32

/-- Lemma 5.10 の歩数: T̂ が状態 q に入ったときの T† のステップ数（q_L なら 1、q_j なら 2j + 1、j = idx3 q）。 -/
abbrev cost3 : Tgt (WSt St Sy) Ps → Nat := Conv510.cost .L idx3

/-- `lookH` の値は T̂ の規則。 -/
theorem lookH_mem : ∀ p s r, lookH p s = some r → r ∈ That := fun _ _ _ h => Conv59.hatLookup_sound hS hQ h

/-- 重みつきの検査器が通れば、T̂ はジッパー z の配置から m の配置へちょうど n ステップで進み、
    入った状態の Lemma 5.10 の歩数の和は w。 -/
theorem hat_of_reachW {n w : Nat} {z m : Zip (WSt St Sy) Ps (WSym St Sy)}
    (h : freachW bkh lookH cost3 n z m w = true) : StepW That cost3 n w (z.cfg bkh) (m.cfg bkh) :=
  stepW_of_reachW lookH_mem h

/-- 検査器が通れば、T32' はジッパー z の配置からちょうど n ステップで停止配置 e に達する（`KRun.check`）。 -/
theorem run32_of_check {n : Nat} {z e : Zip St Ps Sy} (h : check .s0 T32' n z e = true) :
    HaltsIn T32' n (z.cfg .s0) (e.cfg .s0) :=
  halts_of_check h

/-! ## T̂ の配置とジッパー -/

/-- 配置 c の状態・ヘッド位置がジッパー z と同じで、テープが z の並びの窓の中で一致し、窓の外が空白なら、
    c は z の表す配置そのもの（`CTSH3_36654Steps.eq_zip_of_window` の、機械の型に依らない形）。 -/
theorem eq_zip_of_window' {Q P S : Type} {bk : S} {c : Cfg Q P S} {z : Zip Q P S}
    (hst : c.st = z.st) (hpos : c.pos = (z.l.length : Int))
    (hout : ∀ i : Int, i < 0 ∨ ((z.l.reverse ++ z.h :: z.r).length : Int) ≤ i → c.tape i = bk)
    (hwin : (List.range (z.l.reverse ++ z.h :: z.r).length).map (fun i => c.tape (Int.ofNat i)) =
      z.l.reverse ++ z.h :: z.r) :
    c = z.cfg bk := by
  obtain ⟨cst, cpos, ctape⟩ := c
  simp only at hst hpos hout hwin
  have htape : ctape = URTM.CTSH.Sim.tp bk (z.l.reverse ++ z.h :: z.r) := by
    funext i
    cases i with
    | negSucc k => exact hout _ (.inl (Int.negSucc_lt_zero k))
    | ofNat k =>
      show _ = (z.l.reverse ++ z.h :: z.r).getD k bk
      by_cases hk : k < (z.l.reverse ++ z.h :: z.r).length
      · have : ((List.range (z.l.reverse ++ z.h :: z.r).length).map (fun i => ctape (Int.ofNat i))).getD k bk =
            (z.l.reverse ++ z.h :: z.r).getD k bk := by rw [hwin]
        rw [← this, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]
        rfl
      · rw [hout _ (.inr (by rw [Int.ofNat_eq_natCast]; omega)), List.getD_eq_getElem?_getD,
          List.getElem?_eq_none (by omega)]
        rfl
  subst hst hpos htape
  rfl

/-- **T̂ の初期配置とジッパー**: 窓 [0, n0] の中で `W 0 n0 0 (encC32 C w)` のテープが `z.h :: z.r` と一致し、
    z が状態 L・ヘッド 0（`z.l = []`）なら、T̂ の初期配置はジッパー z の表す配置そのもの。 -/
theorem W0_eq_zip (C : CTSH) (w : List Ch) (n0 : Nat) (z : Zip (WSt St Sy) Ps (WSym St Sy))
    (hst : z.st = .go .L) (hl : z.l = []) (hlen : z.r.length = n0)
    (hwin : (List.range (n0 + 1)).map (fun i => (Conv59.W 0 n0 0 (encC32 C w)).tape (Int.ofNat i)) = z.h :: z.r) :
    Conv59.W 0 n0 0 (encC32 C w) = z.cfg bkh := by
  have hL : (z.l.reverse ++ z.h :: z.r).length = n0 + 1 := by simp [hl, hlen]
  have hL' : z.l.reverse ++ z.h :: z.r = z.h :: z.r := by simp [hl]
  refine eq_zip_of_window' (by rw [hst]; rfl) (by rw [hl]; rfl) (fun i h => ?_) ?_
  · show Conv59.pack _ (n0 + 0) _ _ _ i = bkh
    rw [hL] at h
    rw [Conv59.pack_out (by push_cast at h; omega)]
  · rw [hL, hL']; exact hwin

/-- T̂ の停止配置（N ≥ 1）は `Conv59.haltW` の形（状態 h(s0)、テープは位置 1..n0+N−1 の組）。 -/
theorem E_haltW (n0 : Nat) (C : CTSH) (vf : List Ch) (mf : Nat) (rm : List Ch) {N : Nat} (hN : 1 ≤ N) :
    ∃ st x g, Conv59.E Sy.s0 0 n0 N (unhalt f32 (finCfg32 C vf mf rm)) =
      Conv59.haltW Sy.s0 (0 - N) (n0 + N - 1) st x g := by
  obtain ⟨st, x, g, hst⟩ : ∃ st x g,
      (unhalt f32 (finCfg32 C vf mf rm)) = { st := .go st, pos := x, tape := g } := by
    cases vf <;> exact ⟨_, _, _, rfl⟩
  exact ⟨st, x, g, by simp only [Conv59.E, hst, Nat.pos_iff_ne_zero.mp hN, if_false]⟩

/-- **T̂ の停止配置とジッパー**: N ≥ 1 で、T̂ の停止配置の状態・ヘッド位置がジッパー z と同じ、z の並びが
    位置 n0 + N − 1 を覆い、その窓の中でテープが一致するなら、停止配置は z の表す配置そのもの。 -/
theorem E_eq_zip {n0 : Nat} {C : CTSH} {vf : List Ch} {mf : Nat} {rm : List Ch} {N : Nat}
    {z : Zip (WSt St Sy) Ps (WSym St Sy)} (hN : 1 ≤ N)
    (hst : (Conv59.E Sy.s0 0 n0 N (unhalt f32 (finCfg32 C vf mf rm))).st = z.st)
    (hpos : (Conv59.E Sy.s0 0 n0 N (unhalt f32 (finCfg32 C vf mf rm))).pos = (z.l.length : Int))
    (hlen : n0 + N ≤ (z.l.reverse ++ z.h :: z.r).length)
    (hwin : (List.range (z.l.reverse ++ z.h :: z.r).length).map
      (fun i => (Conv59.E Sy.s0 0 n0 N (unhalt f32 (finCfg32 C vf mf rm))).tape (Int.ofNat i)) =
      z.l.reverse ++ z.h :: z.r) :
    Conv59.E Sy.s0 0 n0 N (unhalt f32 (finCfg32 C vf mf rm)) = z.cfg bkh := by
  refine eq_zip_of_window' hst hpos (fun i h => ?_) hwin
  obtain ⟨st, x, g, he⟩ := E_haltW n0 C vf mf rm hN
  rw [he]
  show Conv59.pack _ _ _ _ _ i = bkh
  rw [Conv59.pack_out (by omega)]

/-! ## 2 つの式の合成 -/

/-- **Lemma 5.9 の歩数を (32,3) の実行に当てる**: T32' が `encC32 C w` から N + 1 ステップで止まるなら、
    T̂ は主定理の初期配置からちょうど N (2 n0 + N + 3) + (n0 + N + 1) ステップで止まる。 -/
theorem hat_of_run32 {C : CTSH} {w : List Ch} {n0 : Nat}
    (hn0 : (URTM.CTSH.U32_3.RA nm32 C 0).length + 6 ≤ 2 * n0 ∧
      (URTM.CTSH.U32_3.tapeList nm32 C 0 [] w).length + 1 ≤ 2 * n0)
    {N : Nat} {vf : List Ch} {mf : Nat} {rm : List Ch}
    (h : HaltsIn T32' (N + 1) (encC32 C w) (unhalt f32 (finCfg32 C vf mf rm))) :
    HaltsIn That (N * (2 * n0 + N + 3) + (n0 + N + 1)) (Conv59.W 0 n0 0 (encC32 C w))
      (Conv59.E Sy.s0 0 n0 (N + 1) (unhalt f32 (finCfg32 C vf mf rm))) :=
  Conv59.halts_sim_exact hyp59 (p0 := St.q0) rfl (inv0 C w n0 hn0) h

/-- **Lemma 5.10 の歩数を T̂ の実行に沿って足す**: T̂ が主定理の初期配置から停止配置（N ≥ 1）まで K ステップで進み、
    入った状態の歩数 `cost3` の和が M なら、表 T3 は主定理の初期配置 `E3 C w n0` からちょうど M ステップで
    主定理の停止配置 `fin3 n0 C vf mf rm N` に止まる。 -/
theorem dag_of_hat {C : CTSH} {w : List Ch} {n0 : Nat} {vf : List Ch} {mf : Nat} {rm : List Ch} {N K M : Nat}
    (hN : 1 ≤ N)
    (hW : StepW That cost3 K M (Conv59.W 0 n0 0 (encC32 C w))
      (Conv59.E Sy.s0 0 n0 N (unhalt f32 (finCfg32 C vf mf rm)))) :
    HaltsIn T3 M (E3 C w n0) (fin3 n0 C vf mf rm N) := by
  obtain ⟨st, x, g, he⟩ := E_haltW n0 C vf mf rm hN
  have hh : HaltsIn Tdag M (E3 C w n0) (fin3 n0 C vf mf rm N) :=
    Conv510.haltsW_sim hyp510 hW (p := .h .s0) (by rw [he]; rfl) (by rw [he]; exact Conv59.haltW_halted _ _ _ _ _)
  exact HaltsIn.congr sup3 sub3 hh

end URTM.CTSH.U3_36654
