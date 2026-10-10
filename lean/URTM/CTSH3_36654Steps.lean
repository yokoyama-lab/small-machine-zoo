/-
  URTM(3,36654) の試験例の停止までのステップ数を、記述ファイルの表 `T3`（37936 本）そのものについて
  カーネルの評価で示すための道具。具体例（記述ファイルの 3 つの試験例）は生成モジュール
  `URTM.Gen.S3_36654`（`tools/gen_steps36654_lean.py`）。

  * 表の引き当ては線形の探索ではなく、T† の規則を (状態, 記号) から作る `look3`（CTSH3_36654Main.lean）を使う。
    `look3` の値が表の規則であること（`look3_mem`）は引き当ての健全性 `Conv510.lookup_sound`・
    `Conv59.hatLookup_sound` と T† ⊆ 表（`sup3`）から、表の規則がどれも `look3` で引けること（`look3_complete`）は
    表の照合 `chk3` そのもの。
  * 検査器は `KRunF`（`fcheck`・`freach`）。健全性は一般証明。
  * 主定理の初期配置 `E3 C w n0` と停止配置 `fin3 n0 C vf mf rm N` が、記述ファイルの初期配置・Python で
    実行した停止配置（ジッパー）と等しいこと（`E3_eq_zip`・`fin3_eq_zip`）。窓の中の一致だけを具体例で `decide` し、
    窓の外の空白は詰め方の定義（`Conv59.pack_out`）から示す。
  * 決定性（`hD3`）により、主定理の停止（`urtm3_36654_simulates_ctsh`）のステップ数と停止配置は、
    ジッパーで示した実行のものに一致する（`steps_E3`。N と rm を与えずに言える形）。

  mathlib 非依存。未証明の穴・新規公理・native_decide を使わない。
-/
import URTM.CTSH3_36654Thm
import URTM.KRunF

set_option maxRecDepth 100000

namespace URTM.CTSH.U3_36654

open URTM URTM.KState URTM.CTSH URTM.SimLemmas URTM.Gen.K32_3 URTM.Gen.F3_36654 URTM.Gen.V3_36654
open URTM.KState.Run URTM.KState.RunF
open URTM.Conv55 (FSym)
open URTM.Conv59 (WSt WSym)
open URTM.Conv510 (TSt)
open URTM.CTSH.U32_3 (encC32 finCfg32 nm32)

/-- 記述ファイルの空白 `b`。 -/
abbrev bk3 : FSym (WSym St Sy) := .pl .bl

/-- `look3` の値は表の規則。 -/
theorem look3_mem : ∀ p s ρ, look3 p s = some ρ → ρ ∈ T3 := fun _ _ ρ h =>
  sup3 ρ (Conv510.lookup_sound (T := That) (ss := allW) allW_all
    (fun _ _ _ hh => Conv59.hatLookup_sound hS hQ hh) h)

/-- 表の規則はどれも自分の (状態, 記号) で `look3` に引ける（表の照合 `chk3`）。 -/
theorem look3_complete : ∀ ρ ∈ T3, look3 ρ.p ρ.s = some ρ := chk3

/-- 検査器が通れば、表 `T3` はジッパー `z` の配置からちょうど `n` ステップで停止配置 `e` に達する。 -/
theorem halts3_of_check {n : Nat} {z e : Zip TSt Ps (FSym (WSym St Sy))}
    (h : fcheck bk3 look3 n z e = true) : HaltsIn T3 n (z.cfg bk3) (e.cfg bk3) :=
  fhalts_of_check look3_mem look3_complete h

/-- 分割した実行の合成。 -/
theorem halts3_of_reach {a b : Nat} {z m e : Zip TSt Ps (FSym (WSym St Sy))}
    (h : freach bk3 look3 a z m = true) (h' : HaltsIn T3 b (m.cfg bk3) (e.cfg bk3)) :
    HaltsIn T3 (a + b) (z.cfg bk3) (e.cfg bk3) :=
  fhalts_of_reach look3_mem h h'

/-! ## 主定理の初期配置・停止配置とジッパー -/

/-- 配置 `c` の状態・ヘッド位置がジッパー `z` と同じで、テープが `z` の並びの窓の中で一致し、窓の外が空白なら、
    `c` は `z` の表す配置そのもの。 -/
theorem eq_zip_of_window {c : Cfg TSt Ps (FSym (WSym St Sy))} {z : Zip TSt Ps (FSym (WSym St Sy))}
    (hst : c.st = z.st) (hpos : c.pos = (z.l.length : Int))
    (hout : ∀ i : Int, i < 0 ∨ ((z.l.reverse ++ z.h :: z.r).length : Int) ≤ i → c.tape i = bk3)
    (hwin : (List.range (z.l.reverse ++ z.h :: z.r).length).map (fun i => c.tape (Int.ofNat i)) =
      z.l.reverse ++ z.h :: z.r) :
    c = z.cfg bk3 := by
  obtain ⟨cst, cpos, ctape⟩ := c
  simp only at hst hpos hout hwin
  have htape : ctape = URTM.CTSH.Sim.tp bk3 (z.l.reverse ++ z.h :: z.r) := by
    funext i
    cases i with
    | negSucc k => exact hout _ (.inl (Int.negSucc_lt_zero k))
    | ofNat k =>
      show _ = (z.l.reverse ++ z.h :: z.r).getD k bk3
      by_cases hk : k < (z.l.reverse ++ z.h :: z.r).length
      · have : ((List.range (z.l.reverse ++ z.h :: z.r).length).map (fun i => ctape (Int.ofNat i))).getD k bk3 =
            (z.l.reverse ++ z.h :: z.r).getD k bk3 := by rw [hwin]
        rw [← this, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]
        rfl
      · rw [hout _ (.inr (by rw [Int.ofNat_eq_natCast]; omega)), List.getD_eq_getElem?_getD,
          List.getElem?_eq_none (by omega)]
        rfl
  subst hst hpos htape
  rfl

/-- `E3 C w n0` の状態は L、ヘッドは 0、テープは位置 1..n0 の外が空白。 -/
theorem E3_st (C : CTSH) (w : List Ch) (n0 : Nat) : (E3 C w n0).st = .go .L := rfl
theorem E3_pos (C : CTSH) (w : List Ch) (n0 : Nat) : (E3 C w n0).pos = 0 := rfl
theorem E3_out (C : CTSH) (w : List Ch) (n0 : Nat) (i : Int) (h : i < 1 ∨ (n0 : Int) < i) :
    (E3 C w n0).tape i = bk3 := by
  show FSym.pl (Conv59.pack _ (n0 + 0) _ _ _ i) = bk3
  rw [Conv59.pack_out (by omega)]

/-- **初期配置の一致**: 窓 [0, n0] の中で `E3 C w n0` のテープが `z.h :: z.r` と一致し、`z` が状態 L・ヘッド 0
    （`z.l = []`）なら、`E3 C w n0` はジッパー `z` の表す配置そのもの。 -/
theorem E3_eq_zip (C : CTSH) (w : List Ch) (n0 : Nat) (z : Zip TSt Ps (FSym (WSym St Sy)))
    (hst : z.st = .go .L) (hl : z.l = []) (hlen : z.r.length = n0)
    (hwin : (List.range (n0 + 1)).map (fun i => (E3 C w n0).tape (Int.ofNat i)) = z.h :: z.r) :
    E3 C w n0 = z.cfg bk3 := by
  have hL : (z.l.reverse ++ z.h :: z.r).length = n0 + 1 := by simp [hl, hlen]
  have hL' : z.l.reverse ++ z.h :: z.r = z.h :: z.r := by simp [hl]
  refine eq_zip_of_window (by rw [hst]; rfl) (by rw [hl]; rfl) (fun i h => E3_out C w n0 i ?_) ?_
  · rw [hL] at h; push_cast at h; omega
  · rw [hL, hL']; exact hwin

/-- 主定理の停止配置 `fin3 n0 C vf mf rm N`（N ≥ 1）のテープは、位置 1..n0+N の外が空白。 -/
theorem fin3_out (n0 : Nat) (C : CTSH) (vf : List Ch) (mf : Nat) (rm : List Ch) {N : Nat} (hN : 1 ≤ N)
    (i : Int) (h : i < 1 ∨ ((n0 + N : Nat) : Int) < i) : (fin3 n0 C vf mf rm N).tape i = bk3 := by
  obtain ⟨st, x, g, hst⟩ : ∃ st x g,
      (unhalt f32 (finCfg32 C vf mf rm)) = { st := .go st, pos := x, tape := g } := by
    cases vf <;> exact ⟨_, _, _, rfl⟩
  simp only [fin3, hst, Conv59.E, Nat.pos_iff_ne_zero.mp hN, if_false, Conv59.haltW, Conv510.enc,
    show (WSt.h Sy.s0 : WSt St Sy) ≠ .L from nofun, if_false]
  rw [Conv55.upd_ne _ _ (by omega), Conv59.pack_out (by omega)]

/-- **停止配置の一致**: N ≥ 1 で、`fin3 n0 C vf mf rm N` の状態・ヘッド位置がジッパー `z` と同じ、
    `z` の並びが位置 n0+N を覆い、その窓の中でテープが一致するなら、`fin3 n0 C vf mf rm N` は `z` の表す配置そのもの。 -/
theorem fin3_eq_zip {n0 : Nat} {C : CTSH} {vf : List Ch} {mf : Nat} {rm : List Ch} {N : Nat}
    {z : Zip TSt Ps (FSym (WSym St Sy))} (hN : 1 ≤ N)
    (hst : (fin3 n0 C vf mf rm N).st = z.st) (hpos : (fin3 n0 C vf mf rm N).pos = (z.l.length : Int))
    (hlen : n0 + N < (z.l.reverse ++ z.h :: z.r).length)
    (hwin : (List.range (z.l.reverse ++ z.h :: z.r).length).map (fun i => (fin3 n0 C vf mf rm N).tape (Int.ofNat i)) =
      z.l.reverse ++ z.h :: z.r) :
    fin3 n0 C vf mf rm N = z.cfg bk3 :=
  eq_zip_of_window hst hpos (fun i h => fin3_out n0 C vf mf rm hN i (by omega)) hwin

/-- **ステップ数の移送**: `E3 C w n0` がジッパー `z` の配置で、表がそこからちょうど M ステップで `e` に止まるなら、
    主定理の停止配置 `fin3 n0 C vf mf rm N` に止まる実行（存在は主定理が与える）のステップ数も M で、
    停止配置は `e` の表す配置。 -/
theorem steps_E3 {C : CTSH} {w : List Ch} {n0 M : Nat} {z e : Zip TSt Ps (FSym (WSym St Sy))}
    (hz : E3 C w n0 = z.cfg bk3) (hM : HaltsIn T3 M (z.cfg bk3) (e.cfg bk3))
    {vf : List Ch} {mf : Nat}
    (hex : ∃ N M' rm, HaltsIn T3 M' (E3 C w n0) (fin3 n0 C vf mf rm N)) :
    ∃ N rm, HaltsIn T3 M (E3 C w n0) (fin3 n0 C vf mf rm N) ∧ fin3 n0 C vf mf rm N = e.cfg bk3 := by
  obtain ⟨N, M', rm, h⟩ := hex
  rw [hz] at h ⊢
  have he : fin3 n0 C vf mf rm N = e.cfg bk3 := halts_unique hD3 h hM
  exact ⟨N, rm, he ▸ hM, he⟩

end URTM.CTSH.U3_36654
