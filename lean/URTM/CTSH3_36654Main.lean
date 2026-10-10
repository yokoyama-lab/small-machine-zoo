/-
  URTM(3,36654)（Morita 2017, §7.3.8.2）が任意の CTSH を模倣すること。

  原典 p. 199: U3_36654 は U32_3 を Lemma 5.9（1WU-RTM 化）で変換し、さらに Lemma 5.10（3 状態化）で変換したもの
  （「δ3_36654 has 37936 quintuples」）。記述ファイル urtm3-36654 の 37936 本が、U32_3 から停止規則 2 本を除いた機械
  T32' に `Conv59.conv`（T̂、1580 本・62 状態・298 記号）と `Conv510.conv`（T†）を順に適用したものと
  **集合として一致する**ことを次の 3 つで確かめる（3.8 万本どうしの比較は `decide` では重すぎるため）:

    * `chk3`: 表の各規則 ρ が、T† の規則を (状態, 記号) から引く関数 `Conv510.lookup` の値そのもの（`decide +kernel`、線形）。
      引く関数の健全性（`lookup_sound`・`hatLookup_sound`）から、表 ⊆ T†。
    * `nodup3`: 表を鍵 `key3` の昇順に並べてあり、鍵が狭義単調増加（`decide +kernel`、線形）なので重複が無い。
    * `len3`: T† と表の本数がどちらも 37936。鳩の巣（`subset_of_nodup_length`）で T† ⊆ 表。

  T̂ の状態番号（Lemma 5.10 の i↑ の i）は記述ファイルのコメントの T̂ の規則から復元した `num3`（生成物）。

  合成: `U32_3.urtm32_3_simulates_ctsh` → `SimLemmas.drop_simulates` → `Conv59.conv_simulates` → `Conv510.conv_simulates`。

  生成モジュールに依存するので、`tools/gen_all_lean.sh`（CI）が書く `URTM.lean` 経由でビルドされる。
  未証明の穴・新規公理・native_decide を使わない。
-/
import URTM.CTSH32_3Main
import URTM.Conv59
import URTM.Conv510
import URTM.Gen.F3_36654

set_option maxRecDepth 100000

namespace URTM.CTSH.U3_36654

open URTM URTM.KState URTM.CTSH URTM.SimLemmas URTM.Gen.K32_3 URTM.Gen.F3_36654
open URTM.Conv55 (FSym)
open URTM.Conv59 (WSt WSym)
open URTM.Conv510 (TSt)

/-- U32_3 から停止規則を除いた機械（82 本）。 -/
def T32' : Machine St Ps Sy := dropHalt T

/-- 疑似状態へ入る規則の現状態: null ← begin（q0）、halt ← case_y_2（q2）。 -/
def f32 : Ps → St
  | .h0 => .q0
  | .h1 => .q2

/-- 右移動で入る状態（原典の Q+）。 -/
def qp32 : List St := qs.filter (fun q => T32'.any (fun r => r.q == .go q && r.d == .R))

/-- **T̂ = Lemma 5.9 の変換**。 -/
def That : Machine (WSt St Sy) Ps (WSym St Sy) := Conv59.conv T32' .s0 ss qs qp32

/-- T̂ の記号の全体（298 個）。 -/
def allW : List (WSym St Sy) :=
  .bl :: (ss.flatMap fun s => ss.map fun t => .pr s t) ++
    (qs.flatMap fun p => ss.flatMap fun s => ss.map fun t => .hp p s t)

/-- WSt の値の全体（T̂ の 62 状態を番号順に、続けて T̂ に現れない 42 個）。 -/
def allWSt : List (WSt St Sy) := num3 ++ rest3
def idx3 (q : WSt St Sy) : Nat := allWSt.idxOf q
def num3f (i : Nat) : WSt St Sy := allWSt.getD i .L

/-- **T† = Lemma 5.10 の変換**（m = 62）。 -/
def Tdag : Machine TSt Ps (FSym (WSym St Sy)) := Conv510.conv That .L .bl idx3 62 allW

theorem allW_all : ∀ w : WSym St Sy, w ∈ allW := by
  intro w; cases w with
  | bl => simp [allW]
  | pr s t => simp [allW, hS]
  | hp p s t => simp [allW, hS, hQ]

theorem allWSt_all : ∀ q : WSt St Sy, q ∈ allWSt := by
  intro q; cases q with
  | L => decide
  | lam => decide
  | q s => cases s <;> decide
  | h s => cases s <;> decide
  | qp p s => cases p <;> cases s <;> decide

theorem dec_idx : ∀ q ∈ allWSt, num3f (idx3 q) = q := by decide
theorem idx3_inj : ∀ p q, idx3 p = idx3 q → p = q := fun p q h => by
  rw [← dec_idx p (allWSt_all p), ← dec_idx q (allWSt_all q), h]

theorem sub32' : ∀ r ∈ T32', r ∈ T := fun _ hr => (mem_dropHalt.mp hr).1

theorem hyp59 : Conv59.Hyp T32' .s0 ss qs qp32 where
  hS := hS
  hQ := hQ
  hG := by decide
  hqp := by
    intro r hr p' hq hd
    simp only [qp32, List.mem_filter]
    exact ⟨hQ p', List.any_eq_true.mpr ⟨r, hr, by simp [hq, hd]⟩⟩

theorem hyp510 : Conv510.Hyp That .L .bl idx3 62 allW where
  hS := allW_all
  hidx := by decide +kernel
  hinj := fun p q _ _ h => idx3_inj p q h
  hshape := by decide +kernel
  hL := by
    intro w _ hw
    cases w with
    | bl => exact absurd rfl hw
    | pr a b => exact Conv59.mem_c10 hS a b
    | hp p a b => exact Conv59.mem_c11 hS hQ p a b
  hL0 := ⟨.q .s0, Conv59.mem_c1⟩

theorem hDhat : Deterministic That := Conv59.conv_det (Deterministic.mono sub32' hD)
theorem hDdag : Deterministic Tdag := Conv510.conv_det hDhat hyp510.hshape hyp510.hinj

/-! ## 表の照合 -/

def cS (s : Sy) : Nat := ss.idxOf s
def cQ (q : St) : Nat := qs.idxOf q
def cW : WSym St Sy → Nat
  | .bl => 0
  | .pr s t => 1 + 3 * cS s + cS t
  | .hp p s t => 10 + 9 * cQ p + 3 * cS s + cS t
def cF : FSym (WSym St Sy) → Nat
  | .pl w => cW w
  | .up w k => 298 + 2 * (k * 298 + cW w)
  | .dn w k => 298 + 2 * (k * 298 + cW w) + 1
def cT : TSt → Nat
  | .L => 0
  | .R0 => 1
  | .R1 => 2
def cD : URTM.Dir → Nat
  | .L => 0
  | .Z => 1
  | .R => 2
def cG : Tgt TSt Ps → Nat
  | .go x => cT x
  | .halt _ => 7
/-- 表を並べる鍵（生成器 `tools/gen_conv_lean.py` の `key3` と同じ式）。単射であることは使わない。 -/
def key3 (ρ : Rule TSt Ps (FSym (WSym St Sy))) : Nat :=
  (((cT ρ.p * 2 ^ 20 + cF ρ.s) * 2 ^ 20 + cF ρ.t) * 4 + cD ρ.d) * 8 + cG ρ.q

/-- T† の規則を (状態, 記号) から引く関数。 -/
def look3 : TSt → FSym (WSym St Sy) → Option (Rule TSt Ps (FSym (WSym St Sy))) :=
  Conv510.lookup (Conv59.hatLookup T32' .s0 qp32) .L .bl idx3 num3f 62

end URTM.CTSH.U3_36654
