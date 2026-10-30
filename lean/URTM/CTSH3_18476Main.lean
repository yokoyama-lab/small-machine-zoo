/-
  18476 記号の 3 状態機械が任意の CTSH を模倣すること（URTM(3,36654) の主定理 `urtm3_36654_simulates_ctsh` と同じ形）。

  機械: Morita の 1WU 機械 T̂（Lemma 5.9 を U32_3 から停止規則を除いた T32' に適用したもの。`CTSH3_36654Main.That`、
  298 記号・62 状態）に、↑ と ↓ をまとめた 1 種類の計数 `ct x k` の 3 状態化（`Conv3P.conv`）を、計数を刈り込まずに
  （どの記号 x にも計数 1..61 を置く。`need ≡ 61 = M − 1`）かけた Lean の項

      Conv3P.conv That .L .bl idx3 (fun _ => 61) allW

  そのもの（記号数 298 · 62 = 18476 は lean-univ の `FinalValues.shared3_32_3`）。この機械の規則の表・記述ファイルは
  作らない。番号付け idx3 は Morita の番号付け（記述ファイル urtm3-36654 のコメントの T̂ の規則から復元した
  `num3`、生成モジュール `URTM.Gen.F3_36654`）で、T̂ の規則の行き先の状態（q_L 以外）の番号は 1..61
  （`hyp510.hidx`）。

  合成: `U32_3.urtm32_3_simulates_ctsh` → `SimLemmas.drop_simulates`（停止規則の除去）→ `Conv59.conv_simulates`
  （Lemma 5.9）→ `Conv3P.conv_simulates`（Conv3PSim.lean。3 状態化の停止の 3 項の移送）。前半は
  `CTSH3_36654Thm.urtm3_36654_simulates_ctsh` と同じで、最後の段だけが `Conv510.conv_simulates` から替わる。

  刈り込みの健全性（`Conv3P.NeedOK`）: T̂ の規則の行き先 q ≠ q_L の番号は 1..61（`hyp510.hidx`）で、記号はどれも
  allW にある（`allW_all`）ので、need ≡ 61 なら T̂ の各ステップの行き先の配置で成り立つ（`hfull`）。
  どの配置でも成り立つわけではない（`idx3` は規則の行き先にならない状態に 62 以上の番号を付けうる）。

  初期配置・停止配置は (3,36654) の `E3`・`fin3` の Lemma 5.10 の符号化 `Conv510.enc` を `Conv3P.enc` に替えたもの。

  生成モジュールに依存するので、`tools/gen_all_lean.sh`（CI）が書く `URTM.lean` 経由でビルドされる。
  未証明の穴・新規公理・native_decide を使わない。
-/
import URTM.CTSH3_36654Rev
import URTM.Conv3PSim

set_option maxRecDepth 100000

namespace URTM.CTSH.U3_18476

open URTM URTM.KState URTM.CTSH URTM.SimLemmas URTM.Gen.K32_3
open URTM.Conv59 (WSt WSym)
open URTM.Conv510 (TSt)
open URTM.Conv3P (CSym)
open URTM.CTSH.U3_36654 (T32' f32 That allW idx3 allW_all hyp59 hyp510 hDhat hRhat sub32' hH32 inv0)
open URTM.CTSH.U32_3 (encC32 finCfg32 urtm32_3_simulates_ctsh nm32)

/-! ## 1. 3 状態化の仮定 -/

/-- 計数を刈り込まない: T̂ の規則の行き先 q ≠ q_L の番号はどの記号の計数（1..61）にも収まる。 -/
theorem hfull : ∀ r ∈ That, ∀ q, r.q = .go q → q ≠ .L → ∀ _x : WSym St Sy, idx3 q ≤ 61 := by
  intro r hr q hq hqL _
  have := Conv510.idxOK_spec (hyp510.hidx r hr) hq hqL
  omega

/-- `Conv3P` の仮定（T̂ の規則が読み書きする記号は allW にあり、規則の形は 1WU、番号は 1..61 で単射）。 -/
theorem hyp3P : Conv3P.Hyp That .L .bl idx3 (fun _ => 61) allW where
  hS := fun _ _ => ⟨allW_all _, allW_all _⟩
  hshape := hyp510.hshape
  hidx := by
    intro r hr q hq hqL
    have := Conv510.idxOK_spec (hyp510.hidx r hr) hq hqL
    show 1 ≤ idx3 q ∧ idx3 q ≤ 61
    omega
  hinj := hyp510.hinj

/-! ## 2. 決定性と可逆性 -/

theorem hD18476 : Deterministic (Conv3P.conv That .L .bl idx3 (fun _ => 61) allW) :=
  Conv3P.conv_det hDhat hyp510.hshape hyp510.hinj

theorem hR18476 : Reversible (Conv3P.conv That .L .bl idx3 (fun _ => 61) allW) :=
  Conv3P.conv_rev hRhat hyp510.hshape hyp510.hinj

/-- **18476 記号の 3 状態機械は決定的かつ可逆**（T̂ の可逆性 `hRhat` から `Conv3P.conv_rev`）。 -/
theorem urtm3_18476_det_rev :
    Deterministic (Conv3P.conv That .L .bl idx3 (fun _ => 61) allW) ∧
    Reversible (Conv3P.conv That .L .bl idx3 (fun _ => 61) allW) :=
  ⟨hD18476, hR18476⟩

/-! ## 3. 主定理 -/

/-- 初期配置（(3,36654) の `E3` と同じ T̂ の配置 `Conv59.W 0 n0 0 (encC32 C w)` を `Conv3P.enc` で符号化したもの）:
    `L` が位置 0 の空白を読み、位置 1.. に U32_3 の初期テープを 2 マスずつ詰めた組。 -/
def E18476 (C : CTSH) (w : List Ch) (n0 : Nat) : Cfg TSt Ps (CSym (WSym St Sy)) :=
  Conv3P.enc .L idx3 (Conv59.W 0 n0 0 (encC32 C w))

/-- 停止配置: U32_3 の停止配置から停止規則を戻し（`unhalt f32`）、それに T32' が N ステップで達したときの
    T̂ の停止配置（`Conv59.E`）を `Conv3P.enc` で符号化したもの。 -/
def fin18476 (n0 : Nat) (C : CTSH) (vf : List Ch) (mf : Nat) (rm : List Ch) (N : Nat) :
    Cfg TSt Ps (CSym (WSym St Sy)) :=
  Conv3P.enc .L idx3 (Conv59.E Sy.s0 0 n0 N (unhalt f32 (finCfg32 C vf mf rm)))

/-- **主定理（18476 記号の 3 状態機械は任意の CTSH を模倣する）**。`Conv3P.conv That .L .bl idx3 (fun _ => 61) allW`
    は決定的で、任意の CTSH C・初期語 w・十分大きい n0 について、初期配置 `E18476 C w n0` から:

    1. C が (w, 0) から n ステップで停止 ID (vf, mf) に達するなら、U32_3 から停止規則を除いた機械 T32' は
       `encC32 C w` から N ステップ（n ≤ N + 1）で `unhalt f32 (finCfg32 C vf mf rm)` に止まり、18476 記号の機械は
       `fin18476 n0 C vf mf rm N` で止まる。
    2. 逆に 18476 記号の機械が止まるなら C も止まり、停止配置は 1 の形。
    3. C が停止しない ⇔ 18476 記号の機械が停止しない。 -/
theorem urtm3_18476_simulates_ctsh (C : CTSH) (w : List Ch) (n0 : Nat)
    (hn0 : (URTM.CTSH.U32_3.RA nm32 C 0).length + 6 ≤ 2 * n0 ∧
      (URTM.CTSH.U32_3.tapeList nm32 C 0 [] w).length + 1 ≤ 2 * n0) :
    Deterministic (Conv3P.conv That .L .bl idx3 (fun _ => 61) allW) ∧
    (∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) →
      ∃ N M rm, n ≤ N + 1 ∧ HaltsIn T32' N (encC32 C w) (unhalt f32 (finCfg32 C vf mf rm)) ∧
        HaltsIn (Conv3P.conv That .L .bl idx3 (fun _ => 61) allW) M (E18476 C w n0)
          (fin18476 n0 C vf mf rm N)) ∧
    (∀ M e, HaltsIn (Conv3P.conv That .L .bl idx3 (fun _ => 61) allW) M (E18476 C w n0) e →
      ∃ n vf mf rm N, CHaltsIn C n (w, 0) (vf, mf) ∧ e = fin18476 n0 C vf mf rm N) ∧
    ((∀ n f, ¬ CHaltsIn C n (w, 0) f) ↔
      (∀ M e, ¬ HaltsIn (Conv3P.conv That .L .bl idx3 (fun _ => 61) allW) M (E18476 C w n0) e)) := by
  have h32 := urtm32_3_simulates_ctsh C w
  have hfin : ∀ vf mf rm, ∃ h, (finCfg32 C vf mf rm).st = .halt h := by
    intro vf mf rm; cases vf <;> exact ⟨_, rfl⟩
  have hd := drop_simulates hD hH32 C w (encC32 C w) ⟨.q0, rfl⟩ (finCfg32 C) hfin ⟨h32.1, h32.2.1⟩
  -- Lemma 5.9（`urtm3_36654_simulates_ctsh` と同じ）
  let fin : Nat × List Ch × Nat × List Ch → Cfg St Ps Sy := fun x => unhalt f32 (finCfg32 C x.2.1 x.2.2.1 x.2.2.2)
  let Halts : Nat × List Ch × Nat × List Ch → Prop := fun x =>
    CHaltsIn C x.1 (w, 0) (x.2.1, x.2.2.1) ∧ ∃ N, x.1 ≤ N + 1 ∧ HaltsIn T32' N (encC32 C w) (fin x)
  have c59 := Conv59.conv_simulates (T := T32') (s0 := Sy.s0) (ss := ss) (qs := qs)
    (qp := URTM.CTSH.U3_36654.qp32) (a0 := 0) (n0 := n0)
    hyp59 hDhat Halts (encC32 C w) (p0 := St.q0) rfl (inv0 C w n0 hn0) fin
    ⟨fun x hx => let ⟨N, _, h⟩ := hx.2; ⟨N, h⟩, fun N e he => by
      obtain ⟨n, vf, mf, rm, hc, rfl⟩ := hd.2.1 N e he
      obtain ⟨N', rm', hN', hh'⟩ := hd.1 n vf mf hc
      refine ⟨(n, vf, mf, rm), ⟨hc, N, ?_, he⟩, rfl⟩
      have := (stepN_prefix (Deterministic.mono sub32' hD) hh'.1 hh'.2 he.1).1
      have := (stepN_prefix (Deterministic.mono sub32' hD) he.1 he.2 hh'.1).1
      omega⟩
  -- 3 状態化（計数を刈り込まない Conv3P）
  have hW : ∃ q, (Conv59.W 0 n0 0 (encC32 C w)).st = .go q := ⟨.L, rfl⟩
  have c3 := Conv3P.conv_simulates hyp3P allW_all hfull hyp510.hL hyp510.hL0 hD18476 _
    (Conv59.W 0 n0 0 (encC32 C w)) hW _ c59
  have fwd : ∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) →
      ∃ N M rm, n ≤ N + 1 ∧ HaltsIn T32' N (encC32 C w) (unhalt f32 (finCfg32 C vf mf rm)) ∧
        HaltsIn (Conv3P.conv That .L .bl idx3 (fun _ => 61) allW) M (E18476 C w n0)
          (fin18476 n0 C vf mf rm N) := by
    intro n vf mf hc
    obtain ⟨N, rm, hN, hh⟩ := hd.1 n vf mf hc
    obtain ⟨M, hM⟩ := c3.1 ((n, vf, mf, rm), N) ⟨⟨hc, N, hN, hh⟩, N, hh, rfl⟩
    exact ⟨N, M, rm, hN, hh, hM⟩
  have bwd : ∀ M e, HaltsIn (Conv3P.conv That .L .bl idx3 (fun _ => 61) allW) M (E18476 C w n0) e →
      ∃ n vf mf rm N, CHaltsIn C n (w, 0) (vf, mf) ∧ e = fin18476 n0 C vf mf rm N := by
    intro M e he
    obtain ⟨⟨⟨n, vf, mf, rm⟩, N⟩, ⟨⟨hc, _⟩, _⟩, rfl⟩ := c3.2 M e he
    exact ⟨n, vf, mf, rm, N, hc, rfl⟩
  refine ⟨hD18476, fwd, bwd, ?_⟩
  constructor
  · intro hn M e he
    obtain ⟨n, vf, mf, rm, N, hc, _⟩ := bwd M e he
    exact hn n _ hc
  · intro hu n ⟨vf, mf⟩ hc
    obtain ⟨N, M, rm, _, _, hM⟩ := fwd n vf mf hc
    exact hu M _ hM

end URTM.CTSH.U3_18476
