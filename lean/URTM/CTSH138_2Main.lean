/-
  URTM(138,2)（Morita 2017, §7.3.7）が任意の CTSH を模倣すること。

  原典 p. 196–197: U138_2 は U24_4 を Theorem 5.4（§5.3.3、2 記号化）で変換したもの。記号 b y n ∗ を
  00 01 10 11 で符号化し（「each step of U24_4 is simulated by U138_2 in four steps」）、220 本。
  記述ファイル urtm138-2.txt の表が、U24_4 から停止規則 2 本（null・halt への 0 シフト）を除いた機械に
  Theorem 5.4 の 2 ビット版（原典 Example 5.7 の形）を適用し、続く規則の無い δr・δw 6 本を省いたもの
  （`Conv54.conv`）と**集合として一致する**こと、および原典どおりの δ̃（`convFull`、226 本）に含まれることを
  `decide` で確かめ、次の 3 つを合成する:

    1. `U24_4.urtm24_4_simulates_ctsh`（CTSH24_4Main.lean）
    2. `SimLemmas.drop_simulates`（停止規則の除去）
    3. `Conv54.conv_simulates`（Theorem 5.4 の 2 ビット版の一般の模倣証明）

  生成モジュールに依存するので、`tools/gen_all_lean.sh`（CI）が書く `URTM.lean` 経由でビルドされる。
  未証明の穴・新規公理・native_decide を使わない。
-/
import URTM.CTSH24_4Main
import URTM.Conv54
import URTM.Gen.F138_2

set_option maxRecDepth 100000

namespace URTM.CTSH.U138_2

open URTM URTM.KState URTM.CTSH URTM.SimLemmas URTM.Conv54 URTM.Gen.K24_4 URTM.Gen.F138_2
open URTM.CTSH.U24_4 (encC24 finCfg24 urtm24_4_simulates_ctsh)

/-- U24_4 から停止規則を除いた機械（82 本）。 -/
def T24' : Machine St Ps Sy := dropHalt T

/-- 疑似状態へ入る規則の現状態: null ← begin（q0）、halt ← case_y_2（q2）。 -/
def f24 : Ps → St
  | .h0 => .q0
  | .h1 => .q2

/-- 符号（urtm138-2.txt の注記 codes([[b,[0,0]],[y,[0,1]],[n,[1,0]],[*,[1,1]]])、原典 p. 196 の ϕ3）。 -/
def code24 : Sy → Bool × Bool
  | .s0 => (false, false)
  | .s1 => (false, true)
  | .s2 => (true, false)
  | .s3 => (true, true)

/-- 状態に入る向き（原典の hsd）。T24' の規則から読む。 -/
def dir24 (q : St) : Dir := if T24'.any (fun r => r.q == .go q && r.d == .R) then .R else .L

theorem hH24 : HaltRulesId T f24 := by decide
theorem len24' : T24'.length = 82 := by decide

theorem hyp24 : Conv54.Hyp T24' code24 dir24 qs where
  hQ := hQ
  hG := by decide
  hdir := by decide
  hinj := by intro s t h; cases s <;> cases t <;> first | rfl | exact absurd h (by decide)

/-- 記述ファイルの表（220 本）は、T24' に Theorem 5.4（2 ビット、使われうる規則だけ）を適用したものに含まれる。 -/
theorem rules138_sub : ∀ ρ ∈ T138, ρ ∈ Conv54.conv T24' code24 dir24 qs := by decide +kernel
/-- 逆に、変換の規則はすべて記述ファイルの表にある。 -/
theorem rules138_sup : ∀ ρ ∈ Conv54.conv T24' code24 dir24 qs, ρ ∈ T138 := by decide +kernel
/-- 記述ファイルの表は原典どおりの δ̃（δr・δw をすべての組に置いたもの）に含まれ、原典の δ̃ は 226 本・表は 220 本。 -/
theorem rules138_full : ∀ ρ ∈ T138, ρ ∈ convFull T24' code24 dir24 qs := by decide +kernel
theorem len138 : T138.length = 220 ∧ (convFull T24' code24 dir24 qs).length = 226 := by decide +kernel

theorem sub24' : ∀ r ∈ T24', r ∈ T := fun _ hr => (mem_dropHalt.mp hr).1

/-- 決定性: `Conv54.conv_det` から、記述ファイルの表との一致を通して。 -/
theorem hD138 : Deterministic T138 :=
  Deterministic.mono rules138_sub (Conv54.conv_det (Deterministic.mono sub24' hD) hyp24.hinj)
theorem hR138 : Reversible T138 := by decide +kernel

/-- U138_2 の状態の全体（表に現れる状態。原典の数え方で 138 個）。 -/
def sts138 : List (BSt St) := (T138.map (·.p) ++ T138.filterMap (fun ρ => match ρ.q with
  | .go x => some x
  | .halt _ => none)).eraseDups

theorem sts138_ok : (∀ ρ ∈ T138, ρ.p ∈ sts138 ∧ ρ.q ∈ sts138.map Tgt.go) ∧ sts138.length = 138 := by
  decide +kernel

/-- U24_4 の配置の符号化（各記号を 2 ビットに、ヘッドを 2 倍の位置に、状態 q を [q^r] に）。 -/
def E (c : Cfg St Ps Sy) : Cfg (BSt St) Ps Bool := enc code24 c

/-- 停止配置: U24_4 の停止配置から停止規則を 1 つ戻し（begin / case_y_2 が b を読む配置）、T̃ の停止配置へ
    （begin は b = 00 の 1 ビット目 0 を読む δr があるので 1 ステップ進んで止まる。case_y_2 は進まない）。 -/
def fin138 (C : CTSH) (vf : List Ch) (mf : Nat) (rm : List Ch) : Cfg (BSt St) Ps Bool :=
  pre T24' code24 (unhalt f24 (finCfg24 C vf mf rm))

/-- **主定理（URTM(138,2) は任意の CTSH を模倣する）**。U138_2 = `T138`（記述ファイルの表）は決定的かつ可逆、
    状態は 138 個の `sts138` に入り、記号は {0, 1}。任意の CTSH C と初期語 w について、Morita の初期配置
    `E (encC24 C w)`（= ϕ3(b ϕ₁(w^R_{k−1}) ∗ ⋯ ∗ ϕ₁(w^R_1) ∗ b b) [q^r_begin] ϕ3(ϕ₁(w) b)、原典 p. 197）から:

    1. C が (w, 0) から n ステップで停止 ID (vf, mf) に達するなら、U138_2 は停止し（N + 1 ≥ n）、停止配置は `fin138 C vf mf rm`。
    2. 逆に U138_2 が停止するなら C も停止し、停止配置は 1 の形。
    3. C が停止しない ⇔ U138_2 が停止しない。 -/
theorem urtm138_2_simulates_ctsh (C : CTSH) (w : List Ch) :
    Deterministic T138 ∧ Reversible T138 ∧
    (∀ ρ ∈ T138, ρ.p ∈ sts138 ∧ ρ.q ∈ sts138.map Tgt.go) ∧ sts138.length = 138 ∧
    (∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) →
      ∃ N rm, n ≤ N + 1 ∧ HaltsIn T138 N (E (encC24 C w)) (fin138 C vf mf rm)) ∧
    (∀ N e, HaltsIn T138 N (E (encC24 C w)) e →
      ∃ n vf mf rm, CHaltsIn C n (w, 0) (vf, mf) ∧ e = fin138 C vf mf rm) ∧
    ((∀ n f, ¬ CHaltsIn C n (w, 0) f) ↔ (∀ N e, ¬ HaltsIn T138 N (E (encC24 C w)) e)) := by
  have h24 := urtm24_4_simulates_ctsh C w
  have hfin : ∀ vf mf rm, ∃ h, (finCfg24 C vf mf rm).st = .halt h := by
    intro vf mf rm; cases vf <;> exact ⟨_, rfl⟩
  have hd := drop_simulates hD hH24 C w (encC24 C w) ⟨.q0, rfl⟩ (finCfg24 C) hfin ⟨h24.1, h24.2.1⟩
  have hDc : Deterministic (Conv54.conv T24' code24 dir24 qs) := Deterministic.mono rules138_sup hD138
  have hc := Conv54.conv_simulates hyp24 hDc C w (encC24 C w) ⟨.q0, rfl⟩
    (fun vf mf rm => unhalt f24 (finCfg24 C vf mf rm)) ⟨hd.1, hd.2.1⟩
  refine ⟨hD138, hR138, sts138_ok.1, sts138_ok.2, ?_, ?_, ?_⟩
  · intro n vf mf h
    obtain ⟨N, rm, hN, hh⟩ := hc.1 n vf mf h
    exact ⟨N, rm, hN, HaltsIn.congr rules138_sup rules138_sub hh⟩
  · intro N e he
    exact hc.2.1 N e (HaltsIn.congr rules138_sub rules138_sup he)
  · rw [hc.2.2]
    exact ⟨fun h N e he => h N e (HaltsIn.congr rules138_sub rules138_sup he),
      fun h N e he => h N e (HaltsIn.congr rules138_sup rules138_sub he)⟩

end URTM.CTSH.U138_2
