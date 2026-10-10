/-
  URTM(3,36654) が任意の CTSH を模倣すること（主定理）。定義と仮定の確認は CTSH3_36654Main.lean、
  記述ファイルの表の照合は生成モジュール `URTM.Gen.V3_36654`（`chk3`・`len3`・`inc3`）。

  合成: `U32_3.urtm32_3_simulates_ctsh`（(32,3) の CTSH 模倣）→ `SimLemmas.drop_simulates`（停止規則の除去）
  → `Conv59.conv_simulates`（Lemma 5.9）→ `Conv510.conv_simulates`（Lemma 5.10）→ 表との一致。

  初期配置: U32_3 の Morita の初期配置 `encC32 C w` を、T̂ の組を n0 個並べた配置（`Conv59.W 0 n0 0`）にし、
  Lemma 5.10 の符号化（`Conv510.enc`）をかけたもの。n0 は十分大きければ何でもよい（`hn0`）。
  記述ファイルの試験例は n0 = 12 などで、生成モジュール `URTM.Gen.C3_36654` がテープそのものを照合する。

  停止配置は U32_3' のステップ数 N に依る（T̂ は T の 1 ステップごとにテープの詰め方を 1 マスずらすので）。

  未証明の穴・新規公理・native_decide を使わない。
-/
import URTM.Gen.V3_36654

set_option maxRecDepth 100000

namespace URTM.CTSH.U3_36654

open URTM URTM.KState URTM.CTSH URTM.SimLemmas URTM.Gen.K32_3 URTM.Gen.F3_36654 URTM.Gen.V3_36654
open URTM.Conv55 (FSym)
open URTM.Conv59 (WSt WSym)
open URTM.Conv510 (TSt)
open URTM.CTSH.U32_3 (encC32 finCfg32 urtm32_3_simulates_ctsh nm32)

/-! ## 1. 表と T† の一致 -/

/-- 表の規則はすべて T† にある（引き当ての健全性から）。 -/
theorem sub3 : ∀ ρ ∈ T3, ρ ∈ Tdag := fun ρ h =>
  Conv510.lookup_sound allW_all (fun _ _ _ hh => Conv59.hatLookup_sound hS hQ hh) (chk3 ρ h)

theorem lenDag : Tdag.length = 37936 := by decide +kernel

/-- 表には重複が無い（鍵が狭義単調増加）。 -/
theorem nodup3 : T3.Nodup := by
  have := List.pairwise_map.mp inc3
  exact this.imp (fun hab e => by subst e; exact Nat.lt_irrefl _ hab)

/-- T† の規則はすべて表にある（鳩の巣: 表は重複の無い 37936 本で T† に含まれ、T† も 37936 本）。 -/
theorem sup3 : ∀ ρ ∈ Tdag, ρ ∈ T3 :=
  subset_of_nodup_length T3 Tdag nodup3 sub3 (Nat.le_of_eq (by rw [lenDag, len3]))

theorem hD3 : Deterministic T3 := Deterministic.mono sub3 hDdag

/-! ## 2. 初期配置の不変量 -/

theorem E_len (w : List Ch) : (URTM.CTSH.U32_3.E nm32 w).length = 2 * w.length := by
  induction w with
  | nil => rfl
  | cons c w ih => rw [URTM.CTSH.U32_3.E_cons]; simp [ih]; omega

theorem blks_even (L : List (List Ch)) :
    ((L.map (URTM.CTSH.U32_3.blk nm32)).flatten).length % 2 = 0 := by
  induction L with
  | nil => rfl
  | cons w L ih => simp [URTM.CTSH.U32_3.blk, E_len] at ih ⊢; omega

theorem RA_even (C : CTSH) (m : Nat) : (URTM.CTSH.U32_3.RA nm32 C m).length % 2 = 0 := by
  have hHi : (URTM.CTSH.U32_3.Hi nm32 C m).length % 2 = 0 := blks_even ((C.drop m).reverse)
  have hLC : (URTM.CTSH.U32_3.LoCore nm32 C m).length % 2 = 0 := blks_even ((C.take (m - 1)).reverse)
  have hLo : (URTM.CTSH.U32_3.Lo nm32 C m).length % 2 = 0 := by
    unfold URTM.CTSH.U32_3.Lo; split
    · rfl
    · simp only [List.length_append, List.length_cons, List.length_nil]; omega
  unfold URTM.CTSH.U32_3.RA
  simp only [List.length_append, List.length_cons, E_len]
  omega

/-- `encC32 C w` は、n0 が十分大きければ組の始まり 0・組の数 n0 で不変量を満たす。 -/
theorem inv0 (C : CTSH) (w : List Ch) (n0 : Nat)
    (hn0 : (URTM.CTSH.U32_3.RA nm32 C 0).length + 6 ≤ 2 * n0 ∧
      (URTM.CTSH.U32_3.tapeList nm32 C 0 [] w).length + 1 ≤ 2 * n0) :
    Conv59.Inv (Sy.s0) 0 n0 (encC32 C w).pos (encC32 C w).tape := by
  have he := RA_even C 0
  obtain ⟨h1, h2⟩ := hn0
  simp only [encC32, URTM.CTSH.U32_3.encC, URTM.CTSH.U32_3.rep, List.length_nil]
  refine ⟨by omega, by omega, by omega, fun j hj => ?_, ?_⟩
  · rcases hj with hj | hj
    · obtain ⟨k, rfl⟩ : ∃ k : Nat, j = Int.negSucc k := ⟨(-j - 1).toNat, by omega⟩
      rfl
    · obtain ⟨k, rfl⟩ : ∃ k : Nat, j = (k : Int) := ⟨j.toNat, by omega⟩
      simp only [URTM.CTSH.Sim.tp_ofNat]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
  · obtain ⟨k, hk⟩ : ∃ k : Nat, (0 : Int) + 2 * (n0 : Int) - 1 = (k : Int) := ⟨2 * n0 - 1, by omega⟩
    rw [hk]
    simp only [URTM.CTSH.Sim.tp_ofNat]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl

/-! ## 3. 主定理 -/

theorem hH32 : HaltRulesId T f32 := by decide

/-- Morita の初期配置（原典 p. 199: `L` が位置 0 の空白を読み、位置 1.. に U32_3 の初期テープを 2 マスずつ詰めた組）。 -/
def E3 (C : CTSH) (w : List Ch) (n0 : Nat) : Cfg TSt Ps (FSym (WSym St Sy)) :=
  Conv510.enc .L idx3 (Conv59.W 0 n0 0 (encC32 C w))

/-- 停止配置: U32_3 の停止配置から停止規則を戻し（`unhalt f32`）、それに U32_3' が N ステップで達したときの
    T̂ の停止配置（`Conv59.E`）を Lemma 5.10 で符号化したもの。 -/
def fin3 (n0 : Nat) (C : CTSH) (vf : List Ch) (mf : Nat) (rm : List Ch) (N : Nat) :
    Cfg TSt Ps (FSym (WSym St Sy)) :=
  Conv510.enc .L idx3 (Conv59.E Sy.s0 0 n0 N (unhalt f32 (finCfg32 C vf mf rm)))

/-- **主定理（URTM(3,36654) は任意の CTSH を模倣する）**。U3_36654 = `T3`（記述ファイルの 37936 本）は決定的で、
    任意の CTSH C・初期語 w・十分大きい n0 について、初期配置 `E3 C w n0` から:

    1. C が (w, 0) から n ステップで停止 ID (vf, mf) に達するなら、U32_3 から停止規則を除いた機械 T32' は
       `encC32 C w` から N ステップ（n ≤ N + 1）で `unhalt f32 (finCfg32 C vf mf rm)` に止まり、U3_36654 は
       `fin3 n0 C vf mf rm N` で止まる。
    2. 逆に U3_36654 が止まるなら C も止まり、停止配置は 1 の形。
    3. C が停止しない ⇔ U3_36654 が停止しない。 -/
theorem urtm3_36654_simulates_ctsh (C : CTSH) (w : List Ch) (n0 : Nat)
    (hn0 : (URTM.CTSH.U32_3.RA nm32 C 0).length + 6 ≤ 2 * n0 ∧
      (URTM.CTSH.U32_3.tapeList nm32 C 0 [] w).length + 1 ≤ 2 * n0) :
    Deterministic T3 ∧
    (∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) →
      ∃ N M rm, n ≤ N + 1 ∧ HaltsIn T32' N (encC32 C w) (unhalt f32 (finCfg32 C vf mf rm)) ∧
        HaltsIn T3 M (E3 C w n0) (fin3 n0 C vf mf rm N)) ∧
    (∀ M e, HaltsIn T3 M (E3 C w n0) e →
      ∃ n vf mf rm N, CHaltsIn C n (w, 0) (vf, mf) ∧ e = fin3 n0 C vf mf rm N) ∧
    ((∀ n f, ¬ CHaltsIn C n (w, 0) f) ↔ (∀ M e, ¬ HaltsIn T3 M (E3 C w n0) e)) := by
  have h32 := urtm32_3_simulates_ctsh C w
  have hfin : ∀ vf mf rm, ∃ h, (finCfg32 C vf mf rm).st = .halt h := by
    intro vf mf rm; cases vf <;> exact ⟨_, rfl⟩
  have hd := drop_simulates hD hH32 C w (encC32 C w) ⟨.q0, rfl⟩ (finCfg32 C) hfin ⟨h32.1, h32.2.1⟩
  -- Lemma 5.9
  let fin : Nat × List Ch × Nat × List Ch → Cfg St Ps Sy := fun x => unhalt f32 (finCfg32 C x.2.1 x.2.2.1 x.2.2.2)
  let Halts : Nat × List Ch × Nat × List Ch → Prop := fun x =>
    CHaltsIn C x.1 (w, 0) (x.2.1, x.2.2.1) ∧ ∃ N, x.1 ≤ N + 1 ∧ HaltsIn T32' N (encC32 C w) (fin x)
  have c59 := Conv59.conv_simulates (T := T32') (s0 := Sy.s0) (ss := ss) (qs := qs) (qp := qp32) (a0 := 0) (n0 := n0)
    hyp59 hDhat Halts (encC32 C w) (p0 := St.q0) rfl (inv0 C w n0 hn0) fin
    ⟨fun x hx => let ⟨N, _, h⟩ := hx.2; ⟨N, h⟩, fun N e he => by
      obtain ⟨n, vf, mf, rm, hc, rfl⟩ := hd.2.1 N e he
      obtain ⟨N', rm', hN', hh'⟩ := hd.1 n vf mf hc
      refine ⟨(n, vf, mf, rm), ⟨hc, N, ?_, he⟩, rfl⟩
      have := (stepN_prefix (Deterministic.mono sub32' hD) hh'.1 hh'.2 he.1).1
      have := (stepN_prefix (Deterministic.mono sub32' hD) he.1 he.2 hh'.1).1
      omega⟩
  -- Lemma 5.10
  have hW : ∃ q, (Conv59.W 0 n0 0 (encC32 C w)).st = .go q := ⟨.L, rfl⟩
  have c510 := Conv510.conv_simulates hyp510 hDdag _ (Conv59.W 0 n0 0 (encC32 C w)) hW _ c59
  have fwd : ∀ n vf mf, CHaltsIn C n (w, 0) (vf, mf) →
      ∃ N M rm, n ≤ N + 1 ∧ HaltsIn T32' N (encC32 C w) (unhalt f32 (finCfg32 C vf mf rm)) ∧
        HaltsIn T3 M (E3 C w n0) (fin3 n0 C vf mf rm N) := by
    intro n vf mf hc
    obtain ⟨N, rm, hN, hh⟩ := hd.1 n vf mf hc
    obtain ⟨M, hM⟩ := c510.1 ((n, vf, mf, rm), N) ⟨⟨hc, N, hN, hh⟩, N, hh, rfl⟩
    exact ⟨N, M, rm, hN, hh, HaltsIn.congr sup3 sub3 hM⟩
  have bwd : ∀ M e, HaltsIn T3 M (E3 C w n0) e →
      ∃ n vf mf rm N, CHaltsIn C n (w, 0) (vf, mf) ∧ e = fin3 n0 C vf mf rm N := by
    intro M e he
    obtain ⟨⟨⟨n, vf, mf, rm⟩, N⟩, ⟨⟨hc, _⟩, _⟩, rfl⟩ := c510.2 M e (HaltsIn.congr sub3 sup3 he)
    exact ⟨n, vf, mf, rm, N, hc, rfl⟩
  refine ⟨hD3, fwd, bwd, ?_⟩
  constructor
  · intro hn M e he
    obtain ⟨n, vf, mf, rm, N, hc, _⟩ := bwd M e he
    exact hn n _ hc
  · intro hu n ⟨vf, mf⟩ hc
    obtain ⟨N, M, rm, _, _, hM⟩ := fwd n vf mf hc
    exact hu M _ hM

/-! ## 4. 停止テープからの読み戻し（最終文字列 vf が停止配置から一意に読める） -/

/-- U3_36654 のテープから、組の始まり a の詰め方で U32_3 のマス j を読み戻す。 -/
def get3 (tape : Int → FSym (WSym St Sy)) (a : Int) (j : Int) : Sy :=
  match tape (1 + (j - a) / 2) with
  | .pl (.pr s t) => if (j - a) % 2 = 0 then s else t
  | .pl (.hp _ s t) => if (j - a) % 2 = 0 then s else t
  | _ => .s0

/-- **w = λ の場合**: U32_3' が 0 ステップで止まる（N = 0）のは最終 ID が (λ, m) のときだけ
    （0 ステップの停止配置は初期配置そのもので状態 begin、(Y v, 0) の停止配置は case_y_2 に戻るため）。 -/
theorem stepN_zero_eq {Q P S : Type} {T : Machine Q P S} {a b : Cfg Q P S} (h : StepN T 0 a b) : a = b := by
  cases h; rfl

theorem N_zero {C : CTSH} {w vf : List Ch} {mf : Nat} {rm : List Ch}
    (h : HaltsIn T32' 0 (encC32 C w) (unhalt f32 (finCfg32 C vf mf rm))) : vf = [] := by
  have e := congrArg Cfg.st (stepN_zero_eq h.1)
  cases vf with
  | nil => rfl
  | cons c v =>
    exfalso
    simp [encC32, URTM.CTSH.U32_3.encC, URTM.CTSH.U32_3.rep, unhalt, finCfg32, URTM.CTSH.U32_3.finCfg,
      nm32, f32] at e

/-- **読み戻し**（N ≥ 1 の場合）: 停止配置 `fin3 n0 C vf mf rm N` のテープから、組の始まり −N の詰め方で
    U32_3 の停止配置（停止規則を戻したもの）のテープのマス j（−N ≤ j < −N + 2(n0 + N − 1)）がそのまま読める。
    U32_3 の停止テープ `finList` は最終文字列 ϕ₁(vf) を明示的に含む（(32,3) の `finList`）ので、vf が停止配置から一意に決まる。 -/
theorem get3_fin3 (n0 : Nat) (C : CTSH) (vf : List Ch) (mf : Nat) (rm : List Ch) {N : Nat} (hN : 1 ≤ N)
    (j : Int) (hj : -(N : Int) ≤ j ∧ j < -(N : Int) + 2 * ((n0 + N - 1 : Nat) : Int)) :
    get3 (fin3 n0 C vf mf rm N).tape (-(N : Int)) j = (finCfg32 C vf mf rm).tape j := by
  obtain ⟨st, x, g, hst, htape⟩ : ∃ st x g, (unhalt f32 (finCfg32 C vf mf rm)) = { st := .go st, pos := x, tape := g } ∧
      g = (finCfg32 C vf mf rm).tape := by
    cases vf <;> exact ⟨_, _, _, rfl, rfl⟩
  have hi : 1 ≤ 1 + (j - -(N : Int)) / 2 ∧ 1 + (j - -(N : Int)) / 2 ≤ ((n0 + N - 1 : Nat) : Int) := by
    constructor <;> omega
  simp only [fin3, hst, Conv59.E, Nat.pos_iff_ne_zero.mp hN, if_false, Conv59.haltW, Conv510.enc,
    show (WSt.h Sy.s0 : WSt St Sy) ≠ .L from nofun, if_false, Int.zero_sub]
  simp only [get3]
  rw [Conv55.upd_ne _ _ (by push_cast at hi ⊢; omega)]
  simp only [Conv59.pack]
  rw [if_pos hi]
  rw [← htape]
  by_cases hx : -(N : Int) + 2 * (1 + (j - -(N : Int)) / 2 - 1) = x
  · rw [if_pos hx]
    by_cases he : (j - -(N : Int)) % 2 = 0
    · dsimp only; rw [if_pos he]; congr 1; omega
    · dsimp only; rw [if_neg he]; congr 1; omega
  · rw [if_neg hx]
    by_cases he : (j - -(N : Int)) % 2 = 0
    · dsimp only; rw [if_pos he]; congr 1; omega
    · dsimp only; rw [if_neg he]; congr 1; omega

end URTM.CTSH.U3_36654
