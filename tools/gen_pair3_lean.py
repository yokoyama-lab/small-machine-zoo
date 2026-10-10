#!/usr/bin/env python3
"""Morita の 1WU 機械 T̂（Lemma 5.9、対の 1WU）に、改良版の 3 状態化の計数（↑↓ を 1 種類にまとめ、
現れる計数だけを残す。docs/09 §2.1–2.2）を当てたときの番号付け ν と計数の上限 need
（`tools/threestate.py` の `build(path, "pair", "pruned", "auto")`）を Lean のモジュールに書き出す。

    python3 tools/gen_pair3_lean.py data/urtm/urtm32-3.txt --module P3_1820 > lean/URTM/Gen/P3_1820.lean

Lean 側の T̂ は `URTM.CTSH.U3_36654.That`（`Conv59.conv`。Morita の記述ファイルの 3 状態機械と集合として一致することは
CTSH3_36654Main で確かめてある）。ここでは番号付けと need をそのまま写し、
  * 一般の変換 `Conv3P.conv` の仮定（番号付けの単射性、規則の行き先と現状態の番号が need 以下）の有限検査、
  * Python の記号数（`len(ThreeState.symbols)`）と `|allW| + Σ need` の一致
を `decide +kernel` で確かめる。記号数の一般の式（`nsym (Conv3P.conv …) = |allW| + Σ need`）は
LeanUniv.SymExact の `conv3P_nsym`。need は「その状態が読みうる記号」（Python の `W.reads`、T̂ の構造から決めたもの）
を含むが、Lean ではその健全性（実行の各ステップで計数が足りること）は示していない。記号数の主張だけに使う。
"""

import argparse
import sys

sys.path.insert(0, __file__.rsplit("/", 1)[0])
import threestate as ts  # noqa: E402


def main(path, module):
    T, ti, W, TS = ts.build(path, "pair", "pruned", "auto", False)
    assert W.kind == "pair" and not TS.mirror
    sid = {s: f"St.q{i}" for i, s in enumerate(T.states)}
    yid = {s: f"Sy.s{i}" for i, s in enumerate(T.symbols)}
    S = sorted(ti.S)
    # W の記号: 名前 → Lean の項
    vsym = {W.s0: "WSym.bl"}
    for s in S:
        for t in S:
            vsym[W.P(s, t)] = f"(WSym.pr {yid[s]} {yid[t]})"
    for p in sorted(ti.states):
        for s in S:
            for t in S:
                vsym[W.Mk(p, s, t)] = f"(WSym.hp {sid[p]} {yid[s]} {yid[t]})"
    assert set(vsym) == set(W.symbols) and len(vsym) == len(W.symbols)
    # W の状態: 名前 → Lean の項
    vst = {W.qL: "WSt.L"}
    for name, nm in W.name_of.items():
        if nm[0] == "h":
            vst[name] = f"(WSt.h {yid[nm[1]]})"
        elif nm[0] == "q" and nm[1] == "lambda":
            vst[name] = "WSt.lam"
        elif nm[0] == "q":
            vst[name] = f"(WSt.q {yid[nm[1]]})"
        else:
            vst[name] = f"(WSt.qp {sid[nm[1]]} {yid[nm[2]]})"
    assert len(vst) == len(W.states)
    order = sorted(TS.nu, key=lambda q: TS.nu[q])
    assert [TS.nu[q] for q in order] == list(range(1, len(order) + 1))
    ordP = ["WSt.L"] + [vst[q] for q in order]
    allv = ["WSt.L"] + [f"(WSt.q {yid[s]})" for s in T.symbols] + ["WSt.lam"] + \
        [f"(WSt.h {yid[s]})" for s in T.symbols] + \
        [f"(WSt.qp {sid[p]} {yid[s]})" for p in T.states for s in T.symbols]
    rest = [x for x in allv if x not in set(ordP)]
    assert len(ordP) + len(rest) == len(allv)
    needL = [(vsym[x], TS.need[x]) for x in W.symbols]
    nsyms = len(TS.symbols)
    assert nsyms == len(W.symbols) + sum(k for _, k in needL)

    L = []
    L.append("/-")
    L.append(f"  {path.split('/')[-1]} から自動生成（tools/gen_pair3_lean.py）。手で編集しないこと。")
    L.append(f"  {TS.title()}")
    L.append(f"  （Python の 3 状態機械は {len(TS.quints)} 本。表そのものは写さない。）")
    L.append("-/")
    L.append("import URTM.Conv3P")
    L.append("import URTM.CTSH3_36654Main")
    L.append("")
    L.append("set_option maxRecDepth 100000")
    L.append("")
    L.append(f"namespace URTM.Gen.{module}")
    L.append("")
    L.append("open URTM URTM.KState URTM.Gen.K32_3")
    L.append("open URTM.Conv59 (WSt WSym)")
    L.append("open URTM.CTSH.U3_36654 (That allW allW_all hyp510)")
    L.append("")
    L.append("/-- T̂ の状態の番号付け ν（`threestate.py` の群の並べ方の最適解）: 位置が番号。先頭は q_L（0）、")
    L.append("    続いて ν = 1, 2, … の順、残りは T̂ に現れない状態。 -/")
    L.append("def allP : List (WSt St Sy) := [" + ", ".join(ordP + rest) + "]")
    L.append("def idxP (q : WSt St Sy) : Nat := allP.idxOf q")
    L.append("def decP (i : Nat) : WSt St Sy := allP.getD i .L")
    L.append("")
    L.append("/-- 計数の上限 need（`threestate.py` の need。T̂ の記号ごと）。 -/")
    L.append("def needL : List (WSym St Sy × Nat) := [" + ", ".join(f"({x}, {k})" for x, k in needL) + "]")
    L.append("def needP (x : WSym St Sy) : Nat := (needL.lookup x).getD 0")
    L.append("")
    L.append("/-! ## 仮定の有限検査（`Conv3P.Hyp`） -/")
    L.append("")
    L.append("def idxOK (r : Rule (WSt St Sy) Ps (WSym St Sy)) : Bool :=")
    L.append("  match r.q with")
    L.append("  | .go q => q == .L || (decide (1 ≤ idxP q) && decide (idxP q ≤ needP r.t))")
    L.append("  | .halt _ => true")
    L.append("def srcOK (r : Rule (WSt St Sy) Ps (WSym St Sy)) : Bool :=")
    L.append("  r.p == .L || (decide (1 ≤ idxP r.p) && decide (idxP r.p ≤ needP r.s))")
    L.append("theorem hidx' : ∀ r ∈ That, idxOK r = true := by decide +kernel")
    L.append("theorem hsrc' : ∀ r ∈ That, srcOK r = true := by decide +kernel")
    L.append("theorem dec_idx : ∀ q ∈ allP, decP (idxP q) = q := by decide +kernel")
    L.append("theorem allP_all : ∀ q : WSt St Sy, q ∈ allP := by")
    L.append("  intro q")
    L.append("  cases q with")
    L.append("  | L => decide +kernel")
    L.append("  | q s => cases s <;> decide +kernel")
    L.append("  | lam => decide +kernel")
    L.append("  | h s => cases s <;> decide +kernel")
    L.append("  | qp p s => cases p <;> cases s <;> decide +kernel")
    L.append("theorem idx_inj (p q : WSt St Sy) (h : idxP p = idxP q) : p = q := by")
    L.append("  rw [← dec_idx p (allP_all p), ← dec_idx q (allP_all q), h]")
    L.append("")
    L.append("theorem hyp : Conv3P.Hyp That .L .bl idxP needP allW where")
    L.append("  hS := fun _ _ => ⟨allW_all _, allW_all _⟩")
    L.append("  hshape := hyp510.hshape")
    L.append("  hidx := by")
    L.append("    intro r hr q hq hqL")
    L.append("    have := hidx' r hr")
    L.append("    unfold idxOK at this")
    L.append("    rw [hq] at this; dsimp only at this")
    L.append("    have hb : (q == WSt.L) = false := by simp [hqL]")
    L.append("    simp only [hb, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at this")
    L.append("    exact this")
    L.append("  hinj := fun p q _ _ h => idx_inj p q h")
    L.append("")
    L.append("theorem hsrc : ∀ r ∈ That, r.p ≠ .L → 1 ≤ idxP r.p ∧ idxP r.p ≤ needP r.s := by")
    L.append("  intro r hr hp")
    L.append("  have := hsrc' r hr")
    L.append("  unfold srcOK at this")
    L.append("  have hb : (r.p == WSt.L) = false := by simp [hp]")
    L.append("  simp only [hb, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at this")
    L.append("  exact this")
    L.append("")
    L.append("theorem allW_nodup : allW.Nodup := by decide +kernel")
    L.append(f"/-- Python の記号数 {nsyms}（`len(ThreeState.symbols)`）は `|allW| + Σ need`。 -/")
    L.append(f"theorem count_py : allW.length + (allW.map needP).sum = {nsyms} := by decide +kernel")
    L.append("")
    L.append(f"end URTM.Gen.{module}")
    print("\n".join(L))
    print(f"{module}: {nsyms} symbols (|allW| {len(W.symbols)} + sum need {nsyms - len(W.symbols)})", file=sys.stderr)


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("path")
    ap.add_argument("--module", default="P3_1820")
    a = ap.parse_args()
    main(a.path, a.module)
