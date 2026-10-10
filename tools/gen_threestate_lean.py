#!/usr/bin/env python3
"""改良版の 3 状態化（tools/threestate.py、docs/09）の生成結果を Lean のモジュールに書き出す。

    python3 tools/gen_threestate_lean.py data/urtm/urtm32-3.txt --module T3_600 --base K32_3 \
        > lean/URTM/Gen/T3_600.lean
    python3 tools/gen_threestate_lean.py data/urtm/urtm32-3.txt --module T3_659 --base K32_3 --no-mirror \
        > lean/URTM/Gen/T3_659.lean

`--no-mirror` は反転しない版（`build(..., mirror=False)`、(32,3) では (3,659)）を `Conv3S.conv` と照合する。
既定（反転版）の出力は従来と同じ。

threestate.py の `build(path, "single", "pruned", "auto", mirror=True)`（URTM(3,600)）が作る
  * 反転した T の Q₋ の状態の列（`qmR`）、右移動の組 R（`RlR`）と Q₊ の印の組 G（`GlR`）、
  * 1WU 機械の状態の番号付け ν（`ordW`。番号は位置 + 1）と計数の上限 need（`needL`）、
  * 3 状態機械の規則（方向を入れ替え直したもの。`Tpy`）と記号（`symPy`）
をそのまま写し、Lean 側の一般の変換 `Conv3S.convM` の値と規則の並びまで一致することを `decide +kernel` で確かめる。
Lean の定理は生成物を信じない: `convM` の一般定理（Conv3S.lean）が模倣を与え、ここでは
「Python の表 = Lean の変換の値」と、仮定（番号付け・刈り込みの健全性）の有限検査だけを行う。
"""

import argparse
import sys

sys.path.insert(0, __file__.rsplit("/", 1)[0])
import threestate as ts  # noqa: E402

CHUNK = 400


def main(path, module, base, mirror=True):
    T, ti, W, TS = ts.build(path, "single", "pruned", "auto", mirror)
    assert TS.mirror == mirror
    # 反転版は反転した T'（TR）を、反転なしは T' そのものを 1WU 化する。名前の接尾辞 R は反転版だけ。
    R = "R" if mirror else ""
    TM = "TR" if mirror else "T'"
    WM = "WR" if mirror else "W"
    CV = "convM" if mirror else "conv"
    sid = {s: f"St.q{i}" for i, s in enumerate(T.states)}
    yid = {s: f"Sy.s{i}" for i, s in enumerate(T.symbols)}
    assert list(ti.S) == list(T.symbols)
    # W の記号: 名前 → Lean の項
    vsym = {W.s0: "VSym.bl"}
    for s, name in W.plain.items():
        vsym[name] = f"(VSym.pl {yid[s]})"
    for (p, s), name in W.mk.items():
        vsym[name] = f"(VSym.mk {sid[p]} {yid[s]})"
    for (p, v), name in W.mkp.items():
        vsym[name] = f"(VSym.mkp {sid[p]} {yid[v]})"
    assert len(vsym) == len(W.symbols)
    # W の状態: 名前 → Lean の項
    vst = {W.qL: "VSt.L", "e1": "VSt.e1", "e2": "VSt.e2"}
    for s, name in W.c.items():
        vst[name] = f"(VSt.c {yid[s]})"
    for (p, v), name in W.r.items():
        vst[name] = f"(VSt.r {sid[p]} {yid[v]})"
    for (p, v), name in W.g.items():
        vst[name] = f"(VSt.g {sid[p]} {yid[v]})"
    assert len(vst) == len(W.states)
    # 3 状態機械の記号: W の記号と計数 [x,k,c]
    from check_urtm import split_top

    def csym(x):
        if x in vsym:
            return f"(CSym.pl {vsym[x]})"
        assert x.startswith("[") and x.endswith(",c]"), x
        a, k, c = split_top(x[1:-1])
        assert c == "c"
        return f"(CSym.ct {vsym[a]} {int(k)})"

    tst = {"l": "TSt.L", "r0": "TSt.R0", "r1": "TSt.R1"}
    dirs = {"-": ".L", "0": ".Z", "+": ".R"}
    rules = TS.output_quints()
    order = sorted(TS.nu, key=lambda q: TS.nu[q])
    assert [TS.nu[q] for q in order] == list(range(1, len(order) + 1))
    ordW = [vst[q] for q in order]
    # VSt の残り（L と、W に現れない r・g）
    allv = ["VSt.L"] + [f"(VSt.c {yid[s]})" for s in T.symbols] + ["VSt.e1", "VSt.e2"] + \
        [f"(VSt.r {sid[p]} {yid[v]})" for p in T.states for v in T.symbols] + \
        [f"(VSt.g {sid[p]} {yid[v]})" for p in T.states for v in T.symbols]
    rest = [x for x in allv if x not in set(ordW)]
    assert len(ordW) + len(rest) == len(allv)
    needL = [(vsym[x], TS.need[x]) for x in W.symbols]
    assert all(k >= 1 for _, k in needL)

    L = []
    L.append("/-")
    L.append(f"  {path.split('/')[-1]} から自動生成（tools/gen_threestate_lean.py --base {base}）。手で編集しないこと。")
    L.append(f"  {TS.title()}")
    L.append(f"  規則 {len(rules)} 本（1WU 機械 {len(W.quints)} 本）。" +
             ("反転版（`Conv3S.convM`）。" if mirror else "反転なし（`Conv3S.conv`）。"))
    L.append("-/")
    L.append("import URTM.Conv3S")
    L.append(f"import URTM.Gen.{base}")
    L.append("")
    L.append("set_option maxRecDepth 100000")
    L.append("set_option maxHeartbeats 0")
    L.append("")
    L.append(f"namespace URTM.Gen.{module}")
    L.append("")
    L.append(f"open URTM URTM.KState URTM.SimLemmas URTM.Conv3Base URTM.Gen.{base}")
    L.append("open URTM.Conv1W (VSt VSym isPlus)")
    L.append("open URTM.Conv3P (CSym)")
    L.append("open URTM.Conv510 (TSt)")
    L.append("")
    L.append("/-- 停止規則を除いた T（`threestate.py` の T⁻）。 -/")
    L.append("def T' : Machine St Ps Sy := dropHalt T")
    if mirror:
        L.append("/-- 左右反転した T'。 -/")
        L.append("def TR : Machine St Ps Sy := mirror T'")
    L.append("")
    L.append(("/-- 反転した T' の" if mirror else "/-- T' の") + " Q₋ の状態（`threestate.py` の W.minus と同じ順）。 -/")
    L.append(f"def qm{R} : List St := [" + ", ".join(sid[q] for q in W.minus) + "]")
    L.append("/-- 右移動の行き先と書込記号の組 R（W.Rset）。 -/")
    L.append(f"def Rl{R} : List (St × Sy) := [" + ", ".join(f"({sid[p]}, {yid[v]})" for p, v in W.Rset) + "]")
    L.append("/-- Q₊ の印の組 G（W.Gset）。 -/")
    L.append(f"def Gl{R} : List (St × Sy) := [" + ", ".join(f"({sid[p]}, {yid[v]})" for p, v in W.Gset) + "]")
    L.append("")
    L.append("/-- 1WU 機械の状態の番号付け ν（`threestate.py` の群の並べ方の最適解。番号は位置 + 1）。 -/")
    L.append("def ordW : List (VSt St Sy) := [" + ", ".join(ordW) + "]")
    L.append("/-- VSt の残り（q_L と、W に現れない r・g）。 -/")
    L.append("def restW : List (VSt St Sy) := [" + ", ".join(rest) + "]")
    L.append("def allVSt : List (VSt St Sy) := ordW ++ restW")
    L.append("def idx (q : VSt St Sy) : Nat := allVSt.idxOf q + 1")
    L.append("def numf (i : Nat) : VSt St Sy := allVSt.getD (i - 1) .L")
    L.append("")
    L.append("/-- 計数の上限 need（`threestate.py` の need。W の記号ごと）。 -/")
    L.append("def needL : List (VSym St Sy × Nat) := [" + ", ".join(f"({x}, {k})" for x, k in needL) + "]")
    L.append("def need (x : VSym St Sy) : Nat := (needL.lookup x).getD 0")
    L.append("")
    names = []
    for i in range(0, len(rules), CHUNK):
        nm = f"T3py{i // CHUNK}"
        names.append(nm)
        L.append(f"def {nm} : Machine TSt Ps (CSym (VSym St Sy)) := [")
        chunk = rules[i:i + CHUNK]
        for j, (p, s, t, d, q) in enumerate(chunk):
            sep = "," if j + 1 < len(chunk) else ""
            L.append(f"  ⟨{tst[p]}, {csym(s)}, {csym(t)}, {dirs[d]}, .go {tst[q]}⟩{sep}")
        L.append("]")
    L.append("")
    if mirror:
        L.append("/-- `tools/threestate.py convert --mirror` の 3 状態機械（URTM(3,600)）の規則をそのまま写したもの。 -/")
    else:
        L.append(f"/-- `tools/threestate.py convert`（反転なし）の 3 状態機械（{len(TS.symbols)} 記号）の規則をそのまま写したもの。 -/")
    L.append("def T3py : Machine TSt Ps (CSym (VSym St Sy)) := " + " ++ ".join(names))
    L.append("/-- 同じく記号（W の記号と計数）。 -/")
    L.append("def sym3py : List (CSym (VSym St Sy)) := [" + ", ".join(csym(x) for x in TS.symbols) + "]")
    L.append("")
    L.append("/-- **Lean の一般の変換（" + ("反転版" if mirror else "反転なし") + "）の値は Python の表と規則の並びまで一致する**。 -/")
    L.append(f"theorem {CV}_eq_py : Conv3S.{CV} T' Sy.s0 ss qm{R} Rl{R} Gl{R} idx need = T3py := by decide +kernel")
    L.append("/-- 記号の全体（Conv3P.univ）も Python の記号の列と一致する。 -/")
    L.append(f"theorem univ_eq_py : Conv3P.univ need (Conv3S.wsyms ss qm{R} Gl{R}) = sym3py := by decide +kernel")
    L.append(f"theorem card3 : sym3py.length = {len(TS.symbols)} ∧ T3py.length = {len(rules)} := by decide +kernel")
    L.append("theorem sym3py_nodup : sym3py.Nodup := by decide +kernel")
    L.append("")
    L.append(f"/-! ## 仮定の有限検査（一般定理 `Conv3S.{CV}_main` に渡す） -/")
    L.append("")
    L.append("theorem subT' : ∀ r ∈ T', r ∈ T := fun _ hr => (mem_dropHalt.mp hr).1")
    if mirror:
        L.append("theorem hDR : Deterministic TR := det_mirror (Deterministic.mono subT' hD)")
        L.append("theorem hRR : Reversible TR := rev_mirror (Reversible.mono subT' hR)")
        L.append("/-- 反転した T' の 1WU 化。 -/")
    else:
        L.append("theorem hDT : Deterministic T' := Deterministic.mono subT' hD")
        L.append("theorem hRT : Reversible T' := Reversible.mono subT' hR")
        L.append("/-- T' の 1WU 化。 -/")
    L.append(f"def {WM} : Machine (VSt St Sy) Ps (VSym St Sy) := Conv1W.conv {TM} Sy.s0 ss qm{R} Rl{R} Gl{R}")
    L.append("def rlOK (r : Rule St Ps Sy) : Bool :=")
    L.append("  match r.q with")
    L.append(f"  | .go q => r.d != .R || Rl{R}.contains (q, r.t)")
    L.append("  | .halt _ => true")
    L.append("def idxOK (r : Rule (VSt St Sy) Ps (VSym St Sy)) : Bool :=")
    L.append("  match r.q with")
    L.append("  | .go q => q == .L || (decide (1 ≤ idx q) && decide (idx q ≤ need r.t))")
    L.append("  | .halt _ => true")
    L.append("def srcOK (r : Rule (VSt St Sy) Ps (VSym St Sy)) : Bool :=")
    L.append("  r.p == .L || (decide (1 ≤ idx r.p) && decide (idx r.p ≤ need r.s))")
    L.append(f"theorem hG' : ∀ r ∈ {TM}, r.q.isGo = true ∧ r.d ≠ .Z := by decide +kernel")
    L.append(f"theorem hRl' : ∀ r ∈ {TM}, rlOK r = true := by decide +kernel")
    L.append(f"theorem hqm' : ∀ p ∈ qm{R}, isPlus {TM} p = false := by decide +kernel")
    L.append(f"theorem hRG : ∀ pv ∈ Rl{R}, pv ∈ Gl{R} := by decide +kernel")
    L.append(f"theorem hGl : ∀ pv ∈ Gl{R}, isPlus {TM} pv.1 = true := by decide +kernel")
    L.append(f"theorem hqm : ∀ q, isPlus {TM} q = false → q ∈ qm{R} := by intro q; cases q <;> decide +kernel")
    L.append(f"theorem hidx' : ∀ r ∈ {WM}, idxOK r = true := by decide +kernel")
    L.append(f"theorem hsrc' : ∀ r ∈ {WM}, srcOK r = true := by decide +kernel")
    L.append("theorem dec_idx : ∀ q ∈ allVSt, numf (idx q) = q := by decide +kernel")
    L.append("theorem allVSt_all : ∀ q : VSt St Sy, q ∈ allVSt := by")
    L.append("  intro q")
    L.append("  cases q with")
    L.append("  | L => decide +kernel")
    L.append("  | c s => cases s <;> decide +kernel")
    L.append("  | e1 => decide +kernel")
    L.append("  | e2 => decide +kernel")
    L.append("  | r p v => cases p <;> cases v <;> decide +kernel")
    L.append("  | g p v => cases p <;> cases v <;> decide +kernel")
    L.append("theorem idx_inj (p q : VSt St Sy) (h : idx p = idx q) : p = q := by")
    L.append("  rw [← dec_idx p (allVSt_all p), ← dec_idx q (allVSt_all q), h]")
    L.append(f"theorem need_c' : ∀ s ∈ ss, ∀ x ∈ Conv3S.wsyms ss qm{R} Gl{R}, idx (.c s) ≤ need x := by decide +kernel")
    L.append(f"theorem need_r' : ∀ pv ∈ Rl{R}, ∀ x ∈ ss, idx (.r pv.1 pv.2) ≤ need (.pl x) := by decide +kernel")
    L.append(f"theorem need_g' : ∀ pv ∈ Gl{R}, ∀ u ∈ ss, idx (.g pv.1 pv.2) ≤ need (.pl u) := by decide +kernel")
    L.append("")
    L.append(f"theorem hyp : Conv3S.Hyp {TM} Sy.s0 ss qm{R} Rl{R} Gl{R} idx need where")
    L.append("  hS := hS")
    L.append("  hG := hG'")
    L.append("  hD := " + ("hDR" if mirror else "hDT"))
    L.append("  hR := " + ("hRR" if mirror else "hRT"))
    L.append("  hqm := hqm")
    L.append("  hqm' := hqm'")
    L.append("  hRl := by")
    L.append("    intro r hr q hq hd")
    L.append("    have := hRl' r hr")
    L.append("    simp only [rlOK, hq, hd, bne_self_eq_false, Bool.false_or] at this")
    L.append("    exact List.mem_of_elem_eq_true this")
    L.append("  hRG := hRG")
    L.append("  hGl := hGl")
    L.append("  hidx := by")
    L.append("    intro r hr q hq hqL")
    L.append("    have := hidx' r hr")
    L.append("    unfold idxOK at this")
    L.append("    rw [hq] at this; dsimp only at this")
    L.append("    have hb : (q == VSt.L) = false := by simp [hqL]")
    L.append("    simp only [hb, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at this")
    L.append("    exact this")
    L.append("  hinj := fun p q _ _ h => idx_inj p q h")
    L.append("  need_c := fun s => need_c' s (hS s)")
    L.append("  need_r := fun pv hpv x => need_r' pv hpv x (hS x)")
    L.append("  need_g := fun pv hpv u => need_g' pv hpv u (hS u)")
    L.append("  need_e1 := by decide +kernel")
    L.append("  need_e2 := by decide +kernel")
    L.append("")
    L.append(f"theorem hsrc : ∀ r ∈ Conv1W.conv {TM} Sy.s0 ss qm{R} Rl{R} Gl{R}, r.p ≠ .L → 1 ≤ idx r.p ∧ idx r.p ≤ need r.s := by")
    L.append("  intro r hr hp")
    L.append("  have := hsrc' r hr")
    L.append("  unfold srcOK at this")
    L.append("  have hb : (r.p == VSt.L) = false := by simp [hp]")
    L.append("  simp only [hb, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at this")
    L.append("  exact this")
    L.append("")
    L.append(f"end URTM.Gen.{module}")
    print("\n".join(L))
    print(f"{module}: {len(TS.symbols)} symbols, {len(rules)} rules, W {len(W.quints)} rules", file=sys.stderr)


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("path")
    ap.add_argument("--module", default="T3_600")
    ap.add_argument("--base", default="K32_3")
    ap.add_argument("--no-mirror", dest="mirror", action="store_false",
                    help="反転しない版（Conv3S.conv）。既定は反転版（Conv3S.convM）")
    a = ap.parse_args()
    main(a.path, a.module, a.base, a.mirror)
