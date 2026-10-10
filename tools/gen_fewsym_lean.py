#!/usr/bin/env python3
"""記号削減＋併合の記録（results/fewsym/records/*.merge.json、docs/23）から Lean モジュールを生成する。

生成物は lean/URTM/FewSym.lean の一般定理 `fs_simulates` に渡す具体の材料:
  * `M`    : 併合した 2 記号機械の表（fewsym_merge.Merged の規則をそのまま。状態は通し番号 Nat、記号は Bool）
  * `E`    : 符号化（記号の符号 `code`、ブロック長 k、読み始める状態 ρ（併合後の名前）、ブロック内の桁 ce）
  * `cost` : T の規則ごとの模倣のステップ数（fewsym3.ConvK.costs）
と、カーネルの `decide` で確かめる事実（検査 `certB` が通る・決定的・可逆・状態数・ステップ数の内訳）。

    python3 tools/gen_fewsym_lean.py results/fewsym/records/urtm24-4.2.merge.json --module FS94_2 --base K24_4 \
        > lean/URTM/Gen/FS94_2.lean

`--unmerged` は併合する前の表（記録の `base`、fewsym3 の CP-SAT の解をそのまま。(13,7) では 135 状態）を同じ形で
書き出す。`--merged-module FS92_2` を付けると、併合の写像 `hm`（併合前の状態の番号 → 併合後の番号）と、
併合後の表がちょうど併合前の表の像であること（`merge_img`・`merge_onto`）、読み始める状態が写ること（`merge_ρ`）を
`decide +kernel` で確かめる定理も書く。既定（併合後の表）の出力は従来と同じ。

    python3 tools/gen_fewsym_lean.py results/fewsym/records/urtm13-7.2.merge.json --module FS135_2 --base K13_7 \
        --unmerged --merged-module FS92_2 > lean/URTM/Gen/FS135_2.lean
"""

import argparse
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import fewsym_merge as FM  # noqa: E402
import fewsym2 as G  # noqa: E402
from kstate import Machine  # noqa: E402

DIR = {"+": ".R", "-": ".L", "0": ".Z"}


def bl(x):
    return "true" if x else "false"


def main(argv):
    ap = argparse.ArgumentParser()
    ap.add_argument("record")
    ap.add_argument("--module", required=True)
    ap.add_argument("--base", required=True, help="元機械の生成モジュール（K24_4 など）")
    ap.add_argument("--unmerged", action="store_true", help="併合する前の表を書き出す")
    ap.add_argument("--merged-module", default=None, help="（--unmerged のとき）併合後の表の生成モジュール（FS92_2 など）")
    a = ap.parse_args(argv)
    m = json.load(open(a.record))
    cv, sol = FM.load_conv(m["base"])
    rep = {FM.unkey(k): FM.unkey(v) for k, v in m["rep"].items()}
    mgm = FM.Merged(cv, rep)
    assert a.merged_module is None or a.unmerged, "--merged-module は --unmerged と組で使う"
    mg = FM.Merged(cv, {}) if a.unmerged else mgm
    assert not mg.check_table(), mg.check_table()
    T = cv.T
    assert cv.r == 2, "2 記号（Bool）のみ"
    K = Machine(os.path.join("data/urtm", T.name + ".txt"))
    sid = {s: f"q{i}" for i, s in enumerate(K.states)}
    yid = {s: f"s{i}" for i, s in enumerate(K.symbols)}
    # 状態の通し番号（名前の辞書順）
    states = sorted(mg.states(), key=G.sname)
    num = {s: i for i, s in enumerate(states)}
    n = len(states)
    if a.unmerged:
        assert n == m["from"] == cv.nstates(), (n, m["from"], cv.nstates())
    else:
        assert n == m["states"], (n, m["states"])
        assert len(mg.rules) == m["rules"], (len(mg.rules), m["rules"])
    costs = sorted({cv.costs[(p, s)] for (p, s, t, d, q) in T.rules})
    L = []
    L.append("/-")
    L.append(f"  {os.path.basename(a.record)} から自動生成（tools/gen_fewsym_lean.py）。手で編集しないこと。")
    if a.unmerged:
        L.append(f"  {T.name} → 併合前の表 ({n},2)、{len(mg.rules)} 本（併合すると {mgm.nstates()} 状態）。k = {cv.k}、"
                 f"符号 {json.dumps({s: ''.join(map(str, c)) for s, c in cv.code.items()})}。")
    else:
        L.append(f"  {T.name} → ({n},2)、{len(mg.rules)} 本（併合前 {cv.nstates()} 状態）。k = {cv.k}、"
                 f"符号 {json.dumps({s: ''.join(map(str, c)) for s, c in cv.code.items()})}。")
    L.append(f"  T の 1 ステップの模倣は {costs} ステップ（規則ごと）。")
    L.append("-/")
    L.append("import URTM.FewSym")
    L.append(f"import URTM.Gen.{a.base}")
    if a.merged_module:
        L.append(f"import URTM.Gen.{a.merged_module}")
    L.append("")
    L.append("set_option maxRecDepth 100000")
    L.append("")
    L.append(f"namespace URTM.Gen.{a.module}")
    L.append("")
    L.append(f"open URTM URTM.KState URTM.FewSym URTM.Gen.{a.base}")
    L.append("")
    L.append("-- 状態: " + ", ".join(f"{i}={G.sname(s)}" for i, s in enumerate(states)))
    L.append("")
    if a.unmerged:
        L.append("/-- 併合する前の 2 記号機械（fewsym3 の CP-SAT の解から作った表をそのまま）。 -/")
    else:
        L.append("/-- 併合した 2 記号機械（fewsym_merge.Merged の規則をそのまま）。 -/")
    L.append("def M : Machine Nat Ps Bool := [")
    L.append(",\n".join(f"  ⟨{num[x]}, {bl(b)}, {bl(y)}, {DIR[d]}, .go {num[z]}⟩" for (x, b, y, d, z) in mg.rules))
    L.append("]")
    L.append("")
    L.append("/-- 記号の符号（長さ k のビット列）。 -/")
    L.append("def code : Sy → List Bool")
    for s in K.symbols:
        L.append(f"  | .{yid[s]} => [{', '.join(bl(x) for x in cv.code[s])}]")
    L.append("")
    L.append("/-- 状態 p を読み始める状態（[p^r] の併合後の名前）。 -/")
    L.append("def ρ : St → Nat")
    for q in K.states:
        L.append(f"  | .{sid[q]} => {num[mg.m(('r', q))]}")
    L.append("")
    L.append("/-- [p^r] でヘッドが居るブロック内の桁（向き e(p) = L なら 0、R なら k − 1）。 -/")
    L.append("def ce : St → Nat")
    for q in K.states:
        L.append(f"  | .{sid[q]} => {cv.ce(q)}")
    L.append("")
    L.append(f"def E : Enc St Sy Nat := ⟨code, {cv.k}, ρ, ce⟩")
    L.append("")
    L.append("/-- 規則 [p, s, …] の 1 ステップの模倣のステップ数（fewsym3.ConvK.costs）。 -/")
    L.append("def costPS : St → Sy → Nat")
    for (p, s, t, d, q) in T.rules:
        L.append(f"  | .{sid[p]}, .{yid[s]} => {cv.costs[(p, s)]}")
    L.append("  | _, _ => 0")
    L.append("def cost (r : Rule St Ps Sy) : Nat := costPS r.p r.s")
    L.append("")
    L.append("/-- 表に現れる状態の全体。 -/")
    L.append("def sts : List Nat := (M.map (·.p) ++ M.filterMap (fun ρ => match ρ.q with")
    L.append("  | .go x => some x")
    L.append("  | .halt _ => none)).eraseDups")
    L.append("")
    L.append("/-- 規則ごとの有限の検査（窓の上の実行）。 -/")
    L.append("theorem cert : certB T M E cost ss = true := by decide +kernel")
    L.append("theorem hyp : Hyp T M E cost ss := ⟨by decide, by intro s; cases s <;> rfl, hS, cert⟩")
    L.append("theorem det : Deterministic M := by decide +kernel")
    L.append("theorem rev : Reversible M := by decide +kernel")
    L.append(f"theorem card : (∀ ρ ∈ M, ρ.p ∈ sts ∧ ρ.q ∈ sts.map Tgt.go) ∧ sts.length = {n} ∧ M.length = {len(mg.rules)} := by")
    L.append("  decide +kernel")
    L.append("/-- 模倣のステップ数の内訳（停止しない規則ごと）。 -/")
    L.append("theorem costs : ∀ r ∈ T, r.q.isGo = true → " +
             " ∨ ".join(f"cost r = {c}" for c in costs) + " := by decide")
    L.append("")
    if a.merged_module:
        mm = f"URTM.Gen.{a.merged_module}"
        states2 = sorted(mgm.states(), key=G.sname)
        num2 = {s: i for i, s in enumerate(states2)}
        L.append(f"/-! ## 併合の写像（併合後の表 `{mm}.M` は、この表の状態を `hm` で名前替えした像） -/")
        L.append("")
        L.append(f"/-- 併合前の状態の番号 → 併合後の状態の番号（`{mm}` の番号付け）。 -/")
        L.append("def hmL : List (Nat × Nat) := [" + ", ".join(f"({num[s]}, {num2[mgm.m(s)]})" for s in states) + "]")
        L.append("def hm (i : Nat) : Nat := (hmL.lookup i).getD 0")
        L.append("/-- 規則の状態の名前替え。 -/")
        L.append("def mapR (r : Rule Nat Ps Bool) : Rule Nat Ps Bool :=")
        L.append("  ⟨hm r.p, r.s, r.t, r.d, match r.q with")
        L.append("    | .go x => .go (hm x)")
        L.append("    | .halt h => .halt h⟩")
        L.append(f"theorem merge_img : ∀ r ∈ M, mapR r ∈ {mm}.M := by decide +kernel")
        L.append(f"theorem merge_onto : ∀ r ∈ {mm}.M, ∃ r' ∈ M, mapR r' = r := by decide +kernel")
        L.append(f"theorem merge_ρ : ∀ p ∈ qs, hm (ρ p) = {mm}.ρ p := by decide +kernel")
        L.append("")
    L.append(f"end URTM.Gen.{a.module}")
    print("\n".join(L))
    return True


if __name__ == "__main__":
    sys.exit(0 if main(sys.argv[1:]) else 1)
