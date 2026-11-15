#!/usr/bin/env python3
"""ブロック分け × 役割の併合 × ε の変換（`lean/URTM/KStateBlocks.lean` の `bconv`、docs/22）を具体機械に適用する
Lean モジュール。

    python3 tools/gen_blocks_lean.py results/kstate_blocks/records/urtm4-46.json \\
        --module KB4_46 --base K10_8 > lean/URTM/Gen/KB4_46.lean

T・St・Sy・Ps は生成済みの密な版モジュール `URTM.Gen.BASE`（tools/gen_kstate_lean.py）のものを使う。
基底の表が `URTM.Gen.BASE.T` でないとき（(11,7) の `T11 = T.map chg` など。2026-11-02）は `--table T11 --table-import MOD
--table-open "NS (T11 hW11 hR11)" --hw hW11 --hr hR11` で表と ZeroShiftHalts・Reversible の名前を与え、`--parent PARENT.txt`
で St・Sy・Ps の名前の順を決める記述ファイル（BASE のもの）を、`--state-map JSON` で記述ファイルの状態名から PARENT の状態名
への写し（併合した状態 `m_…` など）を与える。PARENT にあって記述ファイルに無い状態（併合で消えた状態）は `qsB` の末尾に
置かれ（規則を持たないので往復の規則は出ない）、`spB` では 0 にする。`--mu JSON`（PARENT の状態名 → 記述ファイルの
状態名。併合した対）を与えると、記述ファイルの規則を Lean の表 `T.map chg` の並び（親の規則の順）に並べ替えてから
T' を作る（`lean_order`。対応は tools/gen_tagchain_lean.py と同じ道具で求める）。`bconv` は T の規則の順に R1 を置くので、
並びが違うと `bconv_eq_py` が偽になる（2026-11-02 に (4,40) で実測）。
親の 1 本が子の複数本に写る表（(10,7) の `T10 = (T11.flatMap chg).eraseDups`、2026-11-04）は `--mu` の代わりに
`--order-spec results/joint-2026-11-02/urtm10-7.desc.json`（tools/gen_child_desc.py の spec）で並べ替え（`lean_order_spec`）、
記述ファイルの記号名が PARENT と違うもの（(10,7) の `*_t3` は (13,7) の n1 の座）は `--sym-map '{"*_t3": "n1"}'` で写す。
足すもの:
  * `spB : BSpec St k` — 解（JSON）のブロック `blk`・計数値 `v`・番兵 `sg`・役割の類 `cls`
    （類の番号は `tools/kstate_blocks.py` の `Gen.states` の並び。規則を持たない類は 0 に寄せる）
  * `qsB` — Python の `Gen._build` が往復の規則を置く順（+ のブロック 1.. → − のブロック 1..、各ブロック内は
    T の状態の順）。`ssB` — 記号を名前の順に並べたもの（Python の `sorted(reads[q])`・`sorted(W[q])`）
  * `TpyB` — `tools/kstate_blocks.py` の `Gen` が作る T'（規則の並びもそのまま）
  * `bconv_eq_py : bconv T spB qsB ssB = TpyB`（カーネルの `decide`）— Lean の変換と Python の表は
    規則の並びまで一致する
  * `det_rev` — 生成表の決定性・可逆性（カーネルの `decide`。主定理の仮定 `hD'` にも使う）
  * `card` — 規則数、記号の全体 `symB`（Python の `Gen.symbols`）の長さと重複の無さ、表の記号が `symB` に
    入ること、`symB` のどの記号も表に現れること、`Fin k` のどの状態も表の現状態に現れること
"""

import argparse
import json
import os
import sys

sys.path.insert(0, __file__.rsplit("/", 1)[0])
import kstate_blocks  # noqa: E402

DIR = {"-": ".L", "0": ".Z", "+": ".R"}


def lean_order(info, parent, mu):
    """記述ファイルの規則を、Lean の表 `T.map chg`（親の規則の順に写したもの）の並びに並べ替える（info.T.quints を書き換える）。
    親の規則 (p,s,t,d,q) に対応する子の規則は tools/gen_tagchain_lean.py の `solve`（CTSH11_7.lean の `chg` を作った道具）で
    決める。並べ替えは規則の集合を変えない（検査する）。"""
    import gen_tagchain_lean as TC
    P, cases = TC.load(parent if os.path.exists(parent) else kstate_blocks.machine_path(parent))
    C, _ = TC.load(info.T.path)
    chg, ok = TC.solve(P, C, mu, cases, False)
    assert ok, "gen_tagchain_lean.solve could not match the parent's rules to the child's"
    order = []
    for (p, s), (t, d, q) in P.items():
        (s2, t2), = chg.get((p, s), [(s, t)])
        order.append((mu.get(p, p), s2, t2, d, mu.get(q, q)))
    old = list(info.T.quints)
    assert sorted(order) == sorted(old) and len(set(order)) == len(order), "the parent's image is not the child's rule set"
    info.T.quints = order


def lean_order_spec(info, spec):
    """記述ファイルの規則を Lean の表の並びに並べ替える（info.T.quints を書き換える）。`lean_order` の、親の 1 本が子の
    複数本に写る表（`(T.flatMap chg).eraseDups`、(10,7)）にも使える形: tools/gen_child_desc.py の spec
    （results/joint-2026-11-02/urtm10-7.desc.json など）から、祖先の記述ファイルの順を Lean の mu・chgSym で写して求める
    （`gen_child_desc.lean_order_rules`）。並べ替えは規則の集合を変えない（検査する）。2026-11-04（T25）。"""
    import gen_child_desc as GC
    order = GC.lean_order_rules(spec, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "data"))
    old = list(info.T.quints)
    assert sorted(order) == sorted(old) and len(set(order)) == len(order), "the Lean order is not the child's rule set"
    info.T.quints = order


def main(sol, module, base, parent=None, state_map=None, table="T", table_import=None, table_open=None,
         hw="hW", hr="hR", mu=None, sym_map=None, order_spec=None, sym_type="Sy", sym_names=None):
    r = json.load(open(sol))
    info = kstate_blocks.Info(kstate_blocks.machine_path(r["machine"]))
    if mu:
        lean_order(info, parent, mu)
    if order_spec:
        lean_order_spec(info, order_spec)
    symap = sym_map or {}            # 記述ファイルの記号名 → PARENT の記号名（違うものだけ。(10,7) の *_t3 は (13,7) の n1 の座）
    T = info.T
    g = kstate_blocks.gen_of(info, r)
    assert not g.conflicts(), g.conflicts()[:2]
    k = g.k
    bp, bm = g.bp, g.bm

    # St・Sy・Ps の名前は PARENT（既定は記述ファイル自身）の順。smap: 記述ファイルの状態名 → PARENT の状態名
    P = kstate_blocks.Info(kstate_blocks.machine_path(parent)).T if parent else T
    smap = {q: (state_map or {}).get(q, q) for q in T.states}
    bad = [q for q in T.states if smap[q] not in P.states]
    assert not bad, f"states not in the parent {parent}: {bad}"
    assert len(set(smap.values())) == len(T.states), "the state map is not injective"
    SY = sym_type                    # 記号の型の Lean 名（既定 Sy。基底の記号が PARENT と別の型のとき、(9,8) の Sy8。T28）
    if sym_names:
        # 記述ファイルの記号名 → Lean の構成子名（基底の記号の数が PARENT と違うとき）。symap は使わない
        assert not symap and set(sym_names) == set(T.symbols) and len(set(sym_names.values())) == len(sym_names), \
            "sym-names must name exactly the symbols of the description file"
        assert set(T.pseudo) == set(P.pseudo), "pseudo-states differ from the parent"
        yid = dict(sym_names)
    else:
        assert {symap.get(s, s) for s in T.symbols} == set(P.symbols) and len({symap.get(s, s) for s in T.symbols}) == len(T.symbols) \
            and set(T.pseudo) == set(P.pseudo), "symbols or pseudo-states differ from the parent"
        yid = {s: f"s{i}" for i, s in enumerate(P.symbols)}
    unused = [q for q in P.states if q not in smap.values()]       # 併合で消えた状態（規則を持たない）
    sid = {s: f"q{i}" for i, s in enumerate(P.states)}
    pid = {s: f"h{i}" for i, s in enumerate(P.pseudo)}
    sidx = {name: i for i, name in enumerate(g.states)}

    def sym(x):
        if g.is_counter(x):
            i, s = g.split_counter(x)
            assert i >= 0, x
            return f"KSym.ctr {i} {SY}.{yid[symap.get(s, s)]}"
        return f"KSym.pl {SY}.{yid[symap.get(x, x)]}"

    def st(c):
        return f"({sidx[c]} : Fin {k})"

    def tgt(q):
        return f".halt Ps.{pid[q]}" if q in T.pseudo else f".go {st(q)}"

    qsB = [q for d in "+-" for b in range(1, (bp if d == "+" else bm) + 1)
           for q in info.Qd[d] if g.blk[q] == b]
    assert sorted(qsB) == sorted(T.states)
    ssB = sorted(T.symbols)
    rules = g.quints
    nsym = len(g.symbols)

    cls_lines = []
    for role in kstate_blocks.roles_of(bp, bm):
        kind, d, b = role
        name = g.cls[role]
        cls_lines.append(f"    | .{kind}, {DIR[d]}, {b} => {sidx.get(name, 0)}")

    L = []
    L.append("/-")
    L.append(f"  {r['machine']} と {sol.split('/')[-1]} から自動生成（tools/gen_blocks_lean.py）。手で編集しないこと。")
    if parent:
        L.append(f"  基底の表は `{table}`（St・Sy・Ps の名前は {parent} の順）。状態の写し: "
                 + ", ".join(f"{q}={smap[q]}" for q in T.states if smap[q] != q)
                 + (f"。{parent} にあって現れない状態: {', '.join(unused)}" if unused else "")
                 + ("。記号の写し: " + ", ".join(f"{s}={t}" for s, t in sorted(symap.items())) if symap else ""))
    L.append(f"  ブロック分け × 役割の併合 × ε（tools/kstate_blocks.py、docs/22）: ブロック ({bp},{bm})、"
             f"状態 {k} / 記号 {nsym} / 五つ組 {len(rules)}")
    L.append("  併合: " + "; ".join("&".join(x) for x in g.groups) if g.groups else "  併合: なし")
    L.append("  状態の番号: " + ", ".join(f"{i}={n}" for i, n in enumerate(g.states)))
    L.append("  計数値: " + ", ".join(f"{q}={info.dir[q]}{g.blk[q]}:{g.v[q]}" for q in qsB)
             + "、番兵: " + ", ".join(f"{key}={val}" for key, val in sorted(g.sigma.items())))
    L.append("-/")
    L.append("import URTM.KStateBlocks")
    L.append(f"import URTM.Gen.{base}")
    if table_import:
        L.append(f"import {table_import}")
    L.append("")
    L.append("set_option maxRecDepth 100000")
    L.append("")
    L.append(f"namespace URTM.Gen.{module}")
    L.append("")
    L.append(f"open URTM URTM.KState URTM.KStateSparse URTM.KStateBlocks URTM.Gen.{base}")
    if table_open:
        L.append(f"open {table_open}")
    L.append("")
    L.append("/-- ブロック分け・計数値・番兵・役割の類（解の JSON から）。 -/")
    L.append(f"def spB : BSpec St {k} where")
    L.append("  blk q := match q with")
    L += [f"    | .{sid[smap[q]]} => {g.blk[q]}" for q in T.states] + [f"    | .{sid[q]} => 0" for q in unused]
    L.append("  v q := match q with")
    L += [f"    | .{sid[smap[q]]} => {g.v[q]}" for q in T.states] + [f"    | .{sid[q]} => 0" for q in unused]
    L.append("  sg d b := match d, b with")
    L += [f"    | {DIR[key[0]]}, {int(key[1:])} => {val}" for key, val in sorted(g.sigma.items())]
    L.append("    | _, _ => 0")
    L.append("  cls r d b := match r, d, b with")
    L += cls_lines
    L.append("    | _, _, _ => 0")
    L.append("")
    L.append("/-- 往復の規則を置く状態の順（Python の `Gen._build` の順）。 -/")
    L.append("def qsB : List St := [" + ", ".join(f".{sid[smap[q]]}" for q in qsB)
             + "".join(f", .{sid[q]}" for q in unused) + "]")
    L.append("/-- 記号を名前の順に（Python の `sorted`）。 -/")
    L.append(f"def ssB : List {SY} := [" + ", ".join(f".{yid[symap.get(s, s)]}" for s in ssB) + "]")
    L.append("")
    L.append("/-- `tools/kstate_blocks.py` の `Gen` が作った T'（規則の並びもそのまま）。 -/")
    L.append(f"def TpyB : Machine (Fin {k}) Ps (KSym {SY}) := [")
    L.append(",\n".join(f"  ⟨{st(p)}, {sym(s)}, {sym(t)}, {DIR[d]}, {tgt(q)}⟩" for (p, s, t, d, q) in rules))
    L.append("]")
    L.append("")
    L.append("/-- 記号の全体（Python の `Gen.symbols`: T の記号と、表に現れる計数記号）。 -/")
    L.append(f"def symB : List (KSym {SY}) := [" + ", ".join(sym(x) for x in g.symbols) + "]")
    L.append("")
    L.append("theorem hQB : ∀ q, q ∈ qsB := by intro q; cases q <;> decide")
    L.append("theorem hSB : ∀ s, s ∈ ssB := by intro s; cases s <;> decide")
    L.append("")
    L.append("/-- Lean の変換 `bconv` と Python の生成表は、規則の並びまで一致する（カーネルで検査）。 -/")
    L.append(f"theorem bconv_eq_py : bconv {table} spB qsB ssB = TpyB := by decide +kernel")
    L.append("")
    L.append("/-- 生成表の決定性・可逆性（カーネルの `decide`）。 -/")
    L.append("theorem det_rev : Deterministic TpyB ∧ Reversible TpyB := by")
    L.append("  constructor <;> decide +kernel")
    L.append("")
    L.append(f"theorem card : TpyB.length = {len(rules)} ∧ symB.length = {nsym} ∧ symB.Nodup ∧")
    L.append("    (∀ ρ ∈ TpyB, ρ.s ∈ symB ∧ ρ.t ∈ symB) ∧ (∀ σ ∈ symB, ∃ ρ ∈ TpyB, ρ.s = σ ∨ ρ.t = σ) ∧")
    L.append(f"    (∀ x : Fin {k}, ∃ ρ ∈ TpyB, ρ.p = x) := by decide +kernel")
    L.append("")
    L.append(f"""/-- 変換を {r['machine']} に適用した結論。T' = `bconv T spB qsB ssB`（= `TpyB`）は
    {k} 状態（型 `Fin {k}`、どの状態も現状態に現れる）・記号は {nsym} 要素の `symB` に入る（どれも実際に現れる）・
    規則 {len(rules)} 本の決定的可逆機械で、{table} の各ステップを `bcost` = 3 + 2|v − σ| ステップで模倣する。 -/
theorem main :
    let T' := bconv {table} spB qsB ssB
    let E := benc {table} spB
    Deterministic T' ∧ Reversible T' ∧
    (∀ ρ ∈ T', ρ.s ∈ symB ∧ ρ.t ∈ symB) ∧ symB.length = {nsym} ∧ symB.Nodup ∧
    (∀ x : Fin {k}, ∃ ρ ∈ T', ρ.p = x) ∧ T'.length = {len(rules)} ∧ T' = TpyB ∧
    (∀ c c' : Cfg St Ps {SY}, Step {table} c c' → Live {table} c' → StepN T' (bcost {table} spB c') (E c) (E c')) ∧
    (∀ (n : Nat) (c cf : Cfg St Ps {SY}), HaltsIn {table} n c cf → (∃ h, cf.st = .halt h) →
      ∃ N, n ≤ N ∧ HaltsIn T' N (E c) (E cf)) ∧
    (∀ (N : Nat) (c : Cfg St Ps {SY}) (e : Cfg (Fin {k}) Ps (KSym {SY})), NoStuck {table} c →
      HaltsIn T' N (E c) e → ∃ n cf, HaltsIn {table} n c cf ∧ e = E cf) ∧
    (∀ c : Cfg St Ps {SY}, NoStuck {table} c →
      ((∀ n cf, ¬ HaltsIn {table} n c cf) ↔ (∀ N e, ¬ HaltsIn T' N (E c) e))) := by
  intro T' E
  have hT : T' = TpyB := bconv_eq_py
  obtain ⟨hD', hR'⟩ := det_rev
  obtain ⟨hlen, hsl, hsn, hsym, -, hst⟩ := card
  rw [← hT] at hD' hR' hsym hst hlen
  exact ⟨hD', hR', hsym, hsl, hsn, hst, hlen, hT, bconv_main {hw} {hr} hQB hSB hD'⟩""")
    L.append("")
    L.append(f"end URTM.Gen.{module}")
    print("\n".join(L))


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("solution", help="tools/kstate_blocks.py の解の JSON（results/kstate_blocks/records/*.json）")
    ap.add_argument("--module", required=True)
    ap.add_argument("--base", required=True, help="同じ記述ファイルから作った密な版のモジュール名（K10_8 など）")
    ap.add_argument("--parent", help="St・Sy・Ps の名前の順を決める記述ファイル（BASE のもの。既定は解の記述ファイル）")
    ap.add_argument("--state-map", help="JSON: 解の記述ファイルの状態名 → PARENT の状態名（違うものだけ）")
    ap.add_argument("--table", default="T", help="基底の表の Lean の名前（既定 T）")
    ap.add_argument("--table-import", help="表を定義するモジュール（import 行）")
    ap.add_argument("--table-open", help="open 行の中身（例: URTM.CTSH.U11_7 (T11 hW11 hR11)）")
    ap.add_argument("--hw", default="hW", help="ZeroShiftHalts TABLE の定理名")
    ap.add_argument("--hr", default="hR", help="Reversible TABLE の定理名")
    ap.add_argument("--mu", help="JSON: PARENT の状態名 → 記述ファイルの状態名（併合した対）。規則を Lean の表の並びに並べ替える")
    ap.add_argument("--sym-map", help="JSON: 記述ファイルの記号名 → PARENT の記号名（違うものだけ）")
    ap.add_argument("--sym-type", default="Sy", help="記号の型の Lean 名（基底の記号が PARENT と別の型のとき。(9,8) の URTM.CTSH.U9_8.Sy8）")
    ap.add_argument("--sym-names", help="JSON: 記述ファイルの記号名 → Lean の構成子名（基底の記号の数が PARENT と違うとき。--sym-map の代わり）")
    ap.add_argument("--order-spec", help="tools/gen_child_desc.py の spec。規則を Lean の表の並び（祖先の順を mu・chgSym で写したもの）に並べ替える（--mu の代わり）")
    a = ap.parse_args()
    main(a.solution, a.module, a.base, a.parent, json.loads(a.state_map) if a.state_map else None, a.table,
         a.table_import, a.table_open, a.hw, a.hr, json.loads(a.mu) if a.mu else None,
         json.loads(a.sym_map) if a.sym_map else None, a.order_spec, a.sym_type,
         json.loads(a.sym_names) if a.sym_names else None)
