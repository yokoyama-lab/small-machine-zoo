#!/usr/bin/env python3
"""1 ブロック 3 状態の変種（旧リポ kstate_convert.py --mode pure）の疎版（docs/15）。

ブロック分けと並びを局所探索で選び、使われない計数記号 [s,c] を落として生成し、
元機械と配置単位で突き合わせる。

    python3 tools/kstate_sparse_pure.py data/urtm/urtm10-8.txt 1 1 out/urtm6-45.txt   # → URTM(6,45)
    python3 tools/kstate_sparse_pure.py data/urtm/urtm15-6.txt 2 1 out/urtm9-37.txt   # → URTM(9,37)

`--lean FILE --module NAME --base BASE` を付けると、Lean の一般定理（lean/URTM/KStatePure.lean の
`spconv`）を具体機械に当てる生成モジュールも書く（T・St・Sy・Ps は密な定理 A 版の `URTM.Gen.BASE`）。

記号 [s,c] が要るのは、ブロック内の位置 loc(q) ≥ c の状態 q が s を使う（読む、または q に入る
規則が書く）ときだけ（計数は元セルで loc(q) から 0 へ、行き先で 0 から loc(q) へ動く）。
全ブロックが同じ計数値を共有するので、各方向の状態を下の段から H_d 個ずつ詰めた並びを探す。

疑似状態（halt・null）へ入る規則（Morita の記述ファイルでは 0 シフト）は、定理 A（KState.lean の R1'）
と同じく規則 A' [安定状態, [s, loc p], t, d, 疑似状態] として残す（2026-09-27、docs/15 §6）。
旧リポの kstate_convert.py はこれを落として「規則が無いこと」で止めていたが、zoo の CTSH 模倣の
定理は疑似状態で止まる配置を扱うので、それに合わせた。記号は増えない（読む [s, loc p] は need(p) に入る）。
そのため突き合わせも旧リポの check_kstate（規則の無いことで止まる前提）ではなく、この下の `check`
（T の 1 ステップごとに T' がちょうど 3 + 2·loc(q)（停止規則は 1）ステップで符号化に達するか）で行う。
"""

import argparse
import random
import sys

HERE = __file__.rsplit("/", 1)[0]
sys.path.insert(0, HERE)
sys.path.insert(0, HERE + "/../legacy/small-urtm/tools")
import kstate  # noqa: E402
import kstate_convert  # noqa: E402
from kstate_sparse_k4 import need_sets  # noqa: E402

MOVE = {"-": -1, "0": 0, "+": 1}


def levels(order, h):
    """下から h 個ずつ段に詰めたときの各状態の段（= ブロック内の位置）。"""
    return {q: i // h for i, q in enumerate(order)}


def cost(orders, hs, need, n):
    lv = {}
    for d in "+-":
        lv.update(levels(orders[d], hs[d]))
    top = max(lv.values()) + 1
    return n + sum(len(set().union(*[need[q] for q in lv if lv[q] >= c])) for c in range(top))


def search(T, hs, iters=6000, seed=0):
    rnd = random.Random(seed)
    need = need_sets(T)
    n = len(T.symbols)
    qd = kstate.Construction(T, "k4", (1, 1)).Qd
    cur = {d: sorted(qd[d], key=lambda q: -len(need[q])) for d in "+-"}
    best = cost(cur, hs, need, n)
    for _ in range(iters):
        d = rnd.choice("+-")
        if len(cur[d]) < 2:
            continue
        o = list(cur[d])
        i, j = rnd.sample(range(len(o)), 2)
        o[i], o[j] = o[j], o[i]
        cand = dict(cur)
        cand[d] = o
        c = cost(cand, hs, need, n)
        if c <= best:
            best, cur = c, cand
    return best, cur


def run_to_halt_or(delta, pseudo, cfg):
    """1 ステップ。規則が無い・疑似状態なら None。"""
    st, pos, tape = cfg
    if st in pseudo:
        return None
    r = delta.get((st, tape.get(pos, BLANK[0])))
    if r is None:
        return None
    t, d, q = r
    tape = dict(tape)
    tape[pos] = t
    return (q, pos + MOVE[d], tape)


BLANK = [None]


def check(T, conv, pseudo, cases, limit):
    """T の 1 ステップごとに、T' がちょうど cost ステップで符号化に達することを確かめる。"""
    loc, h, dirmap = conv["l"], conv["h"], conv["dirmap"]
    blank = BLANK[0]
    dT = {(p, s): (t, d, q) for (p, s, t, d, q) in T.quints}
    dP = {}
    for (p, s, t, d, q) in conv["quints_out"]:
        assert (p, s) not in dP, "T' が決定的でない"
        dP[(p, s)] = (t, d, q)

    def enc(cfg):
        st, pos, tape = cfg
        if st in pseudo:
            return (st, pos, {i: x for i, x in tape.items() if x != blank})
        name = ("r0" if dirmap[st] == "+" else "l0") + f"_{h[st]}"
        tp = {i: x for i, x in tape.items() if x != blank}
        tp[pos] = (tape.get(pos, blank), loc[st])
        return (name, pos, tp)

    def norm(cfg):
        st, pos, tape = cfg
        return (st, pos, {i: x for i, x in tape.items() if x != blank})

    res = []
    for case in cases:
        c = (case["state"], case["pos"], dict(enumerate(case["tape"])))
        e = enc(c)
        n = 0
        status = None
        while True:
            c2 = run_to_halt_or(dT, pseudo, c)
            if c2 is None:
                status = "ok" if run_to_halt_or(dP, pseudo, e) is None else "mismatch"
                break
            if n >= limit:
                status = "truncated"
                break
            k = 1 if c2[0] in pseudo else 3 + 2 * loc[c2[0]]
            for _ in range(k):
                e = run_to_halt_or(dP, pseudo, e)
                if e is None:
                    break
            if e is None or norm(e) != enc(c2):
                status = "mismatch"
                break
            c, n = c2, n + 1
        res.append((status, n))
    return res


def build(src, hp, hm):
    T = kstate.Machine(src)
    BLANK[0] = T.blank
    hs = {"+": hp, "-": hm}
    est, orders = min((search(T, hs, seed=s) for s in range(6)), key=lambda x: x[0])

    def custom_blocks(states, dirmap, mode, maxblock):
        blocks, hh = {}, 0
        for d in "+-":
            for b in range(hs[d]):
                blk = orders[d][b::hs[d]]
                if blk:
                    blocks[hh] = blk
                    hh += 1
        h, loc = {}, {}
        for k, blk in blocks.items():
            for i, q in enumerate(blk):
                h[q], loc[q] = k, i
        return h, loc, blocks

    kstate_convert.assign_blocks = custom_blocks
    info = kstate_convert.load_source(src)
    conv = kstate_convert.convert(info, "pure", None)
    pseudo = set(T.pseudo)
    loc, h, dirmap = conv["l"], conv["h"], conv["dirmap"]
    # A / A': T の規則をすべて（疑似状態行きも）T の並びで。
    A = []
    for (p, s, t, d, q) in info["quints"]:
        frm = ("r0" if dirmap[p] == "+" else "l0") + f"_{h[p]}"
        if q in pseudo:
            A.append((frm, (s, loc[p]), t, d, q))
        else:
            assert d != "0", "0 シフトで実状態へ入る規則"
            A.append((frm, (s, loc[p]), (t, loc[q]), d, ("r0" if d == "+" else "l0") + f"_{h[q]}"))
    dense = A + conv["quints_out"][len(conv["kept"]):]
    need = need_sets(T)
    keep = {(s, c) for q, pos in loc.items() for c in range(pos + 1) for s in need[q]}

    def kept(sym):
        return sym in keep if isinstance(sym, tuple) else True

    conv["quints_out"] = [r for r in dense if kept(r[1]) and kept(r[2])]
    syms = {r[1] for r in dense} | {r[2] for r in dense} | set(info["symbols"])
    conv["symbols_out"] = sorted((s for s in syms if kept(s)), key=kstate_convert.sym_sort_key)
    conv["states_out"] = sorted({r[0] for r in conv["quints_out"]}
                                | {r[4] for r in conv["quints_out"] if r[4] not in pseudo})
    conv["dropped_zero"] = conv["dropped_nostate"] = 0
    return T, info, conv, est


def lean_module(T, conv, src, module, base):
    sid = {s: f"q{i}" for i, s in enumerate(T.states)}
    yid = {s: f"s{i}" for i, s in enumerate(T.symbols)}
    pid = {s: f"h{i}" for i, s in enumerate(T.pseudo)}
    DIR = {"-": ".L", "0": ".Z", "+": ".R"}

    def st2(name):
        kind, b = name.split("_")
        return {"r0": f"PSt.z .R {b}", "l0": f"PSt.z .L {b}",
                "r1": f"PSt.o .R {b}", "l1": f"PSt.o .L {b}"}[kind]

    def sym2(x):
        if isinstance(x, tuple):
            return f"KSym.ctr {x[1]} Sy.{yid[x[0]]}"
        return f"KSym.pl Sy.{yid[x]}"

    def tgt2(q):
        return f".halt Ps.{pid[q]}" if q in T.pseudo else f".go ({st2(q)})"

    blocks = [conv["blocks"][k] for k in sorted(conv["blocks"])]
    ns, nsym, nr = len(conv["states_out"]), len(conv["symbols_out"]), len(conv["quints_out"])
    name = src.split("/")[-1]
    L = []
    L.append("/-")
    L.append(f"  {name} から自動生成（tools/kstate_sparse_pure.py --lean, --base {base}）。手で編集しないこと。")
    L.append(f"  1 ブロック 3 状態の変換の疎版（lean/URTM/KStatePure.lean の spconv）: "
             f"状態 {ns} / 記号 {nsym} / 五つ組 {nr}")
    for k, blk in enumerate(blocks):
        L.append(f"  ブロック {k}（dir {conv['dirmap'][blk[0]]}、位置 0 から）: " + ", ".join(blk))
    L.append("-/")
    L.append("import URTM.KStatePure")
    L.append(f"import URTM.Gen.{base}")
    L.append("")
    L.append("set_option maxRecDepth 100000")
    L.append("set_option maxHeartbeats 0")
    L.append("")
    L.append(f"namespace URTM.Gen.{module}")
    L.append("")
    L.append(f"open URTM URTM.KState URTM.KStatePure URTM.Gen.{base}")
    L.append("")
    L.append("/-- `tools/kstate_sparse_pure.py` が選んだブロック分け（各ブロックの状態を位置 0 から）。 -/")
    L.append("def blocksPy : List (List St) := [" + ", ".join(
        "[" + ", ".join(f".{sid[q]}" for q in blk) + "]" for blk in blocks) + "]")
    L.append("")
    L.append("/-- ブロック分け（`layoutOf`）。 -/")
    L.append("def LP : Layout St := layoutOf T blocksPy")
    L.append("")
    L.append("/-- `tools/kstate_sparse_pure.py` が生成した疎版 T' をそのまま写したもの（規則の並びも）。 -/")
    L.append("def TpyP : Machine PSt Ps (KSym Sy) := [")
    L.append(",\n".join(f"  ⟨{st2(p)}, {sym2(s)}, {sym2(t)}, {DIR[d]}, {tgt2(q)}⟩"
                        for (p, s, t, d, q) in conv["quints_out"]))
    L.append("]")
    L.append("")
    L.append("/-- `tools/kstate_sparse_pure.py` の記号の表（出力ファイルの `symbols` と同じ並び）。 -/")
    L.append("def symPy : List (KSym Sy) := [" + ", ".join(sym2(x) for x in conv["symbols_out"]) + "]")
    L.append("")
    L.append("/-- `tools/kstate_sparse_pure.py` の状態の表（出力ファイルの `states` と同じ並び）。 -/")
    L.append("def stPy : List PSt := [" + ", ".join(st2(x) for x in conv["states_out"]) + "]")
    L.append("")
    L.append("/-- ブロック分けの条件（有限の検査）。 -/")
    L.append("theorem hGL : GoodL T LP qs := by decide")
    L.append("")
    L.append("theorem hG : Good T LP := good_of_L hQ hGL")
    L.append("")
    L.append("/-- Lean の疎版 `spconv` と Python の生成表は、規則の並びまで一致する（カーネルで検査）。 -/")
    L.append("theorem spconv_eq_py : spconv T LP qs ss = TpyP := by decide +kernel")
    L.append("")
    L.append(f"theorem card : TpyP.length = {nr} ∧ symPy.length = {nsym} ∧ symPy.Nodup ∧"
             f" stPy.length = {ns} ∧ stPy.Nodup := by decide +kernel")
    L.append("")
    L.append("/-- 規則の記号はすべて `symPy` に、状態はすべて `stPy` に入る。 -/")
    L.append("theorem syms_sts : ∀ ρ ∈ TpyP, ρ.s ∈ symPy ∧ ρ.t ∈ symPy ∧ ρ.p ∈ stPy ∧"
             " tgtIn stPy ρ.q = true := by decide +kernel")
    L.append("")
    L.append(f"end URTM.Gen.{module}")
    return "\n".join(L) + "\n"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("src")
    ap.add_argument("hp", type=int)
    ap.add_argument("hm", type=int)
    ap.add_argument("out")
    ap.add_argument("--lean", default=None, help="生成する Lean モジュールのパス")
    ap.add_argument("--module", default=None)
    ap.add_argument("--base", default=None, help="T・St・Sy・Ps を持つ密な版のモジュール名（K10_8 など）")
    a = ap.parse_args()
    T, info, conv, est = build(a.src, a.hp, a.hm)
    kstate_convert.render(a.src, info, conv, a.out)
    print(f"{a.src.split('/')[-1]} H=({a.hp},{a.hm}): 見積もり {est} → 生成 {len(conv['states_out'])} 状態 "
          f"{len(conv['symbols_out'])} 記号 {len(conv['quints_out'])} 規則"
          f"（疑似状態行き {sum(1 for r in conv['quints_out'] if r[4] in T.pseudo)} 本を含む）")
    print("  blocks:", conv["blocks"])
    res = check(T, conv, set(T.pseudo), info["cases"], info["maxstep"])
    st = [r[0] for r in res]
    print("  check: " + " ".join(f"{s}({n})" for s, n in res))
    print(f"  check: ok={st.count('ok')} truncated={st.count('truncated')} "
          f"mismatch={st.count('mismatch')} / {len(res)}")
    if a.lean:
        with open(a.lean, "w", encoding="utf-8") as f:
            f.write(lean_module(T, conv, a.src, a.module, a.base))
    return 1 if "mismatch" in st else 0


if __name__ == "__main__":
    sys.exit(main())
