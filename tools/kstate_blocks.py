#!/usr/bin/env python3
"""ブロック分け × 役割の併合 × 数える向き ε の一般形と、その記号数の最適化（docs/22）。

kstate5.py（docs/20）の枠組みを、状態のブロック分け（定理 B、docs/03 §3）に広げたもの。

  * T の状態は入る向きで Q+ / Q- に分かれる（kstate5 と同じ。入られない状態は Q+）。
  * 方向 d ごとに b_d 個のブロックを置き、各状態 q ∈ Q_d をどれか 1 つのブロック blk(q) に入れる。
  * 各ブロック β（方向 d）は 3 つの役割 H_{dβ}・O_{dβ}・D_{dβ} を持つ（kstate5 の H_d・O^d・D^d をブロックごとに複製）。
    ブロックごとに計数値 v（ブロック内で単射）・番兵 σ_β・向き ε_β を持つ。計数記号 [i,s] はブロックを持たない
    （全ブロックで共有する。記号数はすべてのブロックが使う [i,s] の和集合で決まる）。
  * 規則（kstate5 と同じ。ブロック β の役割で置く）:
      R1  [H_{blk(p)}, [v(p),s], [v(q),t] (q が疑似状態なら t), d, H_{blk(q)} (または疑似状態)]
      R2  [H_β, s2, [σ_β,s2], e, O_β]                 s2 ∈ reads(q)、q ∈ β
      R3  [O_β, [i,t], [i-ε_β,t], d, D_β]            i ∈ (σ_β, v(q)]、t ∈ W(q)、q ∈ β
      R4  [O_β, [σ_β,t], t, d, H_β]                   t ∈ W(q)、q ∈ β
      R5  [D_β, [j,s2], [j+ε_β,s2], e, O_β]           j ∈ [σ_β, v(q))、s2 ∈ reads(q)、q ∈ β
  * 「併合」は役割の分割。同じ類の役割は同じ状態。入る向きが同じ役割だけを併合できる（Def 5.4）。
    H 同士の併合は扱わない（枠組みの外）。同じブロックの H と D の併合は docs/20 §3 の証明書で不可なので列挙しない。
    完全に同じ規則は 1 本と数える（ε を逆向きにした混合ブロックで O+ と D- の規則が一致する仕組み、docs/20 §3）。
  * 定理 B（docs/03）= ブロック β の O+_β & D-_β、D+_β & O-_β を併合（β ≤ min(b+,b-)）、ε 同じ向き・範囲分離。
    その ε 逆向き版 = 本稿の「εB」。pure（kstate_sparse_pure.py）= 併合なし。

    ~/.venvs/urtm/bin/python tools/kstate_blocks.py opt data/urtm/urtm10-8.txt --blocks 2,2 --spec thmB
    ~/.venvs/urtm/bin/python tools/kstate_blocks.py sweep --out out/kb --k 5-12
    python3 tools/kstate_blocks.py build SOL.json -o OUT.txt     # 解から機械を作って検査
"""

import argparse
import itertools
import json
import os
import sys
import time
from collections import defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import kstate  # noqa: E402
import kstate5  # noqa: E402
from kstate5 import Info, between  # noqa: E402

OPP = {"+": "-", "-": "+"}
# 役割 (kind, d, β) の入る向き: H_d・D_d は d 向き、O_d は逆向き
def entry(role):
    kind, d, _ = role
    return OPP[d] if kind == "o" else d


def tok(role):
    kind, d, b = role
    return f"{kind.upper()}{d}{b}"


def untok(s):
    return (s[0].lower(), s[1], int(s[2:]))


def sname(role):
    kind, d, b = role
    return f"{kind}{'p' if d == '+' else 'm'}{b}"


def roles_of(bp, bm):
    return [(k, d, b) for d, bb in (("+", bp), ("-", bm)) for b in range(1, bb + 1) for k in "hod"]


def classes_from_groups(bp, bm, groups):
    """groups: 併合する役割の組の列（各組は tok のリスト）。役割 → 状態名。"""
    cls = {r: sname(r) for r in roles_of(bp, bm)}
    seen = set()
    for g in groups:
        rs = [untok(t) for t in g]
        for r in rs:
            if r not in cls:
                raise SystemExit(f"{tok(r)}: no such role for blocks {bp},{bm}")
            if r in seen:
                raise SystemExit(f"{tok(r)}: in two groups")
            seen.add(r)
        if len({entry(r) for r in rs}) != 1:
            raise SystemExit(f"{g}: entry directions differ (violates Def 5.4)")
        if sum(r[0] == "h" for r in rs) > 1:
            raise SystemExit(f"{g}: merging two H roles is outside the framework")
        name = "_".join(sname(r) for r in rs)
        for r in rs:
            cls[r] = name
    return cls


def thmB_groups(bp, bm, pairs=None):
    """定理 B の併合: ブロック β の O+β & D-β、D+β & O-β（β = 1..min）。"""
    k = min(bp, bm) if pairs is None else pairs
    g = []
    for b in range(1, k + 1):
        g.append([f"O+{b}", f"D-{b}"])
        g.append([f"D+{b}", f"O-{b}"])
    return g


# ---------------------------------------------------------------- 構成
class Gen:
    """ブロック・併合・計数値・番兵・向きから T' を作る。kstate.lockstep と同じ口を持つ。"""

    def __init__(self, info: Info, bp, bm, groups, blk, v, sigma, eps, prefix="c"):
        self.info = info
        self.T = info.T
        self.bp, self.bm = bp, bm
        self.groups = [list(g) for g in groups]
        self.cls = classes_from_groups(bp, bm, groups)
        self.blk, self.v = dict(blk), dict(v)
        self.sigma = {k: int(x) for k, x in sigma.items()}   # key "+1"
        self.eps = {k: int(x) for k, x in eps.items()}
        self.prefix = prefix
        for d in "+-":
            for q in info.Qd[d]:
                b = self.blk[q]
                if not 1 <= b <= (bp if d == "+" else bm):
                    raise SystemExit(f"blk({q}) out of range")
                key = f"{d}{b}"
                if self.eps[key] * (self.v[q] - self.sigma[key]) < 0:
                    raise SystemExit(f"v({q}) on the wrong side of sigma_{key}")
            vals = [(self.blk[q], self.v[q]) for q in info.Qd[d]]
            if len(set(vals)) != len(vals):
                raise SystemExit(f"v not injective within a block ({d})")
        self._build()

    def C(self, i, s):
        return f"{self.prefix}{i}_{s}"

    def is_counter(self, sym):
        return isinstance(sym, str) and sym.startswith(self.prefix) and "_" in sym and \
            sym[len(self.prefix):].split("_", 1)[0].lstrip("-").isdigit()

    def split_counter(self, sym):
        i, s = sym[len(self.prefix):].split("_", 1)
        return int(i), s

    def role_state(self, kind, d, b):
        return self.cls[(kind, d, b)]

    def H(self, q):
        d = self.info.dir[q]
        return self.cls[("h", d, self.blk[q])]

    def _build(self):
        nf, T, v = self.info, self.T, self.v
        R = []
        for (p, s, t, d, q) in T.quints:
            src = self.H(p)
            if q in T.pseudo:
                R.append(((src, self.C(v[p], s), t, d, q), f"R1 {p},{s}"))
            else:
                R.append(((src, self.C(v[p], s), self.C(v[q], t), d, self.H(q)), f"R1 {p},{s}"))
        for d in "+-":
            e = OPP[d]
            for b in range(1, (self.bp if d == "+" else self.bm) + 1):
                key = f"{d}{b}"
                sg, ep = self.sigma[key], self.eps[key]
                Hc, Oc, Dc = (self.cls[(k, d, b)] for k in "hod")
                for q in nf.Qd[d]:
                    if self.blk[q] != b:
                        continue
                    for s2 in sorted(nf.reads[q]):
                        R.append(((Hc, s2, self.C(sg, s2), e, Oc), f"R2 ->{q}"))
                        for j in between(sg, v[q], closed_b=False):
                            R.append(((Dc, self.C(j, s2), self.C(j + ep, s2), e, Oc), f"R5 ->{q}"))
                    for t in sorted(nf.W[q]):
                        for i in between(sg, v[q]):
                            if i == sg:
                                R.append(((Oc, self.C(sg, t), t, d, Hc), f"R4 ->{q}"))
                            else:
                                R.append(((Oc, self.C(i, t), self.C(i - ep, t), d, Dc), f"R3 ->{q}"))
        seen = {}
        for rule, why in R:
            seen.setdefault(rule, why)
        self.tagged = {r: (None, w) for r, w in seen.items()}
        self.quints = list(seen)
        syms = set(T.symbols)
        for (p, s, t, d, q) in self.quints:
            syms.add(s)
            syms.add(t)
        cnt = sorted((x for x in syms if self.is_counter(x)), key=lambda x: (self.split_counter(x)[0], x))
        self.symbols = list(T.symbols) + cnt
        self.nctr = max(abs(self.v[q] - self.sigma[f"{self.info.dir[q]}{self.blk[q]}"]) for q in T.states) + 1
        used = set()
        for (p, s, t, d, q) in self.quints:
            used.add(p)
            if q not in T.pseudo:
                used.add(q)
        self.states = [c for c in dict.fromkeys(self.cls.values()) if c in used]
        self.k = len(self.states)

    conflicts = kstate5.Gen.conflicts

    def cost_k4(self, q, d):
        if q in self.T.pseudo:
            return 1
        return 3 + 2 * abs(self.v[q] - self.sigma[f"{self.info.dir[q]}{self.blk[q]}"])

    def encode_state(self, p):
        return self.H(p)

    def encode_cell(self, p, s):
        return self.C(self.v[p], s)

    def decode_state(self, hstate, counter):
        if not self.is_counter(counter):
            return None
        i, s = self.split_counter(counter)
        for q in self.T.states:
            if self.H(q) == hstate and self.v[q] == i:
                return q
        return None

    encode_conf = kstate.Construction.encode_conf
    decode_tape = kstate.Construction.decode_tape
    decode_conf = kstate.Construction.decode_conf
    step = kstate.Construction.step

    def title(self):
        return (f"kstate_blocks blocks={self.bp},{self.bm} groups={';'.join('&'.join(g) for g in self.groups) or '-'}"
                f" from {self.T.name}: {len(self.T.states)} states {len(self.T.symbols)} symbols"
                f" -> {self.k} states {len(self.symbols)} symbols")

    def emit(self, out):
        T = self.T
        maxstep = T.maxstep * (3 + 2 * max(1, self.nctr)) + 10
        L = [f"title('{self.title()}').",
             "% 生成: tools/kstate_blocks.py（docs/22）。blk=" + json.dumps(self.blk, ensure_ascii=False)
             + " v=" + json.dumps(self.v, ensure_ascii=False) + f" sigma={self.sigma} eps={self.eps}",
             f"initial_state({self.encode_state(T.initial_state)}).",
             "final_states([]).",
             f"states([{','.join(self.states)}]).",
             f"symbols([{','.join(self.symbols)}]).",
             f"blank({T.blank}).",
             f"maxstep({maxstep}).",
             ]
        delta = {(p, s): (t, d, q) for (p, s, t, d, q) in self.quints}
        for (state, pos, tape, exp_steps, exp_out) in T.cases:
            st, ps, tp = self.encode_conf(state, pos, tape)
            steps, final, why = kstate.run(delta, T.blank, (st, ps, tp), maxstep)
            L.append(f"initial_conf([{st},{ps},[{','.join(tp)}]]).")
            if why == "maxstep reached":
                L.append(f"%% null (maxstep {steps} reached; T' does not halt within maxstep)")
            else:
                L.append(f"%% {steps} {''.join(self.decode_tape(final)).rstrip(T.blank)}")
        for (p, s, t, d, q) in self.quints:
            L.append(f"[{p},{s},{t},{d},{q}].")
        out.write("\n".join(L) + "\n")


def symbol_count(info, blk, v, sigma):
    """Gen を作らずに記号数を数える（最適化の検算用）。"""
    S = set()
    for d in "+-":
        for q in info.Qd[d]:
            for i in between(sigma[f"{d}{blk[q]}"], v[q]):
                for x in info.need[q]:
                    S.add((i, x))
    return len(info.T.symbols) + len(S)


# ---------------------------------------------------------------- 最適化（CP-SAT）
def optimize(info, bp, bm, groups, V=None, slack=2, time_limit=600.0, workers=8, eps_fixed=None, hint=None,
             log=False, cutoff=None):
    """記号数を最小にするブロックの割当て・計数値・番兵・向きを CP-SAT で求める（kstate5.optimize の一般化）。

    ε_β も変数（eps_fixed={"+1": 1, ...} で固定もできる）。計数値は 1..V（既定 V = ⌈m+/b+⌉ + ⌈m-/b-⌉ + slack）。
    規則の粒度のモデル: 潜在的な規則を (類, 読む記号) と (類, 書く記号) で束ね、
      決定性: 同じ (類, 読む記号) の規則で動作 (書く記号, 向き, 次の類) が異なるものは 1 つまで
      可逆性: 同じ (次の類, 書く記号) に入る規則で (類, 読む記号) が異なるものは 1 つまで
    完全に同じ規則は同じ鍵になるので 1 本と数える。
    R1 の読みは鍵 ("R1",) にまとめる（R1 と同じ規則が他の役割から出る場合も衝突として扱う。保守側）。
    素の記号を読むのは H だけで H 同士は併合しないので、素の記号の読みは衝突しない。素の記号を書いて
    H_β に入るのは O_β の R4 だけ（t ごとに 1 本）なので、素の記号の書き込みも衝突しない。
    値の軸の反転（i → V+1-i、全ブロックの ε を反転）で解は解に移るので、ε_{+1} = +1 に固定する。
    cutoff を与えると「記号数 < cutoff」を制約に加える（INFEASIBLE = この分割では cutoff 未満が無い、の証明）。
    返り値: dict(status, obj, bound, blk, v, sigma, eps, ...)。"""
    from ortools.sat.python import cp_model
    cls = classes_from_groups(bp, bm, groups)
    Qd = info.Qd
    nb = {"+": bp, "-": bm}
    if V is None:
        V = -(-len(Qd["+"]) // bp) + -(-len(Qd["-"]) // bm) + slack
    vals = list(range(1, V + 1))
    syms = list(info.T.symbols)
    M = cp_model.CpModel()
    blocks = [(d, b) for d in "+-" for b in range(1, nb[d] + 1)]
    x = {}
    for d in "+-":
        for q in Qd[d]:
            for b in range(1, nb[d] + 1):
                for i in vals:
                    x[q, b, i] = M.NewBoolVar("")
            M.AddExactlyOne(x[q, b, i] for b in range(1, nb[d] + 1) for i in vals)
        for b in range(1, nb[d] + 1):
            for i in vals:
                M.AddAtMostOne(x[q, b, i] for q in Qd[d])
    sig, E = {}, {}
    for (d, b) in blocks:
        for i in vals:
            sig[d, b, i] = M.NewBoolVar("")
        M.AddExactlyOne(sig[d, b, i] for i in vals)
        E[d, b] = M.NewBoolVar("")          # 1: ε = +1
        key = f"{d}{b}"
        if eps_fixed and key in eps_fixed:
            M.Add(E[d, b] == (1 if eps_fixed[key] == 1 else 0))
        elif not eps_fixed and key == "+1":
            M.Add(E[d, b] == 1)
        for q in Qd[d]:
            for i in vals:
                # ε=+1 なら v ≥ σ、ε=-1 なら v ≤ σ
                M.Add(x[q, b, i] + sum(sig[d, b, c] for c in vals if c > i) + E[d, b] <= 2)
                M.Add(x[q, b, i] + sum(sig[d, b, c] for c in vals if c < i) + (1 - E[d, b]) <= 2)
    M.AddBoolOr([x[k] for k in x if k[2] == 1] + [sig[d, b, 1] for (d, b) in blocks])   # 平行移動の対称性
    # ブロックの所属
    y = {}
    for d in "+-":
        for q in Qd[d]:
            for b in range(1, nb[d] + 1):
                y[q, b] = sum(x[q, b, i] for i in vals)
    # 区間: inn = i が σ と v(q) の間（両端含む）、inS = 同じで v(q) を含まない
    inn, inS = {}, {}
    for d in "+-":
        for q in Qd[d]:
            for b in range(1, nb[d] + 1):
                for i in vals:
                    ge = sum(x[q, b, a] for a in vals if a >= i)
                    le = sum(x[q, b, a] for a in vals if a <= i)
                    gt = sum(x[q, b, a] for a in vals if a > i)
                    lt = sum(x[q, b, a] for a in vals if a < i)
                    sle = sum(sig[d, b, c] for c in vals if c <= i)
                    sge = sum(sig[d, b, c] for c in vals if c >= i)
                    a1 = M.NewBoolVar("")
                    M.Add(ge + sle - 1 <= a1)
                    M.Add(le + sge - 1 <= a1)
                    inn[q, b, i] = a1
                    a2 = M.NewBoolVar("")
                    M.Add(gt + sle - 1 <= a2)
                    M.Add(lt + sge - 1 <= a2)
                    inS[q, b, i] = a2
    Wc, Rc, Rh, RB = {}, {}, {}, {}
    for (d, b) in blocks:
        for s in syms:
            rb = M.NewBoolVar("")
            for q in Qd[d]:
                if s in info.reads[q]:
                    M.Add(y[q, b] <= rb)
            RB[d, b, s] = rb
        for i in vals:
            for s in syms:
                for store, src, sets in ((Wc, inn, info.W), (Rc, inn, info.reads), (Rh, inS, info.reads)):
                    bb = M.NewBoolVar("")
                    for q in Qd[d]:
                        if s in sets[q]:
                            M.AddImplication(src[q, b, i], bb)
                    store[d, b, i, s] = bb
    by_read = defaultdict(lambda: defaultdict(list))
    by_write = defaultdict(lambda: defaultdict(list))
    for (d, b) in blocks:
        e = OPP[d]
        Hc, Oc, Dc = (cls[(k, d, b)] for k in "hod")
        for i in vals:
            for s in syms:
                sr = sum(x[q, b, i] for q in Qd[d] if s in info.reads[q])
                sw = sum(x[q, b, i] for q in Qd[d] if s in info.W[q])
                by_read[Hc, ("c", i, s)][("R1",)].append(sr)
                by_write[Hc, ("c", i, s)][("R1", i, s)].append(sw)
                # R2
                r2 = M.NewBoolVar("")
                M.Add(RB[d, b, s] + sig[d, b, i] - 1 <= r2)
                by_write[Oc, ("c", i, s)][(Hc, ("p", s))].append(r2)
                # R3 / R4
                p3 = M.NewBoolVar("")
                M.Add(Wc[d, b, i, s] - sig[d, b, i] <= p3)
                p4 = M.NewBoolVar("")
                M.Add(Wc[d, b, i, s] + sig[d, b, i] - 1 <= p4)
                by_read[Oc, ("c", i, s)][(("p", s), d, Hc)].append(p4)
                for ep, ev in ((1, E[d, b]), (-1, 1 - E[d, b])):
                    p3e = M.NewBoolVar("")
                    M.Add(p3 + ev - 1 <= p3e)
                    by_read[Oc, ("c", i, s)][(("c", i - ep, s), d, Dc)].append(p3e)
                    if i - ep in vals:
                        by_write[Dc, ("c", i - ep, s)][(Oc, ("c", i, s))].append(p3e)
                    else:
                        M.Add(p3e == 0)
                    # R5
                    r5 = M.NewBoolVar("")
                    M.Add(Rh[d, b, i, s] + ev - 1 <= r5)
                    by_read[Dc, ("c", i, s)][(("c", i + ep, s), e, Oc)].append(r5)
                    if i + ep in vals:
                        by_write[Oc, ("c", i + ep, s)][(Dc, ("c", i, s))].append(r5)
                    else:
                        M.Add(r5 == 0)

    def at_most_one_group(groups_):
        if len(groups_) < 2:
            return
        inds = []
        for key, exprs in groups_.items():
            bv = M.NewBoolVar("")
            for ex in exprs:
                M.Add(ex <= bv)
            inds.append(bv)
        M.Add(sum(inds) <= 1)

    for g in by_read.values():
        at_most_one_group(g)
    for g in by_write.values():
        at_most_one_group(g)
    U = []
    for i in vals:
        for s in syms:
            u = M.NewBoolVar("")
            for (d, b) in blocks:
                M.AddImplication(Wc[d, b, i, s], u)
                M.AddImplication(Rc[d, b, i, s], u)
            U.append(u)
    M.Minimize(sum(U))
    if cutoff is not None:
        M.Add(sum(U) + len(syms) <= cutoff - 1)
    if hint:
        for (q, b, i), var in x.items():
            M.AddHint(var, 1 if (hint["blk"].get(q) == b and hint["v"].get(q) == i) else 0)
    S = cp_model.CpSolver()
    S.parameters.max_time_in_seconds = time_limit
    S.parameters.num_workers = workers
    S.parameters.log_search_progress = log
    st = S.Solve(M)
    res = {"machine": info.T.name, "blocks": [bp, bm], "groups": [list(g) for g in groups],
           "status": S.StatusName(st), "V": V, "wall": round(S.WallTime(), 1), "cutoff": cutoff}
    if st in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        blk, v = {}, {}
        for (q, b, i), var in x.items():
            if S.Value(var):
                blk[q], v[q] = b, i
        res.update(obj=int(round(S.ObjectiveValue())) + len(syms),
                   bound=int(round(S.BestObjectiveBound())) + len(syms),
                   blk=blk, v=v,
                   sigma={f"{d}{b}": next(i for i in vals if S.Value(sig[d, b, i])) for (d, b) in blocks},
                   eps={f"{d}{b}": (1 if S.Value(E[d, b]) else -1) for (d, b) in blocks})
    elif st == cp_model.UNKNOWN:
        res["bound"] = int(round(S.BestObjectiveBound())) + len(syms)
    return res


def pure_opt(info, bp, bm, time_limit=300.0, workers=8):
    """併合なし（pure）の厳密最適。どの分割の最適値もこれ以上（併合は制約を足すだけで、記号の集合は
    (blk, v, σ) だけで決まる）なので、同じブロック数の全分割に対する下界になる。

    併合が無ければ衝突は無く、記号数は n + Σ_x |∪_β [σ_β, 最も遠い v(q)（q ∈ β、x ∈ need(q)）]|。
    番兵をすべて同じ値・同じ向きにそろえると各 x の和集合は最長の区間 1 本になり、これは下から一致するので最適。
    よって「段」lvl(q) ≥ 0（同じ方向・同じ段に b_d 個まで）を選び n + Σ_x (1 + max{lvl(q) : x ∈ need(q)}) を最小化する。"""
    from ortools.sat.python import cp_model
    nb = {"+": bp, "-": bm}
    Qd = info.Qd
    L = max(-(-len(Qd[d]) // nb[d]) for d in "+-")
    M = cp_model.CpModel()
    x = {}
    for d in "+-":
        for q in Qd[d]:
            for lv in range(L):
                x[q, lv] = M.NewBoolVar("")
            M.AddExactlyOne(x[q, lv] for lv in range(L))
        for lv in range(L):
            M.Add(sum(x[q, lv] for q in Qd[d]) <= nb[d])
    X = sorted(set().union(*info.need.values()))
    mx = {}
    for s in X:
        mx[s] = M.NewIntVar(0, L - 1, "")
        for q in info.T.states:
            if s in info.need[q]:
                for lv in range(L):
                    M.Add(mx[s] >= lv).OnlyEnforceIf(x[q, lv])
    M.Minimize(sum(mx.values()))
    S = cp_model.CpSolver()
    S.parameters.max_time_in_seconds = time_limit
    S.parameters.num_workers = workers
    st = S.Solve(M)
    res = {"machine": info.T.name, "blocks": [bp, bm], "groups": [], "status": S.StatusName(st),
           "wall": round(S.WallTime(), 1)}
    if st in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        base = len(info.T.symbols) + len(X)
        res["obj"] = base + int(round(S.ObjectiveValue()))
        res["bound"] = base + int(round(S.BestObjectiveBound()))
        blk, v = {}, {}
        for d in "+-":
            used = defaultdict(int)
            for q in Qd[d]:
                lv = next(i for i in range(L) if S.Value(x[q, i]))
                used[lv] += 1
                blk[q], v[q] = used[lv], lv + 1
        res.update(blk=blk, v=v, sigma={f"{d}{b}": 1 for d in "+-" for b in range(1, nb[d] + 1)},
                   eps={f"{d}{b}": 1 for d in "+-" for b in range(1, nb[d] + 1)})
    return res


# ---------------------------------------------------------------- 検査
def verify(info, g):
    return kstate5.verify(info, g)


def local_check(info, g):
    return kstate5.local_check(info, g)


def gen_of(info, r):
    return Gen(info, r["blocks"][0], r["blocks"][1], r["groups"], r["blk"], r["v"], r["sigma"], r["eps"])


def machine_path(name):
    name = name.replace(".txt", "")
    return f"{HERE}/../data/urtm/{name}.txt"


def cmd_opt(a):
    info = Info(machine_path(a.input))
    bp, bm = (int(t) for t in a.blocks.split(","))
    groups = spec_groups(a.spec, bp, bm)
    r = optimize(info, bp, bm, groups, V=a.V, slack=a.slack, time_limit=a.time, workers=a.workers, log=a.log)
    if "v" in r:
        g = gen_of(info, r)
        ok, lines = verify(info, g)
        r.update(built_symbols=len(g.symbols), states=g.k, rules=len(g.quints), verify_ok=ok,
                 local=local_check(info, g)[:2])
    print(json.dumps(r, ensure_ascii=False))
    if a.json:
        json.dump(r, open(a.json, "w"), ensure_ascii=False, indent=1)
    return True


def spec_groups(spec, bp, bm):
    if spec in (None, "", "pure"):
        return []
    if spec == "thmB":
        return thmB_groups(bp, bm)
    return [g.split("&") for g in spec.split(";") if g]


def cmd_build(a):
    r = json.load(open(a.json))
    info = Info(machine_path(r["machine"]))
    g = gen_of(info, r)
    ok, lines = verify(info, g)
    lok, n, why = local_check(info, g)
    cnt = symbol_count(info, g.blk, g.v, g.sigma)
    print(f"{info.T.name} blocks={g.bp},{g.bm} groups={g.groups}: k={g.k} n'={len(g.symbols)} "
          f"|delta'|={len(g.quints)} (symbol_count={cnt}) conflicts={len(g.conflicts())} local={lok} {n} {why or ''}")
    print("\n".join(lines))
    if a.output:
        with open(a.output, "w") as f:
            g.emit(f)
    return ok and lok and not g.conflicts()


def cmd_mutate(a):
    """局所全数検査の検出力（kstate5 mutate と同じ）: 規則を 1 本消す／書く記号を替える変異を全部。"""
    r = json.load(open(a.json))
    info = Info(machine_path(r["machine"]))
    g = gen_of(info, r)
    base_ok = local_check(info, g)[0]
    killed = total = 0
    syms = g.symbols
    for k, rule in enumerate(g.quints):
        p, s, t, d, q = rule
        alt = syms[(syms.index(t) + 1) % len(syms)] if t in syms else t
        for var in (None, (p, s, alt, d, q)):
            g2 = gen_of(info, r)
            g2.quints = g.quints[:k] + ([var] if var else []) + g.quints[k + 1:]
            total += 1
            killed += not local_check(info, g2)[0]
    print(f"{info.T.name} {r['blocks']} {r['groups']}: base local_check={base_ok}; mutants killed {killed}/{total}")
    return base_ok and killed == total


# ---------------------------------------------------------------- 分割の列挙
def canon(bp, bm, groups):
    """ブロック番号の置換で同じになる分割を 1 つにまとめる鍵。"""
    best = None
    for pp in itertools.permutations(range(1, bp + 1)):
        for pm in itertools.permutations(range(1, bm + 1)):
            mp = {"+": dict(zip(range(1, bp + 1), pp)), "-": dict(zip(range(1, bm + 1), pm))}
            gs = []
            for g in groups:
                rs = sorted(f"{r[0].upper()}{r[1]}{mp[r[1]][r[2]]}" for r in (untok(t) for t in g))
                gs.append(tuple(rs))
            key = tuple(sorted(gs))
            if best is None or key < best:
                best = key
    return best


def enum_partitions(bp, bm, nmerge, maxclass=2):
    """役割を併合する分割を列挙する（入る向きが同じ・H を 2 つ含まない・同じブロックの H と D を含まない、
    類の大きさは maxclass まで）。併合の数（= 役割数 - 類の数）が nmerge のもの。ブロック置換で重複を除く。"""
    roles = roles_of(bp, bm)
    side = {"L": [r for r in roles if entry(r) == "-"], "R": [r for r in roles if entry(r) == "+"]}

    def ok_class(c):
        if sum(r[0] == "h" for r in c) > 1:
            return False
        hs = [r for r in c if r[0] == "h"]
        for h in hs:
            if any(r[0] == "d" and r[1] == h[1] and r[2] == h[2] for r in c):
                return False
        return True

    def set_partitions(items):
        if not items:
            yield []
            return
        first, rest = items[0], items[1:]
        for p in set_partitions(rest):
            yield [[first]] + p
            for k in range(len(p)):
                if len(p[k]) < maxclass:
                    c = p[k] + [first]
                    if ok_class(c):
                        yield p[:k] + [c] + p[k + 1:]

    L = [(p, len(side["L"]) - len(p)) for p in set_partitions(side["L"])]
    R = [(p, len(side["R"]) - len(p)) for p in set_partitions(side["R"])]
    out = {}
    for pl, ml in L:
        for pr, mr in R:
            if ml + mr != nmerge:
                continue
            groups = [[tok(r) for r in c] for c in pl + pr if len(c) > 1]
            key = canon(bp, bm, groups)
            out.setdefault(key, groups)
    return list(out.values())


MACHINES = kstate5.MACHINES


def cmd_sweep(a):
    """指定した (b+,b-)・分割の族を 6 台で解く。結果は a.out/<tag>.json。"""
    os.makedirs(a.out, exist_ok=True)
    jobs = json.load(open(a.jobs)) if a.jobs else None
    for job in jobs:
        mname, (bp, bm), groups = job["machine"], job["blocks"], job["groups"]
        tag = job.get("tag") or f"{mname}.b{bp}{bm}." + (";".join("&".join(g) for g in groups) or "pure")
        tag = tag.replace("+", "p").replace("-", "m").replace("&", "").replace(";", "_")
        path = f"{a.out}/{tag}.json"
        if os.path.exists(path) and not a.force:
            r = json.load(open(path))
        else:
            info = Info(machine_path(mname))
            r = optimize(info, bp, bm, groups, V=job.get("V"), slack=a.slack, time_limit=job.get("time", a.time),
                         workers=a.workers)
            if "v" in r:
                g = gen_of(info, r)
                ok, lines = verify(info, g)
                r.update(built_symbols=len(g.symbols), states=g.k, rules=len(g.quints), verify_ok=ok,
                         verify=lines, local=list(local_check(info, g)[:2]))
            r["tag"] = tag
            json.dump(r, open(path, "w"), ensure_ascii=False, indent=1)
        print(f"{tag}: {r['status']} obj={r.get('obj')} bound={r.get('bound')} k={r.get('states')} "
              f"verify={r.get('verify_ok')} local={r.get('local')} wall={r.get('wall')}s", flush=True)
    return True


def thmB_like(groups):
    """定理 B 型（同じ番号のブロックの O+&D-・D+&O-）の併合の数。列挙の順番付けに使う。"""
    n = 0
    for g in groups:
        rs = sorted(untok(t) for t in g)
        if len(rs) == 2 and rs[0][2] == rs[1][2] and {(r[0], r[1]) for r in rs} in ({("o", "+"), ("d", "-")},
                                                                                    {("d", "+"), ("o", "-")}):
            n += 1
    return n


def partial_thmB(bp, bm, nm):
    full = thmB_groups(bp, bm)
    out = {}
    for sub in itertools.combinations(full, nm):
        out.setdefault(canon(bp, bm, list(sub)), [list(g) for g in sub])
    return list(out.values())


SMALL = [(1, 1), (2, 1), (1, 2), (2, 2), (3, 1), (1, 3)]      # 全分割を列挙するブロック数
MID = [(3, 2), (2, 3)]                                        # k ≤ 5 では全分割も列挙する
LARGE = [(3, 2), (2, 3), (3, 3)]                              # 定理 B 型の併合（その部分集合）だけ


def maxclass(k):
    """列挙する類の大きさの上限: k ≤ 6 は無制限（= 18）、k ≥ 7 は 2（併合 1 対ずつ）。"""
    return 18 if k <= 6 else 2


def families(k):
    """状態数 k（名目）の (b+, b-, 併合の列, 族の名前)。"""
    out = []
    for bp, bm in SMALL + (MID if k <= 5 else []):
        nm = 3 * (bp + bm) - k
        if nm < 0:
            continue
        mc = maxclass(k)
        for g in enum_partitions(bp, bm, nm, mc):
            out.append((bp, bm, g, f"all(class<={mc})"))
    for bp, bm in LARGE:
        nm = 3 * (bp + bm) - k
        if 0 <= nm <= 2 * min(bp, bm):
            for g in partial_thmB(bp, bm, nm):
                out.append((bp, bm, g, "thmB-subsets"))
    return out


def cmd_search(a):
    """元機械 1 台について、k ごとに族の全分割を下界つきで解く（exact の判定つき）。"""
    info = Info(machine_path(a.machine))
    lbs = {}
    log = open(a.log, "a")
    summary = {}
    for k in range(a.kmin, a.kmax + 1):
        fam = families(k)
        cfgs = sorted({(bp, bm) for bp, bm, _, _ in fam})
        for c in cfgs:
            if c not in lbs:
                lbs[c] = pure_opt(info, *c, time_limit=60, workers=a.workers)["obj"]
        fam.sort(key=lambda f: (lbs[(f[0], f[1])], -thmB_like(f[2]), len(f[2])))
        seed = dict(tuple(int(t) for t in kv.split(":")) for kv in a.inc_map.split(",")) if a.inc_map else {}
        inc, best, exact, nsolve, npr = seed.get(k, a.inc), None, True, 0, 0
        done_cfg = set()
        t0 = time.time()
        for bp, bm, groups, fname in fam:
            lb = lbs[(bp, bm)]
            if (inc is not None and lb >= inc) or (bp, bm) in done_cfg:
                npr += 1
                continue
            r = optimize(info, bp, bm, groups, slack=a.slack, time_limit=a.time, workers=a.workers, cutoff=inc)
            nsolve += 1
            rec = {"k": k, "blocks": [bp, bm], "groups": groups, "family": fname, "lb": lb,
                   "status": r["status"], "obj": r.get("obj"), "bound": r.get("bound"), "cutoff": inc,
                   "wall": r["wall"]}
            if "v" in r:
                g = gen_of(info, r)
                rec["states"] = g.k
                if inc is None or r["obj"] < inc:
                    inc, best = r["obj"], r
                    best["family"] = fname
                if r["obj"] == lb:
                    done_cfg.add((bp, bm))
            if r["status"] not in ("OPTIMAL", "INFEASIBLE"):
                exact = False
            log.write(json.dumps(rec, ensure_ascii=False) + "\n")
            log.flush()
        summary[k] = {"best": inc, "exact": exact, "solved": nsolve, "pruned": npr, "lbs": {f"{c[0]},{c[1]}": v for c, v in lbs.items()},
                      "sol": best, "wall": round(time.time() - t0, 1)}
        print(f"{info.T.name} k={k}: best={inc} exact={exact} solved={nsolve} pruned={npr} "
              f"cfg={best and best['blocks']} groups={best and best['groups']} wall={summary[k]['wall']}s", flush=True)
        json.dump(summary, open(a.out, "w"), ensure_ascii=False, indent=1)
    return True


def cmd_summary(a):
    """解の JSON（opt/sweep/search の出力）を作り直して検査し、状態数ごとの表を出す。"""
    rows = []
    for path in sorted(a.sols):
        r = json.load(open(path))
        if "v" not in r:
            continue
        info = Info(machine_path(r["machine"]))
        g = gen_of(info, r)
        ok, lines = verify(info, g)
        lok, n, _ = local_check(info, g)
        rows.append((g.k, len(g.symbols), r["machine"].replace(".txt", ""), r["blocks"],
                     ";".join("&".join(x) for x in r["groups"]) or "pure", r["status"], len(g.quints),
                     "ok" if ok else "NG", f"{'ok' if lok else 'NG'} {n}", not g.conflicts(), os.path.basename(path)))
    rows.sort()
    L = ["| 状態 | 記号 | 元機械 | ブロック | 併合 | 求解 | 規則 | 逐段 | 局所全数 | 衝突なし | 解 |",
         "|---:|---:|---|---|---|---|---:|---|---|---|---|"]
    for row in rows:
        L.append("| " + " | ".join(str(x) for x in row) + " |")
    text = "\n".join(L) + "\n"
    if a.out:
        open(a.out, "w").write(text)
    print(text)
    return all(r[7] == "ok" and r[8].startswith("ok") and r[9] for r in rows)


def main(argv):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    o = sub.add_parser("opt")
    o.add_argument("input")
    o.add_argument("--blocks", required=True)
    o.add_argument("--spec", default="thmB", help="pure / thmB / 'O+1&D-1;D+1&O-1'")
    o.add_argument("--V", type=int)
    o.add_argument("--slack", type=int, default=2)
    o.add_argument("--time", type=float, default=600.0)
    o.add_argument("--workers", type=int, default=8)
    o.add_argument("--json")
    o.add_argument("--log", action="store_true")
    o.set_defaults(fn=cmd_opt)
    b = sub.add_parser("build")
    b.add_argument("json")
    b.add_argument("-o", "--output")
    b.set_defaults(fn=cmd_build)
    u = sub.add_parser("mutate")
    u.add_argument("json")
    u.set_defaults(fn=cmd_mutate)
    s = sub.add_parser("sweep")
    s.add_argument("--out", required=True)
    s.add_argument("--jobs", required=True, help="JSON のジョブ列 [{machine, blocks, groups, V?, time?}]")
    s.add_argument("--slack", type=int, default=2)
    s.add_argument("--time", type=float, default=300.0)
    s.add_argument("--workers", type=int, default=8)
    s.add_argument("--force", action="store_true")
    s.set_defaults(fn=cmd_sweep)
    se = sub.add_parser("search")
    se.add_argument("machine")
    se.add_argument("--kmin", type=int, default=5)
    se.add_argument("--kmax", type=int, default=12)
    se.add_argument("--inc", type=int, help="初期の上界（この値未満だけを探す）")
    se.add_argument("--inc-map", help="k ごとの初期の上界 '4:46,5:46,...'（記録の閾値。これ未満だけを探す）")
    se.add_argument("--slack", type=int, default=2)
    se.add_argument("--time", type=float, default=60.0)
    se.add_argument("--workers", type=int, default=4)
    se.add_argument("--out", required=True)
    se.add_argument("--log", required=True)
    se.set_defaults(fn=cmd_search)
    sm = sub.add_parser("summary")
    sm.add_argument("sols", nargs="+")
    sm.add_argument("--out")
    sm.set_defaults(fn=cmd_summary)
    a = ap.parse_args(argv)
    return 0 if a.fn(a) is not False else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
