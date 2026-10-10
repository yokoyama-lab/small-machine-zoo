#!/usr/bin/env python3
"""k 桁（r = 2, 3）の記号削減の改良版（docs/23 §3.3）: fewsym2 の向き・先書き・経路の型を k 桁に一般化し、
局所探索で選ぶ（発見的。k = 2 では fewsym2 の CP-SAT の厳密値と突き合わせる）。

T の規則 ρ = [p, s, t, d, q]、向き e(p) から読む順に並べた桁 x_1..x_k（s）、y_1..y_k（t）。
  読み:  B(p, x_1..x_{i-1}) がセル i の x_i を読み、先書き v(p, x_1..x_i) を書き、f 側へ（i < k）。B(p) = [p^r]。
  T2:    B(p, x_1..x_{k-1}) が x_k を読み y_k を書き d へ。v(p, x_1..x_i) = y_i（i < k）のときだけ使える。
  T1:    x_k を読み y_k を書き e 側へ戻り、W(q, e(p), y_1..y_j, v_1..v_j) がセル j の v_j を読んで y_j を書く
         （j = k-1, …, 1）。最後に d へ。
  どちらも d へ動いた先から e(q) のセルまで S(q, 1..sh) で移る（通るセルの値が分かっていればその規則だけ）。
探索は T2 にする規則の集合 X。v は X の規則が通る枝で y に決まり、ほかは 0。表の決定性・可逆性で可否を判定する。

    python3 tools/fewsym3.py search urtm10-8 --restarts 20 --json results/fewsym/urtm10-8.x3.json
    python3 tools/fewsym3.py check results/fewsym/urtm10-8.x3.json
"""

import argparse
import json
import os
import random
import sys
from collections import defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import fewsym as F  # noqa: E402
import fewsym2 as G  # noqa: E402

OPP = {"+": "-", "-": "+"}


class ConvK:
    def __init__(self, T, r, k, code, e, t2set, vfree=None, tm=None):
        self.T, self.r, self.k = T, r, k
        self.tm = {int(i): int(x) for i, x in (tm or {}).items()}
        self.vfree = dict(vfree or {})
        self.code, self.e = code, dict(e)
        self.t2 = set(t2set)
        self.mode = "xk"
        self.problem = None
        self.costs = {}
        self._build()

    def ce(self, p):
        return 0 if self.e[p] == "L" else self.k - 1

    def order(self, p):
        return list(range(self.k)) if self.e[p] == "L" else list(range(self.k - 1, -1, -1))

    def tmpl(self, i):
        """規則 i の型 a: 書き戻さないで済む（先書きが正しい）桁の数。a = k-1 が T2、0 が T1（原典）。"""
        if i in self.t2:
            return self.k - 1
        return self.tm.get(i, 0)

    def _build(self):
        T, k, r = self.T, self.k, self.r
        v = {}
        for i, (p, s, t, d, q) in enumerate(T.rules):
            a = self.tmpl(i)
            o = self.order(p)
            xs = [self.code[s][j] for j in o]
            ys = [self.code[t][j] for j in o]
            for j in range(a):
                key = (p, tuple(xs[:j + 1]))
                if v.setdefault(key, ys[j]) != ys[j]:
                    self.problem = f"v conflict at {key}"
                    return
        self.v = v
        R, seen = [], set()

        def add(rl):
            if rl not in seen:
                seen.add(rl)
                R.append(rl)
        spath = defaultdict(lambda: defaultdict(set))
        shs = defaultdict(set)
        for i, (p, s, t, d, q) in enumerate(T.rules):
            a = self.tmpl(i)
            o = self.order(p)
            fwd = "+" if self.e[p] == "L" else "-"
            bwd = OPP[fwd]
            xs = [self.code[s][j] for j in o]
            ys = [self.code[t][j] for j in o]
            vs = [v.get((p, tuple(xs[:j + 1])), self.vfree.get((p, tuple(xs[:j + 1])), 0)) for j in range(k - 1)]
            for j in range(k - 1):
                st = ("r", p) if j == 0 else ("B", p, *xs[:j])
                add((st, xs[j], vs[j], fwd, ("B", p, *xs[:j + 1])))
            last = ("r", p) if k == 1 else ("B", p, *xs[:k - 1])
            cells = {o[j]: ys[j] for j in range(k)}
            if a == k - 1:
                head = (last, xs[k - 1], ys[k - 1], d)
                steps = k
            else:
                # 書き戻し: セル o[i]（i = k-2 .. a）の W(q, e, a, y_a..y_i, v_a..v_i) が v_i を読み y_i を書く
                def W(i):
                    return ("W", q, self.e[p], a, *ys[a:i + 1], "v", *vs[a:i + 1])
                add((last, xs[k - 1], ys[k - 1], bwd, W(k - 2)))
                for i2 in range(k - 2, a, -1):
                    add((W(i2), vs[i2], ys[i2], bwd, W(i2 - 1)))
                head = (W(a), vs[a], ys[a], d)
                steps = k + (k - 1 - a)
            land = o[a] + (1 if d == "+" else -1)
            tgt = (k if d == "+" else -k) + self.ce(q)
            sh = abs(tgt - land)
            shs[q].add(sh)
            self.costs[(p, s)] = steps + sh
            st, x, y, dd = head
            add((st, x, y, dd, ("S", q, 1) if sh else ("r", q)))
            pos = land
            for j in range(1, sh + 1):
                spath[q][j].add(cells.get(pos))
                pos += 1 if d == "+" else -1
        for q, lv in spath.items():
            if len(shs[q] - {0}) > 1:
                self.problem = f"state {q}: shift lengths {sorted(shs[q])}"
                return
            n = max(lv)
            for j in range(1, n + 1):
                vals = lv[j]
                if None in vals:
                    vals = set(range(r))
                nxt = ("S", q, j + 1) if j < n else ("r", q)
                for z in sorted(vals):
                    add((("S", q, j), z, z, T.hsd[q], nxt))
        self.rules = R

    states = G.ConvX.states
    nstates = G.ConvX.nstates
    breakdown = G.ConvX.breakdown
    check_table = F.Conv.check_table

    def enc(self, p, pos, tape):
        bits = []
        for s in tape:
            bits.extend(self.code[s])
        return (("r", p), self.k * pos + (self.ce(p) if p in self.e else 0), bits)

    def cost(self, p, s, d, q):
        return self.costs[(p, s)]

    def emit(self, f, title=None):
        T = self.T
        f.write(f"title('{title or f'{T.name} -> ({self.nstates()},{self.r}) by fewsym3.py (docs/23)'}').\n")
        f.write(f"% 生成: tools/fewsym3.py。k={self.k} code={json.dumps({s: ''.join(map(str, v)) for s, v in self.code.items()})}\n")
        f.write(f"% e={json.dumps(self.e)} t2={sorted(self.t2)}\n")
        init = T.initial or T.states[0]
        f.write(f"initial_state({G.sname(('r', init))}).\nfinal_states([]).\n")
        f.write(f"symbols([{','.join(str(x) for x in range(self.r))}]).\nblank(0).\n")
        f.write(f"maxstep({T.maxstep * (3 * self.k + 2) + 10}).\n")
        for (state, pos, tape, _, _) in T.cases:
            st, ps, bits = self.enc(state, pos, tape)
            f.write(f"initial_conf([{G.sname(st)},{ps},[{','.join(map(str, bits))}]]).\n")
        for (a, x, y, d, b) in self.rules:
            f.write(f"[{G.sname(a)},{x},{y},{d},{G.sname(b)}].\n")
        f.write("states([" + ",".join(sorted(G.sname(s) for s in self.states())) + "]).\n")


def score(cv):
    if cv.problem:
        return 10 ** 6
    errs = cv.check_table()
    return cv.nstates() + 1000 * len(errs)


def branches(T, k, code, e):
    out = set()
    for (p, s, t, d, q) in T.rules:
        o = list(range(k)) if e[p] == "L" else list(range(k - 1, -1, -1))
        xs = tuple(code[s][j] for j in o)
        for j in range(k - 1):
            out.add((p, xs[:j + 1]))
    return sorted(out, key=str)


def local_search(T, r, k, code, e, rng, iters=3000, init=None, initv=None):
    n = len(T.rules)
    br = branches(T, k, code, e)
    cur = set(init or ())
    curv = dict(initv or {})
    cs = score(ConvK(T, r, k, code, e, cur, curv))
    best = (cs, set(cur), dict(curv))
    for it in range(iters):
        nxt = set(cur)
        nv = dict(curv)
        i = rng.randrange(n)
        if br and rng.random() < 0.3:
            b = rng.choice(br)
            nv[b] = rng.randrange(r)
        elif i in nxt:
            nxt.discard(i)
        else:
            nxt.add(i)
            # 同じ状態の他の規則も一緒に動かす（先書きが揃う）ことがある
            if rng.random() < 0.3:
                p = T.rules[i][0]
                for j, rl in enumerate(T.rules):
                    if rl[0] == p and rng.random() < 0.5:
                        nxt.add(j)
        sc = score(ConvK(T, r, k, code, e, nxt, nv))
        temp = max(0.05, 1.5 * (1 - it / iters))
        if sc <= cs or (sc < 10 ** 5 and rng.random() < pow(2.718, (cs - sc) / temp)):
            cur, cs, curv = nxt, sc, nv
            if sc < best[0]:
                best = (sc, set(nxt), dict(nv))
    return best


def solve_cp(T, r, k, code, e, time_limit=60.0, workers=8, tmpls=None, perturb=None, slack=0):
    """向き e と符号を固定し、v と経路の型 a を CP-SAT で選ぶ（この族の中で厳密）。
    返り値 (status, tm = {規則: a}, vfree, 目的値, 下界)。"""
    import itertools
    from ortools.sat.python import cp_model
    M = cp_model.CpModel()
    vals = list(range(r))
    tmpls = list(range(k)) if tmpls is None else tmpls
    Veq = {}

    def veq(key):
        if key not in Veq:
            bs = {x: M.NewBoolVar("") for x in vals}
            M.AddExactlyOne(bs.values())
            Veq[key] = bs
        return Veq[key]
    info = []
    for i, (p, s, t, d, q) in enumerate(T.rules):
        o = list(range(k)) if e[p] == "L" else list(range(k - 1, -1, -1))
        xs = [code[s][j] for j in o]
        ys = [code[t][j] for j in o]
        cq = 0 if e[q] == "L" else k - 1
        tgt = (k if d == "+" else -k) + cq
        cells = {o[j]: ys[j] for j in range(k)}
        br = [(p, tuple(xs[:j + 1])) for j in range(k - 1)]
        A = {}
        for a in tmpls:
            land = o[a] + (1 if d == "+" else -1)
            sh = abs(tgt - land)
            cr, pos = [], land
            for _ in range(sh):
                cr.append(cells.get(pos))
                pos += 1 if d == "+" else -1
            lit = M.NewBoolVar(f"a_{i}_{a}")
            for j in range(a):
                M.AddImplication(lit, veq(br[j])[ys[j]])
            A[a] = dict(lit=lit, sh=sh, cr=cr)
        M.AddExactlyOne([x["lit"] for x in A.values()])
        info.append(dict(i=i, q=q, e=e[p], ys=ys, br=br, A=A))
    # 移動の長さは q ごとに 1 種類（0 を除く）
    for q in T.states:
        rs = [it for it in info if it["q"] == q]
        lens = sorted({x["sh"] for it in rs for x in it["A"].values()} - {0})
        if len(lens) > 1:
            use = {L: M.NewBoolVar("") for L in lens}
            M.Add(sum(use.values()) <= 1)
            for it in rs:
                for x in it["A"].values():
                    if x["sh"]:
                        M.AddImplication(x["lit"], use[x["sh"]])
    # W の鍵 (q, e, a, y_a..y_i, v_a..v_i)、i = a..k-2
    W = {}
    topin = defaultdict(lambda: defaultdict(list))
    exits = defaultdict(list)       # q -> [(書く値, sh, リテラル)]
    for it in info:
        for a, x in it["A"].items():
            if a == k - 1:
                exits[it["q"]].append((it["ys"][k - 1], x["sh"], x["lit"]))
                continue
            for i in range(a, k - 1):
                for vt in itertools.product(vals, repeat=i - a + 1):
                    key = (it["q"], it["e"], a, tuple(it["ys"][a:i + 1]), vt)
                    if key not in W:
                        W[key] = (M.NewBoolVar(""), x["sh"])
                    lit = M.NewBoolVar("")
                    conds = [x["lit"]] + [veq(it["br"][a + jj])[vt[jj]] for jj in range(i - a + 1)]
                    M.AddBoolAnd(conds).OnlyEnforceIf(lit)
                    M.AddBoolOr([c.Not() for c in conds] + [lit])
                    M.AddImplication(lit, W[key][0])
                    if i == k - 2:
                        topin[key][it["ys"][k - 1]].append(lit)
    # 最上段の W に入る δt（y_k を書く）は相異なる値（a > 0 では y_1..y_a が違うだけの t が衝突しうる）
    for key, d in topin.items():
        for b, lits in d.items():
            if len(lits) > 1:
                M.Add(sum(lits) <= 1)
    # W_i に入る W_{i+1}（y_{i+1} を書く）は相異なる値
    byparent = defaultdict(lambda: defaultdict(list))
    for key, (u, sh) in W.items():
        q, ee, a, ys, vt = key
        if len(ys) >= 2:
            parent = (q, ee, a, ys[:-1], vt[:-1])
            byparent[parent][ys[-1]].append(u)
        else:
            exits[q].append((ys[0], sh, u))
    for parent, d in byparent.items():
        for b, us in d.items():
            if len(us) > 1:
                M.Add(sum(us) <= 1)
    obj = [u for (u, _) in W.values()]
    for q in sorted({it["q"] for it in info}, key=str):
        rs = [it for it in info if it["q"] == q]
        maxsh = max(x["sh"] for it in rs for x in it["A"].values())
        Sz = {(j, z): M.NewBoolVar("") for j in range(1, maxsh + 1) for z in vals}
        Sx = {j: M.NewBoolVar("") for j in range(1, maxsh + 1)}
        for (j, z), b in Sz.items():
            M.AddImplication(b, Sx[j])
        obj += list(Sx.values())
        ends = {L: M.NewBoolVar("") for L in range(1, maxsh + 1)}
        for it in rs:
            for x in it["A"].values():
                for j in range(1, x["sh"] + 1):
                    zs = vals if x["cr"][j - 1] is None else [x["cr"][j - 1]]
                    for z in zs:
                        M.AddImplication(x["lit"], Sz[(j, z)])
                if x["sh"]:
                    M.AddImplication(x["lit"], ends[x["sh"]])
        for b in vals:
            s1 = [lit for (y, sh, lit) in exits[q] if y == b and sh > 0]
            rr = [lit for (y, sh, lit) in exits[q] if y == b and sh == 0]
            if len(s1) > 1:
                M.Add(sum(s1) <= 1)
            for L in range(1, maxsh + 1):
                zb = M.NewBoolVar("")
                M.AddBoolAnd([ends[L], Sz[(L, b)]]).OnlyEnforceIf(zb)
                M.AddBoolOr([ends[L].Not(), Sz[(L, b)].Not(), zb])
                rr.append(zb)
            M.Add(sum(rr) <= 1)
    if perturb is None:
        M.Minimize(sum(obj))
    else:
        # 同じ最適値（slack > 0 なら最適値 + slack 以下）の解を乱択で選ぶ（併合の前処理の多様化）
        S0 = cp_model.CpSolver()
        S0.parameters.max_time_in_seconds = time_limit
        S0.parameters.num_workers = workers
        M.Minimize(sum(obj))
        st0 = S0.Solve(M)
        if st0 not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
            return S0.StatusName(st0), None, None, None, None
        M.Add(sum(obj) <= int(S0.ObjectiveValue()) + slack)
        rng = random.Random(perturb)
        lits = [b for bs in Veq.values() for b in bs.values()] + [x["lit"] for it in info for x in it["A"].values()]
        M.Minimize(sum(rng.randint(-5, 5) * b for b in lits))
    S = cp_model.CpSolver()
    S.parameters.max_time_in_seconds = time_limit
    S.parameters.num_workers = workers
    st = S.Solve(M)
    if st not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        return S.StatusName(st), None, None, None, None
    if perturb is not None:
        tm = {it["i"]: next(a for a, x in it["A"].items() if S.Value(x["lit"])) for it in info}
        vf = {key: next(x for x, b in bs.items() if S.Value(b)) for key, bs in Veq.items()}
        return S.StatusName(st), tm, vf, float(sum(S.Value(o) for o in obj)), None
    tm = {it["i"]: next(a for a, x in it["A"].items() if S.Value(x["lit"])) for it in info}
    vf = {key: next(x for x, b in bs.items() if S.Value(b)) for key, bs in Veq.items()}
    return S.StatusName(st), tm, vf, S.ObjectiveValue(), S.BestObjectiveBound()


def orient_of(T, name, rng=None):
    if name == "allL":
        return {q: "L" for q in T.states}
    if name == "allR":
        return {q: "R" for q in T.states}
    if name == "near":
        return G.near(T)
    return {q: rng.choice("LR") for q in T.states}


def cmd_search(a):
    T = F.load(a.input)
    r = a.radix
    k = a.k or F.digits_needed(len(T.symbols), r)
    rng = random.Random(a.seed)
    if a.code:
        codes = [{s: tuple(int(ch) for ch in c) for s, c in json.load(open(a.code))["code"].items()}]
    else:
        # Morita 構成で最良の符号と、既定の符号
        c1, code1, _, _ = F.opt_code(T, r, k, iters=4000, seed=a.seed)
        codes = [code1, F.default_code(T, r, k)]
    best = None
    for ci, code in enumerate(codes):
        for oname in a.orients.split(","):
            for rs in range(a.restarts):
                e = orient_of(T, oname, rng)
                sc, t2, vf = local_search(T, r, k, code, e, rng, iters=a.iters)
                # e の山登り（1 状態ずつ）
                for _ in range(a.eflips):
                    q = rng.choice(T.states)
                    e2 = dict(e)
                    e2[q] = "R" if e[q] == "L" else "L"
                    sc2, t22, vf2 = local_search(T, r, k, code, e2, rng, iters=a.iters // 4, init=t2, initv=vf)
                    if sc2 <= sc:
                        e, sc, t2, vf = e2, sc2, t22, vf2
                print(f"code#{ci} {oname} restart {rs}: {sc}", flush=True)
                if sc < 10 ** 3 and (best is None or sc < best[0]):
                    best = (sc, code, dict(e), sorted(t2), dict(vf))
    sc, code, e, t2, vf = best
    cv = ConvK(T, r, k, code, e, t2, vf)
    sol = {"machine": T.name, "radix": r, "k": k, "code": {s: "".join(map(str, c)) for s, c in code.items()},
           "e": e, "t2": t2, "vfree": [[p, list(xs), x] for (p, xs), x in sorted(vf.items(), key=str)], "states": cv.nstates(), "rules": len(cv.rules), "breakdown": cv.breakdown(),
           "search": f"local search (restarts {a.restarts}, iters {a.iters}, eflips {a.eflips}, seed {a.seed})"}
    print(json.dumps({x: sol[x] for x in ("machine", "radix", "k", "states", "rules", "breakdown")}))
    if a.json:
        os.makedirs(os.path.dirname(a.json) or ".", exist_ok=True)
        json.dump(sol, open(a.json, "w"), ensure_ascii=False, indent=1)
    return True


def _scan_one(args):
    name, r, k, code, oname, tlim = args
    T = F.load(name)
    e = orient_of(T, oname)
    st, tm, vf, obj, bd = solve_cp(T, r, k, code, e, time_limit=tlim, workers=1)
    if tm is None:
        return None
    cv = ConvK(T, r, k, code, e, [], vf, tm)
    if cv.problem or cv.check_table():
        return None
    return cv.nstates(), st, code, oname, tm, vf


def cmd_cpscan(a):
    """符号（空白 = 0^k を固定した全割り当て、または焼きなましの上位）× 向き で CP-SAT を回す。"""
    import itertools
    from multiprocessing import Pool
    T = F.load(a.input)
    r = a.radix
    k = a.k or F.digits_needed(len(T.symbols), r)
    words = [w for w in F.all_words(r, k) if any(w)]
    others = [x for x in T.symbols if x != T.blank]
    codes = [{T.blank: (0,) * k, **dict(zip(others, perm))} for perm in itertools.permutations(words, len(others))]
    if a.limit and len(codes) > a.limit:
        random.Random(a.seed).shuffle(codes)
        codes = codes[:a.limit]
    jobs = [(T.name, r, k, c, o, a.time) for c in codes for o in a.orients.split(",")]
    best = []
    with Pool(a.procs) as pool:
        for n, res in enumerate(pool.imap_unordered(_scan_one, jobs, chunksize=4)):
            if res is None:
                continue
            best.append(res)
            best.sort(key=lambda x: x[0])
            best = best[:a.keep]
            if n % 200 == 0:
                print(f"{n}/{len(jobs)} best so far {best[0][0]}", flush=True)
    ns, st, code, oname, tm, vf = best[0]
    cv = ConvK(T, r, k, code, orient_of(T, oname), [], vf, tm)
    sol = {"machine": T.name, "radix": r, "k": k, "code": {x: "".join(map(str, c)) for x, c in code.items()},
           "e": orient_of(T, oname), "orient": oname, "t2": [], "tm": {str(i): x for i, x in tm.items()},
           "vfree": [[p, list(xs), x] for (p, xs), x in sorted(vf.items(), key=str)],
           "states": cv.nstates(), "rules": len(cv.rules), "breakdown": cv.breakdown(), "cp_status": st,
           "search": f"CP-SAT per (code, orient); codes {len(codes)} of {'all' if not a.limit else 'sample'}; orients {a.orients}",
           "top": [[x[0], x[3], {s: ''.join(map(str, c)) for s, c in x[2].items()}] for x in best]}
    print(json.dumps({x: sol[x] for x in ("machine", "radix", "k", "states", "rules", "breakdown", "cp_status")}))
    if a.json:
        os.makedirs(os.path.dirname(a.json) or ".", exist_ok=True)
        json.dump(sol, open(a.json, "w"), ensure_ascii=False, indent=1)
    return True


def conv_of(sol):
    T = F.load(sol["machine"])
    code = {s: tuple(int(ch) for ch in c) for s, c in sol["code"].items()}
    vf = {(p, tuple(xs)): x for p, xs, x in sol.get("vfree", [])}
    return ConvK(T, sol["radix"], sol["k"], code, sol["e"], sol.get("t2", []), vf, sol.get("tm"))


def cmd_check(a):
    cv = conv_of(json.load(open(a.json)))
    ok, lines = F.check_all(cv, a.random)
    print(f"{cv.T.name} -> ({cv.nstates()},{cv.r}) rules={len(cv.rules)} breakdown={cv.breakdown()}")
    print("\n".join("  " + x for x in lines))
    return ok


def cmd_build(a):
    cv = conv_of(json.load(open(a.json)))
    print(f"{cv.T.name} -> ({cv.nstates()},{cv.r}) rules={len(cv.rules)}")
    if a.output:
        os.makedirs(os.path.dirname(a.output) or ".", exist_ok=True)
        with open(a.output, "w") as f:
            cv.emit(f)
    return True


def main(argv):
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("search")
    p.add_argument("input")
    p.add_argument("--radix", type=int, default=2)
    p.add_argument("-k", type=int, default=None)
    p.add_argument("--code")
    p.add_argument("--orients", default="allL,near")
    p.add_argument("--restarts", type=int, default=3)
    p.add_argument("--iters", type=int, default=3000)
    p.add_argument("--eflips", type=int, default=0)
    p.add_argument("--seed", type=int, default=1)
    p.add_argument("--json")
    p = sub.add_parser("cpscan")
    p.add_argument("input")
    p.add_argument("--radix", type=int, default=2)
    p.add_argument("-k", type=int, default=None)
    p.add_argument("--orients", default="allL,allR")
    p.add_argument("--time", type=float, default=20.0)
    p.add_argument("--procs", type=int, default=12)
    p.add_argument("--limit", type=int, default=0)
    p.add_argument("--keep", type=int, default=10)
    p.add_argument("--seed", type=int, default=1)
    p.add_argument("--json")
    p = sub.add_parser("check")
    p.add_argument("json")
    p.add_argument("--random", type=int, default=300)
    p = sub.add_parser("build")
    p.add_argument("json")
    p.add_argument("-o", "--output")
    a = ap.parse_args(argv)
    return {"search": cmd_search, "cpscan": cmd_cpscan, "check": cmd_check, "build": cmd_build}[a.cmd](a)


if __name__ == "__main__":
    sys.exit(0 if main(sys.argv[1:]) else 1)
