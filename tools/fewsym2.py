#!/usr/bin/env python3
"""2 ビット符号（k = 2）の記号削減の改良版（docs/23 §3）: 向き・先書き・経路の型を選ぶ。

Theorem 5.4（fewsym.py の morita）は T の 1 ステップを必ず「読む → 読む・書く → 戻って書く → 1 マス移る」の
4 ステップで模倣し、状態 q ごとに移動の状態 [q^s] を 1 つ置く。ここでは次の自由度を足す。

  * 向き e(p) ∈ {L, R}: 状態 [p^r] でヘッドが居るのはブロックの左端（L）か右端（R）か。読みは e(p) のセル
    （e セル）から反対端（f セル）へ。既定は「入ってくる側」（hsd(p) = + なら L、− なら R）。
  * 先書き v(p, x1): [p^r] が e セルの桁 x1 を読んだとき、そこへ書く値（原典は常に 0）。
  * 経路の型（T の規則 ρ = [p, s, t, d, q] ごと）。y1・y2 は t の e セル・f セルの桁（e = e(p)）。
      T1（原典の形）: [p^r] --x1/v--> B(p,x1) --x2/y2--> W(q, e(p), y1, v) --v/y1, d--> …
      T2（先書き）  : [p^r] --x1/v--> B(p,x1) --x2/y2, d--> …        （v(p, x1) = y1 のときだけ使える）
    「…」は d へ動いた先から q のセル e(q) まで、移動の状態 S(q,1), S(q,2), … で sh マス（0 なら直接 [q^r]）。
    S(q,i) は通過するセルに実際に来うる値についてだけ規則を持つ（x → x）。
  状態は [p^r]・B(p,x1)・W(q,e,y1,v)・S(q,i)。決定性は構成から自動で、可逆性は [q^r] と S(q,i) に入る規則の
  書く値が相異なることだけが条件になる（W は同じ (q, e, y1) の t が y2 で区別されるので自動）。

`opt` は符号（空白 = 00 固定の全数）× 向き（入ってくる側、または全部 L）ごとに、v と経路の型を CP-SAT で選び
状態数を最小化する（その族の中で厳密。OPTIMAL を表示する）。

    ~/.venvs/urtm/bin/python tools/fewsym2.py opt urtm24-4 --json results/fewsym/urtm24-4.x2.json
    python3 tools/fewsym2.py check results/fewsym/urtm24-4.x2.json --random 500
    python3 tools/fewsym2.py build results/fewsym/urtm24-4.x2.json -o out/fs/x.txt
"""

import argparse
import itertools
import json
import os
import random
import sys
from collections import defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import fewsym as F  # noqa: E402

OPP = {"+": "-", "-": "+"}


def near(T):
    return {q: ("L" if T.hsd.get(q, "+") == "+" else "R") for q in T.states}


class ConvX:
    def __init__(self, T, code, e, v, tmpl, r=2):
        """code: sym -> (b0, b1)（ブロックの左セル・右セルの桁）。e: state -> L/R。
        v: (p, x1) -> 0/1。tmpl: 規則の添字 -> 'T1'/'T2'。"""
        self.T, self.r, self.k = T, r, 2
        self.code, self.e, self.v, self.tmpl = code, dict(e), dict(v), dict(tmpl)
        self.mode = "x2"
        self.problem = None
        self.costs = {}
        self._build()

    def ce(self, p):
        return 0 if self.e[p] == "L" else 1

    def bits(self, p, s):
        """(e セルの桁, f セルの桁)。"""
        c = self.code[s]
        return (c[0], c[1]) if self.e[p] == "L" else (c[1], c[0])

    def _build(self):
        T = self.T
        R, seen = [], set()

        def add(rl):
            if rl not in seen:
                seen.add(rl)
                R.append(rl)
        spath = defaultdict(lambda: defaultdict(set))    # q -> i -> 通過する値（None = 未知）
        sh_of = defaultdict(set)
        for i, (p, s, t, d, q) in enumerate(T.rules):
            ce, cf = self.ce(p), 1 - self.ce(p)
            fwd = "+" if ce == 0 else "-"
            x1, x2 = self.bits(p, s)
            y1, y2 = self.bits(p, t)
            vv = self.v.get((p, x1), 0)
            tm = self.tmpl.get(i, "T1")
            if tm == "T2" and vv != y1:
                self.problem = f"rule {i} T2 needs v({p},{x1}) = {y1}"
                return
            add((("r", p), x1, vv, fwd, ("B", p, x1)))
            cells = {ce: y1, cf: y2}                      # 書いた後のブロックの中身
            if tm == "T2":
                last, land = ("B", p, x1), cf + (1 if d == "+" else -1)
                steps = 2
            else:
                w = ("W", q, self.e[p], y1, vv)
                add((("B", p, x1), x2, y2, OPP[fwd], w))
                last, land = w, ce + (1 if d == "+" else -1)
                steps = 3
            tgt = (2 if d == "+" else -2) + self.ce(q)
            sh = abs(tgt - land)
            sh_of[q].add(sh)
            self.costs[(p, s)] = steps + sh
            nxt = ("S", q, 1) if sh else ("r", q)
            if tm == "T2":
                add((("B", p, x1), x2, y2, d, nxt))
            else:
                add((last, vv, y1, d, nxt))
            pos = land
            for j in range(1, sh + 1):
                spath[q][j].add(cells.get(pos))           # ブロックの外は未知（None）
                pos += 1 if d == "+" else -1
        for q, lv in spath.items():
            if len(sh_of[q] - {0}) > 1:
                self.problem = f"state {q}: different shift lengths {sorted(sh_of[q])}"
                return
            n = max(lv)
            for j in range(1, n + 1):
                vals = lv[j]
                if None in vals:
                    vals = set(range(self.r))
                nxt = ("S", q, j + 1) if j < n else ("r", q)
                for z in sorted(vals):
                    add((("S", q, j), z, z, T.hsd[q], nxt))
        self.rules = R

    # fewsym.Conv と同じ口
    def states(self):
        S = set()
        for (a, _, _, _, b) in self.rules:
            S.add(a)
            S.add(b)
        return S

    def nstates(self):
        return len(self.states())

    def breakdown(self):
        cnt = defaultdict(int)
        for st in self.states():
            cnt[st[0]] += 1
        return dict(cnt)

    check_table = F.Conv.check_table

    def enc(self, p, pos, tape):
        bits = []
        for s in tape:
            bits.extend(self.code[s])
        return (("r", p), 2 * pos + self.ce(p) if p in self.e else 2 * pos, bits)

    def cost(self, p, s, d, q):
        return self.costs[(p, s)]

    def emit(self, f, title=None):
        T = self.T
        f.write(f"title('{title or f'{T.name} -> ({self.nstates()},2) by fewsym2.py (docs/23)'}').\n")
        f.write(f"% 生成: tools/fewsym2.py。code={json.dumps({s: ''.join(map(str, v)) for s, v in self.code.items()})}\n")
        f.write(f"% e={json.dumps(self.e)}\n")
        init = T.initial or T.states[0]
        f.write(f"initial_state({sname(('r', init))}).\nfinal_states([]).\n")
        f.write("symbols([0,1]).\nblank(0).\n")
        f.write(f"maxstep({T.maxstep * 5 + 10}).\n")
        for (state, pos, tape, _, _) in T.cases:
            st, ps, bits = self.enc(state, pos, tape)
            f.write(f"initial_conf([{sname(st)},{ps},[{','.join(map(str, bits))}]]).\n")
        for (a, x, y, d, b) in self.rules:
            f.write(f"[{sname(a)},{x},{y},{d},{sname(b)}].\n")
        f.write("states([" + ",".join(sorted(sname(s) for s in self.states())) + "]).\n")


def sname(st):
    kind, q, *rest = st
    return "[" + ",".join([f"{q}_{kind.lower()}"] + [str(x) for x in rest]) + "]"


# ---------------------------------------------------------------- CP-SAT
def solve(T, code, e, time_limit=60.0, workers=8, forbid_t2=False):
    """符号と向きを固定し、v と経路の型を CP-SAT で選ぶ。sh ∈ {0, 1} の場合だけ（入ってくる側の向き、または全部 L）。"""
    from ortools.sat.python import cp_model
    M = cp_model.CpModel()
    cvx = ConvX.__new__(ConvX)
    cvx.code, cvx.e = code, e
    info = []
    V = {}
    for i, (p, s, t, d, q) in enumerate(T.rules):
        x1, x2 = cvx.bits(p, s)
        y1, y2 = cvx.bits(p, t)
        if (p, x1) not in V:
            V[(p, x1)] = M.NewBoolVar(f"v_{p}_{x1}")
        ce = cvx.ce(p)
        cf = 1 - ce
        tgt = (2 if d == "+" else -2) + cvx.ce(q)
        land1 = ce + (1 if d == "+" else -1)
        land2 = cf + (1 if d == "+" else -1)
        sh1, sh2 = abs(tgt - land1), abs(tgt - land2)
        cells = {ce: y1, cf: y2}
        if min(sh1, sh2) > 1:
            return None
        t2 = M.NewBoolVar(f"t2_{i}")
        if forbid_t2 or sh2 > 1:
            M.Add(t2 == 0)
        if sh1 > 1:
            M.Add(t2 == 1)
        # T2 なら v = y1
        M.Add(V[(p, x1)] == y1).OnlyEnforceIf(t2)
        info.append(dict(i=i, p=p, q=q, x1=x1, y1=y1, y2=y2, sh1=sh1, sh2=sh2, t2=t2, e=e[p],
                         cross1=cells.get(land1), cross2=cells.get(land2)))
    # W の鍵 (q, e, y1, vv) の使用
    W = {}
    for it in info:
        if it["sh1"] > 1:
            continue
        for vv in (0, 1):
            key = (it["q"], it["e"], it["y1"], vv)
            if key not in W:
                W[key] = (M.NewBoolVar(f"w_{len(W)}"), it["sh1"])
            u = W[key][0]
            # T1 かつ v = vv なら使う
            vb = V[(it["p"], it["x1"])]
            lit = M.NewBoolVar("")
            if vv == 1:
                M.AddBoolAnd([it["t2"].Not(), vb]).OnlyEnforceIf(lit)
                M.AddBoolOr([it["t2"], vb.Not(), lit])
            else:
                M.AddBoolAnd([it["t2"].Not(), vb.Not()]).OnlyEnforceIf(lit)
                M.AddBoolOr([it["t2"], vb, lit])
            M.AddImplication(lit, u)
            it.setdefault("wl", {})[vv] = lit
    qs = sorted({it["q"] for it in info})
    Sz = {}
    Sx = {}
    obj = [u for (u, _) in W.values()]
    for q in qs:
        rs = [it for it in info if it["q"] == q]
        Sx[q] = M.NewBoolVar(f"s_{q}")
        obj.append(Sx[q])
        for z in (0, 1):
            Sz[(q, z)] = M.NewBoolVar(f"sz_{q}_{z}")
            M.AddImplication(Sz[(q, z)], Sx[q])
        # S を通る経路と通過する値
        for it in rs:
            # T1 で sh1 = 1: f セル（y2）を通過。T2 で sh2 = 1: e セル（y1）を通過
            for sh, cross, lit in ((it["sh1"], it["cross1"], it["t2"].Not()), (it["sh2"], it["cross2"], it["t2"])):
                if sh == 1:
                    for z in ((0, 1) if cross is None else (cross,)):
                        M.AddImplication(lit, Sz[(q, z)])
        for b in (0, 1):
            # S に入る: sh1 = 1 の W 鍵（y1 = b）と、sh2 = 1 の T2 規則（y2 = b）
            ins = [u for (key, (u, sh1)) in W.items() if key[0] == q and sh1 == 1 and key[2] == b]
            ins += [it["t2"] for it in rs if it["sh2"] == 1 and it["y2"] == b]
            M.Add(sum(ins) <= 1)
            # [q^r] に入る: S の規則（z = b）、sh1 = 0 の W 鍵（y1 = b）、sh2 = 0 の T2 規則（y2 = b）
            ins = [Sz[(q, b)]]
            ins += [u for (key, (u, sh1)) in W.items() if key[0] == q and sh1 == 0 and key[2] == b]
            ins += [it["t2"] for it in rs if it["sh2"] == 0 and it["y2"] == b]
            M.Add(sum(ins) <= 1)
    M.Minimize(sum(obj))
    S = cp_model.CpSolver()
    S.parameters.max_time_in_seconds = time_limit
    S.parameters.num_workers = workers
    st = S.Solve(M)
    if st not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        return {"status": S.StatusName(st)}
    v = {f"{p}|{x1}": int(S.Value(b)) for (p, x1), b in V.items()}
    tmpl = {it["i"]: ("T2" if S.Value(it["t2"]) else "T1") for it in info}
    return {"status": S.StatusName(st), "obj": S.ObjectiveValue(), "bound": S.BestObjectiveBound(),
            "v": v, "tmpl": tmpl}


def conv_of(T, sol):
    code = {s: tuple(int(ch) for ch in c) for s, c in sol["code"].items()}
    v = {}
    for key, b in sol["v"].items():
        p, x1 = key.rsplit("|", 1)
        v[(p, int(x1))] = b
    tmpl = {int(i): t for i, t in sol["tmpl"].items()}
    return ConvX(T, code, sol["e"], v, tmpl)


def codes_k2(T):
    others = [s for s in T.symbols if s != T.blank]
    words = [(0, 1), (1, 0), (1, 1)]
    for assign in itertools.permutations(words, len(others)):
        yield {T.blank: (0, 0), **dict(zip(others, assign))}


def cmd_opt(a):
    T = F.load(a.input)
    assert len(T.symbols) <= 4
    best = None
    rows = []
    orients = {"near": near(T), "allL": {q: "L" for q in T.states}}
    for oname, e in orients.items():
        for code in codes_k2(T):
            res = solve(T, code, e, time_limit=a.time, workers=a.workers, forbid_t2=a.no_t2)
            if res is None or "v" not in res:
                continue
            sol = {"machine": T.name, "orient": oname, "e": e,
                   "code": {s: "".join(map(str, c)) for s, c in code.items()}, **res}
            cv = conv_of(T, sol)
            n = cv.nstates()
            errs = cv.check_table()
            rows.append((n, oname, sol["code"], res["status"], len(errs)))
            print(f"{oname} code={sol['code']}: states={n} rules={len(cv.rules)} {res['status']} "
                  f"(obj {res['obj']:.0f} bound {res['bound']:.0f}) table={'OK' if not errs else errs[:2]}", flush=True)
            if not errs and (best is None or n < best[0]):
                best = (n, sol, cv)
    n, sol, cv = best
    sol.update(states=n, rules=len(cv.rules), breakdown=cv.breakdown())
    print(json.dumps({k: sol[k] for k in ("machine", "orient", "code", "states", "rules", "breakdown", "status")},
                     ensure_ascii=False))
    if a.json:
        os.makedirs(os.path.dirname(a.json) or ".", exist_ok=True)
        json.dump(sol, open(a.json, "w"), ensure_ascii=False, indent=1)
    return True


def evaluate(T, code, e, time_limit=10.0, workers=8):
    res = solve(T, code, e, time_limit=time_limit, workers=workers)
    if res is None or "v" not in res:
        return None, None
    sol = {"machine": T.name, "e": dict(e), "code": {s: "".join(map(str, c)) for s, c in code.items()}, **res}
    cv = conv_of(T, sol)
    if cv.problem or cv.check_table():
        return None, None
    return cv.nstates(), sol


def cmd_search(a):
    """向き e の山登り（1 状態ずつ反転、改善か同点なら受理）。符号は全数。内側は CP-SAT（厳密）。外側は発見的。"""
    T = F.load(a.input)
    rng = random.Random(a.seed)
    best = None
    codes = list(codes_k2(T))
    for ci, code in enumerate(codes):
        for start in ("allL", "near", "rand"):
            e = {"allL": {q: "L" for q in T.states}, "near": near(T),
                 "rand": {q: rng.choice("LR") for q in T.states}}[start]
            cur, sol = evaluate(T, code, e, a.time, a.workers)
            if cur is None:
                cur = 10 ** 6
            improved = True
            rounds = 0
            while improved and rounds < a.rounds:
                improved = False
                rounds += 1
                order = list(T.states)
                rng.shuffle(order)
                for q in order:
                    e2 = dict(e)
                    e2[q] = "R" if e[q] == "L" else "L"
                    n, s2 = evaluate(T, code, e2, a.time, a.workers)
                    if n is not None and n <= cur:
                        if n < cur:
                            improved = True
                        e, cur, sol = e2, n, s2
            print(f"code#{ci} {sol and sol['code']} start={start}: {cur} (rounds {rounds})", flush=True)
            if sol and (best is None or cur < best[0]):
                best = (cur, sol)
    n, sol = best
    cv = conv_of(T, sol)
    sol.update(orient="search", states=n, rules=len(cv.rules), breakdown=cv.breakdown())
    print(json.dumps({k: sol[k] for k in ("machine", "code", "states", "rules", "breakdown", "status")}, ensure_ascii=False))
    if a.json:
        os.makedirs(os.path.dirname(a.json) or ".", exist_ok=True)
        json.dump(sol, open(a.json, "w"), ensure_ascii=False, indent=1)
    return True


def cmd_check(a):
    sol = json.load(open(a.json))
    T = F.load(sol["machine"])
    cv = conv_of(T, sol)
    ok, lines = F.check_all(cv, a.random, seed=a.seed)
    print(f"{T.name} -> ({cv.nstates()},2) rules={len(cv.rules)} breakdown={cv.breakdown()}")
    print("\n".join("  " + x for x in lines))
    return ok


def cmd_build(a):
    sol = json.load(open(a.json))
    T = F.load(sol["machine"])
    cv = conv_of(T, sol)
    print(f"{T.name} -> ({cv.nstates()},2) rules={len(cv.rules)}")
    if a.output:
        os.makedirs(os.path.dirname(a.output) or ".", exist_ok=True)
        with open(a.output, "w") as f:
            cv.emit(f)
    return True


def mutants(cv):
    """規則を 1 本消す／書く値を反転する／行き先を別の状態にする（決まった乱数で 1 本ずつ）。"""
    rng = random.Random(7)
    sts = sorted(cv.states(), key=str)
    for i, (a, x, y, d, b) in enumerate(cv.rules):
        yield f"del {i}", cv.rules[:i] + cv.rules[i + 1:]
        yield f"flip {i}", cv.rules[:i] + [(a, x, 1 - y, d, b)] + cv.rules[i + 1:]
        b2 = rng.choice([s for s in sts if s != b])
        yield f"retarget {i}", cv.rules[:i] + [(a, x, y, d, b2)] + cv.rules[i + 1:]


def cmd_mutate(a):
    sol = json.load(open(a.json))
    T = F.load(sol["machine"])
    cv = conv_of(T, sol)
    base, _ = F.local_all(cv)
    assert not base
    orig = cv.rules
    killed = total = 0
    survivors = []
    for name, rules in mutants(cv):
        cv.rules = rules
        bad, _ = F.local_all(cv)
        errs = cv.check_table()
        total += 1
        if bad or errs:
            killed += 1
        else:
            survivors.append(name)
    cv.rules = orig
    print(f"mutants killed (local exhaustive or table check): {killed}/{total}; survivors: {survivors[:10]}")
    return killed == total


def main(argv):
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("opt")
    p.add_argument("input")
    p.add_argument("--time", type=float, default=60.0)
    p.add_argument("--workers", type=int, default=8)
    p.add_argument("--no-t2", action="store_true", help="先書き（T2）を使わない（向きだけの効果を見る）")
    p.add_argument("--json")
    p = sub.add_parser("search")
    p.add_argument("input")
    p.add_argument("--time", type=float, default=10.0)
    p.add_argument("--workers", type=int, default=8)
    p.add_argument("--rounds", type=int, default=4)
    p.add_argument("--seed", type=int, default=1)
    p.add_argument("--json")
    p = sub.add_parser("check")
    p.add_argument("json")
    p.add_argument("--random", type=int, default=500)
    p.add_argument("--seed", type=int, default=20260929)
    p = sub.add_parser("build")
    p.add_argument("json")
    p.add_argument("-o", "--output")
    p = sub.add_parser("mutate")
    p.add_argument("json")
    a = ap.parse_args(argv)
    return {"opt": cmd_opt, "search": cmd_search, "check": cmd_check, "build": cmd_build, "mutate": cmd_mutate}[a.cmd](a)


if __name__ == "__main__":
    sys.exit(0 if main(sys.argv[1:]) else 1)
