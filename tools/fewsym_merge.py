#!/usr/bin/env python3
"""記号削減した T̃ の状態の併合（docs/23 §4）。部分的な規則表の併合（未定義の読みは相手の規則で埋める）。

T̃ の 2 状態 a, b を併合してよいのは:
  * 同じ読みの規則が両方にあれば、書く値・向きが同じで、行き先も（再帰的に）併合できる（閉包）
  * 停止の読み（T が停止規則 [p, s, s, 0, halt/null] を使う配置で T̃ が止まる (状態, 読み)）は、併合後も未定義のまま
  * 併合後の表が決定的・可逆（Morita Def. 5.4）
併合の前後で、定義されていた遷移はそのまま残る（名前が変わるだけ）ので、T の実行を模倣する T̃ の実行は併合後も
同じ形で残る。変わるのは「T̃ が規則の無い配置で止まっていたところ」だけで、それは T が規則の無い配置（停止規則でもない）
で止まる場合にしか起きない。**そこで併合した機械は NoStuck な実行（CTSH の符号化から始まる実行など）についてだけ T を
模倣する**（docs/22 の記録と同じ前提）。検査も NoStuck な実行で行う（fewsym.check_all の nostuck）。

貪欲法（乱択の順で対を試し、通れば併合）を何度か回して最小を取る。発見的。

    python3 tools/fewsym_merge.py results/fewsym/urtm24-4.x2s.json --restarts 20 --json results/fewsym/urtm24-4.x2m.json
    python3 tools/fewsym_merge.py --check results/fewsym/urtm24-4.x2m.json
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


def key(st):
    return json.dumps(list(st))


def unkey(s):
    return tuple(json.loads(s))


class Merged:
    """cv（Conv / ConvX）の状態を rep で名前替えしたもの。fewsym の検査の口を持つ。"""

    def __init__(self, cv, rep):
        self.cv, self.rep = cv, dict(rep)
        self.T, self.k, self.r = cv.T, cv.k, cv.r
        self.problem = None
        seen, R = set(), []
        for (a, x, y, d, b) in cv.rules:
            rl = (self.m(a), x, y, d, self.m(b))
            if rl not in seen:
                seen.add(rl)
                R.append(rl)
        self.rules = R

    def m(self, st):
        return self.rep.get(st, st)

    check_table = F.Conv.check_table
    states = G.ConvX.states
    nstates = G.ConvX.nstates

    def breakdown(self):
        return {"merged_from": self.cv.nstates(), "states": self.nstates()}

    def enc(self, p, pos, tape):
        st, ps, bits = self.cv.enc(p, pos, tape)
        return self.m(st), ps, bits

    def cost(self, p, s, d, q):
        return self.cv.cost(p, s, d, q)


def protected(cv):
    """T の停止規則の配置で T̃ が止まる (状態, 読み)。"""
    T = cv.T
    out = set()
    delta = {(a, x): (y, d, b) for (a, x, y, d, b) in cv.rules}
    for (p, s, t, d, q) in T.halt_rules:
        st, ps, bits = cv.enc(p, 0, [s])
        bits = list(bits)
        for _ in range(3 * cv.k + 2):
            if not 0 <= ps < len(bits):
                raise SystemExit(f"halting run of {p},{s} leaves the block")
            r = delta.get((st, bits[ps]))
            if r is None:
                out.add((st, bits[ps]))
                break
            y, dd, b = r
            bits[ps] = y
            ps += F.MOVE[dd]
            st = b
    return out


def try_merge(rules_by, uf, a, b, prot_by):
    """uf（dict）の写しに a, b の併合を閉包つきで施す。失敗なら None。"""
    uf = dict(uf)

    def find(x):
        while uf.get(x, x) != x:
            x = uf[x]
        return x
    members = defaultdict(set)
    for s in rules_by:
        members[find(s)].add(s)
    table = {}          # 代表 -> {読み: (書く値, 向き, 行き先)}
    prot = defaultdict(set)
    for rep, ms in members.items():
        t = {}
        for s in ms:
            for x, v in rules_by[s].items():
                t.setdefault(x, v)
            prot[rep] |= prot_by.get(s, set())
        table[rep] = t
    queue = [(a, b)]
    while queue:
        u, v = queue.pop()
        ru, rv = find(u), find(v)
        if ru == rv:
            continue
        tu, tv = table.get(ru, {}), table.get(rv, {})
        pu, pv = prot[ru], prot[rv]
        if any(x in tv for x in pu) or any(x in tu for x in pv):
            return None
        uf[rv] = ru
        new = dict(tu)
        for x, (y, d, nb) in tv.items():
            if x in new:
                y0, d0, nb0 = new[x]
                if (y0, d0) != (y, d):
                    return None
                queue.append((nb0, nb))
            else:
                new[x] = (y, d, nb)
        table[ru] = new
        prot[ru] = pu | pv
        table.pop(rv, None)
    return uf


def rep_of(uf, states):
    def find(x):
        while uf.get(x, x) != x:
            x = uf[x]
        return x
    return {s: find(s) for s in states}


def greedy(cv, rng, prot):
    rules_by = defaultdict(dict)
    for (a, x, y, d, b) in cv.rules:
        rules_by[a][x] = (y, d, b)
    states = sorted(cv.states(), key=str)
    for s in states:
        rules_by.setdefault(s, {})
    prot_by = defaultdict(set)
    for (s, x) in prot:
        prot_by[s].add(x)
    uf = {}
    changed = True
    while changed:
        changed = False
        pairs = [(states[i], states[j]) for i in range(len(states)) for j in range(i + 1, len(states))]
        rng.shuffle(pairs)
        for (a, b) in pairs:
            rep = rep_of(uf, states)
            if rep[a] == rep[b]:
                continue
            uf2 = try_merge(rules_by, uf, a, b, prot_by)
            if uf2 is None:
                continue
            mg = Merged(cv, rep_of(uf2, states))
            if mg.check_table():
                continue
            uf = uf2
            changed = True
    return Merged(cv, rep_of(uf, states))


def exact(cv, prot, time_limit=300.0, workers=8, hint=None):
    """併合の最小化を CP-SAT で（対の変数 same[a,b]、推移律、閉包、停止の保護、可逆性）。
    返り値 (status, Merged, 下界)。"""
    from ortools.sat.python import cp_model
    states = sorted(cv.states(), key=str)
    idx = {s: i for i, s in enumerate(states)}
    rules_by = defaultdict(dict)
    for (a, x, y, d, b) in cv.rules:
        rules_by[a][x] = (y, d, b)
    entry = {}
    for (a, x, y, d, b) in cv.rules:
        entry[b] = d
    prot_by = defaultdict(set)
    for (s, x) in prot:
        prot_by[s].add(x)
    n = len(states)

    def static_ok(a, b):
        if entry.get(a) and entry.get(b) and entry[a] != entry[b]:
            return False
        if any(x in rules_by[b] for x in prot_by[a]) or any(x in rules_by[a] for x in prot_by[b]):
            return False
        for x, (y, d, _) in rules_by[a].items():
            if x in rules_by[b] and rules_by[b][x][:2] != (y, d):
                return False
        return True
    cand = {}
    M = cp_model.CpModel()
    for i in range(n):
        for j in range(i + 1, n):
            if static_ok(states[i], states[j]):
                cand[(i, j)] = M.NewBoolVar("")

    def same(a, b):
        i, j = idx[a], idx[b]
        if i == j:
            return True
        if i > j:
            i, j = j, i
        return cand.get((i, j), False)
    # 閉包
    for (i, j), v in cand.items():
        a, b = states[i], states[j]
        for x, (y, d, ta) in rules_by[a].items():
            if x in rules_by[b]:
                tb = rules_by[b][x][2]
                sv = same(ta, tb)
                if sv is False:
                    M.Add(v == 0)
                elif sv is not True:
                    M.AddImplication(v, sv)
    # 推移律
    nbr = defaultdict(set)
    for (i, j) in cand:
        nbr[i].add(j)
        nbr[j].add(i)
    for (i, j), v in cand.items():
        for kk in nbr[i] | nbr[j]:
            if kk in (i, j):
                continue
            a, b = sorted((i, kk)), sorted((j, kk))
            vik, vjk = cand.get(tuple(a)), cand.get(tuple(b))
            if vik is None and vjk is None:
                continue
            if vik is None:
                M.AddBoolOr([v.Not(), vjk.Not()])
            elif vjk is None:
                M.AddBoolOr([v.Not(), vik.Not()])
            else:
                M.AddBoolOr([v.Not(), vik.Not(), vjk])
                M.AddBoolOr([v.Not(), vjk.Not(), vik])
    # 可逆性: 同じ類に入る相異なる規則は書く値が違う（同じなら、併合後に同じ規則になる場合だけ）
    into = defaultdict(list)
    for rl in cv.rules:
        into[rl[4]].append(rl)
    for (i, j), v in cand.items():
        for r1 in into[states[i]]:
            for r2 in into[states[j]]:
                if r1[2] != r2[2]:
                    continue
                if r1[1] != r2[1]:
                    M.Add(v == 0)
                    continue
                sa = same(r1[0], r2[0])
                if sa is False:
                    M.Add(v == 0)
                elif sa is not True:
                    M.AddImplication(v, sa)
    leader = []
    for jj in range(n):
        prev = [cand[(i, jj)] for i in range(jj) if (i, jj) in cand]
        L = M.NewBoolVar("")
        M.AddBoolOr(prev + [L])
        leader.append(L)
    M.Minimize(sum(leader))
    if hint is not None:
        for (i, j), v in cand.items():
            M.AddHint(v, 1 if hint.get(states[i], states[i]) == hint.get(states[j], states[j]) else 0)
    S = cp_model.CpSolver()
    S.parameters.max_time_in_seconds = time_limit
    S.parameters.num_workers = workers
    st = S.Solve(M)
    if st not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        return S.StatusName(st), None, None
    rep = {}
    for jj, s in enumerate(states):
        r = s
        for i in range(jj):
            if (i, jj) in cand and S.Value(cand[(i, jj)]):
                r = rep[states[i]]
                break
        rep[s] = r
    return S.StatusName(st), Merged(cv, rep), S.BestObjectiveBound()


def sweep(name, r, k, codes, orients, perturbs, slack, merge_time, rng, log=None):
    """CP-SAT の構成（fewsym3.solve_cp、同じ最適値の解を乱択）→ 厳密な併合、を回して最小を取る。"""
    import fewsym3 as H
    T = F.load(name)
    best = None
    for code in codes:
        for oname in orients:
            e = oname if isinstance(oname, dict) else H.orient_of(T, oname, rng)
            for pt in [None] + list(range(perturbs)):
                st, tm, vf, obj, bd = H.solve_cp(T, r, k, code, e, time_limit=30, workers=8,
                                                 perturb=pt, slack=slack if pt is not None else 0)
                if tm is None:
                    continue
                cv = H.ConvK(T, r, k, code, e, [], vf, tm)
                if cv.problem or cv.check_table():
                    continue
                prot = protected(cv)
                g = greedy(cv, rng, prot)
                stx, mg, bdx = exact(cv, prot, time_limit=merge_time, hint=g.rep)
                if mg is None or mg.check_table() or mg.nstates() > g.nstates():
                    mg, stx = g, "greedy"
                line = (f"code={''.join(''.join(map(str, code[s])) for s in T.symbols)} orient={oname if isinstance(oname, str) else 'custom'} "
                        f"perturb={pt}: {cv.nstates()} -> {mg.nstates()} ({stx})")
                print(line, flush=True)
                if log:
                    log.write(line + "\n")
                    log.flush()
                if best is None or mg.nstates() < best[0]:
                    sol = {"machine": T.name, "radix": r, "k": k,
                           "code": {x: "".join(map(str, c)) for x, c in code.items()}, "e": e, "t2": [],
                           "tm": {str(i): x for i, x in tm.items()},
                           "vfree": [[p, list(xs), x] for (p, xs), x in sorted(vf.items(), key=str)],
                           "states": cv.nstates(), "rules": len(cv.rules)}
                    best = (mg.nstates(), sol, mg, stx)
    return best


def emit_merged(mg, f):
    T = mg.T
    f.write(f"title('{T.name} -> ({mg.nstates()},{mg.r}) by fewsym + fewsym_merge (docs/23)').\n")
    f.write("% 生成: tools/fewsym_merge.py --check ... -o。NoStuck な実行（CTSH の符号化から）についてだけ T を模倣する。\n")
    f.write(f"initial_state({G.sname(mg.m(('r', T.initial or T.states[0])))}).\nfinal_states([]).\n")
    f.write(f"symbols([{','.join(str(x) for x in range(mg.r))}]).\nblank(0).\nmaxstep({T.maxstep * 8}).\n")
    for (state, pos, tape, _, _) in T.cases:
        st, ps, bits = mg.enc(state, pos, tape)
        f.write(f"initial_conf([{G.sname(st)},{ps},[{','.join(map(str, bits))}]]).\n")
    for (a, x, y, d, b) in mg.rules:
        f.write(f"[{G.sname(a)},{x},{y},{d},{G.sname(b)}].\n")
    f.write("states([" + ",".join(sorted(G.sname(s) for s in mg.states())) + "]).\n")


def load_conv(path):
    sol = json.load(open(path))
    T = F.load(sol["machine"])
    if "tmpl" in sol:
        return G.conv_of(T, sol), sol
    if "e" in sol and "k" in sol:
        import fewsym3 as H
        return H.conv_of(sol), sol
    code = {s: tuple(int(ch) for ch in c) for s, c in sol["code"].items()}
    return F.Conv(T, r=sol.get("radix", 2), k=sol["k"], code=code, mode=sol.get("mode", "morita")), sol


def cmd_sweep(argv):
    import itertools
    ap = argparse.ArgumentParser(prog="fewsym_merge.py sweep")
    ap.add_argument("machine")
    ap.add_argument("--radix", type=int, default=2)
    ap.add_argument("-k", type=int, default=None)
    ap.add_argument("--codes", default="all", help="all / JSON ファイル（top の符号を使う）")
    ap.add_argument("--ncodes", type=int, default=6)
    ap.add_argument("--code-index", type=int, default=None, help="符号の一覧のうちこの 1 つだけ（並列実行用）")
    ap.add_argument("--orients", default="allL")
    ap.add_argument("--orient-json", action="append", default=[], help="向き e を持つ解の JSON（追加）")
    ap.add_argument("--perturbs", type=int, default=4)
    ap.add_argument("--slack", type=int, default=0)
    ap.add_argument("--merge-time", type=float, default=60.0)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--out")
    ap.add_argument("--log")
    a = ap.parse_args(argv)
    T = F.load(a.machine)
    r = a.radix
    k = a.k or F.digits_needed(len(T.symbols), r)
    if a.codes.endswith(".json") and "top" not in json.load(open(a.codes)):
        codes = [{x: tuple(int(ch) for ch in c) for x, c in json.load(open(a.codes))["code"].items()}]
    elif a.codes == "random":
        words = [w for w in F.all_words(r, k) if any(w)]
        others = [x for x in T.symbols if x != T.blank]
        rr = random.Random(a.seed)
        codes = [{T.blank: (0,) * k, **dict(zip(others, rr.sample(words, len(others))))} for _ in range(a.ncodes)]
    elif a.codes == "all":
        words = [w for w in F.all_words(r, k) if any(w)]
        others = [x for x in T.symbols if x != T.blank]
        codes = [{T.blank: (0,) * k, **dict(zip(others, perm))} for perm in itertools.permutations(words, len(others))]
        codes = codes[:a.ncodes] if len(codes) > a.ncodes else codes
    else:
        top = json.load(open(a.codes))["top"][:a.ncodes]
        codes = [{x: tuple(int(ch) for ch in c) for x, c in t[2].items()} for t in top]
    if a.code_index is not None:
        codes = codes[a.code_index:a.code_index + 1]
    orients = a.orients.split(",") + [json.load(open(p))["e"] for p in a.orient_json]
    log = open(a.log, "a") if a.log else None
    best = sweep(T.name, r, k, codes, orients, a.perturbs, a.slack, a.merge_time, random.Random(a.seed), log)
    n, sol, mg, stx = best
    print(f"best: {sol['states']} -> ({n},{r}) ({stx})")
    if a.out:
        base = a.out.replace(".merge.json", ".json")
        json.dump(sol, open(base, "w"), ensure_ascii=False, indent=1)
        rep = {key(s): key(rr) for s, rr in mg.rep.items() if s != rr}
        json.dump({"base": base, "machine": T.name, "states": n, "rules": len(mg.rules), "from": sol["states"],
                   "search": f"sweep ({stx}); codes {len(codes)} orients {len(orients)} perturbs {a.perturbs} slack {a.slack}",
                   "protected": [[key(s), x] for (s, x) in sorted(protected(mg.cv), key=str)], "rep": rep},
                  open(a.out, "w"), ensure_ascii=False, indent=1)
    return True


def main(argv):
    if argv and argv[0] == "sweep":
        return cmd_sweep(argv[1:])
    ap = argparse.ArgumentParser()
    ap.add_argument("json")
    ap.add_argument("--restarts", type=int, default=10)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--mutate", action="store_true")
    ap.add_argument("--big", type=int, default=0, help="大きい乱択 CTSH の件数")
    ap.add_argument("--exact", type=float, default=0.0, help="CP-SAT の制限時間（秒）。0 なら貪欲だけ")
    ap.add_argument("--check", action="store_true", help="保存した併合を読み、NoStuck の検査をする")
    ap.add_argument("--json-out", "--out", dest="out")
    ap.add_argument("-o", "--output", help="併合した機械の記述ファイル")
    a = ap.parse_args(argv)
    if a.check:
        m = json.load(open(a.json))
        cv, _ = load_conv(m["base"])
        rep = {unkey(k): unkey(v) for k, v in m["rep"].items()}
        mg = Merged(cv, rep)
        ok, lines = F.check_all(mg, 0, nostuck=True, nctsh=a.restarts if a.restarts > 10 else 1000)
        print(f"{cv.T.name}: merged {cv.nstates()} -> ({mg.nstates()},{cv.r}) rules={len(mg.rules)}")
        print("\n".join("  " + x for x in lines))
        if a.big:
            bad, halted = F.check_ctsh(mg, a.big, seed=7, limit=20000, big=True)
            print(f"  {'ok' if not bad else 'NG'} large random CTSH (k<=7, |w_i|<=6, |w|<=8, 20000 T steps): "
                  f"{a.big - bad}/{a.big} ({halted} halt; T steps total {F.check_ctsh.last[0]}, median {F.check_ctsh.last[1]})")
            ok &= bad == 0
        if a.mutate:
            kd, tot, surv = F.mutation_test(mg, nostuck=True)
            print(f"  mutants killed: {kd}/{tot}; survivors: {surv[:10]}")
            ok &= kd == tot
        if a.output:
            with open(a.output, "w") as f:
                emit_merged(mg, f)
        return ok
    cv, sol = load_conv(a.json)
    prot = protected(cv)
    rng = random.Random(a.seed)
    best = None
    for i in range(a.restarts):
        mg = greedy(cv, rng, prot)
        print(f"restart {i}: {cv.nstates()} -> {mg.nstates()}", flush=True)
        if best is None or mg.nstates() < best.nstates():
            best = mg
    how = f"greedy x{a.restarts}"
    if a.exact:
        st, mg, bd = exact(cv, prot, time_limit=a.exact, hint=best.rep)
        print(f"exact: {st} {mg and mg.nstates()} (bound {bd})")
        if mg is not None and not mg.check_table() and mg.nstates() <= best.nstates():
            best = mg
            how = f"CP-SAT {st} (bound {bd})"
    print(f"best: ({best.nstates()},{cv.r}) rules={len(best.rules)} protected={sorted(prot, key=str)}")
    if a.out:
        rep = {key(s): key(r) for s, r in best.rep.items() if s != r}
        json.dump({"base": a.json, "machine": cv.T.name, "states": best.nstates(), "rules": len(best.rules),
                   "from": cv.nstates(), "search": how, "protected": [[key(s), x] for (s, x) in sorted(prot, key=str)],
                   "rep": rep}, open(a.out, "w"), ensure_ascii=False, indent=1)
    return True


if __name__ == "__main__":
    sys.exit(0 if main(sys.argv[1:]) else 1)
