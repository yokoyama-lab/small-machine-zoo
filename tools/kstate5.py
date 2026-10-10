#!/usr/bin/env python3
"""役割の併合による k 状態化（k = 4, 5, 6）の一般形と、その記号数の厳密最適化（docs/20）。

枠組み（詳細は docs/20_five_state_2026-09-28.md §1）:
  * T の状態は入る向きで Q+（右移動で入る。入られない状態も Q+）と Q- に分かれる。
  * 変換後の機械は 6 つの「役割」でできている（d ∈ {+,-}、e = d の逆向き）:
      H_d  安定状態（q ∈ Q_d のセルで [v(q),s] を読む）と、転送先に着いた直後に素の記号を読む状態。d 向きに入る。
      O^d  d 向き転送の元セルで計数を 1 ずつ σ_d へ近づける状態。e 向きに入る。
      D^d  d 向き転送の行き先で計数を σ_d から 1 ずつ遠ざける状態。d 向きに入る。
    入る向き: H+ D+ O- は右、H- D- O+ は左。
  * 「併合」は役割の分割（同じ類の役割は同じ状態になる）。可逆性（Morita Def 5.4）により
    同じ類の役割は入る向きが同じでなければならない。6 類 = pure、{O+,D-}{D+,O-} を併合した 4 類 = 定理 A。
    5 類 = 同じ向きの 1 対だけを併合（左: O+D-, H-O+, H-D-／右: O-D+, H+O-, H+D+ の 6 通り）。
  * 計数値: 方向ごとに単射 v_d : Q_d → Z、番兵 σ_d、向き ε_d ∈ {+1,-1}（ε_d (v(q) - σ_d) ≥ 0）。
    元セルは v(q) から σ_d へ 1 ずつ、行き先は σ_d から v(q) へ 1 ずつ。
  * 規則は構文的に要るものだけ置く（docs/15 と同じ基準。reads(q) = q が読む記号、W(q) = q に入る規則が書く記号）:
      R1  [H_{dir p}, [v(p),s], [v(q),t] (q が疑似状態なら t), d, H_d (または疑似状態)]   T の各規則 [p,s,t,d,q]
      R2  [H_d, s2, [σ_d,s2], e, O^d]                 s2 ∈ ∪_{q∈Q_d} reads(q)
      R3  [O^d, [i,t], [i-ε_d,t], d, D^d]            i ∈ (σ_d, v(q)]、t ∈ W(q)、q ∈ Q_d
      R4  [O^d, [σ_d,t], t, d, H_d]                   t ∈ W(q)、q ∈ Q_d
      R5  [D^d, [j,s2], [j+ε_d,s2], e, O^d]           j ∈ [σ_d, v(q))、s2 ∈ reads(q)、q ∈ Q_d
    （区間は ε_d の向きで読む。）役割 → 状態の写像で状態名を付け、同じ規則は 1 本にまとめる。

    python3 tools/kstate5.py build IN --classes 'op+dm' --json SOL.json -o OUT     # 解から機械を作って検査
    ~/.venvs/urtm/bin/python tools/kstate5.py opt IN --classes 'op+dm' --eps -1  # CP-SAT で記号数を最小化
    ~/.venvs/urtm/bin/python tools/kstate5.py sweep --out results/kstate5         # 6 台 × 全分割 × 向き
"""

import argparse
import json
import os
import sys
from collections import defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import kstate  # noqa: E402

ROLES = ["hp", "hm", "op", "om", "dp", "dm"]          # H+ H- O+ O- D+ D-
ENTRY = {"hp": "+", "dp": "+", "om": "+", "hm": "-", "dm": "-", "op": "-"}
PRETTY = {"hp": "H+", "hm": "H-", "op": "O+", "om": "O-", "dp": "D+", "dm": "D-"}
OPP = {"+": "-", "-": "+"}

# 名前 → 併合する対（空 = pure）。5 状態は同じ向きの 1 対。
PARTITIONS = {
    "pure": [],
    "k4": [("op", "dm"), ("dp", "om")],
    "op+dm": [("op", "dm")],
    "hm+op": [("hm", "op")],
    "hm+dm": [("hm", "dm")],
    "dp+om": [("dp", "om")],
    "hp+om": [("hp", "om")],
    "hp+dp": [("hp", "dp")],
}
FIVE = ["op+dm", "hm+op", "hm+dm", "dp+om", "hp+om", "hp+dp"]


def classes_of(name):
    pairs = PARTITIONS[name]
    cls = {r: r for r in ROLES}
    for a, b in pairs:
        if ENTRY[a] != ENTRY[b]:
            raise SystemExit(f"{a},{b}: entry directions differ (violates Def 5.4)")
        cls[a] = cls[b] = f"{a}_{b}"
    return cls


# ---------------------------------------------------------------- 元機械の情報
class Info:
    def __init__(self, path):
        self.T = T = kstate.Machine(path)
        self.dir = kstate.Construction(T, "k4", (1, 1)).dir   # Q+/Q- の分け方は既存の定理 A と同じ
        self.Qd = {d: [q for q in T.states if self.dir[q] == d] for d in "+-"}
        self.reads = {q: set() for q in T.states}
        self.W = {q: set() for q in T.states}
        for (p, s, t, d, q) in T.quints:
            self.reads[p].add(s)
            if q in self.W:
                self.W[q].add(t)
        self.need = {q: self.reads[q] | self.W[q] for q in T.states}


def between(a, b, closed_b=True):
    """a から b へ（a を含む）。closed_b=False なら b を含まない。"""
    step = 1 if b >= a else -1
    end = b + step if closed_b else b
    return range(a, end, step)


# ---------------------------------------------------------------- 構成
class Gen:
    """役割の分割・計数値・番兵・向きから T' を作る。kstate.lockstep と同じ口を持つ。"""

    def __init__(self, info: Info, partition, v, sigma, eps, prefix="c"):
        self.info = info
        self.T = info.T
        self.partition = partition
        self.cls = classes_of(partition)
        self.v, self.sigma, self.eps = dict(v), dict(sigma), dict(eps)
        self.prefix = prefix
        for d in "+-":
            vals = [self.v[q] for q in info.Qd[d]]
            if len(set(vals)) != len(vals):
                raise SystemExit(f"v_{d} not injective")
            for q in info.Qd[d]:
                if self.eps[d] * (self.v[q] - self.sigma[d]) < 0:
                    raise SystemExit(f"v({q}) on the wrong side of sigma_{d}")
        self.states = list(dict.fromkeys(self.cls[r] for r in ROLES))
        self.k = len(self.states)
        self._build()

    def C(self, i, s):
        return f"{self.prefix}{i}_{s}"

    def is_counter(self, sym):
        return isinstance(sym, str) and sym.startswith(self.prefix) and "_" in sym and \
            sym[len(self.prefix):].split("_", 1)[0].isdigit()

    def split_counter(self, sym):
        i, s = sym[len(self.prefix):].split("_", 1)
        return int(i), s

    def _build(self):
        nf, T, cls, v = self.info, self.T, self.cls, self.v
        R = []   # (rule, role, why)
        for (p, s, t, d, q) in T.quints:
            src = cls["h" + ("p" if nf.dir[p] == "+" else "m")]
            if q in T.pseudo:
                R.append(((src, self.C(v[p], s), t, d, q), src, f"R1 {p},{s}"))
            else:
                R.append(((src, self.C(v[p], s), self.C(v[q], t), d, cls["h" + ("p" if d == "+" else "m")]),
                          src, f"R1 {p},{s}"))
        for d in "+-":
            e = OPP[d]
            sg, ep = self.sigma[d], self.eps[d]
            dn = "p" if d == "+" else "m"
            Hc, Oc, Dc = cls["h" + dn], cls["o" + dn], cls["d" + dn]
            for q in nf.Qd[d]:
                for s2 in sorted(nf.reads[q]):
                    R.append(((Hc, s2, self.C(sg, s2), e, Oc), "h" + dn, f"R2 ->{q}"))
                    for j in between(sg, v[q], closed_b=False):
                        R.append(((Dc, self.C(j, s2), self.C(j + ep, s2), e, Oc), "d" + dn, f"R5 ->{q}"))
                for t in sorted(nf.W[q]):
                    for i in between(sg, v[q]):
                        if i == sg:
                            R.append(((Oc, self.C(sg, t), t, d, Hc), "o" + dn, f"R4 ->{q}"))
                        else:
                            R.append(((Oc, self.C(i, t), self.C(i - ep, t), d, Dc), "o" + dn, f"R3 ->{q}"))
        seen = {}
        for rule, role, why in R:
            seen.setdefault(rule, (role, why))
        self.tagged = seen
        self.quints = list(seen)
        syms = set(T.symbols)
        for (p, s, t, d, q) in self.quints:
            syms.add(s)
            syms.add(t)
        cnt = sorted((x for x in syms if self.is_counter(x)), key=lambda x: (self.split_counter(x)[0], x))
        self.symbols = list(T.symbols) + cnt
        self.nctr = max(abs(self.split_counter(x)[0]) for x in cnt) if cnt else 1

    # -- 決定性・可逆性（Def 5.4）。衝突の組を返す。
    def conflicts(self):
        out = []
        by_dom, by_tgt = defaultdict(list), defaultdict(list)
        for r in self.quints:
            by_dom[(r[0], r[1])].append(r)
            by_tgt[r[4]].append(r)
        for k, rs in by_dom.items():
            if len(rs) > 1:
                out.append(("determinism", rs[0], rs[1]))
        for q, rs in by_tgt.items():
            if len({r[3] for r in rs}) > 1:
                out.append(("direction", rs[0], rs[1]))
            byw = defaultdict(list)
            for r in rs:
                byw[r[2]].append(r)
            for w, rr in byw.items():
                if len(rr) > 1:
                    out.append(("reversibility", rr[0], rr[1]))
        return out

    # -- kstate.lockstep の口
    def cost_k4(self, q, d):
        if q in self.T.pseudo:
            return 1
        return 3 + 2 * abs(self.v[q] - self.sigma[d])

    def encode_state(self, p):
        return self.cls["h" + ("p" if self.info.dir[p] == "+" else "m")]

    def encode_cell(self, p, s):
        return self.C(self.v[p], s)

    def decode_state(self, hstate, counter):
        if not self.is_counter(counter):
            return None
        i, s = self.split_counter(counter)
        for q in self.T.states:
            if self.encode_state(q) == hstate and self.v[q] == i:
                return q
        return None

    encode_conf = kstate.Construction.encode_conf
    decode_tape = kstate.Construction.decode_tape
    decode_conf = kstate.Construction.decode_conf
    step = kstate.Construction.step

    def title(self):
        return (f"kstate5 partition={self.partition} from {self.T.name}: {len(self.T.states)} states "
                f"{len(self.T.symbols)} symbols -> {self.k} states {len(self.symbols)} symbols")

    def emit(self, out):
        T = self.T
        maxstep = T.maxstep * (3 + 2 * max(1, self.nctr)) + 10
        L = [f"title('{self.title()}').",
             "% 生成: tools/kstate5.py（docs/20）。v=" + json.dumps(self.v, ensure_ascii=False)
             + f" sigma={self.sigma} eps={self.eps}",
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


def symbol_count(info, v, sigma):
    """Gen を作らずに記号数を数える（最適化の検算用）。"""
    S = set()
    for d in "+-":
        for q in info.Qd[d]:
            for i in between(sigma[d], v[q]):
                for x in info.need[q]:
                    S.add((i, x))
    return len(info.T.symbols) + len(S)


# ---------------------------------------------------------------- 最適化（CP-SAT）
def optimize(info, partition, eps_minus, slack=2, time_limit=600.0, workers=8, hint=None):
    """記号数を最小にする計数値・番兵を CP-SAT で求める（厳密。規則の粒度でモデル化）。

    ε+ = +1 に固定（値の軸の反転で一般性を失わない）、ε- = eps_minus。計数値は 1..V（V = m+ + m- + slack）。
    番兵 σ_d は変数（各方向の値がすべてその片側にあること）。
    潜在的な規則を (役割, 値, 記号, 変種) ごとに並べ、存在を下から縛る指示変数で表す。
      決定性: 同じ (状態, 読む記号) の規則で、動作 (書く記号, 向き, 次状態) が異なるものは 1 つまで
              （まったく同じ規則が 2 つの役割から出るのは 1 本と数える。k4 で ε- = -ε+ のとき起きる）
      可逆性: 同じ (次状態, 書く記号) に入る規則で、(状態, 読む記号) が異なるものは 1 つまで
    素の記号を読むのは H だけ、素の記号を書いて状態に入るのは R4（→ H）と疑似状態行きの R1 だけなので、
    素の記号の衝突は起きない（R4 は読む [σ,t] ごとに 1 本、T の可逆性から疑似状態行きも衝突しない）。
    R1 同士は T の決定性・可逆性と v の単射性から衝突しない。
    返り値: dict(status, obj, bound, v, sigma, eps)。"""
    from ortools.sat.python import cp_model
    Qd = info.Qd
    cls = classes_of(partition)
    V = len(Qd["+"]) + len(Qd["-"]) + slack
    vals = list(range(1, V + 1))
    eps = {"+": 1, "-": eps_minus}
    syms = list(info.T.symbols)
    M = cp_model.CpModel()
    x = {}
    for d in "+-":
        for q in Qd[d]:
            for i in vals:
                x[q, i] = M.NewBoolVar(f"x[{q},{i}]")
            M.AddExactlyOne(x[q, i] for i in vals)
        for i in vals:
            M.AddAtMostOne(x[q, i] for q in Qd[d])
    M.AddBoolOr([x[q, 1] for d in "+-" for q in Qd[d]])          # 平行移動の対称性を破る

    def side(d, i, toward_sigma, strict):
        if (eps[d] == 1) == toward_sigma:
            return [j for j in vals if (j < i if strict else j <= i)]
        return [j for j in vals if (j > i if strict else j >= i)]

    sig, low = {}, {}
    for d in "+-":
        for i in vals:
            sig[d, i] = M.NewBoolVar(f"sig[{d},{i}]")
        M.AddExactlyOne(sig[d, i] for i in vals)
        for i in vals:
            low[d, i] = sum(sig[d, j] for j in side(d, i, True, False))   # σ_d が i か i より手前
            for q in Qd[d]:
                M.Add(x[q, i] <= low[d, i])
    inn, inS = {}, {}
    for d in "+-":
        for q in Qd[d]:
            for i in vals:
                for strict, store in ((False, inn), (True, inS)):
                    b = M.NewBoolVar("")
                    M.Add(sum(x[q, j] for j in side(d, i, False, strict)) + low[d, i] - 1 <= b)
                    store[q, i] = b
    Wc, Rc, Rh = {}, {}, {}
    for d in "+-":
        for i in vals:
            for s in syms:
                for store, src, sets in ((Wc, inn, info.W), (Rc, inn, info.reads), (Rh, inS, info.reads)):
                    b = M.NewBoolVar("")
                    for q in Qd[d]:
                        if s in sets[q]:
                            M.AddImplication(src[q, i], b)
                    store[d, i, s] = b
    # 潜在的な規則: (読む状態, 読む記号) -> {動作: [存在の式]}、(入る状態, 書く記号) -> {読む鍵: [存在の式]}
    by_read = defaultdict(lambda: defaultdict(list))
    by_write = defaultdict(lambda: defaultdict(list))
    for d in "+-":
        e = OPP[d]
        dn = "p" if d == "+" else "m"
        Hc, Oc, Dc = cls["h" + dn], cls["o" + dn], cls["d" + dn]
        ep = eps[d]
        ru = set().union(*[info.reads[q] for q in Qd[d]]) if Qd[d] else set()
        for i in vals:
            for s in syms:
                # R1（H_d が安定配置で読む / H_d に入る R1 が書く）
                sr = sum(x[q, i] for q in Qd[d] if s in info.reads[q])
                sw = sum(x[q, i] for q in Qd[d] if s in info.W[q])
                by_read[Hc, (i, s)][("R1",)].append(sr)
                by_write[Hc, (i, s)][("R1", i, s)].append(sw)
                # R2: H_d が素の s を読み [σ_d, s] を書いて Oc^d へ
                if s in ru:
                    by_write[Oc, (i, s)][(Hc, s)].append(sig[d, i])
                # R3 / R4: Oc^d が [i,s] を読む
                p3 = M.NewBoolVar("")
                M.Add(Wc[d, i, s] - sig[d, i] <= p3)
                p4 = M.NewBoolVar("")
                M.Add(Wc[d, i, s] + sig[d, i] - 1 <= p4)
                by_read[Oc, (i, s)][("w", i - ep, s, d, Dc)].append(p3)
                by_read[Oc, (i, s)][("w", s, s, d, Hc, "plain")].append(p4)
                if i - ep in vals:
                    by_write[Dc, (i - ep, s)][(Oc, i, s)].append(p3)
                else:
                    M.Add(p3 == 0)
                # R5: Dc^d が [i,s] を読み [i+ε,s] を書いて Oc^d へ
                by_read[Dc, (i, s)][("w", i + ep, s, e, Oc)].append(Rh[d, i, s])
                if i + ep in vals:
                    by_write[Oc, (i + ep, s)][(Dc, i, s)].append(Rh[d, i, s])
                else:
                    M.Add(Rh[d, i, s] == 0)

    def at_most_one_group(groups):
        if len(groups) < 2:
            return
        inds = []
        for key, exprs in groups.items():
            b = M.NewBoolVar("")
            for ex in exprs:
                M.Add(ex <= b)
            inds.append(b)
        M.Add(sum(inds) <= 1)

    for groups in by_read.values():
        at_most_one_group(groups)
    for groups in by_write.values():
        at_most_one_group(groups)
    U = []
    for i in vals:
        for s in syms:
            u = M.NewBoolVar("")
            for d in "+-":
                M.AddImplication(Wc[d, i, s], u)
                M.AddImplication(Rc[d, i, s], u)
            U.append(u)
    M.Minimize(sum(U))
    if hint:
        for (q, i), var in x.items():
            M.AddHint(var, 1 if hint.get(q) == i else 0)
    S = cp_model.CpSolver()
    S.parameters.max_time_in_seconds = time_limit
    S.parameters.num_workers = workers
    st = S.Solve(M)
    res = {"status": S.StatusName(st), "partition": partition, "eps": eps, "V": V, "slack": slack,
           "wall": round(S.WallTime(), 1)}
    if st in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        v = {q: i for (q, i), var in x.items() if S.Value(var)}
        sigma = {d: next(i for i in vals if S.Value(sig[d, i])) for d in "+-"}
        res.update(obj=int(S.ObjectiveValue()) + len(syms), bound=int(round(S.BestObjectiveBound())) + len(syms),
                   v=v, sigma=sigma)
    return res


# ---------------------------------------------------------------- 検査
def verify(info, g: Gen, outpath=None):
    """決定性・可逆性、全試験例の逐段突き合わせ。(ok, 報告行の列)"""
    lines = []
    conf = g.conflicts()
    if conf:
        for c in conf[:4]:
            lines.append(f"  conflict {c[0]}: {c[1]} [{g.tagged[c[1]][1]}] vs {c[2]} [{g.tagged[c[2]][1]}]")
        return False, lines
    delta = {(p, s): (t, d, q) for (p, s, t, d, q) in g.quints}
    res = kstate.check_cases(info.T, g, delta)
    nok = sum(1 for r in res if r[0])
    bad = [r[1] for r in res if not r[0]]
    # 原典の誤植（urtm13-7 case4 の期待値 1073 → 1173）だけの NG は逐段一致として数える
    typo = [b for b in bad if "both halt" in b and "T steps 1173 != expected 1073" in b]
    lines.append(f"  lockstep {nok}/{len(res)} ok" + (f" (+{len(typo)} 原典誤植のみ)" if typo else ""))
    for b in bad:
        if b not in typo:
            lines.append("   " + b[:240])
    return nok + len(typo) == len(res), lines


def local_check(info, g: Gen):
    """1 ステップ模倣の局所的な全数検査。

    T の各規則 [p,s,t,d,q] と、行き先セルの記号 s2 ∈ reads(q)（q が疑似状態なら不要）のすべてについて、
    元セル [v(p),s]・行き先 s2 の 2 セルだけのテープから T' をちょうど cost ステップ走らせ、
    (a) 途中でヘッドがこの 2 セルの外に出ない、(b) 途中で止まらない、(c) 終わりの配置が T の次の配置の符号化、
    を確かめる。シャトルはこの 2 セルしか読み書きしないので、(a) が成り立てば残りのテープは結果に影響しない。
    したがって、T が疑似状態以外で行き詰まらない（NoStuck）実行について、これは 1 ステップ模倣の補題を
    全ての場合で確かめたことになる（機械の全数検査。定理証明系の証明ではない）。
    返り値: (ok, 検査した場合の数, 最初の失敗)"""
    T = info.T
    delta = {(p, s): (t, d, q) for (p, s, t, d, q) in g.quints}
    n = 0
    for (p, s, t, d, q) in T.quints:
        s2s = [None] if q in T.pseudo else sorted(info.reads[q])
        for s2 in s2s:
            n += 1
            src = 1
            dst = src + kstate.MOVE[d]
            tape = [T.blank] * 3
            tape[src] = g.encode_cell(p, s)
            if s2 is not None and d != "0":
                tape[dst] = s2
            conf = (g.encode_state(p), src, list(tape))
            for _ in range(g.cost_k4(q, d)):
                if conf[1] not in (src, dst):
                    return False, n, f"head left the two cells: rule {p},{s} s2={s2}"
                nxt = g.step(delta, conf)
                if nxt is None or nxt == "fell":
                    return False, n, f"T' stopped early: rule {p},{s} s2={s2} at {conf[0]}@{conf[1]} {conf[2]}"
                conf = nxt
            exp_tape = list(tape)
            exp_tape[src] = t
            if q in T.pseudo:
                exp = (q, dst, exp_tape)
            else:
                exp_tape[dst] = g.encode_cell(q, s2)
                exp = (g.encode_state(q), dst, exp_tape)
            if (conf[0], conf[1], conf[2][:3]) != exp:
                return False, n, f"mismatch: rule {p},{s} s2={s2}: got {conf[0]}@{conf[1]} {conf[2][:3]} exp {exp}"
    return True, n, None


def load_solution(path):
    s = json.load(open(path))
    return s["v"], s["sigma"], s["eps"]


def cmd_build(a):
    info = Info(a.input)
    v, sigma, eps = load_solution(a.json)
    g = Gen(info, a.classes, v, sigma, eps)
    ok, lines = verify(info, g)
    print(f"{info.T.name} {a.classes}: k={g.k} n'={len(g.symbols)} |delta'|={len(g.quints)}"
          f" (symbol_count={symbol_count(info, v, sigma)})")
    print("\n".join(lines))
    if a.output:
        with open(a.output, "w") as f:
            g.emit(f)
    return ok


def cmd_opt(a):
    info = Info(a.input)
    r = optimize(info, a.classes, a.eps, a.slack, a.time, a.workers)
    print(json.dumps(r, ensure_ascii=False))
    return True


MACHINES = ["urtm10-8", "urtm13-7", "urtm15-6", "urtm17-5", "urtm24-4", "urtm32-3"]


def cmd_sweep(a):
    os.makedirs(a.out, exist_ok=True)
    parts = a.partitions.split(",") if a.partitions else ["pure", "k4"] + FIVE
    for mname in (a.machines.split(",") if a.machines else MACHINES):
        info = Info(f"{HERE}/../data/urtm/{mname}.txt")
        for part in parts:
            for em in (1, -1):
                tag = f"{mname}.{part}.eps{'+' if em == 1 else '-'}"
                path = f"{a.out}/{tag}.json"
                if os.path.exists(path) and not a.force:
                    r = json.load(open(path))
                else:
                    r = optimize(info, part, em, a.slack, a.time, a.workers)
                    if "v" in r:
                        g = Gen(info, part, r["v"], r["sigma"], r["eps"])
                        ok, lines = verify(info, g)
                        r["built_symbols"] = len(g.symbols)
                        r["rules"] = len(g.quints)
                        r["verify_ok"] = ok
                        r["verify"] = lines
                        with open(f"{a.out}/{tag}.txt", "w") as f:
                            g.emit(f)
                    json.dump(r, open(path, "w"), ensure_ascii=False, indent=1)
                print(f"{tag}: {r['status']} obj={r.get('obj')} bound={r.get('bound')} "
                      f"built={r.get('built_symbols')} rules={r.get('rules')} verify={r.get('verify_ok')} "
                      f"wall={r.get('wall')}s", flush=True)
    return True


def cmd_mutate(a):
    """局所全数検査の検出力: 規則を 1 本消す／書く記号を別の記号に替える変異を全部作り、何本殺せるか。
    誤検出の側は、変異前の機械が通ること（summary の 局所全数 ok）で見る。"""
    info = Info(a.input)
    r = json.load(open(a.json))
    g = Gen(info, r["partition"], r["v"], r["sigma"], r["eps"])
    base_ok = local_check(info, g)[0]
    killed = total = 0
    syms = g.symbols
    for k, rule in enumerate(g.quints):
        variants = [None]
        p, s, t, d, q = rule
        alt = syms[(syms.index(t) + 1) % len(syms)]
        variants.append((p, s, alt, d, q))
        for var in variants:
            g2 = Gen(info, r["partition"], r["v"], r["sigma"], r["eps"])
            g2.quints = g.quints[:k] + ([var] if var else []) + g.quints[k + 1:]
            total += 1
            killed += not local_check(info, g2)[0]
    print(f"{info.T.name} {r['partition']}: base local_check={base_ok}; mutants killed {killed}/{total}")
    return base_ok and killed == total


def cmd_summary(a):
    """sweep の結果（JSON）から表を作り、各解を作り直して局所全数検査も走らせる。"""
    rows = []
    best = {}
    for mname in MACHINES:
        info = Info(f"{HERE}/../data/urtm/{mname}.txt")
        for part in ["pure", "k4"] + FIVE:
            for em in ("+", "-"):
                path = f"{a.dir}/{mname}.{part}.eps{em}.json"
                if not os.path.exists(path):
                    rows.append((mname, part, em, "missing", "", "", "", ""))
                    continue
                r = json.load(open(path))
                if "v" not in r:
                    rows.append((mname, part, em, r["status"], "", "", "", ""))
                    continue
                g = Gen(info, part, r["v"], r["sigma"], r["eps"])
                lok, ncase, why = local_check(info, g)
                ok = r.get("verify_ok") and lok and not g.conflicts()
                rows.append((mname, part, em, r["status"], len(g.symbols), len(g.quints),
                             "ok" if r.get("verify_ok") else "NG", f"{'ok' if lok else 'NG'} {ncase}"))
                if ok and r["status"] == "OPTIMAL":
                    key = (mname, g.k if part != "pure" else 6, part)
                    if key not in best or len(g.symbols) < best[key]:
                        best[key] = len(g.symbols)
    L = ["# kstate5 の掃引結果（tools/kstate5.py summary が生成）", "",
         "列: 元機械・分割・ε- の向き（ε+ = +1 固定）・CP-SAT の状態・記号数・規則数・"
         "全試験例の逐段突き合わせ・1 ステップ模倣の局所全数検査（場合の数）。", "",
         "| 元機械 | 分割 | ε- | 求解 | 記号 | 規則 | 逐段 | 局所全数 |", "|---|---|---|---|---:|---:|---|---|"]
    for row in rows:
        L.append("| " + " | ".join(str(x) for x in row) + " |")
    with open(a.out, "w") as f:
        f.write("\n".join(L) + "\n")
    print("\n".join(L))
    return True


def main(argv):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    b = sub.add_parser("build")
    b.add_argument("input")
    b.add_argument("--classes", required=True, choices=list(PARTITIONS))
    b.add_argument("--json", required=True)
    b.add_argument("-o", "--output")
    b.set_defaults(fn=cmd_build)
    o = sub.add_parser("opt")
    o.add_argument("input")
    o.add_argument("--classes", required=True, choices=list(PARTITIONS))
    o.add_argument("--eps", type=int, default=1, choices=[1, -1])
    o.add_argument("--slack", type=int, default=2)
    o.add_argument("--time", type=float, default=600.0)
    o.add_argument("--workers", type=int, default=8)
    o.set_defaults(fn=cmd_opt)
    s = sub.add_parser("sweep")
    s.add_argument("--out", required=True)
    s.add_argument("--machines")
    s.add_argument("--partitions")
    s.add_argument("--slack", type=int, default=2)
    s.add_argument("--time", type=float, default=600.0)
    s.add_argument("--workers", type=int, default=8)
    s.add_argument("--force", action="store_true")
    s.set_defaults(fn=cmd_sweep)
    m = sub.add_parser("summary")
    m.add_argument("--dir", required=True)
    m.add_argument("--out", required=True)
    m.set_defaults(fn=cmd_summary)
    u = sub.add_parser("mutate")
    u.add_argument("input")
    u.add_argument("--json", required=True)
    u.set_defaults(fn=cmd_mutate)
    a = ap.parse_args(argv)
    return 0 if a.fn(a) is not False else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
