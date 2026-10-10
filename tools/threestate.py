#!/usr/bin/env python3
"""3 状態化変換: 任意の 1 テープ RTM T を 3 状態の RTM T† に変換する（Morita 2017 §5.3.5 の系統）。

Morita の構成は 2 段:
  Lemma 5.9  T（m 状態 n 記号）→ one-way-updating RTM T̂（(m₊n+2n+2) 状態 (mn²+n²+1) 記号）
  Lemma 5.10 1WU-RTM（M 状態 N 記号）→ 3 状態 (2MN−N) 記号の RTM
この道具は両段を別々に選べるように実装する（詳細と記号数の式は docs/09_three_state_2026-09-26.md）。

1 段目 (--onewu):
  pair      Lemma 5.9 そのもの（T の 2 セルを 1 セルに詰め、毎掃引でテープを 1 セル右へずらす）
  single    本稿の構成。詰めずに 1 セル 1 記号のまま右へずらす。T の状態は
            Q₋ の状態ならヘッドのセルに [p,s]、Q₊ の状態ならヘッドの 1 つ左のセルに [p,v,+] として置く
            （Q₊ の状態には右移動でしか入らないので、書いた記号 v を運ぶ状態 r(p,v) と、
            読んだ印から v を運ぶ状態 g(p,v) の 2 族で足りる）
2 段目 (--counter):
  morita    Lemma 5.10 そのもの。計数記号は S×{1..M−1}×{↑,↓}（N(2M−1) 記号）
  shared    ↑ と ↓ を 1 種類にする（NM 記号）。往復中に L が読む計数は常に元セル側、R0/R1 が読む計数は
            常に行き先側なので、区別しなくても決定性・可逆性が保たれる
  pruned    shared のうち、実際に書かれる・読まれる計数記号 [x,k] だけを残す。k ≤ need(x),
            need(x) = max{ν(q) : q が x を読みうる、または x を書いて q に入る}。ν は Q̂₊ の番号付け

    python3 tools/threestate.py convert data/urtm/urtm32-3.txt --onewu pair --counter morita -o out/m.txt
    python3 tools/threestate.py convert data/urtm/urtm32-3.txt --onewu single --counter pruned -o out/s.txt
    python3 tools/threestate.py check data/urtm/urtm32-3.txt out/s.txt     # 逐段等価性（2 層）
    python3 tools/threestate.py onewu data/urtm/urtm32-3.txt --onewu single -o out/t1wu.txt  # 1WU 機械だけ
    python3 tools/threestate.py table data/urtm/urtm{10-8,13-7,15-6,17-5,24-4,32-3}.txt  # 記号数の表

T の 0 シフト停止規則 [p,s,t,0,halt] は Morita のファイルと同じく「規則なし（停止）」として扱う
（Morita の実機械の 0 シフト規則はすべて t = s なので停止テープは変わらない）。
"""

import argparse
import sys
from collections import defaultdict

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from check_urtm import parse  # noqa: E402
from kstate import Machine, PSEUDO  # noqa: E402
from simulate import maxstep_of  # noqa: E402

MOVE = {"-": -1, "0": 0, "+": 1}


def fresh(base, taken):
    name = base
    k = 0
    while name in taken:
        k += 1
        name = f"{base}{k}"
    return name


class TInfo:
    """T から 0 シフト規則を除いた T⁻ と、Q₊/Q₋ の分割。"""

    def __init__(self, T: Machine, twoway=False, mirrored=False):
        self.T = T
        self.twoway = twoway          # T を両側無限テープとして動かす（左端から落ちない）
        self.mirrored = mirrored      # T は mirror_machine で左右反転済み（出力時に方向を入れ替え直す）
        self.S = list(T.symbols)
        self.blank = T.blank
        self.rules = {}
        for (p, s, t, d, q) in T.quints:
            if d == "0":
                if q not in PSEUDO:
                    raise SystemExit(f"{T.name}: 0-shift rule into non-pseudo state {q}")
                continue          # 停止（規則なし）として扱う
            self.rules[(p, s)] = (t, d, q)
        dirs = defaultdict(set)
        for (p, s), (t, d, q) in self.rules.items():
            dirs[q].add(d)
        self.dir = {}
        for q in T.states:
            ds = dirs.get(q, set())
            if len(ds) > 1:
                raise SystemExit(f"{T.name}: state {q} entered with dirs {sorted(ds)} (not reversible)")
            self.dir[q] = next(iter(ds)) if ds else None   # None: 一度も入られない
        self.states = list(T.states)

    def step(self, conf):
        """T⁻ の 1 ステップ。conf = (state, pos, tape)。規則なしなら None、左端から落ちたら 'fell'。"""
        st, pos, tape = conf
        while pos >= len(tape):
            tape.append(self.blank)
        r = self.rules.get((st, tape[pos]))
        if r is None:
            return None
        t, d, q = r
        tape[pos] = t
        pos += MOVE[d]
        if pos < 0:
            if not self.twoway:
                return "fell"
            tape.insert(0, self.blank)
            pos = 0
        return (q, pos, tape)


def mirror_machine(T: Machine):
    """T を左右反転する（規則の方向を入れ替え、初期配置のテープを逆順にする）。
    反転した T の 3 状態化の方向を入れ替え直せば、元の T を模倣する 3 状態機械になる（記号数は同じ）。"""
    sw = {"+": "-", "-": "+", "0": "0"}
    T.quints = [(p, s, t, sw[d], q) for (p, s, t, d, q) in T.quints]
    T.delta = {(p, s): (t, d, q) for (p, s, t, d, q) in T.quints}
    cases = []
    for (st, pos, tape, steps, out) in T.cases:
        tape = list(tape) + [T.blank] * max(0, pos + 1 - len(tape))
        cases.append((st, len(tape) - 1 - pos, tape[::-1], steps, out))
    T.cases = cases
    return T


def norm_T(state, cells, head, blank):
    """T の配置の正規形: 両端の空白を落とし、ヘッドの相対位置で持つ（両側無限テープとして比べる）。"""
    cells = list(cells)
    while head >= len(cells):
        cells.append(blank)
    if head < 0:
        cells = [blank] * (-head) + cells
        head = 0
    lo = 0
    while lo < head and cells[lo] == blank:
        lo += 1
    hi = len(cells)
    while hi > head + 1 and cells[hi - 1] == blank:
        hi -= 1
    return (state, head - lo, tuple(cells[lo:hi]))


# ================================================================ 1 段目: 1WU-RTM
class OneWU:
    """1WU-RTM の共通部分。states[0] が qL。reads[q] は「q が読みうる記号」（停止する読みを含む）。"""

    s0: str
    qL: str
    states: list
    symbols: list
    quints: list
    reads: dict

    def delta(self):
        return {(p, s): (t, d, q) for (p, s, t, d, q) in self.quints}

    def check_1wu(self):
        """Def. 5.20 の条件 1〜5 を機械的に確かめる。問題の列を返す（空なら OK）。"""
        probs = []
        qplus = [q for q in self.states if q != self.qL]
        into = defaultdict(set)
        for (p, s, t, d, q) in self.quints:
            if q in self.states:
                into[q].add(d)
        # 1: Q̂₋ = {qL}
        for q in qplus:
            if "-" in into[q]:
                probs.append(f"cond1: {q} entered by a left move")
        if into[self.qL] - {"-"}:
            probs.append("cond1: qL entered by a non-left move")
        dl = self.delta()
        # 2, 3
        for s in self.symbols:
            r = dl.get((self.qL, s))
            if s != self.s0 and r != (s, "-", self.qL):
                probs.append(f"cond2: qL on {s}: {r}")
        r = dl.get((self.qL, self.s0))
        if not r or r[0] != self.s0 or r[1] != "+" or r[2] == self.qL:
            probs.append(f"cond3: qL on s0: {r}")
        for (p, s, t, d, q) in self.quints:
            if p == self.qL:
                continue
            if t != self.s0 and not (d == "+" and q != self.qL):
                probs.append(f"cond4: {[p, s, t, d, q]}")
            if t == self.s0 and not (s == self.s0 and d == "-" and q == self.qL):
                probs.append(f"cond5: {[p, s, t, d, q]}")
        return probs

    def emit(self, out, title, cases=()):
        L = [f"title('{title}').", f"initial_state({self.qL}).", "final_states([]).",
             f"states([{','.join(self.states)}]).", f"symbols([{','.join(self.symbols)}]).",
             f"blank({self.s0}).", "maxstep(10000000)."]
        for (st, pos, tape) in cases:
            L.append(f"initial_conf([{st},{pos},[{','.join(tape)}]]).")
        L += [f"[{p},{s},{t},{d},{q}]." for (p, s, t, d, q) in self.quints]
        out.write("\n".join(L) + "\n")


class PairWU(OneWU):
    """Morita 2017 Lemma 5.9。命名と番号付けは Morita の urtm3-36654 のコメントに合わせる
    （状態 0 = qL、以下 h(s), q(s)/q(λ), q(p,s) を名前順に番号付け）。"""

    kind = "pair"

    def __init__(self, ti: TInfo):
        self.ti = ti
        S = sorted(ti.S)
        b = ti.blank
        self.s0 = b
        Qplus = sorted(q for q in ti.states if ti.dir[q] != "-")   # 入られない状態は Q₊（Morita と同じ）
        self.Qplus = Qplus
        lam = "lambda"
        names = [("h", s) for s in S] + [("q", s) for s in sorted(S + [lam])] + \
                [("qp", p, s) for p in Qplus for s in S]
        self.num = {nm: i + 1 for i, nm in enumerate(names)}
        self.qL = "0"
        st = lambda nm: str(self.num[nm])  # noqa: E731
        self.name_of = {str(v): k for k, v in self.num.items()}
        P = lambda s, t: f"[{s},{t}]"  # noqa: E731
        Mk = lambda p, s, t: f"[[q_{p},{s}],{t}]"  # noqa: E731
        self.P, self.Mk = P, Mk
        self.symbols = [b] + [P(s, t) for s in S for t in S] + [Mk(p, s, t) for p in sorted(ti.states) for s in S for t in S]
        defined = lambda p, s: (p, s) in ti.rules  # noqa: E731
        R = []
        R.append((self.qL, b, b, "+", st(("q", b))))                                     # δ1
        for s in S:
            for t in S:
                for u in S:
                    R.append((st(("q", s)), P(t, u), P(s, t), "+", st(("q", u))))        # δ2
        for (p, t), (t2, d, p2) in sorted(ti.rules.items()):
            for s in S:
                for u in S:
                    if d == "-":
                        nxt = ("q", u) if defined(p2, s) else ("h", u)                 # δ3 / δ4
                        R.append((st(("q", s)), Mk(p, t, u), Mk(p2, s, t2), "+", st(nxt)))
                    else:
                        R.append((st(("q", s)), Mk(p, t, u), P(s, t2), "+", st(("qp", p2, u))))  # δ5
        for p2 in Qplus:
            for u in S:
                for s in S:
                    for t in S:
                        nxt = ("q", t) if defined(p2, u) else ("h", t)                     # δ6 / δ7
                        R.append((st(("qp", p2, u)), P(s, t), Mk(p2, u, s), "+", st(nxt)))
        for s in S:
            R.append((st(("q", s)), b, P(s, b), "+", st(("q", lam))))                    # δ8
        R.append((st(("q", lam)), b, b, "-", self.qL))                                    # δ9
        for x in self.symbols[1:]:
            R.append((self.qL, x, x, "-", self.qL))                                       # δ10, δ11
        for s in S:
            for t in S:
                for u in S:
                    R.append((st(("h", s)), P(t, u), P(s, t), "+", st(("h", u))))        # δ12
        self.quints = R
        self.states = [self.qL] + [str(i) for i in range(1, len(names) + 1)]
        plain = {P(s, t) for s in S for t in S}
        markers = set(self.symbols[1 + len(plain):])
        self.reads = {}
        for nm, i in self.num.items():
            if nm[0] == "q" and nm[1] != lam:
                self.reads[str(i)] = set(self.symbols)                 # q(s): 対・印・s0
            elif nm[0] == "q":
                self.reads[str(i)] = {b}                               # q(λ)
            elif nm[0] == "h":
                self.reads[str(i)] = plain | {b}                       # h(s): 対と右端
            else:
                self.reads[str(i)] = plain                             # q(p,u): 印の直後は常に対
        self.reads[self.qL] = set(self.symbols)
        self.markers = markers

    # -- 符号化 / 復号
    def encode(self, state, pos, tape):
        b = self.s0
        tape = list(tape)
        while pos >= len(tape):
            tape.append(b)
        left = tape[:pos]
        right = tape[pos:]
        if len(left) % 2:
            left = [b] + left
        while len(right) < 4 or len(right) % 2:
            right.append(b)
        cells = [b] + [self.P(left[i], left[i + 1]) for i in range(0, len(left), 2)]
        cells.append(self.Mk(state, right[0], right[1]))
        cells += [self.P(right[i], right[i + 1]) for i in range(2, len(right), 2)]
        return (self.qL, 0, cells)

    def _split(self, x):
        from check_urtm import split_top
        a, c = split_top(x[1:-1])
        if a.startswith("["):
            p, s = split_top(a[1:-1])
            return p[2:], s, c
        return None, a, c

    def decode(self, st, pos, tape):
        """T̂ の配置 → T の正規形。掃引の開始点 (qL@0) と停止配置で呼ぶ。"""
        b = self.s0
        tape = list(tape)
        while pos >= len(tape):
            tape.append(b)
        carried = None
        if st != self.qL:
            nm = self.name_of[st]
            if nm[0] in ("q", "h") and nm[1] != "lambda":
                carried = nm[1]
            elif nm[0] == "q":
                carried = None
            else:
                return None
        cells, head, state = [], None, None
        for i, x in enumerate(tape):
            if i == 0 and x == b:
                continue
            if i == pos and carried is not None:
                cells.append(carried)
            if x == b:
                cells.append(b)
                continue
            p, s, c = self._split(x)
            if p is not None:
                head, state = len(cells), p
            cells += [s, c]
        if carried is not None and pos >= len(tape):
            cells.append(carried)
        if head is None:
            return None
        return norm_T(state, cells, head, b)


class SingleWU(OneWU):
    """本稿の 1WU 化（対にしない版）。"""

    kind = "single"

    def __init__(self, ti: TInfo):
        self.ti = ti
        T = ti.T
        S = list(ti.S)
        b = ti.blank
        self.s0 = b
        taken = set(S) | set(T.states) | set(PSEUDO)
        B = fresh(b + "_", taken)
        taken.add(B)
        self.plain = {s: (B if s == b else s) for s in S}
        self.unplain = {v: k for k, v in self.plain.items()}
        pl = self.plain
        # Q₊/Q₋: 入られない状態は Q₋ に置く（印をヘッドに置けて安い）
        self.minus = [q for q in T.states if ti.dir[q] != "+"]
        self.plus = [q for q in T.states if ti.dir[q] == "+"]
        Rset = sorted({(q, t) for (p, s), (t, d, q) in ti.rules.items() if d == "+"})
        # 初期状態が Q₊ にあれば、任意の左隣の記号で始められるよう g(p0, x) を全部用意する
        init = T.initial_state
        Gset = set(Rset)
        if init in self.plus:
            Gset |= {(init, s) for s in S}
        Gset = sorted(Gset)
        self.Rset, self.Gset = Rset, Gset
        self.qL = fresh("qL", taken)
        taken.add(self.qL)
        c = {s: f"c({pl[s]})" for s in S}
        e1, e2 = "e1", "e2"
        r = {(p, v): f"r({p},{pl[v]})" for (p, v) in Rset}
        g = {(p, v): f"g({p},{pl[v]})" for (p, v) in Gset}
        self.c, self.r, self.g = c, r, g
        mk = {(p, s): f"[{p},{pl[s]}]" for p in self.minus for s in S}
        mkp = {(p, v): f"[{p},{pl[v]},+]" for (p, v) in Gset}
        self.mk, self.mkp = mk, mkp
        self.symbols = [b] + [pl[s] for s in S] + list(mk.values()) + list(mkp.values())
        self.states = [self.qL] + [c[s] for s in S] + [e1, e2] + list(r.values()) + list(g.values())
        rules = ti.rules
        Rq = []
        Rq.append((self.qL, b, b, "+", c[b]))
        for x in self.symbols[1:]:
            Rq.append((self.qL, x, x, "-", self.qL))
        for s in S:
            for x in S:
                Rq.append((c[s], pl[x], pl[s], "+", c[x]))                   # ずらす
            Rq.append((c[s], b, pl[s], "+", e1))                               # 右端: 運んだ記号を書く
            for p in self.minus:                                               # Q₋ の印（ヘッドのセル）
                for u in S:
                    rr = rules.get((p, u))
                    if rr is None:
                        continue                                               # T は停止
                    t, d, q = rr
                    if d == "-":
                        Rq.append((c[s], mk[(p, u)], mk[(q, s)], "+", c[t]))
                    else:
                        Rq.append((c[s], mk[(p, u)], pl[s], "+", r[(q, t)]))
            for (p, v) in Gset:                                                # Q₊ の印（ヘッドの左）
                Rq.append((c[s], mkp[(p, v)], pl[s], "+", g[(p, v)]))
        Rq.append((e1, b, pl[b], "+", e2))                                     # 右端にもう 1 つ空白
        Rq.append((e2, b, b, "-", self.qL))
        for (p, v) in Rset:
            for x in S:
                Rq.append((r[(p, v)], pl[x], mkp[(p, v)], "+", c[x]))          # 印をヘッドの左に置く
        for (p, v) in Gset:
            for u in S:
                rr = rules.get((p, u))
                if rr is None:
                    continue
                t, d, q = rr
                if d == "-":
                    Rq.append((g[(p, v)], pl[u], mk[(q, v)], "+", c[t]))
                else:
                    Rq.append((g[(p, v)], pl[u], pl[v], "+", r[(q, t)]))
        self.quints = Rq
        plains = {pl[s] for s in S}
        marks = set(mk.values()) | set(mkp.values())
        self.reads = {self.qL: set(self.symbols), e1: {b}, e2: {b}}
        for s in S:
            self.reads[c[s]] = plains | marks | {b}
        for x in r.values():
            self.reads[x] = set(plains)
        for x in g.values():
            self.reads[x] = set(plains)
        self.markers = marks
        # 復号用
        self.cstate = {v: k for k, v in c.items()}
        self.gstate = {v: k for k, v in g.items()}
        self.mk_inv = {v: k for k, v in mk.items()}
        self.mkp_inv = {v: k for k, v in mkp.items()}

    def encode(self, state, pos, tape):
        b = self.s0
        tape = list(tape)
        while pos + 2 > len(tape):
            tape.append(b)
        cells = [b, self.plain[b]] + [self.plain[x] for x in tape]   # 左に 1 セル余白
        h = pos + 2
        if state in self.minus:
            cells[h] = self.mk[(state, tape[pos])]
        else:
            cells[h - 1] = self.mkp[(state, tape[pos - 1] if pos >= 1 else b)]
        return (self.qL, 0, cells)

    def decode(self, st, pos, tape):
        b = self.s0
        tape = list(tape)
        while pos >= len(tape):
            tape.append(b)
        carried = None
        extra_head = None
        if st != self.qL:
            if st in self.cstate:
                carried = self.cstate[st]
            elif st in self.gstate:
                p, v = self.gstate[st]
                carried = v
                extra_head = p
            else:
                return None
        cells, head, state = [], None, None
        for i, x in enumerate(tape):
            if i == 0:
                continue
            if i == pos and carried is not None:
                cells.append(carried)
                if extra_head is not None:
                    head, state = len(cells), extra_head
            if x == b:
                cells.append(b)
            elif x in self.unplain:
                cells.append(self.unplain[x])
            elif x in self.mk_inv:
                p, s = self.mk_inv[x]
                head, state = len(cells), p
                cells.append(s)
            elif x in self.mkp_inv:
                p, v = self.mkp_inv[x]
                cells.append(v)
                head, state = len(cells), p
            else:
                return None
        if head is None:
            return None
        return norm_T(state, cells, head, b)


ONEWU = {"pair": PairWU, "single": SingleWU}


# ================================================================ 2 段目: 3 状態
class ThreeState:
    def __init__(self, W: OneWU, counter="pruned", order="auto"):
        self.W = W
        self.mirror = W.ti.mirrored
        if counter != "pruned":
            order = "given"          # morita / shared は記号数が番号付けに依らない。Morita の番号をそのまま使う
        self.counter = counter
        b = W.s0
        self.s0 = b
        qplus = [q for q in W.states if q != W.qL]
        self.nu = self._numbering(qplus, order)
        M1 = len(qplus)
        dl = W.delta()
        # need(x): 計数記号 [x,k] を k = 1..need(x) だけ用意する
        need = defaultdict(int)
        if counter == "pruned":
            for q in qplus:
                for x in W.reads[q]:
                    need[x] = max(need[x], self.nu[q])
            for (p, s, t, d, q) in W.quints:
                if q in self.nu:
                    need[t] = max(need[t], self.nu[q])
        else:
            for x in W.symbols:
                need[x] = M1
        self.need = need
        L, R0, R1 = "l", "r0", "r1"
        self.states = [L, R0, R1]
        if counter == "morita":
            up = lambda x, k: f"[{x},{k},u]"  # noqa: E731
            dn = lambda x, k: f"[{x},{k},d]"  # noqa: E731
        else:
            up = dn = lambda x, k: f"[{x},{k},c]"  # noqa: E731
        self.up, self.dn = up, dn
        syms = list(W.symbols)
        if counter == "morita":
            syms += [up(x, k) for x in W.symbols for k in range(1, M1 + 1)]
            syms += [dn(x, k) for x in W.symbols for k in range(1, M1 + 1)]
        else:
            syms += [up(x, k) for x in W.symbols for k in range(1, need[x] + 1)]
        self.symbols = syms
        have = set(syms)
        nu = self.nu
        Rq = []
        j0 = dl[(W.qL, b)][2]
        Rq.append((L, b, dn(b, nu[j0]), "+", R0))                                   # δ1
        for (p, s, t, d, q) in W.quints:
            if p == W.qL:
                continue
            if d == "+":
                Rq.append((R0, up(s, nu[p]), dn(t, nu[q]), "+", R0))                # δ2
            else:
                Rq.append((R0, up(s, nu[p]), s, "-", L))                            # δ7
        for u in W.symbols:
            if up(u, 1) in have:
                Rq.append((R0, u, up(u, 1), "-", L))                                # δ3
        for x in W.symbols:
            hi = M1 if counter != "pruned" else need[x]
            for k in range(2, hi + 1):
                Rq.append((L, dn(x, k), dn(x, k - 1), "+", R1))                     # δ4
            for k in range(1, hi):
                Rq.append((R1, up(x, k), up(x, k + 1), "-", L))                     # δ5
            if dn(x, 1) in have:
                Rq.append((L, dn(x, 1), x, "+", R0))                                # δ6
        for x in W.symbols:
            if x != b:
                Rq.append((L, x, x, "-", L))                                        # δ8
        self.quints = Rq
        missing = sorted({z for r in Rq for z in (r[1], r[2])} - have)
        if missing:
            raise SystemExit(f"internal: symbols used but not generated: {missing[:5]}")

    def _numbering(self, qplus, order):
        """Q̂₊ の番号付け ν。pruned の記号数は N + Σ_x need(x), need(x) = max{ν(q) : x ∈ U(q)}。
        U(q) = q が読みうる記号 ∪ q に入るとき書かれる記号。

        order="given": 1WU 機械の状態の並び順のまま（pair は Morita の番号、single は c, e, r, g の順）。
        order="auto" : U(q) が同じ状態を 1 群にまとめ、群の並べ方を全部試して総和を最小にする。
          群の中の並びは総和に効かず、また同じ U の状態を隣り合わせても総和は増えない
          （a > c > b の位置で U(a) = U(b) なら b と c を入れ替えても U(b) の記号の最大は pos(a) のまま、
          c の記号は下がるだけ）ので、群の数が 8 以下ならこれで全順序の中の最小になる。
        """
        import itertools
        W = self.W
        if order == "given":
            return {q: i + 1 for i, q in enumerate(qplus)}
        U = {q: set(W.reads[q]) for q in qplus}
        for (p, s, t, d, q) in W.quints:
            if q in U:
                U[q].add(t)
        groups = {}
        for q in qplus:
            groups.setdefault(frozenset(U[q]), []).append(q)
        keys = list(groups)
        if len(keys) > 8:
            raise SystemExit(f"{len(keys)} groups: exhaustive ordering not implemented")

        def cost(seq):
            need = {}
            pos = 0
            for key in seq:
                pos += len(groups[key])
                for x in key:
                    need[x] = pos
            return sum(need.values())

        best = min(itertools.permutations(keys), key=cost)
        seq = [q for key in best for q in groups[key]]
        return {q: i + 1 for i, q in enumerate(seq)}

    def cost(self, rule):
        """1WU の規則 1 本を模倣する T† のステップ数。"""
        p, s, t, d, q = rule
        if d == "-":
            return 1
        return 2 * self.nu[q] + 1

    def encode(self, st, pos, tape):
        tape = list(tape)
        while pos >= len(tape):
            tape.append(self.s0)
        if st == self.W.qL:
            return ("l", pos, tape)
        tape[pos] = self.up(tape[pos], self.nu[st])
        return ("r0", pos, tape)

    def title(self):
        return (f"threestate onewu={self.W.kind} counter={self.counter} mirror={int(self.mirror)} from {self.W.ti.T.name}: "
                f"{len(self.W.ti.states)} states {len(self.W.ti.S)} symbols -> 1WU {len(self.W.states)} states "
                f"{len(self.W.symbols)} symbols -> 3 states {len(self.symbols)} symbols")

    SWAP = {"+": "-", "-": "+", "0": "0"}

    def output_quints(self):
        """ファイルに書く規則。mirror のときは T^R 用に作った規則の方向を入れ替え直し、元の T を模倣する機械にする。"""
        if not self.mirror:
            return list(self.quints)
        return [(p, s, t, self.SWAP[d], q) for (p, s, t, d, q) in self.quints]

    def decode_to_T(self, st, pos, tape):
        """T†（入れ替え直す前の向き）の停止配置 → T（mirror なら T^R）の正規形。"""
        W = self.W
        tape = list(tape)
        while pos >= len(tape):
            tape.append(self.s0)
        if st == "l":
            wst = W.qL
        else:
            from check_urtm import split_top
            x, k, _ = split_top(tape[pos][1:-1])
            inv = {v: q for q, v in self.nu.items()}
            wst = inv[int(k)]
            tape[pos] = x
        return W.decode(wst, pos, tape)

    def standalone_conf(self, state, pos, tape, maxstep):
        """T の配置 (state, pos, tape)（mirror なら T.cases は反転済み）から、ファイルに書く T† の初期配置と、
        T† 単体で走らせた結果を返す。mirror のときはテープを逆順にし、T† が左へ伸ばす分だけ左に空白を詰める
        （右無限テープのシミュレータで位置が負にならないように。詰める量は実際に走らせた最大位置から決める）。"""
        W = self.W
        st, ps, tp = self.encode(*W.encode(state, pos, tape))
        delta = {(p, s): (t, d, q) for (p, s, t, d, q) in self.quints}
        steps, why, final, hi = run_track(delta, self.s0, (st, ps, tp), maxstep)
        if not self.mirror:
            return (st, ps, tp), steps, why, final
        n = len(tp)
        pad = max(0, hi - (n - 1))
        rtp = [self.s0] * pad + tp[::-1]
        return (st, pad + n - 1 - ps, rtp), steps, why, final

    def emit(self, out, maxstep):
        W = self.W
        T = W.ti.T
        orient = ("元の T を模倣する（T^R を変換した機械の方向を入れ替え直したもの。テープは左へ伸びるので、"
                  "初期配置の左に必要な数だけ空白を詰めてある）" if self.mirror else "元の T を模倣する")
        L = [f"title('{self.title()}').",
             "% 生成: tools/threestate.py（docs/09_three_state_2026-09-26.md）",
             f"% {orient}。各 initial_conf は、T の記述ファイルの初期配置を符号化したもの（同じ順）。",
             "% %% 行は T† 単体で走らせた停止ステップ数（maxstep までに止まらなければ null）。",
             "% 直後の % T: 行は、T† の停止配置を T の配置に復号したもの（状態@ヘッド位置 テープ）。",
             "initial_state(l).", "final_states([]).", "states([l,r0,r1]).",
             f"symbols([{','.join(self.symbols)}]).", f"blank({self.s0}).", f"maxstep({maxstep})."]
        for (state, pos, tape, _, _) in T.cases:
            (st, ps, tp), steps, why, final = self.standalone_conf(state, pos, tape, maxstep)
            L.append(f"initial_conf([{st},{ps},[{','.join(tp)}]]).")
            if why == "halt":
                L.append(f"%% {steps}")
                dec = self.decode_to_T(*final)
                if dec is not None:
                    dst, dh, cells = dec
                    if self.mirror:
                        cells, dh = cells[::-1], len(cells) - 1 - dh
                    L.append(f"% T: {dst}@{dh} {' '.join(cells)}")
            else:
                L.append(f"%% null (maxstep {maxstep} reached; T† does not halt within maxstep)")
        L += [f"[{p},{s},{t},{d},{q}]." for (p, s, t, d, q) in self.output_quints()]
        out.write("\n".join(L) + "\n")


def run_track(delta, blank, conf, limit):
    """run_count と同じ数え方で走らせ、(steps, why, 最終配置, 到達した最大位置) を返す。"""
    st, pos, tape = conf
    tape = list(tape)
    hi = pos
    for k in range(limit + 1):
        while pos >= len(tape):
            tape.append(blank)
        r = delta.get((st, tape[pos]))
        if r is None:
            return k, "halt", (st, pos, tape), hi
        if k == limit:
            break
        t, d, q = r
        tape[pos] = t
        pos += MOVE[d]
        st = q
        hi = max(hi, pos)
        if pos < 0:
            return k + 1, "fell", (st, pos, tape), hi
    return limit, "maxstep", (st, pos, tape), hi


def step(delta, blank, conf):
    st, pos, tape = conf
    while pos >= len(tape):
        tape.append(blank)
    r = delta.get((st, tape[pos]))
    if r is None:
        return None
    t, d, q = r
    tape[pos] = t
    pos += MOVE[d]
    if pos < 0:
        return "fell"
    return (q, pos, tape)


def run_count(delta, blank, conf, limit):
    st, pos, tape = conf
    tape = list(tape)
    for k in range(limit + 1):
        while pos >= len(tape):
            tape.append(blank)
        r = delta.get((st, tape[pos]))
        if r is None:
            return k, "halt"
        if k == limit:
            break
        t, d, q = r
        tape[pos] = t
        pos += MOVE[d]
        st = q
        if pos < 0:
            return k + 1, "fell"
    return limit, "maxstep"


def _trim(tape, blank):
    tape = list(tape)
    while tape and tape[-1] == blank:
        tape.pop()
    return tape


# ================================================================ 逐段等価性
def lockstep_T_W(W: OneWU, state, pos, tape, max_t_steps, max_w_steps=10 ** 8):
    """T⁻ の 1 ステップ ⇔ W の 1 掃引。掃引の開始点 (qL@0 で s0 を読む) ごとに W を復号して T と比べる。

    返り値 (ok, t_steps, w_steps, reason, w_trace)。w_trace は W の規則の列（2 段目の検査に使う）ではなく、
    W の初期配置（2 段目は同じ初期配置から独立に走らせる）。
    """
    ti = W.ti
    b = ti.blank
    dw = W.delta()
    t_conf = (state, pos, list(tape))
    w_conf = W.encode(state, pos, tape)
    exp = norm_T(state, tape, pos, b)
    got = W.decode(*w_conf)
    if got != exp:
        return False, 0, 0, f"initial decode mismatch: {got} vs {exp}"
    ts = ws = 0
    while True:
        # W を次の掃引の開始点（または停止）まで進める
        first = True
        while True:
            st, ps, tp = w_conf
            if not first and st == W.qL and ps == 0:
                break
            first = False
            nxt = step(dw, W.s0, w_conf)
            if nxt is None:
                break
            if nxt == "fell":
                return False, ts, ws, "W fell off the left end"
            w_conf = nxt
            ws += 1
            if ws > max_w_steps:
                return True, ts, ws, "W step budget reached (still in lockstep)"
        halted_w = not (w_conf[0] == W.qL and w_conf[1] == 0)
        if halted_w:
            # pair 版は T の最後のステップを実行した掃引の中で停止する（δ̂4/δ̂7 → h(u) → 右端で停止）。
            # single 版は最後のステップの次の掃引で、印を読んだところで停止する。
            nt = ti.step((t_conf[0], t_conf[1], list(t_conf[2])))
            if nt == "fell":
                return True, ts, ws, "T fell off the left end (W simulates a two-way tape; stop here)"
            if nt is not None and W.kind == "pair":
                t_conf = nt
                ts += 1
                nt = ti.step((t_conf[0], t_conf[1], list(t_conf[2])))
            if nt is not None:
                return False, ts, ws, f"W halted but T continues at T step {ts}"
            got = W.decode(*w_conf)
            exp = norm_T(t_conf[0], t_conf[2], t_conf[1], b)
            if got != exp:
                return False, ts, ws, f"halt decode mismatch at T step {ts}: W={got} T={exp}"
            return True, ts, ws, "both halt"
        if True:
            nt = ti.step(t_conf)
            if nt is None:
                return False, ts, ws, f"T halted at step {ts} but W completed a sweep"
            if nt == "fell":
                return True, ts, ws, "T fell off the left end (W simulates a two-way tape; stop here)"
            t_conf = nt
            ts += 1
            got = W.decode(*w_conf)
            exp = norm_T(t_conf[0], t_conf[2], t_conf[1], b)
            if got != exp:
                return False, ts, ws, f"decode mismatch after T step {ts}: W={got} T={exp}"
            if ts >= max_t_steps:
                return True, ts, ws, "T step budget reached (still in lockstep)"


def lockstep_W_3(TS: ThreeState, delta3, w_conf, max_w_steps):
    """W の 1 ステップ ⇔ T† の cost(規則) ステップ。各区切りで T† の配置が encode(W の配置) と完全一致するか。"""
    W = TS.W
    dw = W.delta()
    b = W.s0
    p_conf = TS.encode(*w_conf)
    w_conf = (w_conf[0], w_conf[1], list(w_conf[2]))
    ws = ps_ = 0
    while ws < max_w_steps:
        st, pos, tp = w_conf
        while pos >= len(tp):
            tp.append(b)
        r = dw.get((st, tp[pos]))
        if r is None:
            if step(delta3, b, (p_conf[0], p_conf[1], list(p_conf[2]))) is not None:
                return False, ws, ps_, f"W halted at W step {ws} but T† has a rule at {p_conf[0]}@{p_conf[1]}"
            return True, ws, ps_, "both halt"
        cost = TS.cost((st, tp[pos]) + r)
        for k in range(cost):
            nxt = step(delta3, b, p_conf)
            if nxt is None or nxt == "fell":
                return False, ws, ps_, f"T† stopped ({nxt}) inside W step {ws + 1} (sub-step {k + 1}/{cost})"
            p_conf = nxt
            ps_ += 1
        w_conf = step(dw, b, w_conf)
        ws += 1
        exp = TS.encode(*w_conf)
        if (p_conf[0], p_conf[1]) != (exp[0], exp[1]) or _trim(p_conf[2], b) != _trim(exp[2], b):
            return False, ws, ps_, f"mismatch after W step {ws}: T†={p_conf[0]}@{p_conf[1]} vs {exp[0]}@{exp[1]}"
    return True, ws, ps_, "W step budget reached (still in lockstep)"


def build(path, onewu, counter, order="auto", mirror=False):
    T = Machine(path)
    if mirror:
        mirror_machine(T)
    ti = TInfo(T, twoway=mirror, mirrored=mirror)
    W = ONEWU[onewu](ti)
    return T, ti, W, ThreeState(W, counter, order)


def check_all(T, W, TS, delta3, max_t_steps, max_w_steps=None):
    """初期配置ごとに 2 層の逐段等価性を検査する。(ok, 行) の列。"""
    out = []
    for k, (state, pos, tape, exp_steps, exp_out) in enumerate(T.cases):
        ok1, ts, ws, why1 = lockstep_T_W(W, state, pos, tape, max_t_steps)
        budget = max_w_steps if max_w_steps else ws + 1
        ok2, ws2, ps, why2 = lockstep_W_3(TS, delta3, W.encode(state, pos, tape), budget)
        # T が停止した例では 2 層目も同じ W ステップ数で停止していなければならない
        if ok2 and why1 == "both halt" and not (why2 == "both halt" and ws2 == ws):
            ok2, why2 = False, f"W halts after {ws} steps but 3-state check says {why2} at {ws2}"
        ok = ok1 and ok2
        out.append((ok, f"{'ok ' if ok else 'NG '}{T.name} case{k}: T {ts} steps (file: {exp_steps}); "
                        f"1WU {ws} steps [{why1}]; T† {ps} steps [{why2}]"))
    return out


# ================================================================ CLI
def cmd_convert(a):
    T, ti, W, TS = build(a.input, a.onewu, a.counter, a.order, a.mirror)
    probs = W.check_1wu()
    if probs:
        print("1WU conditions violated:", probs[:5], file=sys.stderr)
        return False
    with (open(a.output, "w") if a.output else sys.stdout) as out:
        TS.emit(out, a.maxstep)
    print(f"{T.name}: m={len(ti.states)} n={len(ti.S)} -> 1WU[{a.onewu}] M={len(W.states)} N={len(W.symbols)} "
          f"|δ̂|={len(W.quints)} -> 3 states, counter={a.counter}: n'={len(TS.symbols)} |δ†|={len(TS.quints)}",
          file=sys.stderr)
    return True


def cmd_onewu(a):
    T = Machine(a.input)
    W = ONEWU[a.onewu](TInfo(T))
    probs = W.check_1wu()
    cases = [W.encode(st, pos, tp) for (st, pos, tp, _, _) in T.cases]
    with (open(a.output, "w") if a.output else sys.stdout) as out:
        W.emit(out, f"1WU[{a.onewu}] of {T.name}: {len(W.states)} states {len(W.symbols)} symbols", cases)
    print(f"1WU[{a.onewu}] of {T.name}: M={len(W.states)} N={len(W.symbols)} |δ̂|={len(W.quints)}; "
          f"Def 5.20: {'OK' if not probs else probs[:3]}", file=sys.stderr)
    return not probs


def cmd_check(a):
    import re
    from simulate import fact_of
    title = fact_of(a.output, "title", "") or ""
    onewu = re.search(r"onewu=(\S+)", title).group(1)
    counter = re.search(r"counter=(\S+)", title).group(1)
    mm = re.search(r"mirror=(\d)", title)
    T, ti, W, TS = build(a.input, onewu, counter, a.order, bool(mm and mm.group(1) == "1"))
    _, _, q3 = parse(a.output)
    if sorted(q3) != sorted(TS.output_quints()):
        print(f"NG {a.output}: rule set differs from a fresh regeneration")
        return False
    # 逐段検査は入れ替え直す前の向きで行う（mirror なら T^R に対して。方向の入れ替えは全単射なので同値）
    delta3 = {(p, s): (t, d, q) for (p, s, t, d, q) in TS.quints}
    allok = True
    mt = a.max_t_steps if a.max_t_steps else maxstep_of(a.input)
    for ok, line in check_all(T, W, TS, delta3, mt):
        allok &= ok
        print(line)
    # ファイルの initial_conf が T の初期配置の符号化であり、%% 行が T† 単体の停止ステップ数であること
    from simulate import read_cases as rc
    fcases = rc(a.output)
    if len(fcases) != len(T.cases):
        print(f"NG {a.output}: {len(fcases)} initial_conf vs {len(T.cases)} cases in {a.input}")
        return False
    fmax = maxstep_of(a.output)
    for k, ((state, pos, tape, _, _), (fst, fpos, ftape, fsteps, _)) in enumerate(zip(T.cases, fcases)):
        (st, ps, tp), steps, why, _ = TS.standalone_conf(state, pos, tape, fmax)
        same = (st, ps, list(tp)) == (fst, fpos, list(ftape))
        exp = steps if why == "halt" else None
        good = same and fsteps == exp
        allok &= good
        print(f"{'ok ' if good else 'NG '}file case{k}: initial_conf {'matches' if same else 'DIFFERS FROM'} "
              f"the encoding of T case{k}; %% {fsteps} vs T† standalone {steps} [{why}]")
    return allok


def cmd_table(a):
    print("| 入力 | m | m₊ | m₋ | n | 1WU | M | N | 3 状態の記号数 |δ†| |")
    print("|---|---:|---:|---:|---:|---|---:|---:|---:|---:|")
    for path in a.inputs:
        for onewu, counter, mir in [("pair", "morita", 0), ("pair", "shared", 0), ("pair", "pruned", 0),
                                    ("single", "morita", 0), ("single", "shared", 0), ("single", "pruned", 0),
                                    ("single", "pruned", 1)]:
            T, ti, W, TS = build(path, onewu, counter, "auto", bool(mir))
            mp = sum(1 for q in ti.states if ti.dir[q] == "+")
            print(f"| {T.name} | {len(ti.states)} | {mp} | {len(ti.states) - mp} | {len(ti.S)} | {onewu}/{counter}{'/mirror' if mir else ''} | "
                  f"{len(W.states)} | {len(W.symbols)} | {len(TS.symbols)} | {len(TS.quints)} |")
    return True


def main(argv):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    c = sub.add_parser("convert")
    c.add_argument("input")
    c.add_argument("-o", "--output")
    c.add_argument("--onewu", default="single", choices=sorted(ONEWU))
    c.add_argument("--counter", default="pruned", choices=["morita", "shared", "pruned"])
    c.add_argument("--order", default="auto", choices=["auto", "given"])
    c.add_argument("--maxstep", type=int, default=50_000_000)
    c.add_argument("--mirror", action="store_true",
                   help="T を左右反転した T^R を変換し、方向を入れ替え直して出力する（出力は元の T を模倣する。"
                        "テープは左へ伸びるので、初期配置は左に空白を詰めて右無限テープで走るように置く）")
    c.set_defaults(fn=cmd_convert)
    w = sub.add_parser("onewu")
    w.add_argument("input")
    w.add_argument("-o", "--output")
    w.add_argument("--onewu", default="single", choices=sorted(ONEWU))
    w.set_defaults(fn=cmd_onewu)
    k = sub.add_parser("check")
    k.add_argument("input")
    k.add_argument("output")
    k.add_argument("--order", default="auto", choices=["auto", "given"])
    k.add_argument("--max-t-steps", type=int, default=None)
    k.set_defaults(fn=cmd_check)
    t = sub.add_parser("table")
    t.add_argument("inputs", nargs="+")
    t.set_defaults(fn=cmd_table)
    a = ap.parse_args(argv)
    return 0 if a.fn(a) else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
