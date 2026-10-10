#!/usr/bin/env python3
"""記号数の少ない側の URTM（docs/23）: Morita 2017 Theorem 5.4 の記号削減の再現と改良。

T（m 状態 n 記号の RTM、Morita の記述ファイルか kstate_blocks が作った表）を、r 記号（r = 2, 3）の RTM T̃ に変換する。
記号 s は長さ k の r 進の符号 c(s) = c_1(s) ⋯ c_k(s) でテープの k マス（ブロック）に置く。空白は 0^k。

構成（`--mode`）:

  morita  原典の Theorem 5.4（§5.3.3）をそのまま、ただし発火しえない規則を省く（docs/10 §7.1 と同じ省き方。
          r = 2・k = 2 で (24,4) から (138,2) の 220 本と一致する）。
            δr [[p^r, x1..xj], x_{j+1}, 0, +, [p^r, x1..x_{j+1}]]           j = 0..k-2
            δt [[p^r, c1..c_{k-1}(s)], c_k(s), c_k(t), −, [q^w, c1..c_{k-1}(t)]]
            δw [[q^w, y1..yj], 0, yj, −, [q^w, y1..y_{j-1}]] (j ≥ 2)、[[q^w, y1], 0, y1, hsd(q), [q^s, 1]]
            δs [[q^s, i], x, x, hsd(q), [q^s, i+1]]、最後は [q^r] へ
          T の 1 ステップを 3k − 2 ステップで模倣する。
  orient  状態ごとにヘッドの居るセル（ブロックの左端 L / 右端 R）e(q) を選ぶ（原典は全部 L）。読みは e(p) から
          反対端へ、書き戻しは反対端から e(p) へ。書き戻しの最後に hsd(q) へ動いた先から q のセル e(q) まで
          sh ∈ {0, 1, 2} マスの移動（δs）。可逆性のため、q に入る規則の出どころ p の e(p) は q ごとにそろえる
          （そろわなければ構成できない。`orient_ok`）。sh = 0 の状態は δs が要らない。

共通: 符号は機械ごとに選べる（`--code`、既定は Morita の番号順）。`opt` は符号と e を探して状態数を最小化する。

検査（`check`）:
  * Morita Def. 5.4 の決定性・可逆性（check_urtm と同じ条件を表に対して）
  * 逐段: 記述ファイルの全試験例と乱択配置で、T の 1 ステップごとに T̃ が決まったステップ数で符号化に達し、
    T が止まる配置では T̃ も k 未満のステップでブロックの中で止まる
  * 変異注入（`mutate`）: T̃ の規則を 1 本消す／書く記号を替える／行き先を替える変異を逐段検査が落とすか

    python3 tools/fewsym.py stats data/urtm/urtm24-4.txt
    python3 tools/fewsym.py build data/urtm/urtm24-4.txt --mode morita -o out/fs/u138.txt
    python3 tools/fewsym.py check data/urtm/urtm24-4.txt --mode morita --random 200
    python3 tools/fewsym.py opt data/urtm/urtm24-4.txt --mode orient
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
from check_urtm import parse  # noqa: E402
from simulate import blank_of, maxstep_of, read_cases, fact_of  # noqa: E402

MOVE = {"-": -1, "0": 0, "+": 1}
OPP = {"+": "-", "-": "+"}
PSEUDO = ("halt", "null")


# ---------------------------------------------------------------- T
class Base:
    def __init__(self, path):
        self.path = path
        self.name = os.path.basename(path).replace(".txt", "")
        states, symbols, quints = parse(path)
        self.blank = blank_of(path)
        self.maxstep = maxstep_of(path)
        self.cases = read_cases(path)
        self.initial = fact_of(path, "initial_state", None)
        # 0 シフトの停止規則（疑似状態 halt/null へ）は落とす（Lean の dropHalt と同じ）。T はそこで止まる。
        self.halt_rules = [r for r in quints if r[4] in PSEUDO]
        assert all(r[3] == "0" for r in self.halt_rules), self.halt_rules
        self.rules = [r for r in quints if r[4] not in PSEUDO]
        assert all(r[3] in "+-" for r in self.rules), "zero shift in a non-halting rule"
        used = [r[0] for r in quints] + [r[4] for r in self.rules]
        self.states = list(dict.fromkeys(list(states or []) + used))
        self.states = [s for s in self.states if s not in PSEUDO]
        syms = [r[1] for r in quints] + [r[2] for r in quints]
        self.symbols = list(dict.fromkeys([self.blank] + list(symbols or []) + syms))
        self.delta = {(p, s): (t, d, q) for (p, s, t, d, q) in quints}
        self.hsd = {}
        for (p, s, t, d, q) in self.rules:
            assert self.hsd.setdefault(q, d) == d, f"T not reversible at {q}"
        self.reads = defaultdict(list)       # p -> [s]（停止しない規則）
        self.writes = defaultdict(list)      # q -> [t]
        self.srcs = defaultdict(set)
        for (p, s, t, d, q) in self.rules:
            self.reads[p].append(s)
            self.writes[q].append(t)
            self.srcs[q].add(p)


def digits_needed(n, r):
    k = 1
    while r ** k < n:
        k += 1
    return k


def default_code(T, r, k):
    """Morita の番号順: 記号の宣言順に 0, 1, 2, … の r 進 k 桁（空白が先頭なので 0^k）。"""
    out = {}
    for i, s in enumerate(T.symbols):
        ds = []
        x = i
        for _ in range(k):
            ds.append(x % r)
            x //= r
        out[s] = tuple(reversed(ds))
    return out


# ---------------------------------------------------------------- T̃
def sname(st):
    """状態の名前（Prolog のアトムのリスト）。"""
    kind, q, *rest = st
    return "[" + ",".join([f"{q}_{kind}"] + [str(x) for x in rest]) + "]"


class Conv:
    """T と符号・向きから T̃ を作る。rules は (p̃, a, b, d, q̃)、状態は tuple。"""

    def __init__(self, T: Base, r=2, k=None, code=None, mode="morita", orient=None):
        self.T, self.r = T, r
        self.k = k or digits_needed(len(T.symbols), r)
        self.code = code or default_code(T, r, self.k)
        assert all(len(c) == self.k for c in self.code.values())
        assert len(set(self.code.values())) == len(self.code), "code not injective"
        assert self.code[T.blank] == (0,) * self.k, "blank must be 0^k"
        self.mode = mode
        # e(q): ヘッドの居るセル（ブロック内の添字 0 = 左端 or k-1 = 右端）
        self.e = {q: "L" for q in T.states}
        if orient:
            self.e.update(orient)
        self.rules = []
        self.problem = None
        self.shift = {}
        self._build()

    # ブロック内のセル添字 j の符号の桁。e = L なら左から、R なら右から読む。
    def order(self, e):
        return list(range(self.k)) if e == "L" else list(range(self.k - 1, -1, -1))

    def sh_of(self, p, d, q):
        """規則 p → q（向き d）の最後の書込（セル e(p)）から d へ 1 マス動いた先から、q のセルまでのマス数。"""
        k = self.k
        cell = 0 if self.e[p] == "L" else k - 1
        land = cell + (1 if d == "+" else -1)            # 同じブロックの座標系（ブロック x = 0..k-1）
        tgt = (k if d == "+" else -k) + (0 if self.e[q] == "L" else k - 1)
        return abs(tgt - land)

    def _build(self):
        T, k, r, c = self.T, self.k, self.r, self.code
        R = []
        seen = set()

        def add(rule):
            if rule not in seen:
                seen.add(rule)
                R.append(rule)
        # 行き先 q ごとに sh をそろえる
        for q in T.states:
            shs = {self.sh_of(p, d, q2) for (p, s, t, d, q2) in T.rules if q2 == q}
            es = {self.e[p] for p in T.srcs[q]}
            if len(shs) > 1 or len(es) > 1:
                self.problem = f"state {q}: sources with e={sorted(es)} need shifts {sorted(shs)}"
                return
            if shs:
                self.shift[q] = shs.pop()
        for (p, s, t, d, q) in T.rules:
            ep = self.e[p]
            fwd = "+" if ep == "L" else "-"               # 読み進む向き
            bwd = OPP[fwd]
            o = self.order(ep)
            cs = [c[s][j] for j in o]                     # 読む順の桁
            ct = [c[t][j] for j in o]
            # δr
            for j in range(k - 1):
                add((("r", p, *cs[:j]), cs[j], 0, fwd, ("r", p, *cs[:j + 1])))
            # δt
            if k == 1:
                raise SystemExit("k = 1 is not a symbol reduction")
            tag = (ep,) if self.mode == "orient" else ()
            ew = ("w", q, *tag, *ct[:k - 1])
            add((("r", p, *cs[:k - 1]), cs[k - 1], ct[k - 1], bwd, ew))
            # δw
            for j in range(k - 1, 1, -1):
                add((("w", q, *tag, *ct[:j]), 0, ct[j - 1], bwd, ("w", q, *tag, *ct[:j - 1])))
            sh = self.shift[q]
            nxt = self.sst(q, 1) if sh > 0 else ("r", q)
            add((("w", q, *tag, ct[0]), 0, ct[0], d, nxt))
        for q, sh in self.shift.items():
            for i in range(1, sh + 1):
                nxt = self.sst(q, i + 1) if i < sh else ("r", q)
                for x in range(r):
                    add((self.sst(q, i), x, x, T.hsd[q], nxt))
        # 原典の記述ファイルの形に合わせ、[q^w, e] の e は向きが 1 種類なら落とす（名前だけ）
        self.rules = R

    def sst(self, q, i):
        """δs の状態。原典の記述ファイル（k = 2）は添字を書かない。"""
        return ("s", q) if self.k == 2 else ("s", q, i)

    # ---- 数え
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
            cnt[st[0] if st[0] != "r" or len(st) == 2 else "r+"] += 1
        return dict(cnt)

    # ---- 可逆性・決定性（Morita Def. 5.4）
    def check_table(self):
        errs = []
        dom = {}
        for rl in self.rules:
            key = (rl[0], rl[1])
            if key in dom:
                errs.append(f"nondeterministic {key}")
            dom[key] = rl
        into = defaultdict(list)
        for rl in self.rules:
            into[rl[4]].append(rl)
        for q, g in into.items():
            if len({x[3] for x in g}) > 1:
                errs.append(f"entered with two directions: {q}")
            ws = [x[2] for x in g]
            if len(set(ws)) != len(ws):
                errs.append(f"entered writing the same symbol: {q}")
        return errs

    # ---- 符号化
    def enc(self, p, pos, tape):
        bits = []
        for s in tape:
            bits.extend(self.code[s])
        cell = 0 if self.e.get(p, "L") == "L" else self.k - 1
        return (("r", p), self.k * pos + cell, bits)

    def cost(self, p, s, d, q):
        return 3 * self.k - 2 - (self.k - 1) + self.shift[q]   # (k-1) 読み + 1 + (k-1) 書き + sh

    # ---- 出力
    def emit(self, f, title=None):
        T = self.T
        f.write(f"title('{title or f'{T.name} -> {self.r} symbols by fewsym.py mode={self.mode}'}').\n")
        f.write(f"% 生成: tools/fewsym.py（docs/23）。k={self.k} code={json.dumps({s: ''.join(map(str, v)) for s, v in self.code.items()})}\n")
        if self.mode == "orient":
            f.write(f"% orient={json.dumps(self.e)}\n")
        init = T.initial or T.states[0]
        f.write(f"initial_state({sname(('r', init))}).\nfinal_states([]).\n")
        f.write(f"symbols([{','.join(str(x) for x in range(self.r))}]).\nblank(0).\n")
        f.write(f"maxstep({T.maxstep * (3 * self.k + 1) + 10}).\n")
        for (state, pos, tape, _, _) in T.cases:
            st, ps, bits = self.enc(state, pos, tape)
            f.write(f"initial_conf([{sname(st)},{ps},[{','.join(map(str, bits))}]]).\n")
        for (a, x, y, d, b) in self.rules:
            f.write(f"[{sname(a)},{x},{y},{d},{sname(b)}].\n")
        f.write("states([" + ",".join(sorted(sname(s) for s in self.states())) + "]).\n")


# ---------------------------------------------------------------- 逐段検査
def run_T(T, state, pos, tape):
    """T の 1 ステップ。規則が無い・停止規則なら None。"""
    while pos >= len(tape):
        tape.append(T.blank)
    rl = T.delta.get((state, tape[pos]))
    if rl is None or rl[2] in PSEUDO:
        return None
    t, d, q = rl
    tape[pos] = t
    return q, pos + MOVE[d], (t, d, q)


def lockstep(cv: Conv, state, pos, tape, limit):
    """返り値 (ok, t_steps, tt_steps, why)。"""
    T = cv.T
    delta = {(a, x): (y, d, b) for (a, x, y, d, b) in cv.rules}
    tape = list(tape)
    st, ps, bits = cv.enc(state, pos, tape)
    ts = tts = 0

    def tstep(st, ps, bits):
        while ps >= len(bits):
            bits.append(0)
        if ps < 0:
            return "fell"
        rl = delta.get((st, bits[ps]))
        if rl is None:
            return None
        y, d, b = rl
        bits[ps] = y
        return b, ps + MOVE[d]

    while ts < limit:
        p0, pos0 = state, pos
        while pos >= len(tape):
            tape.append(T.blank)
        s0 = tape[pos]
        nxt = run_T(T, state, pos, tape)
        if nxt is None:
            # T は止まる。T̃ は k-1 ステップ以内に止まり、テープは符号化のまま（読んだマスは 0 に消えうる）
            before = list(bits)
            for j in range(cv.k):
                o = tstep(st, ps, bits)
                if o is None:
                    lo, hi = cv.k * pos0, cv.k * pos0 + cv.k
                    for i in range(max(len(bits), len(before))):
                        a = bits[i] if i < len(bits) else 0
                        b0 = before[i] if i < len(before) else 0
                        if a != b0 and not (lo <= i < hi):
                            return False, ts, tts, f"T halted; T̃ changed cell {i} outside the block"
                    return True, ts, tts, "both halt"
                if o == "fell":
                    return False, ts, tts, "T̃ fell"
                st, ps = o
                tts += 1
            return False, ts, tts, f"T halted at ({p0},{tape[pos0]}) but T̃ keeps running"
        q, npos, (t, d, _) = nxt
        if npos < 0:
            return True, ts, tts, "T fell off (stop comparing)"
        n = cv.cost(p0, s0, d, q)
        for j in range(n):
            o = tstep(st, ps, bits)
            if o is None or o == "fell":
                return False, ts, tts, f"T̃ stopped inside T step {ts + 1} ({p0} -> {q}) sub-step {j + 1}/{n}"
            st, ps = o
            tts += 1
        state, pos = q, npos
        ts += 1
        est, eps_, ebits = cv.enc(state, pos, tape)
        L = max(len(bits), len(ebits))
        if st != est or ps != eps_ or bits + [0] * (L - len(bits)) != ebits + [0] * (L - len(ebits)):
            return False, ts, tts, f"mismatch after T step {ts}: T̃ {sname(st)}@{ps} vs enc {sname(est)}@{eps_}"
    return True, ts, tts, "budget"


def random_configs(T: Base, rng, n, width=12):
    """乱択配置: 状態・テープ（T の記号から一様）・ヘッド位置。T が読む記号に偏らせる。"""
    out = []
    for _ in range(n):
        p = rng.choice(T.states)
        tape = [rng.choice(T.symbols) for _ in range(width)]
        pos = rng.randrange(2, width - 2)
        out.append((p, pos, tape))
    return out


def ctsh_tape(T: Base, C, w, pad=6):
    """CTSH (C = [w_1..w_{k-1}], w) を Morita の原典の機械の初期配置にする（gen_ctsh_lean.decode/decode2 の逆）。
    返り値 (state, pos, tape)。kstate_blocks の派生機械（out/kb）は扱わない。"""
    lo = {"Y": "y", "N": "n"}
    name = T.name
    if name == "urtm32-3":
        body = []
        for seg in reversed(C):
            for ch in reversed(seg):
                body += ["y", "y"] if ch == "Y" else ["n", "y"]
            body += ["n", "n"]
        body += ["n", "b"]
        tape = ["b"] + body + ["b"]
    else:
        body = []
        for seg in reversed(C):
            body += [lo[ch] for ch in reversed(seg)] + ["*"]
        tape = ["b"] + body + (["b", "b"] if name == "urtm24-4" else ["b", "$"])
    pos = len(tape)
    tape += [lo[ch] for ch in w] + ["b"] * pad
    return T.initial or "begin_", pos, tape


def random_ctsh(rng, maxk=4, maxc=3, maxw=5):
    k = rng.randint(2, maxk)
    C = [[rng.choice("YN") for _ in range(rng.randint(0, maxc))] for _ in range(k - 1)]
    w = [rng.choice("YN") for _ in range(rng.randint(1, maxw))]
    if rng.random() < 0.8:
        w[0] = "N"          # 先頭が Y だと相 0 で即停止するので、たいていは N で始める
    return C, w


def check_ctsh(cv, n, seed=20260929, limit=3000, big=False):
    """乱択 CTSH の初期配置から逐段（NoStuck な実行）。T が規則の無い配置で止まったら入力の誤りとして数える。"""
    T = cv.T
    rng = random.Random(seed)
    bad, halted = 0, 0
    steps = []
    for _ in range(n):
        C, w = random_ctsh(rng, 7, 6, 8) if big else random_ctsh(rng)
        st, pos, tape = ctsh_tape(T, C, w)
        ok, ts, tts, why = lockstep(cv, st, pos, tape, limit)
        bad += not ok
        halted += why == "both halt"
        steps.append(ts)
    check_ctsh.last = (sum(steps), sorted(steps)[len(steps) // 2] if steps else 0)
    return bad, halted


def local_all(cv: Conv, nostuck=False):
    """局所全数: T の全規則 × ヘッドの隣のセルの全記号で、1 ステップの模倣を確かめる。
    T が止まる全組 (p, s) でも T̃ がブロック内で止まることを確かめる。
    nostuck: T の規則が無い組 (p, s)（停止規則でもない）は飛ばす（NoStuck な実行だけを見る。状態の併合をしたとき）。"""
    T = cv.T
    bad, n = [], 0
    for p in T.states:
        for s in T.symbols:
            if nostuck and (p, s) not in T.delta:
                continue
            for a in T.symbols:
                for b in T.symbols:
                    tape = [T.blank, a, s, b, T.blank]
                    ok, ts, tts, why = lockstep(cv, p, 2, tape, 1)
                    n += 1
                    if not ok:
                        bad.append((p, s, a, b, why))
    return bad, n


def check_all(cv: Conv, nrand=0, seed=20260929, quiet=False, nostuck=False, nctsh=300):
    """nostuck: 状態を併合した機械（T が規則の無い配置で止まる場合は保存しない）。乱択配置の検査をしない。"""
    T = cv.T
    lines = []
    errs = cv.check_table()
    lines.append(f"table: {'OK' if not errs else 'NG ' + '; '.join(errs[:5])}")
    allok = not errs
    for i, (state, pos, tape, exp, _) in enumerate(T.cases):
        ok, ts, tts, why = lockstep(cv, state, pos, tape, T.maxstep)
        # 記述ファイルの %% の数は停止規則（0 シフト）も 1 と数える（lockstep は数えない）。
        # urtm13-7.txt case4 のコメントの誤植（1073 → 1173）は gen_lean.CORRECTIONS と同じく直す
        exp = {("urtm13-7", 4): 1173}.get((T.name, i), exp)
        if exp is not None and why == "both halt":
            ok &= ts + 1 == exp
        allok &= ok
        lines.append(f"{'ok' if ok else 'NG'} case{i}: T {ts} steps, T̃ {tts} steps ({why}; file says {exp})")
    if T.name in ("urtm10-8", "urtm13-7", "urtm15-6", "urtm17-5", "urtm24-4", "urtm32-3") and nctsh:
        bad, halted = check_ctsh(cv, nctsh, seed=seed)
        allok &= bad == 0
        lines.append(f"{'ok' if not bad else 'NG'} random CTSH instances: {nctsh - bad}/{nctsh} in lockstep "
                     f"({halted} halt, rest run 3000 T steps; T steps total {check_ctsh.last[0]}, median {check_ctsh.last[1]})")
    if nostuck:
        nrand = 0
    if nrand:
        rng = random.Random(seed)
        bad = 0
        for (p, pos, tape) in random_configs(T, rng, nrand):
            ok, ts, tts, why = lockstep(cv, p, pos, tape, 2000)
            bad += not ok
        allok &= bad == 0
        lines.append(f"{'ok' if not bad else 'NG'} random configs: {nrand - bad}/{nrand}")
    bad, n = local_all(cv, nostuck)
    allok &= not bad
    lines.append(f"{'ok' if not bad else 'NG'} local exhaustive{' (NoStuck)' if nostuck else ''}: {n - len(bad)}/{n}" + (f" e.g. {bad[0]}" if bad else ""))
    return allok, lines


def mutation_test(cv, nostuck=False, seed=7):
    """変異注入: 規則を 1 本消す／書く値を替える／行き先を別の状態にする。
    検出 = 表の検査（決定性・可逆性）か局所全数か試験例・乱択 CTSH の逐段が落とす。
    返り値 (検出数, 総数, 生き残り)。変異前に全部通ることを先に確かめる。"""
    rng = random.Random(seed)
    base_bad, _ = local_all(cv, nostuck)
    assert not base_bad and not cv.check_table()
    orig = list(cv.rules)
    sts = sorted({x for rl in orig for x in (rl[0], rl[4])}, key=str)
    muts = []
    for i, (a, x, y, d, b) in enumerate(orig):
        muts.append((f"del {i}", orig[:i] + orig[i + 1:]))
        y2 = (y + 1) % cv.r
        muts.append((f"write {i}", orig[:i] + [(a, x, y2, d, b)] + orig[i + 1:]))
        b2 = rng.choice([z for z in sts if z != b])
        muts.append((f"retarget {i}", orig[:i] + [(a, x, y, d, b2)] + orig[i + 1:]))
    killed, survivors = 0, []
    for name, rules in muts:
        cv.rules = rules
        dead = bool(cv.check_table()) or bool(local_all(cv, nostuck)[0])
        if not dead:
            for (state, pos, tape, _, _) in T_cases(cv):
                if not lockstep(cv, state, pos, tape, 3000)[0]:
                    dead = True
                    break
        if not dead and cv.T.name in ("urtm10-8", "urtm13-7", "urtm15-6", "urtm17-5", "urtm24-4", "urtm32-3"):
            dead = check_ctsh(cv, 200)[0] > 0
        killed += dead
        if not dead:
            survivors.append(name)
    cv.rules = orig
    return killed, len(muts), survivors


def T_cases(cv):
    return cv.T.cases


# ---------------------------------------------------------------- 符号の最適化
def all_words(r, k):
    out = [()]
    for _ in range(k):
        out = [w + (x,) for w in out for x in range(r)]
    return out


def opt_code(T, r, k, mode="morita", orient=None, exhaustive_limit=200000, iters=20000, seed=1):
    """空白 = 0^k を固定し、残りの記号への符号の割り当てで状態数を最小化する。
    割り当ての数が exhaustive_limit 以下なら全数（厳密）、そうでなければ焼きなまし（発見的）。"""
    words = [w for w in all_words(r, k) if any(w)]
    others = [s for s in T.symbols if s != T.blank]
    n = len(others)
    total = 1
    for i in range(n):
        total *= len(words) - i
    zero = (0,) * k

    def cost(assign):
        code = {T.blank: zero, **dict(zip(others, assign))}
        cv = Conv(T, r=r, k=k, code=code, mode=mode, orient=orient)
        return (10 ** 6 if cv.problem else cv.nstates()), code
    best = None
    if total <= exhaustive_limit:
        for assign in itertools.permutations(words, n):
            c, code = cost(assign)
            if best is None or c < best[0]:
                best = (c, code)
        return best[0], best[1], "exhaustive", total
    rng = random.Random(seed)
    cur = list(rng.sample(words, n))
    unused = [w for w in words if w not in cur]
    cc, code = cost(cur)
    best = (cc, code)
    import math
    for it in range(iters):
        temp = max(0.05, 2.0 * (1 - it / iters))
        nxt = list(cur)
        i = rng.randrange(n)
        if unused and rng.random() < 0.3:
            j = rng.randrange(len(unused))
            nxt[i], newun = unused[j], unused[:j] + [cur[i]] + unused[j + 1:]
        else:
            j = rng.randrange(n)
            nxt[i], nxt[j] = nxt[j], nxt[i]
            newun = unused
        c, code = cost(nxt)
        if c <= cc or rng.random() < math.exp((cc - c) / temp):
            cur, cc, unused = nxt, c, newun
            if c < best[0]:
                best = (c, code)
    return best[0], best[1], f"annealing({iters})", total


# ---------------------------------------------------------------- CLI
def load(path):
    if not os.path.exists(path):
        cand = os.path.join(HERE, "..", "data", "urtm", path + ".txt")
        path = cand if os.path.exists(cand) else os.path.join(HERE, "..", "out", "kb", path + ".txt")
    return Base(path)


def parse_code(s, T, k):
    if not s:
        return None
    d = json.loads(s) if s.startswith("{") else json.load(open(s))
    if "code" in d:
        d = d["code"]
    return {sym: tuple(int(ch) for ch in v) for sym, v in d.items()}


def conv_from_args(a, T):
    r = a.radix
    k = a.k or digits_needed(len(T.symbols), r)
    code = parse_code(a.code, T, k)
    orient = json.loads(a.orient) if a.orient and a.orient.startswith("{") else (
        json.load(open(a.orient)).get("orient") if a.orient else None)
    return Conv(T, r=r, k=k, code=code, mode=a.mode, orient=orient)


def cmd_stats(a):
    for path in a.inputs:
        T = load(path)
        m, n = len(T.states), len(T.symbols)
        ind = defaultdict(int)
        for (p, s, t, d, q) in T.rules:
            ind[q] += 1
        sweep = sum(1 for (p, s, t, d, q) in T.rules if T.hsd.get(p) == d)
        print(f"{T.name}: m={m} n={n} rules={len(T.rules)} (+{len(T.halt_rules)} halt) "
              f"sweep={sweep} turn={len(T.rules) - sweep} hsd+={sum(1 for q in T.hsd if T.hsd[q] == '+')} "
              f"no-entry={[q for q in T.states if q not in T.hsd]}")
    return True


def cmd_build(a):
    T = load(a.input)
    cv = conv_from_args(a, T)
    if cv.problem:
        print("cannot build:", cv.problem)
        return False
    print(f"{T.name} -> ({cv.nstates()},{cv.r}) k={cv.k} rules={len(cv.rules)} breakdown={cv.breakdown()}")
    if a.output:
        os.makedirs(os.path.dirname(a.output) or ".", exist_ok=True)
        with open(a.output, "w") as f:
            cv.emit(f)
    return True


def cmd_check(a):
    T = load(a.input)
    cv = conv_from_args(a, T)
    if cv.problem:
        print("cannot build:", cv.problem)
        return False
    ok, lines = check_all(cv, a.random)
    print(f"{T.name} -> ({cv.nstates()},{cv.r}) k={cv.k} rules={len(cv.rules)}")
    print("\n".join("  " + x for x in lines))
    return ok


def cmd_opt(a):
    T = load(a.input)
    r = a.radix
    k = a.k or digits_needed(len(T.symbols), r)
    base = Conv(T, r=r, k=k, mode=a.mode)
    c, code, how, total = opt_code(T, r, k, mode=a.mode, iters=a.iters, seed=a.seed)
    cv = Conv(T, r=r, k=k, code=code, mode=a.mode)
    ok = not cv.check_table()
    res = {"machine": T.name, "mode": a.mode, "radix": r, "k": k, "states": cv.nstates(), "rules": len(cv.rules),
           "default_code_states": base.nstates(), "search": how, "space": total, "table_ok": ok,
           "breakdown": cv.breakdown(), "code": {s: "".join(map(str, v)) for s, v in code.items()}}
    print(json.dumps(res, ensure_ascii=False))
    if a.json:
        os.makedirs(os.path.dirname(a.json) or ".", exist_ok=True)
        json.dump(res, open(a.json, "w"), ensure_ascii=False, indent=1)
    return ok


def main(argv):
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)

    def common(p):
        p.add_argument("--mode", default="morita", choices=["morita", "orient"])
        p.add_argument("--radix", type=int, default=2)
        p.add_argument("-k", type=int, default=None)
        p.add_argument("--code", default=None, help='JSON {"sym": "01", ...} または解の JSON ファイル')
        p.add_argument("--orient", default=None, help='JSON {"state": "L"|"R"} または解の JSON ファイル')
    p = sub.add_parser("stats")
    p.add_argument("inputs", nargs="+")
    p = sub.add_parser("build")
    p.add_argument("input")
    common(p)
    p.add_argument("-o", "--output")
    p = sub.add_parser("check")
    p.add_argument("input")
    common(p)
    p.add_argument("--random", type=int, default=200)
    p = sub.add_parser("opt")
    p.add_argument("input")
    common(p)
    p.add_argument("--iters", type=int, default=20000)
    p.add_argument("--seed", type=int, default=1)
    p.add_argument("--json")
    a = ap.parse_args(argv)
    return {"stats": cmd_stats, "build": cmd_build, "check": cmd_check, "opt": cmd_opt}[a.cmd](a)


if __name__ == "__main__":
    sys.exit(0 if main(sys.argv[1:]) else 1)
