#!/usr/bin/env python3
"""k 状態化変換: 任意の 1 テープ RTM T（m 状態 n 記号）を、少数状態の RTM T' に変換する。

Morita 2017 Thm 5.5（4 状態・2mn+n 記号）の系統の構成を、**独立に設計し直して**実装したもの。
記述ファイル（Morita 形式の Prolog ファクト）を読み、同じ形式で T' を書き出す。

    python3 tools/kstate.py convert data/urtm/urtm10-8.txt -o out/k4.txt              # 4 状態 (m+1)n 記号
    python3 tools/kstate.py convert IN --variant k4 --blocks 2,1 -o out/k7.txt         # 7 状態
    python3 tools/kstate.py convert IN --variant hab6 -o out/k6.txt                   # 6 状態 (m+1)n 記号
    python3 tools/kstate.py check IN OUT          # 逐段（lockstep）等価性: T' が T を忠実に模倣するか
                                                  #   （T は IN の maxstep で打ち切る。停止しない例も検査できる）
    python3 tools/kstate.py decode IN OUT         # T' の停止配置を T の配置に復号して表示

構成の要点（詳細は docs/03_kstate_2026-09-23.md）:
  * T の可逆性条件から、各状態 q には「q に入る規則の方向」 dir(q) が一意に定まる。
    T の状態集合は Q+（右移動で入る）と Q-（左移動で入る）に分かれる。初期状態など
    一度も入られない状態は Q+ に入れる。
  * T' のテープ記号は、素の記号 s（n 個）と計数記号 [i,s]（i = 1..B, n 個ずつ）。
    「安定配置」では計数記号がちょうど 1 個だけあり、それがヘッド位置と T の状態を表す。
  * T の 1 ステップ [p,s,t,d,q] を、元セルと移動先セルの間をヘッドが往復する
    「シャトル」で模倣する。元セルの計数を 1 ずつ減らし、移動先の計数を 1 ずつ増やす。
  * Q+ と Q- に**互いに素な番号範囲**を割り当てると、往復中に「元セルで減算する状態」と
    「移動先で加算する状態」を同一視できる（読む計数の範囲が違うので決定性が保てる）。
    これで状態は H+, H-, A+, A- の 4 つ、記号は (m+1)n になる。
  * 状態番号の一部（ブロック）を制御に持たせると、状態を増やして記号を減らせる
    （--blocks b+,b-: 状態 b+ + b- + 2 max(b+,b-)、記号 (ceil(m+/b+) + ceil(m-/b-) + 1) n）。

変種 (--variant):
  k4          上記。--blocks 1,1 で 4 状態。既定。
  hab6        H/A/B の 3 種 × 2 方向 = 6 状態、(m+1)n 記号。範囲分離を使わない素朴版。
  hab6-offset 最初に提案された「e オフセット付き」の 6 状態版（2mn+n 記号）。
              **可逆性条件を満たさない**（R4 の衝突）ことを再現するために残してある。
"""

import argparse
import math
import re
import sys
from collections import defaultdict

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from check_urtm import parse  # noqa: E402
from simulate import blank_of, fact_of, maxstep_of, read_cases  # noqa: E402

PSEUDO = ("halt", "null")
OPP = {"+": "-", "-": "+"}
MOVE = {"-": -1, "0": 0, "+": 1}


# ---------------------------------------------------------------- 入力機械 T
class Machine:
    """記述ファイル 1 本ぶん。"""

    def __init__(self, path):
        self.path = path
        self.name = path.split("/")[-1]
        states, symbols, quints = parse(path)
        self.quints = quints
        used_states = [q[0] for q in quints] + [q[4] for q in quints]
        self.states = list(dict.fromkeys(list(states or []) + used_states))
        self.pseudo = [s for s in self.states if s in PSEUDO and s not in (states or [])]
        self.states = [s for s in self.states if s not in self.pseudo]
        used_syms = [q[1] for q in quints] + [q[2] for q in quints]
        self.symbols = list(dict.fromkeys(list(symbols or []) + used_syms))
        self.blank = blank_of(path)
        if self.blank not in self.symbols:
            self.symbols.append(self.blank)
        self.maxstep = maxstep_of(path)
        self.cases = read_cases(path)
        self.initial_state = fact_of(path, "initial_state", self.states[0] if self.states else None)
        self.delta = {(p, s): (t, d, q) for (p, s, t, d, q) in quints}

    # T の可逆性条件から決まる「入る方向」
    def entering_dirs(self):
        dirs = defaultdict(set)
        for (p, s, t, d, q) in self.quints:
            dirs[q].add(d)
        return dirs

    def step(self, conf):
        """conf = (state, pos, tape list)。規則が無ければ None。左端から落ちたら 'fell'。"""
        state, pos, tape = conf
        while pos >= len(tape):
            tape.append(self.blank)
        r = self.delta.get((state, tape[pos]))
        if r is None:
            return None
        t, d, q = r
        tape[pos] = t
        pos += MOVE[d]
        if pos < 0:
            return "fell"
        return (q, pos, tape)


# ---------------------------------------------------------------- 変換
class Construction:
    """T から T' を作る。variant と blocks で系列を選ぶ。"""

    def __init__(self, T: Machine, variant="k4", blocks=(1, 1)):
        self.T = T
        self.variant = variant
        self.blocks = tuple(blocks)
        self._partition()
        self._name_symbols()
        if variant == "k4":
            self._build_k4()
        elif variant == "hab6":
            self._build_hab6(offset=False)
        elif variant == "hab6-offset":
            self._build_hab6(offset=True)
        else:
            raise SystemExit(f"unknown variant {variant}")

    # -- Q+ / Q- と番号付け
    def _partition(self):
        T = self.T
        dirs = T.entering_dirs()
        self.dir = {}
        for q in T.states:
            ds = dirs.get(q, set())
            if len(ds) > 1:
                raise SystemExit(f"{T.name}: state {q} entered with dirs {sorted(ds)} (not reversible)")
            if ds == {"0"}:
                raise SystemExit(f"{T.name}: state {q} entered by a 0-shift rule; "
                                 "only pseudo states (halt/null) may be entered by 0-shift")
            self.dir[q] = next(iter(ds)) if ds else "+"   # 入られない状態は Q+ に置く
        for (p, s, t, d, q) in T.quints:
            if q in T.pseudo:
                continue
            if d == "0":
                raise SystemExit(f"{T.name}: 0-shift rule into non-pseudo state {q}")
        self.Qd = {"+": [q for q in T.states if self.dir[q] == "+"],
                   "-": [q for q in T.states if self.dir[q] == "-"]}

    def _name_symbols(self):
        S = self.T.symbols
        for prefix in ("c", "cc", "ctr", "kc"):
            if not any(re.match(rf"^{prefix}\d+_", s) for s in S):
                self.prefix = prefix
                return
        raise SystemExit("could not find a counter-name prefix free of collisions")

    def C(self, i, s):
        return f"{self.prefix}{i}_{s}"

    def is_counter(self, sym):
        return sym.startswith(self.prefix) and re.match(rf"^{self.prefix}(\d+)_(.*)$", sym) is not None

    def split_counter(self, sym):
        m = re.match(rf"^{self.prefix}(\d+)_(.*)$", sym)
        return int(m.group(1)), m.group(2)

    # -- 4 状態系列（ブロック付き）
    def _build_k4(self):
        T = self.T
        bp, bm = self.blocks
        if bp < 1 or bm < 1:
            raise SystemExit("blocks must be >= 1")
        self.beta = {"+": bp, "-": bm}
        m = {"+": len(self.Qd["+"]), "-": len(self.Qd["-"])}
        B = {"+": math.ceil(m["+"] / bp) if m["+"] else 0,
             "-": math.ceil(m["-"] / bm) if m["-"] else 0}
        self.B = B
        self.lo = {"+": 1, "-": B["+"] + 1}
        self.hi = {"+": B["+"], "-": B["+"] + B["-"]}
        self.nctr = B["+"] + B["-"]
        # 状態 q -> (方向, ブロック, オフセット)。ブロック内でオフセットは相異なる。
        self.blk, self.off = {}, {}
        for d in "+-":
            for k, q in enumerate(self.Qd[d]):
                self.blk[q] = k // B[d] + 1
                self.off[q] = self.lo[d] + k % B[d]
        nA = max(bp, bm)

        def H(d, b):
            return ("hp" if d == "+" else "hm") + (str(b) if self.beta[d] > 1 else "")

        def A(d, b):
            return ("ap" if d == "+" else "am") + (str(b) if nA > 1 else "")

        self.H, self.A = H, A
        self.k = bp + bm + 2 * nA
        hs = [H(d, b) for d in "+-" for b in range(1, self.beta[d] + 1)]
        as_ = [A(d, b) for d in "+-" for b in range(1, nA + 1)]
        self.states = hs + as_
        self.hstates = set(hs)
        self.symbols = list(T.symbols) + [self.C(i, s) for i in range(1, self.nctr + 1) for s in T.symbols]
        R = []
        # R1: T の規則そのもの（安定配置で発火）
        for (p, s, t, d, q) in T.quints:
            src = H(self.dir[p], self.blk[p])
            if q in T.pseudo:
                R.append((src, self.C(self.off[p], s), t, d, q))
            else:
                R.append((src, self.C(self.off[p], s), self.C(self.off[q], t), d, H(d, self.blk[q])))
        # R2..R5: シャトル（方向 d、ブロック b ごと）
        for d in "+-":
            if m[d] == 0:
                continue
            e = OPP[d]
            lo, hi = self.lo[d], self.hi[d]
            for b in range(1, self.beta[d] + 1):
                for s2 in T.symbols:
                    R.append((H(d, b), s2, self.C(lo, s2), e, A(e, b)))               # R2
                for i in range(lo + 1, hi + 1):
                    for t in T.symbols:
                        R.append((A(e, b), self.C(i, t), self.C(i - 1, t), d, A(d, b)))  # R3
                for t in T.symbols:
                    R.append((A(e, b), self.C(lo, t), t, d, H(d, b)))                  # R4
                for j in range(lo, hi):
                    for s2 in T.symbols:
                        R.append((A(d, b), self.C(j, s2), self.C(j + 1, s2), e, A(e, b)))  # R5
        self.quints = R
        self.formula = (f"k = b+ + b- + 2 max(b+,b-) = {self.k}, "
                        f"n' = (ceil(m+/b+) + ceil(m-/b-) + 1) n = ({B['+']} + {B['-']} + 1) * {len(T.symbols)}"
                        f" = {len(self.symbols)}")

    def cost_k4(self, q, d):
        """T の 1 ステップ（次状態 q, 方向 d）にかかる T' のステップ数。"""
        if q in self.T.pseudo:
            return 1
        return 3 + 2 * (self.off[q] - self.lo[d])

    def encode_state(self, p):
        return self.H(self.dir[p], self.blk[p])

    def encode_cell(self, p, s):
        return self.C(self.off[p], s)

    def decode_state(self, hstate, counter):
        """(H 状態, 計数記号) -> T の状態。安定配置でなければ None。"""
        if hstate not in self.hstates or not self.is_counter(counter):
            return None
        i, s = self.split_counter(counter)
        for q in self.T.states:
            if self.encode_state(q) == hstate and self.off[q] == i:
                return q
        return None

    # -- 6 状態 H/A/B 系列
    def _build_hab6(self, offset):
        T = self.T
        m = len(T.states)
        self.idx = {q: k + 1 for k, q in enumerate(T.states)}
        self.nctr = 2 * m if offset else m
        self.k = 6
        H = {"+": "hp", "-": "hm"}
        A = {"+": "ap", "-": "am"}
        Bs = {"+": "bp", "-": "bm"}
        self.H6, self.hstates = H, set(H.values())
        self.states = [H["+"], H["-"], A["+"], A["-"], Bs["+"], Bs["-"]]
        self.symbols = list(T.symbols) + [self.C(i, s) for i in range(1, self.nctr + 1) for s in T.symbols]
        R = []
        for (p, s, t, d, q) in T.quints:
            e = self.dir[p]
            if q in T.pseudo:
                R.append((H[e], self.C(self.idx[p], s), t, d, q))
            else:
                v = self.idx[q] + (m if (offset and e == "+") else 0)
                R.append((H[e], self.C(self.idx[p], s), self.C(v, t), d, H[d]))
        sentinels = {1, m + 1} if offset else {1}
        for d in "+-":
            e = OPP[d]
            for s2 in T.symbols:
                R.append((H[d], s2, self.C(1, s2), e, Bs[e]))                       # R2
            for i in range(2, self.nctr + 1):
                if i in sentinels:
                    continue
                for t in T.symbols:
                    R.append((Bs[e], self.C(i, t), self.C(i - 1, t), d, A[d]))       # R3
            for i in sorted(sentinels):
                for t in T.symbols:
                    R.append((Bs[e], self.C(i, t), t, d, H[d]))                       # R4
            for j in range(1, m):
                for s2 in T.symbols:
                    R.append((A[d], self.C(j, s2), self.C(j + 1, s2), e, Bs[e]))     # R5
        self.quints = R
        self.formula = (f"k = 6, n' = ({'2' if offset else ''}m + 1) n = {len(self.symbols)}")
        self.encode_state = lambda p: H[self.dir[p]]
        self.encode_cell = lambda p, s: self.C(self.idx[p], s)

        def cost(q, d):
            return 1 if q in T.pseudo else 3 + 2 * (self.idx[q] - 1)

        def decode_state(hstate, counter):
            if hstate not in self.hstates or not self.is_counter(counter):
                return None
            i, s = self.split_counter(counter)
            for q in T.states:
                if self.idx[q] == i and H[self.dir[q]] == hstate:
                    return q
            return None

        self.cost_k4 = cost
        self.decode_state = decode_state

    # -- 符号化 / 復号
    def encode_conf(self, state, pos, tape):
        tape = list(tape)
        while pos >= len(tape):
            tape.append(self.T.blank)
        tape[pos] = self.encode_cell(state, tape[pos])
        return (self.encode_state(state), pos, tape)

    def decode_tape(self, tape):
        return [self.split_counter(x)[1] if self.is_counter(x) else x for x in tape]

    def decode_conf(self, state, pos, tape):
        """T' の配置 -> T の配置 (state, pos, tape)。状態は復号できなければ None（過渡配置）。"""
        tape = list(tape)
        while pos >= len(tape):
            tape.append(self.T.blank)
        if state in self.T.pseudo:
            st = state
        else:
            st = self.decode_state(state, tape[pos])
        return (st, pos, self.decode_tape(tape))

    def step(self, delta, conf):
        state, pos, tape = conf
        while pos >= len(tape):
            tape.append(self.T.blank)
        r = delta.get((state, tape[pos]))
        if r is None:
            return None
        t, d, q = r
        tape[pos] = t
        pos += MOVE[d]
        if pos < 0:
            return "fell"
        return (q, pos, tape)

    # -- 出力
    def title(self):
        return (f"kstate variant={self.variant} blocks={self.blocks[0]},{self.blocks[1]} "
                f"from {self.T.name}: {len(self.T.states)} states {len(self.T.symbols)} symbols "
                f"-> {self.k} states {len(self.symbols)} symbols")

    def emit(self, out, maxstep=None):
        T = self.T
        span = 3 + 2 * max(1, self.nctr)
        if maxstep is None:
            maxstep = T.maxstep * span + 10
        L = [f"title('{self.title()}').",
             f"% 生成: tools/kstate.py（{self.formula}）",
             f"% 計数記号 {self.prefix}<i>_<s> は「T が状態番号 i で記号 s を読んでいる」。"
             f" %% 行の出力は T' の停止テープを T の記号に復号したもの。",
             f"initial_state({self.encode_state(T.initial_state) if T.initial_state in self.dir else self.states[0]}).",
             "final_states([]).",
             f"states([{','.join(self.states)}]).",
             f"symbols([{','.join(self.symbols)}]).",
             f"blank({T.blank}).",
             f"maxstep({maxstep}).",
             ]
        delta = {(p, s): (t, d, q) for (p, s, t, d, q) in self.quints}
        for (state, pos, tape, exp_steps, exp_out) in T.cases:
            st, ps, tp = self.encode_conf(state, pos, tape)
            steps, final, why = run(delta, T.blank, (st, ps, tp), maxstep)
            L.append(f"initial_conf([{st},{ps},[{','.join(tp)}]]).")
            if why == "maxstep reached":
                # 停止していないので期待ステップ数は書かない。数字で始まらない %% 行は
                # simulate.py / gen_lean.py が「期待値なし」と読む（Morita の null 例と同じ扱い）。
                # T' が maxstep' = maxstep(T)*span+10 で止まらないのは T が maxstep(T) 以内に停止しないとき。
                L.append(f"%% null (maxstep {steps} reached; T' does not halt within maxstep)")
            else:
                dec = "".join(self.decode_tape(final)).rstrip(T.blank)
                L.append(f"%% {steps} {dec}")
        for (p, s, t, d, q) in self.quints:
            L.append(f"[{p},{s},{t},{d},{q}].")
        out.write("\n".join(L) + "\n")


def run(delta, blank, conf, limit):
    """simulate.run と同じ数え方で走らせる。(steps, tape, why)"""
    state, pos, tape = conf
    tape = list(tape)
    for step in range(limit + 1):
        while pos >= len(tape):
            tape.append(blank)
        if pos < 0:
            return step, tape, "fell off the left end"
        r = delta.get((state, tape[pos]))
        if r is None:
            return step, tape, "halt (no rule)"
        t, d, q = r
        tape[pos] = t
        pos += MOVE[d]
        state = q
        if q in PSEUDO:
            return step + 1, tape, f"halt ({q})"
    return limit, tape, "maxstep reached"


# ---------------------------------------------------------------- 逐段等価性
def _window(tape, pos, blank, w=3):
    """ヘッド位置 pos の前後 w セル（ヘッドのセルは [ ] で囲む）。診断用。"""
    cells = []
    for i in range(pos - w, pos + w + 1):
        if i < 0:
            continue
        c = tape[i] if i < len(tape) else blank
        cells.append(f"[{c}]" if i == pos else c)
    return " ".join(cells)


def _show(conf, blank):
    st, pos, tape = conf
    return f"{st}@{pos} {_window(tape, pos, blank)}"


def lockstep(cons: Construction, delta_p, state, pos, tape, max_t_steps):
    """T を 1 ステップずつ進め、T' を予測ステップ数だけ進めて、安定配置の復号が一致するか。

    返り値: (ok, t_steps, tp_steps, reason)。ok のときの reason は
      "both halt (no rule)" / "both halt (<疑似状態>)" / "both fell off the left end" /
      "step budget reached (still in lockstep)"  — T が max_t_steps 以内に停止しなかった。
    max_t_steps に記述ファイルの maxstep を渡せば simulate.py の打ち切りと同じ意味になる
    （Morita の urtm10-8 には maxstep 以内に停止しない例がある）。
    ステップの数え方は simulate.run と同じ: 実行した規則の本数（疑似状態に入る規則、
    左端から落ちる規則も 1 本と数える）。
    ok でないときの reason には最初の不一致の T ステップ番号と、T' の生配置・その復号・T の配置
    （状態@ヘッド位置 とヘッド前後の窓）を入れる。
    """
    T = cons.T
    blank = T.blank
    t_conf = (state, pos, list(tape))
    p_conf = cons.encode_conf(state, pos, tape)
    t_steps = tp_steps = 0
    if cons.decode_conf(*p_conf) != (t_conf[0], t_conf[1], _pad(t_conf[2], p_conf[2], blank)):
        return False, 0, 0, f"initial decode mismatch: T'={_show(p_conf, blank)} vs T={_show(t_conf, blank)}"
    while t_steps < max_t_steps:
        st, ps, tp = t_conf
        while ps >= len(tp):
            tp.append(blank)
        r = T.delta.get((st, tp[ps]))
        if r is None:
            # T は停止（規則なし）。T' も安定配置で規則なしのはず。
            pst, pps, ptp = p_conf
            while pps >= len(ptp):
                ptp.append(blank)
            if (pst, ptp[pps]) in delta_p:
                return False, t_steps, tp_steps, (f"T halted (no rule) after step {t_steps} but T' has a rule: "
                                                  f"T'={_show(p_conf, blank)}")
            return True, t_steps, tp_steps, "both halt (no rule)"
        t, d, q = r
        t_falls = ps + MOVE[d] < 0           # T はこのステップで左端から落ちる
        cost = cons.cost_k4(q, d)
        for k in range(cost):
            nxt = cons.step(delta_p, p_conf)
            if nxt is None:
                return False, t_steps, tp_steps, (f"T' halted early in T step {t_steps + 1} "
                                                  f"(sub-step {k + 1}/{cost}): T'={_show(p_conf, blank)}")
            if nxt == "fell":
                tp_steps += 1
                if t_falls and k == 0:      # R1 が T と同じ向きに動いて同時に落ちる
                    return True, t_steps + 1, tp_steps, "both fell off the left end"
                return False, t_steps, tp_steps, (f"T' fell off the left end in T step {t_steps + 1} "
                                                  f"(sub-step {k + 1}/{cost}) but T does not")
            p_conf = nxt
            tp_steps += 1
        nxt = T.step(t_conf)
        t_steps += 1
        if nxt == "fell":
            return False, t_steps, tp_steps, f"T fell off the left end at step {t_steps} but T' did not"
        t_conf = nxt
        dec = cons.decode_conf(*p_conf)
        exp = (t_conf[0], t_conf[1], _pad(t_conf[2], p_conf[2], blank))
        if dec != exp:
            return False, t_steps, tp_steps, (
                f"decode mismatch after T step {t_steps}: T'={_show(p_conf, blank)} "
                f"decoded={dec[0]}@{dec[1]} {_window(dec[2], dec[1], blank)} "
                f"vs T={exp[0]}@{exp[1]} {_window(exp[2], exp[1], blank)}")
        if q in T.pseudo:
            return True, t_steps, tp_steps, f"both halt ({q})"
    return True, t_steps, tp_steps, "step budget reached (still in lockstep)"


def check_cases(T: Machine, cons: Construction, delta_p, max_t_steps=None, maxstep_p=None):
    """記述ファイルの各初期配置について逐段等価性を検査し、(ok, 報告 1 行) の列を返す。

    * T は max_t_steps（既定: T の maxstep）で打ち切る。%% 行の期待ステップ数は simulate.py が
      maxstep で打ち切った値なので、それより先まで追うと「maxstep 以内に停止しない例」が必ず
      不一致になる（実データ urtm10-8 で lockstep NG と出た原因）。
    * T' 単体の実行（simulate.py と同じ数え方）は maxstep_p（既定: emit が書く maxstep'）で打ち切り、
      T が停止した例では逐段のステップ数と一致、打ち切った例では逐段のステップ数以上を要求する。
    """
    if max_t_steps is None:
        max_t_steps = T.maxstep
    if maxstep_p is None:
        maxstep_p = T.maxstep * (3 + 2 * max(1, cons.nctr)) + 10
    results = []
    for k, (state, pos, tape, exp_steps, exp_out) in enumerate(T.cases):
        ok, ts, tps, why = lockstep(cons, delta_p, state, pos, tape, max_t_steps)
        budget = why.startswith("step budget")
        steps_p, _, why_p = run(delta_p, T.blank, cons.encode_conf(state, pos, tape), maxstep_p)
        problems = []
        if not ok:
            problems.append(why)
        if exp_steps is not None and ts != exp_steps and not (budget and ts < exp_steps):
            problems.append(f"T steps {ts} != expected {exp_steps}")
        if budget:
            if steps_p < tps:
                problems.append(f"T' alone halts at {steps_p} < lockstep {tps}")
        elif steps_p != tps:
            problems.append(f"T' alone: {steps_p} steps ({why_p}) != lockstep {tps}")
        extra = [x for x in problems if x != why]
        line = (f"{'ok ' if not problems else 'NG '}{T.name} case{k}: T {ts} steps (expected {exp_steps}) "
                f"~ T' {tps} steps (simulate: {steps_p}); {why}" + ("; " + "; ".join(extra) if extra else ""))
        results.append((not problems, line))
    return results


def _pad(tape, ref, blank):
    tape = list(tape)
    while len(tape) < len(ref):
        tape.append(blank)
    return tape


def parse_title(path):
    """出力ファイルの title から variant と blocks を読む。"""
    t = fact_of(path, "title", "") or ""
    mv = re.search(r"variant=(\S+)", t)
    mb = re.search(r"blocks=(\d+),(\d+)", t)
    if not mv:
        raise SystemExit(f"{path}: title has no 'variant=' (not produced by kstate.py?)")
    return mv.group(1), (int(mb.group(1)), int(mb.group(2))) if mb else (1, 1)


# ---------------------------------------------------------------- CLI
def cmd_convert(a):
    T = Machine(a.input)
    blocks = tuple(int(x) for x in a.blocks.split(","))
    cons = Construction(T, a.variant, blocks)
    with (open(a.output, "w") if a.output else sys.stdout) as out:
        cons.emit(out, a.maxstep)
    print(f"{T.name}: m={len(T.states)} (m+={len(cons.Qd['+'])}, m-={len(cons.Qd['-'])}) n={len(T.symbols)} "
          f"|delta|={len(T.quints)} -> variant={a.variant} blocks={blocks}: "
          f"k={cons.k} n'={len(cons.symbols)} |delta'|={len(cons.quints)}  [{cons.formula}]",
          file=sys.stderr)


def cmd_check(a):
    T = Machine(a.input)
    variant, blocks = parse_title(a.output)
    cons = Construction(T, variant, blocks)
    _, _, quints_p = parse(a.output)
    if set(quints_p) != set(cons.quints) or len(quints_p) != len(cons.quints):
        print(f"NG {a.output}: rule set differs from a fresh regeneration")
        return False
    delta_p = {(p, s): (t, d, q) for (p, s, t, d, q) in quints_p}
    allok = True
    for ok, line in check_cases(T, cons, delta_p, a.max_t_steps, maxstep_of(a.output)):
        allok &= ok
        print(line)
    return allok


def cmd_decode(a):
    T = Machine(a.input)
    variant, blocks = parse_title(a.output)
    cons = Construction(T, variant, blocks)
    _, _, quints_p = parse(a.output)
    delta_p = {(p, s): (t, d, q) for (p, s, t, d, q) in quints_p}
    for k, (state, pos, tape, exp_steps, exp_out) in enumerate(read_cases(a.output)):
        steps, final, why = run(delta_p, T.blank, (state, pos, tape), maxstep_of(a.output))
        st, ps, tp = cons.decode_conf(state, pos, final)
        # 停止時のヘッド位置と状態を取り直す
        print(f"case{k}: T' {steps} steps, {why}; decoded tape = {''.join(tp).rstrip(T.blank)}")
    return True


def main(argv):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    c = sub.add_parser("convert")
    c.add_argument("input")
    c.add_argument("-o", "--output")
    c.add_argument("--variant", default="k4", choices=["k4", "hab6", "hab6-offset"])
    c.add_argument("--blocks", default="1,1", help="k4 のみ: b+,b-")
    c.add_argument("--maxstep", type=int)
    c.set_defaults(fn=cmd_convert)
    k = sub.add_parser("check")
    k.add_argument("input")
    k.add_argument("output")
    k.add_argument("--max-t-steps", type=int, default=None,
                   help="T をここで打ち切る（既定: 入力の maxstep。%% 行の期待値と同じ打ち切り）")
    k.set_defaults(fn=cmd_check)
    d = sub.add_parser("decode")
    d.add_argument("input")
    d.add_argument("output")
    d.set_defaults(fn=cmd_decode)
    a = ap.parse_args(argv)
    ok = a.fn(a)
    return 0 if ok is not False else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
