#!/usr/bin/env python3
"""Morita の Thm 5.5（RTM の 4 状態化変換）を一般化した構成で、
URTM 記述ファイル（`tools/check_urtm.py` が読める Prolog ファクト形式）を
状態数の少ない機械へ変換する。

使い方:
    python3 tools/kstate_convert.py <source.txt> --mode morita [-o out.txt]
    python3 tools/kstate_convert.py <source.txt> --mode pure [--maxblock D] [-o out.txt]
    python3 tools/kstate_convert.py --report

設計（符号化・規則スキーマ）はすべて呼び出し元の依頼文に書かれている。
このファイルはその設計をそのまま実装したもので、設計の再発明はしていない。

用語（依頼文と対応）:
    dir(q)   : q へ入ってくる規則の移動方向 ('+' か '-')。1 状態に入る規則の
               向きは全部同じ（Morita の可逆性条件）なので well-defined。
    ブロック : 状態集合の分割。q は (h(q), l(q)) = (ブロック番号, ブロック内の位置)。
    D        : 最大ブロックサイズ。マーカのカウンタは 0..D-1 を取る。
    pure     : ブロック内の全状態の dir が同じ。mixed: 両方混ざる。

--mode morita は H=1（ブロック 1 個、被模倣機械の全状態を保持）で
Morita の Thm 5.5 そのもの（4 状態）になる。
--mode pure は dir='+' の状態と dir='-' の状態を別々のブロック列に分け、
各ブロックを pure にすることで 3 状態ブロックだけで済ませる。
"""

import argparse
import glob
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from check_urtm import parse, split_top  # noqa: E402
import simulate  # noqa: E402


# ----------------------------------------------------------------------
# 記号・状態の表現
#
#   plain symbol : str
#   marker       : (s, c)       -- pure モード（フラグ無し）
#                  (s, c, flag) -- flag in {'u','d'}（mixed ブロックがあるとき）
# ----------------------------------------------------------------------

def fmt_sym(sym):
    if isinstance(sym, tuple):
        return "[" + ",".join(str(x) for x in sym) + "]"
    return str(sym)


def sym_sort_key(sym):
    """素の記号を先に、マーカを後ろに、マーカは (記号, 位置, フラグ) で並べる。"""
    if isinstance(sym, tuple):
        s = sym[0]
        c = sym[1]
        flag = sym[2] if len(sym) > 2 else ""
        return (1, s, c, flag)
    return (0, sym, 0, "")


def marker_u(s, c, flagged):
    return (s, c, "u") if flagged else (s, c)


def marker_d(s, c, flagged):
    return (s, c, "d") if flagged else (s, c)


def state_name(kind, h, mode):
    """kind in {'r0','r1','l0','l1'}。morita モードだけブロック接尾辞を落とす。"""
    if mode == "morita":
        return kind
    return f"{kind}_{h}"


# ----------------------------------------------------------------------
# 入力ファイルの読み込み
# ----------------------------------------------------------------------

def read_cases_flagged(path):
    """simulate.read_cases() と同じだが、元の行がコメントアウトされていたか
    （`commented`）も返す。initial_conf の非コメント/コメント構成を
    そのまま引き継ぐために必要（simulate.py 側は変更しない）。
    """
    cases = []
    lines = open(path, encoding="utf-8", errors="replace").read().splitlines()
    for i, line in enumerate(lines):
        stripped = line.lstrip()
        commented = stripped.startswith("%")
        body = stripped.lstrip("%").strip()
        if not body.startswith("initial_conf("):
            continue
        inner_s = body[len("initial_conf("):].rstrip()
        inner_s = inner_s.rstrip(".").rstrip(")").strip()
        if inner_s.startswith("[") and inner_s.endswith("]"):
            inner_s = inner_s[1:-1]
        parts = split_top(inner_s)
        if len(parts) != 3:
            continue
        state, pos, tape_s = parts[0], int(parts[1]), parts[2]
        tape = split_top(tape_s.strip()[1:-1])
        steps = out = None
        if i + 1 < len(lines):
            m = simulate.EXPECT.match(lines[i + 1])
            if m:
                steps = int(m.group(1).replace(",", ""))
                out = m.group(2) or None
        cases.append({
            "state": state, "pos": pos, "tape": tape,
            "steps": steps, "out": out, "commented": commented,
        })
    return cases


def load_source(path):
    """状態・記号・規則・blank・maxstep・initial_state・title・cases を返す。

    `states([...])` が宣言されていないファイル（urtm138-2.txt 等）では、
    規則中の状態が現れる順（先頭から）を代わりに使う。
    """
    states, symbols, quints = parse(path)
    if states is None:
        seen, seenset = [], set()
        for (p, s, t, d, q) in quints:
            for x in (p, q):
                if x not in seenset:
                    seenset.add(x)
                    seen.append(x)
        states = seen
    if symbols is None:
        used = {q[1] for q in quints} | {q[2] for q in quints}
        symbols = sorted(used)
    return {
        "states": states,
        "symbols": symbols,
        "quints": quints,
        "blank": simulate.blank_of(path),
        "maxstep": simulate.maxstep_of(path),
        "initial_state": simulate.fact_of(path, "initial_state"),
        "title": simulate.fact_of(path, "title", "''"),
        "cases": read_cases_flagged(path),
    }


# ----------------------------------------------------------------------
# dir(q) の計算と検証
# ----------------------------------------------------------------------

class ConversionError(Exception):
    pass


def compute_dir(states, quints):
    """dir(q) を計算する。0 シフト規則と非宣言状態行きの規則は落とす。

    戻り値: (dirmap, kept_quints, dropped_zero, dropped_nostate)
    mixed（1 状態に複数の向きから入る）や未到達があれば ConversionError。
    """
    declared = set(states)
    dirmap = {}
    dropped_zero = 0
    dropped_nostate = 0
    kept = []
    for q in quints:
        p, s, t, d, qn = q
        if d == "0":
            dropped_zero += 1
            continue
        if qn not in declared:
            dropped_nostate += 1
            continue
        kept.append(q)
        dirmap.setdefault(qn, set()).add(d)

    mixed = {q: sorted(dirmap[q]) for q in states if len(dirmap.get(q, ())) > 1}
    unreached = [q for q in states if q not in dirmap]
    if mixed or unreached:
        msg = ["dir(q) の計算に失敗した（設計の前提が崩れている）。"]
        if mixed:
            msg.append(f"  mixed（複数の向きから入る状態）: {mixed}")
        if unreached:
            msg.append(f"  unreached（入る規則が無い状態）: {unreached}")
        raise ConversionError("\n".join(msg))

    dirfinal = {q: next(iter(dirmap[q])) for q in states}
    return dirfinal, kept, dropped_zero, dropped_nostate


# ----------------------------------------------------------------------
# ブロック分割
# ----------------------------------------------------------------------

def assign_blocks(states, dirmap, mode, maxblock):
    """状態 -> (h, l) の割当てと、ブロック番号 -> 状態列 を返す。"""
    if mode == "morita":
        blocks = {0: list(states)}
    else:
        plus = [q for q in states if dirmap[q] == "+"]
        minus = [q for q in states if dirmap[q] == "-"]

        def chunk(lst):
            size = maxblock if maxblock and maxblock > 0 else (len(lst) or 1)
            return [lst[i:i + size] for i in range(0, len(lst), size)]

        blocks = {}
        hi = 0
        for part in (chunk(plus), chunk(minus)):
            for blk in part:
                blocks[hi] = blk
                hi += 1

    h, loc = {}, {}
    for hh, blk in blocks.items():
        for i, q in enumerate(blk):
            h[q] = hh
            loc[q] = i
    return h, loc, blocks


# ----------------------------------------------------------------------
# 変換本体
# ----------------------------------------------------------------------

def convert(info, mode, maxblock):
    states = info["states"]
    symbols_prime = list(info["symbols"])
    dirmap, kept, dropped_zero, dropped_nostate = compute_dir(states, info["quints"])
    h, loc, blocks = assign_blocks(states, dirmap, mode, maxblock)

    have_plus = {hh: any(dirmap[q] == "+" for q in blk) for hh, blk in blocks.items()}
    have_minus = {hh: any(dirmap[q] == "-" for q in blk) for hh, blk in blocks.items()}
    flagged = any(have_plus[hh] and have_minus[hh] for hh in blocks)
    d_global = max((len(blk) for blk in blocks.values()), default=0)

    quints_out = []

    # A: 模倣ステップの適用
    for (p, s, t, d, q) in kept:
        from_state = state_name("r0" if dirmap[p] == "+" else "l0", h[p], mode)
        to_state = state_name("r0" if d == "+" else "l0", h[q], mode)
        read_sym = marker_u(s, loc[p], flagged)
        write_sym = marker_d(t, loc[q], flagged)
        quints_out.append((from_state, read_sym, write_sym, d, to_state))

    for hh, blk in blocks.items():
        dh = len(blk)
        # B: 行き先セルの初期化
        for s in symbols_prime:
            if have_plus[hh]:
                quints_out.append((
                    state_name("r0", hh, mode), s, marker_u(s, 0, flagged),
                    "-", state_name("l0", hh, mode)))
            if have_minus[hh]:
                quints_out.append((
                    state_name("l0", hh, mode), s, marker_u(s, 0, flagged),
                    "+", state_name("r0", hh, mode)))
        # C: 元セルの減算 (j=1..dh-1)
        for j in range(1, dh):
            for s in symbols_prime:
                if have_plus[hh]:
                    quints_out.append((
                        state_name("l0", hh, mode), marker_d(s, j, flagged),
                        marker_d(s, j - 1, flagged), "+", state_name("r1", hh, mode)))
                if have_minus[hh]:
                    quints_out.append((
                        state_name("r0", hh, mode), marker_d(s, j, flagged),
                        marker_d(s, j - 1, flagged), "-", state_name("l1", hh, mode)))
        # D: 行き先セルの加算 (e=0..dh-2)
        for e in range(0, dh - 1):
            for s in symbols_prime:
                if have_plus[hh]:
                    quints_out.append((
                        state_name("r1", hh, mode), marker_u(s, e, flagged),
                        marker_u(s, e + 1, flagged), "-", state_name("l0", hh, mode)))
                if have_minus[hh]:
                    quints_out.append((
                        state_name("l1", hh, mode), marker_u(s, e, flagged),
                        marker_u(s, e + 1, flagged), "+", state_name("r0", hh, mode)))
        # E: 元セルが 0 になった（転送完了）
        for s in symbols_prime:
            if have_plus[hh]:
                quints_out.append((
                    state_name("l0", hh, mode), marker_d(s, 0, flagged),
                    s, "+", state_name("r0", hh, mode)))
            if have_minus[hh]:
                quints_out.append((
                    state_name("r0", hh, mode), marker_d(s, 0, flagged),
                    s, "-", state_name("l0", hh, mode)))

    states_out = sorted({q[0] for q in quints_out} | {q[4] for q in quints_out})
    symbols_out = sorted(
        ({q[1] for q in quints_out} | {q[2] for q in quints_out} | set(symbols_prime)),
        key=sym_sort_key)

    if info["initial_state"] not in dirmap:
        raise ConversionError(
            f"initial_state({info['initial_state']}) が states([...]) に無い")
    p0 = info["initial_state"]
    initial_state_out = state_name("r0" if dirmap[p0] == "+" else "l0", h[p0], mode)

    # check_kstate.py が「clean な配置」を元の配置へ復号するための逆引き表。
    #   state_kind: 変換後の状態名 -> (kind, ブロック番号)
    #   q_at      : (ブロック番号, ブロック内位置) -> 元の状態 q
    state_kind = {}
    for hh in blocks:
        state_kind[state_name("r0", hh, mode)] = ("r0", hh)
        state_kind[state_name("l0", hh, mode)] = ("l0", hh)
        if have_plus[hh]:
            state_kind[state_name("r1", hh, mode)] = ("r1", hh)
        if have_minus[hh]:
            state_kind[state_name("l1", hh, mode)] = ("l1", hh)
    q_at = {(h[q], loc[q]): q for q in states}

    return {
        "mode": mode, "maxblock": maxblock,
        "h": h, "l": loc, "blocks": blocks, "dirmap": dirmap,
        "have_plus": have_plus, "have_minus": have_minus, "flagged": flagged,
        "d_global": d_global,
        "quints_out": quints_out,
        "states_out": states_out, "symbols_out": symbols_out,
        "initial_state_out": initial_state_out,
        "dropped_zero": dropped_zero, "dropped_nostate": dropped_nostate,
        "kept": kept,
        "state_kind": state_kind, "q_at": q_at,
    }


def convert_conf(case, h, loc, dirmap, flagged, mode):
    state, pos, tape = case["state"], case["pos"], list(case["tape"])
    if state not in dirmap:
        raise ConversionError(f"initial_conf の状態 {state} が states([...]) に無い")
    if not (0 <= pos < len(tape)):
        raise ConversionError(f"initial_conf の位置 {pos} がテープ範囲外")
    new_state = state_name("r0" if dirmap[state] == "+" else "l0", h[state], mode)
    tape[pos] = marker_u(tape[pos], loc[state], flagged)
    return new_state, pos, tape


# ----------------------------------------------------------------------
# 生成した機械を自分で走らせる（simulate.run と同じロジックだが、
# マーカがタプルでも動くよう "".join に頼らずテープをリストのまま返す）
# ----------------------------------------------------------------------

def run_generic(quints, blank, state, pos, tape, limit):
    delta = {(p, s): (t, d, q) for (p, s, t, d, q) in quints}
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
        pos += {"-": -1, "0": 0, "+": 1}[d]
        state = q
        if q in ("halt", "null"):
            return step + 1, tape, f"halt ({q})"
    return limit, tape, "maxstep reached"


# ----------------------------------------------------------------------
# 出力ファイルの生成
# ----------------------------------------------------------------------

def render(src_path, info, conv, out):
    mode, maxblock = conv["mode"], conv["maxblock"]
    n = len(info["symbols"])
    m = len(info["states"])
    blocks = conv["blocks"]
    m_plus = sum(1 for q in info["states"] if conv["dirmap"][q] == "+")
    m_minus = sum(1 for q in info["states"] if conv["dirmap"][q] == "-")

    lines = []
    lines.append(f"% kstate_convert.py --mode {mode}"
                  + (f" --maxblock {maxblock}" if maxblock else "")
                  + f" で {os.path.basename(src_path)} から生成。")
    lines.append("% 注意: 各 initial_conf 直後の %% 行のステップ数は、"
                  "この生成器が生成した機械を自分で実際に走らせて数えた実測値であり、"
                  "文献（Morita 2017 等）に記載の値ではない。")
    lines.append(f"% 元: m={m} 状態, n={n} 記号, "
                 f"dir + = {m_plus}, dir - = {m_minus}")
    lines.append(f"% 変換後: {len(conv['states_out'])} 状態, "
                 f"{len(conv['symbols_out'])} 記号, "
                 f"{len(conv['quints_out'])} 規則"
                 f"（0シフト規則 {conv['dropped_zero']} 本, "
                 f"非宣言状態行き規則 {conv['dropped_nostate']} 本を除外）")
    lines.append(f"% ブロック分割（H={len(blocks)}, D={conv['d_global']}, "
                 f"flagged={conv['flagged']}）:")
    for hh in sorted(blocks):
        blk = blocks[hh]
        dirs = {conv["dirmap"][q] for q in blk}
        lines.append(f"%   h={hh} dir={sorted(dirs)} size={len(blk)}: {blk}")
    lines.append("%")

    # 題名は Morita 自身の urtm4-168.txt の書き方に合わせ、
    # 「変換後のサイズ + converted from + 元の題名」にする。
    # 元の題名をそのまま写すと、生成物が元機械のサイズを名乗ってしまう。
    src_title = info["title"].strip()
    if src_title.startswith("'") and src_title.endswith("'"):
        src_title = src_title[1:-1]
    title = (f"'URTM({len(conv['states_out'])},{len(conv['symbols_out'])})"
             f" converted from {src_title}'")
    lines.append(f"title({title}).")
    lines.append(f"initial_state({conv['initial_state_out']}).")
    lines.append("final_states([]).")
    lines.append("states([" + ",".join(conv["states_out"]) + "]).")
    lines.append("symbols([" + ",".join(fmt_sym(s) for s in conv["symbols_out"]) + "]).")
    lines.append(f"blank({info['blank']}).")
    # maxstep は元の 4*(D+1) 倍くらいの安全側の値にする。
    # 模倣 1 ステップは構成された機械の最大 2*(D-1)+3 ステップに対応する
    # （A・B・E で 3 ステップ、C/D のペアを最大 D-1 回で 2*(D-1) ステップ。
    #  tools/check_kstate.py で実測・手計算の両方から確認した）。
    # 元の maxstep をそれだけ引き伸ばしても届かない場合の余裕を見込んだ。
    new_maxstep = info["maxstep"] * 4 * (conv["d_global"] + 1)
    lines.append(f"maxstep({new_maxstep})."
                 f"  % 元 maxstep({info['maxstep']}) * 4*(D+1), D={conv['d_global']}")
    lines.append("")

    for case in info["cases"]:
        try:
            new_state, pos, tape = convert_conf(
                case, conv["h"], conv["l"], conv["dirmap"], conv["flagged"], mode)
        except ConversionError as e:
            lines.append(f"% 変換不能な initial_conf: {e}")
            continue
        conf_txt = ("initial_conf([" + new_state + "," + str(pos) + ",["
                    + ",".join(fmt_sym(x) for x in tape) + "]]).")
        prefix = "" if not case["commented"] else "% "
        lines.append(prefix + conf_txt)
        steps, _final, _why = run_generic(
            conv["quints_out"], info["blank"], new_state, pos, tape, new_maxstep)
        out_word = case["out"] or "-"
        # 期待値行は必ず行頭 `%%` で出す（`% %%` だと simulate.py の EXPECT に
        # 掛からず、コメントアウトしたケースが**黙って未検査**になる。
        # Morita 自身の記述ファイルも、コメントアウトした initial_conf の
        # 直後の期待値行は行頭 `%%` で書いている）。
        lines.append(f"%% {steps} {out_word}")

    lines.append("")
    for (frm, r, w, d, to) in conv["quints_out"]:
        lines.append(f"[{frm},{fmt_sym(r)},{fmt_sym(w)},{d},{to}].")
    lines.append("")

    text = "\n".join(lines)
    if out:
        with open(out, "w", encoding="utf-8") as f:
            f.write(text)
    else:
        print(text)


# ----------------------------------------------------------------------
# --report
# ----------------------------------------------------------------------

def report():
    paths = sorted(
        p for p in glob.glob("data/urtm/urtm*.txt")
        if "36654" not in p)
    print(f"{'file':<20}{'m':>5}{'n':>5}{'m+':>5}{'m-':>5}"
          f"{'morita(4,n)':>14}{'pure(3H,n(D+1))':>18}")
    for path in paths:
        name = os.path.basename(path)
        try:
            info = load_source(path)
            states = info["states"]
            n = len(info["symbols"])
            m = len(states)
            dirmap, _kept, _dz, _dn = compute_dir(states, info["quints"])
            m_plus = sum(1 for q in states if dirmap[q] == "+")
            m_minus = sum(1 for q in states if dirmap[q] == "-")
            morita_sz = (4, n * (2 * m + 1))
            h_default = (1 if m_plus else 0) + (1 if m_minus else 0)
            d_default = max(m_plus, m_minus)
            pure_sz = (3 * h_default, n * (d_default + 1))
            print(f"{name:<20}{m:>5}{n:>5}{m_plus:>5}{m_minus:>5}"
                  f"{str(morita_sz):>14}{str(pure_sz):>18}")
        except (ConversionError, ValueError, KeyError) as e:
            print(f"{name:<20}  変換不能: {e}")

    print()
    print("--maxblock を振ったときの (状態数, 記号数):")
    for path in paths:
        name = os.path.basename(path)
        try:
            info = load_source(path)
            states = info["states"]
            n = len(info["symbols"])
            dirmap, _kept, _dz, _dn = compute_dir(states, info["quints"])
            m_plus = sum(1 for q in states if dirmap[q] == "+")
            m_minus = sum(1 for q in states if dirmap[q] == "-")
            mx = max(m_plus, m_minus)
            if mx == 0:
                continue
            row = []
            for d in range(1, mx + 1):
                h, _l, blocks = assign_blocks(states, dirmap, "pure", d)
                have_plus = {hh: any(dirmap[q] == "+" for q in blk)
                             for hh, blk in blocks.items()}
                have_minus = {hh: any(dirmap[q] == "-" for q in blk)
                              for hh, blk in blocks.items()}
                nstates = sum(3 if (have_plus[hh] != have_minus[hh]) else 4
                              for hh in blocks)
                d_global = max((len(blk) for blk in blocks.values()), default=0)
                nsymbols = n * (d_global + 1)
                row.append(f"D={d}:({nstates},{nsymbols})")
            print(f"  {name}: " + " ".join(row))
        except (ConversionError, ValueError, KeyError) as e:
            print(f"  {name}: 変換不能: {e}")


# ----------------------------------------------------------------------
# CLI
# ----------------------------------------------------------------------

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("source", nargs="?")
    ap.add_argument("--mode", choices=["morita", "pure"])
    ap.add_argument("--maxblock", type=int, default=None)
    ap.add_argument("-o", "--output")
    ap.add_argument("--report", action="store_true")
    args = ap.parse_args()

    if args.report:
        report()
        return

    if not args.source or not args.mode:
        ap.error("source と --mode を指定するか、--report を使うこと")

    info = load_source(args.source)
    try:
        conv = convert(info, args.mode, args.maxblock)
    except ConversionError as e:
        print(f"エラー: {e}", file=sys.stderr)
        sys.exit(1)

    print(f"[{os.path.basename(args.source)}] 0シフト規則 {conv['dropped_zero']} 本、"
          f"非宣言状態行き規則 {conv['dropped_nostate']} 本を除外した", file=sys.stderr)
    render(args.source, info, conv, args.output)


if __name__ == "__main__":
    main()
