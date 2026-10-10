"""定理 A（k4, blocks 1,1）の疎版: 番号を最適に並べ、使われない計数記号を落とす。

need(q) = {q で読む記号} ∪ {q に入る規則が書く記号}。
計数値 i（方向 d）で要る記号 = ∪{ need(q) : q ∈ Q_d, off(q) ≥ i }。
番号の並べ方は、その総和を最小にする順（部分集合 DP）。

    python3 tools/kstate_sparse_k4.py _ data/urtm/urtm13-7.txt out/urtm4-79.txt   # → URTM(4,79)
"""
import sys
from functools import lru_cache

sys.path.insert(0, __file__.rsplit("/", 1)[0])
import kstate  # noqa: E402
from check_urtm import parse  # noqa: E402
from simulate import maxstep_of  # noqa: E402


def need_sets(T):
    need = {q: set() for q in T.states}
    for (p, s, t, d, q) in T.quints:
        need[p].add(s)
        if q in need:
            need[q].add(t)
    return need


def best_order(Q, need):
    """下（lo）から上（hi）への並び。上位の和集合の大きさの総和を最小にする。"""
    idx = {q: i for i, q in enumerate(Q)}

    def union(mask):
        u = set()
        for q in Q:
            if mask >> idx[q] & 1:
                u |= need[q]
        return u

    @lru_cache(None)
    def f(mask):
        if mask == 0:
            return 0, ()
        best = None
        for q in Q:
            if mask >> idx[q] & 1:
                c, order = f(mask & ~(1 << idx[q]))
                if best is None or c < best[0]:
                    best = (c, (q,) + order)      # q が集合の最下位
        return best[0] + len(union(mask)), best[1]

    return f((1 << len(Q)) - 1)


class Sparse(kstate.Construction):
    def _partition(self):
        super()._partition()
        self.need = need_sets(self.T)
        self.cost = {}
        for d in "+-":
            if self.Qd[d]:
                c, order = best_order(self.Qd[d], self.need)
                self.Qd[d] = list(order)
                self.cost[d] = c

    def _build_k4(self):
        super()._build_k4()
        keep = set(self.T.symbols)
        for d in "+-":
            for q in self.Qd[d]:
                for i in range(self.lo[d], self.off[q] + 1):
                    for s in self.need[q]:
                        keep.add(self.C(i, s))
        self.symbols = [s for s in self.symbols if s in keep]
        self.quints = [r for r in self.quints if r[1] in keep and r[2] in keep]
        self.formula = f"sparse k4: 番号を最適化し未使用の計数記号を除去（{len(self.symbols)} 記号）"


if __name__ == "__main__":
    T = kstate.Machine(sys.argv[2])
    cons = Sparse(T, "k4", (1, 1))
    with open(sys.argv[3], "w") as out:
        cons.emit(out)
    _, _, qp = parse(sys.argv[3])
    delta_p = {(p, s): (t, d, q) for (p, s, t, d, q) in qp}
    res = kstate.check_cases(T, cons, delta_p, None, maxstep_of(sys.argv[3]))
    print(f"{T.name}: m={len(T.states)} n={len(T.symbols)} -> k=4 n'={len(cons.symbols)} |delta'|={len(cons.quints)}"
          f"  (密なら {(len(T.states) + 1) * len(T.symbols)})  cost={cons.cost}")
    print("  順序:", {d: cons.Qd[d] for d in "+-"})
    ok = sum(1 for r in res if r[0])
    print(f"  lockstep: {ok}/{len(res)} ok")
    for r in res:
        if not r[0]:
            print("  ", r[1][:220])
