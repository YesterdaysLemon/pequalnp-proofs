"""Two applications of the checked elimination theorem, with small graph restrictions."""
from collections import Counter
from functools import lru_cache
from itertools import permutations

from generic_fanout import ALL, EDGES, NEGATIVES, VERTICES, move
from generic_cycle import neighbors


ADJ = [{w for w in VERTICES if neighbors(v,w)} for v in VERTICES]
EXT = [sum(1 << j for j,n in enumerate(NEGATIVES) if n >> v & 1) for v in VERTICES]


@lru_cache(maxsize=100000)
def false(mask):
    choices = (1 << len(NEGATIVES))-1
    while mask and choices:
        bit = mask & -mask
        choices &= EXT[bit.bit_length()-1]
        mask ^= bit
    return bool(choices)


def vertices(s):
    return [v for v in VERTICES if s >> v & 1]


def has_edge(s):
    return any(s & e == e for e in EDGES)


def test_symmetry():
    def image(mask,p):
        return sum(1 << move(v,p) for v in vertices(mask))
    for fixed in VERTICES:
        assert {image(e,fixed) for e in EDGES} == set(EDGES)
        assert {image(n,fixed) for n in NEGATIVES} == set(NEGATIVES)


def known_projection(ones,p,q,free):
    return any(has_edge(ones | ctx | 1 << p) and false(ones | ctx | 1 << q)
               for ctx in [0]+[1 << v for v in free if v not in (p,q)])


def check_fanout(ones,zeros):
    free = vertices(ALL & ~(ones|zeros))
    for p,q in permutations(free,2):
        assert known_projection(ones,p,q,free), (ones,zeros,p,q)


@lru_cache
def candidates(size,cyclic):
    result = []
    def extend(path):
        if len(path) == size:
            if path[0] > path[-1] or cyclic != (path[-1] in ADJ[path[0]]):
                return
            if cyclic and (path[0] != min(path) or path[1] > path[-1]):
                return
            result.append(tuple(path))
            return
        for v in sorted(ADJ[path[-1]]):
            if v in path:
                continue
            allowed = path[1:-1] if len(path)+1 == size and cyclic else path[:-1]
            if any(w in ADJ[v] for w in allowed):
                continue
            extend(path+[v])
    for v in VERTICES:
        extend([v])
    return result


@lru_cache
def independent_rows(size,cyclic):
    def edge(mask):
        return bool(mask & (mask >> 1) or cyclic and mask & 1 and mask >> (size-1) & 1)
    return [m for m in range(1<<size) if not edge(m) and
            all(edge(m|1<<i) for i in range(size) if not m>>i & 1)]


def attach(ones,free,seed):
    remaining = set(free)-set(seed)
    order = list(seed)
    if not false(ones):
        return len(order)
    for _ in range(len(remaining)):
        for p in sorted(remaining):
            if any(false(ones|ctx) and has_edge(ones|ctx|1<<p)
                   for ctx in [0]+[1<<v for v in order]):
                order.append(p)
                remaining.remove(p)
                break
        else:
            break
    return len(order)


def bound(ones,zeros):
    free = vertices(ALL & ~(ones|zeros))
    best = 0
    shape = None
    allowed = set(v for v in free if not has_edge(ones|1<<v))
    for size,cyclic in ((8,True),(6,True),(8,False),(7,False),(6,False),
                        (5,False),(4,False),(3,False),(2,False)):
        complexity = size + ((size+1)//2 if cyclic else size//2) - (1 if cyclic else 2)
        ceiling = len(free)-size+complexity
        if ceiling <= best:
            continue
        for path in candidates(size,cyclic):
            if any(v not in allowed for v in path):
                continue
            if not all(false(ones | sum(1<<v for i,v in enumerate(path) if m>>i & 1))
                       for m in independent_rows(size,cyclic)):
                continue
            value = attach(ones,free,path)-size+complexity
            if value > best:
                best,shape = value, ("C" if cyclic else "P",size)
            if best == ceiling:
                break
    return best,shape


def next_round(ones,zeros):
    check_fanout(ones,zeros)
    histogram = Counter()
    worst = 100
    for v in vertices(ALL & ~(ones|zeros)):
        for val,cost in ((False,3),(True,4)):
            bit = 1 << v
            lb,shape = bound(ones | (bit if val else 0),zeros | (0 if val else bit))
            assert shape is not None
            histogram[(val,lb,shape)] += 1
            worst = min(worst,cost+lb)
    return worst,histogram


if __name__ == "__main__":
    test_symmetry()
    check_fanout(0,0)
    # By symmetry the first coordinate can be chosen as point 0. When it is
    # true, each of its four neighboring lines is a sufficient singleton.
    # Setting these four to zero saves at least one gate per line. The empty
    # input and a surviving edge witness nonconstancy at every step.
    literal_neighbors = sum(1<<w for w in ADJ[0])
    assert all(has_edge(1|1<<w) for w in ADJ[0]) and false(1)
    assert any(not (e & (literal_neighbors|1)) for e in EDGES)
    lower_false,hist_false = next_round(0,1)
    lower_true,hist_true = next_round(1,literal_neighbors)
    print("first false, child cases:",sorted(hist_false.items()),flush=True)
    print("first true, child cases after deleting four literals:",sorted(hist_true.items()),flush=True)
    print("restricted lower bounds:",lower_false,4+lower_true)
    print("two-round full lower bound:",min(3+lower_false,4+4+lower_true))
