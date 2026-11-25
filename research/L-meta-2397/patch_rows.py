"""Compressed point-star boundary data for the order-three arc promise."""
import sys


LINES = [sum(1 << ((l + d) % 13) for d in (0, 1, 3, 9)) for l in range(13)]
THROUGH = [sum(1 << l for l, points in enumerate(LINES) if points >> p & 1) for p in range(13)]


def maximal(rows):
    result = []
    for row in sorted(set(rows), key=lambda r: (-r.bit_count(), r)):
        if all(row & r != row for r in result):
            result.append(row)
    return sorted(result)


def boundary(centers):
    groups = {}
    for l, points in enumerate(LINES):
        mask = sum(1 << i for i, p in enumerate(centers) if points >> p & 1)
        if mask:
            groups[mask] = groups.get(mask, 0) | (1 << l)
    columns = list(groups.values())
    charged = sum(g.bit_count()-1 for g in columns)
    width = len(centers) + len(columns)
    pos = sorted({(1 << i) | (1 << (len(centers) + j)) for j, mask in enumerate(groups)
                  for i in range(len(centers)) if mask >> i & 1})
    valid_points = [s for s in range(8192) if all((s & n).bit_count() <= 2 for n in LINES)]
    valid_lines = [s for s in range(8192) if all((s & n).bit_count() <= 2 for n in THROUGH)]
    def project(s, masks):
        return sum(1 << i for i, m in enumerate(masks) if s & m)
    point_cols = [1 << p for p in centers]
    projected_lines = [(s, project(s, columns) << len(centers)) for s in valid_lines]
    neg = set()
    for p in valid_points:
        lines_hit = sum(1 << l for l, points in enumerate(LINES) if p & points)
        point_projection = project(p, point_cols)
        neg.update(point_projection | q for l, q in projected_lines if not l & lines_hit)
    neg = maximal(neg)
    assert all(p & n != p for p in pos for n in neg)
    assert all(any(p & ~n == (1 << i) for p in pos for n in neg) for i in range(width))
    return width, charged, pos, neg


if __name__ == "__main__":
    centers = tuple(map(int, sys.argv[1:]))
    assert centers and len(set(centers)) == len(centers) and all(0 <= p < 13 for p in centers)
    width, charged, positives, negatives = boundary(centers)
    print(width, 5 * len(centers) - 2 - charged, len(positives), len(negatives))
    print(*positives)
    print(*negatives)
