# How far rectangle covers get on the order-four plane

The open step L-meta-4197 asks for a monotone binary circuit with at most 124 gates. There are 21 points and 21 lines. Point `p` lies on line `l` when their difference modulo 21 is 0, 1, 4, 14, or 16.

## A sharp bound for rectangle formulas

A rectangle consists of a set of points and a set of lines for which every point lies on every line. Its formula ORs together the points, ORs together the lines, and ANDs those two results. Consider any collection of nonempty rectangles covering all 105 incident pairs. Building each rectangle separately and combining the results with binary OR gates costs at least **125 gates**. The 21 line stars achieve equality.

Two distinct points have only one common line. Consequently each valid rectangle has a side of size one and its other side has at most five elements. For side sizes `a` and `b`, this gives `6ab ≤ 5(a + b)`. Summing over a cover gives total side size at least 126, even with overlapping rectangles. The gate count is total side size minus one. The Lean file checks this calculation, the attaining construction, and uniqueness of the line containing a shared sum of two or more distinct point variables. It also checks the dual statement for line variables. The 124-gate question for general circuits remains open here. [Lean proof](Plane4RectangleCover.lean)

## Search on the exact Boolean function

The 105 positive incidence pairs and 25,237 maximal negative inputs determine the function on every input by monotonicity. To find the negatives, take a point subset, select every line disjoint from it, and check that adding any omitted point would create an incidence. An independent enumeration of all 2,097,152 point subsets gives the same test set. [Boundary check](check_plane_boundary.py)

Starting from 90 variants of the 125-gate construction, a single-region search tried replacing a gate and its unused predecessors with an existing wire or up to two new binary gates. A second search tried all 22,500 ways to bypass one gate by either of its inputs across those variants, then tried resynthesizing one surviving gate from any eligible wires. A further 90 starting circuits used a mixture of point and line stars. These searches found no circuit with 124 gates. Sampled rows screened candidates cheaply. Every candidate that passed the screen was checked on the full boundary. [Single-region search](plane_search.py) · [Two-region search](plane_repair.py)

## Reproduction

Run the Lean check from the checkout's `lean` directory with the pinned Lean 4.36.0 toolchain and Mathlib dependencies.

```sh
lake build PEqualNP.Defs
lake env lean ../research/L-meta-4197/Plane4RectangleCover.lean
```

Run the searches from this directory using Python 3.10 or later. Each uses one CPU thread.

```sh
python3 check_plane_boundary.py
python3 plane_search.py --redundant --seeds 1
python3 plane_repair.py --self-test
python3 plane_search.py --seeds 90 --max-size 124
python3 plane_repair.py --seeds 90
python3 plane_search.py --mixed --seeds 90 --max-size 124
```
