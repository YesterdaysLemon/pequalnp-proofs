# Testing AND gates on negative inputs of the order-four projective plane

The project's 124-gate question singles out an AND gate which fires on a particular ten-vertex independent set. This condition captures **every possible dirty AND**, up to relabeling an equivalent circuit. Lean checks the equivalence for the exact posted statement. Whether such a circuit of size at most 124 exists remains open here. [Posted step](https://pequalnp.com/desk/step?gap=L-meta-1894) · [Equivalence to the posted statement](Plane4Posted.lean)

## A test for any negative input

Call an AND active on an input when its output wire is true. In a fan-in-at-most-two AND/OR circuit, if some AND is active on a vertex set S, some AND is already active on a subset of S of size at most two. Take the first active AND in gate order. Each true operand before that gate is witnessed by a single primary input because its trace follows true OR branches backwards. The two witnesses together activate the AND. The proof covers constants, unary gates, repeated inputs, and nonexistent wires under the project's semantics. [General Lean theorem](SmallAnd.lean)

A family of negative inputs therefore tests all AND gates if every negative set of size at most two lies in one member of the family. For the edge function of a graph, the negative inputs are its independent sets. If the tests miss a nonadjacent pair, the one-gate AND of those two vertices witnesses the omission.

## The 42 images of the posted input

Number the points and lines separately modulo 21. Start with points 0, 1, 2, 6, 8, 18 and lines 3, 10, 12, 16. Translate both sets by each residue. Then swap points and lines, negate their coordinates, and repeat the translations. The resulting 42 independent sets cover all 756 unordered pairs of distinct nonadjacent vertices.

The test family is irredundant. In the original set, point pair {0,18} belongs to no other member. Its images give a private pair for each of the 42 tests. Lean verifies pair coverage, independence, the private pairs, and the transport of circuit gates under the relabelings. A counterexample firing on any independent set can be relabeled to fire on the posted input at precisely the same size. [Finite geometry](Plane4Tests.lean) · [Circuit transport](Plane4Transport.lean)

Using other independent sets reduces the suite to **17 tests**. At least eleven are necessary. The corresponding optimum for the Fano plane is exactly eight. [Counting argument and explicit suites](test-counts.md)

## Formula bounds in three projective planes

For the Heawood graph, the incidence graph of the Fano plane, **27 binary AND/OR gates are necessary and sufficient as a formula**. For each point, OR together its three incident lines, then AND that result with the point. An OR tree combines the seven stars. This gives seven point leaves and 21 line leaves. Lean checks the matching lower bound with a signed integer weighting of the Karchmer–Wigderson game. Its total weight is 168, and any single-variable rectangle has weight at most six. A partition therefore needs at least 28 leaves. [General weighted formula bound](KWWeight.lean) · [Exact Fano theorem](FanoFormula.lean)

The same search for integer weights gives the following bounds. The weight assigned to a cell can be negative. To verify the maximum for a label, enumerate each subset of its incident edge rows, sum its weights at each eligible negative column, and keep the positive column sums. This checks every possible rectangle in the game.

| Plane order | Incidence edges | Maximal independent sets | Total weight | Maximum rectangle weight | Formula gate bounds |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 2 | 21 | 37 | 168 | 6 | 27 exactly |
| 3 | 52 | 704 | 22,464 | 378 | 59–64 |
| 4 | 105 | 25,237 | 15,120 | 144 | 104–125 |

The upper bounds use point stars and an OR tree. The order-three and order-four lower bounds are numerical certificate checks. The accompanying program verifies their integer weights directly. NumPy suffices for verification. SciPy is needed only when searching for weights. [Certificate verifier](plane-dual.py)

## Replay

With the repository's pinned Lean toolchain and mathlib installed, run the commands from the repository root.

```sh
bash research/plane-negative-tests/check.sh
python3 research/plane-negative-tests/verify-tests.py
python3 research/plane-negative-tests/plane-dual.py 2 research/plane-negative-tests/weights-2.json --check
python3 research/plane-negative-tests/plane-dual.py 3 research/plane-negative-tests/weights-3.json --check
python3 research/plane-negative-tests/plane-dual.py 4 research/plane-negative-tests/weights-4.json --check
```
