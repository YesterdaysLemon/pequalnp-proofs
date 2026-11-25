# The order-four plane with one incidence removed

The posted graph has 21 points, 21 lines and 104 edges. The existing point-star construction uses 124 gates. A 20-cycle gives a 51-gate lower bound even for circuits allowed to use NOT. Lean checks both bounds on the posted edge list. A search for the requested 123-gate circuit found no witness. [Posted step](https://pequalnp.com/desk/step?gap=L-meta-9743) · [Circuit and lower-bound proof](PuncturedPlane.lean)

There is also an exact result about local replacements. **For every nonempty four-cycle-free bipartite graph with matching number at most five, its edge function has minimum monotone binary circuit size `|E| + ν − 1`.** Here `ν` is the maximum matching size and a true input has both endpoints of some edge set to one. The proof below reduces the claim to 113 finite graphs. Two enumerations check the structural reduction. Exhaustive circuit searches settle the finite cases. This family result has a reproducible programmatic proof.

In particular, take any five or fewer points of the plane and try to replace all their stars by a single subcircuit. A cyclic shift, sending point `p` to line `p−1 mod 21`, gives a perfect matching avoiding the missing flag. It restricts to a matching saturating the selected centers. The family result gives exactly the cost of the original stars and their connecting ORs, even for a replacement with internal sharing and arbitrary depth. This conclusion applies to a subcircuit over the original input wires. A replacement that taps gates of the retained stars can share additional work.

## Reduction to 113 graphs

1. Suppose there is a counterexample and choose one with as few edges as possible. Take a vertex cover `S` of size `k = ν` by Kőnig's theorem. Every maximum matching pairs each vertex of `S` with a distinct vertex outside it. An edge with both ends in `S` would use two of the `k` available cover vertices for a single matching edge.
2. Outside the cover there are only isolated vertices, private neighbors of one cover vertex and shared neighbors of two or more. Two distinct shared neighbors cannot contain the same pair of cover vertices in their neighborhoods, since that would give a four-cycle. Each neighborhood lies on one side of the bipartition. Edges internal to the cover can cross its two sides.
3. For each set of shared neighborhoods, keep only enough available private neighbors to saturate the cover by a matching. Set the deleted leaves to zero one at a time. A deleted leaf is essential because its neighbor alone is negative and the pair is positive. Propagating zero through its first reader removes at least one gate. Every residual still contains the matching. Each removal decreases the predicted size by exactly one. Isolated inputs can be discarded. A smallest counterexample therefore occurs among the finite cores. The upper bound follows by assigning each edge to one covering endpoint, building a star at that endpoint, and ORing the star outputs.
4. The first enumerator generates the possible shared neighborhoods and internal edges, selects private neighbors and identifies isomorphic cores. An independent audit begins with pairs of cover vertices. For each pair, it decides whether that pair has a shared neighbor and which other vertices join its neighborhood. It then tests every choice of available private neighbors and looks for a listed core by trying all cover labelings of the catalogue graphs. For matching size five the audit checks 3,810 labelled shared-neighborhood templates and 83,511 saturating choices of available private neighbors. [Enumerators](five_cover.py) · [Independent coverage audit](cover_audit.py)

| Maximum matching | Nonisomorphic cores | Maximum inputs | Maximum edges |
| ---: | ---: | ---: | ---: |
| 1 | 1 | 2 | 1 |
| 2 | 2 | 4 | 3 |
| 3 | 5 | 6 | 6 |
| 4 | 18 | 10 | 12 |
| 5 | 87 | 15 | 20 |

The matching-four catalogue includes the two hubs joined by three internally disjoint paths of length three. Its nine edges need exactly twelve gates. Subdividing every edge of `K₄` gives a 12-edge graph needing fifteen gates. Subdividing every edge of `K₅` gives a 20-edge graph needing twenty-four. [Finite results and search counts](results.json)

## Circuit search

The checker uses every minimal positive input (an edge) and every maximal independent set as a negative input. These rows determine an exact monotone graph function. All nonisolated vertices are essential. In a minimum circuit every gate and input has a path to the output. The search enumerates both operations, their two predecessors and which predecessors have future uses. If there are `b` live wires, at least `b−1` further gates are needed. A positive row and a negative row must differ on some live wire that is true on the positive and false on the negative. An existing wire can replace a new gate if it is at least as large on the positive rows and at most as large on the negative rows. All suffix gates are monotone, which makes this substitution sound. Constants, repeated operands and unary gates simplify away in a minimum circuit for a nonconstant target.

One C++ search checks all 26 cores through matching size four using only these rules. A separate Python implementation uses the effects of deleting individual vertices. For matching size five, two C++ searches use the minimal-counterexample assumption to account for gates lost under restrictions.

When a coordinate is set to zero, the exact lower bound for the smaller graph bounds how many gates can disappear. A gate with a known constant operand disappears by constant propagation. Each constant wire still in the live bank must also disappear before the nonconstant output. Combining two constant wires leaves one constant wire, so a single such gate consumes at most one net constant. The first search tracks these losses for each single zero restriction.

The independent search uses zero and one restrictions together. If the coordinates fixed to one include an edge, the restricted target is constant and the search omits that restriction. Otherwise the target is an OR of the free neighboring literals and the edge function on the remaining induced graph. With a nonempty residual graph, successively fixing those literals to zero saves one gate each. With an edgeless residual, the OR of `d` literals requires `d−1` gates. Each nonempty residual graph has strictly fewer edges, so the minimal-counterexample assumption applies. All 87 matching-five cores pass both searches. [Single-deletion checker](deletion_search.cpp) · [Multiple-restriction checker](multi_search.cpp) · [Probe generator](multi_data.py)

## The full plane

The induced 20-cycle used in the Lean lower bound visits these vertices. Lines are numbered 21 through 41.

```text
0 26 5 22 2 23 3 24 4 21 14 34 13 39 11 37 20 27 10 38
```

The cycle function needs 29 gates. Fixing the other 22 inputs to zero in an order that keeps each deleted input essential gives 51 gates. A chordless-cycle enumeration found 1,152 induced 20-cycles and no longer cycle. For the upper bound the proof evaluates the project's explicit cover-circuit construction on all inputs, symbolically, and computes its exact size of 124. [Cycle enumeration](punctured_cycles.cpp) · [Cycle lifting](CycleLifting.lean)

A separate search tested 48 point, line and mixed-center starting circuits and 5,952 single-gate deletions followed by local repairs. It checked candidates on all 104 minimal positives and 24,925 maximal negatives. It found no 123-gate circuit in these neighborhoods. [Repair search](punctured_repair.py)

## Reproduction

The finite family check uses Python's standard library and a C++20 compiler. The command rebuilds both catalogues, audits every cover class, and runs the multiple-restriction search on every core. It writes the per-core counts to `scratch/replay.json`.

```sh
python3 verify-cover-family.py scratch
g++ -O3 -std=c++20 punctured_cycles.cpp -o count-cycles
./count-cycles
```

The optional whole-plane repair experiment reuses the earlier plane search. A checkout of the consolidated research branch contains both directories. From `research/L-meta-9743` run `PYTHONPATH=../L-meta-4197 python3 punctured_repair.py --seeds 24`. [Consolidated research branch](https://github.com/YesterdaysLemon/pequalnp-proofs/tree/research/contributor-notes/research)

To check both Lean files, start in the repository's `lean` directory with its pinned toolchain.

```sh
src=$(cd ../research/L-meta-9743 && pwd)
lake build PEqualNP.MetaComplexity.L106 PEqualNP.MetaComplexity.Helpers.PermInputs PEqualNP.MetaComplexity.Helpers.CoverCircuitList
lake env lean -R "$src" -o .lake/build/lib/lean/CycleLifting.olean "$src/CycleLifting.lean"
lake env lean -R "$src" "$src/PuncturedPlane.lean"
```
