# Cleaning AND gates by their incident pairs

[L-meta-3457](https://pequalnp.com/desk/step?gap=L-meta-3457) asks for a size-preserving change to a fan-in-two monotone circuit computing a bipartite edge function. All AND gates already reject single vertices. The desired circuit must also make every AND gate reject every nonincident point–line pair.

## A size-preserving rewrite

For a gate $g$, let $S_g$ be the set of genuine edges whose two endpoints alone make $g$ true. Replace every AND with empty $S_g$ by a zero-input OR. When $S_g$ consists of one edge, replace that AND with the AND of the two input vertices of the edge. Keep the gate indices and the output index. Lean checks the following claims for every finite bipartite incidence relation, including ones with four-cycles.

- Every new wire is pointwise below its old value. For the literal product, any input containing its two vertices dominates their isolated edge assignment. Monotonicity of the old wire gives the inequality.
- Every wire keeps its value on every genuine edge assignment. For a replaced gate this follows from the definition of $S_g$. For a retained gate it follows inductively from the values of its inputs.
- The output computes the original edge function. Each minimal positive input still reaches the output. Every larger positive input then reaches it by monotonicity, and pointwise domination excludes all false positives.
- Gate count, fan-in, backward reads, and rejection of one-hot inputs by every AND are preserved. Every AND that still accepts a nonincident pair accepts **at least two distinct genuine edges**. Consequently the full cleaning conclusion holds if every original AND that accepts a nonincident pair accepts at most one genuine edge. Clean ANDs may accept arbitrarily many edges.

The checked declarations are `prune` and `exactIfSparse`. They use the project’s actual `Circuit.wires` evaluator and allow sharing, isolated vertices, arbitrary output indices and empty relations. [Lean source](FlagPruning.lean)

There is also a graph-level consequence of the earlier circuit-size work. Assign each edge to one end in a minimum vertex cover, build the star at each used cover vertex, and OR the stars together. On a nonempty bipartite graph with $m$ edges and matching number $k$, this gives a clean circuit with at most $m+k-1$ gates by Kőnig’s theorem. The project’s forest lower bound and the earlier matching-number-three argument each show that every input circuit in their respective graph classes is at least this large. Thus the unrestricted cleaning conclusion also holds on all forests and on all four-cycle-free bipartite graphs of matching number at most three, even when individual dirty ANDs accept many true edges. The empty graph has a constant-false realization with zero gates using the project’s missing-output convention. [Lower-bound argument and sources](https://github.com/YesterdaysLemon/pequalnp-proofs/tree/8201da3d0888a76d9b39e16de8295b4076668315/research/L-meta-2872)

## Why a one-gate rewrite stops at two flags

Take the matching $p_0l_0,p_1l_1$. A seven-gate circuit first builds $(p_0 \lor p_1) \land (l_0 \lor l_1)$, then intersects it with $p_0 \lor l_1$ and $p_1 \lor l_0$. This computes the matching on all 16 inputs, and every AND rejects every singleton. The first AND fires on both matching edges and on both off-diagonal pairs.

At that AND, the bank contains four literal inputs and the two side ORs. Across both gate operations and all 36 ordered pairs of earlier wires, no replacement accepts both matching edges and rejects both off-diagonal pairs. Repeated inputs cover unary gates, and constant gates cannot distinguish those assignments. The entire circuit does have a clean three-gate implementation. The `MatchingExample` proofs check both complete circuits, the dirty gate and the local obstruction. [Lean source](FlagPruning.lean)

## Paying for a larger batch

Let $B$ be any set of gates that contains every AND accepting a nonincident pair. Compute all the $S_g$ on the original circuit. Build one literal product per distinct edge in $U=\bigcup_{g\in B}S_g$, and one OR of those products per distinct nonempty signature. Reuse these wires for the old gates in $B$. Rebuild all other gates in order. A missing wire represents false internally, so an AND with a false operand can be dropped and an OR with a false operand can use its other wire. A completely false output can use an absent wire under the project's evaluator.

As in the Lean argument, this circuit is pointwise below the original on corresponding wires and agrees on every genuine edge assignment. All new ANDs are literal products of incident edges. Each retained AND is pointwise below its original clean value on singleton and nonincident pairs. The output is exact. The number of gates is at most

$$
|C|-|B|+|U|+\sum_{S\in\{S_g:g\in B\}}\max(0,|S|-1).
$$

This gives a checkable sufficient condition for the posted size bound. For a chosen signature it always pays to include **every** old gate with that signature. The compiler minimizes the displayed bound by a minimum cut. Each signature has weight equal to its multiplicity minus its OR cost. Each edge has weight $-1$. Selecting a signature requires selecting all of its edges. Signatures of dirty ANDs are mandatory. A maximum-weight closed set in this network gives an optimal batch for this bound. The construction can use fewer gates after sharing OR prefixes, rerouting an output that already represents every true edge, and discarding unreachable gates. The general batch argument above is mathematical. The executable implementation and finite checks are in [batch_clean.py](batch_clean.py).

| Number of points and lines per side | Four-cycle-free labeled graphs | Input circuits | Dirty ANDs alone meet the counting bound | Optimized batch meets it | Actual cleaned circuit fits |
| --- | ---: | ---: | ---: | ---: | ---: |
| 2 | 15 | 30 | 14 | 30 | 30 |
| 3 | 334 | 668 | 68 | 650 | 668 |

The two circuits per graph conjoin the clauses of its maximal independent sets in opposite orders, starting with a gate that requires a point and a line. For each circuit the check tests every input, every AND on every singleton and nonedge, and the gate-count inequality. It also enumerates all optional batches in every trial and compares their minimum with the flow result. The 668 three-point trials have 7,314 such choices in total. All 18 three-point trials outside the counting condition have five edges and nine input gates. Their optimized upper bound is eleven and the constructed circuit uses nine. These tests cover these two circuit families per graph. Whether every circuit in the posted problem has a no-larger clean realization remains open here.

From the checkout's `lean` directory, after building project dependencies, run

```sh
lake build PEqualNP.Defs PEqualNP.MetaComplexity.Helpers.LowMergeWires
lake env lean ../research/L-meta-3457/FlagPruning.lean
python3 ../research/L-meta-3457/batch_clean.py
```
