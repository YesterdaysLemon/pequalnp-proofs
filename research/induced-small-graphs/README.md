# Exact small graph circuits and an induced-cycle lower bound

The edge function of a graph answers whether the selected vertices contain both ends of at least one edge. An induced five-cycle gives a lower bound on this function for graphs of any size.

**Theorem.** A loopless graph on $N$ non-isolated vertices containing an induced five-cycle needs at least $N+2$ binary gates. This holds with arbitrary fan-out, all sixteen Boolean operations of two arguments, and free constants and unary operations. Extra isolated vertices can be omitted. [Lean theorem](InducedCycle.lean)

The five-cycle itself needs seven gates. The upper bound is the following expression, where juxtaposition means AND.

$$x_0(x_1\lor x_4)\lor x_2(x_1\lor x_3)\lor x_3x_4.$$

For the lower bound, Lean's kernel rules out all circuits of size six. The finite check includes XOR and exhaustive wire reuse. It checks all 231 pairs of five-bit inputs on which the edge function takes opposite values. Fixing the other $N-5$ vertices to zero leaves that cycle. Each discarded vertex is essential to the original function because turning it on beside one neighbor selects an edge. The circuit loses at least one binary gate per discarded input. [Seven-gate bound](CycleCircuit.lean) · [Search instance](CycleTable.lean)

The restriction argument works for any Boolean function. If a projection fixes $t$ distinct essential variables, leaves a nonconstant function $g$, and maps every remaining primary wire to a constant or an available literal, then the original circuit costs at least $t$ gates more than the minimum for $g$. Other variables may be renamed, identified or complemented in the same projection. [Projection and restriction lemmas](EssentialRestrictions.lean)

**Equality examples.** Replace a vertex of the five-cycle by any number of independent vertices with the same neighbors. Do this at any of its five vertices. An OR of each group recovers the original cycle input, giving an $N+2$ gate circuit. The lower bound proves it is optimal. More generally, recursively replacing any input by its AND or OR with a fresh input yields exact size $7+d$ after $d$ replacements. [Expansion theorem](CycleExpansions.lean)

The induced-cycle argument also supplies the lower bound in an eight-vertex project submission. Its eleven-gate monotone witness combines two vertices with identical neighborhoods. [Upstream submission](https://github.com/open-goat/pequalnp-proofs/pull/19130)

## Exhaustive catalogue through five vertices

A separate C++ enumeration found the same minimum over the full binary basis and over AND/OR for every graph in the table. The search covers each isomorphism class with no isolated vertices. Removing isolated vertices gives the circuit for any nonempty graph on at most five vertices. Each JSON record gives a representative, its number of labeled copies, both minima and both circuits. The Python driver checks both circuits on every assignment.

| Vertices | Classes | Labeled graphs | Exact full-basis and AND/OR gate counts (number of classes) |
| ---: | ---: | ---: | --- |
| 2 | 1 | 1 | 1 (1) |
| 3 | 2 | 4 | 2 (1), 4 (1) |
| 4 | 7 | 41 | 3 (3), 4 (1), 5 (2), 7 (1) |
| 5 | 23 | 768 | 4 (3), 5 (3), 6 (8), 7 (4), 8 (4), 10 (1) |

The five-clique is the unique five-vertex class above eight gates. Excluding a nine-gate full-basis circuit required 13,937,856 search calls for the whole clique after its smaller induced subgraphs had been classified. The native enumeration supplies the catalogue minima. The independent Lean lower bound above covers the five-cycle and its stated extensions. [Five-vertex catalogue](graph-5.json) · [Search](small_graph.cpp) · [Orbit enumeration and circuit replay](small-graphs.py)

The C++ search discards unused gates and visits possible banks of live wires, including alternatives that keep either or both operands. A bank must distinguish every relevant positive/negative pair. Each previously computed induced-subgraph lower bound limits the number of gates that can still be spent on values that become constant under restriction. In the full basis, normalizing each wire to zero on the all-zero assignment leaves AND, OR, XOR and both ordered differences as the nontrivial gate choices. In monotone mode, the search can also discard a wire dominated on all minimal positive and maximal negative inputs by an available wire. A node cap produces an explicit unknown result. Every displayed minimum finished within the cap.

## Replay

With the repository's pinned Lean dependencies and a C++20 compiler, run the following from the repository root.

```sh
bash research/induced-small-graphs/check.sh
```

The script checks the Lean declarations and their axioms, recompiles the search, regenerates the four catalogues, and compares them with the published records. The binary-circuit compiler, live-wire restriction and finite search build on the linked research packages. [Paired circuit library](../L-meta-13719/) · [Packed search](../L-meta-13560/) · [Input substitution](../read-once-inputs/)
