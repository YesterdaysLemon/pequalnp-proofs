# Exact AND/OR formula size for the eleven-vertex graph

The edge function of the project's graph G11 needs **22 binary AND/OR gates as a formula**. A formula is a tree and may read an input variable any number of times. The smallest formula has 23 variable occurrences. The posted question allows internal gate outputs to be shared. Its 21-gate circuit bound remains open here. [Posted G11 step](https://pequalnp.com/desk/step?gap=L-meta-2384)

The upper witness chooses seven vertices covering the sixteen edges, assigns each edge to one of those vertices, and writes an OR of seven stars. Lean evaluates the resulting formula on all 2,048 inputs and identifies the function with the project's own definition on the posted edge list. [Witness](G11Upper.lean) · [Project definition and theorem](G11Project.lean)

## Lower bound

Consider the Karchmer–Wigderson game where a row is one of the sixteen edges, and a column is one of the twenty-four maximal independent vertex sets. An answer is an endpoint of the edge that is absent from the independent set. Every AND/OR formula gives a partition of these 384 cells into monochromatic rectangles, one per variable occurrence. At OR gates split the rows according to which operand is true. At AND gates split the columns according to which operand is false. Lean proves this construction for arbitrary finite row and column sets. [Formula-to-partition proof](KWPartition.lean)

For a rectangle labeled by a vertex, its rows form a nonempty subset of the edges incident to that vertex. G11 has 85 such choices of label and row set. Rectangles with the same choice may be combined across columns. A Boolean constraint system selects at most 22 choices and asks for exactly one covering rectangle at every cell. Lean proves that any formula with at most 21 gates would give a satisfying assignment. It also constructs the constraint system from the graph data. [Graph encoding](G11Game.lean) · [Selection and cardinality](KWSemantics.lean) · [Soundness for G11](G11Bridge.lean)

The constraint system is unsatisfiable. The bundled LRAT certificate has 55,227 actions. The replay uses the standard Lean LRAT checker on exactly the constraint system in the theorem. The kernel checks that a successful LRAT check implies the stated lower bound, and the replay evaluates that check on the certificate. [Certificate](formula-22.lrat.gz) · [LRAT interface](KWEncoding.lean)

## Reproduce the formula result

With the repository's pinned Lean toolchain and mathlib dependencies, run the following from the repository root. The replay builds the modules in a temporary directory, checks the certificate, and prints the axioms of the theorem.

```sh
bash research/G11-formulas/check.sh
```

To regenerate the certificate, add `--regenerate`. The script uses the CaDiCaL executable bundled with the pinned Lean toolchain.
