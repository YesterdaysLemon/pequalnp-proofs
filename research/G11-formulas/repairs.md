# Vertex-cover repairs after deleting edges of G11

The posted repair question fixes a set of uncovered edges `U` from a particular circuit. It asks for a minimum cover of the residual graph which can be completed to a cover of G11 within a specified budget. The following computation removes the graph optimization from that question. [Posted statement](https://pequalnp.com/desk/step?gap=L-meta-2384)

Let `k` be the minimum vertex-cover size of `G11 − U`. In **65,519 of the 65,536** edge-deletion sets, some minimum residual cover extends to a minimum cover of G11, which has size seven. The optimum repair adds exactly `7 − k` vertices. The other **17** edge-deletion sets require exactly `8 − k` additional vertices. For all seventeen, the output lists an optimal residual cover and a completed cover.

The posted condition is thus equivalent to showing that the circuit budget minus the number of deleted edges is at least this explicit repair cost for its particular deletion set. The relationship between that budget and the circuit remains open here.

Each bit of the deletion mask selects an edge in the order of the posted statement, beginning with bit zero. The exceptional masks in hexadecimal are

```text
8f00 af00 af40 afc0 bf40 cf00 cf80 cfc0 df80
ef00 ef40 ef80 efc0 ff00 ff40 ff80 ffc0
```

Two exhaustive algorithms check the list. First, for each vertex subset, record its uncovered edges and its smallest extension to a full cover. A minimum-over-subsets transform gives the lexicographically smallest pair (residual size, repair size) for each deletion mask. Second, encode all deletion sets in a 65,536-bit integer. For every vertex subset, intersect the truth columns of the edges it misses and use the twenty-four inclusion-minimal full covers to compute its best extension. Taking the first feasible pair in sorted order reproduces the same exception masks. The enumerations use Python's standard library and take less than a second on the development machine. [Program](repair.py) · [Counts and witnesses](repairs.json)

```sh
python3 research/G11-formulas/repair.py
```
