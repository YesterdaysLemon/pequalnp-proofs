# The matching-number-three case of the incidence circuit bound

[L-meta-2872](https://pequalnp.com/desk/step?gap=L-meta-2872) asks whether an exact fan-in-two AND/OR circuit on a four-cycle-free bipartite graph must have at least `|E| + |M| − 1` gates for every matching `M`.

**The bound holds for every such graph whose maximum matching has at most three edges.** On every nonempty graph in that class, the minimum is exactly `|E| + ν − 1`, where `ν` is its maximum matching size. This includes arbitrary numbers of vertices. The lower-bound argument also permits NOT gates. A counterexample to the posted statement would therefore need a graph with a matching of at least four edges.

## The cyclic case

1. In a bipartite graph with no four-cycle, a shortest cycle has even length at least six. Alternating edges on a cycle of length at least eight form a matching of size at least four. Under the matching bound every cyclic example therefore contains a six-cycle, and three alternating edges of that cycle already form a maximum matching.
2. An edge between two vertices outside that matching would extend it to four. Any two point vertices of the six-cycle already share a line vertex on the cycle. Any two of its line vertices likewise share a point. An outside vertex cannot have two neighbors on the cycle, since those neighbors and their common neighbor would give a four-cycle. Any additional edge between cycle vertices would also close a four-cycle. The nonisolated graph is consequently exactly the six-cycle with pendant leaves attached. The proof of `sixCycleStructure` checks these conclusions on the same bipartite edge and matching representation as the posted question. [Matching and six-cycle lemmas](MatchedCore.lean)
3. Let there be `t` leaves. The exact six-cycle function needs eight gates by the project's cycle theorem. Each leaf can be fixed to zero for a saving of at least one gate. Its neighbor alone is a false input, and the neighbor together with the leaf is a true input. After the leaf is fixed, the surviving six-cycle witnesses nonconstancy. Repeating this gives a lower bound of `8 + t = |E| + 3 − 1`. Isolated inputs may be identified with an existing input at no gate cost since the function ignores them. [Cycle lifting proof](CycleLifting.lean) · [Upstream exact cycle size](../../lean/PEqualNP/MetaComplexity/L106.lean) · [Input renaming](../../lean/PEqualNP/MetaComplexity/Helpers/PermInputs.lean)

For a forest, apply the project's forest lower bound. Every vertex cover meets each matching edge at a different vertex. A minimum vertex cover in a bipartite graph has size `ν` by König's theorem. The usual star circuit built from that cover attains `|E| + ν − 1`: assign each edge to one endpoint in the cover, form a star at each used endpoint, and OR the stars. If there are no edges, the inequality in the posted statement holds immediately. The graph classification and this assembly are given here as a mathematical argument. The linked local Lean files check the circuit restriction and structural lemmas. [Upstream forest theorem](../../lean/PEqualNP/MetaComplexity/L104.lean) · [Upstream star upper bound](../../lean/PEqualNP/MetaComplexity/L105.lean)

## Two reusable extensions

**Lifting any induced cycle.** Suppose the first `b ≥ 5` vertices induce a cycle. Order the remaining vertices so that each has an earlier neighbor, as is possible in a connected graph. Any fan-in-two circuit for the edge function on `N` vertices with `s` gates satisfies `N + ceil(b/2) ≤ s + 1`. The proof removes vertices in reverse order and then uses the exact cycle bound. The theorem `liftCycle` also works for any Boolean function whose singleton, pair and restricted-cycle values give the same dependence witnesses. In particular this gives the full posted bound on unicyclic bipartite graphs whose maximum matching is already attained on the cycle. Attaching a tree increases the vertex and edge counts equally. [Lean theorems](CycleLifting.lean)

**Attaching a two-edge path.** For any nonempty graph with edge function `f`, attach new vertices `v,u` and edges `wv,vu` at any old vertex `w`. This raises the minimum gate count by exactly three in the fan-in-two AND/OR/NOT model. The new function is

```text
f(x) OR (v AND (u OR x_w)).
```

The three displayed gates give the upper bound. For the lower bound, the new leaf `u` is essential, and either fixed value leaves a nonconstant function. The project's two-gate elimination lemma saves two gates for one of those values. For both values the remaining function depends on `v`, as witnessed by the old singleton `w`, for which `f` is false. Fixing `v` to zero saves one more gate and recovers `f`. The theorem `transfer` proves the lower-bound increment directly for every circuit. The matching number increases by exactly one because the edge `vu` extends an old maximum matching and both new edges share `v`. Any starting `|E| + ν − 1` lower bound that permits NOT gates therefore extends along an arbitrary sequence of these attachments. [Lean proof](PendantPath.lean)

## Eight-vertex search

The graph with two hubs joined by three internally disjoint paths of length three has nine edges and a matching of four. The posted lower bound predicts twelve gates. Its eight inputs have nine minimal positive rows and nine maximal negative rows. `theta_shards.py` encodes exact fan-in-two AND/OR synthesis on this boundary and splits the first gate under the twelve graph symmetries. A planted twelve-gate star circuit satisfies the CNF and is independently correct on all 256 inputs. The tested searches at ten and eleven gates reached their conflict budgets. They do not settle this graph. [SAT encoder](theta_shards.py)

Run the Lean files from the checkout's `lean` directory after building the listed dependencies.

```sh
lake build PEqualNP.Defs PEqualNP.MetaComplexity.L106 PEqualNP.MetaComplexity.Helpers.Parity
lake env lean ../research/L-meta-2872/CycleLifting.lean
lake env lean ../research/L-meta-2872/MatchedCore.lean
lake env lean ../research/L-meta-2872/PendantPath.lean
```

The optional SAT experiment requires `python-sat` with CaDiCaL 1.9.5.

```sh
python3 theta_shards.py 10 --conflicts 160000
python3 theta_shards.py 11 --conflicts 180000
```
