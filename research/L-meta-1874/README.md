# Two outputs on the order-three plane

Step L-meta-1874 asks for a 63-gate lower bound for two wires in an unrestricted monotone circuit. Both wires must accept every incident point-line pair. On each quadrangle input at least one must reject, and each must reject an input accepted by the other. A quadrangle consists of four points with no three collinear. Its input selects those points and every line missing them.

## An extremal pair of outputs

Fix a point `z` outside a line `m`. Let `F` detect an incidence between any selected point and line. Define two monotone outputs.

* A accepts when `F` holds, or when some selected point lies on `m` and some selected line passes through `z`.
* B accepts when `F` holds, point `z` is selected, or line `m` is selected.

Their conjunction equals `F` on every input. If A accepts through its extra condition, selecting `z` or `m` completes an incidence. Lean checks quadrangles that distinguish the outputs in both directions.

A accepts **12** extra nonincident singleton pairs. B accepts **17**. Every extra pair from A and every extra pair from B have a cross incidence. This attains the previously proved bound that the smaller of two such sets has size at most 12. The construction works for every choice of `z` outside `m`. [Explicit construction and proof](Plane3LeakPacking.lean) · [Upstream packing bound](../../lean/PEqualNP/Outside/L_meta_6208.lean)

## A restricted 63-gate lower bound

Consider two ORs of independently built rectangle terms, with shared terms computed once. A rectangle ANDs a disjunction of points with a disjunction of lines. Suppose every shared rectangle contains only true incidences. Every extra pair of a private A rectangle must have its point on `m`. B may also use individual point or line inputs.

Lean proves that covering all 52 flags at both outputs requires total rectangle side weight, plus the number of B literals, of at least **65**. Even allowing two separate final OR trees, this costs at least **63** binary gates. This result applies to the construction above in the stated architecture. The original unrestricted lower bound remains open here.

The counting argument assigns four units to covering a flag at A and one at B. A shared rectangle is a star of at most four edges. For an A rectangle, either all its points lie on `m` or some point outside `m` lies on every one of its lines. In either case the number of true incidences is at most the sum of its side sizes. Each B literal covers four flags. Together these inequalities account for all 260 units.

## Exhaustive check of one shared circuit prefix

Twelve complete point stars on the 13-point plane, ORed together, take 59 gates. The search gives the remaining circuit free access to every side disjunction from each of the twelve stars, both constants, the individual inputs, and the shared result. Replacing a partial OR of completed stars by the shared result can only add required positives and preserves every negative. The same construction works with point and line roles reversed.

For each orientation there are 161 distinct free wire signatures on the 52 flags and 234 quadrangles. The search checks all 16,601 new first-gate signatures and every possible pair of incomparable outputs using up to three additional binary gates. Neither orientation has a separating pair in 62 gates by this route. [Exhaustive search](plane3_suffix.py)

Run the Lean proof from the checkout's `lean` directory after building `PEqualNP.Defs`. The Python search uses the standard library and one CPU thread.

```sh
lake env lean ../research/L-meta-1874/Plane3LeakPacking.lean
python3 ../research/L-meta-1874/plane3_suffix.py
```
