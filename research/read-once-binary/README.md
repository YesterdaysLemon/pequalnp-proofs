# Substituting arbitrary binary gates into an essential input

Suppose a Boolean function $f$ depends on input $p$. Choose a fresh input $q$ and a Boolean operation $h$ that depends on both its arguments. In every occurrence of $p$, substitute $h(p,q)$. **The minimum number of genuine two-input gates increases by exactly one.** Fan-out is unrestricted, all sixteen binary operations are available, and constants and unary operations are free. The ten choices of $h$ include XOR, NAND and the two directed differences. [Lean proof](BinarySubstitution.lean)

The upper bound computes $h(p,q)$ once. For the lower bound, fix $q$ to a constant for which $p\mapsto h(p,q)$ is either the identity or negation. A free choice of input polarity recovers $f$. The fresh input was essential before the restriction, so at least one binary gate disappears. The proof checks that an invertible unary section exists in both directions for every one of the ten operations. [Restriction argument](../induced-small-graphs/EssentialRestrictions.lean)

## Counting every gate

For any function depending on at least two primary inputs, charging every listed gate gives the same minimum as charging only gates that depend on both arguments. Compile a circuit for the normalized truth function. If the result needs a final negation, its output came from a binary gate. Stop the list at that gate and complement its truth table. The proof handles arbitrary fan-out and the project's convention for reads of a wire that does not yet exist. [Compiler and proof](BinaryWireCost.lean)

The hypothesis about two essential inputs matters for a raw gate count. The function $\lnot p$ has weighted size zero and ordinary size one.

## Consequences

- A read-once formula on $N$ distinct inputs, using any binary operations that depend on both inputs, has exact ordinary circuit size $N-1$. The formula itself provides the upper bound, even when competing circuits can share wires freely.
- Start from $F_n=(\bigwedge_i a_i)\lor\bigvee_i(a_i\land b_i)$ for $n\ge2$, and make $d$ fresh-input substitutions. The resulting function has ordinary minimum $3n+d-2$. For example, substituting XOR for one input and NAND for another in $F_2$ gives an exact six-gate function on six inputs. [Original family](../L-meta-13719/)
- Starting from the five-cycle edge function gives ordinary minimum $7+d$ after $d$ substitutions. Replacing one input by its XOR with a sixth variable gives an exact eight-gate function. [Five-cycle base case](../induced-small-graphs/)

The inductive relation permits later substitutions at either child of an earlier substitution. The proofs apply directly to the project's `BinaryCircuit` evaluator. [Exact-size theorems](ReadOnceBinary.lean)

## Replay

With the repository's pinned Lean toolchain and dependencies installed, run the following from the repository root.

```sh
bash research/read-once-binary/check.sh
```

The script compiles the dependencies and the three modules here in a clean temporary directory and prints the axioms of the main declarations.
