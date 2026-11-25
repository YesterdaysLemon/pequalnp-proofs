# Exact binary circuit size of majority on five inputs

A vote is true when at least three inputs are true. With arbitrary two-input Boolean gates, the smallest circuit for this vote has **nine gates**. With AND and OR, it needs **ten**. The ten-gate lower bound holds even when every wire may be complemented for free, or when every two-input operation except XOR and XNOR is available. Fan-out is unrestricted. Lean checks both lower bounds and both explicit circuits. [Witness circuits and size theorems](MajoritySizes.lean)

The same one-gate difference occurs on arbitrarily many inputs. Start with majority of five. Replace any current input by the AND or OR of itself and a fresh input, and repeat in any order. After `d` replacements the resulting function has an unrestricted optimum of `9 + d` and an AND/OR optimum of `10 + d`, even with free wire complements. For example, majority of `(a AND b), c, d, e, f` takes ten arbitrary gates or eleven AND/OR gates. [Expansion theorem](MajorityExpansions.lean)

## Lower bound

1. Fix one voter to false. The remaining vote is three-of-four. A finite search rules out six arbitrary gates for this function. The dual cofactor, two-of-four, has the same lower bound. The finite checks split at the first gate and run in the Lean kernel. [Search decomposition](SearchFrontier.lean) · [Four-input certificate](ThresholdFour.lean)
2. In a smallest live circuit, the first gate combines two distinct voters. Its one output cannot distinguish all three possible counts of true votes in that pair. A later gate must have access to at least one of the two original voters. The finite collision witnesses make this step explicit for every gate operation. [Voting collisions](MajorityCombinatorics.lean)
3. Fix that retained voter. The first gate becomes at most unary, and the retained voter becomes constant. The resulting circuit saves at least two binary gates and computes a cofactor requiring seven. This gives nine. If the first gate is nonparity, the witnesses force access to the relevant operand and a choice of its value that also makes the first output constant. The resulting circuit saves at least three gates. This gives ten. [Restriction argument](MajorityLower.lean)
4. For a fresh two-input substitution, fix one of its operands so that the other recovers the old input up to polarity. Restricting a live circuit saves at least one gate. Applying this argument with the nonparity family gives the lower bound after any sequence of substitutions. Each AND or OR substitution also adds just one gate to either upper witness. [Family-preserving restriction](FirstGateRestriction.lean)

The finite catalogue separately gives the exact sizes for all 7,581 labeled monotone functions on at most five input positions. [Five-input catalogue](../five-input-circuits/)

## Verification

From the repository root, with the project's pinned Lean toolchain and mathlib dependencies, run the following command. It rebuilds the proof modules in a temporary directory and prints the axioms used by the public theorems.

```sh
bash research/majority-five/check.sh
```
