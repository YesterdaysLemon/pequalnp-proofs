# Exact circuit size for a conjunction and a matching

For every integer $n\ge 2$, consider the monotone function

$$
F_n(a,b)=\left(\bigwedge_{i=1}^n a_i\right)\lor
          \bigvee_{i=1}^n(a_i\land b_i).
$$

**Its minimum is $3n-2$ gates.** An AND/OR circuit attains the minimum. The lower bound allows every Boolean function of two arguments, including XOR. It counts only gates that depend on both arguments, so constants and unary operations are free. Fan-out is unrestricted.

At $n=3$, ordering the inputs as $a_1,a_2,a_3,b_3,b_2,b_1$ gives the [posted six-input problem L-meta-13719](https://pequalnp.com/desk/step?gap=L-meta-13719). Its truth table is `0xfeeefaaafcccf080`. An independent proof of the posted comparison is [upstream PR 18019](https://github.com/open-goat/pequalnp-proofs/pull/18019). The family proof in this directory uses the project's native circuit types.

## Why three gates disappear

Start with a circuit that computes $F_n$ and discard unused wires. All $2n$ inputs are essential. For any two distinct primary inputs, assigning their four possible pairs of values gives at least three distinct functions on the other inputs. To see this, keep the two matching pairs containing the chosen inputs. If both inputs belong to the same pair, keep any second pair. Set every other pair to $(a_i,b_i)=(1,0)$. This leaves $F_2$. Its six unordered pairs of inputs give 3, 4, 3, 3, 4 and 3 distinct functions in interleaved input order.

The first binary gate therefore has to leave at least one of its two primary inputs available for a subsequent use. If both disappeared, the rest of the circuit would learn only the gate's single Boolean value about them. It could distinguish at most two functions on the remaining inputs.

Choose a retained input and fix its entire matching pair to $(1,0)$. The first gate now costs zero. Immediately after it there are at least two distinct live wires whose restricted values are constant. One is the retained input. If the gate also read its partner, the gate's output is the second constant wire. Otherwise the partner is still available and supplies the second constant wire.

In any live computation with a nonconstant restricted output, $t$ distinct live wires fixed to constants save at least $t$ later binary gates. Follow the live wires forward. A gate reading a constant becomes a unary operation or a constant. Two constant operands can disappear at once only when their replacement is itself constant, so the net decrease in the count of live constant wires is at most one per such gate. A gate with two nonconstant operands cannot decrease this count. The restricted output is nonconstant, so the final count is zero. [Formal restriction lemma](FamilyLive.lean)

The restriction computes $F_{n-1}$. For $n\ge3$, this proves a saving of at least three gates. In the base case $F_2$, four essential inputs are present initially. The first gate retains an operand, so at least four wires remain live afterward. Reducing that number to one requires at least three more binary gates. Thus $F_2$ needs four and $F_n$ needs at least $4+3$n-2$=3n-2$.

For the upper bound, compute the conjunction of the first $n-1$ of the $a_i$. Place it in

$$
a_n\land\left(b_n\lor\bigwedge_{i<n} a_i\right).
$$

Compute the other $n-1$ products $a_i\land b_i$ and OR the $n$ terms together. These parts cost $n-2$, 2, $n-1$, and $n-1$ gates.

## Checked statements and replay

| Lean declaration | Statement |
| --- | --- |
| [`Paired.circuit_lower`](PairedCircuit.lean) | Every project `BinaryCircuit` computing the function has at least $3n-2$ gates that depend on both arguments. |
| [`Paired.monotone_upper`](PairedUpper.lean) | Constructs a project `Circuit` using exactly $3n-2$ AND/OR gates and checks its evaluation on every input. |
| [`Paired.binary_size_iff`](PairedExact.lean) | In the project's `HasBinarySize` interface, the function on $2n$ inputs has a circuit of size at most $s$ exactly when $3n\le s+2$. |
| [`Paired.monotone_replacement`](PairedExact.lean) | Every size bound attained by an AND/OR/NOT circuit is attained by an AND/OR circuit. |

The formal interfaces use the interleaved order $a_1,b_1,a_2,b_2,\ldots$. The finite base check evaluates the two-pair table in the Lean kernel. The induction works with an arbitrary finite set of pair indices. The construction compiles a monotone formula into the project's gate list, and the lower-bound compiler handles missing wires using the project's default value.

From a checkout with the repository's pinned Lean toolchain and Mathlib cache, run

```sh
bash research/L-meta-13719/check.sh
```

The script rebuilds all six proof modules in a fresh temporary directory, prints the axioms of the four interface theorems and runs [the independent Python audit](audit.py). The audit checks every input through $n=8$. A separate exhaustive circuit search rules out three gates at $n=2$ in 31 states and six gates at $n=3$ in 2,668 states, including XOR and free complements. It also reproduces the exact posted truth table.

The live-wire representation and compression proof derive from the project's [L-meta-9136](https://github.com/open-goat/pequalnp-proofs/blob/main/lean/PEqualNP/Outside/L_meta_9136.lean). The restriction lemma first appeared in our [L-meta-10590 submission](https://github.com/open-goat/pequalnp-proofs/pull/15586).
