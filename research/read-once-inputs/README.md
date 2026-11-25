# Replacing an essential input by a read-once formula

Let $f$ be any Boolean function with an essential input $p$. Replace every occurrence of $p$ by $p\land q$, where $q$ is a fresh input. The minimum number of binary gates increases by **exactly one**. The same holds for $p\lor q$. The theorem allows all sixteen Boolean operations of two arguments, repeated uses of a wire, and free unary operations and constants.

For the lower bound, fix $q$ to true for AND or false for OR. The restricted circuit computes $f$. Before restriction, $q$ is essential, so a circuit computing the expanded function must use it. Once $q$ is fixed, at least one binary gate can be removed. The proof tracks live wires to cover arbitrary fan-out. For the upper bound, compute the replacement once and send its output to every previous use of $p$. [Lower and upper bounds](ReadOnceSplit.lean) · [Project binary-circuit interface](SplitCircuits.lean)

If a monotone circuit already attains the minimum for $f$, then a monotone circuit also attains the new minimum. The construction inserts one gate and updates every gate-input index and the output index. It also works when the original circuit outputs an input directly. [Monotone circuit construction](SplitMonotone.lean)

## An exact infinite family

Start with

$$F_n(a,b)=(a_1\land\cdots\land a_n)\lor\bigvee_{i=1}^n(a_i\land b_i),\qquad n\ge2.$$

At each step choose any current input and replace it with its AND or OR with a new variable. A later step can split a variable introduced by an earlier step. After $d$ steps, the minimum is **$3n+d-2$ gates**, attained using AND and OR alone. There are $N=2n+d$ distinct essential inputs, giving the equivalent count $N+n-2$. Thus each original input may be replaced by a read-once monotone formula on its own set of leaves. [Base family](../L-meta-13719/) · [Expansion theorem](PairedExpansion.lean)

For example, start with $F_2=(a_1a_2)\lor(a_1b_1)\lor(a_2b_2)$. Replace $a_1$ by $(a_1\lor q)\land r$ everywhere it appears. The function on the six resulting variables has minimum six gates.

## Replay

Run the following from the repository root with the pinned Lean toolchain and project dependencies installed.

```sh
bash research/read-once-inputs/check.sh
```

The script compiles the six base modules and all four extension modules in a temporary directory and prints the axioms for the split identity and both exact-size results.
