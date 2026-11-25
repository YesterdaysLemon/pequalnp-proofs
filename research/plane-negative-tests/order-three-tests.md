# A lower bound of eleven tests for the order-three plane

At least **eleven negative inputs** are necessary to detect every AND gate that fires on an independent input. An explicit family of 13 negative inputs suffices. [Test family](order-three-suite.json) · [Verifier](verify-order-three.py)

There are thirteen points, thirteen lines, and four points per line. Form the $13\times13$ nonincidence matrix $A$. Each row has nine ones. Any two distinct rows have six ones in common, since their incident line sets have sizes four and meet in one line. Hence $AA^\top=3I+6J$ is positive definite over the reals, and $A$ has rank thirteen.

An independent test with $p$ points and $l$ lines contributes a nonincidence rectangle of area $pl$. Every such rectangle has area at most twelve. One point leaves nine available lines, and two points leave six. Three collinear points leave three and three noncollinear points leave four. Any four points leave at most three: a collinear triple already ensures that bound, and if there is no collinear triple, the four points meet $4\cdot4-\binom42=10$ lines. The dual counts give the same bounds on the other side. Area twelve requires shape $(2,6),(6,2),(3,4)$, or $(4,3)$.

Suppose ten tests suffice, padding shorter families with empty tests. Let $M$ be the sum of their rectangle matrices. It covers all 117 ones of $A$, and every summand has rank at most one. The nonnegative integer matrix $E=M-A$ has rank at most the sum of its entries: expand it as that many elementary matrices. Since $A=M-E$, the rank inequality forces at least $13-10=3$ excess entries, counted with multiplicity. Thus the ten rectangles have total area at least 120. All ten must have area exactly twelve.

The family must also cover the 156 pairs on the same side. A test of shape $(2,6)$ covers 16 such pairs, and one of shape $(3,4)$ covers nine. Even one test of the latter shape would give at most $9+9\cdot16=153$. Every test therefore has sides of sizes two and six. For each point, the total number of lines in the tests containing it is even. Covering its nine nonincident lines requires at least ten line occurrences. Across thirteen points this gives at least 130, contradicting total area 120.

This is a counting and rank argument. The program below checks the incidence matrix identity, all maximal independent-set shapes, and every pair in the explicit upper witness.

```sh
python3 research/plane-negative-tests/verify-order-three.py
```
