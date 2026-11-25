# How many negative inputs suffice?

For a graph, a universal family of negative tests has to cover every nonadjacent pair. A test covers a pair when it contains both vertices. A missed pair gives a one-gate counterexample, the AND of those two vertices. The general Lean theorem includes singletons and the empty set, so it also applies to circuits with unary or constant gates. [Exact testing criterion](SmallAnd.lean)

For the order-four plane, **17 tests suffice and at least 11 are necessary**. The explicit family covers all 756 nonadjacent pairs and all singletons. Lean verifies every test is an independent set and proves the detection result for every monotone binary circuit. [Tests](small-suite.json) · [Closed Lean theorem](Plane4Compact.lean)

The earlier family consisting of the 42 images of the posted input is irredundant within that orbit. The smaller family uses other independent sets.

The search uses a graph with one vertex per nonadjacent pair. Two such vertices conflict if their endpoints include an incidence. A set of pairs can share one negative test exactly when they contain no conflict, since the union of their endpoints is then independent. Lean proves that coloring the conflict graph is equivalent to a universal test family of the same size, for any finite graph. Its general formulation includes the demands of size zero and one. Coloring the uncovered pairs after removing a few tests gives candidate improvements. Each accepted improvement is checked against all pairs. [Equivalence to coloring](TestColoring.lean) · [Initial search](search-suite.py) · [Coloring repair](improve-suite.py)

## A counting lower bound

An independent test with $p$ points and $l$ lines satisfies $(p+4)(l+4)\le100$. To see this, let $a_j$ count selected points on line $j$. Each point is on five lines and each pair of points is on one line. Hence $\sum a_j=5p$ and $\sum a_j^2=p^2+4p$. The selected lines all have $a_j=0$. Cauchy–Schwarz gives $25p^2\le(21-l)(p^2+4p)$. Rearranging yields the bound for $p>0$, and $p=0$ follows from $l\le21$.

Give each pair on the same side weight one and each nonincident mixed pair weight five. There are 420 same-side pairs and 336 nonincident mixed pairs, of total weight 2,100. A test covers weight $\binom p2+\binom l2+5pl\le210$. Equality requires $(p,l)$ to be $(21,0)$, $(0,21)$, or $(6,6)$. These small numerical inequalities are kernel-checked for all integer values satisfying the geometric bound. [Counting lemmas](TestCounts.lean)

Ten tests would have to attain equality everywhere and cover each pair exactly once. Each equality case covers zero or 36 mixed pairs. Since 336 is not a multiple of 36, at least eleven tests are needed.

## The Fano plane needs exactly eight tests

For each of the seven points, take that point together with its four nonincident lines. Add the set of all seven points. These eight tests cover all nonadjacent pairs. Two distinct lines have a union of five points, so the test of either remaining point contains both lines.

The same moment calculation gives $(p+2)(l+2)\le18$. Assign same-side pairs weight one and mixed pairs weight four. The 42 same-side pairs and 28 mixed pairs have total weight 154. Any independent test covers at most 22, with equality only for one point and four lines, or four points and one line. Seven tests would all have to attain equality and cover every point pair exactly once. Each such test covers zero or six point pairs, while there are 21 in total. This proves the lower bound of eight. The Lean counting lemma derives both planes' strict bounds from the incidence inequality and pair-coverage totals. [Counting lemmas](TestCounts.lean)
