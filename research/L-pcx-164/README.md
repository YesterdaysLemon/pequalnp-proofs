# Resolution length for five pigeons and four holes

[L-pcx-164](https://pequalnp.com/desk/step?gap=L-pcx-164) asks whether every ordinary binary-resolution refutation of unary PHP(5,4) needs at least 120 listed clauses. The formula has five positive pigeon clauses and forty negative collision clauses. The project counts the axioms that appear in a refutation.

| Proof model | Result |
| --- | --- |
| Tree-like, counting every occurrence of an axiom | Exactly **377 lines**. There are 189 leaves and 188 inferences. |
| Tree-like, listing a repeated axiom only once | Exactly **233 lines**. The same 188 inferences use all 45 distinct axioms. |
| General resolution DAG | The counting argument below gives **at least 96 lines**. A Hall-clause construction gives 157. The 119-line threshold remains open here. |

## Two independent tree calculations

A resolution proof can be read backwards as a variable-query tree. Start at the empty clause. At a resolution on $x$, follow the positive parent when $x$ is false and the negative parent when $x$ is true. From a false resolvent the selected parent is false. At a leaf the assignment therefore violates its axiom.

The first calculation uses only 360 assignments with a unique violated axiom. If pigeon $p$ has no hole, the other four pigeons form one of 24 permutations. If two specified pigeons collide in a specified hole, the other three form one of six permutations of the remaining holes. All 45 possible labels occur.

For any remaining set of these assignments, the number of distinct labels is a lower bound on leaves. To look one level deeper, try every variable that splits the set and minimize the sum of the two child bounds. A variable constant on the remaining set gives an uninformative branch and may be skipped. The best lower bounds at depths 1, 2, 3, 4, 9, 14 and 15 are respectively 67, 86, 102, 105, 159, 187 and **189**. At depth 15 the two subproblems below the first variable need 142 and 47 leaves. [Critical-assignment recurrence](php_tree.py)

The second calculation tracks the three values unknown, false and true for each of the 20 variables. A state costs one leaf as soon as a pigeon clause or collision clause is false. Otherwise its cost is the minimum, over unassigned variables, of the sum of the two successor costs. The program identifies states under simultaneous pigeon and hole permutations. It evaluates **59,692** nonterminal equivalence classes and finds **189** leaves at the all-unknown state. An explicit tree attains the answer, and every resolution has been replayed against the original clauses. [Full-assignment calculation](php_tree_exact.cpp) · [Tree certificate](tree-certificate.json)

Lean checks the depth-two lower bound of 86 leaves, the resulting 130-line bound when axioms are shared, and the explicit 188-inference tree with all 45 original axioms. The lower bound of 189 leaves comes from the two finite calculations above. [Lean proof and explicit tree](TreeResolution.lean)

## A 96-line unrestricted lower bound

Choose a shortest refutation, retain the ancestors of its empty clause, and share equal axioms. Duplicate clauses can be redirected to their earlier occurrence. Tautologies can also be removed. If just one parent is tautological and the resolvent is not, the other parent is a subclause of the resolvent. When a premise has been replaced by a subclause, resolve the smaller premises if both pivot literals survive, or keep the premise that lost its pivot. This produces a tautology-free proof of no greater length. Every original axiom remains necessary because of the unique-violation assignments.

1. **At most one pigeon axiom is used only once.** Suppose pigeon clause $P_i$ has just one successor $R_i$. Every assignment missing pigeon $i$ and placing the others bijectively must falsify $R_i$. Following false parents from the root is forced to reach $P_i$, so the path must go through $R_i$. The only literals false on *all* those assignments are positive literals from row $i$. Since the proof is tautology-free, $R_i$ loses its pivot. Thus $R_i$ is a strict subclause of $P_i$. Deriving it requires every other pigeon axiom $P_j$. Without $P_j$, place pigeon $i$ in a hole omitted by $R_i$ and assign the other three required pigeons injectively to the remaining holes. This satisfies all remaining axioms and falsifies $R_i$. If two rows had single successors, each successor would have to precede the other. Two positive row axioms cannot resolve with one another. The five row axioms therefore use at least four extra parent references beyond their first uses.
2. **A short DAG has few repeated uses of derived clauses.** With $T$ inferences there are $2T$ parent references and $45+T-1$ non-root nodes, each used at least once. There are $T-44$ extra references in total. At 95 lines or fewer, $T\leq50$. After the four extra row references, at most two extra references to derived clauses remain.
3. **Two extra references do not give a large enough unfolding.** Orient the DAG from the empty clause toward its parents. There are no triangles. An inference result and one of its parents cannot have complementary literals in a tautology-free proof. All the parent's nonpivot literals remain in the result, and the opposite pivot has been removed from the other parent. Parallel parent edges are also impossible. If no inferred node occurs four times in the unrolled tree, it has at most $3T$ inferences. Four occurrences require two distinct joins with two incoming edges each. The first joins two paths of multiplicity one. Both paths into the second must descend from the first and have multiplicity two. At each join, the two paths from their last common fork form a cycle of length at least four. There are consequently at least three inferred nodes of multiplicity one before the first join and three of multiplicity two between the joins. All others have multiplicity at most four. The unrolled tree has at most $4T-15\leq185$ inferences, below the required 188. This rules out 95 lines.

The same unfolding count shows that a hypothetical 119-line refutation would need **at least two extra uses of derived clauses**. With just one extra use, unfolding at most 74 inferences yields at most 147. The 96-line calculation is a mathematical argument using the finite tree bound.

## Local restrictions on axiom use

A critical assignment for an axiom must falsify at least one clause derived immediately from it and different from it. Lean checks this statement for any annotated resolution trace. If every such successor of a collision axiom contains a negative literal outside its two endpoints, the successors must include at least three distinct clauses. Each such literal can be false on at most two of the six collision-critical assignments. If every successor of a pigeon axiom contains a negative literal, at least four distinct clauses are required, since a negative literal can be false on at most six of the 24 corresponding assignments. The proofs cover every pigeon, pigeon pair and hole. [Lean proof](CriticalExits.lean)

## Checking the results

From the checkout's `lean` directory, after building `PEqualNP.Defs`, run

```sh
lake env lean ../research/L-pcx-164/CriticalExits.lean
lake env lean ../research/L-pcx-164/TreeResolution.lean
```

Run the computations from this research directory with Python 3 and a C++20 compiler.

```sh
python3 php_tree.py 4 --depth 15
c++ -std=c++20 -O3 php_tree_exact.cpp -o /tmp/php_tree_exact
/tmp/php_tree_exact 10 /tmp/shared.json /tmp/unshared.json
python3 verify_certificates.py
```

The verifier checks each signed literal, both earlier parents, and the exact union after removal of the pivot. The Hall certificate has 112 binary inferences and lists each of the 45 axioms once. A 159-line upper-bound submission was already public when this assignment was acquired. [Hall certificate](hall-certificate.json) · [Earlier upstream submission](https://github.com/open-goat/pequalnp-proofs/pull/13435)
