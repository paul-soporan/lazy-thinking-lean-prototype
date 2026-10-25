# 1. The foundation: a sorting obligation with unknown helpers

The research motivation is to start with a specification and a recursive scheme, inspect what the proof requires of its helpers, and turn that requirement into separately usable contracts. Here the specification and scheme are intentionally small so the logical step stays visible.

## The specification

For lists of natural numbers, define:

\[
\operatorname{SortSpec}(X,Y)
\quad\Longleftrightarrow\quad
\operatorname{Sorted}(Y)\;\land\;Y\sim X.
\]

Here \(Y\sim X\) means that the lists are permutations: every value occurs the same number of times in each. This expresses multiset equality without implementing a separate multiset theory. Merely preserving the set of values would be insufficient: `[1]` must not count as a sorted version of `[1, 1]`.

Lean encodes this in `Spec.lean` using `List.Pairwise` for sortedness and `List.Perm` for contents.

## The recursive scheme

Lists of length zero or one are returned unchanged. For longer lists:

\[
F(X)=c(F(l(X)),F(r(X))).
\]

The symbols \(l,r,c\) stand for the split and combine helpers. They are function parameters, not untrusted logical axioms.

Let \(Y=F(l(X))\) and \(Z=F(r(X))\). The induction hypotheses give:

\[
\operatorname{SortSpec}(l(X),Y),\qquad
\operatorname{SortSpec}(r(X),Z).
\]

The remaining obligation is that these guarantees imply \(\operatorname{SortSpec}(X,c(Y,Z))\). This implication, universally quantified over the input and the recursive results, is `JointRequirement`.

It is a requirement about possible recursive results, rather than permission to assume that a recursive function is correct. The full program also needs both recursive lists to be shorter. `SchemeRequirements` packages recursive decrease with the joint requirement.

## The initial decomposition

A sufficient split contract says:

\[
l(X)\mathbin{++}r(X)\sim X,
\]

and requires both lengths to decrease for nontrivial inputs. A sufficient combine contract says:

\[
\operatorname{Sorted}(Y)\land\operatorname{Sorted}(Z)
\Rightarrow
\operatorname{SortSpec}(Y\mathbin{++}Z,c(Y,Z)).
\]

The notation \(++\) denotes list append. In the content argument it supplies a concrete representation of the union of the two input multisets. It need not be the actual combining operation: ordinary merging also preserves the contents of \(Y++Z\).

The content calculation is:

\[
c(Y,Z)\sim Y++Z
\sim l(X)++r(X)
\sim X.
\]

The middle step uses the two recursive permutation guarantees. Sortedness comes from the combine contract. `joint_of_contracts` proves this decomposition; `scheme_of_contracts` adds decrease.

This is a sufficient decomposition. The implementation does not claim it is necessary, weakest, or automatically discovered from first principles.

## Obtaining an actual program

`Scheme.lean` defines `sortUsing` with termination measured by list length. Its theorem `sortUsing_correct` proves that any helpers satisfying `SchemeRequirements` produce a correct sorter. Lists of length at most one supply the base cases.

`Witness.lean` supplies a concrete half split and a merge operation, using Lean's existing list-merge theory. Their contract proofs instantiate the generic scheme. This separates the reusable synthesis step from the mathematical facts about particular helpers.

`VerifiedSorter` packages the executable function with its all-input correctness theorem. There is no unproved obligation hidden inside that package.

## What the original tactic does

`lazy_thinking` attempts a small initial proof, applies the fixed decomposition if needed, and tries local assumptions or explicitly supplied facts on the resulting obligations. If a proof attempt fails, its assignments are rolled back. If no supplied fact proves a premise, that premise remains a goal.

This is the fixed-rule baseline for the next experiment. It does not yet analyze arbitrary induction proofs or synthesize an arbitrary contract language.

Continue with [the guard-search experiment](02-guard-search.md), where the combining operation may require more than sorted inputs.
