# 2. Choosing a contract with a preserved precondition

The new development step asks a narrow question: **can a small search select a useful modular decomposition when the combiner may need an additional precondition?** Two patterns are supplied, and their premises must be proved. This gives a concrete experiment before attempting open-ended contract generation.

## Why the original contract is sometimes too strong

Merge accepts any two sorted lists. Concatenation does not: `[2]` and `[1]` are individually sorted, but `[2, 1]` is not.

Concatenation works if every left element is at most every right element. Call that condition separation:

\[
\operatorname{Separated}(U,V)
\quad\Longleftrightarrow\quad
\forall a\in U\;\forall b\in V,\ a\le b.
\]

The inequality is inclusive. Equal values may occur on both sides. Empty sides also satisfy the condition.

The extra condition creates two distinct questions. Can the split establish separation? If it does, why is separation still true after recursively sorting both sides?

## The transport step

Let \(U=l(X)\), \(V=r(X)\), and let \(Y,Z\) be their recursive results. Suppose:

\[
\operatorname{Separated}(U,V),\qquad Y\sim U,\qquad Z\sim V.
\]

To prove separation of \(Y,Z\), choose any \(a\in Y\) and \(b\in Z\). Permutations preserve membership, so \(a\in U\) and \(b\in V\). The original separation then gives \(a\le b\). This is the entire mathematical reason the precondition survives.

The proof does not use the recursive results' internal order. It uses their preservation of contents. That distinction matters when deciding what recursive guarantees are sufficient.

`Guards.lean` proves this fact as `separation_survives`. `Candidates.lean` presents it as an instance of a generic condition:

```lean
def GuardTransport (guard : CombiningGuard) : Prop :=
  ∀ u v ys zs, guard u v → ys.Perm u → zs.Perm v → guard ys zs
```

`CombiningGuard` simply means a predicate on two lists. `GuardTransport guard` says that this predicate is unchanged in the direction needed when both lists are replaced by permutations. This is a sufficient property; not every useful precondition has it.

## The guarded decomposition

The generic theorem has four mathematical premises:

| Premise | What must be established |
| --- | --- |
| Split contract | The split preserves all contents, and both recursive inputs are shorter. |
| Guard on the split | The original split lists satisfy a chosen predicate \(G\). |
| Guard transport | The recursive permutation guarantees carry \(G\) to the returned lists. |
| Guarded combine contract | Sorted inputs satisfying \(G\) produce a sorted output with their combined contents. |

In `Candidates.lean`, the theorem is `scheme_of_guarded_contracts`. Its logical order is:

1. Establish \(G(l(X),r(X))\) at the split.
2. Use the recursive permutation guarantees to obtain \(G(Y,Z)\).
3. Apply the guarded combine contract to get sortedness and \(c(Y,Z)\sim Y++Z\).
4. Use the same content calculation as before to conclude \(c(Y,Z)\sim X\).

The connecting content expression remains \(Y++Z\), representing the combined multiset. Adding a guard does not change it. This experiment explores the combining precondition, not the invention of a new connecting expression.

The theorem is generic in \(G\). The search currently instantiates it only with the supplied predicate `Separated`.

## A splitter that makes concatenation work for all inputs

The new witness uses a minimum-value partition. For a nonuniform input, choose its minimum \(m\), put all occurrences of \(m\) on the left, and put the remaining elements on the right.

For example:

\[
[3,1,2,1]\quad\longmapsto\quad([1,1],[3,2]).
\]

Both sides together preserve exactly the original occurrences. Every left value equals \(m\), and every right value is at least \(m\). Thus separation holds. Because the input is nonuniform, both sides are proper sublists and both lengths decrease.

There is a termination trap. On `[4, 4]`, the raw partition would return `([4, 4], [])`, so the left recursive call would repeat the original input. Conservation and separation would both be true, but termination would not follow.

The implemented splitter detects uniform inputs and splits them in half. Both halves are shorter on nontrivial inputs, and separation still holds because every value is equal. Empty and singleton inputs are handled by the recursive scheme's base case.

`MinimumSplit.lean` proves the two supplied facts:

```lean
minimumSplit_contract : SplitContract minimumLeft minimumRight
minimumSplit_separated :
  ∀ xs, 2 ≤ xs.length → Separated (minimumLeft xs) (minimumRight xs)
```

The splitter does not call a sorting routine. The complete algorithm repeatedly sorts the split lists and concatenates the results. It is intentionally simple and can be unbalanced; this experiment makes no complexity improvement claim.

## What the search actually does

`lazy_search` receives a `SchemeRequirements` or `JointRequirement` goal and an optional list of proved facts. It has a fixed, ordered menu:

1. Apply the unconditional decomposition theorem.
2. If premises remain, restore the original proof state and apply the separated-input decomposition theorem.

For each pattern it tries local assumptions and the supplied terms against the generated premises. For the separated pattern it also supplies the proved `separation_transport` lemma. A term that fails to prove a premise is rolled back before the next term is tried.

A pattern is accepted only if all its premises have proofs and the resulting proof has no unresolved expression metavariables or unapproved axiom dependencies. The enclosing Lean declaration then undergoes ordinary kernel checking.

If no pattern completes, the tactic retains the branch with the fewest open goals, with earlier patterns winning ties. This rule only chooses which unfinished proof to show; it is not a semantic optimality criterion. The trace retains the residual goals for every attempted pattern, including branches that are not retained.

An unresolved pattern has not been refuted. Missing facts, incomplete premise discharge, or an unsuitable pattern can all cause the same outcome. Separate theorems in `Diagnostics.lean` prove impossibility for the selected invalid examples.

## Supplied knowledge and automatic choices

| Supplied by the implementation or experiment | Chosen or assembled during the run |
| --- | --- |
| Sorting specification and recursive scheme | Which of the two available patterns closes the goal first. |
| Two decomposition theorems | Their application to the actual helper functions. |
| `Separated` predicate and its transport theorem | Which supplied facts discharge which premises. |
| Concrete helper code and helper lemmas | A composed proof of the joint requirement and scheme requirements. |
| Fixed append/permutation content representation | A structured record of attempted and unresolved patterns. |

The witness lemmas are mathematical input, not discoveries claimed by the search. The automatic contribution is currently selection, instantiation, premise matching, and proof assembly within a declared finite language.

## Positive experiments

`Experiments.lean` runs three traced searches:

| Experiment | Available evidence | Observed result |
| --- | --- | --- |
| Half split + merge | Split and unconditional merge contracts | Selects `unconditional`. |
| Minimum partition + concatenation | Split, separation, guarded concatenation | Unconditional premise remains open; selects `separated`. |
| Minimum partition + merge | Evidence for both patterns | Selects `unconditional`, which is tried first. |

The second case produces the following sequence of event kinds:

```text
attempt
candidate             unconditional
candidate_unresolved  unconditional
candidate             separated
selected              separated
complete              separated
```

The complete JSON events also include the generated or remaining goals. They are captured in `docs/results/summary.json` and the experiment log.

Both accepted helper combinations instantiate the same already verified recursive scheme. `minimumPartitionSort_correct` proves the second program's specification for every natural-number list. The program tests enumerate all lists of lengths zero through five over `{0, 1, 2, 3}`: 1,365 inputs. Six additional stress cases include a uniform list, ascending and descending lists, duplicates, a large natural value, and a nearly uniform list. Each program is checked on all 1,371 inputs, giving 2,742 executable specification checks; their outputs are also compared.

The finite tests do not replace the universal correctness theorems. They exercise the compiled programs and catch integration or execution mistakes.

## Controlled failures and ablations

An ablation removes one ingredient to see whether the remaining system still succeeds.

| Fixture | Ingredient absent or invalid | Obligation observed |
| --- | --- | --- |
| `UnknownHelpers` | Any facts about arbitrary helpers | Split and combine requirements remain open. |
| `BadCombine` | Separation for the half split with concatenation | `GuardOnSplit leftHalf rightHalf Separated`. |
| `FixedBaseline` | Guarded pattern unavailable to the original tactic | Unconditional concatenation contract. |
| `PlainOnly` | Guarded pattern disabled in the new search | Unconditional concatenation contract. |
| `NoTransport` | Automatic supply of the transport lemma disabled | `GuardTransport Separated` in the guarded branch. |
| `MissingSplitGuard` | Separation witness omitted | Guard on the minimum split. |
| `NoProgress` | Raw minimum partition has no uniform fallback | Split contract, whose decrease component is impossible. |
| `UntrustedFact` | A false contract is supplied as a custom axiom | The axiom is refused; the combine requirement stays open. |

`Tests.lean` also shows that explicitly supplying `separation_transport` recovers success when automatic transport supply is disabled. This checks that the ablation changes available evidence rather than making the guarded rule unusable.

`Diagnostics.lean` contains proved counterexamples:

- `[2, 1]` refutes half-split sorting with concatenation.
- `[4, 4]` refutes strict decrease for the raw minimum partition.
- Replacing left `[1]` by `[3]` while keeping right `[2]` preserves sortedness and lengths but destroys separation. Thus those weaker recursive guarantees cannot replace content preservation in this transport argument.
- Removing a duplicate violates the sorting specification even when the result is sorted.

The script checks the intended residual premise in the relevant branch, rather than assuming that the final retained branch is always the guarded one.

## Inspecting the certificates

The proof certificate is the Lean term attached to each theorem. The trace is a readable explanation of the search, not a substitute for that term. `Audit.lean` prints the foundational dependencies of 23 declarations. The checker allows only `propext`, `Quot.sound`, and `Classical.choice`; some declarations use no axioms at all. No accepted closed theorem depends on an experiment-specific axiom or an admitted proof.

To reproduce the whole experiment:

```sh
python3 scripts/check.py --report
```

Do not import the expected-failure fixtures into the production library. In particular, the deliberately false axiom in `UntrustedFact.lean` belongs only to that rejection test.

## What this establishes, and what remains open

The prototype demonstrates checked selection between two modular contract patterns, including a precondition established by splitting and transported using recursive guarantees. It also demonstrates that termination can remain an independent obstacle after conservation and a combining precondition have both been established.

These are two controlled sorting variants, not independent research domains. No novelty, completeness, weakest-contract, or general synthesis result follows from these experiments.

A useful next research step is to make candidate production less prescribed: extract a recognizable joint obligation from the scheme proof, enumerate a documented small guard language, and compare the resulting search with this fixed menu and a manual proof baseline. Predicates depending on positions or order would test where permutation-only transport stops being sufficient. Those extensions should preserve the same boundary: proposed facts may guide search, but accepted results need Lean proofs.
