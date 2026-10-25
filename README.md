# Lazy thinking in Lean — experiment 2

This is a small, executable research prototype for deriving helper requirements from a recursive sorting specification. Version 0.2 adds a finite search over **two supplied contract patterns**: an unconditional combiner, and a combiner requiring separation between its inputs.

The search constructs Lean proofs. It now selects different patterns for two actual sorting programs, both proved correct for every list of natural numbers. It also leaves visible obligations when the supplied facts are insufficient.

This remains a bounded experiment toward lazy thinking: the rules, guard, helper implementations, and witness lemmas are supplied. The system does not yet extract contracts from an arbitrary failed induction, invent new guards, or synthesize helper code.

## Run it

Prerequisites: Lean/Elan with Lake, and Python 3 for the experiment runner. The project pins **Lean 4.24.0** in `lean-toolchain`; it uses Lean's bundled libraries and has no Mathlib dependency.

From this directory:

```sh
lake build
lake exe lazy-thinking-demo
python3 scripts/check.py --report
```

The last command builds the tests, runs both programs on 1,371 inputs each, checks three positive search traces, checks eight expected proof failures, and audits 23 theorem dependencies. It writes logs and structured results to `docs/results/`. The expected-failure files must fail; compiling every `.lean` file as though all should succeed is not the test procedure.

To see the actual proof-search trace:

```sh
lake env lean Experiments.lean
```

## What changed

The original `lazy_thinking` tactic still supplies a fixed split/combine decomposition. The new `lazy_search` tactic tries an unconditional contract first, then a separated-input contract. It accepts a pattern only after its premises have proofs.

| Helpers supplied | Pattern selected | Reason |
| --- | --- | --- |
| Half split + merge | Unconditional | Merge sorts the union of any two sorted input lists. |
| Minimum partition + concatenation | Separated | Every left value is at most every right value; sorting preserves that fact. |
| Minimum partition + merge | Unconditional | Both patterns are available, but the first one suffices. |

The second program uses a deliberately simple splitter. On `[3, 1, 2, 1]`, it separates `[1, 1]` from `[3, 2]`. Recursive sorting produces `[1, 1]` and `[2, 3]`, which can be concatenated. On a uniform list such as `[7, 7, 7, 7]`, it splits in half instead: collecting all minima on one side would otherwise prevent progress.

The minimum-partition algorithm is a proof witness, not a proposed performance improvement over merge sort. It can produce very unbalanced recursion on distinct values. No efficiency or novelty claim is made for it.

## The new proof call

```lean
theorem selectedMinimumRequirements :
    SchemeRequirements minimumLeft minimumRight concatenate := by
  lazy_search using [minimumSplit_contract, minimumSplit_separated,
    concatenate_guarded_contract]
```

These three supplied lemmas establish conservation and recursive decrease, separation at the split, and correctness of concatenation under separation. The search also has a proved separation-transport lemma in its declared knowledge. It assembles those ingredients into the joint obligation, which instantiates the already verified recursive scheme.

The conclusion is then:

```lean
theorem minimumPartitionSort_correct (xs : Items) :
    SortSpec xs (minimumPartitionSort xs)
```

`SortSpec xs output` means that `output` is sorted and is a permutation of `xs`. A permutation preserves duplicate counts as well as values. The theorem covers all inputs; the executable tests provide additional checks of execution and integration.

## Read in this order

1. [Foundation](docs/01-foundation.md): the specification, induction step, and original decomposition.
2. [Guard search walkthrough](docs/02-guard-search.md): the new mathematical obligation and experiments.
3. `LazyThinking/Candidates.lean`: the generic guarded decomposition theorem.
4. `LazyThinking/DerivedPrograms.lean`: the short proof calls and resulting program.
5. `LazyThinking/MinimumSplit.lean`: the supplied splitter and its proofs.
6. `LazyThinking/Search.lean`: the finite candidate search and state restoration.

## Source map

| File | Role |
| --- | --- |
| `Spec.lean`, `Decomposition.lean`, `Scheme.lean` | Specification, fixed decomposition, terminating recursive scheme and correctness. |
| `Witness.lean` | Half split and a wrapper around Lean's library merge. |
| `Guards.lean`, `Candidates.lean` | Separation, transport, and generic guarded decomposition. |
| `Evidence.lean` | Premise discharge, proof-state rollback, and dependency checks. |
| `Tactic.lean`, `Search.lean` | Fixed-rule baseline and finite candidate search. |
| `MinimumSplit.lean`, `DerivedPrograms.lean` | A second all-input sorting program and checked requirements. |
| `Diagnostics.lean` | Proved counterexamples to invalid combinations and weaker guarantees. |
| `Examples.lean`, `Experiments.lean` | Fixed-rule and search traces. |
| `Tests.lean`, `tests/`, `Audit.lean` | Positive tests, expected failures, and foundational dependency inventory. |
| `scripts/check.py` | Reproducible checks and report generation. |

The module names in the first seven rows are relative to `LazyThinking/`; the remaining paths are relative to the project root.

## Proofs and traces

Lean proof terms are the certificates. JSON trace events are explanations for inspection or a future interface; replaying their text is not proof checking. Unresolved candidates remain genuine Lean goals.

Accepted closed results use only the audited standard foundations `propext`, `Quot.sound`, and, for some results, `Classical.choice`. There are no admitted theorems or custom axioms in the production modules. `tests/UntrustedFact.lean` deliberately introduces a false axiom to check that the tactic refuses it; this file is an expected failure and is not imported by the library.

The included results were generated with the pinned toolchain. The archive contains source and small result files, not Lean binaries or build products.
