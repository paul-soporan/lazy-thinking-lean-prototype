import LazyThinking
import LazyThinking.Diagnostics
open LazyThinking

theorem witness_backtracking : SchemeRequirements leftHalf rightHalf mergeNat := by
  lazy_thinking using [Nat.zero_le, mergeNat_contract, halfSplit_contract]

theorem search_witness_backtracking :
    SchemeRequirements minimumLeft minimumRight concatenate := by
  lazy_search using [Nat.zero_le, concatenate_guarded_contract,
    minimumSplit_separated, minimumSplit_contract]

theorem local_decomposition (left right : Splitter) (combine : Combiner)
    (contents : SplitContents left right) (merge : CombineContract combine) :
    JointRequirement left right combine := by
  lazy_thinking

theorem local_guard_search (left right : Splitter) (combine : Combiner)
    (contents : SplitContents left right) (establish : GuardOnSplit left right Separated)
    (contract : GuardedCombineContract Separated combine) :
    JointRequirement left right combine := by
  lazy_search

theorem manual_guarded_baseline : SchemeRequirements minimumLeft minimumRight concatenate :=
  scheme_of_guarded_contracts _ _ _ Separated minimumSplit_contract
    minimumSplit_separated separation_transport concatenate_guarded_contract

/-- The ablation disables automatic supply, not the transport theorem itself. -/
theorem explicit_transport_recovers :
    SchemeRequirements minimumLeft minimumRight concatenate := by
  lazy_search_no_transport using [minimumSplit_contract, minimumSplit_separated,
    concatenate_guarded_contract, separation_transport]

example : True := by
  fail_if_success lazy_thinking
  fail_if_success lazy_search
  trivial

example (l r : Splitter) (c : Combiner) (h : SchemeRequirements l r c) :
    SchemeRequirements l r c := by
  lazy_search

theorem both_patterns_valid_for_minimum_merge :
    SchemeRequirements minimumLeft minimumRight mergeNat := by
  apply scheme_of_guarded_contracts (guard := Separated)
  · exact minimumSplit_contract
  · exact minimumSplit_separated
  · exact separation_transport
  · intro ys zs sy sz _
    exact mergeNat_contract ys zs sy sz

def listsOfLength : Nat → List Items
  | 0 => [[]]
  | n + 1 => (listsOfLength n).flatMap fun xs => [0, 1, 2, 3].map (· :: xs)

def main : IO Unit := do
  let exhaustive := (List.range 6).flatMap listsOfLength
  let stress : List Items := [List.replicate 64 7, List.range 80,
    (List.range 80).reverse, [1000000, 0, 1000000, 2, 0],
    [9, 9, 0, 8, 8, 0, 7, 7, 1, 6, 6, 1],
    List.replicate 31 3 ++ [0] ++ List.replicate 31 3]
  let mut checked := 0
  for xs in exhaustive ++ stress do
    let a := mergeSort xs
    let b := minimumPartitionSort xs
    unless decide (SortSpec xs a) && decide (SortSpec xs b) && a == b do
      throw (IO.userError s!"Specification or agreement failure on {xs}: {a}; {b}")
    checked := checked + 1
  unless checked == 1371 do throw (IO.userError s!"Wrong corpus size: {checked}")
  IO.println "PASS: 1365 exhaustive inputs plus 6 stress cases for BOTH sorting programs."
  IO.println "PASS: 2742 specification checks, plus agreement of the two outputs."
  IO.println "PASS: negative counterexamples, conditional rules, and backtracking proofs checked."
