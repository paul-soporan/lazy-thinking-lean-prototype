import LazyThinking
open LazyThinking

/-! Compile this file to observe actual candidate generation and checking. -/

set_option trace.LazyThinking.Search true in
theorem experimentMerge : SchemeRequirements leftHalf rightHalf mergeNat := by
  lazy_search using [halfSplit_contract, mergeNat_contract]

set_option trace.LazyThinking.Search true in
theorem experimentMinimumConcat :
    SchemeRequirements minimumLeft minimumRight concatenate := by
  lazy_search using [minimumSplit_contract, minimumSplit_separated, concatenate_guarded_contract]

/-- Both patterns can work here; the default menu tries the unguarded one first. -/
theorem mergeNat_guarded_contract : GuardedCombineContract Separated mergeNat := by
  intro ys zs sy sz _
  exact mergeNat_contract ys zs sy sz

set_option trace.LazyThinking.Search true in
theorem experimentPreference : SchemeRequirements minimumLeft minimumRight mergeNat := by
  lazy_search using [minimumSplit_contract, mergeNat_contract,
    minimumSplit_separated, mergeNat_guarded_contract]

#print axioms experimentMerge
#print axioms experimentMinimumConcat
#print axioms experimentPreference
#print axioms LazyThinking.minimumPartitionSort_correct
#eval minimumPartitionSort [5, 2, 4, 1, 6, 3, 2]
#eval minimumPartitionSort [7, 7, 7, 7, 7]
