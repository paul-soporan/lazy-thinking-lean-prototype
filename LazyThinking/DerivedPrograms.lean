import LazyThinking.Search
import LazyThinking.MinimumSplit

namespace LazyThinking

theorem selectedMergeRequirements : SchemeRequirements leftHalf rightHalf mergeNat := by
  lazy_search using [halfSplit_contract, mergeNat_contract]

theorem selectedMinimumRequirements :
    SchemeRequirements minimumLeft minimumRight concatenate := by
  lazy_search using [minimumSplit_contract, minimumSplit_separated, concatenate_guarded_contract]

/-- A second actual program, with no restriction on the input lists. -/
def minimumPartitionProgram : VerifiedSorter :=
  instantiateScheme minimumLeft minimumRight concatenate selectedMinimumRequirements

def minimumPartitionSort (xs : Items) : Items := minimumPartitionProgram.run xs

theorem minimumPartitionSort_correct (xs : Items) :
    SortSpec xs (minimumPartitionSort xs) := minimumPartitionProgram.correct xs

end LazyThinking
