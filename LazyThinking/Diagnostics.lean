import LazyThinking.MinimumSplit
import LazyThinking.Candidates

namespace LazyThinking

theorem concatenation_requires_more : ¬ CombineContract concatenate := by
  intro contract
  have result := contract [2] [1] (by decide) (by decide)
  simp [SortSpec, Sorted, concatenate] at result

theorem halfSplit_not_separated : ¬ GuardOnSplit leftHalf rightHalf Separated := by
  intro guard
  have bad := guard [2, 1] (by decide)
  simp [Separated, leftHalf, rightHalf] at bad

theorem halfSplit_concat_wrong : ¬ SchemeRequirements leftHalf rightHalf concatenate := by
  intro requirements
  have bad := requirements.2 [2, 1] [2] [1] (by decide) (by decide) (by decide)
  simp [SortSpec, Sorted, concatenate] at bad

def rawMinimumLeft (xs : Items) : Items :=
  let pivot := minimumValue xs
  xs.filter (fun a => a == pivot)

def rawMinimumRight (xs : Items) : Items :=
  let pivot := minimumValue xs
  xs.filter (fun a => !(a == pivot))

theorem rawMinimum_contents : SplitContents rawMinimumLeft rawMinimumRight := by
  intro xs _
  exact List.filter_append_perm _ xs

theorem rawMinimum_separated : GuardOnSplit rawMinimumLeft rawMinimumRight Separated := by
  intro xs _ a inLeft b inRight
  have aEq : a = minimumValue xs := by
    simpa [rawMinimumLeft] using (List.mem_filter.mp inLeft).2
  rw [aEq]
  exact minimumValue_le xs b (List.mem_filter.mp inRight).1

theorem rawMinimum_does_not_decrease : ¬ Decreases rawMinimumLeft rawMinimumRight := by
  intro progress
  have bad := (progress [4, 4] (by decide)).1
  simp [rawMinimumLeft, minimumValue] at bad

theorem unchanged_split_cannot_decrease :
    ¬ SplitContract (fun xs => xs) (fun _ => []) := by
  intro contract
  have smaller := contract.decreases [1, 1] (by decide)
  simp at smaller

theorem dropping_duplicates_violates_spec : ¬ SortSpec [1, 1] [1] := by
  intro spec
  have lengths := spec.2.length_eq
  simp at lengths

/-- Sortedness and equal lengths alone do not transport element separation. -/
theorem lengths_and_sortedness_are_insufficient :
    Separated [1] [2] ∧ Sorted [3] ∧ Sorted [2] ∧
    ([1] : Items).length = [3].length ∧ ([2] : Items).length = [2].length ∧
    ¬ Separated [3] [2] := by decide

end LazyThinking
