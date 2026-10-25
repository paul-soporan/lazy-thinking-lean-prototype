import LazyThinking.Spec

namespace LazyThinking

/-- Supplied theory knowledge: the connecting expression is concatenation. -/
theorem joint_of_contracts
    (left right : Splitter) (combine : Combiner)
    (split : SplitContents left right) (merge : CombineContract combine) :
    JointRequirement left right combine := by
  intro xs ys zs nontrivial recurLeft recurRight
  obtain ⟨sortedLeft, contentsLeft⟩ := recurLeft
  obtain ⟨sortedRight, contentsRight⟩ := recurRight
  obtain ⟨sortedOutput, contentsOutput⟩ := merge ys zs sortedLeft sortedRight
  exact ⟨sortedOutput, contentsOutput.trans
    ((contentsLeft.append contentsRight).trans (split xs nontrivial))⟩

theorem scheme_of_contracts
    (left right : Splitter) (combine : Combiner)
    (split : SplitContract left right) (merge : CombineContract combine) :
    SchemeRequirements left right combine :=
  ⟨split.decreases, joint_of_contracts left right combine split.contents merge⟩

theorem trivial_spec (xs : Items) (small : xs.length ≤ 1) : SortSpec xs xs := by
  constructor
  · cases xs with
    | nil => simp [Sorted]
    | cons x tail =>
      cases tail with
      | nil => simp [Sorted]
      | cons y rest => simp at small
  · exact List.Perm.refl xs

end LazyThinking
