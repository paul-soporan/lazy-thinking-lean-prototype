import Std

namespace LazyThinking

abbrev Items := List Nat
abbrev Splitter := Items → Items
abbrev Combiner := Items → Items → Items

def Sorted (xs : Items) : Prop := xs.Pairwise (· ≤ ·)

instance (xs : Items) : Decidable (Sorted xs) := by
  unfold Sorted
  infer_instance

/-- Permutation retains multiplicities, unlike equality of sets. -/
def SortSpec (input output : Items) : Prop :=
  Sorted output ∧ output.Perm input

instance (input output : Items) : Decidable (SortSpec input output) := by
  unfold SortSpec
  infer_instance

def SplitContents (left right : Splitter) : Prop :=
  ∀ xs, 2 ≤ xs.length → (left xs ++ right xs).Perm xs

def Decreases (left right : Splitter) : Prop :=
  ∀ xs, 2 ≤ xs.length →
    (left xs).length < xs.length ∧ (right xs).length < xs.length

structure SplitContract (left right : Splitter) : Prop where
  contents : SplitContents left right
  decreases : Decreases left right

def CombineContract (combine : Combiner) : Prop :=
  ∀ ys zs, Sorted ys → Sorted zs → SortSpec (ys ++ zs) (combine ys zs)

/-- The inductive step jointly constrains the three unknown helpers. -/
def JointRequirement (left right : Splitter) (combine : Combiner) : Prop :=
  ∀ xs ys zs, 2 ≤ xs.length →
    SortSpec (left xs) ys → SortSpec (right xs) zs →
    SortSpec xs (combine ys zs)

def SchemeRequirements (left right : Splitter) (combine : Combiner) : Prop :=
  Decreases left right ∧ JointRequirement left right combine

end LazyThinking
