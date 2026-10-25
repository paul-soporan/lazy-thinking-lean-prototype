import LazyThinking.Guards

namespace LazyThinking

abbrev CombiningGuard := Items → Items → Prop

def GuardOnSplit (left right : Splitter) (guard : CombiningGuard) : Prop :=
  ∀ xs, 2 ≤ xs.length → guard (left xs) (right xs)

/-- A sufficient transport property using only the recursive content guarantees. -/
def GuardTransport (guard : CombiningGuard) : Prop :=
  ∀ u v ys zs, guard u v → ys.Perm u → zs.Perm v → guard ys zs

def GuardedCombineContract (guard : CombiningGuard) (combine : Combiner) : Prop :=
  ∀ ys zs, Sorted ys → Sorted zs → guard ys zs → SortSpec (ys ++ zs) (combine ys zs)

/-- A candidate is accepted only after all of these premises have proofs. -/
theorem joint_of_guarded_contracts (left right : Splitter) (combine : Combiner)
    (guard : CombiningGuard) (contents : SplitContents left right)
    (establish : GuardOnSplit left right guard)
    (transport : GuardTransport guard) (merge : GuardedCombineContract guard combine) :
    JointRequirement left right combine := by
  intro xs ys zs nontrivial recurLeft recurRight
  have onResults := transport _ _ _ _ (establish xs nontrivial) recurLeft.2 recurRight.2
  have output := merge ys zs recurLeft.1 recurRight.1 onResults
  exact ⟨output.1, output.2.trans
    ((recurLeft.2.append recurRight.2).trans (contents xs nontrivial))⟩

theorem scheme_of_guarded_contracts (left right : Splitter) (combine : Combiner)
    (guard : CombiningGuard) (split : SplitContract left right)
    (establish : GuardOnSplit left right guard)
    (transport : GuardTransport guard) (merge : GuardedCombineContract guard combine) :
    SchemeRequirements left right combine :=
  ⟨split.decreases, joint_of_guarded_contracts left right combine guard
    split.contents establish transport merge⟩

theorem separation_transport : GuardTransport Separated := by
  intro u v ys zs h py pz
  exact separation_survives h py pz

theorem concatenate_guarded_contract : GuardedCombineContract Separated concatenate :=
  concatenate_correct

/-- The finite menu is part of the experiment's supplied knowledge. -/
inductive ContractCandidate where
  | unconditional
  | separated
  deriving Repr, BEq, Inhabited

def ContractCandidate.label : ContractCandidate → String
  | .unconditional => "unconditional"
  | .separated => "separated"

end LazyThinking
