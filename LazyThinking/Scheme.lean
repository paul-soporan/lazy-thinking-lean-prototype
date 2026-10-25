import LazyThinking.Decomposition

namespace LazyThinking

def sortUsing (left right : Splitter) (combine : Combiner)
    (progress : Decreases left right) (xs : Items) : Items :=
  if _small : xs.length ≤ 1 then xs
  else combine (sortUsing left right combine progress (left xs))
    (sortUsing left right combine progress (right xs))
termination_by xs.length
decreasing_by
  all_goals have nontrivial : 2 ≤ xs.length := by omega
  · exact (progress xs nontrivial).1
  · exact (progress xs nontrivial).2

theorem sortUsing_correct (left right : Splitter) (combine : Combiner)
    (requirements : SchemeRequirements left right combine) :
    ∀ xs, SortSpec xs (sortUsing left right combine requirements.1 xs) := by
  have byLength : ∀ n xs, xs.length = n →
      SortSpec xs (sortUsing left right combine requirements.1 xs) := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro xs lengthEq
      rw [sortUsing]
      split
      · rename_i small
        exact trivial_spec xs small
      · rename_i notSmall
        have nontrivial : 2 ≤ xs.length := by omega
        have smaller := requirements.1 xs nontrivial
        apply requirements.2 xs _ _ nontrivial
        · exact ih (left xs).length (by omega) (left xs) rfl
        · exact ih (right xs).length (by omega) (right xs) rfl
  intro xs
  exact byLength xs.length xs rfl

structure VerifiedSorter where
  run : Items → Items
  correct : ∀ xs, SortSpec xs (run xs)

def instantiateScheme (left right : Splitter) (combine : Combiner)
    (requirements : SchemeRequirements left right combine) : VerifiedSorter where
  run := sortUsing left right combine requirements.1
  correct := sortUsing_correct left right combine requirements

end LazyThinking
