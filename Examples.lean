import LazyThinking
open LazyThinking

set_option trace.LazyThinking true in
theorem inferredMergeSortRequirements :
    SchemeRequirements leftHalf rightHalf mergeNat := by
  lazy_thinking using [halfSplit_contract, mergeNat_contract]

theorem conditionalInference (left right : Splitter) (combine : Combiner)
    (split : SplitContract left right) (merge : CombineContract combine) :
    SchemeRequirements left right combine := by
  lazy_thinking

theorem inferredMergeSortCorrect (xs : Items) : SortSpec xs
    (sortUsing leftHalf rightHalf mergeNat inferredMergeSortRequirements.1 xs) :=
  sortUsing_correct leftHalf rightHalf mergeNat inferredMergeSortRequirements xs

def inferredProgram : VerifiedSorter :=
  instantiateScheme leftHalf rightHalf mergeNat inferredMergeSortRequirements

#print axioms inferredMergeSortRequirements
#print axioms inferredMergeSortCorrect
#eval inferredProgram.run [5, 2, 4, 1, 6, 3, 2]
