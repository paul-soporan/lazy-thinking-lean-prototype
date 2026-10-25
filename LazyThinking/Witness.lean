import LazyThinking.Scheme
import Init.Data.List.Sort.Lemmas

namespace LazyThinking

def leftHalf (xs : Items) : Items := xs.take (xs.length / 2)
def rightHalf (xs : Items) : Items := xs.drop (xs.length / 2)

theorem halfSplit_contract : SplitContract leftHalf rightHalf := by
  constructor
  · intro xs _
    simp only [leftHalf, rightHalf, List.take_append_drop]
    exact List.Perm.refl xs
  · intro xs nontrivial
    constructor
    · simp only [leftHalf, List.length_take]
      omega
    · simp only [rightHalf, List.length_drop]
      omega

def natLE (a b : Nat) : Bool := decide (a ≤ b)
def mergeNat (ys zs : Items) : Items := List.merge ys zs natLE

theorem mergeNat_contract : CombineContract mergeNat := by
  intro ys zs sortedLeft sortedRight
  constructor
  · have trans : ∀ a b c, natLE a b = true → natLE b c = true → natLE a c = true := by
      intro a b c ab bc
      simp only [natLE, decide_eq_true_eq] at *
      omega
    have total : ∀ a b, (natLE a b || natLE b a) = true := by
      intro a b
      simp only [natLE, Bool.or_eq_true, decide_eq_true_eq]
      omega
    simpa only [Sorted, mergeNat, natLE, decide_eq_true_eq] using
      List.sorted_merge (le := natLE) trans total ys zs
        (by simpa only [Sorted, natLE, decide_eq_true_eq] using sortedLeft)
        (by simpa only [Sorted, natLE, decide_eq_true_eq] using sortedRight)
  · exact List.merge_perm_append natLE

theorem mergeSort_requirements : SchemeRequirements leftHalf rightHalf mergeNat :=
  scheme_of_contracts leftHalf rightHalf mergeNat halfSplit_contract mergeNat_contract

def mergeSort (xs : Items) : Items :=
  sortUsing leftHalf rightHalf mergeNat mergeSort_requirements.1 xs

theorem mergeSort_correct (xs : Items) : SortSpec xs (mergeSort xs) :=
  sortUsing_correct leftHalf rightHalf mergeNat mergeSort_requirements xs

end LazyThinking
