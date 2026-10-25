import LazyThinking.Witness
import LazyThinking.Guards

/-!
A supplied, unrestricted witness for guarded concatenation. Separate all
occurrences of the minimum from the other values. On uniform inputs use the
half split, so neither recursive call receives the whole nontrivial input.
No sorting algorithm is called by the splitter.
-/

namespace LazyThinking

def minimumValue : Items → Nat
  | [] => 0
  | [a] => a
  | a :: b :: rest =>
      if a ≤ minimumValue (b :: rest) then a else minimumValue (b :: rest)

theorem minimumValue_mem (xs : Items) (nonempty : xs ≠ []) : minimumValue xs ∈ xs := by
  induction xs with
  | nil => contradiction
  | cons a tail ih =>
    cases tail with
    | nil => simp [minimumValue]
    | cons b rest =>
      by_cases h : a ≤ minimumValue (b :: rest)
      · simp [minimumValue, h]
      · rw [minimumValue, if_neg h]
        exact List.mem_cons_of_mem a (ih (by simp))

theorem minimumValue_le (xs : Items) (a : Nat) (member : a ∈ xs) :
    minimumValue xs ≤ a := by
  induction xs with
  | nil => simp at member
  | cons b tail ih =>
    cases tail with
    | nil =>
      have same : a = b := by simpa using member
      subst a
      exact Nat.le_refl b
    | cons c rest =>
      by_cases h : b ≤ minimumValue (c :: rest)
      · rw [minimumValue, if_pos h]
        rcases List.mem_cons.mp member with same | inTail
        · subst a; exact Nat.le_refl b
        · exact Nat.le_trans h (ih inTail)
      · rw [minimumValue, if_neg h]
        rcases List.mem_cons.mp member with same | inTail
        · subst a; omega
        · exact ih inTail

def allMinimum (xs : Items) : Bool := xs.all (fun a => a == minimumValue xs)

def minimumLeft (xs : Items) : Items :=
  if allMinimum xs then leftHalf xs
  else let pivot := minimumValue xs; xs.filter (fun a => a == pivot)

def minimumRight (xs : Items) : Items :=
  if allMinimum xs then rightHalf xs
  else let pivot := minimumValue xs; xs.filter (fun a => !(a == pivot))

theorem minimumSplit_contract : SplitContract minimumLeft minimumRight := by
  constructor
  · intro xs nontrivial
    by_cases uniform : allMinimum xs = true
    · simpa [minimumLeft, minimumRight, uniform] using
        halfSplit_contract.contents xs nontrivial
    · simpa [minimumLeft, minimumRight, uniform] using
        List.filter_append_perm (fun a => a == minimumValue xs) xs
  · intro xs nontrivial
    by_cases uniform : allMinimum xs = true
    · simpa [minimumLeft, minimumRight, uniform] using
        halfSplit_contract.decreases xs nontrivial
    · simp only [minimumLeft, minimumRight, if_neg uniform]
      have leftLe := List.length_filter_le (fun a => a == minimumValue xs) xs
      have rightLe := List.length_filter_le (fun a => !(a == minimumValue xs)) xs
      have leftNe : (xs.filter (fun a => a == minimumValue xs)).length ≠ xs.length := by
        intro equal
        apply uniform
        exact List.all_eq_true.mpr (List.length_filter_eq_length_iff.mp equal)
      have nonempty : xs ≠ [] := by intro equal; subst xs; simp at nontrivial
      have rightNe : (xs.filter (fun a => !(a == minimumValue xs))).length ≠ xs.length := by
        intro equal
        have absent := List.length_filter_eq_length_iff.mp equal
          (minimumValue xs) (minimumValue_mem xs nonempty)
        simp at absent
      omega

theorem minimumSplit_separated :
    ∀ xs, 2 ≤ xs.length → Separated (minimumLeft xs) (minimumRight xs) := by
  intro xs _ a inLeft b inRight
  by_cases uniform : allMinimum xs = true
  · simp [minimumLeft, minimumRight, uniform] at inLeft inRight
    have all := List.all_eq_true.mp uniform
    have aEq : a = minimumValue xs := by
      simpa only [allMinimum, beq_iff_eq] using all a (List.mem_of_mem_take inLeft)
    have bEq : b = minimumValue xs := by
      simpa only [allMinimum, beq_iff_eq] using all b (List.mem_of_mem_drop inRight)
    omega
  · simp [minimumLeft, minimumRight, uniform] at inLeft inRight
    have aEq : a = minimumValue xs := inLeft.2
    rw [aEq]
    exact minimumValue_le xs b inRight.1

end LazyThinking
