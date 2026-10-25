import LazyThinking.Decomposition

namespace LazyThinking

def Separated (left right : Items) : Prop :=
  ∀ a, a ∈ left → ∀ b, b ∈ right → a ≤ b

instance (left right : Items) : Decidable (Separated left right) := by
  unfold Separated
  infer_instance

def concatenate (left right : Items) : Items := left ++ right

theorem separation_survives {u v ys zs : Items}
    (separated : Separated u v)
    (leftContents : ys.Perm u) (rightContents : zs.Perm v) :
    Separated ys zs := by
  intro a inLeft b inRight
  exact separated a (leftContents.mem_iff.mp inLeft)
    b (rightContents.mem_iff.mp inRight)

theorem concatenate_correct (ys zs : Items)
    (sortedLeft : Sorted ys) (sortedRight : Sorted zs)
    (separated : Separated ys zs) : SortSpec (ys ++ zs) (concatenate ys zs) := by
  constructor
  · exact List.pairwise_append.mpr ⟨sortedLeft, sortedRight, separated⟩
  · exact List.Perm.refl _

theorem concatenate_joint_of_separated_split
    (left right : Splitter) (contents : SplitContents left right)
    (separated : ∀ xs, 2 ≤ xs.length → Separated (left xs) (right xs)) :
    JointRequirement left right concatenate := by
  intro xs ys zs nontrivial recurLeft recurRight
  have guard := separation_survives (separated xs nontrivial) recurLeft.2 recurRight.2
  obtain ⟨sortedOutput, contentsOutput⟩ :=
    concatenate_correct ys zs recurLeft.1 recurRight.1 guard
  exact ⟨sortedOutput, contentsOutput.trans
    ((recurLeft.2.append recurRight.2).trans (contents xs nontrivial))⟩

theorem separated_of_bounds (p : Nat) (ys zs : Items)
    (upper : ∀ a, a ∈ ys → a ≤ p) (lower : ∀ b, b ∈ zs → p ≤ b) :
    Separated ys zs := by
  intro a inLeft b inRight
  exact Nat.le_trans (upper a inLeft) (lower b inRight)

end LazyThinking
