import Game.Metadata

World "Algebra_Structure"
Level 6

open group

Title "mul_left_cancel"

Introduction "在群G中，对于G中元素a，x，y，满足左右消去律，这里先证明左消去律"

--Statement (p q : Prop) (h:p∧q):q∧p:=by
  --exact And.intro (And.right h) (And.left h)
universe u

Statement {G : Type u} [Group G]{a x y : G} (h : a ∘ x = a ∘ y) : x = y := by
  calc
    x = Monoid.one ∘ x := by rw [Monoid.one_mul]
    _ = (a⁻¹ ∘ a) ∘ x := by rw [Group.mul_left_inv]
    _ = a⁻¹ ∘ (a ∘ x) := by rw [← Semigroup.mul_assoc]
    _ = a⁻¹ ∘ (a ∘ y) := by rw [h]
    _ = (a⁻¹ ∘ a) ∘ y := by rw [Semigroup.mul_assoc]
    _ = Monoid.one ∘ y := by rw [Group.mul_left_inv]
    _ = y := by rw [Monoid.one_mul]




Conclusion "."

/- Use these commands to add items to the game's inventory. -/

--NewTactic calc
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
