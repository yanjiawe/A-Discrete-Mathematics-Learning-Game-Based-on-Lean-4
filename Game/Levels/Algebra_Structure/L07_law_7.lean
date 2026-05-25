import Game.Metadata

World "Algebra_Structure"
Level 7

open group

Title "mul_right_cancel"

Introduction "在群G中，对于G中元素a，x，y，满足左右消去律，接下来证明右消去律"

--Statement (p q : Prop) (h:p∧q):q∧p:=by
  --exact And.intro (And.right h) (And.left h)
universe u

Statement {G : Type u} [Group G]{x y a : G} (h : x ∘ a = y ∘ a) : x = y := by
  calc
    x = x ∘ Monoid.one := by rw [Monoid.mul_one]
    _ = x ∘ (a ∘ a⁻¹) := by rw [Group.mul_right_inv]
    _ = (x ∘ a) ∘ a⁻¹ := by rw [← Semigroup.mul_assoc]
    _ = (y ∘ a) ∘ a⁻¹ := by rw [h]
    _ = y ∘ (a ∘ a⁻¹) := by rw [Semigroup.mul_assoc]
    _ = y ∘ Monoid.one := by rw [Group.mul_right_inv]
    _ = y := by rw [Monoid.mul_one]




Conclusion "."

/- Use these commands to add items to the game's inventory. -/

--NewTactic calc
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
