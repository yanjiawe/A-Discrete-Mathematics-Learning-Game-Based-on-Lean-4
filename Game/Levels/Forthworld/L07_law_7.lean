import Game.Metadata

World "forthworld"
Level 7

open Set

Title "吸收律"

Introduction "集合的交和并也满足吸收律,这里我们证明并对交的吸收律"

--Statement (p q : Prop) (h:p∧q):q∧p:=by
  --exact And.intro (And.right h) (And.left h)
universe u

Statement (α : Type u)(A B : Set α) : A ∪ (A ∩ B) = A := by
  apply setext
  intro x
  constructor
  · intro h
    rcases h with ha | hab
    ·exact ha
    ·rcases hab with ⟨ha,hb⟩
     exact ha
  · intro ha
    left; exact ha


Conclusion "."

/- Use these commands to add items to the game's inventory. -/

--NewTactic exfalso apply
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
