import Game.Metadata

World "Set_Theory"
Level 8

open Set

Title "双重否定律"

Introduction "双重否定律即是集合两次补即他本身"

--Statement (p q : Prop) (h:p∧q):q∧p:=by
  --exact And.intro (And.right h) (And.left h)
universe u

Statement (α : Type u)(a : Set α) : ~(~a) = a := by
  apply setext
  intro x
  constructor
  · intro hnn
    by_cases h : a x
    · exact h
    · exfalso
      exact hnn h
  · intro ha hna
    exact hna ha


Conclusion "."

/- Use these commands to add items to the game's inventory. -/

--NewTactic exfalso apply
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
