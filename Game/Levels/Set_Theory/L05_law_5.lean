import Game.Metadata

World "Set_Theory"
Level 5

open Set

Title "零律"

Introduction "零律有两种，分别是任意集合和全集的并都是该集合，任意集合和空集
的交都是空集这里证明第一种"

--Statement (p q : Prop) (h:p∧q):q∧p:=by
  --exact And.intro (And.right h) (And.left h)
universe u

Statement (α : Type u)(a : Set α) : a ∪ E = E :=by
  apply setext
  intro x
  constructor
  ·intro h
   rcases h with ha |hea
   ·trivial
   ·exact hea
  ·intro h
   exact Or.inr h


Conclusion "."

/- Use these commands to add items to the game's inventory. -/

--NewTactic exfalso apply
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
