import Game.Metadata

World "forthworld"
Level 4

open Set

Title "同一律"

Introduction "同一律有两种，分别是空集和任意集合的并都是该集合，
任意集合和全集的交都是该集合，这里证明第一种"

--Statement (p q : Prop) (h:p∧q):q∧p:=by
  --exact And.intro (And.right h) (And.left h)
universe u

Statement (α : Type u)(a : Set α) : a ∪ ∅ = a :=by
  apply setext
  intro x
  constructor
  ·intro h
   rcases h with ha | hfalse
   ·exact ha
   ·exact False.elim hfalse
  ·intro ha
   exact Or.inl ha


Conclusion "."

/- Use these commands to add items to the game's inventory. -/

--NewTactic exfalso apply
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
