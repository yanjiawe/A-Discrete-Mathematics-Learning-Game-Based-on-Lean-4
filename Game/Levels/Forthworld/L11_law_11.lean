import Game.Metadata

World "forthworld"
Level 11

open Set

Title "德摩根律"

Introduction "接下来证明空集的补为全集"

--Statement (p q : Prop) (h:p∧q):q∧p:=by
  --exact And.intro (And.right h) (And.left h)
universe u



Statement (α : Type u):(~ (∅ : Set α)) = E :=by
  apply setext
  intro x
  constructor
  · intro h
    trivial
  · intro _
    intro h
    exact h

Conclusion "."

/- Use these commands to add items to the game's inventory. -/

--NewTactic exfalso apply
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
