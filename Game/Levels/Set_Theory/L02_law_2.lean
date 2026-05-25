import Game.Metadata

World "Set_Theory"
Level 2

open Set

Title "结合律"

Introduction "集合的交和并也满足结合律"

--Statement (p q : Prop) (h:p∧q):q∧p:=by
  --exact And.intro (And.right h) (And.left h)
universe u

Statement (α : Type u)(a b c : Set α) : (a ∪ b) ∪ c = a ∪ (b ∪ c) :=by
  apply setext
  intro x
  constructor
  ·intro h
   rcases h with hab | hc
   ·rcases hab with ha | hb
    ·exact Or.inl ha
    ·exact Or.inr (Or.inl hb)
   ·exact Or.inr (Or.inr hc)
  ·intro h
   rcases h with ha | hbc
   ·exact Or.inl (Or.inl ha)
   ·rcases hbc with hb | hc
    ·exact Or.inl (Or.inr hb)
    ·exact Or.inr hc


Conclusion "."

/- Use these commands to add items to the game's inventory. -/

--NewTactic exfalso apply
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
