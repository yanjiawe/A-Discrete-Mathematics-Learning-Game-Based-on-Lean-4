import Game.Metadata

World "forthworld"
Level 13

open Set

Title "笛卡尔积"

Introduction "两个元素按一定顺序组成的二元组叫有序对，形如<x,y>，对于集合A，B
分别用他们的元素构成有序对，这些有序对的集合为A，B的笛卡尔积，记作A×B,笛卡尔积对交并
满足分配律，这里我们证明并的分配律"

--Statement (p q : Prop) (h:p∧q):q∧p:=by
  --exact And.intro (And.right h) (And.left h)
universe u

Statement (α : Type u)(β: Type u) (a b : Set α) (c : Set β) :
  (a ∪ b) ×₁ c = (a ×₁ c) ∪ (b ×₁ c) := by
  apply setext
  intro p
  constructor
  · intro h
    rcases h with ⟨h1ab,h2c⟩
    rcases h1ab with h1a | h1b
    ·exact Or.inl ⟨h1a,h2c⟩
    ·exact Or.inr ⟨h1b,h2c⟩
  · intro h
    rcases h with hac| hbc
    ·rcases hac with ⟨h1a,h2c⟩
     exact ⟨(Or.inl h1a),h2c⟩
    ·rcases hbc with ⟨h1b,h2c⟩
     exact ⟨(Or.inr h1b),h2c⟩

Conclusion "."

/- Use these commands to add items to the game's inventory. -/

--NewTactic exfalso apply
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
