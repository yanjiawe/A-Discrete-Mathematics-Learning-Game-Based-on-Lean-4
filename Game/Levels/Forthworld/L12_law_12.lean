import Game.Metadata

World "forthworld"
Level 12

open Set

Title "笛卡尔积"

Introduction "两个元素按一定顺序组成的二元组叫有序对，形如<x,y>，对于集合A，B
分别用他们的元素构成有序对，这些有序对的集合为A，B的笛卡尔积，记作A×B,任意集合和
空集的笛卡尔积为空集,这里我们将符号改为×₁"

--Statement (p q : Prop) (h:p∧q):q∧p:=by
  --exact And.intro (And.right h) (And.left h)
universe u

Statement (α : Type u)(β: Type u) (s : Set β) :
  (∅ : Set α) ×₁ s = ∅ := by
  apply setext
  intro p
  constructor
  · intro h
    rcases h with ⟨h1,h2⟩
    exact h1
  · intro h
    exact False.elim h


Conclusion "."

/- Use these commands to add items to the game's inventory. -/

--NewTactic exfalso apply
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
