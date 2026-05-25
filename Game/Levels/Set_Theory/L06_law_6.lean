import Game.Metadata

World "Set_Theory"
Level 6

open Set

Title "矛盾律"

Introduction "排中律为任意集合和他补的并为全集，矛盾律为任意集合和他补的交为空
集，这里我们证明矛盾律"

--Statement (p q : Prop) (h:p∧q):q∧p:=by
  --exact And.intro (And.right h) (And.left h)
universe u

Statement (α : Type u) (a : Set α) : a ∩ ~a = ∅ := by
  apply setext
  intro x
  constructor
  · intro ⟨ha, hna⟩
    exact hna ha
  · intro h
    exact False.elim h


Conclusion "."

/- Use these commands to add items to the game's inventory. -/

--NewTactic exfalso apply
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
