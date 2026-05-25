import Game.Metadata

World "Set_Theory"
Level 10

open Set

Title "德摩根律"

Introduction "接下来证明两个集合的交的补为两个集合补的并"

--Statement (p q : Prop) (h:p∧q):q∧p:=by
  --exact And.intro (And.right h) (And.left h)
universe u

Statement (α : Type u)(a b : Set α) : ~(a ∩ b) = ~a ∪ ~b :=by
 apply setext
 intro x
 constructor
 ·intro h
  by_cases ha : x ∈ a
  · right; intro hb; exact h ⟨ha, hb⟩
  · left; exact ha
 ·intro h
  rcases h with hna|hnb
  ·intro hab
   rcases hab with ⟨ha,hb⟩
   exact hna ha
  ·intro hab
   rcases hab with ⟨ha,hb⟩
   exact hnb hb

Conclusion "."

/- Use these commands to add items to the game's inventory. -/

--NewTactic exfalso apply
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
