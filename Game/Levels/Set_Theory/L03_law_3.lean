import Game.Metadata

World "Set_Theory"
Level 3

open Set

Title "分配律"

Introduction "集合的交和并也满足分配律"

--Statement (p q : Prop) (h:p∧q):q∧p:=by
  --exact And.intro (And.right h) (And.left h)
universe u

Statement {α : Type u} (A B C : Set α) :
  A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) :=by
  apply setext
  intro x
  constructor
  ·intro h
   rcases h with ⟨ha,hbc⟩
   rcases hbc with hb | hc
   ·exact Or.inl ⟨ha, hb⟩
   ·exact Or.inr ⟨ha, hc⟩
  ·intro h
   rcases h with hab | hac
   ·rcases hab with ⟨ha,hb⟩
    exact ⟨ha, Or.inl hb⟩
   ·rcases hac with ⟨ha,hc⟩
    exact ⟨ha, Or.inr hc⟩


Conclusion "."

/- Use these commands to add items to the game's inventory. -/

--NewTactic exfalso apply
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
