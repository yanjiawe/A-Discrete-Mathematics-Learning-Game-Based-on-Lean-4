import Game.Metadata

World "thirdworld"
Level 11

Title "量词分配等值式"

Introduction "设A(x)，B(x)含自由出现的个体变项x，则(∀ x, ((A x) ∧ (B x))) ↔ ((∀ x, A x) ∧ (∀ x, B x))."

--Statement (p q : Prop) (h:p∧q):q∧p:=by
  --exact And.intro (And.right h) (And.left h)
universe u

Statement  {X : Type u} {A : X → Prop} {B : X → Prop} :
    (∀ x, ((A x) ∧ (B x))) ↔ ((∀ x, A x) ∧ (∀ x, B x)) := by
  constructor
  · intro h
    constructor
    · intro x
      exact (h x).left
    · intro x
      exact (h x).right
  · intro h x
    rcases h with ⟨hA, hB⟩
    exact ⟨hA x, hB x⟩


Conclusion "."

/- Use these commands to add items to the game's inventory. -/

--NewTactic exfalso apply
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
