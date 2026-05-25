import Game.Metadata

World "Predicate_Logic"
Level 2

Title "量词否定等值式2"

Introduction "设A(x)含自由出现的个体变项x，则并不存在性质A的x与所有x都
没有性质A等价，即(¬ ∃ x, A x) ↔ (∀ x, ¬ A x)."

--Statement (p q : Prop) (h:p∧q):q∧p:=by
  --exact And.intro (And.right h) (And.left h)
universe u

Statement  {X : Type u} {A : X → Prop}
: (¬ ∃ x, A x) ↔ (∀ x, ¬ A x)
:= by
constructor
· intro h x hx
  exact h ⟨x, hx⟩
· intro h ⟨x, hx⟩
  exact (h x) hx


Conclusion "."

/- Use these commands to add items to the game's inventory. -/

--NewTactic exfalso apply
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
