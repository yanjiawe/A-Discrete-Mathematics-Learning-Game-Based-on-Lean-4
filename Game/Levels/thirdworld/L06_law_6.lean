import Game.Metadata

World "thirdworld"
Level 6

Title "量词辖域收缩与扩张等值式"

Introduction "Ax含自由变元x，而B不含x的自由出现，
则(∀x,(B→(A x))) ↔ (B→(∀x,A x))."

--Statement (p q : Prop) (h:p∧q):q∧p:=by
  --exact And.intro (And.right h) (And.left h)
universe u

Statement {X : Type u}{x:Nonempty X} {A : X→ Prop}{B:Prop}
: (∀x,(B→(A x))) ↔ (B→(∀x,A x))
:= by
  constructor
  · intro h hb x
    exact h x hb
  · intro h hx hb
    exact h hb hx


Conclusion "."

/- Use these commands to add items to the game's inventory. -/

--NewTactic exfalso apply
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
