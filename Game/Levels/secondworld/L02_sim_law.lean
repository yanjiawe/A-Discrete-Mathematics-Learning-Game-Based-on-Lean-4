import Game.Metadata

World "Secondworld"
Level 2

Title "化简律"

Introduction "化简律，即合取可以取其中之一."

--Statement (p q : Prop) (h:p∧q):q∧p:=by
  --exact And.intro (And.right h) (And.left h)

Statement (a b:Prop)
:(a∧b)→a:=by
intro ⟨ha,hb⟩
exact ha


Conclusion "这样便是化简律."

/- Use these commands to add items to the game's inventory. -/

--NewTactic constructor rcases intro exact
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
