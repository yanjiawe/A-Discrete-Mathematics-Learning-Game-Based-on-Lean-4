import Game.Metadata

World "Secondworld"
Level 5

Title "析取三段论"

Introduction "接下来是析取三段论的证明."

--Statement (p q : Prop) (h:p∧q):q∧p:=by
  --exact And.intro (And.right h) (And.left h)

Statement(a b:Prop)
:((a∨b)∧¬b)→a:= by
intro ⟨hab,hnb⟩
rcases hab with ha | hb
·exact ha
·exact False.elim (hnb hb)


Conclusion "这样便是析取三段论."

/- Use these commands to add items to the game's inventory. -/

--NewTactic constructor rcases intro exact
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
