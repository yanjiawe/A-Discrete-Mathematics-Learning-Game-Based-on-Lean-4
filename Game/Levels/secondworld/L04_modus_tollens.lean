import Game.Metadata

World "Secondworld"
Level 4

Title "拒取式"

Introduction "接下来是拒取式的证明."

--Statement (p q : Prop) (h:p∧q):q∧p:=by
  --exact And.intro (And.right h) (And.left h)

Statement(a b:Prop)
:((a→b)∧¬b)→¬a:= by
intro ⟨hab,hnb⟩ hna
exact hnb (hab hna)


Conclusion "这样便是拒取式."

/- Use these commands to add items to the game's inventory. -/

--NewTactic constructor rcases intro exact
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
