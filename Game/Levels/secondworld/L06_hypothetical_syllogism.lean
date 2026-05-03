import Game.Metadata

World "Secondworld"
Level 6

Title "假言三段论"

Introduction "接下来要证明假言三段论，相当与蕴含的传递."

--Statement (p q : Prop) (h:p∧q):q∧p:=by
  --exact And.intro (And.right h) (And.left h)

Statement(a b c:Prop)
:((a→b)∧(b→c))→(a→c):= by
intro ⟨hab,hbc⟩ ha
exact hbc (hab ha)


Conclusion "这样便是假言三段论."

/- Use these commands to add items to the game's inventory. -/

--NewTactic constructor rcases intro exact
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
