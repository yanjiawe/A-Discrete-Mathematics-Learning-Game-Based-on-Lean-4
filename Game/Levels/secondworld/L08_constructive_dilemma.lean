import Game.Metadata

World "Secondworld"
Level 8

Title "构造性二难"

Introduction "构造性二难有普通和特殊两种形式，这里是普通形式."

--Statement (p q : Prop) (h:p∧q):q∧p:=by
  --exact And.intro (And.right h) (And.left h)

Statement(a b c d:Prop)
:((a→b)∧(c→d)∧(a∨c))→(b∨d):=by
intro ⟨hab,hcd,hac⟩
rcases hac with ha | hc
·exact Or.inl (hab ha)
·exact Or.inr (hcd hc)


Conclusion "这样便是普通形式的构造性二难."

/- Use these commands to add items to the game's inventory. -/

--NewTactic constructor rcases intro exact
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
