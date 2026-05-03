import Game.Metadata

World "Secondworld"
Level 3

Title "假言推理"

Introduction "接下来是假言推理."

--Statement (p q : Prop) (h:p∧q):q∧p:=by
  --exact And.intro (And.right h) (And.left h)

Statement(a b:Prop)
:((a→b)∧a)→b:=by
intro ⟨hab,ha⟩
exact (hab ha)


Conclusion "至此假言推理证明完毕."

/- Use these commands to add items to the game's inventory. -/

--NewTactic constructor rcases intro exact
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
