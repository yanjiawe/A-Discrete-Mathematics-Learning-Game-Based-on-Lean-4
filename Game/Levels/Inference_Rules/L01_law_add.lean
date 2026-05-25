import Game.Metadata

World "Inference_Rules"
Level 1

Title "附加律"

Introduction "接下来要证明几条推理规则，这里要证明附加律."

--Statement (p q : Prop) (h:p∧q):q∧p:=by
  --exact And.intro (And.right h) (And.left h)

Statement(a b:Prop)
:a→(a∨b):=by
intro x
exact Or.inl x


Conclusion "这样便是附加律."

/- Use these commands to add items to the game's inventory. -/

--NewTactic constructor rcases intro exact
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
