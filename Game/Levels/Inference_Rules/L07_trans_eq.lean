import Game.Metadata

World "Inference_Rules"
Level 7

Title "等价三段论"

Introduction "等价三段论，两个等价的传递."

--Statement (p q : Prop) (h:p∧q):q∧p:=by
  --exact And.intro (And.right h) (And.left h)

Statement(a b c : Prop) : ((a ↔ b) ∧ (b ↔ c)) → (a ↔ c) := by
  intro h
  rcases h with ⟨hab, hbc⟩
  constructor
  · intro ha
    exact hbc.1 (hab.1 ha)
  · intro hc
    exact hab.2 (hbc.2 hc)

Conclusion "这样便是等价三段论."

/- Use these commands to add items to the game's inventory. -/

--NewTactic constructor rcases intro exact
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
