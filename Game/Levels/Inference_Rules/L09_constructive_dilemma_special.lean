import Game.Metadata

World "Inference_Rules"
Level 9

Title "构造性二难(特殊)"

Introduction "构造性二难有普通和特殊两种形式，这里是特殊形式."

--Statement (p q : Prop) (h:p∧q):q∧p:=by
  --exact And.intro (And.right h) (And.left h)

Statement(a b : Prop) :
  ((a → b) ∧ (¬a → b)) → b := by
  intro ⟨hab, hnab⟩
  by_cases ha : a
  · --a 成立
    exact hab ha
  · -- ¬a 成立
    exact hnab ha


Conclusion "这样便是特殊形式的构造性二难."

/- Use these commands to add items to the game's inventory. -/

--NewTactic constructor rcases intro exact
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
