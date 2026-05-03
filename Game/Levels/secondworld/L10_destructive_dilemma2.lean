import Game.Metadata

World "Secondworld"
Level 10

Title "破坏性二难"

Introduction "下面是最后一条推理规则，破坏性二难的证明."

--Statement (p q : Prop) (h:p∧q):q∧p:=by
  --exact And.intro (And.right h) (And.left h)

Statement(a b c d : Prop) :
  ((a → b) ∧ (c → d) ∧ (¬b ∨ ¬d)) → (¬a ∨ ¬c) := by
  intro h
  rcases h with ⟨hab, hcd, hnbnd⟩
  rcases hnbnd with (hnb | hnd)
  · left
    intro ha
    exact hnb (hab ha)
  · right
    intro hc
    exact hnd (hcd hc)



Conclusion "这样便是破坏性二难."

/- Use these commands to add items to the game's inventory. -/

--NewTactic constructor rcases intro exact
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
