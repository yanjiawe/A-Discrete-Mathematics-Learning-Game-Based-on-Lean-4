import Game.Metadata

World "Propositional_Logic"
Level 2

Title "communtative law"

Introduction "合取的交换律和析取的类似，将等价拆分然后分别证明."

--Statement (p q : Prop) (h : p ∨ q) : q ∨ p := by
 -- rcases h with hp | hq
  --· exact Or.inr hp
 -- · exact Or.inl hq

Statement(p q : Prop)
: p ∨ q ↔ q ∨ p:=by
constructor
· intro h
  rcases h with hp | hq
  Hint "Or.inl Or.inr可以将已经有的命题自动匹配一个目标"
  · exact Or.inr hp
  · exact Or.inl hq
· intro h
  rcases h with hp | hq
  · exact Or.inr hp
  · exact Or.inl hq


Conclusion "交换律已经证明完成，接下来将对德摩根律进行证明."

/- Use these commands to add items to the game's inventory. -/
--NewTactic rcases
  NewTheorem Or.inr Or.inl
-- NewDefinition Nat Add Eq
