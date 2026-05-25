import Game.Metadata

World "Propositional_Logic"
Level 14

Title "communtative law"

Introduction "零律有两种，第一个是使任意一个命题和1的合取是1，1可以变成和任意命题的合取."


Statement(a : Prop) : a ∨ True ↔ True := by
  constructor
  · intro h
    rcases h with ha | ht
    Hint "True.intro可以制造一个True"
    · exact True.intro
    · exact ht
  · intro h
    exact Or.inr True.intro
--零律

Conclusion "至此零律第一部分证明完毕."

/- Use these commands to add items to the game's inventory. -/
--NewTactic trivial
--NewTheorem Iff.intro
-- NewDefinition Nat Add Eq
