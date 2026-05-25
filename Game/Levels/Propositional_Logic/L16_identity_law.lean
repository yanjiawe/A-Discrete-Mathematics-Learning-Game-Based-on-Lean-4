import Game.Metadata

World "Propositional_Logic"
Level 16

Title "communtative law"

Introduction "同一律和零律形式相反，第一种是任意命题和假合取会得到该命题，任意命题可以表现为和假的合取."


Statement(a:Prop)
:(a∨False)↔a:=by
constructor
· intro h
  rcases h with ha | hf
  · exact ha
  · exact False.elim hf
· intro h
  exact Or.inl h

--同一律

Conclusion "至此第一种同一律证明完毕."

/- Use these commands to add items to the game's inventory. -/
--NewTactic trivial
--NewTheorem Iff.intro
-- NewDefinition Nat Add Eq
