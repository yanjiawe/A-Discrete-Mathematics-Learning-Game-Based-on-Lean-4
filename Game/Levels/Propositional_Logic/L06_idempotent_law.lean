import Game.Metadata

World "Propositional_Logic"
Level 6

Title "communtative law"

Introduction "幂等律，即一个命题可以转换成同一命题的合取."

Statement(p:Prop)
:p↔(p∨p):=by
 constructor
 · intro h
   exact Or.inr h
 · intro h
   rcases h with h1 | h2
   · exact h1
   · exact h2

--幂等律

Conclusion "合取的幂等律构造完成了."

/- Use these commands to add items to the game's inventory. -/
--NewTactic constructor
--NewTheorem Iff.intro
-- NewDefinition Nat Add Eq
