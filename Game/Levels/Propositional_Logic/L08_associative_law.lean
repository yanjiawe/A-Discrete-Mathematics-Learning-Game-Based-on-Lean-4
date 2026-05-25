import Game.Metadata

World "Propositional_Logic"
Level 8

Title "communtative law"

Introduction "结合律对于析取和合取都适用，这里先证明析取的结合律."

Statement(a b c:Prop)
:((a∧b)∧c)↔(a∧(b∧c)):=by
 constructor
 · intro h
   rcases h with ⟨h1,h2⟩
   rcases h1 with ⟨ha,hb⟩
   · exact ⟨ha,⟨hb,h2⟩⟩
 · intro h
   rcases h with ⟨h1,h2⟩
   rcases h2 with ⟨hb,hc⟩
   · exact ⟨ ⟨h1,hb⟩ ,hc⟩

--结合律

Conclusion "至此析取的结合律证明完毕了."

/- Use these commands to add items to the game's inventory. -/
--NewTactic constructor
--NewTheorem Iff.intro
-- NewDefinition Nat Add Eq
