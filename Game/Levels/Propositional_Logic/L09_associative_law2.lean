import Game.Metadata

World "Propositional_Logic"
Level 9

Title "communtative law"

Introduction "对于合取，结合律也成立."

Statement(a b c:Prop)
:((a∨b)∨c)↔(a∨(b∨c)):= by
 constructor
 · intro h
   rcases h with h1 | hc
   · rcases h1 with ha | hb
     · exact Or.inl ha
     · exact Or.inr (Or.inl hb)
   · exact Or.inr (Or.inr hc)
 · intro h
   rcases h with ha | h2
   · exact Or.inl (Or.inl ha)
   · rcases h2 with hb | hc
     · exact Or.inl (Or.inr hb)
     · exact Or.inr hc

--结合律

Conclusion "至此结合律证明完成."

/- Use these commands to add items to the game's inventory. -/
--NewTactic constructor
--NewTheorem Iff.intro
-- NewDefinition Nat Add Eq
