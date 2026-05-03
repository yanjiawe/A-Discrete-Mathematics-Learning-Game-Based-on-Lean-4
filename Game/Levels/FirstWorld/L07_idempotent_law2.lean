import Game.Metadata

World "Firstworld"
Level 7

Title "communtative law"

Introduction "幂等律，即一个命题可以转换成同一命题的析取."

Statement(p:Prop)
:p↔(p∧p):=by
 constructor
 · intro h
   exact ⟨h,h⟩
 · intro h
   rcases h with ⟨h1,h2⟩
   · exact h1

--幂等律

Conclusion "到这里完成了幂等律证明."

/- Use these commands to add items to the game's inventory. -/
--NewTactic constructor
--NewTheorem Iff.intro
-- NewDefinition Nat Add Eq
