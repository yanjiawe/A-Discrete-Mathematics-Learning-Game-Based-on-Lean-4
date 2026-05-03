import Game.Metadata

World "Firstworld"
Level 17

Title "communtative law"

Introduction "第二种同一律即是任意命题和1的析取都是该命题，任意命题可以推出任意命题和1的析取."

Statement(a:Prop)
:(a∧True)↔a:=by
constructor
· intro h
  rcases h with ⟨ha,hf⟩
  · exact ha
· intro h
  exact ⟨h,True.intro⟩

--同一律

Conclusion "至此同一律证明完毕."

/- Use these commands to add items to the game's inventory. -/
--NewTactic trivial
--NewTheorem Iff.intro
-- NewDefinition Nat Add Eq
