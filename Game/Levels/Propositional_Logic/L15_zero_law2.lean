import Game.Metadata

World "Propositional_Logic"
Level 15

Title "communtative law"

Introduction "下来零律的第二种，任意命题和假析取会得到假，假可以推出和任意命题的析取."


Statement(a : Prop) : a ∧  False ↔ False := by
  constructor
  · intro h
    rcases h with ⟨ha,hf⟩
    · exact hf
  · intro h
    exact ⟨(False.elim h),h⟩

--零律

Conclusion "至此零律证明完毕."

/- Use these commands to add items to the game's inventory. -/
--NewTactic trivial
--NewTheorem Iff.intro
-- NewDefinition Nat Add Eq
