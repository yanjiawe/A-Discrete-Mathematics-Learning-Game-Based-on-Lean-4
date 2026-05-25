import Game.Metadata

World "Propositional_Logic"
Level 12

Title "communtative law"

Introduction "吸收律分别有合取的和析取的，一个命题合取一个范围比他小的命题即是它的本身."

Statement(a b:Prop)
:(a∨(a∧b))↔a:=by
constructor
·intro h
 rcases h with ha | hab
 ·exact ha
 ·rcases hab with⟨ha1,hb⟩
  ·exact ha1
·intro h
 ·exact Or.inl h
--吸收律

Conclusion "至此第一部分吸收律证明完毕."

/- Use these commands to add items to the game's inventory. -/
--NewTactic constructor
--NewTheorem Iff.intro
-- NewDefinition Nat Add Eq
