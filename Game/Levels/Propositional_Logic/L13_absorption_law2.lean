import Game.Metadata

World "Propositional_Logic"
Level 13

Title "communtative law"

Introduction "这里开始吸收律第二部分，一个命题析取比他范围大的命题即是命题本身."

Statement(a b:Prop)
:(a∧(a∨b))↔a:=by
constructor
·intro h
 rcases h with ⟨ha,hab⟩
 ·exact ha
·intro h
 ·exact ⟨h,(Or.inl h)⟩
--吸收律

Conclusion "至此吸收律证明完毕."

/- Use these commands to add items to the game's inventory. -/
--NewTactic constructor
--NewTheorem Iff.intro
-- NewDefinition Nat Add Eq
