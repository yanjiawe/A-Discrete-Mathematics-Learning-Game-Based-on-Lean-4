import Game.Metadata

World "Propositional_Logic"
Level 18

Title "communtative law"

Introduction "归谬论，即((a → b) ∧ (a → ¬b)) ↔ ¬a，
由a得到两个矛盾的命题，则a为假，从另一个方向来看，两个蕴含均已假为前件，必然为真."

Statement(a b : Prop)
 : ((a → b) ∧ (a → ¬b)) ↔ ¬a := by
  constructor
  · intro ⟨hab, hanb⟩
    intro ha
    exact (hanb ha) (hab ha)
  · intro h
    constructor
    · intro ha
      exact False.elim (h ha)
    · intro ha hb
      exact False.elim (h ha)


--归谬论

Conclusion "至此归谬论证明完毕."

/- Use these commands to add items to the game's inventory. -/
--NewTactic trivial
--NewTheorem Iff.intro
-- NewDefinition Nat Add Eq
