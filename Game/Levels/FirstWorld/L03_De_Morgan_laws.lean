import Game.Metadata
--open Classical

World "Firstworld"
Level 3

Title "communtative law"

Introduction "德摩根律，即¬(a ∨ b) ↔ ¬a ∧ ¬b，接下来要对该式进行证明."

 --Statement (p q : Prop) (hp : p) (hnp : ¬p) : q :=by
 --exact False.elim (hnp hp)
--交换律，排中律
--Statement(p : Prop) : p ∨ ¬p ↔ True := by
  --constructor
 -- · intro _
  --  trivial
 -- · intro _
  --  exact Classical.em p

Statement(a b : Prop) : ¬(a ∨ b) ↔ ¬a ∧ ¬b := by
  constructor
  · intro h
    constructor
    · intro ha
      Hint "¬a可以看成a→False，可以当成一个函数使用"
      exact h (Or.inl ha)
    · intro hb
      exact h (Or.inr hb)
  · intro ⟨hna, hnb⟩ h
    rcases h with (ha | hb)
    · exact hna ha
    · exact hnb hb

--德摩根律

Conclusion "到这里德摩根律的证明完成了."

/- Use these commands to add items to the game's inventory. -/

  --NewTactic rcases
--NewTheorem Classical.em
-- NewDefinition Nat Add Eq
