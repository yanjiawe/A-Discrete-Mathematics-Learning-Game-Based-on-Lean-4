import Game.Metadata

World "Firstworld"
Level 10

Title "communtative law"

Introduction "分配律分为析取对合取，和合取对析取的两种."

Statement(a b c:Prop)
:(a∨(b∧c))↔((a∨b)∧(a∨c)):= by
constructor
· intro h
  rcases h with ha | h2
  · exact ⟨(Or.inl ha),(Or.inl ha)⟩
  · rcases h2 with ⟨hb,hc⟩
    · exact ⟨(Or.inr hb),(Or.inr hc)⟩
· intro h
  rcases h with ⟨hab,hac⟩
  · rcases hab with ha | hb
    ·exact Or.inl ha
    ·rcases hac with ha2 | hc
     · exact Or.inl ha2
     · exact Or.inr ⟨hb,hc⟩

--分配律

Conclusion "至此第一部分分配律证明完毕了."

/- Use these commands to add items to the game's inventory. -/
--NewTactic constructor
--NewTheorem Iff.intro
-- NewDefinition Nat Add Eq
