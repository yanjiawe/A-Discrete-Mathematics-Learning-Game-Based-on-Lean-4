import Game.Metadata

World "Firstworld"
Level 11

Title "communtative law"

Introduction "接下来证明第二部分分配律."

Statement(a b c:Prop)
:(a∧(b∨c))↔((a∧b)∨(a∧c)):= by
constructor
· intro h
  rcases h with  ⟨ha,hbc⟩
  · rcases hbc with hb | hc
    · exact Or.inl ⟨ha,hb⟩
    · exact Or.inr ⟨ha,hc⟩
· intro h
  rcases h with hab | hac
  · rcases hab with ⟨ha,hb⟩
    · exact ⟨ha,(Or.inl hb)⟩
  · rcases hac with ⟨ha,hc⟩
    · exact⟨ha,(Or.inr hc)⟩
--分配律

Conclusion "至此分配律证明完毕."

/- Use these commands to add items to the game's inventory. -/
--NewTactic constructor
--NewTheorem Iff.intro
-- NewDefinition Nat Add Eq
