import Game.Metadata

World "thirdworld"
Level 7

Title "量词辖域收缩与扩张等值式"

Introduction "Ax含自由变元x，而B不含x的自由出现，
则(∃x,((A x)∨B)) ↔ ((∃ x, A x)∨B)."

--Statement (p q : Prop) (h:p∧q):q∧p:=by
  --exact And.intro (And.right h) (And.left h)
universe u

Statement {X : Type u}{x:Nonempty X} {A : X→ Prop}{B:Prop}
: (∃x,((A x)∨B)) ↔ ((∃ x, A x)∨B)
:= by
  constructor
  · intro h
    rcases h with ⟨x,hx⟩
    rcases hx with hax | hb
    ·exact Or.inl ⟨x, hax⟩
    ·exact Or.inr hb
  · intro h
    rcases h with (h_exists | hb)
    · rcases h_exists with ⟨x, hax⟩
      exact ⟨x, Or.inl hax⟩
    · have x0: X :=by  exact Classical.choice x
      exact ⟨x0, Or.inr hb⟩


Conclusion "."

/- Use these commands to add items to the game's inventory. -/

--NewTactic exfalso apply
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
