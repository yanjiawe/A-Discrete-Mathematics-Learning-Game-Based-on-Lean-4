import Game.Metadata

World "Predicate_Logic"
Level 3

Title "量词辖域收缩与扩张等值式"

Introduction "Ax含自由变元x，而B不含x的自由出现，
则(∀x,((A x)∨B)) ↔ ((∀ x, A x)∨B)."

--Statement (p q : Prop) (h:p∧q):q∧p:=by
  --exact And.intro (And.right h) (And.left h)
universe u

Statement {x : Type u} {A : x → Prop}{B:Prop}
: (∀x,((A x)∨B)) ↔ ((∀ x, A x)∨B)
:= by
  constructor
  · intro h
    by_cases b : B
    · exact Or.inr b
    · Hint "left会将析取的证明变成证明左分支"
      left
      intro x
      rcases h x with ha | hb
      ·exact ha
      ·exact False.elim (b hb)
  · intro H
    intro x
    rcases H with hxa | hb
    ·exact Or.inl (hxa x)
    ·exact Or.inr hb


Conclusion "."

/- Use these commands to add items to the game's inventory. -/

NewTactic left
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
