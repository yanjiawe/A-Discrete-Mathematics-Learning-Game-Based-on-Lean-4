import Game.Metadata

World "thirdworld"
Level 4

Title "量词辖域收缩与扩张等值式"

Introduction "Ax含自由变元x，而B不含x的自由出现，
则(∀x,((A x)∧B)) ↔ ((∀ x, A x)∧B)."

--Statement (p q : Prop) (h:p∧q):q∧p:=by
  --exact And.intro (And.right h) (And.left h)
universe u

Statement {X : Type u}{x:Nonempty X} {A : X→ Prop}{B:Prop}
: (∀x,((A x)∧B)) ↔ ((∀ x, A x)∧B)
:= by
  constructor
  · intro h
    have h1 : ∀ x, A x := by
      intro x
      exact (h x).1
    Hint "Classical.choice会从∀x中选出一个x"
    have x0: X :=by  exact Classical.choice x
    have hB : B := (h x0).2
    exact ⟨h1, hB⟩
  · intro ⟨hall, hB⟩
    intro x
    exact ⟨hall x, hB⟩


Conclusion "."

/- Use these commands to add items to the game's inventory. -/

--NewTactic exfalso apply
 NewTheorem Classical.choice
-- NewDefinition Nat Add Eq
