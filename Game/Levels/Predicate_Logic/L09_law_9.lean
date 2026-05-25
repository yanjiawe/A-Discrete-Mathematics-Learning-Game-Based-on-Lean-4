import Game.Metadata

World "Predicate_Logic"
Level 9

open theo
NewTheorem theo.law_1


Title "量词辖域收缩与扩张等值式"

Introduction "Ax含自由变元x，而B不含x的自由出现，
则(∃x,((A x)→B)) ↔ ((∀x, A x)→ B)."


--Statement (p q : Prop) (h:p∧q):q∧p:=by
  --exact And.intro (And.right h) (And.left h)
universe u

Statement {X : Type u}{x:Nonempty X} {A : X→ Prop}{B:Prop}
: (∃x,((A x)→B)) ↔ ((∀x, A x)→ B)
:= by
  constructor
  · intro h h_exists
    rcases h with ⟨x, hx⟩
    exact hx (h_exists x)
  · intro h
    by_cases hb : B
    · have x0 : X := by exact Classical.choice x
      exact ⟨x0, λ _ => hb⟩
    · by_cases h_forall : ∀ x, A x
      · exfalso
        exact hb (h h_forall)
      · rw [law_1] at h_forall
        rcases h_forall with ⟨x, hx⟩
        exact ⟨x, λ ha => False.elim (hx ha)⟩

Conclusion "."

/- Use these commands to add items to the game's inventory. -/

--NewTactic exfalso apply

-- NewDefinition Nat Add Eq
