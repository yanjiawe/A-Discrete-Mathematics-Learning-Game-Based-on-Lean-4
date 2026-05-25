import Game.Metadata

World "Graph_Theory"
Level 9

open GraphTheory

Title "odd_degree_count_even"

Introduction "odd_degree_count_even将证明所有顶点度数之和为偶数。
"

--Statement (p q : Prop) (h:p∧q):q∧p:=by
  --exact And.intro (And.right h) (And.left h)

Statement {α : Type} (f : Nat → α → Nat) (l : List α) (init c : Nat)
    (h : ∀ b a, f (b + c) a = f b a + c) :
    List.foldl f (init + c) l = List.foldl f init l + c := by
  induction l generalizing init with
  | nil => simp
  | cons a l' ih =>
      simp [List.foldl_cons]
      rw [←ih (f init a)]
      rw [h init a]



Conclusion "."

/- Use these commands to add items to the game's inventory. -/

--NewTactic calc
NewTheorem GraphTheory.sumRange_mul_const
-- NewDefinition Nat Add Eq
