import Game.Metadata

World "sixthworld"
Level 6

open GraphTheory

Title "List.foldl_add_const"

Introduction "List.foldl_add_const将证明累加的初始值可以拆分为初始值与0的和。
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
NewTheorem GraphTheory.sumRange_indicator_two
-- NewDefinition Nat Add Eq
