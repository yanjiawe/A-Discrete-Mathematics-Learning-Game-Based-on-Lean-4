import Game.Metadata

World "Graph_Theory"
Level 2

open GraphTheory

Title "sumRange_add"

Introduction "sumRange_add将第一条辅助定理的形式进行转换。
"

--Statement (p q : Prop) (h:p∧q):q∧p:=by
  --exact And.intro (And.right h) (And.left h)

Statement (n : Nat) (f g : Vertex → Nat) :
    sumRange n (fun i => f i + g i) = sumRange n f + sumRange n g := by
  induction n with
  | zero => simp [sumRange]
  | succ n ih =>
      simp[sumRange]



Conclusion "."

/- Use these commands to add items to the game's inventory. -/

--NewTactic calc
NewTheorem GraphTheory.sumRange GraphTheory.List.foldl_range_add
-- NewDefinition Nat Add Eq
