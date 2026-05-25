import Game.Metadata

World "Graph_Theory"
Level 4

open GraphTheory

Title "sumRange_zero'"

Introduction "这条辅助定理sumRange_zero'证明了当 f 恒为零时 sumRange 为 0
"

--Statement (p q : Prop) (h:p∧q):q∧p:=by
  --exact And.intro (And.right h) (And.left h)

Statement(n : Nat) : sumRange n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [sumRange]
      rw[ List.range_succ,List.foldl_append, List.foldl_cons]
      rw[←sumRange]
      rw[ih]
      rw[List.foldl_nil]



Conclusion "."

/- Use these commands to add items to the game's inventory. -/

--NewTactic calc
NewTheorem GraphTheory.sumRange_congr
-- NewDefinition Nat Add Eq
