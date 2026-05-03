import Game.Metadata

World "sixthworld"
Level 3

open GraphTheory

Title "sumRange_congr "

Introduction "sumRange_congr证明了对每个 i，f i = g i，
则 sumRange n f = sumRange n g。
"

--Statement (p q : Prop) (h:p∧q):q∧p:=by
  --exact And.intro (And.right h) (And.left h)

Statement (n : Nat) (f g : Vertex → Nat)
    (h : ∀ i, i < n → f i = g i) : sumRange n f = sumRange n g := by
  induction n with
  | zero => simp [sumRange]
  | succ n ih =>
      simp [sumRange, List.range_succ, List.foldl_append, List.foldl_cons]
      rw[←sumRange]
      rw[←sumRange]
      rw [ih]
      · rw [h n (Nat.lt_succ_self n)]
      · intro i hi
        apply h
        exact Nat.lt_succ_of_lt hi



Conclusion "."

/- Use these commands to add items to the game's inventory. -/

--NewTactic calc
NewTheorem GraphTheory.sumRange_add
-- NewDefinition Nat Add Eq
