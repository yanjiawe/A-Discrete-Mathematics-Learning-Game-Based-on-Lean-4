import Game.Metadata

World "sixthworld"
Level 12

open GraphTheory

Title "two_mul_add_mul_sub_one"

Introduction "two_mul_add_mul_sub_one将证明2*n + n*(n-1) = (n+1)*n.
"

--Statement (p q : Prop) (h:p∧q):q∧p:=by
  --exact And.intro (And.right h) (And.left h)

Statement (n : Nat) : 2 * n + n * (n - 1) = (n + 1) * n := by
  cases n with
  | zero => simp
  | succ n =>
    simp [Nat.succ_sub_succ, Nat.sub_zero]
    calc
      2 * (n + 1) + (n + 1) * n = (n + 1) * n + 2 * (n + 1) := by rw [Nat.add_comm]
      _ = (n + 1) * n + (n + 1) * 2 := by rw [Nat.mul_comm (n + 1) 2]
      _ = (n + 1) * (n + 2) := by rw [Nat.mul_add]
      _ = (n + 2) * (n + 1) := by rw [Nat.mul_comm]



Conclusion "."

/- Use these commands to add items to the game's inventory. -/

--NewTactic calc
NewTheorem GraphTheory.two_dvd_mul_succ
-- NewDefinition Nat Add Eq
