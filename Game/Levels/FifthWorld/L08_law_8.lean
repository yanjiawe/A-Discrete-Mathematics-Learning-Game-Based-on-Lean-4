import Game.Metadata

World "fifthworld"
Level 8

open group

Title "ring1"

Introduction "对于一个代数系统有两个二元运算，若对+构成交换群，∘构成半群，并
且∘关于+适合分配律，那么该代数系统称为环，接下来证明几条环的性质。任意元素a与零元的
∘运算结果均为零元"

--Statement (p q : Prop) (h:p∧q):q∧p:=by
  --exact And.intro (And.right h) (And.left h)
universe u

Statement {R : Type u} [Ring R](a : R)
: a ∘ AddAbelgroup.zero = AddAbelgroup.zero := by
have h : (a ∘ AddAbelgroup.zero) +' AddAbelgroup.zero = (a ∘ AddAbelgroup.zero) +' (a ∘ AddAbelgroup.zero) := by
  calc (a ∘ AddAbelgroup.zero) +' AddAbelgroup.zero = a ∘ AddAbelgroup.zero := by rw [AddAbelgroup.add_zero]
        _ = a∘(AddAbelgroup.zero +' AddAbelgroup.zero):= by rw[AddAbelgroup.add_zero]
        _ =a∘AddAbelgroup.zero +' a∘AddAbelgroup.zero:=by rw[Ring.left_distrib]
have eq0 := add_left_cancel (h)
exact eq0.symm



Conclusion "."

/- Use these commands to add items to the game's inventory. -/

--NewTactic calc
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
