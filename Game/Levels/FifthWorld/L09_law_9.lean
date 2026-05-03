import Game.Metadata

World "fifthworld"
Level 9

open group

Title "ring2"

Introduction "对于环R中的元素a,b，a的负元与b的∘运算结果等于a与b的∘运算结果的负元"

--Statement (p q : Prop) (h:p∧q):q∧p:=by
  --exact And.intro (And.right h) (And.left h)
universe u

Statement {R : Type u} [Ring R](a b : R)
:(-'a)∘b=-'(a∘b):=by
have h:(-'a)∘b+'a∘b=-'(a∘b)+'a∘b:=by
  calc (-'a)∘b+'a∘b=(-'a+'a)∘b:=by rw[Ring.right_distrib]
       _=AddAbelgroup.zero∘b:=by rw[AddAbelgroup.add_left_neg]
       _=AddAbelgroup.zero:=by rw [Ring.zero_mul]
       _=-'(a∘b)+'a∘b:=by rw[←AddAbelgroup.add_left_neg]
have eq0 := add_right_cancel (h)
exact eq0



Conclusion "."

/- Use these commands to add items to the game's inventory. -/

--NewTactic calc
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
