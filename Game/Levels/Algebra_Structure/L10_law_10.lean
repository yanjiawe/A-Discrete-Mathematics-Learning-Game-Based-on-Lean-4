import Game.Metadata

World "Algebra_Structure"
Level 10

open group

Title "ring3"

Introduction "对于环R中的元素a,b,c，(b-'c)∘a等于b∘a-'c∘a，这里的-相当于+(-x)"

--Statement (p q : Prop) (h:p∧q):q∧p:=by
  --exact And.intro (And.right h) (And.left h)
universe u

Statement {R : Type u} [Ring R](a b c: R)
:(b-'c)∘a=b∘a-'c∘a:=by
calc (b-'c)∘a=(b+'(-'c))∘a:=by rw [AddAbelgroup.sub_to_add]
_=(b∘a)+'(-'c∘a):=by rw[Ring.right_distrib]
_=(b∘a)+'(-'(c∘a)):=by rw[ring_2]
_=b∘a-'c∘a:=by rw [AddAbelgroup.sub_to_add (b∘a) (c∘a)]



Conclusion "."

/- Use these commands to add items to the game's inventory. -/

--NewTactic calc
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
