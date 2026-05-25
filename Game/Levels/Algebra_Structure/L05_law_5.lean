import Game.Metadata

World "Algebra_Structure"
Level 5

open group

Title "pow5"

Introduction "在群G中，对于G中元素a,b，他们运算可以交换，那么群为交换群或者叫阿贝尔群，
对于阿贝尔群，它满足(a∘b)^'n=(a ^'n)∘(b^'n)"
--Statement (p q : Prop) (h:p∧q):q∧p:=by
  --exact And.intro (And.right h) (And.left h)
universe u

Statement {G' : Type u} [Abel G'](a b: G') : ∀n : Nat, (a∘b)^'n=(a ^'n)∘(b^'n):=by
intro n
induction n with
|zero =>
  simp [pow_zero,Monoid.one_mul]
| succ n ih
calc
(a∘b)^'(n+1)=(a∘b)∘(a∘b)^'n:= by simp[pow_succ]
_=(a∘b)∘((a ^'n)∘(b^'n)) := by rw[ih]
_=(b∘a)∘((a ^'n)∘(b^'n)) := by rw [←Abel.mul_mul a b]
_=b ∘ (a ∘ ((a ^' n) ∘ (b ^' n))) := by rw [Semigroup.mul_assoc]
_=b ∘ ((a ∘ (a ^' n)) ∘ (b ^' n)) := by rw [Semigroup.mul_assoc]
_=b ∘ ((a ^' (n+1)) ∘ (b ^' n)) := by simp [pow_succ]
_=((a ^' (n+1)) ∘ (b ^' n))∘b :=by rw [←Abel.mul_mul]
_=(a ^' (n+1)) ∘ ((b ^' n)∘b) :=by rw [Semigroup.mul_assoc]
_=(a ^' (n+1)) ∘ (b∘(b ^' n)) :=by rw [Abel.mul_mul b]
_=(a ^' (n+1)) ∘ (b ^' (n+1)) :=by simp [pow_succ]



Conclusion "."

/- Use these commands to add items to the game's inventory. -/

--NewTactic calc
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
