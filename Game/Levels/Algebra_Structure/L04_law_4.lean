import Game.Metadata

World "Algebra_Structure"
Level 4

open group

Title "pow4"

Introduction "在群G中，对于G中元素a，他们运算(a ^' n)^'m等于(a ^'(n*m))"

--Statement (p q : Prop) (h:p∧q):q∧p:=by
  --exact And.intro (And.right h) (And.left h)
universe u

Statement {G : Type u} [Group G](a : G) : ∀ m n : Nat, (a ^' n)^'m=(a ^'(n*m)):=by
intro m n
induction m generalizing n with
|zero =>
  simp [pow_zero]
|succ m ih
calc
(a ^' n)^'(m+1)=(a ^'n)∘(a^'n)^'m := by simp [pow_succ]
_=(a ^'n)∘a ^'(n*m):= by rw [ih]
_=a^'(n+n*m):= by rw [pow_3]
_=a^'(n+m*n):= by rw [Nat.mul_comm]
_=a^'(m*n+n):= by rw [Nat.add_comm]
_=a^'((m+1)*n):= by rw [←Nat.add_one_mul]
_=a^'(n*(m+1)):= by rw [Nat.mul_comm]




Conclusion "."

/- Use these commands to add items to the game's inventory. -/

--NewTactic calc
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
