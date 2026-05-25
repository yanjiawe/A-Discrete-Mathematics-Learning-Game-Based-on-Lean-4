import Game.Metadata

World "Algebra_Structure"
Level 3

open group

Title "pow3"

Introduction "在群G中，对于G中元素b，他们运算(a ^' n) ∘ (a ^' m)
等于a ^' (n + m).这里我们定义了两个定理分别是pow_zero,pow_succ，他们会将0
次方变成单位元，以及a ^' (n + 1) 变成 a ∘ a ^' n的形式，并且用simp标记会进行反复重写"

--Statement (p q : Prop) (h:p∧q):q∧p:=by
  --exact And.intro (And.right h) (And.left h)
universe u

Statement {G : Type u} [Group G](a : G) : ∀ m n : Nat, (a ^' n) ∘ (a ^' m)=a ^' (n + m):=by
intro m n
induction n generalizing m with
|zero =>
  simp [pow_zero, Monoid.one_mul]
|succ n ih=>
calc
(a ^' (n+1)) ∘ (a ^' m) = (a∘a ^' n) ∘ (a ^' m) := by simp [pow_succ]
_ = a∘((a ^'n) ∘ (a ^' m)) := by rw [Semigroup.mul_assoc]
_ = a ∘ a ^' (n + m) := by rw [ih]
_ = a ^' ((n + m) + 1) := by simp [pow_succ]
_ = a ^' (n + 1 + m) := by have : (n + m) + 1 = (n + 1) + m := by
                                calc (n + m) + 1 = n + (m + 1) := by rw [Nat.add_assoc]
                                     _ = n + (1 + m) := by rw [Nat.add_comm m 1]
                                     _ = (n + 1) + m := by rw [←Nat.add_assoc]
                           rw [this]


Conclusion "."

/- Use these commands to add items to the game's inventory. -/

--NewTactic calc
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
