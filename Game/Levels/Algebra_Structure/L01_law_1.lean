import Game.Metadata

World "Algebra_Structure"
Level 1

open group

Title "pow1"

Introduction "设V=<S,∘>为代数系统，∘为二元运算，若可结合则为半群，若半群中
存在关于该运算的单位元，则为幺半群（独异点），若任意元素a都有逆元a⁻¹则为群，记作G
接下来会证明一些群的关于幂运算的性质，这里先证明一个元素逆的逆是他本身"

--Statement (p q : Prop) (h:p∧q):q∧p:=by
  --exact And.intro (And.right h) (And.left h)
universe u

Statement {G : Type u} [Group G](a : G) : (a⁻¹)⁻¹ = a := by
--Hint "calc是一种结构化语法，计算证明以calc开始，将一系列中间结果组合起来"
have h : (a⁻¹)⁻¹ ∘ a⁻¹ = a ∘ a⁻¹ := by rw [Group.mul_left_inv,Group.mul_right_inv]
have h2 : ((a⁻¹)⁻¹ ∘ a⁻¹) ∘ a = (a ∘ a⁻¹) ∘ a := by rw [h]
rw [Semigroup.mul_assoc] at h2
rw [Semigroup.mul_assoc] at h2
rw [Group.mul_left_inv, Monoid.mul_one, Monoid.mul_one] at h2
exact h2


Conclusion "."

/- Use these commands to add items to the game's inventory. -/

--NewTactic calc
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
