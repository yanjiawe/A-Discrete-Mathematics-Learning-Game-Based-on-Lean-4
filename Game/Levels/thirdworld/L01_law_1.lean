import Game.Metadata

World "thirdworld"
Level 1

Title "量词否定等值式"

Introduction "设A(x)含自由出现的个体变项x，则并不是所有的X都有性质A与存在
没有性质A的x等价，即(¬ ∀ x, A x) ↔ (∃ x, ¬ A x)."

--Statement (p q : Prop) (h:p∧q):q∧p:=by
  --exact And.intro (And.right h) (And.left h)
universe u

Statement {X : Type u} {A : X → Prop}
: (¬ ∀ x, A x) ↔ (∃ x, ¬ A x)
:= by
  constructor
  · intro h
    Hint"by_cases会生成¬p和p两种假设，这里可以构造∃ x, ¬ A x"
    by_cases H : ∃ x, ¬ A x
    · exact H
    · Hint "exfalso将当前目标变成False，因为假可以导出任意命题，即矛盾证出任意"
      exfalso
      Hint "apply会将证明目标替换为前提，上一步我们将目标替换成了假，而h则是∀ (x : X), A x导出假"
      apply h
      intro x
      Hint "至此目标变成了A x,可以再次构造¬p和p两种假设，即Ax，¬Ax"
      by_cases hx : A x
      · exact hx
      · exfalso
        apply H
        exact ⟨x, hx⟩
  · intro ⟨x, hx⟩ hforall
    exact hx (hforall x)


Conclusion "."

/- Use these commands to add items to the game's inventory. -/

NewTactic exfalso apply
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
