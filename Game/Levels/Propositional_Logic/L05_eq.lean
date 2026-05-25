import Game.Metadata

World "Propositional_Logic"
Level 5

Title "communtative law"

Introduction "等价等值式表示一个等价可以是两个蕴含的析取"

Statement(p q:Prop)
:(p↔q)↔((p→q)∧(q→p)):=by
 constructor
 ·intro h
  Hint "对于一个等价，它的.1,.2会得出两个蕴含"
  exact ⟨h.1,h.2⟩
 ·intro ⟨hpq, hqp⟩
  Hint "Iff.intro可以将两个不同方向的蕴含变成等价"
  exact Iff.intro hpq hqp

--等价等值式

Conclusion "这里等价等值式构造完成了."

/- Use these commands to add items to the game's inventory. -/
--NewTactic constructor
NewTheorem Iff.intro
-- NewDefinition Nat Add Eq
