import Game.Metadata

World "forthworld"
Level 1

open Set
NewTheorem Set.setext

Title "幂等律"

Introduction "把一些事物聚集到一起就是集合，而这些事物就是集合的元素.集合有
列元素法和谓词表示法，谓词表示法大致形式为B={x|x∈R∧x²-1=0}的形式.元素和集合
有属于与不属于两种关系，分别记为∈,∉.集合之间也有包含和不包含的关系，记为⊆,⊈ .
不含任何元素的集合称为空集，记作∅，若一个问题涉及的集合都是某个集合的子集，则
该集合为全集，记作E.集合有交，并，补和对称差运算，接下来将会证明一些集合恒等式"

--Statement (p q : Prop) (h:p∧q):q∧p:=by
  --exact And.intro (And.right h) (And.left h)
universe u

Statement (α : Type u)(a : Set α) : a ∩ a = a :=by
  Hint "setext会把集合的等于变成谓词形式的等价"
  apply setext
  intro x
  constructor
  Hint "x∈a∩a的本质是x∈a∧x∈a"
  ·intro ⟨ha, _⟩
   exact ha
  ·intro ha
   exact ⟨ha, ha⟩


Conclusion "."

/- Use these commands to add items to the game's inventory. -/

--NewTactic exfalso apply

-- NewDefinition Nat Add Eq
