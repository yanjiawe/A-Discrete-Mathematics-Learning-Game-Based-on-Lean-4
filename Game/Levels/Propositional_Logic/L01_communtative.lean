import Game.Metadata

World "Propositional_Logic"
Level 1

Title "communtative law"

Introduction "首先证明析取的交换律，可以使用intro拆分为两个蕴含来证明，⟨a,b⟩会将a,b变成a∧b的样子."

--Statement (p q : Prop) (h:p∧q):q∧p:=by
  --exact And.intro (And.right h) (And.left h)

Statement (p q : Prop)
: p ∧ q ↔ q ∧ p:=by
Hint "constructor可以将等价分解"
constructor
· intro h
  Hint "rcases可以把两个命题的析取，合取拆分"
  rcases h with ⟨hp, hq⟩
  Hint "exact会将当前项作为证据提交与目标匹配"
  exact ⟨hq, hp⟩
· intro h
  rcases h with ⟨hq, hp⟩
  exact ⟨hp, hq⟩

Conclusion "析取的交换律已经证明好了，接下来是对合取的交换律的证明."

/- Use these commands to add items to the game's inventory. -/

  NewTactic constructor rcases intro exact
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
