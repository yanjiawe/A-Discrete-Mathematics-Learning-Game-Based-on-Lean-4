import Game.Metadata

World "Firstworld"
Level 4

Title "communtative law"

Introduction "矛盾律，通过两个互斥的析取得到一个假，或者一个假可以得到任意一个命题及其补的析取."

Statement(p:Prop)
:p∧¬p↔False:=by
constructor
· intro ⟨hp, hnp⟩
  exact hnp hp
· intro f
  Hint "False.elim在给定一个假的情况下，可以构造任意命题"
  exact False.elim f
--矛盾律

Conclusion "矛盾律证明完毕."

/- Use these commands to add items to the game's inventory. -/
  NewTactic constructor
--NewTheorem False.elim
-- NewDefinition Nat Add Eq
