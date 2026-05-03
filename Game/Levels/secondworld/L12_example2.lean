import Game.Metadata

open theo

World "Secondworld"
Level 12


Title "例题2"

NewTheorem theo.modus_tollens theo.De_Morgan_laws2

Introduction "如果小张守第一垒并且小李向B队投球，则A队取胜;或者A队未取胜，或者
A队成为联赛第一名;A队没有成为联赛的第一名;小张守第一垒.因此，小李没向B队投球.
解 设简单命题
p:小张守第一垒.
q:小李向B队投球.
r:A队取胜.
s:A队成为联赛第一名.
前提:(p∧q)→r,¬r∨s,¬s,p
结论:¬q"

--Statement (p q : Prop) (h:p∧q):q∧p:=by
  --exact And.intro (And.right h) (And.left h)

Statement (p q r s:Prop)(h1:(p∧q)→r)(h2:¬r∨s)(h3:¬s)(hp:p)
:¬q:=by
  have hnr : ¬r := disjunctive_syllogism (a := ¬r) (b:=s) ⟨h2,h3⟩
  have hnpq:¬(p∧q):=modus_tollens (a:= (p ∧ q)) (b:=r) ⟨h1, hnr⟩
  have hnpq':¬p∨¬q:=(De_Morgan_laws2 (a:= p) (b:=q)).mp hnpq
  have hnqp':¬q∨¬p:=(communtative_or (p:=¬p) (q:=¬q)).mp hnpq'
  have hnnp :¬¬p:= (double_neg_law (a := p)).mp hp
  have hnq : ¬q := disjunctive_syllogism (a := ¬q) (b:=¬p) ⟨hnqp',hnnp⟩
  -- 用 modus_ponens 从 h1 和 hpq 得到 r
  exact hnq




Conclusion "到这里第二个例题证明完毕了."

/- Use these commands to add items to the game's inventory. -/

--NewTactic constructor rcases intro exact
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
