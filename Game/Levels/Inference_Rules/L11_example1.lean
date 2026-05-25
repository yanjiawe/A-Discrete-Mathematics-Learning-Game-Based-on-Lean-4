import Game.Metadata

open theo

World "Inference_Rules"
Level 11


Title "例题1"

NewTheorem theo.double_neg_law theo.disjunctive_syllogism theo.modus_ponens theo.communtative_or


Introduction "接下来的例题请应用等值式模式和推理规则证明结论,如果小张和小王去看
电影，则小李也去看电影;小赵不去看电影或小张去看电影;小王去看电影.所以，当小赵去看
电影时，小李也去.
解 设简单命题
p:小张去看电影.
q:小王去看电影.
r:小李去看电影.
s:小赵去看电影.
前提:(p∧q)→r,¬s∨p,q
结论:s-r"

--Statement (p q : Prop) (h:p∧q):q∧p:=by
  --exact And.intro (And.right h) (And.left h)

Statement (p q r s:Prop)(h1:(p∧q)→r)(h2:¬s∨p)(hq:q)
:s→r:=by
  intro hs
  have hnn : ¬¬s := (double_neg_law (a := s)).mp hs
  have h2':p∨¬s:= (communtative_or (p:=¬s) (q:=p)).mp h2
  have hp : p := disjunctive_syllogism (a := p) (b:=¬s) ⟨h2',hnn⟩
  have hpq : p ∧ q := ⟨hp, hq⟩
  -- 用 modus_ponens 从 h1 和 hpq 得到 r
  exact modus_ponens (a:= (p ∧ q)) (b:=r) ⟨h1, hpq⟩




Conclusion "到这里第一个例题证明完毕了."

/- Use these commands to add items to the game's inventory. -/

--NewTactic constructor rcases intro exact
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
