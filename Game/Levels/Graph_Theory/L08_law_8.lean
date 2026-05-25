import Game.Metadata

World "Graph_Theory"
Level 8

open GraphTheory

Title "sumRange_mul_const"

Introduction " isOddDegree是预先定义的函数，表示该点的度数为奇数。
接下来是证明握手定理的特例，若每个节点的度数都为k，则K与顶点度数的积等于边数的两倍
首先证明sumRange_mul_const，和之前实现的辅助定理类似，不同的是该定理是将乘从固定
值sumrange种提取出来。
"

--Statement (p q : Prop) (h:p∧q):q∧p:=by
  --exact And.intro (And.right h) (And.left h)

Statement (n : Nat) (c : Nat) (f : Vertex → Nat) :
    sumRange n (fun i => c * f i) = c * sumRange n f := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [sumRange, List.range_succ, List.foldl_append, List.foldl_cons]
      rw [Nat.mul_add]
      simp
      rw[←sumRange]
      rw[←sumRange]
      exact ih



Conclusion "."

/- Use these commands to add items to the game's inventory. -/

--NewTactic calc
NewTheorem GraphTheory.handshaking_lemma Nat.mul_add
-- NewDefinition Nat Add Eq
