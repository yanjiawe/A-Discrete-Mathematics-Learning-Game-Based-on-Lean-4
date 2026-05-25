import Game.Metadata

World "Graph_Theory"
Level 1

open GraphTheory

Title "List.foldl_range_add"

Introduction "握手定理是图论的一个经典定理，这里我们将为握手定理的证明进行一
些铺垫。我们预先定义了几个函数，其中一个便是sumrange函数，他会对列表种的每个元素应用
传入的f函数，然后将这些返回值累加返回。List.foldl_range_add是一条辅助定理，证明两个
函数对列表元素应用的累加和与分别计算每个函数的累加和再相加相等。
"

--Statement (p q : Prop) (h:p∧q):q∧p:=by
  --exact And.intro (And.right h) (And.left h)
Statement{n : Nat} {f g : Nat → Nat} :
    (List.range n).foldl (fun acc i => acc + (f i + g i)) 0 =
    (List.range n).foldl (fun acc i => acc + f i) 0 +
    (List.range n).foldl (fun acc i => acc + g i) 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp [List.range_succ, List.foldl_append, List.foldl_cons, ih]
      rw [Nat.add_assoc, Nat.add_assoc, Nat.add_left_comm (f n)]




Conclusion "."

/- Use these commands to add items to the game's inventory. -/

--NewTactic calc
NewTheorem Nat.add_left_comm  List.range_succ  List.foldl_append List.foldl_cons
-- NewDefinition Nat Add Eq
