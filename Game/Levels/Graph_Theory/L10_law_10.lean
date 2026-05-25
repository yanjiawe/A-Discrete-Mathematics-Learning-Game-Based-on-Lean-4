import Game.Metadata

World "Graph_Theory"
Level 10

open GraphTheory

Title "regular_graph_edge_count"

Introduction "regular_graph_edge_count即我们要证明的握手定理特例。
"

--Statement (p q : Prop) (h:p∧q):q∧p:=by
  --exact And.intro (And.right h) (And.left h)

Statement (g : Graph) (k : Nat) (hreg : isRegular g k):k * g.n = 2 * edgeCount g := by
  have h_hand := handshaking_lemma g
  -- 将度数之和替换为常数 k 的和
  rw [sumRange_congr g.n (degree g) (fun _ => k) (by intro i hi; exact hreg i hi)] at h_hand
  -- 常数求和为 k * g.n
  have sum_const : sumRange g.n (fun _ => k) = k * g.n := by
    induction g.n with
    | zero => simp [sumRange]
    | succ n ih =>
        simp [sumRange, List.range_succ, List.foldl_append, List.foldl_cons,Nat.mul_succ]
  rw [sum_const] at h_hand
  exact h_hand



Conclusion "."

/- Use these commands to add items to the game's inventory. -/

--NewTactic calc
NewTheorem GraphTheory.odd_degree_count_even
-- NewDefinition Nat Add Eq
