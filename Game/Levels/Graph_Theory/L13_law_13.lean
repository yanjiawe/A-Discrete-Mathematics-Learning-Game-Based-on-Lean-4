import Game.Metadata

World "Graph_Theory"
Level 13

open GraphTheory

Title "complete_graph_edge_count"

Introduction "通过应用之前的两条引理，这里将证明完全图的度数为(n-1)*n/2.
"

--Statement (p q : Prop) (h:p∧q):q∧p:=by
  --exact And.intro (And.right h) (And.left h)

Statement (n : Nat) :
    edgeCount (completeGraph n) = n * (n - 1) / 2 := by
  simp [edgeCount, completeGraph]
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [completeEdges]
    simp [List.length_append, List.length_map, List.length_range, ih]
    --rw[]
    -- 目标：n + n * (n - 1) / 2 = (n + 1) * n / 2
    --apply Nat.mul_left_cancel 2 (n + n * (n - 1) / 2) (n + 1) * n / 2
    have hdiv_left : 2 ∣ n * (n - 1) := by
      cases n with
      | zero => simp
      | succ n =>
      have : (Nat.succ n) * (Nat.succ n - 1) = (Nat.succ n) * n := by simp
      rw [this, Nat.mul_comm]
      exact two_dvd_mul_succ n
    have hdiv_right : 2 ∣ (n + 1) * n := by
      rw [Nat.mul_comm]
      exact two_dvd_mul_succ n
    apply (Nat.eq_of_mul_eq_mul_left (by decide : 0<2))
    calc
      2 * (n + n * (n - 1) / 2) = 2 * n + 2 *(n * (n - 1) / 2) := by rw [Nat.mul_add]
      --_ = 2 * n + 2 *((n * (n - 1))) / 2 := by rw [Nat.mul_div_assoc 2 hdiv_left]
      --_ = 2 * n + (n * (n - 1)) * 2 / 2 := by rw [Nat.mul_comm 2 (n * (n - 1))]
      _ = 2 * n + n * (n - 1) := by rw [Nat.mul_div_cancel' hdiv_left]
      _ = (n + 1) * n := two_mul_add_mul_sub_one n
      _ = 2 * ((n + 1) * n / 2) := by rw [Nat.mul_div_cancel' hdiv_right]




Conclusion "."

/- Use these commands to add items to the game's inventory. -/

--NewTactic calc
NewTheorem GraphTheory.two_mul_add_mul_sub_one Nat.mul_div_cancel' Nat.eq_of_mul_eq_mul_left
-- NewDefinition Nat Add Eq
