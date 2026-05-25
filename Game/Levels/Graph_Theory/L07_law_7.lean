import Game.Metadata

World "Graph_Theory"
Level 7

open GraphTheory

Title "handshaking_lemma"

NewTheorem GraphTheory.List.foldl_add_const Nat.mul_succ Nat.add_right_comm Nat.zero_add

Introduction "这里将对握手定理进行证明。
"

--Statement (p q : Prop) (h:p∧q):q∧p:=by
  --exact And.intro (And.right h) (And.left h)

Statement(g : Graph) :
    sumRange g.n (degree g) = 2 * edgeCount g := by
  induction h : g.edges generalizing g with
  | nil =>
      have degree_zero : ∀ v, degree g v = 0 := by
        intro v
        simp [degree, h]
      rw [sumRange_congr g.n (degree g) (fun _ => 0) (by
        intro i _
        rw [degree_zero i])]
      simp [sumRange_zero', edgeCount, h]
  |cons e es ih =>
      rcases e with ⟨u, v⟩
      let g' : Graph := {
        n := g.n
        edges := es
        valid := by intro e' he'; have := g.valid e' (by simp [h, he']); simp [this]
        ordered := by intro e' he'; have := g.ordered e' (by simp [h, he']); simp [this]
      }
      have ih' := ih g' (by rfl)
      have degree_eq : ∀ w, degree g w = degree g' w + if w == u ∨ w == v then 1 else 0 := by
        intro w
        -- 展开 degree 的定义
        simp [degree]
        -- 利用 edges = (u,v) :: es 将 foldl 展开
        rw [h]
        simp [List.foldl_cons]
        have h1:g'.edges=es:=by rfl
        -- 化简条件表达式
        rw [h1]
        rw[←GraphTheory.List.foldl_add_const]
        rw[Nat.zero_add]
        simp [eq_comm]
        · intro b a
          by_cases hcase : a.fst = w ∨ a.snd = w
          · simp [hcase, Nat.add_right_comm]
          · simp [hcase]
      rw [sumRange_congr g.n (degree g) (fun w => degree g' w + if w == u ∨ w == v then 1 else 0) (by intro i _; rw [degree_eq])]
      rw [sumRange_add]
      rw [ih']
      have sum_indicator : sumRange g.n (fun w => if w == u ∨ w == v then 1 else 0) = 2 := by
        have hu : u < g.n := (g.valid (u, v) (by simp [h])).1
        have hv : v < g.n := (g.valid (u, v) (by simp [h])).2
        have u_ne_v : u ≠ v := Nat.ne_of_lt (g.ordered (u, v) (by simp [h]))
        simp [beq_iff_eq]
        exact sumRange_indicator_two hu hv u_ne_v
      rw [sum_indicator]
      simp [edgeCount, h]
      rw [Nat.mul_succ]



Conclusion "."

/- Use these commands to add items to the game's inventory. -/

--NewTactic calc

-- NewDefinition Nat Add Eq
