import Game.Metadata

World "Algebra_Structure"
Level 2

open group

Title "pow2"

Introduction "在群G中，对于G中元素a,b，他们运算（a∘b）⁻¹等于b⁻¹∘a⁻¹"

--Statement (p q : Prop) (h:p∧q):q∧p:=by
  --exact And.intro (And.right h) (And.left h)
universe u

Statement {G : Type u} [Group G](a b: G) : (a∘b)⁻¹ = b⁻¹∘a⁻¹:= by
calc
  (a∘b)⁻¹=(a∘b)⁻¹∘Monoid.one (α:=G) := by exact Eq.symm (Monoid.mul_one (α := G) ((a∘b)⁻¹))
  _ =(a∘b)⁻¹∘(a∘(a⁻¹)):= by rw [←Group.mul_right_inv (α := G)]
  _ =(a∘b)⁻¹∘((a∘(Monoid.one (α:=G)))∘(a⁻¹)) := by apply congrArg (fun x => (a∘b)⁻¹ ∘ (x ∘ (a⁻¹)))
                                                   exact Eq.symm (Monoid.mul_one (α := G) a)
  _ =(a∘b)⁻¹∘((a∘(b∘b⁻¹))∘(a⁻¹)):=by rw [←Group.mul_right_inv (α := G)]
  _ =(a∘b)⁻¹∘(((a∘b)∘b⁻¹)∘(a⁻¹)):= by apply congrArg (fun x => (a∘b)⁻¹ ∘ (x ∘ (a⁻¹)))
                                      rw [←Semigroup.mul_assoc (α := G)]
  _ =(a∘b)⁻¹∘((a∘b)∘(b⁻¹∘(a⁻¹))):= by apply congrArg (fun x => (a∘b)⁻¹ ∘ x )
                                      rw [←Semigroup.mul_assoc (α := G)]
  _ =((a∘b)⁻¹∘(a∘b))∘(b⁻¹∘(a⁻¹)):= by rw [←Semigroup.mul_assoc (α := G)]
  _ =Monoid.one (α := G) ∘ (b⁻¹∘(a⁻¹)) := by rw [Group.mul_left_inv (α := G) (a∘b)]
  _ =b⁻¹∘a⁻¹ := by rw [Monoid.one_mul (α := G) (b⁻¹∘a⁻¹)]



Conclusion "."

/- Use these commands to add items to the game's inventory. -/

--NewTactic calc
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
