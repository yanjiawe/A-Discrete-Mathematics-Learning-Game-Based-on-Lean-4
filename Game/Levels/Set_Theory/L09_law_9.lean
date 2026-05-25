import Game.Metadata

World "Set_Theory"
Level 9

open Set

Title "德摩根律"

Introduction "德摩根律有六种，分别是补对交和并的分配律，空集和全集的转换，
以及交和并的补，这里我们先证明分配律"

--Statement (p q : Prop) (h:p∧q):q∧p:=by
  --exact And.intro (And.right h) (And.left h)
universe u

Statement (α : Type u)(a b c : Set α) : a-(b∪c) = (a-b)∩(a-c) :=by
  apply setext
  intro x
  constructor
  · intro h
    have ha : x ∈ a := h.left
    have hnot : x ∉ (b ∪ c) := h.right
    have hnb : x ∉ b := fun hb => hnot (Or.inl hb)
    have hnc : x ∉ c := fun hc => hnot (Or.inr hc)
    exact ⟨⟨ha, hnb⟩, ⟨ha, hnc⟩⟩
  · intro ⟨⟨ha, hnb⟩, ⟨_, hnc⟩⟩
    exact ⟨ha, fun hbc => match hbc with | Or.inl hb => hnb hb | Or.inr hc => hnc hc⟩


Conclusion "."

/- Use these commands to add items to the game's inventory. -/

--NewTactic exfalso apply
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
