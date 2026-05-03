namespace Set

def Set (α : Type u) := α → Prop

def mem (x : α) (a : Set α) := a x

infix:50 "∈" => mem

def notin (x : α) (s : Set α) : Prop := ¬ (x ∈ s)
infix:50 " ∉ " => notin


theorem setext {a b : Set α} (h : ∀ x, x ∈ a ↔ x ∈ b) : a = b :=
  funext (fun x => propext (h x))



def empty : Set α := fun x => False

notation (priority := high) "∅" => empty

def E : Set α := fun _ => True
notation "E" => E

def inter (a b : Set α) : Set α :=
  fun x => x ∈ a ∧ x ∈ b

infix:70 " ∩ " => inter

def union (a b : Set α) : Set α := fun x => x ∈ a ∨ x ∈ b
infix:65 " ∪ " => union

def compl (a : Set α) : Set α := fun x => ¬ (a x)
prefix:100 "~" => compl

def subset (a b : Set α) : Prop := ∀ x, x ∈ a → x ∈ b
infix:50 " ⊆ " => subset

def sdiff (a b : Set α) : Set α := fun x => a x ∧ ¬ b x
infixl:70 " - " => sdiff

def prod (a : Set α) (b : Set β) : Set (α × β)
:= fun p => p.1 ∈ a ∧ p.2 ∈ b
infix:80 " ×₁ " => prod



theorem inter_self (a : Set α) : a ∩ a = a :=
  setext fun x => Iff.intro
    (fun ⟨h, _⟩ => h)
    (fun h => ⟨h, h⟩)

theorem inter_self1 (a : Set α) : a ∩ a = a :=by
  apply setext
  intro x
  constructor
  ·intro ⟨ha, _⟩
   exact ha
  ·intro ha
   exact ⟨ha, ha⟩

theorem union_self (a : Set α) : a ∪ a = a :=
  setext fun x => Iff.intro
    (fun h => h.elim id id)
    (fun h => Or.inl h)
--law1

theorem union_assoc (a b c : Set α) : (a ∪ b) ∪ c = a ∪ (b ∪ c) :=
  setext fun x => Iff.intro
    (fun h => by
      match h with
      | Or.inl (Or.inl ha) => exact Or.inl ha
      | Or.inl (Or.inr hb) => exact Or.inr (Or.inl hb)
      | Or.inr hc => exact Or.inr (Or.inr hc))
    (fun h => by
      match h with
      | Or.inl ha => exact Or.inl (Or.inl ha)
      | Or.inr (Or.inl hb) => exact Or.inl (Or.inr hb)
      | Or.inr (Or.inr hc) => exact Or.inr hc)



theorem union_assoc1 (a b c : Set α) : (a ∪ b) ∪ c = a ∪ (b ∪ c) :=by
  apply setext
  intro x
  constructor
  ·intro h
   match h with
      | Or.inl (Or.inl ha) => exact Or.inl ha
      | Or.inl (Or.inr hb) => exact Or.inr (Or.inl hb)
      | Or.inr hc => exact Or.inr (Or.inr hc)
  ·intro h
   match h with
      | Or.inl ha => exact Or.inl (Or.inl ha)
      | Or.inr (Or.inl hb) => exact Or.inl (Or.inr hb)
      | Or.inr (Or.inr hc) => exact Or.inr hc


theorem union_assoc2 (a b c : Set α) : (a ∪ b) ∪ c = a ∪ (b ∪ c) :=by
  apply setext
  intro x
  constructor
  ·intro h
   rcases h with hab | hc
   ·rcases hab with ha | hb
    ·exact Or.inl ha
    ·exact Or.inr (Or.inl hb)
   ·exact Or.inr (Or.inr hc)
  ·intro h
   rcases h with ha | hbc
   ·exact Or.inl (Or.inl ha)
   ·rcases hbc with hb | hc
    ·exact Or.inl (Or.inr hb)
    ·exact Or.inr hc


theorem inter_assoc (a b c : Set α) : (a ∩ b) ∩ c = a ∩ (b ∩ c) :=
  setext fun x => Iff.intro
    (fun ⟨⟨ha, hb⟩, hc⟩ => ⟨ha, ⟨hb, hc⟩⟩)
    (fun ⟨ha, ⟨hb, hc⟩⟩ => ⟨⟨ha, hb⟩, hc⟩)

--law2

theorem inter.comm (a b : Set α) : a ∩ b = b ∩ a :=
  setext fun x => Iff.intro
    (fun ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩)
    (fun ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩)

theorem union.comm (a b : Set α) :a ∪ b = b ∪ a :=
  setext fun x => Iff.intro
    (fun h => h.elim Or.inr Or.inl)
    (fun h => h.elim Or.inr Or.inl)

--law3

theorem union_inter_distrib_left' {α : Type u} (A B C : Set α) :
  A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) :=
  setext fun x => Iff.intro
    (fun h => match h with
      | Or.inl ha => ⟨Or.inl ha, Or.inl ha⟩
      | Or.inr ⟨hb, hc⟩ => ⟨Or.inr hb, Or.inr hc⟩)
    (fun ⟨h1, h2⟩ =>
      match h1, h2 with
      | Or.inl ha, _ => Or.inl ha
      | Or.inr hb, Or.inr hc => Or.inr ⟨hb, hc⟩
      | Or.inr hb, Or.inl ha => Or.inl ha)


theorem inter_union_distrib_left' {α : Type u} (A B C : Set α) :
  A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) :=
  setext fun x => Iff.intro
    (fun h => match h with
      | ⟨ha, Or.inl hb⟩ => Or.inl ⟨ha, hb⟩
      | ⟨ha, Or.inr hc⟩ => Or.inr ⟨ha, hc⟩)
    (fun h => match h with
      | Or.inl ⟨ha, hb⟩ => ⟨ha, Or.inl hb⟩
      | Or.inr ⟨ha, hc⟩ => ⟨ha, Or.inr hc⟩)


theorem inter_union_distrib_left'1 {α : Type u} (A B C : Set α) :
  A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) :=
  setext fun x => Iff.intro
    (fun h => match h with
      | ⟨ha, Or.inl hb⟩ => Or.inl ⟨ha, hb⟩
      | ⟨ha, Or.inr hc⟩ => Or.inr ⟨ha, hc⟩)
    (fun h => match h with
      | Or.inl ⟨ha, hb⟩ => ⟨ha, Or.inl hb⟩
      | Or.inr ⟨ha, hc⟩ => ⟨ha, Or.inr hc⟩)



theorem inter_union_distrib_left'12 {α : Type u} (A B C : Set α) :
  A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) :=by
  apply setext
  intro x
  constructor
  ·intro h
   rcases h with ⟨ha,hbc⟩
   rcases hbc with hb | hc
   ·exact Or.inl ⟨ha, hb⟩
   ·exact Or.inr ⟨ha, hc⟩
  ·intro h
   rcases h with hab | hac
   ·rcases hab with ⟨ha,hb⟩
    exact ⟨ha, Or.inl hb⟩
   ·rcases hac with ⟨ha,hc⟩
    exact ⟨ha, Or.inr hc⟩


--law4

theorem union_empty (a : Set α) : a ∪ ∅ = a :=
  setext fun x => Iff.intro
    (fun h => h.elim id (fun hfalse => False.elim hfalse))
    (fun ha => Or.inl ha)


theorem union_empty1 (a : Set α) : a ∪ ∅ = a :=by
  apply setext
  intro x
  constructor
  ·intro h
   rcases h with ha | hfalse
   ·exact ha
   ·exact False.elim hfalse
  ·intro ha
   exact Or.inl ha


theorem empty_union (a : Set α) : ∅ ∪ a = a :=
  setext fun x => Iff.intro
    (fun h => h.elim (fun hfalse => False.elim hfalse) id)
    (fun ha => Or.inr ha)

theorem inter_univ (a : Set α) : a ∩ E = a :=
  setext fun x => Iff.intro
    (fun ⟨ha, _⟩ => ha)
    (fun ha => ⟨ha, trivial⟩)

--law5

theorem inter_empty (a : Set α) : a ∩ ∅ = ∅ :=
  setext fun x => Iff.intro
    (fun ⟨_, h⟩ => h)
    (fun h => False.elim h)

theorem empty_inter (a : Set α) : ∅ ∩ a = ∅ :=
  setext fun x => Iff.intro
    (fun ⟨h, _⟩ => h)
    (fun h => False.elim h)

theorem union_univ (a : Set α) : a ∪ E = E :=
  setext fun x => Iff.intro
    (fun _ => trivial)
    (fun _ => Or.inr trivial)




theorem union_univ1 (a : Set α) : a ∪ E = E :=by
  apply setext
  intro x
  constructor
  ·intro h
   rcases h with ha |hea
   ·trivial
   ·exact hea
  ·intro h
   exact Or.inr h

--law6

theorem law7 (a : Set α) : a ∪ ~a = E :=by
  apply setext
  intro x
  constructor
  · intro _
    trivial
  · intro _
    exact Classical.em (a x)
--law7


theorem law8 {α : Type u} (a : Set α) : a ∩ ~a = ∅ := by
  apply setext
  intro x
  constructor
  · intro ⟨ha, hna⟩
    exact hna ha
  · intro h
    exact False.elim h
--law8


theorem union_absorb {α : Type u} (A B : Set α) : A ∪ (A ∩ B) = A := by
  apply setext
  intro x
  constructor
  · intro h
    match h with
    | Or.inl ha => exact ha
    | Or.inr ⟨ha, _⟩ => exact ha
  · intro ha
    left; exact ha

theorem union_absorb1 {α : Type u} (A B : Set α) : A ∪ (A ∩ B) = A := by
  apply setext
  intro x
  constructor
  · intro h
    rcases h with ha | hab
    ·exact ha
    ·rcases hab with ⟨ha,hb⟩
     exact ha
  · intro ha
    left; exact ha


/-- 吸收律：交吸收律 A ∩ (A ∪ B) = A -/
theorem inter_absorb {α : Type u} (A B : Set α) : A ∩ (A ∪ B) = A := by
  apply setext
  intro x
  constructor
  · intro ⟨ha, _⟩
    -- 若 x ∈ A ∩ (A ∪ B)，则 x ∈ A
    exact ha
  · intro ha
    -- 若 x ∈ A，则 x ∈ A ∩ (A ∪ B)（右边取左分支）
    constructor
    · exact ha
    · left; exact ha

--law8


theorem law9_1 (a b c : Set α) : a-(b∪c) = (a-b)∩(a-c) :=by
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



theorem law9_12 (a b c : Set α) : a-(b∪c) = (a-b)∩(a-c) :=by
  apply setext
  intro x
  constructor
  · intro h
    rcases h with ⟨ha,hnot⟩
    constructor
    ·constructor
     · exact ha
     · intro hb
       apply hnot
       left
       exact hb
    ·constructor
     ·exact ha
     ·intro hc
      apply hnot
      right
      exact hc
  · intro h
    rcases h with ⟨⟨ha, hnb⟩, ⟨_, hnc⟩⟩
    constructor
    · exact ha
    · intro hbc
      rcases hbc with (hb | hc)
      · exact hnb hb
      · exact hnc hc

theorem law9_2 (a b c : Set α) : a - (b ∩ c) = (a - b) ∪ (a - c) := by
  apply setext
  intro x
  constructor
  · intro h
    have hx := h.1
    have hxbc := h.2
    by_cases hb : x ∈ b
    · refine Or.inr ⟨hx, ?_⟩
      intro hc
      exact hxbc ⟨hb, hc⟩
    · refine Or.inl ⟨hx, hb⟩
  · intro h
    rcases h with (⟨hx, hnb⟩ | ⟨hx, hnc⟩)
    · exact ⟨hx, fun hbc => hnb hbc.1⟩
    · exact ⟨hx, fun hbc => hnc hbc.2⟩


theorem law9_3{α : Type u}:(~ (∅ : Set α)) = E :=by
  apply setext
  intro x
  constructor
  · intro h
    trivial
  · intro _
    intro h
    exact h

theorem law9_4 {α : Type u} : ~ (E : Set α) = ∅ := by
  apply setext
  intro x
  constructor
  · intro h
    exact h trivial
  · intro h
    exact False.elim h

theorem compl_union (a b : Set α) : ~(a ∪ b) = ~a ∩ ~b :=
  setext fun x => Iff.intro
    (fun h => ⟨fun ha => h (Or.inl ha), fun hb => h (Or.inr hb)⟩)
    (fun ⟨hna, hnb⟩ => fun h => match h with
      | Or.inl ha => hna ha
      | Or.inr hb => hnb hb)


theorem compl_inter (a b : Set α) : ~(a ∩ b) = ~a ∪ ~b :=
  setext fun x => Iff.intro
    (fun h => by
      by_cases ha : x ∈ a
      · right; intro hb; exact h ⟨ha, hb⟩
      · left; exact ha)
    (fun h => fun ⟨ha, hb⟩ => h.elim (fun ha' => ha' ha) (fun hb' => hb' hb))


#check Ne.elim

theorem compl_inter1 (a b : Set α) : ~(a ∩ b) = ~a ∪ ~b :=by
 apply setext
 intro x
 constructor
 ·intro h
  by_cases ha : x ∈ a
  · right; intro hb; exact h ⟨ha, hb⟩
  · left; exact ha
 ·intro h
  rcases h with hna|hnb
  ·intro hab
   rcases hab with ⟨ha,hb⟩
   exact hna ha
  ·intro hab
   rcases hab with ⟨ha,hb⟩
   exact hnb hb



--law9

theorem compl_compl {α : Type u} (a : Set α) : ~(~a) = a := by
  -- 用集合外延把集合等式转为逐点命题
  apply setext
  intro x
  -- 目标： ¬¬(a x) ↔ a x
  constructor
  · -- 左向右： ¬¬(a x) → a x，需要经典分析
    intro hnn
    by_cases h : a x
    · exact h
    · exfalso
      -- h : ¬ a x, hnn : ¬¬ a x, 由 hnn h 得到矛盾
      exact hnn h
  · -- 右向左： a x → ¬¬(a x) （构造性成立）
    intro ha hna
    exact hna ha

--law 10

theorem mem_prod_iff {a : Set α} {b : Set β} {x : α} {y : β} :
  (x, y) ∈ (a ×₁ b) ↔ x ∈ a ∧ y ∈ b := Iff.rfl

theorem prod_empty_left (s : Set β) :
  Set.prod (∅ : Set α) s = ∅ := by
  apply setext; intro p
  apply Iff.intro
  · intro h; cases h with | intro h1 h2 => cases h1
  · intro h; exact False.elim h


theorem prod_empty_left1 (s : Set β) :
  (∅ : Set α) ×₁ s = ∅ := by
  apply setext
  intro p
  constructor
  · intro h
    rcases h with ⟨h1,h2⟩
    exact h1
  · intro h
    exact False.elim h

theorem prod_empty_right (s : Set α) :
  Set.prod s (∅ : Set β ) = (∅ : Set (α × β)) := by
  apply setext; intro p
  apply Iff.intro
  · intro h; cases h with | intro ha hb => cases hb
  · intro h; exact False.elim h


theorem prod_union_left (a b : Set α) (c : Set β) :
  (a ∪ b) ×₁ c = (a ×₁ c) ∪ (b ×₁ c) := by
  apply setext; intro p
  apply Iff.intro
  · intro h; cases h with | intro h1 h2 =>
      cases h1 with
      | inl ha => apply Or.inl; apply And.intro; exact ha; exact h2
      | inr hb => apply Or.inr; apply And.intro; exact hb; exact h2
  · intro h; cases h with
    | inl hab => cases hab with | intro ha hc => apply And.intro; exact Or.inl ha; exact hc
    | inr hbc => cases hbc with | intro hb hc => apply And.intro; exact Or.inr hb; exact hc

theorem prod_union_right(a : Set α) (b c : Set β) :
  Set.prod a  (b ∪ c) = (a ×₁ b) ∪ (a ×₁ c) := by
  apply setext; intro p
  apply Iff.intro
  · intro h; cases h with | intro h1 h2 =>
      cases h2 with
      | inl hb => apply Or.inl; apply And.intro; exact h1; exact hb
      | inr hc => apply Or.inr; apply And.intro; exact h1; exact hc
  · intro h; cases h with
    | inl hab => cases hab with | intro ha hb => apply And.intro; exact ha; exact Or.inl hb
    | inr hac => cases hac with | intro ha hc => apply And.intro; exact ha; exact Or.inr hc

theorem prod_inter_left (a b : Set α) (c : Set β) :
  Set.prod (a ∩ b)  c = (a ×₁ c) ∩ (b ×₁ c) := by
  apply setext; intro p
  apply Iff.intro
  · intro h; cases h with | intro hab hc =>
      apply And.intro
      · apply And.intro; exact hab.left; exact hc
      · apply And.intro; exact hab.right; exact hc
  · intro h; cases h with
    | intro hac hbc =>
      cases hac with | intro ha hc
      cases hbc with | intro hb _
      apply And.intro (And.intro ha hb) hc

theorem prod_inter_right {α : Type u} {β : Type v} (a : Set α) (b c : Set β) :
  Set.prod a  (b ∩ c) = (a ×₁ b) ∩ (a ×₁ c) := by
  apply setext; intro p
  apply Iff.intro
  · intro h; cases h with | intro ha hbc =>
      apply And.intro
      · apply And.intro; exact ha; exact hbc.left
      · apply And.intro; exact ha; exact hbc.right
  · intro h; cases h with
    | intro hab hac =>
      cases hab with | intro ha hb
      cases hac with | intro _ hc
      apply And.intro; exact ha; exact And.intro hb hc

theorem prod_subset_prod {α : Type u} {β : Type v}
  {a c : Set α} {b d : Set β}
  (ha : a ⊆ c) (hb : b ⊆ d) : Set.prod a b ⊆ Set.prod c d := by
  intro p; intro h
  cases h with | intro h1 h2 =>
    apply And.intro (ha p.1 h1) (hb p.2 h2)



theorem sadsanfja(α : Type u)(β: Type u) (a b : Set α) (c : Set β) :
  (a ∪ b) ×₁ c = (a ×₁ c) ∪ (b ×₁ c) := by
  apply setext
  intro p
  constructor
  · intro h
    rcases h with ⟨h1ab,h2c⟩
    rcases h1ab with h1a | h1b
    ·exact Or.inl ⟨h1a,h2c⟩
    ·exact Or.inr ⟨h1b,h2c⟩
  · intro h
    rcases h with hac| hbc
    ·rcases hac with ⟨h1a,h2c⟩
     exact ⟨(Or.inl h1a),h2c⟩
    ·rcases hbc with ⟨h1b,h2c⟩
     exact ⟨(Or.inr h1b),h2c⟩
