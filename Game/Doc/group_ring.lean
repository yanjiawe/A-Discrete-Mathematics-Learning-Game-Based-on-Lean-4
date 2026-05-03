namespace group
class Semigroup (α : Type u) where
  mul : α → α → α
  mul_assoc : ∀ a b c : α, mul (mul a b) c = mul a (mul b c)
infix:70 " ∘ " => Semigroup.mul--半群


class Monoid (α : Type u) extends Semigroup α where
  one : α
  one_mul : ∀ a : α, one ∘ a = a
  mul_one : ∀ a : α, a ∘ one = a--幺半群

class Group (α : Type u) extends Monoid α where
  inv : α → α
  mul_left_inv : ∀ a : α, inv a ∘ a = one--群
  mul_right_inv :∀ a : α, a ∘ inv a = one
postfix:90 "⁻¹" => Group.inv


class Abel (α : Type u) extends Group α where
  mul_mul : ∀ a b : α, b ∘ a = a∘b--交换群/阿贝尔群

/- 以下关于幂运算的开发 -/
variable {G : Type u} [Group G] [Abel G']

/-- 自然数次幂（递归定义）： a ^ 0 = 1, a ^ (n+1) = a * (a ^ n) -/
def pow (a : G) : Nat → G
| 0     => Monoid.one (α := G)
| n + 1 => a ∘ (pow a n)
infix:80 " ^' " => pow



#check Eq.symm

theorem pow_1 (a : G) : (a⁻¹)⁻¹ = a := by
calc
  (a⁻¹)⁻¹ = (a⁻¹)⁻¹ ∘ Monoid.one (α := G) := by exact Eq.symm (Monoid.mul_one ((a⁻¹)⁻¹))
  _ = (a⁻¹)⁻¹ ∘ (a⁻¹ ∘ a) := by rw [←Group.mul_left_inv (α := G)]
  _ = ((a⁻¹)⁻¹ ∘ a⁻¹) ∘ a := by rw [←Semigroup.mul_assoc (α := G)]
  _ = Monoid.one (α := G) ∘ a := by rw [Group.mul_left_inv (α := G) (a⁻¹)]
  _ = a := by rw [Monoid.one_mul (α := G) a]




theorem pow_2(a b: G) : (a∘b)⁻¹ = b⁻¹∘a⁻¹:= by
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

@[simp] theorem pow_zero (a : G) : a ^' 0 = Monoid.one (α := G) := rfl
@[simp] theorem pow_succ (a : G) (n : Nat) : a ^' (n + 1) = a ∘ a ^' n := rfl


theorem pow_3 (a : G) : ∀ m n : Nat, (a ^' n) ∘ (a ^' m)=a ^' (n + m):=by
intro m n
induction n generalizing m with
|zero =>
  simp [pow_zero, Monoid.one_mul]
|succ n ih=>
calc
(a ^' (n+1)) ∘ (a ^' m) = (a∘a ^' n) ∘ (a ^' m) := by simp [pow_succ]
_ = a∘((a ^'n) ∘ (a ^' m)) := by rw [Semigroup.mul_assoc]
_ = a ∘ a ^' (n + m) := by rw [ih]
_ = a ^' ((n + m) + 1) := by simp [pow_succ]
_ = a ^' (n + 1 + m) := by have : (n + m) + 1 = (n + 1) + m := by
                                calc (n + m) + 1 = n + (m + 1) := by rw [Nat.add_assoc]
                                     _ = n + (1 + m) := by rw [Nat.add_comm m 1]
                                     _ = (n + 1) + m := by rw [←Nat.add_assoc]
                           rw [this]


#check Nat.add_one_mul
#check Nat.add_comm
#check Nat.mul_comm


theorem pow_4 (a : G) : ∀ m n : Nat, (a ^' n)^'m=(a ^'(n*m)):=by
intro m n
induction m generalizing n with
|zero =>
  simp [pow_zero]
|succ m ih
calc
(a ^' n)^'(m+1)=(a ^'n)∘(a^'n)^'m := by simp [pow_succ]
_=(a ^'n)∘a ^'(n*m):= by rw [ih]
_=a^'(n+n*m):= by rw [pow_3]
_=a^'(n+m*n):= by rw [Nat.mul_comm]
_=a^'(m*n+n):= by rw [Nat.add_comm]
_=a^'((m+1)*n):= by rw [←Nat.add_one_mul]
_=a^'(n*(m+1)):= by rw [Nat.mul_comm]

theorem pow_5 (a b: G') : ∀n : Nat, (a∘b)^'n=(a ^'n)∘(b^'n):=by
intro n
induction n with
|zero =>
  simp [pow_zero,Monoid.one_mul]
| succ n ih
calc
(a∘b)^'(n+1)=(a∘b)∘(a∘b)^'n:= by simp[pow_succ]
_=(a∘b)∘((a ^'n)∘(b^'n)) := by rw[ih]
_=(b∘a)∘((a ^'n)∘(b^'n)) := by rw [←Abel.mul_mul a b]
_=b ∘ (a ∘ ((a ^' n) ∘ (b ^' n))) := by rw [Semigroup.mul_assoc]
_=b ∘ ((a ∘ (a ^' n)) ∘ (b ^' n)) := by rw [Semigroup.mul_assoc]
_=b ∘ ((a ^' (n+1)) ∘ (b ^' n)) := by simp [pow_succ]
_=((a ^' (n+1)) ∘ (b ^' n))∘b :=by rw [←Abel.mul_mul]
_=(a ^' (n+1)) ∘ ((b ^' n)∘b) :=by rw [Semigroup.mul_assoc]
_=(a ^' (n+1)) ∘ (b∘(b ^' n)) :=by rw [Abel.mul_mul b]
_=(a ^' (n+1)) ∘ (b ^' (n+1)) :=by simp [pow_succ]



theorem mul_left_cancel {a x y : G} (h : a ∘ x = a ∘ y) : x = y := by
  calc
    x = Monoid.one ∘ x := by rw [Monoid.one_mul]
    _ = (a⁻¹ ∘ a) ∘ x := by rw [Group.mul_left_inv]
    _ = a⁻¹ ∘ (a ∘ x) := by rw [← Semigroup.mul_assoc]
    _ = a⁻¹ ∘ (a ∘ y) := by rw [h]
    _ = (a⁻¹ ∘ a) ∘ y := by rw [Semigroup.mul_assoc]
    _ = Monoid.one ∘ y := by rw [Group.mul_left_inv]
    _ = y := by rw [Monoid.one_mul]

theorem mul_right_cancel {x y a : G} (h : x ∘ a = y ∘ a) : x = y := by
  calc
    x = x ∘ Monoid.one := by rw [Monoid.mul_one]
    _ = x ∘ (a ∘ a⁻¹) := by rw [Group.mul_right_inv]
    _ = (x ∘ a) ∘ a⁻¹ := by rw [← Semigroup.mul_assoc]
    _ = (y ∘ a) ∘ a⁻¹ := by rw [h]
    _ = y ∘ (a ∘ a⁻¹) := by rw [Semigroup.mul_assoc]
    _ = y ∘ Monoid.one := by rw [Group.mul_right_inv]
    _ = y := by rw [Monoid.mul_one]



class AddAbelgroup (α : Type u) where
  add : α → α → α
  add_assoc : ∀ a b c : α, add (add a b) c = add a (add b c)
  zero : α
  zero_add : ∀ a : α, add zero a = a
  add_zero  : ∀ a : α, add a zero = a
  neg : α → α
  add_left_neg : ∀ a : α, add (neg a) a = zero
  add_right_neg : ∀ a : α, add a (neg a) = zero
  add_comm : ∀ a b : α, add a b = add b a
  sub :α → α → α
  sub_to_add:∀ a b : α, sub a b = add a (neg b)
infixl:65 " +' " => AddAbelgroup.add
prefix:100 " -' " => AddAbelgroup.neg
infixl:65 " -' " => AddAbelgroup.sub


class Ring (α : Type u) extends AddAbelgroup α, Semigroup α where
  zero_mul:∀ a: α, mul zero a =zero
  left_distrib  : ∀ a b c : α, mul a (add b c) = add (mul a b) (mul a c)
  right_distrib : ∀ a b c : α, mul (add a b) c = add (mul a c) (mul b c)


variable {R : Type u} [Ring R]


theorem add_left_cancel {a x y : R} (h : a +' x = a +' y) : x = y := by
  calc
    x = AddAbelgroup.zero +' x := by rw [AddAbelgroup.zero_add]
    _ = (-'a +' a) +' x := by rw [AddAbelgroup.add_left_neg]
    _ = -'a +' (a +' x) := by rw [← AddAbelgroup.add_assoc]
    _ = -'a +' (a +' y) := by rw [h]
    _ = (-'a +' a) +' y := by rw [AddAbelgroup.add_assoc]
    _ = AddAbelgroup.zero +' y := by rw [AddAbelgroup.add_left_neg]
    _ = y := by rw [AddAbelgroup.zero_add]

theorem add_right_cancel {x y a : R} (h : x +' a = y +' a) : x = y := by
  calc
    x = x +' AddAbelgroup.zero := by rw [AddAbelgroup.add_zero]
    _ = x +' (a +' -'a) := by rw [AddAbelgroup.add_right_neg]
    _ = (x +' a) +' -'a := by rw [← AddAbelgroup.add_assoc]
    _ = (y +' a) +' -'a := by rw [h]
    _ = y +' (a +' -'a) := by rw [AddAbelgroup.add_assoc]
    _ = y +' AddAbelgroup.zero := by rw [AddAbelgroup.add_right_neg]
    _ = y := by rw [AddAbelgroup.add_zero]

theorem ring_1 (a : R)
: a ∘ AddAbelgroup.zero = AddAbelgroup.zero := by
have h : (a ∘ AddAbelgroup.zero) +' AddAbelgroup.zero = (a ∘ AddAbelgroup.zero) +' (a ∘ AddAbelgroup.zero) := by
  calc (a ∘ AddAbelgroup.zero) +' AddAbelgroup.zero = a ∘ AddAbelgroup.zero := by rw [AddAbelgroup.add_zero]
        _ = a∘(AddAbelgroup.zero +' AddAbelgroup.zero):= by rw[AddAbelgroup.add_zero]
        _ =a∘AddAbelgroup.zero +' a∘AddAbelgroup.zero:=by rw[Ring.left_distrib]
have eq0 := add_left_cancel (h)
exact eq0.symm

theorem ring_2 (a b : R)
:(-'a)∘b=-'(a∘b):=by
have h:(-'a)∘b+'a∘b=-'(a∘b)+'a∘b:=by
  calc (-'a)∘b+'a∘b=(-'a+'a)∘b:=by rw[Ring.right_distrib]
       _=AddAbelgroup.zero∘b:=by rw[AddAbelgroup.add_left_neg]
       _=AddAbelgroup.zero:=by rw [Ring.zero_mul]
       _=-'(a∘b)+'a∘b:=by rw[←AddAbelgroup.add_left_neg]
have eq0 := add_right_cancel (h)
exact eq0

theorem ring_3 (a b c: R)
:(b-'c)∘a=b∘a-'c∘a:=by
calc (b-'c)∘a=(b+'(-'c))∘a:=by rw [AddAbelgroup.sub_to_add]
_=(b∘a)+'(-'c∘a):=by rw[Ring.right_distrib]
_=(b∘a)+'(-'(c∘a)):=by rw[ring_2]
_=b∘a-'c∘a:=by rw [AddAbelgroup.sub_to_add (b∘a) (c∘a)]
