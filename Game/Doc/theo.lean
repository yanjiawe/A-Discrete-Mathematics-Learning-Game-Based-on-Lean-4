import GameServer.Commands
universe u

namespace theo

def double_neg_law{a:Prop}:a ↔ ¬¬a := by
  constructor
  · intro ha hna
    exact hna ha
  · intro hnn
    by_cases h : a
    · exact h
    · exfalso
      exact hnn h

/--
# 双重否定律
### `double_neg_law : a ↔ ¬¬a`

任意命题`a`与它的双重否定命题`¬¬a`等价，这就是双重否定律
-/
TheoremDoc theo.double_neg_law as "双重否定律" in "等值式模式"


def idempotent_law_or{p q:Prop}
:p↔(p∨p):=by
 constructor
 · intro h
   exact Or.inr h
 · intro h
   rcases h with h1 | h2
   · exact h1
   · exact h2

/--
# 幂等律（析取）
### `idempotent_law_or : p↔(p∨p)`

任意命题`p`可以转换成`p∨p`，也可以转换回去，这就是幂等律（析取）
-/
TheoremDoc theo.idempotent_law_or as "幂等律（析取）" in "等值式模式"

def idempotent_law_and{p q:Prop}
:p↔(p∧p):=by
 constructor
 · intro h
   exact ⟨h,h⟩
 · intro h
   rcases h with ⟨h1,h2⟩
   · exact h1

/--
# 幂等律（合取）
### `idempotent_law_and : p↔(p∨p)`

任意命题`p`可以转换成`p∧p`，也可以转换回去，这就是幂等律（合取）
-/
TheoremDoc theo.idempotent_law_and as "幂等律（合取）" in "等值式模式"

def communtative_and{p q:Prop}
: p ∧ q ↔ q ∧ p:=by
constructor
· intro h
  rcases h with ⟨hp, hq⟩
  exact ⟨hq, hp⟩
· intro h
  rcases h with ⟨hq, hp⟩
  exact ⟨hp, hq⟩

/--
# 交换律（合取）
### `communtative_and :  p ∧ q ↔ q ∧ p`

形如`p ∧ q`和`q ∧ p`等价可以转换，这就是交换律
-/
TheoremDoc theo.communtative_and as "交换律（合取）" in "等值式模式"


def communtative_or{p q:Prop}
: p ∨ q ↔ q ∨ p:=by
constructor
· intro h
  rcases h with hp | hq
  · exact Or.inr hp
  · exact Or.inl hq
· intro h
  rcases h with hp | hq
  · exact Or.inr hp
  · exact Or.inl hq

/--
# 交换律（析取）
### `communtative_and :  p ∨ q ↔ q ∨ p`

形如`p ∨ q`和`q ∨ p`等价可以转换，这就是交换律
-/
TheoremDoc theo.communtative_or as "交换律（析取）" in "等值式模式"



def associative_and{a b c:Prop}
:((a∧b)∧c)↔(a∧(b∧c)):=by
 constructor
 · intro h
   rcases h with ⟨h1,h2⟩
   rcases h1 with ⟨ha,hb⟩
   · exact ⟨ha,⟨hb,h2⟩⟩
 · intro h
   rcases h with ⟨h1,h2⟩
   rcases h2 with ⟨hb,hc⟩
   · exact ⟨ ⟨h1,hb⟩ ,hc⟩

/--
# 结合律（合取）
### `associative_and : ((a∧b)∧c)↔((a∧b)∧c)`

形如`(a∧b)∧c`和`(a∧b)∧c`等价可以转换，这就是结合律
-/
TheoremDoc theo.associative_and as "结合律（合取）" in "等值式模式"


def associative_or{a b c:Prop}
:((a∨b)∨c)↔(a∨(b∨c)):= by
 constructor
 · intro h
   rcases h with h1 | hc
   · rcases h1 with ha | hb
     · exact Or.inl ha
     · exact Or.inr (Or.inl hb)
   · exact Or.inr (Or.inr hc)
 · intro h
   rcases h with ha | h2
   · exact Or.inl (Or.inl ha)
   · rcases h2 with hb | hc
     · exact Or.inl (Or.inr hb)
     · exact Or.inr hc

/--
# 结合律（析取）
### `associative_or : ((a∨b)∨c)↔(a∨(b∨c))`

形如`(a∨b)∨c`和`a∨(b∨c)`等价可以转换，这就是结合律
-/
TheoremDoc theo.associative_or as "结合律（析取）" in "等值式模式"


def distribute_law1{a b c:Prop}
:(a∨(b∧c))↔((a∨b)∧(a∨c)):= by
constructor
· intro h
  rcases h with ha | h2
  · exact ⟨(Or.inl ha),(Or.inl ha)⟩
  · rcases h2 with ⟨hb,hc⟩
    · exact ⟨(Or.inr hb),(Or.inr hc)⟩
· intro h
  rcases h with ⟨hab,hac⟩
  · rcases hab with ha | hb
    ·exact Or.inl ha
    ·rcases hac with ha2 | hc
     · exact Or.inl ha2
     · exact Or.inr ⟨hb,hc⟩

/--
# 分配律1
### `distribute_law1 :  (a∨(b∧c))↔((a∨b)∧(a∨c))`

析取对合取存在分配律，即`(a∨(b∧c))`和`((a∨b)∧(a∨c))`可以互相转换
-/
TheoremDoc theo.communtative_or as "分配律1" in "等值式模式"


def distribute_law2{a b c:Prop}
:(a∧(b∨c))↔((a∧b)∨(a∧c)):= by
constructor
· intro h
  rcases h with  ⟨ha,hbc⟩
  · rcases hbc with hb | hc
    · exact Or.inl ⟨ha,hb⟩
    · exact Or.inr ⟨ha,hc⟩
· intro h
  rcases h with hab | hac
  · rcases hab with ⟨ha,hb⟩
    · exact ⟨ha,(Or.inl hb)⟩
  · rcases hac with ⟨ha,hc⟩
    · exact⟨ha,(Or.inr hc)⟩

/--
# 分配律2
### `distribute_law2 :  (a∧(b∨c))↔((a∧b)∨(a∧c))`

合取对析取存在分配律，即`(a∧(b∨c))`和`((a∧b)∨(a∧c))`可以互相转换
-/
TheoremDoc theo.communtative_or as "分配律2" in "等值式模式"

def De_Morgan_laws{a b:Prop} : ¬(a ∨ b) ↔ ¬a ∧ ¬b := by
  constructor
  · intro h
    constructor
    · intro ha
      exact h (Or.inl ha)
    · intro hb
      exact h (Or.inr hb)
  · intro ⟨hna, hnb⟩ h
    rcases h with (ha | hb)
    · exact hna ha
    · exact hnb hb

/--
# 德摩根律
### `De_Morgan_laws:¬(a ∨ b) ↔ ¬a ∧ ¬b`

应用德摩根律可以将否分配到括号中或者将否提取出来。

-/
TheoremDoc theo.De_Morgan_laws as "德摩根律" in "等值式模式"


def De_Morgan_laws2 {a b : Prop} : ¬(a ∧ b) ↔ ¬a ∨ ¬b := by
  constructor
  · intro h
    by_cases ha : a
    · by_cases hb : b
      · exfalso
        exact h ⟨ha, hb⟩
      · exact Or.inr hb
    · exact Or.inl ha
  · intro h h_ab
    rcases h with (hna | hnb)
    · exact hna h_ab.left
    · exact hnb h_ab.right

/--
# 德摩根律2
### `De_Morgan_laws2:¬(a ∧ b) ↔ ¬a ∨ ¬b`

应用德摩根律可以将否分配到括号中或者将否提取出来。

-/
TheoremDoc theo.De_Morgan_laws2 as "德摩根律2" in "等值式模式"


def absorb_law1{a b:Prop}:(a∨(a∧b))↔a:=by
constructor
·intro h
 rcases h with ha | hab
 ·exact ha
 ·rcases hab with⟨ha1,hb⟩
  ·exact ha1
·intro h
 ·exact Or.inl h

/--
# 吸收律1
### `absorb_law1:(a∨(a∧b))↔a`

吸收律，可以在`(a∨(a∧b))`和`a`之间转换。

-/
TheoremDoc theo.absorb_law1 as "吸收律1" in "等值式模式"


def absorb_law2{a b:Prop}:(a∧(a∨b))↔a:=by
constructor
·intro h
 rcases h with ⟨ha,hab⟩
 ·exact ha
·intro h
 ·exact ⟨h,(Or.inl h)⟩

/--
# 吸收律2
### `absorb_law2:(a∧(a∨b))↔a`

吸收律，可以在`(a∧(a∨b))`和`a`之间转换。

-/
TheoremDoc theo.absorb_law1 as "吸收律2" in "等值式模式"


def zero_law1{a b:Prop}: a ∨ True ↔ True := by
  constructor
  · intro h
    rcases h with ha | ht
    · exact True.intro
    · exact ht
  · intro h
    exact Or.inr True.intro

/--
# 零律1
### `zero_law1:a ∨ True ↔ True`

零律，可以在`a ∨ True`和`True`之间转换。

-/
TheoremDoc theo.zero_law1 as "零律1" in "等值式模式"



def zero_law2{a b:Prop}: a ∧  False ↔ False := by
  constructor
  · intro h
    rcases h with ⟨ha,hf⟩
    · exact hf
  · intro h
    exact ⟨(False.elim h),h⟩

/--
# 零律2
### `zero_law2:a ∨ True ↔ True`

零律，可以在` a ∧  False`和`False`之间转换。

-/
TheoremDoc theo.zero_law2 as "零律2" in "等值式模式"




def identity_law1{a b:Prop}:(a∨False)↔a:=by
constructor
· intro h
  rcases h with ha | hf
  · exact ha
  · exact False.elim hf
· intro h
  exact Or.inl h

/--
# 同一律1
### `identity_law1:(a∨False)↔a`

同一律1，可以在` a `和`a∨False`之间转换。

-/
TheoremDoc theo.identity_law1 as "同一律1" in "等值式模式"


def identity_law2{a b:Prop}:(a∧True)↔a:=by
constructor
· intro h
  rcases h with ⟨ha,hf⟩
  · exact ha
· intro h
  exact ⟨h,True.intro⟩

/--
# 同一律2
### `identity_law2:(a∧True)↔a`

同一律2，可以在` a `和`a∧True`之间转换。

-/
TheoremDoc theo.identity_law2 as "同一律2" in "等值式模式"


def lem{p:Prop}: p ∨ ¬p ↔ True := by
   constructor
   · intro _; trivial
   · intro _; exact Classical.em p

/--
# 排中律
### `lem:p ∨ ¬p ↔ True`

排中律，可以在`True `和`p ∨ ¬p`之间转换,`p ∨ ¬p`包含了所有，所以与1等价。

-/
TheoremDoc theo.lem as "排中律" in "等值式模式"

def no_contradiction{p:Prop}:p∧¬p↔False:=by
constructor
· intro ⟨hp, hnp⟩
  exact hnp hp
· intro f
  exact False.elim f

/--
# 矛盾律
### `lem:p∧¬p↔False`

矛盾律，即一个命题和它的否命题的合取是假，反之假也可以推出任意命题和它否命题的合取。

-/
TheoremDoc theo.lem as "矛盾律" in "等值式模式"



def Imp_eq_law {a b : Prop} : (a → b) ↔ (¬a ∨ b) := by
  constructor
  · intro h
    by_cases ha : a
    · exact Or.inr (h ha)
    · exact Or.inl ha
  · intro h
    intro ha
    rcases h with (hna | hb)
    · exact False.elim (hna ha)
    · exact hb

/--
# 蕴含等值式
### `Imp_eq_law:(a → b) ↔ (¬a ∨ b)`

`(a → b)`和`(¬a ∨ b)`可以转换，就是蕴含等值式。

-/
TheoremDoc theo.Imp_eq_law as "蕴含等值式" in "等值式模式"



def eq{p q : Prop} :(p↔q)↔((p→q)∧(q→p)):=by
 constructor
 ·intro h
  exact ⟨h.1,h.2⟩
 ·intro ⟨hpq, hqp⟩
  exact Iff.intro hpq hqp

/--
# 等价等值式
### `eq:(p↔q)↔((p→q)∧(q→p))`

`(q→p)`和`(p→q)∧(q→p)`可以转换，就是等价等值式。

-/
TheoremDoc theo.eq as "等价等值式" in "等值式模式"



def contraposition_iff {a b : Prop} : (a → b) ↔ (¬b → ¬a) := by
  constructor
  · intro h
    intro hnb ha
    exact hnb (h ha)
  · intro h
    intro ha
    by_cases hb : b
    · exact hb
    · exfalso
      exact (h hb) ha

/--
# 假言易位
### `contraposition_iff:(a → b) ↔ (¬b → ¬a)`

`(a → b)`和`(¬b → ¬a)`可以转换，就是假言易位。

-/
TheoremDoc theo.contraposition_iff as "假言易位" in "等值式模式"



def eq_not {a b : Prop} : (a ↔ b) ↔ (¬a ↔ ¬b) := by
  constructor
  · intro h
    constructor
    · intro na hb
      exact na (h.2 hb)
    · intro nb ha
      exact nb (h.1 ha)
  · intro k
    constructor
    · intro ha
      by_cases hb : b
      · exact hb
      · exfalso
        exact (k.2 hb) ha
    · intro hb
      by_cases ha : a
      · exact ha
      · exfalso
        exact (k.1 ha) hb


/--
# 等价否定等值式
### `eq_not:(a ↔ b) ↔ (¬a ↔ ¬b)`

`(a ↔ b)`和`(¬a ↔ ¬b)`可以转换，就是等价否定等值式。

-/
TheoremDoc theo.eq_not as "等价否定等值式" in "等值式模式"


def pro_con_law{a b : Prop}: ((a → b) ∧ (a → ¬b)) ↔ ¬a := by
  constructor
  · intro ⟨hab, hanb⟩
    intro ha
    exact (hanb ha) (hab ha)
  · intro h
    constructor
    · intro ha
      exact False.elim (h ha)
    · intro ha hb
      exact False.elim (h ha)

/--
# 归谬论
### `pro_con_law : ((a → b) ∧ (a → ¬b)) ↔ ¬a`

若`(a → b) ∧ (a → ¬b)`成立，易知`a`为假，则`¬a`成立，反之亦然，这就是归谬论。
-/
TheoremDoc theo.pro_con_law as "归谬论" in "等值式模式"




def law_add {a b : Prop}(h:a):a ∨ b := Or.inl h

/--
# 附加律
### `law_add : a→a∨b`

已知一个命题`a`,利用附加律可以制造出和任意其它命题的析取。
-/
TheoremDoc theo.law_add as "附加律" in "推理规则"


def sim_law{a b:Prop}(h:a∧b):a:= And.left h

/--
# 化简律
### `sim_law : a∧b→a`

已知一个命题`a∧b`成立,利用化简律可以提取出a。
-/
TheoremDoc theo.sim_law as "化简律" in "推理规则"


def modus_ponens{a b:Prop}(h:(a→b)∧a):b:=(And.left h) (And.right h)

/--
# 假言推理
### `modus_ponens : ((a→b)∧a)→b`

已知两个命题`a→b`和`a`成立,利用假言推理可以得出b。
-/
TheoremDoc theo.modus_ponens as "假言推理" in "推理规则"

def modus_tollens{a b:Prop}(h:(a→b)∧¬b):¬a:=by
intro h1
exact  (And.right h) ((And.left h) h1)

/--
# 拒取式
### `modus_tollens : ((a→b)∧¬b)→¬a`

已知两个命题`a→b`和`¬b`成立,利用拒取式可以得出¬a。
-/
TheoremDoc theo.modus_tollens as "拒取式" in "推理规则"


--def disjunctive_syllogism {a b : Prop} (h : (a ∨ b) ∧ ¬b) : a :=
--match h with
--| ⟨Or.inl ha, _⟩ => ha
--| ⟨Or.inr hb, hnb⟩ => False.elim (hnb hb)

def disjunctive_syllogism{a b:Prop}(h:(a∨b)∧¬b):a:=by
rcases And.left h with ha | hb
·exact ha
·exact False.elim ((And.right h) hb)

/--
# 析取三段论
### `disjunctive_syllogism : ((a∨b)∧¬b)→a`

已知两个命题`a∨b`和`¬b`成立,`a∨b`成立代表其中一个为真，而`¬b`成立易得出`a`为真，
利用析取三段论可以得出¬a。
-/
TheoremDoc theo.disjunctive_syllogism as "析取三段论" in "推理规则"



def hypothetical_syllogism{a b c:Prop}(h:(a→b)∧(b→c)):a→c:= by
intro ha
exact (And.right h) ((And.left h) ha)

/--
# 假言三段论
### `hypothetical_syllogism : ((a∨b)∧¬b)→a`

已知两个命题`a→b`和`b→c`成立,利用假言三段论可以得出`a→c`。
-/
TheoremDoc theo.hypothetical_syllogism as "假言三段论" in "推理规则"


def trans_eq(a b c:Prop)(h:(a ↔ b) ∧ (b ↔ c)):a ↔ c:=by
  rcases h with ⟨hab, hbc⟩
  constructor
  · intro ha
    exact hbc.1 (hab.1 ha)
  · intro hc
    exact hab.2 (hbc.2 hc)

/--
# 等价三段论
### `trans_eq : ((a ↔ b) ∧ (b ↔ c))→(a ↔ c)`

已知两个命题`a ↔ b`和`b ↔ c`成立,则`a ↔ c`也成立，这就是等价三段论。
-/
TheoremDoc theo.trans_eq as "等价三段论" in "推理规则"


def constructive_dilemma {a b c d : Prop} (h : (a → b) ∧ (c → d) ∧ (a ∨ c)) : b ∨ d := by
  rcases h with ⟨hab, hcd, hac⟩
  rcases hac with ha | hc
  · exact Or.inl (hab ha)
  · exact Or.inr (hcd hc)

/--
# 构造性二难
### `constructive_dilemma : ((a→b)∧(c→d)∧(a∨c))→(b∨d)`

已知命题`a→b`和`c→d`成立,同时`a∨c`成立，则`b∨d`成立，这就是构造性二难。
-/
TheoremDoc theo.constructive_dilemma as "构造性二难" in "推理规则"


def constructive_dilemma_special{a b:Prop}(h:(a → b) ∧ (¬a → b)):b:= by
by_cases ha:a
·exact And.left h ha
·exact And.right h ha

/--
# 构造性二难（特殊形式）
### `constructive_dilemma_special :  ((a → b) ∧ (¬a → b)) → b`

已知命题`a→b`和`¬a → b`成立,则`b`成立，这就是构造性二难。
-/
TheoremDoc theo.constructive_dilemma_special as "构造性二难（特殊形式）" in "推理规则"


def destructive_dilemma{a b c d:Prop}(h:(a→b)∧(c→d)∧(¬b∨¬d)):¬a∨¬c:= by
rcases h with ⟨hab, hcd, hnbnd⟩
rcases hnbnd with (hnb | hnd)
· left
  intro ha
  exact hnb (hab ha)
· right
  intro hc
  exact hnd (hcd hc)

/--
# 破坏性二难
### `destructive_dilemma :  ((a→b)∧(c→d)∧(¬b∨¬d))→(¬a∨¬c)`

已知命题`a→b`和`c→d`成立,同时`¬b∨¬d`成立，则`¬a∨¬c`成立，，这就是破坏性二难。
-/
TheoremDoc theo.destructive_dilemma as "破坏性二难" in "推理规则"


def law_1 {X : Type u} {A : X → Prop}
: (¬ ∀ x, A x) ↔ (∃ x, ¬ A x)
:= by
  constructor
  · -- 从 ¬∀x A(x) 推出 ∃x ¬A(x)
    intro h
    by_cases H : ∃ x, ¬ A x
    · exact H
    · -- H : ¬ ∃ x, ¬A x
      -- 先把目标变为 False，这样 apply h 就能工作
      exfalso
      apply h
      intro x
      by_cases hx : A x
      · exact hx
      · exfalso
        apply H
        exact ⟨x, hx⟩
  · -- 反向：从 ∃x ¬A(x) 推出 ¬∀x A(x)，构造即可
    intro ⟨x, hx⟩ hforall
    exact hx (hforall x)


/--
# 量词否定等值式1
### `law1 :  (¬ ∀ x, A x) ↔ (∃ x, ¬ A x)`

设A(x)含自由出现的个体变项x，则并不是所有的X都有性质A与存在
没有性质A的x等价，即(¬ ∀ x, A x) ↔ (∃ x, ¬ A x)。
-/
TheoremDoc theo.law_1 as "law1" in "third"
