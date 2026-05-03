import Game.Metadata

World "sixthworld"
Level 11

open GraphTheory

Title "two_dvd_mul_succ"

Introduction "本条定理将证明完全图的最大边数为n*(n-1)/2
two_dvd_mul_succ将证明连续两个自然数的乘可以被2整除。
"

--Statement (p q : Prop) (h:p∧q):q∧p:=by
  --exact And.intro (And.right h) (And.left h)

Statement (n : Nat) : 2 ∣ n * (n + 1) := by
  have hmod := Nat.mod_two_eq_zero_or_one n
  rcases hmod with (h0 | h1)
  · -- n 是偶数
    have hn : 2 ∣ n := Nat.dvd_of_mod_eq_zero h0
    exact Nat.dvd_mul_right_of_dvd hn (n+1)
  · -- n 是奇数，则 n+1 是偶数
    have h_succ_mod : (n + 1) % 2 = 0 := by
      calc
        (n + 1) % 2 = ((n % 2) + (1 % 2)) % 2 := by rw [Nat.add_mod]
        _ = (1 + 1) % 2 := by rw [h1, show (1 : Nat) % 2 = 1 by simp]
        _ = 2 % 2 := by simp
        _ = 0 := by simp
    have h_succ_dvd : 2 ∣ n + 1 := Nat.dvd_of_mod_eq_zero h_succ_mod
    exact Nat.dvd_mul_left_of_dvd h_succ_dvd n



Conclusion "."

/- Use these commands to add items to the game's inventory. -/

--NewTactic calc
NewTheorem Nat.dvd_mul_left_of_dvd Nat.mod_two_eq_zero_or_one Nat.dvd_of_mod_eq_zero
-- NewDefinition Nat Add Eq
