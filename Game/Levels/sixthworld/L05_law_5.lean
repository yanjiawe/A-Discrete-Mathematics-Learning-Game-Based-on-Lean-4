import Game.Metadata

World "sixthworld"
Level 5

open GraphTheory

Title "sumRange_indicator_two"

Introduction "sumRange_indicator_two将对握手定理的证明一部分进行化简，即
sumRange n (fun w => if w = u ∨ w = v then 1 else 0) = 2。
"

--Statement (p q : Prop) (h:p∧q):q∧p:=by
  --exact And.intro (And.right h) (And.left h)

Statement{n : Nat} {u v : Nat} (hu : u < n) (hv : v < n) (hneq : u ≠ v) :
    sumRange n (fun w => if w = u ∨ w = v then 1 else 0) = 2 := by
  induction n with
  | zero => contradiction  -- 因为 hu 要求 0 < 0 不可能
  | succ n ih =>
      simp [sumRange, List.range_succ, List.foldl_append, List.foldl_cons]
      --rw [←sumRange]
      --rw [ih]
      by_cases h : u = n ∨ v = n
      · cases h with
        | inl hu_eq=>
          have v_ne_n' : ¬v = n:= by
            intro h'
            subst h'
            exact hneq hu_eq
          have v_lt_n' : v < n :=by
            have v_m: v<=n:= by
              rw[←Nat.lt_succ,←Nat.add_one]
              exact hv
            exact Nat.lt_of_le_of_ne (v_m) (v_ne_n')
          --subst hu_eq
          rw [← sumRange]
          rw[hu_eq]
          simp
            -- 此时需要 sumRange n' (if w = v then 1 else 0) = 1
          have tmp: sumRange n (fun w => if w = v then 1 else 0) = 1 := by
            clear ih
            induction n with
            | zero => contradiction
            | succ n _ =>
                simp [sumRange, List.range_succ, List.foldl_append, List.foldl_cons]
                rw[←sumRange]
                by_cases h_v : v = n
                · rw [h_v]
                  simp
                  rw [sumRange_congr n (fun i => if i = n then 1 else 0) (fun _ => 0) (by
                      intro i hi
                      simp [Nat.ne_of_lt hi])]
                  rw [sumRange_zero' n]
                · rw [if_neg (Ne.symm h_v)]
                  simp
                  have v_lt_n'' : v < n :=by
                    rw[Nat.add_one] at v_lt_n'
                    rw[Nat.lt_succ] at v_lt_n'
                    exact Nat.lt_of_le_of_ne v_lt_n' h_v
                  clear a hu hv hu_eq v_ne_n' hneq h_v
                  induction n with
                  | zero => contradiction  -- 因为 v < 0 不可能
                  | succ m ihm =>
                      simp [sumRange, List.range_succ, List.foldl_append, List.foldl_cons]
                      rw [← sumRange]
                      by_cases h_vm : v = m
                      · rw [h_vm]
                        simp
                        rw [sumRange_congr m (fun i => if i = m then 1 else 0) (fun _ => 0) (by
                          intro i hi
                          simp [Nat.ne_of_lt hi])]
                        rw [sumRange_zero' m]
                      · have v_lt_m : v < m := by
                          apply Nat.lt_of_le_of_ne
                          · exact Nat.le_of_lt_succ v_lt_n''
                          · exact h_vm
                        rw [if_neg (Ne.symm h_vm)]
                        simp
                        rw [ihm v_lt_n'' v_lt_m]
          rw [sumRange_congr n (fun i => if i = n ∨ i = v then 1 else 0) (fun i => if i = v then 1 else 0)]
          rotate_left
          · -- 证明函数相等：对所有 i < n，有 (i = n ∨ i = v) ↔ (i = v)
           intro i hi
           have hni:¬i=n:=by
            exact Nat.ne_of_lt hi
           simp [hni]
          rw [tmp]
        | inr hv_eq => -- v = n'
            have u_ne_n' : ¬u = n:= by
              intro h'
              subst h'
              exact hneq hv_eq.symm
            have u_lt_n' : u < n :=by
              have u_m: u<=n:= by
                rw[←Nat.lt_succ,←Nat.add_one]
                exact hu
              exact Nat.lt_of_le_of_ne (u_m) (u_ne_n')
          --subst hu_eq
            rw [← sumRange]
            rw[hv_eq]
            simp
            -- 此时需要 sumRange n' (if w = v then 1 else 0) = 1
            have tmp: sumRange n (fun w => if w = u then 1 else 0) = 1 := by
              clear ih
              induction n with
              | zero => contradiction
              | succ n _ =>
                simp [sumRange, List.range_succ, List.foldl_append, List.foldl_cons]
                rw[←sumRange]
                by_cases h_u : u = n
                · rw [h_u]
                  simp
                  rw [sumRange_congr n (fun i => if i = n then 1 else 0) (fun _ => 0) (by
                      intro i hi
                      simp [Nat.ne_of_lt hi])]
                  rw [sumRange_zero' n]
                · rw [if_neg (Ne.symm h_u)]
                  simp
                  have u_lt_n'' : u < n :=by
                    rw[Nat.add_one] at u_lt_n'
                    rw[Nat.lt_succ] at u_lt_n'
                    exact Nat.lt_of_le_of_ne u_lt_n' h_u
                  clear a hu hv hv_eq u_ne_n' hneq h_u
                  induction n with
                  | zero => contradiction  -- 因为 v < 0 不可能
                  | succ m ihm =>
                      simp [sumRange, List.range_succ, List.foldl_append, List.foldl_cons]
                      rw [← sumRange]
                      by_cases h_um : u = m
                      · rw [h_um]
                        simp
                        rw [sumRange_congr m (fun i => if i = m then 1 else 0) (fun _ => 0) (by
                          intro i hi
                          simp [Nat.ne_of_lt hi])]
                        rw [sumRange_zero' m]
                      · have u_lt_m : u < m := by
                          apply Nat.lt_of_le_of_ne
                          · exact Nat.le_of_lt_succ u_lt_n''
                          · exact h_um
                        rw [if_neg (Ne.symm h_um)]
                        simp
                        rw [ihm u_lt_n'' u_lt_m]
            rw [sumRange_congr n (fun i => if i = u ∨ i = n then 1 else 0) (fun i => if i = u then 1 else 0)]
            rotate_left
            · -- 证明函数相等：对所有 i < n，有 (i = n ∨ i = v) ↔ (i = v)
             intro i hi
             have hni:¬i=n:=by
              exact Nat.ne_of_lt hi
             simp [hni]
            rw [tmp]
      · -- 从 h 推导出 n ≠ u 且 n ≠ v
        have n_ne_u : u ≠ n := fun heq => h (Or.inl heq)
        have n_ne_v : v ≠ n := fun heq => h (Or.inr heq)

-- 化简当前项为 0
        have cur_zero : (if n = u ∨ n = v then 1 else 0) = 0 := by
          simp [n_ne_u.symm, n_ne_v.symm]

        rw [cur_zero, Nat.add_zero]

-- 从 hu, hv 结合 n ≠ u, n ≠ v 推出 u < n 和 v < n
        have u_lt_n : u < n := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hu) n_ne_u
        have v_lt_n : v < n := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hv) n_ne_v

-- 应用归纳假设
        exact ih u_lt_n v_lt_n




Conclusion "."

/- Use these commands to add items to the game's inventory. -/

--NewTactic calc
NewTheorem Nat.le_of_lt_succ Nat.add_zero Nat.lt_of_le_of_ne Nat.add_one Nat.lt_succ Nat.ne_of_lt
-- NewDefinition Nat Add Eq
