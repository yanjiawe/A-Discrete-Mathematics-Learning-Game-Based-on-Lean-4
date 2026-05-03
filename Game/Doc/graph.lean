import Init.Data.List.Basic
import Init.Data.Nat.Basic
import Init.Data.Bool

namespace GraphTheory

/-! ## 图的基本定义 -/

abbrev Vertex := Nat


structure Graph where
  n : Nat
  edges : List (Vertex × Vertex)
  valid : ∀ e ∈ edges, e.1 < n ∧ e.2 < n
  ordered : ∀ e ∈ edges, e.1 < e.2

def edgeCount (g : Graph) : Nat := g.edges.length

def adjacent (g : Graph) (u v : Vertex) : Bool :=
  g.edges.any fun (a, b) => (a == u && b == v) || (a == v && b == u)

def degree (g : Graph) (v : Vertex) : Nat :=
  g.edges.foldl (fun acc (u, w) => if u == v || w == v then acc + 1 else acc) 0

def sumRange (n : Nat) (f : Vertex → Nat) : Nat :=
  (List.range n).foldl (fun acc i => acc + f i) 0

@[simp]
theorem List.foldl_range_add {n : Nat} {f g : Nat → Nat} :
    (List.range n).foldl (fun acc i => acc + (f i + g i)) 0 =
    (List.range n).foldl (fun acc i => acc + f i) 0 +
    (List.range n).foldl (fun acc i => acc + g i) 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp [List.range_succ, List.foldl_append, List.foldl_cons, ih]
      rw [Nat.add_assoc, Nat.add_assoc, Nat.add_left_comm (f n)]

#check Nat.add_add_add_comm

theorem sumRange_add (n : Nat) (f g : Vertex → Nat) :
    sumRange n (fun i => f i + g i) = sumRange n f + sumRange n g := by
  induction n with
  | zero => simp [sumRange]
  | succ n ih =>
      simp[sumRange]

-- 求和一致：若对每个 i，f i = g i，则 sumRange n f = sumRange n g
theorem sumRange_congr (n : Nat) (f g : Vertex → Nat)
    (h : ∀ i, i < n → f i = g i) : sumRange n f = sumRange n g := by
  induction n with
  | zero => simp [sumRange]
  | succ n ih =>
      simp [sumRange, List.range_succ, List.foldl_append, List.foldl_cons]
      rw[←sumRange]
      rw[←sumRange]
      rw [ih]
      · rw [h n (Nat.lt_succ_self n)]
      · intro i hi
        apply h
        exact Nat.lt_succ_of_lt hi

-- 当 n = 0 时 sumRange 为 0
@[simp] theorem sumRange_zero (f : Vertex → Nat) : sumRange 0 f = 0 := rfl

-- 当 f 恒为零时 sumRange 为 0
theorem sumRange_zero' (n : Nat) : sumRange n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [sumRange]
      rw[ List.range_succ,List.foldl_append, List.foldl_cons]
      rw[←sumRange]
      rw[ih]
      rw[List.foldl_nil]


theorem sumRange_indicator_two {n : Nat} {u v : Nat} (hu : u < n) (hv : v < n) (hneq : u ≠ v) :
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


theorem List.foldl_add_const {α : Type} (f : Nat → α → Nat) (l : List α) (init c : Nat)
    (h : ∀ b a, f (b + c) a = f b a + c) :
    List.foldl f (init + c) l = List.foldl f init l + c := by
  induction l generalizing init with
  | nil => simp
  | cons a l' ih =>
      simp [List.foldl_cons]
      rw [←ih (f init a)]
      rw [h init a]
#check List.foldl_cons
#check eq_comm
#check Bool.or_eq_true

theorem handshaking_lemma (g : Graph) :
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
        rw[←List.foldl_add_const]
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

def isOddDegree (g : Graph) (v : Vertex) : Bool :=
  degree g v % 2 == 1

theorem sumRange_mul_const (n : Nat) (c : Nat) (f : Vertex → Nat) :
    sumRange n (fun i => c * f i) = c * sumRange n f := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [sumRange, List.range_succ, List.foldl_append, List.foldl_cons]
      rw [Nat.mul_add]
      simp
      rw[←sumRange]
      rw[←sumRange]
      exact ih


theorem odd_degree_count_even (g : Graph) :(sumRange g.n (fun v => if isOddDegree g v then 1 else 0)) % 2 = 0 := by
  -- 所有顶点度数之和为偶数 (2 * edgeCount g)
  have h_hand := handshaking_lemma g
  --rw [←Nat.mul_comm] at h
  have h_decomp : sumRange g.n (degree g) =
                  2 * sumRange g.n (fun v => degree g v / 2) +
                  sumRange g.n (fun v => degree g v % 2) := by
    conv => lhs; rw [sumRange_congr g.n (degree g)
              (fun v => 2 * (degree g v / 2) + degree g v % 2)
              (by intro i _; exact (Nat.div_add_mod (degree g i) 2).symm)]
    rw [sumRange_add, sumRange_mul_const]
  have h_rem : (sumRange g.n fun v => degree g v % 2) % 2 = 0 := by
    replace h_decomp := congrArg (· % 2) h_decomp
    simp [ Nat.mul_mod_right, h_hand, Nat.mul_mod_right] at h_decomp
    exact h_decomp.symm
  -- 将 degree g v % 2 替换为指示函数形式（两者逐元素相等）
  have h_eq : sumRange g.n (fun v => degree g v % 2) =
              sumRange g.n (fun v => if isOddDegree g v then 1 else 0) := by
    apply sumRange_congr
    intro v _
    simp [isOddDegree]
    by_cases hv : degree g v % 2 = 1
    · simp [hv]
    · have : degree g v % 2 = 0 := by omega
      simp [this]
  rw [← h_eq]
  exact h_rem


def isRegular (g : Graph) (k : Nat) : Prop :=
  ∀ v, v < g.n → degree g v = k

theorem regular_graph_edge_count (g : Graph) (k : Nat) (hreg : isRegular g k):k * g.n = 2 * edgeCount g := by
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

def completeEdges : Nat → List (Vertex × Vertex)
  | 0 => []
  | n+1 => (List.range n).map (fun i => (i, n)) ++ completeEdges n

def completeGraph (n : Nat) : Graph := {
  n := n
  edges := completeEdges n
  valid := by
    intro e h
    induction n with
    | zero => simp [completeEdges] at h
    | succ n ih =>
      rw [completeEdges] at h
      rcases List.mem_append.mp h with (h | h)
      · -- e ∈ map (fun i => (i, n)) (range n)
        rcases List.mem_map.mp h with ⟨i, hi, rfl⟩
        have hi_lt_n : i < n := List.mem_range.mp hi
        simp
        exact Nat.lt_succ_of_le (Nat.le_of_lt hi_lt_n)
      · -- e ∈ completeEdges n
        rcases ih h with ⟨h1, h2⟩
        exact ⟨Nat.lt_succ_of_lt h1, Nat.lt_succ_of_lt h2⟩
  ordered := by
    intro e h
    induction n with
    | zero => simp [completeEdges] at h
    | succ n ih =>
      rw [completeEdges] at h
      rcases List.mem_append.mp h with (h | h)
      · rcases List.mem_map.mp h with ⟨i, hi, rfl⟩
        exact List.mem_range.mp hi
      · exact ih h
}

#check Nat.dvd_mul_left_of_dvd

theorem two_dvd_mul_succ (n : Nat) : 2 ∣ n * (n + 1) := by
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


-- 引理2: 2*n + n*(n-1) = (n+1)*n
theorem two_mul_add_mul_sub_one (n : Nat) : 2 * n + n * (n - 1) = (n + 1) * n := by
  cases n with
  | zero => simp
  | succ n =>
    simp [Nat.succ_sub_succ, Nat.sub_zero]
    calc
      2 * (n + 1) + (n + 1) * n = (n + 1) * n + 2 * (n + 1) := by rw [Nat.add_comm]
      _ = (n + 1) * n + (n + 1) * 2 := by rw [Nat.mul_comm (n + 1) 2]
      _ = (n + 1) * (n + 2) := by rw [Nat.mul_add]
      _ = (n + 2) * (n + 1) := by rw [Nat.mul_comm]

#check Nat.mul_div_assoc

example (n : Nat) : n + n * (n - 1) / 2 = (n + 1) * n / 2 := by
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


theorem complete_graph_edge_count (n : Nat) :
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
