import Aegis.CanChoose.Code.Funs

/-!
# Specifications of `Aegis.CanChoose.can_choose`

LeetCode problem `form-array-by-concatenating-subarrays-of-another-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.CanChoose

abbrev I64 := Aeneas.Std.I64

abbrev Group := Aeneas.Std.alloc.vec.Vec I64

abbrev Groups := Aeneas.Std.Slice Group

abbrev Nums := Aeneas.Std.Slice I64

def gvals (groups : Groups) (i : ℕ) : List I64 :=
  match groups.val[i]? with
  | some g => g.val
  | none => []

def glist (groups : Groups) (i : ℕ) : List ℤ := (gvals groups i).map (fun x => x.val)

def glen (groups : Groups) (i : ℕ) : ℕ := (gvals groups i).length

def gcell (groups : Groups) (i j : ℕ) : ℤ := (glist groups i).getD j 0

def nth (nums : Nums) (k : ℕ) : ℤ :=
  match nums.val[k]? with
  | some x => x.val
  | none => 0

def gtotal (groups : Groups) : ℕ := (groups.val.map (fun g => g.val.length)).sum

def offset (groups : Groups) (i : ℕ) : ℕ :=
  ((groups.val.take i).map (fun g => g.val.length)).sum

def Places (groups : Groups) (nums : Nums) (s : ℕ → ℕ) : Prop :=
  (∀ i, i < groups.val.length → s i + glen groups i ≤ nums.val.length) ∧
  (∀ i, i < groups.val.length → ∀ j, j < glen groups i →
    nth nums (s i + j) = gcell groups i j) ∧
  (∀ i, 1 ≤ i → i < groups.val.length →
    s (i - 1) + glen groups (i - 1) ≤ s i)

def StrictIncrBelow (p : ℕ → ℕ) (n m : ℕ) : Prop :=
  (∀ i, i + 1 < n → p i < p (i + 1)) ∧ (∀ i, i < n → p i < m)

def Occurs (groups : Groups) (nums : Nums) (x : I64) : Prop :=
  (∃ i, i < groups.val.length ∧ x ∈ gvals groups i) ∨ x ∈ nums.val

theorem thousand_le_usize_max : 1000 ≤ Aeneas.Std.Usize.max := by
  have h := Aeneas.Std.Usize.cMax_bound_concrete
  omega

theorem slice_val_length_le_max {α : Type} (s : Aeneas.Std.Slice α) :
    s.val.length ≤ Aeneas.Std.Usize.max := by
  have h1 : s.val.length = s.leng := Aeneas.Data.ListN.ListN_length s.list
  have h2 : s.leng ≤ Aeneas.Std.Usize.max := s.bound
  omega

def mkNums (l : List I64) (hl : l.length ≤ 1000) : Nums :=
  Aeneas.Std.Slice.from l (by have h := thousand_le_usize_max; omega)

def mkGroups (l : List Group) (hl : l.length ≤ 1000) : Groups :=
  Aeneas.Std.Slice.from l (by have h := thousand_le_usize_max; omega)

def mapGroup (f : I64 → I64) (g : Group) : Group :=
  Aeneas.Std.alloc.vec.Vec.from (g.val.map f)
    (by rw [List.length_map]; exact slice_val_length_le_max g.slice)

def mapGroups (f : I64 → I64) (groups : Groups) : Groups :=
  Aeneas.Std.Slice.from (groups.val.map (fun g => mapGroup f g))
    (by rw [List.length_map]; exact slice_val_length_le_max groups)

def mapNums (f : I64 → I64) (nums : Nums) : Nums :=
  Aeneas.Std.Slice.from (nums.val.map f)
    (by rw [List.length_map]; exact slice_val_length_le_max nums)

/-- can_choose(groups, nums) returns a result r, and r = true if and only if there exist integers s_0, ..., s_{n-1} such that: (1) for every i with 0 <= i < n, 0 <= s_i and s_i + len(groups[i]) <= len(nums); (2) for every i with 0 <= i < n and every j with 0 <= j < len(groups[i]), nums[s_i + j] = groups[i][j]; (3) for every i with 1 <= i < n, s_{i-1} + len(groups[i-1]) <= s_i. Equivalently, r = false exactly when no such tuple of start indices exists.
  Preconditions: Let n = len(groups). Assume 1 <= n <= 1000; for every i with 0 <= i < n, 1 <= len(groups[i]); sum_{i=0}^{n-1} len(groups[i]) <= 1000; 1 <= len(nums) <= 1000; and for every valid i, j, k, -10^7 <= groups[i][j] <= 10^7 and -10^7 <= nums[k] <= 10^7. -/
theorem spec_1
    (groups : Groups) (nums : Nums)
    (h_n_pos : 1 ≤ groups.val.length) (h_n_le : groups.val.length ≤ 1000)
    (h_glen_pos : ∀ i, i < groups.val.length → 1 ≤ glen groups i)
    (h_sum_le : gtotal groups ≤ 1000)
    (h_m_pos : 1 ≤ nums.val.length) (h_m_le : nums.val.length ≤ 1000)
    (h_g_bound : ∀ i, i < groups.val.length → ∀ j, j < glen groups i →
      -(10 ^ 7) ≤ gcell groups i j ∧ gcell groups i j ≤ 10 ^ 7)
    (h_n_bound : ∀ k, k < nums.val.length →
      -(10 ^ 7) ≤ nth nums k ∧ nth nums k ≤ 10 ^ 7) :
    ∃ r, Aegis.CanChoose.can_choose groups nums = ok r ∧
      (r = true ↔ ∃ s, Places groups nums s) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (groups : Groups) (nums : Nums)
    (h_n_pos : 1 ≤ groups.val.length) (h_n_le : groups.val.length ≤ 1000)
    (h_glen_pos : ∀ i, i < groups.val.length → 1 ≤ glen groups i)
    (h_sum_le : gtotal groups ≤ 1000)
    (h_m_pos : 1 ≤ nums.val.length) (h_m_le : nums.val.length ≤ 1000)
    (h_g_bound : ∀ i, i < groups.val.length → ∀ j, j < glen groups i →
      -(10 ^ 7) ≤ gcell groups i j ∧ gcell groups i j ≤ 10 ^ 7)
    (h_n_bound : ∀ k, k < nums.val.length →
      -(10 ^ 7) ≤ nth nums k ∧ nth nums k ≤ 10 ^ 7), ∃ r, Aegis.CanChoose.can_choose groups nums = ok r ∧
      (r = true ↔ ∃ s, Places groups nums s)) := by
  sorry

/-- can_choose(groups, nums) returns a result r; it does not fail by overflow, out-of-bounds access, or panic.
  Preconditions: Let n = len(groups). Assume 1 <= n <= 1000; for every i with 0 <= i < n, 1 <= len(groups[i]); sum_{i=0}^{n-1} len(groups[i]) <= 1000; 1 <= len(nums) <= 1000; and for every valid i, j, k, -10^7 <= groups[i][j] <= 10^7 and -10^7 <= nums[k] <= 10^7. -/
theorem spec_2
    (groups : Groups) (nums : Nums)
    (h_n_pos : 1 ≤ groups.val.length) (h_n_le : groups.val.length ≤ 1000)
    (h_glen_pos : ∀ i, i < groups.val.length → 1 ≤ glen groups i)
    (h_sum_le : gtotal groups ≤ 1000)
    (h_m_pos : 1 ≤ nums.val.length) (h_m_le : nums.val.length ≤ 1000)
    (h_g_bound : ∀ i, i < groups.val.length → ∀ j, j < glen groups i →
      -(10 ^ 7) ≤ gcell groups i j ∧ gcell groups i j ≤ 10 ^ 7)
    (h_n_bound : ∀ k, k < nums.val.length →
      -(10 ^ 7) ≤ nth nums k ∧ nth nums k ≤ 10 ^ 7) :
    ∃ r, Aegis.CanChoose.can_choose groups nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (groups : Groups) (nums : Nums)
    (h_n_pos : 1 ≤ groups.val.length) (h_n_le : groups.val.length ≤ 1000)
    (h_glen_pos : ∀ i, i < groups.val.length → 1 ≤ glen groups i)
    (h_sum_le : gtotal groups ≤ 1000)
    (h_m_pos : 1 ≤ nums.val.length) (h_m_le : nums.val.length ≤ 1000)
    (h_g_bound : ∀ i, i < groups.val.length → ∀ j, j < glen groups i →
      -(10 ^ 7) ≤ gcell groups i j ∧ gcell groups i j ≤ 10 ^ 7)
    (h_n_bound : ∀ k, k < nums.val.length →
      -(10 ^ 7) ≤ nth nums k ∧ nth nums k ≤ 10 ^ 7), ∃ r, Aegis.CanChoose.can_choose groups nums = ok r) := by
  sorry

/-- Whenever sum_{i=0}^{n-1} len(groups[i]) > len(nums), can_choose(groups, nums) returns a result r and r = false.
  Preconditions: Let n = len(groups). Assume 1 <= n <= 1000; for every i with 0 <= i < n, 1 <= len(groups[i]); sum_{i=0}^{n-1} len(groups[i]) <= 1000; 1 <= len(nums) <= 1000; and for every valid i, j, k, -10^7 <= groups[i][j] <= 10^7 and -10^7 <= nums[k] <= 10^7. -/
theorem spec_3
    (groups : Groups) (nums : Nums)
    (h_n_pos : 1 ≤ groups.val.length) (h_n_le : groups.val.length ≤ 1000)
    (h_glen_pos : ∀ i, i < groups.val.length → 1 ≤ glen groups i)
    (h_sum_le : gtotal groups ≤ 1000)
    (h_m_pos : 1 ≤ nums.val.length) (h_m_le : nums.val.length ≤ 1000)
    (h_g_bound : ∀ i, i < groups.val.length → ∀ j, j < glen groups i →
      -(10 ^ 7) ≤ gcell groups i j ∧ gcell groups i j ≤ 10 ^ 7)
    (h_n_bound : ∀ k, k < nums.val.length →
      -(10 ^ 7) ≤ nth nums k ∧ nth nums k ≤ 10 ^ 7)
    (h_gt : nums.val.length < gtotal groups) :
    ∃ r, Aegis.CanChoose.can_choose groups nums = ok r ∧ r = false := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (groups : Groups) (nums : Nums)
    (h_n_pos : 1 ≤ groups.val.length) (h_n_le : groups.val.length ≤ 1000)
    (h_glen_pos : ∀ i, i < groups.val.length → 1 ≤ glen groups i)
    (h_sum_le : gtotal groups ≤ 1000)
    (h_m_pos : 1 ≤ nums.val.length) (h_m_le : nums.val.length ≤ 1000)
    (h_g_bound : ∀ i, i < groups.val.length → ∀ j, j < glen groups i →
      -(10 ^ 7) ≤ gcell groups i j ∧ gcell groups i j ≤ 10 ^ 7)
    (h_n_bound : ∀ k, k < nums.val.length →
      -(10 ^ 7) ≤ nth nums k ∧ nth nums k ≤ 10 ^ 7)
    (h_gt : nums.val.length < gtotal groups), ∃ r, Aegis.CanChoose.can_choose groups nums = ok r ∧ r = false) := by
  sorry

/-- Whenever can_choose(groups, nums) returns a result r with r = true, for every i with 0 <= i < n there exists an integer p_i such that 0 <= p_i, p_i + len(groups[i]) <= len(nums), and for every j with 0 <= j < len(groups[i]), nums[p_i + j] = groups[i][j].
  Preconditions: Let n = len(groups). Assume 1 <= n <= 1000; for every i with 0 <= i < n, 1 <= len(groups[i]); sum_{i=0}^{n-1} len(groups[i]) <= 1000; 1 <= len(nums) <= 1000; and for every valid i, j, k, -10^7 <= groups[i][j] <= 10^7 and -10^7 <= nums[k] <= 10^7. -/
theorem spec_4
    (groups : Groups) (nums : Nums)
    (h_n_pos : 1 ≤ groups.val.length) (h_n_le : groups.val.length ≤ 1000)
    (h_glen_pos : ∀ i, i < groups.val.length → 1 ≤ glen groups i)
    (h_sum_le : gtotal groups ≤ 1000)
    (h_m_pos : 1 ≤ nums.val.length) (h_m_le : nums.val.length ≤ 1000)
    (h_g_bound : ∀ i, i < groups.val.length → ∀ j, j < glen groups i →
      -(10 ^ 7) ≤ gcell groups i j ∧ gcell groups i j ≤ 10 ^ 7)
    (h_n_bound : ∀ k, k < nums.val.length →
      -(10 ^ 7) ≤ nth nums k ∧ nth nums k ≤ 10 ^ 7) :
    Aegis.CanChoose.can_choose groups nums = ok true →
      ∀ i, i < groups.val.length →
        ∃ p, p + glen groups i ≤ nums.val.length ∧
          ∀ j, j < glen groups i → nth nums (p + j) = gcell groups i j := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (groups : Groups) (nums : Nums)
    (h_n_pos : 1 ≤ groups.val.length) (h_n_le : groups.val.length ≤ 1000)
    (h_glen_pos : ∀ i, i < groups.val.length → 1 ≤ glen groups i)
    (h_sum_le : gtotal groups ≤ 1000)
    (h_m_pos : 1 ≤ nums.val.length) (h_m_le : nums.val.length ≤ 1000)
    (h_g_bound : ∀ i, i < groups.val.length → ∀ j, j < glen groups i →
      -(10 ^ 7) ≤ gcell groups i j ∧ gcell groups i j ≤ 10 ^ 7)
    (h_n_bound : ∀ k, k < nums.val.length →
      -(10 ^ 7) ≤ nth nums k ∧ nth nums k ≤ 10 ^ 7), Aegis.CanChoose.can_choose groups nums = ok true →
      ∀ i, i < groups.val.length →
        ∃ p, p + glen groups i ≤ nums.val.length ∧
          ∀ j, j < glen groups i → nth nums (p + j) = gcell groups i j) := by
  sorry

/-- Whenever can_choose(groups, nums) returns a result r with r = true, there exist integers p_0, ..., p_{n-1} such that 0 <= p_0 < p_1 < ... < p_{n-1} < len(nums) and nums[p_i] = groups[i][0] for every i with 0 <= i < n.
  Preconditions: Let n = len(groups). Assume 1 <= n <= 1000; for every i with 0 <= i < n, 1 <= len(groups[i]); sum_{i=0}^{n-1} len(groups[i]) <= 1000; 1 <= len(nums) <= 1000; and for every valid i, j, k, -10^7 <= groups[i][j] <= 10^7 and -10^7 <= nums[k] <= 10^7. -/
theorem spec_5
    (groups : Groups) (nums : Nums)
    (h_n_pos : 1 ≤ groups.val.length) (h_n_le : groups.val.length ≤ 1000)
    (h_glen_pos : ∀ i, i < groups.val.length → 1 ≤ glen groups i)
    (h_sum_le : gtotal groups ≤ 1000)
    (h_m_pos : 1 ≤ nums.val.length) (h_m_le : nums.val.length ≤ 1000)
    (h_g_bound : ∀ i, i < groups.val.length → ∀ j, j < glen groups i →
      -(10 ^ 7) ≤ gcell groups i j ∧ gcell groups i j ≤ 10 ^ 7)
    (h_n_bound : ∀ k, k < nums.val.length →
      -(10 ^ 7) ≤ nth nums k ∧ nth nums k ≤ 10 ^ 7) :
    Aegis.CanChoose.can_choose groups nums = ok true →
      ∃ p, StrictIncrBelow p groups.val.length nums.val.length ∧
        ∀ i, i < groups.val.length → nth nums (p i) = gcell groups i 0 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (groups : Groups) (nums : Nums)
    (h_n_pos : 1 ≤ groups.val.length) (h_n_le : groups.val.length ≤ 1000)
    (h_glen_pos : ∀ i, i < groups.val.length → 1 ≤ glen groups i)
    (h_sum_le : gtotal groups ≤ 1000)
    (h_m_pos : 1 ≤ nums.val.length) (h_m_le : nums.val.length ≤ 1000)
    (h_g_bound : ∀ i, i < groups.val.length → ∀ j, j < glen groups i →
      -(10 ^ 7) ≤ gcell groups i j ∧ gcell groups i j ≤ 10 ^ 7)
    (h_n_bound : ∀ k, k < nums.val.length →
      -(10 ^ 7) ≤ nth nums k ∧ nth nums k ≤ 10 ^ 7), Aegis.CanChoose.can_choose groups nums = ok true →
      ∃ p, StrictIncrBelow p groups.val.length nums.val.length ∧
        ∀ i, i < groups.val.length → nth nums (p i) = gcell groups i 0) := by
  sorry

/-- Let offset_i = sum_{h=0}^{i-1} len(groups[h]) for 0 <= i < n. Then can_choose(groups, nums) returns a result r, and r = true if and only if for every i with 0 <= i < n and every j with 0 <= j < len(groups[i]), nums[offset_i + j] = groups[i][j]. Equivalently, nums is exactly the concatenation groups[0] ++ groups[1] ++ ... ++ groups[n-1].
  Preconditions: Let n = len(groups). Assume 1 <= n <= 1000; for every i with 0 <= i < n, 1 <= len(groups[i]); sum_{i=0}^{n-1} len(groups[i]) <= 1000; 1 <= len(nums) <= 1000; and for every valid i, j, k, -10^7 <= groups[i][j] <= 10^7 and -10^7 <= nums[k] <= 10^7. Additionally assume sum_{i=0}^{n-1} len(groups[i]) = len(nums). -/
theorem spec_6
    (groups : Groups) (nums : Nums)
    (h_n_pos : 1 ≤ groups.val.length) (h_n_le : groups.val.length ≤ 1000)
    (h_glen_pos : ∀ i, i < groups.val.length → 1 ≤ glen groups i)
    (h_sum_le : gtotal groups ≤ 1000)
    (h_m_pos : 1 ≤ nums.val.length) (h_m_le : nums.val.length ≤ 1000)
    (h_g_bound : ∀ i, i < groups.val.length → ∀ j, j < glen groups i →
      -(10 ^ 7) ≤ gcell groups i j ∧ gcell groups i j ≤ 10 ^ 7)
    (h_n_bound : ∀ k, k < nums.val.length →
      -(10 ^ 7) ≤ nth nums k ∧ nth nums k ≤ 10 ^ 7)
    (h_total : gtotal groups = nums.val.length) :
    ∃ r, Aegis.CanChoose.can_choose groups nums = ok r ∧
      (r = true ↔ ∀ i, i < groups.val.length → ∀ j, j < glen groups i →
        nth nums (offset groups i + j) = gcell groups i j) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (groups : Groups) (nums : Nums)
    (h_n_pos : 1 ≤ groups.val.length) (h_n_le : groups.val.length ≤ 1000)
    (h_glen_pos : ∀ i, i < groups.val.length → 1 ≤ glen groups i)
    (h_sum_le : gtotal groups ≤ 1000)
    (h_m_pos : 1 ≤ nums.val.length) (h_m_le : nums.val.length ≤ 1000)
    (h_g_bound : ∀ i, i < groups.val.length → ∀ j, j < glen groups i →
      -(10 ^ 7) ≤ gcell groups i j ∧ gcell groups i j ≤ 10 ^ 7)
    (h_n_bound : ∀ k, k < nums.val.length →
      -(10 ^ 7) ≤ nth nums k ∧ nth nums k ≤ 10 ^ 7)
    (h_total : gtotal groups = nums.val.length), ∃ r, Aegis.CanChoose.can_choose groups nums = ok r ∧
      (r = true ↔ ∀ i, i < groups.val.length → ∀ j, j < glen groups i →
        nth nums (offset groups i + j) = gcell groups i j)) := by
  sorry

/-- can_choose(groups, nums) returns a result r, and r = true if and only if there exist integers p_0, ..., p_{n-1} such that 0 <= p_0 < p_1 < ... < p_{n-1} < len(nums) and nums[p_i] = groups[i][0] for every i with 0 <= i < n.
  Preconditions: Let n = len(groups). Assume 1 <= n <= 1000; for every i with 0 <= i < n, len(groups[i]) = 1; 1 <= len(nums) <= 1000; and for every valid i, k, -10^7 <= groups[i][0] <= 10^7 and -10^7 <= nums[k] <= 10^7. -/
theorem spec_7
    (groups : Groups) (nums : Nums)
    (h_n_pos : 1 ≤ groups.val.length) (h_n_le : groups.val.length ≤ 1000)
    (h_glen_one : ∀ i, i < groups.val.length → glen groups i = 1)
    (h_m_pos : 1 ≤ nums.val.length) (h_m_le : nums.val.length ≤ 1000)
    (h_g_bound : ∀ i, i < groups.val.length →
      -(10 ^ 7) ≤ gcell groups i 0 ∧ gcell groups i 0 ≤ 10 ^ 7)
    (h_n_bound : ∀ k, k < nums.val.length →
      -(10 ^ 7) ≤ nth nums k ∧ nth nums k ≤ 10 ^ 7) :
    ∃ r, Aegis.CanChoose.can_choose groups nums = ok r ∧
      (r = true ↔ ∃ p, StrictIncrBelow p groups.val.length nums.val.length ∧
        ∀ i, i < groups.val.length → nth nums (p i) = gcell groups i 0) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (groups : Groups) (nums : Nums)
    (h_n_pos : 1 ≤ groups.val.length) (h_n_le : groups.val.length ≤ 1000)
    (h_glen_one : ∀ i, i < groups.val.length → glen groups i = 1)
    (h_m_pos : 1 ≤ nums.val.length) (h_m_le : nums.val.length ≤ 1000)
    (h_g_bound : ∀ i, i < groups.val.length →
      -(10 ^ 7) ≤ gcell groups i 0 ∧ gcell groups i 0 ≤ 10 ^ 7)
    (h_n_bound : ∀ k, k < nums.val.length →
      -(10 ^ 7) ≤ nth nums k ∧ nth nums k ≤ 10 ^ 7), ∃ r, Aegis.CanChoose.can_choose groups nums = ok r ∧
      (r = true ↔ ∃ p, StrictIncrBelow p groups.val.length nums.val.length ∧
        ∀ i, i < groups.val.length → nth nums (p i) = gcell groups i 0)) := by
  sorry

/-- If there exists an integer p such that 0 <= p, p + sum_{i=0}^{n-1} len(groups[i]) <= len(nums), and for every i with 0 <= i < n and every j with 0 <= j < len(groups[i]), nums[p + offset_i + j] = groups[i][j], where offset_i = sum_{h=0}^{i-1} len(groups[h]), then can_choose(groups, nums) returns a result r and r = true.
  Preconditions: Let n = len(groups). Assume 1 <= n <= 1000; for every i with 0 <= i < n, 1 <= len(groups[i]); sum_{i=0}^{n-1} len(groups[i]) <= 1000; 1 <= len(nums) <= 1000; and for every valid i, j, k, -10^7 <= groups[i][j] <= 10^7 and -10^7 <= nums[k] <= 10^7. -/
theorem spec_8
    (groups : Groups) (nums : Nums)
    (h_n_pos : 1 ≤ groups.val.length) (h_n_le : groups.val.length ≤ 1000)
    (h_glen_pos : ∀ i, i < groups.val.length → 1 ≤ glen groups i)
    (h_sum_le : gtotal groups ≤ 1000)
    (h_m_pos : 1 ≤ nums.val.length) (h_m_le : nums.val.length ≤ 1000)
    (h_g_bound : ∀ i, i < groups.val.length → ∀ j, j < glen groups i →
      -(10 ^ 7) ≤ gcell groups i j ∧ gcell groups i j ≤ 10 ^ 7)
    (h_n_bound : ∀ k, k < nums.val.length →
      -(10 ^ 7) ≤ nth nums k ∧ nth nums k ≤ 10 ^ 7)
    (h_witness : ∃ p, p + gtotal groups ≤ nums.val.length ∧
      ∀ i, i < groups.val.length → ∀ j, j < glen groups i →
        nth nums (p + offset groups i + j) = gcell groups i j) :
    ∃ r, Aegis.CanChoose.can_choose groups nums = ok r ∧ r = true := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (groups : Groups) (nums : Nums)
    (h_n_pos : 1 ≤ groups.val.length) (h_n_le : groups.val.length ≤ 1000)
    (h_glen_pos : ∀ i, i < groups.val.length → 1 ≤ glen groups i)
    (h_sum_le : gtotal groups ≤ 1000)
    (h_m_pos : 1 ≤ nums.val.length) (h_m_le : nums.val.length ≤ 1000)
    (h_g_bound : ∀ i, i < groups.val.length → ∀ j, j < glen groups i →
      -(10 ^ 7) ≤ gcell groups i j ∧ gcell groups i j ≤ 10 ^ 7)
    (h_n_bound : ∀ k, k < nums.val.length →
      -(10 ^ 7) ≤ nth nums k ∧ nth nums k ≤ 10 ^ 7)
    (h_witness : ∃ p, p + gtotal groups ≤ nums.val.length ∧
      ∀ i, i < groups.val.length → ∀ j, j < glen groups i →
        nth nums (p + offset groups i + j) = gcell groups i j), ∃ r, Aegis.CanChoose.can_choose groups nums = ok r ∧ r = true) := by
  sorry

/-- Whenever can_choose(groups, nums) returns a result r with r = true, for every finite list pre of 64-bit integers such that len(pre) + len(nums) <= 1000 and every entry of pre lies in [-10^7, 10^7], can_choose(groups, pre ++ nums) returns a result r' with r' = true.
  Preconditions: Let n = len(groups). Assume 1 <= n <= 1000; for every i with 0 <= i < n, 1 <= len(groups[i]); sum_{i=0}^{n-1} len(groups[i]) <= 1000; 1 <= len(nums) <= 1000; and for every valid i, j, k, -10^7 <= groups[i][j] <= 10^7 and -10^7 <= nums[k] <= 10^7. -/
theorem spec_9
    (groups : Groups) (nums : Nums)
    (h_n_pos : 1 ≤ groups.val.length) (h_n_le : groups.val.length ≤ 1000)
    (h_glen_pos : ∀ i, i < groups.val.length → 1 ≤ glen groups i)
    (h_sum_le : gtotal groups ≤ 1000)
    (h_m_pos : 1 ≤ nums.val.length) (h_m_le : nums.val.length ≤ 1000)
    (h_g_bound : ∀ i, i < groups.val.length → ∀ j, j < glen groups i →
      -(10 ^ 7) ≤ gcell groups i j ∧ gcell groups i j ≤ 10 ^ 7)
    (h_n_bound : ∀ k, k < nums.val.length →
      -(10 ^ 7) ≤ nth nums k ∧ nth nums k ≤ 10 ^ 7) :
    Aegis.CanChoose.can_choose groups nums = ok true →
      ∀ (pre : List I64) (h_pre_len : pre.length + nums.val.length ≤ 1000),
        (∀ x, x ∈ pre → -(10 ^ 7) ≤ x.val ∧ x.val ≤ 10 ^ 7) →
        ∃ r', Aegis.CanChoose.can_choose groups
            (mkNums (pre ++ nums.val) (by rw [List.length_append]; omega)) = ok r' ∧
          r' = true := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (groups : Groups) (nums : Nums)
    (h_n_pos : 1 ≤ groups.val.length) (h_n_le : groups.val.length ≤ 1000)
    (h_glen_pos : ∀ i, i < groups.val.length → 1 ≤ glen groups i)
    (h_sum_le : gtotal groups ≤ 1000)
    (h_m_pos : 1 ≤ nums.val.length) (h_m_le : nums.val.length ≤ 1000)
    (h_g_bound : ∀ i, i < groups.val.length → ∀ j, j < glen groups i →
      -(10 ^ 7) ≤ gcell groups i j ∧ gcell groups i j ≤ 10 ^ 7)
    (h_n_bound : ∀ k, k < nums.val.length →
      -(10 ^ 7) ≤ nth nums k ∧ nth nums k ≤ 10 ^ 7), Aegis.CanChoose.can_choose groups nums = ok true →
      ∀ (pre : List I64) (h_pre_len : pre.length + nums.val.length ≤ 1000),
        (∀ x, x ∈ pre → -(10 ^ 7) ≤ x.val ∧ x.val ≤ 10 ^ 7) →
        ∃ r', Aegis.CanChoose.can_choose groups
            (mkNums (pre ++ nums.val) (by rw [List.length_append]; omega)) = ok r' ∧
          r' = true) := by
  sorry

/-- Whenever can_choose(groups, nums) returns a result r with r = true, for every finite list suf of 64-bit integers such that len(nums) + len(suf) <= 1000 and every entry of suf lies in [-10^7, 10^7], can_choose(groups, nums ++ suf) returns a result r' with r' = true.
  Preconditions: Let n = len(groups). Assume 1 <= n <= 1000; for every i with 0 <= i < n, 1 <= len(groups[i]); sum_{i=0}^{n-1} len(groups[i]) <= 1000; 1 <= len(nums) <= 1000; and for every valid i, j, k, -10^7 <= groups[i][j] <= 10^7 and -10^7 <= nums[k] <= 10^7. -/
theorem spec_10
    (groups : Groups) (nums : Nums)
    (h_n_pos : 1 ≤ groups.val.length) (h_n_le : groups.val.length ≤ 1000)
    (h_glen_pos : ∀ i, i < groups.val.length → 1 ≤ glen groups i)
    (h_sum_le : gtotal groups ≤ 1000)
    (h_m_pos : 1 ≤ nums.val.length) (h_m_le : nums.val.length ≤ 1000)
    (h_g_bound : ∀ i, i < groups.val.length → ∀ j, j < glen groups i →
      -(10 ^ 7) ≤ gcell groups i j ∧ gcell groups i j ≤ 10 ^ 7)
    (h_n_bound : ∀ k, k < nums.val.length →
      -(10 ^ 7) ≤ nth nums k ∧ nth nums k ≤ 10 ^ 7) :
    Aegis.CanChoose.can_choose groups nums = ok true →
      ∀ (suf : List I64) (h_suf_len : nums.val.length + suf.length ≤ 1000),
        (∀ x, x ∈ suf → -(10 ^ 7) ≤ x.val ∧ x.val ≤ 10 ^ 7) →
        ∃ r', Aegis.CanChoose.can_choose groups
            (mkNums (nums.val ++ suf) (by rw [List.length_append]; omega)) = ok r' ∧
          r' = true := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (groups : Groups) (nums : Nums)
    (h_n_pos : 1 ≤ groups.val.length) (h_n_le : groups.val.length ≤ 1000)
    (h_glen_pos : ∀ i, i < groups.val.length → 1 ≤ glen groups i)
    (h_sum_le : gtotal groups ≤ 1000)
    (h_m_pos : 1 ≤ nums.val.length) (h_m_le : nums.val.length ≤ 1000)
    (h_g_bound : ∀ i, i < groups.val.length → ∀ j, j < glen groups i →
      -(10 ^ 7) ≤ gcell groups i j ∧ gcell groups i j ≤ 10 ^ 7)
    (h_n_bound : ∀ k, k < nums.val.length →
      -(10 ^ 7) ≤ nth nums k ∧ nth nums k ≤ 10 ^ 7), Aegis.CanChoose.can_choose groups nums = ok true →
      ∀ (suf : List I64) (h_suf_len : nums.val.length + suf.length ≤ 1000),
        (∀ x, x ∈ suf → -(10 ^ 7) ≤ x.val ∧ x.val ≤ 10 ^ 7) →
        ∃ r', Aegis.CanChoose.can_choose groups
            (mkNums (nums.val ++ suf) (by rw [List.length_append]; omega)) = ok r' ∧
          r' = true) := by
  sorry

/-- Let V be the set of all integers occurring in groups or nums. For every function f from 64-bit integers to 64-bit integers that is injective on V and satisfies -10^7 <= f(x) <= 10^7 for every x in V, let groups_f be obtained from groups by replacing every element x by f(x), and let nums_f be obtained from nums by replacing every element x by f(x). Then can_choose(groups, nums) returns a result r, can_choose(groups_f, nums_f) returns a result r_f, and r = r_f.
  Preconditions: Let n = len(groups). Assume 1 <= n <= 1000; for every i with 0 <= i < n, 1 <= len(groups[i]); sum_{i=0}^{n-1} len(groups[i]) <= 1000; 1 <= len(nums) <= 1000; and for every valid i, j, k, -10^7 <= groups[i][j] <= 10^7 and -10^7 <= nums[k] <= 10^7. -/
theorem spec_11
    (groups : Groups) (nums : Nums)
    (h_n_pos : 1 ≤ groups.val.length) (h_n_le : groups.val.length ≤ 1000)
    (h_glen_pos : ∀ i, i < groups.val.length → 1 ≤ glen groups i)
    (h_sum_le : gtotal groups ≤ 1000)
    (h_m_pos : 1 ≤ nums.val.length) (h_m_le : nums.val.length ≤ 1000)
    (h_g_bound : ∀ i, i < groups.val.length → ∀ j, j < glen groups i →
      -(10 ^ 7) ≤ gcell groups i j ∧ gcell groups i j ≤ 10 ^ 7)
    (h_n_bound : ∀ k, k < nums.val.length →
      -(10 ^ 7) ≤ nth nums k ∧ nth nums k ≤ 10 ^ 7)
    (f : I64 → I64)
    (h_f_inj : ∀ x, Occurs groups nums x → ∀ y, Occurs groups nums y →
      f x = f y → x = y)
    (h_f_range : ∀ x, Occurs groups nums x →
      -(10 ^ 7) ≤ (f x).val ∧ (f x).val ≤ 10 ^ 7) :
    ∃ r, Aegis.CanChoose.can_choose groups nums = ok r ∧
      ∃ r_f, Aegis.CanChoose.can_choose (mapGroups f groups) (mapNums f nums) = ok r_f ∧
        r = r_f := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (groups : Groups) (nums : Nums)
    (h_n_pos : 1 ≤ groups.val.length) (h_n_le : groups.val.length ≤ 1000)
    (h_glen_pos : ∀ i, i < groups.val.length → 1 ≤ glen groups i)
    (h_sum_le : gtotal groups ≤ 1000)
    (h_m_pos : 1 ≤ nums.val.length) (h_m_le : nums.val.length ≤ 1000)
    (h_g_bound : ∀ i, i < groups.val.length → ∀ j, j < glen groups i →
      -(10 ^ 7) ≤ gcell groups i j ∧ gcell groups i j ≤ 10 ^ 7)
    (h_n_bound : ∀ k, k < nums.val.length →
      -(10 ^ 7) ≤ nth nums k ∧ nth nums k ≤ 10 ^ 7)
    (f : I64 → I64)
    (h_f_inj : ∀ x, Occurs groups nums x → ∀ y, Occurs groups nums y →
      f x = f y → x = y)
    (h_f_range : ∀ x, Occurs groups nums x →
      -(10 ^ 7) ≤ (f x).val ∧ (f x).val ≤ 10 ^ 7), ∃ r, Aegis.CanChoose.can_choose groups nums = ok r ∧
      ∃ r_f, Aegis.CanChoose.can_choose (mapGroups f groups) (mapNums f nums) = ok r_f ∧
        r = r_f) := by
  sorry

/-- Whenever can_choose(groups, nums) returns a result r with r = true, let p be the least integer such that 0 <= p, p + len(groups[0]) <= len(nums), and nums[p + j] = groups[0][j] for every j with 0 <= j < len(groups[0]). Then such p exists, and there exist integers s_1, ..., s_{n-1} such that, setting s_0 = p, the tuple s_0, ..., s_{n-1} satisfies: for every i with 0 <= i < n, 0 <= s_i and s_i + len(groups[i]) <= len(nums); for every i, j with 0 <= i < n and 0 <= j < len(groups[i]), nums[s_i + j] = groups[i][j]; and for every i with 1 <= i < n, s_{i-1} + len(groups[i-1]) <= s_i.
  Preconditions: Let n = len(groups). Assume 1 <= n <= 1000; for every i with 0 <= i < n, 1 <= len(groups[i]); sum_{i=0}^{n-1} len(groups[i]) <= 1000; 1 <= len(nums) <= 1000; and for every valid i, j, k, -10^7 <= groups[i][j] <= 10^7 and -10^7 <= nums[k] <= 10^7. -/
theorem spec_12
    (groups : Groups) (nums : Nums)
    (h_n_pos : 1 ≤ groups.val.length) (h_n_le : groups.val.length ≤ 1000)
    (h_glen_pos : ∀ i, i < groups.val.length → 1 ≤ glen groups i)
    (h_sum_le : gtotal groups ≤ 1000)
    (h_m_pos : 1 ≤ nums.val.length) (h_m_le : nums.val.length ≤ 1000)
    (h_g_bound : ∀ i, i < groups.val.length → ∀ j, j < glen groups i →
      -(10 ^ 7) ≤ gcell groups i j ∧ gcell groups i j ≤ 10 ^ 7)
    (h_n_bound : ∀ k, k < nums.val.length →
      -(10 ^ 7) ≤ nth nums k ∧ nth nums k ≤ 10 ^ 7) :
    Aegis.CanChoose.can_choose groups nums = ok true →
      ∃ p, p + glen groups 0 ≤ nums.val.length ∧
        (∀ j, j < glen groups 0 → nth nums (p + j) = gcell groups 0 j) ∧
        (∀ q, q + glen groups 0 ≤ nums.val.length →
          (∀ j, j < glen groups 0 → nth nums (q + j) = gcell groups 0 j) → p ≤ q) ∧
        ∃ s, s 0 = p ∧ Places groups nums s := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (groups : Groups) (nums : Nums)
    (h_n_pos : 1 ≤ groups.val.length) (h_n_le : groups.val.length ≤ 1000)
    (h_glen_pos : ∀ i, i < groups.val.length → 1 ≤ glen groups i)
    (h_sum_le : gtotal groups ≤ 1000)
    (h_m_pos : 1 ≤ nums.val.length) (h_m_le : nums.val.length ≤ 1000)
    (h_g_bound : ∀ i, i < groups.val.length → ∀ j, j < glen groups i →
      -(10 ^ 7) ≤ gcell groups i j ∧ gcell groups i j ≤ 10 ^ 7)
    (h_n_bound : ∀ k, k < nums.val.length →
      -(10 ^ 7) ≤ nth nums k ∧ nth nums k ≤ 10 ^ 7), Aegis.CanChoose.can_choose groups nums = ok true →
      ∃ p, p + glen groups 0 ≤ nums.val.length ∧
        (∀ j, j < glen groups 0 → nth nums (p + j) = gcell groups 0 j) ∧
        (∀ q, q + glen groups 0 ≤ nums.val.length →
          (∀ j, j < glen groups 0 → nth nums (q + j) = gcell groups 0 j) → p ≤ q) ∧
        ∃ s, s 0 = p ∧ Places groups nums s) := by
  sorry

/-- Whenever can_choose(groups, nums) returns a result r with r = true, there exist integers s_0, ..., s_{n-1} satisfying 0 <= s_i, s_i + len(groups[i]) <= len(nums), nums[s_i + j] = groups[i][j] for every 0 <= j < len(groups[i]), and s_{i-1} + len(groups[i-1]) <= s_i for every 1 <= i < n. For every list nums' with len(nums') = len(nums), every entry in [-10^7, 10^7], and nums'[k] = nums[k] for every k that belongs to at least one interval {s_i, s_i+1, ..., s_i+len(groups[i])-1}, can_choose(groups, nums') returns a result r' with r' = true.
  Preconditions: Let n = len(groups). Assume 1 <= n <= 1000; for every i with 0 <= i < n, 1 <= len(groups[i]); sum_{i=0}^{n-1} len(groups[i]) <= 1000; 1 <= len(nums) <= 1000; and for every valid i, j, k, -10^7 <= groups[i][j] <= 10^7 and -10^7 <= nums[k] <= 10^7. -/
theorem spec_13
    (groups : Groups) (nums : Nums)
    (h_n_pos : 1 ≤ groups.val.length) (h_n_le : groups.val.length ≤ 1000)
    (h_glen_pos : ∀ i, i < groups.val.length → 1 ≤ glen groups i)
    (h_sum_le : gtotal groups ≤ 1000)
    (h_m_pos : 1 ≤ nums.val.length) (h_m_le : nums.val.length ≤ 1000)
    (h_g_bound : ∀ i, i < groups.val.length → ∀ j, j < glen groups i →
      -(10 ^ 7) ≤ gcell groups i j ∧ gcell groups i j ≤ 10 ^ 7)
    (h_n_bound : ∀ k, k < nums.val.length →
      -(10 ^ 7) ≤ nth nums k ∧ nth nums k ≤ 10 ^ 7) :
    Aegis.CanChoose.can_choose groups nums = ok true →
      ∃ s, Places groups nums s ∧
        ∀ nums' : Nums, nums'.val.length = nums.val.length →
          (∀ k, k < nums'.val.length →
            -(10 ^ 7) ≤ nth nums' k ∧ nth nums' k ≤ 10 ^ 7) →
          (∀ k, k < nums'.val.length →
            (∃ i, i < groups.val.length ∧ s i ≤ k ∧ k < s i + glen groups i) →
            nth nums' k = nth nums k) →
          ∃ r', Aegis.CanChoose.can_choose groups nums' = ok r' ∧ r' = true := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (groups : Groups) (nums : Nums)
    (h_n_pos : 1 ≤ groups.val.length) (h_n_le : groups.val.length ≤ 1000)
    (h_glen_pos : ∀ i, i < groups.val.length → 1 ≤ glen groups i)
    (h_sum_le : gtotal groups ≤ 1000)
    (h_m_pos : 1 ≤ nums.val.length) (h_m_le : nums.val.length ≤ 1000)
    (h_g_bound : ∀ i, i < groups.val.length → ∀ j, j < glen groups i →
      -(10 ^ 7) ≤ gcell groups i j ∧ gcell groups i j ≤ 10 ^ 7)
    (h_n_bound : ∀ k, k < nums.val.length →
      -(10 ^ 7) ≤ nth nums k ∧ nth nums k ≤ 10 ^ 7), Aegis.CanChoose.can_choose groups nums = ok true →
      ∃ s, Places groups nums s ∧
        ∀ nums' : Nums, nums'.val.length = nums.val.length →
          (∀ k, k < nums'.val.length →
            -(10 ^ 7) ≤ nth nums' k ∧ nth nums' k ≤ 10 ^ 7) →
          (∀ k, k < nums'.val.length →
            (∃ i, i < groups.val.length ∧ s i ≤ k ∧ k < s i + glen groups i) →
            nth nums' k = nth nums k) →
          ∃ r', Aegis.CanChoose.can_choose groups nums' = ok r' ∧ r' = true) := by
  sorry

/-- Whenever can_choose(groups, nums) returns a result r with r = true, there exist integers s_0, ..., s_{n-1} such that: for every i with 0 <= i < n, 0 <= s_i and s_i + len(groups[i]) <= len(nums); for every i, j with 0 <= i < n and 0 <= j < len(groups[i]), nums[s_i + j] = groups[i][j]; for every i with 1 <= i < n, s_{i-1} + len(groups[i-1]) <= s_i; and moreover s_0 is the least q with 0 <= q, q + len(groups[0]) <= len(nums), and nums[q + j] = groups[0][j] for all j, while for every i with 1 <= i < n, s_i is the least q with s_{i-1} + len(groups[i-1]) <= q, q + len(groups[i]) <= len(nums), and nums[q + j] = groups[i][j] for all j.
  Preconditions: Let n = len(groups). Assume 1 <= n <= 1000; for every i with 0 <= i < n, 1 <= len(groups[i]); sum_{i=0}^{n-1} len(groups[i]) <= 1000; 1 <= len(nums) <= 1000; and for every valid i, j, k, -10^7 <= groups[i][j] <= 10^7 and -10^7 <= nums[k] <= 10^7. -/
theorem spec_14
    (groups : Groups) (nums : Nums)
    (h_n_pos : 1 ≤ groups.val.length) (h_n_le : groups.val.length ≤ 1000)
    (h_glen_pos : ∀ i, i < groups.val.length → 1 ≤ glen groups i)
    (h_sum_le : gtotal groups ≤ 1000)
    (h_m_pos : 1 ≤ nums.val.length) (h_m_le : nums.val.length ≤ 1000)
    (h_g_bound : ∀ i, i < groups.val.length → ∀ j, j < glen groups i →
      -(10 ^ 7) ≤ gcell groups i j ∧ gcell groups i j ≤ 10 ^ 7)
    (h_n_bound : ∀ k, k < nums.val.length →
      -(10 ^ 7) ≤ nth nums k ∧ nth nums k ≤ 10 ^ 7) :
    Aegis.CanChoose.can_choose groups nums = ok true →
      ∃ s, Places groups nums s ∧
        (∀ q, q + glen groups 0 ≤ nums.val.length →
          (∀ j, j < glen groups 0 → nth nums (q + j) = gcell groups 0 j) → s 0 ≤ q) ∧
        (∀ i, 1 ≤ i → i < groups.val.length →
          ∀ q, s (i - 1) + glen groups (i - 1) ≤ q → q + glen groups i ≤ nums.val.length →
            (∀ j, j < glen groups i → nth nums (q + j) = gcell groups i j) → s i ≤ q) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (groups : Groups) (nums : Nums)
    (h_n_pos : 1 ≤ groups.val.length) (h_n_le : groups.val.length ≤ 1000)
    (h_glen_pos : ∀ i, i < groups.val.length → 1 ≤ glen groups i)
    (h_sum_le : gtotal groups ≤ 1000)
    (h_m_pos : 1 ≤ nums.val.length) (h_m_le : nums.val.length ≤ 1000)
    (h_g_bound : ∀ i, i < groups.val.length → ∀ j, j < glen groups i →
      -(10 ^ 7) ≤ gcell groups i j ∧ gcell groups i j ≤ 10 ^ 7)
    (h_n_bound : ∀ k, k < nums.val.length →
      -(10 ^ 7) ≤ nth nums k ∧ nth nums k ≤ 10 ^ 7), Aegis.CanChoose.can_choose groups nums = ok true →
      ∃ s, Places groups nums s ∧
        (∀ q, q + glen groups 0 ≤ nums.val.length →
          (∀ j, j < glen groups 0 → nth nums (q + j) = gcell groups 0 j) → s 0 ≤ q) ∧
        (∀ i, 1 ≤ i → i < groups.val.length →
          ∀ q, s (i - 1) + glen groups (i - 1) ≤ q → q + glen groups i ≤ nums.val.length →
            (∀ j, j < glen groups i → nth nums (q + j) = gcell groups i j) → s i ≤ q)) := by
  sorry

/-- Whenever can_choose(groups, nums) returns a result r with r = true, for every k with 1 <= k <= n, can_choose(groups[0..k], nums) returns a result r_k with r_k = true, where groups[0..k] denotes the prefix consisting of the first k groups.
  Preconditions: Let n = len(groups). Assume 1 <= n <= 1000; for every i with 0 <= i < n, 1 <= len(groups[i]); sum_{i=0}^{n-1} len(groups[i]) <= 1000; 1 <= len(nums) <= 1000; and for every valid i, j, k, -10^7 <= groups[i][j] <= 10^7 and -10^7 <= nums[k] <= 10^7. -/
theorem spec_15
    (groups : Groups) (nums : Nums)
    (h_n_pos : 1 ≤ groups.val.length) (h_n_le : groups.val.length ≤ 1000)
    (h_glen_pos : ∀ i, i < groups.val.length → 1 ≤ glen groups i)
    (h_sum_le : gtotal groups ≤ 1000)
    (h_m_pos : 1 ≤ nums.val.length) (h_m_le : nums.val.length ≤ 1000)
    (h_g_bound : ∀ i, i < groups.val.length → ∀ j, j < glen groups i →
      -(10 ^ 7) ≤ gcell groups i j ∧ gcell groups i j ≤ 10 ^ 7)
    (h_n_bound : ∀ k, k < nums.val.length →
      -(10 ^ 7) ≤ nth nums k ∧ nth nums k ≤ 10 ^ 7) :
    Aegis.CanChoose.can_choose groups nums = ok true →
      ∀ (k : ℕ) (h_k_pos : 1 ≤ k) (h_k_le : k ≤ groups.val.length),
        ∃ r_k, Aegis.CanChoose.can_choose
            (mkGroups (groups.val.take k) (by rw [List.length_take]; omega)) nums = ok r_k ∧
          r_k = true := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (groups : Groups) (nums : Nums)
    (h_n_pos : 1 ≤ groups.val.length) (h_n_le : groups.val.length ≤ 1000)
    (h_glen_pos : ∀ i, i < groups.val.length → 1 ≤ glen groups i)
    (h_sum_le : gtotal groups ≤ 1000)
    (h_m_pos : 1 ≤ nums.val.length) (h_m_le : nums.val.length ≤ 1000)
    (h_g_bound : ∀ i, i < groups.val.length → ∀ j, j < glen groups i →
      -(10 ^ 7) ≤ gcell groups i j ∧ gcell groups i j ≤ 10 ^ 7)
    (h_n_bound : ∀ k, k < nums.val.length →
      -(10 ^ 7) ≤ nth nums k ∧ nth nums k ≤ 10 ^ 7), Aegis.CanChoose.can_choose groups nums = ok true →
      ∀ (k : ℕ) (h_k_pos : 1 ≤ k) (h_k_le : k ≤ groups.val.length),
        ∃ r_k, Aegis.CanChoose.can_choose
            (mkGroups (groups.val.take k) (by rw [List.length_take]; omega)) nums = ok r_k ∧
          r_k = true) := by
  sorry

end AegisSpec.CanChoose
