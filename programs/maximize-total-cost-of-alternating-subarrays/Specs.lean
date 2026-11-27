import Aegis.MaximumTotalCost.Code.Funs

/-!
# Specifications of `Aegis.MaximumTotalCost.maximum_total_cost`

LeetCode problem `maximize-total-cost-of-alternating-subarrays`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaximumTotalCost

open Aegis.MaximumTotalCost

def content (nums : Slice Std.I64) : List ℤ := nums.val.map (fun x => x.val)

def altSum (xs : List ℤ) : ℤ :=
  ((List.range xs.length).map (fun i => (-1 : ℤ) ^ i * xs.getD i 0)).sum

def absSum (xs : List ℤ) : ℤ := (xs.map fun x => |x|).sum

def segCost (xs : List ℤ) (l r : ℕ) : ℤ :=
  ((List.range (r + 1 - l)).map (fun k => (-1 : ℤ) ^ k * xs.getD (l + k) 0)).sum

def segmentsOf (rs : List ℕ) : List (ℕ × ℕ) := (0 :: rs.map (fun r => r + 1)).zip rs

def IsValidSplit (n : ℕ) (rs : List ℕ) : Prop :=
  rs ≠ [] ∧ rs.Pairwise (· < ·) ∧ (∀ r ∈ rs, r < n) ∧ rs.getLast? = some (n - 1)

def splitCost (xs : List ℤ) (rs : List ℕ) : ℤ :=
  ((segmentsOf rs).map (fun p => segCost xs p.1 p.2)).sum

def IsMaxSplitCost (xs : List ℤ) (s : ℤ) : Prop :=
  (∀ rs, IsValidSplit xs.length rs → splitCost xs rs ≤ s) ∧
    ∃ rs, IsValidSplit xs.length rs ∧ splitCost xs rs = s

def IsIndepSet (n : ℕ) (S : Finset ℕ) : Prop :=
  (∀ i ∈ S, 1 ≤ i ∧ i < n) ∧ ∀ i ∈ S, i + 1 ∉ S

def indepBonus (xs : List ℤ) (S : Finset ℕ) : ℤ := S.sum (fun i => max 0 (-(xs.getD i 0)))

def IsMaxIndepBonus (xs : List ℤ) (M : ℤ) : Prop :=
  (∀ S : Finset ℕ, IsIndepSet xs.length S → indepBonus xs S ≤ M) ∧
    ∃ S : Finset ℕ, IsIndepSet xs.length S ∧ indepBonus xs S = M

def dpStep (p : ℤ) (q : Option ℤ) (x : ℤ) : ℤ × Option ℤ :=
  (q.elim p (fun q => max p q) + x, some (p - x))

def dpRun (xs : List ℤ) : ℕ → ℤ × Option ℤ
  | 0 => (xs.getD 0 0, none)
  | k + 1 => dpStep (dpRun xs k).1 (dpRun xs k).2 (xs.getD (k + 1) 0)

def prefP (xs : List ℤ) (i : ℕ) : ℤ := (dpRun xs i).1

def prefQ (xs : List ℤ) (i : ℕ) : Option ℤ := (dpRun xs i).2

def dpResult (xs : List ℤ) (i : ℕ) : ℤ :=
  match prefQ xs i with
  | none => prefP xs i
  | some q => max (prefP xs i) q

/-- Whenever maximum_total_cost(nums) returns a result r, r is the maximum total cost over all valid splits of nums. A valid split is a sequence of nonempty contiguous subarrays [l_0,r_0],...,[l_{k-1},r_{k-1}] with k >= 1, l_0 = 0, r_{k-1} = len(nums)-1, and l_{j+1} = r_j + 1 for all j < k-1. The cost of a subarray [l,r] is cost(l,r) = sum_{j=l}^{r} (-1)^(j-l) * nums[j] = nums[l] - nums[l+1] + ... + (-1)^(r-l) * nums[r]. The total cost of the split is the sum of cost(l_j,r_j) over j = 0,...,k-1.
  Preconditions: 1 <= len(nums) <= 10^5 and for every i with 0 <= i < len(nums), -10^9 <= nums[i] <= 10^9. -/
theorem spec_1 (nums : Slice Std.I64)
    (h_len_lb : 1 ≤ nums.val.length) (h_len_ub : nums.val.length ≤ 10 ^ 5)
    (h_bounds : ∀ (i : ℕ) (hi : i < nums.val.length),
      -(10 ^ 9 : ℤ) ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 9) :
    ∀ r, maximum_total_cost nums = ok r → IsMaxSplitCost (content nums) r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_lb : 1 ≤ nums.val.length) (h_len_ub : nums.val.length ≤ 10 ^ 5)
    (h_bounds : ∀ (i : ℕ) (hi : i < nums.val.length),
      -(10 ^ 9 : ℤ) ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 9), ∀ r, maximum_total_cost nums = ok r → IsMaxSplitCost (content nums) r.val) := by
  sorry

/-- For every nums satisfying the preconditions, maximum_total_cost(nums) returns a result; it does not fail, panic, or overflow.
  Preconditions: 1 <= len(nums) <= 10^5 and for every i with 0 <= i < len(nums), -10^9 <= nums[i] <= 10^9. -/
theorem spec_2 (nums : Slice Std.I64)
    (h_len_lb : 1 ≤ nums.val.length) (h_len_ub : nums.val.length ≤ 10 ^ 5)
    (h_bounds : ∀ (i : ℕ) (hi : i < nums.val.length),
      -(10 ^ 9 : ℤ) ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 9) :
    ∃ r, maximum_total_cost nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_lb : 1 ≤ nums.val.length) (h_len_ub : nums.val.length ≤ 10 ^ 5)
    (h_bounds : ∀ (i : ℕ) (hi : i < nums.val.length),
      -(10 ^ 9 : ℤ) ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 9), ∃ r, maximum_total_cost nums = ok r) := by
  sorry

/-- Whenever maximum_total_cost(nums) returns a result r, r >= sum_{i=0}^{len(nums)-1} nums[i]. This lower bound is the total cost of the valid split into the len(nums) singleton subarrays [0,0],[1,1],...,[len(nums)-1,len(nums)-1].
  Preconditions: 1 <= len(nums) <= 10^5 and for every i with 0 <= i < len(nums), -10^9 <= nums[i] <= 10^9. -/
theorem spec_3 (nums : Slice Std.I64)
    (h_len_lb : 1 ≤ nums.val.length) (h_len_ub : nums.val.length ≤ 10 ^ 5)
    (h_bounds : ∀ (i : ℕ) (hi : i < nums.val.length),
      -(10 ^ 9 : ℤ) ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 9) :
    ∀ r, maximum_total_cost nums = ok r → (content nums).sum ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_lb : 1 ≤ nums.val.length) (h_len_ub : nums.val.length ≤ 10 ^ 5)
    (h_bounds : ∀ (i : ℕ) (hi : i < nums.val.length),
      -(10 ^ 9 : ℤ) ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 9), ∀ r, maximum_total_cost nums = ok r → (content nums).sum ≤ r.val) := by
  sorry

/-- Whenever maximum_total_cost(nums) returns a result r, r >= sum_{i=0}^{len(nums)-1} (-1)^i * nums[i], which is the cost of the single subarray [0,len(nums)-1].
  Preconditions: 1 <= len(nums) <= 10^5 and for every i with 0 <= i < len(nums), -10^9 <= nums[i] <= 10^9. -/
theorem spec_4 (nums : Slice Std.I64)
    (h_len_lb : 1 ≤ nums.val.length) (h_len_ub : nums.val.length ≤ 10 ^ 5)
    (h_bounds : ∀ (i : ℕ) (hi : i < nums.val.length),
      -(10 ^ 9 : ℤ) ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 9) :
    ∀ r, maximum_total_cost nums = ok r → altSum (content nums) ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_lb : 1 ≤ nums.val.length) (h_len_ub : nums.val.length ≤ 10 ^ 5)
    (h_bounds : ∀ (i : ℕ) (hi : i < nums.val.length),
      -(10 ^ 9 : ℤ) ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 9), ∀ r, maximum_total_cost nums = ok r → altSum (content nums) ≤ r.val) := by
  sorry

/-- Whenever maximum_total_cost(nums) returns a result r, r <= sum_{i=0}^{len(nums)-1} |nums[i]|, where |x| is the usual absolute value.
  Preconditions: 1 <= len(nums) <= 10^5 and for every i with 0 <= i < len(nums), -10^9 <= nums[i] <= 10^9. -/
theorem spec_5 (nums : Slice Std.I64)
    (h_len_lb : 1 ≤ nums.val.length) (h_len_ub : nums.val.length ≤ 10 ^ 5)
    (h_bounds : ∀ (i : ℕ) (hi : i < nums.val.length),
      -(10 ^ 9 : ℤ) ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 9) :
    ∀ r, maximum_total_cost nums = ok r → r.val ≤ absSum (content nums) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_lb : 1 ≤ nums.val.length) (h_len_ub : nums.val.length ≤ 10 ^ 5)
    (h_bounds : ∀ (i : ℕ) (hi : i < nums.val.length),
      -(10 ^ 9 : ℤ) ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 9), ∀ r, maximum_total_cost nums = ok r → r.val ≤ absSum (content nums)) := by
  sorry

/-- Whenever maximum_total_cost(nums) returns a result r, r = nums[0] + |nums[1]|.
  Preconditions: len(nums) = 2 and for every i with 0 <= i < 2, -10^9 <= nums[i] <= 10^9. -/
theorem spec_6 (nums : Slice Std.I64)
    (h_len : nums.val.length = 2)
    (h_bounds : ∀ (i : ℕ) (hi : i < nums.val.length),
      -(10 ^ 9 : ℤ) ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 9) :
    ∀ r, maximum_total_cost nums = ok r → r.val = (nums.val[0]).val + |(nums.val[1]).val| := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len : nums.val.length = 2)
    (h_bounds : ∀ (i : ℕ) (hi : i < nums.val.length),
      -(10 ^ 9 : ℤ) ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 9), ∀ r, maximum_total_cost nums = ok r → r.val = (nums.val[0]).val + |(nums.val[1]).val|) := by
  sorry

/-- Whenever maximum_total_cost(nums) returns a result r, r = sum_{i=0}^{len(nums)-1} nums[i].
  Preconditions: 1 <= len(nums) <= 10^5 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 10^9. -/
theorem spec_7 (nums : Slice Std.I64)
    (h_len_lb : 1 ≤ nums.val.length) (h_len_ub : nums.val.length ≤ 10 ^ 5)
    (h_bounds : ∀ (i : ℕ) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 9) :
    ∀ r, maximum_total_cost nums = ok r → r.val = (content nums).sum := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_lb : 1 ≤ nums.val.length) (h_len_ub : nums.val.length ≤ 10 ^ 5)
    (h_bounds : ∀ (i : ℕ) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 9), ∀ r, maximum_total_cost nums = ok r → r.val = (content nums).sum) := by
  sorry

/-- Whenever maximum_total_cost(nums) returns a result r, r = nums[0].
  Preconditions: 1 <= len(nums) <= 10^5, -10^9 <= nums[0] <= 10^9, and for every i with 1 <= i < len(nums), nums[i] = 0. -/
theorem spec_8 (nums : Slice Std.I64)
    (h_len_lb : 1 ≤ nums.val.length) (h_len_ub : nums.val.length ≤ 10 ^ 5)
    (h_head : -(10 ^ 9 : ℤ) ≤ (nums.val[0]).val ∧ (nums.val[0]).val ≤ 10 ^ 9)
    (h_rest : ∀ (i : ℕ) (hi : 1 ≤ i) (hi' : i < nums.val.length), (nums.val[i]).val = 0) :
    ∀ r, maximum_total_cost nums = ok r → r.val = (nums.val[0]).val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_lb : 1 ≤ nums.val.length) (h_len_ub : nums.val.length ≤ 10 ^ 5)
    (h_head : -(10 ^ 9 : ℤ) ≤ (nums.val[0]).val ∧ (nums.val[0]).val ≤ 10 ^ 9)
    (h_rest : ∀ (i : ℕ) (hi : 1 ≤ i) (hi' : i < nums.val.length), (nums.val[i]).val = 0), ∀ r, maximum_total_cost nums = ok r → r.val = (nums.val[0]).val) := by
  sorry

/-- Whenever maximum_total_cost(nums) returns a result r, the integer r - sum_{i=0}^{len(nums)-1} nums[i] is even; equivalently, r and sum_{i=0}^{len(nums)-1} nums[i] have the same parity.
  Preconditions: 1 <= len(nums) <= 10^5 and for every i with 0 <= i < len(nums), -10^9 <= nums[i] <= 10^9. -/
theorem spec_9 (nums : Slice Std.I64)
    (h_len_lb : 1 ≤ nums.val.length) (h_len_ub : nums.val.length ≤ 10 ^ 5)
    (h_bounds : ∀ (i : ℕ) (hi : i < nums.val.length),
      -(10 ^ 9 : ℤ) ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 9) :
    ∀ r, maximum_total_cost nums = ok r → Even (r.val - (content nums).sum) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_lb : 1 ≤ nums.val.length) (h_len_ub : nums.val.length ≤ 10 ^ 5)
    (h_bounds : ∀ (i : ℕ) (hi : i < nums.val.length),
      -(10 ^ 9 : ℤ) ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 9), ∀ r, maximum_total_cost nums = ok r → Even (r.val - (content nums).sum)) := by
  sorry

/-- Whenever maximum_total_cost(nums) returns a result r and maximum_total_cost(nums') returns a result r', we have r' = r + c.
  Preconditions: nums and nums' both satisfy 1 <= len <= 10^5 and all entries between -10^9 and 10^9. len(nums') = len(nums), nums'[0] = nums[0] + c for some integer c, and nums'[i] = nums[i] for every i with 1 <= i < len(nums). -/
theorem spec_10 (nums nums' : Slice Std.I64) (c : ℤ)
    (h_len_lb : 1 ≤ nums.val.length) (h_len_ub : nums.val.length ≤ 10 ^ 5)
    (h_bounds : ∀ (i : ℕ) (hi : i < nums.val.length),
      -(10 ^ 9 : ℤ) ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 9)
    (h_len_lb' : 1 ≤ nums'.val.length) (h_len_ub' : nums'.val.length ≤ 10 ^ 5)
    (h_bounds' : ∀ (i : ℕ) (hi : i < nums'.val.length),
      -(10 ^ 9 : ℤ) ≤ (nums'.val[i]).val ∧ (nums'.val[i]).val ≤ 10 ^ 9)
    (h_same_len : nums'.val.length = nums.val.length)
    (h_head : (nums'.val[0]).val = (nums.val[0]).val + c)
    (h_tail : ∀ (i : ℕ) (hi : 1 ≤ i) (hi' : i < nums.val.length),
      (nums'.val[i]).val = (nums.val[i]).val) :
    ∀ r r', maximum_total_cost nums = ok r → maximum_total_cost nums' = ok r' →
      r'.val = r.val + c := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (c : ℤ)
    (h_len_lb : 1 ≤ nums.val.length) (h_len_ub : nums.val.length ≤ 10 ^ 5)
    (h_bounds : ∀ (i : ℕ) (hi : i < nums.val.length),
      -(10 ^ 9 : ℤ) ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 9)
    (h_len_lb' : 1 ≤ nums'.val.length) (h_len_ub' : nums'.val.length ≤ 10 ^ 5)
    (h_bounds' : ∀ (i : ℕ) (hi : i < nums'.val.length),
      -(10 ^ 9 : ℤ) ≤ (nums'.val[i]).val ∧ (nums'.val[i]).val ≤ 10 ^ 9)
    (h_same_len : nums'.val.length = nums.val.length)
    (h_head : (nums'.val[0]).val = (nums.val[0]).val + c)
    (h_tail : ∀ (i : ℕ) (hi : 1 ≤ i) (hi' : i < nums.val.length),
      (nums'.val[i]).val = (nums.val[i]).val), ∀ r r', maximum_total_cost nums = ok r → maximum_total_cost nums' = ok r' →
      r'.val = r.val + c) := by
  sorry

/-- Whenever maximum_total_cost(nums) returns a result r and maximum_total_cost(B) returns a result r_B, we have r_B = c * r.
  Preconditions: nums satisfies 1 <= len(nums) <= 10^5 and all entries between -10^9 and 10^9. Let B be the same-length array with B[i] = c * nums[i] for every i, where c is a nonnegative integer and every B[i] satisfies -10^9 <= B[i] <= 10^9. -/
theorem spec_11 (nums numsB : Slice Std.I64) (c : ℤ)
    (h_len_lb : 1 ≤ nums.val.length) (h_len_ub : nums.val.length ≤ 10 ^ 5)
    (h_bounds : ∀ (i : ℕ) (hi : i < nums.val.length),
      -(10 ^ 9 : ℤ) ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 9)
    (h_c_nonneg : 0 ≤ c)
    (h_same_len : numsB.val.length = nums.val.length)
    (h_scale : ∀ (i : ℕ) (hi : i < nums.val.length),
      (numsB.val[i]).val = c * (nums.val[i]).val)
    (h_boundsB : ∀ (i : ℕ) (hi : i < numsB.val.length),
      -(10 ^ 9 : ℤ) ≤ (numsB.val[i]).val ∧ (numsB.val[i]).val ≤ 10 ^ 9) :
    ∀ r rB, maximum_total_cost nums = ok r → maximum_total_cost numsB = ok rB →
      rB.val = c * r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums numsB : Slice Std.I64) (c : ℤ)
    (h_len_lb : 1 ≤ nums.val.length) (h_len_ub : nums.val.length ≤ 10 ^ 5)
    (h_bounds : ∀ (i : ℕ) (hi : i < nums.val.length),
      -(10 ^ 9 : ℤ) ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 9)
    (h_c_nonneg : 0 ≤ c)
    (h_same_len : numsB.val.length = nums.val.length)
    (h_scale : ∀ (i : ℕ) (hi : i < nums.val.length),
      (numsB.val[i]).val = c * (nums.val[i]).val)
    (h_boundsB : ∀ (i : ℕ) (hi : i < numsB.val.length),
      -(10 ^ 9 : ℤ) ≤ (numsB.val[i]).val ∧ (numsB.val[i]).val ≤ 10 ^ 9), ∀ r rB, maximum_total_cost nums = ok r → maximum_total_cost numsB = ok rB →
      rB.val = c * r.val) := by
  sorry

/-- Whenever maximum_total_cost(nums) returns a result r and maximum_total_cost(nums') returns a result r', we have r' = r.
  Preconditions: nums satisfies 1 <= len(nums) <= 99999 and all entries between -10^9 and 10^9. Let nums' be the length len(nums)+1 array with nums'[i] = nums[i] for 0 <= i < len(nums) and nums'[len(nums)] = 0. -/
theorem spec_12 (nums nums' : Slice Std.I64)
    (h_len_lb : 1 ≤ nums.val.length) (h_len_ub : nums.val.length ≤ 99999)
    (h_bounds : ∀ (i : ℕ) (hi : i < nums.val.length),
      -(10 ^ 9 : ℤ) ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 9)
    (h_len' : nums'.val.length = nums.val.length + 1)
    (h_prefix : ∀ (i : ℕ) (hi : i < nums.val.length), (nums'.val[i]).val = (nums.val[i]).val)
    (h_last : (nums'.val[nums.val.length]).val = 0) :
    ∀ r r', maximum_total_cost nums = ok r → maximum_total_cost nums' = ok r' →
      r'.val = r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums nums' : Slice Std.I64)
    (h_len_lb : 1 ≤ nums.val.length) (h_len_ub : nums.val.length ≤ 99999)
    (h_bounds : ∀ (i : ℕ) (hi : i < nums.val.length),
      -(10 ^ 9 : ℤ) ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 9)
    (h_len' : nums'.val.length = nums.val.length + 1)
    (h_prefix : ∀ (i : ℕ) (hi : i < nums.val.length), (nums'.val[i]).val = (nums.val[i]).val)
    (h_last : (nums'.val[nums.val.length]).val = 0), ∀ r r', maximum_total_cost nums = ok r → maximum_total_cost nums' = ok r' →
      r'.val = r.val) := by
  sorry

/-- Whenever maximum_total_cost(nums) returns a result r, the following holds: if a >= 0 then r = len(nums) * a; if a < 0 and len(nums) is even then r = 0; if a < 0 and len(nums) is odd then r = a.
  Preconditions: 1 <= len(nums) <= 10^5, there is an integer a with nums[i] = a for every i with 0 <= i < len(nums), and -10^9 <= a <= 10^9. -/
theorem spec_13 (nums : Slice Std.I64) (a : ℤ)
    (h_len_lb : 1 ≤ nums.val.length) (h_len_ub : nums.val.length ≤ 10 ^ 5)
    (h_const : ∀ (i : ℕ) (hi : i < nums.val.length), (nums.val[i]).val = a)
    (h_a_lb : -(10 ^ 9 : ℤ) ≤ a) (h_a_ub : a ≤ 10 ^ 9) :
    ∀ r, maximum_total_cost nums = ok r →
      (0 ≤ a → r.val = (nums.val.length : ℤ) * a) ∧
      (a < 0 → Even nums.val.length → r.val = 0) ∧
      (a < 0 → Odd nums.val.length → r.val = a) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums : Slice Std.I64) (a : ℤ)
    (h_len_lb : 1 ≤ nums.val.length) (h_len_ub : nums.val.length ≤ 10 ^ 5)
    (h_const : ∀ (i : ℕ) (hi : i < nums.val.length), (nums.val[i]).val = a)
    (h_a_lb : -(10 ^ 9 : ℤ) ≤ a) (h_a_ub : a ≤ 10 ^ 9), ∀ r, maximum_total_cost nums = ok r →
      (0 ≤ a → r.val = (nums.val.length : ℤ) * a) ∧
      (a < 0 → Even nums.val.length → r.val = 0) ∧
      (a < 0 → Odd nums.val.length → r.val = a)) := by
  sorry

/-- Whenever maximum_total_cost(nums) returns a result r, r >= nums[0] + |nums[1]| + sum_{i=2}^{len(nums)-1} nums[i].
  Preconditions: 2 <= len(nums) <= 10^5 and for every i with 0 <= i < len(nums), -10^9 <= nums[i] <= 10^9. -/
theorem spec_14 (nums : Slice Std.I64)
    (h_len_lb : 2 ≤ nums.val.length) (h_len_ub : nums.val.length ≤ 10 ^ 5)
    (h_bounds : ∀ (i : ℕ) (hi : i < nums.val.length),
      -(10 ^ 9 : ℤ) ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 9) :
    ∀ r, maximum_total_cost nums = ok r →
      (nums.val[0]).val + |(nums.val[1]).val| + ((content nums).drop 2).sum ≤ r.val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_lb : 2 ≤ nums.val.length) (h_len_ub : nums.val.length ≤ 10 ^ 5)
    (h_bounds : ∀ (i : ℕ) (hi : i < nums.val.length),
      -(10 ^ 9 : ℤ) ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 9), ∀ r, maximum_total_cost nums = ok r →
      (nums.val[0]).val + |(nums.val[1]).val| + ((content nums).drop 2).sum ≤ r.val) := by
  sorry

/-- Whenever maximum_total_cost(nums) returns a result r, let n=len(nums), T=sum_{i=0}^{n-1} nums[i], and let M be the maximum of sum_{i in S} max(0, -nums[i]) over all finite sets S subset of {i | 1 <= i < n} that contain no two consecutive integers (the empty set is allowed). Then r = T + 2*M.
  Preconditions: 1 <= len(nums) <= 10^5 and for every i with 0 <= i < len(nums), -10^9 <= nums[i] <= 10^9. -/
theorem spec_15 (nums : Slice Std.I64)
    (h_len_lb : 1 ≤ nums.val.length) (h_len_ub : nums.val.length ≤ 10 ^ 5)
    (h_bounds : ∀ (i : ℕ) (hi : i < nums.val.length),
      -(10 ^ 9 : ℤ) ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 9) :
    ∀ r, maximum_total_cost nums = ok r →
      ∀ M : ℤ, IsMaxIndepBonus (content nums) M →
        r.val = (content nums).sum + 2 * M := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_lb : 1 ≤ nums.val.length) (h_len_ub : nums.val.length ≤ 10 ^ 5)
    (h_bounds : ∀ (i : ℕ) (hi : i < nums.val.length),
      -(10 ^ 9 : ℤ) ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 9), ∀ r, maximum_total_cost nums = ok r →
      ∀ M : ℤ, IsMaxIndepBonus (content nums) M →
        r.val = (content nums).sum + 2 * M) := by
  sorry

/-- Whenever maximum_total_cost(nums) returns a result r, let n=len(nums). For 0 <= i < n let P_i be the maximum total cost over valid splits of the prefix nums[0..i] in which nums[i] has coefficient +1, and let Q_i be the analogous maximum in which nums[i] has coefficient -1 (Q_0 is undefined). Then P_0=nums[0] and, for 1 <= i < n, P_i = max(P_{i-1}, Q_{i-1}) + nums[i] and Q_i = P_{i-1} - nums[i] (ignoring an undefined value in the max); finally r = max(P_{n-1}, Q_{n-1}) (ignoring an undefined value).
  Preconditions: 1 <= len(nums) <= 10^5 and for every i with 0 <= i < len(nums), -10^9 <= nums[i] <= 10^9. -/
theorem spec_16 (nums : Slice Std.I64)
    (h_len_lb : 1 ≤ nums.val.length) (h_len_ub : nums.val.length ≤ 10 ^ 5)
    (h_bounds : ∀ (i : ℕ) (hi : i < nums.val.length),
      -(10 ^ 9 : ℤ) ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 9) :
    ∀ r, maximum_total_cost nums = ok r →
      r.val = dpResult (content nums) (nums.val.length - 1) := by
  sorry

theorem spec_16_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_lb : 1 ≤ nums.val.length) (h_len_ub : nums.val.length ≤ 10 ^ 5)
    (h_bounds : ∀ (i : ℕ) (hi : i < nums.val.length),
      -(10 ^ 9 : ℤ) ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 9), ∀ r, maximum_total_cost nums = ok r →
      r.val = dpResult (content nums) (nums.val.length - 1)) := by
  sorry

/-- Whenever maximum_total_cost(nums) returns a result r, r <= nums[0] + sum_{i=1}^{len(nums)-1} |nums[i]|.
  Preconditions: 1 <= len(nums) <= 10^5 and for every i with 0 <= i < len(nums), -10^9 <= nums[i] <= 10^9. -/
theorem spec_17 (nums : Slice Std.I64)
    (h_len_lb : 1 ≤ nums.val.length) (h_len_ub : nums.val.length ≤ 10 ^ 5)
    (h_bounds : ∀ (i : ℕ) (hi : i < nums.val.length),
      -(10 ^ 9 : ℤ) ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 9) :
    ∀ r, maximum_total_cost nums = ok r →
      r.val ≤ (nums.val[0]).val + absSum ((content nums).drop 1) := by
  sorry

theorem spec_17_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_lb : 1 ≤ nums.val.length) (h_len_ub : nums.val.length ≤ 10 ^ 5)
    (h_bounds : ∀ (i : ℕ) (hi : i < nums.val.length),
      -(10 ^ 9 : ℤ) ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 9), ∀ r, maximum_total_cost nums = ok r →
      r.val ≤ (nums.val[0]).val + absSum ((content nums).drop 1)) := by
  sorry

end AegisSpec.MaximumTotalCost
