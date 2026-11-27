import Aegis.MaxSubarrays.Code.Funs

/-!
# Specifications of `Aegis.MaxSubarrays.max_subarrays`

LeetCode problem `split-array-into-maximum-number-of-subarrays`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MaxSubarrays

namespace AegisSpec.MaxSubarrays

def vals (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

def band (a b : Int) : Int := (BitVec.ofInt 64 a &&& BitVec.ofInt 64 b).toInt

def segAnd (l : List Int) (lo hi : Nat) : Int :=
  ((l.drop lo).take (hi - lo)).foldl band (-1)

def fullAnd (l : List Int) : Int := segAnd l 0 l.length

def partAnds (l : List Int) (p : List Nat) : List Int :=
  (p.zip p.tail).map (fun q => segAnd l q.1 q.2)

def splitCost (l : List Int) (p : List Nat) : Int := (partAnds l p).sum

def IsSplit (n k : Nat) (p : List Nat) : Prop :=
  p.length = k + 1 ∧ p.head? = some 0 ∧ p.getLast? = some n ∧ p.Pairwise (· < ·)

def IsMinCost (l : List Int) (C : Int) : Prop :=
  (∃ k p, IsSplit l.length k p ∧ splitCost l p = C) ∧
    ∀ k p, IsSplit l.length k p → C ≤ splitCost l p

/-- For 0 <= l <= r < n let AND(l,r) denote the bitwise AND nums[l] & nums[l+1] & ... & nums[r]. A split into k >= 1 subarrays is a choice of indices 0 = p_0 < p_1 < ... < p_k = n, whose parts are nums[p_t .. p_{t+1}-1] for t = 0..k-1; the cost of such a split is the sum over t = 0..k-1 of AND(p_t, p_{t+1}-1). Let C be the minimum cost over all splits (the set is nonempty because the one-part split p_0 = 0, p_1 = n always exists). The function returns a result r such that r is the largest k for which some split into k subarrays has cost C; equivalently (i) there exists a split into r subarrays with cost C, and (ii) for every split into k subarrays with cost C, k <= r.
  Preconditions: Let n = len(nums). The parameters satisfy 1 <= n <= 100000 and 0 <= nums[i] <= 1000000 for every integer i with 0 <= i < n. -/
theorem spec_1 (nums : Slice Std.I64)
    (hn : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hb : ∀ i, i < nums.val.length → 0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000)
    (C : Int) (hC : IsMinCost (vals nums) C) :
    ∃ r, max_subarrays nums = Std.Result.ok r ∧
      (∃ k p, IsSplit (vals nums).length k p ∧ splitCost (vals nums) p = C ∧
        r.val = (k : Int)) ∧
      (∀ k p, IsSplit (vals nums).length k p → splitCost (vals nums) p = C →
        (k : Int) ≤ r.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hb : ∀ i, i < nums.val.length → 0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000)
    (C : Int) (hC : IsMinCost (vals nums) C), ∃ r, max_subarrays nums = Std.Result.ok r ∧
      (∃ k p, IsSplit (vals nums).length k p ∧ splitCost (vals nums) p = C ∧
        r.val = (k : Int)) ∧
      (∀ k p, IsSplit (vals nums).length k p → splitCost (vals nums) p = C →
        (k : Int) ≤ r.val)) := by
  sorry

/-- Let M = nums[0] & nums[1] & ... & nums[n-1] (the bitwise AND of all elements; well defined since n >= 1). If M != 0 then the function returns r = 1.
  Preconditions: Let n = len(nums). The parameters satisfy 1 <= n <= 100000 and 0 <= nums[i] <= 1000000 for every integer i with 0 <= i < n. -/
theorem spec_2 (nums : Slice Std.I64)
    (hn : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hb : ∀ i, i < nums.val.length → 0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000)
    (hM : fullAnd (vals nums) ≠ 0) :
    ∃ r, max_subarrays nums = Std.Result.ok r ∧ r.val = 1 := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hb : ∀ i, i < nums.val.length → 0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000)
    (hM : fullAnd (vals nums) ≠ 0), ∃ r, max_subarrays nums = Std.Result.ok r ∧ r.val = 1) := by
  sorry

/-- Let M = nums[0] & nums[1] & ... & nums[n-1]. If M = 0 then the function returns r equal to the largest k such that there exist indices 0 = p_0 < p_1 < ... < p_k = n with, for every t = 0..k-1, the bitwise AND of nums[p_t], nums[p_t+1], ..., nums[p_{t+1}-1] equal to 0. That is, r is the maximum number of contiguous nonempty subarrays in a partition of the whole array such that every subarray has bitwise AND 0.
  Preconditions: Let n = len(nums). The parameters satisfy 1 <= n <= 100000 and 0 <= nums[i] <= 1000000 for every integer i with 0 <= i < n. -/
theorem spec_3 (nums : Slice Std.I64)
    (hn : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hb : ∀ i, i < nums.val.length → 0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000)
    (hM : fullAnd (vals nums) = 0) :
    ∃ r, max_subarrays nums = Std.Result.ok r ∧
      (∃ k p, IsSplit (vals nums).length k p ∧
        (∀ x, x ∈ partAnds (vals nums) p → x = 0) ∧ r.val = (k : Int)) ∧
      (∀ k p, IsSplit (vals nums).length k p →
        (∀ x, x ∈ partAnds (vals nums) p → x = 0) → (k : Int) ≤ r.val) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hb : ∀ i, i < nums.val.length → 0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000)
    (hM : fullAnd (vals nums) = 0), ∃ r, max_subarrays nums = Std.Result.ok r ∧
      (∃ k p, IsSplit (vals nums).length k p ∧
        (∀ x, x ∈ partAnds (vals nums) p → x = 0) ∧ r.val = (k : Int)) ∧
      (∀ k p, IsSplit (vals nums).length k p →
        (∀ x, x ∈ partAnds (vals nums) p → x = 0) → (k : Int) ≤ r.val)) := by
  sorry

/-- The function returns r with r >= 1.
  Preconditions: Let n = len(nums). The parameters satisfy 1 <= n <= 100000 and 0 <= nums[i] <= 1000000 for every integer i with 0 <= i < n. -/
theorem spec_4 (nums : Slice Std.I64)
    (hn : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hb : ∀ i, i < nums.val.length → 0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000) :
    ∃ r, max_subarrays nums = Std.Result.ok r ∧ 1 ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hb : ∀ i, i < nums.val.length → 0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000), ∃ r, max_subarrays nums = Std.Result.ok r ∧ 1 ≤ r.val) := by
  sorry

/-- The function returns r with r <= n.
  Preconditions: Let n = len(nums). The parameters satisfy 1 <= n <= 100000 and 0 <= nums[i] <= 1000000 for every integer i with 0 <= i < n. -/
theorem spec_5 (nums : Slice Std.I64)
    (hn : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hb : ∀ i, i < nums.val.length → 0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000) :
    ∃ r, max_subarrays nums = Std.Result.ok r ∧ r.val ≤ (nums.val.length : Int) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hb : ∀ i, i < nums.val.length → 0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000), ∃ r, max_subarrays nums = Std.Result.ok r ∧ r.val ≤ (nums.val.length : Int)) := by
  sorry

/-- If nums[i] = 0 for every integer i with 0 <= i < n, then the function returns r = n.
  Preconditions: Let n = len(nums). The parameters satisfy 1 <= n <= 100000 and 0 <= nums[i] <= 1000000 for every integer i with 0 <= i < n. -/
theorem spec_6 (nums : Slice Std.I64)
    (hn : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hb : ∀ i, i < nums.val.length → 0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000)
    (hzero : ∀ i, i < nums.val.length → (nums.val[i]!).val = 0) :
    ∃ r, max_subarrays nums = Std.Result.ok r ∧ r.val = (nums.val.length : Int) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hb : ∀ i, i < nums.val.length → 0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000)
    (hzero : ∀ i, i < nums.val.length → (nums.val[i]!).val = 0), ∃ r, max_subarrays nums = Std.Result.ok r ∧ r.val = (nums.val.length : Int)) := by
  sorry

/-- If n >= 2 and the function returns r = n, then nums[i] = 0 for every integer i with 0 <= i < n.
  Preconditions: Let n = len(nums). The parameters satisfy 1 <= n <= 100000 and 0 <= nums[i] <= 1000000 for every integer i with 0 <= i < n. -/
theorem spec_7 (nums : Slice Std.I64)
    (hn : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hb : ∀ i, i < nums.val.length → 0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000)
    (hn2 : 2 ≤ nums.val.length) :
    ∀ r, max_subarrays nums = Std.Result.ok r → r.val = (nums.val.length : Int) →
      ∀ i, i < nums.val.length → (nums.val[i]!).val = 0 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hb : ∀ i, i < nums.val.length → 0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000)
    (hn2 : 2 ≤ nums.val.length), ∀ r, max_subarrays nums = Std.Result.ok r → r.val = (nums.val.length : Int) →
      ∀ i, i < nums.val.length → (nums.val[i]!).val = 0) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result (it does not overflow, panic, or otherwise fail).
  Preconditions: Let n = len(nums). The parameters satisfy 1 <= n <= 100000 and 0 <= nums[i] <= 1000000 for every integer i with 0 <= i < n. -/
theorem spec_8 (nums : Slice Std.I64)
    (hn : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hb : ∀ i, i < nums.val.length → 0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000) :
    ∃ r, max_subarrays nums = Std.Result.ok r := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hb : ∀ i, i < nums.val.length → 0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000), ∃ r, max_subarrays nums = Std.Result.ok r) := by
  sorry

/-- Let C be the minimum cost over all splits of nums into contiguous nonempty parts, where the cost of a split is the sum of the bitwise ANDs of its parts. The function returns r, and there exists a split of nums into exactly r contiguous nonempty subarrays whose cost equals C.
  Preconditions: Let n = len(nums). The parameters satisfy 1 <= n <= 100000 and 0 <= nums[i] <= 1000000 for every integer i with 0 <= i < n. -/
theorem spec_9 (nums : Slice Std.I64)
    (hn : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hb : ∀ i, i < nums.val.length → 0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000)
    (C : Int) (hC : IsMinCost (vals nums) C) :
    ∃ r, max_subarrays nums = Std.Result.ok r ∧
      ∃ k p, IsSplit (vals nums).length k p ∧ splitCost (vals nums) p = C ∧ r.val = (k : Int) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hb : ∀ i, i < nums.val.length → 0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000)
    (C : Int) (hC : IsMinCost (vals nums) C), ∃ r, max_subarrays nums = Std.Result.ok r ∧
      ∃ k p, IsSplit (vals nums).length k p ∧ splitCost (vals nums) p = C ∧ r.val = (k : Int)) := by
  sorry

/-- The function returns r, and for every split of nums into k contiguous nonempty subarrays whose cost equals the minimum cost C over all splits, we have k <= r.
  Preconditions: Let n = len(nums). The parameters satisfy 1 <= n <= 100000 and 0 <= nums[i] <= 1000000 for every integer i with 0 <= i < n. -/
theorem spec_10 (nums : Slice Std.I64)
    (hn : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hb : ∀ i, i < nums.val.length → 0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000)
    (C : Int) (hC : IsMinCost (vals nums) C) :
    ∃ r, max_subarrays nums = Std.Result.ok r ∧
      ∀ k p, IsSplit (vals nums).length k p → splitCost (vals nums) p = C →
        (k : Int) ≤ r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hb : ∀ i, i < nums.val.length → 0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000)
    (C : Int) (hC : IsMinCost (vals nums) C), ∃ r, max_subarrays nums = Std.Result.ok r ∧
      ∀ k p, IsSplit (vals nums).length k p → splitCost (vals nums) p = C →
        (k : Int) ≤ r.val) := by
  sorry

/-- The function returns r, and the minimum cost C over all splits of nums into contiguous nonempty parts (the sum of the bitwise ANDs of the parts) equals M = nums[0] & nums[1] & ... & nums[n-1], the bitwise AND of all elements.
  Preconditions: Let n = len(nums). The parameters satisfy 1 <= n <= 100000 and 0 <= nums[i] <= 1000000 for every integer i with 0 <= i < n. -/
theorem spec_11 (nums : Slice Std.I64)
    (hn : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hb : ∀ i, i < nums.val.length → 0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000) :
    ∃ r, max_subarrays nums = Std.Result.ok r ∧
      ∀ C, IsMinCost (vals nums) C → C = fullAnd (vals nums) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hb : ∀ i, i < nums.val.length → 0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000), ∃ r, max_subarrays nums = Std.Result.ok r ∧
      ∀ C, IsMinCost (vals nums) C → C = fullAnd (vals nums)) := by
  sorry

/-- If n = 2, then the function returns r = 2 when nums[0] = 0 and nums[1] = 0, and returns r = 1 otherwise.
  Preconditions: Let n = len(nums). The parameters satisfy 1 <= n <= 100000 and 0 <= nums[i] <= 1000000 for every integer i with 0 <= i < n. -/
theorem spec_12 (nums : Slice Std.I64)
    (hn : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hb : ∀ i, i < nums.val.length → 0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000)
    (hn2 : nums.val.length = 2) :
    (((nums.val[0]!).val = 0 ∧ (nums.val[1]!).val = 0) →
        ∃ r, max_subarrays nums = Std.Result.ok r ∧ r.val = 2) ∧
      (¬ ((nums.val[0]!).val = 0 ∧ (nums.val[1]!).val = 0) →
        ∃ r, max_subarrays nums = Std.Result.ok r ∧ r.val = 1) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hb : ∀ i, i < nums.val.length → 0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000)
    (hn2 : nums.val.length = 2), (((nums.val[0]!).val = 0 ∧ (nums.val[1]!).val = 0) →
        ∃ r, max_subarrays nums = Std.Result.ok r ∧ r.val = 2) ∧
      (¬ ((nums.val[0]!).val = 0 ∧ (nums.val[1]!).val = 0) →
        ∃ r, max_subarrays nums = Std.Result.ok r ∧ r.val = 1)) := by
  sorry

end AegisSpec.MaxSubarrays
