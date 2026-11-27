import Aegis.MinChanges.Code.Funs

/-!
# Specifications of `Aegis.MinChanges.min_changes`

LeetCode problem `make-the-xor-of-all-segments-equal-to-zero`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinChanges

def xorAll : List Std.I64 → Std.I64
  | [] => 0#i64
  | x :: xs => x ^^^ xorAll xs

def segXor (b : List Std.I64) (left len : Nat) : Std.I64 :=
  xorAll ((b.drop left).take len)

def windowsXorZero (b : List Std.I64) (k : Nat) : Prop :=
  ∀ left, left + k ≤ b.length → segXor b left k = 0#i64

def diffCost (nums b : List Std.I64) : Nat :=
  (nums.zipWith (fun x y => if x = y then 0 else 1) b).sum

def IsMinCost (nums : List Std.I64) (k : Nat) (r : Int) : Prop :=
  (∃ b, b.length = nums.length ∧ windowsXorZero b k ∧ (diffCost nums b : Int) = r) ∧
    ∀ b, b.length = nums.length → windowsXorZero b k → r ≤ (diffCost nums b : Int)

def periodic (c : List Std.I64) (n : Nat) : List Std.I64 :=
  (List.range n).map (fun i => c.getD (i % c.length) 0#i64)

def residueIndices (nums : List Std.I64) (k a : Nat) : List Nat :=
  (List.range nums.length).filter (fun i => i % k = a)

def residueValues (nums : List Std.I64) (k a : Nat) : List Std.I64 :=
  (residueIndices nums k a).map (fun i => nums.getD i 0#i64)

def countResidue (nums : List Std.I64) (k a : Nat) (v : Int) : Nat :=
  (residueValues nums k a).countP (fun x => decide (x.val = v))

def maxResidueCount (nums : List Std.I64) (k a : Nat) : Nat :=
  ((residueValues nums k a).map (fun x => countResidue nums k a x.val)).foldr max 0

def countValue (nums : List Std.I64) (v : Int) : Nat :=
  nums.countP (fun x => decide (x.val = v))

def maxValueCount (nums : List Std.I64) : Nat :=
  (nums.map (fun x => countValue nums x.val)).foldr max 0

def nonzeroCount (nums : List Std.I64) : Nat :=
  nums.countP (fun x => decide (x.val ≠ 0))

def IsReverse (nums rev : Slice Std.I64) : Prop :=
  rev.val = nums.val.reverse

/-- Whenever min_changes(nums, k) returns a result r, r is the minimum, over all arrays b of length n of 64-bit integers satisfying: for every left with 0 <= left <= n-k, the XOR of b[left], b[left+1], ..., b[left+k-1] is 0, of the number of indices i with 0 <= i < n and b[i] != nums[i].
  Preconditions: Let n = len(nums). 1 <= k <= n, n <= 2000, and 0 <= nums[i] < 1024 for every i with 0 <= i < n. -/
theorem spec_1 (nums : Slice Std.I64) (k r : Std.I64)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (nums.val.length : Int))
    (hn : nums.val.length ≤ 2000)
    (hrange : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val < 1024)
    (h : Aegis.MinChanges.min_changes nums k = ok r) :
    IsMinCost nums.val k.val.toNat r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (k r : Std.I64)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (nums.val.length : Int))
    (hn : nums.val.length ≤ 2000)
    (hrange : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val < 1024)
    (h : Aegis.MinChanges.min_changes nums k = ok r), IsMinCost nums.val k.val.toNat r.val) := by
  sorry

/-- For every input satisfying the preconditions, there exists a 64-bit integer r such that min_changes(nums, k) returns the successful result `ok r`; in particular, the call never returns an error.
  Preconditions: Let n = len(nums). 1 <= k <= n, n <= 2000, and 0 <= nums[i] < 1024 for every i with 0 <= i < n. -/
theorem spec_2 (nums : Slice Std.I64) (k : Std.I64)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (nums.val.length : Int))
    (hn : nums.val.length ≤ 2000)
    (hrange : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val < 1024) :
    ∃ r : Std.I64, Aegis.MinChanges.min_changes nums k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (nums.val.length : Int))
    (hn : nums.val.length ≤ 2000)
    (hrange : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val < 1024), ∃ r : Std.I64, Aegis.MinChanges.min_changes nums k = ok r) := by
  sorry

/-- Whenever min_changes(nums, k) returns a result r, 0 <= r <= len(nums).
  Preconditions: Let n = len(nums). 1 <= k <= n, n <= 2000, and 0 <= nums[i] < 1024 for every i with 0 <= i < n. -/
theorem spec_3 (nums : Slice Std.I64) (k r : Std.I64)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (nums.val.length : Int))
    (hn : nums.val.length ≤ 2000)
    (hrange : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val < 1024)
    (h : Aegis.MinChanges.min_changes nums k = ok r) :
    0 ≤ r.val ∧ r.val ≤ (nums.val.length : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (k r : Std.I64)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (nums.val.length : Int))
    (hn : nums.val.length ≤ 2000)
    (hrange : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val < 1024)
    (h : Aegis.MinChanges.min_changes nums k = ok r), 0 ≤ r.val ∧ r.val ≤ (nums.val.length : Int)) := by
  sorry

/-- Whenever min_changes(nums, k) returns a result r, there exists an array b of length n of 64-bit integers such that every length-k contiguous segment of b has XOR equal to 0, and exactly r indices i with 0 <= i < n satisfy b[i] != nums[i].
  Preconditions: Let n = len(nums). 1 <= k <= n, n <= 2000, and 0 <= nums[i] < 1024 for every i with 0 <= i < n. -/
theorem spec_4 (nums : Slice Std.I64) (k r : Std.I64)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (nums.val.length : Int))
    (hn : nums.val.length ≤ 2000)
    (hrange : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val < 1024)
    (h : Aegis.MinChanges.min_changes nums k = ok r) :
    ∃ b : List Std.I64,
      b.length = nums.val.length ∧ windowsXorZero b k.val.toNat ∧
        (diffCost nums.val b : Int) = r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (k r : Std.I64)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (nums.val.length : Int))
    (hn : nums.val.length ≤ 2000)
    (hrange : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val < 1024)
    (h : Aegis.MinChanges.min_changes nums k = ok r), ∃ b : List Std.I64,
      b.length = nums.val.length ∧ windowsXorZero b k.val.toNat ∧
        (diffCost nums.val b : Int) = r.val) := by
  sorry

/-- Whenever min_changes(nums, k) returns a result r, every array b of length n of 64-bit integers whose every length-k contiguous segment has XOR equal to 0 satisfies: the number of indices i with 0 <= i < n and b[i] != nums[i] is at least r.
  Preconditions: Let n = len(nums). 1 <= k <= n, n <= 2000, and 0 <= nums[i] < 1024 for every i with 0 <= i < n. -/
theorem spec_5 (nums : Slice Std.I64) (k r : Std.I64)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (nums.val.length : Int))
    (hn : nums.val.length ≤ 2000)
    (hrange : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val < 1024)
    (h : Aegis.MinChanges.min_changes nums k = ok r) :
    ∀ b : List Std.I64,
      b.length = nums.val.length → windowsXorZero b k.val.toNat →
        r.val ≤ (diffCost nums.val b : Int) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (k r : Std.I64)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (nums.val.length : Int))
    (hn : nums.val.length ≤ 2000)
    (hrange : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val < 1024)
    (h : Aegis.MinChanges.min_changes nums k = ok r), ∀ b : List Std.I64,
      b.length = nums.val.length → windowsXorZero b k.val.toNat →
        r.val ≤ (diffCost nums.val b : Int)) := by
  sorry

/-- Whenever min_changes(nums, k) returns a result r, there exist integers c_0, ..., c_{k-1} such that c_0 XOR c_1 XOR ... XOR c_{k-1} = 0 and the array b of length n defined by b[i] = c_(i mod k) for every 0 <= i < n has exactly r indices i with b[i] != nums[i]. Moreover, every array defined this way from such c_0, ..., c_{k-1} has XOR 0 on every length-k contiguous segment.
  Preconditions: Let n = len(nums). 1 <= k <= n, n <= 2000, and 0 <= nums[i] < 1024 for every i with 0 <= i < n. -/
theorem spec_6 (nums : Slice Std.I64) (k r : Std.I64)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (nums.val.length : Int))
    (hn : nums.val.length ≤ 2000)
    (hrange : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val < 1024)
    (h : Aegis.MinChanges.min_changes nums k = ok r) :
    (∃ c : List Std.I64,
        c.length = k.val.toNat ∧ xorAll c = 0#i64 ∧
          (diffCost nums.val (periodic c nums.val.length) : Int) = r.val) ∧
      ∀ c : List Std.I64,
        c.length = k.val.toNat → xorAll c = 0#i64 →
          windowsXorZero (periodic c nums.val.length) k.val.toNat := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (k r : Std.I64)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (nums.val.length : Int))
    (hn : nums.val.length ≤ 2000)
    (hrange : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val < 1024)
    (h : Aegis.MinChanges.min_changes nums k = ok r), (∃ c : List Std.I64,
        c.length = k.val.toNat ∧ xorAll c = 0#i64 ∧
          (diffCost nums.val (periodic c nums.val.length) : Int) = r.val) ∧
      ∀ c : List Std.I64,
        c.length = k.val.toNat → xorAll c = 0#i64 →
          windowsXorZero (periodic c nums.val.length) k.val.toNat) := by
  sorry

/-- Whenever min_changes(nums, 1) returns a result r, r is the number of indices i with 0 <= i < len(nums) and nums[i] != 0.
  Preconditions: Let n = len(nums). 1 <= k <= n, n <= 2000, 0 <= nums[i] < 1024 for every i with 0 <= i < n, and k = 1. -/
theorem spec_7 (nums : Slice Std.I64) (k r : Std.I64)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (nums.val.length : Int))
    (hn : nums.val.length ≤ 2000)
    (hrange : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val < 1024)
    (hkone : k.val = 1)
    (h : Aegis.MinChanges.min_changes nums k = ok r) :
    r.val = (nonzeroCount nums.val : Int) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (k r : Std.I64)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (nums.val.length : Int))
    (hn : nums.val.length ≤ 2000)
    (hrange : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val < 1024)
    (hkone : k.val = 1)
    (h : Aegis.MinChanges.min_changes nums k = ok r), r.val = (nonzeroCount nums.val : Int)) := by
  sorry

/-- Let X = nums[0] XOR nums[1] XOR ... XOR nums[n-1]. Whenever min_changes(nums, k) returns a result r, r = 0 if X = 0, and r = 1 if X != 0.
  Preconditions: Let n = len(nums). 1 <= k <= n, n <= 2000, 0 <= nums[i] < 1024 for every i with 0 <= i < n, and k = n. -/
theorem spec_8 (nums : Slice Std.I64) (k r : Std.I64)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (nums.val.length : Int))
    (hn : nums.val.length ≤ 2000)
    (hrange : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val < 1024)
    (hkn' : k.val = (nums.val.length : Int))
    (h : Aegis.MinChanges.min_changes nums k = ok r) :
    (xorAll nums.val = 0#i64 → r.val = 0) ∧ (xorAll nums.val ≠ 0#i64 → r.val = 1) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (k r : Std.I64)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (nums.val.length : Int))
    (hn : nums.val.length ≤ 2000)
    (hrange : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val < 1024)
    (hkn' : k.val = (nums.val.length : Int))
    (h : Aegis.MinChanges.min_changes nums k = ok r), (xorAll nums.val = 0#i64 → r.val = 0) ∧ (xorAll nums.val ≠ 0#i64 → r.val = 1)) := by
  sorry

/-- Whenever min_changes(nums, k) returns a result r, r = 0.
  Preconditions: Let n = len(nums). 1 <= k <= n, n <= 2000, 0 <= nums[i] < 1024 for every i with 0 <= i < n, and nums itself already satisfies: every contiguous segment of length k has XOR equal to 0. -/
theorem spec_9 (nums : Slice Std.I64) (k r : Std.I64)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (nums.val.length : Int))
    (hn : nums.val.length ≤ 2000)
    (hrange : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val < 1024)
    (hsat : windowsXorZero nums.val k.val.toNat)
    (h : Aegis.MinChanges.min_changes nums k = ok r) :
    r.val = 0 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64) (k r : Std.I64)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (nums.val.length : Int))
    (hn : nums.val.length ≤ 2000)
    (hrange : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val < 1024)
    (hsat : windowsXorZero nums.val k.val.toNat)
    (h : Aegis.MinChanges.min_changes nums k = ok r), r.val = 0) := by
  sorry

/-- Whenever min_changes(nums, k) returns a result r: if c = 0 or k is even, then r = 0; if c != 0 and k is odd, then r = floor(n / k).
  Preconditions: Let n = len(nums). 1 <= k <= n, n <= 2000, 0 <= nums[i] < 1024 for every i with 0 <= i < n, and there exists an integer c such that nums[i] = c for every 0 <= i < n. -/
theorem spec_10 (nums : Slice Std.I64) (k r : Std.I64) (c : Int)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (nums.val.length : Int))
    (hn : nums.val.length ≤ 2000)
    (hrange : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val < 1024)
    (hconst : ∀ x ∈ nums.val, x.val = c)
    (h : Aegis.MinChanges.min_changes nums k = ok r) :
    (c = 0 ∨ Even k.val → r.val = 0) ∧
      (c ≠ 0 → Odd k.val → r.val = ((nums.val.length / k.val.toNat : Nat) : Int)) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64) (k r : Std.I64) (c : Int)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (nums.val.length : Int))
    (hn : nums.val.length ≤ 2000)
    (hrange : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val < 1024)
    (hconst : ∀ x ∈ nums.val, x.val = c)
    (h : Aegis.MinChanges.min_changes nums k = ok r), (c = 0 ∨ Even k.val → r.val = 0) ∧
      (c ≠ 0 → Odd k.val → r.val = ((nums.val.length / k.val.toNat : Nat) : Int))) := by
  sorry

/-- For each a with 0 <= a < k, let M_a be the maximum, over all integers v, of the number of indices i such that 0 <= i < n, i mod k = a, and nums[i] = v. Whenever min_changes(nums, k) returns a result r, r >= n - (M_0 + M_1 + ... + M_{k-1}).
  Preconditions: Let n = len(nums). 1 <= k <= n, n <= 2000, and 0 <= nums[i] < 1024 for every i with 0 <= i < n. -/
theorem spec_11 (nums : Slice Std.I64) (k r : Std.I64)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (nums.val.length : Int))
    (hn : nums.val.length ≤ 2000)
    (hrange : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val < 1024)
    (h : Aegis.MinChanges.min_changes nums k = ok r) :
    r.val ≥ (nums.val.length : Int) -
      (((List.range k.val.toNat).map
        (fun a => maxResidueCount nums.val k.val.toNat a)).sum : Int) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64) (k r : Std.I64)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (nums.val.length : Int))
    (hn : nums.val.length ≤ 2000)
    (hrange : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val < 1024)
    (h : Aegis.MinChanges.min_changes nums k = ok r), r.val ≥ (nums.val.length : Int) -
      (((List.range k.val.toNat).map
        (fun a => maxResidueCount nums.val k.val.toNat a)).sum : Int)) := by
  sorry

/-- Let M be the maximum, over all integers v, of the number of indices i with 0 <= i < n and nums[i] = v. Whenever min_changes(nums, k) returns a result r, r = n - M.
  Preconditions: Let n = len(nums). 1 <= k <= n, n <= 2000, 0 <= nums[i] < 1024 for every i with 0 <= i < n, and k = 2. -/
theorem spec_12 (nums : Slice Std.I64) (k r : Std.I64)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (nums.val.length : Int))
    (hn : nums.val.length ≤ 2000)
    (hrange : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val < 1024)
    (hktwo : k.val = 2)
    (h : Aegis.MinChanges.min_changes nums k = ok r) :
    r.val = ((nums.val.length - maxValueCount nums.val : Nat) : Int) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64) (k r : Std.I64)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (nums.val.length : Int))
    (hn : nums.val.length ≤ 2000)
    (hrange : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val < 1024)
    (hktwo : k.val = 2)
    (h : Aegis.MinChanges.min_changes nums k = ok r), r.val = ((nums.val.length - maxValueCount nums.val : Nat) : Int)) := by
  sorry

/-- Let rev be the array of length n defined by rev[i] = nums[n-1-i] for 0 <= i < n. Whenever min_changes(nums, k) returns r and min_changes(rev, k) returns r_rev, we have r = r_rev.
  Preconditions: Let n = len(nums). 1 <= k <= n, n <= 2000, and 0 <= nums[i] < 1024 for every i with 0 <= i < n. -/
theorem spec_13 (nums rev : Slice Std.I64) (k r r_rev : Std.I64)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (nums.val.length : Int))
    (hn : nums.val.length ≤ 2000)
    (hrange : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val < 1024)
    (hrev : IsReverse nums rev)
    (h : Aegis.MinChanges.min_changes nums k = ok r)
    (h_rev : Aegis.MinChanges.min_changes rev k = ok r_rev) :
    r.val = r_rev.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums rev : Slice Std.I64) (k r r_rev : Std.I64)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (nums.val.length : Int))
    (hn : nums.val.length ≤ 2000)
    (hrange : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val < 1024)
    (hrev : IsReverse nums rev)
    (h : Aegis.MinChanges.min_changes nums k = ok r)
    (h_rev : Aegis.MinChanges.min_changes rev k = ok r_rev), r.val = r_rev.val) := by
  sorry

/-- Suppose that for every a with 0 <= a < k, the multiset of values nums[i] over indices i with 0 <= i < n and i mod k = a equals the multiset of values nums2[i] over the same residue class. Whenever min_changes(nums, k) returns r and min_changes(nums2, k) returns r2, we have r = r2.
  Preconditions: Let n = len(nums). 1 <= k <= n, n <= 2000, and 0 <= nums[i] < 1024 for every i with 0 <= i < n. Let nums2 be any array of length n with 0 <= nums2[i] < 1024 for every 0 <= i < n. -/
theorem spec_14 (nums nums2 : Slice Std.I64) (k r r2 : Std.I64)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (nums.val.length : Int))
    (hn : nums.val.length ≤ 2000)
    (hrange : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val < 1024)
    (hlen : nums2.val.length = nums.val.length)
    (hrange2 : ∀ x ∈ nums2.val, 0 ≤ x.val ∧ x.val < 1024)
    (hmult : ∀ a, a < k.val.toNat →
      List.Perm (residueValues nums.val k.val.toNat a)
        (residueValues nums2.val k.val.toNat a))
    (h : Aegis.MinChanges.min_changes nums k = ok r)
    (h2 : Aegis.MinChanges.min_changes nums2 k = ok r2) :
    r.val = r2.val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (nums nums2 : Slice Std.I64) (k r r2 : Std.I64)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (nums.val.length : Int))
    (hn : nums.val.length ≤ 2000)
    (hrange : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val < 1024)
    (hlen : nums2.val.length = nums.val.length)
    (hrange2 : ∀ x ∈ nums2.val, 0 ≤ x.val ∧ x.val < 1024)
    (hmult : ∀ a, a < k.val.toNat →
      List.Perm (residueValues nums.val k.val.toNat a)
        (residueValues nums2.val k.val.toNat a))
    (h : Aegis.MinChanges.min_changes nums k = ok r)
    (h2 : Aegis.MinChanges.min_changes nums2 k = ok r2), r.val = r2.val) := by
  sorry

/-- Whenever min_changes(nums, k) returns a result r, there exists an array b of length n such that every length-k contiguous segment of b has XOR equal to 0, exactly r indices i satisfy b[i] != nums[i], and 0 <= b[i] < 1024 for every 0 <= i < n.
  Preconditions: Let n = len(nums). 1 <= k <= n, n <= 2000, and 0 <= nums[i] < 1024 for every i with 0 <= i < n. -/
theorem spec_15 (nums : Slice Std.I64) (k r : Std.I64)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (nums.val.length : Int))
    (hn : nums.val.length ≤ 2000)
    (hrange : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val < 1024)
    (h : Aegis.MinChanges.min_changes nums k = ok r) :
    ∃ b : List Std.I64,
      b.length = nums.val.length ∧ windowsXorZero b k.val.toNat ∧
        (diffCost nums.val b : Int) = r.val ∧ ∀ x ∈ b, 0 ≤ x.val ∧ x.val < 1024 := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (nums : Slice Std.I64) (k r : Std.I64)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (nums.val.length : Int))
    (hn : nums.val.length ≤ 2000)
    (hrange : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val < 1024)
    (h : Aegis.MinChanges.min_changes nums k = ok r), ∃ b : List Std.I64,
      b.length = nums.val.length ∧ windowsXorZero b k.val.toNat ∧
        (diffCost nums.val b : Int) = r.val ∧ ∀ x ∈ b, 0 ≤ x.val ∧ x.val < 1024) := by
  sorry

/-- Whenever min_changes(nums, k) returns a result r, r = 0 if and only if the original array nums already satisfies: every contiguous segment of length k has XOR equal to 0.
  Preconditions: Let n = len(nums). 1 <= k <= n, n <= 2000, and 0 <= nums[i] < 1024 for every i with 0 <= i < n. -/
theorem spec_16 (nums : Slice Std.I64) (k r : Std.I64)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (nums.val.length : Int))
    (hn : nums.val.length ≤ 2000)
    (hrange : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val < 1024)
    (h : Aegis.MinChanges.min_changes nums k = ok r) :
    (r.val = 0 ↔ windowsXorZero nums.val k.val.toNat) := by
  sorry

theorem spec_16_neg :
    ¬ (∀ (nums : Slice Std.I64) (k r : Std.I64)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (nums.val.length : Int))
    (hn : nums.val.length ≤ 2000)
    (hrange : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val < 1024)
    (h : Aegis.MinChanges.min_changes nums k = ok r), (r.val = 0 ↔ windowsXorZero nums.val k.val.toNat)) := by
  sorry

end AegisSpec.MinChanges
