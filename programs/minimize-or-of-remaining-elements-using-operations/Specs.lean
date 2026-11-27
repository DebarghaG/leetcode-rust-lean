import Aegis.MinOrAfterOperations.Code.Funs

/-!
# Specifications of `Aegis.MinOrAfterOperations.min_or_after_operations`

LeetCode problem `minimize-or-of-remaining-elements-using-operations`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MinOrAfterOperations

set_option maxHeartbeats 1000000

namespace AegisSpec.MinOrAfterOperations

def iAnd (a b : ℤ) : ℤ := ((a.toNat &&& b.toNat : ℕ) : ℤ)

def iOr (a b : ℤ) : ℤ := ((a.toNat ||| b.toNat : ℕ) : ℤ)

def allOnes : ℤ := 2 ^ 30 - 1

def band : List ℤ → ℤ
  | [] => allOnes
  | [a] => a
  | a :: b :: rest => iAnd a (band (b :: rest))

def bor : List ℤ → ℤ
  | [] => 0
  | [a] => a
  | a :: b :: rest => iOr a (bor (b :: rest))

def vals (l : List Std.I64) : List ℤ := l.map (fun x => x.val)

def blockAnd (l : List ℤ) (s e : ℕ) : ℤ := band ((l.drop s).take (e - s))

def partitionValue (l : List ℤ) : List ℕ → ℤ
  | [] => 0
  | [_] => 0
  | a :: b :: rest => iOr (blockAnd l a b) (partitionValue l (b :: rest))

def numBlocks (p : List ℕ) : ℕ := p.length - 1

def IsPartition (l : List ℤ) (p : List ℕ) : Prop :=
  p.head? = some 0 ∧ p.getLast? = some l.length ∧ p.Pairwise (· < ·)

def Admissible (l : List ℤ) (k : ℤ) (p : List ℕ) : Prop :=
  IsPartition l p ∧ (l.length : ℤ) - (numBlocks p : ℤ) ≤ k

def achievable (l : List ℤ) (k : ℤ) : Set ℤ :=
  partitionValue l '' { p : List ℕ | Admissible l k p }

def cutValue (l : List ℤ) (s : ℕ) : ℤ := iOr (blockAnd l 0 s) (blockAnd l s l.length)

/-- The function returns a result r and r is the minimum possible bitwise OR of the remaining array after at most k operations. Explicitly, for a partition P given by 0 = p0 < p1 < ... < pm = n with m >= 1, define V(P) = (nums[p0] & ... & nums[p1-1]) | ... | (nums[p_{m-1}] & ... & nums[p_m-1]). Then r = min { V(P) : P is such a partition and n - m <= k }. Here & and | are 64-bit bitwise AND and OR on nonnegative values.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 10^5, 0 <= nums[i] < 2^30 for every i with 0 <= i < n, and 0 <= k < n. -/
theorem spec_1 (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 10 ^ 5)
    (hrange : ∀ (i : ℕ) (h : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val < 2 ^ 30)
    (hk0 : 0 ≤ k.val) (hkn : k.val < (nums.val.length : ℤ)) :
    ∃ r : Std.I64, min_or_after_operations nums k = ok r ∧
      IsLeast (achievable (vals nums.val) k.val) r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 10 ^ 5)
    (hrange : ∀ (i : ℕ) (h : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val < 2 ^ 30)
    (hk0 : 0 ≤ k.val) (hkn : k.val < (nums.val.length : ℤ)), ∃ r : Std.I64, min_or_after_operations nums k = ok r ∧
      IsLeast (achievable (vals nums.val) k.val) r.val) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r; it does not panic, overflow, or otherwise fail.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 10^5, 0 <= nums[i] < 2^30 for every i with 0 <= i < n, and 0 <= k < n. -/
theorem spec_2 (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 10 ^ 5)
    (hrange : ∀ (i : ℕ) (h : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val < 2 ^ 30)
    (hk0 : 0 ≤ k.val) (hkn : k.val < (nums.val.length : ℤ)) :
    ∃ r : Std.I64, min_or_after_operations nums k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 10 ^ 5)
    (hrange : ∀ (i : ℕ) (h : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val < 2 ^ 30)
    (hk0 : 0 ≤ k.val) (hkn : k.val < (nums.val.length : ℤ)), ∃ r : Std.I64, min_or_after_operations nums k = ok r) := by
  sorry

/-- The returned result r satisfies r >= 0.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 10^5, 0 <= nums[i] < 2^30 for every i with 0 <= i < n, and 0 <= k < n. -/
theorem spec_3 (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 10 ^ 5)
    (hrange : ∀ (i : ℕ) (h : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val < 2 ^ 30)
    (hk0 : 0 ≤ k.val) (hkn : k.val < (nums.val.length : ℤ)) :
    ∃ r : Std.I64, min_or_after_operations nums k = ok r ∧ 0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 10 ^ 5)
    (hrange : ∀ (i : ℕ) (h : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val < 2 ^ 30)
    (hk0 : 0 ≤ k.val) (hkn : k.val < (nums.val.length : ℤ)), ∃ r : Std.I64, min_or_after_operations nums k = ok r ∧ 0 ≤ r.val) := by
  sorry

/-- The returned result r satisfies r < 2^30.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 10^5, 0 <= nums[i] < 2^30 for every i with 0 <= i < n, and 0 <= k < n. -/
theorem spec_4 (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 10 ^ 5)
    (hrange : ∀ (i : ℕ) (h : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val < 2 ^ 30)
    (hk0 : 0 ≤ k.val) (hkn : k.val < (nums.val.length : ℤ)) :
    ∃ r : Std.I64, min_or_after_operations nums k = ok r ∧ r.val < 2 ^ 30 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 10 ^ 5)
    (hrange : ∀ (i : ℕ) (h : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val < 2 ^ 30)
    (hk0 : 0 ≤ k.val) (hkn : k.val < (nums.val.length : ℤ)), ∃ r : Std.I64, min_or_after_operations nums k = ok r ∧ r.val < 2 ^ 30) := by
  sorry

/-- Let O = nums[0] | nums[1] | ... | nums[n-1]. The returned result r satisfies r | O = O; equivalently, every bit position that is 1 in r is also 1 in at least one nums[i].
  Preconditions: Let n = len(nums). Assume 1 <= n <= 10^5, 0 <= nums[i] < 2^30 for every i with 0 <= i < n, and 0 <= k < n. -/
theorem spec_5 (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 10 ^ 5)
    (hrange : ∀ (i : ℕ) (h : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val < 2 ^ 30)
    (hk0 : 0 ≤ k.val) (hkn : k.val < (nums.val.length : ℤ)) :
    ∃ r : Std.I64, min_or_after_operations nums k = ok r ∧
      iOr r.val (bor (vals nums.val)) = bor (vals nums.val) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 10 ^ 5)
    (hrange : ∀ (i : ℕ) (h : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val < 2 ^ 30)
    (hk0 : 0 ≤ k.val) (hkn : k.val < (nums.val.length : ℤ)), ∃ r : Std.I64, min_or_after_operations nums k = ok r ∧
      iOr r.val (bor (vals nums.val)) = bor (vals nums.val)) := by
  sorry

/-- Let A = nums[0] & nums[1] & ... & nums[n-1]. The returned result r satisfies r & A = A; equivalently, every bit position that is 1 in A is also 1 in r.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 10^5, 0 <= nums[i] < 2^30 for every i with 0 <= i < n, and 0 <= k < n. -/
theorem spec_6 (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 10 ^ 5)
    (hrange : ∀ (i : ℕ) (h : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val < 2 ^ 30)
    (hk0 : 0 ≤ k.val) (hkn : k.val < (nums.val.length : ℤ)) :
    ∃ r : Std.I64, min_or_after_operations nums k = ok r ∧
      iAnd r.val (band (vals nums.val)) = band (vals nums.val) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 10 ^ 5)
    (hrange : ∀ (i : ℕ) (h : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val < 2 ^ 30)
    (hk0 : 0 ≤ k.val) (hkn : k.val < (nums.val.length : ℤ)), ∃ r : Std.I64, min_or_after_operations nums k = ok r ∧
      iAnd r.val (band (vals nums.val)) = band (vals nums.val)) := by
  sorry

/-- There exists a partition of nums into m nonempty contiguous blocks, with n - m <= k, such that the bitwise OR of the bitwise ANDs of those blocks equals r.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 10^5, 0 <= nums[i] < 2^30 for every i with 0 <= i < n, and 0 <= k < n. -/
theorem spec_7 (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 10 ^ 5)
    (hrange : ∀ (i : ℕ) (h : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val < 2 ^ 30)
    (hk0 : 0 ≤ k.val) (hkn : k.val < (nums.val.length : ℤ)) :
    ∃ r : Std.I64, min_or_after_operations nums k = ok r ∧
      ∃ p : List ℕ, Admissible (vals nums.val) k.val p ∧
        partitionValue (vals nums.val) p = r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 10 ^ 5)
    (hrange : ∀ (i : ℕ) (h : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val < 2 ^ 30)
    (hk0 : 0 ≤ k.val) (hkn : k.val < (nums.val.length : ℤ)), ∃ r : Std.I64, min_or_after_operations nums k = ok r ∧
      ∃ p : List ℕ, Admissible (vals nums.val) k.val p ∧
        partitionValue (vals nums.val) p = r.val) := by
  sorry

/-- For every partition of nums into m nonempty contiguous blocks with n - m <= k, if W is the bitwise OR of the bitwise ANDs of those blocks, then r <= W.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 10^5, 0 <= nums[i] < 2^30 for every i with 0 <= i < n, and 0 <= k < n. -/
theorem spec_8 (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 10 ^ 5)
    (hrange : ∀ (i : ℕ) (h : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val < 2 ^ 30)
    (hk0 : 0 ≤ k.val) (hkn : k.val < (nums.val.length : ℤ)) :
    ∃ r : Std.I64, min_or_after_operations nums k = ok r ∧
      ∀ p : List ℕ, Admissible (vals nums.val) k.val p →
        r.val ≤ partitionValue (vals nums.val) p := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 10 ^ 5)
    (hrange : ∀ (i : ℕ) (h : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val < 2 ^ 30)
    (hk0 : 0 ≤ k.val) (hkn : k.val < (nums.val.length : ℤ)), ∃ r : Std.I64, min_or_after_operations nums k = ok r ∧
      ∀ p : List ℕ, Admissible (vals nums.val) k.val p →
        r.val ≤ partitionValue (vals nums.val) p) := by
  sorry

/-- There exists a partition of nums into exactly n - k nonempty contiguous blocks such that the bitwise OR of the bitwise ANDs of those blocks equals r.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 10^5, 0 <= nums[i] < 2^30 for every i with 0 <= i < n, and 0 <= k < n. -/
theorem spec_9 (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 10 ^ 5)
    (hrange : ∀ (i : ℕ) (h : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val < 2 ^ 30)
    (hk0 : 0 ≤ k.val) (hkn : k.val < (nums.val.length : ℤ)) :
    ∃ r : Std.I64, min_or_after_operations nums k = ok r ∧
      ∃ p : List ℕ, IsPartition (vals nums.val) p ∧
        (numBlocks p : ℤ) = (nums.val.length : ℤ) - k.val ∧
        partitionValue (vals nums.val) p = r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 10 ^ 5)
    (hrange : ∀ (i : ℕ) (h : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val < 2 ^ 30)
    (hk0 : 0 ≤ k.val) (hkn : k.val < (nums.val.length : ℤ)), ∃ r : Std.I64, min_or_after_operations nums k = ok r ∧
      ∃ p : List ℕ, IsPartition (vals nums.val) p ∧
        (numBlocks p : ℤ) = (nums.val.length : ℤ) - k.val ∧
        partitionValue (vals nums.val) p = r.val) := by
  sorry

/-- If k = 0, then r = nums[0] | nums[1] | ... | nums[n-1].
  Preconditions: Let n = len(nums). Assume 1 <= n <= 10^5, 0 <= nums[i] < 2^30 for every i with 0 <= i < n, and 0 <= k < n. -/
theorem spec_10 (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 10 ^ 5)
    (hrange : ∀ (i : ℕ) (h : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val < 2 ^ 30)
    (hk0 : 0 ≤ k.val) (hkn : k.val < (nums.val.length : ℤ)) :
    ∃ r : Std.I64, min_or_after_operations nums k = ok r ∧
      (k.val = 0 → r.val = bor (vals nums.val)) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 10 ^ 5)
    (hrange : ∀ (i : ℕ) (h : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val < 2 ^ 30)
    (hk0 : 0 ≤ k.val) (hkn : k.val < (nums.val.length : ℤ)), ∃ r : Std.I64, min_or_after_operations nums k = ok r ∧
      (k.val = 0 → r.val = bor (vals nums.val))) := by
  sorry

/-- If k = n - 1, then r = nums[0] & nums[1] & ... & nums[n-1].
  Preconditions: Let n = len(nums). Assume 1 <= n <= 10^5, 0 <= nums[i] < 2^30 for every i with 0 <= i < n, and 0 <= k < n. -/
theorem spec_11 (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 10 ^ 5)
    (hrange : ∀ (i : ℕ) (h : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val < 2 ^ 30)
    (hk0 : 0 ≤ k.val) (hkn : k.val < (nums.val.length : ℤ)) :
    ∃ r : Std.I64, min_or_after_operations nums k = ok r ∧
      (k.val = (nums.val.length : ℤ) - 1 → r.val = band (vals nums.val)) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 10 ^ 5)
    (hrange : ∀ (i : ℕ) (h : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val < 2 ^ 30)
    (hk0 : 0 ≤ k.val) (hkn : k.val < (nums.val.length : ℤ)), ∃ r : Std.I64, min_or_after_operations nums k = ok r ∧
      (k.val = (nums.val.length : ℤ) - 1 → r.val = band (vals nums.val))) := by
  sorry

/-- The returned result r satisfies r = min over 1 <= s < n of ((nums[0] & ... & nums[s-1]) | (nums[s] & ... & nums[n-1])).
  Preconditions: Let n = len(nums). Assume 2 <= n <= 10^5, 0 <= nums[i] < 2^30 for every i with 0 <= i < n, and k = n - 2. -/
theorem spec_12 (nums : Slice Std.I64) (k : Std.I64)
    (hn2 : 2 ≤ nums.val.length) (hn3 : nums.val.length ≤ 10 ^ 5)
    (hrange : ∀ (i : ℕ) (h : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val < 2 ^ 30)
    (hk : k.val = (nums.val.length : ℤ) - 2) :
    ∃ r : Std.I64, min_or_after_operations nums k = ok r ∧
      IsLeast (cutValue (vals nums.val) '' { s : ℕ | 1 ≤ s ∧ s < nums.val.length }) r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn2 : 2 ≤ nums.val.length) (hn3 : nums.val.length ≤ 10 ^ 5)
    (hrange : ∀ (i : ℕ) (h : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val < 2 ^ 30)
    (hk : k.val = (nums.val.length : ℤ) - 2), ∃ r : Std.I64, min_or_after_operations nums k = ok r ∧
      IsLeast (cutValue (vals nums.val) '' { s : ℕ | 1 ≤ s ∧ s < nums.val.length }) r.val) := by
  sorry

/-- If there exists a value c such that nums[i] = c for every i with 0 <= i < n, then r = c.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 10^5, 0 <= nums[i] < 2^30 for every i with 0 <= i < n, and 0 <= k < n. -/
theorem spec_13 (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 10 ^ 5)
    (hrange : ∀ (i : ℕ) (h : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val < 2 ^ 30)
    (hk0 : 0 ≤ k.val) (hkn : k.val < (nums.val.length : ℤ)) :
    ∃ r : Std.I64, min_or_after_operations nums k = ok r ∧
      ∀ c : ℤ, (∀ (i : ℕ) (h : i < nums.val.length), (nums.val[i]).val = c) → r.val = c := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 10 ^ 5)
    (hrange : ∀ (i : ℕ) (h : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val < 2 ^ 30)
    (hk0 : 0 ≤ k.val) (hkn : k.val < (nums.val.length : ℤ)), ∃ r : Std.I64, min_or_after_operations nums k = ok r ∧
      ∀ c : ℤ, (∀ (i : ℕ) (h : i < nums.val.length), (nums.val[i]).val = c) → r.val = c) := by
  sorry

/-- Let r1 = min_or_after_operations(nums, k1) and r2 = min_or_after_operations(nums, k2). Then r1 >= r2; allowing more operations cannot increase the minimum achievable OR.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 10^5, 0 <= nums[i] < 2^30 for every i with 0 <= i < n, and 0 <= k1 <= k2 < n. -/
theorem spec_14 (nums : Slice Std.I64) (k1 k2 : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 10 ^ 5)
    (hrange : ∀ (i : ℕ) (h : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val < 2 ^ 30)
    (hk10 : 0 ≤ k1.val) (hkk : k1.val ≤ k2.val) (hk2n : k2.val < (nums.val.length : ℤ)) :
    ∀ r1 r2 : Std.I64, min_or_after_operations nums k1 = ok r1 →
      min_or_after_operations nums k2 = ok r2 → r2.val ≤ r1.val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (nums : Slice Std.I64) (k1 k2 : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 10 ^ 5)
    (hrange : ∀ (i : ℕ) (h : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val < 2 ^ 30)
    (hk10 : 0 ≤ k1.val) (hkk : k1.val ≤ k2.val) (hk2n : k2.val < (nums.val.length : ℤ)), ∀ r1 r2 : Std.I64, min_or_after_operations nums k1 = ok r1 →
      min_or_after_operations nums k2 = ok r2 → r2.val ≤ r1.val) := by
  sorry

end AegisSpec.MinOrAfterOperations
