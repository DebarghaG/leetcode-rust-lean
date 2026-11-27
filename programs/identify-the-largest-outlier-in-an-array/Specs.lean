import Aegis.GetLargestOutlier.Code.Funs

/-!
# Specifications of `Aegis.GetLargestOutlier.get_largest_outlier`

LeetCode problem `identify-the-largest-outlier-in-an-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.GetLargestOutlier

def vals (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

def size (nums : Slice Std.I64) : Nat := (vals nums).length

def entry (nums : Slice Std.I64) (i : Nat) : Int := (vals nums).getD i 0

def total (nums : Slice Std.I64) : Int := (vals nums).sum

def sumExcept (nums : Slice Std.I64) (o s : Nat) : Int :=
  (((List.range (size nums)).filter (fun i => i != o && i != s)).map
    (fun i => entry nums i)).sum

def maxEntry (nums : Slice Std.I64) : Int := (vals nums).foldr max ((vals nums).headD 0)

def minEntry (nums : Slice Std.I64) : Int := (vals nums).foldr min ((vals nums).headD 0)

def IsPotentialOutlier (nums : Slice Std.I64) (o : Nat) : Prop :=
  o < size nums ∧
    ∃ s, s < size nums ∧ s ≠ o ∧ sumExcept nums o s = entry nums s

def IsOutlierValue (nums : Slice Std.I64) (v : Int) : Prop :=
  ∃ o, o < size nums ∧ entry nums o = v ∧
    ∃ s, s < size nums ∧ s ≠ o ∧ total nums - entry nums o = 2 * entry nums s

def IsLargestOutlier (nums : Slice Std.I64) (m : Int) : Prop :=
  IsOutlierValue nums m ∧ ∀ v, IsOutlierValue nums v → v ≤ m

/-- Let T = sum_{i=0}^{n-1} nums[i]. Whenever get_largest_outlier nums returns a result r, r = max { nums[o] | 0 <= o < n and there exists s with 0 <= s < n, s != o, and T - nums[o] = 2*nums[s] }.
  Preconditions: Let n = len(nums). 3 <= n <= 100000. For every i with 0 <= i < n, -1000 <= nums[i] <= 1000. Also, at least one potential-outlier index exists, where an index o with 0 <= o < n is a potential-outlier index if there exists an index s with 0 <= s < n, s != o, such that the sum of nums[i] over all i with 0 <= i < n, i != o, and i != s equals nums[s]; all arithmetic here is in ordinary integers. -/
theorem spec_1 (nums : Slice Std.I64) (r : Std.I64)
    (h_n_lower : 3 ≤ size nums) (h_n_upper : size nums ≤ 100000)
    (h_entry_bounds : ∀ i, i < size nums → -1000 ≤ entry nums i ∧ entry nums i ≤ 1000)
    (h_outlier_exists : ∃ o, IsPotentialOutlier nums o)
    (h_ret : Aegis.GetLargestOutlier.get_largest_outlier nums = ok r) :
    IsLargestOutlier nums r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
    (h_n_lower : 3 ≤ size nums) (h_n_upper : size nums ≤ 100000)
    (h_entry_bounds : ∀ i, i < size nums → -1000 ≤ entry nums i ∧ entry nums i ≤ 1000)
    (h_outlier_exists : ∃ o, IsPotentialOutlier nums o)
    (h_ret : Aegis.GetLargestOutlier.get_largest_outlier nums = ok r), IsLargestOutlier nums r.val) := by
  sorry

/-- The function returns a result r and does not fail; in particular it does not overflow, go out of bounds, or panic.
  Preconditions: Let n = len(nums). 3 <= n <= 100000. For every i with 0 <= i < n, -1000 <= nums[i] <= 1000. Also, at least one potential-outlier index exists, where an index o with 0 <= o < n is a potential-outlier index if there exists an index s with 0 <= s < n, s != o, such that the sum of nums[i] over all i with 0 <= i < n, i != o, and i != s equals nums[s]; all arithmetic here is in ordinary integers. -/
theorem spec_2 (nums : Slice Std.I64)
    (h_n_lower : 3 ≤ size nums) (h_n_upper : size nums ≤ 100000)
    (h_entry_bounds : ∀ i, i < size nums → -1000 ≤ entry nums i ∧ entry nums i ≤ 1000)
    (h_outlier_exists : ∃ o, IsPotentialOutlier nums o) :
    ∃ r : Std.I64, Aegis.GetLargestOutlier.get_largest_outlier nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_n_lower : 3 ≤ size nums) (h_n_upper : size nums ≤ 100000)
    (h_entry_bounds : ∀ i, i < size nums → -1000 ≤ entry nums i ∧ entry nums i ≤ 1000)
    (h_outlier_exists : ∃ o, IsPotentialOutlier nums o), ∃ r : Std.I64, Aegis.GetLargestOutlier.get_largest_outlier nums = ok r) := by
  sorry

/-- Let T = sum_{i=0}^{n-1} nums[i]. Whenever get_largest_outlier nums returns r, there exist indices o and s with 0 <= o < n, 0 <= s < n, and o != s, such that nums[o] = r and T - nums[o] = 2*nums[s]. Equivalently, the sum of nums[i] over all i other than o and s equals nums[s].
  Preconditions: Let n = len(nums). 3 <= n <= 100000. For every i with 0 <= i < n, -1000 <= nums[i] <= 1000. Also, at least one potential-outlier index exists, where an index o with 0 <= o < n is a potential-outlier index if there exists an index s with 0 <= s < n, s != o, such that the sum of nums[i] over all i with 0 <= i < n, i != o, and i != s equals nums[s]; all arithmetic here is in ordinary integers. -/
theorem spec_3 (nums : Slice Std.I64) (r : Std.I64)
    (h_n_lower : 3 ≤ size nums) (h_n_upper : size nums ≤ 100000)
    (h_entry_bounds : ∀ i, i < size nums → -1000 ≤ entry nums i ∧ entry nums i ≤ 1000)
    (h_outlier_exists : ∃ o, IsPotentialOutlier nums o)
    (h_ret : Aegis.GetLargestOutlier.get_largest_outlier nums = ok r) :
    ∃ o s, o < size nums ∧ s < size nums ∧ o ≠ s ∧ entry nums o = r.val ∧
      total nums - entry nums o = 2 * entry nums s := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
    (h_n_lower : 3 ≤ size nums) (h_n_upper : size nums ≤ 100000)
    (h_entry_bounds : ∀ i, i < size nums → -1000 ≤ entry nums i ∧ entry nums i ≤ 1000)
    (h_outlier_exists : ∃ o, IsPotentialOutlier nums o)
    (h_ret : Aegis.GetLargestOutlier.get_largest_outlier nums = ok r), ∃ o s, o < size nums ∧ s < size nums ∧ o ≠ s ∧ entry nums o = r.val ∧
      total nums - entry nums o = 2 * entry nums s) := by
  sorry

/-- Let T = sum_{i=0}^{n-1} nums[i]. Whenever get_largest_outlier nums returns r, for every o and s with 0 <= o < n, 0 <= s < n, s != o, if T - nums[o] = 2*nums[s], then nums[o] <= r.
  Preconditions: Let n = len(nums). 3 <= n <= 100000. For every i with 0 <= i < n, -1000 <= nums[i] <= 1000. Also, at least one potential-outlier index exists, where an index o with 0 <= o < n is a potential-outlier index if there exists an index s with 0 <= s < n, s != o, such that the sum of nums[i] over all i with 0 <= i < n, i != o, and i != s equals nums[s]; all arithmetic here is in ordinary integers. -/
theorem spec_4 (nums : Slice Std.I64) (r : Std.I64)
    (h_n_lower : 3 ≤ size nums) (h_n_upper : size nums ≤ 100000)
    (h_entry_bounds : ∀ i, i < size nums → -1000 ≤ entry nums i ∧ entry nums i ≤ 1000)
    (h_outlier_exists : ∃ o, IsPotentialOutlier nums o)
    (h_ret : Aegis.GetLargestOutlier.get_largest_outlier nums = ok r) :
    ∀ o s, o < size nums → s < size nums → s ≠ o →
      total nums - entry nums o = 2 * entry nums s → entry nums o ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
    (h_n_lower : 3 ≤ size nums) (h_n_upper : size nums ≤ 100000)
    (h_entry_bounds : ∀ i, i < size nums → -1000 ≤ entry nums i ∧ entry nums i ≤ 1000)
    (h_outlier_exists : ∃ o, IsPotentialOutlier nums o)
    (h_ret : Aegis.GetLargestOutlier.get_largest_outlier nums = ok r), ∀ o s, o < size nums → s < size nums → s ≠ o →
      total nums - entry nums o = 2 * entry nums s → entry nums o ≤ r.val) := by
  sorry

/-- Whenever get_largest_outlier nums returns r, min(nums) <= r <= max(nums), where min(nums) and max(nums) are taken over all entries of nums.
  Preconditions: Let n = len(nums). 3 <= n <= 100000. For every i with 0 <= i < n, -1000 <= nums[i] <= 1000. Also, at least one potential-outlier index exists, where an index o with 0 <= o < n is a potential-outlier index if there exists an index s with 0 <= s < n, s != o, such that the sum of nums[i] over all i with 0 <= i < n, i != o, and i != s equals nums[s]; all arithmetic here is in ordinary integers. -/
theorem spec_5 (nums : Slice Std.I64) (r : Std.I64)
    (h_n_lower : 3 ≤ size nums) (h_n_upper : size nums ≤ 100000)
    (h_entry_bounds : ∀ i, i < size nums → -1000 ≤ entry nums i ∧ entry nums i ≤ 1000)
    (h_outlier_exists : ∃ o, IsPotentialOutlier nums o)
    (h_ret : Aegis.GetLargestOutlier.get_largest_outlier nums = ok r) :
    minEntry nums ≤ r.val ∧ r.val ≤ maxEntry nums := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
    (h_n_lower : 3 ≤ size nums) (h_n_upper : size nums ≤ 100000)
    (h_entry_bounds : ∀ i, i < size nums → -1000 ≤ entry nums i ∧ entry nums i ≤ 1000)
    (h_outlier_exists : ∃ o, IsPotentialOutlier nums o)
    (h_ret : Aegis.GetLargestOutlier.get_largest_outlier nums = ok r), minEntry nums ≤ r.val ∧ r.val ≤ maxEntry nums) := by
  sorry

/-- Let M = max { nums[i] | 0 <= i < n }. Whenever get_largest_outlier nums returns r, r = M if and only if there exists an index k with 0 <= k < n, nums[k] = M, and k is a potential-outlier index, i.e. there exists s with 0 <= s < n, s != k, such that T - nums[k] = 2*nums[s], where T = sum_{i=0}^{n-1} nums[i].
  Preconditions: Let n = len(nums). 3 <= n <= 100000. For every i with 0 <= i < n, -1000 <= nums[i] <= 1000. Also, at least one potential-outlier index exists, where an index o with 0 <= o < n is a potential-outlier index if there exists an index s with 0 <= s < n, s != o, such that the sum of nums[i] over all i with 0 <= i < n, i != o, and i != s equals nums[s]; all arithmetic here is in ordinary integers. -/
theorem spec_6 (nums : Slice Std.I64) (r : Std.I64)
    (h_n_lower : 3 ≤ size nums) (h_n_upper : size nums ≤ 100000)
    (h_entry_bounds : ∀ i, i < size nums → -1000 ≤ entry nums i ∧ entry nums i ≤ 1000)
    (h_outlier_exists : ∃ o, IsPotentialOutlier nums o)
    (h_ret : Aegis.GetLargestOutlier.get_largest_outlier nums = ok r) :
    r.val = maxEntry nums ↔
      ∃ k, k < size nums ∧ entry nums k = maxEntry nums ∧
        ∃ s, s < size nums ∧ s ≠ k ∧ total nums - entry nums k = 2 * entry nums s := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
    (h_n_lower : 3 ≤ size nums) (h_n_upper : size nums ≤ 100000)
    (h_entry_bounds : ∀ i, i < size nums → -1000 ≤ entry nums i ∧ entry nums i ≤ 1000)
    (h_outlier_exists : ∃ o, IsPotentialOutlier nums o)
    (h_ret : Aegis.GetLargestOutlier.get_largest_outlier nums = ok r), r.val = maxEntry nums ↔
      ∃ k, k < size nums ∧ entry nums k = maxEntry nums ∧
        ∃ s, s < size nums ∧ s ≠ k ∧ total nums - entry nums k = 2 * entry nums s) := by
  sorry

/-- For every permutation p of {0, ..., n-1}, let nums' be the slice of length n defined by nums'[i] = nums[p(i)] for 0 <= i < n. Then nums' satisfies the same preconditions, and whenever get_largest_outlier nums returns r and get_largest_outlier nums' returns r', we have r' = r.
  Preconditions: Let n = len(nums). 3 <= n <= 100000. For every i with 0 <= i < n, -1000 <= nums[i] <= 1000. Also, at least one potential-outlier index exists, where an index o with 0 <= o < n is a potential-outlier index if there exists an index s with 0 <= s < n, s != o, such that the sum of nums[i] over all i with 0 <= i < n, i != o, and i != s equals nums[s]; all arithmetic here is in ordinary integers. -/
theorem spec_7 (nums nums' : Slice Std.I64) (r r' : Std.I64)
    (h_n_lower : 3 ≤ size nums) (h_n_upper : size nums ≤ 100000)
    (h_entry_bounds : ∀ i, i < size nums → -1000 ≤ entry nums i ∧ entry nums i ≤ 1000)
    (h_outlier_exists : ∃ o, IsPotentialOutlier nums o)
    (h_perm : (vals nums').Perm (vals nums))
    (h_ret : Aegis.GetLargestOutlier.get_largest_outlier nums = ok r)
    (h_ret' : Aegis.GetLargestOutlier.get_largest_outlier nums' = ok r') :
    3 ≤ size nums' ∧ size nums' ≤ 100000 ∧
      (∀ i, i < size nums' → -1000 ≤ entry nums' i ∧ entry nums' i ≤ 1000) ∧
      (∃ o, IsPotentialOutlier nums' o) ∧
      r'.val = r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (r r' : Std.I64)
    (h_n_lower : 3 ≤ size nums) (h_n_upper : size nums ≤ 100000)
    (h_entry_bounds : ∀ i, i < size nums → -1000 ≤ entry nums i ∧ entry nums i ≤ 1000)
    (h_outlier_exists : ∃ o, IsPotentialOutlier nums o)
    (h_perm : (vals nums').Perm (vals nums))
    (h_ret : Aegis.GetLargestOutlier.get_largest_outlier nums = ok r)
    (h_ret' : Aegis.GetLargestOutlier.get_largest_outlier nums' = ok r'), 3 ≤ size nums' ∧ size nums' ≤ 100000 ∧
      (∀ i, i < size nums' → -1000 ≤ entry nums' i ∧ entry nums' i ≤ 1000) ∧
      (∃ o, IsPotentialOutlier nums' o) ∧
      r'.val = r.val) := by
  sorry

end AegisSpec.GetLargestOutlier
