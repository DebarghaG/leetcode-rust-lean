import Aegis.CountQuadruplets.Code.Funs

/-!
# Specifications of `Aegis.CountQuadruplets.count_quadruplets`

LeetCode problem `count-special-quadruplets`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.CountQuadruplets

namespace AegisSpec.CountQuadruplets

def binom4 (n : Nat) : Nat := n * (n - 1) * (n - 2) * (n - 3) / 24

def quadCount (nums : Slice I64) : Nat :=
  Fintype.card
    {p : Fin nums.val.length × Fin nums.val.length × Fin nums.val.length × Fin nums.val.length //
      p.1.val < p.2.1.val ∧ p.2.1.val < p.2.2.1.val ∧ p.2.2.1.val < p.2.2.2.val ∧
      (nums.val[p.1.val]!).val + (nums.val[p.2.1.val]!).val + (nums.val[p.2.2.1.val]!).val
        = (nums.val[p.2.2.2.val]!).val}

def tripleCountBelow (nums : Slice I64) (bound : Nat) (target : Int) : Nat :=
  Fintype.card
    {p : Fin bound × Fin bound × Fin bound //
      p.1.val < p.2.1.val ∧ p.2.1.val < p.2.2.val ∧
      (nums.val[p.1.val]!).val + (nums.val[p.2.1.val]!).val + (nums.val[p.2.2.val]!).val = target}

def quadCountSumLE (nums : Slice I64) (bound : Int) : Nat :=
  Fintype.card
    {p : Fin nums.val.length × Fin nums.val.length × Fin nums.val.length × Fin nums.val.length //
      p.1.val < p.2.1.val ∧ p.2.1.val < p.2.2.1.val ∧ p.2.2.1.val < p.2.2.2.val ∧
      (nums.val[p.1.val]!).val + (nums.val[p.2.1.val]!).val + (nums.val[p.2.2.1.val]!).val ≤ bound}

/-- The function returns a result r, and r is the number of quadruplets (a,b,c,d) of indices such that 0 <= a < b < c < d < len(nums) and nums[a] + nums[b] + nums[c] = nums[d]. A quadruplet means an ordered 4-tuple of indices; two quadruplets are distinct exactly when their index tuples differ.
  Preconditions: 4 <= len(nums) <= 50 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
theorem spec_1 (nums : Slice I64)
    (hlen4 : 4 ≤ nums.val.length) (hlen50 : nums.val.length ≤ 50)
    (hval : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100) :
    ∃ r, count_quadruplets nums = ok r ∧ r.val = (quadCount nums : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen4 : 4 ≤ nums.val.length) (hlen50 : nums.val.length ≤ 50)
    (hval : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100), ∃ r, count_quadruplets nums = ok r ∧ r.val = (quadCount nums : Int)) := by
  sorry

/-- The function returns a result r (Ok r); under the stated preconditions it does not fail, panic, access out of bounds, or overflow.
  Preconditions: 4 <= len(nums) <= 50 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
theorem spec_2 (nums : Slice I64)
    (hlen4 : 4 ≤ nums.val.length) (hlen50 : nums.val.length ≤ 50)
    (hval : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100) :
    ∃ r, count_quadruplets nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen4 : 4 ≤ nums.val.length) (hlen50 : nums.val.length ≤ 50)
    (hval : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100), ∃ r, count_quadruplets nums = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r <= binomial(len(nums),4), where binomial(n,4) = n*(n-1)*(n-2)*(n-3)/24 is the number of 4-element subsets of {0,...,n-1}.
  Preconditions: 4 <= len(nums) <= 50 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
theorem spec_3 (nums : Slice I64)
    (hlen4 : 4 ≤ nums.val.length) (hlen50 : nums.val.length ≤ 50)
    (hval : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100) :
    ∀ r, count_quadruplets nums = ok r → 0 ≤ r.val ∧ r.val ≤ (binom4 nums.val.length : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen4 : 4 ≤ nums.val.length) (hlen50 : nums.val.length ≤ 50)
    (hval : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100), ∀ r, count_quadruplets nums = ok r → 0 ≤ r.val ∧ r.val ≤ (binom4 nums.val.length : Int)) := by
  sorry

/-- Whenever the function returns a result r, r = 0.
  Preconditions: 4 <= len(nums) <= 50, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100, and for every i with 0 <= i+1 < len(nums), nums[i] >= nums[i+1]. -/
theorem spec_4 (nums : Slice I64)
    (hlen4 : 4 ≤ nums.val.length) (hlen50 : nums.val.length ≤ 50)
    (hval : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100)
    (hsorted : ∀ i, i + 1 < nums.val.length → (nums.val[i]!).val ≥ (nums.val[i+1]!).val) :
    ∀ r, count_quadruplets nums = ok r → r.val = 0 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen4 : 4 ≤ nums.val.length) (hlen50 : nums.val.length ≤ 50)
    (hval : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100)
    (hsorted : ∀ i, i + 1 < nums.val.length → (nums.val[i]!).val ≥ (nums.val[i+1]!).val), ∀ r, count_quadruplets nums = ok r → r.val = 0) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if there do not exist integers a,b,c,d with 0 <= a < b < c < d < len(nums) and nums[a] + nums[b] + nums[c] = nums[d].
  Preconditions: 4 <= len(nums) <= 50 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
theorem spec_5 (nums : Slice I64)
    (hlen4 : 4 ≤ nums.val.length) (hlen50 : nums.val.length ≤ 50)
    (hval : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100) :
    ∀ r, count_quadruplets nums = ok r →
      (r.val = 0 ↔
        ¬ ∃ a b c d : Nat, a < b ∧ b < c ∧ c < d ∧ d < nums.val.length ∧
          (nums.val[a]!).val + (nums.val[b]!).val + (nums.val[c]!).val = (nums.val[d]!).val) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen4 : 4 ≤ nums.val.length) (hlen50 : nums.val.length ≤ 50)
    (hval : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100), ∀ r, count_quadruplets nums = ok r →
      (r.val = 0 ↔
        ¬ ∃ a b c d : Nat, a < b ∧ b < c ∧ c < d ∧ d < nums.val.length ∧
          (nums.val[a]!).val + (nums.val[b]!).val + (nums.val[c]!).val = (nums.val[d]!).val)) := by
  sorry

/-- Whenever the function returns a result r, r = sum_{d=0}^{len(nums)-1} T(d), where for each integer d with 0 <= d < len(nums), T(d) is the number of triples (a,b,c) of integers such that 0 <= a < b < c < d and nums[a] + nums[b] + nums[c] = nums[d].
  Preconditions: 4 <= len(nums) <= 50 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
theorem spec_6 (nums : Slice I64)
    (hlen4 : 4 ≤ nums.val.length) (hlen50 : nums.val.length ≤ 50)
    (hval : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100) :
    ∀ r, count_quadruplets nums = ok r →
      r.val = Finset.sum (Finset.range nums.val.length)
        (fun d => (tripleCountBelow nums d (nums.val[d]!).val : Int)) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen4 : 4 ≤ nums.val.length) (hlen50 : nums.val.length ≤ 50)
    (hval : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100), ∀ r, count_quadruplets nums = ok r →
      r.val = Finset.sum (Finset.range nums.val.length)
        (fun d => (tripleCountBelow nums d (nums.val[d]!).val : Int))) := by
  sorry

/-- Whenever count_quadruplets(xs) returns a result r and count_quadruplets(ys) returns a result s, s = r + T, where T is the number of triples (a,b,c) of integers such that 0 <= a < b < c < n and xs[a] + xs[b] + xs[c] = x.
  Preconditions: Let n = len(xs). Assume 4 <= n <= 49, for every i with 0 <= i < n, 1 <= xs[i] <= 100, and x is an integer with 1 <= x <= 100. Let ys be a slice of length n+1 such that ys[i] = xs[i] for every 0 <= i < n and ys[n] = x. -/
theorem spec_7 (xs ys : Slice I64) (x : Int) (n : Nat)
    (hxslen : xs.val.length = n) (hyslen : ys.val.length = n + 1)
    (hlen4 : 4 ≤ n) (hlen49 : n ≤ 49)
    (hxval : ∀ i, i < n → 1 ≤ (xs.val[i]!).val ∧ (xs.val[i]!).val ≤ 100)
    (hx1 : 1 ≤ x) (hx100 : x ≤ 100)
    (hys : ∀ i, i < n → (ys.val[i]!).val = (xs.val[i]!).val)
    (hysn : (ys.val[n]!).val = x) :
    ∀ r s, count_quadruplets xs = ok r → count_quadruplets ys = ok s →
      s.val = r.val + (tripleCountBelow xs n x : Int) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (xs ys : Slice I64) (x : Int) (n : Nat)
    (hxslen : xs.val.length = n) (hyslen : ys.val.length = n + 1)
    (hlen4 : 4 ≤ n) (hlen49 : n ≤ 49)
    (hxval : ∀ i, i < n → 1 ≤ (xs.val[i]!).val ∧ (xs.val[i]!).val ≤ 100)
    (hx1 : 1 ≤ x) (hx100 : x ≤ 100)
    (hys : ∀ i, i < n → (ys.val[i]!).val = (xs.val[i]!).val)
    (hysn : (ys.val[n]!).val = x), ∀ r s, count_quadruplets xs = ok r → count_quadruplets ys = ok s →
      s.val = r.val + (tripleCountBelow xs n x : Int)) := by
  sorry

/-- Whenever count_quadruplets(nums) returns a result r and count_quadruplets(p) returns a result s, s <= r.
  Preconditions: Let n = len(nums). Assume 4 <= n <= 50, for every i with 0 <= i < n, 1 <= nums[i] <= 100, and m is an integer with 4 <= m <= n. Let p be the prefix slice of length m with p[i] = nums[i] for every 0 <= i < m. -/
theorem spec_8 (nums p : Slice I64) (n m : Nat)
    (hn : nums.val.length = n) (h4 : 4 ≤ n) (h50 : n ≤ 50)
    (hval : ∀ i, i < n → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100)
    (hm4 : 4 ≤ m) (hmn : m ≤ n)
    (hp : p.val.length = m)
    (hpre : ∀ i, i < m → (p.val[i]!).val = (nums.val[i]!).val) :
    ∀ r s, count_quadruplets nums = ok r → count_quadruplets p = ok s → s.val ≤ r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums p : Slice I64) (n m : Nat)
    (hn : nums.val.length = n) (h4 : 4 ≤ n) (h50 : n ≤ 50)
    (hval : ∀ i, i < n → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100)
    (hm4 : 4 ≤ m) (hmn : m ≤ n)
    (hp : p.val.length = m)
    (hpre : ∀ i, i < m → (p.val[i]!).val = (nums.val[i]!).val), ∀ r s, count_quadruplets nums = ok r → count_quadruplets p = ok s → s.val ≤ r.val) := by
  sorry

/-- Whenever count_quadruplets(xs) returns a result r and count_quadruplets(ys) returns a result s, r = s.
  Preconditions: Let xs and ys be slices of the same length n with 4 <= n <= 50, and assume for every i with 0 <= i < n, 1 <= xs[i] <= 100 and 1 <= ys[i] <= 100. Assume there exists a positive integer k such that ys[i] = k * xs[i] for every 0 <= i < n. -/
theorem spec_9 (xs ys : Slice I64) (n k : Nat)
    (hxs : xs.val.length = n) (hys : ys.val.length = n)
    (h4 : 4 ≤ n) (h50 : n ≤ 50)
    (hxval : ∀ i, i < n → 1 ≤ (xs.val[i]!).val ∧ (xs.val[i]!).val ≤ 100)
    (hyval : ∀ i, i < n → 1 ≤ (ys.val[i]!).val ∧ (ys.val[i]!).val ≤ 100)
    (hkpos : 0 < k)
    (hmul : ∀ i, i < n → (ys.val[i]!).val = (k : Int) * (xs.val[i]!).val) :
    ∀ r s, count_quadruplets xs = ok r → count_quadruplets ys = ok s → r.val = s.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (xs ys : Slice I64) (n k : Nat)
    (hxs : xs.val.length = n) (hys : ys.val.length = n)
    (h4 : 4 ≤ n) (h50 : n ≤ 50)
    (hxval : ∀ i, i < n → 1 ≤ (xs.val[i]!).val ∧ (xs.val[i]!).val ≤ 100)
    (hyval : ∀ i, i < n → 1 ≤ (ys.val[i]!).val ∧ (ys.val[i]!).val ≤ 100)
    (hkpos : 0 < k)
    (hmul : ∀ i, i < n → (ys.val[i]!).val = (k : Int) * (xs.val[i]!).val), ∀ r s, count_quadruplets xs = ok r → count_quadruplets ys = ok s → r.val = s.val) := by
  sorry

/-- Whenever the function returns a result r, r <= U, where U is the number of index quadruplets (a,b,c,d) with 0 <= a < b < c < d < len(nums) and nums[a] + nums[b] + nums[c] <= 100.
  Preconditions: 4 <= len(nums) <= 50 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
theorem spec_10 (nums : Slice I64)
    (hlen4 : 4 ≤ nums.val.length) (hlen50 : nums.val.length ≤ 50)
    (hval : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100) :
    ∀ r, count_quadruplets nums = ok r → r.val ≤ (quadCountSumLE nums 100 : Int) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen4 : 4 ≤ nums.val.length) (hlen50 : nums.val.length ≤ 50)
    (hval : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100), ∀ r, count_quadruplets nums = ok r → r.val ≤ (quadCountSumLE nums 100 : Int)) := by
  sorry

end AegisSpec.CountQuadruplets
