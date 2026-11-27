import Aegis.TotalSteps.Code.Funs

/-!
# Specifications of `Aegis.TotalSteps.total_steps`

LeetCode problem `steps-to-make-array-non-decreasing`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.TotalSteps

namespace AegisSpec.TotalSteps

def nextAux : Std.I64 → List Std.I64 → List Std.I64
  | _, [] => []
  | prev, x :: xs => if prev.val ≤ x.val then x :: nextAux x xs else nextAux x xs

def next : List Std.I64 → List Std.I64
  | [] => []
  | x :: xs => x :: nextAux x xs

def step : ℕ → List Std.I64 → List Std.I64
  | 0, xs => xs
  | k + 1, xs => next (step k xs)

def IsNondecreasing (xs : List Std.I64) : Prop :=
  ∀ (i : ℕ) (h0 : 0 < i) (hi : i < xs.length), (xs[i - 1]'(by omega)).val ≤ (xs[i]'hi).val

def IsLeastSteps (xs : List Std.I64) (r : ℕ) : Prop :=
  IsNondecreasing (step r xs) ∧ ∀ k : ℕ, k < r → ¬ IsNondecreasing (step k xs)

def ValuesInRange (xs : List Std.I64) : Prop :=
  ∀ (i : ℕ) (hi : i < xs.length), 1 ≤ (xs[i]'hi).val ∧ (xs[i]'hi).val ≤ 1000000000

def SameWeakOrder (xs ys : List Std.I64) : Prop :=
  ∀ (i j : ℕ) (hxi : i < xs.length) (hxj : j < xs.length)
    (hyi : i < ys.length) (hyj : j < ys.length),
    (xs[i]'hxi).val ≤ (xs[j]'hxj).val ↔ (ys[i]'hyi).val ≤ (ys[j]'hyj).val

def prefixMaximaAux (m : Int) : List Std.I64 → List Std.I64
  | [] => []
  | x :: xs =>
    if m ≤ x.val then x :: prefixMaximaAux (max m x.val) xs
    else prefixMaximaAux (max m x.val) xs

def prefixMaxima : List Std.I64 → List Std.I64
  | [] => []
  | x :: xs => x :: prefixMaximaAux x.val xs

/-- Define next(xs), for a nonempty list xs, as the list consisting of xs[0] followed, in increasing order of original index, by exactly those xs[i] with 0 < i < len(xs) and xs[i-1] <= xs[i]. Define step^0(nums) = nums and step^{k+1}(nums) = next(step^k(nums)). The function returns a result r and r is the least nonnegative integer k such that step^k(nums) is non-decreasing, i.e. for every j with 0 < j < len(step^k(nums)), step^k(nums)[j-1] <= step^k(nums)[j].
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
theorem spec_1 (nums : Slice Std.I64) (hlen1 : 1 ≤ nums.val.length)
    (hlen2 : nums.val.length ≤ 100000) (hvals : ValuesInRange nums.val) :
    ∃ r : Std.I64, total_steps nums = ok r ∧ IsLeastSteps nums.val r.val.toNat := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (hlen1 : 1 ≤ nums.val.length)
    (hlen2 : nums.val.length ≤ 100000) (hvals : ValuesInRange nums.val), ∃ r : Std.I64, total_steps nums = ok r ∧ IsLeastSteps nums.val r.val.toNat) := by
  sorry

/-- The function returns a result r and does not fail.
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
theorem spec_2 (nums : Slice Std.I64) (hlen1 : 1 ≤ nums.val.length)
    (hlen2 : nums.val.length ≤ 100000) (hvals : ValuesInRange nums.val) :
    ∃ r : Std.I64, total_steps nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (hlen1 : 1 ≤ nums.val.length)
    (hlen2 : nums.val.length ≤ 100000) (hvals : ValuesInRange nums.val), ∃ r : Std.I64, total_steps nums = ok r) := by
  sorry

/-- The function returns a result r and 0 <= r <= len(nums) - 1.
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
theorem spec_3 (nums : Slice Std.I64) (hlen1 : 1 ≤ nums.val.length)
    (hlen2 : nums.val.length ≤ 100000) (hvals : ValuesInRange nums.val) :
    ∃ r : Std.I64, total_steps nums = ok r ∧ 0 ≤ r.val ∧ r.val ≤ (nums.val.length : Int) - 1 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (hlen1 : 1 ≤ nums.val.length)
    (hlen2 : nums.val.length ≤ 100000) (hvals : ValuesInRange nums.val), ∃ r : Std.I64, total_steps nums = ok r ∧ 0 ≤ r.val ∧ r.val ≤ (nums.val.length : Int) - 1) := by
  sorry

/-- The function returns a result r and r = 0 if and only if nums is non-decreasing, i.e. for every i with 0 < i < len(nums), nums[i-1] <= nums[i].
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
theorem spec_4 (nums : Slice Std.I64) (hlen1 : 1 ≤ nums.val.length)
    (hlen2 : nums.val.length ≤ 100000) (hvals : ValuesInRange nums.val) :
    ∃ r : Std.I64, total_steps nums = ok r ∧ (r.val = 0 ↔ IsNondecreasing nums.val) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (hlen1 : 1 ≤ nums.val.length)
    (hlen2 : nums.val.length ≤ 100000) (hvals : ValuesInRange nums.val), ∃ r : Std.I64, total_steps nums = ok r ∧ (r.val = 0 ↔ IsNondecreasing nums.val)) := by
  sorry

/-- Define next(xs), for a nonempty list xs, as the list consisting of xs[0] followed, in increasing order of original index, by exactly those xs[i] with 0 < i < len(xs) and xs[i-1] <= xs[i]. Define step^0(nums) = nums and step^{k+1}(nums) = next(step^k(nums)). Whenever total_steps(nums) returns r, for every integer k >= 0, step^{r+k}(nums) = step^r(nums).
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
theorem spec_5 (nums : Slice Std.I64) (hlen1 : 1 ≤ nums.val.length)
    (hlen2 : nums.val.length ≤ 100000) (hvals : ValuesInRange nums.val) :
    ∀ r : Std.I64, total_steps nums = ok r →
      ∀ k : ℕ, step (r.val.toNat + k) nums.val = step r.val.toNat nums.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (hlen1 : 1 ≤ nums.val.length)
    (hlen2 : nums.val.length ≤ 100000) (hvals : ValuesInRange nums.val), ∀ r : Std.I64, total_steps nums = ok r →
      ∀ k : ℕ, step (r.val.toNat + k) nums.val = step r.val.toNat nums.val) := by
  sorry

/-- Define next(xs), for a nonempty list xs, as the list consisting of xs[0] followed, in increasing order of original index, by exactly those xs[i] with 0 < i < len(xs) and xs[i-1] <= xs[i]. Define step^0(nums) = nums and step^{k+1}(nums) = next(step^k(nums)). Whenever total_steps(nums) returns r, for every k with 1 <= k <= r, len(step^k(nums)) < len(step^{k-1}(nums)).
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
theorem spec_6 (nums : Slice Std.I64) (hlen1 : 1 ≤ nums.val.length)
    (hlen2 : nums.val.length ≤ 100000) (hvals : ValuesInRange nums.val) :
    ∀ r : Std.I64, total_steps nums = ok r →
      ∀ k : ℕ, 1 ≤ k → k ≤ r.val.toNat →
        (step k nums.val).length < (step (k - 1) nums.val).length := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (hlen1 : 1 ≤ nums.val.length)
    (hlen2 : nums.val.length ≤ 100000) (hvals : ValuesInRange nums.val), ∀ r : Std.I64, total_steps nums = ok r →
      ∀ k : ℕ, 1 ≤ k → k ≤ r.val.toNat →
        (step k nums.val).length < (step (k - 1) nums.val).length) := by
  sorry

/-- Define next(xs), for a nonempty list xs, as the list consisting of xs[0] followed, in increasing order of original index, by exactly those xs[i] with 0 < i < len(xs) and xs[i-1] <= xs[i]. Define step^0(nums) = nums and step^{k+1}(nums) = next(step^k(nums)). Whenever total_steps(nums) returns r, for every k with 0 <= k <= r, step^k(nums) is nonempty and step^k(nums)[0] = nums[0].
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
theorem spec_7 (nums : Slice Std.I64) (hlen1 : 1 ≤ nums.val.length)
    (hlen2 : nums.val.length ≤ 100000) (hvals : ValuesInRange nums.val) :
    ∀ r : Std.I64, total_steps nums = ok r →
      ∀ k : ℕ, k ≤ r.val.toNat →
        1 ≤ (step k nums.val).length ∧ (step k nums.val).head? = nums.val.head? := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (hlen1 : 1 ≤ nums.val.length)
    (hlen2 : nums.val.length ≤ 100000) (hvals : ValuesInRange nums.val), ∀ r : Std.I64, total_steps nums = ok r →
      ∀ k : ℕ, k ≤ r.val.toNat →
        1 ≤ (step k nums.val).length ∧ (step k nums.val).head? = nums.val.head?) := by
  sorry

/-- Whenever total_steps(nums) returns r, for every list ys satisfying 1 <= len(ys) <= 100000, 1 <= ys[i] <= 1000000000 for all i with 0 <= i < len(ys), len(ys) = len(nums), and for all i,j with 0 <= i < len(nums) and 0 <= j < len(nums), nums[i] <= nums[j] if and only if ys[i] <= ys[j], if total_steps(ys) returns r', then r' = r.
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
theorem spec_8 (nums : Slice Std.I64) (hlen1 : 1 ≤ nums.val.length)
    (hlen2 : nums.val.length ≤ 100000) (hvals : ValuesInRange nums.val) :
    ∀ r : Std.I64, total_steps nums = ok r →
      ∀ ys : Slice Std.I64, 1 ≤ ys.val.length → ys.val.length ≤ 100000 →
        ValuesInRange ys.val → ys.val.length = nums.val.length →
          SameWeakOrder nums.val ys.val →
            ∀ r' : Std.I64, total_steps ys = ok r' → r' = r := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (hlen1 : 1 ≤ nums.val.length)
    (hlen2 : nums.val.length ≤ 100000) (hvals : ValuesInRange nums.val), ∀ r : Std.I64, total_steps nums = ok r →
      ∀ ys : Slice Std.I64, 1 ≤ ys.val.length → ys.val.length ≤ 100000 →
        ValuesInRange ys.val → ys.val.length = nums.val.length →
          SameWeakOrder nums.val ys.val →
            ∀ r' : Std.I64, total_steps ys = ok r' → r' = r) := by
  sorry

/-- Define next(xs), for a nonempty list xs, as the list consisting of xs[0] followed, in increasing order of original index, by exactly those xs[i] with 0 < i < len(xs) and xs[i-1] <= xs[i]. Define step^0(nums) = nums and step^{k+1}(nums) = next(step^k(nums)). Whenever total_steps(nums) returns r, len(step^r(nums)) <= len(nums) - r.
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
theorem spec_9 (nums : Slice Std.I64) (hlen1 : 1 ≤ nums.val.length)
    (hlen2 : nums.val.length ≤ 100000) (hvals : ValuesInRange nums.val) :
    ∀ r : Std.I64, total_steps nums = ok r →
      ((step r.val.toNat nums.val).length : Int) ≤ (nums.val.length : Int) - r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64) (hlen1 : 1 ≤ nums.val.length)
    (hlen2 : nums.val.length ≤ 100000) (hvals : ValuesInRange nums.val), ∀ r : Std.I64, total_steps nums = ok r →
      ((step r.val.toNat nums.val).length : Int) ≤ (nums.val.length : Int) - r.val) := by
  sorry

/-- Define next and step as in spec_1. Whenever total_steps(nums) returns r, step^r(nums) is exactly the list, in increasing order of i, of those nums[i] with 0 <= i < len(nums) and for every j with 0 <= j < i, nums[j] <= nums[i]. Equivalently, after the process terminates the remaining elements are precisely the non-strict prefix maxima of nums.
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
theorem spec_10 (nums : Slice Std.I64) (hlen1 : 1 ≤ nums.val.length)
    (hlen2 : nums.val.length ≤ 100000) (hvals : ValuesInRange nums.val) :
    ∀ r : Std.I64, total_steps nums = ok r →
      step r.val.toNat nums.val = prefixMaxima nums.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64) (hlen1 : 1 ≤ nums.val.length)
    (hlen2 : nums.val.length ≤ 100000) (hvals : ValuesInRange nums.val), ∀ r : Std.I64, total_steps nums = ok r →
      step r.val.toNat nums.val = prefixMaxima nums.val) := by
  sorry

end AegisSpec.TotalSteps
