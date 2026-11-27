import Aegis.MaximumTripletValue.Code.Funs

/-!
# Specifications of `Aegis.MaximumTripletValue.maximum_triplet_value`

LeetCode problem `maximum-value-of-an-ordered-triplet-i`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MaximumTripletValue

namespace AegisSpec.MaximumTripletValue

def entries (nums : Slice I64) : List ℤ := nums.val.map (fun x => x.val)

def tripletValue (nums : Slice I64) (i j k : ℕ) : ℤ :=
  ((nums.val.getD i 0#i64).val - (nums.val.getD j 0#i64).val) * (nums.val.getD k 0#i64).val

def orderedTriplets (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.range n).product ((Finset.range n).product (Finset.range n))).filter
    (fun p => p.1 < p.2.1 ∧ p.2.1 < p.2.2)

def tripletValues (nums : Slice I64) : Finset ℤ :=
  (orderedTriplets nums.val.length).image (fun p => tripletValue nums p.1 p.2.1 p.2.2)

noncomputable def maxTripletValue (nums : Slice I64) : ℤ :=
  max 0 (if h : (tripletValues nums).Nonempty then (tripletValues nums).max' h else 0)

def listMax (l : List ℤ) : ℤ :=
  match l with
  | [] => 0
  | a :: t => t.foldl max a

def listMin (l : List ℤ) : ℤ :=
  match l with
  | [] => 0
  | a :: t => t.foldl min a

/-- Whenever maximum_triplet_value(nums) returns a result r, r is equal to max(0, max { (nums[i] - nums[j]) * nums[k] | 0 <= i < j < k < len(nums) }). The inner maximum ranges over the nonempty finite set of all ordered index triplets with i < j < k; the outer max clamps a nonpositive maximum to 0.
  Preconditions: 3 <= len(nums) <= 100 and for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 10^6. -/
theorem spec_1 (nums : Slice I64)
    (hlen : 3 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
    (helems : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 6)
    (r : I64) (hr : maximum_triplet_value nums = ok r) :
    r.val = maxTripletValue nums := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen : 3 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
    (helems : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 6)
    (r : I64) (hr : maximum_triplet_value nums = ok r), r.val = maxTripletValue nums) := by
  sorry

/-- For every input satisfying the preconditions, maximum_triplet_value(nums) returns a successful result (Result.ok r); in particular, it does not fail by out-of-bounds indexing, panic, or i64 arithmetic overflow.
  Preconditions: 3 <= len(nums) <= 100 and for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 10^6. -/
theorem spec_2 (nums : Slice I64)
    (hlen : 3 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
    (helems : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 6) :
    ∃ r : I64, maximum_triplet_value nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen : 3 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
    (helems : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 6), ∃ r : I64, maximum_triplet_value nums = ok r) := by
  sorry

/-- Whenever maximum_triplet_value(nums) returns a result r, 0 <= r.
  Preconditions: 3 <= len(nums) <= 100 and for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 10^6. -/
theorem spec_3 (nums : Slice I64)
    (hlen : 3 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
    (helems : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 6)
    (r : I64) (hr : maximum_triplet_value nums = ok r) :
    0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen : 3 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
    (helems : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 6)
    (r : I64) (hr : maximum_triplet_value nums = ok r), 0 ≤ r.val) := by
  sorry

/-- Whenever maximum_triplet_value(nums) returns a result r, for every index triplet (i, j, k) with 0 <= i < j < k < len(nums), (nums[i] - nums[j]) * nums[k] <= r.
  Preconditions: 3 <= len(nums) <= 100 and for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 10^6. -/
theorem spec_4 (nums : Slice I64)
    (hlen : 3 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
    (helems : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 6)
    (r : I64) (hr : maximum_triplet_value nums = ok r)
    (i j k : ℕ) (hij : i < j) (hjk : j < k) (hk : k < nums.val.length) :
    ((nums.val[i]).val - (nums.val[j]).val) * (nums.val[k]).val ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen : 3 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
    (helems : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 6)
    (r : I64) (hr : maximum_triplet_value nums = ok r)
    (i j k : ℕ) (hij : i < j) (hjk : j < k) (hk : k < nums.val.length), ((nums.val[i]).val - (nums.val[j]).val) * (nums.val[k]).val ≤ r.val) := by
  sorry

/-- Whenever maximum_triplet_value(nums) returns a result r and r > 0, there exist indices i, j, k with 0 <= i < j < k < len(nums) such that (nums[i] - nums[j]) * nums[k] = r.
  Preconditions: 3 <= len(nums) <= 100 and for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 10^6. -/
theorem spec_5 (nums : Slice I64)
    (hlen : 3 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
    (helems : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 6)
    (r : I64) (hr : maximum_triplet_value nums = ok r) (hpos : 0 < r.val) :
    ∃ (i j k : ℕ) (hij : i < j) (hjk : j < k) (hk : k < nums.val.length),
      ((nums.val[i]).val - (nums.val[j]).val) * (nums.val[k]).val = r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen : 3 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
    (helems : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 6)
    (r : I64) (hr : maximum_triplet_value nums = ok r) (hpos : 0 < r.val), ∃ (i j k : ℕ) (hij : i < j) (hjk : j < k) (hk : k < nums.val.length),
      ((nums.val[i]).val - (nums.val[j]).val) * (nums.val[k]).val = r.val) := by
  sorry

/-- Whenever maximum_triplet_value(nums) returns a result r, r = 0 if and only if for every index triplet (i, j, k) with 0 <= i < j < k < len(nums), (nums[i] - nums[j]) * nums[k] <= 0.
  Preconditions: 3 <= len(nums) <= 100 and for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 10^6. -/
theorem spec_6 (nums : Slice I64)
    (hlen : 3 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
    (helems : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 6)
    (r : I64) (hr : maximum_triplet_value nums = ok r) :
    (r.val = 0 ↔
      ∀ (i j k : ℕ) (hij : i < j) (hjk : j < k) (hk : k < nums.val.length),
        ((nums.val[i]).val - (nums.val[j]).val) * (nums.val[k]).val ≤ 0) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen : 3 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
    (helems : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 6)
    (r : I64) (hr : maximum_triplet_value nums = ok r), (r.val = 0 ↔
      ∀ (i j k : ℕ) (hij : i < j) (hjk : j < k) (hk : k < nums.val.length),
        ((nums.val[i]).val - (nums.val[j]).val) * (nums.val[k]).val ≤ 0)) := by
  sorry

/-- Whenever maximum_triplet_value(nums) returns a result r and nums is nondecreasing, that is for all 0 <= i < j < len(nums), nums[i] <= nums[j], we have r = 0.
  Preconditions: 3 <= len(nums) <= 100 and for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 10^6. -/
theorem spec_7 (nums : Slice I64)
    (hlen : 3 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
    (helems : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 6)
    (hmono : ∀ (i j : ℕ) (hij : i < j) (hj : j < nums.val.length),
      (nums.val[i]).val ≤ (nums.val[j]).val)
    (r : I64) (hr : maximum_triplet_value nums = ok r) :
    r.val = 0 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen : 3 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
    (helems : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 6)
    (hmono : ∀ (i j : ℕ) (hij : i < j) (hj : j < nums.val.length),
      (nums.val[i]).val ≤ (nums.val[j]).val)
    (r : I64) (hr : maximum_triplet_value nums = ok r), r.val = 0) := by
  sorry

/-- Whenever maximum_triplet_value(nums) returns a result r, r <= (max(nums) - min(nums)) * max(nums), where max(nums) and min(nums) denote the maximum and minimum entries of nums.
  Preconditions: 3 <= len(nums) <= 100 and for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 10^6. -/
theorem spec_8 (nums : Slice I64)
    (hlen : 3 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
    (helems : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 6)
    (r : I64) (hr : maximum_triplet_value nums = ok r) :
    r.val ≤ (listMax (entries nums) - listMin (entries nums)) * listMax (entries nums) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen : 3 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
    (helems : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 6)
    (r : I64) (hr : maximum_triplet_value nums = ok r), r.val ≤ (listMax (entries nums) - listMin (entries nums)) * listMax (entries nums)) := by
  sorry

/-- Whenever maximum_triplet_value(nums) returns a result r and maximum_triplet_value(other) returns a result s, s >= r.
  Preconditions: nums and other are slices satisfying the problem constraints: 3 <= len(nums) <= 100, 3 <= len(other) <= 100, for every 0 <= i < len(nums), 1 <= nums[i] <= 10^6, and for every 0 <= i < len(other), 1 <= other[i] <= 10^6. Also len(other) = len(nums) + 1, other[i] = nums[i] for every 0 <= i < len(nums), and other[len(nums)] >= 1. -/
theorem spec_9 (nums other : Slice I64)
    (hlen : 3 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
    (helems : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 6)
    (hlen2 : 3 ≤ other.val.length) (hlen2' : other.val.length ≤ 100)
    (helems2 : ∀ (i : ℕ) (hi : i < other.val.length),
      1 ≤ (other.val[i]).val ∧ (other.val[i]).val ≤ 10 ^ 6)
    (hlenlen : other.val.length = nums.val.length + 1)
    (hprefix : ∀ (i : ℕ) (hi : i < nums.val.length), (other.val[i]).val = (nums.val[i]).val)
    (hlast : 1 ≤ (other.val[nums.val.length]).val)
    (r s : I64) (hr : maximum_triplet_value nums = ok r)
    (hs : maximum_triplet_value other = ok s) :
    r.val ≤ s.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums other : Slice I64)
    (hlen : 3 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
    (helems : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 6)
    (hlen2 : 3 ≤ other.val.length) (hlen2' : other.val.length ≤ 100)
    (helems2 : ∀ (i : ℕ) (hi : i < other.val.length),
      1 ≤ (other.val[i]).val ∧ (other.val[i]).val ≤ 10 ^ 6)
    (hlenlen : other.val.length = nums.val.length + 1)
    (hprefix : ∀ (i : ℕ) (hi : i < nums.val.length), (other.val[i]).val = (nums.val[i]).val)
    (hlast : 1 ≤ (other.val[nums.val.length]).val)
    (r s : I64) (hr : maximum_triplet_value nums = ok r)
    (hs : maximum_triplet_value other = ok s), r.val ≤ s.val) := by
  sorry

/-- Whenever maximum_triplet_value(nums) returns a result r and maximum_triplet_value(scaled) returns a result r', r' = c * c * r.
  Preconditions: nums and scaled are slices satisfying the problem constraints: 3 <= len(nums) <= 100, 3 <= len(scaled) <= 100, for every 0 <= i < len(nums), 1 <= nums[i] <= 10^6, and for every 0 <= i < len(scaled), 1 <= scaled[i] <= 10^6. There exists an integer c with 1 <= c <= 10^6 such that len(scaled) = len(nums), scaled[i] = c * nums[i] for every 0 <= i < len(nums), and every scaled[i] is in 1 .. 10^6. -/
theorem spec_10 (nums scaled : Slice I64)
    (hlen : 3 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
    (helems : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 6)
    (hlen2 : 3 ≤ scaled.val.length) (hlen2' : scaled.val.length ≤ 100)
    (helems2 : ∀ (i : ℕ) (hi : i < scaled.val.length),
      1 ≤ (scaled.val[i]).val ∧ (scaled.val[i]).val ≤ 10 ^ 6)
    (c : ℤ) (hc1 : 1 ≤ c) (hc6 : c ≤ 10 ^ 6)
    (hlenlen : scaled.val.length = nums.val.length)
    (hscale : ∀ (i : ℕ) (hi : i < nums.val.length), (scaled.val[i]).val = c * (nums.val[i]).val)
    (r r' : I64) (hr : maximum_triplet_value nums = ok r)
    (hr' : maximum_triplet_value scaled = ok r') :
    r'.val = c * c * r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums scaled : Slice I64)
    (hlen : 3 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
    (helems : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 6)
    (hlen2 : 3 ≤ scaled.val.length) (hlen2' : scaled.val.length ≤ 100)
    (helems2 : ∀ (i : ℕ) (hi : i < scaled.val.length),
      1 ≤ (scaled.val[i]).val ∧ (scaled.val[i]).val ≤ 10 ^ 6)
    (c : ℤ) (hc1 : 1 ≤ c) (hc6 : c ≤ 10 ^ 6)
    (hlenlen : scaled.val.length = nums.val.length)
    (hscale : ∀ (i : ℕ) (hi : i < nums.val.length), (scaled.val[i]).val = c * (nums.val[i]).val)
    (r r' : I64) (hr : maximum_triplet_value nums = ok r)
    (hr' : maximum_triplet_value scaled = ok r'), r'.val = c * c * r.val) := by
  sorry

end AegisSpec.MaximumTripletValue
