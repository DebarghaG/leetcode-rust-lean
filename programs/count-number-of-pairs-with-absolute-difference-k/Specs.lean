import Aegis.CountKDifference.Code.Funs

/-!
# Specifications of `Aegis.CountKDifference.count_k_difference`

LeetCode problem `count-number-of-pairs-with-absolute-difference-k`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.CountKDifference (count_k_difference)

namespace AegisSpec.CountKDifference

def vals (nums : Slice I64) : List ℤ := nums.val.map (fun x => x.val)

@[simp] theorem vals_length (nums : Slice I64) : (vals nums).length = nums.val.length := by
  simp [vals]

def freq (l : List ℤ) (v : ℤ) : ℕ := (l.filter (fun x => x = v)).length

def pairCount (l : List ℤ) (k : ℤ) : ℕ :=
  (((Finset.range l.length).product (Finset.range l.length)).filter
    (fun p => p.1 < p.2 ∧ |l.getD p.1 0 - l.getD p.2 0| = k)).card

def orderedPairCount (l : List ℤ) (k : ℤ) : ℕ :=
  (((Finset.range l.length).product (Finset.range l.length)).filter
    (fun p => p.1 ≠ p.2 ∧ |l.getD p.1 0 - l.getD p.2 0| = k)).card

def HasPair (l : List ℤ) (k : ℤ) : Prop :=
  ∃ i j : ℕ, i < j ∧ j < l.length ∧ |l.getD i 0 - l.getD j 0| = k

def lmax (l : List ℤ) : ℤ := l.foldr max (l.headD 0)

def lmin (l : List ℤ) : ℤ := l.foldr min (l.headD 0)

def equalPairSum (l : List ℤ) : ℕ :=
  ∑ v ∈ Finset.Icc (1 : ℕ) 100, freq l (v : ℤ) * (freq l (v : ℤ) - 1) / 2

def diffPairSum (l : List ℤ) (k : ℤ) : ℕ :=
  ∑ v ∈ Finset.Icc (1 : ℕ) 100, freq l (v : ℤ) * freq l ((v : ℤ) + k)

def IsFlip (flip nums : Slice I64) : Prop :=
  ∀ i : ℕ, i < (vals nums).length → (vals flip).getD i 0 = 101 - (vals nums).getD i 0

def IsShift (nums' nums : Slice I64) (c : ℤ) : Prop :=
  ∀ i : ℕ, i < (vals nums).length → (vals nums').getD i 0 = (vals nums).getD i 0 + c

/-- Whenever the function returns a result r, r equals the number of pairs (i, j) of indices such that 0 <= i < j < len(nums) and |nums[i] - nums[j]| == k, where |x| = x if x >= 0 and |x| = -x if x < 0.
  Preconditions: 1 <= len(nums) <= 200; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100; 0 <= k <= 99. -/
theorem spec_1 (nums : Slice I64) (k : I64) (r : I64)
    (hlen : 1 ≤ (vals nums).length ∧ (vals nums).length ≤ 200)
    (helem : ∀ (i : ℕ) (_ : i < (vals nums).length),
      1 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 100)
    (hk : 0 ≤ k.val ∧ k.val ≤ 99)
    (hres : count_k_difference nums k = ok r) :
    r.val = (pairCount (vals nums) k.val : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (r : I64)
    (hlen : 1 ≤ (vals nums).length ∧ (vals nums).length ≤ 200)
    (helem : ∀ (i : ℕ) (_ : i < (vals nums).length),
      1 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 100)
    (hk : 0 ≤ k.val ∧ k.val ≤ 99)
    (hres : count_k_difference nums k = ok r), r.val = (pairCount (vals nums) k.val : ℤ)) := by
  sorry

/-- The function returns a result r (it does not fail, panic, or overflow) for every input satisfying the preconditions.
  Preconditions: 1 <= len(nums) <= 200; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100; 0 <= k <= 99. -/
theorem spec_2 (nums : Slice I64) (k : I64)
    (hlen : 1 ≤ (vals nums).length ∧ (vals nums).length ≤ 200)
    (helem : ∀ (i : ℕ) (_ : i < (vals nums).length),
      1 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 100)
    (hk : 0 ≤ k.val ∧ k.val ≤ 99) :
    ∃ r : I64, count_k_difference nums k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice I64) (k : I64)
    (hlen : 1 ≤ (vals nums).length ∧ (vals nums).length ≤ 200)
    (helem : ∀ (i : ℕ) (_ : i < (vals nums).length),
      1 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 100)
    (hk : 0 ≤ k.val ∧ k.val ≤ 99), ∃ r : I64, count_k_difference nums k = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r <= len(nums) * (len(nums) - 1) / 2.
  Preconditions: 1 <= len(nums) <= 200; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100; 0 <= k <= 99. -/
theorem spec_3 (nums : Slice I64) (k : I64) (r : I64)
    (hlen : 1 ≤ (vals nums).length ∧ (vals nums).length ≤ 200)
    (helem : ∀ (i : ℕ) (_ : i < (vals nums).length),
      1 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 100)
    (hk : 0 ≤ k.val ∧ k.val ≤ 99)
    (hres : count_k_difference nums k = ok r) :
    0 ≤ r.val ∧
      r.val ≤ ((vals nums).length : ℤ) * (((vals nums).length : ℤ) - 1) / 2 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (r : I64)
    (hlen : 1 ≤ (vals nums).length ∧ (vals nums).length ≤ 200)
    (helem : ∀ (i : ℕ) (_ : i < (vals nums).length),
      1 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 100)
    (hk : 0 ≤ k.val ∧ k.val ≤ 99)
    (hres : count_k_difference nums k = ok r), 0 ≤ r.val ∧
      r.val ≤ ((vals nums).length : ℤ) * (((vals nums).length : ℤ) - 1) / 2) := by
  sorry

/-- Whenever the function returns a result r, r = sum_{v=1}^{100} (f(v) * (f(v) - 1) / 2), where f(v) is the number of indices i with 0 <= i < len(nums) and nums[i] = v.
  Preconditions: 1 <= len(nums) <= 200; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100; and k = 0. -/
theorem spec_4 (nums : Slice I64) (k : I64) (r : I64)
    (hlen : 1 ≤ (vals nums).length ∧ (vals nums).length ≤ 200)
    (helem : ∀ (i : ℕ) (_ : i < (vals nums).length),
      1 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 100)
    (hk : k.val = 0)
    (hres : count_k_difference nums k = ok r) :
    r.val = (equalPairSum (vals nums) : ℤ) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (r : I64)
    (hlen : 1 ≤ (vals nums).length ∧ (vals nums).length ≤ 200)
    (helem : ∀ (i : ℕ) (_ : i < (vals nums).length),
      1 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 100)
    (hk : k.val = 0)
    (hres : count_k_difference nums k = ok r), r.val = (equalPairSum (vals nums) : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, r = 0.
  Preconditions: 1 <= len(nums) <= 200; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100; 0 <= k <= 99; and k > max(nums) - min(nums), where max(nums) and min(nums) are the maximum and minimum values in nums. -/
theorem spec_5 (nums : Slice I64) (k : I64) (r : I64)
    (hlen : 1 ≤ (vals nums).length ∧ (vals nums).length ≤ 200)
    (helem : ∀ (i : ℕ) (_ : i < (vals nums).length),
      1 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 100)
    (hk : 0 ≤ k.val ∧ k.val ≤ 99)
    (hgap : k.val > lmax (vals nums) - lmin (vals nums))
    (hres : count_k_difference nums k = ok r) :
    r.val = 0 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (r : I64)
    (hlen : 1 ≤ (vals nums).length ∧ (vals nums).length ≤ 200)
    (helem : ∀ (i : ℕ) (_ : i < (vals nums).length),
      1 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 100)
    (hk : 0 ≤ k.val ∧ k.val ≤ 99)
    (hgap : k.val > lmax (vals nums) - lmin (vals nums))
    (hres : count_k_difference nums k = ok r), r.val = 0) := by
  sorry

/-- Whenever the function returns a result r, r > 0 if and only if there exist indices i and j such that 0 <= i < j < len(nums) and |nums[i] - nums[j]| == k.
  Preconditions: 1 <= len(nums) <= 200; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100; 0 <= k <= 99. -/
theorem spec_6 (nums : Slice I64) (k : I64) (r : I64)
    (hlen : 1 ≤ (vals nums).length ∧ (vals nums).length ≤ 200)
    (helem : ∀ (i : ℕ) (_ : i < (vals nums).length),
      1 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 100)
    (hk : 0 ≤ k.val ∧ k.val ≤ 99)
    (hres : count_k_difference nums k = ok r) :
    0 < r.val ↔ HasPair (vals nums) k.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (r : I64)
    (hlen : 1 ≤ (vals nums).length ∧ (vals nums).length ≤ 200)
    (helem : ∀ (i : ℕ) (_ : i < (vals nums).length),
      1 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 100)
    (hk : 0 ≤ k.val ∧ k.val ≤ 99)
    (hres : count_k_difference nums k = ok r), 0 < r.val ↔ HasPair (vals nums) k.val) := by
  sorry

/-- Whenever count_k_difference(nums, k) returns r and count_k_difference(nums', k) returns r', we have r = r'.
  Preconditions: 1 <= len(nums) <= 200; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100; 0 <= k <= 99; and for another slice nums': 1 <= len(nums') <= 200; for every i with 0 <= i < len(nums'), 1 <= nums'[i] <= 100; len(nums') = len(nums); and there exists an integer c such that nums'[i] = nums[i] + c for all 0 <= i < len(nums). -/
theorem spec_7 (nums nums' : Slice I64) (k : I64) (r r' : I64)
    (hlen : 1 ≤ (vals nums).length ∧ (vals nums).length ≤ 200)
    (helem : ∀ (i : ℕ) (_ : i < (vals nums).length),
      1 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 100)
    (hk : 0 ≤ k.val ∧ k.val ≤ 99)
    (hlen' : 1 ≤ (vals nums').length ∧ (vals nums').length ≤ 200)
    (helem' : ∀ (i : ℕ) (_ : i < (vals nums').length),
      1 ≤ (vals nums')[i] ∧ (vals nums')[i] ≤ 100)
    (hlen_eq : (vals nums').length = (vals nums).length)
    (hshift : ∃ c : ℤ, IsShift nums' nums c)
    (hres : count_k_difference nums k = ok r)
    (hres' : count_k_difference nums' k = ok r') :
    r = r' := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums nums' : Slice I64) (k : I64) (r r' : I64)
    (hlen : 1 ≤ (vals nums).length ∧ (vals nums).length ≤ 200)
    (helem : ∀ (i : ℕ) (_ : i < (vals nums).length),
      1 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 100)
    (hk : 0 ≤ k.val ∧ k.val ≤ 99)
    (hlen' : 1 ≤ (vals nums').length ∧ (vals nums').length ≤ 200)
    (helem' : ∀ (i : ℕ) (_ : i < (vals nums').length),
      1 ≤ (vals nums')[i] ∧ (vals nums')[i] ≤ 100)
    (hlen_eq : (vals nums').length = (vals nums).length)
    (hshift : ∃ c : ℤ, IsShift nums' nums c)
    (hres : count_k_difference nums k = ok r)
    (hres' : count_k_difference nums' k = ok r'), r = r') := by
  sorry

/-- Whenever the function returns a result r, r = sum_{v=1}^{100} f(v) * f(v + k), where f(x) is the number of indices i with 0 <= i < len(nums) and nums[i] = x, and f(x) = 0 for x outside 1..100.
  Preconditions: 1 <= len(nums) <= 200; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100; and k > 0 with 0 <= k <= 99. -/
theorem spec_8 (nums : Slice I64) (k : I64) (r : I64)
    (hlen : 1 ≤ (vals nums).length ∧ (vals nums).length ≤ 200)
    (helem : ∀ (i : ℕ) (_ : i < (vals nums).length),
      1 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 100)
    (hk : 0 < k.val ∧ k.val ≤ 99)
    (hres : count_k_difference nums k = ok r) :
    r.val = (diffPairSum (vals nums) k.val : ℤ) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (r : I64)
    (hlen : 1 ≤ (vals nums).length ∧ (vals nums).length ≤ 200)
    (helem : ∀ (i : ℕ) (_ : i < (vals nums).length),
      1 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 100)
    (hk : 0 < k.val ∧ k.val ≤ 99)
    (hres : count_k_difference nums k = ok r), r.val = (diffPairSum (vals nums) k.val : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, 2 * r equals the number of ordered pairs (i, j) of indices such that 0 <= i < len(nums), 0 <= j < len(nums), i != j, and |nums[i] - nums[j]| == k.
  Preconditions: 1 <= len(nums) <= 200; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100; 0 <= k <= 99. -/
theorem spec_9 (nums : Slice I64) (k : I64) (r : I64)
    (hlen : 1 ≤ (vals nums).length ∧ (vals nums).length ≤ 200)
    (helem : ∀ (i : ℕ) (_ : i < (vals nums).length),
      1 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 100)
    (hk : 0 ≤ k.val ∧ k.val ≤ 99)
    (hres : count_k_difference nums k = ok r) :
    2 * r.val = (orderedPairCount (vals nums) k.val : ℤ) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (r : I64)
    (hlen : 1 ≤ (vals nums).length ∧ (vals nums).length ≤ 200)
    (helem : ∀ (i : ℕ) (_ : i < (vals nums).length),
      1 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 100)
    (hk : 0 ≤ k.val ∧ k.val ≤ 99)
    (hres : count_k_difference nums k = ok r), 2 * r.val = (orderedPairCount (vals nums) k.val : ℤ)) := by
  sorry

/-- Let flip be the slice of length len(nums) defined by flip[i] = 101 - nums[i] for every i with 0 <= i < len(nums). Whenever count_k_difference(nums, k) returns r and count_k_difference(flip, k) returns r', we have r = r'.
  Preconditions: 1 <= len(nums) <= 200; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100; 0 <= k <= 99. -/
theorem spec_10 (nums flip : Slice I64) (k : I64) (r r' : I64)
    (hlen : 1 ≤ (vals nums).length ∧ (vals nums).length ≤ 200)
    (helem : ∀ (i : ℕ) (_ : i < (vals nums).length),
      1 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 100)
    (hk : 0 ≤ k.val ∧ k.val ≤ 99)
    (hlen_flip : (vals flip).length = (vals nums).length)
    (hflip : IsFlip flip nums)
    (hres : count_k_difference nums k = ok r)
    (hres' : count_k_difference flip k = ok r') :
    r = r' := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums flip : Slice I64) (k : I64) (r r' : I64)
    (hlen : 1 ≤ (vals nums).length ∧ (vals nums).length ≤ 200)
    (helem : ∀ (i : ℕ) (_ : i < (vals nums).length),
      1 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 100)
    (hk : 0 ≤ k.val ∧ k.val ≤ 99)
    (hlen_flip : (vals flip).length = (vals nums).length)
    (hflip : IsFlip flip nums)
    (hres : count_k_difference nums k = ok r)
    (hres' : count_k_difference flip k = ok r'), r = r') := by
  sorry

end AegisSpec.CountKDifference
