import Aegis.NumberOfSubarrays.Code.Funs

/-!
# Specifications of `Aegis.NumberOfSubarrays.number_of_subarrays`

LeetCode problem `find-the-number-of-subarrays-where-boundary-elements-are-maximum`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.NumberOfSubarrays

def elems (nums : Slice Std.I64) : List ℤ := nums.val.map (fun x => x.val)

def len (nums : Slice Std.I64) : ℕ := nums.val.length

def elemAt (l : List ℤ) (i : ℕ) : ℤ := l.getD i 0

noncomputable def pairCount (n : ℕ) (p : ℕ → ℕ → Prop) : ℕ := by
  classical
  exact ((Finset.range n).product (Finset.range n)).filter
    (fun q => q.1 ≤ q.2 ∧ p q.1 q.2) |>.card

noncomputable def countVal (l : List ℤ) (v : ℤ) : ℕ := by
  classical
  exact (Finset.range l.length).filter (fun i => elemAt l i = v) |>.card

def IsMaxOf (l : List ℤ) (M : ℤ) : Prop :=
  M ∈ l ∧ ∀ x, x ∈ l → x ≤ M

def Good (l : List ℤ) (i j : ℕ) : Prop :=
  elemAt l i = elemAt l j ∧ ∀ k, i ≤ k → k ≤ j → elemAt l k ≤ elemAt l i

def PairwiseDistinct (l : List ℤ) : Prop :=
  ∀ i j, i < j → j < l.length → elemAt l i ≠ elemAt l j

def Nondecreasing (l : List ℤ) : Prop :=
  ∀ i, i + 1 < l.length → elemAt l i ≤ elemAt l (i + 1)

def Nonincreasing (l : List ℤ) : Prop :=
  ∀ i, i + 1 < l.length → elemAt l (i + 1) ≤ elemAt l i

noncomputable def countUpTo (l : List ℤ) (j : ℕ) : ℕ := by
  classical
  exact (Finset.range (j + 1)).filter (fun i => elemAt l i = elemAt l j ∧
    ∀ k, i ≤ k → k ≤ j → elemAt l k ≤ elemAt l i) |>.card

/-- The function returns a result r and r equals the number of pairs (i, j) of indices with 0 <= i <= j < len(nums) such that nums[i] = nums[j] and, for every k with i <= k <= j, nums[k] <= nums[i].
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9. -/
theorem spec_1 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 100000)
    (hval : ∀ i, i < len nums → 1 ≤ elemAt (elems nums) i ∧ elemAt (elems nums) i ≤ 10 ^ 9) :
    ∃ r : Std.I64,
      Aegis.NumberOfSubarrays.number_of_subarrays nums = ok r ∧
      r.val = (pairCount (len nums) (Good (elems nums)) : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 100000)
    (hval : ∀ i, i < len nums → 1 ≤ elemAt (elems nums) i ∧ elemAt (elems nums) i ≤ 10 ^ 9), ∃ r : Std.I64,
      Aegis.NumberOfSubarrays.number_of_subarrays nums = ok r ∧
      r.val = (pairCount (len nums) (Good (elems nums)) : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, len(nums) <= r <= len(nums) * (len(nums) + 1) / 2.
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9. -/
theorem spec_2 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 100000)
    (hval : ∀ i, i < len nums → 1 ≤ elemAt (elems nums) i ∧ elemAt (elems nums) i ≤ 10 ^ 9) :
    ∀ r : Std.I64, Aegis.NumberOfSubarrays.number_of_subarrays nums = ok r →
      (len nums : ℤ) ≤ r.val ∧
        r.val ≤ (len nums : ℤ) * ((len nums : ℤ) + 1) / 2 := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 100000)
    (hval : ∀ i, i < len nums → 1 ≤ elemAt (elems nums) i ∧ elemAt (elems nums) i ≤ 10 ^ 9), ∀ r : Std.I64, Aegis.NumberOfSubarrays.number_of_subarrays nums = ok r →
      (len nums : ℤ) ≤ r.val ∧
        r.val ≤ (len nums : ℤ) * ((len nums : ℤ) + 1) / 2) := by
  sorry

/-- Whenever the function returns a result r, if nums[i] != nums[j] for all i, j with 0 <= i < j < len(nums), then r = len(nums).
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9. -/
theorem spec_3 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 100000)
    (hval : ∀ i, i < len nums → 1 ≤ elemAt (elems nums) i ∧ elemAt (elems nums) i ≤ 10 ^ 9) :
    ∀ r : Std.I64, Aegis.NumberOfSubarrays.number_of_subarrays nums = ok r →
      PairwiseDistinct (elems nums) → r.val = (len nums : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 100000)
    (hval : ∀ i, i < len nums → 1 ≤ elemAt (elems nums) i ∧ elemAt (elems nums) i ≤ 10 ^ 9), ∀ r : Std.I64, Aegis.NumberOfSubarrays.number_of_subarrays nums = ok r →
      PairwiseDistinct (elems nums) → r.val = (len nums : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, if the array nums is non-decreasing (nums[i] <= nums[i+1] for all 0 <= i < len(nums)-1) or non-increasing (nums[i] >= nums[i+1] for all 0 <= i < len(nums)-1), then r equals the number of pairs (i, j) with 0 <= i <= j < len(nums) and nums[i] = nums[j].
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9. -/
theorem spec_4 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 100000)
    (hval : ∀ i, i < len nums → 1 ≤ elemAt (elems nums) i ∧ elemAt (elems nums) i ≤ 10 ^ 9) :
    ∀ r : Std.I64, Aegis.NumberOfSubarrays.number_of_subarrays nums = ok r →
      (Nondecreasing (elems nums) ∨ Nonincreasing (elems nums)) →
      r.val = (pairCount (len nums)
        (fun i j => elemAt (elems nums) i = elemAt (elems nums) j) : ℤ) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 100000)
    (hval : ∀ i, i < len nums → 1 ≤ elemAt (elems nums) i ∧ elemAt (elems nums) i ≤ 10 ^ 9), ∀ r : Std.I64, Aegis.NumberOfSubarrays.number_of_subarrays nums = ok r →
      (Nondecreasing (elems nums) ∨ Nonincreasing (elems nums)) →
      r.val = (pairCount (len nums)
        (fun i j => elemAt (elems nums) i = elemAt (elems nums) j) : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, let m = len(nums) and define the reversed array b by b[i] = nums[m-1-i] for 0 <= i < m. Then r equals the number of pairs (i, j) with 0 <= i <= j < m such that b[i] = b[j] and b[k] <= b[i] for every k with i <= k <= j.
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9. -/
theorem spec_5 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 100000)
    (hval : ∀ i, i < len nums → 1 ≤ elemAt (elems nums) i ∧ elemAt (elems nums) i ≤ 10 ^ 9) :
    ∀ r : Std.I64, Aegis.NumberOfSubarrays.number_of_subarrays nums = ok r →
      r.val = (pairCount (len nums) (Good (elems nums).reverse) : ℤ) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 100000)
    (hval : ∀ i, i < len nums → 1 ≤ elemAt (elems nums) i ∧ elemAt (elems nums) i ≤ 10 ^ 9), ∀ r : Std.I64, Aegis.NumberOfSubarrays.number_of_subarrays nums = ok r →
      r.val = (pairCount (len nums) (Good (elems nums).reverse) : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, if f is any strictly increasing function from the set of values occurring in nums to the 64-bit integers (i.e., f(x) < f(y) whenever x < y for x, y in that set), and b is defined by b[i] = f(nums[i]) for 0 <= i < len(nums), then r equals the number of pairs (i, j) with 0 <= i <= j < len(nums) such that b[i] = b[j] and b[k] <= b[i] for every k with i <= k <= j.
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9. -/
theorem spec_6 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 100000)
    (hval : ∀ i, i < len nums → 1 ≤ elemAt (elems nums) i ∧ elemAt (elems nums) i ≤ 10 ^ 9) :
    ∀ r : Std.I64, Aegis.NumberOfSubarrays.number_of_subarrays nums = ok r →
      ∀ g : ℤ → ℤ,
        (∀ x, x ∈ elems nums → ∀ y, y ∈ elems nums → x < y → g x < g y) →
        r.val = (pairCount (len nums) (Good ((elems nums).map g)) : ℤ) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 100000)
    (hval : ∀ i, i < len nums → 1 ≤ elemAt (elems nums) i ∧ elemAt (elems nums) i ≤ 10 ^ 9), ∀ r : Std.I64, Aegis.NumberOfSubarrays.number_of_subarrays nums = ok r →
      ∀ g : ℤ → ℤ,
        (∀ x, x ∈ elems nums → ∀ y, y ∈ elems nums → x < y → g x < g y) →
        r.val = (pairCount (len nums) (Good ((elems nums).map g)) : ℤ)) := by
  sorry

/-- For every input nums satisfying the preconditions, the function returns a result r (it does not fail due to arithmetic overflow, out-of-bounds indexing, or panic).
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9. -/
theorem spec_7 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 100000)
    (hval : ∀ i, i < len nums → 1 ≤ elemAt (elems nums) i ∧ elemAt (elems nums) i ≤ 10 ^ 9) :
    ∃ r : Std.I64, Aegis.NumberOfSubarrays.number_of_subarrays nums = ok r := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 100000)
    (hval : ∀ i, i < len nums → 1 ≤ elemAt (elems nums) i ∧ elemAt (elems nums) i ≤ 10 ^ 9), ∃ r : Std.I64, Aegis.NumberOfSubarrays.number_of_subarrays nums = ok r) := by
  sorry

/-- Whenever the function returns a result r, r > len(nums) if and only if there exist indices i and j with 0 <= i < j < len(nums), nums[i] = nums[j], and nums[k] <= nums[i] for every k with i <= k <= j.
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9. -/
theorem spec_8 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 100000)
    (hval : ∀ i, i < len nums → 1 ≤ elemAt (elems nums) i ∧ elemAt (elems nums) i ≤ 10 ^ 9) :
    ∀ r : Std.I64, Aegis.NumberOfSubarrays.number_of_subarrays nums = ok r →
      ((len nums : ℤ) < r.val ↔
        ∃ i j, i < j ∧ j < len nums ∧ elemAt (elems nums) i = elemAt (elems nums) j ∧
          ∀ k, i ≤ k → k ≤ j → elemAt (elems nums) k ≤ elemAt (elems nums) i) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 100000)
    (hval : ∀ i, i < len nums → 1 ≤ elemAt (elems nums) i ∧ elemAt (elems nums) i ≤ 10 ^ 9), ∀ r : Std.I64, Aegis.NumberOfSubarrays.number_of_subarrays nums = ok r →
      ((len nums : ℤ) < r.val ↔
        ∃ i j, i < j ∧ j < len nums ∧ elemAt (elems nums) i = elemAt (elems nums) j ∧
          ∀ k, i ≤ k → k ≤ j → elemAt (elems nums) k ≤ elemAt (elems nums) i)) := by
  sorry

/-- Whenever the function returns a result r, for each j with 0 <= j < len(nums), let c(j) be the number of indices i with 0 <= i <= j such that nums[i] = nums[j] and nums[k] <= nums[i] for every k with i <= k <= j. Then r = sum_{j=0}^{len(nums)-1} c(j).
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9. -/
theorem spec_9 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 100000)
    (hval : ∀ i, i < len nums → 1 ≤ elemAt (elems nums) i ∧ elemAt (elems nums) i ≤ 10 ^ 9) :
    ∀ r : Std.I64, Aegis.NumberOfSubarrays.number_of_subarrays nums = ok r →
      r.val = Finset.sum (Finset.range (len nums))
        (fun j => (countUpTo (elems nums) j : ℤ)) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 100000)
    (hval : ∀ i, i < len nums → 1 ≤ elemAt (elems nums) i ∧ elemAt (elems nums) i ≤ 10 ^ 9), ∀ r : Std.I64, Aegis.NumberOfSubarrays.number_of_subarrays nums = ok r →
      r.val = Finset.sum (Finset.range (len nums))
        (fun j => (countUpTo (elems nums) j : ℤ))) := by
  sorry

/-- Whenever the function returns a result r, let E be the number of pairs (i, j) with 0 <= i <= j < len(nums) and nums[i] = nums[j]. Then r <= E.
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9. -/
theorem spec_10 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 100000)
    (hval : ∀ i, i < len nums → 1 ≤ elemAt (elems nums) i ∧ elemAt (elems nums) i ≤ 10 ^ 9) :
    ∀ r : Std.I64, Aegis.NumberOfSubarrays.number_of_subarrays nums = ok r →
      r.val ≤ (pairCount (len nums)
        (fun i j => elemAt (elems nums) i = elemAt (elems nums) j) : ℤ) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 100000)
    (hval : ∀ i, i < len nums → 1 ≤ elemAt (elems nums) i ∧ elemAt (elems nums) i ≤ 10 ^ 9), ∀ r : Std.I64, Aegis.NumberOfSubarrays.number_of_subarrays nums = ok r →
      r.val ≤ (pairCount (len nums)
        (fun i j => elemAt (elems nums) i = elemAt (elems nums) j) : ℤ)) := by
  sorry

end AegisSpec.NumberOfSubarrays
