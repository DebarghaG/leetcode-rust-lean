import Aegis.MinOperations.Code.Funs

/-!
# Specifications of `Aegis.MinOperations.min_operations`

LeetCode problem `minimum-operations-to-make-array-values-equal-to-k`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinOperations

def contents (nums : Slice I64) : List ℤ := nums.val.map (fun x => x.val)

def pre (nums : Slice I64) (k : I64) : Prop :=
  1 ≤ nums.val.length ∧ nums.val.length ≤ 100 ∧
    (∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 100) ∧
    1 ≤ k.val ∧ k.val ≤ 100

def Occurs (nums : Slice I64) (v : ℤ) : Prop := v ∈ contents nums

def OccursBelow (nums : Slice I64) (k : I64) : Prop := ∃ v ∈ contents nums, v < k.val

def AllAtLeast (nums : Slice I64) (k : I64) : Prop := ∀ v ∈ contents nums, k.val ≤ v

def aboveValues (nums : Slice I64) (k : I64) : Finset ℤ :=
  (contents nums).toFinset.filter (fun v => k.val < v)

def countAbove (nums : Slice I64) (k : I64) : ℤ := ((aboveValues nums k).card : ℤ)

def occCount (xs : List ℤ) (v : ℤ) : ℕ := (xs.filter (fun x => decide (x = v))).length

def SameMultiplicity (xs ys : List ℤ) : Prop := ∀ v : ℤ, occCount xs v = occCount ys v

def deleteValues (c : ℤ) (xs : List ℤ) : List ℤ := xs.filter (fun x => decide (x ≠ c))

def Step (xs ys : List ℤ) : Prop :=
  ∃ h : ℤ,
    (∀ a ∈ xs, ∀ b ∈ xs, h < a → h < b → a = b) ∧
      ys = xs.map (fun x => if h < x then h else x)

inductive ReachesIn : ℕ → List ℤ → List ℤ → Prop where
  | zero (xs : List ℤ) : ReachesIn 0 xs xs
  | succ {n : ℕ} {xs ys zs : List ℤ} :
      Step xs ys → ReachesIn n ys zs → ReachesIn (n + 1) xs zs

def Reachable (xs ys : List ℤ) : Prop := ∃ n, ReachesIn n xs ys

def AllEqual (xs : List ℤ) (c : ℤ) : Prop := ∀ x ∈ xs, x = c

def ReachableAllK (nums : Slice I64) (k : I64) : Prop :=
  ∃ ys : List ℤ, Reachable (contents nums) ys ∧ AllEqual ys k.val

open Aegis.MinOperations

/-- The function returns a result r, and: (a) if there exists an index i with 0 <= i < len(nums) and nums[i] < k, then r = -1; (b) if nums[i] >= k for every index i with 0 <= i < len(nums), then r equals the number of distinct integers v such that v > k and v = nums[i] for some index i with 0 <= i < len(nums).
  Preconditions: len(nums) >= 1 and len(nums) <= 100 and for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 100, and 1 <= k <= 100. -/
theorem spec_1 (nums : Slice I64) (k : I64) (hpre : pre nums k) :
    ∃ r : I64, min_operations nums k = ok r ∧
      (OccursBelow nums k → r.val = -1) ∧
      (AllAtLeast nums k → r.val = countAbove nums k) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (hpre : pre nums k), ∃ r : I64, min_operations nums k = ok r ∧
      (OccursBelow nums k → r.val = -1) ∧
      (AllAtLeast nums k → r.val = countAbove nums k)) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result (it does not fail, panic, or overflow).
  Preconditions: len(nums) >= 1 and len(nums) <= 100 and for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 100, and 1 <= k <= 100. -/
theorem spec_2 (nums : Slice I64) (k : I64) (hpre : pre nums k) :
    ∃ r : I64, min_operations nums k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (hpre : pre nums k), ∃ r : I64, min_operations nums k = ok r) := by
  sorry

/-- Whenever the function returns a result r: r != -1 if and only if there exists a finite sequence of operations (each operation choosing an integer h such that all current array values strictly greater than h are equal to each other, then replacing every current value strictly greater than h by h) after which every element of the array equals k.
  Preconditions: len(nums) >= 1 and len(nums) <= 100 and for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 100, and 1 <= k <= 100. -/
theorem spec_3 (nums : Slice I64) (k : I64) (hpre : pre nums k) (r : I64)
    (hr : min_operations nums k = ok r) :
    (r.val ≠ -1) ↔ ReachableAllK nums k := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (hpre : pre nums k) (r : I64)
    (hr : min_operations nums k = ok r), (r.val ≠ -1) ↔ ReachableAllK nums k) := by
  sorry

/-- Whenever the function returns a result r: -1 <= r and r <= len(nums).
  Preconditions: len(nums) >= 1 and len(nums) <= 100 and for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 100, and 1 <= k <= 100. -/
theorem spec_4 (nums : Slice I64) (k : I64) (hpre : pre nums k) (r : I64)
    (hr : min_operations nums k = ok r) :
    -1 ≤ r.val ∧ r.val ≤ (nums.val.length : ℤ) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (hpre : pre nums k) (r : I64)
    (hr : min_operations nums k = ok r), -1 ≤ r.val ∧ r.val ≤ (nums.val.length : ℤ)) := by
  sorry

/-- Whenever the function returns a result r: r = 0 if and only if nums[i] = k for every index i with 0 <= i < len(nums).
  Preconditions: len(nums) >= 1 and len(nums) <= 100 and for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 100, and 1 <= k <= 100. -/
theorem spec_5 (nums : Slice I64) (k : I64) (hpre : pre nums k) (r : I64)
    (hr : min_operations nums k = ok r) :
    r.val = 0 ↔ ∀ v ∈ contents nums, v = k.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (hpre : pre nums k) (r : I64)
    (hr : min_operations nums k = ok r), r.val = 0 ↔ ∀ v ∈ contents nums, v = k.val) := by
  sorry

/-- Whenever the function returns a result r: r = 1 if and only if (i) nums[i] >= k for every index i with 0 <= i < len(nums), and (ii) the set of values {nums[i] : 0 <= i < len(nums) and nums[i] > k} is nonempty and all of its elements are equal to one another.
  Preconditions: len(nums) >= 1 and len(nums) <= 100 and for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 100, and 1 <= k <= 100. -/
theorem spec_6 (nums : Slice I64) (k : I64) (hpre : pre nums k) (r : I64)
    (hr : min_operations nums k = ok r) :
    r.val = 1 ↔ AllAtLeast nums k ∧ (aboveValues nums k).Nonempty ∧
      (∀ a ∈ aboveValues nums k, ∀ b ∈ aboveValues nums k, a = b) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (hpre : pre nums k) (r : I64)
    (hr : min_operations nums k = ok r), r.val = 1 ↔ AllAtLeast nums k ∧ (aboveValues nums k).Nonempty ∧
      (∀ a ∈ aboveValues nums k, ∀ b ∈ aboveValues nums k, a = b)) := by
  sorry

/-- If there exists an integer v such that nums[i] = v for every index i with 0 <= i < len(nums), then whenever the function returns a result r: r = 0 if v = k, r = 1 if v > k, and r = -1 if v < k.
  Preconditions: len(nums) >= 1 and len(nums) <= 100 and for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 100, and 1 <= k <= 100. -/
theorem spec_7 (nums : Slice I64) (k : I64) (hpre : pre nums k) (r : I64)
    (hr : min_operations nums k = ok r) :
    ∀ v : ℤ, (∀ x ∈ nums.val, x.val = v) →
      ((v = k.val → r.val = 0) ∧ (k.val < v → r.val = 1) ∧ (v < k.val → r.val = -1)) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (hpre : pre nums k) (r : I64)
    (hr : min_operations nums k = ok r), ∀ v : ℤ, (∀ x ∈ nums.val, x.val = v) →
      ((v = k.val → r.val = 0) ∧ (k.val < v → r.val = 1) ∧ (v < k.val → r.val = -1))) := by
  sorry

/-- For every slice nums2 that also satisfies the preconditions (with the same k) and is a permutation of nums (i.e. every integer occurs the same number of times in nums2 as in nums), the function returns the same result on (nums2, k) as on (nums, k).
  Preconditions: len(nums) >= 1 and len(nums) <= 100 and for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 100, and 1 <= k <= 100. -/
theorem spec_8 (nums nums2 : Slice I64) (k : I64) (hpre : pre nums k)
    (hpre2 : pre nums2 k) (hperm : SameMultiplicity (contents nums2) (contents nums)) :
    min_operations nums2 k = min_operations nums k := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums nums2 : Slice I64) (k : I64) (hpre : pre nums k)
    (hpre2 : pre nums2 k) (hperm : SameMultiplicity (contents nums2) (contents nums)), min_operations nums2 k = min_operations nums k) := by
  sorry

/-- For any two slices a and b satisfying the preconditions (with the same k) such that a[i] >= k for every index i of a, b[i] >= k for every index i of b, and for every integer v > k, v occurs in a if and only if v occurs in b, the function returns the same result on (a, k) as on (b, k).
  Preconditions: len(nums) >= 1 and len(nums) <= 100 and for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 100, and 1 <= k <= 100. -/
theorem spec_9 (a b : Slice I64) (k : I64) (hprea : pre a k) (hpreb : pre b k)
    (hga : AllAtLeast a k) (hgb : AllAtLeast b k)
    (hsame : ∀ v : ℤ, k.val < v → (Occurs a v ↔ Occurs b v)) :
    min_operations a k = min_operations b k := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (a b : Slice I64) (k : I64) (hprea : pre a k) (hpreb : pre b k)
    (hga : AllAtLeast a k) (hgb : AllAtLeast b k)
    (hsame : ∀ v : ℤ, k.val < v → (Occurs a v ↔ Occurs b v)), min_operations a k = min_operations b k) := by
  sorry

/-- If the function returns r on (nums, k) and returns r1 on (nums, k1), then r != -1, r1 != -1, and r1 >= r.
  Preconditions: len(nums) >= 1 and len(nums) <= 100 and for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 100, and 1 <= k <= 100; additionally 1 <= k1 <= k and nums[i] >= k for every index i with 0 <= i < len(nums). -/
theorem spec_10 (nums : Slice I64) (k k1 : I64) (r r1 : I64) (hpre : pre nums k)
    (hk1lo : 1 ≤ k1.val) (hk1le : k1.val ≤ k.val) (hge : AllAtLeast nums k)
    (hr : min_operations nums k = ok r) (hr1 : min_operations nums k1 = ok r1) :
    r.val ≠ -1 ∧ r1.val ≠ -1 ∧ r.val ≤ r1.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice I64) (k k1 : I64) (r r1 : I64) (hpre : pre nums k)
    (hk1lo : 1 ≤ k1.val) (hk1le : k1.val ≤ k.val) (hge : AllAtLeast nums k)
    (hr : min_operations nums k = ok r) (hr1 : min_operations nums k1 = ok r1), r.val ≠ -1 ∧ r1.val ≠ -1 ∧ r.val ≤ r1.val) := by
  sorry

/-- Whenever the function returns a result r with r != -1, r is the minimum length of a sequence of operations (each operation choosing an integer h such that all current array values strictly greater than h are equal to each other, then replacing every current value strictly greater than h by h) that transforms nums into an array all of whose elements equal k: a sequence of length r exists, and no sequence of length less than r exists.
  Preconditions: len(nums) >= 1 and len(nums) <= 100 and for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 100, and 1 <= k <= 100. -/
theorem spec_11 (nums : Slice I64) (k : I64) (hpre : pre nums k) (r : I64)
    (hr : min_operations nums k = ok r) (hrne : r.val ≠ -1) :
    (∃ ys : List ℤ, ReachesIn r.val.toNat (contents nums) ys ∧ AllEqual ys k.val) ∧
      (∀ (n : ℕ) (ys : List ℤ), ReachesIn n (contents nums) ys → AllEqual ys k.val →
        r.val ≤ (n : ℤ)) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (hpre : pre nums k) (r : I64)
    (hr : min_operations nums k = ok r) (hrne : r.val ≠ -1), (∃ ys : List ℤ, ReachesIn r.val.toNat (contents nums) ys ∧ AllEqual ys k.val) ∧
      (∀ (n : ℕ) (ys : List ℤ), ReachesIn n (contents nums) ys → AllEqual ys k.val →
        r.val ≤ (n : ℤ))) := by
  sorry

/-- Whenever the function returns a result r with r != -1, r <= 100 - k.
  Preconditions: len(nums) >= 1 and len(nums) <= 100 and for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 100, and 1 <= k <= 100. -/
theorem spec_12 (nums : Slice I64) (k : I64) (hpre : pre nums k) (r : I64)
    (hr : min_operations nums k = ok r) (hrne : r.val ≠ -1) :
    r.val ≤ 100 - k.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (hpre : pre nums k) (r : I64)
    (hr : min_operations nums k = ok r) (hrne : r.val ≠ -1), r.val ≤ 100 - k.val) := by
  sorry

/-- For every slice nums2 satisfying the preconditions and obtained from nums by deleting every element equal to k while keeping the relative order of the remaining elements, if len(nums2) >= 1 then the function returns the same result on (nums2, k) as on (nums, k).
  Preconditions: len(nums) >= 1 and len(nums) <= 100 and for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 100, and 1 <= k <= 100. -/
theorem spec_13 (nums nums2 : Slice I64) (k : I64) (hpre : pre nums k)
    (hpre2 : pre nums2 k) (hdel : contents nums2 = deleteValues k.val (contents nums))
    (hlen : 1 ≤ nums2.val.length) :
    min_operations nums2 k = min_operations nums k := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums nums2 : Slice I64) (k : I64) (hpre : pre nums k)
    (hpre2 : pre nums2 k) (hdel : contents nums2 = deleteValues k.val (contents nums))
    (hlen : 1 ≤ nums2.val.length), min_operations nums2 k = min_operations nums k) := by
  sorry

/-- Whenever the function returns the result -1, there exists an index i with 0 <= i < len(nums) and nums[i] < k.
  Preconditions: len(nums) >= 1 and len(nums) <= 100 and for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 100, and 1 <= k <= 100. -/
theorem spec_14 (nums : Slice I64) (k : I64) (hpre : pre nums k) (r : I64)
    (hr : min_operations nums k = ok r) (hr1 : r.val = -1) :
    ∃ v ∈ contents nums, v < k.val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (hpre : pre nums k) (r : I64)
    (hr : min_operations nums k = ok r) (hr1 : r.val = -1), ∃ v ∈ contents nums, v < k.val) := by
  sorry

end AegisSpec.MinOperations
