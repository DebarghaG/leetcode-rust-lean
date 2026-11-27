import Aegis.EvenProduct.Code.Funs

/-!
# Specifications of `Aegis.EvenProduct.even_product`

LeetCode problem `number-of-subarrays-having-even-product`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.EvenProduct

abbrev SliceI64 : Type := Aeneas.Std.Slice Aeneas.Std.I64

def IsEven (x : Int) : Prop := ∃ k : Int, x = 2 * k

def IsOdd (x : Int) : Prop := ¬ IsEven x

def entry (nums : SliceI64) (i : Nat) : Int :=
  match nums.val[i]? with
  | some x => x.val
  | none => 0

def size (nums : SliceI64) : Nat := nums.val.length

def Precondition (nums : SliceI64) : Prop :=
  1 ≤ size nums ∧ size nums ≤ 100000 ∧
    ∀ i, i < size nums → 1 ≤ entry nums i ∧ entry nums i ≤ 100000

def totalSubarrays (nums : SliceI64) : Nat := size nums * (size nums + 1) / 2

def HasEvenEntry (nums : SliceI64) (l u : Nat) : Prop :=
  ∃ k, l ≤ k ∧ k ≤ u ∧ IsEven (entry nums k)

def AllOddBetween (nums : SliceI64) (l u : Nat) : Prop :=
  ∀ k, l ≤ k → k ≤ u → IsOdd (entry nums k)

noncomputable def evenSubarrayCount (nums : SliceI64) : Nat :=
  by
  classical
  exact (((Finset.range (size nums)).product (Finset.range (size nums))).filter
    (fun p : Nat × Nat => p.1 ≤ p.2 ∧ HasEvenEntry nums p.1 p.2)).card

noncomputable def oddOnlySubarrayCount (nums : SliceI64) : Nat :=
  by
  classical
  exact (((Finset.range (size nums)).product (Finset.range (size nums))).filter
    (fun p : Nat × Nat => p.1 ≤ p.2 ∧ AllOddBetween nums p.1 p.2)).card

def IsMaxOddRun (nums : SliceI64) (a L : Nat) : Prop :=
  0 < L ∧ a + L ≤ size nums ∧
    AllOddBetween nums a (a + L - 1) ∧
    (a = 0 ∨ IsEven (entry nums (a - 1))) ∧
    (a + L = size nums ∨ IsEven (entry nums (a + L)))

noncomputable def maxOddRunSum (nums : SliceI64) : Nat :=
  by
  classical
  exact ((((Finset.range (size nums)).product (Finset.range (size nums + 1))).filter
    (fun p : Nat × Nat => IsMaxOddRun nums p.1 p.2)).sum
    (fun p => p.2 * (p.2 + 1) / 2))

noncomputable def evenPositions (nums : SliceI64) : List Nat :=
  by
  classical
  exact (List.range (size nums)).filter (fun i => decide (IsEven (entry nums i)))

noncomputable def evenPositionSum (nums : SliceI64) : Int :=
  let ps := evenPositions nums
  ((ps.zip ((-1 : Int) :: ps.map (fun p => (p : Int)))).map
    (fun pr : Nat × Int => ((pr.1 : Int) - pr.2) * ((size nums : Int) - (pr.1 : Int)))).sum

def IsReversal (rev nums : SliceI64) : Prop :=
  size rev = size nums ∧
    ∀ i, i < size nums → entry rev i = entry nums (size nums - 1 - i)

/-- The function returns a result q and q equals the number of pairs (l, u) of indices such that 0 <= l <= u < n and there exists an index k with l <= k <= u and nums[k] is even, i.e. divisible by 2. Equivalently, q is the number of nonempty contiguous subarrays nums[l..u] whose product is even.
  Preconditions: Let n = len(nums). The slice satisfies 1 <= n <= 100000 and, for every i with 0 <= i < n, 1 <= nums[i] <= 100000. -/
theorem spec_1 (nums : SliceI64) (h : Precondition nums) :
    ∃ q, Aegis.EvenProduct.even_product nums = Aeneas.Std.Result.ok q ∧
      (q : Int) = (evenSubarrayCount nums : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : SliceI64) (h : Precondition nums), ∃ q, Aegis.EvenProduct.even_product nums = Aeneas.Std.Result.ok q ∧
      (q : Int) = (evenSubarrayCount nums : Int)) := by
  sorry

/-- The function returns a result q; it does not fail through overflow, out-of-bounds access, or panic.
  Preconditions: Let n = len(nums). The slice satisfies 1 <= n <= 100000 and, for every i with 0 <= i < n, 1 <= nums[i] <= 100000. -/
theorem spec_2 (nums : SliceI64) (h : Precondition nums) :
    ∃ q, Aegis.EvenProduct.even_product nums = Aeneas.Std.Result.ok q := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : SliceI64) (h : Precondition nums), ∃ q, Aegis.EvenProduct.even_product nums = Aeneas.Std.Result.ok q) := by
  sorry

/-- Whenever the function returns a result q, 0 <= q <= n*(n+1)/2.
  Preconditions: Let n = len(nums). The slice satisfies 1 <= n <= 100000 and, for every i with 0 <= i < n, 1 <= nums[i] <= 100000. -/
theorem spec_3 (nums : SliceI64) (h : Precondition nums) (q : Aeneas.Std.I64)
    (hq : Aegis.EvenProduct.even_product nums = Aeneas.Std.Result.ok q) :
    0 ≤ (q : Int) ∧ (q : Int) ≤ (totalSubarrays nums : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : SliceI64) (h : Precondition nums) (q : Aeneas.Std.I64)
    (hq : Aegis.EvenProduct.even_product nums = Aeneas.Std.Result.ok q), 0 ≤ (q : Int) ∧ (q : Int) ≤ (totalSubarrays nums : Int)) := by
  sorry

/-- Whenever the function returns a result q, for every index i with 0 <= i < n and nums[i] even, q >= (i+1)*(n-i).
  Preconditions: Let n = len(nums). The slice satisfies 1 <= n <= 100000 and, for every i with 0 <= i < n, 1 <= nums[i] <= 100000. -/
theorem spec_4 (nums : SliceI64) (h : Precondition nums) (q : Aeneas.Std.I64)
    (hq : Aegis.EvenProduct.even_product nums = Aeneas.Std.Result.ok q) :
    ∀ i, i < size nums → IsEven (entry nums i) →
      ((i : Int) + 1) * ((size nums : Int) - (i : Int)) ≤ (q : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : SliceI64) (h : Precondition nums) (q : Aeneas.Std.I64)
    (hq : Aegis.EvenProduct.even_product nums = Aeneas.Std.Result.ok q), ∀ i, i < size nums → IsEven (entry nums i) →
      ((i : Int) + 1) * ((size nums : Int) - (i : Int)) ≤ (q : Int)) := by
  sorry

/-- Whenever the function returns a result q, q = 0 if and only if every entry nums[i] is odd (not divisible by 2) for all i with 0 <= i < n.
  Preconditions: Let n = len(nums). The slice satisfies 1 <= n <= 100000 and, for every i with 0 <= i < n, 1 <= nums[i] <= 100000. -/
theorem spec_5 (nums : SliceI64) (h : Precondition nums) (q : Aeneas.Std.I64)
    (hq : Aegis.EvenProduct.even_product nums = Aeneas.Std.Result.ok q) :
    ((q : Int) = 0 ↔ ∀ i, i < size nums → IsOdd (entry nums i)) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : SliceI64) (h : Precondition nums) (q : Aeneas.Std.I64)
    (hq : Aegis.EvenProduct.even_product nums = Aeneas.Std.Result.ok q), ((q : Int) = 0 ↔ ∀ i, i < size nums → IsOdd (entry nums i))) := by
  sorry

/-- Whenever the function returns a result q, q = n*(n+1)/2 if and only if every entry nums[i] is even for all i with 0 <= i < n.
  Preconditions: Let n = len(nums). The slice satisfies 1 <= n <= 100000 and, for every i with 0 <= i < n, 1 <= nums[i] <= 100000. -/
theorem spec_6 (nums : SliceI64) (h : Precondition nums) (q : Aeneas.Std.I64)
    (hq : Aegis.EvenProduct.even_product nums = Aeneas.Std.Result.ok q) :
    ((q : Int) = (totalSubarrays nums : Int) ↔
      ∀ i, i < size nums → IsEven (entry nums i)) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : SliceI64) (h : Precondition nums) (q : Aeneas.Std.I64)
    (hq : Aegis.EvenProduct.even_product nums = Aeneas.Std.Result.ok q), ((q : Int) = (totalSubarrays nums : Int) ↔
      ∀ i, i < size nums → IsEven (entry nums i))) := by
  sorry

/-- Whenever the function returns a result q, q + O = n*(n+1)/2, where O is the number of pairs (l, u) with 0 <= l <= u < n such that every index k with l <= k <= u has nums[k] odd.
  Preconditions: Let n = len(nums). The slice satisfies 1 <= n <= 100000 and, for every i with 0 <= i < n, 1 <= nums[i] <= 100000. -/
theorem spec_7 (nums : SliceI64) (h : Precondition nums) (q : Aeneas.Std.I64)
    (hq : Aegis.EvenProduct.even_product nums = Aeneas.Std.Result.ok q) :
    (q : Int) + (oddOnlySubarrayCount nums : Int) = (totalSubarrays nums : Int) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : SliceI64) (h : Precondition nums) (q : Aeneas.Std.I64)
    (hq : Aegis.EvenProduct.even_product nums = Aeneas.Std.Result.ok q), (q : Int) + (oddOnlySubarrayCount nums : Int) = (totalSubarrays nums : Int)) := by
  sorry

/-- Let L_1, ..., L_m be the lengths of the maximal intervals [a,b] with 0 <= a <= b < n such that every nums[k] for a <= k <= b is odd and the interval cannot be enlarged without including an even entry; if there are no odd entries then m = 0. Whenever the function returns a result q, q = n*(n+1)/2 - sum_{t=1}^m L_t*(L_t+1)/2.
  Preconditions: Let n = len(nums). The slice satisfies 1 <= n <= 100000 and, for every i with 0 <= i < n, 1 <= nums[i] <= 100000. -/
theorem spec_8 (nums : SliceI64) (h : Precondition nums) (q : Aeneas.Std.I64)
    (hq : Aegis.EvenProduct.even_product nums = Aeneas.Std.Result.ok q) :
    (q : Int) = (totalSubarrays nums : Int) - (maxOddRunSum nums : Int) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : SliceI64) (h : Precondition nums) (q : Aeneas.Std.I64)
    (hq : Aegis.EvenProduct.even_product nums = Aeneas.Std.Result.ok q), (q : Int) = (totalSubarrays nums : Int) - (maxOddRunSum nums : Int)) := by
  sorry

/-- Let p_1 < p_2 < ... < p_m be all indices i with 0 <= i < n such that nums[i] is even, and set p_0 = -1. If m = 0 the sum below is empty and equals 0. Whenever the function returns a result q, q = sum_{t=1}^m (p_t - p_{t-1}) * (n - p_t).
  Preconditions: Let n = len(nums). The slice satisfies 1 <= n <= 100000 and, for every i with 0 <= i < n, 1 <= nums[i] <= 100000. -/
theorem spec_9 (nums : SliceI64) (h : Precondition nums) (q : Aeneas.Std.I64)
    (hq : Aegis.EvenProduct.even_product nums = Aeneas.Std.Result.ok q) :
    (q : Int) = evenPositionSum nums := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : SliceI64) (h : Precondition nums) (q : Aeneas.Std.I64)
    (hq : Aegis.EvenProduct.even_product nums = Aeneas.Std.Result.ok q), (q : Int) = evenPositionSum nums) := by
  sorry

/-- Whenever even_product(nums) returns a result q and even_product(nums') returns a result q', we have q = q'.
  Preconditions: Let nums and nums' be two slices, each satisfying 1 <= len(nums) = len(nums') = n <= 100000 and 1 <= value <= 100000 for every entry. Suppose that for every i with 0 <= i < n, nums[i] is even if and only if nums'[i] is even. -/
theorem spec_10 (nums nums' : SliceI64) (q q' : Aeneas.Std.I64)
    (h : Precondition nums) (h' : Precondition nums')
    (hlen : size nums = size nums')
    (heven : ∀ i, i < size nums → (IsEven (entry nums i) ↔ IsEven (entry nums' i)))
    (hq : Aegis.EvenProduct.even_product nums = Aeneas.Std.Result.ok q)
    (hq' : Aegis.EvenProduct.even_product nums' = Aeneas.Std.Result.ok q') :
    q = q' := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums nums' : SliceI64) (q q' : Aeneas.Std.I64)
    (h : Precondition nums) (h' : Precondition nums')
    (hlen : size nums = size nums')
    (heven : ∀ i, i < size nums → (IsEven (entry nums i) ↔ IsEven (entry nums' i)))
    (hq : Aegis.EvenProduct.even_product nums = Aeneas.Std.Result.ok q)
    (hq' : Aegis.EvenProduct.even_product nums' = Aeneas.Std.Result.ok q'), q = q') := by
  sorry

/-- Whenever even_product(nums) returns a result q and even_product(rev) returns a result q', we have q = q'.
  Preconditions: Let n = len(nums) and let rev be the slice of length n defined by rev[i] = nums[n-1-i] for 0 <= i < n. Suppose nums, and hence rev, satisfies 1 <= n <= 100000 and 1 <= nums[i] <= 100000 for all i with 0 <= i < n. -/
theorem spec_11 (nums rev : SliceI64) (q q' : Aeneas.Std.I64)
    (h : Precondition nums) (hrev : IsReversal rev nums)
    (hq : Aegis.EvenProduct.even_product nums = Aeneas.Std.Result.ok q)
    (hq' : Aegis.EvenProduct.even_product rev = Aeneas.Std.Result.ok q') :
    q = q' := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums rev : SliceI64) (q q' : Aeneas.Std.I64)
    (h : Precondition nums) (hrev : IsReversal rev nums)
    (hq : Aegis.EvenProduct.even_product nums = Aeneas.Std.Result.ok q)
    (hq' : Aegis.EvenProduct.even_product rev = Aeneas.Std.Result.ok q'), q = q') := by
  sorry

/-- Whenever even_product(nums) returns a result q and even_product(nums') returns a result q', we have q <= q'.
  Preconditions: Let nums and nums' be two slices with len(nums) = len(nums') = n, each satisfying 1 <= n <= 100000 and 1 <= value <= 100000 for every entry. Suppose that for every i with 0 <= i < n, if nums[i] is even then nums'[i] is even; that is, the even positions of nums are a subset of the even positions of nums'. -/
theorem spec_12 (nums nums' : SliceI64) (q q' : Aeneas.Std.I64)
    (h : Precondition nums) (h' : Precondition nums')
    (hlen : size nums = size nums')
    (hsub : ∀ i, i < size nums → IsEven (entry nums i) → IsEven (entry nums' i))
    (hq : Aegis.EvenProduct.even_product nums = Aeneas.Std.Result.ok q)
    (hq' : Aegis.EvenProduct.even_product nums' = Aeneas.Std.Result.ok q') :
    (q : Int) ≤ (q' : Int) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums nums' : SliceI64) (q q' : Aeneas.Std.I64)
    (h : Precondition nums) (h' : Precondition nums')
    (hlen : size nums = size nums')
    (hsub : ∀ i, i < size nums → IsEven (entry nums i) → IsEven (entry nums' i))
    (hq : Aegis.EvenProduct.even_product nums = Aeneas.Std.Result.ok q)
    (hq' : Aegis.EvenProduct.even_product nums' = Aeneas.Std.Result.ok q'), (q : Int) ≤ (q' : Int)) := by
  sorry

end AegisSpec.EvenProduct
