import Aegis.MinOperations.Code.Funs

/-!
# Specifications of `Aegis.MinOperations.min_operations`

LeetCode problem `minimum-operations-to-make-the-array-increasing`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinOperations

def contents (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

def nth (nums : Slice Std.I64) (i : Nat) : Int := (nums.val[i]!).val

def SizeOK (nums : Slice Std.I64) : Prop :=
  1 ≤ nums.val.length ∧ nums.val.length ≤ 5000

def BoundsOK (nums : Slice Std.I64) : Prop :=
  ∀ i, i < nums.val.length → 1 ≤ nth nums i ∧ nth nums i ≤ 10000

def GEAll (nums b : List Int) : Prop :=
  b.length = nums.length ∧ ∀ i, i < nums.length → nums[i]! ≤ b[i]!

def StrictInc (b : List Int) : Prop :=
  ∀ i, i + 1 < b.length → b[i]! < b[i+1]!

def totalInc (nums b : List Int) : Int :=
  ((List.range nums.length).map (fun i => b[i]! - nums[i]!)).sum

def IsMinInc (nums : List Int) (r : Int) : Prop :=
  (∃ b, GEAll nums b ∧ StrictInc b ∧ totalInc nums b = r) ∧
    ∀ c, GEAll nums c → StrictInc c → r ≤ totalInc nums c

def seg (nums : List Int) (l u : Nat) : List Int := (nums.drop l).take (u - l + 1)

/-- The function returns a result r (an i64) and r is the minimum total number of increments needed to make nums strictly increasing. Formally, r is the least integer for which there exists an integer array b of length n such that: (a) for every i with 0 <= i < n, b[i] >= nums[i]; (b) for every i with 0 <= i < n-1, b[i] < b[i+1]; and (c) sum_{i=0}^{n-1} (b[i] - nums[i]) = r. Equivalently, every strictly increasing integer array c of length n with c[i] >= nums[i] for all i has sum_{i=0}^{n-1}(c[i]-nums[i]) >= r, and some such c attains equality.
  Preconditions: Let n = len(nums). 1 <= n <= 5000 and for every i with 0 <= i < n, 1 <= nums[i] <= 10000. -/
theorem spec_1 (nums : Slice Std.I64) (hs : SizeOK nums) (hb : BoundsOK nums) :
    ∃ r : Std.I64, Aegis.MinOperations.min_operations nums = ok r ∧
      IsMinInc (contents nums) r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (hs : SizeOK nums) (hb : BoundsOK nums), ∃ r : Std.I64, Aegis.MinOperations.min_operations nums = ok r ∧
      IsMinInc (contents nums) r.val) := by
  sorry

/-- For every input satisfying the preconditions, min_operations(nums) returns a result; it does not fail, panic, access out of bounds, or overflow in i64 arithmetic.
  Preconditions: Let n = len(nums). 1 <= n <= 5000 and for every i with 0 <= i < n, 1 <= nums[i] <= 10000. -/
theorem spec_2 (nums : Slice Std.I64) (hs : SizeOK nums) (hb : BoundsOK nums) :
    ∃ r : Std.I64, Aegis.MinOperations.min_operations nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (hs : SizeOK nums) (hb : BoundsOK nums), ∃ r : Std.I64, Aegis.MinOperations.min_operations nums = ok r) := by
  sorry

/-- Whenever min_operations(nums) returns a result r, r >= 0.
  Preconditions: Let n = len(nums). 1 <= n <= 5000 and for every i with 0 <= i < n, 1 <= nums[i] <= 10000. -/
theorem spec_3 (nums : Slice Std.I64) (hs : SizeOK nums) (hb : BoundsOK nums) :
    ∀ r : Std.I64, Aegis.MinOperations.min_operations nums = ok r → 0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (hs : SizeOK nums) (hb : BoundsOK nums), ∀ r : Std.I64, Aegis.MinOperations.min_operations nums = ok r → 0 ≤ r.val) := by
  sorry

/-- Whenever min_operations(nums) returns a result r, r <= 10000*n + n*(n-1)/2 - sum_{i=0}^{n-1} nums[i].
  Preconditions: Let n = len(nums). 1 <= n <= 5000 and for every i with 0 <= i < n, 1 <= nums[i] <= 10000. -/
theorem spec_4 (nums : Slice Std.I64) (hs : SizeOK nums) (hb : BoundsOK nums) :
    ∀ r : Std.I64, Aegis.MinOperations.min_operations nums = ok r →
      r.val ≤ 10000 * (nums.val.length : Int) +
                (nums.val.length : Int) * ((nums.val.length : Int) - 1) / 2 -
                (contents nums).sum := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (hs : SizeOK nums) (hb : BoundsOK nums), ∀ r : Std.I64, Aegis.MinOperations.min_operations nums = ok r →
      r.val ≤ 10000 * (nums.val.length : Int) +
                (nums.val.length : Int) * ((nums.val.length : Int) - 1) / 2 -
                (contents nums).sum) := by
  sorry

/-- Whenever min_operations(nums) returns a result r, r = 0 if and only if for every i with 0 <= i < n-1, nums[i] < nums[i+1].
  Preconditions: Let n = len(nums). 1 <= n <= 5000 and for every i with 0 <= i < n, 1 <= nums[i] <= 10000. -/
theorem spec_5 (nums : Slice Std.I64) (hs : SizeOK nums) (hb : BoundsOK nums) :
    ∀ r : Std.I64, Aegis.MinOperations.min_operations nums = ok r →
      (r.val = 0 ↔ ∀ i, i + 1 < nums.val.length → nth nums i < nth nums (i + 1)) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (hs : SizeOK nums) (hb : BoundsOK nums), ∀ r : Std.I64, Aegis.MinOperations.min_operations nums = ok r →
      (r.val = 0 ↔ ∀ i, i + 1 < nums.val.length → nth nums i < nth nums (i + 1))) := by
  sorry

/-- Whenever min_operations(nums) returns a result r, r = max(0, nums[0] + 1 - nums[1]).
  Preconditions: Let n = len(nums). n = 2 and for every i with 0 <= i < 2, 1 <= nums[i] <= 10000. -/
theorem spec_6 (nums : Slice Std.I64) (hn : nums.val.length = 2)
    (hb : ∀ i, i < 2 → 1 ≤ nth nums i ∧ nth nums i ≤ 10000) :
    ∀ r : Std.I64, Aegis.MinOperations.min_operations nums = ok r →
      r.val = max 0 (nth nums 0 + 1 - nth nums 1) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (hn : nums.val.length = 2)
    (hb : ∀ i, i < 2 → 1 ≤ nth nums i ∧ nth nums i ≤ 10000), ∀ r : Std.I64, Aegis.MinOperations.min_operations nums = ok r →
      r.val = max 0 (nth nums 0 + 1 - nth nums 1)) := by
  sorry

/-- Whenever min_operations(nums) returns a result r, r = n*(n-1)/2.
  Preconditions: Let n = len(nums). 1 <= n <= 5000, for every i with 0 <= i < n, 1 <= nums[i] <= 10000, and there exists an integer c such that nums[i] = c for every i with 0 <= i < n. -/
theorem spec_7 (nums : Slice Std.I64) (hs : SizeOK nums) (hb : BoundsOK nums)
    (hc : ∃ c : Int, ∀ i, i < nums.val.length → nth nums i = c) :
    ∀ r : Std.I64, Aegis.MinOperations.min_operations nums = ok r →
      r.val = (nums.val.length : Int) * ((nums.val.length : Int) - 1) / 2 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (hs : SizeOK nums) (hb : BoundsOK nums)
    (hc : ∃ c : Int, ∀ i, i < nums.val.length → nth nums i = c), ∀ r : Std.I64, Aegis.MinOperations.min_operations nums = ok r →
      r.val = (nums.val.length : Int) * ((nums.val.length : Int) - 1) / 2) := by
  sorry

/-- Whenever min_operations(nums) returns a result r, r = n*(n-1).
  Preconditions: Let n = len(nums). 1 <= n <= 5000, for every i with 0 <= i < n, 1 <= nums[i] <= 10000, and there exists an integer c such that nums[i] = c - i for every i with 0 <= i < n. -/
theorem spec_8 (nums : Slice Std.I64) (hs : SizeOK nums) (hb : BoundsOK nums)
    (hc : ∃ c : Int, ∀ i, i < nums.val.length → nth nums i = c - (i : Int)) :
    ∀ r : Std.I64, Aegis.MinOperations.min_operations nums = ok r →
      r.val = (nums.val.length : Int) * ((nums.val.length : Int) - 1) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (hs : SizeOK nums) (hb : BoundsOK nums)
    (hc : ∃ c : Int, ∀ i, i < nums.val.length → nth nums i = c - (i : Int)), ∀ r : Std.I64, Aegis.MinOperations.min_operations nums = ok r →
      r.val = (nums.val.length : Int) * ((nums.val.length : Int) - 1)) := by
  sorry

/-- Let nums' be the array of length n with nums'[i] = nums[i] + d for every i. If min_operations(nums) returns r and min_operations(nums') returns r', then r = r'.
  Preconditions: Let n = len(nums). 1 <= n <= 5000; for every i with 0 <= i < n, 1 <= nums[i] <= 10000; and let d be an integer such that for every i with 0 <= i < n, 1 <= nums[i] + d <= 10000. -/
theorem spec_9 (nums nums' : Slice Std.I64) (hs : SizeOK nums) (hb : BoundsOK nums)
    (d : Int) (hd : ∀ i, i < nums.val.length → 1 ≤ nth nums i + d ∧ nth nums i + d ≤ 10000)
    (hne : nums'.val.length = nums.val.length)
    (hns : ∀ i, i < nums.val.length → nth nums' i = nth nums i + d) :
    ∀ r r' : Std.I64, Aegis.MinOperations.min_operations nums = ok r →
      Aegis.MinOperations.min_operations nums' = ok r' → r.val = r'.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (hs : SizeOK nums) (hb : BoundsOK nums)
    (d : Int) (hd : ∀ i, i < nums.val.length → 1 ≤ nth nums i + d ∧ nth nums i + d ≤ 10000)
    (hne : nums'.val.length = nums.val.length)
    (hns : ∀ i, i < nums.val.length → nth nums' i = nth nums i + d), ∀ r r' : Std.I64, Aegis.MinOperations.min_operations nums = ok r →
      Aegis.MinOperations.min_operations nums' = ok r' → r.val = r'.val) := by
  sorry

/-- Whenever min_operations(nums) returns a result r, there exists an integer array b of length n such that for every i with 0 <= i < n, b[i] >= nums[i]; for every i with 0 <= i < n-1, b[i] < b[i+1]; and sum_{i=0}^{n-1}(b[i]-nums[i]) = r.
  Preconditions: Let n = len(nums). 1 <= n <= 5000 and for every i with 0 <= i < n, 1 <= nums[i] <= 10000. -/
theorem spec_10 (nums : Slice Std.I64) (hs : SizeOK nums) (hb : BoundsOK nums) :
    ∀ r : Std.I64, Aegis.MinOperations.min_operations nums = ok r →
      ∃ b : List Int, GEAll (contents nums) b ∧ StrictInc b ∧
        totalInc (contents nums) b = r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64) (hs : SizeOK nums) (hb : BoundsOK nums), ∀ r : Std.I64, Aegis.MinOperations.min_operations nums = ok r →
      ∃ b : List Int, GEAll (contents nums) b ∧ StrictInc b ∧
        totalInc (contents nums) b = r.val) := by
  sorry

/-- Whenever min_operations(nums) returns a result r, for every integer array c of length n such that c[i] >= nums[i] for all 0 <= i < n and c[i] < c[i+1] for all 0 <= i < n-1, we have sum_{i=0}^{n-1}(c[i]-nums[i]) >= r.
  Preconditions: Let n = len(nums). 1 <= n <= 5000 and for every i with 0 <= i < n, 1 <= nums[i] <= 10000. -/
theorem spec_11 (nums : Slice Std.I64) (hs : SizeOK nums) (hb : BoundsOK nums) :
    ∀ r : Std.I64, Aegis.MinOperations.min_operations nums = ok r →
      ∀ c : List Int, GEAll (contents nums) c → StrictInc c →
        r.val ≤ totalInc (contents nums) c := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64) (hs : SizeOK nums) (hb : BoundsOK nums), ∀ r : Std.I64, Aegis.MinOperations.min_operations nums = ok r →
      ∀ c : List Int, GEAll (contents nums) c → StrictInc c →
        r.val ≤ totalInc (contents nums) c) := by
  sorry

/-- Whenever min_operations(nums) returns r, for every l and u with 0 <= l <= u < n, r is greater than or equal to the least integer k for which there exists an integer array c of length u-l+1 such that c[j] >= nums[l+j] for all 0 <= j <= u-l, c[j] < c[j+1] for all 0 <= j < u-l, and sum_{j=0}^{u-l}(c[j]-nums[l+j]) = k.
  Preconditions: Let n = len(nums). 1 <= n <= 5000 and for every i with 0 <= i < n, 1 <= nums[i] <= 10000. -/
theorem spec_12 (nums : Slice Std.I64) (hs : SizeOK nums) (hb : BoundsOK nums) :
    ∀ r : Std.I64, Aegis.MinOperations.min_operations nums = ok r →
      ∀ (l u : Nat), l ≤ u → u < nums.val.length →
        ∀ k : Int, IsMinInc (seg (contents nums) l u) k → k ≤ r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64) (hs : SizeOK nums) (hb : BoundsOK nums), ∀ r : Std.I64, Aegis.MinOperations.min_operations nums = ok r →
      ∀ (l u : Nat), l ≤ u → u < nums.val.length →
        ∀ k : Int, IsMinInc (seg (contents nums) l u) k → k ≤ r.val) := by
  sorry

/-- Whenever min_operations(nums) returns a result r, for every i with 0 <= i < n-1, r >= max(0, nums[i] + 1 - nums[i+1]).
  Preconditions: Let n = len(nums). 1 <= n <= 5000 and for every i with 0 <= i < n, 1 <= nums[i] <= 10000. -/
theorem spec_13 (nums : Slice Std.I64) (hs : SizeOK nums) (hb : BoundsOK nums) :
    ∀ r : Std.I64, Aegis.MinOperations.min_operations nums = ok r →
      ∀ i, i + 1 < nums.val.length → max 0 (nth nums i + 1 - nth nums (i + 1)) ≤ r.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums : Slice Std.I64) (hs : SizeOK nums) (hb : BoundsOK nums), ∀ r : Std.I64, Aegis.MinOperations.min_operations nums = ok r →
      ∀ i, i + 1 < nums.val.length → max 0 (nth nums i + 1 - nth nums (i + 1)) ≤ r.val) := by
  sorry

/-- Whenever min_operations(nums) returns a result r, there exists an integer array b of length n such that b[i] >= nums[i] for all 0 <= i < n, b[i] < b[i+1] for all 0 <= i < n-1, sum_{i=0}^{n-1}(b[i]-nums[i]) = r, and b[0] = nums[0].
  Preconditions: Let n = len(nums). 1 <= n <= 5000 and for every i with 0 <= i < n, 1 <= nums[i] <= 10000. -/
theorem spec_14 (nums : Slice Std.I64) (hs : SizeOK nums) (hb : BoundsOK nums) :
    ∀ r : Std.I64, Aegis.MinOperations.min_operations nums = ok r →
      ∃ b : List Int, GEAll (contents nums) b ∧ StrictInc b ∧
        totalInc (contents nums) b = r.val ∧ b[0]! = (contents nums)[0]! := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (nums : Slice Std.I64) (hs : SizeOK nums) (hb : BoundsOK nums), ∀ r : Std.I64, Aegis.MinOperations.min_operations nums = ok r →
      ∃ b : List Int, GEAll (contents nums) b ∧ StrictInc b ∧
        totalInc (contents nums) b = r.val ∧ b[0]! = (contents nums)[0]!) := by
  sorry

/-- Whenever min_operations(nums) returns a result r, there is exactly one integer array b of length n satisfying: b[i] >= nums[i] for all 0 <= i < n; b[i] < b[i+1] for all 0 <= i < n-1; and sum_{i=0}^{n-1}(b[i]-nums[i]) = r.
  Preconditions: Let n = len(nums). 1 <= n <= 5000 and for every i with 0 <= i < n, 1 <= nums[i] <= 10000. -/
theorem spec_15 (nums : Slice Std.I64) (hs : SizeOK nums) (hb : BoundsOK nums) :
    ∀ r : Std.I64, Aegis.MinOperations.min_operations nums = ok r →
      ∃! b : List Int, GEAll (contents nums) b ∧ StrictInc b ∧
        totalInc (contents nums) b = r.val := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (nums : Slice Std.I64) (hs : SizeOK nums) (hb : BoundsOK nums), ∀ r : Std.I64, Aegis.MinOperations.min_operations nums = ok r →
      ∃! b : List Int, GEAll (contents nums) b ∧ StrictInc b ∧
        totalInc (contents nums) b = r.val) := by
  sorry

end AegisSpec.MinOperations
