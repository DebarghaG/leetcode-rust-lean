import Aegis.MinimumIndex.Code.Funs

/-!
# Specifications of `Aegis.MinimumIndex.minimum_index`

LeetCode problem `minimum-index-of-a-valid-split`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MinimumIndex

namespace AegisSpec.MinimumIndex

def countVal (a : List I64) (x : Int) : Nat :=
  a.countP (fun v => v.val == x)

def DominantIn (x : Int) (a : List I64) : Prop :=
  2 * countVal a x > a.length

def IsUniqueDominant (a : List I64) (d : Int) : Prop :=
  DominantIn d a ∧ ∀ x : Int, DominantIn x a → x = d

def HasUniqueDominant (a : List I64) : Prop :=
  ∃ d : Int, IsUniqueDominant a d

def prefSeg (a : List I64) (i : Nat) : List I64 := a.take (i + 1)

def suffSeg (a : List I64) (i : Nat) : List I64 := a.drop (i + 1)

def SplitsAt (a : List I64) (i : Nat) : Prop :=
  ∃ x : Int, DominantIn x (prefSeg a i) ∧ DominantIn x (suffSeg a i)

def HasSplit (a : List I64) : Prop :=
  ∃ i : Nat, i < a.length - 1 ∧ SplitsAt a i

def IsLeastSplit (a : List I64) (r : Int) : Prop :=
  0 ≤ r ∧ r.toNat < a.length - 1 ∧ SplitsAt a r.toNat ∧
    ∀ j : Nat, j < a.length - 1 → SplitsAt a j → r ≤ (j : Int)

def IsLeastPrefixDominant (a : List I64) (d : Int) (r : Int) : Prop :=
  0 ≤ r ∧ r.toNat < a.length - 1 ∧ DominantIn d (prefSeg a r.toNat) ∧
    ∀ j : Nat, j < a.length - 1 → DominantIn d (prefSeg a j) → r ≤ (j : Int)

def balance (a : List I64) (d : Int) : Int :=
  2 * (countVal a d : Int) - (a.length : Int)

def dMask (a : List I64) (d : Int) : List Bool :=
  a.map (fun v => v.val == d)

/-- For every input satisfying the preconditions, whenever minimum_index(nums) returns a result r, the following holds. Let V be the set of all integers i such that 0 <= i < len(nums) - 1, and there exists an integer x that is dominant in nums[0..i] and also dominant in nums[i+1..len(nums)-1]. If V is nonempty, r is the least element of V; if V is empty, r = -1.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. Also nums has exactly one dominant element, where an integer x is dominant in a finite array or segment a iff 2 * (the number of positions j in a with a[j] = x) > len(a). -/
theorem spec_1 (nums : Slice I64)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hbound : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 1000000000)
    (hdom : HasUniqueDominant nums.val) :
    ∀ r : I64, minimum_index nums = ok r →
      ((HasSplit nums.val → IsLeastSplit nums.val r.val) ∧
        (¬ HasSplit nums.val → r.val = -1)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hbound : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 1000000000)
    (hdom : HasUniqueDominant nums.val), ∀ r : I64, minimum_index nums = ok r →
      ((HasSplit nums.val → IsLeastSplit nums.val r.val) ∧
        (¬ HasSplit nums.val → r.val = -1))) := by
  sorry

/-- For every input satisfying the preconditions, the call minimum_index(nums) returns a result r; it does not fail, panic, or overflow.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. Also nums has exactly one dominant element, where an integer x is dominant in a finite array or segment a iff 2 * (the number of positions j in a with a[j] = x) > len(a). -/
theorem spec_2 (nums : Slice I64)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hbound : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 1000000000)
    (hdom : HasUniqueDominant nums.val) :
    ∃ r : I64, minimum_index nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hbound : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 1000000000)
    (hdom : HasUniqueDominant nums.val), ∃ r : I64, minimum_index nums = ok r) := by
  sorry

/-- For every input satisfying the preconditions, whenever minimum_index(nums) returns r, either r = -1 or 0 <= r < len(nums) - 1.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. Also nums has exactly one dominant element, where an integer x is dominant in a finite array or segment a iff 2 * (the number of positions j in a with a[j] = x) > len(a). -/
theorem spec_3 (nums : Slice I64)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hbound : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 1000000000)
    (hdom : HasUniqueDominant nums.val) :
    ∀ r : I64, minimum_index nums = ok r →
      (r.val = -1 ∨ (0 ≤ r.val ∧ r.val < (nums.val.length : Int) - 1)) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hbound : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 1000000000)
    (hdom : HasUniqueDominant nums.val), ∀ r : I64, minimum_index nums = ok r →
      (r.val = -1 ∨ (0 ≤ r.val ∧ r.val < (nums.val.length : Int) - 1))) := by
  sorry

/-- For every input satisfying the preconditions, whenever minimum_index(nums) returns r with r != -1, there exists an integer x that is dominant in nums[0..r] and dominant in nums[r+1..len(nums)-1].
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. Also nums has exactly one dominant element, where an integer x is dominant in a finite array or segment a iff 2 * (the number of positions j in a with a[j] = x) > len(a). -/
theorem spec_4 (nums : Slice I64)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hbound : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 1000000000)
    (hdom : HasUniqueDominant nums.val) :
    ∀ r : I64, minimum_index nums = ok r → r.val ≠ -1 →
      SplitsAt nums.val r.val.toNat := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hbound : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 1000000000)
    (hdom : HasUniqueDominant nums.val), ∀ r : I64, minimum_index nums = ok r → r.val ≠ -1 →
      SplitsAt nums.val r.val.toNat) := by
  sorry

/-- For every input satisfying the preconditions, whenever minimum_index(nums) returns r with r != -1, for every integer j with 0 <= j < r and j < len(nums) - 1, there is no integer x that is dominant in both nums[0..j] and nums[j+1..len(nums)-1].
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. Also nums has exactly one dominant element, where an integer x is dominant in a finite array or segment a iff 2 * (the number of positions j in a with a[j] = x) > len(a). -/
theorem spec_5 (nums : Slice I64)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hbound : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 1000000000)
    (hdom : HasUniqueDominant nums.val) :
    ∀ r : I64, minimum_index nums = ok r → r.val ≠ -1 →
      ∀ j : Nat, (j : Int) < r.val → j < nums.val.length - 1 →
        ¬ SplitsAt nums.val j := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hbound : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 1000000000)
    (hdom : HasUniqueDominant nums.val), ∀ r : I64, minimum_index nums = ok r → r.val ≠ -1 →
      ∀ j : Nat, (j : Int) < r.val → j < nums.val.length - 1 →
        ¬ SplitsAt nums.val j) := by
  sorry

/-- For every input satisfying the preconditions, whenever minimum_index(nums) returns r, r = -1 if and only if there is no integer i with 0 <= i < len(nums) - 1 for which some integer x is dominant in both nums[0..i] and nums[i+1..len(nums)-1].
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. Also nums has exactly one dominant element, where an integer x is dominant in a finite array or segment a iff 2 * (the number of positions j in a with a[j] = x) > len(a). -/
theorem spec_6 (nums : Slice I64)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hbound : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 1000000000)
    (hdom : HasUniqueDominant nums.val) :
    ∀ r : I64, minimum_index nums = ok r →
      (r.val = -1 ↔ ¬ HasSplit nums.val) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hbound : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 1000000000)
    (hdom : HasUniqueDominant nums.val), ∀ r : I64, minimum_index nums = ok r →
      (r.val = -1 ↔ ¬ HasSplit nums.val)) := by
  sorry

/-- Let d be the unique dominant element of nums. For every input satisfying the preconditions, whenever minimum_index(nums) returns r with r != -1, every integer x that is dominant in both nums[0..r] and nums[r+1..len(nums)-1] satisfies x = d.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. Also nums has exactly one dominant element, where an integer x is dominant in a finite array or segment a iff 2 * (the number of positions j in a with a[j] = x) > len(a). -/
theorem spec_7 (nums : Slice I64)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hbound : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 1000000000)
    (d : Int) (hd : IsUniqueDominant nums.val d) :
    ∀ r : I64, minimum_index nums = ok r → r.val ≠ -1 →
      ∀ x : Int, DominantIn x (prefSeg nums.val r.val.toNat) →
        DominantIn x (suffSeg nums.val r.val.toNat) → x = d := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hbound : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 1000000000)
    (d : Int) (hd : IsUniqueDominant nums.val d), ∀ r : I64, minimum_index nums = ok r → r.val ≠ -1 →
      ∀ x : Int, DominantIn x (prefSeg nums.val r.val.toNat) →
        DominantIn x (suffSeg nums.val r.val.toNat) → x = d) := by
  sorry

/-- Let d be the unique dominant element of nums and let C be the total number of positions j with 0 <= j < len(nums) and nums[j] = d. For every input satisfying the preconditions, whenever minimum_index(nums) returns r with r != -1, if P is the number of positions j with 0 <= j <= r and nums[j] = d, then 2 * P > r + 1 and 2 * (C - P) > len(nums) - r - 1.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. Also nums has exactly one dominant element, where an integer x is dominant in a finite array or segment a iff 2 * (the number of positions j in a with a[j] = x) > len(a). -/
theorem spec_8 (nums : Slice I64)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hbound : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 1000000000)
    (d : Int) (hd : IsUniqueDominant nums.val d) :
    ∀ r : I64, minimum_index nums = ok r → r.val ≠ -1 →
      (let C := countVal nums.val d
       let P := countVal (prefSeg nums.val r.val.toNat) d
       2 * P > r.val.toNat + 1 ∧
         2 * (C - P) > nums.val.length - (r.val.toNat + 1)) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hbound : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 1000000000)
    (d : Int) (hd : IsUniqueDominant nums.val d), ∀ r : I64, minimum_index nums = ok r → r.val ≠ -1 →
      (let C := countVal nums.val d
       let P := countVal (prefSeg nums.val r.val.toNat) d
       2 * P > r.val.toNat + 1 ∧
         2 * (C - P) > nums.val.length - (r.val.toNat + 1))) := by
  sorry

/-- Let d be the unique dominant element of nums and let C be the total number of positions j with nums[j] = d. If 2 * C - len(nums) = 1, then whenever minimum_index(nums) returns r, r = -1.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. Also nums has exactly one dominant element, where an integer x is dominant in a finite array or segment a iff 2 * (the number of positions j in a with a[j] = x) > len(a). -/
theorem spec_9 (nums : Slice I64)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hbound : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 1000000000)
    (d : Int) (hd : IsUniqueDominant nums.val d) :
    balance nums.val d = 1 →
      ∀ r : I64, minimum_index nums = ok r → r.val = -1 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hbound : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 1000000000)
    (d : Int) (hd : IsUniqueDominant nums.val d), balance nums.val d = 1 →
      ∀ r : I64, minimum_index nums = ok r → r.val = -1) := by
  sorry

/-- Let d be the unique dominant element of nums and let C be the total number of positions j with nums[j] = d. If 2 * C - len(nums) >= 2, then whenever minimum_index(nums) returns r, r != -1.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. Also nums has exactly one dominant element, where an integer x is dominant in a finite array or segment a iff 2 * (the number of positions j in a with a[j] = x) > len(a). -/
theorem spec_10 (nums : Slice I64)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hbound : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 1000000000)
    (d : Int) (hd : IsUniqueDominant nums.val d) :
    2 ≤ balance nums.val d →
      ∀ r : I64, minimum_index nums = ok r → r.val ≠ -1 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hbound : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 1000000000)
    (d : Int) (hd : IsUniqueDominant nums.val d), 2 ≤ balance nums.val d →
      ∀ r : I64, minimum_index nums = ok r → r.val ≠ -1) := by
  sorry

/-- Let d be the unique dominant element of nums. For every input satisfying the preconditions, whenever minimum_index(nums) returns r with r != -1, r is the least integer i such that 0 <= i < len(nums) - 1 and d is dominant in nums[0..i].
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. Also nums has exactly one dominant element, where an integer x is dominant in a finite array or segment a iff 2 * (the number of positions j in a with a[j] = x) > len(a). -/
theorem spec_11 (nums : Slice I64)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hbound : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 1000000000)
    (d : Int) (hd : IsUniqueDominant nums.val d) :
    ∀ r : I64, minimum_index nums = ok r → r.val ≠ -1 →
      IsLeastPrefixDominant nums.val d r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hbound : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 1000000000)
    (d : Int) (hd : IsUniqueDominant nums.val d), ∀ r : I64, minimum_index nums = ok r → r.val ≠ -1 →
      IsLeastPrefixDominant nums.val d r.val) := by
  sorry

/-- Let d be the unique dominant element of nums and let C be the total number of positions j with nums[j] = d. For every input satisfying the preconditions, whenever minimum_index(nums) returns r with r = -1, 2 * C - len(nums) = 1.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. Also nums has exactly one dominant element, where an integer x is dominant in a finite array or segment a iff 2 * (the number of positions j in a with a[j] = x) > len(a). -/
theorem spec_12 (nums : Slice I64)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hbound : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 1000000000)
    (d : Int) (hd : IsUniqueDominant nums.val d) :
    ∀ r : I64, minimum_index nums = ok r → r.val = -1 →
      balance nums.val d = 1 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hbound : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 1000000000)
    (d : Int) (hd : IsUniqueDominant nums.val d), ∀ r : I64, minimum_index nums = ok r → r.val = -1 →
      balance nums.val d = 1) := by
  sorry

/-- If minimum_index(nums) returns r and minimum_index(nums2) returns r2, then r = r2.
  Preconditions: Let n = len(nums) = len(nums2). Assume 1 <= n <= 100000, and all entries of nums and nums2 lie in the interval [1, 1000000000]. Assume there is an integer d such that d is the unique dominant element of nums and, for every j with 0 <= j < n, nums[j] = d if and only if nums2[j] = d. Here an integer x is dominant in a finite array or segment a iff 2 * (the number of positions in a equal to x) > len(a). -/
theorem spec_13 (nums nums2 : Slice I64)
    (hlen : nums.val.length = nums2.val.length)
    (hn : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hbound1 : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 1000000000)
    (hbound2 : ∀ v ∈ nums2.val, 1 ≤ v.val ∧ v.val ≤ 1000000000)
    (hd : ∃ d : Int, IsUniqueDominant nums.val d ∧ dMask nums.val d = dMask nums2.val d) :
    ∀ r r2 : I64, minimum_index nums = ok r → minimum_index nums2 = ok r2 →
      r.val = r2.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums nums2 : Slice I64)
    (hlen : nums.val.length = nums2.val.length)
    (hn : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hbound1 : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 1000000000)
    (hbound2 : ∀ v ∈ nums2.val, 1 ≤ v.val ∧ v.val ≤ 1000000000)
    (hd : ∃ d : Int, IsUniqueDominant nums.val d ∧ dMask nums.val d = dMask nums2.val d), ∀ r r2 : I64, minimum_index nums = ok r → minimum_index nums2 = ok r2 →
      r.val = r2.val) := by
  sorry

end AegisSpec.MinimumIndex
