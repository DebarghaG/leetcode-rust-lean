import Aegis.CountElements.Code.Funs

/-!
# Specifications of `Aegis.CountElements.count_elements`

LeetCode problem `count-elements-with-strictly-smaller-and-greater-elements`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.CountElements

  namespace AegisSpec.CountElements

  def len (nums : Slice Std.I64) : Nat := nums.val.length

  def elem (nums : Slice Std.I64) (i : Nat) : Int := (nums.val.getD i default).val

  def values (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

  def listMin : List Int → Int
    | [] => 0
    | a :: l => l.foldl min a

  def listMax : List Int → Int
    | [] => 0
    | a :: l => l.foldl max a

  def mn (nums : Slice Std.I64) : Int := listMin (values nums)

  def mx (nums : Slice Std.I64) : Int := listMax (values nums)

  def countOfVal (nums : Slice Std.I64) (v : Int) : Nat :=
    nums.val.countP (fun x => x.val == v)

  def sameMultiset (nums b : Slice Std.I64) : Prop :=
    ∀ v : Int, countOfVal nums v = countOfVal b v

  def existsBelow (nums : Slice Std.I64) (i : Nat) : Prop :=
    ∃ j, j < len nums ∧ elem nums j < elem nums i

  def existsAbove (nums : Slice Std.I64) (i : Nat) : Prop :=
    ∃ k, k < len nums ∧ elem nums i < elem nums k

  def inside (nums : Slice Std.I64) (i : Nat) : Prop :=
    existsBelow nums i ∧ existsAbove nums i

  noncomputable def countInside (nums : Slice Std.I64) : Nat :=
    letI := Classical.decPred (fun i => inside nums i)
    ((Finset.range (len nums)).filter (fun i => inside nums i)).card

  /-- The function returns a result r and r equals the number of indices i with 0 <= i < len(nums) such that there exists j with 0 <= j < len(nums) and nums[j] < nums[i], and there exists k with 0 <= k < len(nums) and nums[k] > nums[i].
    Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000. -/
  theorem spec_1 (nums : Slice Std.I64)
      (hlo : 1 ≤ len nums) (hhi : len nums ≤ 100)
      (hval : ∀ i, i < len nums → -100000 ≤ elem nums i ∧ elem nums i ≤ 100000) :
      ∃ r, count_elements nums = ok r ∧ r.val = (countInside nums : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlo : 1 ≤ len nums) (hhi : len nums ≤ 100)
        (hval : ∀ i, i < len nums → -100000 ≤ elem nums i ∧ elem nums i ≤ 100000), ∃ r, count_elements nums = ok r ∧ r.val = (countInside nums : Int)) := by
    sorry

  /-- The function returns a result r and 0 <= r <= len(nums) - 1.
    Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000. -/
  theorem spec_2 (nums : Slice Std.I64)
      (hlo : 1 ≤ len nums) (hhi : len nums ≤ 100)
      (hval : ∀ i, i < len nums → -100000 ≤ elem nums i ∧ elem nums i ≤ 100000) :
      ∃ r, count_elements nums = ok r ∧ 0 ≤ r.val ∧ r.val ≤ (len nums : Int) - 1 := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlo : 1 ≤ len nums) (hhi : len nums ≤ 100)
        (hval : ∀ i, i < len nums → -100000 ≤ elem nums i ∧ elem nums i ≤ 100000), ∃ r, count_elements nums = ok r ∧ 0 ≤ r.val ∧ r.val ≤ (len nums : Int) - 1) := by
    sorry

  /-- Whenever the function returns a result r, if there exist indices p and q with 0 <= p < len(nums) and 0 <= q < len(nums) and nums[p] != nums[q], then r <= len(nums) - 2.
    Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000. -/
  theorem spec_3 (nums : Slice Std.I64)
      (hlo : 1 ≤ len nums) (hhi : len nums ≤ 100)
      (hval : ∀ i, i < len nums → -100000 ≤ elem nums i ∧ elem nums i ≤ 100000) :
      ∀ r, count_elements nums = ok r →
        (∃ p q, p < len nums ∧ q < len nums ∧ elem nums p ≠ elem nums q) →
        r.val ≤ (len nums : Int) - 2 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlo : 1 ≤ len nums) (hhi : len nums ≤ 100)
        (hval : ∀ i, i < len nums → -100000 ≤ elem nums i ∧ elem nums i ≤ 100000), ∀ r, count_elements nums = ok r →
          (∃ p q, p < len nums ∧ q < len nums ∧ elem nums p ≠ elem nums q) →
          r.val ≤ (len nums : Int) - 2) := by
    sorry

  /-- Let mn be the minimum of the set of values {nums[t] | 0 <= t < len(nums)} and mx be the maximum of that set. If mn < mx, then the function returns a result r and r = len(nums) - (the number of indices i with 0 <= i < len(nums) and nums[i] = mn) - (the number of indices i with 0 <= i < len(nums) and nums[i] = mx).
    Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000. -/
  theorem spec_4 (nums : Slice Std.I64)
      (hlo : 1 ≤ len nums) (hhi : len nums ≤ 100)
      (hval : ∀ i, i < len nums → -100000 ≤ elem nums i ∧ elem nums i ≤ 100000) :
      mn nums < mx nums →
        ∃ r, count_elements nums = ok r ∧
          r.val = (len nums : Int) - (countOfVal nums (mn nums) : Int)
                    - (countOfVal nums (mx nums) : Int) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlo : 1 ≤ len nums) (hhi : len nums ≤ 100)
        (hval : ∀ i, i < len nums → -100000 ≤ elem nums i ∧ elem nums i ≤ 100000), mn nums < mx nums →
          ∃ r, count_elements nums = ok r ∧
            r.val = (len nums : Int) - (countOfVal nums (mn nums) : Int)
                      - (countOfVal nums (mx nums) : Int)) := by
    sorry

  /-- The function returns a result r and r > 0 if and only if there exist indices a, b, and c with 0 <= a < len(nums), 0 <= b < len(nums), and 0 <= c < len(nums) such that nums[a] < nums[b] < nums[c].
    Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000. -/
  theorem spec_5 (nums : Slice Std.I64)
      (hlo : 1 ≤ len nums) (hhi : len nums ≤ 100)
      (hval : ∀ i, i < len nums → -100000 ≤ elem nums i ∧ elem nums i ≤ 100000) :
      ∃ r, count_elements nums = ok r ∧
        (r.val > 0 ↔ ∃ a b c, a < len nums ∧ b < len nums ∧ c < len nums ∧
          elem nums a < elem nums b ∧ elem nums b < elem nums c) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlo : 1 ≤ len nums) (hhi : len nums ≤ 100)
        (hval : ∀ i, i < len nums → -100000 ≤ elem nums i ∧ elem nums i ≤ 100000), ∃ r, count_elements nums = ok r ∧
          (r.val > 0 ↔ ∃ a b c, a < len nums ∧ b < len nums ∧ c < len nums ∧
            elem nums a < elem nums b ∧ elem nums b < elem nums c)) := by
    sorry

  /-- The function returns a result r and r = len(nums) - 2.
    Preconditions: 1 <= len(nums) <= 100, for every i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000, len(nums) >= 2, and for every i with 0 <= i < len(nums) - 1, nums[i] < nums[i+1]. -/
  theorem spec_6 (nums : Slice Std.I64)
      (hlo : 1 ≤ len nums) (hhi : len nums ≤ 100)
      (hval : ∀ i, i < len nums → -100000 ≤ elem nums i ∧ elem nums i ≤ 100000)
      (h2 : 2 ≤ len nums)
      (hsorted : ∀ i, i < len nums - 1 → elem nums i < elem nums (i + 1)) :
      ∃ r, count_elements nums = ok r ∧ r.val = (len nums : Int) - 2 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlo : 1 ≤ len nums) (hhi : len nums ≤ 100)
        (hval : ∀ i, i < len nums → -100000 ≤ elem nums i ∧ elem nums i ≤ 100000)
        (h2 : 2 ≤ len nums)
        (hsorted : ∀ i, i < len nums - 1 → elem nums i < elem nums (i + 1)), ∃ r, count_elements nums = ok r ∧ r.val = (len nums : Int) - 2) := by
    sorry

  /-- For every slice b of 64-bit integers with len(b) = len(nums) and all entries in [-100000, 100000], if b has the same multiset of values as nums (that is, for every integer v, the number of indices i with nums[i] = v equals the number of indices j with b[j] = v), then the function returns a result r for nums and a result r_b for b, and r = r_b.
    Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000. -/
  theorem spec_7 (nums : Slice Std.I64)
      (hlo : 1 ≤ len nums) (hhi : len nums ≤ 100)
      (hval : ∀ i, i < len nums → -100000 ≤ elem nums i ∧ elem nums i ≤ 100000) :
      ∀ b : Slice Std.I64, len b = len nums →
        (∀ j, j < len b → -100000 ≤ elem b j ∧ elem b j ≤ 100000) →
        sameMultiset nums b →
        ∃ r rb, count_elements nums = ok r ∧ count_elements b = ok rb ∧ r.val = rb.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlo : 1 ≤ len nums) (hhi : len nums ≤ 100)
        (hval : ∀ i, i < len nums → -100000 ≤ elem nums i ∧ elem nums i ≤ 100000), ∀ b : Slice Std.I64, len b = len nums →
          (∀ j, j < len b → -100000 ≤ elem b j ∧ elem b j ≤ 100000) →
          sameMultiset nums b →
          ∃ r rb, count_elements nums = ok r ∧ count_elements b = ok rb ∧ r.val = rb.val) := by
    sorry

  /-- Let mn be the minimum of the set of values {nums[t] | 0 <= t < len(nums)} and mx be the maximum of that set. For every integer v such that v = mn or v = mx, let nums2 be the slice of length len(nums) + 1 with nums2[i] = nums[i] for 0 <= i < len(nums) and nums2[len(nums)] = v. Then the function returns a result r for nums and a result r2 for nums2, and r2 = r.
    Preconditions: 1 <= len(nums) <= 99 and for every i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000. -/
  theorem spec_8 (nums : Slice Std.I64)
      (hlo : 1 ≤ len nums) (hhi : len nums ≤ 99)
      (hval : ∀ i, i < len nums → -100000 ≤ elem nums i ∧ elem nums i ≤ 100000) :
      ∀ v : Std.I64, (v.val = mn nums ∨ v.val = mx nums) →
        ∀ nums2 : Slice Std.I64, nums2.val = nums.val ++ [v] →
          ∃ r r2, count_elements nums = ok r ∧ count_elements nums2 = ok r2 ∧
            r2.val = r.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlo : 1 ≤ len nums) (hhi : len nums ≤ 99)
        (hval : ∀ i, i < len nums → -100000 ≤ elem nums i ∧ elem nums i ≤ 100000), ∀ v : Std.I64, (v.val = mn nums ∨ v.val = mx nums) →
          ∀ nums2 : Slice Std.I64, nums2.val = nums.val ++ [v] →
            ∃ r r2, count_elements nums = ok r ∧ count_elements nums2 = ok r2 ∧
              r2.val = r.val) := by
    sorry

  /-- Let mn be the minimum of the set of values {nums[t] | 0 <= t < len(nums)} and mx be the maximum of that set. For every integer v with mn < v < mx, let nums2 be the slice of length len(nums) + 1 with nums2[i] = nums[i] for 0 <= i < len(nums) and nums2[len(nums)] = v. Then the function returns a result r for nums and a result r2 for nums2, and r2 = r + 1.
    Preconditions: 1 <= len(nums) <= 99 and for every i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000. -/
  theorem spec_9 (nums : Slice Std.I64)
      (hlo : 1 ≤ len nums) (hhi : len nums ≤ 99)
      (hval : ∀ i, i < len nums → -100000 ≤ elem nums i ∧ elem nums i ≤ 100000) :
      ∀ v : Std.I64, mn nums < v.val → v.val < mx nums →
        ∀ nums2 : Slice Std.I64, nums2.val = nums.val ++ [v] →
          ∃ r r2, count_elements nums = ok r ∧ count_elements nums2 = ok r2 ∧
            r2.val = r.val + 1 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlo : 1 ≤ len nums) (hhi : len nums ≤ 99)
        (hval : ∀ i, i < len nums → -100000 ≤ elem nums i ∧ elem nums i ≤ 100000), ∀ v : Std.I64, mn nums < v.val → v.val < mx nums →
          ∀ nums2 : Slice Std.I64, nums2.val = nums.val ++ [v] →
            ∃ r r2, count_elements nums = ok r ∧ count_elements nums2 = ok r2 ∧
              r2.val = r.val + 1) := by
    sorry

  /-- Let nums2 be the slice of length 2 * len(nums) with nums2[i] = nums[i] for 0 <= i < len(nums) and nums2[i] = nums[i - len(nums)] for len(nums) <= i < 2 * len(nums). Then the function returns a result r for nums and a result r2 for nums2, and r2 = 2 * r.
    Preconditions: 1 <= len(nums) <= 50 and for every i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000. -/
  theorem spec_10 (nums : Slice Std.I64)
      (hlo : 1 ≤ len nums) (hhi : len nums ≤ 50)
      (hval : ∀ i, i < len nums → -100000 ≤ elem nums i ∧ elem nums i ≤ 100000) :
      ∀ nums2 : Slice Std.I64, nums2.val = nums.val ++ nums.val →
        ∃ r r2, count_elements nums = ok r ∧ count_elements nums2 = ok r2 ∧
          r2.val = 2 * r.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlo : 1 ≤ len nums) (hhi : len nums ≤ 50)
        (hval : ∀ i, i < len nums → -100000 ≤ elem nums i ∧ elem nums i ≤ 100000), ∀ nums2 : Slice Std.I64, nums2.val = nums.val ++ nums.val →
          ∃ r r2, count_elements nums = ok r ∧ count_elements nums2 = ok r2 ∧
            r2.val = 2 * r.val) := by
    sorry

  end AegisSpec.CountElements
