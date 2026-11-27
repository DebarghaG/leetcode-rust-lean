import Aegis.SubsequencesWithMiddleMode.Code.Funs

/-!
# Specifications of `Aegis.SubsequencesWithMiddleMode.subsequences_with_middle_mode`

LeetCode problem `subsequences-with-a-unique-middle-mode-i`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.SubsequencesWithMiddleMode

  def M : Nat := 1000000007

  def size (nums : Slice Std.I64) : Nat := nums.val.length

  def elemAt (nums : Slice Std.I64) (i : Nat) : Option Int :=
    (nums.val[i]?).map fun x => x.val

  def elemAtD (nums : Slice Std.I64) (i : Nat) : Int := (elemAt nums i).getD 0

  def countOcc (v : Int) (l : List Int) : Nat := (l.filter fun x => decide (x = v)).length

  def fiveVals (nums : Slice Std.I64) (p0 p1 p2 p3 p4 : Nat) : List Int :=
    [elemAtD nums p0, elemAtD nums p1, elemAtD nums p2, elemAtD nums p3, elemAtD nums p4]

  def MiddleUniqueMode (a0 a1 a2 a3 a4 : Int) : Prop :=
    ∀ v : Int, v ≠ a2 → countOcc v [a0, a1, a2, a3, a4] < countOcc a2 [a0, a1, a2, a3, a4]

  def GoodTuple (nums : Slice Std.I64) (p0 p1 p2 p3 p4 : Nat) : Prop :=
    p0 < p1 ∧ p1 < p2 ∧ p2 < p3 ∧ p3 < p4 ∧ p4 < size nums ∧
      MiddleUniqueMode (elemAtD nums p0) (elemAtD nums p1) (elemAtD nums p2)
        (elemAtD nums p3) (elemAtD nums p4)

  structure IdxTuple where

    p0 : Nat

    p1 : Nat

    p2 : Nat

    p3 : Nat

    p4 : Nat
    deriving Repr, DecidableEq

  def idxTuples (n : Nat) : List IdxTuple :=
    (List.range n).flatMap fun p0 =>
      (List.range n).flatMap fun p1 =>
        (List.range n).flatMap fun p2 =>
          (List.range n).flatMap fun p3 =>
            (List.range n).map fun p4 => ⟨p0, p1, p2, p3, p4⟩

  noncomputable def goodCount (nums : Slice Std.I64) : Nat := by
    classical
    exact ((idxTuples (size nums)).map fun t =>
      if GoodTuple nums t.p0 t.p1 t.p2 t.p3 t.p4 then 1 else 0).sum

  def EntriesInRange (nums : Slice Std.I64) : Prop :=
    ∀ (i : Nat), i < size nums →
      ∃ x : Int, elemAt nums i = some x ∧ -(10 ^ 9 : Int) ≤ x ∧ x ≤ (10 ^ 9 : Int)

  def IsReversal (nums rev : Slice Std.I64) : Prop :=
    size rev = size nums ∧
      ∀ (i : Nat), i < size nums → elemAt rev i = elemAt nums (size nums - 1 - i)

  /-- Let M = 1000000007. A length-5 index subsequence is a tuple (p0,p1,p2,p3,p4) with 0 <= p0 < p1 < p2 < p3 < p4 < len(nums). For such a tuple let a_j = nums[p_j] for j=0..4, and for every integer value v let count(v) be the number of j in {0,1,2,3,4} with a_j = v. Call the tuple good when count(v) < count(a2) for every integer v with v != a2; equivalently, the third selected value a2 is the unique value of maximum frequency among the five selected values. Let N be the number of good tuples. Then the function returns a result r and r = N mod M, where 0 <= r < M.
    Preconditions: len(nums) is between 5 and 1000 inclusive, and for every index i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
  theorem spec_1 (nums : Slice Std.I64) (h_len5 : 5 ≤ size nums)
      (h_len1000 : size nums ≤ 1000) (h_entries : EntriesInRange nums) :
      ∃ r : Std.I64,
        Aegis.SubsequencesWithMiddleMode.subsequences_with_middle_mode nums = ok r ∧
          r.val = ((goodCount nums % M : Nat) : Int) ∧ 0 ≤ r.val ∧ r.val < (M : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (h_len5 : 5 ≤ size nums)
        (h_len1000 : size nums ≤ 1000) (h_entries : EntriesInRange nums), ∃ r : Std.I64,
          Aegis.SubsequencesWithMiddleMode.subsequences_with_middle_mode nums = ok r ∧
            r.val = ((goodCount nums % M : Nat) : Int) ∧ 0 ≤ r.val ∧ r.val < (M : Int)) := by
    sorry

  /-- Whenever the function returns a result r on an input satisfying the preconditions, 0 <= r <= 1000000006.
    Preconditions: len(nums) is between 5 and 1000 inclusive, and for every index i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
  theorem spec_2 (nums : Slice Std.I64) (h_len5 : 5 ≤ size nums)
      (h_len1000 : size nums ≤ 1000) (h_entries : EntriesInRange nums) :
      ∀ r : Std.I64,
        Aegis.SubsequencesWithMiddleMode.subsequences_with_middle_mode nums = ok r →
          0 ≤ r.val ∧ r.val ≤ 1000000006 := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (h_len5 : 5 ≤ size nums)
        (h_len1000 : size nums ≤ 1000) (h_entries : EntriesInRange nums), ∀ r : Std.I64,
          Aegis.SubsequencesWithMiddleMode.subsequences_with_middle_mode nums = ok r →
            0 ≤ r.val ∧ r.val ≤ 1000000006) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r and does not fail: no arithmetic overflow, no out-of-bounds access, and no panic occurs.
    Preconditions: len(nums) is between 5 and 1000 inclusive, and for every index i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
  theorem spec_3 (nums : Slice Std.I64) (h_len5 : 5 ≤ size nums)
      (h_len1000 : size nums ≤ 1000) (h_entries : EntriesInRange nums) :
      ∃ r : Std.I64,
        Aegis.SubsequencesWithMiddleMode.subsequences_with_middle_mode nums = ok r := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (h_len5 : 5 ≤ size nums)
        (h_len1000 : size nums ≤ 1000) (h_entries : EntriesInRange nums), ∃ r : Std.I64,
          Aegis.SubsequencesWithMiddleMode.subsequences_with_middle_mode nums = ok r) := by
    sorry

  /-- Let f0 be the number of occurrences of nums[2] among the five entries nums[0], nums[1], nums[2], nums[3], nums[4], and for each value v different from nums[2] let f(v) be the number of occurrences of v among those five entries. The function returns r = 1 if f0 > f(v) for every v != nums[2], and returns r = 0 otherwise.
    Preconditions: len(nums) = 5 and each nums[i] is between -1000000000 and 1000000000 inclusive. -/
  theorem spec_4 (nums : Slice Std.I64) (h_len : size nums = 5)
      (h_entries : EntriesInRange nums) :
      ∃ r : Std.I64,
        Aegis.SubsequencesWithMiddleMode.subsequences_with_middle_mode nums = ok r ∧
          (MiddleUniqueMode (elemAtD nums 0) (elemAtD nums 1) (elemAtD nums 2)
                (elemAtD nums 3) (elemAtD nums 4) →
              r.val = 1) ∧
          (¬ MiddleUniqueMode (elemAtD nums 0) (elemAtD nums 1) (elemAtD nums 2)
                (elemAtD nums 3) (elemAtD nums 4) →
              r.val = 0) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (h_len : size nums = 5)
        (h_entries : EntriesInRange nums), ∃ r : Std.I64,
          Aegis.SubsequencesWithMiddleMode.subsequences_with_middle_mode nums = ok r ∧
            (MiddleUniqueMode (elemAtD nums 0) (elemAtD nums 1) (elemAtD nums 2)
                  (elemAtD nums 3) (elemAtD nums 4) →
                r.val = 1) ∧
            (¬ MiddleUniqueMode (elemAtD nums 0) (elemAtD nums 1) (elemAtD nums 2)
                  (elemAtD nums 3) (elemAtD nums 4) →
                r.val = 0)) := by
    sorry

  /-- The function returns r = (len(nums) choose 5) mod 1000000007.
    Preconditions: 5 <= len(nums) <= 1000 and there is an integer c such that nums[i] = c for every i with 0 <= i < len(nums), with c between -1000000000 and 1000000000. -/
  theorem spec_5 (nums : Slice Std.I64) (h_len5 : 5 ≤ size nums)
      (h_len1000 : size nums ≤ 1000) (c : Int)
      (h_c : -(10 ^ 9 : Int) ≤ c ∧ c ≤ (10 ^ 9 : Int))
      (h_const : ∀ (i : Nat), i < size nums → elemAt nums i = some c) :
      ∃ r : Std.I64,
        Aegis.SubsequencesWithMiddleMode.subsequences_with_middle_mode nums = ok r ∧
          r.val = (((size nums).choose 5 % M : Nat) : Int) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (h_len5 : 5 ≤ size nums)
        (h_len1000 : size nums ≤ 1000) (c : Int)
        (h_c : -(10 ^ 9 : Int) ≤ c ∧ c ≤ (10 ^ 9 : Int))
        (h_const : ∀ (i : Nat), i < size nums → elemAt nums i = some c), ∃ r : Std.I64,
          Aegis.SubsequencesWithMiddleMode.subsequences_with_middle_mode nums = ok r ∧
            r.val = (((size nums).choose 5 % M : Nat) : Int)) := by
    sorry

  /-- The function returns r = 0.
    Preconditions: 5 <= len(nums) <= 1000, each nums[i] is between -1000000000 and 1000000000, and nums[i] != nums[j] for all i,j with 0 <= i < j < len(nums). -/
  theorem spec_6 (nums : Slice Std.I64) (h_len5 : 5 ≤ size nums)
      (h_len1000 : size nums ≤ 1000) (h_entries : EntriesInRange nums)
      (h_distinct : ∀ (i j : Nat), i < j → j < size nums → elemAt nums i ≠ elemAt nums j) :
      ∃ r : Std.I64,
        Aegis.SubsequencesWithMiddleMode.subsequences_with_middle_mode nums = ok r ∧
          r.val = 0 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (h_len5 : 5 ≤ size nums)
        (h_len1000 : size nums ≤ 1000) (h_entries : EntriesInRange nums)
        (h_distinct : ∀ (i j : Nat), i < j → j < size nums → elemAt nums i ≠ elemAt nums j), ∃ r : Std.I64,
          Aegis.SubsequencesWithMiddleMode.subsequences_with_middle_mode nums = ok r ∧
            r.val = 0) := by
    sorry

  /-- Let N be the number of length-5 index subsequences whose third selected value is the unique mode among the five selected values. Whenever the function returns a nonzero result r (r != 0), N > 0; equivalently, there exist indices 0 <= p0 < p1 < p2 < p3 < p4 < len(nums) such that nums[p2] is the unique mode among nums[p0], nums[p1], nums[p2], nums[p3], nums[p4].
    Preconditions: len(nums) is between 5 and 1000 inclusive, and every nums[i] is between -1000000000 and 1000000000. -/
  theorem spec_7 (nums : Slice Std.I64) (h_len5 : 5 ≤ size nums)
      (h_len1000 : size nums ≤ 1000) (h_entries : EntriesInRange nums) :
      ∀ r : Std.I64,
        Aegis.SubsequencesWithMiddleMode.subsequences_with_middle_mode nums = ok r →
          r.val ≠ 0 → 0 < goodCount nums := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (h_len5 : 5 ≤ size nums)
        (h_len1000 : size nums ≤ 1000) (h_entries : EntriesInRange nums), ∀ r : Std.I64,
          Aegis.SubsequencesWithMiddleMode.subsequences_with_middle_mode nums = ok r →
            r.val ≠ 0 → 0 < goodCount nums) := by
    sorry

  /-- The result returned for nums equals the result returned for rev.
    Preconditions: nums and its reversal rev both have length between 5 and 1000 inclusive and all their entries are between -1000000000 and 1000000000, where rev[i] = nums[len(nums)-1-i]. -/
  theorem spec_8 (nums rev : Slice Std.I64) (h_rev : IsReversal nums rev)
      (h_len5 : 5 ≤ size nums) (h_len1000 : size nums ≤ 1000)
      (h_entries : EntriesInRange nums) (h_len5' : 5 ≤ size rev)
      (h_len1000' : size rev ≤ 1000) (h_entries' : EntriesInRange rev) :
      ∀ r s : Std.I64,
        Aegis.SubsequencesWithMiddleMode.subsequences_with_middle_mode nums = ok r →
          Aegis.SubsequencesWithMiddleMode.subsequences_with_middle_mode rev = ok s →
            r = s := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums rev : Slice Std.I64) (h_rev : IsReversal nums rev)
        (h_len5 : 5 ≤ size nums) (h_len1000 : size nums ≤ 1000)
        (h_entries : EntriesInRange nums) (h_len5' : 5 ≤ size rev)
        (h_len1000' : size rev ≤ 1000) (h_entries' : EntriesInRange rev), ∀ r s : Std.I64,
          Aegis.SubsequencesWithMiddleMode.subsequences_with_middle_mode nums = ok r →
            Aegis.SubsequencesWithMiddleMode.subsequences_with_middle_mode rev = ok s →
              r = s) := by
    sorry

  /-- The result returned for nums equals the result returned for nums2.
    Preconditions: nums and nums2 are two slices with the same length n, where 5 <= n <= 1000, all entries of both slices are between -1000000000 and 1000000000, and for all i,j with 0 <= i < n and 0 <= j < n, nums[i] = nums[j] if and only if nums2[i] = nums2[j]. -/
  theorem spec_9 (nums nums2 : Slice Std.I64) (n : Nat) (h_len : size nums = n)
      (h_len2 : size nums2 = n) (h_n5 : 5 ≤ n) (h_n1000 : n ≤ 1000)
      (h_entries : EntriesInRange nums) (h_entries2 : EntriesInRange nums2)
      (h_same : ∀ (i j : Nat), i < n → j < n →
        (elemAt nums i = elemAt nums j ↔ elemAt nums2 i = elemAt nums2 j)) :
      ∀ r s : Std.I64,
        Aegis.SubsequencesWithMiddleMode.subsequences_with_middle_mode nums = ok r →
          Aegis.SubsequencesWithMiddleMode.subsequences_with_middle_mode nums2 = ok s →
            r = s := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums nums2 : Slice Std.I64) (n : Nat) (h_len : size nums = n)
        (h_len2 : size nums2 = n) (h_n5 : 5 ≤ n) (h_n1000 : n ≤ 1000)
        (h_entries : EntriesInRange nums) (h_entries2 : EntriesInRange nums2)
        (h_same : ∀ (i j : Nat), i < n → j < n →
          (elemAt nums i = elemAt nums j ↔ elemAt nums2 i = elemAt nums2 j)), ∀ r s : Std.I64,
          Aegis.SubsequencesWithMiddleMode.subsequences_with_middle_mode nums = ok r →
            Aegis.SubsequencesWithMiddleMode.subsequences_with_middle_mode nums2 = ok s →
              r = s) := by
    sorry

  /-- Let N be the number of length-5 index subsequences for which the third selected value is the unique mode among the five selected values. Then the function returns r = N.
    Preconditions: 5 <= len(nums) <= 100 and all entries are between -1000000000 and 1000000000. -/
  theorem spec_10 (nums : Slice Std.I64) (h_len5 : 5 ≤ size nums) (h_len100 : size nums ≤ 100)
      (h_entries : EntriesInRange nums) :
      ∃ r : Std.I64,
        Aegis.SubsequencesWithMiddleMode.subsequences_with_middle_mode nums = ok r ∧
          r.val = (goodCount nums : Int) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64) (h_len5 : 5 ≤ size nums) (h_len100 : size nums ≤ 100)
        (h_entries : EntriesInRange nums), ∃ r : Std.I64,
          Aegis.SubsequencesWithMiddleMode.subsequences_with_middle_mode nums = ok r ∧
            r.val = (goodCount nums : Int)) := by
    sorry

  /-- Let N be the number of length-5 index subsequences whose third selected value is the unique mode among the five selected values. Whenever the function returns a result r, r - N is divisible by 1000000007.
    Preconditions: len(nums) is between 5 and 1000 inclusive, and every nums[i] is between -1000000000 and 1000000000. -/
  theorem spec_11 (nums : Slice Std.I64) (h_len5 : 5 ≤ size nums)
      (h_len1000 : size nums ≤ 1000) (h_entries : EntriesInRange nums) :
      ∀ r : Std.I64,
        Aegis.SubsequencesWithMiddleMode.subsequences_with_middle_mode nums = ok r →
          ∃ k : Int, r.val - (goodCount nums : Int) = (1000000007 : Int) * k := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64) (h_len5 : 5 ≤ size nums)
        (h_len1000 : size nums ≤ 1000) (h_entries : EntriesInRange nums), ∀ r : Std.I64,
          Aegis.SubsequencesWithMiddleMode.subsequences_with_middle_mode nums = ok r →
            ∃ k : Int, r.val - (goodCount nums : Int) = (1000000007 : Int) * k) := by
    sorry

  /-- If there is no index tuple 0 <= p0 < p1 < p2 < p3 < p4 < len(nums) for which nums[p2] is the unique mode among nums[p0], nums[p1], nums[p2], nums[p3], nums[p4], then the function returns r = 0.
    Preconditions: len(nums) is between 5 and 1000 inclusive, and every nums[i] is between -1000000000 and 1000000000. -/
  theorem spec_12 (nums : Slice Std.I64) (h_len5 : 5 ≤ size nums)
      (h_len1000 : size nums ≤ 1000) (h_entries : EntriesInRange nums)
      (h_none : ∀ (p0 p1 p2 p3 p4 : Nat), p0 < p1 → p1 < p2 → p2 < p3 → p3 < p4 →
        p4 < size nums →
          ¬ MiddleUniqueMode (elemAtD nums p0) (elemAtD nums p1) (elemAtD nums p2)
            (elemAtD nums p3) (elemAtD nums p4)) :
      ∃ r : Std.I64,
        Aegis.SubsequencesWithMiddleMode.subsequences_with_middle_mode nums = ok r ∧
          r.val = 0 := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice Std.I64) (h_len5 : 5 ≤ size nums)
        (h_len1000 : size nums ≤ 1000) (h_entries : EntriesInRange nums)
        (h_none : ∀ (p0 p1 p2 p3 p4 : Nat), p0 < p1 → p1 < p2 → p2 < p3 → p3 < p4 →
          p4 < size nums →
            ¬ MiddleUniqueMode (elemAtD nums p0) (elemAtD nums p1) (elemAtD nums p2)
              (elemAtD nums p3) (elemAtD nums p4)), ∃ r : Std.I64,
          Aegis.SubsequencesWithMiddleMode.subsequences_with_middle_mode nums = ok r ∧
            r.val = 0) := by
    sorry

  end AegisSpec.SubsequencesWithMiddleMode
