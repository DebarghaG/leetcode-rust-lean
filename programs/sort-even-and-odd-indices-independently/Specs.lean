import Aegis.SortEvenOdd.Code.Funs

/-!
# Specifications of `Aegis.SortEvenOdd.sort_even_odd`

LeetCode problem `sort-even-and-odd-indices-independently`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.SortEvenOdd

  def getI (xs : List Aeneas.Std.I64) (i : Nat) : Int :=
    match xs[i]? with
    | some x => x.val
    | none => 0

  def countEvenEq (xs : List Aeneas.Std.I64) (n : Nat) (v : Int) : Nat :=
    ((List.range n).filter (fun i => (i % 2 == 0) && (getI xs i == v))).length

  def countOddEq (xs : List Aeneas.Std.I64) (n : Nat) (v : Int) : Nat :=
    ((List.range n).filter (fun i => (i % 2 == 1) && (getI xs i == v))).length

  def countAllEq (xs : List Aeneas.Std.I64) (n : Nat) (v : Int) : Nat :=
    ((List.range n).filter (fun i => getI xs i == v)).length

  def listMin : List Int → Int
    | [] => 0
    | x :: xs => xs.foldl min x

  def listMax : List Int → Int
    | [] => 0
    | x :: xs => xs.foldl max x

  def minEven (xs : List Aeneas.Std.I64) (n : Nat) : Int :=
    listMin (((List.range n).filter (fun j => j % 2 == 0)).map (fun j => getI xs j))

  def maxOdd (xs : List Aeneas.Std.I64) (n : Nat) : Int :=
    listMax (((List.range n).filter (fun j => j % 2 == 1)).map (fun j => getI xs j))

  /-- Whenever the function returns a result r, let n = len(nums). Then len(r) = n, and all of the following hold: (a) for every i and j with 0 <= i < j < n, if i and j are both even then r[i] <= r[j]; (b) for every i and j with 0 <= i < j < n, if i and j are both odd then r[i] >= r[j]; (c) for every integer v, the number of even i with 0 <= i < n and r[i] = v equals the number of even i with 0 <= i < n and nums[i] = v; (d) for every integer v, the number of odd i with 0 <= i < n and r[i] = v equals the number of odd i with 0 <= i < n and nums[i] = v.
    Preconditions: len(nums) >= 1, len(nums) <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_1 (nums : Aeneas.Std.Slice Aeneas.Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
      (hrange : ∀ i, i < nums.val.length → 1 ≤ getI nums.val i ∧ getI nums.val i ≤ 100) :
      ∀ r, Aegis.SortEvenOdd.sort_even_odd nums = ok r →
        r.val.length = nums.val.length ∧
        (∀ i j, i < j → j < nums.val.length → i % 2 = 0 → j % 2 = 0 →
          getI r.val i ≤ getI r.val j) ∧
        (∀ i j, i < j → j < nums.val.length → i % 2 = 1 → j % 2 = 1 →
          getI r.val i ≥ getI r.val j) ∧
        (∀ v : Int, countEvenEq r.val nums.val.length v =
          countEvenEq nums.val nums.val.length v) ∧
        (∀ v : Int, countOddEq r.val nums.val.length v =
          countOddEq nums.val nums.val.length v) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Aeneas.Std.Slice Aeneas.Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
        (hrange : ∀ i, i < nums.val.length → 1 ≤ getI nums.val i ∧ getI nums.val i ≤ 100), ∀ r, Aegis.SortEvenOdd.sort_even_odd nums = ok r →
          r.val.length = nums.val.length ∧
          (∀ i j, i < j → j < nums.val.length → i % 2 = 0 → j % 2 = 0 →
            getI r.val i ≤ getI r.val j) ∧
          (∀ i j, i < j → j < nums.val.length → i % 2 = 1 → j % 2 = 1 →
            getI r.val i ≥ getI r.val j) ∧
          (∀ v : Int, countEvenEq r.val nums.val.length v =
            countEvenEq nums.val nums.val.length v) ∧
          (∀ v : Int, countOddEq r.val nums.val.length v =
            countOddEq nums.val nums.val.length v)) := by
    sorry

  /-- Whenever the function returns a result r, len(r) = len(nums).
    Preconditions: len(nums) >= 1, len(nums) <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_2 (nums : Aeneas.Std.Slice Aeneas.Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
      (hrange : ∀ i, i < nums.val.length → 1 ≤ getI nums.val i ∧ getI nums.val i ≤ 100) :
      ∀ r, Aegis.SortEvenOdd.sort_even_odd nums = ok r →
        r.val.length = nums.val.length := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Aeneas.Std.Slice Aeneas.Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
        (hrange : ∀ i, i < nums.val.length → 1 ≤ getI nums.val i ∧ getI nums.val i ≤ 100), ∀ r, Aegis.SortEvenOdd.sort_even_odd nums = ok r →
          r.val.length = nums.val.length) := by
    sorry

  /-- Whenever the function returns a result r, for every i and j with 0 <= i < j < len(nums), if i and j are both even then r[i] <= r[j].
    Preconditions: len(nums) >= 1, len(nums) <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_3 (nums : Aeneas.Std.Slice Aeneas.Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
      (hrange : ∀ i, i < nums.val.length → 1 ≤ getI nums.val i ∧ getI nums.val i ≤ 100) :
      ∀ r, Aegis.SortEvenOdd.sort_even_odd nums = ok r →
        ∀ i j, i < j → j < nums.val.length → i % 2 = 0 → j % 2 = 0 →
          getI r.val i ≤ getI r.val j := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Aeneas.Std.Slice Aeneas.Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
        (hrange : ∀ i, i < nums.val.length → 1 ≤ getI nums.val i ∧ getI nums.val i ≤ 100), ∀ r, Aegis.SortEvenOdd.sort_even_odd nums = ok r →
          ∀ i j, i < j → j < nums.val.length → i % 2 = 0 → j % 2 = 0 →
            getI r.val i ≤ getI r.val j) := by
    sorry

  /-- Whenever the function returns a result r, for every i and j with 0 <= i < j < len(nums), if i and j are both odd then r[i] >= r[j].
    Preconditions: len(nums) >= 1, len(nums) <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_4 (nums : Aeneas.Std.Slice Aeneas.Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
      (hrange : ∀ i, i < nums.val.length → 1 ≤ getI nums.val i ∧ getI nums.val i ≤ 100) :
      ∀ r, Aegis.SortEvenOdd.sort_even_odd nums = ok r →
        ∀ i j, i < j → j < nums.val.length → i % 2 = 1 → j % 2 = 1 →
          getI r.val i ≥ getI r.val j := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Aeneas.Std.Slice Aeneas.Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
        (hrange : ∀ i, i < nums.val.length → 1 ≤ getI nums.val i ∧ getI nums.val i ≤ 100), ∀ r, Aegis.SortEvenOdd.sort_even_odd nums = ok r →
          ∀ i j, i < j → j < nums.val.length → i % 2 = 1 → j % 2 = 1 →
            getI r.val i ≥ getI r.val j) := by
    sorry

  /-- Whenever the function returns a result r, for every integer v, the number of even indices i with 0 <= i < len(nums) and r[i] = v equals the number of even indices i with 0 <= i < len(nums) and nums[i] = v.
    Preconditions: len(nums) >= 1, len(nums) <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_5 (nums : Aeneas.Std.Slice Aeneas.Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
      (hrange : ∀ i, i < nums.val.length → 1 ≤ getI nums.val i ∧ getI nums.val i ≤ 100) :
      ∀ r, Aegis.SortEvenOdd.sort_even_odd nums = ok r →
        ∀ v : Int, countEvenEq r.val nums.val.length v =
          countEvenEq nums.val nums.val.length v := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Aeneas.Std.Slice Aeneas.Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
        (hrange : ∀ i, i < nums.val.length → 1 ≤ getI nums.val i ∧ getI nums.val i ≤ 100), ∀ r, Aegis.SortEvenOdd.sort_even_odd nums = ok r →
          ∀ v : Int, countEvenEq r.val nums.val.length v =
            countEvenEq nums.val nums.val.length v) := by
    sorry

  /-- Whenever the function returns a result r, for every integer v, the number of odd indices i with 0 <= i < len(nums) and r[i] = v equals the number of odd indices i with 0 <= i < len(nums) and nums[i] = v.
    Preconditions: len(nums) >= 1, len(nums) <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_6 (nums : Aeneas.Std.Slice Aeneas.Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
      (hrange : ∀ i, i < nums.val.length → 1 ≤ getI nums.val i ∧ getI nums.val i ≤ 100) :
      ∀ r, Aegis.SortEvenOdd.sort_even_odd nums = ok r →
        ∀ v : Int, countOddEq r.val nums.val.length v =
          countOddEq nums.val nums.val.length v := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Aeneas.Std.Slice Aeneas.Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
        (hrange : ∀ i, i < nums.val.length → 1 ≤ getI nums.val i ∧ getI nums.val i ≤ 100), ∀ r, Aegis.SortEvenOdd.sort_even_odd nums = ok r →
          ∀ v : Int, countOddEq r.val nums.val.length v =
            countOddEq nums.val nums.val.length v) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(r), 1 <= r[i] <= 100.
    Preconditions: len(nums) >= 1, len(nums) <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_7 (nums : Aeneas.Std.Slice Aeneas.Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
      (hrange : ∀ i, i < nums.val.length → 1 ≤ getI nums.val i ∧ getI nums.val i ≤ 100) :
      ∀ r, Aegis.SortEvenOdd.sort_even_odd nums = ok r →
        ∀ i, i < r.val.length → 1 ≤ getI r.val i ∧ getI r.val i ≤ 100 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Aeneas.Std.Slice Aeneas.Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
        (hrange : ∀ i, i < nums.val.length → 1 ≤ getI nums.val i ∧ getI nums.val i ≤ 100), ∀ r, Aegis.SortEvenOdd.sort_even_odd nums = ok r →
          ∀ i, i < r.val.length → 1 ≤ getI r.val i ∧ getI r.val i ≤ 100) := by
    sorry

  /-- Whenever the function returns a result r, if len(nums) <= 2 then for every i with 0 <= i < len(r), r[i] = nums[i].
    Preconditions: len(nums) >= 1, len(nums) <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_8 (nums : Aeneas.Std.Slice Aeneas.Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
      (hrange : ∀ i, i < nums.val.length → 1 ≤ getI nums.val i ∧ getI nums.val i ≤ 100) :
      ∀ r, Aegis.SortEvenOdd.sort_even_odd nums = ok r →
        nums.val.length ≤ 2 → ∀ i, i < r.val.length → getI r.val i = getI nums.val i := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Aeneas.Std.Slice Aeneas.Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
        (hrange : ∀ i, i < nums.val.length → 1 ≤ getI nums.val i ∧ getI nums.val i ≤ 100), ∀ r, Aegis.SortEvenOdd.sort_even_odd nums = ok r →
          nums.val.length ≤ 2 → ∀ i, i < r.val.length → getI r.val i = getI nums.val i) := by
    sorry

  /-- The function returns a result r for every input satisfying the preconditions; it does not fail, panic, overflow, or access out of bounds.
    Preconditions: len(nums) >= 1, len(nums) <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_9 (nums : Aeneas.Std.Slice Aeneas.Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
      (hrange : ∀ i, i < nums.val.length → 1 ≤ getI nums.val i ∧ getI nums.val i ≤ 100) :
      ∃ r, Aegis.SortEvenOdd.sort_even_odd nums = ok r := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Aeneas.Std.Slice Aeneas.Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
        (hrange : ∀ i, i < nums.val.length → 1 ≤ getI nums.val i ∧ getI nums.val i ≤ 100), ∃ r, Aegis.SortEvenOdd.sort_even_odd nums = ok r) := by
    sorry

  /-- Whenever the function returns a result r, for every integer v, the number of indices i with 0 <= i < len(nums) and r[i] = v equals the number of indices i with 0 <= i < len(nums) and nums[i] = v.
    Preconditions: len(nums) >= 1, len(nums) <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_10 (nums : Aeneas.Std.Slice Aeneas.Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
      (hrange : ∀ i, i < nums.val.length → 1 ≤ getI nums.val i ∧ getI nums.val i ≤ 100) :
      ∀ r, Aegis.SortEvenOdd.sort_even_odd nums = ok r →
        ∀ v : Int, countAllEq r.val nums.val.length v =
          countAllEq nums.val nums.val.length v := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Aeneas.Std.Slice Aeneas.Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
        (hrange : ∀ i, i < nums.val.length → 1 ≤ getI nums.val i ∧ getI nums.val i ≤ 100), ∀ r, Aegis.SortEvenOdd.sort_even_odd nums = ok r →
          ∀ v : Int, countAllEq r.val nums.val.length v =
            countAllEq nums.val nums.val.length v) := by
    sorry

  /-- Whenever the function returns a result r, r[0] = min { nums[j] | 0 <= j < len(nums) and j is even }.
    Preconditions: len(nums) >= 1, len(nums) <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_11 (nums : Aeneas.Std.Slice Aeneas.Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
      (hrange : ∀ i, i < nums.val.length → 1 ≤ getI nums.val i ∧ getI nums.val i ≤ 100) :
      ∀ r, Aegis.SortEvenOdd.sort_even_odd nums = ok r →
        getI r.val 0 = minEven nums.val nums.val.length := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Aeneas.Std.Slice Aeneas.Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
        (hrange : ∀ i, i < nums.val.length → 1 ≤ getI nums.val i ∧ getI nums.val i ≤ 100), ∀ r, Aegis.SortEvenOdd.sort_even_odd nums = ok r →
          getI r.val 0 = minEven nums.val nums.val.length) := by
    sorry

  /-- Whenever the function returns a result r, if len(nums) >= 2 then r[1] = max { nums[j] | 0 <= j < len(nums) and j is odd }.
    Preconditions: len(nums) >= 1, len(nums) <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_12 (nums : Aeneas.Std.Slice Aeneas.Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
      (hrange : ∀ i, i < nums.val.length → 1 ≤ getI nums.val i ∧ getI nums.val i ≤ 100) :
      ∀ r, Aegis.SortEvenOdd.sort_even_odd nums = ok r →
        2 ≤ nums.val.length → getI r.val 1 = maxOdd nums.val nums.val.length := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Aeneas.Std.Slice Aeneas.Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
        (hrange : ∀ i, i < nums.val.length → 1 ≤ getI nums.val i ∧ getI nums.val i ≤ 100), ∀ r, Aegis.SortEvenOdd.sort_even_odd nums = ok r →
          2 ≤ nums.val.length → getI r.val 1 = maxOdd nums.val nums.val.length) := by
    sorry

  end AegisSpec.SortEvenOdd
