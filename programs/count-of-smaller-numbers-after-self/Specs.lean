import Aegis.CountSmaller.Code.Funs

/-!
# Specifications of `Aegis.CountSmaller.count_smaller`

LeetCode problem `count-of-smaller-numbers-after-self`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.CountSmaller

  def valAt (l : List Std.I64) (j : Nat) : Int :=
    match l[j]? with
    | some v => v.val
    | none => 0

  def numSmallerAfter (l : List Std.I64) (i : Nat) : Nat :=
    ((List.range l.length).filter
      (fun j => decide (i < j ∧ valAt l j < valAt l i))).length

  def inversionCount (l : List Std.I64) : Nat :=
    (((List.range l.length).product (List.range l.length)).filter
      (fun p => decide (p.1 < p.2 ∧ valAt l p.2 < valAt l p.1))).length

  def occurrencesAfter (l : List Std.I64) (i : Nat) (v : Int) : Nat :=
    ((List.range l.length).filter
      (fun j => decide (i < j ∧ valAt l j = v))).length

  /-- Whenever count_smaller returns a result r, len(r) = n and, for every i with 0 <= i < n, r[i] is the number of indices j such that i < j < n and nums[j] < nums[i].
    Preconditions: Let n = len(nums). The preconditions are 1 <= n <= 100000 and, for every i with 0 <= i < n, -10000 <= nums[i] <= 10000. -/
  theorem spec_1 (nums : Slice Std.I64)
      (hne : 1 ≤ nums.val.length)
      (hle : nums.val.length ≤ 100000)
      (hvals : ∀ (i : Nat), i < nums.val.length → -10000 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 10000)
      (r : alloc.vec.Vec Std.I64) (hr : Aegis.CountSmaller.count_smaller nums = ok r) :
      r.val.length = nums.val.length ∧
        ∀ (i : Nat), i < nums.val.length →
          valAt r.val i = (numSmallerAfter nums.val i : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hne : 1 ≤ nums.val.length)
        (hle : nums.val.length ≤ 100000)
        (hvals : ∀ (i : Nat), i < nums.val.length → -10000 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 10000)
        (r : alloc.vec.Vec Std.I64) (hr : Aegis.CountSmaller.count_smaller nums = ok r), r.val.length = nums.val.length ∧
          ∀ (i : Nat), i < nums.val.length →
            valAt r.val i = (numSmallerAfter nums.val i : Int)) := by
    sorry

  /-- For every slice nums satisfying the preconditions, count_smaller returns a result r; it does not fail, panic, or overflow.
    Preconditions: Let n = len(nums). The preconditions are 1 <= n <= 100000 and, for every i with 0 <= i < n, -10000 <= nums[i] <= 10000. -/
  theorem spec_2 (nums : Slice Std.I64)
      (hne : 1 ≤ nums.val.length)
      (hle : nums.val.length ≤ 100000)
      (hvals : ∀ (i : Nat), i < nums.val.length → -10000 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 10000) :
      ∃ r : alloc.vec.Vec Std.I64, Aegis.CountSmaller.count_smaller nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hne : 1 ≤ nums.val.length)
        (hle : nums.val.length ≤ 100000)
        (hvals : ∀ (i : Nat), i < nums.val.length → -10000 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 10000), ∃ r : alloc.vec.Vec Std.I64, Aegis.CountSmaller.count_smaller nums = ok r) := by
    sorry

  /-- Whenever count_smaller returns a result r, len(r) = len(nums).
    Preconditions: Let n = len(nums). The preconditions are 1 <= n <= 100000 and, for every i with 0 <= i < n, -10000 <= nums[i] <= 10000. -/
  theorem spec_3 (nums : Slice Std.I64)
      (hne : 1 ≤ nums.val.length)
      (hle : nums.val.length ≤ 100000)
      (hvals : ∀ (i : Nat), i < nums.val.length → -10000 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 10000)
      (r : alloc.vec.Vec Std.I64) (hr : Aegis.CountSmaller.count_smaller nums = ok r) :
      r.val.length = nums.val.length := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hne : 1 ≤ nums.val.length)
        (hle : nums.val.length ≤ 100000)
        (hvals : ∀ (i : Nat), i < nums.val.length → -10000 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 10000)
        (r : alloc.vec.Vec Std.I64) (hr : Aegis.CountSmaller.count_smaller nums = ok r), r.val.length = nums.val.length) := by
    sorry

  /-- Whenever count_smaller returns a result r, for every i with 0 <= i < n, 0 <= r[i].
    Preconditions: Let n = len(nums). The preconditions are 1 <= n <= 100000 and, for every i with 0 <= i < n, -10000 <= nums[i] <= 10000. -/
  theorem spec_4 (nums : Slice Std.I64)
      (hne : 1 ≤ nums.val.length)
      (hle : nums.val.length ≤ 100000)
      (hvals : ∀ (i : Nat), i < nums.val.length → -10000 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 10000)
      (r : alloc.vec.Vec Std.I64) (hr : Aegis.CountSmaller.count_smaller nums = ok r) :
      ∀ (i : Nat), i < nums.val.length → 0 ≤ valAt r.val i := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hne : 1 ≤ nums.val.length)
        (hle : nums.val.length ≤ 100000)
        (hvals : ∀ (i : Nat), i < nums.val.length → -10000 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 10000)
        (r : alloc.vec.Vec Std.I64) (hr : Aegis.CountSmaller.count_smaller nums = ok r), ∀ (i : Nat), i < nums.val.length → 0 ≤ valAt r.val i) := by
    sorry

  /-- Whenever count_smaller returns a result r, for every i with 0 <= i < n, r[i] <= n - 1 - i.
    Preconditions: Let n = len(nums). The preconditions are 1 <= n <= 100000 and, for every i with 0 <= i < n, -10000 <= nums[i] <= 10000. -/
  theorem spec_5 (nums : Slice Std.I64)
      (hne : 1 ≤ nums.val.length)
      (hle : nums.val.length ≤ 100000)
      (hvals : ∀ (i : Nat), i < nums.val.length → -10000 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 10000)
      (r : alloc.vec.Vec Std.I64) (hr : Aegis.CountSmaller.count_smaller nums = ok r) :
      ∀ (i : Nat), i < nums.val.length →
        valAt r.val i ≤ (nums.val.length : Int) - 1 - (i : Int) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hne : 1 ≤ nums.val.length)
        (hle : nums.val.length ≤ 100000)
        (hvals : ∀ (i : Nat), i < nums.val.length → -10000 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 10000)
        (r : alloc.vec.Vec Std.I64) (hr : Aegis.CountSmaller.count_smaller nums = ok r), ∀ (i : Nat), i < nums.val.length →
          valAt r.val i ≤ (nums.val.length : Int) - 1 - (i : Int)) := by
    sorry

  /-- Whenever count_smaller returns a result r, the sum of r[0], r[1], ..., r[n - 1] equals the number of pairs (i, j) such that 0 <= i < j < n and nums[j] < nums[i].
    Preconditions: Let n = len(nums). The preconditions are 1 <= n <= 100000 and, for every i with 0 <= i < n, -10000 <= nums[i] <= 10000. -/
  theorem spec_6 (nums : Slice Std.I64)
      (hne : 1 ≤ nums.val.length)
      (hle : nums.val.length ≤ 100000)
      (hvals : ∀ (i : Nat), i < nums.val.length → -10000 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 10000)
      (r : alloc.vec.Vec Std.I64) (hr : Aegis.CountSmaller.count_smaller nums = ok r) :
      ((List.range nums.val.length).map (fun i => valAt r.val i)).sum
        = (inversionCount nums.val : Int) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hne : 1 ≤ nums.val.length)
        (hle : nums.val.length ≤ 100000)
        (hvals : ∀ (i : Nat), i < nums.val.length → -10000 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 10000)
        (r : alloc.vec.Vec Std.I64) (hr : Aegis.CountSmaller.count_smaller nums = ok r), ((List.range nums.val.length).map (fun i => valAt r.val i)).sum
          = (inversionCount nums.val : Int)) := by
    sorry

  /-- Whenever count_smaller returns a result r, for every i with 0 <= i < n - 1, if nums[i] <= nums[i + 1], then r[i] <= r[i + 1].
    Preconditions: Let n = len(nums). The preconditions are 1 <= n <= 100000 and, for every i with 0 <= i < n, -10000 <= nums[i] <= 10000. -/
  theorem spec_7 (nums : Slice Std.I64)
      (hne : 1 ≤ nums.val.length)
      (hle : nums.val.length ≤ 100000)
      (hvals : ∀ (i : Nat), i < nums.val.length → -10000 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 10000)
      (r : alloc.vec.Vec Std.I64) (hr : Aegis.CountSmaller.count_smaller nums = ok r) :
      ∀ (i : Nat), i + 1 < nums.val.length →
        valAt nums.val i ≤ valAt nums.val (i + 1) →
        valAt r.val i ≤ valAt r.val (i + 1) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hne : 1 ≤ nums.val.length)
        (hle : nums.val.length ≤ 100000)
        (hvals : ∀ (i : Nat), i < nums.val.length → -10000 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 10000)
        (r : alloc.vec.Vec Std.I64) (hr : Aegis.CountSmaller.count_smaller nums = ok r), ∀ (i : Nat), i + 1 < nums.val.length →
          valAt nums.val i ≤ valAt nums.val (i + 1) →
          valAt r.val i ≤ valAt r.val (i + 1)) := by
    sorry

  /-- Whenever count_smaller returns a result r, for every i and j with 0 <= i < j < n and nums[i] > nums[j], r[i] >= r[j] + 1.
    Preconditions: Let n = len(nums). The preconditions are 1 <= n <= 100000 and, for every i with 0 <= i < n, -10000 <= nums[i] <= 10000. -/
  theorem spec_8 (nums : Slice Std.I64)
      (hne : 1 ≤ nums.val.length)
      (hle : nums.val.length ≤ 100000)
      (hvals : ∀ (i : Nat), i < nums.val.length → -10000 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 10000)
      (r : alloc.vec.Vec Std.I64) (hr : Aegis.CountSmaller.count_smaller nums = ok r) :
      ∀ (i j : Nat), i < j → j < nums.val.length →
        valAt nums.val j < valAt nums.val i →
        valAt r.val i ≥ valAt r.val j + 1 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hne : 1 ≤ nums.val.length)
        (hle : nums.val.length ≤ 100000)
        (hvals : ∀ (i : Nat), i < nums.val.length → -10000 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 10000)
        (r : alloc.vec.Vec Std.I64) (hr : Aegis.CountSmaller.count_smaller nums = ok r), ∀ (i j : Nat), i < j → j < nums.val.length →
          valAt nums.val j < valAt nums.val i →
          valAt r.val i ≥ valAt r.val j + 1) := by
    sorry

  /-- Whenever count_smaller returns a result r, for every i with 0 <= i < n and every integer v with v < nums[i], r[i] is at least the number of indices j such that i < j < n and nums[j] = v.
    Preconditions: Let n = len(nums). The preconditions are 1 <= n <= 100000 and, for every i with 0 <= i < n, -10000 <= nums[i] <= 10000. -/
  theorem spec_9 (nums : Slice Std.I64)
      (hne : 1 ≤ nums.val.length)
      (hle : nums.val.length ≤ 100000)
      (hvals : ∀ (i : Nat), i < nums.val.length → -10000 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 10000)
      (r : alloc.vec.Vec Std.I64) (hr : Aegis.CountSmaller.count_smaller nums = ok r) :
      ∀ (i : Nat), i < nums.val.length → ∀ (v : Int), v < valAt nums.val i →
        (occurrencesAfter nums.val i v : Int) ≤ valAt r.val i := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hne : 1 ≤ nums.val.length)
        (hle : nums.val.length ≤ 100000)
        (hvals : ∀ (i : Nat), i < nums.val.length → -10000 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 10000)
        (r : alloc.vec.Vec Std.I64) (hr : Aegis.CountSmaller.count_smaller nums = ok r), ∀ (i : Nat), i < nums.val.length → ∀ (v : Int), v < valAt nums.val i →
          (occurrencesAfter nums.val i v : Int) ≤ valAt r.val i) := by
    sorry

  /-- Whenever count_smaller returns a result r, for every i with 0 <= i < n - 1, if nums[i] = nums[i + 1], then r[i] = r[i + 1].
    Preconditions: Let n = len(nums). The preconditions are 1 <= n <= 100000 and, for every i with 0 <= i < n, -10000 <= nums[i] <= 10000. -/
  theorem spec_10 (nums : Slice Std.I64)
      (hne : 1 ≤ nums.val.length)
      (hle : nums.val.length ≤ 100000)
      (hvals : ∀ (i : Nat), i < nums.val.length → -10000 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 10000)
      (r : alloc.vec.Vec Std.I64) (hr : Aegis.CountSmaller.count_smaller nums = ok r) :
      ∀ (i : Nat), i + 1 < nums.val.length →
        valAt nums.val i = valAt nums.val (i + 1) →
        valAt r.val i = valAt r.val (i + 1) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hne : 1 ≤ nums.val.length)
        (hle : nums.val.length ≤ 100000)
        (hvals : ∀ (i : Nat), i < nums.val.length → -10000 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 10000)
        (r : alloc.vec.Vec Std.I64) (hr : Aegis.CountSmaller.count_smaller nums = ok r), ∀ (i : Nat), i + 1 < nums.val.length →
          valAt nums.val i = valAt nums.val (i + 1) →
          valAt r.val i = valAt r.val (i + 1)) := by
    sorry

  end AegisSpec.CountSmaller
