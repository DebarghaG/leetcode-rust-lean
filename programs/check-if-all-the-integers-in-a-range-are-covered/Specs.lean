import Aegis.IsCovered.Code.Funs

/-!
# Specifications of `Aegis.IsCovered.is_covered`

LeetCode problem `check-if-all-the-integers-in-a-range-are-covered`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.IsCovered

  namespace AegisSpec.IsCovered

  def rowInts (row : alloc.vec.Vec Std.I64) : List Int := row.val.map (fun v => v.val)

  def IsIntervalAt (ranges : Slice (alloc.vec.Vec Std.I64)) (i : Nat) (s e : Int) : Prop :=
    ∃ row : alloc.vec.Vec Std.I64, ranges.val[i]? = some row ∧ rowInts row = [s, e]

  def RowsWellFormed (ranges : Slice (alloc.vec.Vec Std.I64)) : Prop :=
    1 ≤ ranges.val.length ∧ ranges.val.length ≤ 50 ∧
      ∀ i, i < ranges.val.length → ∃ s e : Int, IsIntervalAt ranges i s e ∧ 1 ≤ s ∧ s ≤ e ∧ e ≤ 50

  def BoundsWellFormed (left right : Std.I64) : Prop :=
    1 ≤ left.val ∧ left.val ≤ right.val ∧ right.val ≤ 50

  def CoversPoint (ranges : Slice (alloc.vec.Vec Std.I64)) (i : Nat) (x : Int) : Prop :=
    ∃ s e : Int, IsIntervalAt ranges i s e ∧ s ≤ x ∧ x ≤ e

  def CoversInterval (ranges : Slice (alloc.vec.Vec Std.I64)) (i : Nat) (l r : Int) : Prop :=
    ∃ s e : Int, IsIntervalAt ranges i s e ∧ s ≤ l ∧ r ≤ e

  def Covered (ranges : Slice (alloc.vec.Vec Std.I64)) (left right : Std.I64) : Prop :=
    ∀ x : Int, left.val ≤ x → x ≤ right.val →
      ∃ i, i < ranges.val.length ∧ CoversPoint ranges i x

  /-- The function returns a result r, and r is true if and only if for every integer x with left <= x <= right, there exists an index i with 0 <= i < len(ranges) such that start_i <= x <= end_i. Here start_i and end_i are the two entries of ranges[i], and intervals are inclusive.
    Preconditions: Write len(ranges) for the number of intervals and, for each index i with 0 <= i < len(ranges), write ranges[i] = [start_i, end_i]. Preconditions: 1 <= len(ranges) <= 50; for every i with 0 <= i < len(ranges), ranges[i] has length exactly 2 and 1 <= start_i <= end_i <= 50; and 1 <= left <= right <= 50. -/
  theorem spec_1 (ranges : Slice (alloc.vec.Vec Std.I64)) (left right : Std.I64)
      (hR : RowsWellFormed ranges) (hB : BoundsWellFormed left right) :
      ∃ r : Bool, is_covered ranges left right = ok r ∧ (r = true ↔ Covered ranges left right) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (ranges : Slice (alloc.vec.Vec Std.I64)) (left right : Std.I64)
        (hR : RowsWellFormed ranges) (hB : BoundsWellFormed left right), ∃ r : Bool, is_covered ranges left right = ok r ∧ (r = true ↔ Covered ranges left right)) := by
    sorry

  /-- The function returns a result r and does not fail: it does not return an error, panic, or out-of-bounds/overflow failure for any input satisfying the preconditions.
    Preconditions: Write len(ranges) for the number of intervals and, for each index i with 0 <= i < len(ranges), write ranges[i] = [start_i, end_i]. Preconditions: 1 <= len(ranges) <= 50; for every i with 0 <= i < len(ranges), ranges[i] has length exactly 2 and 1 <= start_i <= end_i <= 50; and 1 <= left <= right <= 50. -/
  theorem spec_2 (ranges : Slice (alloc.vec.Vec Std.I64)) (left right : Std.I64)
      (hR : RowsWellFormed ranges) (hB : BoundsWellFormed left right) :
      ∃ r : Bool, is_covered ranges left right = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (ranges : Slice (alloc.vec.Vec Std.I64)) (left right : Std.I64)
        (hR : RowsWellFormed ranges) (hB : BoundsWellFormed left right), ∃ r : Bool, is_covered ranges left right = ok r) := by
    sorry

  /-- Whenever the function returns false, there exists an integer x with left <= x <= right such that for every index i with 0 <= i < len(ranges), either x < start_i or x > end_i. In other words, a false answer always has a witness x in [left, right] that is not covered by any interval.
    Preconditions: Write len(ranges) for the number of intervals and, for each index i with 0 <= i < len(ranges), write ranges[i] = [start_i, end_i]. Preconditions: 1 <= len(ranges) <= 50; for every i with 0 <= i < len(ranges), ranges[i] has length exactly 2 and 1 <= start_i <= end_i <= 50; and 1 <= left <= right <= 50. -/
  theorem spec_3 (ranges : Slice (alloc.vec.Vec Std.I64)) (left right : Std.I64)
      (hR : RowsWellFormed ranges) (hB : BoundsWellFormed left right)
      (h : is_covered ranges left right = ok false) :
      ∃ x : Int, left.val ≤ x ∧ x ≤ right.val ∧
        ∀ i, i < ranges.val.length → ∀ s e : Int, IsIntervalAt ranges i s e → (x < s ∨ e < x) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (ranges : Slice (alloc.vec.Vec Std.I64)) (left right : Std.I64)
        (hR : RowsWellFormed ranges) (hB : BoundsWellFormed left right)
        (h : is_covered ranges left right = ok false), ∃ x : Int, left.val ≤ x ∧ x ≤ right.val ∧
          ∀ i, i < ranges.val.length → ∀ s e : Int, IsIntervalAt ranges i s e → (x < s ∨ e < x)) := by
    sorry

  /-- If there exists an index i with 0 <= i < len(ranges) such that start_i <= left and right <= end_i, then the function returns true.
    Preconditions: Write len(ranges) for the number of intervals and, for each index i with 0 <= i < len(ranges), write ranges[i] = [start_i, end_i]. Preconditions: 1 <= len(ranges) <= 50; for every i with 0 <= i < len(ranges), ranges[i] has length exactly 2 and 1 <= start_i <= end_i <= 50; and 1 <= left <= right <= 50. -/
  theorem spec_4 (ranges : Slice (alloc.vec.Vec Std.I64)) (left right : Std.I64)
      (hR : RowsWellFormed ranges) (hB : BoundsWellFormed left right)
      (h : ∃ i, i < ranges.val.length ∧ CoversInterval ranges i left.val right.val) :
      is_covered ranges left right = ok true := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (ranges : Slice (alloc.vec.Vec Std.I64)) (left right : Std.I64)
        (hR : RowsWellFormed ranges) (hB : BoundsWellFormed left right)
        (h : ∃ i, i < ranges.val.length ∧ CoversInterval ranges i left.val right.val), is_covered ranges left right = ok true) := by
    sorry

  /-- If for every index i with 0 <= i < len(ranges), either end_i < left or start_i > right, then the function returns false.
    Preconditions: Write len(ranges) for the number of intervals and, for each index i with 0 <= i < len(ranges), write ranges[i] = [start_i, end_i]. Preconditions: 1 <= len(ranges) <= 50; for every i with 0 <= i < len(ranges), ranges[i] has length exactly 2 and 1 <= start_i <= end_i <= 50; and 1 <= left <= right <= 50. -/
  theorem spec_5 (ranges : Slice (alloc.vec.Vec Std.I64)) (left right : Std.I64)
      (hR : RowsWellFormed ranges) (hB : BoundsWellFormed left right)
      (h : ∀ i, i < ranges.val.length → ∀ s e : Int, IsIntervalAt ranges i s e →
        (e < left.val ∨ s > right.val)) :
      is_covered ranges left right = ok false := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (ranges : Slice (alloc.vec.Vec Std.I64)) (left right : Std.I64)
        (hR : RowsWellFormed ranges) (hB : BoundsWellFormed left right)
        (h : ∀ i, i < ranges.val.length → ∀ s e : Int, IsIntervalAt ranges i s e →
          (e < left.val ∨ s > right.val)), is_covered ranges left right = ok false) := by
    sorry

  /-- For any array ranges' that is a permutation of ranges and satisfies the same interval constraints, if the function returns Boolean r on ranges with parameters left, right and returns Boolean r' on ranges' with the same left, right, then r = r'.
    Preconditions: Write len(ranges) for the number of intervals and, for each index i with 0 <= i < len(ranges), write ranges[i] = [start_i, end_i]. Preconditions: 1 <= len(ranges) <= 50; for every i with 0 <= i < len(ranges), ranges[i] has length exactly 2 and 1 <= start_i <= end_i <= 50; and 1 <= left <= right <= 50. -/
  theorem spec_6 (ranges ranges' : Slice (alloc.vec.Vec Std.I64)) (left right : Std.I64)
      (hR : RowsWellFormed ranges) (hB : BoundsWellFormed left right)
      (hR' : RowsWellFormed ranges')
      (hperm : ranges.val.Perm ranges'.val)
      (r r' : Bool) (h : is_covered ranges left right = ok r)
      (h' : is_covered ranges' left right = ok r') :
      r = r' := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (ranges ranges' : Slice (alloc.vec.Vec Std.I64)) (left right : Std.I64)
        (hR : RowsWellFormed ranges) (hB : BoundsWellFormed left right)
        (hR' : RowsWellFormed ranges')
        (hperm : ranges.val.Perm ranges'.val)
        (r r' : Bool) (h : is_covered ranges left right = ok r)
        (h' : is_covered ranges' left right = ok r'), r = r') := by
    sorry

  /-- For any index i with 0 <= i < len(ranges) such that end_i < left or start_i > right, if ranges_without_i is obtained by deleting entry i from ranges and still satisfies 1 <= len(ranges_without_i) <= 50 and all interval constraints, then whenever the function returns Boolean r on ranges and Boolean r' on ranges_without_i with the same left, right, we have r = r'.
    Preconditions: Write len(ranges) for the number of intervals and, for each index i with 0 <= i < len(ranges), write ranges[i] = [start_i, end_i]. Preconditions: 1 <= len(ranges) <= 50; for every i with 0 <= i < len(ranges), ranges[i] has length exactly 2 and 1 <= start_i <= end_i <= 50; and 1 <= left <= right <= 50. -/
  theorem spec_7 (ranges ranges_without_i : Slice (alloc.vec.Vec Std.I64))
      (left right : Std.I64)
      (hR : RowsWellFormed ranges) (hB : BoundsWellFormed left right)
      (i : Nat) (hi : i < ranges.val.length)
      (hdisj : ∀ s e : Int, IsIntervalAt ranges i s e → (e < left.val ∨ s > right.val))
      (hdel : ranges_without_i.val = ranges.val.eraseIdx i)
      (hRw : RowsWellFormed ranges_without_i)
      (r r' : Bool) (h : is_covered ranges left right = ok r)
      (h' : is_covered ranges_without_i left right = ok r') :
      r = r' := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (ranges ranges_without_i : Slice (alloc.vec.Vec Std.I64))
        (left right : Std.I64)
        (hR : RowsWellFormed ranges) (hB : BoundsWellFormed left right)
        (i : Nat) (hi : i < ranges.val.length)
        (hdisj : ∀ s e : Int, IsIntervalAt ranges i s e → (e < left.val ∨ s > right.val))
        (hdel : ranges_without_i.val = ranges.val.eraseIdx i)
        (hRw : RowsWellFormed ranges_without_i)
        (r r' : Bool) (h : is_covered ranges left right = ok r)
        (h' : is_covered ranges_without_i left right = ok r'), r = r') := by
    sorry

  /-- If the function returns true on ranges with parameters left, right, then for any array ranges' obtained by appending one or more intervals [s, e] with 1 <= s <= e <= 50 and with len(ranges') <= 50, the function returns true on ranges' with the same left, right.
    Preconditions: Write len(ranges) for the number of intervals and, for each index i with 0 <= i < len(ranges), write ranges[i] = [start_i, end_i]. Preconditions: 1 <= len(ranges) <= 50; for every i with 0 <= i < len(ranges), ranges[i] has length exactly 2 and 1 <= start_i <= end_i <= 50; and 1 <= left <= right <= 50. -/
  theorem spec_8 (ranges ranges' : Slice (alloc.vec.Vec Std.I64)) (left right : Std.I64)
      (hR : RowsWellFormed ranges) (hB : BoundsWellFormed left right)
      (happend : ∃ extra : List (alloc.vec.Vec Std.I64),
        extra ≠ [] ∧ ranges'.val = ranges.val ++ extra ∧
          ∀ row ∈ extra, ∃ s e : Int, rowInts row = [s, e] ∧ 1 ≤ s ∧ s ≤ e ∧ e ≤ 50)
      (hlen : ranges'.val.length ≤ 50)
      (h : is_covered ranges left right = ok true) :
      is_covered ranges' left right = ok true := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (ranges ranges' : Slice (alloc.vec.Vec Std.I64)) (left right : Std.I64)
        (hR : RowsWellFormed ranges) (hB : BoundsWellFormed left right)
        (happend : ∃ extra : List (alloc.vec.Vec Std.I64),
          extra ≠ [] ∧ ranges'.val = ranges.val ++ extra ∧
            ∀ row ∈ extra, ∃ s e : Int, rowInts row = [s, e] ∧ 1 ≤ s ∧ s ≤ e ∧ e ≤ 50)
        (hlen : ranges'.val.length ≤ 50)
        (h : is_covered ranges left right = ok true), is_covered ranges' left right = ok true) := by
    sorry

  /-- If the function returns true on ranges with parameters left, right, then for every right' with left <= right' <= right, the function returns true on ranges with parameters left, right'.
    Preconditions: Write len(ranges) for the number of intervals and, for each index i with 0 <= i < len(ranges), write ranges[i] = [start_i, end_i]. Preconditions: 1 <= len(ranges) <= 50; for every i with 0 <= i < len(ranges), ranges[i] has length exactly 2 and 1 <= start_i <= end_i <= 50; and 1 <= left <= right <= 50. -/
  theorem spec_9 (ranges : Slice (alloc.vec.Vec Std.I64)) (left right : Std.I64)
      (hR : RowsWellFormed ranges) (hB : BoundsWellFormed left right)
      (h : is_covered ranges left right = ok true)
      (right' : Std.I64) (h1 : left.val ≤ right'.val) (h2 : right'.val ≤ right.val) :
      is_covered ranges left right' = ok true := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (ranges : Slice (alloc.vec.Vec Std.I64)) (left right : Std.I64)
        (hR : RowsWellFormed ranges) (hB : BoundsWellFormed left right)
        (h : is_covered ranges left right = ok true)
        (right' : Std.I64) (h1 : left.val ≤ right'.val) (h2 : right'.val ≤ right.val), is_covered ranges left right' = ok true) := by
    sorry

  /-- If the function returns true on ranges with parameters left, right, then for every left' with left <= left' <= right, the function returns true on ranges with parameters left', right.
    Preconditions: Write len(ranges) for the number of intervals and, for each index i with 0 <= i < len(ranges), write ranges[i] = [start_i, end_i]. Preconditions: 1 <= len(ranges) <= 50; for every i with 0 <= i < len(ranges), ranges[i] has length exactly 2 and 1 <= start_i <= end_i <= 50; and 1 <= left <= right <= 50. -/
  theorem spec_10 (ranges : Slice (alloc.vec.Vec Std.I64)) (left right : Std.I64)
      (hR : RowsWellFormed ranges) (hB : BoundsWellFormed left right)
      (h : is_covered ranges left right = ok true)
      (left' : Std.I64) (h1 : left.val ≤ left'.val) (h2 : left'.val ≤ right.val) :
      is_covered ranges left' right = ok true := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (ranges : Slice (alloc.vec.Vec Std.I64)) (left right : Std.I64)
        (hR : RowsWellFormed ranges) (hB : BoundsWellFormed left right)
        (h : is_covered ranges left right = ok true)
        (left' : Std.I64) (h1 : left.val ≤ left'.val) (h2 : left'.val ≤ right.val), is_covered ranges left' right = ok true) := by
    sorry

  /-- If the function returns true on ranges with parameters left, right, and ranges' is an array of the same length such that each ranges'[i] = [start_i', end_i'] satisfies 1 <= start_i' <= start_i <= end_i <= end_i' <= 50, then the function returns true on ranges' with the same left, right.
    Preconditions: Write len(ranges) for the number of intervals and, for each index i with 0 <= i < len(ranges), write ranges[i] = [start_i, end_i]. Preconditions: 1 <= len(ranges) <= 50; for every i with 0 <= i < len(ranges), ranges[i] has length exactly 2 and 1 <= start_i <= end_i <= 50; and 1 <= left <= right <= 50. -/
  theorem spec_11 (ranges ranges' : Slice (alloc.vec.Vec Std.I64)) (left right : Std.I64)
      (hR : RowsWellFormed ranges) (hB : BoundsWellFormed left right)
      (hlen : ranges'.val.length = ranges.val.length)
      (hwide : ∀ i, i < ranges.val.length → ∃ s e s' e' : Int,
        IsIntervalAt ranges i s e ∧ IsIntervalAt ranges' i s' e' ∧
          1 ≤ s' ∧ s' ≤ s ∧ e ≤ e' ∧ e' ≤ 50)
      (h : is_covered ranges left right = ok true) :
      is_covered ranges' left right = ok true := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (ranges ranges' : Slice (alloc.vec.Vec Std.I64)) (left right : Std.I64)
        (hR : RowsWellFormed ranges) (hB : BoundsWellFormed left right)
        (hlen : ranges'.val.length = ranges.val.length)
        (hwide : ∀ i, i < ranges.val.length → ∃ s e s' e' : Int,
          IsIntervalAt ranges i s e ∧ IsIntervalAt ranges' i s' e' ∧
            1 ≤ s' ∧ s' ≤ s ∧ e ≤ e' ∧ e' ≤ 50)
        (h : is_covered ranges left right = ok true), is_covered ranges' left right = ok true) := by
    sorry

  end AegisSpec.IsCovered
