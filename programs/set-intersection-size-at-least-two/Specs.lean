import Aegis.IntersectionSizeTwo.Code.Funs

/-!
# Specifications of `Aegis.IntersectionSizeTwo.intersection_size_two`

LeetCode problem `set-intersection-size-at-least-two`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.IntersectionSizeTwo

  open Aeneas.Std.Result

  def vecInterval (v : alloc.vec.Vec Std.I64) : Option (ℤ × ℤ) :=
    match v.val with
    | [x, y] => some (x.val, y.val)
    | _ => none

  def intervalAt (intervals : Slice (alloc.vec.Vec Std.I64)) (i : ℕ) : Option (ℤ × ℤ) :=
    (intervals.val[i]?).bind vecInterval

  def startOf (intervals : Slice (alloc.vec.Vec Std.I64)) (i : ℕ) : ℤ :=
    match intervalAt intervals i with
    | some p => p.1
    | none => 0

  def endOf (intervals : Slice (alloc.vec.Vec Std.I64)) (i : ℕ) : ℤ :=
    match intervalAt intervals i with
    | some p => p.2
    | none => 0

  def countIn (S : Finset ℤ) (a b : ℤ) : ℕ :=
    (S.filter (fun x => a ≤ x ∧ x ≤ b)).card

  def countInInterval (intervals : Slice (alloc.vec.Vec Std.I64)) (i : ℕ) (S : Finset ℤ) : ℕ :=
    countIn S (startOf intervals i) (endOf intervals i)

  def CoversAll (intervals : Slice (alloc.vec.Vec Std.I64)) (S : Finset ℤ) : Prop :=
    ∀ i : ℕ, i < intervals.val.length → 2 ≤ countInInterval intervals i S

  def ValidInput (intervals : Slice (alloc.vec.Vec Std.I64)) (n : ℕ) : Prop :=
    intervals.val.length = n ∧
      ∀ i : ℕ, i < n →
        intervalAt intervals i = some (startOf intervals i, endOf intervals i) ∧
          0 ≤ startOf intervals i ∧ startOf intervals i < endOf intervals i ∧
            endOf intervals i ≤ 100000000

  def InsertEntry (intervals intervals' : Slice (alloc.vec.Vec Std.I64))
      (v : alloc.vec.Vec Std.I64) : Prop :=
    ∃ k : ℕ, k ≤ intervals.val.length ∧
      intervals'.val = intervals.val.take k ++ [v] ++ intervals.val.drop k

  /-- The function returns a result r and r equals the minimum cardinality of a finite set S of integers such that for every i with 0 <= i < n, the number of elements of S lying in the closed integer interval [a_i, b_i] is at least 2. Equivalently, r = min { |S| : S is a finite set of integers and, for every i, |{x in S : a_i <= x <= b_i}| >= 2 }.
    Preconditions: Let n = len(intervals). Assume 1 <= n <= 3000. For every i with 0 <= i < n, len(intervals[i]) = 2; write a_i = intervals[i][0] and b_i = intervals[i][1]. Assume 0 <= a_i < b_i <= 100000000 for every i. -/
  theorem spec_1 (intervals : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
      (hvalid : ValidInput intervals n) (hpos : 1 ≤ n) (hmax : n ≤ 3000) :
      ∃ r : Std.I64,
        Aegis.IntersectionSizeTwo.intersection_size_two intervals = ok r ∧
          (∀ S : Finset ℤ, CoversAll intervals S → r.val ≤ (S.card : ℤ)) ∧
          ∃ S : Finset ℤ, CoversAll intervals S ∧ (S.card : ℤ) = r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (intervals : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
        (hvalid : ValidInput intervals n) (hpos : 1 ≤ n) (hmax : n ≤ 3000), ∃ r : Std.I64,
          Aegis.IntersectionSizeTwo.intersection_size_two intervals = ok r ∧
            (∀ S : Finset ℤ, CoversAll intervals S → r.val ≤ (S.card : ℤ)) ∧
            ∃ S : Finset ℤ, CoversAll intervals S ∧ (S.card : ℤ) = r.val) := by
    sorry

  /-- The function returns a result r: evaluation does not fail, panic, or overflow on any input satisfying the preconditions.
    Preconditions: Let n = len(intervals). Assume 1 <= n <= 3000. For every i with 0 <= i < n, len(intervals[i]) = 2; write a_i = intervals[i][0] and b_i = intervals[i][1]. Assume 0 <= a_i < b_i <= 100000000 for every i. -/
  theorem spec_2 (intervals : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
      (hvalid : ValidInput intervals n) (hpos : 1 ≤ n) (hmax : n ≤ 3000) :
      ∃ r : Std.I64, Aegis.IntersectionSizeTwo.intersection_size_two intervals = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (intervals : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
        (hvalid : ValidInput intervals n) (hpos : 1 ≤ n) (hmax : n ≤ 3000), ∃ r : Std.I64, Aegis.IntersectionSizeTwo.intersection_size_two intervals = ok r) := by
    sorry

  /-- Whenever the function returns a result r, r >= 2.
    Preconditions: Let n = len(intervals). Assume 1 <= n <= 3000. For every i with 0 <= i < n, len(intervals[i]) = 2; write a_i = intervals[i][0] and b_i = intervals[i][1]. Assume 0 <= a_i < b_i <= 100000000 for every i. -/
  theorem spec_3 (intervals : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
      (hvalid : ValidInput intervals n) (hpos : 1 ≤ n) (hmax : n ≤ 3000) :
      ∀ r : Std.I64,
        Aegis.IntersectionSizeTwo.intersection_size_two intervals = ok r → 2 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (intervals : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
        (hvalid : ValidInput intervals n) (hpos : 1 ≤ n) (hmax : n ≤ 3000), ∀ r : Std.I64,
          Aegis.IntersectionSizeTwo.intersection_size_two intervals = ok r → 2 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r <= 2 * len(intervals).
    Preconditions: Let n = len(intervals). Assume 1 <= n <= 3000. For every i with 0 <= i < n, len(intervals[i]) = 2; write a_i = intervals[i][0] and b_i = intervals[i][1]. Assume 0 <= a_i < b_i <= 100000000 for every i. -/
  theorem spec_4 (intervals : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
      (hvalid : ValidInput intervals n) (hpos : 1 ≤ n) (hmax : n ≤ 3000) :
      ∀ r : Std.I64,
        Aegis.IntersectionSizeTwo.intersection_size_two intervals = ok r →
          r.val ≤ 2 * (intervals.val.length : ℤ) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (intervals : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
        (hvalid : ValidInput intervals n) (hpos : 1 ≤ n) (hmax : n ≤ 3000), ∀ r : Std.I64,
          Aegis.IntersectionSizeTwo.intersection_size_two intervals = ok r →
            r.val ≤ 2 * (intervals.val.length : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, for every finite set S of integers satisfying |{x in S : a_i <= x <= b_i}| >= 2 for every i with 0 <= i < n, we have |S| >= r.
    Preconditions: Let n = len(intervals). Assume 1 <= n <= 3000. For every i with 0 <= i < n, len(intervals[i]) = 2; write a_i = intervals[i][0] and b_i = intervals[i][1]. Assume 0 <= a_i < b_i <= 100000000 for every i. -/
  theorem spec_5 (intervals : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
      (hvalid : ValidInput intervals n) (hpos : 1 ≤ n) (hmax : n ≤ 3000) :
      ∀ r : Std.I64,
        Aegis.IntersectionSizeTwo.intersection_size_two intervals = ok r →
          ∀ S : Finset ℤ, CoversAll intervals S → r.val ≤ (S.card : ℤ) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (intervals : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
        (hvalid : ValidInput intervals n) (hpos : 1 ≤ n) (hmax : n ≤ 3000), ∀ r : Std.I64,
          Aegis.IntersectionSizeTwo.intersection_size_two intervals = ok r →
            ∀ S : Finset ℤ, CoversAll intervals S → r.val ≤ (S.card : ℤ)) := by
    sorry

  /-- If there exist integers x and y with x < y such that a_i <= x < y <= b_i for every i with 0 <= i < n, then whenever the function returns a result r, r = 2.
    Preconditions: Let n = len(intervals). Assume 1 <= n <= 3000. For every i with 0 <= i < n, len(intervals[i]) = 2; write a_i = intervals[i][0] and b_i = intervals[i][1]. Assume 0 <= a_i < b_i <= 100000000 for every i. -/
  theorem spec_6 (intervals : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
      (hvalid : ValidInput intervals n) (hpos : 1 ≤ n) (hmax : n ≤ 3000)
      (hcore : ∃ x y : ℤ, x < y ∧
        ∀ i : ℕ, i < n → startOf intervals i ≤ x ∧ y ≤ endOf intervals i) :
      ∀ r : Std.I64,
        Aegis.IntersectionSizeTwo.intersection_size_two intervals = ok r → r.val = 2 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (intervals : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
        (hvalid : ValidInput intervals n) (hpos : 1 ≤ n) (hmax : n ≤ 3000)
        (hcore : ∃ x y : ℤ, x < y ∧
          ∀ i : ℕ, i < n → startOf intervals i ≤ x ∧ y ≤ endOf intervals i), ∀ r : Std.I64,
          Aegis.IntersectionSizeTwo.intersection_size_two intervals = ok r → r.val = 2) := by
    sorry

  /-- If the closed intervals are pairwise disjoint, that is, for all i and j with 0 <= i < n, 0 <= j < n, and i != j, either b_i < a_j or b_j < a_i, then whenever the function returns a result r, r = 2 * n.
    Preconditions: Let n = len(intervals). Assume 1 <= n <= 3000. For every i with 0 <= i < n, len(intervals[i]) = 2; write a_i = intervals[i][0] and b_i = intervals[i][1]. Assume 0 <= a_i < b_i <= 100000000 for every i. -/
  theorem spec_7 (intervals : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
      (hvalid : ValidInput intervals n) (hpos : 1 ≤ n) (hmax : n ≤ 3000)
      (hdisj : ∀ i j : ℕ, i < n → j < n → i ≠ j →
        endOf intervals i < startOf intervals j ∨ endOf intervals j < startOf intervals i) :
      ∀ r : Std.I64,
        Aegis.IntersectionSizeTwo.intersection_size_two intervals = ok r →
          r.val = 2 * (n : ℤ) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (intervals : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
        (hvalid : ValidInput intervals n) (hpos : 1 ≤ n) (hmax : n ≤ 3000)
        (hdisj : ∀ i j : ℕ, i < n → j < n → i ≠ j →
          endOf intervals i < startOf intervals j ∨ endOf intervals j < startOf intervals i), ∀ r : Std.I64,
          Aegis.IntersectionSizeTwo.intersection_size_two intervals = ok r →
            r.val = 2 * (n : ℤ)) := by
    sorry

  /-- Whenever the function returns r on intervals and r' on intervals', we have r' = r.
    Preconditions: Let n = len(intervals). Assume 1 <= n <= 3000. For every i with 0 <= i < n, len(intervals[i]) = 2; write a_i = intervals[i][0] and b_i = intervals[i][1]. Assume 0 <= a_i < b_i <= 100000000 for every i. Let intervals' be any slice satisfying the same preconditions with len(intervals') = n, and suppose there is a permutation pi of {0,...,n-1} such that intervals'[i] = intervals[pi(i)] for every i. -/
  theorem spec_8 (intervals intervals' : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
      (hvalid : ValidInput intervals n) (hvalid' : ValidInput intervals' n)
      (hpos : 1 ≤ n) (hmax : n ≤ 3000)
      (hperm : ∃ π : Equiv.Perm (Fin n),
        ∀ i : Fin n, intervals'.val[i.val]? = intervals.val[(π i).val]?) :
      ∀ r r' : Std.I64,
        Aegis.IntersectionSizeTwo.intersection_size_two intervals = ok r →
          Aegis.IntersectionSizeTwo.intersection_size_two intervals' = ok r' →
            r'.val = r.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (intervals intervals' : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
        (hvalid : ValidInput intervals n) (hvalid' : ValidInput intervals' n)
        (hpos : 1 ≤ n) (hmax : n ≤ 3000)
        (hperm : ∃ π : Equiv.Perm (Fin n),
          ∀ i : Fin n, intervals'.val[i.val]? = intervals.val[(π i).val]?), ∀ r r' : Std.I64,
          Aegis.IntersectionSizeTwo.intersection_size_two intervals = ok r →
            Aegis.IntersectionSizeTwo.intersection_size_two intervals' = ok r' →
              r'.val = r.val) := by
    sorry

  /-- Whenever the function returns r on intervals and r' on intervals', we have r' >= r.
    Preconditions: Let n = len(intervals). Assume 1 <= n <= 2999. For every i with 0 <= i < n, len(intervals[i]) = 2; write a_i = intervals[i][0] and b_i = intervals[i][1]. Assume 0 <= a_i < b_i <= 100000000 for every i. Let intervals' be any slice satisfying the same preconditions with len(intervals') = n+1 obtained by inserting one additional valid interval [a,b], where 0 <= a < b <= 100000000, into intervals. -/
  theorem spec_9 (intervals intervals' : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
      (v : alloc.vec.Vec Std.I64)
      (hvalid : ValidInput intervals n) (hpos : 1 ≤ n) (hmax : n ≤ 2999)
      (hvalid' : ValidInput intervals' (n + 1))
      (hins : InsertEntry intervals intervals' v)
      (hv : ∃ a b : ℤ, vecInterval v = some (a, b) ∧ 0 ≤ a ∧ a < b ∧ b ≤ 100000000) :
      ∀ r r' : Std.I64,
        Aegis.IntersectionSizeTwo.intersection_size_two intervals = ok r →
          Aegis.IntersectionSizeTwo.intersection_size_two intervals' = ok r' →
            r.val ≤ r'.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (intervals intervals' : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
        (v : alloc.vec.Vec Std.I64)
        (hvalid : ValidInput intervals n) (hpos : 1 ≤ n) (hmax : n ≤ 2999)
        (hvalid' : ValidInput intervals' (n + 1))
        (hins : InsertEntry intervals intervals' v)
        (hv : ∃ a b : ℤ, vecInterval v = some (a, b) ∧ 0 ≤ a ∧ a < b ∧ b ≤ 100000000), ∀ r r' : Std.I64,
          Aegis.IntersectionSizeTwo.intersection_size_two intervals = ok r →
            Aegis.IntersectionSizeTwo.intersection_size_two intervals' = ok r' →
              r.val ≤ r'.val) := by
    sorry

  /-- Whenever the function returns r on intervals and r' on intervals', we have r' <= r + 2.
    Preconditions: Let n = len(intervals). Assume 1 <= n <= 2999. For every i with 0 <= i < n, len(intervals[i]) = 2; write a_i = intervals[i][0] and b_i = intervals[i][1]. Assume 0 <= a_i < b_i <= 100000000 for every i. Let intervals' be any slice satisfying the same preconditions with len(intervals') = n+1 obtained by inserting one additional valid interval [a,b], where 0 <= a < b <= 100000000, into intervals. -/
  theorem spec_10 (intervals intervals' : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
      (v : alloc.vec.Vec Std.I64)
      (hvalid : ValidInput intervals n) (hpos : 1 ≤ n) (hmax : n ≤ 2999)
      (hvalid' : ValidInput intervals' (n + 1))
      (hins : InsertEntry intervals intervals' v)
      (hv : ∃ a b : ℤ, vecInterval v = some (a, b) ∧ 0 ≤ a ∧ a < b ∧ b ≤ 100000000) :
      ∀ r r' : Std.I64,
        Aegis.IntersectionSizeTwo.intersection_size_two intervals = ok r →
          Aegis.IntersectionSizeTwo.intersection_size_two intervals' = ok r' →
            r'.val ≤ r.val + 2 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (intervals intervals' : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
        (v : alloc.vec.Vec Std.I64)
        (hvalid : ValidInput intervals n) (hpos : 1 ≤ n) (hmax : n ≤ 2999)
        (hvalid' : ValidInput intervals' (n + 1))
        (hins : InsertEntry intervals intervals' v)
        (hv : ∃ a b : ℤ, vecInterval v = some (a, b) ∧ 0 ≤ a ∧ a < b ∧ b ≤ 100000000), ∀ r r' : Std.I64,
          Aegis.IntersectionSizeTwo.intersection_size_two intervals = ok r →
            Aegis.IntersectionSizeTwo.intersection_size_two intervals' = ok r' →
              r'.val ≤ r.val + 2) := by
    sorry

  /-- Whenever the function returns a result r, there exists a finite set S of integers such that |S| = r, for every i with 0 <= i < n we have |{x in S : a_i <= x <= b_i}| >= 2, and every x in S is equal to a_i or b_i for some i with 0 <= i < n.
    Preconditions: Let n = len(intervals). Assume 1 <= n <= 3000. For every i with 0 <= i < n, len(intervals[i]) = 2; write a_i = intervals[i][0] and b_i = intervals[i][1]. Assume 0 <= a_i < b_i <= 100000000 for every i. -/
  theorem spec_11 (intervals : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
      (hvalid : ValidInput intervals n) (hpos : 1 ≤ n) (hmax : n ≤ 3000) :
      ∀ r : Std.I64,
        Aegis.IntersectionSizeTwo.intersection_size_two intervals = ok r →
          ∃ S : Finset ℤ,
            (S.card : ℤ) = r.val ∧ CoversAll intervals S ∧
              ∀ x : ℤ, x ∈ S →
                ∃ i : ℕ, i < n ∧ (x = startOf intervals i ∨ x = endOf intervals i) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (intervals : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
        (hvalid : ValidInput intervals n) (hpos : 1 ≤ n) (hmax : n ≤ 3000), ∀ r : Std.I64,
          Aegis.IntersectionSizeTwo.intersection_size_two intervals = ok r →
            ∃ S : Finset ℤ,
              (S.card : ℤ) = r.val ∧ CoversAll intervals S ∧
                ∀ x : ℤ, x ∈ S →
                  ∃ i : ℕ, i < n ∧ (x = startOf intervals i ∨ x = endOf intervals i)) := by
    sorry

  /-- Whenever the function returns a result r, for every i with b_i = a_i + 1, every finite set S of integers with |S| = r and |{x in S : a_j <= x <= b_j}| >= 2 for all j with 0 <= j < n necessarily contains both a_i and b_i.
    Preconditions: Let n = len(intervals). Assume 1 <= n <= 3000. For every i with 0 <= i < n, len(intervals[i]) = 2; write a_i = intervals[i][0] and b_i = intervals[i][1]. Assume 0 <= a_i < b_i <= 100000000 for every i. -/
  theorem spec_12 (intervals : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
      (hvalid : ValidInput intervals n) (hpos : 1 ≤ n) (hmax : n ≤ 3000) :
      ∀ r : Std.I64,
        Aegis.IntersectionSizeTwo.intersection_size_two intervals = ok r →
          ∀ i : ℕ, i < n → endOf intervals i = startOf intervals i + 1 →
            ∀ S : Finset ℤ, (S.card : ℤ) = r.val → CoversAll intervals S →
              startOf intervals i ∈ S ∧ endOf intervals i ∈ S := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (intervals : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
        (hvalid : ValidInput intervals n) (hpos : 1 ≤ n) (hmax : n ≤ 3000), ∀ r : Std.I64,
          Aegis.IntersectionSizeTwo.intersection_size_two intervals = ok r →
            ∀ i : ℕ, i < n → endOf intervals i = startOf intervals i + 1 →
              ∀ S : Finset ℤ, (S.card : ℤ) = r.val → CoversAll intervals S →
                startOf intervals i ∈ S ∧ endOf intervals i ∈ S) := by
    sorry

  end AegisSpec.IntersectionSizeTwo
