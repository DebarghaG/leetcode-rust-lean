import Aegis.IsZeroArray.Code.Funs

/-!
# Specifications of `Aegis.IsZeroArray.is_zero_array`

LeetCode problem `zero-array-transformation-i`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

open Aegis.IsZeroArray

namespace AegisSpec.IsZeroArray

def i64At (l : List Std.I64) (k : Nat) : Int :=
  match l[k]? with
  | some x => x.val
  | none => 0

def queryStart (queries : Slice (alloc.vec.Vec Std.I64)) (j : Nat) : Int :=
  match queries.val[j]? with
  | some q => i64At q.val 0
  | none => 0

def queryEnd (queries : Slice (alloc.vec.Vec Std.I64)) (j : Nat) : Int :=
  match queries.val[j]? with
  | some q => i64At q.val 1
  | none => 0

def coverCount (queries : Slice (alloc.vec.Vec Std.I64)) (i : Int) : Nat :=
  ((List.range queries.val.length).filter
    (fun j => decide (queryStart queries j ≤ i ∧ i ≤ queryEnd queries j))).length

def numsSum (nums : Slice Std.I64) : Int :=
  (nums.val.map (fun x => x.val)).sum

def queryWidthSum (queries : Slice (alloc.vec.Vec Std.I64)) : Int :=
  ((List.range queries.val.length).map
    (fun j => queryEnd queries j - queryStart queries j + 1)).sum

/-- Whenever is_zero_array returns a result r, r = true if and only if for every integer i with 0 <= i < len(nums), nums[i] <= c(i), where c(i) is the number of integers j such that 0 <= j < len(queries) and queries[j][0] <= i <= queries[j][1].
  Preconditions: len(nums) is an integer with 1 <= len(nums) <= 100000; for every integer i with 0 <= i < len(nums), nums[i] is an integer with 0 <= nums[i] <= 100000; len(queries) is an integer with 1 <= len(queries) <= 100000; for every integer j with 0 <= j < len(queries), len(queries[j]) = 2, queries[j][0] and queries[j][1] are integers, and 0 <= queries[j][0] <= queries[j][1] < len(nums). -/
theorem spec_1
    (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hnums_len : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hnums : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (hqueries_len : 1 ≤ queries.val.length ∧ queries.val.length ≤ 100000)
    (hqueries : ∀ (j : Nat) (hj : j < queries.val.length),
      (queries.val[j]).val.length = 2 ∧
        0 ≤ queryStart queries j ∧ queryStart queries j ≤ queryEnd queries j ∧
          queryEnd queries j < (nums.val.length : Int))
    (r : Bool) (hr : is_zero_array nums queries = ok r) :
    (r = true ↔ ∀ (i : Nat) (hi : i < nums.val.length),
      (nums.val[i]).val ≤ ((coverCount queries (i : Int) : Nat) : Int)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hnums_len : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hnums : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (hqueries_len : 1 ≤ queries.val.length ∧ queries.val.length ≤ 100000)
    (hqueries : ∀ (j : Nat) (hj : j < queries.val.length),
      (queries.val[j]).val.length = 2 ∧
        0 ≤ queryStart queries j ∧ queryStart queries j ≤ queryEnd queries j ∧
          queryEnd queries j < (nums.val.length : Int))
    (r : Bool) (hr : is_zero_array nums queries = ok r), (r = true ↔ ∀ (i : Nat) (hi : i < nums.val.length),
      (nums.val[i]).val ≤ ((coverCount queries (i : Int) : Nat) : Int))) := by
  sorry

/-- is_zero_array returns a result r (it does not fail).
  Preconditions: len(nums) is an integer with 1 <= len(nums) <= 100000; for every integer i with 0 <= i < len(nums), nums[i] is an integer with 0 <= nums[i] <= 100000; len(queries) is an integer with 1 <= len(queries) <= 100000; for every integer j with 0 <= j < len(queries), len(queries[j]) = 2, queries[j][0] and queries[j][1] are integers, and 0 <= queries[j][0] <= queries[j][1] < len(nums). -/
theorem spec_2
    (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hnums_len : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hnums : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (hqueries_len : 1 ≤ queries.val.length ∧ queries.val.length ≤ 100000)
    (hqueries : ∀ (j : Nat) (hj : j < queries.val.length),
      (queries.val[j]).val.length = 2 ∧
        0 ≤ queryStart queries j ∧ queryStart queries j ≤ queryEnd queries j ∧
          queryEnd queries j < (nums.val.length : Int)) :
    ∃ r, is_zero_array nums queries = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hnums_len : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hnums : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (hqueries_len : 1 ≤ queries.val.length ∧ queries.val.length ≤ 100000)
    (hqueries : ∀ (j : Nat) (hj : j < queries.val.length),
      (queries.val[j]).val.length = 2 ∧
        0 ≤ queryStart queries j ∧ queryStart queries j ≤ queryEnd queries j ∧
          queryEnd queries j < (nums.val.length : Int)), ∃ r, is_zero_array nums queries = ok r) := by
  sorry

/-- Whenever is_zero_array returns a result r, if for every integer i with 0 <= i < len(nums) we have nums[i] <= c(i), where c(i) is the number of j with 0 <= j < len(queries) and queries[j][0] <= i <= queries[j][1], then r = true.
  Preconditions: len(nums) is an integer with 1 <= len(nums) <= 100000; for every integer i with 0 <= i < len(nums), nums[i] is an integer with 0 <= nums[i] <= 100000; len(queries) is an integer with 1 <= len(queries) <= 100000; for every integer j with 0 <= j < len(queries), len(queries[j]) = 2, queries[j][0] and queries[j][1] are integers, and 0 <= queries[j][0] <= queries[j][1] < len(nums). -/
theorem spec_3
    (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hnums_len : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hnums : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (hqueries_len : 1 ≤ queries.val.length ∧ queries.val.length ≤ 100000)
    (hqueries : ∀ (j : Nat) (hj : j < queries.val.length),
      (queries.val[j]).val.length = 2 ∧
        0 ≤ queryStart queries j ∧ queryStart queries j ≤ queryEnd queries j ∧
          queryEnd queries j < (nums.val.length : Int))
    (r : Bool) (hr : is_zero_array nums queries = ok r)
    (hcov : ∀ (i : Nat) (hi : i < nums.val.length),
      (nums.val[i]).val ≤ ((coverCount queries (i : Int) : Nat) : Int)) :
    r = true := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hnums_len : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hnums : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (hqueries_len : 1 ≤ queries.val.length ∧ queries.val.length ≤ 100000)
    (hqueries : ∀ (j : Nat) (hj : j < queries.val.length),
      (queries.val[j]).val.length = 2 ∧
        0 ≤ queryStart queries j ∧ queryStart queries j ≤ queryEnd queries j ∧
          queryEnd queries j < (nums.val.length : Int))
    (r : Bool) (hr : is_zero_array nums queries = ok r)
    (hcov : ∀ (i : Nat) (hi : i < nums.val.length),
      (nums.val[i]).val ≤ ((coverCount queries (i : Int) : Nat) : Int)), r = true) := by
  sorry

/-- Whenever is_zero_array returns a result r, if r = false then there exists an integer i with 0 <= i < len(nums) such that nums[i] > c(i), where c(i) is the number of j with 0 <= j < len(queries) and queries[j][0] <= i <= queries[j][1].
  Preconditions: len(nums) is an integer with 1 <= len(nums) <= 100000; for every integer i with 0 <= i < len(nums), nums[i] is an integer with 0 <= nums[i] <= 100000; len(queries) is an integer with 1 <= len(queries) <= 100000; for every integer j with 0 <= j < len(queries), len(queries[j]) = 2, queries[j][0] and queries[j][1] are integers, and 0 <= queries[j][0] <= queries[j][1] < len(nums). -/
theorem spec_4
    (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hnums_len : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hnums : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (hqueries_len : 1 ≤ queries.val.length ∧ queries.val.length ≤ 100000)
    (hqueries : ∀ (j : Nat) (hj : j < queries.val.length),
      (queries.val[j]).val.length = 2 ∧
        0 ≤ queryStart queries j ∧ queryStart queries j ≤ queryEnd queries j ∧
          queryEnd queries j < (nums.val.length : Int))
    (r : Bool) (hr : is_zero_array nums queries = ok r) (hfalse : r = false) :
    ∃ (i : Nat) (hi : i < nums.val.length),
      ((coverCount queries (i : Int) : Nat) : Int) < (nums.val[i]).val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hnums_len : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hnums : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (hqueries_len : 1 ≤ queries.val.length ∧ queries.val.length ≤ 100000)
    (hqueries : ∀ (j : Nat) (hj : j < queries.val.length),
      (queries.val[j]).val.length = 2 ∧
        0 ≤ queryStart queries j ∧ queryStart queries j ≤ queryEnd queries j ∧
          queryEnd queries j < (nums.val.length : Int))
    (r : Bool) (hr : is_zero_array nums queries = ok r) (hfalse : r = false), ∃ (i : Nat) (hi : i < nums.val.length),
      ((coverCount queries (i : Int) : Nat) : Int) < (nums.val[i]).val) := by
  sorry

/-- Whenever is_zero_array returns a result r, if r = true then sum_{i=0}^{len(nums)-1} nums[i] <= sum_{j=0}^{len(queries)-1} (queries[j][1] - queries[j][0] + 1).
  Preconditions: len(nums) is an integer with 1 <= len(nums) <= 100000; for every integer i with 0 <= i < len(nums), nums[i] is an integer with 0 <= nums[i] <= 100000; len(queries) is an integer with 1 <= len(queries) <= 100000; for every integer j with 0 <= j < len(queries), len(queries[j]) = 2, queries[j][0] and queries[j][1] are integers, and 0 <= queries[j][0] <= queries[j][1] < len(nums). -/
theorem spec_5
    (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hnums_len : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hnums : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (hqueries_len : 1 ≤ queries.val.length ∧ queries.val.length ≤ 100000)
    (hqueries : ∀ (j : Nat) (hj : j < queries.val.length),
      (queries.val[j]).val.length = 2 ∧
        0 ≤ queryStart queries j ∧ queryStart queries j ≤ queryEnd queries j ∧
          queryEnd queries j < (nums.val.length : Int))
    (r : Bool) (hr : is_zero_array nums queries = ok r) (htrue : r = true) :
    numsSum nums ≤ queryWidthSum queries := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hnums_len : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hnums : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (hqueries_len : 1 ≤ queries.val.length ∧ queries.val.length ≤ 100000)
    (hqueries : ∀ (j : Nat) (hj : j < queries.val.length),
      (queries.val[j]).val.length = 2 ∧
        0 ≤ queryStart queries j ∧ queryStart queries j ≤ queryEnd queries j ∧
          queryEnd queries j < (nums.val.length : Int))
    (r : Bool) (hr : is_zero_array nums queries = ok r) (htrue : r = true), numsSum nums ≤ queryWidthSum queries) := by
  sorry

/-- Whenever is_zero_array returns a result r, if there exists an integer i with 0 <= i < len(nums) and nums[i] > len(queries), then r = false.
  Preconditions: len(nums) is an integer with 1 <= len(nums) <= 100000; for every integer i with 0 <= i < len(nums), nums[i] is an integer with 0 <= nums[i] <= 100000; len(queries) is an integer with 1 <= len(queries) <= 100000; for every integer j with 0 <= j < len(queries), len(queries[j]) = 2, queries[j][0] and queries[j][1] are integers, and 0 <= queries[j][0] <= queries[j][1] < len(nums). -/
theorem spec_6
    (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hnums_len : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hnums : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (hqueries_len : 1 ≤ queries.val.length ∧ queries.val.length ≤ 100000)
    (hqueries : ∀ (j : Nat) (hj : j < queries.val.length),
      (queries.val[j]).val.length = 2 ∧
        0 ≤ queryStart queries j ∧ queryStart queries j ≤ queryEnd queries j ∧
          queryEnd queries j < (nums.val.length : Int))
    (r : Bool) (hr : is_zero_array nums queries = ok r)
    (hwit : ∃ (i : Nat) (hi : i < nums.val.length),
      ((queries.val.length : Nat) : Int) < (nums.val[i]).val) :
    r = false := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hnums_len : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hnums : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (hqueries_len : 1 ≤ queries.val.length ∧ queries.val.length ≤ 100000)
    (hqueries : ∀ (j : Nat) (hj : j < queries.val.length),
      (queries.val[j]).val.length = 2 ∧
        0 ≤ queryStart queries j ∧ queryStart queries j ≤ queryEnd queries j ∧
          queryEnd queries j < (nums.val.length : Int))
    (r : Bool) (hr : is_zero_array nums queries = ok r)
    (hwit : ∃ (i : Nat) (hi : i < nums.val.length),
      ((queries.val.length : Nat) : Int) < (nums.val[i]).val), r = false) := by
  sorry

/-- Whenever is_zero_array returns a result r, if for every integer i with 0 <= i < len(nums) we have nums[i] = 0, then r = true.
  Preconditions: len(nums) is an integer with 1 <= len(nums) <= 100000; for every integer i with 0 <= i < len(nums), nums[i] is an integer with 0 <= nums[i] <= 100000; len(queries) is an integer with 1 <= len(queries) <= 100000; for every integer j with 0 <= j < len(queries), len(queries[j]) = 2, queries[j][0] and queries[j][1] are integers, and 0 <= queries[j][0] <= queries[j][1] < len(nums). -/
theorem spec_7
    (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hnums_len : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hnums : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (hqueries_len : 1 ≤ queries.val.length ∧ queries.val.length ≤ 100000)
    (hqueries : ∀ (j : Nat) (hj : j < queries.val.length),
      (queries.val[j]).val.length = 2 ∧
        0 ≤ queryStart queries j ∧ queryStart queries j ≤ queryEnd queries j ∧
          queryEnd queries j < (nums.val.length : Int))
    (r : Bool) (hr : is_zero_array nums queries = ok r)
    (hzero : ∀ (i : Nat) (hi : i < nums.val.length), (nums.val[i]).val = 0) :
    r = true := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hnums_len : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hnums : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (hqueries_len : 1 ≤ queries.val.length ∧ queries.val.length ≤ 100000)
    (hqueries : ∀ (j : Nat) (hj : j < queries.val.length),
      (queries.val[j]).val.length = 2 ∧
        0 ≤ queryStart queries j ∧ queryStart queries j ≤ queryEnd queries j ∧
          queryEnd queries j < (nums.val.length : Int))
    (r : Bool) (hr : is_zero_array nums queries = ok r)
    (hzero : ∀ (i : Nat) (hi : i < nums.val.length), (nums.val[i]).val = 0), r = true) := by
  sorry

/-- Whenever is_zero_array returns a result r, if len(nums) = 1, then r = true if and only if nums[0] <= len(queries).
  Preconditions: len(nums) is an integer with 1 <= len(nums) <= 100000; for every integer i with 0 <= i < len(nums), nums[i] is an integer with 0 <= nums[i] <= 100000; len(queries) is an integer with 1 <= len(queries) <= 100000; for every integer j with 0 <= j < len(queries), len(queries[j]) = 2, queries[j][0] and queries[j][1] are integers, and 0 <= queries[j][0] <= queries[j][1] < len(nums). -/
theorem spec_8
    (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hnums_len : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hnums : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (hqueries_len : 1 ≤ queries.val.length ∧ queries.val.length ≤ 100000)
    (hqueries : ∀ (j : Nat) (hj : j < queries.val.length),
      (queries.val[j]).val.length = 2 ∧
        0 ≤ queryStart queries j ∧ queryStart queries j ≤ queryEnd queries j ∧
          queryEnd queries j < (nums.val.length : Int))
    (r : Bool) (hr : is_zero_array nums queries = ok r)
    (hlen : nums.val.length = 1) :
    (r = true ↔ (nums.val[0]).val ≤ ((queries.val.length : Nat) : Int)) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hnums_len : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hnums : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (hqueries_len : 1 ≤ queries.val.length ∧ queries.val.length ≤ 100000)
    (hqueries : ∀ (j : Nat) (hj : j < queries.val.length),
      (queries.val[j]).val.length = 2 ∧
        0 ≤ queryStart queries j ∧ queryStart queries j ≤ queryEnd queries j ∧
          queryEnd queries j < (nums.val.length : Int))
    (r : Bool) (hr : is_zero_array nums queries = ok r)
    (hlen : nums.val.length = 1), (r = true ↔ (nums.val[0]).val ≤ ((queries.val.length : Nat) : Int))) := by
  sorry

/-- Whenever is_zero_array returns a result r, if len(queries) = 1, then r = true if and only if, writing L = queries[0][0] and R = queries[0][1], (for every integer i with 0 <= i < len(nums) and (i < L or i > R), nums[i] = 0) and (for every integer i with L <= i <= R, nums[i] <= 1).
  Preconditions: len(nums) is an integer with 1 <= len(nums) <= 100000; for every integer i with 0 <= i < len(nums), nums[i] is an integer with 0 <= nums[i] <= 100000; len(queries) is an integer with 1 <= len(queries) <= 100000; for every integer j with 0 <= j < len(queries), len(queries[j]) = 2, queries[j][0] and queries[j][1] are integers, and 0 <= queries[j][0] <= queries[j][1] < len(nums). -/
theorem spec_9
    (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hnums_len : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hnums : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (hqueries_len : 1 ≤ queries.val.length ∧ queries.val.length ≤ 100000)
    (hqueries : ∀ (j : Nat) (hj : j < queries.val.length),
      (queries.val[j]).val.length = 2 ∧
        0 ≤ queryStart queries j ∧ queryStart queries j ≤ queryEnd queries j ∧
          queryEnd queries j < (nums.val.length : Int))
    (r : Bool) (hr : is_zero_array nums queries = ok r)
    (hlen : queries.val.length = 1) :
    (r = true ↔
      (∀ (i : Nat) (hi : i < nums.val.length),
        ((i : Nat) : Int) < queryStart queries 0 ∨ queryEnd queries 0 < ((i : Nat) : Int) →
          (nums.val[i]).val = 0) ∧
      (∀ (i : Nat) (hi : i < nums.val.length),
        queryStart queries 0 ≤ ((i : Nat) : Int) → ((i : Nat) : Int) ≤ queryEnd queries 0 →
          (nums.val[i]).val ≤ 1)) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hnums_len : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hnums : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (hqueries_len : 1 ≤ queries.val.length ∧ queries.val.length ≤ 100000)
    (hqueries : ∀ (j : Nat) (hj : j < queries.val.length),
      (queries.val[j]).val.length = 2 ∧
        0 ≤ queryStart queries j ∧ queryStart queries j ≤ queryEnd queries j ∧
          queryEnd queries j < (nums.val.length : Int))
    (r : Bool) (hr : is_zero_array nums queries = ok r)
    (hlen : queries.val.length = 1), (r = true ↔
      (∀ (i : Nat) (hi : i < nums.val.length),
        ((i : Nat) : Int) < queryStart queries 0 ∨ queryEnd queries 0 < ((i : Nat) : Int) →
          (nums.val[i]).val = 0) ∧
      (∀ (i : Nat) (hi : i < nums.val.length),
        queryStart queries 0 ≤ ((i : Nat) : Int) → ((i : Nat) : Int) ≤ queryEnd queries 0 →
          (nums.val[i]).val ≤ 1))) := by
  sorry

/-- Whenever is_zero_array returns a result r, if for every integer j with 0 <= j < len(queries) we have queries[j][0] = 0 and queries[j][1] = len(nums) - 1, then r = true if and only if for every integer i with 0 <= i < len(nums), nums[i] <= len(queries).
  Preconditions: len(nums) is an integer with 1 <= len(nums) <= 100000; for every integer i with 0 <= i < len(nums), nums[i] is an integer with 0 <= nums[i] <= 100000; len(queries) is an integer with 1 <= len(queries) <= 100000; for every integer j with 0 <= j < len(queries), len(queries[j]) = 2, queries[j][0] and queries[j][1] are integers, and 0 <= queries[j][0] <= queries[j][1] < len(nums). -/
theorem spec_10
    (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hnums_len : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hnums : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (hqueries_len : 1 ≤ queries.val.length ∧ queries.val.length ≤ 100000)
    (hqueries : ∀ (j : Nat) (hj : j < queries.val.length),
      (queries.val[j]).val.length = 2 ∧
        0 ≤ queryStart queries j ∧ queryStart queries j ≤ queryEnd queries j ∧
          queryEnd queries j < (nums.val.length : Int))
    (r : Bool) (hr : is_zero_array nums queries = ok r)
    (hfull : ∀ (j : Nat) (hj : j < queries.val.length),
      queryStart queries j = 0 ∧
        queryEnd queries j = ((nums.val.length : Nat) : Int) - 1) :
    (r = true ↔ ∀ (i : Nat) (hi : i < nums.val.length),
      (nums.val[i]).val ≤ ((queries.val.length : Nat) : Int)) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hnums_len : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hnums : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (hqueries_len : 1 ≤ queries.val.length ∧ queries.val.length ≤ 100000)
    (hqueries : ∀ (j : Nat) (hj : j < queries.val.length),
      (queries.val[j]).val.length = 2 ∧
        0 ≤ queryStart queries j ∧ queryStart queries j ≤ queryEnd queries j ∧
          queryEnd queries j < (nums.val.length : Int))
    (r : Bool) (hr : is_zero_array nums queries = ok r)
    (hfull : ∀ (j : Nat) (hj : j < queries.val.length),
      queryStart queries j = 0 ∧
        queryEnd queries j = ((nums.val.length : Nat) : Int) - 1), (r = true ↔ ∀ (i : Nat) (hi : i < nums.val.length),
      (nums.val[i]).val ≤ ((queries.val.length : Nat) : Int))) := by
  sorry

/-- Whenever is_zero_array nums queries returns true, for every slice a of length len(nums) such that 0 <= a[i] <= nums[i] for every integer i with 0 <= i < len(nums), the call is_zero_array a queries returns a result and that result is true.
  Preconditions: len(nums) is an integer with 1 <= len(nums) <= 100000; for every integer i with 0 <= i < len(nums), nums[i] is an integer with 0 <= nums[i] <= 100000; len(queries) is an integer with 1 <= len(queries) <= 100000; for every integer j with 0 <= j < len(queries), len(queries[j]) = 2, queries[j][0] and queries[j][1] are integers, and 0 <= queries[j][0] <= queries[j][1] < len(nums). -/
theorem spec_11
    (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hnums_len : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hnums : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (hqueries_len : 1 ≤ queries.val.length ∧ queries.val.length ≤ 100000)
    (hqueries : ∀ (j : Nat) (hj : j < queries.val.length),
      (queries.val[j]).val.length = 2 ∧
        0 ≤ queryStart queries j ∧ queryStart queries j ≤ queryEnd queries j ∧
          queryEnd queries j < (nums.val.length : Int))
    (haccept : is_zero_array nums queries = ok true)
    (a : Slice Std.I64) (hlen : a.val.length = nums.val.length)
    (ha : ∀ (i : Nat) (hi : i < a.val.length),
      0 ≤ (a.val[i]).val ∧ (a.val[i]).val ≤ (nums.val[i]'(by omega)).val) :
    ∃ r, is_zero_array a queries = ok r ∧ r = true := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hnums_len : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hnums : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (hqueries_len : 1 ≤ queries.val.length ∧ queries.val.length ≤ 100000)
    (hqueries : ∀ (j : Nat) (hj : j < queries.val.length),
      (queries.val[j]).val.length = 2 ∧
        0 ≤ queryStart queries j ∧ queryStart queries j ≤ queryEnd queries j ∧
          queryEnd queries j < (nums.val.length : Int))
    (haccept : is_zero_array nums queries = ok true)
    (a : Slice Std.I64) (hlen : a.val.length = nums.val.length)
    (ha : ∀ (i : Nat) (hi : i < a.val.length),
      0 ≤ (a.val[i]).val ∧ (a.val[i]).val ≤ (nums.val[i]'(by omega)).val), ∃ r, is_zero_array a queries = ok r ∧ r = true) := by
  sorry

/-- Whenever is_zero_array nums queries returns true, for every query list q' satisfying the same query preconditions with respect to len(nums), if c'(i) >= c(i) for every integer i with 0 <= i < len(nums), where c(i) is the number of j with 0 <= j < len(queries) and queries[j][0] <= i <= queries[j][1], and c'(i) is the number of j with 0 <= j < len(q') and q'[j][0] <= i <= q'[j][1], then the call is_zero_array nums q' returns a result and that result is true.
  Preconditions: len(nums) is an integer with 1 <= len(nums) <= 100000; for every integer i with 0 <= i < len(nums), nums[i] is an integer with 0 <= nums[i] <= 100000; len(queries) is an integer with 1 <= len(queries) <= 100000; for every integer j with 0 <= j < len(queries), len(queries[j]) = 2, queries[j][0] and queries[j][1] are integers, and 0 <= queries[j][0] <= queries[j][1] < len(nums). -/
theorem spec_12
    (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hnums_len : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hnums : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (hqueries_len : 1 ≤ queries.val.length ∧ queries.val.length ≤ 100000)
    (hqueries : ∀ (j : Nat) (hj : j < queries.val.length),
      (queries.val[j]).val.length = 2 ∧
        0 ≤ queryStart queries j ∧ queryStart queries j ≤ queryEnd queries j ∧
          queryEnd queries j < (nums.val.length : Int))
    (haccept : is_zero_array nums queries = ok true)
    (queries' : Slice (alloc.vec.Vec Std.I64))
    (hqueries'_len : 1 ≤ queries'.val.length ∧ queries'.val.length ≤ 100000)
    (hqueries' : ∀ (j : Nat) (hj : j < queries'.val.length),
      (queries'.val[j]).val.length = 2 ∧
        0 ≤ queryStart queries' j ∧ queryStart queries' j ≤ queryEnd queries' j ∧
          queryEnd queries' j < (nums.val.length : Int))
    (hcov : ∀ (i : Nat) (hi : i < nums.val.length),
      coverCount queries (i : Int) ≤ coverCount queries' (i : Int)) :
    ∃ r, is_zero_array nums queries' = ok r ∧ r = true := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hnums_len : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hnums : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (hqueries_len : 1 ≤ queries.val.length ∧ queries.val.length ≤ 100000)
    (hqueries : ∀ (j : Nat) (hj : j < queries.val.length),
      (queries.val[j]).val.length = 2 ∧
        0 ≤ queryStart queries j ∧ queryStart queries j ≤ queryEnd queries j ∧
          queryEnd queries j < (nums.val.length : Int))
    (haccept : is_zero_array nums queries = ok true)
    (queries' : Slice (alloc.vec.Vec Std.I64))
    (hqueries'_len : 1 ≤ queries'.val.length ∧ queries'.val.length ≤ 100000)
    (hqueries' : ∀ (j : Nat) (hj : j < queries'.val.length),
      (queries'.val[j]).val.length = 2 ∧
        0 ≤ queryStart queries' j ∧ queryStart queries' j ≤ queryEnd queries' j ∧
          queryEnd queries' j < (nums.val.length : Int))
    (hcov : ∀ (i : Nat) (hi : i < nums.val.length),
      coverCount queries (i : Int) ≤ coverCount queries' (i : Int)), ∃ r, is_zero_array nums queries' = ok r ∧ r = true) := by
  sorry

/-- For every query list q' satisfying the same query preconditions with respect to len(nums), if for every integer i with 0 <= i < len(nums) the number of j with 0 <= j < len(queries) and queries[j][0] <= i <= queries[j][1] equals the number of j with 0 <= j < len(q') and q'[j][0] <= i <= q'[j][1], then whenever both calls is_zero_array nums queries and is_zero_array nums q' return results, the two results are equal.
  Preconditions: len(nums) is an integer with 1 <= len(nums) <= 100000; for every integer i with 0 <= i < len(nums), nums[i] is an integer with 0 <= nums[i] <= 100000; len(queries) is an integer with 1 <= len(queries) <= 100000; for every integer j with 0 <= j < len(queries), len(queries[j]) = 2, queries[j][0] and queries[j][1] are integers, and 0 <= queries[j][0] <= queries[j][1] < len(nums). -/
theorem spec_13
    (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hnums_len : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hnums : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (hqueries_len : 1 ≤ queries.val.length ∧ queries.val.length ≤ 100000)
    (hqueries : ∀ (j : Nat) (hj : j < queries.val.length),
      (queries.val[j]).val.length = 2 ∧
        0 ≤ queryStart queries j ∧ queryStart queries j ≤ queryEnd queries j ∧
          queryEnd queries j < (nums.val.length : Int))
    (queries' : Slice (alloc.vec.Vec Std.I64))
    (hqueries'_len : 1 ≤ queries'.val.length ∧ queries'.val.length ≤ 100000)
    (hqueries' : ∀ (j : Nat) (hj : j < queries'.val.length),
      (queries'.val[j]).val.length = 2 ∧
        0 ≤ queryStart queries' j ∧ queryStart queries' j ≤ queryEnd queries' j ∧
          queryEnd queries' j < (nums.val.length : Int))
    (hcov : ∀ (i : Nat) (hi : i < nums.val.length),
      coverCount queries (i : Int) = coverCount queries' (i : Int))
    (r r' : Bool)
    (hr : is_zero_array nums queries = ok r)
    (hr' : is_zero_array nums queries' = ok r') :
    r = r' := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hnums_len : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hnums : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (hqueries_len : 1 ≤ queries.val.length ∧ queries.val.length ≤ 100000)
    (hqueries : ∀ (j : Nat) (hj : j < queries.val.length),
      (queries.val[j]).val.length = 2 ∧
        0 ≤ queryStart queries j ∧ queryStart queries j ≤ queryEnd queries j ∧
          queryEnd queries j < (nums.val.length : Int))
    (queries' : Slice (alloc.vec.Vec Std.I64))
    (hqueries'_len : 1 ≤ queries'.val.length ∧ queries'.val.length ≤ 100000)
    (hqueries' : ∀ (j : Nat) (hj : j < queries'.val.length),
      (queries'.val[j]).val.length = 2 ∧
        0 ≤ queryStart queries' j ∧ queryStart queries' j ≤ queryEnd queries' j ∧
          queryEnd queries' j < (nums.val.length : Int))
    (hcov : ∀ (i : Nat) (hi : i < nums.val.length),
      coverCount queries (i : Int) = coverCount queries' (i : Int))
    (r r' : Bool)
    (hr : is_zero_array nums queries = ok r)
    (hr' : is_zero_array nums queries' = ok r'), r = r') := by
  sorry

end AegisSpec.IsZeroArray
