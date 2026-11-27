import Aegis.ResultArray.Code.Funs

/-!
# Specifications of `Aegis.ResultArray.result_array`

LeetCode problem `distribute-elements-into-two-arrays-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result Aegis.ResultArray

namespace AegisSpec.ResultArray

def ints (l : List Std.I64) : List Int := l.map (fun x => x.val)

def valAt (l : List Std.I64) (i : Nat) : Int := (l.getD i 0#i64).val

def countGt (l : List Int) (x : Int) : Nat := (l.filter (fun y => decide (x < y))).length

def countOcc (l : List Std.I64) (v : Int) : Nat :=
  (l.filter (fun x => decide (x.val = v))).length

def step (arr1 arr2 : List Int) (x : Int) : List Int × List Int :=
  if countGt arr1 x > countGt arr2 x ∨
      (countGt arr1 x = countGt arr2 x ∧ arr1.length ≤ arr2.length) then
    (arr1 ++ [x], arr2)
  else
    (arr1, arr2 ++ [x])

def split : List Int → List Int × List Int
  | a :: b :: rest => rest.foldl (fun p x => step p.1 p.2 x) ([a], [b])
  | _ => ([], [])

def arr1Of (l : List Int) : List Int := (split l).1

def arr2Of (l : List Int) : List Int := (split l).2

def countGtP (l : List (Nat × Int)) (x : Int) : Nat :=
  (l.filter (fun p => decide (x < p.2))).length

def stepIdx (arr1 arr2 : List (Nat × Int)) (i : Nat) (x : Int) :
    List (Nat × Int) × List (Nat × Int) :=
  if countGtP arr1 x > countGtP arr2 x ∨
      (countGtP arr1 x = countGtP arr2 x ∧ arr1.length ≤ arr2.length) then
    (arr1 ++ [(i, x)], arr2)
  else
    (arr1, arr2 ++ [(i, x)])

def splitIdx : List Int → List (Nat × Int) × List (Nat × Int)
  | a :: b :: rest =>
    (rest.zipIdx 2).foldl (fun p e => stepIdx p.1 p.2 e.2 e.1)
      ([((0 : Nat), a)], [((1 : Nat), b)])
  | _ => ([], [])

def firstIdx (l : List Int) : List Nat := (splitIdx l).1.map Prod.fst

def secondIdx (l : List Int) : List Nat := (splitIdx l).2.map Prod.fst

def pick (l : List Int) (idx : List Nat) : List Int := idx.map (fun i => l.getD i 0)

/-- The function returns a result r and r = A_n ++ B_n, where the sequences A_i and B_i for 2 <= i <= n are defined as follows. Start with A_2 = [nums[0]] and B_2 = [nums[1]]. For each i with 2 <= i < n, let c1 be the number of indices j with 0 <= j < len(A_i) and A_i[j] > nums[i], and let c2 be the number of indices j with 0 <= j < len(B_i) and B_i[j] > nums[i]. If c1 > c2, or if c1 = c2 and len(A_i) <= len(B_i), then set A_{i+1} = A_i ++ [nums[i]] and B_{i+1} = B_i; otherwise set A_{i+1} = A_i and B_{i+1} = B_i ++ [nums[i]]. Here A_n is the final arr1, B_n is the final arr2, and r is their concatenation.
  Preconditions: Let n = len(nums). Assume 3 <= n <= 10^5 and, for every i with 0 <= i < n, 1 <= nums[i] <= 10^9. This specification uses 0-based indices for the Lean slice nums; the problem statement's 1-based nums[k] is nums[k-1] here. -/
theorem spec_1 (nums : Slice Std.I64)
    (hn : 3 ≤ nums.val.length) (hnmax : nums.val.length ≤ 100000)
    (hval : ∀ i, i < nums.val.length → 1 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 1000000000) :
    ∃ r : alloc.vec.Vec Std.I64,
      result_array nums = ok r ∧
        ints r.val = arr1Of (ints nums.val) ++ arr2Of (ints nums.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn : 3 ≤ nums.val.length) (hnmax : nums.val.length ≤ 100000)
    (hval : ∀ i, i < nums.val.length → 1 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 1000000000), ∃ r : alloc.vec.Vec Std.I64,
      result_array nums = ok r ∧
        ints r.val = arr1Of (ints nums.val) ++ arr2Of (ints nums.val)) := by
  sorry

/-- The function returns a result r for every input satisfying the preconditions; it does not fail with integer overflow, out-of-bounds access, or panic.
  Preconditions: Let n = len(nums). Assume 3 <= n <= 10^5 and, for every i with 0 <= i < n, 1 <= nums[i] <= 10^9. -/
theorem spec_2 (nums : Slice Std.I64)
    (hn : 3 ≤ nums.val.length) (hnmax : nums.val.length ≤ 100000)
    (hval : ∀ i, i < nums.val.length → 1 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 1000000000) :
    ∃ r : alloc.vec.Vec Std.I64, result_array nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn : 3 ≤ nums.val.length) (hnmax : nums.val.length ≤ 100000)
    (hval : ∀ i, i < nums.val.length → 1 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 1000000000), ∃ r : alloc.vec.Vec Std.I64, result_array nums = ok r) := by
  sorry

/-- Whenever the function returns a result r, len(r) = len(nums).
  Preconditions: Let n = len(nums). Assume 3 <= n <= 10^5 and, for every i with 0 <= i < n, 1 <= nums[i] <= 10^9. -/
theorem spec_3 (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
    (hn : 3 ≤ nums.val.length) (hnmax : nums.val.length ≤ 100000)
    (hval : ∀ i, i < nums.val.length → 1 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 1000000000)
    (hres : result_array nums = ok r) :
    r.val.length = nums.val.length := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
    (hn : 3 ≤ nums.val.length) (hnmax : nums.val.length ≤ 100000)
    (hval : ∀ i, i < nums.val.length → 1 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 1000000000)
    (hres : result_array nums = ok r), r.val.length = nums.val.length) := by
  sorry

/-- Whenever the function returns a result r, for every integer v, the number of indices j with 0 <= j < len(r) and r[j] = v equals the number of indices i with 0 <= i < len(nums) and nums[i] = v.
  Preconditions: Let n = len(nums). Assume 3 <= n <= 10^5 and, for every i with 0 <= i < n, 1 <= nums[i] <= 10^9. -/
theorem spec_4 (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
    (hn : 3 ≤ nums.val.length) (hnmax : nums.val.length ≤ 100000)
    (hval : ∀ i, i < nums.val.length → 1 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 1000000000)
    (hres : result_array nums = ok r) :
    ∀ v : Int, countOcc r.val v = countOcc nums.val v := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
    (hn : 3 ≤ nums.val.length) (hnmax : nums.val.length ≤ 100000)
    (hval : ∀ i, i < nums.val.length → 1 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 1000000000)
    (hres : result_array nums = ok r), ∀ v : Int, countOcc r.val v = countOcc nums.val v) := by
  sorry

/-- Whenever the function returns a result r, len(r) >= 1 and r[0] = nums[0].
  Preconditions: Let n = len(nums). Assume 3 <= n <= 10^5 and, for every i with 0 <= i < n, 1 <= nums[i] <= 10^9. -/
theorem spec_5 (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
    (hn : 3 ≤ nums.val.length) (hnmax : nums.val.length ≤ 100000)
    (hval : ∀ i, i < nums.val.length → 1 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 1000000000)
    (hres : result_array nums = ok r) :
    1 ≤ r.val.length ∧ valAt r.val 0 = valAt nums.val 0 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
    (hn : 3 ≤ nums.val.length) (hnmax : nums.val.length ≤ 100000)
    (hval : ∀ i, i < nums.val.length → 1 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 1000000000)
    (hres : result_array nums = ok r), 1 ≤ r.val.length ∧ valAt r.val 0 = valAt nums.val 0) := by
  sorry

/-- Let A and B be the final arr1 and arr2 produced by the deterministic operation described in spec_1. Whenever the function returns r, there exists an integer p with 1 <= p <= len(nums)-1 such that r[0..p) = A and r[p..len(r)) = B.
  Preconditions: Let n = len(nums). Assume 3 <= n <= 10^5 and, for every i with 0 <= i < n, 1 <= nums[i] <= 10^9. -/
theorem spec_6 (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
    (hn : 3 ≤ nums.val.length) (hnmax : nums.val.length ≤ 100000)
    (hval : ∀ i, i < nums.val.length → 1 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 1000000000)
    (hres : result_array nums = ok r) :
    ∃ p : Nat,
      1 ≤ p ∧ p ≤ nums.val.length - 1 ∧
        (ints r.val).take p = arr1Of (ints nums.val) ∧
          (ints r.val).drop p = arr2Of (ints nums.val) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
    (hn : 3 ≤ nums.val.length) (hnmax : nums.val.length ≤ 100000)
    (hval : ∀ i, i < nums.val.length → 1 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 1000000000)
    (hres : result_array nums = ok r), ∃ p : Nat,
      1 ≤ p ∧ p ≤ nums.val.length - 1 ∧
        (ints r.val).take p = arr1Of (ints nums.val) ∧
          (ints r.val).drop p = arr2Of (ints nums.val)) := by
  sorry

/-- Whenever the function returns r, for every j with 0 <= j < len(r), 1 <= r[j] <= 10^9.
  Preconditions: Let n = len(nums). Assume 3 <= n <= 10^5 and, for every i with 0 <= i < n, 1 <= nums[i] <= 10^9. -/
theorem spec_7 (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
    (hn : 3 ≤ nums.val.length) (hnmax : nums.val.length ≤ 100000)
    (hval : ∀ i, i < nums.val.length → 1 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 1000000000)
    (hres : result_array nums = ok r) :
    ∀ j, j < r.val.length → 1 ≤ valAt r.val j ∧ valAt r.val j ≤ 1000000000 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
    (hn : 3 ≤ nums.val.length) (hnmax : nums.val.length ≤ 100000)
    (hval : ∀ i, i < nums.val.length → 1 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 1000000000)
    (hres : result_array nums = ok r), ∀ j, j < r.val.length → 1 ≤ valAt r.val j ∧ valAt r.val j ≤ 1000000000) := by
  sorry

/-- Whenever the function returns r and len(nums) = 3, let a = nums[0], b = nums[1], c = nums[2]. If a <= c < b, then r = [a, b, c]; otherwise r = [a, c, b].
  Preconditions: Let n = len(nums). Assume 3 <= n <= 10^5 and, for every i with 0 <= i < n, 1 <= nums[i] <= 10^9. -/
theorem spec_8 (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
    (hn : 3 ≤ nums.val.length) (hnmax : nums.val.length ≤ 100000)
    (hval : ∀ i, i < nums.val.length → 1 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 1000000000)
    (hres : result_array nums = ok r) (hlen : nums.val.length = 3) :
    (valAt nums.val 0 ≤ valAt nums.val 2 ∧ valAt nums.val 2 < valAt nums.val 1 →
        ints r.val = [valAt nums.val 0, valAt nums.val 1, valAt nums.val 2]) ∧
      (¬ (valAt nums.val 0 ≤ valAt nums.val 2 ∧ valAt nums.val 2 < valAt nums.val 1) →
        ints r.val = [valAt nums.val 0, valAt nums.val 2, valAt nums.val 1]) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
    (hn : 3 ≤ nums.val.length) (hnmax : nums.val.length ≤ 100000)
    (hval : ∀ i, i < nums.val.length → 1 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 1000000000)
    (hres : result_array nums = ok r) (hlen : nums.val.length = 3), (valAt nums.val 0 ≤ valAt nums.val 2 ∧ valAt nums.val 2 < valAt nums.val 1 →
        ints r.val = [valAt nums.val 0, valAt nums.val 1, valAt nums.val 2]) ∧
      (¬ (valAt nums.val 0 ≤ valAt nums.val 2 ∧ valAt nums.val 2 < valAt nums.val 1) →
        ints r.val = [valAt nums.val 0, valAt nums.val 2, valAt nums.val 1])) := by
  sorry

end AegisSpec.ResultArray
