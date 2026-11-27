import Aegis.ResultArray.Code.Funs

/-!
# Specifications of `Aegis.ResultArray.result_array`

LeetCode problem `distribute-elements-into-two-arrays-i`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.ResultArray (result_array)

namespace AegisSpec.ResultArray

def vals (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

def outVals (r : alloc.vec.Vec Std.I64) : List Int := r.val.map (fun x => x.val)

def valueAt (vs : List Int) (i : Nat) : Int := vs.getD i 0

def posOf (v : Int) (l : List Int) : Nat := l.idxOf v

def occursInB (v : Int) (l : List Int) : Bool := Nat.blt (posOf v l) l.length

def beforeB (v w : Int) (l : List Int) : Bool :=
  occursInB v l && occursInB w l && Nat.blt (posOf v l) (posOf w l)

def atOrAfterB (v w : Int) (l : List Int) : Bool :=
  occursInB v l && occursInB w l && Nat.ble (posOf w l) (posOf v l)

def occursIn (v : Int) (l : List Int) : Prop := occursInB v l = true

def beforeIn (v w : Int) (l : List Int) : Prop := beforeB v w l = true

def atOrAfterIn (v w : Int) (l : List Int) : Prop := atOrAfterB v w l = true

def beforePart (w : Int) (l : List Int) : List Int := l.take (posOf w l)

def fromPart (w : Int) (l : List Int) : List Int := l.drop (posOf w l)

def splitStep (vs : List Int) (s : List Nat × List Nat × Int × Int) (i : Nat) :
    List Nat × List Nat × Int × Int :=
  let a := s.1
  let b := s.2.1
  let la := s.2.2.1
  let lb := s.2.2.2
  let v := valueAt vs i
  if la > lb then (a ++ [i], b, v, lb) else (a, b ++ [i], la, v)

def splitIdx (vs : List Int) : List Nat × List Nat :=
  match vs with
  | x :: y :: _ =>
    let s : List Nat × List Nat × Int × Int :=
      (List.range (vs.length - 2)).foldl (fun s k => splitStep vs s (k + 2)) ([0], [1], x, y)
    (s.1, s.2.1)
  | _ => ([0], [1])

def splitVals (vs : List Int) : List Int × List Int :=
  ((splitIdx vs).1.filterMap (fun i => vs[i]?), (splitIdx vs).2.filterMap (fun i => vs[i]?))

def StrictInc (l : List Nat) : Prop := l.Pairwise (fun a b => a < b)

def maxOf (l : List Nat) : Nat := l.foldr (fun a b => Nat.max a b) 0

def lastBelow (vs : List Int) (l : List Nat) (i : Nat) : Int :=
  valueAt vs (maxOf ((List.range i).filter (fun p => l.elem p)))

def beforeCand (vs rv : List Int) (i : Nat) : List Nat :=
  (List.range i).filter (fun p => beforeB (valueAt vs p) (valueAt vs 1) rv)

def afterCand (vs rv : List Int) (i : Nat) : List Nat :=
  (List.range i).filter (fun q => atOrAfterB (valueAt vs q) (valueAt vs 1) rv)

def lastBefore (vs rv : List Int) (i : Nat) : Int := valueAt vs (maxOf (beforeCand vs rv i))

def lastAtOrAfter (vs rv : List Int) (i : Nat) : Int := valueAt vs (maxOf (afterCand vs rv i))

/-- Define two sequences of indices A and B as follows. Initialize A = [0] and B = [1]. For i = 2, 3, ..., len(nums)-1 in increasing order, let a be the last element of A and b the last element of B. If nums[a] > nums[b], append i to A; otherwise append i to B. Let arr1 be the sequence [nums[i] for i in A] (in the order of A, which is increasing) and arr2 be [nums[i] for i in B]. The function returns a result r such that len(r) = len(nums) and r is the concatenation arr1 ++ arr2.
  Preconditions: len(nums) >= 3, len(nums) <= 50, all elements of nums are distinct, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
theorem spec_1 (nums : Slice Std.I64)
    (hlen3 : 3 ≤ (vals nums).length) (hlen50 : (vals nums).length ≤ 50)
    (hnd : (vals nums).Nodup)
    (hrange : ∀ (i : Nat) (h : i < (vals nums).length),
      1 ≤ (vals nums).get ⟨i, h⟩ ∧ (vals nums).get ⟨i, h⟩ ≤ 100) :
    ∃ r, result_array nums = ok r ∧
      (outVals r).length = (vals nums).length ∧
      outVals r = (splitVals (vals nums)).1 ++ (splitVals (vals nums)).2 := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen3 : 3 ≤ (vals nums).length) (hlen50 : (vals nums).length ≤ 50)
    (hnd : (vals nums).Nodup)
    (hrange : ∀ (i : Nat) (h : i < (vals nums).length),
      1 ≤ (vals nums).get ⟨i, h⟩ ∧ (vals nums).get ⟨i, h⟩ ≤ 100), ∃ r, result_array nums = ok r ∧
      (outVals r).length = (vals nums).length ∧
      outVals r = (splitVals (vals nums)).1 ++ (splitVals (vals nums)).2) := by
  sorry

/-- The function returns a result r and len(r) = len(nums).
  Preconditions: len(nums) >= 3, len(nums) <= 50, all elements of nums are distinct, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
theorem spec_2 (nums : Slice Std.I64)
    (hlen3 : 3 ≤ (vals nums).length) (hlen50 : (vals nums).length ≤ 50)
    (hnd : (vals nums).Nodup)
    (hrange : ∀ (i : Nat) (h : i < (vals nums).length),
      1 ≤ (vals nums).get ⟨i, h⟩ ∧ (vals nums).get ⟨i, h⟩ ≤ 100) :
    ∃ r, result_array nums = ok r ∧ (outVals r).length = (vals nums).length := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen3 : 3 ≤ (vals nums).length) (hlen50 : (vals nums).length ≤ 50)
    (hnd : (vals nums).Nodup)
    (hrange : ∀ (i : Nat) (h : i < (vals nums).length),
      1 ≤ (vals nums).get ⟨i, h⟩ ∧ (vals nums).get ⟨i, h⟩ ≤ 100), ∃ r, result_array nums = ok r ∧ (outVals r).length = (vals nums).length) := by
  sorry

/-- The function returns a result r and for every j with 0 <= j < len(r), 1 <= r[j] <= 100.
  Preconditions: len(nums) >= 3, len(nums) <= 50, all elements of nums are distinct, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
theorem spec_3 (nums : Slice Std.I64)
    (hlen3 : 3 ≤ (vals nums).length) (hlen50 : (vals nums).length ≤ 50)
    (hnd : (vals nums).Nodup)
    (hrange : ∀ (i : Nat) (h : i < (vals nums).length),
      1 ≤ (vals nums).get ⟨i, h⟩ ∧ (vals nums).get ⟨i, h⟩ ≤ 100) :
    ∃ r, result_array nums = ok r ∧
      ∀ (j : Nat) (h : j < (outVals r).length),
        1 ≤ (outVals r).get ⟨j, h⟩ ∧ (outVals r).get ⟨j, h⟩ ≤ 100 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen3 : 3 ≤ (vals nums).length) (hlen50 : (vals nums).length ≤ 50)
    (hnd : (vals nums).Nodup)
    (hrange : ∀ (i : Nat) (h : i < (vals nums).length),
      1 ≤ (vals nums).get ⟨i, h⟩ ∧ (vals nums).get ⟨i, h⟩ ≤ 100), ∃ r, result_array nums = ok r ∧
      ∀ (j : Nat) (h : j < (outVals r).length),
        1 ≤ (outVals r).get ⟨j, h⟩ ∧ (outVals r).get ⟨j, h⟩ ≤ 100) := by
  sorry

/-- The function returns a result r and r[0] = nums[0].
  Preconditions: len(nums) >= 3, len(nums) <= 50, all elements of nums are distinct, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
theorem spec_4 (nums : Slice Std.I64)
    (hlen3 : 3 ≤ (vals nums).length) (hlen50 : (vals nums).length ≤ 50)
    (hnd : (vals nums).Nodup)
    (hrange : ∀ (i : Nat) (h : i < (vals nums).length),
      1 ≤ (vals nums).get ⟨i, h⟩ ∧ (vals nums).get ⟨i, h⟩ ≤ 100) :
    ∃ r, result_array nums = ok r ∧ (outVals r)[0]? = (vals nums)[0]? := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen3 : 3 ≤ (vals nums).length) (hlen50 : (vals nums).length ≤ 50)
    (hnd : (vals nums).Nodup)
    (hrange : ∀ (i : Nat) (h : i < (vals nums).length),
      1 ≤ (vals nums).get ⟨i, h⟩ ∧ (vals nums).get ⟨i, h⟩ ≤ 100), ∃ r, result_array nums = ok r ∧ (outVals r)[0]? = (vals nums)[0]?) := by
  sorry

/-- The function returns a result r and there exists an integer k with 1 <= k <= len(nums)-1 such that: (1) r[0..k-1] is a subsequence of nums, i.e., there exist indices 0 <= i_0 < i_1 < ... < i_{k-1} < len(nums) with r[j] = nums[i_j] for 0 <= j < k; (2) r[k..len(nums)-1] is a subsequence of nums; (3) r[0] = nums[0]; (4) r[k] = nums[1]; (5) the multiset of values in r[0..k-1] together with the multiset of values in r[k..len(nums)-1] equals the multiset of values in nums.
  Preconditions: len(nums) >= 3, len(nums) <= 50, all elements of nums are distinct, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
theorem spec_5 (nums : Slice Std.I64)
    (hlen3 : 3 ≤ (vals nums).length) (hlen50 : (vals nums).length ≤ 50)
    (hnd : (vals nums).Nodup)
    (hrange : ∀ (i : Nat) (h : i < (vals nums).length),
      1 ≤ (vals nums).get ⟨i, h⟩ ∧ (vals nums).get ⟨i, h⟩ ≤ 100) :
    ∃ r, result_array nums = ok r ∧
      ∃ k : Nat, 1 ≤ k ∧ k ≤ (vals nums).length - 1 ∧
        ((outVals r).take k).Sublist (vals nums) ∧
        ((outVals r).drop k).Sublist (vals nums) ∧
        (outVals r)[0]? = (vals nums)[0]? ∧
        (outVals r)[k]? = (vals nums)[1]? ∧
        ∀ v : Int,
          (((outVals r).take k) ++ ((outVals r).drop k)).count v = (vals nums).count v := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen3 : 3 ≤ (vals nums).length) (hlen50 : (vals nums).length ≤ 50)
    (hnd : (vals nums).Nodup)
    (hrange : ∀ (i : Nat) (h : i < (vals nums).length),
      1 ≤ (vals nums).get ⟨i, h⟩ ∧ (vals nums).get ⟨i, h⟩ ≤ 100), ∃ r, result_array nums = ok r ∧
      ∃ k : Nat, 1 ≤ k ∧ k ≤ (vals nums).length - 1 ∧
        ((outVals r).take k).Sublist (vals nums) ∧
        ((outVals r).drop k).Sublist (vals nums) ∧
        (outVals r)[0]? = (vals nums)[0]? ∧
        (outVals r)[k]? = (vals nums)[1]? ∧
        ∀ v : Int,
          (((outVals r).take k) ++ ((outVals r).drop k)).count v = (vals nums).count v) := by
  sorry

/-- The function returns a result r, and for every i with 2 <= i < len(nums), let p be the largest index with 0 <= p < i such that nums[p] appears before nums[1] in r, and let q be the largest index with 0 <= q < i such that nums[q] appears at or after nums[1] in r. Then nums[i] appears before nums[1] in r if and only if nums[p] > nums[q].
  Preconditions: len(nums) >= 3, len(nums) <= 50, all elements of nums are distinct, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
theorem spec_6 (nums : Slice Std.I64)
    (hlen3 : 3 ≤ (vals nums).length) (hlen50 : (vals nums).length ≤ 50)
    (hnd : (vals nums).Nodup)
    (hrange : ∀ (i : Nat) (h : i < (vals nums).length),
      1 ≤ (vals nums).get ⟨i, h⟩ ∧ (vals nums).get ⟨i, h⟩ ≤ 100) :
    ∃ r, result_array nums = ok r ∧
      ∀ i : Nat, 2 ≤ i → i < (vals nums).length →
        (beforeIn (valueAt (vals nums) i) (valueAt (vals nums) 1) (outVals r) ↔
          lastBefore (vals nums) (outVals r) i > lastAtOrAfter (vals nums) (outVals r) i) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen3 : 3 ≤ (vals nums).length) (hlen50 : (vals nums).length ≤ 50)
    (hnd : (vals nums).Nodup)
    (hrange : ∀ (i : Nat) (h : i < (vals nums).length),
      1 ≤ (vals nums).get ⟨i, h⟩ ∧ (vals nums).get ⟨i, h⟩ ≤ 100), ∃ r, result_array nums = ok r ∧
      ∀ i : Nat, 2 ≤ i → i < (vals nums).length →
        (beforeIn (valueAt (vals nums) i) (valueAt (vals nums) 1) (outVals r) ↔
          lastBefore (vals nums) (outVals r) i > lastAtOrAfter (vals nums) (outVals r) i)) := by
  sorry

/-- The function returns a result r, and the subsequence of r consisting of all elements that appear before nums[1] is a subsequence of nums, and the subsequence of r consisting of nums[1] and all elements after it is also a subsequence of nums.
  Preconditions: len(nums) >= 3, len(nums) <= 50, all elements of nums are distinct, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
theorem spec_7 (nums : Slice Std.I64)
    (hlen3 : 3 ≤ (vals nums).length) (hlen50 : (vals nums).length ≤ 50)
    (hnd : (vals nums).Nodup)
    (hrange : ∀ (i : Nat) (h : i < (vals nums).length),
      1 ≤ (vals nums).get ⟨i, h⟩ ∧ (vals nums).get ⟨i, h⟩ ≤ 100) :
    ∃ r, result_array nums = ok r ∧
      (beforePart (valueAt (vals nums) 1) (outVals r)).Sublist (vals nums) ∧
      (fromPart (valueAt (vals nums) 1) (outVals r)).Sublist (vals nums) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen3 : 3 ≤ (vals nums).length) (hlen50 : (vals nums).length ≤ 50)
    (hnd : (vals nums).Nodup)
    (hrange : ∀ (i : Nat) (h : i < (vals nums).length),
      1 ≤ (vals nums).get ⟨i, h⟩ ∧ (vals nums).get ⟨i, h⟩ ≤ 100), ∃ r, result_array nums = ok r ∧
      (beforePart (valueAt (vals nums) 1) (outVals r)).Sublist (vals nums) ∧
      (fromPart (valueAt (vals nums) 1) (outVals r)).Sublist (vals nums)) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r (i.e., it does not fail).
  Preconditions: len(nums) >= 3, len(nums) <= 50, all elements of nums are distinct, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
theorem spec_8 (nums : Slice Std.I64)
    (hlen3 : 3 ≤ (vals nums).length) (hlen50 : (vals nums).length ≤ 50)
    (hnd : (vals nums).Nodup)
    (hrange : ∀ (i : Nat) (h : i < (vals nums).length),
      1 ≤ (vals nums).get ⟨i, h⟩ ∧ (vals nums).get ⟨i, h⟩ ≤ 100) :
    ∃ r, result_array nums = ok r := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen3 : 3 ≤ (vals nums).length) (hlen50 : (vals nums).length ≤ 50)
    (hnd : (vals nums).Nodup)
    (hrange : ∀ (i : Nat) (h : i < (vals nums).length),
      1 ≤ (vals nums).get ⟨i, h⟩ ∧ (vals nums).get ⟨i, h⟩ ≤ 100), ∃ r, result_array nums = ok r) := by
  sorry

/-- The function returns a result r and for every value v, the number of occurrences of v in r equals the number of occurrences of v in nums.
  Preconditions: len(nums) >= 3, len(nums) <= 50, all elements of nums are distinct, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
theorem spec_9 (nums : Slice Std.I64)
    (hlen3 : 3 ≤ (vals nums).length) (hlen50 : (vals nums).length ≤ 50)
    (hnd : (vals nums).Nodup)
    (hrange : ∀ (i : Nat) (h : i < (vals nums).length),
      1 ≤ (vals nums).get ⟨i, h⟩ ∧ (vals nums).get ⟨i, h⟩ ≤ 100) :
    ∃ r, result_array nums = ok r ∧ ∀ v : Int, (outVals r).count v = (vals nums).count v := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen3 : 3 ≤ (vals nums).length) (hlen50 : (vals nums).length ≤ 50)
    (hnd : (vals nums).Nodup)
    (hrange : ∀ (i : Nat) (h : i < (vals nums).length),
      1 ≤ (vals nums).get ⟨i, h⟩ ∧ (vals nums).get ⟨i, h⟩ ≤ 100), ∃ r, result_array nums = ok r ∧ ∀ v : Int, (outVals r).count v = (vals nums).count v) := by
  sorry

/-- The function returns a result r and there exist two sequences A and B of indices (each in increasing order) such that A and B partition {0,1,...,len(nums)-1}, 0 is in A, 1 is in B, for every i with 2 <= i < len(nums), i is in A if and only if nums[max(A ∩ {0,...,i-1})] > nums[max(B ∩ {0,...,i-1})], and r = [nums[i] for i in A] ++ [nums[i] for i in B].
  Preconditions: len(nums) >= 3, len(nums) <= 50, all elements of nums are distinct, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
theorem spec_10 (nums : Slice Std.I64)
    (hlen3 : 3 ≤ (vals nums).length) (hlen50 : (vals nums).length ≤ 50)
    (hnd : (vals nums).Nodup)
    (hrange : ∀ (i : Nat) (h : i < (vals nums).length),
      1 ≤ (vals nums).get ⟨i, h⟩ ∧ (vals nums).get ⟨i, h⟩ ≤ 100) :
    ∃ r, result_array nums = ok r ∧
      ∃ A B : List Nat,
        StrictInc A ∧ StrictInc B ∧
        (A ++ B).Perm (List.range (vals nums).length) ∧
        0 ∈ A ∧ 1 ∈ B ∧
        (∀ i : Nat, 2 ≤ i → i < (vals nums).length →
          (i ∈ A ↔ lastBelow (vals nums) A i > lastBelow (vals nums) B i)) ∧
        outVals r = (A.filterMap (fun i => (vals nums)[i]?)) ++
          (B.filterMap (fun i => (vals nums)[i]?)) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen3 : 3 ≤ (vals nums).length) (hlen50 : (vals nums).length ≤ 50)
    (hnd : (vals nums).Nodup)
    (hrange : ∀ (i : Nat) (h : i < (vals nums).length),
      1 ≤ (vals nums).get ⟨i, h⟩ ∧ (vals nums).get ⟨i, h⟩ ≤ 100), ∃ r, result_array nums = ok r ∧
      ∃ A B : List Nat,
        StrictInc A ∧ StrictInc B ∧
        (A ++ B).Perm (List.range (vals nums).length) ∧
        0 ∈ A ∧ 1 ∈ B ∧
        (∀ i : Nat, 2 ≤ i → i < (vals nums).length →
          (i ∈ A ↔ lastBelow (vals nums) A i > lastBelow (vals nums) B i)) ∧
        outVals r = (A.filterMap (fun i => (vals nums)[i]?)) ++
          (B.filterMap (fun i => (vals nums)[i]?))) := by
  sorry

end AegisSpec.ResultArray
