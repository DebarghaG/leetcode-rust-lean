import Aegis.ArraysIntersection.Code.Funs

/-!
# Specifications of `Aegis.ArraysIntersection.arrays_intersection`

LeetCode problem `intersection-of-three-sorted-arrays`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.ArraysIntersection

namespace AegisSpec.ArraysIntersection

def valuesList (l : List Std.I64) : List Int := l.map (fun x => x.val)

def values (arr : Slice Std.I64) : List Int := valuesList arr.val

def vecValues (v : alloc.vec.Vec Std.I64) : List Int := valuesList v.val

def Occurs (x : Int) (arr : Slice Std.I64) : Prop := x ∈ values arr

def OccursV (x : Int) (v : alloc.vec.Vec Std.I64) : Prop := x ∈ vecValues v

def StrictlyIncreasingList (l : List Std.I64) : Prop :=
  ∀ i : Nat, ∀ (_ : i + 1 < l.length), (l[i]).val < (l[i + 1]).val

def StrictlyIncreasing (arr : Slice Std.I64) : Prop := StrictlyIncreasingList arr.val

def StrictlyIncreasingVec (v : alloc.vec.Vec Std.I64) : Prop := StrictlyIncreasingList v.val

def BoundedList (l : List Std.I64) : Prop :=
  ∀ i : Nat, ∀ (_ : i < l.length), 1 ≤ (l[i]).val ∧ (l[i]).val ≤ 2000

def Bounded (arr : Slice Std.I64) : Prop := BoundedList arr.val

def ValidArray (arr : Slice Std.I64) : Prop :=
  1 ≤ arr.val.length ∧ arr.val.length ≤ 1000 ∧ Bounded arr ∧ StrictlyIncreasing arr

def ValidInput (arr1 arr2 arr3 : Slice Std.I64) : Prop :=
  ValidArray arr1 ∧ ValidArray arr2 ∧ ValidArray arr3

def commonValues (arr1 arr2 arr3 : Slice Std.I64) : Finset Int :=
  (values arr1).toFinset ∩ (values arr2).toFinset ∩ (values arr3).toFinset

def IsSubsequence (v : alloc.vec.Vec Std.I64) (arr : Slice Std.I64) : Prop :=
  ∃ g : Fin v.val.length → Fin arr.val.length,
    StrictMono g ∧ ∀ k : Fin v.val.length, (arr.val.get (g k)).val = (v.val.get k).val

def lastOf (v : alloc.vec.Vec Std.I64) (h : 0 < v.val.length) : Std.I64 :=
  v.val.get ⟨v.val.length - 1, Nat.sub_one_lt (Nat.ne_of_gt h)⟩

def PermTriple (a1 a2 a3 b1 b2 b3 : Slice Std.I64) : Prop :=
  (b1 = a1 ∧ b2 = a2 ∧ b3 = a3) ∨
  (b1 = a1 ∧ b2 = a3 ∧ b3 = a2) ∨
  (b1 = a2 ∧ b2 = a1 ∧ b3 = a3) ∨
  (b1 = a2 ∧ b2 = a3 ∧ b3 = a1) ∨
  (b1 = a3 ∧ b2 = a1 ∧ b3 = a2) ∨
  (b1 = a3 ∧ b2 = a2 ∧ b3 = a1)

/-- The function returns Ok v for some vector v, and v is exactly the strictly increasing array of all integers that occur in all three arrays. Formally: (1) for every integer x, x occurs in v (there exists i with 0 <= i < len(v) and v[i] = x) if and only if x occurs in arr1, x occurs in arr2, and x occurs in arr3, where x occurs in an array arr means there exists j with 0 <= j < len(arr) and arr[j] = x; and (2) for every i with 0 <= i < len(v)-1, v[i] < v[i+1].
  Preconditions: arr1, arr2, arr3 are 0-indexed arrays; len(arr1), len(arr2), len(arr3) are each between 1 and 1000 inclusive; every element of arr1, arr2, arr3 is an integer between 1 and 2000 inclusive; and each of arr1, arr2, arr3 is strictly increasing (for each t in {1,2,3} and every i with 0 <= i < len(arrt)-1, arrt[i] < arrt[i+1]). -/
theorem spec_1 (arr1 arr2 arr3 : Slice Std.I64) (h : ValidInput arr1 arr2 arr3) :
    ∃ v : alloc.vec.Vec Std.I64,
      arrays_intersection arr1 arr2 arr3 = ok v ∧
        (∀ x : Int, OccursV x v ↔ Occurs x arr1 ∧ Occurs x arr2 ∧ Occurs x arr3) ∧
        StrictlyIncreasingVec v := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (arr1 arr2 arr3 : Slice Std.I64) (h : ValidInput arr1 arr2 arr3), ∃ v : alloc.vec.Vec Std.I64,
      arrays_intersection arr1 arr2 arr3 = ok v ∧
        (∀ x : Int, OccursV x v ↔ Occurs x arr1 ∧ Occurs x arr2 ∧ Occurs x arr3) ∧
        StrictlyIncreasingVec v) := by
  sorry

/-- The function returns Ok v for some vector v; in particular, it does not return a failure.
  Preconditions: arr1, arr2, arr3 are 0-indexed arrays; len(arr1), len(arr2), len(arr3) are each between 1 and 1000 inclusive; every element of arr1, arr2, arr3 is an integer between 1 and 2000 inclusive; and each of arr1, arr2, arr3 is strictly increasing (for each t in {1,2,3} and every i with 0 <= i < len(arrt)-1, arrt[i] < arrt[i+1]). -/
theorem spec_2 (arr1 arr2 arr3 : Slice Std.I64) (h : ValidInput arr1 arr2 arr3) :
    ∃ v : alloc.vec.Vec Std.I64, arrays_intersection arr1 arr2 arr3 = ok v := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (arr1 arr2 arr3 : Slice Std.I64) (h : ValidInput arr1 arr2 arr3), ∃ v : alloc.vec.Vec Std.I64, arrays_intersection arr1 arr2 arr3 = ok v) := by
  sorry

/-- Whenever the function returns Ok v, for every index i with 0 <= i < len(v), the value v[i] occurs in arr1, occurs in arr2, and occurs in arr3, where x occurs in an array arr means there exists j with 0 <= j < len(arr) and arr[j] = x.
  Preconditions: arr1, arr2, arr3 are 0-indexed arrays; len(arr1), len(arr2), len(arr3) are each between 1 and 1000 inclusive; every element of arr1, arr2, arr3 is an integer between 1 and 2000 inclusive; and each of arr1, arr2, arr3 is strictly increasing (for each t in {1,2,3} and every i with 0 <= i < len(arrt)-1, arrt[i] < arrt[i+1]). -/
theorem spec_3 (arr1 arr2 arr3 : Slice Std.I64) (h : ValidInput arr1 arr2 arr3)
    (v : alloc.vec.Vec Std.I64) (hres : arrays_intersection arr1 arr2 arr3 = ok v) :
    ∀ i : Nat, ∀ (_ : i < v.val.length),
      Occurs (v.val[i]).val arr1 ∧ Occurs (v.val[i]).val arr2 ∧ Occurs (v.val[i]).val arr3 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (arr1 arr2 arr3 : Slice Std.I64) (h : ValidInput arr1 arr2 arr3)
    (v : alloc.vec.Vec Std.I64) (hres : arrays_intersection arr1 arr2 arr3 = ok v), ∀ i : Nat, ∀ (_ : i < v.val.length),
      Occurs (v.val[i]).val arr1 ∧ Occurs (v.val[i]).val arr2 ∧ Occurs (v.val[i]).val arr3) := by
  sorry

/-- Whenever the function returns Ok v, for every integer x, if x occurs in arr1, x occurs in arr2, and x occurs in arr3, then x occurs in v, where x occurs in an array arr means there exists j with 0 <= j < len(arr) and arr[j] = x.
  Preconditions: arr1, arr2, arr3 are 0-indexed arrays; len(arr1), len(arr2), len(arr3) are each between 1 and 1000 inclusive; every element of arr1, arr2, arr3 is an integer between 1 and 2000 inclusive; and each of arr1, arr2, arr3 is strictly increasing (for each t in {1,2,3} and every i with 0 <= i < len(arrt)-1, arrt[i] < arrt[i+1]). -/
theorem spec_4 (arr1 arr2 arr3 : Slice Std.I64) (h : ValidInput arr1 arr2 arr3)
    (v : alloc.vec.Vec Std.I64) (hres : arrays_intersection arr1 arr2 arr3 = ok v) :
    ∀ x : Int, Occurs x arr1 → Occurs x arr2 → Occurs x arr3 → OccursV x v := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (arr1 arr2 arr3 : Slice Std.I64) (h : ValidInput arr1 arr2 arr3)
    (v : alloc.vec.Vec Std.I64) (hres : arrays_intersection arr1 arr2 arr3 = ok v), ∀ x : Int, Occurs x arr1 → Occurs x arr2 → Occurs x arr3 → OccursV x v) := by
  sorry

/-- Whenever the function returns Ok v, v is strictly increasing: for every i with 0 <= i < len(v)-1, v[i] < v[i+1].
  Preconditions: arr1, arr2, arr3 are 0-indexed arrays; len(arr1), len(arr2), len(arr3) are each between 1 and 1000 inclusive; every element of arr1, arr2, arr3 is an integer between 1 and 2000 inclusive; and each of arr1, arr2, arr3 is strictly increasing (for each t in {1,2,3} and every i with 0 <= i < len(arrt)-1, arrt[i] < arrt[i+1]). -/
theorem spec_5 (arr1 arr2 arr3 : Slice Std.I64) (h : ValidInput arr1 arr2 arr3)
    (v : alloc.vec.Vec Std.I64) (hres : arrays_intersection arr1 arr2 arr3 = ok v) :
    StrictlyIncreasingVec v := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (arr1 arr2 arr3 : Slice Std.I64) (h : ValidInput arr1 arr2 arr3)
    (v : alloc.vec.Vec Std.I64) (hres : arrays_intersection arr1 arr2 arr3 = ok v), StrictlyIncreasingVec v) := by
  sorry

/-- Whenever the function returns Ok v, every element of v lies between 1 and 2000 inclusive: for every i with 0 <= i < len(v), 1 <= v[i] <= 2000.
  Preconditions: arr1, arr2, arr3 are 0-indexed arrays; len(arr1), len(arr2), len(arr3) are each between 1 and 1000 inclusive; every element of arr1, arr2, arr3 is an integer between 1 and 2000 inclusive; and each of arr1, arr2, arr3 is strictly increasing (for each t in {1,2,3} and every i with 0 <= i < len(arrt)-1, arrt[i] < arrt[i+1]). -/
theorem spec_6 (arr1 arr2 arr3 : Slice Std.I64) (h : ValidInput arr1 arr2 arr3)
    (v : alloc.vec.Vec Std.I64) (hres : arrays_intersection arr1 arr2 arr3 = ok v) :
    ∀ i : Nat, ∀ (_ : i < v.val.length), 1 ≤ (v.val[i]).val ∧ (v.val[i]).val ≤ 2000 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (arr1 arr2 arr3 : Slice Std.I64) (h : ValidInput arr1 arr2 arr3)
    (v : alloc.vec.Vec Std.I64) (hres : arrays_intersection arr1 arr2 arr3 = ok v), ∀ i : Nat, ∀ (_ : i < v.val.length), 1 ≤ (v.val[i]).val ∧ (v.val[i]).val ≤ 2000) := by
  sorry

/-- Whenever the function returns Ok v, len(v) <= len(arr1), len(v) <= len(arr2), and len(v) <= len(arr3).
  Preconditions: arr1, arr2, arr3 are 0-indexed arrays; len(arr1), len(arr2), len(arr3) are each between 1 and 1000 inclusive; every element of arr1, arr2, arr3 is an integer between 1 and 2000 inclusive; and each of arr1, arr2, arr3 is strictly increasing (for each t in {1,2,3} and every i with 0 <= i < len(arrt)-1, arrt[i] < arrt[i+1]). -/
theorem spec_7 (arr1 arr2 arr3 : Slice Std.I64) (h : ValidInput arr1 arr2 arr3)
    (v : alloc.vec.Vec Std.I64) (hres : arrays_intersection arr1 arr2 arr3 = ok v) :
    v.val.length ≤ arr1.val.length ∧ v.val.length ≤ arr2.val.length ∧
      v.val.length ≤ arr3.val.length := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (arr1 arr2 arr3 : Slice Std.I64) (h : ValidInput arr1 arr2 arr3)
    (v : alloc.vec.Vec Std.I64) (hres : arrays_intersection arr1 arr2 arr3 = ok v), v.val.length ≤ arr1.val.length ∧ v.val.length ≤ arr2.val.length ∧
      v.val.length ≤ arr3.val.length) := by
  sorry

/-- Whenever the function returns Ok v, len(v) = 0 if and only if there is no integer x such that x occurs in arr1, x occurs in arr2, and x occurs in arr3, where x occurs in an array arr means there exists j with 0 <= j < len(arr) and arr[j] = x.
  Preconditions: arr1, arr2, arr3 are 0-indexed arrays; len(arr1), len(arr2), len(arr3) are each between 1 and 1000 inclusive; every element of arr1, arr2, arr3 is an integer between 1 and 2000 inclusive; and each of arr1, arr2, arr3 is strictly increasing (for each t in {1,2,3} and every i with 0 <= i < len(arrt)-1, arrt[i] < arrt[i+1]). -/
theorem spec_8 (arr1 arr2 arr3 : Slice Std.I64) (h : ValidInput arr1 arr2 arr3)
    (v : alloc.vec.Vec Std.I64) (hres : arrays_intersection arr1 arr2 arr3 = ok v) :
    (v.val.length = 0 ↔
      ¬ ∃ x : Int, Occurs x arr1 ∧ Occurs x arr2 ∧ Occurs x arr3) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (arr1 arr2 arr3 : Slice Std.I64) (h : ValidInput arr1 arr2 arr3)
    (v : alloc.vec.Vec Std.I64) (hres : arrays_intersection arr1 arr2 arr3 = ok v), (v.val.length = 0 ↔
      ¬ ∃ x : Int, Occurs x arr1 ∧ Occurs x arr2 ∧ Occurs x arr3)) := by
  sorry

/-- Whenever the function returns Ok v, len(v) is the number of integers x such that x occurs in arr1, x occurs in arr2, and x occurs in arr3, where x occurs in an array arr means there exists j with 0 <= j < len(arr) and arr[j] = x.
  Preconditions: arr1, arr2, arr3 are 0-indexed arrays; len(arr1), len(arr2), len(arr3) are each between 1 and 1000 inclusive; every element of arr1, arr2, arr3 is an integer between 1 and 2000 inclusive; and each of arr1, arr2, arr3 is strictly increasing (for each t in {1,2,3} and every i with 0 <= i < len(arrt)-1, arrt[i] < arrt[i+1]). -/
theorem spec_9 (arr1 arr2 arr3 : Slice Std.I64) (h : ValidInput arr1 arr2 arr3)
    (v : alloc.vec.Vec Std.I64) (hres : arrays_intersection arr1 arr2 arr3 = ok v) :
    v.val.length = (commonValues arr1 arr2 arr3).card := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (arr1 arr2 arr3 : Slice Std.I64) (h : ValidInput arr1 arr2 arr3)
    (v : alloc.vec.Vec Std.I64) (hres : arrays_intersection arr1 arr2 arr3 = ok v), v.val.length = (commonValues arr1 arr2 arr3).card) := by
  sorry

/-- Whenever the function returns Ok v, for each t in {1,2,3}, v is a subsequence of arrt: there exist indices j_0, j_1, ..., j_{len(v)-1} such that 0 <= j_0 < j_1 < ... < j_{len(v)-1} < len(arrt) and v[k] = arrt[j_k] for every k with 0 <= k < len(v). For len(v)=0 this condition is vacuous.
  Preconditions: arr1, arr2, arr3 are 0-indexed arrays; len(arr1), len(arr2), len(arr3) are each between 1 and 1000 inclusive; every element of arr1, arr2, arr3 is an integer between 1 and 2000 inclusive; and each of arr1, arr2, arr3 is strictly increasing (for each t in {1,2,3} and every i with 0 <= i < len(arrt)-1, arrt[i] < arrt[i+1]). -/
theorem spec_10 (arr1 arr2 arr3 : Slice Std.I64) (h : ValidInput arr1 arr2 arr3)
    (v : alloc.vec.Vec Std.I64) (hres : arrays_intersection arr1 arr2 arr3 = ok v) :
    IsSubsequence v arr1 ∧ IsSubsequence v arr2 ∧ IsSubsequence v arr3 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (arr1 arr2 arr3 : Slice Std.I64) (h : ValidInput arr1 arr2 arr3)
    (v : alloc.vec.Vec Std.I64) (hres : arrays_intersection arr1 arr2 arr3 = ok v), IsSubsequence v arr1 ∧ IsSubsequence v arr2 ∧ IsSubsequence v arr3) := by
  sorry

/-- Whenever the function returns Ok v and len(v) > 0, v[0] occurs in arr1, occurs in arr2, and occurs in arr3, and for every integer x that occurs in all three arrays, v[0] <= x, where x occurs in an array arr means there exists j with 0 <= j < len(arr) and arr[j] = x.
  Preconditions: arr1, arr2, arr3 are 0-indexed arrays; len(arr1), len(arr2), len(arr3) are each between 1 and 1000 inclusive; every element of arr1, arr2, arr3 is an integer between 1 and 2000 inclusive; and each of arr1, arr2, arr3 is strictly increasing (for each t in {1,2,3} and every i with 0 <= i < len(arrt)-1, arrt[i] < arrt[i+1]). -/
theorem spec_11 (arr1 arr2 arr3 : Slice Std.I64) (h : ValidInput arr1 arr2 arr3)
    (v : alloc.vec.Vec Std.I64) (hres : arrays_intersection arr1 arr2 arr3 = ok v)
    (hne : 0 < v.val.length) :
    Occurs (v.val.get ⟨0, hne⟩).val arr1 ∧ Occurs (v.val.get ⟨0, hne⟩).val arr2 ∧
      Occurs (v.val.get ⟨0, hne⟩).val arr3 ∧
      ∀ x : Int, Occurs x arr1 → Occurs x arr2 → Occurs x arr3 →
        (v.val.get ⟨0, hne⟩).val ≤ x := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (arr1 arr2 arr3 : Slice Std.I64) (h : ValidInput arr1 arr2 arr3)
    (v : alloc.vec.Vec Std.I64) (hres : arrays_intersection arr1 arr2 arr3 = ok v)
    (hne : 0 < v.val.length), Occurs (v.val.get ⟨0, hne⟩).val arr1 ∧ Occurs (v.val.get ⟨0, hne⟩).val arr2 ∧
      Occurs (v.val.get ⟨0, hne⟩).val arr3 ∧
      ∀ x : Int, Occurs x arr1 → Occurs x arr2 → Occurs x arr3 →
        (v.val.get ⟨0, hne⟩).val ≤ x) := by
  sorry

/-- Whenever the function returns Ok v and len(v) > 0, v[len(v)-1] occurs in arr1, occurs in arr2, and occurs in arr3, and for every integer x that occurs in all three arrays, x <= v[len(v)-1], where x occurs in an array arr means there exists j with 0 <= j < len(arr) and arr[j] = x.
  Preconditions: arr1, arr2, arr3 are 0-indexed arrays; len(arr1), len(arr2), len(arr3) are each between 1 and 1000 inclusive; every element of arr1, arr2, arr3 is an integer between 1 and 2000 inclusive; and each of arr1, arr2, arr3 is strictly increasing (for each t in {1,2,3} and every i with 0 <= i < len(arrt)-1, arrt[i] < arrt[i+1]). -/
theorem spec_12 (arr1 arr2 arr3 : Slice Std.I64) (h : ValidInput arr1 arr2 arr3)
    (v : alloc.vec.Vec Std.I64) (hres : arrays_intersection arr1 arr2 arr3 = ok v)
    (hne : 0 < v.val.length) :
    Occurs (lastOf v hne).val arr1 ∧
      Occurs (lastOf v hne).val arr2 ∧
      Occurs (lastOf v hne).val arr3 ∧
      ∀ x : Int, Occurs x arr1 → Occurs x arr2 → Occurs x arr3 →
        x ≤ (lastOf v hne).val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (arr1 arr2 arr3 : Slice Std.I64) (h : ValidInput arr1 arr2 arr3)
    (v : alloc.vec.Vec Std.I64) (hres : arrays_intersection arr1 arr2 arr3 = ok v)
    (hne : 0 < v.val.length), Occurs (lastOf v hne).val arr1 ∧
      Occurs (lastOf v hne).val arr2 ∧
      Occurs (lastOf v hne).val arr3 ∧
      ∀ x : Int, Occurs x arr1 → Occurs x arr2 → Occurs x arr3 →
        x ≤ (lastOf v hne).val) := by
  sorry

/-- Whenever the function returns Ok v on (arr1, arr2, arr3), and whenever it returns Ok v' on any permutation (b1, b2, b3) of the same three arrays (so b1, b2, b3 are arr1, arr2, arr3 in some order and still satisfy the preconditions), the two vectors v and v' are equal: len(v) = len(v') and for every i with 0 <= i < len(v), v[i] = v'[i].
  Preconditions: arr1, arr2, arr3 are 0-indexed arrays; len(arr1), len(arr2), len(arr3) are each between 1 and 1000 inclusive; every element of arr1, arr2, arr3 is an integer between 1 and 2000 inclusive; and each of arr1, arr2, arr3 is strictly increasing (for each t in {1,2,3} and every i with 0 <= i < len(arrt)-1, arrt[i] < arrt[i+1]). -/
theorem spec_13 (arr1 arr2 arr3 : Slice Std.I64) (h : ValidInput arr1 arr2 arr3)
    (v : alloc.vec.Vec Std.I64) (hres : arrays_intersection arr1 arr2 arr3 = ok v)
    (b1 b2 b3 : Slice Std.I64) (hperm : PermTriple arr1 arr2 arr3 b1 b2 b3)
    (hb : ValidInput b1 b2 b3) (v' : alloc.vec.Vec Std.I64)
    (hres' : arrays_intersection b1 b2 b3 = ok v') :
    v.val.length = v'.val.length ∧
      ∀ (i : Nat) (_ : i < v.val.length) (_ : i < v'.val.length),
        (v.val[i]).val = (v'.val[i]).val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (arr1 arr2 arr3 : Slice Std.I64) (h : ValidInput arr1 arr2 arr3)
    (v : alloc.vec.Vec Std.I64) (hres : arrays_intersection arr1 arr2 arr3 = ok v)
    (b1 b2 b3 : Slice Std.I64) (hperm : PermTriple arr1 arr2 arr3 b1 b2 b3)
    (hb : ValidInput b1 b2 b3) (v' : alloc.vec.Vec Std.I64)
    (hres' : arrays_intersection b1 b2 b3 = ok v'), v.val.length = v'.val.length ∧
      ∀ (i : Nat) (_ : i < v.val.length) (_ : i < v'.val.length),
        (v.val[i]).val = (v'.val[i]).val) := by
  sorry

end AegisSpec.ArraysIntersection
