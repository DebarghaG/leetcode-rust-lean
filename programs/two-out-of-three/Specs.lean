import Aegis.TwoOutOfThree.Code.Funs

/-!
# Specifications of `Aegis.TwoOutOfThree.two_out_of_three`

LeetCode problem `two-out-of-three`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.TwoOutOfThree (two_out_of_three)

namespace AegisSpec.TwoOutOfThree

def Occurs (v : ℤ) (l : List Std.I64) : Prop := v ∈ l.map (fun x => x.val)

def OccursS (v : ℤ) (xs : Slice Std.I64) : Prop := Occurs v xs.val

def OccursV (v : ℤ) (r : alloc.vec.Vec Std.I64) : Prop := Occurs v r.val

def OccursTwo (v : ℤ) (nums1 nums2 nums3 : Slice Std.I64) : Prop :=
  (OccursS v nums1 ∧ OccursS v nums2) ∨ (OccursS v nums1 ∧ OccursS v nums3) ∨
    (OccursS v nums2 ∧ OccursS v nums3)

def ArrayOk (xs : Slice Std.I64) : Prop :=
  1 ≤ xs.val.length ∧ xs.val.length ≤ 100 ∧ ∀ x ∈ xs.val, (1 : ℤ) ≤ x.val ∧ x.val ≤ 100

def nthVal (l : List Std.I64) (j : ℕ) (hj : j < l.length) : ℤ := (l.get ⟨j, hj⟩).val

noncomputable def TwoOfThreeSet (nums1 nums2 nums3 : Slice Std.I64) : Finset ℤ := by
  classical
  exact ((nums1.val ++ nums2.val ++ nums3.val).map (fun x => x.val)).toFinset.filter
    (fun v => OccursTwo v nums1 nums2 nums3)

noncomputable def TwoOfThreeCount (nums1 nums2 nums3 : Slice Std.I64) : ℕ :=
  (TwoOfThreeSet nums1 nums2 nums3).card

def IsReorder (p1 p2 p3 nums1 nums2 nums3 : Slice Std.I64) : Prop :=
  (p1 = nums1 ∧ p2 = nums2 ∧ p3 = nums3) ∨
  (p1 = nums1 ∧ p2 = nums3 ∧ p3 = nums2) ∨
  (p1 = nums2 ∧ p2 = nums1 ∧ p3 = nums3) ∨
  (p1 = nums2 ∧ p2 = nums3 ∧ p3 = nums1) ∨
  (p1 = nums3 ∧ p2 = nums1 ∧ p3 = nums2) ∨
  (p1 = nums3 ∧ p2 = nums2 ∧ p3 = nums1)

def SameValues (l m : List Std.I64) : Prop := ∀ v : ℤ, Occurs v l ↔ Occurs v m

def DisjointValues (l m : List Std.I64) : Prop := ∀ v : ℤ, ¬ (Occurs v l ∧ Occurs v m)

def ValuesSubset (l m : List Std.I64) : Prop := ∀ v : ℤ, Occurs v l → Occurs v m

/-- The function returns a result r such that: (1) for every index j with 0 <= j < len(r), the integer r[j] occurs in at least two of the three arrays nums1, nums2, nums3; (2) for every integer v, if v occurs in at least two of the three arrays, then there exists an index j with 0 <= j < len(r) and r[j] = v; and (3) for every i, j with 0 <= i < j < len(r), r[i] != r[j].
  Preconditions: The lengths of nums1, nums2, and nums3 are each between 1 and 100 inclusive, and every element of nums1, nums2, and nums3 is between 1 and 100 inclusive. -/
theorem spec_1 (nums1 nums2 nums3 : Slice Std.I64)
    (h1 : ArrayOk nums1) (h2 : ArrayOk nums2) (h3 : ArrayOk nums3) :
    ∃ r, two_out_of_three nums1 nums2 nums3 = ok r ∧
      (∀ (j : ℕ) (hj : j < r.val.length),
        OccursTwo (nthVal r.val j hj) nums1 nums2 nums3) ∧
      (∀ v : ℤ, OccursTwo v nums1 nums2 nums3 →
        ∃ (j : ℕ) (hj : j < r.val.length), nthVal r.val j hj = v) ∧
      (∀ (i j : ℕ) (hi : i < r.val.length) (hj : j < r.val.length),
        i < j → nthVal r.val i hi ≠ nthVal r.val j hj) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums1 nums2 nums3 : Slice Std.I64)
    (h1 : ArrayOk nums1) (h2 : ArrayOk nums2) (h3 : ArrayOk nums3), ∃ r, two_out_of_three nums1 nums2 nums3 = ok r ∧
      (∀ (j : ℕ) (hj : j < r.val.length),
        OccursTwo (nthVal r.val j hj) nums1 nums2 nums3) ∧
      (∀ v : ℤ, OccursTwo v nums1 nums2 nums3 →
        ∃ (j : ℕ) (hj : j < r.val.length), nthVal r.val j hj = v) ∧
      (∀ (i j : ℕ) (hi : i < r.val.length) (hj : j < r.val.length),
        i < j → nthVal r.val i hi ≠ nthVal r.val j hj)) := by
  sorry

/-- The function returns a result r (it does not fail, panic, or overflow) for every input satisfying the preconditions.
  Preconditions: The lengths of nums1, nums2, and nums3 are each between 1 and 100 inclusive, and every element of nums1, nums2, and nums3 is between 1 and 100 inclusive. -/
theorem spec_2 (nums1 nums2 nums3 : Slice Std.I64)
    (h1 : ArrayOk nums1) (h2 : ArrayOk nums2) (h3 : ArrayOk nums3) :
    ∃ r, two_out_of_three nums1 nums2 nums3 = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums1 nums2 nums3 : Slice Std.I64)
    (h1 : ArrayOk nums1) (h2 : ArrayOk nums2) (h3 : ArrayOk nums3), ∃ r, two_out_of_three nums1 nums2 nums3 = ok r) := by
  sorry

/-- Whenever the function returns a result r, for every index j with 0 <= j < len(r), the integer r[j] occurs in at least two of the three arrays nums1, nums2, nums3.
  Preconditions: The lengths of nums1, nums2, and nums3 are each between 1 and 100 inclusive, and every element of nums1, nums2, and nums3 is between 1 and 100 inclusive. -/
theorem spec_3 (nums1 nums2 nums3 : Slice Std.I64)
    (h1 : ArrayOk nums1) (h2 : ArrayOk nums2) (h3 : ArrayOk nums3)
    (r : alloc.vec.Vec Std.I64) (hr : two_out_of_three nums1 nums2 nums3 = ok r) :
    ∀ (j : ℕ) (hj : j < r.val.length),
      OccursTwo (nthVal r.val j hj) nums1 nums2 nums3 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums1 nums2 nums3 : Slice Std.I64)
    (h1 : ArrayOk nums1) (h2 : ArrayOk nums2) (h3 : ArrayOk nums3)
    (r : alloc.vec.Vec Std.I64) (hr : two_out_of_three nums1 nums2 nums3 = ok r), ∀ (j : ℕ) (hj : j < r.val.length),
      OccursTwo (nthVal r.val j hj) nums1 nums2 nums3) := by
  sorry

/-- Whenever the function returns a result r, for every integer v, if v occurs in at least two of the three arrays nums1, nums2, nums3, then there exists an index j with 0 <= j < len(r) and r[j] = v.
  Preconditions: The lengths of nums1, nums2, and nums3 are each between 1 and 100 inclusive, and every element of nums1, nums2, and nums3 is between 1 and 100 inclusive. -/
theorem spec_4 (nums1 nums2 nums3 : Slice Std.I64)
    (h1 : ArrayOk nums1) (h2 : ArrayOk nums2) (h3 : ArrayOk nums3)
    (r : alloc.vec.Vec Std.I64) (hr : two_out_of_three nums1 nums2 nums3 = ok r) :
    ∀ v : ℤ, OccursTwo v nums1 nums2 nums3 → OccursV v r := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums1 nums2 nums3 : Slice Std.I64)
    (h1 : ArrayOk nums1) (h2 : ArrayOk nums2) (h3 : ArrayOk nums3)
    (r : alloc.vec.Vec Std.I64) (hr : two_out_of_three nums1 nums2 nums3 = ok r), ∀ v : ℤ, OccursTwo v nums1 nums2 nums3 → OccursV v r) := by
  sorry

/-- Whenever the function returns a result r, for every i, j with 0 <= i < j < len(r), r[i] != r[j].
  Preconditions: The lengths of nums1, nums2, and nums3 are each between 1 and 100 inclusive, and every element of nums1, nums2, and nums3 is between 1 and 100 inclusive. -/
theorem spec_5 (nums1 nums2 nums3 : Slice Std.I64)
    (h1 : ArrayOk nums1) (h2 : ArrayOk nums2) (h3 : ArrayOk nums3)
    (r : alloc.vec.Vec Std.I64) (hr : two_out_of_three nums1 nums2 nums3 = ok r) :
    ∀ (i j : ℕ) (hi : i < r.val.length) (hj : j < r.val.length),
      i < j → nthVal r.val i hi ≠ nthVal r.val j hj := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums1 nums2 nums3 : Slice Std.I64)
    (h1 : ArrayOk nums1) (h2 : ArrayOk nums2) (h3 : ArrayOk nums3)
    (r : alloc.vec.Vec Std.I64) (hr : two_out_of_three nums1 nums2 nums3 = ok r), ∀ (i j : ℕ) (hi : i < r.val.length) (hj : j < r.val.length),
      i < j → nthVal r.val i hi ≠ nthVal r.val j hj) := by
  sorry

/-- Whenever the function returns a result r, len(r) <= 100.
  Preconditions: The lengths of nums1, nums2, and nums3 are each between 1 and 100 inclusive, and every element of nums1, nums2, and nums3 is between 1 and 100 inclusive. -/
theorem spec_6 (nums1 nums2 nums3 : Slice Std.I64)
    (h1 : ArrayOk nums1) (h2 : ArrayOk nums2) (h3 : ArrayOk nums3)
    (r : alloc.vec.Vec Std.I64) (hr : two_out_of_three nums1 nums2 nums3 = ok r) :
    r.val.length ≤ 100 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums1 nums2 nums3 : Slice Std.I64)
    (h1 : ArrayOk nums1) (h2 : ArrayOk nums2) (h3 : ArrayOk nums3)
    (r : alloc.vec.Vec Std.I64) (hr : two_out_of_three nums1 nums2 nums3 = ok r), r.val.length ≤ 100) := by
  sorry

/-- Whenever the function returns a result r, for every index j with 0 <= j < len(r), 1 <= r[j] <= 100.
  Preconditions: The lengths of nums1, nums2, and nums3 are each between 1 and 100 inclusive, and every element of nums1, nums2, and nums3 is between 1 and 100 inclusive. -/
theorem spec_7 (nums1 nums2 nums3 : Slice Std.I64)
    (h1 : ArrayOk nums1) (h2 : ArrayOk nums2) (h3 : ArrayOk nums3)
    (r : alloc.vec.Vec Std.I64) (hr : two_out_of_three nums1 nums2 nums3 = ok r) :
    ∀ (j : ℕ) (hj : j < r.val.length),
      1 ≤ nthVal r.val j hj ∧ nthVal r.val j hj ≤ 100 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums1 nums2 nums3 : Slice Std.I64)
    (h1 : ArrayOk nums1) (h2 : ArrayOk nums2) (h3 : ArrayOk nums3)
    (r : alloc.vec.Vec Std.I64) (hr : two_out_of_three nums1 nums2 nums3 = ok r), ∀ (j : ℕ) (hj : j < r.val.length),
      1 ≤ nthVal r.val j hj ∧ nthVal r.val j hj ≤ 100) := by
  sorry

/-- Whenever the function returns a result r, len(r) equals the number of distinct integers v such that v occurs in at least two of the three arrays nums1, nums2, nums3.
  Preconditions: The lengths of nums1, nums2, and nums3 are each between 1 and 100 inclusive, and every element of nums1, nums2, and nums3 is between 1 and 100 inclusive. -/
theorem spec_8 (nums1 nums2 nums3 : Slice Std.I64)
    (h1 : ArrayOk nums1) (h2 : ArrayOk nums2) (h3 : ArrayOk nums3)
    (r : alloc.vec.Vec Std.I64) (hr : two_out_of_three nums1 nums2 nums3 = ok r) :
    r.val.length = TwoOfThreeCount nums1 nums2 nums3 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums1 nums2 nums3 : Slice Std.I64)
    (h1 : ArrayOk nums1) (h2 : ArrayOk nums2) (h3 : ArrayOk nums3)
    (r : alloc.vec.Vec Std.I64) (hr : two_out_of_three nums1 nums2 nums3 = ok r), r.val.length = TwoOfThreeCount nums1 nums2 nums3) := by
  sorry

/-- Whenever the function returns a result r, if no integer v occurs in at least two of the three arrays nums1, nums2, nums3, then len(r) = 0.
  Preconditions: The lengths of nums1, nums2, and nums3 are each between 1 and 100 inclusive, and every element of nums1, nums2, and nums3 is between 1 and 100 inclusive. -/
theorem spec_9 (nums1 nums2 nums3 : Slice Std.I64)
    (h1 : ArrayOk nums1) (h2 : ArrayOk nums2) (h3 : ArrayOk nums3)
    (r : alloc.vec.Vec Std.I64) (hr : two_out_of_three nums1 nums2 nums3 = ok r) :
    (∀ v : ℤ, ¬ OccursTwo v nums1 nums2 nums3) → r.val.length = 0 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums1 nums2 nums3 : Slice Std.I64)
    (h1 : ArrayOk nums1) (h2 : ArrayOk nums2) (h3 : ArrayOk nums3)
    (r : alloc.vec.Vec Std.I64) (hr : two_out_of_three nums1 nums2 nums3 = ok r), (∀ v : ℤ, ¬ OccursTwo v nums1 nums2 nums3) → r.val.length = 0) := by
  sorry

/-- Whenever the function returns a result r, if nums1, nums2, and nums3 are all equal as lists (they have the same length and for every index i in that length, nums1[i] = nums2[i] = nums3[i]), then for every integer v, v occurs in r if and only if v occurs in nums1.
  Preconditions: The lengths of nums1, nums2, and nums3 are each between 1 and 100 inclusive, and every element of nums1, nums2, and nums3 is between 1 and 100 inclusive. -/
theorem spec_10 (nums1 nums2 nums3 : Slice Std.I64)
    (h1 : ArrayOk nums1) (h2 : ArrayOk nums2) (h3 : ArrayOk nums3)
    (r : alloc.vec.Vec Std.I64) (hr : two_out_of_three nums1 nums2 nums3 = ok r) :
    (nums1.val = nums2.val ∧ nums2.val = nums3.val) →
      ∀ v : ℤ, OccursV v r ↔ OccursS v nums1 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums1 nums2 nums3 : Slice Std.I64)
    (h1 : ArrayOk nums1) (h2 : ArrayOk nums2) (h3 : ArrayOk nums3)
    (r : alloc.vec.Vec Std.I64) (hr : two_out_of_three nums1 nums2 nums3 = ok r), (nums1.val = nums2.val ∧ nums2.val = nums3.val) →
      ∀ v : ℤ, OccursV v r ↔ OccursS v nums1) := by
  sorry

/-- Whenever the function returns a result r, if nums1 and nums2 are equal as lists and no value occurs in both nums3 and nums1 (i.e., the sets of values occurring in nums3 and nums1 are disjoint), then for every integer v, v occurs in r if and only if v occurs in nums1.
  Preconditions: The lengths of nums1, nums2, and nums3 are each between 1 and 100 inclusive, and every element of nums1, nums2, and nums3 is between 1 and 100 inclusive. -/
theorem spec_11 (nums1 nums2 nums3 : Slice Std.I64)
    (h1 : ArrayOk nums1) (h2 : ArrayOk nums2) (h3 : ArrayOk nums3)
    (r : alloc.vec.Vec Std.I64) (hr : two_out_of_three nums1 nums2 nums3 = ok r) :
    (nums1.val = nums2.val ∧ DisjointValues nums3.val nums1.val) →
      ∀ v : ℤ, OccursV v r ↔ OccursS v nums1 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums1 nums2 nums3 : Slice Std.I64)
    (h1 : ArrayOk nums1) (h2 : ArrayOk nums2) (h3 : ArrayOk nums3)
    (r : alloc.vec.Vec Std.I64) (hr : two_out_of_three nums1 nums2 nums3 = ok r), (nums1.val = nums2.val ∧ DisjointValues nums3.val nums1.val) →
      ∀ v : ℤ, OccursV v r ↔ OccursS v nums1) := by
  sorry

/-- Whenever the function returns a result r for the inputs (nums1, nums2, nums3), for every reordering (p1, p2, p3) of the three slices (nums1, nums2, nums3), the function returns a result r' for the inputs (p1, p2, p3) such that the set of elements of r' equals the set of elements of r. That is, the set of values in the result is invariant under any reordering of the three input arrays.
  Preconditions: The lengths of nums1, nums2, and nums3 are each between 1 and 100 inclusive, and every element of nums1, nums2, and nums3 is between 1 and 100 inclusive. -/
theorem spec_12 (nums1 nums2 nums3 : Slice Std.I64)
    (h1 : ArrayOk nums1) (h2 : ArrayOk nums2) (h3 : ArrayOk nums3)
    (r : alloc.vec.Vec Std.I64) (hr : two_out_of_three nums1 nums2 nums3 = ok r) :
    ∀ p1 p2 p3 : Slice Std.I64, IsReorder p1 p2 p3 nums1 nums2 nums3 →
      ∃ r', two_out_of_three p1 p2 p3 = ok r' ∧ ∀ v : ℤ, OccursV v r' ↔ OccursV v r := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums1 nums2 nums3 : Slice Std.I64)
    (h1 : ArrayOk nums1) (h2 : ArrayOk nums2) (h3 : ArrayOk nums3)
    (r : alloc.vec.Vec Std.I64) (hr : two_out_of_three nums1 nums2 nums3 = ok r), ∀ p1 p2 p3 : Slice Std.I64, IsReorder p1 p2 p3 nums1 nums2 nums3 →
      ∃ r', two_out_of_three p1 p2 p3 = ok r' ∧ ∀ v : ℤ, OccursV v r' ↔ OccursV v r) := by
  sorry

/-- Whenever the function returns a result r, if no value occurs in both nums1 and nums2 (i.e., the sets of values occurring in nums1 and nums2 are disjoint), then for every integer v, v occurs in r if and only if (v occurs in nums1 and v occurs in nums3) or (v occurs in nums2 and v occurs in nums3).
  Preconditions: The lengths of nums1, nums2, and nums3 are each between 1 and 100 inclusive, and every element of nums1, nums2, and nums3 is between 1 and 100 inclusive. -/
theorem spec_13 (nums1 nums2 nums3 : Slice Std.I64)
    (h1 : ArrayOk nums1) (h2 : ArrayOk nums2) (h3 : ArrayOk nums3)
    (r : alloc.vec.Vec Std.I64) (hr : two_out_of_three nums1 nums2 nums3 = ok r) :
    DisjointValues nums1.val nums2.val →
      ∀ v : ℤ, OccursV v r ↔
        ((OccursS v nums1 ∧ OccursS v nums3) ∨ (OccursS v nums2 ∧ OccursS v nums3)) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums1 nums2 nums3 : Slice Std.I64)
    (h1 : ArrayOk nums1) (h2 : ArrayOk nums2) (h3 : ArrayOk nums3)
    (r : alloc.vec.Vec Std.I64) (hr : two_out_of_three nums1 nums2 nums3 = ok r), DisjointValues nums1.val nums2.val →
      ∀ v : ℤ, OccursV v r ↔
        ((OccursS v nums1 ∧ OccursS v nums3) ∨ (OccursS v nums2 ∧ OccursS v nums3))) := by
  sorry

/-- Whenever the function returns a result r, if every value that occurs in nums3 also occurs in nums1 (i.e., the set of values occurring in nums3 is a subset of the set of values occurring in nums1), then for every integer v, v occurs in r if and only if v occurs in nums3 or (v occurs in nums1 and v occurs in nums2).
  Preconditions: The lengths of nums1, nums2, and nums3 are each between 1 and 100 inclusive, and every element of nums1, nums2, and nums3 is between 1 and 100 inclusive. -/
theorem spec_14 (nums1 nums2 nums3 : Slice Std.I64)
    (h1 : ArrayOk nums1) (h2 : ArrayOk nums2) (h3 : ArrayOk nums3)
    (r : alloc.vec.Vec Std.I64) (hr : two_out_of_three nums1 nums2 nums3 = ok r) :
    ValuesSubset nums3.val nums1.val →
      ∀ v : ℤ, OccursV v r ↔ (OccursS v nums3 ∨ (OccursS v nums1 ∧ OccursS v nums2)) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (nums1 nums2 nums3 : Slice Std.I64)
    (h1 : ArrayOk nums1) (h2 : ArrayOk nums2) (h3 : ArrayOk nums3)
    (r : alloc.vec.Vec Std.I64) (hr : two_out_of_three nums1 nums2 nums3 = ok r), ValuesSubset nums3.val nums1.val →
      ∀ v : ℤ, OccursV v r ↔ (OccursS v nums3 ∨ (OccursS v nums1 ∧ OccursS v nums2))) := by
  sorry

/-- Whenever the function returns a result r for (nums1, nums2, nums3) and a result r' for (nums1', nums2', nums3'), where for each i the set of values occurring in numsi' equals the set of values occurring in numsi (i.e. numsi' is obtained from numsi by reordering and/or adding or removing repetitions of values), the set of elements of r equals the set of elements of r'.
  Preconditions: The lengths of nums1, nums2, and nums3 are each between 1 and 100 inclusive, and every element of nums1, nums2, and nums3 is between 1 and 100 inclusive. -/
theorem spec_15 (nums1 nums2 nums3 nums1' nums2' nums3' : Slice Std.I64)
    (h1 : ArrayOk nums1) (h2 : ArrayOk nums2) (h3 : ArrayOk nums3)
    (h1' : ArrayOk nums1') (h2' : ArrayOk nums2') (h3' : ArrayOk nums3')
    (hset1 : SameValues nums1.val nums1'.val) (hset2 : SameValues nums2.val nums2'.val)
    (hset3 : SameValues nums3.val nums3'.val)
    (r r' : alloc.vec.Vec Std.I64)
    (hr : two_out_of_three nums1 nums2 nums3 = ok r)
    (hr' : two_out_of_three nums1' nums2' nums3' = ok r') :
    ∀ v : ℤ, OccursV v r ↔ OccursV v r' := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (nums1 nums2 nums3 nums1' nums2' nums3' : Slice Std.I64)
    (h1 : ArrayOk nums1) (h2 : ArrayOk nums2) (h3 : ArrayOk nums3)
    (h1' : ArrayOk nums1') (h2' : ArrayOk nums2') (h3' : ArrayOk nums3')
    (hset1 : SameValues nums1.val nums1'.val) (hset2 : SameValues nums2.val nums2'.val)
    (hset3 : SameValues nums3.val nums3'.val)
    (r r' : alloc.vec.Vec Std.I64)
    (hr : two_out_of_three nums1 nums2 nums3 = ok r)
    (hr' : two_out_of_three nums1' nums2' nums3' = ok r'), ∀ v : ℤ, OccursV v r ↔ OccursV v r') := by
  sorry

/-- Whenever the function returns a result r, for every integer v, v occurs in r if and only if (v occurs in nums1 and v occurs in nums2) or (v occurs in nums1 and v occurs in nums3) or (v occurs in nums2 and v occurs in nums3).
  Preconditions: The lengths of nums1, nums2, and nums3 are each between 1 and 100 inclusive, and every element of nums1, nums2, and nums3 is between 1 and 100 inclusive. -/
theorem spec_16 (nums1 nums2 nums3 : Slice Std.I64)
    (h1 : ArrayOk nums1) (h2 : ArrayOk nums2) (h3 : ArrayOk nums3)
    (r : alloc.vec.Vec Std.I64) (hr : two_out_of_three nums1 nums2 nums3 = ok r) :
    ∀ v : ℤ, OccursV v r ↔
      ((OccursS v nums1 ∧ OccursS v nums2) ∨ (OccursS v nums1 ∧ OccursS v nums3) ∨
        (OccursS v nums2 ∧ OccursS v nums3)) := by
  sorry

theorem spec_16_neg :
    ¬ (∀ (nums1 nums2 nums3 : Slice Std.I64)
    (h1 : ArrayOk nums1) (h2 : ArrayOk nums2) (h3 : ArrayOk nums3)
    (r : alloc.vec.Vec Std.I64) (hr : two_out_of_three nums1 nums2 nums3 = ok r), ∀ v : ℤ, OccursV v r ↔
      ((OccursS v nums1 ∧ OccursS v nums2) ∨ (OccursS v nums1 ∧ OccursS v nums3) ∨
        (OccursS v nums2 ∧ OccursS v nums3))) := by
  sorry

/-- Whenever the function returns a result r for (nums1, nums2, nums3) and a result r' for (nums1', nums2', nums3'), if every value occurring in nums1 occurs in nums1', every value occurring in nums2 occurs in nums2', and every value occurring in nums3 occurs in nums3', then every value occurring in r also occurs in r'.
  Preconditions: The lengths of nums1, nums2, and nums3 are each between 1 and 100 inclusive, and every element of nums1, nums2, and nums3 is between 1 and 100 inclusive (likewise for nums1', nums2', nums3'). -/
theorem spec_17 (nums1 nums2 nums3 nums1' nums2' nums3' : Slice Std.I64)
    (h1 : ArrayOk nums1) (h2 : ArrayOk nums2) (h3 : ArrayOk nums3)
    (h1' : ArrayOk nums1') (h2' : ArrayOk nums2') (h3' : ArrayOk nums3')
    (hsub1 : ValuesSubset nums1.val nums1'.val)
    (hsub2 : ValuesSubset nums2.val nums2'.val)
    (hsub3 : ValuesSubset nums3.val nums3'.val)
    (r r' : alloc.vec.Vec Std.I64)
    (hr : two_out_of_three nums1 nums2 nums3 = ok r)
    (hr' : two_out_of_three nums1' nums2' nums3' = ok r') :
    ∀ v : ℤ, OccursV v r → OccursV v r' := by
  sorry

theorem spec_17_neg :
    ¬ (∀ (nums1 nums2 nums3 nums1' nums2' nums3' : Slice Std.I64)
    (h1 : ArrayOk nums1) (h2 : ArrayOk nums2) (h3 : ArrayOk nums3)
    (h1' : ArrayOk nums1') (h2' : ArrayOk nums2') (h3' : ArrayOk nums3')
    (hsub1 : ValuesSubset nums1.val nums1'.val)
    (hsub2 : ValuesSubset nums2.val nums2'.val)
    (hsub3 : ValuesSubset nums3.val nums3'.val)
    (r r' : alloc.vec.Vec Std.I64)
    (hr : two_out_of_three nums1 nums2 nums3 = ok r)
    (hr' : two_out_of_three nums1' nums2' nums3' = ok r'), ∀ v : ℤ, OccursV v r → OccursV v r') := by
  sorry

end AegisSpec.TwoOutOfThree
