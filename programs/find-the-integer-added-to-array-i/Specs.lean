import Aegis.AddedInteger.Code.Funs

/-!
# Specifications of `Aegis.AddedInteger.added_integer`

LeetCode problem `find-the-integer-added-to-array-i`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.AddedInteger

def entries (nums : Slice Std.I64) : List ℤ := nums.val.map (fun x => x.val)

def countOcc (l : List ℤ) (v : ℤ) : ℕ := (l.filter (fun a => a = v)).length

def countOccShift (l : List ℤ) (x v : ℤ) : ℕ := countOcc (l.map (fun a => a + x)) v

def IsShiftBy (nums1 nums2 : Slice Std.I64) (x : ℤ) : Prop :=
  ∀ v : ℤ, countOccShift (entries nums1) x v = countOcc (entries nums2) v

def HasSomeShift (nums1 nums2 : Slice Std.I64) : Prop := ∃ x : ℤ, IsShiftBy nums1 nums2 x

def EntriesBetween (nums : Slice Std.I64) (lo hi : ℤ) : Prop :=
  ∀ i : ℕ, ∀ h : i < nums.val.length, lo ≤ (nums.val.get ⟨i, h⟩).val ∧ (nums.val.get ⟨i, h⟩).val ≤ hi

def listMin (l : List ℤ) : ℤ := (l.min?).getD 0

def listMax (l : List ℤ) : ℤ := (l.max?).getD 0

def listSum (l : List ℤ) : ℤ := l.sum

/-- The function returns a result r, and for every integer v, the number of indices i with 0 <= i < len(nums1) and nums1[i] + r = v equals the number of indices j with 0 <= j < len(nums2) and nums2[j] = v.
  Preconditions: len(nums1) = len(nums2); 1 <= len(nums1) <= 100; for every i with 0 <= i < len(nums1), 0 <= nums1[i] <= 1000 and 0 <= nums2[i] <= 1000; and there exists an integer x such that for every integer v, the number of indices i with nums1[i] + x = v equals the number of indices j with nums2[j] = v. -/
theorem spec_1 (nums1 nums2 : Slice Std.I64)
    (h_len : nums1.val.length = nums2.val.length)
    (h_pos : 1 ≤ nums1.val.length) (h_le : nums1.val.length ≤ 100)
    (h_bnd1 : EntriesBetween nums1 0 1000) (h_bnd2 : EntriesBetween nums2 0 1000)
    (h_shift : HasSomeShift nums1 nums2) :
    ∃ r : I64, Aegis.AddedInteger.added_integer nums1 nums2 = ok r ∧
      ∀ v : ℤ, countOccShift (entries nums1) r.val v = countOcc (entries nums2) v := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (h_len : nums1.val.length = nums2.val.length)
    (h_pos : 1 ≤ nums1.val.length) (h_le : nums1.val.length ≤ 100)
    (h_bnd1 : EntriesBetween nums1 0 1000) (h_bnd2 : EntriesBetween nums2 0 1000)
    (h_shift : HasSomeShift nums1 nums2), ∃ r : I64, Aegis.AddedInteger.added_integer nums1 nums2 = ok r ∧
      ∀ v : ℤ, countOccShift (entries nums1) r.val v = countOcc (entries nums2) v) := by
  sorry

/-- The function returns a result r for every input satisfying the preconditions; it does not fail, overflow, panic, or access an out-of-bounds index.
  Preconditions: len(nums1) = len(nums2); 1 <= len(nums1) <= 100; for every i with 0 <= i < len(nums1), 0 <= nums1[i] <= 1000 and 0 <= nums2[i] <= 1000; and there exists an integer x such that for every integer v, the number of indices i with nums1[i] + x = v equals the number of indices j with nums2[j] = v. -/
theorem spec_2 (nums1 nums2 : Slice Std.I64)
    (h_len : nums1.val.length = nums2.val.length)
    (h_pos : 1 ≤ nums1.val.length) (h_le : nums1.val.length ≤ 100)
    (h_bnd1 : EntriesBetween nums1 0 1000) (h_bnd2 : EntriesBetween nums2 0 1000)
    (h_shift : HasSomeShift nums1 nums2) :
    ∃ r : I64, Aegis.AddedInteger.added_integer nums1 nums2 = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (h_len : nums1.val.length = nums2.val.length)
    (h_pos : 1 ≤ nums1.val.length) (h_le : nums1.val.length ≤ 100)
    (h_bnd1 : EntriesBetween nums1 0 1000) (h_bnd2 : EntriesBetween nums2 0 1000)
    (h_shift : HasSomeShift nums1 nums2), ∃ r : I64, Aegis.AddedInteger.added_integer nums1 nums2 = ok r) := by
  sorry

/-- The function returns a result r and -1000 <= r <= 1000.
  Preconditions: len(nums1) = len(nums2); 1 <= len(nums1) <= 100; for every i with 0 <= i < len(nums1), 0 <= nums1[i] <= 1000 and 0 <= nums2[i] <= 1000; and there exists an integer x such that for every integer v, the number of indices i with nums1[i] + x = v equals the number of indices j with nums2[j] = v. -/
theorem spec_3 (nums1 nums2 : Slice Std.I64)
    (h_len : nums1.val.length = nums2.val.length)
    (h_pos : 1 ≤ nums1.val.length) (h_le : nums1.val.length ≤ 100)
    (h_bnd1 : EntriesBetween nums1 0 1000) (h_bnd2 : EntriesBetween nums2 0 1000)
    (h_shift : HasSomeShift nums1 nums2) :
    ∃ r : I64, Aegis.AddedInteger.added_integer nums1 nums2 = ok r ∧ -1000 ≤ r.val ∧ r.val ≤ 1000 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (h_len : nums1.val.length = nums2.val.length)
    (h_pos : 1 ≤ nums1.val.length) (h_le : nums1.val.length ≤ 100)
    (h_bnd1 : EntriesBetween nums1 0 1000) (h_bnd2 : EntriesBetween nums2 0 1000)
    (h_shift : HasSomeShift nums1 nums2), ∃ r : I64, Aegis.AddedInteger.added_integer nums1 nums2 = ok r ∧ -1000 ≤ r.val ∧ r.val ≤ 1000) := by
  sorry

/-- The function returns a result r and r = min(nums2) - min(nums1), where min(nums) denotes the minimum of the entries nums[0], ..., nums[len(nums)-1] (the arrays are nonempty).
  Preconditions: len(nums1) = len(nums2); 1 <= len(nums1) <= 100; for every i with 0 <= i < len(nums1), 0 <= nums1[i] <= 1000 and 0 <= nums2[i] <= 1000; and there exists an integer x such that for every integer v, the number of indices i with nums1[i] + x = v equals the number of indices j with nums2[j] = v. -/
theorem spec_4 (nums1 nums2 : Slice Std.I64)
    (h_len : nums1.val.length = nums2.val.length)
    (h_pos : 1 ≤ nums1.val.length) (h_le : nums1.val.length ≤ 100)
    (h_bnd1 : EntriesBetween nums1 0 1000) (h_bnd2 : EntriesBetween nums2 0 1000)
    (h_shift : HasSomeShift nums1 nums2) :
    ∃ r : I64, Aegis.AddedInteger.added_integer nums1 nums2 = ok r ∧
      r.val = listMin (entries nums2) - listMin (entries nums1) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (h_len : nums1.val.length = nums2.val.length)
    (h_pos : 1 ≤ nums1.val.length) (h_le : nums1.val.length ≤ 100)
    (h_bnd1 : EntriesBetween nums1 0 1000) (h_bnd2 : EntriesBetween nums2 0 1000)
    (h_shift : HasSomeShift nums1 nums2), ∃ r : I64, Aegis.AddedInteger.added_integer nums1 nums2 = ok r ∧
      r.val = listMin (entries nums2) - listMin (entries nums1)) := by
  sorry

/-- The function returns a result r and r = max(nums2) - max(nums1), where max(nums) denotes the maximum of the entries nums[0], ..., nums[len(nums)-1] (the arrays are nonempty).
  Preconditions: len(nums1) = len(nums2); 1 <= len(nums1) <= 100; for every i with 0 <= i < len(nums1), 0 <= nums1[i] <= 1000 and 0 <= nums2[i] <= 1000; and there exists an integer x such that for every integer v, the number of indices i with nums1[i] + x = v equals the number of indices j with nums2[j] = v. -/
theorem spec_5 (nums1 nums2 : Slice Std.I64)
    (h_len : nums1.val.length = nums2.val.length)
    (h_pos : 1 ≤ nums1.val.length) (h_le : nums1.val.length ≤ 100)
    (h_bnd1 : EntriesBetween nums1 0 1000) (h_bnd2 : EntriesBetween nums2 0 1000)
    (h_shift : HasSomeShift nums1 nums2) :
    ∃ r : I64, Aegis.AddedInteger.added_integer nums1 nums2 = ok r ∧
      r.val = listMax (entries nums2) - listMax (entries nums1) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (h_len : nums1.val.length = nums2.val.length)
    (h_pos : 1 ≤ nums1.val.length) (h_le : nums1.val.length ≤ 100)
    (h_bnd1 : EntriesBetween nums1 0 1000) (h_bnd2 : EntriesBetween nums2 0 1000)
    (h_shift : HasSomeShift nums1 nums2), ∃ r : I64, Aegis.AddedInteger.added_integer nums1 nums2 = ok r ∧
      r.val = listMax (entries nums2) - listMax (entries nums1)) := by
  sorry

/-- The function returns a result r and for every index i with 0 <= i < len(nums1), 0 <= nums1[i] + r <= 1000.
  Preconditions: len(nums1) = len(nums2); 1 <= len(nums1) <= 100; for every i with 0 <= i < len(nums1), 0 <= nums1[i] <= 1000 and 0 <= nums2[i] <= 1000; and there exists an integer x such that for every integer v, the number of indices i with nums1[i] + x = v equals the number of indices j with nums2[j] = v. -/
theorem spec_6 (nums1 nums2 : Slice Std.I64)
    (h_len : nums1.val.length = nums2.val.length)
    (h_pos : 1 ≤ nums1.val.length) (h_le : nums1.val.length ≤ 100)
    (h_bnd1 : EntriesBetween nums1 0 1000) (h_bnd2 : EntriesBetween nums2 0 1000)
    (h_shift : HasSomeShift nums1 nums2) :
    ∃ r : I64, Aegis.AddedInteger.added_integer nums1 nums2 = ok r ∧
      ∀ i : ℕ, ∀ h : i < nums1.val.length,
        0 ≤ (nums1.val.get ⟨i, h⟩).val + r.val ∧ (nums1.val.get ⟨i, h⟩).val + r.val ≤ 1000 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (h_len : nums1.val.length = nums2.val.length)
    (h_pos : 1 ≤ nums1.val.length) (h_le : nums1.val.length ≤ 100)
    (h_bnd1 : EntriesBetween nums1 0 1000) (h_bnd2 : EntriesBetween nums2 0 1000)
    (h_shift : HasSomeShift nums1 nums2), ∃ r : I64, Aegis.AddedInteger.added_integer nums1 nums2 = ok r ∧
      ∀ i : ℕ, ∀ h : i < nums1.val.length,
        0 ≤ (nums1.val.get ⟨i, h⟩).val + r.val ∧ (nums1.val.get ⟨i, h⟩).val + r.val ≤ 1000) := by
  sorry

/-- The function returns a result r and for every index i with 0 <= i < len(nums1), there exists an index j with 0 <= j < len(nums2) such that nums2[j] = nums1[i] + r.
  Preconditions: len(nums1) = len(nums2); 1 <= len(nums1) <= 100; for every i with 0 <= i < len(nums1), 0 <= nums1[i] <= 1000 and 0 <= nums2[i] <= 1000; and there exists an integer x such that for every integer v, the number of indices i with nums1[i] + x = v equals the number of indices j with nums2[j] = v. -/
theorem spec_7 (nums1 nums2 : Slice Std.I64)
    (h_len : nums1.val.length = nums2.val.length)
    (h_pos : 1 ≤ nums1.val.length) (h_le : nums1.val.length ≤ 100)
    (h_bnd1 : EntriesBetween nums1 0 1000) (h_bnd2 : EntriesBetween nums2 0 1000)
    (h_shift : HasSomeShift nums1 nums2) :
    ∃ r : I64, Aegis.AddedInteger.added_integer nums1 nums2 = ok r ∧
      ∀ i : ℕ, ∀ h : i < nums1.val.length,
        ∃ j : ℕ, ∃ hj : j < nums2.val.length,
          (nums2.val.get ⟨j, hj⟩).val = (nums1.val.get ⟨i, h⟩).val + r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (h_len : nums1.val.length = nums2.val.length)
    (h_pos : 1 ≤ nums1.val.length) (h_le : nums1.val.length ≤ 100)
    (h_bnd1 : EntriesBetween nums1 0 1000) (h_bnd2 : EntriesBetween nums2 0 1000)
    (h_shift : HasSomeShift nums1 nums2), ∃ r : I64, Aegis.AddedInteger.added_integer nums1 nums2 = ok r ∧
      ∀ i : ℕ, ∀ h : i < nums1.val.length,
        ∃ j : ℕ, ∃ hj : j < nums2.val.length,
          (nums2.val.get ⟨j, hj⟩).val = (nums1.val.get ⟨i, h⟩).val + r.val) := by
  sorry

/-- The function returns a result r and for every index j with 0 <= j < len(nums2), there exists an index i with 0 <= i < len(nums1) such that nums1[i] + r = nums2[j].
  Preconditions: len(nums1) = len(nums2); 1 <= len(nums1) <= 100; for every i with 0 <= i < len(nums1), 0 <= nums1[i] <= 1000 and 0 <= nums2[i] <= 1000; and there exists an integer x such that for every integer v, the number of indices i with nums1[i] + x = v equals the number of indices j with nums2[j] = v. -/
theorem spec_8 (nums1 nums2 : Slice Std.I64)
    (h_len : nums1.val.length = nums2.val.length)
    (h_pos : 1 ≤ nums1.val.length) (h_le : nums1.val.length ≤ 100)
    (h_bnd1 : EntriesBetween nums1 0 1000) (h_bnd2 : EntriesBetween nums2 0 1000)
    (h_shift : HasSomeShift nums1 nums2) :
    ∃ r : I64, Aegis.AddedInteger.added_integer nums1 nums2 = ok r ∧
      ∀ j : ℕ, ∀ hj : j < nums2.val.length,
        ∃ i : ℕ, ∃ h : i < nums1.val.length,
          (nums1.val.get ⟨i, h⟩).val + r.val = (nums2.val.get ⟨j, hj⟩).val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (h_len : nums1.val.length = nums2.val.length)
    (h_pos : 1 ≤ nums1.val.length) (h_le : nums1.val.length ≤ 100)
    (h_bnd1 : EntriesBetween nums1 0 1000) (h_bnd2 : EntriesBetween nums2 0 1000)
    (h_shift : HasSomeShift nums1 nums2), ∃ r : I64, Aegis.AddedInteger.added_integer nums1 nums2 = ok r ∧
      ∀ j : ℕ, ∀ hj : j < nums2.val.length,
        ∃ i : ℕ, ∃ h : i < nums1.val.length,
          (nums1.val.get ⟨i, h⟩).val + r.val = (nums2.val.get ⟨j, hj⟩).val) := by
  sorry

/-- The function returns a result r, and there exists a bijection pi from the index set {0, ..., len(nums1)-1} to itself such that for every i with 0 <= i < len(nums1), nums2[pi(i)] = nums1[i] + r.
  Preconditions: len(nums1) = len(nums2); 1 <= len(nums1) <= 100; for every i with 0 <= i < len(nums1), 0 <= nums1[i] <= 1000 and 0 <= nums2[i] <= 1000; and there exists an integer x such that for every integer v, the number of indices i with nums1[i] + x = v equals the number of indices j with nums2[j] = v. -/
theorem spec_9 (nums1 nums2 : Slice Std.I64)
    (h_len : nums1.val.length = nums2.val.length)
    (h_pos : 1 ≤ nums1.val.length) (h_le : nums1.val.length ≤ 100)
    (h_bnd1 : EntriesBetween nums1 0 1000) (h_bnd2 : EntriesBetween nums2 0 1000)
    (h_shift : HasSomeShift nums1 nums2) :
    ∃ r : I64, Aegis.AddedInteger.added_integer nums1 nums2 = ok r ∧
      ∃ pi : Fin nums1.val.length → Fin nums1.val.length,
        Function.Bijective pi ∧
        ∀ i : Fin nums1.val.length,
          (nums2.val.get ⟨(pi i).val, by have := (pi i).isLt; omega⟩).val
            = (nums1.val.get i).val + r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (h_len : nums1.val.length = nums2.val.length)
    (h_pos : 1 ≤ nums1.val.length) (h_le : nums1.val.length ≤ 100)
    (h_bnd1 : EntriesBetween nums1 0 1000) (h_bnd2 : EntriesBetween nums2 0 1000)
    (h_shift : HasSomeShift nums1 nums2), ∃ r : I64, Aegis.AddedInteger.added_integer nums1 nums2 = ok r ∧
      ∃ pi : Fin nums1.val.length → Fin nums1.val.length,
        Function.Bijective pi ∧
        ∀ i : Fin nums1.val.length,
          (nums2.val.get ⟨(pi i).val, by have := (pi i).isLt; omega⟩).val
            = (nums1.val.get i).val + r.val) := by
  sorry

/-- The function returns a result r and sum(nums2) = sum(nums1) + len(nums1) * r, where sum(nums) = nums[0] + nums[1] + ... + nums[len(nums)-1].
  Preconditions: len(nums1) = len(nums2); 1 <= len(nums1) <= 100; for every i with 0 <= i < len(nums1), 0 <= nums1[i] <= 1000 and 0 <= nums2[i] <= 1000; and there exists an integer x such that for every integer v, the number of indices i with nums1[i] + x = v equals the number of indices j with nums2[j] = v. -/
theorem spec_10 (nums1 nums2 : Slice Std.I64)
    (h_len : nums1.val.length = nums2.val.length)
    (h_pos : 1 ≤ nums1.val.length) (h_le : nums1.val.length ≤ 100)
    (h_bnd1 : EntriesBetween nums1 0 1000) (h_bnd2 : EntriesBetween nums2 0 1000)
    (h_shift : HasSomeShift nums1 nums2) :
    ∃ r : I64, Aegis.AddedInteger.added_integer nums1 nums2 = ok r ∧
      listSum (entries nums2) = listSum (entries nums1) + (nums1.val.length : ℤ) * r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (h_len : nums1.val.length = nums2.val.length)
    (h_pos : 1 ≤ nums1.val.length) (h_le : nums1.val.length ≤ 100)
    (h_bnd1 : EntriesBetween nums1 0 1000) (h_bnd2 : EntriesBetween nums2 0 1000)
    (h_shift : HasSomeShift nums1 nums2), ∃ r : I64, Aegis.AddedInteger.added_integer nums1 nums2 = ok r ∧
      listSum (entries nums2) = listSum (entries nums1) + (nums1.val.length : ℤ) * r.val) := by
  sorry

/-- The function returns a result r, and for every integer y satisfying the multiset-shift condition (for every integer v, the number of indices i with nums1[i] + y = v equals the number of indices j with nums2[j] = v), we have y = r.
  Preconditions: len(nums1) = len(nums2); 1 <= len(nums1) <= 100; for every i with 0 <= i < len(nums1), 0 <= nums1[i] <= 1000 and 0 <= nums2[i] <= 1000; and there exists an integer x such that for every integer v, the number of indices i with nums1[i] + x = v equals the number of indices j with nums2[j] = v. -/
theorem spec_11 (nums1 nums2 : Slice Std.I64)
    (h_len : nums1.val.length = nums2.val.length)
    (h_pos : 1 ≤ nums1.val.length) (h_le : nums1.val.length ≤ 100)
    (h_bnd1 : EntriesBetween nums1 0 1000) (h_bnd2 : EntriesBetween nums2 0 1000)
    (h_shift : HasSomeShift nums1 nums2) :
    ∃ r : I64, Aegis.AddedInteger.added_integer nums1 nums2 = ok r ∧
      ∀ y : ℤ, IsShiftBy nums1 nums2 y → y = r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (h_len : nums1.val.length = nums2.val.length)
    (h_pos : 1 ≤ nums1.val.length) (h_le : nums1.val.length ≤ 100)
    (h_bnd1 : EntriesBetween nums1 0 1000) (h_bnd2 : EntriesBetween nums2 0 1000)
    (h_shift : HasSomeShift nums1 nums2), ∃ r : I64, Aegis.AddedInteger.added_integer nums1 nums2 = ok r ∧
      ∀ y : ℤ, IsShiftBy nums1 nums2 y → y = r.val) := by
  sorry

/-- The function returns a result r, and for every reordering nums1' of nums1 and every reordering nums2' of nums2, the function added_integer(nums1', nums2') returns the same value r.
  Preconditions: len(nums1) = len(nums2); 1 <= len(nums1) <= 100; for every i with 0 <= i < len(nums1), 0 <= nums1[i] <= 1000 and 0 <= nums2[i] <= 1000; and there exists an integer x such that for every integer v, the number of indices i with nums1[i] + x = v equals the number of indices j with nums2[j] = v. -/
theorem spec_12 (nums1 nums2 : Slice Std.I64)
    (h_len : nums1.val.length = nums2.val.length)
    (h_pos : 1 ≤ nums1.val.length) (h_le : nums1.val.length ≤ 100)
    (h_bnd1 : EntriesBetween nums1 0 1000) (h_bnd2 : EntriesBetween nums2 0 1000)
    (h_shift : HasSomeShift nums1 nums2) :
    ∃ r : I64, Aegis.AddedInteger.added_integer nums1 nums2 = ok r ∧
      ∀ (nums1' nums2' : Slice Std.I64),
        List.Perm (entries nums1') (entries nums1) →
        List.Perm (entries nums2') (entries nums2) →
        Aegis.AddedInteger.added_integer nums1' nums2' = ok r := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (h_len : nums1.val.length = nums2.val.length)
    (h_pos : 1 ≤ nums1.val.length) (h_le : nums1.val.length ≤ 100)
    (h_bnd1 : EntriesBetween nums1 0 1000) (h_bnd2 : EntriesBetween nums2 0 1000)
    (h_shift : HasSomeShift nums1 nums2), ∃ r : I64, Aegis.AddedInteger.added_integer nums1 nums2 = ok r ∧
      ∀ (nums1' nums2' : Slice Std.I64),
        List.Perm (entries nums1') (entries nums1) →
        List.Perm (entries nums2') (entries nums2) →
        Aegis.AddedInteger.added_integer nums1' nums2' = ok r) := by
  sorry

end AegisSpec.AddedInteger
