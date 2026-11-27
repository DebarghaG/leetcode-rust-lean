import Aegis.MinZeroArray.Code.Funs

/-!
# Specifications of `Aegis.MinZeroArray.min_zero_array`

LeetCode problem `zero-array-transformation-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result ControlFlow Error

  namespace AegisSpec.MinZeroArray

  open Aeneas Aeneas.Std

  structure QRow where

    l : ℤ

    r : ℤ

    v : ℤ

  def rowAt (queries : Slice (alloc.vec.Vec Std.I64)) (j : ℕ) : QRow :=
    match queries.val[j]? with
    | some q =>
      match q.val with
      | [l, r, v] => ⟨l.val, r.val, v.val⟩
      | _ => ⟨0, 0, 0⟩
    | none => ⟨0, 0, 0⟩

  def rowLen (queries : Slice (alloc.vec.Vec Std.I64)) (j : ℕ) : ℕ :=
    match queries.val[j]? with
    | some q => q.val.length
    | none => 0

  def numsGet (nums : Slice Std.I64) (i : ℕ) : ℤ :=
    match nums.val[i]? with
    | some x => x.val
    | none => 0

  def cover (queries : Slice (alloc.vec.Vec Std.I64)) (k i : ℕ) : ℤ :=
    ∑ j ∈ Finset.range k,
      if (rowAt queries j).l ≤ (i : ℤ) ∧ (i : ℤ) ≤ (rowAt queries j).r then
        (rowAt queries j).v
      else 0

  theorem numsGet_eq_getElem (nums : Slice Std.I64) (i : ℕ) (h : i < nums.val.length) :
      numsGet nums i = (nums.val.get ⟨i, h⟩).val := by
    simp only [numsGet]
    rw [List.getElem?_eq_getElem h]
    rfl

  theorem rowAt_eq_of_getElem (queries : Slice (alloc.vec.Vec Std.I64)) (j : ℕ)
      (q : alloc.vec.Vec Std.I64) (hq : queries.val[j]? = some q)
      (l r v : Std.I64) (hrow : q.val = [l, r, v]) :
      rowAt queries j = ⟨l.val, r.val, v.val⟩ := by
    simp only [rowAt]
    rw [hq]
    simp only [hrow]

  theorem rowLen_eq_of_getElem (queries : Slice (alloc.vec.Vec Std.I64)) (j : ℕ)
      (q : alloc.vec.Vec Std.I64) (hq : queries.val[j]? = some q) :
      rowLen queries j = q.val.length := by
    simp only [rowLen]
    rw [hq]

  theorem cover_zero (queries : Slice (alloc.vec.Vec Std.I64)) (i : ℕ) :
      cover queries 0 i = 0 := by
    simp [cover]

  theorem cover_succ (queries : Slice (alloc.vec.Vec Std.I64)) (k i : ℕ) :
      cover queries (k + 1) i =
        cover queries k i +
          (if (rowAt queries k).l ≤ (i : ℤ) ∧ (i : ℤ) ≤ (rowAt queries k).r then
            (rowAt queries k).v
          else 0) := by
    rw [cover, Finset.sum_range_succ]
    rfl

  /-- Let C(k,i) = sum over j with 0 <= j < k and queries[j][0] <= i <= queries[j][1] of queries[j][2], for 0 <= k <= len(queries) and 0 <= i < len(nums) (the empty sum is 0). The function returns a result r, and exactly one of the following holds. (a) r = -1 and for every k with 0 <= k <= len(queries) there exists i with 0 <= i < len(nums) such that nums[i] > C(k,i). (b) 0 <= r <= len(queries), for every i with 0 <= i < len(nums) we have nums[i] <= C(r,i), and for every k with 0 <= k < r there exists i with 0 <= i < len(nums) such that nums[i] > C(k,i).
    Preconditions: Let n = len(nums) and m = len(queries). The preconditions are 1 <= n <= 100000, 0 <= nums[i] <= 500000 for every i with 0 <= i < n, 1 <= m <= 100000, and for every j with 0 <= j < m, len(queries[j]) = 3; writing queries[j] = [l_j, r_j, val_j], we have 0 <= l_j <= r_j < n and 1 <= val_j <= 5. -/
  theorem spec_1 (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
      (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
      (hnums : ∀ i, i < nums.val.length → 0 ≤ numsGet nums i ∧ numsGet nums i ≤ 500000)
      (hm_pos : 1 ≤ queries.val.length) (hm_le : queries.val.length ≤ 100000)
      (hrows_len : ∀ j, j < queries.val.length → rowLen queries j = 3)
      (hrows : ∀ j, j < queries.val.length →
        0 ≤ (rowAt queries j).l ∧ (rowAt queries j).l ≤ (rowAt queries j).r ∧
          (rowAt queries j).r < (nums.val.length : ℤ) ∧
            1 ≤ (rowAt queries j).v ∧ (rowAt queries j).v ≤ 5) :
      ∃ r : Std.I64,
        Aegis.MinZeroArray.min_zero_array nums queries = ok r ∧
          ((r.val = -1 ∧
              ∀ k, k ≤ queries.val.length →
                ∃ i, i < nums.val.length ∧ numsGet nums i > cover queries k i) ∨
            (0 ≤ r.val ∧ r.val ≤ (queries.val.length : ℤ) ∧
              (∀ i, i < nums.val.length → numsGet nums i ≤ cover queries r.val.toNat i) ∧
              (∀ k, k < r.val.toNat →
                ∃ i, i < nums.val.length ∧ numsGet nums i > cover queries k i))) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
        (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
        (hnums : ∀ i, i < nums.val.length → 0 ≤ numsGet nums i ∧ numsGet nums i ≤ 500000)
        (hm_pos : 1 ≤ queries.val.length) (hm_le : queries.val.length ≤ 100000)
        (hrows_len : ∀ j, j < queries.val.length → rowLen queries j = 3)
        (hrows : ∀ j, j < queries.val.length →
          0 ≤ (rowAt queries j).l ∧ (rowAt queries j).l ≤ (rowAt queries j).r ∧
            (rowAt queries j).r < (nums.val.length : ℤ) ∧
              1 ≤ (rowAt queries j).v ∧ (rowAt queries j).v ≤ 5), ∃ r : Std.I64,
          Aegis.MinZeroArray.min_zero_array nums queries = ok r ∧
            ((r.val = -1 ∧
                ∀ k, k ≤ queries.val.length →
                  ∃ i, i < nums.val.length ∧ numsGet nums i > cover queries k i) ∨
              (0 ≤ r.val ∧ r.val ≤ (queries.val.length : ℤ) ∧
                (∀ i, i < nums.val.length → numsGet nums i ≤ cover queries r.val.toNat i) ∧
                (∀ k, k < r.val.toNat →
                  ∃ i, i < nums.val.length ∧ numsGet nums i > cover queries k i)))) := by
    sorry

  /-- The function returns a result r (it does not fail) for every input satisfying the preconditions.
    Preconditions: Let n = len(nums) and m = len(queries). The preconditions are 1 <= n <= 100000, 0 <= nums[i] <= 500000 for every i with 0 <= i < n, 1 <= m <= 100000, and for every j with 0 <= j < m, len(queries[j]) = 3; writing queries[j] = [l_j, r_j, val_j], we have 0 <= l_j <= r_j < n and 1 <= val_j <= 5. -/
  theorem spec_2 (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
      (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
      (hnums : ∀ i, i < nums.val.length → 0 ≤ numsGet nums i ∧ numsGet nums i ≤ 500000)
      (hm_pos : 1 ≤ queries.val.length) (hm_le : queries.val.length ≤ 100000)
      (hrows_len : ∀ j, j < queries.val.length → rowLen queries j = 3)
      (hrows : ∀ j, j < queries.val.length →
        0 ≤ (rowAt queries j).l ∧ (rowAt queries j).l ≤ (rowAt queries j).r ∧
          (rowAt queries j).r < (nums.val.length : ℤ) ∧
            1 ≤ (rowAt queries j).v ∧ (rowAt queries j).v ≤ 5) :
      ∃ r : Std.I64, Aegis.MinZeroArray.min_zero_array nums queries = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
        (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
        (hnums : ∀ i, i < nums.val.length → 0 ≤ numsGet nums i ∧ numsGet nums i ≤ 500000)
        (hm_pos : 1 ≤ queries.val.length) (hm_le : queries.val.length ≤ 100000)
        (hrows_len : ∀ j, j < queries.val.length → rowLen queries j = 3)
        (hrows : ∀ j, j < queries.val.length →
          0 ≤ (rowAt queries j).l ∧ (rowAt queries j).l ≤ (rowAt queries j).r ∧
            (rowAt queries j).r < (nums.val.length : ℤ) ∧
              1 ≤ (rowAt queries j).v ∧ (rowAt queries j).v ≤ 5), ∃ r : Std.I64, Aegis.MinZeroArray.min_zero_array nums queries = ok r) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 if and only if for every i with 0 <= i < len(nums), nums[i] = 0.
    Preconditions: Let n = len(nums) and m = len(queries). The preconditions are 1 <= n <= 100000, 0 <= nums[i] <= 500000 for every i with 0 <= i < n, 1 <= m <= 100000, and for every j with 0 <= j < m, len(queries[j]) = 3; writing queries[j] = [l_j, r_j, val_j], we have 0 <= l_j <= r_j < n and 1 <= val_j <= 5. -/
  theorem spec_3 (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
      (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
      (hnums : ∀ i, i < nums.val.length → 0 ≤ numsGet nums i ∧ numsGet nums i ≤ 500000)
      (hm_pos : 1 ≤ queries.val.length) (hm_le : queries.val.length ≤ 100000)
      (hrows_len : ∀ j, j < queries.val.length → rowLen queries j = 3)
      (hrows : ∀ j, j < queries.val.length →
        0 ≤ (rowAt queries j).l ∧ (rowAt queries j).l ≤ (rowAt queries j).r ∧
          (rowAt queries j).r < (nums.val.length : ℤ) ∧
            1 ≤ (rowAt queries j).v ∧ (rowAt queries j).v ≤ 5) :
      ∀ r : Std.I64,
        Aegis.MinZeroArray.min_zero_array nums queries = ok r →
          (r.val = 0 ↔ ∀ i, i < nums.val.length → numsGet nums i = 0) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
        (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
        (hnums : ∀ i, i < nums.val.length → 0 ≤ numsGet nums i ∧ numsGet nums i ≤ 500000)
        (hm_pos : 1 ≤ queries.val.length) (hm_le : queries.val.length ≤ 100000)
        (hrows_len : ∀ j, j < queries.val.length → rowLen queries j = 3)
        (hrows : ∀ j, j < queries.val.length →
          0 ≤ (rowAt queries j).l ∧ (rowAt queries j).l ≤ (rowAt queries j).r ∧
            (rowAt queries j).r < (nums.val.length : ℤ) ∧
              1 ≤ (rowAt queries j).v ∧ (rowAt queries j).v ≤ 5), ∀ r : Std.I64,
          Aegis.MinZeroArray.min_zero_array nums queries = ok r →
            (r.val = 0 ↔ ∀ i, i < nums.val.length → numsGet nums i = 0)) := by
    sorry

  /-- Let C(k,i) = sum over j with 0 <= j < k and queries[j][0] <= i <= queries[j][1] of queries[j][2], for 0 <= k <= len(queries) and 0 <= i < len(nums). Whenever the function returns a result r, if there exists i with 0 <= i < len(nums) such that nums[i] > C(len(queries), i), then r = -1.
    Preconditions: Let n = len(nums) and m = len(queries). The preconditions are 1 <= n <= 100000, 0 <= nums[i] <= 500000 for every i with 0 <= i < n, 1 <= m <= 100000, and for every j with 0 <= j < m, len(queries[j]) = 3; writing queries[j] = [l_j, r_j, val_j], we have 0 <= l_j <= r_j < n and 1 <= val_j <= 5. -/
  theorem spec_4 (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
      (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
      (hnums : ∀ i, i < nums.val.length → 0 ≤ numsGet nums i ∧ numsGet nums i ≤ 500000)
      (hm_pos : 1 ≤ queries.val.length) (hm_le : queries.val.length ≤ 100000)
      (hrows_len : ∀ j, j < queries.val.length → rowLen queries j = 3)
      (hrows : ∀ j, j < queries.val.length →
        0 ≤ (rowAt queries j).l ∧ (rowAt queries j).l ≤ (rowAt queries j).r ∧
          (rowAt queries j).r < (nums.val.length : ℤ) ∧
            1 ≤ (rowAt queries j).v ∧ (rowAt queries j).v ≤ 5) :
      ∀ r : Std.I64,
        Aegis.MinZeroArray.min_zero_array nums queries = ok r →
          (∃ i,
              i < nums.val.length ∧
                numsGet nums i > cover queries queries.val.length i) →
            r.val = -1 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
        (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
        (hnums : ∀ i, i < nums.val.length → 0 ≤ numsGet nums i ∧ numsGet nums i ≤ 500000)
        (hm_pos : 1 ≤ queries.val.length) (hm_le : queries.val.length ≤ 100000)
        (hrows_len : ∀ j, j < queries.val.length → rowLen queries j = 3)
        (hrows : ∀ j, j < queries.val.length →
          0 ≤ (rowAt queries j).l ∧ (rowAt queries j).l ≤ (rowAt queries j).r ∧
            (rowAt queries j).r < (nums.val.length : ℤ) ∧
              1 ≤ (rowAt queries j).v ∧ (rowAt queries j).v ≤ 5), ∀ r : Std.I64,
          Aegis.MinZeroArray.min_zero_array nums queries = ok r →
            (∃ i,
                i < nums.val.length ∧
                  numsGet nums i > cover queries queries.val.length i) →
              r.val = -1) := by
    sorry

  /-- Let C(k,i) = sum over j with 0 <= j < k and queries[j][0] <= i <= queries[j][1] of queries[j][2], for 0 <= k <= len(queries) and 0 <= i < len(nums). Whenever the function returns a result r with r >= 0, for every k with r <= k <= len(queries) and every i with 0 <= i < len(nums), nums[i] <= C(k,i).
    Preconditions: Let n = len(nums) and m = len(queries). The preconditions are 1 <= n <= 100000, 0 <= nums[i] <= 500000 for every i with 0 <= i < n, 1 <= m <= 100000, and for every j with 0 <= j < m, len(queries[j]) = 3; writing queries[j] = [l_j, r_j, val_j], we have 0 <= l_j <= r_j < n and 1 <= val_j <= 5. -/
  theorem spec_5 (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
      (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
      (hnums : ∀ i, i < nums.val.length → 0 ≤ numsGet nums i ∧ numsGet nums i ≤ 500000)
      (hm_pos : 1 ≤ queries.val.length) (hm_le : queries.val.length ≤ 100000)
      (hrows_len : ∀ j, j < queries.val.length → rowLen queries j = 3)
      (hrows : ∀ j, j < queries.val.length →
        0 ≤ (rowAt queries j).l ∧ (rowAt queries j).l ≤ (rowAt queries j).r ∧
          (rowAt queries j).r < (nums.val.length : ℤ) ∧
            1 ≤ (rowAt queries j).v ∧ (rowAt queries j).v ≤ 5) :
      ∀ r : Std.I64,
        Aegis.MinZeroArray.min_zero_array nums queries = ok r → 0 ≤ r.val →
          ∀ k, r.val.toNat ≤ k → k ≤ queries.val.length →
            ∀ i, i < nums.val.length → numsGet nums i ≤ cover queries k i := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
        (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
        (hnums : ∀ i, i < nums.val.length → 0 ≤ numsGet nums i ∧ numsGet nums i ≤ 500000)
        (hm_pos : 1 ≤ queries.val.length) (hm_le : queries.val.length ≤ 100000)
        (hrows_len : ∀ j, j < queries.val.length → rowLen queries j = 3)
        (hrows : ∀ j, j < queries.val.length →
          0 ≤ (rowAt queries j).l ∧ (rowAt queries j).l ≤ (rowAt queries j).r ∧
            (rowAt queries j).r < (nums.val.length : ℤ) ∧
              1 ≤ (rowAt queries j).v ∧ (rowAt queries j).v ≤ 5), ∀ r : Std.I64,
          Aegis.MinZeroArray.min_zero_array nums queries = ok r → 0 ≤ r.val →
            ∀ k, r.val.toNat ≤ k → k ≤ queries.val.length →
              ∀ i, i < nums.val.length → numsGet nums i ≤ cover queries k i) := by
    sorry

  end AegisSpec.MinZeroArray
