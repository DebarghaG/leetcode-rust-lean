import Aegis.MinZeroArray.Code.Funs

/-!
# Specifications of `Aegis.MinZeroArray.min_zero_array`

LeetCode problem `zero-array-transformation-iv`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinZeroArray

  open Aegis.MinZeroArray (min_zero_array)

  def row (queries : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : List Std.I64 :=
    match queries.val[i]? with
    | some v => v.val
    | none => []

  def ql (queries : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Int :=
    ((row queries i).getD 0 0#i64).val

  def qr (queries : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Int :=
    ((row queries i).getD 1 0#i64).val

  def qv (queries : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Int :=
    ((row queries i).getD 2 0#i64).val

  def numAt (nums : Slice Std.I64) (j : Nat) : Int :=
    (nums.val.getD j 0#i64).val

  def covers (queries : Slice (alloc.vec.Vec Std.I64)) (i j : Nat) : Prop :=
    ql queries i ≤ (j : Int) ∧ (j : Int) ≤ qr queries i

  def Feasible (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64)) (k : Nat) : Prop :=
    ∀ j : Nat, j < nums.val.length →
      ∃ T : Finset Nat,
        (∀ i ∈ T, i < k ∧ covers queries i j) ∧
        (∑ i ∈ T, qv queries i) = numAt nums j

  def coverSum (queries : Slice (alloc.vec.Vec Std.I64)) (k j : Nat) : Int :=
    ∑ i ∈ (Finset.range k).filter (fun i => ql queries i ≤ (j : Int) ∧ (j : Int) ≤ qr queries i),
      qv queries i

  /-- Whenever the function returns a result r, if there exists k with 0 <= k <= m such that k is feasible, then r is the least such k; otherwise r = -1.
    Preconditions: Let n = len(nums) and m = len(queries). Assume 1 <= n <= 10; for every j with 0 <= j < n, 0 <= nums[j] <= 1000; 1 <= m <= 1000; for every i with 0 <= i < m, len(queries[i]) = 3, and with l_i = queries[i][0], r_i = queries[i][1], v_i = queries[i][2], we have 0 <= l_i <= r_i < n and 1 <= v_i <= 10. For 0 <= k <= m, say k is feasible iff for every j with 0 <= j < n there exists a subset T_j (possibly empty) of {i | 0 <= i < k and l_i <= j <= r_i} such that the sum of v_i over i in T_j equals nums[j]. -/
  theorem spec_1
      (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 10)
      (hnums : ∀ j, j < nums.val.length → 0 ≤ numAt nums j ∧ numAt nums j ≤ 1000)
      (hm1 : 1 ≤ queries.val.length) (hm2 : queries.val.length ≤ 1000)
      (hlen : ∀ i, i < queries.val.length → (row queries i).length = 3)
      (hint : ∀ i, i < queries.val.length →
        0 ≤ ql queries i ∧ ql queries i ≤ qr queries i ∧
          qr queries i < (nums.val.length : Int))
      (hval : ∀ i, i < queries.val.length → 1 ≤ qv queries i ∧ qv queries i ≤ 10) :
      ∀ r, min_zero_array nums queries = ok r →
        ((∃ k, k ≤ queries.val.length ∧ Feasible nums queries k) →
          ∃ k : Nat, r.val = (k : Int) ∧ k ≤ queries.val.length ∧ Feasible nums queries k ∧
            ∀ k', k' ≤ queries.val.length → Feasible nums queries k' → k ≤ k') ∧
        ((¬ ∃ k, k ≤ queries.val.length ∧ Feasible nums queries k) → r.val = -1) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 10)
        (hnums : ∀ j, j < nums.val.length → 0 ≤ numAt nums j ∧ numAt nums j ≤ 1000)
        (hm1 : 1 ≤ queries.val.length) (hm2 : queries.val.length ≤ 1000)
        (hlen : ∀ i, i < queries.val.length → (row queries i).length = 3)
        (hint : ∀ i, i < queries.val.length →
          0 ≤ ql queries i ∧ ql queries i ≤ qr queries i ∧
            qr queries i < (nums.val.length : Int))
        (hval : ∀ i, i < queries.val.length → 1 ≤ qv queries i ∧ qv queries i ≤ 10), ∀ r, min_zero_array nums queries = ok r →
          ((∃ k, k ≤ queries.val.length ∧ Feasible nums queries k) →
            ∃ k : Nat, r.val = (k : Int) ∧ k ≤ queries.val.length ∧ Feasible nums queries k ∧
              ∀ k', k' ≤ queries.val.length → Feasible nums queries k' → k ≤ k') ∧
          ((¬ ∃ k, k ≤ queries.val.length ∧ Feasible nums queries k) → r.val = -1)) := by
    sorry

  /-- The function returns a result r; it does not fail, panic, or overflow.
    Preconditions: Let n = len(nums) and m = len(queries). Assume 1 <= n <= 10; for every j with 0 <= j < n, 0 <= nums[j] <= 1000; 1 <= m <= 1000; for every i with 0 <= i < m, len(queries[i]) = 3, and with l_i = queries[i][0], r_i = queries[i][1], v_i = queries[i][2], we have 0 <= l_i <= r_i < n and 1 <= v_i <= 10. For 0 <= k <= m, say k is feasible iff for every j with 0 <= j < n there exists a subset T_j (possibly empty) of {i | 0 <= i < k and l_i <= j <= r_i} such that the sum of v_i over i in T_j equals nums[j]. -/
  theorem spec_2
      (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 10)
      (hnums : ∀ j, j < nums.val.length → 0 ≤ numAt nums j ∧ numAt nums j ≤ 1000)
      (hm1 : 1 ≤ queries.val.length) (hm2 : queries.val.length ≤ 1000)
      (hlen : ∀ i, i < queries.val.length → (row queries i).length = 3)
      (hint : ∀ i, i < queries.val.length →
        0 ≤ ql queries i ∧ ql queries i ≤ qr queries i ∧
          qr queries i < (nums.val.length : Int))
      (hval : ∀ i, i < queries.val.length → 1 ≤ qv queries i ∧ qv queries i ≤ 10) :
      ∃ r, min_zero_array nums queries = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 10)
        (hnums : ∀ j, j < nums.val.length → 0 ≤ numAt nums j ∧ numAt nums j ≤ 1000)
        (hm1 : 1 ≤ queries.val.length) (hm2 : queries.val.length ≤ 1000)
        (hlen : ∀ i, i < queries.val.length → (row queries i).length = 3)
        (hint : ∀ i, i < queries.val.length →
          0 ≤ ql queries i ∧ ql queries i ≤ qr queries i ∧
            qr queries i < (nums.val.length : Int))
        (hval : ∀ i, i < queries.val.length → 1 ≤ qv queries i ∧ qv queries i ≤ 10), ∃ r, min_zero_array nums queries = ok r) := by
    sorry

  /-- Whenever the function returns a result r, either r = -1 or 0 <= r <= m.
    Preconditions: Let n = len(nums) and m = len(queries). Assume 1 <= n <= 10; for every j with 0 <= j < n, 0 <= nums[j] <= 1000; 1 <= m <= 1000; for every i with 0 <= i < m, len(queries[i]) = 3, and with l_i = queries[i][0], r_i = queries[i][1], v_i = queries[i][2], we have 0 <= l_i <= r_i < n and 1 <= v_i <= 10. For 0 <= k <= m, say k is feasible iff for every j with 0 <= j < n there exists a subset T_j (possibly empty) of {i | 0 <= i < k and l_i <= j <= r_i} such that the sum of v_i over i in T_j equals nums[j]. -/
  theorem spec_3
      (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 10)
      (hnums : ∀ j, j < nums.val.length → 0 ≤ numAt nums j ∧ numAt nums j ≤ 1000)
      (hm1 : 1 ≤ queries.val.length) (hm2 : queries.val.length ≤ 1000)
      (hlen : ∀ i, i < queries.val.length → (row queries i).length = 3)
      (hint : ∀ i, i < queries.val.length →
        0 ≤ ql queries i ∧ ql queries i ≤ qr queries i ∧
          qr queries i < (nums.val.length : Int))
      (hval : ∀ i, i < queries.val.length → 1 ≤ qv queries i ∧ qv queries i ≤ 10) :
      ∀ r, min_zero_array nums queries = ok r →
        r.val = -1 ∨ (0 ≤ r.val ∧ r.val ≤ (queries.val.length : Int)) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 10)
        (hnums : ∀ j, j < nums.val.length → 0 ≤ numAt nums j ∧ numAt nums j ≤ 1000)
        (hm1 : 1 ≤ queries.val.length) (hm2 : queries.val.length ≤ 1000)
        (hlen : ∀ i, i < queries.val.length → (row queries i).length = 3)
        (hint : ∀ i, i < queries.val.length →
          0 ≤ ql queries i ∧ ql queries i ≤ qr queries i ∧
            qr queries i < (nums.val.length : Int))
        (hval : ∀ i, i < queries.val.length → 1 ≤ qv queries i ∧ qv queries i ≤ 10), ∀ r, min_zero_array nums queries = ok r →
          r.val = -1 ∨ (0 ≤ r.val ∧ r.val ≤ (queries.val.length : Int))) := by
    sorry

  /-- Whenever the function returns a result r with 0 <= r <= m, r is feasible: for every j with 0 <= j < n there exists a subset T_j of {i | 0 <= i < r and l_i <= j <= r_i} whose v_i values sum to nums[j].
    Preconditions: Let n = len(nums) and m = len(queries). Assume 1 <= n <= 10; for every j with 0 <= j < n, 0 <= nums[j] <= 1000; 1 <= m <= 1000; for every i with 0 <= i < m, len(queries[i]) = 3, and with l_i = queries[i][0], r_i = queries[i][1], v_i = queries[i][2], we have 0 <= l_i <= r_i < n and 1 <= v_i <= 10. For 0 <= k <= m, say k is feasible iff for every j with 0 <= j < n there exists a subset T_j (possibly empty) of {i | 0 <= i < k and l_i <= j <= r_i} such that the sum of v_i over i in T_j equals nums[j]. -/
  theorem spec_4
      (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 10)
      (hnums : ∀ j, j < nums.val.length → 0 ≤ numAt nums j ∧ numAt nums j ≤ 1000)
      (hm1 : 1 ≤ queries.val.length) (hm2 : queries.val.length ≤ 1000)
      (hlen : ∀ i, i < queries.val.length → (row queries i).length = 3)
      (hint : ∀ i, i < queries.val.length →
        0 ≤ ql queries i ∧ ql queries i ≤ qr queries i ∧
          qr queries i < (nums.val.length : Int))
      (hval : ∀ i, i < queries.val.length → 1 ≤ qv queries i ∧ qv queries i ≤ 10) :
      ∀ r, min_zero_array nums queries = ok r →
        0 ≤ r.val → r.val ≤ (queries.val.length : Int) →
          Feasible nums queries r.val.toNat := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 10)
        (hnums : ∀ j, j < nums.val.length → 0 ≤ numAt nums j ∧ numAt nums j ≤ 1000)
        (hm1 : 1 ≤ queries.val.length) (hm2 : queries.val.length ≤ 1000)
        (hlen : ∀ i, i < queries.val.length → (row queries i).length = 3)
        (hint : ∀ i, i < queries.val.length →
          0 ≤ ql queries i ∧ ql queries i ≤ qr queries i ∧
            qr queries i < (nums.val.length : Int))
        (hval : ∀ i, i < queries.val.length → 1 ≤ qv queries i ∧ qv queries i ≤ 10), ∀ r, min_zero_array nums queries = ok r →
          0 ≤ r.val → r.val ≤ (queries.val.length : Int) →
            Feasible nums queries r.val.toNat) := by
    sorry

  /-- Whenever the function returns a result r with 0 <= r <= m, every k with 0 <= k < r is not feasible.
    Preconditions: Let n = len(nums) and m = len(queries). Assume 1 <= n <= 10; for every j with 0 <= j < n, 0 <= nums[j] <= 1000; 1 <= m <= 1000; for every i with 0 <= i < m, len(queries[i]) = 3, and with l_i = queries[i][0], r_i = queries[i][1], v_i = queries[i][2], we have 0 <= l_i <= r_i < n and 1 <= v_i <= 10. For 0 <= k <= m, say k is feasible iff for every j with 0 <= j < n there exists a subset T_j (possibly empty) of {i | 0 <= i < k and l_i <= j <= r_i} such that the sum of v_i over i in T_j equals nums[j]. -/
  theorem spec_5
      (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 10)
      (hnums : ∀ j, j < nums.val.length → 0 ≤ numAt nums j ∧ numAt nums j ≤ 1000)
      (hm1 : 1 ≤ queries.val.length) (hm2 : queries.val.length ≤ 1000)
      (hlen : ∀ i, i < queries.val.length → (row queries i).length = 3)
      (hint : ∀ i, i < queries.val.length →
        0 ≤ ql queries i ∧ ql queries i ≤ qr queries i ∧
          qr queries i < (nums.val.length : Int))
      (hval : ∀ i, i < queries.val.length → 1 ≤ qv queries i ∧ qv queries i ≤ 10) :
      ∀ r, min_zero_array nums queries = ok r →
        0 ≤ r.val → r.val ≤ (queries.val.length : Int) →
          ∀ k, k < r.val.toNat → ¬ Feasible nums queries k := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 10)
        (hnums : ∀ j, j < nums.val.length → 0 ≤ numAt nums j ∧ numAt nums j ≤ 1000)
        (hm1 : 1 ≤ queries.val.length) (hm2 : queries.val.length ≤ 1000)
        (hlen : ∀ i, i < queries.val.length → (row queries i).length = 3)
        (hint : ∀ i, i < queries.val.length →
          0 ≤ ql queries i ∧ ql queries i ≤ qr queries i ∧
            qr queries i < (nums.val.length : Int))
        (hval : ∀ i, i < queries.val.length → 1 ≤ qv queries i ∧ qv queries i ≤ 10), ∀ r, min_zero_array nums queries = ok r →
          0 ≤ r.val → r.val ≤ (queries.val.length : Int) →
            ∀ k, k < r.val.toNat → ¬ Feasible nums queries k) := by
    sorry

  /-- Whenever the function returns a result r, r = -1 if and only if no k with 0 <= k <= m is feasible.
    Preconditions: Let n = len(nums) and m = len(queries). Assume 1 <= n <= 10; for every j with 0 <= j < n, 0 <= nums[j] <= 1000; 1 <= m <= 1000; for every i with 0 <= i < m, len(queries[i]) = 3, and with l_i = queries[i][0], r_i = queries[i][1], v_i = queries[i][2], we have 0 <= l_i <= r_i < n and 1 <= v_i <= 10. For 0 <= k <= m, say k is feasible iff for every j with 0 <= j < n there exists a subset T_j (possibly empty) of {i | 0 <= i < k and l_i <= j <= r_i} such that the sum of v_i over i in T_j equals nums[j]. -/
  theorem spec_6
      (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 10)
      (hnums : ∀ j, j < nums.val.length → 0 ≤ numAt nums j ∧ numAt nums j ≤ 1000)
      (hm1 : 1 ≤ queries.val.length) (hm2 : queries.val.length ≤ 1000)
      (hlen : ∀ i, i < queries.val.length → (row queries i).length = 3)
      (hint : ∀ i, i < queries.val.length →
        0 ≤ ql queries i ∧ ql queries i ≤ qr queries i ∧
          qr queries i < (nums.val.length : Int))
      (hval : ∀ i, i < queries.val.length → 1 ≤ qv queries i ∧ qv queries i ≤ 10) :
      ∀ r, min_zero_array nums queries = ok r →
        (r.val = -1 ↔ ¬ ∃ k, k ≤ queries.val.length ∧ Feasible nums queries k) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 10)
        (hnums : ∀ j, j < nums.val.length → 0 ≤ numAt nums j ∧ numAt nums j ≤ 1000)
        (hm1 : 1 ≤ queries.val.length) (hm2 : queries.val.length ≤ 1000)
        (hlen : ∀ i, i < queries.val.length → (row queries i).length = 3)
        (hint : ∀ i, i < queries.val.length →
          0 ≤ ql queries i ∧ ql queries i ≤ qr queries i ∧
            qr queries i < (nums.val.length : Int))
        (hval : ∀ i, i < queries.val.length → 1 ≤ qv queries i ∧ qv queries i ≤ 10), ∀ r, min_zero_array nums queries = ok r →
          (r.val = -1 ↔ ¬ ∃ k, k ≤ queries.val.length ∧ Feasible nums queries k)) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 if and only if nums[j] = 0 for every j with 0 <= j < n.
    Preconditions: Let n = len(nums) and m = len(queries). Assume 1 <= n <= 10; for every j with 0 <= j < n, 0 <= nums[j] <= 1000; 1 <= m <= 1000; for every i with 0 <= i < m, len(queries[i]) = 3, and with l_i = queries[i][0], r_i = queries[i][1], v_i = queries[i][2], we have 0 <= l_i <= r_i < n and 1 <= v_i <= 10. For 0 <= k <= m, say k is feasible iff for every j with 0 <= j < n there exists a subset T_j (possibly empty) of {i | 0 <= i < k and l_i <= j <= r_i} such that the sum of v_i over i in T_j equals nums[j]. -/
  theorem spec_7
      (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 10)
      (hnums : ∀ j, j < nums.val.length → 0 ≤ numAt nums j ∧ numAt nums j ≤ 1000)
      (hm1 : 1 ≤ queries.val.length) (hm2 : queries.val.length ≤ 1000)
      (hlen : ∀ i, i < queries.val.length → (row queries i).length = 3)
      (hint : ∀ i, i < queries.val.length →
        0 ≤ ql queries i ∧ ql queries i ≤ qr queries i ∧
          qr queries i < (nums.val.length : Int))
      (hval : ∀ i, i < queries.val.length → 1 ≤ qv queries i ∧ qv queries i ≤ 10) :
      ∀ r, min_zero_array nums queries = ok r →
        (r.val = 0 ↔ ∀ j, j < nums.val.length → numAt nums j = 0) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 10)
        (hnums : ∀ j, j < nums.val.length → 0 ≤ numAt nums j ∧ numAt nums j ≤ 1000)
        (hm1 : 1 ≤ queries.val.length) (hm2 : queries.val.length ≤ 1000)
        (hlen : ∀ i, i < queries.val.length → (row queries i).length = 3)
        (hint : ∀ i, i < queries.val.length →
          0 ≤ ql queries i ∧ ql queries i ≤ qr queries i ∧
            qr queries i < (nums.val.length : Int))
        (hval : ∀ i, i < queries.val.length → 1 ≤ qv queries i ∧ qv queries i ≤ 10), ∀ r, min_zero_array nums queries = ok r →
          (r.val = 0 ↔ ∀ j, j < nums.val.length → numAt nums j = 0)) := by
    sorry

  /-- Whenever the function returns a result r with 0 <= r <= m, for every j with 0 <= j < n, nums[j] is at most the sum of v_i over all i satisfying 0 <= i < r and l_i <= j <= r_i; the sum over an empty set is 0.
    Preconditions: Let n = len(nums) and m = len(queries). Assume 1 <= n <= 10; for every j with 0 <= j < n, 0 <= nums[j] <= 1000; 1 <= m <= 1000; for every i with 0 <= i < m, len(queries[i]) = 3, and with l_i = queries[i][0], r_i = queries[i][1], v_i = queries[i][2], we have 0 <= l_i <= r_i < n and 1 <= v_i <= 10. For 0 <= k <= m, say k is feasible iff for every j with 0 <= j < n there exists a subset T_j (possibly empty) of {i | 0 <= i < k and l_i <= j <= r_i} such that the sum of v_i over i in T_j equals nums[j]. -/
  theorem spec_8
      (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 10)
      (hnums : ∀ j, j < nums.val.length → 0 ≤ numAt nums j ∧ numAt nums j ≤ 1000)
      (hm1 : 1 ≤ queries.val.length) (hm2 : queries.val.length ≤ 1000)
      (hlen : ∀ i, i < queries.val.length → (row queries i).length = 3)
      (hint : ∀ i, i < queries.val.length →
        0 ≤ ql queries i ∧ ql queries i ≤ qr queries i ∧
          qr queries i < (nums.val.length : Int))
      (hval : ∀ i, i < queries.val.length → 1 ≤ qv queries i ∧ qv queries i ≤ 10) :
      ∀ r, min_zero_array nums queries = ok r →
        0 ≤ r.val → r.val ≤ (queries.val.length : Int) →
          ∀ j, j < nums.val.length → numAt nums j ≤ coverSum queries r.val.toNat j := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 10)
        (hnums : ∀ j, j < nums.val.length → 0 ≤ numAt nums j ∧ numAt nums j ≤ 1000)
        (hm1 : 1 ≤ queries.val.length) (hm2 : queries.val.length ≤ 1000)
        (hlen : ∀ i, i < queries.val.length → (row queries i).length = 3)
        (hint : ∀ i, i < queries.val.length →
          0 ≤ ql queries i ∧ ql queries i ≤ qr queries i ∧
            qr queries i < (nums.val.length : Int))
        (hval : ∀ i, i < queries.val.length → 1 ≤ qv queries i ∧ qv queries i ≤ 10), ∀ r, min_zero_array nums queries = ok r →
          0 ≤ r.val → r.val ≤ (queries.val.length : Int) →
            ∀ j, j < nums.val.length → numAt nums j ≤ coverSum queries r.val.toNat j) := by
    sorry

  /-- Whenever the function returns a result r, r = -1.
    Preconditions: Let n = len(nums) and m = len(queries). Assume 1 <= n <= 10; for every j with 0 <= j < n, 0 <= nums[j] <= 1000; 1 <= m <= 1000; for every i with 0 <= i < m, len(queries[i]) = 3, and with l_i = queries[i][0], r_i = queries[i][1], v_i = queries[i][2], we have 0 <= l_i <= r_i < n and 1 <= v_i <= 10. For 0 <= k <= m, say k is feasible iff for every j with 0 <= j < n there exists a subset T_j (possibly empty) of {i | 0 <= i < k and l_i <= j <= r_i} such that the sum of v_i over i in T_j equals nums[j]. Additionally assume there exists j with 0 <= j < n such that nums[j] is greater than the sum of v_i over all i satisfying 0 <= i < m and l_i <= j <= r_i; the sum over an empty set is 0. -/
  theorem spec_9
      (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 10)
      (hnums : ∀ j, j < nums.val.length → 0 ≤ numAt nums j ∧ numAt nums j ≤ 1000)
      (hm1 : 1 ≤ queries.val.length) (hm2 : queries.val.length ≤ 1000)
      (hlen : ∀ i, i < queries.val.length → (row queries i).length = 3)
      (hint : ∀ i, i < queries.val.length →
        0 ≤ ql queries i ∧ ql queries i ≤ qr queries i ∧
          qr queries i < (nums.val.length : Int))
      (hval : ∀ i, i < queries.val.length → 1 ≤ qv queries i ∧ qv queries i ≤ 10)
      (hneeds : ∃ j, j < nums.val.length ∧
        numAt nums j > coverSum queries queries.val.length j) :
      ∀ r, min_zero_array nums queries = ok r → r.val = -1 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 10)
        (hnums : ∀ j, j < nums.val.length → 0 ≤ numAt nums j ∧ numAt nums j ≤ 1000)
        (hm1 : 1 ≤ queries.val.length) (hm2 : queries.val.length ≤ 1000)
        (hlen : ∀ i, i < queries.val.length → (row queries i).length = 3)
        (hint : ∀ i, i < queries.val.length →
          0 ≤ ql queries i ∧ ql queries i ≤ qr queries i ∧
            qr queries i < (nums.val.length : Int))
        (hval : ∀ i, i < queries.val.length → 1 ≤ qv queries i ∧ qv queries i ≤ 10)
        (hneeds : ∃ j, j < nums.val.length ∧
          numAt nums j > coverSum queries queries.val.length j), ∀ r, min_zero_array nums queries = ok r → r.val = -1) := by
    sorry

  /-- Whenever the function returns a result r with 0 <= r <= m, every k with r <= k <= m is feasible.
    Preconditions: Let n = len(nums) and m = len(queries). Assume 1 <= n <= 10; for every j with 0 <= j < n, 0 <= nums[j] <= 1000; 1 <= m <= 1000; for every i with 0 <= i < m, len(queries[i]) = 3, and with l_i = queries[i][0], r_i = queries[i][1], v_i = queries[i][2], we have 0 <= l_i <= r_i < n and 1 <= v_i <= 10. For 0 <= k <= m, say k is feasible iff for every j with 0 <= j < n there exists a subset T_j (possibly empty) of {i | 0 <= i < k and l_i <= j <= r_i} such that the sum of v_i over i in T_j equals nums[j]. -/
  theorem spec_10
      (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 10)
      (hnums : ∀ j, j < nums.val.length → 0 ≤ numAt nums j ∧ numAt nums j ≤ 1000)
      (hm1 : 1 ≤ queries.val.length) (hm2 : queries.val.length ≤ 1000)
      (hlen : ∀ i, i < queries.val.length → (row queries i).length = 3)
      (hint : ∀ i, i < queries.val.length →
        0 ≤ ql queries i ∧ ql queries i ≤ qr queries i ∧
          qr queries i < (nums.val.length : Int))
      (hval : ∀ i, i < queries.val.length → 1 ≤ qv queries i ∧ qv queries i ≤ 10) :
      ∀ r, min_zero_array nums queries = ok r →
        0 ≤ r.val → r.val ≤ (queries.val.length : Int) →
          ∀ k, r.val.toNat ≤ k → k ≤ queries.val.length → Feasible nums queries k := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 10)
        (hnums : ∀ j, j < nums.val.length → 0 ≤ numAt nums j ∧ numAt nums j ≤ 1000)
        (hm1 : 1 ≤ queries.val.length) (hm2 : queries.val.length ≤ 1000)
        (hlen : ∀ i, i < queries.val.length → (row queries i).length = 3)
        (hint : ∀ i, i < queries.val.length →
          0 ≤ ql queries i ∧ ql queries i ≤ qr queries i ∧
            qr queries i < (nums.val.length : Int))
        (hval : ∀ i, i < queries.val.length → 1 ≤ qv queries i ∧ qv queries i ≤ 10), ∀ r, min_zero_array nums queries = ok r →
          0 ≤ r.val → r.val ≤ (queries.val.length : Int) →
            ∀ k, r.val.toNat ≤ k → k ≤ queries.val.length → Feasible nums queries k) := by
    sorry

  /-- Whenever the function returns a result r, for every k with 0 <= k <= m, if k is feasible then r != -1 and r <= k.
    Preconditions: Let n = len(nums) and m = len(queries). Assume 1 <= n <= 10; for every j with 0 <= j < n, 0 <= nums[j] <= 1000; 1 <= m <= 1000; for every i with 0 <= i < m, len(queries[i]) = 3, and with l_i = queries[i][0], r_i = queries[i][1], v_i = queries[i][2], we have 0 <= l_i <= r_i < n and 1 <= v_i <= 10. For 0 <= k <= m, say k is feasible iff for every j with 0 <= j < n there exists a subset T_j (possibly empty) of {i | 0 <= i < k and l_i <= j <= r_i} such that the sum of v_i over i in T_j equals nums[j]. -/
  theorem spec_11
      (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 10)
      (hnums : ∀ j, j < nums.val.length → 0 ≤ numAt nums j ∧ numAt nums j ≤ 1000)
      (hm1 : 1 ≤ queries.val.length) (hm2 : queries.val.length ≤ 1000)
      (hlen : ∀ i, i < queries.val.length → (row queries i).length = 3)
      (hint : ∀ i, i < queries.val.length →
        0 ≤ ql queries i ∧ ql queries i ≤ qr queries i ∧
          qr queries i < (nums.val.length : Int))
      (hval : ∀ i, i < queries.val.length → 1 ≤ qv queries i ∧ qv queries i ≤ 10) :
      ∀ r, min_zero_array nums queries = ok r →
        ∀ k, k ≤ queries.val.length → Feasible nums queries k →
          r.val ≠ -1 ∧ r.val ≤ (k : Int) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 10)
        (hnums : ∀ j, j < nums.val.length → 0 ≤ numAt nums j ∧ numAt nums j ≤ 1000)
        (hm1 : 1 ≤ queries.val.length) (hm2 : queries.val.length ≤ 1000)
        (hlen : ∀ i, i < queries.val.length → (row queries i).length = 3)
        (hint : ∀ i, i < queries.val.length →
          0 ≤ ql queries i ∧ ql queries i ≤ qr queries i ∧
            qr queries i < (nums.val.length : Int))
        (hval : ∀ i, i < queries.val.length → 1 ≤ qv queries i ∧ qv queries i ≤ 10), ∀ r, min_zero_array nums queries = ok r →
          ∀ k, k ≤ queries.val.length → Feasible nums queries k →
            r.val ≠ -1 ∧ r.val ≤ (k : Int)) := by
    sorry

  /-- The call min_zero_array(nums, queries2) returns the result r.
    Preconditions: Let n = len(nums) and m = len(queries). Assume 1 <= n <= 10; for every j with 0 <= j < n, 0 <= nums[j] <= 1000; 1 <= m <= 1000; for every i with 0 <= i < m, len(queries[i]) = 3, and with l_i = queries[i][0], r_i = queries[i][1], v_i = queries[i][2], we have 0 <= l_i <= r_i < n and 1 <= v_i <= 10. For 0 <= k <= m, say k is feasible iff for every j with 0 <= j < n there exists a subset T_j (possibly empty) of {i | 0 <= i < k and l_i <= j <= r_i} such that the sum of v_i over i in T_j equals nums[j]. Let r be the value returned by min_zero_array(nums, queries), and assume 0 <= r <= m. Let queries2 be any slice of vectors of i64 with m2 = len(queries2) satisfying 1 <= m2 <= 1000; for every i with 0 <= i < m2, len(queries2[i]) = 3, and with l2_i = queries2[i][0], r2_i = queries2[i][1], v2_i = queries2[i][2], we have 0 <= l2_i <= r2_i < n and 1 <= v2_i <= 10; m2 >= r; and for every i with 0 <= i < r, queries2[i] = queries[i]. -/
  theorem spec_12
      (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 10)
      (hnums : ∀ j, j < nums.val.length → 0 ≤ numAt nums j ∧ numAt nums j ≤ 1000)
      (hm1 : 1 ≤ queries.val.length) (hm2 : queries.val.length ≤ 1000)
      (hlen : ∀ i, i < queries.val.length → (row queries i).length = 3)
      (hint : ∀ i, i < queries.val.length →
        0 ≤ ql queries i ∧ ql queries i ≤ qr queries i ∧
          qr queries i < (nums.val.length : Int))
      (hval : ∀ i, i < queries.val.length → 1 ≤ qv queries i ∧ qv queries i ≤ 10) :
      ∀ r, min_zero_array nums queries = ok r →
        0 ≤ r.val → r.val ≤ (queries.val.length : Int) →
          ∀ queries2 : Slice (alloc.vec.Vec Std.I64),
            1 ≤ queries2.val.length →
            queries2.val.length ≤ 1000 →
            (∀ i, i < queries2.val.length → (row queries2 i).length = 3) →
            (∀ i, i < queries2.val.length →
              0 ≤ ql queries2 i ∧ ql queries2 i ≤ qr queries2 i ∧
                qr queries2 i < (nums.val.length : Int)) →
            (∀ i, i < queries2.val.length → 1 ≤ qv queries2 i ∧ qv queries2 i ≤ 10) →
            r.val.toNat ≤ queries2.val.length →
            (∀ i, i < r.val.toNat → row queries2 i = row queries i) →
              min_zero_array nums queries2 = ok r := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 10)
        (hnums : ∀ j, j < nums.val.length → 0 ≤ numAt nums j ∧ numAt nums j ≤ 1000)
        (hm1 : 1 ≤ queries.val.length) (hm2 : queries.val.length ≤ 1000)
        (hlen : ∀ i, i < queries.val.length → (row queries i).length = 3)
        (hint : ∀ i, i < queries.val.length →
          0 ≤ ql queries i ∧ ql queries i ≤ qr queries i ∧
            qr queries i < (nums.val.length : Int))
        (hval : ∀ i, i < queries.val.length → 1 ≤ qv queries i ∧ qv queries i ≤ 10), ∀ r, min_zero_array nums queries = ok r →
          0 ≤ r.val → r.val ≤ (queries.val.length : Int) →
            ∀ queries2 : Slice (alloc.vec.Vec Std.I64),
              1 ≤ queries2.val.length →
              queries2.val.length ≤ 1000 →
              (∀ i, i < queries2.val.length → (row queries2 i).length = 3) →
              (∀ i, i < queries2.val.length →
                0 ≤ ql queries2 i ∧ ql queries2 i ≤ qr queries2 i ∧
                  qr queries2 i < (nums.val.length : Int)) →
              (∀ i, i < queries2.val.length → 1 ≤ qv queries2 i ∧ qv queries2 i ≤ 10) →
              r.val.toNat ≤ queries2.val.length →
              (∀ i, i < r.val.toNat → row queries2 i = row queries i) →
                min_zero_array nums queries2 = ok r) := by
    sorry

  end AegisSpec.MinZeroArray
