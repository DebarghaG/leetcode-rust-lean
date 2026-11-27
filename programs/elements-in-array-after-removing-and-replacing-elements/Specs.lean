import Aegis.ElementInNums.Code.Funs

/-!
# Specifications of `Aegis.ElementInNums.element_in_nums`

LeetCode problem `elements-in-array-after-removing-and-replacing-elements`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.ElementInNums

  namespace AegisSpec.ElementInNums

  def elemsAt (l : List I64) (i : Int) : Int := ((l[i.toNat]?).map (fun v => v.val)).getD 0

  def outAt (l : List I64) (j : Nat) : Int := ((l[j]?).map (fun v => v.val)).getD 0

  def queryAt (queries : List (alloc.vec.Vec I64)) (j : Nat) : List Int :=
    ((queries[j]?).map (fun q => q.val.map (fun v => v.val))).getD []

  def queryT (queries : List (alloc.vec.Vec I64)) (j : Nat) : Int := (queryAt queries j).getD 0 0

  def queryX (queries : List (alloc.vec.Vec I64)) (j : Nat) : Int := (queryAt queries j).getD 1 0

  def periodMod (m t : Int) : Int := t % (2 * m)

  /-- Whenever the function returns a result r, len(r) = len(queries), and for every j with 0 <= j < len(queries), writing m = len(nums), t = queries[j][0], x = queries[j][1], and p = t mod (2*m), so 0 <= p < 2*m, we have: (1) if p <= m and p + x < m, then r[j] = nums[p + x]; (2) if p <= m and p + x >= m, then r[j] = -1; (3) if p > m and x < p - m, then r[j] = nums[x]; (4) if p > m and x >= p - m, then r[j] = -1.
    Preconditions: 1 <= len(nums) <= 100; 1 <= len(queries) <= 100000; for every j with 0 <= j < len(queries), len(queries[j]) = 2, 0 <= queries[j][0] <= 100000, and 0 <= queries[j][1] < len(nums); for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100. -/
  theorem spec_1
      (nums : Slice I64) (queries : Slice (alloc.vec.Vec I64))
      (h_nums_len_ge : 1 ≤ nums.val.length) (h_nums_len_le : nums.val.length ≤ 100)
      (h_queries_len_ge : 1 ≤ queries.val.length) (h_queries_len_le : queries.val.length ≤ 100000)
      (h_query_len : ∀ j, j < queries.val.length → (queryAt queries.val j).length = 2)
      (h_query_t : ∀ j, j < queries.val.length →
        0 ≤ queryT queries.val j ∧ queryT queries.val j ≤ 100000)
      (h_query_x : ∀ j, j < queries.val.length →
        0 ≤ queryX queries.val j ∧ queryX queries.val j < (nums.val.length : Int))
      (h_nums_val : ∀ i : Nat, i < nums.val.length →
        0 ≤ elemsAt nums.val (i : Int) ∧ elemsAt nums.val (i : Int) ≤ 100)
      (r : alloc.vec.Vec I64)
      (h_ret : element_in_nums nums queries = ok r) :
      r.val.length = queries.val.length ∧
        ∀ j, j < queries.val.length →
          (let m : Int := (nums.val.length : Int)
           let t : Int := queryT queries.val j
           let p : Int := periodMod m t
           let x : Int := queryX queries.val j
           0 ≤ p ∧ p < 2 * m ∧
             ((p ≤ m → p + x < m → outAt r.val j = elemsAt nums.val (p + x)) ∧
              (p ≤ m → m ≤ p + x → outAt r.val j = -1) ∧
              (m < p → x < p - m → outAt r.val j = elemsAt nums.val x) ∧
              (m < p → p - m ≤ x → outAt r.val j = -1))) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice I64) (queries : Slice (alloc.vec.Vec I64))
        (h_nums_len_ge : 1 ≤ nums.val.length) (h_nums_len_le : nums.val.length ≤ 100)
        (h_queries_len_ge : 1 ≤ queries.val.length) (h_queries_len_le : queries.val.length ≤ 100000)
        (h_query_len : ∀ j, j < queries.val.length → (queryAt queries.val j).length = 2)
        (h_query_t : ∀ j, j < queries.val.length →
          0 ≤ queryT queries.val j ∧ queryT queries.val j ≤ 100000)
        (h_query_x : ∀ j, j < queries.val.length →
          0 ≤ queryX queries.val j ∧ queryX queries.val j < (nums.val.length : Int))
        (h_nums_val : ∀ i : Nat, i < nums.val.length →
          0 ≤ elemsAt nums.val (i : Int) ∧ elemsAt nums.val (i : Int) ≤ 100)
        (r : alloc.vec.Vec I64)
        (h_ret : element_in_nums nums queries = ok r), r.val.length = queries.val.length ∧
          ∀ j, j < queries.val.length →
            (let m : Int := (nums.val.length : Int)
             let t : Int := queryT queries.val j
             let p : Int := periodMod m t
             let x : Int := queryX queries.val j
             0 ≤ p ∧ p < 2 * m ∧
               ((p ≤ m → p + x < m → outAt r.val j = elemsAt nums.val (p + x)) ∧
                (p ≤ m → m ≤ p + x → outAt r.val j = -1) ∧
                (m < p → x < p - m → outAt r.val j = elemsAt nums.val x) ∧
                (m < p → p - m ≤ x → outAt r.val j = -1)))) := by
    sorry

  /-- Whenever the function returns a result r, len(r) = len(queries).
    Preconditions: 1 <= len(nums) <= 100; 1 <= len(queries) <= 100000; for every j with 0 <= j < len(queries), len(queries[j]) = 2, 0 <= queries[j][0] <= 100000, and 0 <= queries[j][1] < len(nums); for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100. -/
  theorem spec_2
      (nums : Slice I64) (queries : Slice (alloc.vec.Vec I64))
      (h_nums_len_ge : 1 ≤ nums.val.length) (h_nums_len_le : nums.val.length ≤ 100)
      (h_queries_len_ge : 1 ≤ queries.val.length) (h_queries_len_le : queries.val.length ≤ 100000)
      (h_query_len : ∀ j, j < queries.val.length → (queryAt queries.val j).length = 2)
      (h_query_t : ∀ j, j < queries.val.length →
        0 ≤ queryT queries.val j ∧ queryT queries.val j ≤ 100000)
      (h_query_x : ∀ j, j < queries.val.length →
        0 ≤ queryX queries.val j ∧ queryX queries.val j < (nums.val.length : Int))
      (h_nums_val : ∀ i : Nat, i < nums.val.length →
        0 ≤ elemsAt nums.val (i : Int) ∧ elemsAt nums.val (i : Int) ≤ 100)
      (r : alloc.vec.Vec I64)
      (h_ret : element_in_nums nums queries = ok r) :
      r.val.length = queries.val.length := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice I64) (queries : Slice (alloc.vec.Vec I64))
        (h_nums_len_ge : 1 ≤ nums.val.length) (h_nums_len_le : nums.val.length ≤ 100)
        (h_queries_len_ge : 1 ≤ queries.val.length) (h_queries_len_le : queries.val.length ≤ 100000)
        (h_query_len : ∀ j, j < queries.val.length → (queryAt queries.val j).length = 2)
        (h_query_t : ∀ j, j < queries.val.length →
          0 ≤ queryT queries.val j ∧ queryT queries.val j ≤ 100000)
        (h_query_x : ∀ j, j < queries.val.length →
          0 ≤ queryX queries.val j ∧ queryX queries.val j < (nums.val.length : Int))
        (h_nums_val : ∀ i : Nat, i < nums.val.length →
          0 ≤ elemsAt nums.val (i : Int) ∧ elemsAt nums.val (i : Int) ≤ 100)
        (r : alloc.vec.Vec I64)
        (h_ret : element_in_nums nums queries = ok r), r.val.length = queries.val.length) := by
    sorry

  /-- Under these preconditions, the function returns a result r: it does not fail, panic, overflow, or access an array out of bounds.
    Preconditions: 1 <= len(nums) <= 100; 1 <= len(queries) <= 100000; for every j with 0 <= j < len(queries), len(queries[j]) = 2, 0 <= queries[j][0] <= 100000, and 0 <= queries[j][1] < len(nums); for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100. -/
  theorem spec_3
      (nums : Slice I64) (queries : Slice (alloc.vec.Vec I64))
      (h_nums_len_ge : 1 ≤ nums.val.length) (h_nums_len_le : nums.val.length ≤ 100)
      (h_queries_len_ge : 1 ≤ queries.val.length) (h_queries_len_le : queries.val.length ≤ 100000)
      (h_query_len : ∀ j, j < queries.val.length → (queryAt queries.val j).length = 2)
      (h_query_t : ∀ j, j < queries.val.length →
        0 ≤ queryT queries.val j ∧ queryT queries.val j ≤ 100000)
      (h_query_x : ∀ j, j < queries.val.length →
        0 ≤ queryX queries.val j ∧ queryX queries.val j < (nums.val.length : Int))
      (h_nums_val : ∀ i : Nat, i < nums.val.length →
        0 ≤ elemsAt nums.val (i : Int) ∧ elemsAt nums.val (i : Int) ≤ 100) :
      ∃ r : alloc.vec.Vec I64, element_in_nums nums queries = ok r := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice I64) (queries : Slice (alloc.vec.Vec I64))
        (h_nums_len_ge : 1 ≤ nums.val.length) (h_nums_len_le : nums.val.length ≤ 100)
        (h_queries_len_ge : 1 ≤ queries.val.length) (h_queries_len_le : queries.val.length ≤ 100000)
        (h_query_len : ∀ j, j < queries.val.length → (queryAt queries.val j).length = 2)
        (h_query_t : ∀ j, j < queries.val.length →
          0 ≤ queryT queries.val j ∧ queryT queries.val j ≤ 100000)
        (h_query_x : ∀ j, j < queries.val.length →
          0 ≤ queryX queries.val j ∧ queryX queries.val j < (nums.val.length : Int))
        (h_nums_val : ∀ i : Nat, i < nums.val.length →
          0 ≤ elemsAt nums.val (i : Int) ∧ elemsAt nums.val (i : Int) ≤ 100), ∃ r : alloc.vec.Vec I64, element_in_nums nums queries = ok r) := by
    sorry

  /-- Whenever the function returns a result r, for every j with 0 <= j < len(queries), either r[j] = -1, or there exists an i with 0 <= i < len(nums) such that r[j] = nums[i].
    Preconditions: 1 <= len(nums) <= 100; 1 <= len(queries) <= 100000; for every j with 0 <= j < len(queries), len(queries[j]) = 2, 0 <= queries[j][0] <= 100000, and 0 <= queries[j][1] < len(nums); for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100. -/
  theorem spec_4
      (nums : Slice I64) (queries : Slice (alloc.vec.Vec I64))
      (h_nums_len_ge : 1 ≤ nums.val.length) (h_nums_len_le : nums.val.length ≤ 100)
      (h_queries_len_ge : 1 ≤ queries.val.length) (h_queries_len_le : queries.val.length ≤ 100000)
      (h_query_len : ∀ j, j < queries.val.length → (queryAt queries.val j).length = 2)
      (h_query_t : ∀ j, j < queries.val.length →
        0 ≤ queryT queries.val j ∧ queryT queries.val j ≤ 100000)
      (h_query_x : ∀ j, j < queries.val.length →
        0 ≤ queryX queries.val j ∧ queryX queries.val j < (nums.val.length : Int))
      (h_nums_val : ∀ i : Nat, i < nums.val.length →
        0 ≤ elemsAt nums.val (i : Int) ∧ elemsAt nums.val (i : Int) ≤ 100)
      (r : alloc.vec.Vec I64)
      (h_ret : element_in_nums nums queries = ok r) :
      ∀ j, j < queries.val.length →
        outAt r.val j = -1 ∨
          ∃ i : Nat, i < nums.val.length ∧ outAt r.val j = elemsAt nums.val (i : Int) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice I64) (queries : Slice (alloc.vec.Vec I64))
        (h_nums_len_ge : 1 ≤ nums.val.length) (h_nums_len_le : nums.val.length ≤ 100)
        (h_queries_len_ge : 1 ≤ queries.val.length) (h_queries_len_le : queries.val.length ≤ 100000)
        (h_query_len : ∀ j, j < queries.val.length → (queryAt queries.val j).length = 2)
        (h_query_t : ∀ j, j < queries.val.length →
          0 ≤ queryT queries.val j ∧ queryT queries.val j ≤ 100000)
        (h_query_x : ∀ j, j < queries.val.length →
          0 ≤ queryX queries.val j ∧ queryX queries.val j < (nums.val.length : Int))
        (h_nums_val : ∀ i : Nat, i < nums.val.length →
          0 ≤ elemsAt nums.val (i : Int) ∧ elemsAt nums.val (i : Int) ≤ 100)
        (r : alloc.vec.Vec I64)
        (h_ret : element_in_nums nums queries = ok r), ∀ j, j < queries.val.length →
          outAt r.val j = -1 ∨
            ∃ i : Nat, i < nums.val.length ∧ outAt r.val j = elemsAt nums.val (i : Int)) := by
    sorry

  /-- Whenever the function returns a result r, for every j with 0 <= j < len(queries), either r[j] = -1 or 0 <= r[j] <= 100.
    Preconditions: 1 <= len(nums) <= 100; 1 <= len(queries) <= 100000; for every j with 0 <= j < len(queries), len(queries[j]) = 2, 0 <= queries[j][0] <= 100000, and 0 <= queries[j][1] < len(nums); for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100. -/
  theorem spec_5
      (nums : Slice I64) (queries : Slice (alloc.vec.Vec I64))
      (h_nums_len_ge : 1 ≤ nums.val.length) (h_nums_len_le : nums.val.length ≤ 100)
      (h_queries_len_ge : 1 ≤ queries.val.length) (h_queries_len_le : queries.val.length ≤ 100000)
      (h_query_len : ∀ j, j < queries.val.length → (queryAt queries.val j).length = 2)
      (h_query_t : ∀ j, j < queries.val.length →
        0 ≤ queryT queries.val j ∧ queryT queries.val j ≤ 100000)
      (h_query_x : ∀ j, j < queries.val.length →
        0 ≤ queryX queries.val j ∧ queryX queries.val j < (nums.val.length : Int))
      (h_nums_val : ∀ i : Nat, i < nums.val.length →
        0 ≤ elemsAt nums.val (i : Int) ∧ elemsAt nums.val (i : Int) ≤ 100)
      (r : alloc.vec.Vec I64)
      (h_ret : element_in_nums nums queries = ok r) :
      ∀ j, j < queries.val.length →
        outAt r.val j = -1 ∨ (0 ≤ outAt r.val j ∧ outAt r.val j ≤ 100) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice I64) (queries : Slice (alloc.vec.Vec I64))
        (h_nums_len_ge : 1 ≤ nums.val.length) (h_nums_len_le : nums.val.length ≤ 100)
        (h_queries_len_ge : 1 ≤ queries.val.length) (h_queries_len_le : queries.val.length ≤ 100000)
        (h_query_len : ∀ j, j < queries.val.length → (queryAt queries.val j).length = 2)
        (h_query_t : ∀ j, j < queries.val.length →
          0 ≤ queryT queries.val j ∧ queryT queries.val j ≤ 100000)
        (h_query_x : ∀ j, j < queries.val.length →
          0 ≤ queryX queries.val j ∧ queryX queries.val j < (nums.val.length : Int))
        (h_nums_val : ∀ i : Nat, i < nums.val.length →
          0 ≤ elemsAt nums.val (i : Int) ∧ elemsAt nums.val (i : Int) ≤ 100)
        (r : alloc.vec.Vec I64)
        (h_ret : element_in_nums nums queries = ok r), ∀ j, j < queries.val.length →
          outAt r.val j = -1 ∨ (0 ≤ outAt r.val j ∧ outAt r.val j ≤ 100)) := by
    sorry

  /-- Whenever the function returns a result r, for every j with 0 <= j < len(queries), if queries[j][0] mod (2*len(nums)) = len(nums), then r[j] = -1.
    Preconditions: 1 <= len(nums) <= 100; 1 <= len(queries) <= 100000; for every j with 0 <= j < len(queries), len(queries[j]) = 2, 0 <= queries[j][0] <= 100000, and 0 <= queries[j][1] < len(nums); for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100. -/
  theorem spec_6
      (nums : Slice I64) (queries : Slice (alloc.vec.Vec I64))
      (h_nums_len_ge : 1 ≤ nums.val.length) (h_nums_len_le : nums.val.length ≤ 100)
      (h_queries_len_ge : 1 ≤ queries.val.length) (h_queries_len_le : queries.val.length ≤ 100000)
      (h_query_len : ∀ j, j < queries.val.length → (queryAt queries.val j).length = 2)
      (h_query_t : ∀ j, j < queries.val.length →
        0 ≤ queryT queries.val j ∧ queryT queries.val j ≤ 100000)
      (h_query_x : ∀ j, j < queries.val.length →
        0 ≤ queryX queries.val j ∧ queryX queries.val j < (nums.val.length : Int))
      (h_nums_val : ∀ i : Nat, i < nums.val.length →
        0 ≤ elemsAt nums.val (i : Int) ∧ elemsAt nums.val (i : Int) ≤ 100)
      (r : alloc.vec.Vec I64)
      (h_ret : element_in_nums nums queries = ok r) :
      ∀ j, j < queries.val.length →
        (let m : Int := (nums.val.length : Int)
         let t : Int := queryT queries.val j
         periodMod m t = m → outAt r.val j = -1) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice I64) (queries : Slice (alloc.vec.Vec I64))
        (h_nums_len_ge : 1 ≤ nums.val.length) (h_nums_len_le : nums.val.length ≤ 100)
        (h_queries_len_ge : 1 ≤ queries.val.length) (h_queries_len_le : queries.val.length ≤ 100000)
        (h_query_len : ∀ j, j < queries.val.length → (queryAt queries.val j).length = 2)
        (h_query_t : ∀ j, j < queries.val.length →
          0 ≤ queryT queries.val j ∧ queryT queries.val j ≤ 100000)
        (h_query_x : ∀ j, j < queries.val.length →
          0 ≤ queryX queries.val j ∧ queryX queries.val j < (nums.val.length : Int))
        (h_nums_val : ∀ i : Nat, i < nums.val.length →
          0 ≤ elemsAt nums.val (i : Int) ∧ elemsAt nums.val (i : Int) ≤ 100)
        (r : alloc.vec.Vec I64)
        (h_ret : element_in_nums nums queries = ok r), ∀ j, j < queries.val.length →
          (let m : Int := (nums.val.length : Int)
           let t : Int := queryT queries.val j
           periodMod m t = m → outAt r.val j = -1)) := by
    sorry

  /-- Whenever the function returns a result r, for every j with 0 <= j < len(queries), writing m = len(nums), p = queries[j][0] mod (2*m), and x = queries[j][1], if p < m and x < m - p, then r[j] = nums[p + x].
    Preconditions: 1 <= len(nums) <= 100; 1 <= len(queries) <= 100000; for every j with 0 <= j < len(queries), len(queries[j]) = 2, 0 <= queries[j][0] <= 100000, and 0 <= queries[j][1] < len(nums); for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100. -/
  theorem spec_7
      (nums : Slice I64) (queries : Slice (alloc.vec.Vec I64))
      (h_nums_len_ge : 1 ≤ nums.val.length) (h_nums_len_le : nums.val.length ≤ 100)
      (h_queries_len_ge : 1 ≤ queries.val.length) (h_queries_len_le : queries.val.length ≤ 100000)
      (h_query_len : ∀ j, j < queries.val.length → (queryAt queries.val j).length = 2)
      (h_query_t : ∀ j, j < queries.val.length →
        0 ≤ queryT queries.val j ∧ queryT queries.val j ≤ 100000)
      (h_query_x : ∀ j, j < queries.val.length →
        0 ≤ queryX queries.val j ∧ queryX queries.val j < (nums.val.length : Int))
      (h_nums_val : ∀ i : Nat, i < nums.val.length →
        0 ≤ elemsAt nums.val (i : Int) ∧ elemsAt nums.val (i : Int) ≤ 100)
      (r : alloc.vec.Vec I64)
      (h_ret : element_in_nums nums queries = ok r) :
      ∀ j, j < queries.val.length →
        (let m : Int := (nums.val.length : Int)
         let p : Int := periodMod m (queryT queries.val j)
         let x : Int := queryX queries.val j
         p < m → x < m - p → outAt r.val j = elemsAt nums.val (p + x)) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice I64) (queries : Slice (alloc.vec.Vec I64))
        (h_nums_len_ge : 1 ≤ nums.val.length) (h_nums_len_le : nums.val.length ≤ 100)
        (h_queries_len_ge : 1 ≤ queries.val.length) (h_queries_len_le : queries.val.length ≤ 100000)
        (h_query_len : ∀ j, j < queries.val.length → (queryAt queries.val j).length = 2)
        (h_query_t : ∀ j, j < queries.val.length →
          0 ≤ queryT queries.val j ∧ queryT queries.val j ≤ 100000)
        (h_query_x : ∀ j, j < queries.val.length →
          0 ≤ queryX queries.val j ∧ queryX queries.val j < (nums.val.length : Int))
        (h_nums_val : ∀ i : Nat, i < nums.val.length →
          0 ≤ elemsAt nums.val (i : Int) ∧ elemsAt nums.val (i : Int) ≤ 100)
        (r : alloc.vec.Vec I64)
        (h_ret : element_in_nums nums queries = ok r), ∀ j, j < queries.val.length →
          (let m : Int := (nums.val.length : Int)
           let p : Int := periodMod m (queryT queries.val j)
           let x : Int := queryX queries.val j
           p < m → x < m - p → outAt r.val j = elemsAt nums.val (p + x))) := by
    sorry

  /-- Whenever the function returns a result r, for every j with 0 <= j < len(queries), writing m = len(nums), p = queries[j][0] mod (2*m), and x = queries[j][1], if p < m and x >= m - p, then r[j] = -1.
    Preconditions: 1 <= len(nums) <= 100; 1 <= len(queries) <= 100000; for every j with 0 <= j < len(queries), len(queries[j]) = 2, 0 <= queries[j][0] <= 100000, and 0 <= queries[j][1] < len(nums); for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100. -/
  theorem spec_8
      (nums : Slice I64) (queries : Slice (alloc.vec.Vec I64))
      (h_nums_len_ge : 1 ≤ nums.val.length) (h_nums_len_le : nums.val.length ≤ 100)
      (h_queries_len_ge : 1 ≤ queries.val.length) (h_queries_len_le : queries.val.length ≤ 100000)
      (h_query_len : ∀ j, j < queries.val.length → (queryAt queries.val j).length = 2)
      (h_query_t : ∀ j, j < queries.val.length →
        0 ≤ queryT queries.val j ∧ queryT queries.val j ≤ 100000)
      (h_query_x : ∀ j, j < queries.val.length →
        0 ≤ queryX queries.val j ∧ queryX queries.val j < (nums.val.length : Int))
      (h_nums_val : ∀ i : Nat, i < nums.val.length →
        0 ≤ elemsAt nums.val (i : Int) ∧ elemsAt nums.val (i : Int) ≤ 100)
      (r : alloc.vec.Vec I64)
      (h_ret : element_in_nums nums queries = ok r) :
      ∀ j, j < queries.val.length →
        (let m : Int := (nums.val.length : Int)
         let p : Int := periodMod m (queryT queries.val j)
         let x : Int := queryX queries.val j
         p < m → m - p ≤ x → outAt r.val j = -1) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice I64) (queries : Slice (alloc.vec.Vec I64))
        (h_nums_len_ge : 1 ≤ nums.val.length) (h_nums_len_le : nums.val.length ≤ 100)
        (h_queries_len_ge : 1 ≤ queries.val.length) (h_queries_len_le : queries.val.length ≤ 100000)
        (h_query_len : ∀ j, j < queries.val.length → (queryAt queries.val j).length = 2)
        (h_query_t : ∀ j, j < queries.val.length →
          0 ≤ queryT queries.val j ∧ queryT queries.val j ≤ 100000)
        (h_query_x : ∀ j, j < queries.val.length →
          0 ≤ queryX queries.val j ∧ queryX queries.val j < (nums.val.length : Int))
        (h_nums_val : ∀ i : Nat, i < nums.val.length →
          0 ≤ elemsAt nums.val (i : Int) ∧ elemsAt nums.val (i : Int) ≤ 100)
        (r : alloc.vec.Vec I64)
        (h_ret : element_in_nums nums queries = ok r), ∀ j, j < queries.val.length →
          (let m : Int := (nums.val.length : Int)
           let p : Int := periodMod m (queryT queries.val j)
           let x : Int := queryX queries.val j
           p < m → m - p ≤ x → outAt r.val j = -1)) := by
    sorry

  /-- Whenever the function returns a result r, for every j with 0 <= j < len(queries), writing m = len(nums), p = queries[j][0] mod (2*m), and x = queries[j][1], if m < p < 2*m and x < p - m, then r[j] = nums[x].
    Preconditions: 1 <= len(nums) <= 100; 1 <= len(queries) <= 100000; for every j with 0 <= j < len(queries), len(queries[j]) = 2, 0 <= queries[j][0] <= 100000, and 0 <= queries[j][1] < len(nums); for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100. -/
  theorem spec_9
      (nums : Slice I64) (queries : Slice (alloc.vec.Vec I64))
      (h_nums_len_ge : 1 ≤ nums.val.length) (h_nums_len_le : nums.val.length ≤ 100)
      (h_queries_len_ge : 1 ≤ queries.val.length) (h_queries_len_le : queries.val.length ≤ 100000)
      (h_query_len : ∀ j, j < queries.val.length → (queryAt queries.val j).length = 2)
      (h_query_t : ∀ j, j < queries.val.length →
        0 ≤ queryT queries.val j ∧ queryT queries.val j ≤ 100000)
      (h_query_x : ∀ j, j < queries.val.length →
        0 ≤ queryX queries.val j ∧ queryX queries.val j < (nums.val.length : Int))
      (h_nums_val : ∀ i : Nat, i < nums.val.length →
        0 ≤ elemsAt nums.val (i : Int) ∧ elemsAt nums.val (i : Int) ≤ 100)
      (r : alloc.vec.Vec I64)
      (h_ret : element_in_nums nums queries = ok r) :
      ∀ j, j < queries.val.length →
        (let m : Int := (nums.val.length : Int)
         let p : Int := periodMod m (queryT queries.val j)
         let x : Int := queryX queries.val j
         m < p → p < 2 * m → x < p - m → outAt r.val j = elemsAt nums.val x) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice I64) (queries : Slice (alloc.vec.Vec I64))
        (h_nums_len_ge : 1 ≤ nums.val.length) (h_nums_len_le : nums.val.length ≤ 100)
        (h_queries_len_ge : 1 ≤ queries.val.length) (h_queries_len_le : queries.val.length ≤ 100000)
        (h_query_len : ∀ j, j < queries.val.length → (queryAt queries.val j).length = 2)
        (h_query_t : ∀ j, j < queries.val.length →
          0 ≤ queryT queries.val j ∧ queryT queries.val j ≤ 100000)
        (h_query_x : ∀ j, j < queries.val.length →
          0 ≤ queryX queries.val j ∧ queryX queries.val j < (nums.val.length : Int))
        (h_nums_val : ∀ i : Nat, i < nums.val.length →
          0 ≤ elemsAt nums.val (i : Int) ∧ elemsAt nums.val (i : Int) ≤ 100)
        (r : alloc.vec.Vec I64)
        (h_ret : element_in_nums nums queries = ok r), ∀ j, j < queries.val.length →
          (let m : Int := (nums.val.length : Int)
           let p : Int := periodMod m (queryT queries.val j)
           let x : Int := queryX queries.val j
           m < p → p < 2 * m → x < p - m → outAt r.val j = elemsAt nums.val x)) := by
    sorry

  /-- Whenever the function returns a result r, for every j with 0 <= j < len(queries), writing m = len(nums), p = queries[j][0] mod (2*m), and x = queries[j][1], if m < p < 2*m and x >= p - m, then r[j] = -1.
    Preconditions: 1 <= len(nums) <= 100; 1 <= len(queries) <= 100000; for every j with 0 <= j < len(queries), len(queries[j]) = 2, 0 <= queries[j][0] <= 100000, and 0 <= queries[j][1] < len(nums); for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100. -/
  theorem spec_10
      (nums : Slice I64) (queries : Slice (alloc.vec.Vec I64))
      (h_nums_len_ge : 1 ≤ nums.val.length) (h_nums_len_le : nums.val.length ≤ 100)
      (h_queries_len_ge : 1 ≤ queries.val.length) (h_queries_len_le : queries.val.length ≤ 100000)
      (h_query_len : ∀ j, j < queries.val.length → (queryAt queries.val j).length = 2)
      (h_query_t : ∀ j, j < queries.val.length →
        0 ≤ queryT queries.val j ∧ queryT queries.val j ≤ 100000)
      (h_query_x : ∀ j, j < queries.val.length →
        0 ≤ queryX queries.val j ∧ queryX queries.val j < (nums.val.length : Int))
      (h_nums_val : ∀ i : Nat, i < nums.val.length →
        0 ≤ elemsAt nums.val (i : Int) ∧ elemsAt nums.val (i : Int) ≤ 100)
      (r : alloc.vec.Vec I64)
      (h_ret : element_in_nums nums queries = ok r) :
      ∀ j, j < queries.val.length →
        (let m : Int := (nums.val.length : Int)
         let p : Int := periodMod m (queryT queries.val j)
         let x : Int := queryX queries.val j
         m < p → p < 2 * m → p - m ≤ x → outAt r.val j = -1) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice I64) (queries : Slice (alloc.vec.Vec I64))
        (h_nums_len_ge : 1 ≤ nums.val.length) (h_nums_len_le : nums.val.length ≤ 100)
        (h_queries_len_ge : 1 ≤ queries.val.length) (h_queries_len_le : queries.val.length ≤ 100000)
        (h_query_len : ∀ j, j < queries.val.length → (queryAt queries.val j).length = 2)
        (h_query_t : ∀ j, j < queries.val.length →
          0 ≤ queryT queries.val j ∧ queryT queries.val j ≤ 100000)
        (h_query_x : ∀ j, j < queries.val.length →
          0 ≤ queryX queries.val j ∧ queryX queries.val j < (nums.val.length : Int))
        (h_nums_val : ∀ i : Nat, i < nums.val.length →
          0 ≤ elemsAt nums.val (i : Int) ∧ elemsAt nums.val (i : Int) ≤ 100)
        (r : alloc.vec.Vec I64)
        (h_ret : element_in_nums nums queries = ok r), ∀ j, j < queries.val.length →
          (let m : Int := (nums.val.length : Int)
           let p : Int := periodMod m (queryT queries.val j)
           let x : Int := queryX queries.val j
           m < p → p < 2 * m → p - m ≤ x → outAt r.val j = -1)) := by
    sorry

  /-- Whenever the function returns a result r, for every j with 0 <= j < len(queries), writing m = len(nums), p = queries[j][0] mod (2*m), x = queries[j][1], and L = (if p <= m then m - p else p - m), we have r[j] = -1 if and only if x >= L.
    Preconditions: 1 <= len(nums) <= 100; 1 <= len(queries) <= 100000; for every j with 0 <= j < len(queries), len(queries[j]) = 2, 0 <= queries[j][0] <= 100000, and 0 <= queries[j][1] < len(nums); for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100. -/
  theorem spec_11
      (nums : Slice I64) (queries : Slice (alloc.vec.Vec I64))
      (h_nums_len_ge : 1 ≤ nums.val.length) (h_nums_len_le : nums.val.length ≤ 100)
      (h_queries_len_ge : 1 ≤ queries.val.length) (h_queries_len_le : queries.val.length ≤ 100000)
      (h_query_len : ∀ j, j < queries.val.length → (queryAt queries.val j).length = 2)
      (h_query_t : ∀ j, j < queries.val.length →
        0 ≤ queryT queries.val j ∧ queryT queries.val j ≤ 100000)
      (h_query_x : ∀ j, j < queries.val.length →
        0 ≤ queryX queries.val j ∧ queryX queries.val j < (nums.val.length : Int))
      (h_nums_val : ∀ i : Nat, i < nums.val.length →
        0 ≤ elemsAt nums.val (i : Int) ∧ elemsAt nums.val (i : Int) ≤ 100)
      (r : alloc.vec.Vec I64)
      (h_ret : element_in_nums nums queries = ok r) :
      ∀ j, j < queries.val.length →
        (let m : Int := (nums.val.length : Int)
         let p : Int := periodMod m (queryT queries.val j)
         let x : Int := queryX queries.val j
         let L : Int := if p ≤ m then m - p else p - m
         outAt r.val j = -1 ↔ L ≤ x) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice I64) (queries : Slice (alloc.vec.Vec I64))
        (h_nums_len_ge : 1 ≤ nums.val.length) (h_nums_len_le : nums.val.length ≤ 100)
        (h_queries_len_ge : 1 ≤ queries.val.length) (h_queries_len_le : queries.val.length ≤ 100000)
        (h_query_len : ∀ j, j < queries.val.length → (queryAt queries.val j).length = 2)
        (h_query_t : ∀ j, j < queries.val.length →
          0 ≤ queryT queries.val j ∧ queryT queries.val j ≤ 100000)
        (h_query_x : ∀ j, j < queries.val.length →
          0 ≤ queryX queries.val j ∧ queryX queries.val j < (nums.val.length : Int))
        (h_nums_val : ∀ i : Nat, i < nums.val.length →
          0 ≤ elemsAt nums.val (i : Int) ∧ elemsAt nums.val (i : Int) ≤ 100)
        (r : alloc.vec.Vec I64)
        (h_ret : element_in_nums nums queries = ok r), ∀ j, j < queries.val.length →
          (let m : Int := (nums.val.length : Int)
           let p : Int := periodMod m (queryT queries.val j)
           let x : Int := queryX queries.val j
           let L : Int := if p ≤ m then m - p else p - m
           outAt r.val j = -1 ↔ L ≤ x)) := by
    sorry

  /-- Whenever the function returns a result r, for all j and k with 0 <= j < len(queries) and 0 <= k < len(queries), if queries[j][1] = queries[k][1] and queries[j][0] mod (2*len(nums)) = queries[k][0] mod (2*len(nums)), then r[j] = r[k].
    Preconditions: 1 <= len(nums) <= 100; 1 <= len(queries) <= 100000; for every j with 0 <= j < len(queries), len(queries[j]) = 2, 0 <= queries[j][0] <= 100000, and 0 <= queries[j][1] < len(nums); for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100. -/
  theorem spec_12
      (nums : Slice I64) (queries : Slice (alloc.vec.Vec I64))
      (h_nums_len_ge : 1 ≤ nums.val.length) (h_nums_len_le : nums.val.length ≤ 100)
      (h_queries_len_ge : 1 ≤ queries.val.length) (h_queries_len_le : queries.val.length ≤ 100000)
      (h_query_len : ∀ j, j < queries.val.length → (queryAt queries.val j).length = 2)
      (h_query_t : ∀ j, j < queries.val.length →
        0 ≤ queryT queries.val j ∧ queryT queries.val j ≤ 100000)
      (h_query_x : ∀ j, j < queries.val.length →
        0 ≤ queryX queries.val j ∧ queryX queries.val j < (nums.val.length : Int))
      (h_nums_val : ∀ i : Nat, i < nums.val.length →
        0 ≤ elemsAt nums.val (i : Int) ∧ elemsAt nums.val (i : Int) ≤ 100)
      (r : alloc.vec.Vec I64)
      (h_ret : element_in_nums nums queries = ok r) :
      ∀ j k, j < queries.val.length → k < queries.val.length →
        queryX queries.val j = queryX queries.val k →
        queryT queries.val j % (2 * (nums.val.length : Int)) =
          queryT queries.val k % (2 * (nums.val.length : Int)) →
        outAt r.val j = outAt r.val k := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice I64) (queries : Slice (alloc.vec.Vec I64))
        (h_nums_len_ge : 1 ≤ nums.val.length) (h_nums_len_le : nums.val.length ≤ 100)
        (h_queries_len_ge : 1 ≤ queries.val.length) (h_queries_len_le : queries.val.length ≤ 100000)
        (h_query_len : ∀ j, j < queries.val.length → (queryAt queries.val j).length = 2)
        (h_query_t : ∀ j, j < queries.val.length →
          0 ≤ queryT queries.val j ∧ queryT queries.val j ≤ 100000)
        (h_query_x : ∀ j, j < queries.val.length →
          0 ≤ queryX queries.val j ∧ queryX queries.val j < (nums.val.length : Int))
        (h_nums_val : ∀ i : Nat, i < nums.val.length →
          0 ≤ elemsAt nums.val (i : Int) ∧ elemsAt nums.val (i : Int) ≤ 100)
        (r : alloc.vec.Vec I64)
        (h_ret : element_in_nums nums queries = ok r), ∀ j k, j < queries.val.length → k < queries.val.length →
          queryX queries.val j = queryX queries.val k →
          queryT queries.val j % (2 * (nums.val.length : Int)) =
            queryT queries.val k % (2 * (nums.val.length : Int)) →
          outAt r.val j = outAt r.val k) := by
    sorry

  end AegisSpec.ElementInNums
