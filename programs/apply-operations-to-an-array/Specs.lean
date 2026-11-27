import Aegis.ApplyOperations.Code.Funs

/-!
# Specifications of `Aegis.ApplyOperations.apply_operations`

LeetCode problem `apply-operations-to-an-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.ApplyOperations

  def ints (l : List Std.I64) : List ℤ := l.map (fun x => x.val)

  def passStep (l : List ℤ) (i : ℕ) : List ℤ :=
    match l[i]?, l[i+1]? with
    | some x, some y => if x = y then (l.set i (2 * x)).set (i + 1) 0 else l
    | _, _ => l

  def passSweep (l : List ℤ) : ℕ → List ℤ
    | 0 => l
    | k + 1 => passStep (passSweep l k) k

  def finalArray (nums : Slice Std.I64) : List ℤ :=
    passSweep (ints nums.val) (nums.val.length - 1)

  def zerosToEnd (l : List ℤ) : List ℤ :=
    l.filter (· ≠ 0) ++ List.replicate (l.countP (· = 0)) 0

  def nonzeroBefore (l : List ℤ) (k : ℕ) : ℕ := (l.take k).countP (· ≠ 0)

  def maxEntry (l : List ℤ) : ℤ := l.foldr max 0

  /-- Define arrays B_0,...,B_{n-1} of length n by B_0 = nums, and for each i with 0 <= i < n-1, B_{i+1} is obtained from B_i as follows: if B_i[i] = B_i[i+1], then B_{i+1}[i] = 2 * B_i[i], B_{i+1}[i+1] = 0, and B_{i+1}[j] = B_i[j] for every j not in {i,i+1}; if B_i[i] != B_i[i+1], then B_{i+1} = B_i. Let A = B_{n-1}. Let m be the number of indices j with A[j] != 0. The function returns a result r with len(r) = n, and: for every j with 0 <= j < m, r[j] is the (j+1)-th nonzero entry of A when A is read from left to right; and for every j with m <= j < n, r[j] = 0. Equivalently, r is obtained from A by deleting all zero entries, keeping the remaining entries in their original order, and appending n - m zeros.
    Preconditions: Let n = len(nums). Assume 2 <= n <= 2000 and 0 <= nums[i] <= 1000 for every i with 0 <= i < n. -/
  theorem spec_1 (nums : Slice Std.I64)
      (hn : 2 ≤ nums.val.length) (hN : nums.val.length ≤ 2000)
      (hb : ∀ (i : ℕ) (hi : i < nums.val.length),
        0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000) :
      ∃ r, Aegis.ApplyOperations.apply_operations nums = ok r ∧
        (let A := finalArray nums
         let m := A.countP (· ≠ 0)
         r.val.length = nums.val.length ∧
         (∀ (j : ℕ), j < m → (ints r.val).getD j 0 = (A.filter (· ≠ 0)).getD j 0) ∧
         (∀ (j : ℕ), m ≤ j → j < nums.val.length → (ints r.val).getD j 0 = 0)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn : 2 ≤ nums.val.length) (hN : nums.val.length ≤ 2000)
        (hb : ∀ (i : ℕ) (hi : i < nums.val.length),
          0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000), ∃ r, Aegis.ApplyOperations.apply_operations nums = ok r ∧
          (let A := finalArray nums
           let m := A.countP (· ≠ 0)
           r.val.length = nums.val.length ∧
           (∀ (j : ℕ), j < m → (ints r.val).getD j 0 = (A.filter (· ≠ 0)).getD j 0) ∧
           (∀ (j : ℕ), m ≤ j → j < nums.val.length → (ints r.val).getD j 0 = 0))) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r; it does not fail (no overflow, panic, or out-of-bounds failure).
    Preconditions: Let n = len(nums). Assume 2 <= n <= 2000 and 0 <= nums[i] <= 1000 for every i with 0 <= i < n. -/
  theorem spec_2 (nums : Slice Std.I64)
      (hn : 2 ≤ nums.val.length) (hN : nums.val.length ≤ 2000)
      (hb : ∀ (i : ℕ) (hi : i < nums.val.length),
        0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000) :
      ∃ r, Aegis.ApplyOperations.apply_operations nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn : 2 ≤ nums.val.length) (hN : nums.val.length ≤ 2000)
        (hb : ∀ (i : ℕ) (hi : i < nums.val.length),
          0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000), ∃ r, Aegis.ApplyOperations.apply_operations nums = ok r) := by
    sorry

  /-- Whenever the function returns a result r, len(r) = len(nums).
    Preconditions: Let n = len(nums). Assume 2 <= n <= 2000 and 0 <= nums[i] <= 1000 for every i with 0 <= i < n. -/
  theorem spec_3 (nums : Slice Std.I64)
      (hn : 2 ≤ nums.val.length) (hN : nums.val.length ≤ 2000)
      (hb : ∀ (i : ℕ) (hi : i < nums.val.length),
        0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000) :
      ∀ r, Aegis.ApplyOperations.apply_operations nums = ok r →
        r.val.length = nums.val.length := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn : 2 ≤ nums.val.length) (hN : nums.val.length ≤ 2000)
        (hb : ∀ (i : ℕ) (hi : i < nums.val.length),
          0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000), ∀ r, Aegis.ApplyOperations.apply_operations nums = ok r →
          r.val.length = nums.val.length) := by
    sorry

  /-- Let M be the maximum of nums[0],...,nums[n-1]. Whenever the function returns a result r, every entry r[j] satisfies 0 <= r[j] <= 2 * M.
    Preconditions: Let n = len(nums). Assume 2 <= n <= 2000 and 0 <= nums[i] <= 1000 for every i with 0 <= i < n. -/
  theorem spec_4 (nums : Slice Std.I64)
      (hn : 2 ≤ nums.val.length) (hN : nums.val.length ≤ 2000)
      (hb : ∀ (i : ℕ) (hi : i < nums.val.length),
        0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000) :
      ∀ r, Aegis.ApplyOperations.apply_operations nums = ok r →
        ∀ (j : ℕ) (hj : j < r.val.length),
          0 ≤ (r.val[j]).val ∧ (r.val[j]).val ≤ 2 * maxEntry (ints nums.val) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn : 2 ≤ nums.val.length) (hN : nums.val.length ≤ 2000)
        (hb : ∀ (i : ℕ) (hi : i < nums.val.length),
          0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000), ∀ r, Aegis.ApplyOperations.apply_operations nums = ok r →
          ∀ (j : ℕ) (hj : j < r.val.length),
            0 ≤ (r.val[j]).val ∧ (r.val[j]).val ≤ 2 * maxEntry (ints nums.val)) := by
    sorry

  /-- Whenever the function returns a result r, for all i and j with 0 <= i < j < len(r), if r[i] = 0 then r[j] = 0. Thus all zero entries of r form a suffix of r.
    Preconditions: Let n = len(nums). Assume 2 <= n <= 2000 and 0 <= nums[i] <= 1000 for every i with 0 <= i < n. -/
  theorem spec_5 (nums : Slice Std.I64)
      (hn : 2 ≤ nums.val.length) (hN : nums.val.length ≤ 2000)
      (hb : ∀ (i : ℕ) (hi : i < nums.val.length),
        0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000) :
      ∀ r, Aegis.ApplyOperations.apply_operations nums = ok r →
        ∀ (i j : ℕ) (hi : i < r.val.length) (hj : j < r.val.length), i < j →
          (r.val[i]).val = 0 → (r.val[j]).val = 0 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn : 2 ≤ nums.val.length) (hN : nums.val.length ≤ 2000)
        (hb : ∀ (i : ℕ) (hi : i < nums.val.length),
          0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000), ∀ r, Aegis.ApplyOperations.apply_operations nums = ok r →
          ∀ (i j : ℕ) (hi : i < r.val.length) (hj : j < r.val.length), i < j →
            (r.val[i]).val = 0 → (r.val[j]).val = 0) := by
    sorry

  /-- Let A be the final array obtained from nums by performing, in order for i = 0,1,...,n-2, the operation: if the current array has equal entries at positions i and i+1, replace the i-th entry by twice its value and set the (i+1)-st entry to 0; otherwise do nothing. Whenever the function returns a result r, for every integer v, the number of indices j with r[j] = v equals the number of indices j with A[j] = v.
    Preconditions: Let n = len(nums). Assume 2 <= n <= 2000 and 0 <= nums[i] <= 1000 for every i with 0 <= i < n. -/
  theorem spec_6 (nums : Slice Std.I64)
      (hn : 2 ≤ nums.val.length) (hN : nums.val.length ≤ 2000)
      (hb : ∀ (i : ℕ) (hi : i < nums.val.length),
        0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000) :
      ∀ r, Aegis.ApplyOperations.apply_operations nums = ok r →
        ∀ v : ℤ, (ints r.val).countP (· = v) = (finalArray nums).countP (· = v) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn : 2 ≤ nums.val.length) (hN : nums.val.length ≤ 2000)
        (hb : ∀ (i : ℕ) (hi : i < nums.val.length),
          0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000), ∀ r, Aegis.ApplyOperations.apply_operations nums = ok r →
          ∀ v : ℤ, (ints r.val).countP (· = v) = (finalArray nums).countP (· = v)) := by
    sorry

  /-- Let A be the final array obtained from nums by performing, in order for i = 0,1,...,n-2, the operation: if the current array has equal entries at positions i and i+1, replace the i-th entry by twice its value and set the (i+1)-st entry to 0; otherwise do nothing. Whenever the function returns a result r, for every p and q with 0 <= p < q < n and A[p] != 0 and A[q] != 0, if u is the number of indices t < p with A[t] != 0 and v is the number of indices t < q with A[t] != 0, then u < v, r[u] = A[p], and r[v] = A[q].
    Preconditions: Let n = len(nums). Assume 2 <= n <= 2000 and 0 <= nums[i] <= 1000 for every i with 0 <= i < n. -/
  theorem spec_7 (nums : Slice Std.I64)
      (hn : 2 ≤ nums.val.length) (hN : nums.val.length ≤ 2000)
      (hb : ∀ (i : ℕ) (hi : i < nums.val.length),
        0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000) :
      ∀ r, Aegis.ApplyOperations.apply_operations nums = ok r →
        (let A := finalArray nums
         ∀ (p q : ℕ), p < q → q < nums.val.length →
           A.getD p 0 ≠ 0 → A.getD q 0 ≠ 0 →
             nonzeroBefore A p < nonzeroBefore A q ∧
             (ints r.val).getD (nonzeroBefore A p) 0 = A.getD p 0 ∧
             (ints r.val).getD (nonzeroBefore A q) 0 = A.getD q 0) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn : 2 ≤ nums.val.length) (hN : nums.val.length ≤ 2000)
        (hb : ∀ (i : ℕ) (hi : i < nums.val.length),
          0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000), ∀ r, Aegis.ApplyOperations.apply_operations nums = ok r →
          (let A := finalArray nums
           ∀ (p q : ℕ), p < q → q < nums.val.length →
             A.getD p 0 ≠ 0 → A.getD q 0 ≠ 0 →
               nonzeroBefore A p < nonzeroBefore A q ∧
               (ints r.val).getD (nonzeroBefore A p) 0 = A.getD p 0 ∧
               (ints r.val).getD (nonzeroBefore A q) 0 = A.getD q 0)) := by
    sorry

  /-- Whenever the function returns a result r, for every j with 0 <= j < len(r) and r[j] != 0, there exists an input index i with 0 <= i < n such that r[j] = nums[i] or r[j] = 2 * nums[i].
    Preconditions: Let n = len(nums). Assume 2 <= n <= 2000 and 0 <= nums[i] <= 1000 for every i with 0 <= i < n. -/
  theorem spec_8 (nums : Slice Std.I64)
      (hn : 2 ≤ nums.val.length) (hN : nums.val.length ≤ 2000)
      (hb : ∀ (i : ℕ) (hi : i < nums.val.length),
        0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000) :
      ∀ r, Aegis.ApplyOperations.apply_operations nums = ok r →
        ∀ (j : ℕ) (hj : j < r.val.length), (r.val[j]).val ≠ 0 →
          ∃ (i : ℕ) (hi : i < nums.val.length),
            (r.val[j]).val = (nums.val[i]).val ∨
              (r.val[j]).val = 2 * (nums.val[i]).val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn : 2 ≤ nums.val.length) (hN : nums.val.length ≤ 2000)
        (hb : ∀ (i : ℕ) (hi : i < nums.val.length),
          0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000), ∀ r, Aegis.ApplyOperations.apply_operations nums = ok r →
          ∀ (j : ℕ) (hj : j < r.val.length), (r.val[j]).val ≠ 0 →
            ∃ (i : ℕ) (hi : i < nums.val.length),
              (r.val[j]).val = (nums.val[i]).val ∨
                (r.val[j]).val = 2 * (nums.val[i]).val) := by
    sorry

  /-- Whenever the function returns a result r, if for every i with 0 <= i < n-1, nums[i] != 0 implies nums[i] != nums[i+1], then r is obtained from nums by deleting all zero entries while keeping the order of the remaining entries, and then appending as many zero entries as were deleted.
    Preconditions: Let n = len(nums). Assume 2 <= n <= 2000 and 0 <= nums[i] <= 1000 for every i with 0 <= i < n. -/
  theorem spec_9 (nums : Slice Std.I64)
      (hn : 2 ≤ nums.val.length) (hN : nums.val.length ≤ 2000)
      (hb : ∀ (i : ℕ) (hi : i < nums.val.length),
        0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000) :
      ∀ r, Aegis.ApplyOperations.apply_operations nums = ok r →
        (let L := ints nums.val
         (∀ (i : ℕ), i + 1 < nums.val.length → L.getD i 0 ≠ 0 →
            L.getD i 0 ≠ L.getD (i + 1) 0) →
           ints r.val = zerosToEnd L) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn : 2 ≤ nums.val.length) (hN : nums.val.length ≤ 2000)
        (hb : ∀ (i : ℕ) (hi : i < nums.val.length),
          0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000), ∀ r, Aegis.ApplyOperations.apply_operations nums = ok r →
          (let L := ints nums.val
           (∀ (i : ℕ), i + 1 < nums.val.length → L.getD i 0 ≠ 0 →
              L.getD i 0 ≠ L.getD (i + 1) 0) →
             ints r.val = zerosToEnd L)) := by
    sorry

  /-- Whenever the function returns a result r, if r[j] != 0 for every j with 0 <= j < len(r), then r equals nums as a sequence (same length and same entries).
    Preconditions: Let n = len(nums). Assume 2 <= n <= 2000 and 0 <= nums[i] <= 1000 for every i with 0 <= i < n. -/
  theorem spec_10 (nums : Slice Std.I64)
      (hn : 2 ≤ nums.val.length) (hN : nums.val.length ≤ 2000)
      (hb : ∀ (i : ℕ) (hi : i < nums.val.length),
        0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000) :
      ∀ r, Aegis.ApplyOperations.apply_operations nums = ok r →
        (∀ (j : ℕ) (hj : j < r.val.length), (r.val[j]).val ≠ 0) →
          r.val.length = nums.val.length ∧ ints r.val = ints nums.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn : 2 ≤ nums.val.length) (hN : nums.val.length ≤ 2000)
        (hb : ∀ (i : ℕ) (hi : i < nums.val.length),
          0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000), ∀ r, Aegis.ApplyOperations.apply_operations nums = ok r →
          (∀ (j : ℕ) (hj : j < r.val.length), (r.val[j]).val ≠ 0) →
            r.val.length = nums.val.length ∧ ints r.val = ints nums.val) := by
    sorry

  /-- Whenever the function returns a result r, if there exists i with 0 <= i < n and nums[i] = 0, then there exists j with 0 <= j < len(r) and r[j] = 0.
    Preconditions: Let n = len(nums). Assume 2 <= n <= 2000 and 0 <= nums[i] <= 1000 for every i with 0 <= i < n. -/
  theorem spec_11 (nums : Slice Std.I64)
      (hn : 2 ≤ nums.val.length) (hN : nums.val.length ≤ 2000)
      (hb : ∀ (i : ℕ) (hi : i < nums.val.length),
        0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000) :
      ∀ r, Aegis.ApplyOperations.apply_operations nums = ok r →
        (∃ (i : ℕ) (hi : i < nums.val.length), (nums.val[i]).val = 0) →
          ∃ (j : ℕ) (hj : j < r.val.length), (r.val[j]).val = 0 := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn : 2 ≤ nums.val.length) (hN : nums.val.length ≤ 2000)
        (hb : ∀ (i : ℕ) (hi : i < nums.val.length),
          0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000), ∀ r, Aegis.ApplyOperations.apply_operations nums = ok r →
          (∃ (i : ℕ) (hi : i < nums.val.length), (nums.val[i]).val = 0) →
            ∃ (j : ℕ) (hj : j < r.val.length), (r.val[j]).val = 0) := by
    sorry

  /-- Whenever the function returns a result r, the sum of the entries of r equals the sum of the entries of nums.
    Preconditions: Let n = len(nums). Assume 2 <= n <= 2000 and 0 <= nums[i] <= 1000 for every i with 0 <= i < n. -/
  theorem spec_12 (nums : Slice Std.I64)
      (hn : 2 ≤ nums.val.length) (hN : nums.val.length ≤ 2000)
      (hb : ∀ (i : ℕ) (hi : i < nums.val.length),
        0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000) :
      ∀ r, Aegis.ApplyOperations.apply_operations nums = ok r →
        (ints r.val).sum = (ints nums.val).sum := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn : 2 ≤ nums.val.length) (hN : nums.val.length ≤ 2000)
        (hb : ∀ (i : ℕ) (hi : i < nums.val.length),
          0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000), ∀ r, Aegis.ApplyOperations.apply_operations nums = ok r →
          (ints r.val).sum = (ints nums.val).sum) := by
    sorry

  end AegisSpec.ApplyOperations
