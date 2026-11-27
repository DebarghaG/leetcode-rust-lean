import Aegis.MinOperations.Code.Funs

/-!
# Specifications of `Aegis.MinOperations.min_operations`

LeetCode problem `minimum-operations-to-make-all-array-elements-equal`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinOperations

  def vals (l : List Aeneas.Std.I64) : List Int := l.map (fun x => x.val)

  def absI (x : Int) : Int := if x < 0 then -x else x

  def totalDist (l : List Int) (q : Int) : Int :=
    (l.map (fun a => absI (a - q))).sum

  def numLE (l : List Int) (q : Int) : Nat := (l.filter (fun a => a ≤ q)).length

  def numGT (l : List Int) (q : Int) : Nat := (l.filter (fun a => q < a)).length

  def upSum (l : List Int) (q : Int) : Int :=
    ((l.filter (fun a => q < a)).map (fun a => a - q)).sum

  def downSum (l : List Int) (q : Int) : Int :=
    ((l.filter (fun a => a < q)).map (fun a => q - a)).sum

  def unitStep (a b : List Int) : Prop :=
    ∃ (i : Nat) (hi : i < a.length) (d : Int), (d = 1 ∨ d = -1) ∧ b = a.set i (a[i] + d)

  def steps (a b : List Int) : Nat → Prop
    | 0 => a = b
    | k + 1 => ∃ m, unitStep a m ∧ steps m b k

  def flattenIn (l : List Int) (t : Int) (k : Nat) : Prop :=
    ∃ b, steps l b k ∧ b.length = l.length ∧ ∀ a ∈ b, a = t

  def ValidInput (nums queries : Aeneas.Std.Slice Aeneas.Std.I64) : Prop :=
    1 ≤ nums.val.length ∧ nums.val.length ≤ 100000 ∧
    1 ≤ queries.val.length ∧ queries.val.length ≤ 100000 ∧
    (∀ (j : Nat), (hj : j < nums.val.length) →
      1 ≤ (nums.val[j]).val ∧ (nums.val[j]).val ≤ 1000000000) ∧
    (∀ (i : Nat), (hi : i < queries.val.length) →
      1 ≤ (queries.val[i]).val ∧ (queries.val[i]).val ≤ 1000000000)

  def ValidInputSingleton (nums queries : Aeneas.Std.Slice Aeneas.Std.I64) : Prop :=
    nums.val.length = 1 ∧
    (∀ (j : Nat), (hj : j < nums.val.length) →
      1 ≤ (nums.val[j]).val ∧ (nums.val[j]).val ≤ 1000000000) ∧
    1 ≤ queries.val.length ∧ queries.val.length ≤ 100000 ∧
    (∀ (i : Nat), (hi : i < queries.val.length) →
      1 ≤ (queries.val[i]).val ∧ (queries.val[i]).val ≤ 1000000000)

  /-- Whenever the function returns a result r, r is a vector with len(r) = len(queries), and for every i with 0 <= i < len(queries), r[i] = sum_{j=0}^{len(nums)-1} |nums[j] - queries[i]|, where |x| denotes the absolute value of the integer x.
    Preconditions: 1 <= len(nums) <= 100000, 1 <= len(queries) <= 100000, for every j with 0 <= j < len(nums) we have 1 <= nums[j] <= 10^9, and for every i with 0 <= i < len(queries) we have 1 <= queries[i] <= 10^9. -/
  theorem spec_1 (nums queries : Aeneas.Std.Slice Aeneas.Std.I64) (h : ValidInput nums queries) :
      ∀ r, Aegis.MinOperations.min_operations nums queries = ok r →
        r.val.length = queries.val.length ∧
          ∀ (i : Nat), (hi : i < queries.val.length) → (hr : i < r.val.length) →
            (r.val[i]).val = totalDist (vals nums.val) (queries.val[i]).val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums queries : Aeneas.Std.Slice Aeneas.Std.I64) (h : ValidInput nums queries), ∀ r, Aegis.MinOperations.min_operations nums queries = ok r →
          r.val.length = queries.val.length ∧
            ∀ (i : Nat), (hi : i < queries.val.length) → (hr : i < r.val.length) →
              (r.val[i]).val = totalDist (vals nums.val) (queries.val[i]).val) := by
    sorry

  /-- Under these preconditions, the function returns a result r (it does not fail); equivalently, the computation completes without panic, out-of-bounds access, or signed 64-bit arithmetic overflow.
    Preconditions: 1 <= len(nums) <= 100000, 1 <= len(queries) <= 100000, for every j with 0 <= j < len(nums) we have 1 <= nums[j] <= 10^9, and for every i with 0 <= i < len(queries) we have 1 <= queries[i] <= 10^9. -/
  theorem spec_2 (nums queries : Aeneas.Std.Slice Aeneas.Std.I64) (h : ValidInput nums queries) :
      ∃ r, Aegis.MinOperations.min_operations nums queries = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums queries : Aeneas.Std.Slice Aeneas.Std.I64) (h : ValidInput nums queries), ∃ r, Aegis.MinOperations.min_operations nums queries = ok r) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(queries), r[i] >= 0.
    Preconditions: 1 <= len(nums) <= 100000, 1 <= len(queries) <= 100000, for every j with 0 <= j < len(nums) we have 1 <= nums[j] <= 10^9, and for every i with 0 <= i < len(queries) we have 1 <= queries[i] <= 10^9. -/
  theorem spec_3 (nums queries : Aeneas.Std.Slice Aeneas.Std.I64) (h : ValidInput nums queries) :
      ∀ r, Aegis.MinOperations.min_operations nums queries = ok r →
        r.val.length = queries.val.length ∧
          ∀ (i : Nat), (hi : i < queries.val.length) → (hr : i < r.val.length) →
            0 ≤ (r.val[i]).val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums queries : Aeneas.Std.Slice Aeneas.Std.I64) (h : ValidInput nums queries), ∀ r, Aegis.MinOperations.min_operations nums queries = ok r →
          r.val.length = queries.val.length ∧
            ∀ (i : Nat), (hi : i < queries.val.length) → (hr : i < r.val.length) →
              0 ≤ (r.val[i]).val) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(queries), r[i] <= len(nums) * (10^9 - 1). In particular r[i] < 2^63.
    Preconditions: 1 <= len(nums) <= 100000, 1 <= len(queries) <= 100000, for every j with 0 <= j < len(nums) we have 1 <= nums[j] <= 10^9, and for every i with 0 <= i < len(queries) we have 1 <= queries[i] <= 10^9. -/
  theorem spec_4 (nums queries : Aeneas.Std.Slice Aeneas.Std.I64) (h : ValidInput nums queries) :
      ∀ r, Aegis.MinOperations.min_operations nums queries = ok r →
        r.val.length = queries.val.length ∧
          ∀ (i : Nat), (hi : i < queries.val.length) → (hr : i < r.val.length) →
            (r.val[i]).val ≤ ((vals nums.val).length : Int) * (1000000000 - 1) ∧
              (r.val[i]).val < 2 ^ 63 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums queries : Aeneas.Std.Slice Aeneas.Std.I64) (h : ValidInput nums queries), ∀ r, Aegis.MinOperations.min_operations nums queries = ok r →
          r.val.length = queries.val.length ∧
            ∀ (i : Nat), (hi : i < queries.val.length) → (hr : i < r.val.length) →
              (r.val[i]).val ≤ ((vals nums.val).length : Int) * (1000000000 - 1) ∧
                (r.val[i]).val < 2 ^ 63) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(queries), r[i] = 0 if and only if nums[j] = queries[i] for every j with 0 <= j < len(nums).
    Preconditions: 1 <= len(nums) <= 100000, 1 <= len(queries) <= 100000, for every j with 0 <= j < len(nums) we have 1 <= nums[j] <= 10^9, and for every i with 0 <= i < len(queries) we have 1 <= queries[i] <= 10^9. -/
  theorem spec_5 (nums queries : Aeneas.Std.Slice Aeneas.Std.I64) (h : ValidInput nums queries) :
      ∀ r, Aegis.MinOperations.min_operations nums queries = ok r →
        r.val.length = queries.val.length ∧
          ∀ (i : Nat), (hi : i < queries.val.length) → (hr : i < r.val.length) →
            ((r.val[i]).val = 0 ↔
              ∀ (j : Nat), (hj : j < nums.val.length) →
                (nums.val[j]).val = (queries.val[i]).val) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums queries : Aeneas.Std.Slice Aeneas.Std.I64) (h : ValidInput nums queries), ∀ r, Aegis.MinOperations.min_operations nums queries = ok r →
          r.val.length = queries.val.length ∧
            ∀ (i : Nat), (hi : i < queries.val.length) → (hr : i < r.val.length) →
              ((r.val[i]).val = 0 ↔
                ∀ (j : Nat), (hj : j < nums.val.length) →
                  (nums.val[j]).val = (queries.val[i]).val)) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(queries), r[i] = |nums[0] - queries[i]|.
    Preconditions: The base constraints hold: 1 <= len(queries) <= 100000, for every i with 0 <= i < len(queries) we have 1 <= queries[i] <= 10^9, and len(nums) = 1 with 1 <= nums[0] <= 10^9. -/
  theorem spec_6 (nums queries : Aeneas.Std.Slice Aeneas.Std.I64)
      (h : ValidInputSingleton nums queries) :
      ∀ r, Aegis.MinOperations.min_operations nums queries = ok r →
        r.val.length = queries.val.length ∧
          ∀ (i : Nat), (hi : i < queries.val.length) → (hr : i < r.val.length) →
            (r.val[i]).val =
              absI ((nums.val[0]'(by have h1 := h.1; omega)).val -
                (queries.val[i]).val) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums queries : Aeneas.Std.Slice Aeneas.Std.I64)
        (h : ValidInputSingleton nums queries), ∀ r, Aegis.MinOperations.min_operations nums queries = ok r →
          r.val.length = queries.val.length ∧
            ∀ (i : Nat), (hi : i < queries.val.length) → (hr : i < r.val.length) →
              (r.val[i]).val =
                absI ((nums.val[0]'(by have h1 := h.1; omega)).val -
                  (queries.val[i]).val)) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(queries), if queries[i] <= nums[j] for every j with 0 <= j < len(nums), then r[i] = (sum_{j=0}^{len(nums)-1} nums[j]) - len(nums) * queries[i].
    Preconditions: 1 <= len(nums) <= 100000, 1 <= len(queries) <= 100000, for every j with 0 <= j < len(nums) we have 1 <= nums[j] <= 10^9, and for every i with 0 <= i < len(queries) we have 1 <= queries[i] <= 10^9. -/
  theorem spec_7 (nums queries : Aeneas.Std.Slice Aeneas.Std.I64) (h : ValidInput nums queries) :
      ∀ r, Aegis.MinOperations.min_operations nums queries = ok r →
        r.val.length = queries.val.length ∧
          ∀ (i : Nat), (hi : i < queries.val.length) → (hr : i < r.val.length) →
            (∀ (j : Nat), (hj : j < nums.val.length) →
                (queries.val[i]).val ≤ (nums.val[j]).val) →
              (r.val[i]).val =
                (vals nums.val).sum -
                  ((vals nums.val).length : Int) * (queries.val[i]).val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums queries : Aeneas.Std.Slice Aeneas.Std.I64) (h : ValidInput nums queries), ∀ r, Aegis.MinOperations.min_operations nums queries = ok r →
          r.val.length = queries.val.length ∧
            ∀ (i : Nat), (hi : i < queries.val.length) → (hr : i < r.val.length) →
              (∀ (j : Nat), (hj : j < nums.val.length) →
                  (queries.val[i]).val ≤ (nums.val[j]).val) →
                (r.val[i]).val =
                  (vals nums.val).sum -
                    ((vals nums.val).length : Int) * (queries.val[i]).val) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(queries), if queries[i] >= nums[j] for every j with 0 <= j < len(nums), then r[i] = len(nums) * queries[i] - (sum_{j=0}^{len(nums)-1} nums[j]).
    Preconditions: 1 <= len(nums) <= 100000, 1 <= len(queries) <= 100000, for every j with 0 <= j < len(nums) we have 1 <= nums[j] <= 10^9, and for every i with 0 <= i < len(queries) we have 1 <= queries[i] <= 10^9. -/
  theorem spec_8 (nums queries : Aeneas.Std.Slice Aeneas.Std.I64) (h : ValidInput nums queries) :
      ∀ r, Aegis.MinOperations.min_operations nums queries = ok r →
        r.val.length = queries.val.length ∧
          ∀ (i : Nat), (hi : i < queries.val.length) → (hr : i < r.val.length) →
            (∀ (j : Nat), (hj : j < nums.val.length) →
                (nums.val[j]).val ≤ (queries.val[i]).val) →
              (r.val[i]).val =
                ((vals nums.val).length : Int) * (queries.val[i]).val -
                  (vals nums.val).sum := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums queries : Aeneas.Std.Slice Aeneas.Std.I64) (h : ValidInput nums queries), ∀ r, Aegis.MinOperations.min_operations nums queries = ok r →
          r.val.length = queries.val.length ∧
            ∀ (i : Nat), (hi : i < queries.val.length) → (hr : i < r.val.length) →
              (∀ (j : Nat), (hj : j < nums.val.length) →
                  (nums.val[j]).val ≤ (queries.val[i]).val) →
                (r.val[i]).val =
                  ((vals nums.val).length : Int) * (queries.val[i]).val -
                    (vals nums.val).sum) := by
    sorry

  /-- Whenever the function returns a result r, for every i and k with 0 <= i < len(queries) and 0 <= k < len(queries), |r[i] - r[k]| <= len(nums) * |queries[i] - queries[k]|.
    Preconditions: 1 <= len(nums) <= 100000, 1 <= len(queries) <= 100000, for every j with 0 <= j < len(nums) we have 1 <= nums[j] <= 10^9, and for every i with 0 <= i < len(queries) we have 1 <= queries[i] <= 10^9. -/
  theorem spec_9 (nums queries : Aeneas.Std.Slice Aeneas.Std.I64)
      (h : ValidInput nums queries) :
      ∀ r, Aegis.MinOperations.min_operations nums queries = ok r →
        r.val.length = queries.val.length ∧
          ∀ (i k : Nat), (hi : i < queries.val.length) → (hk : k < queries.val.length) →
            (hri : i < r.val.length) → (hrk : k < r.val.length) →
              absI ((r.val[i]).val - (r.val[k]).val) ≤
                ((vals nums.val).length : Int) *
                  absI ((queries.val[i]).val - (queries.val[k]).val) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums queries : Aeneas.Std.Slice Aeneas.Std.I64)
        (h : ValidInput nums queries), ∀ r, Aegis.MinOperations.min_operations nums queries = ok r →
          r.val.length = queries.val.length ∧
            ∀ (i k : Nat), (hi : i < queries.val.length) → (hk : k < queries.val.length) →
              (hri : i < r.val.length) → (hrk : k < r.val.length) →
                absI ((r.val[i]).val - (r.val[k]).val) ≤
                  ((vals nums.val).length : Int) *
                    absI ((queries.val[i]).val - (queries.val[k]).val)) := by
    sorry

  /-- Whenever the function returns a result r, for every i and k with 0 <= i < len(queries) and 0 <= k < len(queries), if queries[i] = queries[k] then r[i] = r[k].
    Preconditions: 1 <= len(nums) <= 100000, 1 <= len(queries) <= 100000, for every j with 0 <= j < len(nums) we have 1 <= nums[j] <= 10^9, and for every i with 0 <= i < len(queries) we have 1 <= queries[i] <= 10^9. -/
  theorem spec_10 (nums queries : Aeneas.Std.Slice Aeneas.Std.I64)
      (h : ValidInput nums queries) :
      ∀ r, Aegis.MinOperations.min_operations nums queries = ok r →
        r.val.length = queries.val.length ∧
          ∀ (i k : Nat), (hi : i < queries.val.length) → (hk : k < queries.val.length) →
            (hri : i < r.val.length) → (hrk : k < r.val.length) →
              (queries.val[i]).val = (queries.val[k]).val →
                (r.val[i]).val = (r.val[k]).val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums queries : Aeneas.Std.Slice Aeneas.Std.I64)
        (h : ValidInput nums queries), ∀ r, Aegis.MinOperations.min_operations nums queries = ok r →
          r.val.length = queries.val.length ∧
            ∀ (i k : Nat), (hi : i < queries.val.length) → (hk : k < queries.val.length) →
              (hri : i < r.val.length) → (hrk : k < r.val.length) →
                (queries.val[i]).val = (queries.val[k]).val →
                  (r.val[i]).val = (r.val[k]).val) := by
    sorry

  /-- Whenever the function returns a result r, for every i and k with 0 <= i < len(queries), 0 <= k < len(queries), and queries[k] = queries[i] + 1, r[k] - r[i] = C_le - C_gt, where C_le is the number of indices j with 0 <= j < len(nums) and nums[j] <= queries[i], and C_gt is the number of indices j with 0 <= j < len(nums) and nums[j] > queries[i].
    Preconditions: 1 <= len(nums) <= 100000, 1 <= len(queries) <= 100000, for every j with 0 <= j < len(nums) we have 1 <= nums[j] <= 10^9, and for every i with 0 <= i < len(queries) we have 1 <= queries[i] <= 10^9. -/
  theorem spec_11 (nums queries : Aeneas.Std.Slice Aeneas.Std.I64)
      (h : ValidInput nums queries) :
      ∀ r, Aegis.MinOperations.min_operations nums queries = ok r →
        r.val.length = queries.val.length ∧
          ∀ (i k : Nat), (hi : i < queries.val.length) → (hk : k < queries.val.length) →
            (hri : i < r.val.length) → (hrk : k < r.val.length) →
              (queries.val[k]).val = (queries.val[i]).val + 1 →
                (r.val[k]).val - (r.val[i]).val =
                  (numLE (vals nums.val) (queries.val[i]).val : Int) -
                    (numGT (vals nums.val) (queries.val[i]).val : Int) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums queries : Aeneas.Std.Slice Aeneas.Std.I64)
        (h : ValidInput nums queries), ∀ r, Aegis.MinOperations.min_operations nums queries = ok r →
          r.val.length = queries.val.length ∧
            ∀ (i k : Nat), (hi : i < queries.val.length) → (hk : k < queries.val.length) →
              (hri : i < r.val.length) → (hrk : k < r.val.length) →
                (queries.val[k]).val = (queries.val[i]).val + 1 →
                  (r.val[k]).val - (r.val[i]).val =
                    (numLE (vals nums.val) (queries.val[i]).val : Int) -
                      (numGT (vals nums.val) (queries.val[i]).val : Int)) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(queries), let Up_i = sum over j with 0 <= j < len(nums) and nums[j] > queries[i] of (nums[j] - queries[i]), and let Down_i = sum over j with 0 <= j < len(nums) and nums[j] < queries[i] of (queries[i] - nums[j]); then r[i] = Up_i + Down_i. Empty sums are 0.
    Preconditions: 1 <= len(nums) <= 100000, 1 <= len(queries) <= 100000, for every j with 0 <= j < len(nums) we have 1 <= nums[j] <= 10^9, and for every i with 0 <= i < len(queries) we have 1 <= queries[i] <= 10^9. -/
  theorem spec_12 (nums queries : Aeneas.Std.Slice Aeneas.Std.I64)
      (h : ValidInput nums queries) :
      ∀ r, Aegis.MinOperations.min_operations nums queries = ok r →
        r.val.length = queries.val.length ∧
          ∀ (i : Nat), (hi : i < queries.val.length) → (hr : i < r.val.length) →
            (r.val[i]).val = upSum (vals nums.val) (queries.val[i]).val +
              downSum (vals nums.val) (queries.val[i]).val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums queries : Aeneas.Std.Slice Aeneas.Std.I64)
        (h : ValidInput nums queries), ∀ r, Aegis.MinOperations.min_operations nums queries = ok r →
          r.val.length = queries.val.length ∧
            ∀ (i : Nat), (hi : i < queries.val.length) → (hr : i < r.val.length) →
              (r.val[i]).val = upSum (vals nums.val) (queries.val[i]).val +
                downSum (vals nums.val) (queries.val[i]).val) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(queries), it is possible to make every element of nums equal to queries[i] using exactly r[i] unit increase/decrease operations, where one operation changes one array element by exactly 1, and no sequence of such operations can make every element equal to queries[i] using fewer than r[i] operations.
    Preconditions: 1 <= len(nums) <= 100000, 1 <= len(queries) <= 100000, for every j with 0 <= j < len(nums) we have 1 <= nums[j] <= 10^9, and for every i with 0 <= i < len(queries) we have 1 <= queries[i] <= 10^9. -/
  theorem spec_13 (nums queries : Aeneas.Std.Slice Aeneas.Std.I64)
      (h : ValidInput nums queries) :
      ∀ r, Aegis.MinOperations.min_operations nums queries = ok r →
        r.val.length = queries.val.length ∧
          ∀ (i : Nat), (hi : i < queries.val.length) → (hr : i < r.val.length) →
            0 ≤ (r.val[i]).val ∧
              flattenIn (vals nums.val) (queries.val[i]).val (r.val[i]).val.toNat ∧
                ∀ k, flattenIn (vals nums.val) (queries.val[i]).val k →
                  (r.val[i]).val.toNat ≤ k := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums queries : Aeneas.Std.Slice Aeneas.Std.I64)
        (h : ValidInput nums queries), ∀ r, Aegis.MinOperations.min_operations nums queries = ok r →
          r.val.length = queries.val.length ∧
            ∀ (i : Nat), (hi : i < queries.val.length) → (hr : i < r.val.length) →
              0 ≤ (r.val[i]).val ∧
                flattenIn (vals nums.val) (queries.val[i]).val (r.val[i]).val.toNat ∧
                  ∀ k, flattenIn (vals nums.val) (queries.val[i]).val k →
                    (r.val[i]).val.toNat ≤ k) := by
    sorry

  end AegisSpec.MinOperations
