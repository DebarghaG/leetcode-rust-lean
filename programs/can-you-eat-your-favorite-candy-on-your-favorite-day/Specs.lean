import Aegis.CanEat.Code.Funs

/-!
# Specifications of `Aegis.CanEat.can_eat`

LeetCode problem `can-you-eat-your-favorite-candy-on-your-favorite-day`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.CanEat

  def candies (candiesCount : Slice Std.I64) : List ℤ := candiesCount.val.map (fun c => c.val)

  def queryAt (queries : Slice (alloc.vec.Vec Std.I64)) (j : ℕ) : List ℤ :=
    ((queries.val.getD j (default : alloc.vec.Vec Std.I64)).val).map (fun x => x.val)

  def qF (queries : Slice (alloc.vec.Vec Std.I64)) (j : ℕ) : ℤ := (queryAt queries j).getD 0 0

  def qD (queries : Slice (alloc.vec.Vec Std.I64)) (j : ℕ) : ℤ := (queryAt queries j).getD 1 0

  def qC (queries : Slice (alloc.vec.Vec Std.I64)) (j : ℕ) : ℤ := (queryAt queries j).getD 2 0

  def prefixSum (l : List ℤ) (f : ℕ) : ℤ := (l.take f).sum

  def candiesBefore (candiesCount : Slice Std.I64) (f : ℕ) : ℤ := prefixSum (candies candiesCount) f

  def candyAt (candiesCount : Slice Std.I64) (i : ℕ) : ℤ := (candies candiesCount).getD i 0

  def candiesThrough (candiesCount : Slice Std.I64) (f : ℕ) : ℤ :=
    candiesBefore candiesCount f + candyAt candiesCount f

  def floorDiv (a b : ℤ) : ℤ := Int.fdiv a b

  def ProblemConstraints (candiesCount : Slice Std.I64)
      (queries : Slice (alloc.vec.Vec Std.I64)) : Prop :=

    1 ≤ candiesCount.val.length ∧ candiesCount.val.length ≤ 10 ^ 5 ∧

    (∀ i (hi : i < candiesCount.val.length),
        1 ≤ (candiesCount.val.get ⟨i, hi⟩).val ∧
          (candiesCount.val.get ⟨i, hi⟩).val ≤ 10 ^ 5) ∧

    1 ≤ queries.val.length ∧ queries.val.length ≤ 10 ^ 5 ∧

    (∀ j (hj : j < queries.val.length),
        (queries.val.get ⟨j, hj⟩).val.length = 3 ∧
          0 ≤ qF queries j ∧ qF queries j < (candiesCount.val.length : ℤ) ∧
          0 ≤ qD queries j ∧ qD queries j ≤ 10 ^ 9 ∧
          1 ≤ qC queries j ∧ qC queries j ≤ 10 ^ 9)

  /-- The function returns a result r with len(r) = len(queries). For every j with 0 <= j < len(queries), set f_j = queries[j][0], d_j = queries[j][1], c_j = queries[j][2], A_j = sum_{i=0}^{f_j-1} candiesCount[i] (A_j = 0 if f_j = 0), and B_j = A_j + candiesCount[f_j]. Then r[j] = true if and only if A_j < c_j * (d_j + 1) and B_j >= d_j + 1; otherwise r[j] = false.
    Preconditions: Assume the problem constraints: n = len(candiesCount), m = len(queries); 1 <= n <= 10^5; for every i with 0 <= i < n, 1 <= candiesCount[i] <= 10^5; 1 <= m <= 10^5; for every j with 0 <= j < m, len(queries[j]) = 3, and with f = queries[j][0], d = queries[j][1], c = queries[j][2], 0 <= f < n, 0 <= d <= 10^9, 1 <= c <= 10^9. All indices are 0-based and all statements use exact mathematical integers. -/
  theorem spec_1 (candiesCount : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
      (hcons : ProblemConstraints candiesCount queries) :
      ∃ r, Aegis.CanEat.can_eat candiesCount queries = ok r ∧
        r.val.length = queries.val.length ∧
        ∀ j (hj : j < queries.val.length),
          (r.val.getD j false = true ↔
            candiesBefore candiesCount (qF queries j).toNat <
                qC queries j * (qD queries j + 1) ∧
              candiesThrough candiesCount (qF queries j).toNat ≥ qD queries j + 1) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (candiesCount : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
        (hcons : ProblemConstraints candiesCount queries), ∃ r, Aegis.CanEat.can_eat candiesCount queries = ok r ∧
          r.val.length = queries.val.length ∧
          ∀ j (hj : j < queries.val.length),
            (r.val.getD j false = true ↔
              candiesBefore candiesCount (qF queries j).toNat <
                  qC queries j * (qD queries j + 1) ∧
                candiesThrough candiesCount (qF queries j).toNat ≥ qD queries j + 1)) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r; it never panics, fails, or overflows. In particular, every favoriteType value is a valid index into candiesCount, and the values A_j, B_j, and c_j * (d_j + 1) are within the i64 range.
    Preconditions: Assume the problem constraints: n = len(candiesCount), m = len(queries); 1 <= n <= 10^5; for every i with 0 <= i < n, 1 <= candiesCount[i] <= 10^5; 1 <= m <= 10^5; for every j with 0 <= j < m, len(queries[j]) = 3, and with f = queries[j][0], d = queries[j][1], c = queries[j][2], 0 <= f < n, 0 <= d <= 10^9, 1 <= c <= 10^9. All indices are 0-based and all statements use exact mathematical integers. -/
  theorem spec_2 (candiesCount : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
      (hcons : ProblemConstraints candiesCount queries) :
      ∃ r, Aegis.CanEat.can_eat candiesCount queries = ok r ∧
        (∀ j (hj : j < queries.val.length),
            0 ≤ qF queries j ∧ qF queries j < (candiesCount.val.length : ℤ)) ∧
        (∀ j (hj : j < queries.val.length),
            -(2 : ℤ) ^ 63 ≤ candiesBefore candiesCount (qF queries j).toNat ∧
              candiesBefore candiesCount (qF queries j).toNat ≤ (2 : ℤ) ^ 63 - 1 ∧
              -(2 : ℤ) ^ 63 ≤ candiesThrough candiesCount (qF queries j).toNat ∧
              candiesThrough candiesCount (qF queries j).toNat ≤ (2 : ℤ) ^ 63 - 1 ∧
              -(2 : ℤ) ^ 63 ≤ qC queries j * (qD queries j + 1) ∧
              qC queries j * (qD queries j + 1) ≤ (2 : ℤ) ^ 63 - 1) := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (candiesCount : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
        (hcons : ProblemConstraints candiesCount queries), ∃ r, Aegis.CanEat.can_eat candiesCount queries = ok r ∧
          (∀ j (hj : j < queries.val.length),
              0 ≤ qF queries j ∧ qF queries j < (candiesCount.val.length : ℤ)) ∧
          (∀ j (hj : j < queries.val.length),
              -(2 : ℤ) ^ 63 ≤ candiesBefore candiesCount (qF queries j).toNat ∧
                candiesBefore candiesCount (qF queries j).toNat ≤ (2 : ℤ) ^ 63 - 1 ∧
                -(2 : ℤ) ^ 63 ≤ candiesThrough candiesCount (qF queries j).toNat ∧
                candiesThrough candiesCount (qF queries j).toNat ≤ (2 : ℤ) ^ 63 - 1 ∧
                -(2 : ℤ) ^ 63 ≤ qC queries j * (qD queries j + 1) ∧
                qC queries j * (qD queries j + 1) ≤ (2 : ℤ) ^ 63 - 1)) := by
    sorry

  /-- The returned vector r has length exactly len(queries); there is exactly one Boolean answer r[j] for each query index j with 0 <= j < len(queries).
    Preconditions: Assume the problem constraints: n = len(candiesCount), m = len(queries); 1 <= n <= 10^5; for every i with 0 <= i < n, 1 <= candiesCount[i] <= 10^5; 1 <= m <= 10^5; for every j with 0 <= j < m, len(queries[j]) = 3, and with f = queries[j][0], d = queries[j][1], c = queries[j][2], 0 <= f < n, 0 <= d <= 10^9, 1 <= c <= 10^9. All indices are 0-based and all statements use exact mathematical integers. -/
  theorem spec_3 (candiesCount : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
      (hcons : ProblemConstraints candiesCount queries) :
      ∃ r, Aegis.CanEat.can_eat candiesCount queries = ok r ∧
        r.val.length = queries.val.length := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (candiesCount : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
        (hcons : ProblemConstraints candiesCount queries), ∃ r, Aegis.CanEat.can_eat candiesCount queries = ok r ∧
          r.val.length = queries.val.length) := by
    sorry

  /-- For every j with 0 <= j < len(queries), let f_j = queries[j][0], d_j = queries[j][1], c_j = queries[j][2], and A_j = sum_{i=0}^{f_j-1} candiesCount[i] (A_j = 0 if f_j = 0). If c_j * (d_j + 1) <= A_j, then r[j] = false.
    Preconditions: Assume the problem constraints: n = len(candiesCount), m = len(queries); 1 <= n <= 10^5; for every i with 0 <= i < n, 1 <= candiesCount[i] <= 10^5; 1 <= m <= 10^5; for every j with 0 <= j < m, len(queries[j]) = 3, and with f = queries[j][0], d = queries[j][1], c = queries[j][2], 0 <= f < n, 0 <= d <= 10^9, 1 <= c <= 10^9. All indices are 0-based and all statements use exact mathematical integers. -/
  theorem spec_4 (candiesCount : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
      (hcons : ProblemConstraints candiesCount queries) :
      ∃ r, Aegis.CanEat.can_eat candiesCount queries = ok r ∧
        ∀ j (hj : j < queries.val.length),
          qC queries j * (qD queries j + 1) ≤ candiesBefore candiesCount (qF queries j).toNat →
            r.val.getD j false = false := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (candiesCount : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
        (hcons : ProblemConstraints candiesCount queries), ∃ r, Aegis.CanEat.can_eat candiesCount queries = ok r ∧
          ∀ j (hj : j < queries.val.length),
            qC queries j * (qD queries j + 1) ≤ candiesBefore candiesCount (qF queries j).toNat →
              r.val.getD j false = false) := by
    sorry

  /-- For every j with 0 <= j < len(queries), let f_j = queries[j][0], d_j = queries[j][1], A_j = sum_{i=0}^{f_j-1} candiesCount[i] (A_j = 0 if f_j = 0), and B_j = A_j + candiesCount[f_j]. If B_j < d_j + 1, then r[j] = false.
    Preconditions: Assume the problem constraints: n = len(candiesCount), m = len(queries); 1 <= n <= 10^5; for every i with 0 <= i < n, 1 <= candiesCount[i] <= 10^5; 1 <= m <= 10^5; for every j with 0 <= j < m, len(queries[j]) = 3, and with f = queries[j][0], d = queries[j][1], c = queries[j][2], 0 <= f < n, 0 <= d <= 10^9, 1 <= c <= 10^9. All indices are 0-based and all statements use exact mathematical integers. -/
  theorem spec_5 (candiesCount : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
      (hcons : ProblemConstraints candiesCount queries) :
      ∃ r, Aegis.CanEat.can_eat candiesCount queries = ok r ∧
        ∀ j (hj : j < queries.val.length),
          candiesThrough candiesCount (qF queries j).toNat < qD queries j + 1 →
            r.val.getD j false = false := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (candiesCount : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
        (hcons : ProblemConstraints candiesCount queries), ∃ r, Aegis.CanEat.can_eat candiesCount queries = ok r ∧
          ∀ j (hj : j < queries.val.length),
            candiesThrough candiesCount (qF queries j).toNat < qD queries j + 1 →
              r.val.getD j false = false) := by
    sorry

  /-- For every j with 0 <= j < len(queries), let f_j = queries[j][0], d_j = queries[j][1], c_j = queries[j][2], A_j = sum_{i=0}^{f_j-1} candiesCount[i] (A_j = 0 if f_j = 0), and B_j = A_j + candiesCount[f_j]. If A_j < c_j * (d_j + 1) and B_j >= d_j + 1, then r[j] = true.
    Preconditions: Assume the problem constraints: n = len(candiesCount), m = len(queries); 1 <= n <= 10^5; for every i with 0 <= i < n, 1 <= candiesCount[i] <= 10^5; 1 <= m <= 10^5; for every j with 0 <= j < m, len(queries[j]) = 3, and with f = queries[j][0], d = queries[j][1], c = queries[j][2], 0 <= f < n, 0 <= d <= 10^9, 1 <= c <= 10^9. All indices are 0-based and all statements use exact mathematical integers. -/
  theorem spec_6 (candiesCount : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
      (hcons : ProblemConstraints candiesCount queries) :
      ∃ r, Aegis.CanEat.can_eat candiesCount queries = ok r ∧
        ∀ j (hj : j < queries.val.length),
          candiesBefore candiesCount (qF queries j).toNat <
              qC queries j * (qD queries j + 1) →
            candiesThrough candiesCount (qF queries j).toNat ≥ qD queries j + 1 →
              r.val.getD j false = true := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (candiesCount : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
        (hcons : ProblemConstraints candiesCount queries), ∃ r, Aegis.CanEat.can_eat candiesCount queries = ok r ∧
          ∀ j (hj : j < queries.val.length),
            candiesBefore candiesCount (qF queries j).toNat <
                qC queries j * (qD queries j + 1) →
              candiesThrough candiesCount (qF queries j).toNat ≥ qD queries j + 1 →
                r.val.getD j false = true) := by
    sorry

  /-- For every j with 0 <= j < len(queries), if queries[j][0] = 0, then r[j] = true if and only if candiesCount[0] >= queries[j][1] + 1.
    Preconditions: Assume the problem constraints: n = len(candiesCount), m = len(queries); 1 <= n <= 10^5; for every i with 0 <= i < n, 1 <= candiesCount[i] <= 10^5; 1 <= m <= 10^5; for every j with 0 <= j < m, len(queries[j]) = 3, and with f = queries[j][0], d = queries[j][1], c = queries[j][2], 0 <= f < n, 0 <= d <= 10^9, 1 <= c <= 10^9. All indices are 0-based and all statements use exact mathematical integers. -/
  theorem spec_7 (candiesCount : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
      (hcons : ProblemConstraints candiesCount queries) :
      ∃ r, Aegis.CanEat.can_eat candiesCount queries = ok r ∧
        ∀ j (hj : j < queries.val.length),
          qF queries j = 0 →
            (r.val.getD j false = true ↔ candyAt candiesCount 0 ≥ qD queries j + 1) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (candiesCount : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
        (hcons : ProblemConstraints candiesCount queries), ∃ r, Aegis.CanEat.can_eat candiesCount queries = ok r ∧
          ∀ j (hj : j < queries.val.length),
            qF queries j = 0 →
              (r.val.getD j false = true ↔ candyAt candiesCount 0 ≥ qD queries j + 1)) := by
    sorry

  /-- For every j with 0 <= j < len(queries), let f_j = queries[j][0], c_j = queries[j][2], and A_j = sum_{i=0}^{f_j-1} candiesCount[i] (A_j = 0 if f_j = 0). If queries[j][1] = 0, then r[j] = true if and only if A_j < c_j.
    Preconditions: Assume the problem constraints: n = len(candiesCount), m = len(queries); 1 <= n <= 10^5; for every i with 0 <= i < n, 1 <= candiesCount[i] <= 10^5; 1 <= m <= 10^5; for every j with 0 <= j < m, len(queries[j]) = 3, and with f = queries[j][0], d = queries[j][1], c = queries[j][2], 0 <= f < n, 0 <= d <= 10^9, 1 <= c <= 10^9. All indices are 0-based and all statements use exact mathematical integers. -/
  theorem spec_8 (candiesCount : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
      (hcons : ProblemConstraints candiesCount queries) :
      ∃ r, Aegis.CanEat.can_eat candiesCount queries = ok r ∧
        ∀ j (hj : j < queries.val.length),
          qD queries j = 0 →
            (r.val.getD j false = true ↔
              candiesBefore candiesCount (qF queries j).toNat < qC queries j) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (candiesCount : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
        (hcons : ProblemConstraints candiesCount queries), ∃ r, Aegis.CanEat.can_eat candiesCount queries = ok r ∧
          ∀ j (hj : j < queries.val.length),
            qD queries j = 0 →
              (r.val.getD j false = true ↔
                candiesBefore candiesCount (qF queries j).toNat < qC queries j)) := by
    sorry

  /-- For every j with 0 <= j < len(queries), let f_j = queries[j][0], d_j = queries[j][1], A_j = sum_{i=0}^{f_j-1} candiesCount[i] (A_j = 0 if f_j = 0), and B_j = A_j + candiesCount[f_j]. If queries[j][2] = 1, then r[j] = true if and only if A_j < d_j + 1 <= B_j.
    Preconditions: Assume the problem constraints: n = len(candiesCount), m = len(queries); 1 <= n <= 10^5; for every i with 0 <= i < n, 1 <= candiesCount[i] <= 10^5; 1 <= m <= 10^5; for every j with 0 <= j < m, len(queries[j]) = 3, and with f = queries[j][0], d = queries[j][1], c = queries[j][2], 0 <= f < n, 0 <= d <= 10^9, 1 <= c <= 10^9. All indices are 0-based and all statements use exact mathematical integers. -/
  theorem spec_9 (candiesCount : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
      (hcons : ProblemConstraints candiesCount queries) :
      ∃ r, Aegis.CanEat.can_eat candiesCount queries = ok r ∧
        ∀ j (hj : j < queries.val.length),
          qC queries j = 1 →
            (r.val.getD j false = true ↔
              candiesBefore candiesCount (qF queries j).toNat < qD queries j + 1 ∧
                candiesThrough candiesCount (qF queries j).toNat ≥ qD queries j + 1) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (candiesCount : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
        (hcons : ProblemConstraints candiesCount queries), ∃ r, Aegis.CanEat.can_eat candiesCount queries = ok r ∧
          ∀ j (hj : j < queries.val.length),
            qC queries j = 1 →
              (r.val.getD j false = true ↔
                candiesBefore candiesCount (qF queries j).toNat < qD queries j + 1 ∧
                  candiesThrough candiesCount (qF queries j).toNat ≥ qD queries j + 1)) := by
    sorry

  /-- For every pair of indices j, k with 0 <= j,k < len(queries), let f_j = queries[j][0], d_j = queries[j][1], c_j = queries[j][2] and f_k = queries[k][0], d_k = queries[k][1], c_k = queries[k][2]. If f_j = f_k, d_j = d_k, and c_j <= c_k, then r[j] = true implies r[k] = true.
    Preconditions: Assume the problem constraints: n = len(candiesCount), m = len(queries); 1 <= n <= 10^5; for every i with 0 <= i < n, 1 <= candiesCount[i] <= 10^5; 1 <= m <= 10^5; for every j with 0 <= j < m, len(queries[j]) = 3, and with f = queries[j][0], d = queries[j][1], c = queries[j][2], 0 <= f < n, 0 <= d <= 10^9, 1 <= c <= 10^9. All indices are 0-based and all statements use exact mathematical integers. -/
  theorem spec_10 (candiesCount : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
      (hcons : ProblemConstraints candiesCount queries) :
      ∃ r, Aegis.CanEat.can_eat candiesCount queries = ok r ∧
        ∀ j (hj : j < queries.val.length), ∀ k (hk : k < queries.val.length),
          qF queries j = qF queries k →
            qD queries j = qD queries k →
              qC queries j ≤ qC queries k →
                r.val.getD j false = true → r.val.getD k false = true := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (candiesCount : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
        (hcons : ProblemConstraints candiesCount queries), ∃ r, Aegis.CanEat.can_eat candiesCount queries = ok r ∧
          ∀ j (hj : j < queries.val.length), ∀ k (hk : k < queries.val.length),
            qF queries j = qF queries k →
              qD queries j = qD queries k →
                qC queries j ≤ qC queries k →
                  r.val.getD j false = true → r.val.getD k false = true) := by
    sorry

  /-- For every j with 0 <= j < len(queries), let f_j = queries[j][0], d_j = queries[j][1], c_j = queries[j][2], A_j = sum_{i=0}^{f_j-1} candiesCount[i] (A_j = 0 if f_j = 0), B_j = A_j + candiesCount[f_j], L_j = floor(A_j / c_j), and R_j = B_j - 1. Then r[j] = true if and only if L_j <= d_j <= R_j.
    Preconditions: Assume the problem constraints: n = len(candiesCount), m = len(queries); 1 <= n <= 10^5; for every i with 0 <= i < n, 1 <= candiesCount[i] <= 10^5; 1 <= m <= 10^5; for every j with 0 <= j < m, len(queries[j]) = 3, and with f = queries[j][0], d = queries[j][1], c = queries[j][2], 0 <= f < n, 0 <= d <= 10^9, 1 <= c <= 10^9. All indices are 0-based and all statements use exact mathematical integers. -/
  theorem spec_11 (candiesCount : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
      (hcons : ProblemConstraints candiesCount queries) :
      ∃ r, Aegis.CanEat.can_eat candiesCount queries = ok r ∧
        ∀ j (hj : j < queries.val.length),
          (r.val.getD j false = true ↔
            floorDiv (candiesBefore candiesCount (qF queries j).toNat) (qC queries j) ≤
                qD queries j ∧
              qD queries j ≤ candiesThrough candiesCount (qF queries j).toNat - 1) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (candiesCount : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
        (hcons : ProblemConstraints candiesCount queries), ∃ r, Aegis.CanEat.can_eat candiesCount queries = ok r ∧
          ∀ j (hj : j < queries.val.length),
            (r.val.getD j false = true ↔
              floorDiv (candiesBefore candiesCount (qF queries j).toNat) (qC queries j) ≤
                  qD queries j ∧
                qD queries j ≤ candiesThrough candiesCount (qF queries j).toNat - 1)) := by
    sorry

  /-- For every j with 0 <= j < len(queries), let f_j = queries[j][0], d_j = queries[j][1], c_j = queries[j][2], A_j = sum_{i=0}^{f_j-1} candiesCount[i] (A_j = 0 if f_j = 0), and B_j = A_j + candiesCount[f_j]. If c_j > A_j, then r[j] = true if and only if d_j + 1 <= B_j.
    Preconditions: Assume the problem constraints: n = len(candiesCount), m = len(queries); 1 <= n <= 10^5; for every i with 0 <= i < n, 1 <= candiesCount[i] <= 10^5; 1 <= m <= 10^5; for every j with 0 <= j < m, len(queries[j]) = 3, and with f = queries[j][0], d = queries[j][1], c = queries[j][2], 0 <= f < n, 0 <= d <= 10^9, 1 <= c <= 10^9. All indices are 0-based and all statements use exact mathematical integers. -/
  theorem spec_12 (candiesCount : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
      (hcons : ProblemConstraints candiesCount queries) :
      ∃ r, Aegis.CanEat.can_eat candiesCount queries = ok r ∧
        ∀ j (hj : j < queries.val.length),
          qC queries j > candiesBefore candiesCount (qF queries j).toNat →
            (r.val.getD j false = true ↔
              qD queries j + 1 ≤ candiesThrough candiesCount (qF queries j).toNat) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (candiesCount : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
        (hcons : ProblemConstraints candiesCount queries), ∃ r, Aegis.CanEat.can_eat candiesCount queries = ok r ∧
          ∀ j (hj : j < queries.val.length),
            qC queries j > candiesBefore candiesCount (qF queries j).toNat →
              (r.val.getD j false = true ↔
                qD queries j + 1 ≤ candiesThrough candiesCount (qF queries j).toNat)) := by
    sorry

  end AegisSpec.CanEat
