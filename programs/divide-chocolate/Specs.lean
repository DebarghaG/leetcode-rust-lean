import Aegis.MaximizeSweetness.Code.Funs

/-!
# Specifications of `Aegis.MaximizeSweetness.maximize_sweetness`

LeetCode problem `divide-chocolate`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaximizeSweetness

  def getVal (s : Slice Std.I64) (i : ℕ) : ℤ :=
    match s.val[i]? with
    | some x => x.val
    | none => 0

  def pieceSum (s : Slice Std.I64) (a b : ℕ) : ℤ :=
    (((s.val.drop a).take (b - a)).map fun x => x.val).sum

  def totalVal (s : Slice Std.I64) : ℤ := (s.val.map fun x => x.val).sum

  def listMin : List ℤ → ℤ
    | [] => 0
    | x :: xs => xs.foldr min x

  def IsPartition (s : Slice Std.I64) (m : ℕ) (b : ℕ → ℕ) : Prop :=
    b 0 = 0 ∧ b m = s.val.length ∧ ∀ j, j < m → b j < b (j + 1)

  def pieceSums (s : Slice Std.I64) (m : ℕ) (b : ℕ → ℕ) : List ℤ :=
    (List.range m).map fun j => pieceSum s (b j) (b (j + 1))

  def partitionMin (s : Slice Std.I64) (m : ℕ) (b : ℕ → ℕ) : ℤ :=
    listMin (pieceSums s m b)

  def AllPiecesAtLeast (s : Slice Std.I64) (m : ℕ) (b : ℕ → ℕ) (x : ℤ) : Prop :=
    ∀ j, j < m → x ≤ pieceSum s (b j) (b (j + 1))

  /-- The function returns a result r (it does not fail) and r = max { min { S(b_{j-1}, b_j) : 1 <= j <= k+1 } : 0 = b_0 < b_1 < ... < b_{k+1} = n }, where S(a,b) denotes the sum of sweetness[i] for all i with a <= i < b. In words, r is the largest possible minimum total sweetness of one piece over all ways to cut the bar into exactly k+1 nonempty consecutive pieces.
    Preconditions: Let n = len(sweetness). The input satisfies n >= 1, n <= 10000, 0 <= k < n, and 1 <= sweetness[i] <= 100000 for every i with 0 <= i < n. The integer k is nonnegative and is interpreted as a natural number. -/
  theorem spec_1 (sweetness : Slice Std.I64) (k : Std.I64)
      (h_n_pos : 1 ≤ sweetness.val.length) (h_n_le : sweetness.val.length ≤ 10000)
      (h_k_nonneg : 0 ≤ k.val) (h_k_lt : k.val < (sweetness.val.length : ℤ))
      (h_bound : ∀ i, i < sweetness.val.length →
        1 ≤ getVal sweetness i ∧ getVal sweetness i ≤ 100000) :
      ∃ r : Std.I64, Aegis.MaximizeSweetness.maximize_sweetness sweetness k = ok r ∧
        (∃ b, IsPartition sweetness (k.val.toNat + 1) b ∧
          partitionMin sweetness (k.val.toNat + 1) b = r.val) ∧
        (∀ b, IsPartition sweetness (k.val.toNat + 1) b →
          partitionMin sweetness (k.val.toNat + 1) b ≤ r.val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (sweetness : Slice Std.I64) (k : Std.I64)
        (h_n_pos : 1 ≤ sweetness.val.length) (h_n_le : sweetness.val.length ≤ 10000)
        (h_k_nonneg : 0 ≤ k.val) (h_k_lt : k.val < (sweetness.val.length : ℤ))
        (h_bound : ∀ i, i < sweetness.val.length →
          1 ≤ getVal sweetness i ∧ getVal sweetness i ≤ 100000), ∃ r : Std.I64, Aegis.MaximizeSweetness.maximize_sweetness sweetness k = ok r ∧
          (∃ b, IsPartition sweetness (k.val.toNat + 1) b ∧
            partitionMin sweetness (k.val.toNat + 1) b = r.val) ∧
          (∀ b, IsPartition sweetness (k.val.toNat + 1) b →
            partitionMin sweetness (k.val.toNat + 1) b ≤ r.val)) := by
    sorry

  /-- The function returns a result r; in particular, it does not fail with overflow, out-of-bounds access, or panic.
    Preconditions: Let n = len(sweetness). The input satisfies n >= 1, n <= 10000, 0 <= k < n, and 1 <= sweetness[i] <= 100000 for every i with 0 <= i < n. -/
  theorem spec_2 (sweetness : Slice Std.I64) (k : Std.I64)
      (h_n_pos : 1 ≤ sweetness.val.length) (h_n_le : sweetness.val.length ≤ 10000)
      (h_k_nonneg : 0 ≤ k.val) (h_k_lt : k.val < (sweetness.val.length : ℤ))
      (h_bound : ∀ i, i < sweetness.val.length →
        1 ≤ getVal sweetness i ∧ getVal sweetness i ≤ 100000) :
      ∃ r : Std.I64, Aegis.MaximizeSweetness.maximize_sweetness sweetness k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (sweetness : Slice Std.I64) (k : Std.I64)
        (h_n_pos : 1 ≤ sweetness.val.length) (h_n_le : sweetness.val.length ≤ 10000)
        (h_k_nonneg : 0 ≤ k.val) (h_k_lt : k.val < (sweetness.val.length : ℤ))
        (h_bound : ∀ i, i < sweetness.val.length →
          1 ≤ getVal sweetness i ∧ getVal sweetness i ≤ 100000), ∃ r : Std.I64, Aegis.MaximizeSweetness.maximize_sweetness sweetness k = ok r) := by
    sorry

  /-- The function returns a result r and min(sweetness) <= r <= floor((sum of all sweetness[i] for 0 <= i < n) / (k+1)), where min(sweetness) = min { sweetness[i] : 0 <= i < n } and floor denotes integer floor division.
    Preconditions: Let n = len(sweetness). The input satisfies n >= 1, n <= 10000, 0 <= k < n, and 1 <= sweetness[i] <= 100000 for every i with 0 <= i < n. -/
  theorem spec_3 (sweetness : Slice Std.I64) (k : Std.I64)
      (h_n_pos : 1 ≤ sweetness.val.length) (h_n_le : sweetness.val.length ≤ 10000)
      (h_k_nonneg : 0 ≤ k.val) (h_k_lt : k.val < (sweetness.val.length : ℤ))
      (h_bound : ∀ i, i < sweetness.val.length →
        1 ≤ getVal sweetness i ∧ getVal sweetness i ≤ 100000) :
      ∃ r : Std.I64, Aegis.MaximizeSweetness.maximize_sweetness sweetness k = ok r ∧
        listMin (sweetness.val.map fun x => x.val) ≤ r.val ∧
        r.val ≤ totalVal sweetness / (k.val + 1) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (sweetness : Slice Std.I64) (k : Std.I64)
        (h_n_pos : 1 ≤ sweetness.val.length) (h_n_le : sweetness.val.length ≤ 10000)
        (h_k_nonneg : 0 ≤ k.val) (h_k_lt : k.val < (sweetness.val.length : ℤ))
        (h_bound : ∀ i, i < sweetness.val.length →
          1 ≤ getVal sweetness i ∧ getVal sweetness i ≤ 100000), ∃ r : Std.I64, Aegis.MaximizeSweetness.maximize_sweetness sweetness k = ok r ∧
          listMin (sweetness.val.map fun x => x.val) ≤ r.val ∧
          r.val ≤ totalVal sweetness / (k.val + 1)) := by
    sorry

  /-- The function returns a result r and there exist integers 0 = b_0 < b_1 < ... < b_{k+1} = n such that, putting S_j = sum of sweetness[i] for b_{j-1} <= i < b_j, we have S_j >= r for every j with 1 <= j <= k+1, and S_j = r for at least one such j.
    Preconditions: Let n = len(sweetness). The input satisfies n >= 1, n <= 10000, 0 <= k < n, and 1 <= sweetness[i] <= 100000 for every i with 0 <= i < n. -/
  theorem spec_4 (sweetness : Slice Std.I64) (k : Std.I64)
      (h_n_pos : 1 ≤ sweetness.val.length) (h_n_le : sweetness.val.length ≤ 10000)
      (h_k_nonneg : 0 ≤ k.val) (h_k_lt : k.val < (sweetness.val.length : ℤ))
      (h_bound : ∀ i, i < sweetness.val.length →
        1 ≤ getVal sweetness i ∧ getVal sweetness i ≤ 100000) :
      ∃ r : Std.I64, Aegis.MaximizeSweetness.maximize_sweetness sweetness k = ok r ∧
        ∃ b, IsPartition sweetness (k.val.toNat + 1) b ∧
          AllPiecesAtLeast sweetness (k.val.toNat + 1) b r.val ∧
          ∃ j, j < k.val.toNat + 1 ∧ pieceSum sweetness (b j) (b (j + 1)) = r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (sweetness : Slice Std.I64) (k : Std.I64)
        (h_n_pos : 1 ≤ sweetness.val.length) (h_n_le : sweetness.val.length ≤ 10000)
        (h_k_nonneg : 0 ≤ k.val) (h_k_lt : k.val < (sweetness.val.length : ℤ))
        (h_bound : ∀ i, i < sweetness.val.length →
          1 ≤ getVal sweetness i ∧ getVal sweetness i ≤ 100000), ∃ r : Std.I64, Aegis.MaximizeSweetness.maximize_sweetness sweetness k = ok r ∧
          ∃ b, IsPartition sweetness (k.val.toNat + 1) b ∧
            AllPiecesAtLeast sweetness (k.val.toNat + 1) b r.val ∧
            ∃ j, j < k.val.toNat + 1 ∧ pieceSum sweetness (b j) (b (j + 1)) = r.val) := by
    sorry

  /-- The function returns a result r and for every choice of integers 0 = b_0 < b_1 < ... < b_{k+1} = n, the minimum of the piece sums S_j = sum of sweetness[i] for b_{j-1} <= i < b_j (1 <= j <= k+1) is at most r. Equivalently, no partition into k+1 nonempty consecutive pieces has all piece sums strictly greater than r.
    Preconditions: Let n = len(sweetness). The input satisfies n >= 1, n <= 10000, 0 <= k < n, and 1 <= sweetness[i] <= 100000 for every i with 0 <= i < n. -/
  theorem spec_5 (sweetness : Slice Std.I64) (k : Std.I64)
      (h_n_pos : 1 ≤ sweetness.val.length) (h_n_le : sweetness.val.length ≤ 10000)
      (h_k_nonneg : 0 ≤ k.val) (h_k_lt : k.val < (sweetness.val.length : ℤ))
      (h_bound : ∀ i, i < sweetness.val.length →
        1 ≤ getVal sweetness i ∧ getVal sweetness i ≤ 100000) :
      ∃ r : Std.I64, Aegis.MaximizeSweetness.maximize_sweetness sweetness k = ok r ∧
        ∀ b, IsPartition sweetness (k.val.toNat + 1) b →
          partitionMin sweetness (k.val.toNat + 1) b ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (sweetness : Slice Std.I64) (k : Std.I64)
        (h_n_pos : 1 ≤ sweetness.val.length) (h_n_le : sweetness.val.length ≤ 10000)
        (h_k_nonneg : 0 ≤ k.val) (h_k_lt : k.val < (sweetness.val.length : ℤ))
        (h_bound : ∀ i, i < sweetness.val.length →
          1 ≤ getVal sweetness i ∧ getVal sweetness i ≤ 100000), ∃ r : Std.I64, Aegis.MaximizeSweetness.maximize_sweetness sweetness k = ok r ∧
          ∀ b, IsPartition sweetness (k.val.toNat + 1) b →
            partitionMin sweetness (k.val.toNat + 1) b ≤ r.val) := by
    sorry

  /-- The function returns a result r and for every integer x, there exists a partition of sweetness into exactly k+1 nonempty consecutive pieces all of whose sums are at least x if and only if x <= r.
    Preconditions: Let n = len(sweetness). The input satisfies n >= 1, n <= 10000, 0 <= k < n, and 1 <= sweetness[i] <= 100000 for every i with 0 <= i < n. -/
  theorem spec_6 (sweetness : Slice Std.I64) (k : Std.I64)
      (h_n_pos : 1 ≤ sweetness.val.length) (h_n_le : sweetness.val.length ≤ 10000)
      (h_k_nonneg : 0 ≤ k.val) (h_k_lt : k.val < (sweetness.val.length : ℤ))
      (h_bound : ∀ i, i < sweetness.val.length →
        1 ≤ getVal sweetness i ∧ getVal sweetness i ≤ 100000) :
      ∃ r : Std.I64, Aegis.MaximizeSweetness.maximize_sweetness sweetness k = ok r ∧
        ∀ x : ℤ, (∃ b, IsPartition sweetness (k.val.toNat + 1) b ∧
          AllPiecesAtLeast sweetness (k.val.toNat + 1) b x) ↔ x ≤ r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (sweetness : Slice Std.I64) (k : Std.I64)
        (h_n_pos : 1 ≤ sweetness.val.length) (h_n_le : sweetness.val.length ≤ 10000)
        (h_k_nonneg : 0 ≤ k.val) (h_k_lt : k.val < (sweetness.val.length : ℤ))
        (h_bound : ∀ i, i < sweetness.val.length →
          1 ≤ getVal sweetness i ∧ getVal sweetness i ≤ 100000), ∃ r : Std.I64, Aegis.MaximizeSweetness.maximize_sweetness sweetness k = ok r ∧
          ∀ x : ℤ, (∃ b, IsPartition sweetness (k.val.toNat + 1) b ∧
            AllPiecesAtLeast sweetness (k.val.toNat + 1) b x) ↔ x ≤ r.val) := by
    sorry

  /-- The function returns results r1 = maximize_sweetness(sweetness, k1) and r2 = maximize_sweetness(sweetness, k2), and r1 >= r2.
    Preconditions: Let n = len(sweetness). The array satisfies n >= 1, n <= 10000, and 1 <= sweetness[i] <= 100000 for every i with 0 <= i < n. Let k1 and k2 be integers with 0 <= k1 <= k2 < n. -/
  theorem spec_7 (sweetness : Slice Std.I64) (k1 k2 : Std.I64)
      (h_n_pos : 1 ≤ sweetness.val.length) (h_n_le : sweetness.val.length ≤ 10000)
      (h_k1_nonneg : 0 ≤ k1.val) (h_k12 : k1.val ≤ k2.val)
      (h_k2_lt : k2.val < (sweetness.val.length : ℤ))
      (h_bound : ∀ i, i < sweetness.val.length →
        1 ≤ getVal sweetness i ∧ getVal sweetness i ≤ 100000) :
      ∃ r1 r2 : Std.I64,
        Aegis.MaximizeSweetness.maximize_sweetness sweetness k1 = ok r1 ∧
        Aegis.MaximizeSweetness.maximize_sweetness sweetness k2 = ok r2 ∧
        r2.val ≤ r1.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (sweetness : Slice Std.I64) (k1 k2 : Std.I64)
        (h_n_pos : 1 ≤ sweetness.val.length) (h_n_le : sweetness.val.length ≤ 10000)
        (h_k1_nonneg : 0 ≤ k1.val) (h_k12 : k1.val ≤ k2.val)
        (h_k2_lt : k2.val < (sweetness.val.length : ℤ))
        (h_bound : ∀ i, i < sweetness.val.length →
          1 ≤ getVal sweetness i ∧ getVal sweetness i ≤ 100000), ∃ r1 r2 : Std.I64,
          Aegis.MaximizeSweetness.maximize_sweetness sweetness k1 = ok r1 ∧
          Aegis.MaximizeSweetness.maximize_sweetness sweetness k2 = ok r2 ∧
          r2.val ≤ r1.val) := by
    sorry

  /-- The function returns results r = maximize_sweetness(sweetness, k) and r' = maximize_sweetness(rev, k), and r = r'.
    Preconditions: Let n = len(sweetness). The input satisfies n >= 1, n <= 10000, 0 <= k < n, and 1 <= sweetness[i] <= 100000 for every i with 0 <= i < n. Let rev be the array of length n defined by rev[i] = sweetness[n-1-i] for every i with 0 <= i < n. -/
  theorem spec_8 (sweetness rev : Slice Std.I64) (k : Std.I64)
      (h_rev : rev.val = sweetness.val.reverse)
      (h_n_pos : 1 ≤ sweetness.val.length) (h_n_le : sweetness.val.length ≤ 10000)
      (h_k_nonneg : 0 ≤ k.val) (h_k_lt : k.val < (sweetness.val.length : ℤ))
      (h_bound : ∀ i, i < sweetness.val.length →
        1 ≤ getVal sweetness i ∧ getVal sweetness i ≤ 100000) :
      ∃ r r' : Std.I64,
        Aegis.MaximizeSweetness.maximize_sweetness sweetness k = ok r ∧
        Aegis.MaximizeSweetness.maximize_sweetness rev k = ok r' ∧
        r.val = r'.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (sweetness rev : Slice Std.I64) (k : Std.I64)
        (h_rev : rev.val = sweetness.val.reverse)
        (h_n_pos : 1 ≤ sweetness.val.length) (h_n_le : sweetness.val.length ≤ 10000)
        (h_k_nonneg : 0 ≤ k.val) (h_k_lt : k.val < (sweetness.val.length : ℤ))
        (h_bound : ∀ i, i < sweetness.val.length →
          1 ≤ getVal sweetness i ∧ getVal sweetness i ≤ 100000), ∃ r r' : Std.I64,
          Aegis.MaximizeSweetness.maximize_sweetness sweetness k = ok r ∧
          Aegis.MaximizeSweetness.maximize_sweetness rev k = ok r' ∧
          r.val = r'.val) := by
    sorry

  /-- The function returns r = c * floor(n / (k+1)), where floor denotes integer floor division.
    Preconditions: Let n = len(sweetness). The input satisfies n >= 1, n <= 10000, 0 <= k < n, and there is an integer c with 1 <= c <= 100000 such that sweetness[i] = c for every i with 0 <= i < n. -/
  theorem spec_9 (sweetness : Slice Std.I64) (k : Std.I64) (c : ℤ)
      (h_n_pos : 1 ≤ sweetness.val.length) (h_n_le : sweetness.val.length ≤ 10000)
      (h_k_nonneg : 0 ≤ k.val) (h_k_lt : k.val < (sweetness.val.length : ℤ))
      (h_c_low : 1 ≤ c) (h_c_high : c ≤ 100000)
      (h_const : ∀ i, i < sweetness.val.length → getVal sweetness i = c) :
      ∃ r : Std.I64, Aegis.MaximizeSweetness.maximize_sweetness sweetness k = ok r ∧
        r.val = c * ((sweetness.val.length / (k.val.toNat + 1) : ℕ) : ℤ) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (sweetness : Slice Std.I64) (k : Std.I64) (c : ℤ)
        (h_n_pos : 1 ≤ sweetness.val.length) (h_n_le : sweetness.val.length ≤ 10000)
        (h_k_nonneg : 0 ≤ k.val) (h_k_lt : k.val < (sweetness.val.length : ℤ))
        (h_c_low : 1 ≤ c) (h_c_high : c ≤ 100000)
        (h_const : ∀ i, i < sweetness.val.length → getVal sweetness i = c), ∃ r : Std.I64, Aegis.MaximizeSweetness.maximize_sweetness sweetness k = ok r ∧
          r.val = c * ((sweetness.val.length / (k.val.toNat + 1) : ℕ) : ℤ)) := by
    sorry

  /-- The function returns results rA = maximize_sweetness(A, k) and rB = maximize_sweetness(B, k), and rA <= rB.
    Preconditions: Let n = len(sweetness). Fix k with 0 <= k < n. Let A and B be two arrays of length n such that n <= 10000 and 1 <= A[i] <= B[i] <= 100000 for every i with 0 <= i < n. -/
  theorem spec_10 (A B : Slice Std.I64) (k : Std.I64)
      (h_len : A.val.length = B.val.length) (h_n_le : A.val.length ≤ 10000)
      (h_k_nonneg : 0 ≤ k.val) (h_k_lt : k.val < (A.val.length : ℤ))
      (h_bound : ∀ i, i < A.val.length →
        1 ≤ getVal A i ∧ getVal A i ≤ getVal B i ∧ getVal B i ≤ 100000) :
      ∃ rA rB : Std.I64, Aegis.MaximizeSweetness.maximize_sweetness A k = ok rA ∧
        Aegis.MaximizeSweetness.maximize_sweetness B k = ok rB ∧ rA.val ≤ rB.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (A B : Slice Std.I64) (k : Std.I64)
        (h_len : A.val.length = B.val.length) (h_n_le : A.val.length ≤ 10000)
        (h_k_nonneg : 0 ≤ k.val) (h_k_lt : k.val < (A.val.length : ℤ))
        (h_bound : ∀ i, i < A.val.length →
          1 ≤ getVal A i ∧ getVal A i ≤ getVal B i ∧ getVal B i ≤ 100000), ∃ rA rB : Std.I64, Aegis.MaximizeSweetness.maximize_sweetness A k = ok rA ∧
          Aegis.MaximizeSweetness.maximize_sweetness B k = ok rB ∧ rA.val ≤ rB.val) := by
    sorry

  /-- The function returns results r = maximize_sweetness(sweetness, k) and rA = maximize_sweetness(A, k), and rA = c * r.
    Preconditions: Let n = len(sweetness). The input satisfies n >= 1, n <= 10000, 0 <= k < n, and 1 <= sweetness[i] <= 100000 for every i with 0 <= i < n. Let c be an integer with c >= 1, and let A be the array of length n defined by A[i] = c * sweetness[i]. Assume 1 <= A[i] <= 100000 for every i with 0 <= i < n. -/
  theorem spec_11 (sweetness A : Slice Std.I64) (k : Std.I64) (c : ℤ)
      (h_len : A.val.length = sweetness.val.length)
      (h_n_pos : 1 ≤ sweetness.val.length) (h_n_le : sweetness.val.length ≤ 10000)
      (h_k_nonneg : 0 ≤ k.val) (h_k_lt : k.val < (sweetness.val.length : ℤ))
      (h_c : 1 ≤ c)
      (h_bound : ∀ i, i < sweetness.val.length →
        1 ≤ getVal sweetness i ∧ getVal sweetness i ≤ 100000)
      (h_scaled_bound : ∀ i, i < A.val.length →
        1 ≤ getVal A i ∧ getVal A i ≤ 100000)
      (h_scale : ∀ i, i < sweetness.val.length → getVal A i = c * getVal sweetness i) :
      ∃ r rA : Std.I64,
        Aegis.MaximizeSweetness.maximize_sweetness sweetness k = ok r ∧
        Aegis.MaximizeSweetness.maximize_sweetness A k = ok rA ∧
        rA.val = c * r.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (sweetness A : Slice Std.I64) (k : Std.I64) (c : ℤ)
        (h_len : A.val.length = sweetness.val.length)
        (h_n_pos : 1 ≤ sweetness.val.length) (h_n_le : sweetness.val.length ≤ 10000)
        (h_k_nonneg : 0 ≤ k.val) (h_k_lt : k.val < (sweetness.val.length : ℤ))
        (h_c : 1 ≤ c)
        (h_bound : ∀ i, i < sweetness.val.length →
          1 ≤ getVal sweetness i ∧ getVal sweetness i ≤ 100000)
        (h_scaled_bound : ∀ i, i < A.val.length →
          1 ≤ getVal A i ∧ getVal A i ≤ 100000)
        (h_scale : ∀ i, i < sweetness.val.length → getVal A i = c * getVal sweetness i), ∃ r rA : Std.I64,
          Aegis.MaximizeSweetness.maximize_sweetness sweetness k = ok r ∧
          Aegis.MaximizeSweetness.maximize_sweetness A k = ok rA ∧
          rA.val = c * r.val) := by
    sorry

  end AegisSpec.MaximizeSweetness
