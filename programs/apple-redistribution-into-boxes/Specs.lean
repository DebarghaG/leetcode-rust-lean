import Aegis.MinimumBoxes.Code.Funs

/-!
# Specifications of `Aegis.MinimumBoxes.minimum_boxes`

LeetCode problem `apple-redistribution-into-boxes`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.MinimumBoxes

  namespace AegisSpec.MinimumBoxes

  open scoped BigOperators

  def sliceSum (s : Slice Std.I64) : ℤ := (s.val.map (fun x => x.val)).sum

  def entry (s : Slice Std.I64) (j : ℕ) : ℤ := (s.val[j]?).elim 0 (fun x => x.val)

  def sumOver (s : Slice Std.I64) (B : Finset ℕ) : ℤ := ∑ j ∈ B, entry s j

  def minEntry (s : Slice Std.I64) : ℤ :=
    match s.val.map (fun x => x.val) with
    | [] => 0
    | x :: xs => xs.foldl min x

  def maxEntry (s : Slice Std.I64) : ℤ :=
    match s.val.map (fun x => x.val) with
    | [] => 0
    | x :: xs => xs.foldl max x

  def prefixSum (c : List Std.I64) (k : ℕ) : ℤ := ((c.take k).map (fun x => x.val)).sum

  def SortedNonincreasing (c : List Std.I64) : Prop := c.Pairwise (fun a b => b.val ≤ a.val)

  def IsNonincreasingSort (c : List Std.I64) (s : Slice Std.I64) : Prop :=
    SortedNonincreasing c ∧ c.Perm s.val

  def IsPermutationOf (s' s : Slice Std.I64) : Prop :=
    ∃ e : Fin s'.val.length ≃ Fin s.val.length,
      ∀ i : Fin s'.val.length, s'.val.get i = s.val.get (e i)

  def IsIndexSet (s : Slice Std.I64) (B : Finset ℕ) : Prop :=
    B ⊆ Finset.range (Slice.len s).val

  def ApplePre (apple : Slice Std.I64) : Prop :=
    1 ≤ (Slice.len apple).val ∧ (Slice.len apple).val ≤ 50 ∧
      ∀ x ∈ apple.val, 1 ≤ x.val ∧ x.val ≤ 50

  def CapacityPre (capacity : Slice Std.I64) : Prop :=
    1 ≤ (Slice.len capacity).val ∧ (Slice.len capacity).val ≤ 50 ∧
      ∀ x ∈ capacity.val, 1 ≤ x.val ∧ x.val ≤ 50

  /-- The function returns a result r, and r is the least integer k with 1 <= k <= len(capacity) for which there exists a set B of indices into capacity such that |B| = k and sum_{j in B} capacity[j] >= S. Equivalently, r boxes suffice to hold all apples, and no smaller positive number of boxes suffices.
    Preconditions: Let S = sum_{i=0}^{len(apple)-1} apple[i]. The inputs satisfy 1 <= len(apple) <= 50, 1 <= len(capacity) <= 50, 1 <= apple[i] <= 50 for every i with 0 <= i < len(apple), 1 <= capacity[j] <= 50 for every j with 0 <= j < len(capacity), and S <= sum_{j=0}^{len(capacity)-1} capacity[j]. -/
  theorem spec_1 (apple capacity : Slice Std.I64)
      (h_apple : ApplePre apple) (h_capacity : CapacityPre capacity)
      (h_sum : sliceSum apple ≤ sliceSum capacity) :
      ∃ r : Std.I64,
        minimum_boxes apple capacity = Result.ok r ∧
        (1 ≤ r.val ∧ r.val ≤ ((Slice.len capacity).val : ℤ)) ∧
        (∃ B : Finset ℕ,
          IsIndexSet capacity B ∧ (B.card : ℤ) = r.val ∧ sliceSum apple ≤ sumOver capacity B) ∧
        (∀ B : Finset ℕ,
          IsIndexSet capacity B → 0 < B.card → (B.card : ℤ) < r.val →
            sumOver capacity B < sliceSum apple) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (apple capacity : Slice Std.I64)
        (h_apple : ApplePre apple) (h_capacity : CapacityPre capacity)
        (h_sum : sliceSum apple ≤ sliceSum capacity), ∃ r : Std.I64,
          minimum_boxes apple capacity = Result.ok r ∧
          (1 ≤ r.val ∧ r.val ≤ ((Slice.len capacity).val : ℤ)) ∧
          (∃ B : Finset ℕ,
            IsIndexSet capacity B ∧ (B.card : ℤ) = r.val ∧ sliceSum apple ≤ sumOver capacity B) ∧
          (∀ B : Finset ℕ,
            IsIndexSet capacity B → 0 < B.card → (B.card : ℤ) < r.val →
              sumOver capacity B < sliceSum apple)) := by
    sorry

  /-- The function returns a result r (it does not fail) for every input satisfying the preconditions.
    Preconditions: Let S = sum_{i=0}^{len(apple)-1} apple[i]. The inputs satisfy 1 <= len(apple) <= 50, 1 <= len(capacity) <= 50, 1 <= apple[i] <= 50 for every i with 0 <= i < len(apple), 1 <= capacity[j] <= 50 for every j with 0 <= j < len(capacity), and S <= sum_{j=0}^{len(capacity)-1} capacity[j]. -/
  theorem spec_2 (apple capacity : Slice Std.I64)
      (h_apple : ApplePre apple) (h_capacity : CapacityPre capacity)
      (h_sum : sliceSum apple ≤ sliceSum capacity) :
      ∃ r : Std.I64, minimum_boxes apple capacity = Result.ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (apple capacity : Slice Std.I64)
        (h_apple : ApplePre apple) (h_capacity : CapacityPre capacity)
        (h_sum : sliceSum apple ≤ sliceSum capacity), ∃ r : Std.I64, minimum_boxes apple capacity = Result.ok r) := by
    sorry

  /-- The function returns a result r and 1 <= r <= len(capacity).
    Preconditions: Let S = sum_{i=0}^{len(apple)-1} apple[i]. The inputs satisfy 1 <= len(apple) <= 50, 1 <= len(capacity) <= 50, 1 <= apple[i] <= 50 for every i with 0 <= i < len(apple), 1 <= capacity[j] <= 50 for every j with 0 <= j < len(capacity), and S <= sum_{j=0}^{len(capacity)-1} capacity[j]. -/
  theorem spec_3 (apple capacity : Slice Std.I64)
      (h_apple : ApplePre apple) (h_capacity : CapacityPre capacity)
      (h_sum : sliceSum apple ≤ sliceSum capacity) :
      ∃ r : Std.I64,
        minimum_boxes apple capacity = Result.ok r ∧
          1 ≤ r.val ∧ r.val ≤ ((Slice.len capacity).val : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (apple capacity : Slice Std.I64)
        (h_apple : ApplePre apple) (h_capacity : CapacityPre capacity)
        (h_sum : sliceSum apple ≤ sliceSum capacity), ∃ r : Std.I64,
          minimum_boxes apple capacity = Result.ok r ∧
            1 ≤ r.val ∧ r.val ≤ ((Slice.len capacity).val : ℤ)) := by
    sorry

  /-- The function returns a result r and there exists a set B of indices into capacity with |B| = r and sum_{j in B} capacity[j] >= S.
    Preconditions: Let S = sum_{i=0}^{len(apple)-1} apple[i]. The inputs satisfy 1 <= len(apple) <= 50, 1 <= len(capacity) <= 50, 1 <= apple[i] <= 50 for every i with 0 <= i < len(apple), 1 <= capacity[j] <= 50 for every j with 0 <= j < len(capacity), and S <= sum_{j=0}^{len(capacity)-1} capacity[j]. -/
  theorem spec_4 (apple capacity : Slice Std.I64)
      (h_apple : ApplePre apple) (h_capacity : CapacityPre capacity)
      (h_sum : sliceSum apple ≤ sliceSum capacity) :
      ∃ r : Std.I64,
        minimum_boxes apple capacity = Result.ok r ∧
          ∃ B : Finset ℕ,
            IsIndexSet capacity B ∧ (B.card : ℤ) = r.val ∧
              sliceSum apple ≤ sumOver capacity B := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (apple capacity : Slice Std.I64)
        (h_apple : ApplePre apple) (h_capacity : CapacityPre capacity)
        (h_sum : sliceSum apple ≤ sliceSum capacity), ∃ r : Std.I64,
          minimum_boxes apple capacity = Result.ok r ∧
            ∃ B : Finset ℕ,
              IsIndexSet capacity B ∧ (B.card : ℤ) = r.val ∧
                sliceSum apple ≤ sumOver capacity B) := by
    sorry

  /-- The function returns a result r and every set B of indices into capacity with |B| < r satisfies sum_{j in B} capacity[j] < S.
    Preconditions: Let S = sum_{i=0}^{len(apple)-1} apple[i]. The inputs satisfy 1 <= len(apple) <= 50, 1 <= len(capacity) <= 50, 1 <= apple[i] <= 50 for every i with 0 <= i < len(apple), 1 <= capacity[j] <= 50 for every j with 0 <= j < len(capacity), and S <= sum_{j=0}^{len(capacity)-1} capacity[j]. -/
  theorem spec_5 (apple capacity : Slice Std.I64)
      (h_apple : ApplePre apple) (h_capacity : CapacityPre capacity)
      (h_sum : sliceSum apple ≤ sliceSum capacity) :
      ∃ r : Std.I64,
        minimum_boxes apple capacity = Result.ok r ∧
          ∀ B : Finset ℕ,
            IsIndexSet capacity B → (B.card : ℤ) < r.val → sumOver capacity B < sliceSum apple := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (apple capacity : Slice Std.I64)
        (h_apple : ApplePre apple) (h_capacity : CapacityPre capacity)
        (h_sum : sliceSum apple ≤ sliceSum capacity), ∃ r : Std.I64,
          minimum_boxes apple capacity = Result.ok r ∧
            ∀ B : Finset ℕ,
              IsIndexSet capacity B → (B.card : ℤ) < r.val → sumOver capacity B < sliceSum apple) := by
    sorry

  /-- The function returns a result r, and r = 1 if and only if there exists an index j with 0 <= j < len(capacity) and capacity[j] >= S.
    Preconditions: Let S = sum_{i=0}^{len(apple)-1} apple[i]. The inputs satisfy 1 <= len(apple) <= 50, 1 <= len(capacity) <= 50, 1 <= apple[i] <= 50 for every i with 0 <= i < len(apple), 1 <= capacity[j] <= 50 for every j with 0 <= j < len(capacity), and S <= sum_{j=0}^{len(capacity)-1} capacity[j]. -/
  theorem spec_6 (apple capacity : Slice Std.I64)
      (h_apple : ApplePre apple) (h_capacity : CapacityPre capacity)
      (h_sum : sliceSum apple ≤ sliceSum capacity) :
      ∃ r : Std.I64,
        minimum_boxes apple capacity = Result.ok r ∧
          (r.val = 1 ↔
            ∃ j : ℕ, j < (Slice.len capacity).val ∧ sliceSum apple ≤ entry capacity j) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (apple capacity : Slice Std.I64)
        (h_apple : ApplePre apple) (h_capacity : CapacityPre capacity)
        (h_sum : sliceSum apple ≤ sliceSum capacity), ∃ r : Std.I64,
          minimum_boxes apple capacity = Result.ok r ∧
            (r.val = 1 ↔
              ∃ j : ℕ, j < (Slice.len capacity).val ∧ sliceSum apple ≤ entry capacity j)) := by
    sorry

  /-- Let C = sum_{j=0}^{len(capacity)-1} capacity[j] and let cmin = min_{0 <= j < len(capacity)} capacity[j], which is well-defined because len(capacity) >= 1. The function returns a result r, and r = len(capacity) if and only if C - cmin < S.
    Preconditions: Let S = sum_{i=0}^{len(apple)-1} apple[i]. The inputs satisfy 1 <= len(apple) <= 50, 1 <= len(capacity) <= 50, 1 <= apple[i] <= 50 for every i with 0 <= i < len(apple), 1 <= capacity[j] <= 50 for every j with 0 <= j < len(capacity), and S <= sum_{j=0}^{len(capacity)-1} capacity[j]. -/
  theorem spec_7 (apple capacity : Slice Std.I64)
      (h_apple : ApplePre apple) (h_capacity : CapacityPre capacity)
      (h_sum : sliceSum apple ≤ sliceSum capacity) :
      ∃ r : Std.I64,
        minimum_boxes apple capacity = Result.ok r ∧
          (r.val = ((Slice.len capacity).val : ℤ) ↔
            sliceSum capacity - minEntry capacity < sliceSum apple) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (apple capacity : Slice Std.I64)
        (h_apple : ApplePre apple) (h_capacity : CapacityPre capacity)
        (h_sum : sliceSum apple ≤ sliceSum capacity), ∃ r : Std.I64,
          minimum_boxes apple capacity = Result.ok r ∧
            (r.val = ((Slice.len capacity).val : ℤ) ↔
              sliceSum capacity - minEntry capacity < sliceSum apple)) := by
    sorry

  /-- Let Cmax = max_{0 <= j < len(capacity)} capacity[j]. The function returns a result r and r * Cmax >= S.
    Preconditions: Let S = sum_{i=0}^{len(apple)-1} apple[i]. The inputs satisfy 1 <= len(apple) <= 50, 1 <= len(capacity) <= 50, 1 <= apple[i] <= 50 for every i with 0 <= i < len(apple), 1 <= capacity[j] <= 50 for every j with 0 <= j < len(capacity), and S <= sum_{j=0}^{len(capacity)-1} capacity[j]. -/
  theorem spec_8 (apple capacity : Slice Std.I64)
      (h_apple : ApplePre apple) (h_capacity : CapacityPre capacity)
      (h_sum : sliceSum apple ≤ sliceSum capacity) :
      ∃ r : Std.I64,
        minimum_boxes apple capacity = Result.ok r ∧ sliceSum apple ≤ r.val * maxEntry capacity := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (apple capacity : Slice Std.I64)
        (h_apple : ApplePre apple) (h_capacity : CapacityPre capacity)
        (h_sum : sliceSum apple ≤ sliceSum capacity), ∃ r : Std.I64,
          minimum_boxes apple capacity = Result.ok r ∧ sliceSum apple ≤ r.val * maxEntry capacity) := by
    sorry

  /-- Whenever minimum_boxes apple1 capacity returns r1 and minimum_boxes apple2 capacity returns r2, we have r1 <= r2.
    Preconditions: Let apple1 and apple2 be any two slices satisfying 1 <= len(apple1) <= 50, 1 <= len(apple2) <= 50, and all their entries lie in [1,50]. Let S1 = sum_{i=0}^{len(apple1)-1} apple1[i] and S2 = sum_{i=0}^{len(apple2)-1} apple2[i]. Assume S1 <= S2 and S2 <= sum_{j=0}^{len(capacity)-1} capacity[j], where capacity satisfies 1 <= len(capacity) <= 50 and all its entries lie in [1,50]. -/
  theorem spec_9 (apple1 apple2 capacity : Slice Std.I64)
      (h_apple1 : ApplePre apple1) (h_apple2 : ApplePre apple2)
      (h_capacity : CapacityPre capacity)
      (h_mono : sliceSum apple1 ≤ sliceSum apple2)
      (h_sum : sliceSum apple2 ≤ sliceSum capacity) :
      ∀ r1 r2 : Std.I64,
        minimum_boxes apple1 capacity = Result.ok r1 → minimum_boxes apple2 capacity = Result.ok r2 →
          r1.val ≤ r2.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (apple1 apple2 capacity : Slice Std.I64)
        (h_apple1 : ApplePre apple1) (h_apple2 : ApplePre apple2)
        (h_capacity : CapacityPre capacity)
        (h_mono : sliceSum apple1 ≤ sliceSum apple2)
        (h_sum : sliceSum apple2 ≤ sliceSum capacity), ∀ r1 r2 : Std.I64,
          minimum_boxes apple1 capacity = Result.ok r1 → minimum_boxes apple2 capacity = Result.ok r2 →
            r1.val ≤ r2.val) := by
    sorry

  /-- Whenever minimum_boxes apple1 capacity returns r1 and minimum_boxes apple2 capacity returns r2, we have r1 = r2.
    Preconditions: Let apple1 and apple2 be any two slices satisfying 1 <= len(apple1) <= 50, 1 <= len(apple2) <= 50, and all their entries lie in [1,50]. Let S = sum_{i=0}^{len(apple1)-1} apple1[i] = sum_{i=0}^{len(apple2)-1} apple2[i]. Assume S <= sum_{j=0}^{len(capacity)-1} capacity[j], where capacity satisfies 1 <= len(capacity) <= 50 and all its entries lie in [1,50]. -/
  theorem spec_10 (apple1 apple2 capacity : Slice Std.I64)
      (h_apple1 : ApplePre apple1) (h_apple2 : ApplePre apple2)
      (h_capacity : CapacityPre capacity)
      (h_eq : sliceSum apple1 = sliceSum apple2)
      (h_sum : sliceSum apple2 ≤ sliceSum capacity) :
      ∀ r1 r2 : Std.I64,
        minimum_boxes apple1 capacity = Result.ok r1 → minimum_boxes apple2 capacity = Result.ok r2 →
          r1.val = r2.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (apple1 apple2 capacity : Slice Std.I64)
        (h_apple1 : ApplePre apple1) (h_apple2 : ApplePre apple2)
        (h_capacity : CapacityPre capacity)
        (h_eq : sliceSum apple1 = sliceSum apple2)
        (h_sum : sliceSum apple2 ≤ sliceSum capacity), ∀ r1 r2 : Std.I64,
          minimum_boxes apple1 capacity = Result.ok r1 → minimum_boxes apple2 capacity = Result.ok r2 →
            r1.val = r2.val) := by
    sorry

  /-- Whenever minimum_boxes apple capacity returns r and minimum_boxes apple capacity' returns r', we have r = r'.
    Preconditions: Let capacity' be a slice with len(capacity') = len(capacity) that is a permutation of capacity: there is a bijection f from {0,...,len(capacity)-1} to itself such that capacity'[i] = capacity[f(i)] for every i. Let apple satisfy 1 <= len(apple) <= 50 with all entries in [1,50], and let S = sum_{i=0}^{len(apple)-1} apple[i] <= sum_{j=0}^{len(capacity)-1} capacity[j]. Also capacity satisfies 1 <= len(capacity) <= 50 with all entries in [1,50]. -/
  theorem spec_11 (apple capacity capacity' : Slice Std.I64)
      (h_perm : IsPermutationOf capacity' capacity)
      (h_apple : ApplePre apple) (h_capacity : CapacityPre capacity)
      (h_sum : sliceSum apple ≤ sliceSum capacity) :
      ∀ r r' : Std.I64,
        minimum_boxes apple capacity = Result.ok r → minimum_boxes apple capacity' = Result.ok r' →
          r.val = r'.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (apple capacity capacity' : Slice Std.I64)
        (h_perm : IsPermutationOf capacity' capacity)
        (h_apple : ApplePre apple) (h_capacity : CapacityPre capacity)
        (h_sum : sliceSum apple ≤ sliceSum capacity), ∀ r r' : Std.I64,
          minimum_boxes apple capacity = Result.ok r → minimum_boxes apple capacity' = Result.ok r' →
            r.val = r'.val) := by
    sorry

  /-- Whenever minimum_boxes apple capacity1 returns r1 and minimum_boxes apple capacity2 returns r2, we have r2 <= r1.
    Preconditions: Let capacity1 and capacity2 be slices of the same length m with 1 <= m <= 50, all entries in [1,50], and capacity1[j] <= capacity2[j] for every j with 0 <= j < m. Let apple satisfy 1 <= len(apple) <= 50 with all entries in [1,50], and let S = sum_{i=0}^{len(apple)-1} apple[i]. Assume S <= sum_{j=0}^{m-1} capacity1[j]. -/
  theorem spec_12 (apple capacity1 capacity2 : Slice Std.I64) (m : ℕ)
      (h_apple : ApplePre apple)
      (h_len1 : (Slice.len capacity1).val = m) (h_len2 : (Slice.len capacity2).val = m)
      (h_m : 1 ≤ m ∧ m ≤ 50)
      (h_entries1 : ∀ x ∈ capacity1.val, 1 ≤ x.val ∧ x.val ≤ 50)
      (h_entries2 : ∀ x ∈ capacity2.val, 1 ≤ x.val ∧ x.val ≤ 50)
      (h_pointwise : ∀ j : ℕ, j < m → entry capacity1 j ≤ entry capacity2 j)
      (h_sum : sliceSum apple ≤ sliceSum capacity1) :
      ∀ r1 r2 : Std.I64,
        minimum_boxes apple capacity1 = Result.ok r1 →
          minimum_boxes apple capacity2 = Result.ok r2 → r2.val ≤ r1.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (apple capacity1 capacity2 : Slice Std.I64) (m : ℕ)
        (h_apple : ApplePre apple)
        (h_len1 : (Slice.len capacity1).val = m) (h_len2 : (Slice.len capacity2).val = m)
        (h_m : 1 ≤ m ∧ m ≤ 50)
        (h_entries1 : ∀ x ∈ capacity1.val, 1 ≤ x.val ∧ x.val ≤ 50)
        (h_entries2 : ∀ x ∈ capacity2.val, 1 ≤ x.val ∧ x.val ≤ 50)
        (h_pointwise : ∀ j : ℕ, j < m → entry capacity1 j ≤ entry capacity2 j)
        (h_sum : sliceSum apple ≤ sliceSum capacity1), ∀ r1 r2 : Std.I64,
          minimum_boxes apple capacity1 = Result.ok r1 →
            minimum_boxes apple capacity2 = Result.ok r2 → r2.val ≤ r1.val) := by
    sorry

  /-- Let c1 >= c2 >= ... >= cm be the values capacity[0],...,capacity[m-1] sorted in nonincreasing order, where m = len(capacity). The function returns a result r and sum_{i=1}^{r} ci >= S.
    Preconditions: Let S = sum_{i=0}^{len(apple)-1} apple[i]. The inputs satisfy 1 <= len(apple) <= 50, 1 <= len(capacity) <= 50, 1 <= apple[i] <= 50 for every i with 0 <= i < len(apple), 1 <= capacity[j] <= 50 for every j with 0 <= j < len(capacity), and S <= sum_{j=0}^{len(capacity)-1} capacity[j]. -/
  theorem spec_13 (apple capacity : Slice Std.I64)
      (h_apple : ApplePre apple) (h_capacity : CapacityPre capacity)
      (h_sum : sliceSum apple ≤ sliceSum capacity) :
      ∃ r : Std.I64,
        minimum_boxes apple capacity = Result.ok r ∧
          ∀ c : List Std.I64,
            IsNonincreasingSort c capacity → sliceSum apple ≤ prefixSum c r.val.toNat := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (apple capacity : Slice Std.I64)
        (h_apple : ApplePre apple) (h_capacity : CapacityPre capacity)
        (h_sum : sliceSum apple ≤ sliceSum capacity), ∃ r : Std.I64,
          minimum_boxes apple capacity = Result.ok r ∧
            ∀ c : List Std.I64,
              IsNonincreasingSort c capacity → sliceSum apple ≤ prefixSum c r.val.toNat) := by
    sorry

  /-- Let c1 >= c2 >= ... >= cm be the values capacity[0],...,capacity[m-1] sorted in nonincreasing order, where m = len(capacity). The function returns a result r and sum_{i=1}^{r-1} ci < S, with the convention that the empty sum when r = 1 is 0.
    Preconditions: Let S = sum_{i=0}^{len(apple)-1} apple[i]. The inputs satisfy 1 <= len(apple) <= 50, 1 <= len(capacity) <= 50, 1 <= apple[i] <= 50 for every i with 0 <= i < len(apple), 1 <= capacity[j] <= 50 for every j with 0 <= j < len(capacity), and S <= sum_{j=0}^{len(capacity)-1} capacity[j]. -/
  theorem spec_14 (apple capacity : Slice Std.I64)
      (h_apple : ApplePre apple) (h_capacity : CapacityPre capacity)
      (h_sum : sliceSum apple ≤ sliceSum capacity) :
      ∃ r : Std.I64,
        minimum_boxes apple capacity = Result.ok r ∧
          ∀ c : List Std.I64,
            IsNonincreasingSort c capacity → prefixSum c (r.val.toNat - 1) < sliceSum apple := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (apple capacity : Slice Std.I64)
        (h_apple : ApplePre apple) (h_capacity : CapacityPre capacity)
        (h_sum : sliceSum apple ≤ sliceSum capacity), ∃ r : Std.I64,
          minimum_boxes apple capacity = Result.ok r ∧
            ∀ c : List Std.I64,
              IsNonincreasingSort c capacity → prefixSum c (r.val.toNat - 1) < sliceSum apple) := by
    sorry

  end AegisSpec.MinimumBoxes
