import Aegis.MaximumBags.Code.Funs

/-!
# Specifications of `Aegis.MaximumBags.maximum_bags`

LeetCode problem `maximum-bags-with-full-capacity-of-rocks`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MaximumBags

namespace AegisSpec.MaximumBags

def i64At (s : Slice I64) (i : ℕ) : ℤ :=
  match s.val[i]? with
  | some v => v.val
  | none => 0

def deficit (capacity rocks : Slice I64) (i : ℕ) : ℤ :=
  i64At capacity i - i64At rocks i

def totalDeficit (capacity rocks : Slice I64) (S : Finset ℕ) : ℤ :=
  S.sum (fun i => deficit capacity rocks i)

def Feasible (capacity rocks : Slice I64) (n : ℕ) (a : I64) (S : Finset ℕ) : Prop :=
  S ⊆ Finset.range n ∧ totalDeficit capacity rocks S ≤ a.val

def fullIndices (capacity rocks : Slice I64) (n : ℕ) : Finset ℕ :=
  (Finset.range n).filter (fun i => i64At rocks i = i64At capacity i)

def affordableIndices (capacity rocks : Slice I64) (n : ℕ) (a : I64) : Finset ℕ :=
  (Finset.range n).filter (fun i => deficit capacity rocks i ≤ a.val)

/-- Whenever maximum_bags(capacity, rocks, additionalRocks) returns a result r, r is the largest integer k such that there exists a set S of indices with S subset of {0,1,...,n-1}, |S| = k, and sum_{i in S} (capacity[i] - rocks[i]) <= additionalRocks. Equivalently, there exists such an S with |S| = r, and for every set T subset of {0,1,...,n-1}, if sum_{i in T} (capacity[i] - rocks[i]) <= additionalRocks then |T| <= r.
  Preconditions: Let n = len(capacity). Assume len(capacity) = len(rocks) = n, 1 <= n <= 50000, and for every i with 0 <= i < n, 1 <= capacity[i] <= 1000000000 and 0 <= rocks[i] <= capacity[i]. Also assume additionalRocks >= 0. -/
theorem spec_1
    (capacity rocks : Slice I64) (additionalRocks : I64) (n : ℕ)
    (hcap_len : capacity.val.length = n)
    (hrocks_len : rocks.val.length = n)
    (hn_pos : 1 ≤ n) (hn_bound : n ≤ 50000)
    (hcap_pos : ∀ i, i < n → 1 ≤ i64At capacity i)
    (hcap_le : ∀ i, i < n → i64At capacity i ≤ 1000000000)
    (hrocks_nonneg : ∀ i, i < n → 0 ≤ i64At rocks i)
    (hrocks_le : ∀ i, i < n → i64At rocks i ≤ i64At capacity i)
    (hadditional : 0 ≤ additionalRocks.val)
    (r : I64) (hres : maximum_bags capacity rocks additionalRocks = ok r) :
    (∃ S : Finset ℕ,
        S ⊆ Finset.range n ∧ (S.card : ℤ) = r.val ∧
          totalDeficit capacity rocks S ≤ additionalRocks.val) ∧
      (∀ T : Finset ℕ,
        T ⊆ Finset.range n →
          totalDeficit capacity rocks T ≤ additionalRocks.val → (T.card : ℤ) ≤ r.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (capacity rocks : Slice I64) (additionalRocks : I64) (n : ℕ)
    (hcap_len : capacity.val.length = n)
    (hrocks_len : rocks.val.length = n)
    (hn_pos : 1 ≤ n) (hn_bound : n ≤ 50000)
    (hcap_pos : ∀ i, i < n → 1 ≤ i64At capacity i)
    (hcap_le : ∀ i, i < n → i64At capacity i ≤ 1000000000)
    (hrocks_nonneg : ∀ i, i < n → 0 ≤ i64At rocks i)
    (hrocks_le : ∀ i, i < n → i64At rocks i ≤ i64At capacity i)
    (hadditional : 0 ≤ additionalRocks.val)
    (r : I64) (hres : maximum_bags capacity rocks additionalRocks = ok r), (∃ S : Finset ℕ,
        S ⊆ Finset.range n ∧ (S.card : ℤ) = r.val ∧
          totalDeficit capacity rocks S ≤ additionalRocks.val) ∧
      (∀ T : Finset ℕ,
        T ⊆ Finset.range n →
          totalDeficit capacity rocks T ≤ additionalRocks.val → (T.card : ℤ) ≤ r.val)) := by
  sorry

/-- The function maximum_bags(capacity, rocks, additionalRocks) returns a result r and does not fail.
  Preconditions: Let n = len(capacity). Assume len(capacity) = len(rocks) = n, 1 <= n <= 50000, and for every i with 0 <= i < n, 1 <= capacity[i] <= 1000000000 and 0 <= rocks[i] <= capacity[i]. Also assume additionalRocks >= 0. -/
theorem spec_2
    (capacity rocks : Slice I64) (additionalRocks : I64) (n : ℕ)
    (hcap_len : capacity.val.length = n)
    (hrocks_len : rocks.val.length = n)
    (hn_pos : 1 ≤ n) (hn_bound : n ≤ 50000)
    (hcap_pos : ∀ i, i < n → 1 ≤ i64At capacity i)
    (hcap_le : ∀ i, i < n → i64At capacity i ≤ 1000000000)
    (hrocks_nonneg : ∀ i, i < n → 0 ≤ i64At rocks i)
    (hrocks_le : ∀ i, i < n → i64At rocks i ≤ i64At capacity i)
    (hadditional : 0 ≤ additionalRocks.val) :
    ∃ r : I64, maximum_bags capacity rocks additionalRocks = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (capacity rocks : Slice I64) (additionalRocks : I64) (n : ℕ)
    (hcap_len : capacity.val.length = n)
    (hrocks_len : rocks.val.length = n)
    (hn_pos : 1 ≤ n) (hn_bound : n ≤ 50000)
    (hcap_pos : ∀ i, i < n → 1 ≤ i64At capacity i)
    (hcap_le : ∀ i, i < n → i64At capacity i ≤ 1000000000)
    (hrocks_nonneg : ∀ i, i < n → 0 ≤ i64At rocks i)
    (hrocks_le : ∀ i, i < n → i64At rocks i ≤ i64At capacity i)
    (hadditional : 0 ≤ additionalRocks.val), ∃ r : I64, maximum_bags capacity rocks additionalRocks = ok r) := by
  sorry

/-- Whenever maximum_bags(capacity, rocks, additionalRocks) returns a result r, 0 <= r <= n.
  Preconditions: Let n = len(capacity). Assume len(capacity) = len(rocks) = n, 1 <= n <= 50000, and for every i with 0 <= i < n, 1 <= capacity[i] <= 1000000000 and 0 <= rocks[i] <= capacity[i]. Also assume additionalRocks >= 0. -/
theorem spec_3
    (capacity rocks : Slice I64) (additionalRocks : I64) (n : ℕ)
    (hcap_len : capacity.val.length = n)
    (hrocks_len : rocks.val.length = n)
    (hn_pos : 1 ≤ n) (hn_bound : n ≤ 50000)
    (hcap_pos : ∀ i, i < n → 1 ≤ i64At capacity i)
    (hcap_le : ∀ i, i < n → i64At capacity i ≤ 1000000000)
    (hrocks_nonneg : ∀ i, i < n → 0 ≤ i64At rocks i)
    (hrocks_le : ∀ i, i < n → i64At rocks i ≤ i64At capacity i)
    (hadditional : 0 ≤ additionalRocks.val)
    (r : I64) (hres : maximum_bags capacity rocks additionalRocks = ok r) :
    0 ≤ r.val ∧ r.val ≤ (n : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (capacity rocks : Slice I64) (additionalRocks : I64) (n : ℕ)
    (hcap_len : capacity.val.length = n)
    (hrocks_len : rocks.val.length = n)
    (hn_pos : 1 ≤ n) (hn_bound : n ≤ 50000)
    (hcap_pos : ∀ i, i < n → 1 ≤ i64At capacity i)
    (hcap_le : ∀ i, i < n → i64At capacity i ≤ 1000000000)
    (hrocks_nonneg : ∀ i, i < n → 0 ≤ i64At rocks i)
    (hrocks_le : ∀ i, i < n → i64At rocks i ≤ i64At capacity i)
    (hadditional : 0 ≤ additionalRocks.val)
    (r : I64) (hres : maximum_bags capacity rocks additionalRocks = ok r), 0 ≤ r.val ∧ r.val ≤ (n : ℤ)) := by
  sorry

/-- Whenever maximum_bags(capacity, rocks, additionalRocks) returns a result r, there exists a set S of indices with S subset of {0,1,...,n-1}, |S| = r, and sum_{i in S} (capacity[i] - rocks[i]) <= additionalRocks.
  Preconditions: Let n = len(capacity). Assume len(capacity) = len(rocks) = n, 1 <= n <= 50000, and for every i with 0 <= i < n, 1 <= capacity[i] <= 1000000000 and 0 <= rocks[i] <= capacity[i]. Also assume additionalRocks >= 0. -/
theorem spec_4
    (capacity rocks : Slice I64) (additionalRocks : I64) (n : ℕ)
    (hcap_len : capacity.val.length = n)
    (hrocks_len : rocks.val.length = n)
    (hn_pos : 1 ≤ n) (hn_bound : n ≤ 50000)
    (hcap_pos : ∀ i, i < n → 1 ≤ i64At capacity i)
    (hcap_le : ∀ i, i < n → i64At capacity i ≤ 1000000000)
    (hrocks_nonneg : ∀ i, i < n → 0 ≤ i64At rocks i)
    (hrocks_le : ∀ i, i < n → i64At rocks i ≤ i64At capacity i)
    (hadditional : 0 ≤ additionalRocks.val)
    (r : I64) (hres : maximum_bags capacity rocks additionalRocks = ok r) :
    ∃ S : Finset ℕ,
      S ⊆ Finset.range n ∧ (S.card : ℤ) = r.val ∧
        totalDeficit capacity rocks S ≤ additionalRocks.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (capacity rocks : Slice I64) (additionalRocks : I64) (n : ℕ)
    (hcap_len : capacity.val.length = n)
    (hrocks_len : rocks.val.length = n)
    (hn_pos : 1 ≤ n) (hn_bound : n ≤ 50000)
    (hcap_pos : ∀ i, i < n → 1 ≤ i64At capacity i)
    (hcap_le : ∀ i, i < n → i64At capacity i ≤ 1000000000)
    (hrocks_nonneg : ∀ i, i < n → 0 ≤ i64At rocks i)
    (hrocks_le : ∀ i, i < n → i64At rocks i ≤ i64At capacity i)
    (hadditional : 0 ≤ additionalRocks.val)
    (r : I64) (hres : maximum_bags capacity rocks additionalRocks = ok r), ∃ S : Finset ℕ,
      S ⊆ Finset.range n ∧ (S.card : ℤ) = r.val ∧
        totalDeficit capacity rocks S ≤ additionalRocks.val) := by
  sorry

/-- Whenever maximum_bags(capacity, rocks, additionalRocks) returns a result r, for every set T of indices with T subset of {0,1,...,n-1}, if sum_{i in T} (capacity[i] - rocks[i]) <= additionalRocks then |T| <= r.
  Preconditions: Let n = len(capacity). Assume len(capacity) = len(rocks) = n, 1 <= n <= 50000, and for every i with 0 <= i < n, 1 <= capacity[i] <= 1000000000 and 0 <= rocks[i] <= capacity[i]. Also assume additionalRocks >= 0. -/
theorem spec_5
    (capacity rocks : Slice I64) (additionalRocks : I64) (n : ℕ)
    (hcap_len : capacity.val.length = n)
    (hrocks_len : rocks.val.length = n)
    (hn_pos : 1 ≤ n) (hn_bound : n ≤ 50000)
    (hcap_pos : ∀ i, i < n → 1 ≤ i64At capacity i)
    (hcap_le : ∀ i, i < n → i64At capacity i ≤ 1000000000)
    (hrocks_nonneg : ∀ i, i < n → 0 ≤ i64At rocks i)
    (hrocks_le : ∀ i, i < n → i64At rocks i ≤ i64At capacity i)
    (hadditional : 0 ≤ additionalRocks.val)
    (r : I64) (hres : maximum_bags capacity rocks additionalRocks = ok r) :
    ∀ T : Finset ℕ,
      T ⊆ Finset.range n →
        totalDeficit capacity rocks T ≤ additionalRocks.val → (T.card : ℤ) ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (capacity rocks : Slice I64) (additionalRocks : I64) (n : ℕ)
    (hcap_len : capacity.val.length = n)
    (hrocks_len : rocks.val.length = n)
    (hn_pos : 1 ≤ n) (hn_bound : n ≤ 50000)
    (hcap_pos : ∀ i, i < n → 1 ≤ i64At capacity i)
    (hcap_le : ∀ i, i < n → i64At capacity i ≤ 1000000000)
    (hrocks_nonneg : ∀ i, i < n → 0 ≤ i64At rocks i)
    (hrocks_le : ∀ i, i < n → i64At rocks i ≤ i64At capacity i)
    (hadditional : 0 ≤ additionalRocks.val)
    (r : I64) (hres : maximum_bags capacity rocks additionalRocks = ok r), ∀ T : Finset ℕ,
      T ⊆ Finset.range n →
        totalDeficit capacity rocks T ≤ additionalRocks.val → (T.card : ℤ) ≤ r.val) := by
  sorry

/-- Whenever maximum_bags(capacity, rocks, additionalRocks) returns a result r, r = n if and only if sum_{i=0}^{n-1} (capacity[i] - rocks[i]) <= additionalRocks.
  Preconditions: Let n = len(capacity). Assume len(capacity) = len(rocks) = n, 1 <= n <= 50000, and for every i with 0 <= i < n, 1 <= capacity[i] <= 1000000000 and 0 <= rocks[i] <= capacity[i]. Also assume additionalRocks >= 0. -/
theorem spec_6
    (capacity rocks : Slice I64) (additionalRocks : I64) (n : ℕ)
    (hcap_len : capacity.val.length = n)
    (hrocks_len : rocks.val.length = n)
    (hn_pos : 1 ≤ n) (hn_bound : n ≤ 50000)
    (hcap_pos : ∀ i, i < n → 1 ≤ i64At capacity i)
    (hcap_le : ∀ i, i < n → i64At capacity i ≤ 1000000000)
    (hrocks_nonneg : ∀ i, i < n → 0 ≤ i64At rocks i)
    (hrocks_le : ∀ i, i < n → i64At rocks i ≤ i64At capacity i)
    (hadditional : 0 ≤ additionalRocks.val)
    (r : I64) (hres : maximum_bags capacity rocks additionalRocks = ok r) :
    r.val = (n : ℤ) ↔ totalDeficit capacity rocks (Finset.range n) ≤ additionalRocks.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (capacity rocks : Slice I64) (additionalRocks : I64) (n : ℕ)
    (hcap_len : capacity.val.length = n)
    (hrocks_len : rocks.val.length = n)
    (hn_pos : 1 ≤ n) (hn_bound : n ≤ 50000)
    (hcap_pos : ∀ i, i < n → 1 ≤ i64At capacity i)
    (hcap_le : ∀ i, i < n → i64At capacity i ≤ 1000000000)
    (hrocks_nonneg : ∀ i, i < n → 0 ≤ i64At rocks i)
    (hrocks_le : ∀ i, i < n → i64At rocks i ≤ i64At capacity i)
    (hadditional : 0 ≤ additionalRocks.val)
    (r : I64) (hres : maximum_bags capacity rocks additionalRocks = ok r), r.val = (n : ℤ) ↔ totalDeficit capacity rocks (Finset.range n) ≤ additionalRocks.val) := by
  sorry

/-- Whenever maximum_bags(capacity, rocks, additionalRocks) returns a result r, r = 0 if and only if for every i with 0 <= i < n, capacity[i] - rocks[i] > additionalRocks.
  Preconditions: Let n = len(capacity). Assume len(capacity) = len(rocks) = n, 1 <= n <= 50000, and for every i with 0 <= i < n, 1 <= capacity[i] <= 1000000000 and 0 <= rocks[i] <= capacity[i]. Also assume additionalRocks >= 0. -/
theorem spec_7
    (capacity rocks : Slice I64) (additionalRocks : I64) (n : ℕ)
    (hcap_len : capacity.val.length = n)
    (hrocks_len : rocks.val.length = n)
    (hn_pos : 1 ≤ n) (hn_bound : n ≤ 50000)
    (hcap_pos : ∀ i, i < n → 1 ≤ i64At capacity i)
    (hcap_le : ∀ i, i < n → i64At capacity i ≤ 1000000000)
    (hrocks_nonneg : ∀ i, i < n → 0 ≤ i64At rocks i)
    (hrocks_le : ∀ i, i < n → i64At rocks i ≤ i64At capacity i)
    (hadditional : 0 ≤ additionalRocks.val)
    (r : I64) (hres : maximum_bags capacity rocks additionalRocks = ok r) :
    r.val = 0 ↔ ∀ i, i < n → additionalRocks.val < deficit capacity rocks i := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (capacity rocks : Slice I64) (additionalRocks : I64) (n : ℕ)
    (hcap_len : capacity.val.length = n)
    (hrocks_len : rocks.val.length = n)
    (hn_pos : 1 ≤ n) (hn_bound : n ≤ 50000)
    (hcap_pos : ∀ i, i < n → 1 ≤ i64At capacity i)
    (hcap_le : ∀ i, i < n → i64At capacity i ≤ 1000000000)
    (hrocks_nonneg : ∀ i, i < n → 0 ≤ i64At rocks i)
    (hrocks_le : ∀ i, i < n → i64At rocks i ≤ i64At capacity i)
    (hadditional : 0 ≤ additionalRocks.val)
    (r : I64) (hres : maximum_bags capacity rocks additionalRocks = ok r), r.val = 0 ↔ ∀ i, i < n → additionalRocks.val < deficit capacity rocks i) := by
  sorry

/-- Whenever maximum_bags(capacity, rocks, additionalRocks) returns a result r, r >= |{i | 0 <= i < n and rocks[i] = capacity[i]}|.
  Preconditions: Let n = len(capacity). Assume len(capacity) = len(rocks) = n, 1 <= n <= 50000, and for every i with 0 <= i < n, 1 <= capacity[i] <= 1000000000 and 0 <= rocks[i] <= capacity[i]. Also assume additionalRocks >= 0. -/
theorem spec_8
    (capacity rocks : Slice I64) (additionalRocks : I64) (n : ℕ)
    (hcap_len : capacity.val.length = n)
    (hrocks_len : rocks.val.length = n)
    (hn_pos : 1 ≤ n) (hn_bound : n ≤ 50000)
    (hcap_pos : ∀ i, i < n → 1 ≤ i64At capacity i)
    (hcap_le : ∀ i, i < n → i64At capacity i ≤ 1000000000)
    (hrocks_nonneg : ∀ i, i < n → 0 ≤ i64At rocks i)
    (hrocks_le : ∀ i, i < n → i64At rocks i ≤ i64At capacity i)
    (hadditional : 0 ≤ additionalRocks.val)
    (r : I64) (hres : maximum_bags capacity rocks additionalRocks = ok r) :
    ((fullIndices capacity rocks n).card : ℤ) ≤ r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (capacity rocks : Slice I64) (additionalRocks : I64) (n : ℕ)
    (hcap_len : capacity.val.length = n)
    (hrocks_len : rocks.val.length = n)
    (hn_pos : 1 ≤ n) (hn_bound : n ≤ 50000)
    (hcap_pos : ∀ i, i < n → 1 ≤ i64At capacity i)
    (hcap_le : ∀ i, i < n → i64At capacity i ≤ 1000000000)
    (hrocks_nonneg : ∀ i, i < n → 0 ≤ i64At rocks i)
    (hrocks_le : ∀ i, i < n → i64At rocks i ≤ i64At capacity i)
    (hadditional : 0 ≤ additionalRocks.val)
    (r : I64) (hres : maximum_bags capacity rocks additionalRocks = ok r), ((fullIndices capacity rocks n).card : ℤ) ≤ r.val) := by
  sorry

/-- Whenever maximum_bags(capacity, rocks, additionalRocks) returns a result r, r <= |{i | 0 <= i < n and capacity[i] - rocks[i] <= additionalRocks}|.
  Preconditions: Let n = len(capacity). Assume len(capacity) = len(rocks) = n, 1 <= n <= 50000, and for every i with 0 <= i < n, 1 <= capacity[i] <= 1000000000 and 0 <= rocks[i] <= capacity[i]. Also assume additionalRocks >= 0. -/
theorem spec_9
    (capacity rocks : Slice I64) (additionalRocks : I64) (n : ℕ)
    (hcap_len : capacity.val.length = n)
    (hrocks_len : rocks.val.length = n)
    (hn_pos : 1 ≤ n) (hn_bound : n ≤ 50000)
    (hcap_pos : ∀ i, i < n → 1 ≤ i64At capacity i)
    (hcap_le : ∀ i, i < n → i64At capacity i ≤ 1000000000)
    (hrocks_nonneg : ∀ i, i < n → 0 ≤ i64At rocks i)
    (hrocks_le : ∀ i, i < n → i64At rocks i ≤ i64At capacity i)
    (hadditional : 0 ≤ additionalRocks.val)
    (r : I64) (hres : maximum_bags capacity rocks additionalRocks = ok r) :
    r.val ≤ ((affordableIndices capacity rocks n additionalRocks).card : ℤ) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (capacity rocks : Slice I64) (additionalRocks : I64) (n : ℕ)
    (hcap_len : capacity.val.length = n)
    (hrocks_len : rocks.val.length = n)
    (hn_pos : 1 ≤ n) (hn_bound : n ≤ 50000)
    (hcap_pos : ∀ i, i < n → 1 ≤ i64At capacity i)
    (hcap_le : ∀ i, i < n → i64At capacity i ≤ 1000000000)
    (hrocks_nonneg : ∀ i, i < n → 0 ≤ i64At rocks i)
    (hrocks_le : ∀ i, i < n → i64At rocks i ≤ i64At capacity i)
    (hadditional : 0 ≤ additionalRocks.val)
    (r : I64) (hres : maximum_bags capacity rocks additionalRocks = ok r), r.val ≤ ((affordableIndices capacity rocks n additionalRocks).card : ℤ)) := by
  sorry

/-- If maximum_bags(capacity, rocks, x) returns a result r_x and maximum_bags(capacity, rocks, y) returns a result r_y, then r_x <= r_y.
  Preconditions: Let n = len(capacity). Assume len(capacity) = len(rocks) = n, 1 <= n <= 50000, and for every i with 0 <= i < n, 1 <= capacity[i] <= 1000000000 and 0 <= rocks[i] <= capacity[i]. For every pair of integers x, y with 0 <= x <= y, both represented as i64, consider the two calls maximum_bags(capacity, rocks, x) and maximum_bags(capacity, rocks, y). -/
theorem spec_10
    (capacity rocks : Slice I64) (n : ℕ)
    (hcap_len : capacity.val.length = n)
    (hrocks_len : rocks.val.length = n)
    (hn_pos : 1 ≤ n) (hn_bound : n ≤ 50000)
    (hcap_pos : ∀ i, i < n → 1 ≤ i64At capacity i)
    (hcap_le : ∀ i, i < n → i64At capacity i ≤ 1000000000)
    (hrocks_nonneg : ∀ i, i < n → 0 ≤ i64At rocks i)
    (hrocks_le : ∀ i, i < n → i64At rocks i ≤ i64At capacity i)
    (x y : I64) (hx : 0 ≤ x.val) (hxy : x.val ≤ y.val)
    (rx ry : I64)
    (hres_x : maximum_bags capacity rocks x = ok rx)
    (hres_y : maximum_bags capacity rocks y = ok ry) :
    rx.val ≤ ry.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (capacity rocks : Slice I64) (n : ℕ)
    (hcap_len : capacity.val.length = n)
    (hrocks_len : rocks.val.length = n)
    (hn_pos : 1 ≤ n) (hn_bound : n ≤ 50000)
    (hcap_pos : ∀ i, i < n → 1 ≤ i64At capacity i)
    (hcap_le : ∀ i, i < n → i64At capacity i ≤ 1000000000)
    (hrocks_nonneg : ∀ i, i < n → 0 ≤ i64At rocks i)
    (hrocks_le : ∀ i, i < n → i64At rocks i ≤ i64At capacity i)
    (x y : I64) (hx : 0 ≤ x.val) (hxy : x.val ≤ y.val)
    (rx ry : I64)
    (hres_x : maximum_bags capacity rocks x = ok rx)
    (hres_y : maximum_bags capacity rocks y = ok ry), rx.val ≤ ry.val) := by
  sorry

/-- If maximum_bags(capacity, rocks1, A) returns a result r1 and maximum_bags(capacity, rocks2, A) returns a result r2, then r1 <= r2.
  Preconditions: Let n = len(capacity). Assume 1 <= n <= 50000 and for every i with 0 <= i < n, 1 <= capacity[i] <= 1000000000. Let rocks1 and rocks2 be slices of length n such that for every i with 0 <= i < n, 0 <= rocks1[i] <= rocks2[i] <= capacity[i]. Let A be an integer with A >= 0. -/
theorem spec_11
    (capacity rocks1 rocks2 : Slice I64) (n : ℕ) (A : I64)
    (hcap_len : capacity.val.length = n)
    (hrocks1_len : rocks1.val.length = n)
    (hrocks2_len : rocks2.val.length = n)
    (hn_pos : 1 ≤ n) (hn_bound : n ≤ 50000)
    (hcap_pos : ∀ i, i < n → 1 ≤ i64At capacity i)
    (hcap_le : ∀ i, i < n → i64At capacity i ≤ 1000000000)
    (hrocks1_nonneg : ∀ i, i < n → 0 ≤ i64At rocks1 i)
    (hrocks12 : ∀ i, i < n → i64At rocks1 i ≤ i64At rocks2 i)
    (hrocks2_cap : ∀ i, i < n → i64At rocks2 i ≤ i64At capacity i)
    (hA : 0 ≤ A.val)
    (r1 r2 : I64)
    (hres1 : maximum_bags capacity rocks1 A = ok r1)
    (hres2 : maximum_bags capacity rocks2 A = ok r2) :
    r1.val ≤ r2.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (capacity rocks1 rocks2 : Slice I64) (n : ℕ) (A : I64)
    (hcap_len : capacity.val.length = n)
    (hrocks1_len : rocks1.val.length = n)
    (hrocks2_len : rocks2.val.length = n)
    (hn_pos : 1 ≤ n) (hn_bound : n ≤ 50000)
    (hcap_pos : ∀ i, i < n → 1 ≤ i64At capacity i)
    (hcap_le : ∀ i, i < n → i64At capacity i ≤ 1000000000)
    (hrocks1_nonneg : ∀ i, i < n → 0 ≤ i64At rocks1 i)
    (hrocks12 : ∀ i, i < n → i64At rocks1 i ≤ i64At rocks2 i)
    (hrocks2_cap : ∀ i, i < n → i64At rocks2 i ≤ i64At capacity i)
    (hA : 0 ≤ A.val)
    (r1 r2 : I64)
    (hres1 : maximum_bags capacity rocks1 A = ok r1)
    (hres2 : maximum_bags capacity rocks2 A = ok r2), r1.val ≤ r2.val) := by
  sorry

/-- If maximum_bags(capacity, rocks, additionalRocks) returns a result r and maximum_bags(capacity', rocks', additionalRocks) returns a result r', then r = r'.
  Preconditions: Let n = len(capacity). Assume len(capacity) = len(rocks) = n, 1 <= n <= 50000, and for every i with 0 <= i < n, 1 <= capacity[i] <= 1000000000 and 0 <= rocks[i] <= capacity[i]. Also assume additionalRocks >= 0. Let pi be any bijection from {0,1,...,n-1} to itself. Define capacity' and rocks' of length n by capacity'[i] = capacity[pi(i)] and rocks'[i] = rocks[pi(i)] for every i with 0 <= i < n. -/
theorem spec_12
    (capacity rocks capacity' rocks' : Slice I64) (additionalRocks : I64) (n : ℕ)
    (π : Equiv.Perm (Fin n))
    (hcap_len : capacity.val.length = n)
    (hrocks_len : rocks.val.length = n)
    (hcap'_len : capacity'.val.length = n)
    (hrocks'_len : rocks'.val.length = n)
    (hn_pos : 1 ≤ n) (hn_bound : n ≤ 50000)
    (hcap_pos : ∀ i, i < n → 1 ≤ i64At capacity i)
    (hcap_le : ∀ i, i < n → i64At capacity i ≤ 1000000000)
    (hrocks_nonneg : ∀ i, i < n → 0 ≤ i64At rocks i)
    (hrocks_le : ∀ i, i < n → i64At rocks i ≤ i64At capacity i)
    (hcap'_perm : ∀ i : Fin n, i64At capacity' i.val = i64At capacity (π i).val)
    (hrocks'_perm : ∀ i : Fin n, i64At rocks' i.val = i64At rocks (π i).val)
    (hadditional : 0 ≤ additionalRocks.val)
    (r r' : I64)
    (hres : maximum_bags capacity rocks additionalRocks = ok r)
    (hres' : maximum_bags capacity' rocks' additionalRocks = ok r') :
    r = r' := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (capacity rocks capacity' rocks' : Slice I64) (additionalRocks : I64) (n : ℕ)
    (π : Equiv.Perm (Fin n))
    (hcap_len : capacity.val.length = n)
    (hrocks_len : rocks.val.length = n)
    (hcap'_len : capacity'.val.length = n)
    (hrocks'_len : rocks'.val.length = n)
    (hn_pos : 1 ≤ n) (hn_bound : n ≤ 50000)
    (hcap_pos : ∀ i, i < n → 1 ≤ i64At capacity i)
    (hcap_le : ∀ i, i < n → i64At capacity i ≤ 1000000000)
    (hrocks_nonneg : ∀ i, i < n → 0 ≤ i64At rocks i)
    (hrocks_le : ∀ i, i < n → i64At rocks i ≤ i64At capacity i)
    (hcap'_perm : ∀ i : Fin n, i64At capacity' i.val = i64At capacity (π i).val)
    (hrocks'_perm : ∀ i : Fin n, i64At rocks' i.val = i64At rocks (π i).val)
    (hadditional : 0 ≤ additionalRocks.val)
    (r r' : I64)
    (hres : maximum_bags capacity rocks additionalRocks = ok r)
    (hres' : maximum_bags capacity' rocks' additionalRocks = ok r'), r = r') := by
  sorry

/-- If maximum_bags(capacity, rocks, additionalRocks) returns a result r and maximum_bags(capacity', rocks', additionalRocks) returns a result r', then r = r' + 1.
  Preconditions: Let n = len(capacity) with n >= 2. Assume len(capacity) = len(rocks) = n, 1 <= n <= 50000, and for every i with 0 <= i < n, 1 <= capacity[i] <= 1000000000 and 0 <= rocks[i] <= capacity[i]. Also assume additionalRocks >= 0. Suppose i is an index with 0 <= i < n and rocks[i] = capacity[i]. Let capacity' and rocks' be the slices of length n-1 obtained by deleting position i from capacity and rocks respectively. -/
theorem spec_13
    (capacity rocks capacity' rocks' : Slice I64) (additionalRocks : I64) (n : ℕ)
    (hcap_len : capacity.val.length = n)
    (hrocks_len : rocks.val.length = n)
    (hn_pos : 1 ≤ n) (hn_bound : n ≤ 50000) (hn_two : 2 ≤ n)
    (hcap_pos : ∀ i, i < n → 1 ≤ i64At capacity i)
    (hcap_le : ∀ i, i < n → i64At capacity i ≤ 1000000000)
    (hrocks_nonneg : ∀ i, i < n → 0 ≤ i64At rocks i)
    (hrocks_le : ∀ i, i < n → i64At rocks i ≤ i64At capacity i)
    (hadditional : 0 ≤ additionalRocks.val)
    (i : ℕ) (hi : i < n) (hfull : i64At rocks i = i64At capacity i)
    (hcap'_val : capacity'.val = capacity.val.eraseIdx i)
    (hrocks'_val : rocks'.val = rocks.val.eraseIdx i)
    (hcap'_len : capacity'.val.length = n - 1)
    (hrocks'_len : rocks'.val.length = n - 1)
    (r r' : I64)
    (hres : maximum_bags capacity rocks additionalRocks = ok r)
    (hres' : maximum_bags capacity' rocks' additionalRocks = ok r') :
    r.val = r'.val + 1 := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (capacity rocks capacity' rocks' : Slice I64) (additionalRocks : I64) (n : ℕ)
    (hcap_len : capacity.val.length = n)
    (hrocks_len : rocks.val.length = n)
    (hn_pos : 1 ≤ n) (hn_bound : n ≤ 50000) (hn_two : 2 ≤ n)
    (hcap_pos : ∀ i, i < n → 1 ≤ i64At capacity i)
    (hcap_le : ∀ i, i < n → i64At capacity i ≤ 1000000000)
    (hrocks_nonneg : ∀ i, i < n → 0 ≤ i64At rocks i)
    (hrocks_le : ∀ i, i < n → i64At rocks i ≤ i64At capacity i)
    (hadditional : 0 ≤ additionalRocks.val)
    (i : ℕ) (hi : i < n) (hfull : i64At rocks i = i64At capacity i)
    (hcap'_val : capacity'.val = capacity.val.eraseIdx i)
    (hrocks'_val : rocks'.val = rocks.val.eraseIdx i)
    (hcap'_len : capacity'.val.length = n - 1)
    (hrocks'_len : rocks'.val.length = n - 1)
    (r r' : I64)
    (hres : maximum_bags capacity rocks additionalRocks = ok r)
    (hres' : maximum_bags capacity' rocks' additionalRocks = ok r'), r.val = r'.val + 1) := by
  sorry

end AegisSpec.MaximumBags
