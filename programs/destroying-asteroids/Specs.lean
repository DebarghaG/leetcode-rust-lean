import Aegis.AsteroidsDestroyed.Code.Funs

/-!
# Specifications of `Aegis.AsteroidsDestroyed.asteroids_destroyed`

LeetCode problem `destroying-asteroids`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.AsteroidsDestroyed

namespace AegisSpec.AsteroidsDestroyed

def astList (asteroids : Slice Std.I64) : List ℤ :=
  asteroids.val.map (fun x => x.val)

def listAt (b : List ℤ) (i : ℕ) : ℤ := b.getD i 0

def astAt (asteroids : Slice Std.I64) (i : ℕ) : ℤ := listAt (astList asteroids) i

def prefixSum (b : List ℤ) (k : ℕ) : ℤ := (b.take k).sum

def permPrefixSum (asteroids : Slice Std.I64) (π : ℕ → ℕ) (k : ℕ) : ℤ :=
  ((List.range k).map (fun j => astAt asteroids (π j))).sum

def listMax (b : List ℤ) : ℤ := b.foldr max 0

def IsPerm (n : ℕ) (σ : ℕ → ℕ) : Prop :=
  (∀ i, i < n → σ i < n) ∧ (∀ j, j < n → ∃ i, i < n ∧ σ i = j)

def IsNondescRearrangement (asteroids : Slice Std.I64) (b : List ℤ) : Prop :=
  b.length = (astList asteroids).length ∧ b.Pairwise (· ≤ ·) ∧
    List.Perm b (astList asteroids)

def DestroysInOrder (mass : Std.I64) (asteroids : Slice Std.I64) (n : ℕ)
    (π : ℕ → ℕ) : Prop :=
  IsPerm n π ∧ ∀ k, k < n → mass.val + permPrefixSum asteroids π k ≥ astAt asteroids (π k)

/-- The function returns a result r, and r = true if and only if there exists a permutation π of the indices {0, 1, ..., n-1} such that for every k with 0 <= k < n, mass + (sum over j with 0 <= j < k of asteroids[π(j)]) >= asteroids[π(k)], where the sum for k = 0 is 0.
  Preconditions: Let n = len(asteroids). Assume 1 <= mass <= 100000, 1 <= n <= 100000, and 1 <= asteroids[i] <= 100000 for every i with 0 <= i < n. -/
theorem spec_1 (mass : Std.I64) (asteroids : Slice Std.I64) (n : ℕ)
    (hn : n = (astList asteroids).length)
    (hmass_lo : 1 ≤ mass.val) (hmass_hi : mass.val ≤ 100000)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hast : ∀ i, i < n → 1 ≤ astAt asteroids i ∧ astAt asteroids i ≤ 100000) :
    ∃ r, asteroids_destroyed mass asteroids = ok r ∧
      (r = true ↔ ∃ π : ℕ → ℕ, DestroysInOrder mass asteroids n π) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (mass : Std.I64) (asteroids : Slice Std.I64) (n : ℕ)
    (hn : n = (astList asteroids).length)
    (hmass_lo : 1 ≤ mass.val) (hmass_hi : mass.val ≤ 100000)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hast : ∀ i, i < n → 1 ≤ astAt asteroids i ∧ astAt asteroids i ≤ 100000), ∃ r, asteroids_destroyed mass asteroids = ok r ∧
      (r = true ↔ ∃ π : ℕ → ℕ, DestroysInOrder mass asteroids n π)) := by
  sorry

/-- The function returns a result r; in particular, it does not fail, panic, overflow, or access an index outside the slice on these inputs.
  Preconditions: Let n = len(asteroids). Assume 1 <= mass <= 100000, 1 <= n <= 100000, and 1 <= asteroids[i] <= 100000 for every i with 0 <= i < n. -/
theorem spec_2 (mass : Std.I64) (asteroids : Slice Std.I64) (n : ℕ)
    (hn : n = (astList asteroids).length)
    (hmass_lo : 1 ≤ mass.val) (hmass_hi : mass.val ≤ 100000)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hast : ∀ i, i < n → 1 ≤ astAt asteroids i ∧ astAt asteroids i ≤ 100000) :
    ∃ r, asteroids_destroyed mass asteroids = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (mass : Std.I64) (asteroids : Slice Std.I64) (n : ℕ)
    (hn : n = (astList asteroids).length)
    (hmass_lo : 1 ≤ mass.val) (hmass_hi : mass.val ≤ 100000)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hast : ∀ i, i < n → 1 ≤ astAt asteroids i ∧ astAt asteroids i ≤ 100000), ∃ r, asteroids_destroyed mass asteroids = ok r) := by
  sorry

/-- Whenever the function returns r with r = true, for every index i with 0 <= i < n and asteroids[i] <= mass there exists a permutation π of {0, 1, ..., n-1} such that π(0) = i and, for every k with 0 <= k < n, mass + (sum over j with 0 <= j < k of asteroids[π(j)]) >= asteroids[π(k)].
  Preconditions: Let n = len(asteroids). Assume 1 <= mass <= 100000, 1 <= n <= 100000, and 1 <= asteroids[i] <= 100000 for every i with 0 <= i < n. -/
theorem spec_3 (mass : Std.I64) (asteroids : Slice Std.I64) (n : ℕ)
    (hn : n = (astList asteroids).length)
    (hmass_lo : 1 ≤ mass.val) (hmass_hi : mass.val ≤ 100000)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hast : ∀ i, i < n → 1 ≤ astAt asteroids i ∧ astAt asteroids i ≤ 100000) :
    ∀ r, asteroids_destroyed mass asteroids = ok r → r = true →
      ∀ i, i < n → astAt asteroids i ≤ mass.val →
        ∃ π : ℕ → ℕ, IsPerm n π ∧ π 0 = i ∧
          ∀ k, k < n →
            mass.val + permPrefixSum asteroids π k ≥ astAt asteroids (π k) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (mass : Std.I64) (asteroids : Slice Std.I64) (n : ℕ)
    (hn : n = (astList asteroids).length)
    (hmass_lo : 1 ≤ mass.val) (hmass_hi : mass.val ≤ 100000)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hast : ∀ i, i < n → 1 ≤ astAt asteroids i ∧ astAt asteroids i ≤ 100000), ∀ r, asteroids_destroyed mass asteroids = ok r → r = true →
      ∀ i, i < n → astAt asteroids i ≤ mass.val →
        ∃ π : ℕ → ℕ, IsPerm n π ∧ π 0 = i ∧
          ∀ k, k < n →
            mass.val + permPrefixSum asteroids π k ≥ astAt asteroids (π k)) := by
  sorry

/-- Whenever the function returns r with r = true, if b is a nondecreasing rearrangement of asteroids (so b[0] <= b[1] <= ... <= b[n-1]), then for every k with 0 <= k < n, mass + (sum over j with 0 <= j < k of b[j]) >= b[k].
  Preconditions: Let n = len(asteroids). Assume 1 <= mass <= 100000, 1 <= n <= 100000, and 1 <= asteroids[i] <= 100000 for every i with 0 <= i < n. -/
theorem spec_4 (mass : Std.I64) (asteroids : Slice Std.I64) (n : ℕ)
    (hn : n = (astList asteroids).length)
    (hmass_lo : 1 ≤ mass.val) (hmass_hi : mass.val ≤ 100000)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hast : ∀ i, i < n → 1 ≤ astAt asteroids i ∧ astAt asteroids i ≤ 100000) :
    ∀ r, asteroids_destroyed mass asteroids = ok r → r = true →
      ∀ b : List ℤ, IsNondescRearrangement asteroids b →
        ∀ k, k < n → mass.val + prefixSum b k ≥ listAt b k := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (mass : Std.I64) (asteroids : Slice Std.I64) (n : ℕ)
    (hn : n = (astList asteroids).length)
    (hmass_lo : 1 ≤ mass.val) (hmass_hi : mass.val ≤ 100000)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hast : ∀ i, i < n → 1 ≤ astAt asteroids i ∧ astAt asteroids i ≤ 100000), ∀ r, asteroids_destroyed mass asteroids = ok r → r = true →
      ∀ b : List ℤ, IsNondescRearrangement asteroids b →
        ∀ k, k < n → mass.val + prefixSum b k ≥ listAt b k) := by
  sorry

/-- Whenever the function returns r, if mass < asteroids[i] for every i with 0 <= i < n, then r = false.
  Preconditions: Let n = len(asteroids). Assume 1 <= mass <= 100000, 1 <= n <= 100000, and 1 <= asteroids[i] <= 100000 for every i with 0 <= i < n. -/
theorem spec_5 (mass : Std.I64) (asteroids : Slice Std.I64) (n : ℕ)
    (hn : n = (astList asteroids).length)
    (hmass_lo : 1 ≤ mass.val) (hmass_hi : mass.val ≤ 100000)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hast : ∀ i, i < n → 1 ≤ astAt asteroids i ∧ astAt asteroids i ≤ 100000) :
    ∀ r, asteroids_destroyed mass asteroids = ok r →
      (∀ i, i < n → mass.val < astAt asteroids i) → r = false := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (mass : Std.I64) (asteroids : Slice Std.I64) (n : ℕ)
    (hn : n = (astList asteroids).length)
    (hmass_lo : 1 ≤ mass.val) (hmass_hi : mass.val ≤ 100000)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hast : ∀ i, i < n → 1 ≤ astAt asteroids i ∧ astAt asteroids i ≤ 100000), ∀ r, asteroids_destroyed mass asteroids = ok r →
      (∀ i, i < n → mass.val < astAt asteroids i) → r = false) := by
  sorry

/-- Whenever the function returns r with r = true, if M = max_{0 <= i < n} asteroids[i] and S = sum_{i=0}^{n-1} asteroids[i], then mass + (S - M) >= M.
  Preconditions: Let n = len(asteroids). Assume 1 <= mass <= 100000, 1 <= n <= 100000, and 1 <= asteroids[i] <= 100000 for every i with 0 <= i < n. -/
theorem spec_6 (mass : Std.I64) (asteroids : Slice Std.I64) (n : ℕ)
    (hn : n = (astList asteroids).length)
    (hmass_lo : 1 ≤ mass.val) (hmass_hi : mass.val ≤ 100000)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hast : ∀ i, i < n → 1 ≤ astAt asteroids i ∧ astAt asteroids i ≤ 100000) :
    ∀ r, asteroids_destroyed mass asteroids = ok r → r = true →
      mass.val + ((astList asteroids).sum - listMax (astList asteroids)) ≥
        listMax (astList asteroids) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (mass : Std.I64) (asteroids : Slice Std.I64) (n : ℕ)
    (hn : n = (astList asteroids).length)
    (hmass_lo : 1 ≤ mass.val) (hmass_hi : mass.val ≤ 100000)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hast : ∀ i, i < n → 1 ≤ astAt asteroids i ∧ astAt asteroids i ≤ 100000), ∀ r, asteroids_destroyed mass asteroids = ok r → r = true →
      mass.val + ((astList asteroids).sum - listMax (astList asteroids)) ≥
        listMax (astList asteroids)) := by
  sorry

/-- Whenever the function returns r, if mass >= asteroids[i] for every i with 0 <= i < n, then r = true.
  Preconditions: Let n = len(asteroids). Assume 1 <= mass <= 100000, 1 <= n <= 100000, and 1 <= asteroids[i] <= 100000 for every i with 0 <= i < n. -/
theorem spec_7 (mass : Std.I64) (asteroids : Slice Std.I64) (n : ℕ)
    (hn : n = (astList asteroids).length)
    (hmass_lo : 1 ≤ mass.val) (hmass_hi : mass.val ≤ 100000)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hast : ∀ i, i < n → 1 ≤ astAt asteroids i ∧ astAt asteroids i ≤ 100000) :
    ∀ r, asteroids_destroyed mass asteroids = ok r →
      (∀ i, i < n → astAt asteroids i ≤ mass.val) → r = true := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (mass : Std.I64) (asteroids : Slice Std.I64) (n : ℕ)
    (hn : n = (astList asteroids).length)
    (hmass_lo : 1 ≤ mass.val) (hmass_hi : mass.val ≤ 100000)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hast : ∀ i, i < n → 1 ≤ astAt asteroids i ∧ astAt asteroids i ≤ 100000), ∀ r, asteroids_destroyed mass asteroids = ok r →
      (∀ i, i < n → astAt asteroids i ≤ mass.val) → r = true) := by
  sorry

/-- Whenever the call with initial mass mass returns r and the call with initial mass mass' on the same asteroids returns r', if r = true then r' = true.
  Preconditions: Let n = len(asteroids). Assume 1 <= mass <= mass' <= 100000, 1 <= n <= 100000, and 1 <= asteroids[i] <= 100000 for every i with 0 <= i < n. -/
theorem spec_8 (mass mass' : Std.I64) (asteroids : Slice Std.I64) (n : ℕ)
    (hn : n = (astList asteroids).length)
    (hmass_lo : 1 ≤ mass.val) (hle : mass.val ≤ mass'.val) (hmass'_hi : mass'.val ≤ 100000)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hast : ∀ i, i < n → 1 ≤ astAt asteroids i ∧ astAt asteroids i ≤ 100000) :
    ∀ r r', asteroids_destroyed mass asteroids = ok r →
      asteroids_destroyed mass' asteroids = ok r' → r = true → r' = true := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (mass mass' : Std.I64) (asteroids : Slice Std.I64) (n : ℕ)
    (hn : n = (astList asteroids).length)
    (hmass_lo : 1 ≤ mass.val) (hle : mass.val ≤ mass'.val) (hmass'_hi : mass'.val ≤ 100000)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hast : ∀ i, i < n → 1 ≤ astAt asteroids i ∧ astAt asteroids i ≤ 100000), ∀ r r', asteroids_destroyed mass asteroids = ok r →
      asteroids_destroyed mass' asteroids = ok r' → r = true → r' = true) := by
  sorry

/-- Let asteroids' be the slice of length n with asteroids'[i] = asteroids[σ(i)] for every i with 0 <= i < n. Whenever the function returns r on (mass, asteroids) and r' on (mass, asteroids'), r = r'.
  Preconditions: Let n = len(asteroids). Assume 1 <= mass <= 100000, 1 <= n <= 100000, 1 <= asteroids[i] <= 100000 for every i with 0 <= i < n, and σ is a permutation of {0, 1, ..., n-1}. -/
theorem spec_9 (mass : Std.I64) (asteroids asteroids' : Slice Std.I64) (n : ℕ)
    (hn : n = (astList asteroids).length)
    (hmass_lo : 1 ≤ mass.val) (hmass_hi : mass.val ≤ 100000)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hast : ∀ i, i < n → 1 ≤ astAt asteroids i ∧ astAt asteroids i ≤ 100000)
    (σ : ℕ → ℕ) (hσ : IsPerm n σ)
    (hlen' : (astList asteroids').length = n)
    (hpt : ∀ i, i < n → astAt asteroids' i = astAt asteroids (σ i)) :
    ∀ r r', asteroids_destroyed mass asteroids = ok r →
      asteroids_destroyed mass asteroids' = ok r' → r = r' := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (mass : Std.I64) (asteroids asteroids' : Slice Std.I64) (n : ℕ)
    (hn : n = (astList asteroids).length)
    (hmass_lo : 1 ≤ mass.val) (hmass_hi : mass.val ≤ 100000)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hast : ∀ i, i < n → 1 ≤ astAt asteroids i ∧ astAt asteroids i ≤ 100000)
    (σ : ℕ → ℕ) (hσ : IsPerm n σ)
    (hlen' : (astList asteroids').length = n)
    (hpt : ∀ i, i < n → astAt asteroids' i = astAt asteroids (σ i)), ∀ r r', asteroids_destroyed mass asteroids = ok r →
      asteroids_destroyed mass asteroids' = ok r' → r = r') := by
  sorry

/-- Let A' be the slice of length n with A'[i] = c * A[i] for every i with 0 <= i < n. Whenever the call on (mass, A) returns r and the call on (c * mass, A') returns r', r = r'.
  Preconditions: Let n = len(A). Assume 1 <= mass <= 100000, 1 <= n <= 100000, 1 <= A[i] <= 100000 for every i with 0 <= i < n, and c is an integer with c >= 1, c * mass <= 100000, and c * A[i] <= 100000 for every i with 0 <= i < n. -/
theorem spec_10 (mass mass' : Std.I64) (c : ℤ) (A A' : Slice Std.I64) (n : ℕ)
    (hn : n = (astList A).length)
    (hmass_lo : 1 ≤ mass.val) (hmass_hi : mass.val ≤ 100000)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hA : ∀ i, i < n → 1 ≤ astAt A i ∧ astAt A i ≤ 100000)
    (hc : 1 ≤ c) (hcmass : c * mass.val ≤ 100000)
    (hcA : ∀ i, i < n → c * astAt A i ≤ 100000)
    (hmass' : mass'.val = c * mass.val)
    (hA' : ∀ i, i < n → astAt A' i = c * astAt A i) :
    ∀ r r', asteroids_destroyed mass A = ok r →
      asteroids_destroyed mass' A' = ok r' → r = r' := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (mass mass' : Std.I64) (c : ℤ) (A A' : Slice Std.I64) (n : ℕ)
    (hn : n = (astList A).length)
    (hmass_lo : 1 ≤ mass.val) (hmass_hi : mass.val ≤ 100000)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hA : ∀ i, i < n → 1 ≤ astAt A i ∧ astAt A i ≤ 100000)
    (hc : 1 ≤ c) (hcmass : c * mass.val ≤ 100000)
    (hcA : ∀ i, i < n → c * astAt A i ≤ 100000)
    (hmass' : mass'.val = c * mass.val)
    (hA' : ∀ i, i < n → astAt A' i = c * astAt A i), ∀ r r', asteroids_destroyed mass A = ok r →
      asteroids_destroyed mass' A' = ok r' → r = r') := by
  sorry

/-- The function returns a result r, and r = true if and only if mass >= asteroids[0].
  Preconditions: Assume 1 <= mass <= 100000, len(asteroids) = 1, and 1 <= asteroids[0] <= 100000. -/
theorem spec_11 (mass : Std.I64) (asteroids : Slice Std.I64)
    (hmass_lo : 1 ≤ mass.val) (hmass_hi : mass.val ≤ 100000)
    (hlen : (astList asteroids).length = 1)
    (hast : 1 ≤ astAt asteroids 0 ∧ astAt asteroids 0 ≤ 100000) :
    ∃ r, asteroids_destroyed mass asteroids = ok r ∧
      (r = true ↔ mass.val ≥ astAt asteroids 0) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (mass : Std.I64) (asteroids : Slice Std.I64)
    (hmass_lo : 1 ≤ mass.val) (hmass_hi : mass.val ≤ 100000)
    (hlen : (astList asteroids).length = 1)
    (hast : 1 ≤ astAt asteroids 0 ∧ astAt asteroids 0 ≤ 100000), ∃ r, asteroids_destroyed mass asteroids = ok r ∧
      (r = true ↔ mass.val ≥ astAt asteroids 0)) := by
  sorry

/-- The function returns a result r, and r = true if and only if mass >= a.
  Preconditions: Let n = len(asteroids). Assume 1 <= mass <= 100000, 1 <= n <= 100000, and there exists an integer a with 1 <= a <= 100000 such that asteroids[i] = a for every i with 0 <= i < n. -/
theorem spec_12 (mass : Std.I64) (asteroids : Slice Std.I64) (n : ℕ) (a : ℤ)
    (hn : n = (astList asteroids).length)
    (hmass_lo : 1 ≤ mass.val) (hmass_hi : mass.val ≤ 100000)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (ha_lo : 1 ≤ a) (ha_hi : a ≤ 100000)
    (hall : ∀ i, i < n → astAt asteroids i = a) :
    ∃ r, asteroids_destroyed mass asteroids = ok r ∧ (r = true ↔ mass.val ≥ a) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (mass : Std.I64) (asteroids : Slice Std.I64) (n : ℕ) (a : ℤ)
    (hn : n = (astList asteroids).length)
    (hmass_lo : 1 ≤ mass.val) (hmass_hi : mass.val ≤ 100000)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (ha_lo : 1 ≤ a) (ha_hi : a ≤ 100000)
    (hall : ∀ i, i < n → astAt asteroids i = a), ∃ r, asteroids_destroyed mass asteroids = ok r ∧ (r = true ↔ mass.val ≥ a)) := by
  sorry

/-- The function returns a result r, and r = true if and only if either (mass >= asteroids[0] and mass + asteroids[0] >= asteroids[1]) or (mass >= asteroids[1] and mass + asteroids[1] >= asteroids[0]).
  Preconditions: Assume 1 <= mass <= 100000, len(asteroids) = 2, and 1 <= asteroids[0] <= 100000 and 1 <= asteroids[1] <= 100000. -/
theorem spec_13 (mass : Std.I64) (asteroids : Slice Std.I64)
    (hmass_lo : 1 ≤ mass.val) (hmass_hi : mass.val ≤ 100000)
    (hlen : (astList asteroids).length = 2)
    (hast : 1 ≤ astAt asteroids 0 ∧ astAt asteroids 0 ≤ 100000)
    (hast1 : 1 ≤ astAt asteroids 1 ∧ astAt asteroids 1 ≤ 100000) :
    ∃ r, asteroids_destroyed mass asteroids = ok r ∧
      (r = true ↔
        (mass.val ≥ astAt asteroids 0 ∧
            mass.val + astAt asteroids 0 ≥ astAt asteroids 1) ∨
          (mass.val ≥ astAt asteroids 1 ∧
            mass.val + astAt asteroids 1 ≥ astAt asteroids 0)) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (mass : Std.I64) (asteroids : Slice Std.I64)
    (hmass_lo : 1 ≤ mass.val) (hmass_hi : mass.val ≤ 100000)
    (hlen : (astList asteroids).length = 2)
    (hast : 1 ≤ astAt asteroids 0 ∧ astAt asteroids 0 ≤ 100000)
    (hast1 : 1 ≤ astAt asteroids 1 ∧ astAt asteroids 1 ≤ 100000), ∃ r, asteroids_destroyed mass asteroids = ok r ∧
      (r = true ↔
        (mass.val ≥ astAt asteroids 0 ∧
            mass.val + astAt asteroids 0 ≥ astAt asteroids 1) ∨
          (mass.val ≥ astAt asteroids 1 ∧
            mass.val + astAt asteroids 1 ≥ astAt asteroids 0))) := by
  sorry

/-- Let A' be the slice of length n-1 defined by A'[j] = asteroids[j] for 0 <= j < i and A'[j] = asteroids[j+1] for i <= j < n-1. Whenever the call on (mass, asteroids) returns r and the call on (mass + asteroids[i], A') returns r', r = r'.
  Preconditions: Let n = len(asteroids). Assume 1 <= mass <= 100000, 2 <= n <= 100000, and 1 <= asteroids[i] <= 100000 for every i with 0 <= i < n. Let i be an index with 0 <= i < n, asteroids[i] <= mass, and mass + asteroids[i] <= 100000. -/
theorem spec_14 (mass mass' : Std.I64) (asteroids A' : Slice Std.I64) (n i : ℕ)
    (hn : n = (astList asteroids).length)
    (hmass_lo : 1 ≤ mass.val) (hmass_hi : mass.val ≤ 100000)
    (hn_lo : 2 ≤ n) (hn_hi : n ≤ 100000)
    (hast : ∀ j, j < n → 1 ≤ astAt asteroids j ∧ astAt asteroids j ≤ 100000)
    (hi : i < n) (hind : astAt asteroids i ≤ mass.val)
    (hnosum : mass.val + astAt asteroids i ≤ 100000)
    (hmass' : mass'.val = mass.val + astAt asteroids i)
    (hlen' : (astList A').length = n - 1)
    (hlow : ∀ j, j < i → astAt A' j = astAt asteroids j)
    (hhigh : ∀ j, i ≤ j → j < n - 1 → astAt A' j = astAt asteroids (j + 1)) :
    ∀ r r', asteroids_destroyed mass asteroids = ok r →
      asteroids_destroyed mass' A' = ok r' → r = r' := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (mass mass' : Std.I64) (asteroids A' : Slice Std.I64) (n i : ℕ)
    (hn : n = (astList asteroids).length)
    (hmass_lo : 1 ≤ mass.val) (hmass_hi : mass.val ≤ 100000)
    (hn_lo : 2 ≤ n) (hn_hi : n ≤ 100000)
    (hast : ∀ j, j < n → 1 ≤ astAt asteroids j ∧ astAt asteroids j ≤ 100000)
    (hi : i < n) (hind : astAt asteroids i ≤ mass.val)
    (hnosum : mass.val + astAt asteroids i ≤ 100000)
    (hmass' : mass'.val = mass.val + astAt asteroids i)
    (hlen' : (astList A').length = n - 1)
    (hlow : ∀ j, j < i → astAt A' j = astAt asteroids j)
    (hhigh : ∀ j, i ≤ j → j < n - 1 → astAt A' j = astAt asteroids (j + 1)), ∀ r r', asteroids_destroyed mass asteroids = ok r →
      asteroids_destroyed mass' A' = ok r' → r = r') := by
  sorry

/-- Let b be a nondecreasing rearrangement of asteroids. The function returns a result r, and r = true if and only if for every k with 0 <= k < n, mass + (sum over j with 0 <= j < k of b[j]) >= b[k].
  Preconditions: Let n = len(asteroids). Assume 1 <= mass <= 100000, 1 <= n <= 100000, and 1 <= asteroids[i] <= 100000 for every i with 0 <= i < n. -/
theorem spec_15 (mass : Std.I64) (asteroids : Slice Std.I64) (n : ℕ)
    (hn : n = (astList asteroids).length)
    (hmass_lo : 1 ≤ mass.val) (hmass_hi : mass.val ≤ 100000)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hast : ∀ i, i < n → 1 ≤ astAt asteroids i ∧ astAt asteroids i ≤ 100000) :
    ∃ r, asteroids_destroyed mass asteroids = ok r ∧
      ∀ b : List ℤ, IsNondescRearrangement asteroids b →
        (r = true ↔ ∀ k, k < n → mass.val + prefixSum b k ≥ listAt b k) := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (mass : Std.I64) (asteroids : Slice Std.I64) (n : ℕ)
    (hn : n = (astList asteroids).length)
    (hmass_lo : 1 ≤ mass.val) (hmass_hi : mass.val ≤ 100000)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hast : ∀ i, i < n → 1 ≤ astAt asteroids i ∧ astAt asteroids i ≤ 100000), ∃ r, asteroids_destroyed mass asteroids = ok r ∧
      ∀ b : List ℤ, IsNondescRearrangement asteroids b →
        (r = true ↔ ∀ k, k < n → mass.val + prefixSum b k ≥ listAt b k)) := by
  sorry

end AegisSpec.AsteroidsDestroyed
