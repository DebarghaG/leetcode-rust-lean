import Aegis.GetFactors.Code.Funs

/-!
# Specifications of `Aegis.GetFactors.get_factors`

LeetCode problem `factor-combinations`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.GetFactors

  open Aegis.GetFactors (get_factors)

  def rowEntries (row : alloc.vec.Vec Std.I64) : List ℤ := row.val.map (fun x => x.val)

  def allRows (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) : List (List ℤ) :=
    r.val.map rowEntries

  def rowAt (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (i : ℕ) : List ℤ :=
    (allRows r).getD i []

  def entryAt (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (i j : ℕ) : ℤ :=
    (rowAt r i).getD j 0

  def SameMultiset (l₁ l₂ : List ℤ) : Prop := l₁.Perm l₂

  def ValidCombo (n : ℤ) (M : List ℤ) : Prop :=
    (∀ x ∈ M, 2 ≤ x ∧ x ≤ n - 1) ∧ 2 ≤ M.length ∧ M.prod = n

  def floorLog2 (n : ℕ) : ℕ := n.log2

  /-- Whenever get_factors(n) returns a result r, r represents exactly the set of all valid factor combinations of n, where a factor combination is a multiset M of integers such that every x in M satisfies 2 <= x <= n - 1, |M| >= 2, and the product of all elements of M equals n. Concretely: (a) for every i with 0 <= i < len(r), the multiset of entries of r[i] has all entries in [2, n - 1], has at least two entries, and has product n; and (b) for every multiset M satisfying those three conditions, there is exactly one index i with 0 <= i < len(r) whose row r[i] has entry-multiset M. No other rows occur.
    Preconditions: 1 <= n <= 10^7. -/
  theorem spec_1 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10 ^ 7)
      (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (hr : get_factors n = ok r) :
      (∀ i : ℕ, i < r.val.length → ValidCombo n.val (rowAt r i)) ∧
      (∀ M : List ℤ, ValidCombo n.val M →
        ∃! i : ℕ, i < r.val.length ∧ SameMultiset (rowAt r i) M) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10 ^ 7)
        (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (hr : get_factors n = ok r), (∀ i : ℕ, i < r.val.length → ValidCombo n.val (rowAt r i)) ∧
        (∀ M : List ℤ, ValidCombo n.val M →
          ∃! i : ℕ, i < r.val.length ∧ SameMultiset (rowAt r i) M)) := by
    sorry

  /-- For every n satisfying 1 <= n <= 10^7, the call get_factors(n) returns a result r; it does not fail (no arithmetic overflow, out-of-bounds access, or panic).
    Preconditions: 1 <= n <= 10^7. -/
  theorem spec_2 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10 ^ 7) :
      ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), get_factors n = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10 ^ 7), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), get_factors n = ok r) := by
    sorry

  /-- Whenever get_factors(n) returns r, for every i with 0 <= i < len(r), len(r[i]) >= 2.
    Preconditions: 1 <= n <= 10^7. -/
  theorem spec_3 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10 ^ 7)
      (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (hr : get_factors n = ok r) :
      ∀ i : ℕ, i < r.val.length → 2 ≤ (rowAt r i).length := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10 ^ 7)
        (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (hr : get_factors n = ok r), ∀ i : ℕ, i < r.val.length → 2 ≤ (rowAt r i).length) := by
    sorry

  /-- Whenever get_factors(n) returns r, for every i and j with 0 <= i < len(r) and 0 <= j < len(r[i]), 2 <= r[i][j] <= n - 1.
    Preconditions: 1 <= n <= 10^7. -/
  theorem spec_4 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10 ^ 7)
      (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (hr : get_factors n = ok r) :
      ∀ (i : ℕ), i < r.val.length →
        ∀ (j : ℕ), j < (rowAt r i).length → 2 ≤ entryAt r i j ∧ entryAt r i j ≤ n.val - 1 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10 ^ 7)
        (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (hr : get_factors n = ok r), ∀ (i : ℕ), i < r.val.length →
          ∀ (j : ℕ), j < (rowAt r i).length → 2 ≤ entryAt r i j ∧ entryAt r i j ≤ n.val - 1) := by
    sorry

  /-- Whenever get_factors(n) returns r, for every i with 0 <= i < len(r), the product of the entries of r[i] equals n: (r[i][0] * ... * r[i][len(r[i]) - 1]) = n.
    Preconditions: 1 <= n <= 10^7. -/
  theorem spec_5 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10 ^ 7)
      (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (hr : get_factors n = ok r) :
      ∀ i : ℕ, i < r.val.length → (rowAt r i).prod = n.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10 ^ 7)
        (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (hr : get_factors n = ok r), ∀ i : ℕ, i < r.val.length → (rowAt r i).prod = n.val) := by
    sorry

  /-- Whenever get_factors(n) returns r, for every multiset M of integers such that every x in M satisfies 2 <= x <= n - 1, |M| >= 2, and the product of all elements of M is n, there exists an index i with 0 <= i < len(r) such that the multiset of entries of r[i] equals M.
    Preconditions: 1 <= n <= 10^7. -/
  theorem spec_6 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10 ^ 7)
      (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (hr : get_factors n = ok r) :
      ∀ M : List ℤ, ValidCombo n.val M →
        ∃ i : ℕ, i < r.val.length ∧ SameMultiset (rowAt r i) M := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10 ^ 7)
        (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (hr : get_factors n = ok r), ∀ M : List ℤ, ValidCombo n.val M →
          ∃ i : ℕ, i < r.val.length ∧ SameMultiset (rowAt r i) M) := by
    sorry

  /-- Whenever get_factors(n) returns r, for all i and k with 0 <= i < k < len(r), the multiset of entries of r[i] is not equal to the multiset of entries of r[k].
    Preconditions: 1 <= n <= 10^7. -/
  theorem spec_7 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10 ^ 7)
      (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (hr : get_factors n = ok r) :
      ∀ (i k : ℕ), i < k → k < r.val.length →
        ¬ SameMultiset (rowAt r i) (rowAt r k) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10 ^ 7)
        (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (hr : get_factors n = ok r), ∀ (i k : ℕ), i < k → k < r.val.length →
          ¬ SameMultiset (rowAt r i) (rowAt r k)) := by
    sorry

  /-- Whenever get_factors(n) returns r, for every integer d such that 2 <= d <= n - 1 and d divides n, there exist i and j with 0 <= i < len(r), 0 <= j < len(r[i]), and r[i][j] = d.
    Preconditions: 1 <= n <= 10^7. -/
  theorem spec_8 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10 ^ 7)
      (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (hr : get_factors n = ok r) :
      ∀ d : ℤ, 2 ≤ d → d ≤ n.val - 1 → d ∣ n.val →
        ∃ (i j : ℕ), i < r.val.length ∧ j < (rowAt r i).length ∧ entryAt r i j = d := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10 ^ 7)
        (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (hr : get_factors n = ok r), ∀ d : ℤ, 2 ≤ d → d ≤ n.val - 1 → d ∣ n.val →
          ∃ (i j : ℕ), i < r.val.length ∧ j < (rowAt r i).length ∧ entryAt r i j = d) := by
    sorry

  /-- Whenever get_factors(n) returns r, for every i and j with 0 <= i < len(r) and 0 <= j < len(r[i]), r[i][j] divides n.
    Preconditions: 1 <= n <= 10^7. -/
  theorem spec_9 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10 ^ 7)
      (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (hr : get_factors n = ok r) :
      ∀ (i j : ℕ), i < r.val.length → j < (rowAt r i).length → entryAt r i j ∣ n.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10 ^ 7)
        (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (hr : get_factors n = ok r), ∀ (i j : ℕ), i < r.val.length → j < (rowAt r i).length → entryAt r i j ∣ n.val) := by
    sorry

  /-- Whenever get_factors(n) returns r, for every i with 0 <= i < len(r), len(r[i]) <= L, where L is the largest integer such that 2^L <= n (equivalently L = floor(log2(n))).
    Preconditions: 2 <= n <= 10^7. -/
  theorem spec_10 (n : Std.I64) (hn : 2 ≤ n.val ∧ n.val ≤ 10 ^ 7)
      (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (hr : get_factors n = ok r) :
      ∀ i : ℕ, i < r.val.length → (rowAt r i).length ≤ floorLog2 n.val.toNat := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n : Std.I64) (hn : 2 ≤ n.val ∧ n.val ≤ 10 ^ 7)
        (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (hr : get_factors n = ok r), ∀ i : ℕ, i < r.val.length → (rowAt r i).length ≤ floorLog2 n.val.toNat) := by
    sorry

  /-- Whenever get_factors(n) returns r, for every i and j with 0 <= i < len(r) and 0 <= j < len(r[i]), 2 * r[i][j] <= n.
    Preconditions: 1 <= n <= 10^7. -/
  theorem spec_11 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10 ^ 7)
      (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (hr : get_factors n = ok r) :
      ∀ (i j : ℕ), i < r.val.length → j < (rowAt r i).length → 2 * entryAt r i j ≤ n.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10 ^ 7)
        (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (hr : get_factors n = ok r), ∀ (i j : ℕ), i < r.val.length → j < (rowAt r i).length → 2 * entryAt r i j ≤ n.val) := by
    sorry

  end AegisSpec.GetFactors
