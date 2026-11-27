import Aegis.Combine.Code.Funs

/-!
# Specifications of `Aegis.Combine.combine`

LeetCode problem `combinations`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.Combine

  def entries (row : alloc.vec.Vec Std.I64) : List ℤ :=
    row.val.map (fun x => x.val)

  def rows (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) : List (List ℤ) :=
    r.val.map entries

  def iota (m : ℕ) : List ℤ :=
    (List.range m).map (fun i => ((i : ℤ) + 1))

  def binom (a b : ℕ) : ℕ :=
    a.choose b

  def rowAt (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (i : ℕ) : List ℤ :=
    ((rows r)[i]?).getD []

  def rowSet (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (i : ℕ) : Finset ℤ :=
    (rowAt r i).toFinset

  def countRows (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (p : List ℤ → Prop)
      [DecidablePred p] : ℕ :=
    (rows r).countP (fun l => decide (p l))

  /-- Whenever the function returns a result r, r is exactly the collection of all k-element subsets of {1,2,...,n}, represented as lists with arbitrary outer order and arbitrary order inside each list: (1) for every i with 0 <= i < len(r), len(r[i]) = k, the entries of r[i] are pairwise distinct, and every entry lies in {1,2,...,n}; (2) for every subset S of {1,2,...,n} with |S| = k, there is exactly one index i with 0 <= i < len(r) such that the set of entries of r[i] is S.
    Preconditions: 1 <= n <= 20 and 1 <= k <= n, where n and k denote the mathematical integer values of the Std.I64 arguments. -/
  theorem spec_1
      (n k : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20) (hk1 : 1 ≤ k.val)
      (hk2 : k.val ≤ n.val)
      (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (hr : Aegis.Combine.combine n k = ok r) :
      (∀ l ∈ rows r, l.length = k.val.toNat) ∧
      (∀ l ∈ rows r, l.Nodup) ∧
      (∀ l ∈ rows r, ∀ x ∈ l, 1 ≤ x ∧ x ≤ n.val) ∧
      (∀ S : Finset ℤ, (∀ x ∈ S, 1 ≤ x ∧ x ≤ n.val) → S.card = k.val.toNat →
        countRows r (fun l => l.toFinset = S) = 1) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n k : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20) (hk1 : 1 ≤ k.val)
        (hk2 : k.val ≤ n.val)
        (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
        (hr : Aegis.Combine.combine n k = ok r), (∀ l ∈ rows r, l.length = k.val.toNat) ∧
        (∀ l ∈ rows r, l.Nodup) ∧
        (∀ l ∈ rows r, ∀ x ∈ l, 1 ≤ x ∧ x ≤ n.val) ∧
        (∀ S : Finset ℤ, (∀ x ∈ S, 1 ≤ x ∧ x ≤ n.val) → S.card = k.val.toNat →
          countRows r (fun l => l.toFinset = S) = 1)) := by
    sorry

  /-- For every n and k satisfying the preconditions, the function returns a result r; it does not fail due to overflow, out-of-bounds access, or panic.
    Preconditions: 1 <= n <= 20 and 1 <= k <= n, where n and k denote the mathematical integer values of the Std.I64 arguments. -/
  theorem spec_2
      (n k : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20) (hk1 : 1 ≤ k.val)
      (hk2 : k.val ≤ n.val) :
      ∃ r, Aegis.Combine.combine n k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n k : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20) (hk1 : 1 ≤ k.val)
        (hk2 : k.val ≤ n.val), ∃ r, Aegis.Combine.combine n k = ok r) := by
    sorry

  /-- Whenever the function returns a result r, len(r) = C(n,k), where C(n,k) = n!/(k!(n-k)!) is the number of k-element subsets of {1,2,...,n}.
    Preconditions: 1 <= n <= 20 and 1 <= k <= n, where n and k denote the mathematical integer values of the Std.I64 arguments. -/
  theorem spec_3
      (n k : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20) (hk1 : 1 ≤ k.val)
      (hk2 : k.val ≤ n.val)
      (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (hr : Aegis.Combine.combine n k = ok r) :
      (rows r).length = binom n.val.toNat k.val.toNat := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n k : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20) (hk1 : 1 ≤ k.val)
        (hk2 : k.val ≤ n.val)
        (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
        (hr : Aegis.Combine.combine n k = ok r), (rows r).length = binom n.val.toNat k.val.toNat) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(r), len(r[i]) = k.
    Preconditions: 1 <= n <= 20 and 1 <= k <= n, where n and k denote the mathematical integer values of the Std.I64 arguments. -/
  theorem spec_4
      (n k : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20) (hk1 : 1 ≤ k.val)
      (hk2 : k.val ≤ n.val)
      (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (hr : Aegis.Combine.combine n k = ok r) :
      ∀ l ∈ rows r, l.length = k.val.toNat := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n k : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20) (hk1 : 1 ≤ k.val)
        (hk2 : k.val ≤ n.val)
        (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
        (hr : Aegis.Combine.combine n k = ok r), ∀ l ∈ rows r, l.length = k.val.toNat) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(r) and every j with 0 <= j < len(r[i]), 1 <= r[i][j] <= n, interpreting each r[i][j] as a mathematical integer.
    Preconditions: 1 <= n <= 20 and 1 <= k <= n, where n and k denote the mathematical integer values of the Std.I64 arguments. -/
  theorem spec_5
      (n k : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20) (hk1 : 1 ≤ k.val)
      (hk2 : k.val ≤ n.val)
      (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (hr : Aegis.Combine.combine n k = ok r) :
      ∀ l ∈ rows r, ∀ x ∈ l, 1 ≤ x ∧ x ≤ n.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n k : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20) (hk1 : 1 ≤ k.val)
        (hk2 : k.val ≤ n.val)
        (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
        (hr : Aegis.Combine.combine n k = ok r), ∀ l ∈ rows r, ∀ x ∈ l, 1 ≤ x ∧ x ≤ n.val) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(r) and all j1, j2 with 0 <= j1 < j2 < len(r[i]), r[i][j1] != r[i][j2].
    Preconditions: 1 <= n <= 20 and 1 <= k <= n, where n and k denote the mathematical integer values of the Std.I64 arguments. -/
  theorem spec_6
      (n k : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20) (hk1 : 1 ≤ k.val)
      (hk2 : k.val ≤ n.val)
      (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (hr : Aegis.Combine.combine n k = ok r) :
      ∀ l ∈ rows r, ∀ (j1 j2 : ℕ) (hlt : j1 < j2) (hlen : j2 < l.length), l[j1] ≠ l[j2] := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n k : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20) (hk1 : 1 ≤ k.val)
        (hk2 : k.val ≤ n.val)
        (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
        (hr : Aegis.Combine.combine n k = ok r), ∀ l ∈ rows r, ∀ (j1 j2 : ℕ) (hlt : j1 < j2) (hlen : j2 < l.length), l[j1] ≠ l[j2]) := by
    sorry

  /-- Whenever the function returns a result r, for every subset S of {1,2,...,n} with |S| = k, there exists an index i with 0 <= i < len(r) such that the set of entries of r[i] is exactly S.
    Preconditions: 1 <= n <= 20 and 1 <= k <= n, where n and k denote the mathematical integer values of the Std.I64 arguments. -/
  theorem spec_7
      (n k : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20) (hk1 : 1 ≤ k.val)
      (hk2 : k.val ≤ n.val)
      (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (hr : Aegis.Combine.combine n k = ok r) :
      ∀ S : Finset ℤ, (∀ x ∈ S, 1 ≤ x ∧ x ≤ n.val) → S.card = k.val.toNat →
        ∃ l ∈ rows r, l.toFinset = S := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n k : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20) (hk1 : 1 ≤ k.val)
        (hk2 : k.val ≤ n.val)
        (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
        (hr : Aegis.Combine.combine n k = ok r), ∀ S : Finset ℤ, (∀ x ∈ S, 1 ≤ x ∧ x ≤ n.val) → S.card = k.val.toNat →
          ∃ l ∈ rows r, l.toFinset = S) := by
    sorry

  /-- Whenever the function returns a result r, for all i1 and i2 with 0 <= i1 < i2 < len(r), the set of entries of r[i1] is not equal to the set of entries of r[i2].
    Preconditions: 1 <= n <= 20 and 1 <= k <= n, where n and k denote the mathematical integer values of the Std.I64 arguments. -/
  theorem spec_8
      (n k : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20) (hk1 : 1 ≤ k.val)
      (hk2 : k.val ≤ n.val)
      (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (hr : Aegis.Combine.combine n k = ok r) :
      ∀ i1 i2 : ℕ, i1 < i2 → i2 < (rows r).length → rowSet r i1 ≠ rowSet r i2 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n k : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20) (hk1 : 1 ≤ k.val)
        (hk2 : k.val ≤ n.val)
        (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
        (hr : Aegis.Combine.combine n k = ok r), ∀ i1 i2 : ℕ, i1 < i2 → i2 < (rows r).length → rowSet r i1 ≠ rowSet r i2) := by
    sorry

  /-- Whenever the function returns a result r, for every v with 1 <= v <= n, the number of indices i with 0 <= i < len(r) such that v occurs among the entries of r[i] equals C(n-1,k-1), where C(a,b) is the binomial coefficient a!/(b!(a-b)!).
    Preconditions: 1 <= n <= 20 and 1 <= k <= n, where n and k denote the mathematical integer values of the Std.I64 arguments. -/
  theorem spec_9
      (n k : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20) (hk1 : 1 ≤ k.val)
      (hk2 : k.val ≤ n.val)
      (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (hr : Aegis.Combine.combine n k = ok r) :
      ∀ v : ℤ, 1 ≤ v → v ≤ n.val →
        countRows r (fun l => v ∈ l) = binom (n.val.toNat - 1) (k.val.toNat - 1) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n k : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20) (hk1 : 1 ≤ k.val)
        (hk2 : k.val ≤ n.val)
        (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
        (hr : Aegis.Combine.combine n k = ok r), ∀ v : ℤ, 1 ≤ v → v ≤ n.val →
          countRows r (fun l => v ∈ l) = binom (n.val.toNat - 1) (k.val.toNat - 1)) := by
    sorry

  /-- Whenever the function returns a result r, for every pair (a,b) with 1 <= a < b <= n, the number of indices i with 0 <= i < len(r) such that both a and b occur among the entries of r[i] equals C(n-2,k-2) if k >= 2, and equals 0 if k = 1.
    Preconditions: 1 <= n <= 20 and 1 <= k <= n, where n and k denote the mathematical integer values of the Std.I64 arguments. -/
  theorem spec_10
      (n k : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20) (hk1 : 1 ≤ k.val)
      (hk2 : k.val ≤ n.val)
      (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (hr : Aegis.Combine.combine n k = ok r) :
      ∀ a b : ℤ, 1 ≤ a → a < b → b ≤ n.val →
        countRows r (fun l => a ∈ l ∧ b ∈ l) =
          if 2 ≤ k.val then binom (n.val.toNat - 2) (k.val.toNat - 2) else 0 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n k : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20) (hk1 : 1 ≤ k.val)
        (hk2 : k.val ≤ n.val)
        (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
        (hr : Aegis.Combine.combine n k = ok r), ∀ a b : ℤ, 1 ≤ a → a < b → b ≤ n.val →
          countRows r (fun l => a ∈ l ∧ b ∈ l) =
            if 2 ≤ k.val then binom (n.val.toNat - 2) (k.val.toNat - 2) else 0) := by
    sorry

  /-- Whenever the function returns a result r, the sum of all entries of all inner lists, namely sum over 0 <= i < len(r) and 0 <= j < len(r[i]) of r[i][j], equals C(n-1,k-1) * n(n+1)/2, interpreting the sum and the product as mathematical integers.
    Preconditions: 1 <= n <= 20 and 1 <= k <= n, where n and k denote the mathematical integer values of the Std.I64 arguments. -/
  theorem spec_11
      (n k : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20) (hk1 : 1 ≤ k.val)
      (hk2 : k.val ≤ n.val)
      (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (hr : Aegis.Combine.combine n k = ok r) :
      (rows r).flatten.sum =
        (((binom (n.val.toNat - 1) (k.val.toNat - 1)) *
            (n.val.toNat * (n.val.toNat + 1) / 2) : ℕ) : ℤ) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (n k : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20) (hk1 : 1 ≤ k.val)
        (hk2 : k.val ≤ n.val)
        (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
        (hr : Aegis.Combine.combine n k = ok r), (rows r).flatten.sum =
          (((binom (n.val.toNat - 1) (k.val.toNat - 1)) *
              (n.val.toNat * (n.val.toNat + 1) / 2) : ℕ) : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r and k = n, len(r) = 1 and the unique inner list r[0] is a permutation of [1,2,...,n], i.e. its entries are exactly 1,2,...,n in some order.
    Preconditions: 1 <= n <= 20 and 1 <= k <= n, where n and k denote the mathematical integer values of the Std.I64 arguments. -/
  theorem spec_12
      (n k : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20) (hk1 : 1 ≤ k.val)
      (hk2 : k.val ≤ n.val)
      (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (hr : Aegis.Combine.combine n k = ok r)
      (hkn : k.val = n.val) :
      (rows r).length = 1 ∧ ∃ l, rows r = [l] ∧ l.Perm (iota n.val.toNat) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (n k : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20) (hk1 : 1 ≤ k.val)
        (hk2 : k.val ≤ n.val)
        (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
        (hr : Aegis.Combine.combine n k = ok r)
        (hkn : k.val = n.val), (rows r).length = 1 ∧ ∃ l, rows r = [l] ∧ l.Perm (iota n.val.toNat)) := by
    sorry

  /-- Whenever the function returns a result r and k = 1, len(r) = n and for every v with 1 <= v <= n there is exactly one index i with 0 <= i < len(r) such that r[i] is the singleton list [v].
    Preconditions: 1 <= n <= 20 and 1 <= k <= n, where n and k denote the mathematical integer values of the Std.I64 arguments. -/
  theorem spec_13
      (n k : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20) (hk1 : 1 ≤ k.val)
      (hk2 : k.val ≤ n.val)
      (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (hr : Aegis.Combine.combine n k = ok r)
      (hk1' : k.val = 1) :
      (rows r).length = n.val.toNat ∧
        ∀ v : ℤ, 1 ≤ v → v ≤ n.val → countRows r (fun l => l = [v]) = 1 := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (n k : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20) (hk1 : 1 ≤ k.val)
        (hk2 : k.val ≤ n.val)
        (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
        (hr : Aegis.Combine.combine n k = ok r)
        (hk1' : k.val = 1), (rows r).length = n.val.toNat ∧
          ∀ v : ℤ, 1 ≤ v → v ≤ n.val → countRows r (fun l => l = [v]) = 1) := by
    sorry

  end AegisSpec.Combine
