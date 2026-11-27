import Aegis.CombinationSum3.Code.Funs

/-!
# Specifications of `Aegis.CombinationSum3.combination_sum3`

LeetCode problem `combination-sum-iii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.CombinationSum3

  open Aegis.CombinationSum3

  def vals (c : Aeneas.Std.alloc.vec.Vec Aeneas.Std.I64) : List ℤ :=
    c.val.map (fun x => x.val)

  def entries (c : Aeneas.Std.alloc.vec.Vec Aeneas.Std.I64) : Finset ℤ :=
    (vals c).toFinset

  def nine : Finset ℤ := {1, 2, 3, 4, 5, 6, 7, 8, 9}

  def IsKSubsetOfNine (k : ℤ) (S : Finset ℤ) : Prop :=
    S ⊆ nine ∧ (S.card : ℤ) = k

  def IsSolution (k n : ℤ) (S : Finset ℤ) : Prop :=
    IsKSubsetOfNine k S ∧ S.sum (fun x => x) = n

  /-- Whenever the function returns a result r, the following holds. (1) For every vector c in r, len(c) = k, every entry c[i] with 0 <= i < len(c) satisfies 1 <= c[i] <= 9, the entries of c are pairwise distinct, and sum_{i=0}^{len(c)-1} c[i] = n. (2) For every k-element subset S of {1,2,...,9} with sum_{x in S} x = n, there is exactly one vector c in r whose set of entries {c[i] : 0 <= i < len(c)} equals S. (3) Conversely, for every vector c in r, its set of entries is a k-element subset of {1,2,...,9} with sum n. Equivalently, the collection of sets of entries of the vectors in r is exactly the set of all k-element subsets S of {1,2,...,9} satisfying sum_{x in S} x = n, with each such subset represented by exactly one vector.
    Preconditions: k and n are integers with 2 <= k <= 9 and 1 <= n <= 60. All sums mentioned are mathematical sums of the listed entries. -/
  theorem spec_1 (k n : Std.I64)
      (r : Aeneas.Std.alloc.vec.Vec (Aeneas.Std.alloc.vec.Vec Aeneas.Std.I64))
      (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ 9)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 60)
      (h : combination_sum3 k n = ok r) :
      (∀ c ∈ r.val,
          (c.val.length : ℤ) = k.val ∧
          (∀ (i : Nat) (hi : i < c.val.length),
            1 ≤ (c.val[i]'hi).val ∧ (c.val[i]'hi).val ≤ 9) ∧
          (vals c).Nodup ∧
          (vals c).sum = n.val) ∧
      (∀ S : Finset ℤ, IsSolution k.val n.val S → ∃! c, c ∈ r.val ∧ entries c = S) ∧
      (∀ c ∈ r.val,
          entries c ⊆ nine ∧ ((entries c).card : ℤ) = k.val ∧
          (entries c).sum (fun x => x) = n.val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (k n : Std.I64)
        (r : Aeneas.Std.alloc.vec.Vec (Aeneas.Std.alloc.vec.Vec Aeneas.Std.I64))
        (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ 9)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 60)
        (h : combination_sum3 k n = ok r), (∀ c ∈ r.val,
            (c.val.length : ℤ) = k.val ∧
            (∀ (i : Nat) (hi : i < c.val.length),
              1 ≤ (c.val[i]'hi).val ∧ (c.val[i]'hi).val ≤ 9) ∧
            (vals c).Nodup ∧
            (vals c).sum = n.val) ∧
        (∀ S : Finset ℤ, IsSolution k.val n.val S → ∃! c, c ∈ r.val ∧ entries c = S) ∧
        (∀ c ∈ r.val,
            entries c ⊆ nine ∧ ((entries c).card : ℤ) = k.val ∧
            (entries c).sum (fun x => x) = n.val)) := by
    sorry

  /-- For every k and n satisfying the preconditions, the function returns a result r; it does not fail, overflow, or panic.
    Preconditions: k and n are integers with 2 <= k <= 9 and 1 <= n <= 60. -/
  theorem spec_2 (k n : Std.I64)
      (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ 9)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 60) :
      ∃ r : Aeneas.Std.alloc.vec.Vec (Aeneas.Std.alloc.vec.Vec Aeneas.Std.I64),
        combination_sum3 k n = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (k n : Std.I64)
        (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ 9)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 60), ∃ r : Aeneas.Std.alloc.vec.Vec (Aeneas.Std.alloc.vec.Vec Aeneas.Std.I64),
          combination_sum3 k n = ok r) := by
    sorry

  /-- Whenever the function returns a result r, for every vector c in r, len(c) = k.
    Preconditions: k and n are integers with 2 <= k <= 9 and 1 <= n <= 60. -/
  theorem spec_3 (k n : Std.I64)
      (r : Aeneas.Std.alloc.vec.Vec (Aeneas.Std.alloc.vec.Vec Aeneas.Std.I64))
      (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ 9)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 60)
      (h : combination_sum3 k n = ok r) :
      ∀ c ∈ r.val, (c.val.length : ℤ) = k.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (k n : Std.I64)
        (r : Aeneas.Std.alloc.vec.Vec (Aeneas.Std.alloc.vec.Vec Aeneas.Std.I64))
        (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ 9)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 60)
        (h : combination_sum3 k n = ok r), ∀ c ∈ r.val, (c.val.length : ℤ) = k.val) := by
    sorry

  /-- Whenever the function returns a result r, for every vector c in r and every index i with 0 <= i < len(c), the entry c[i] satisfies 1 <= c[i] <= 9.
    Preconditions: k and n are integers with 2 <= k <= 9 and 1 <= n <= 60. -/
  theorem spec_4 (k n : Std.I64)
      (r : Aeneas.Std.alloc.vec.Vec (Aeneas.Std.alloc.vec.Vec Aeneas.Std.I64))
      (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ 9)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 60)
      (h : combination_sum3 k n = ok r) :
      ∀ c ∈ r.val, ∀ (i : Nat) (hi : i < c.val.length),
        1 ≤ (c.val[i]'hi).val ∧ (c.val[i]'hi).val ≤ 9 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (k n : Std.I64)
        (r : Aeneas.Std.alloc.vec.Vec (Aeneas.Std.alloc.vec.Vec Aeneas.Std.I64))
        (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ 9)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 60)
        (h : combination_sum3 k n = ok r), ∀ c ∈ r.val, ∀ (i : Nat) (hi : i < c.val.length),
          1 ≤ (c.val[i]'hi).val ∧ (c.val[i]'hi).val ≤ 9) := by
    sorry

  /-- Whenever the function returns a result r, for every vector c in r, the entries of c are pairwise distinct: for all indices i and j with 0 <= i < len(c), 0 <= j < len(c), and i != j, c[i] != c[j].
    Preconditions: k and n are integers with 2 <= k <= 9 and 1 <= n <= 60. -/
  theorem spec_5 (k n : Std.I64)
      (r : Aeneas.Std.alloc.vec.Vec (Aeneas.Std.alloc.vec.Vec Aeneas.Std.I64))
      (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ 9)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 60)
      (h : combination_sum3 k n = ok r) :
      ∀ c ∈ r.val, ∀ (i j : Nat) (hi : i < c.val.length) (hj : j < c.val.length),
        i ≠ j → (c.val[i]'hi).val ≠ (c.val[j]'hj).val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (k n : Std.I64)
        (r : Aeneas.Std.alloc.vec.Vec (Aeneas.Std.alloc.vec.Vec Aeneas.Std.I64))
        (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ 9)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 60)
        (h : combination_sum3 k n = ok r), ∀ c ∈ r.val, ∀ (i j : Nat) (hi : i < c.val.length) (hj : j < c.val.length),
          i ≠ j → (c.val[i]'hi).val ≠ (c.val[j]'hj).val) := by
    sorry

  /-- Whenever the function returns a result r, for every vector c in r, sum_{i=0}^{len(c)-1} c[i] = n.
    Preconditions: k and n are integers with 2 <= k <= 9 and 1 <= n <= 60. -/
  theorem spec_6 (k n : Std.I64)
      (r : Aeneas.Std.alloc.vec.Vec (Aeneas.Std.alloc.vec.Vec Aeneas.Std.I64))
      (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ 9)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 60)
      (h : combination_sum3 k n = ok r) :
      ∀ c ∈ r.val, (vals c).sum = n.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (k n : Std.I64)
        (r : Aeneas.Std.alloc.vec.Vec (Aeneas.Std.alloc.vec.Vec Aeneas.Std.I64))
        (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ 9)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 60)
        (h : combination_sum3 k n = ok r), ∀ c ∈ r.val, (vals c).sum = n.val) := by
    sorry

  /-- Whenever the function returns a result r, no two distinct positions of r contain vectors with the same set of entries: for all indices p and q with 0 <= p < len(r), 0 <= q < len(r), and p != q, the set {r[p][i] : 0 <= i < len(r[p])} is not equal to the set {r[q][i] : 0 <= i < len(r[q])}.
    Preconditions: k and n are integers with 2 <= k <= 9 and 1 <= n <= 60. -/
  theorem spec_7 (k n : Std.I64)
      (r : Aeneas.Std.alloc.vec.Vec (Aeneas.Std.alloc.vec.Vec Aeneas.Std.I64))
      (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ 9)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 60)
      (h : combination_sum3 k n = ok r) :
      ∀ (p q : Nat) (hp : p < r.val.length) (hq : q < r.val.length), p ≠ q →
        entries (r.val[p]'hp) ≠ entries (r.val[q]'hq) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (k n : Std.I64)
        (r : Aeneas.Std.alloc.vec.Vec (Aeneas.Std.alloc.vec.Vec Aeneas.Std.I64))
        (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ 9)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 60)
        (h : combination_sum3 k n = ok r), ∀ (p q : Nat) (hp : p < r.val.length) (hq : q < r.val.length), p ≠ q →
          entries (r.val[p]'hp) ≠ entries (r.val[q]'hq)) := by
    sorry

  /-- Whenever the function returns a result r, for every k-element subset S of {1,2,...,9} whose element sum is n, there exists a vector c in r such that the set of entries of c is exactly S.
    Preconditions: k and n are integers with 2 <= k <= 9 and 1 <= n <= 60. -/
  theorem spec_8 (k n : Std.I64)
      (r : Aeneas.Std.alloc.vec.Vec (Aeneas.Std.alloc.vec.Vec Aeneas.Std.I64))
      (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ 9)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 60)
      (h : combination_sum3 k n = ok r) :
      ∀ S : Finset ℤ, IsSolution k.val n.val S → ∃ c, c ∈ r.val ∧ entries c = S := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (k n : Std.I64)
        (r : Aeneas.Std.alloc.vec.Vec (Aeneas.Std.alloc.vec.Vec Aeneas.Std.I64))
        (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ 9)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 60)
        (h : combination_sum3 k n = ok r), ∀ S : Finset ℤ, IsSolution k.val n.val S → ∃ c, c ∈ r.val ∧ entries c = S) := by
    sorry

  /-- Whenever the function returns a result r, len(r) <= C(9,k), where C(9,k) is the number of k-element subsets of {1,2,...,9}. Equivalently, len(r) <= 9!/(k!*(9-k)!).
    Preconditions: k and n are integers with 2 <= k <= 9 and 1 <= n <= 60. -/
  theorem spec_9 (k n : Std.I64)
      (r : Aeneas.Std.alloc.vec.Vec (Aeneas.Std.alloc.vec.Vec Aeneas.Std.I64))
      (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ 9)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 60)
      (h : combination_sum3 k n = ok r) :
      r.val.length ≤ Nat.choose 9 k.val.toNat := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (k n : Std.I64)
        (r : Aeneas.Std.alloc.vec.Vec (Aeneas.Std.alloc.vec.Vec Aeneas.Std.I64))
        (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ 9)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 60)
        (h : combination_sum3 k n = ok r), r.val.length ≤ Nat.choose 9 k.val.toNat) := by
    sorry

  /-- Whenever the function returns a result r, if n < k*(k+1)/2, then len(r) = 0. Here k*(k+1)/2 is the minimum possible sum of k distinct positive integers.
    Preconditions: k and n are integers with 2 <= k <= 9 and 1 <= n <= 60. -/
  theorem spec_10 (k n : Std.I64)
      (r : Aeneas.Std.alloc.vec.Vec (Aeneas.Std.alloc.vec.Vec Aeneas.Std.I64))
      (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ 9)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 60)
      (h : combination_sum3 k n = ok r) :
      n.val < k.val * (k.val + 1) / 2 → r.val.length = 0 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (k n : Std.I64)
        (r : Aeneas.Std.alloc.vec.Vec (Aeneas.Std.alloc.vec.Vec Aeneas.Std.I64))
        (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ 9)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 60)
        (h : combination_sum3 k n = ok r), n.val < k.val * (k.val + 1) / 2 → r.val.length = 0) := by
    sorry

  /-- Whenever the function returns a result r, if n > k*(19-k)/2, then len(r) = 0. Here k*(19-k)/2 is the maximum possible sum of k distinct numbers chosen from {1,...,9}.
    Preconditions: k and n are integers with 2 <= k <= 9 and 1 <= n <= 60. -/
  theorem spec_11 (k n : Std.I64)
      (r : Aeneas.Std.alloc.vec.Vec (Aeneas.Std.alloc.vec.Vec Aeneas.Std.I64))
      (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ 9)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 60)
      (h : combination_sum3 k n = ok r) :
      k.val * (19 - k.val) / 2 < n.val → r.val.length = 0 := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (k n : Std.I64)
        (r : Aeneas.Std.alloc.vec.Vec (Aeneas.Std.alloc.vec.Vec Aeneas.Std.I64))
        (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ 9)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 60)
        (h : combination_sum3 k n = ok r), k.val * (19 - k.val) / 2 < n.val → r.val.length = 0) := by
    sorry

  /-- Whenever the function returns a result r, for every vector c in r, if S is the set of entries of c, then the complement of S in {1,2,...,9} has size 9-k and its elements sum to 45-n.
    Preconditions: k and n are integers with 2 <= k <= 9 and 1 <= n <= 60. -/
  theorem spec_12 (k n : Std.I64)
      (r : Aeneas.Std.alloc.vec.Vec (Aeneas.Std.alloc.vec.Vec Aeneas.Std.I64))
      (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ 9)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 60)
      (h : combination_sum3 k n = ok r) :
      ∀ c ∈ r.val,
        ((nine \ entries c).card : ℤ) = 9 - k.val ∧
        (nine \ entries c).sum (fun x => x) = 45 - n.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (k n : Std.I64)
        (r : Aeneas.Std.alloc.vec.Vec (Aeneas.Std.alloc.vec.Vec Aeneas.Std.I64))
        (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ 9)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 60)
        (h : combination_sum3 k n = ok r), ∀ c ∈ r.val,
          ((nine \ entries c).card : ℤ) = 9 - k.val ∧
          (nine \ entries c).sum (fun x => x) = 45 - n.val) := by
    sorry

  /-- Whenever the function returns a result r, if len(r) > 0, then k*(k+1)/2 <= n <= k*(19-k)/2.
    Preconditions: k and n are integers with 2 <= k <= 9 and 1 <= n <= 60. -/
  theorem spec_13 (k n : Std.I64)
      (r : Aeneas.Std.alloc.vec.Vec (Aeneas.Std.alloc.vec.Vec Aeneas.Std.I64))
      (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ 9)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 60)
      (h : combination_sum3 k n = ok r) :
      0 < r.val.length →
        k.val * (k.val + 1) / 2 ≤ n.val ∧ n.val ≤ k.val * (19 - k.val) / 2 := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (k n : Std.I64)
        (r : Aeneas.Std.alloc.vec.Vec (Aeneas.Std.alloc.vec.Vec Aeneas.Std.I64))
        (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ 9)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 60)
        (h : combination_sum3 k n = ok r), 0 < r.val.length →
          k.val * (k.val + 1) / 2 ≤ n.val ∧ n.val ≤ k.val * (19 - k.val) / 2) := by
    sorry

  /-- Whenever the function returns a result r, if k*(k+1)/2 <= n <= k*(19-k)/2, then len(r) > 0.
    Preconditions: k and n are integers with 2 <= k <= 9 and 1 <= n <= 60. -/
  theorem spec_14 (k n : Std.I64)
      (r : Aeneas.Std.alloc.vec.Vec (Aeneas.Std.alloc.vec.Vec Aeneas.Std.I64))
      (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ 9)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 60)
      (h : combination_sum3 k n = ok r) :
      k.val * (k.val + 1) / 2 ≤ n.val → n.val ≤ k.val * (19 - k.val) / 2 →
        0 < r.val.length := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (k n : Std.I64)
        (r : Aeneas.Std.alloc.vec.Vec (Aeneas.Std.alloc.vec.Vec Aeneas.Std.I64))
        (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ 9)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 60)
        (h : combination_sum3 k n = ok r), k.val * (k.val + 1) / 2 ≤ n.val → n.val ≤ k.val * (19 - k.val) / 2 →
          0 < r.val.length) := by
    sorry

  end AegisSpec.CombinationSum3
