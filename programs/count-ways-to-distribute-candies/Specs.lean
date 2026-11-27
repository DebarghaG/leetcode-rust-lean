import Aegis.WaysToDistribute.Code.Funs

/-!
# Specifications of `Aegis.WaysToDistribute.ways_to_distribute`

LeetCode problem `count-ways-to-distribute-candies`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.WaysToDistribute

  def IsSetPartition {n : ℕ} (P : Finset (Finset (Fin n))) : Prop :=
    (∀ p ∈ P, p.Nonempty) ∧
    (∀ p ∈ P, ∀ q ∈ P, p ≠ q → Disjoint p q) ∧
    (∀ x : Fin n, ∃ p ∈ P, x ∈ p)

  instance instDecidablePredIsSetPartition {n : ℕ} :
      DecidablePred (fun P : Finset (Finset (Fin n)) => IsSetPartition P) :=
    fun _ => by unfold IsSetPartition; infer_instance

  def setPartitions (n k : ℕ) : Finset (Finset (Finset (Fin n))) :=
    Finset.univ.filter (fun P => P.card = k ∧ IsSetPartition P)

  def stirlingSecond (n k : ℕ) : ℕ := (setPartitions n k).card

  def setPartitionsAny (n : ℕ) : Finset (Finset (Finset (Fin n))) :=
    Finset.univ.filter (fun P => IsSetPartition P)

  def bellNumber (n : ℕ) : ℕ := (setPartitionsAny n).card

  /-- Let M = 1,000,000,007. Let S(n,k) be the number of partitions of the set {1,2,...,n} into exactly k nonempty, pairwise disjoint, unordered parts whose union is {1,2,...,n}. The function returns a result r such that 0 <= r < M and r ≡ S(n,k) (mod M); equivalently, r is the least nonnegative representative of S(n,k) modulo M.
    Preconditions: n and k are Std.I64 values with 1 <= k <= n <= 1000. -/
  theorem spec_1 (n k : Std.I64)
      (hk1 : 1 ≤ k.val) (hkn : k.val ≤ n.val) (hn : n.val ≤ 1000) :
      ∃ r : Std.I64,
        Aegis.WaysToDistribute.ways_to_distribute n k = ok r ∧
          0 ≤ r.val ∧ r.val < 1000000007 ∧
            Int.ModEq 1000000007 r.val
              ((stirlingSecond n.val.toNat k.val.toNat : ℕ) : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n k : Std.I64)
        (hk1 : 1 ≤ k.val) (hkn : k.val ≤ n.val) (hn : n.val ≤ 1000), ∃ r : Std.I64,
          Aegis.WaysToDistribute.ways_to_distribute n k = ok r ∧
            0 ≤ r.val ∧ r.val < 1000000007 ∧
              Int.ModEq 1000000007 r.val
                ((stirlingSecond n.val.toNat k.val.toNat : ℕ) : ℤ)) := by
    sorry

  /-- For every n,k satisfying the preconditions, the function returns a result and does not fail (no overflow, out-of-bounds, panic, or other failure).
    Preconditions: n and k are Std.I64 values with 1 <= k <= n <= 1000. -/
  theorem spec_2 (n k : Std.I64)
      (hk1 : 1 ≤ k.val) (hkn : k.val ≤ n.val) (hn : n.val ≤ 1000) :
      ∃ r : Std.I64, Aegis.WaysToDistribute.ways_to_distribute n k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n k : Std.I64)
        (hk1 : 1 ≤ k.val) (hkn : k.val ≤ n.val) (hn : n.val ≤ 1000), ∃ r : Std.I64, Aegis.WaysToDistribute.ways_to_distribute n k = ok r) := by
    sorry

  /-- For every such n,k, if ways_to_distribute(n,k) returns r, ways_to_distribute(n-1,k) returns r1, and ways_to_distribute(n-1,k-1) returns r2, then r ≡ k*r1 + r2 (mod 1,000,000,007).
    Preconditions: n and k are Std.I64 values with 2 <= k < n <= 1000. -/
  theorem spec_3 (n k n1 k1 : Std.I64)
      (hk2 : 2 ≤ k.val) (hkn : k.val < n.val) (hn : n.val ≤ 1000)
      (hn1 : n1.val = n.val - 1) (hk1 : k1.val = k.val - 1)
      (r r1 r2 : Std.I64)
      (hr : Aegis.WaysToDistribute.ways_to_distribute n k = ok r)
      (hr1 : Aegis.WaysToDistribute.ways_to_distribute n1 k = ok r1)
      (hr2 : Aegis.WaysToDistribute.ways_to_distribute n1 k1 = ok r2) :
      Int.ModEq 1000000007 r.val (k.val * r1.val + r2.val) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n k n1 k1 : Std.I64)
        (hk2 : 2 ≤ k.val) (hkn : k.val < n.val) (hn : n.val ≤ 1000)
        (hn1 : n1.val = n.val - 1) (hk1 : k1.val = k.val - 1)
        (r r1 r2 : Std.I64)
        (hr : Aegis.WaysToDistribute.ways_to_distribute n k = ok r)
        (hr1 : Aegis.WaysToDistribute.ways_to_distribute n1 k = ok r1)
        (hr2 : Aegis.WaysToDistribute.ways_to_distribute n1 k1 = ok r2), Int.ModEq 1000000007 r.val (k.val * r1.val + r2.val)) := by
    sorry

  /-- For every n satisfying the precondition, if for each j with 1 <= j <= n the call ways_to_distribute(n,j) returns a result r_j, then the sum of r_j over 1 <= j <= n is congruent modulo 1,000,000,007 to B(n), where B(n) is the number of partitions of {1,...,n} into any number (from 1 through n) of nonempty unordered parts.
    Preconditions: n is a Std.I64 value with 1 <= n <= 1000. -/
  theorem spec_4 (n : Std.I64)
      (hn1 : 1 ≤ n.val) (hn : n.val ≤ 1000)
      (R : ℤ → Std.I64)
      (hR : ∀ j : Std.I64, 1 ≤ j.val → j.val ≤ n.val →
        Aegis.WaysToDistribute.ways_to_distribute n j = ok (R j.val)) :
      Int.ModEq 1000000007
        (∑ i ∈ Finset.Icc 1 n.val.toNat, (R (i : ℤ)).val)
        ((bellNumber n.val.toNat : ℕ) : ℤ) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : Std.I64)
        (hn1 : 1 ≤ n.val) (hn : n.val ≤ 1000)
        (R : ℤ → Std.I64)
        (hR : ∀ j : Std.I64, 1 ≤ j.val → j.val ≤ n.val →
          Aegis.WaysToDistribute.ways_to_distribute n j = ok (R j.val)), Int.ModEq 1000000007
          (∑ i ∈ Finset.Icc 1 n.val.toNat, (R (i : ℤ)).val)
          ((bellNumber n.val.toNat : ℕ) : ℤ)) := by
    sorry

  end AegisSpec.WaysToDistribute
