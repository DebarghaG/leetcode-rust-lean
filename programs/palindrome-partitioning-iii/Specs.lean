import Aegis.PalindromePartition.Code.Funs

/-!
# Specifications of `Aegis.PalindromePartition.palindrome_partition`

LeetCode problem `palindrome-partitioning-iii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.PalindromePartition

  def mis (s : Slice U8) (l r : Nat) : Nat :=
    (List.range ((r - l) / 2)).countP
      (fun t => decide (s.val[l + t]? ≠ s.val[r - 1 - t]?))

  def IsKPartition (n k : Nat) (c : List Nat) : Prop :=
    c.length = k + 1 ∧ c.head? = some 0 ∧ c.getLast? = some n ∧ c.Pairwise (· < ·)

  def partitionCost (s : Slice U8) (c : List Nat) : Nat :=
    ((c.zip c.tail).map (fun p => mis s p.1 p.2)).sum

  noncomputable def minPartitionCost (s : Slice U8) (k : Nat) : Nat :=
    sInf {m : Nat | ∃ c : List Nat, IsKPartition s.val.length k c ∧ partitionCost s c = m}

  def IsMinPartitionCost (s : Slice U8) (k m : Nat) : Prop :=
    (∃ c : List Nat, IsKPartition s.val.length k c ∧ partitionCost s c = m) ∧
      ∀ c : List Nat, IsKPartition s.val.length k c → m ≤ partitionCost s c

  def ValidInput (s : Slice U8) (k : I64) : Prop :=
    (1 : Int) ≤ k.val ∧ k.val ≤ (s.val.length : Int) ∧ s.val.length ≤ 100 ∧
      ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122

  def SamePattern (s t : Slice U8) : Prop :=
    t.val.length = s.val.length ∧
      ∀ i j : Nat, (s.val[i]? = s.val[j]? ↔ t.val[i]? = t.val[j]?)

  def revSlice (s : Slice U8) : Slice U8 :=
    Slice.mk s.val.reverse.length (Aeneas.Data.ListN.ListN.fromList s.val.reverse) (by
      rw [List.length_reverse]
      show s.list.toList.length ≤ Usize.max
      rw [Aeneas.Data.ListN.ListN_length]
      exact s.bound)

  /-- Whenever the function returns a result r, r equals the minimum over all k-partitions of s of the sum of the minimum changes needed to make each part a palindrome. Formally, let n = len(s). For 0 <= l < r <= n define mis(l,r) as the number of indices t with 0 <= t < floor((r-l)/2) and s[l+t] != s[r-1-t]; this is exactly the minimum number of character changes that makes s[l..r) a palindrome. A k-partition is a sequence c_0,...,c_k with 0 = c_0 < c_1 < ... < c_k = n. Then r = min { sum_{j=1..k} mis(c_{j-1}, c_j) : c_0,...,c_k is a k-partition }.
    Preconditions: Let n = len(s). The input satisfies 1 <= k <= n <= 100 and every byte of s is in 97..122 (lowercase English letters). -/
  theorem spec_1 (s : Slice U8) (k : I64) (hk : ValidInput s k) :
      ∀ r : I64, Aegis.PalindromePartition.palindrome_partition s k = ok r →
        r.val = ((minPartitionCost s k.val.toNat : Nat) : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s : Slice U8) (k : I64) (hk : ValidInput s k), ∀ r : I64, Aegis.PalindromePartition.palindrome_partition s k = ok r →
          r.val = ((minPartitionCost s k.val.toNat : Nat) : Int)) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r; it does not fail (in particular, no arithmetic overflow, no out-of-bounds slice access, and no panic).
    Preconditions: Let n = len(s). The input satisfies 1 <= k <= n <= 100 and every byte of s is in 97..122. -/
  theorem spec_2 (s : Slice U8) (k : I64) (hk : ValidInput s k) :
      ∃ r : I64, Aegis.PalindromePartition.palindrome_partition s k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s : Slice U8) (k : I64) (hk : ValidInput s k), ∃ r : I64, Aegis.PalindromePartition.palindrome_partition s k = ok r) := by
    sorry

  /-- Whenever the function returns a result r, r <= floor(n/2).
    Preconditions: Let n = len(s). The input satisfies 1 <= k <= n <= 100 and every byte of s is in 97..122. -/
  theorem spec_3 (s : Slice U8) (k : I64) (hk : ValidInput s k) :
      ∀ r : I64, Aegis.PalindromePartition.palindrome_partition s k = ok r →
        r.val ≤ ((s.val.length / 2 : Nat) : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s : Slice U8) (k : I64) (hk : ValidInput s k), ∀ r : I64, Aegis.PalindromePartition.palindrome_partition s k = ok r →
          r.val ≤ ((s.val.length / 2 : Nat) : Int)) := by
    sorry

  /-- Whenever the function returns a result r, r <= n - k.
    Preconditions: Let n = len(s). The input satisfies 1 <= k <= n <= 100 and every byte of s is in 97..122. -/
  theorem spec_4 (s : Slice U8) (k : I64) (hk : ValidInput s k) :
      ∀ r : I64, Aegis.PalindromePartition.palindrome_partition s k = ok r →
        r.val ≤ ((s.val.length : Int) - k.val) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s : Slice U8) (k : I64) (hk : ValidInput s k), ∀ r : I64, Aegis.PalindromePartition.palindrome_partition s k = ok r →
          r.val ≤ ((s.val.length : Int) - k.val)) := by
    sorry

  /-- Whenever the function returns a result r on input (s,k) and a result r' on input (rev,k), r = r'.
    Preconditions: Let n = len(s). The input satisfies 1 <= k <= n <= 100 and every byte of s is in 97..122. Let rev be the byte sequence of length n with rev[i] = s[n-1-i]; it satisfies the same constraints. -/
  theorem spec_5 (s : Slice U8) (k : I64) (hk : ValidInput s k) :
      ∀ r r' : I64, Aegis.PalindromePartition.palindrome_partition s k = ok r →
        Aegis.PalindromePartition.palindrome_partition (revSlice s) k = ok r' → r = r' := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s : Slice U8) (k : I64) (hk : ValidInput s k), ∀ r r' : I64, Aegis.PalindromePartition.palindrome_partition s k = ok r →
          Aegis.PalindromePartition.palindrome_partition (revSlice s) k = ok r' → r = r') := by
    sorry

  /-- Whenever the function returns a result r on input (s,k) and a result r' on input (t,k), r = r'.
    Preconditions: Let n = len(s). The input satisfies 1 <= k <= n <= 100 and every byte of s is in 97..122. Let t be another byte sequence of length n containing only bytes in 97..122 such that for all i,j with 0 <= i < n and 0 <= j < n, s[i] = s[j] if and only if t[i] = t[j]. -/
  theorem spec_6 (s t : Slice U8) (k : I64) (hs : ValidInput s k) (ht : ValidInput t k)
      (hpat : SamePattern s t) :
      ∀ r r' : I64, Aegis.PalindromePartition.palindrome_partition s k = ok r →
        Aegis.PalindromePartition.palindrome_partition t k = ok r' → r = r' := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s t : Slice U8) (k : I64) (hs : ValidInput s k) (ht : ValidInput t k)
        (hpat : SamePattern s t), ∀ r r' : I64, Aegis.PalindromePartition.palindrome_partition s k = ok r →
          Aegis.PalindromePartition.palindrome_partition t k = ok r' → r = r') := by
    sorry

  end AegisSpec.PalindromePartition
