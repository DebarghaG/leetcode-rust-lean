import Aegis.ReinitializePermutation.Code.Funs

/-!
# Specifications of `Aegis.ReinitializePermutation.reinitialize_permutation`

LeetCode problem `minimum-number-of-operations-to-reinitialize-a-permutation`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.ReinitializePermutation

  def shuffle (n : Nat) (i : Nat) : Nat :=
    if i % 2 = 0 then i / 2 else n / 2 + (i - 1) / 2

  def shufflePow (n : Nat) (k : Nat) (i : Nat) : Nat := (shuffle n)^[k] i

  def fixedBy (n : Nat) (k : Nat) (i : Nat) : Prop := (shuffle n)^[k] i = i

  def cycleLength (n i : Nat) : Nat :=
    ((List.range (n + 2)).find? (fun k => decide (0 < k ∧ (shuffle n)^[k] i = i))).getD 0

  def cycleLcm (n : Nat) : Nat :=
    ((List.range n).filter (fun i => decide (0 < i))).map (cycleLength n) |>.foldr Nat.lcm 1

  def totient (m : Nat) : Nat :=
    ((List.range m).filter (fun i => decide (Nat.gcd (i + 1) m = 1))).length

  /-- The function returns a result r, and r is the smallest positive integer k such that for every integer i with 0 <= i < n, f_n^k(i) = i, where f_n: {0,1,...,n-1} -> {0,1,...,n-1} is defined by: f_n(i) = i/2 if i is even, and f_n(i) = n/2 + (i-1)/2 if i is odd. Here integer division is used for i/2 and (i-1)/2, and f_n^k denotes the k-fold composition of f_n with itself (with f_n^0 being the identity function).
    Preconditions: n is an integer with 2 <= n <= 1000 and n is even. -/
  theorem spec_1 (n : Std.I64) (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 1000)
      (hn_even : n.val % 2 = 0) :
      ∃ r : Std.I64,
        Aegis.ReinitializePermutation.reinitialize_permutation n = Result.ok r ∧
          0 < r.val ∧
          (∀ i : Nat, i < n.val.toNat → (shuffle n.val.toNat)^[r.val.toNat] i = i) ∧
          (∀ k : Nat, 0 < k →
            (∀ i : Nat, i < n.val.toNat → (shuffle n.val.toNat)^[k] i = i) → r.val.toNat ≤ k) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : Std.I64) (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 1000)
        (hn_even : n.val % 2 = 0), ∃ r : Std.I64,
          Aegis.ReinitializePermutation.reinitialize_permutation n = Result.ok r ∧
            0 < r.val ∧
            (∀ i : Nat, i < n.val.toNat → (shuffle n.val.toNat)^[r.val.toNat] i = i) ∧
            (∀ k : Nat, 0 < k →
              (∀ i : Nat, i < n.val.toNat → (shuffle n.val.toNat)^[k] i = i) → r.val.toNat ≤ k)) := by
    sorry

  /-- For every n with 2 <= n <= 1000 and n even, the function returns a result r (i.e., it does not fail, overflow, or panic).
    Preconditions: n is an integer with 2 <= n <= 1000 and n is even. -/
  theorem spec_2 (n : Std.I64) (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 1000)
      (hn_even : n.val % 2 = 0) :
      ∃ r : Std.I64, Aegis.ReinitializePermutation.reinitialize_permutation n = Result.ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : Std.I64) (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 1000)
        (hn_even : n.val % 2 = 0), ∃ r : Std.I64, Aegis.ReinitializePermutation.reinitialize_permutation n = Result.ok r) := by
    sorry

  /-- Whenever the function returns a result r, we have r <= n-1.
    Preconditions: n is an integer with 2 <= n <= 1000 and n is even. -/
  theorem spec_3 (n : Std.I64) (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 1000)
      (hn_even : n.val % 2 = 0) (r : Std.I64)
      (h : Aegis.ReinitializePermutation.reinitialize_permutation n = Result.ok r) :
      r.val ≤ n.val - 1 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : Std.I64) (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 1000)
        (hn_even : n.val % 2 = 0) (r : Std.I64)
        (h : Aegis.ReinitializePermutation.reinitialize_permutation n = Result.ok r), r.val ≤ n.val - 1) := by
    sorry

  /-- Whenever the function returns a result r, r is the smallest positive integer k such that 2^k ≡ 1 (mod n-1). (For n=2, n-1=1, and the smallest positive k satisfying the congruence modulo 1 is k=1.)
    Preconditions: n is an integer with 2 <= n <= 1000 and n is even. -/
  theorem spec_4 (n : Std.I64) (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 1000)
      (hn_even : n.val % 2 = 0) (r : Std.I64)
      (h : Aegis.ReinitializePermutation.reinitialize_permutation n = Result.ok r) :
      0 < r.val ∧
        2 ^ r.val.toNat % (n.val.toNat - 1) = 1 % (n.val.toNat - 1) ∧
        (∀ k : Nat, 0 < k →
          2 ^ k % (n.val.toNat - 1) = 1 % (n.val.toNat - 1) → r.val.toNat ≤ k) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : Std.I64) (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 1000)
        (hn_even : n.val % 2 = 0) (r : Std.I64)
        (h : Aegis.ReinitializePermutation.reinitialize_permutation n = Result.ok r), 0 < r.val ∧
          2 ^ r.val.toNat % (n.val.toNat - 1) = 1 % (n.val.toNat - 1) ∧
          (∀ k : Nat, 0 < k →
            2 ^ k % (n.val.toNat - 1) = 1 % (n.val.toNat - 1) → r.val.toNat ≤ k)) := by
    sorry

  /-- Whenever the function returns a result r, we have 2^r ≡ 1 (mod n-1).
    Preconditions: n is an integer with 2 <= n <= 1000 and n is even. -/
  theorem spec_5 (n : Std.I64) (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 1000)
      (hn_even : n.val % 2 = 0) (r : Std.I64)
      (h : Aegis.ReinitializePermutation.reinitialize_permutation n = Result.ok r) :
      2 ^ r.val.toNat % (n.val.toNat - 1) = 1 % (n.val.toNat - 1) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : Std.I64) (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 1000)
        (hn_even : n.val % 2 = 0) (r : Std.I64)
        (h : Aegis.ReinitializePermutation.reinitialize_permutation n = Result.ok r), 2 ^ r.val.toNat % (n.val.toNat - 1) = 1 % (n.val.toNat - 1)) := by
    sorry

  /-- Whenever the function returns a result r, for every integer k with 0 < k < r, we have 2^k mod (n-1) ≠ 1 mod (n-1).
    Preconditions: n is an integer with 2 <= n <= 1000 and n is even. -/
  theorem spec_6 (n : Std.I64) (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 1000)
      (hn_even : n.val % 2 = 0) (r : Std.I64)
      (h : Aegis.ReinitializePermutation.reinitialize_permutation n = Result.ok r) :
      ∀ k : Nat, 0 < k → k < r.val.toNat →
        2 ^ k % (n.val.toNat - 1) ≠ 1 % (n.val.toNat - 1) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n : Std.I64) (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 1000)
        (hn_even : n.val % 2 = 0) (r : Std.I64)
        (h : Aegis.ReinitializePermutation.reinitialize_permutation n = Result.ok r), ∀ k : Nat, 0 < k → k < r.val.toNat →
          2 ^ k % (n.val.toNat - 1) ≠ 1 % (n.val.toNat - 1)) := by
    sorry

  /-- Whenever the function returns a result r, r is the length of the cycle containing the integer 1 under the permutation f_n defined in spec_1. That is, r is the smallest positive integer k such that f_n^k(1) = 1.
    Preconditions: n is an integer with 2 <= n <= 1000 and n is even. -/
  theorem spec_7 (n : Std.I64) (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 1000)
      (hn_even : n.val % 2 = 0) (r : Std.I64)
      (h : Aegis.ReinitializePermutation.reinitialize_permutation n = Result.ok r) :
      0 < r.val ∧
        (shuffle n.val.toNat)^[r.val.toNat] 1 = 1 ∧
        (∀ k : Nat, 0 < k → (shuffle n.val.toNat)^[k] 1 = 1 → r.val.toNat ≤ k) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n : Std.I64) (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 1000)
        (hn_even : n.val % 2 = 0) (r : Std.I64)
        (h : Aegis.ReinitializePermutation.reinitialize_permutation n = Result.ok r), 0 < r.val ∧
          (shuffle n.val.toNat)^[r.val.toNat] 1 = 1 ∧
          (∀ k : Nat, 0 < k → (shuffle n.val.toNat)^[k] 1 = 1 → r.val.toNat ≤ k)) := by
    sorry

  /-- Whenever the function returns a result r, r is the least common multiple of the lengths of all cycles of the permutation f_n on the set {1,2,...,n-1}. (The element 0 is fixed and its cycle length 1 does not affect the LCM.)
    Preconditions: n is an integer with 2 <= n <= 1000 and n is even. -/
  theorem spec_8 (n : Std.I64) (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 1000)
      (hn_even : n.val % 2 = 0) (r : Std.I64)
      (h : Aegis.ReinitializePermutation.reinitialize_permutation n = Result.ok r) :
      r.val.toNat = cycleLcm n.val.toNat := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n : Std.I64) (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 1000)
        (hn_even : n.val % 2 = 0) (r : Std.I64)
        (h : Aegis.ReinitializePermutation.reinitialize_permutation n = Result.ok r), r.val.toNat = cycleLcm n.val.toNat) := by
    sorry

  /-- Whenever the function returns a result r, r divides φ(n-1), where φ(m) is the number of integers in {1,2,...,m} that are coprime to m (Euler's totient function).
    Preconditions: n is an integer with 2 <= n <= 1000 and n is even. -/
  theorem spec_9 (n : Std.I64) (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 1000)
      (hn_even : n.val % 2 = 0) (r : Std.I64)
      (h : Aegis.ReinitializePermutation.reinitialize_permutation n = Result.ok r) :
      r.val.toNat ∣ totient (n.val.toNat - 1) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n : Std.I64) (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 1000)
        (hn_even : n.val % 2 = 0) (r : Std.I64)
        (h : Aegis.ReinitializePermutation.reinitialize_permutation n = Result.ok r), r.val.toNat ∣ totient (n.val.toNat - 1)) := by
    sorry

  /-- Whenever the function returns a result r, applying the operation r times to the identity permutation of size n yields the identity permutation. Formally, for every integer i with 0 <= i < n, f_n^r(i) = i.
    Preconditions: n is an integer with 2 <= n <= 1000 and n is even. -/
  theorem spec_10 (n : Std.I64) (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 1000)
      (hn_even : n.val % 2 = 0) (r : Std.I64)
      (h : Aegis.ReinitializePermutation.reinitialize_permutation n = Result.ok r) :
      ∀ i : Nat, i < n.val.toNat → (shuffle n.val.toNat)^[r.val.toNat] i = i := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n : Std.I64) (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 1000)
        (hn_even : n.val % 2 = 0) (r : Std.I64)
        (h : Aegis.ReinitializePermutation.reinitialize_permutation n = Result.ok r), ∀ i : Nat, i < n.val.toNat → (shuffle n.val.toNat)^[r.val.toNat] i = i) := by
    sorry

  /-- Whenever the function returns a result r, for every integer k with 0 < k < r, there exists an integer i with 0 <= i < n such that f_n^k(i) ≠ i.
    Preconditions: n is an integer with 2 <= n <= 1000 and n is even. -/
  theorem spec_11 (n : Std.I64) (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 1000)
      (hn_even : n.val % 2 = 0) (r : Std.I64)
      (h : Aegis.ReinitializePermutation.reinitialize_permutation n = Result.ok r) :
      ∀ k : Nat, 0 < k → k < r.val.toNat →
        ∃ i : Nat, i < n.val.toNat ∧ (shuffle n.val.toNat)^[k] i ≠ i := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (n : Std.I64) (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 1000)
        (hn_even : n.val % 2 = 0) (r : Std.I64)
        (h : Aegis.ReinitializePermutation.reinitialize_permutation n = Result.ok r), ∀ k : Nat, 0 < k → k < r.val.toNat →
          ∃ i : Nat, i < n.val.toNat ∧ (shuffle n.val.toNat)^[k] i ≠ i) := by
    sorry

  end AegisSpec.ReinitializePermutation
