import Aegis.NumberOfSets.Code.Funs

/-!
# Specifications of `Aegis.NumberOfSets.number_of_sets`

LeetCode problem `number-of-sets-of-k-non-overlapping-line-segments`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AegisSpec.NumberOfSets

abbrev M : ℤ := 1000000007

abbrev Segment (n : ℕ) : Type := {p : Fin n × Fin n // p.1 < p.2}

namespace Segment

variable {n : ℕ}

abbrev left (s : Segment n) : ℕ := (s.1.1 : ℕ)

abbrev right (s : Segment n) : ℕ := (s.1.2 : ℕ)

end Segment

abbrev NonOverlapping {n : ℕ} (s t : Segment n) : Prop :=
  s.right ≤ t.left ∨ t.right ≤ s.left

abbrev IsSegmentSet (n k : ℕ) (T : Finset (Segment n)) : Prop :=
  T.card = k ∧ ∀ s ∈ T, ∀ t ∈ T, s ≠ t → NonOverlapping s t

section

attribute [local instance] Finset.decidableDforallFinset

def Cnt (n k : ℕ) : ℕ :=
  ((Finset.univ : Finset (Finset (Segment n))).filter (fun T => IsSegmentSet n k T)).card

end

def Fib : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | m + 2 => Fib (m + 1) + Fib m

def i64OfNat (m : ℕ) : Std.I64 := ⟨BitVec.ofNat 64 m⟩

def Returns (n k : Std.I64) (v : ℤ) : Prop :=
  ∃ r : Std.I64, Aegis.NumberOfSets.number_of_sets n k = ok r ∧ r.val = v

/-- Let M = 1000000007. For these n,k, define Cnt(n,k) as follows. A segment over the points {0,1,...,n-1} is a pair (a,b) of integers with 0 <= a < b <= n-1. Two segments (a,b) and (c,d) are non-overlapping if b <= c or d <= a; thus sharing an endpoint is allowed. Cnt(n,k) is the number of sets T of exactly k pairwise non-overlapping segments over {0,1,...,n-1}, where T is an unordered set of distinct segments. Whenever the function returns a result r on these inputs, r is the unique integer with 0 <= r < M and r congruent to Cnt(n,k) modulo M.
  Preconditions: n and k are i64 values with 2 <= n <= 1000 and 1 <= k <= n-1. -/
theorem spec_1 (n k : Std.I64)
    (hn : 2 ≤ n.val) (hn_ub : n.val ≤ 1000) (hk : 1 ≤ k.val) (hk_ub : k.val ≤ n.val - 1) :
    ∀ r : Std.I64, Aegis.NumberOfSets.number_of_sets n k = ok r →
      0 ≤ r.val ∧ r.val < M ∧
        r.val ≡ (Cnt n.val.toNat k.val.toNat : ℤ) [ZMOD M] ∧
        (∀ s : ℤ, 0 ≤ s → s < M → s ≡ (Cnt n.val.toNat k.val.toNat : ℤ) [ZMOD M] →
          s = r.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n k : Std.I64)
    (hn : 2 ≤ n.val) (hn_ub : n.val ≤ 1000) (hk : 1 ≤ k.val) (hk_ub : k.val ≤ n.val - 1), ∀ r : Std.I64, Aegis.NumberOfSets.number_of_sets n k = ok r →
      0 ≤ r.val ∧ r.val < M ∧
        r.val ≡ (Cnt n.val.toNat k.val.toNat : ℤ) [ZMOD M] ∧
        (∀ s : ℤ, 0 ≤ s → s < M → s ≡ (Cnt n.val.toNat k.val.toNat : ℤ) [ZMOD M] →
          s = r.val)) := by
  sorry

/-- For every n and k satisfying the preconditions, the function returns a result r (it does not fail).
  Preconditions: n and k are i64 values with 2 <= n <= 1000 and 1 <= k <= n-1. -/
theorem spec_2 (n k : Std.I64)
    (hn : 2 ≤ n.val) (hn_ub : n.val ≤ 1000) (hk : 1 ≤ k.val) (hk_ub : k.val ≤ n.val - 1) :
    ∃ r : Std.I64, Aegis.NumberOfSets.number_of_sets n k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n k : Std.I64)
    (hn : 2 ≤ n.val) (hn_ub : n.val ≤ 1000) (hk : 1 ≤ k.val) (hk_ub : k.val ≤ n.val - 1), ∃ r : Std.I64, Aegis.NumberOfSets.number_of_sets n k = ok r) := by
  sorry

/-- Whenever the function returns a result r on inputs satisfying the preconditions, 0 <= r < 1000000007.
  Preconditions: n and k are i64 values with 2 <= n <= 1000 and 1 <= k <= n-1. -/
theorem spec_3 (n k : Std.I64)
    (hn : 2 ≤ n.val) (hn_ub : n.val ≤ 1000) (hk : 1 ≤ k.val) (hk_ub : k.val ≤ n.val - 1) :
    ∀ r : Std.I64, Aegis.NumberOfSets.number_of_sets n k = ok r → 0 ≤ r.val ∧ r.val < M := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n k : Std.I64)
    (hn : 2 ≤ n.val) (hn_ub : n.val ≤ 1000) (hk : 1 ≤ k.val) (hk_ub : k.val ≤ n.val - 1), ∀ r : Std.I64, Aegis.NumberOfSets.number_of_sets n k = ok r → 0 ≤ r.val ∧ r.val < M) := by
  sorry

/-- Whenever the function returns a result r on inputs satisfying the preconditions, r is not equal to 0.
  Preconditions: n and k are i64 values with 2 <= n <= 1000 and 1 <= k <= n-1. -/
theorem spec_4 (n k : Std.I64)
    (hn : 2 ≤ n.val) (hn_ub : n.val ≤ 1000) (hk : 1 ≤ k.val) (hk_ub : k.val ≤ n.val - 1) :
    ∀ r : Std.I64, Aegis.NumberOfSets.number_of_sets n k = ok r → r.val ≠ 0 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n k : Std.I64)
    (hn : 2 ≤ n.val) (hn_ub : n.val ≤ 1000) (hk : 1 ≤ k.val) (hk_ub : k.val ≤ n.val - 1), ∀ r : Std.I64, Aegis.NumberOfSets.number_of_sets n k = ok r → r.val ≠ 0) := by
  sorry

/-- Whenever the function returns a result r on inputs satisfying the preconditions, r is congruent modulo M = 1000000007 to the binomial coefficient binom(n+k-1, 2k). Here binom(A,B) is the usual number of B-element subsets of an A-element set (and is 0 if B<0 or B>A).
  Preconditions: n and k are i64 values with 2 <= n <= 1000 and 1 <= k <= n-1. -/
theorem spec_5 (n k : Std.I64)
    (hn : 2 ≤ n.val) (hn_ub : n.val ≤ 1000) (hk : 1 ≤ k.val) (hk_ub : k.val ≤ n.val - 1) :
    ∀ r : Std.I64, Aegis.NumberOfSets.number_of_sets n k = ok r →
      r.val ≡ (Nat.choose (n.val.toNat + k.val.toNat - 1) (2 * k.val.toNat) : ℤ) [ZMOD M] := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n k : Std.I64)
    (hn : 2 ≤ n.val) (hn_ub : n.val ≤ 1000) (hk : 1 ≤ k.val) (hk_ub : k.val ≤ n.val - 1), ∀ r : Std.I64, Aegis.NumberOfSets.number_of_sets n k = ok r →
      r.val ≡ (Nat.choose (n.val.toNat + k.val.toNat - 1) (2 * k.val.toNat) : ℤ) [ZMOD M]) := by
  sorry

/-- Whenever the function returns a result r, r = n*(n-1)/2 exactly (not merely modulo M).
  Preconditions: n is an i64 with 2 <= n <= 1000 and k = 1. -/
theorem spec_6 (n k : Std.I64)
    (hn : 2 ≤ n.val) (hn_ub : n.val ≤ 1000) (hk : k.val = 1) :
    ∀ r : Std.I64, Aegis.NumberOfSets.number_of_sets n k = ok r →
      r.val = n.val * (n.val - 1) / 2 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n k : Std.I64)
    (hn : 2 ≤ n.val) (hn_ub : n.val ≤ 1000) (hk : k.val = 1), ∀ r : Std.I64, Aegis.NumberOfSets.number_of_sets n k = ok r →
      r.val = n.val * (n.val - 1) / 2) := by
  sorry

/-- Whenever the function returns a result r, r = 1.
  Preconditions: n is an i64 with 2 <= n <= 1000 and k = n-1. -/
theorem spec_7 (n k : Std.I64)
    (hn : 2 ≤ n.val) (hn_ub : n.val ≤ 1000) (hk : k.val = n.val - 1) :
    ∀ r : Std.I64, Aegis.NumberOfSets.number_of_sets n k = ok r → r.val = 1 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n k : Std.I64)
    (hn : 2 ≤ n.val) (hn_ub : n.val ≤ 1000) (hk : k.val = n.val - 1), ∀ r : Std.I64, Aegis.NumberOfSets.number_of_sets n k = ok r → r.val = 1) := by
  sorry

/-- Whenever the function returns a result r, r = 2*n - 3.
  Preconditions: n is an i64 with 3 <= n <= 1000 and k = n-2. -/
theorem spec_8 (n k : Std.I64)
    (hn : 3 ≤ n.val) (hn_ub : n.val ≤ 1000) (hk : k.val = n.val - 2) :
    ∀ r : Std.I64, Aegis.NumberOfSets.number_of_sets n k = ok r → r.val = 2 * n.val - 3 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n k : Std.I64)
    (hn : 3 ≤ n.val) (hn_ub : n.val ≤ 1000) (hk : k.val = n.val - 2), ∀ r : Std.I64, Aegis.NumberOfSets.number_of_sets n k = ok r → r.val = 2 * n.val - 3) := by
  sorry

/-- Whenever the function returns a result r, r = 5.
  Preconditions: n = 4 and k = 2. -/
theorem spec_9 (n k : Std.I64) (hn : n.val = 4) (hk : k.val = 2) :
    ∀ r : Std.I64, Aegis.NumberOfSets.number_of_sets n k = ok r → r.val = 5 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n k : Std.I64) (hn : n.val = 4) (hk : k.val = 2), ∀ r : Std.I64, Aegis.NumberOfSets.number_of_sets n k = ok r → r.val = 5) := by
  sorry

/-- For each j with 1 <= j <= n-1, let r_j be the result returned by number_of_sets(n,j). Then (sum_{j=1}^{n-1} r_j) modulo 1000000007 equals (F_{2n-1} - 1) modulo 1000000007, where F_0 = 0, F_1 = 1, and F_{m+2} = F_{m+1} + F_m for all m >= 0.
  Preconditions: n is an i64 with 2 <= n <= 1000. -/
theorem spec_10 (n : Std.I64) (hn : 2 ≤ n.val) (hn_ub : n.val ≤ 1000) :
    ∀ rs : ℕ → ℤ,
      (∀ j : ℕ, 1 ≤ j → j ≤ n.val.toNat - 1 → Returns n (i64OfNat j) (rs j)) →
        (∑ j ∈ Finset.Icc 1 (n.val.toNat - 1), rs j) ≡
          ((Fib (2 * n.val.toNat - 1) : ℤ) - 1) [ZMOD M] := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n : Std.I64) (hn : 2 ≤ n.val) (hn_ub : n.val ≤ 1000), ∀ rs : ℕ → ℤ,
      (∀ j : ℕ, 1 ≤ j → j ≤ n.val.toNat - 1 → Returns n (i64OfNat j) (rs j)) →
        (∑ j ∈ Finset.Icc 1 (n.val.toNat - 1), rs j) ≡
          ((Fib (2 * n.val.toNat - 1) : ℤ) - 1) [ZMOD M]) := by
  sorry

/-- For each n with k+1 <= n <= N, let r_n be the result returned by number_of_sets(n,k). Then (sum_{n=k+1}^{N} r_n) modulo 1000000007 equals binom(N+k, 2k+1) modulo 1000000007, where binom(A,B) is the usual binomial coefficient.
  Preconditions: k and N are i64 values with 1 <= k <= 999 and k+1 <= N <= 1000. -/
theorem spec_11 (k N : Std.I64)
    (hk : 1 ≤ k.val) (hk_ub : k.val ≤ 999) (hN : k.val + 1 ≤ N.val) (hN_ub : N.val ≤ 1000) :
    ∀ rs : ℕ → ℤ,
      (∀ n : ℕ, k.val.toNat + 1 ≤ n → n ≤ N.val.toNat → Returns (i64OfNat n) k (rs n)) →
        (∑ n ∈ Finset.Icc (k.val.toNat + 1) N.val.toNat, rs n) ≡
          (Nat.choose (N.val.toNat + k.val.toNat) (2 * k.val.toNat) : ℤ) [ZMOD M] := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (k N : Std.I64)
    (hk : 1 ≤ k.val) (hk_ub : k.val ≤ 999) (hN : k.val + 1 ≤ N.val) (hN_ub : N.val ≤ 1000), ∀ rs : ℕ → ℤ,
      (∀ n : ℕ, k.val.toNat + 1 ≤ n → n ≤ N.val.toNat → Returns (i64OfNat n) k (rs n)) →
        (∑ n ∈ Finset.Icc (k.val.toNat + 1) N.val.toNat, rs n) ≡
          (Nat.choose (N.val.toNat + k.val.toNat) (2 * k.val.toNat) : ℤ) [ZMOD M]) := by
  sorry

/-- Whenever the function returns a result r, r = 70047606.
  Preconditions: n = 1000 and k = 500. -/
theorem spec_12 (n k : Std.I64) (hn : n.val = 1000) (hk : k.val = 500) :
    ∀ r : Std.I64, Aegis.NumberOfSets.number_of_sets n k = ok r → r.val = 70047606 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (n k : Std.I64) (hn : n.val = 1000) (hk : k.val = 500), ∀ r : Std.I64, Aegis.NumberOfSets.number_of_sets n k = ok r → r.val = 70047606) := by
  sorry

end AegisSpec.NumberOfSets
