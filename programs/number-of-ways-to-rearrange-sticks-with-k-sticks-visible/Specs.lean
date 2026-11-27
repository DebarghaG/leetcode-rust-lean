import Aegis.RearrangeSticks.Code.Funs

/-!
# Specifications of `Aegis.RearrangeSticks.rearrange_sticks`

LeetCode problem `number-of-ways-to-rearrange-sticks-with-k-sticks-visible`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.RearrangeSticks
open scoped BigOperators

namespace AegisSpec.RearrangeSticks

def MOD : Nat := 1000000007

def i64 (i : Int) : Aeneas.Std.I64 := ⟨BitVec.ofInt 64 i⟩

def residue (x : Int) : Int := x.emod (MOD : Int)

def IsVisible (p : List Nat) (i : Fin p.length) : Bool :=
  (List.finRange i.val).all fun j =>
    decide (p.get ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩ < p.get i)

def visibleCount (p : List Nat) : Nat :=
  List.countP (fun i => IsVisible p i) (List.finRange p.length)

def permutationsOfRange (n : Nat) : List (List Nat) :=
  ((List.range n).map (· + 1)).permutations

def permCount (n k : Nat) : Nat :=
  List.countP (fun p => decide (visibleCount p = k)) (permutationsOfRange n)

def binom (a b : Nat) : Nat := Nat.choose a b

def sumQuotients (m : Nat) : Nat :=
  Finset.sum (Finset.Icc 1 (m - 1)) (fun i => Nat.factorial (m - 1) / i)

/-- The function returns a result r and r is the canonical residue modulo M = 1000000007 of the number C(n,k) of permutations p of {1,2,...,n} that have exactly k visible sticks from the left, i.e. exactly k indices i with 0 <= i < n such that p[i] > p[j] for every j with 0 <= j < i. Thus 0 <= r <= M - 1 and r ≡ C(n,k) (mod M).
  Preconditions: n and k are integers with 1 <= n <= 1000 and 1 <= k <= n. -/
theorem spec_1 (n k : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ n.val) :
    ∃ r : Aeneas.Std.I64,
      rearrange_sticks n k = ok r ∧
        r.val = (((permCount n.val.toNat k.val.toNat) % MOD : Nat) : Int) ∧
        0 ≤ r.val ∧ r.val ≤ 1000000006 := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n k : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ n.val), ∃ r : Aeneas.Std.I64,
      rearrange_sticks n k = ok r ∧
        r.val = (((permCount n.val.toNat k.val.toNat) % MOD : Nat) : Int) ∧
        0 ≤ r.val ∧ r.val ≤ 1000000006) := by
  sorry

/-- Whenever n and k satisfy 1 <= n <= 1000 and 1 <= k <= n, the call rearrange_sticks(n,k) returns some result r (a successful Result.ok value); it does not fail, panic, or return an error.
  Preconditions: n and k are integers with 1 <= n <= 1000 and 1 <= k <= n. -/
theorem spec_2 (n k : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ n.val) :
    ∃ r : Aeneas.Std.I64, rearrange_sticks n k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n k : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ n.val), ∃ r : Aeneas.Std.I64, rearrange_sticks n k = ok r) := by
  sorry

/-- Whenever the function returns a result r for inputs satisfying 1 <= n <= 1000 and 1 <= k <= n, the returned integer r satisfies 0 <= r <= 1000000006.
  Preconditions: n and k are integers with 1 <= n <= 1000 and 1 <= k <= n. -/
theorem spec_3 (n k : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ n.val) :
    ∀ r : Aeneas.Std.I64, rearrange_sticks n k = ok r → 0 ≤ r.val ∧ r.val ≤ 1000000006 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n k : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ n.val), ∀ r : Aeneas.Std.I64, rearrange_sticks n k = ok r → 0 ≤ r.val ∧ r.val ≤ 1000000006) := by
  sorry

/-- The function returns r = 1.
  Preconditions: n is an integer with 1 <= n <= 1000 and k = n. -/
theorem spec_4 (n k : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000)
    (hk : k.val = n.val) :
    ∃ r : Aeneas.Std.I64, rearrange_sticks n k = ok r ∧ r.val = 1 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n k : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000)
    (hk : k.val = n.val), ∃ r : Aeneas.Std.I64, rearrange_sticks n k = ok r ∧ r.val = 1) := by
  sorry

/-- The function returns r = ((n-1)! mod 1000000007), represented as the canonical residue in [0,1000000006], where 0! = 1.
  Preconditions: n is an integer with 1 <= n <= 1000 and k = 1. -/
theorem spec_5 (n k : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000)
    (hk : k.val = 1) :
    ∃ r : Aeneas.Std.I64,
      rearrange_sticks n k = ok r ∧
        r.val = ((Nat.factorial (n.val.toNat - 1) % MOD : Nat) : Int) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n k : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000)
    (hk : k.val = 1), ∃ r : Aeneas.Std.I64,
      rearrange_sticks n k = ok r ∧
        r.val = ((Nat.factorial (n.val.toNat - 1) % MOD : Nat) : Int)) := by
  sorry

/-- The function returns r = (n*(n-1)/2) mod 1000000007, represented as the canonical residue in [0,1000000006].
  Preconditions: n is an integer with 2 <= n <= 1000 and k = n - 1. -/
theorem spec_6 (n k : Aeneas.Std.I64) (hn1 : 2 ≤ n.val) (hn2 : n.val ≤ 1000)
    (hk : k.val = n.val - 1) :
    ∃ r : Aeneas.Std.I64,
      rearrange_sticks n k = ok r ∧
        r.val = (((n.val.toNat * (n.val.toNat - 1)) / 2) % MOD : Nat) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n k : Aeneas.Std.I64) (hn1 : 2 ≤ n.val) (hn2 : n.val ≤ 1000)
    (hk : k.val = n.val - 1), ∃ r : Aeneas.Std.I64,
      rearrange_sticks n k = ok r ∧
        r.val = (((n.val.toNat * (n.val.toNat - 1)) / 2) % MOD : Nat)) := by
  sorry

/-- Let S = sum_{i=1}^{n-1} ((n-1)! / i), where each division is the exact integer quotient. The function returns r = (S mod 1000000007), represented as the canonical residue in [0,1000000006].
  Preconditions: n is an integer with 2 <= n <= 1000 and k = 2. -/
theorem spec_7 (n k : Aeneas.Std.I64) (hn1 : 2 ≤ n.val) (hn2 : n.val ≤ 1000)
    (hk : k.val = 2) :
    ∃ r : Aeneas.Std.I64,
      rearrange_sticks n k = ok r ∧
        r.val = (((sumQuotients n.val.toNat) % MOD : Nat) : Int) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n k : Aeneas.Std.I64) (hn1 : 2 ≤ n.val) (hn2 : n.val ≤ 1000)
    (hk : k.val = 2), ∃ r : Aeneas.Std.I64,
      rearrange_sticks n k = ok r ∧
        r.val = (((sumQuotients n.val.toNat) % MOD : Nat) : Int)) := by
  sorry

/-- Let r be the result of rearrange_sticks(n,k), let r_prev_1 be the result of rearrange_sticks(n-1,k-1), and let r_prev_2 be the result of rearrange_sticks(n-1,k). Then r = (r_prev_1 + (n-1)*r_prev_2) mod 1000000007, represented as the canonical residue in [0,1000000006].
  Preconditions: n and k are integers with 2 <= n <= 1000 and 2 <= k <= n - 1. -/
theorem spec_8 (n k : Aeneas.Std.I64) (hn1 : 2 ≤ n.val) (hn2 : n.val ≤ 1000)
    (hk1 : 2 ≤ k.val) (hk2 : k.val ≤ n.val - 1) :
    ∀ r r₁ r₂ : Aeneas.Std.I64,
      rearrange_sticks n k = ok r →
        rearrange_sticks (i64 (n.val - 1)) (i64 (k.val - 1)) = ok r₁ →
          rearrange_sticks (i64 (n.val - 1)) k = ok r₂ →
            r.val = residue (r₁.val + (n.val - 1) * r₂.val) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n k : Aeneas.Std.I64) (hn1 : 2 ≤ n.val) (hn2 : n.val ≤ 1000)
    (hk1 : 2 ≤ k.val) (hk2 : k.val ≤ n.val - 1), ∀ r r₁ r₂ : Aeneas.Std.I64,
      rearrange_sticks n k = ok r →
        rearrange_sticks (i64 (n.val - 1)) (i64 (k.val - 1)) = ok r₁ →
          rearrange_sticks (i64 (n.val - 1)) k = ok r₂ →
            r.val = residue (r₁.val + (n.val - 1) * r₂.val)) := by
  sorry

/-- For every k with 1 <= k <= n, let r_k be the result of rearrange_sticks(n,k). Then (sum_{k=1}^{n} r_k) mod 1000000007 = (n! mod 1000000007), and both sides are interpreted as canonical residues in [0,1000000006].
  Preconditions: n is an integer with 1 <= n <= 1000. -/
theorem spec_9 (n : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000) :
    ∃ rs : Nat → Int,
      (∀ k : Nat, 1 ≤ k → k ≤ n.val.toNat →
          ∃ r : Aeneas.Std.I64,
            rearrange_sticks n (i64 (k : Int)) = ok r ∧ rs k = r.val) ∧
        residue (Finset.sum (Finset.Icc 1 n.val.toNat) rs) =
          residue ((Nat.factorial n.val.toNat : Nat) : Int) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000), ∃ rs : Nat → Int,
      (∀ k : Nat, 1 ≤ k → k ≤ n.val.toNat →
          ∃ r : Aeneas.Std.I64,
            rearrange_sticks n (i64 (k : Int)) = ok r ∧ rs k = r.val) ∧
        residue (Finset.sum (Finset.Icc 1 n.val.toNat) rs) =
          residue ((Nat.factorial n.val.toNat : Nat) : Int)) := by
  sorry

/-- Let binom(a,b) denote the binomial coefficient, with binom(a,b) = 0 when b < 0 or b > a. The function returns r = (2*binom(n,3) + 3*binom(n,4)) mod 1000000007, represented as the canonical residue in [0,1000000006].
  Preconditions: n is an integer with 3 <= n <= 1000 and k = n - 2. -/
theorem spec_10 (n k : Aeneas.Std.I64) (hn1 : 3 ≤ n.val) (hn2 : n.val ≤ 1000)
    (hk : k.val = n.val - 2) :
    ∃ r : Aeneas.Std.I64,
      rearrange_sticks n k = ok r ∧
        r.val = (((2 * binom n.val.toNat 3 + 3 * binom n.val.toNat 4) % MOD : Nat) : Int) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n k : Aeneas.Std.I64) (hn1 : 3 ≤ n.val) (hn2 : n.val ≤ 1000)
    (hk : k.val = n.val - 2), ∃ r : Aeneas.Std.I64,
      rearrange_sticks n k = ok r ∧
        r.val = (((2 * binom n.val.toNat 3 + 3 * binom n.val.toNat 4) % MOD : Nat) : Int)) := by
  sorry

end AegisSpec.RearrangeSticks
