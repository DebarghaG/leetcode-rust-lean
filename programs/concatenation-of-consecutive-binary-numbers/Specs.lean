import Aegis.ConcatenatedBinary.Code.Funs

/-!
# Specifications of `Aegis.ConcatenatedBinary.concatenated_binary`

LeetCode problem `concatenation-of-consecutive-binary-numbers`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.ConcatenatedBinary

  def bits (n : Nat) : Nat := Nat.log2 n + 1

  def binaryConcat : Nat → Nat
    | 0 => 0
    | k + 1 => binaryConcat k * 2 ^ bits (k + 1) + (k + 1)

  /-- The function returns a result r. Let C be the exact integer obtained by concatenating, in order, the binary representations of 1,2,...,n, each with no leading zeros. Then r is the unique integer satisfying 0 <= r < 1000000007 and C = q * 1000000007 + r for some nonnegative integer q. Equivalently, r = C mod 1000000007.
    Preconditions: n is a Std.I64 with 1 <= n <= 100000. -/
  theorem spec_1 (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 100000) :
      ∃ r : Std.I64,
        Aegis.ConcatenatedBinary.concatenated_binary n = ok r ∧
        0 ≤ r.val ∧
        r.val < 1000000007 ∧
        (∃ q : ℤ, 0 ≤ q ∧
          (binaryConcat n.val.toNat : ℤ) = q * 1000000007 + r.val) ∧
        (∀ r' : ℤ, 0 ≤ r' → r' < 1000000007 →
          (∃ q : ℤ, 0 ≤ q ∧
            (binaryConcat n.val.toNat : ℤ) = q * 1000000007 + r') →
          r' = r.val) ∧
        r.val = (binaryConcat n.val.toNat : ℤ) % 1000000007 := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 100000), ∃ r : Std.I64,
          Aegis.ConcatenatedBinary.concatenated_binary n = ok r ∧
          0 ≤ r.val ∧
          r.val < 1000000007 ∧
          (∃ q : ℤ, 0 ≤ q ∧
            (binaryConcat n.val.toNat : ℤ) = q * 1000000007 + r.val) ∧
          (∀ r' : ℤ, 0 ≤ r' → r' < 1000000007 →
            (∃ q : ℤ, 0 ≤ q ∧
              (binaryConcat n.val.toNat : ℤ) = q * 1000000007 + r') →
            r' = r.val) ∧
          r.val = (binaryConcat n.val.toNat : ℤ) % 1000000007) := by
    sorry

  /-- For every n with 1 <= n <= 100000, the function returns a result r; it does not panic and does not report overflow.
    Preconditions: n is a Std.I64 with 1 <= n <= 100000. -/
  theorem spec_2 (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 100000) :
      ∃ r : Std.I64, Aegis.ConcatenatedBinary.concatenated_binary n = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 100000), ∃ r : Std.I64, Aegis.ConcatenatedBinary.concatenated_binary n = ok r) := by
    sorry

  /-- Whenever the function returns q on input n-1 and r on input n, r = (q * 2^(bits(n)) + n) mod 1000000007.
    Preconditions: n is a Std.I64 with 2 <= n <= 100000. Let q be the result returned by the function on input n-1, and let r be the result returned on input n. Let bits(n) be the number of bits in the binary representation of n, i.e. the unique positive integer b with 2^(b-1) <= n < 2^b. -/
  theorem spec_3 (n m : Std.I64) (hlo : 2 ≤ n.val) (hhi : n.val ≤ 100000)
      (hm : m.val = n.val - 1) :
      ∀ q r : Std.I64,
        Aegis.ConcatenatedBinary.concatenated_binary m = ok q →
        Aegis.ConcatenatedBinary.concatenated_binary n = ok r →
        r.val = (q.val * (2 : ℤ) ^ (bits n.val.toNat) + n.val) % 1000000007 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n m : Std.I64) (hlo : 2 ≤ n.val) (hhi : n.val ≤ 100000)
        (hm : m.val = n.val - 1), ∀ q r : Std.I64,
          Aegis.ConcatenatedBinary.concatenated_binary m = ok q →
          Aegis.ConcatenatedBinary.concatenated_binary n = ok r →
          r.val = (q.val * (2 : ℤ) ^ (bits n.val.toNat) + n.val) % 1000000007) := by
    sorry

  end AegisSpec.ConcatenatedBinary
