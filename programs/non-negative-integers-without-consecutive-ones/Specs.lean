import Aegis.FindIntegers.Code.Funs

/-!
# Specifications of `Aegis.FindIntegers.find_integers`

LeetCode problem `non-negative-integers-without-consecutive-ones`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.FindIntegers

  def hasTwoAdjacentOnes (k : ℕ) : Bool :=
    (List.range (k + 1)).any fun i => k.testBit i && k.testBit (i + 1)

  def Good (k : ℕ) : Prop := hasTwoAdjacentOnes k = false

  def Bad (k : ℕ) : Prop := hasTwoAdjacentOnes k = true

  instance : DecidablePred Good := fun k => by
    dsimp only [Good]
    infer_instance

  instance : DecidablePred Bad := fun k => by
    dsimp only [Bad]
    infer_instance

  def countGood (N : ℕ) : ℕ := ((Finset.range (N + 1)).filter Good).card

  def countBad (N : ℕ) : ℕ := ((Finset.range (N + 1)).filter Bad).card

  def fib : ℕ → ℕ
    | 0 => 0
    | 1 => 1
    | n + 2 => fib (n + 1) + fib n

  /-- Let an integer k ≥ 0 be called good if its binary representation, written without leading zeros and with 0 represented as '0', contains no occurrence of two consecutive 1 bits. Let C(N) be the number of good integers k with 0 ≤ k ≤ N. Whenever find_integers(n) returns a result r, the mathematical integer R represented by r satisfies R = C(N).
    Preconditions: The machine integer n represents an integer N with 1 ≤ N ≤ 1000000000. -/
  theorem spec_1 (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 1000000000)
      (r : Std.I64) (hr : Aegis.FindIntegers.find_integers n = ok r) :
      r.val = (countGood n.val.toNat : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 1000000000)
        (r : Std.I64) (hr : Aegis.FindIntegers.find_integers n = ok r), r.val = (countGood n.val.toNat : ℤ)) := by
    sorry

  /-- For every machine integer n satisfying the precondition, find_integers(n) returns a result r; it does not fail, panic, or overflow.
    Preconditions: The machine integer n represents an integer N with 1 ≤ N ≤ 1000000000. -/
  theorem spec_2 (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 1000000000) :
      ∃ r : Std.I64, Aegis.FindIntegers.find_integers n = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 1000000000), ∃ r : Std.I64, Aegis.FindIntegers.find_integers n = ok r) := by
    sorry

  /-- Whenever find_integers(n) returns a result r, the integer value R of r satisfies 1 ≤ R ≤ N + 1.
    Preconditions: The machine integer n represents an integer N with 1 ≤ N ≤ 1000000000. -/
  theorem spec_3 (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 1000000000)
      (r : Std.I64) (hr : Aegis.FindIntegers.find_integers n = ok r) :
      1 ≤ r.val ∧ r.val ≤ n.val + 1 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 1000000000)
        (r : Std.I64) (hr : Aegis.FindIntegers.find_integers n = ok r), 1 ≤ r.val ∧ r.val ≤ n.val + 1) := by
    sorry

  /-- Whenever find_integers(n) returns a result r, the integer value R of r satisfies R = F_{m+2} + 1, where F_0 = 0, F_1 = 1, and F_{j+2} = F_{j+1} + F_j for all j ≥ 0.
    Preconditions: The machine integer n represents N = 2^m for some integer m with 0 ≤ m ≤ 29. -/
  theorem spec_4 (n : Std.I64) (m : ℕ) (hn : n.val = (2 : ℤ) ^ m) (hm : m ≤ 29)
      (r : Std.I64) (hr : Aegis.FindIntegers.find_integers n = ok r) :
      r.val = (fib (m + 2) : ℤ) + 1 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : Std.I64) (m : ℕ) (hn : n.val = (2 : ℤ) ^ m) (hm : m ≤ 29)
        (r : Std.I64) (hr : Aegis.FindIntegers.find_integers n = ok r), r.val = (fib (m + 2) : ℤ) + 1) := by
    sorry

  /-- If find_integers(n1) returns a result r1 and find_integers(n2) returns a result r2, then the integer values R1 and R2 satisfy R1 ≤ R2.
    Preconditions: n1 and n2 are machine integers representing integers N1 and N2 with 1 ≤ N1 ≤ N2 ≤ 1000000000. -/
  theorem spec_5 (n1 n2 : Std.I64) (hlo : 1 ≤ n1.val) (hle : n1.val ≤ n2.val)
      (hhi : n2.val ≤ 1000000000)
      (r1 r2 : Std.I64) (hr1 : Aegis.FindIntegers.find_integers n1 = ok r1)
      (hr2 : Aegis.FindIntegers.find_integers n2 = ok r2) :
      r1.val ≤ r2.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n1 n2 : Std.I64) (hlo : 1 ≤ n1.val) (hle : n1.val ≤ n2.val)
        (hhi : n2.val ≤ 1000000000)
        (r1 r2 : Std.I64) (hr1 : Aegis.FindIntegers.find_integers n1 = ok r1)
        (hr2 : Aegis.FindIntegers.find_integers n2 = ok r2), r1.val ≤ r2.val) := by
    sorry

  /-- Let an integer k ≥ 0 be good if its binary representation, written without leading zeros and with 0 represented as '0', contains no two consecutive 1 bits. If find_integers(n) returns a result r and find_integers(n2) returns a result r2, then the integer values R and R2 satisfy R2 - R = 1 when N+1 is good, and R2 - R = 0 when N+1 is not good.
    Preconditions: n and n2 are machine integers representing N and N+1, where 1 ≤ N < 1000000000. -/
  theorem spec_6 (n n2 : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val < 1000000000)
      (hn2 : n2.val = n.val + 1)
      (r r2 : Std.I64) (hr : Aegis.FindIntegers.find_integers n = ok r)
      (hr2 : Aegis.FindIntegers.find_integers n2 = ok r2) :
      (Good (n.val + 1).toNat → r2.val - r.val = 1) ∧
        (¬ Good (n.val + 1).toNat → r2.val - r.val = 0) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n n2 : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val < 1000000000)
        (hn2 : n2.val = n.val + 1)
        (r r2 : Std.I64) (hr : Aegis.FindIntegers.find_integers n = ok r)
        (hr2 : Aegis.FindIntegers.find_integers n2 = ok r2), (Good (n.val + 1).toNat → r2.val - r.val = 1) ∧
          (¬ Good (n.val + 1).toNat → r2.val - r.val = 0)) := by
    sorry

  /-- Let bad(k) mean that the binary representation of k, written without leading zeros and with 0 represented as '0', contains at least one occurrence of two consecutive 1 bits. Let B(N) be the number of integers k with 0 ≤ k ≤ N for which bad(k) holds. Whenever find_integers(n) returns a result r with integer value R, we have R + B(N) = N + 1.
    Preconditions: The machine integer n represents an integer N with 1 ≤ N ≤ 1000000000. -/
  theorem spec_7 (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 1000000000)
      (r : Std.I64) (hr : Aegis.FindIntegers.find_integers n = ok r) :
      r.val + (countBad n.val.toNat : ℤ) = n.val + 1 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 1000000000)
        (r : Std.I64) (hr : Aegis.FindIntegers.find_integers n = ok r), r.val + (countBad n.val.toNat : ℤ) = n.val + 1) := by
    sorry

  /-- If find_integers(n1) returns a result r1 and find_integers(n2) returns a result r2, then the integer values R1 and R2 satisfy R2 - R1 ≤ N2 - N1.
    Preconditions: n1 and n2 are machine integers representing integers N1 and N2 with 1 ≤ N1 ≤ N2 ≤ 1000000000. -/
  theorem spec_8 (n1 n2 : Std.I64) (hlo : 1 ≤ n1.val) (hle : n1.val ≤ n2.val)
      (hhi : n2.val ≤ 1000000000)
      (r1 r2 : Std.I64) (hr1 : Aegis.FindIntegers.find_integers n1 = ok r1)
      (hr2 : Aegis.FindIntegers.find_integers n2 = ok r2) :
      r2.val - r1.val ≤ n2.val - n1.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n1 n2 : Std.I64) (hlo : 1 ≤ n1.val) (hle : n1.val ≤ n2.val)
        (hhi : n2.val ≤ 1000000000)
        (r1 r2 : Std.I64) (hr1 : Aegis.FindIntegers.find_integers n1 = ok r1)
        (hr2 : Aegis.FindIntegers.find_integers n2 = ok r2), r2.val - r1.val ≤ n2.val - n1.val) := by
    sorry

  /-- Whenever find_integers(n) returns a result r, the integer value R of r satisfies R = F_{m+2}, where F_0 = 0, F_1 = 1, and F_{j+2} = F_{j+1} + F_j for all j ≥ 0.
    Preconditions: The machine integer n represents N = 2^m - 1 for some integer m with 1 ≤ m ≤ 29. -/
  theorem spec_9 (n : Std.I64) (m : ℕ) (hn : n.val = (2 : ℤ) ^ m - 1) (hm1 : 1 ≤ m)
      (hm29 : m ≤ 29)
      (r : Std.I64) (hr : Aegis.FindIntegers.find_integers n = ok r) :
      r.val = (fib (m + 2) : ℤ) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n : Std.I64) (m : ℕ) (hn : n.val = (2 : ℤ) ^ m - 1) (hm1 : 1 ≤ m)
        (hm29 : m ≤ 29)
        (r : Std.I64) (hr : Aegis.FindIntegers.find_integers n = ok r), r.val = (fib (m + 2) : ℤ)) := by
    sorry

  end AegisSpec.FindIntegers
