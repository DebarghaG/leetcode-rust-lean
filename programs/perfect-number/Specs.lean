import Aegis.CheckPerfectNumber.Code.Funs

/-!
# Specifications of `Aegis.CheckPerfectNumber.check_perfect_number`

LeetCode problem `perfect-number`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.CheckPerfectNumber

  def properDivisors (n : ℤ) : Finset ℕ :=
    (Finset.Ico 1 n.toNat).filter (fun d : ℕ => (d : ℤ) ∣ n)

  def sumProperDivisors (n : ℤ) : ℤ :=
    (properDivisors n).sum (fun d => (d : ℤ))

  def divisorsUpTo (n : ℤ) : Finset ℕ :=
    (Finset.Ico 1 (n.toNat + 1)).filter (fun d : ℕ => (d : ℤ) ∣ n)

  def sumDivisorsUpTo (n : ℤ) : ℤ :=
    (divisorsUpTo n).sum (fun d => (d : ℤ))

  def IsPerfect (n : ℤ) : Prop :=
    n = sumProperDivisors n

  def IsPrime (n : ℤ) : Prop :=
    1 < n ∧ ∀ d : ℤ, 0 < d → d ∣ n → d = 1 ∨ d = n

  def IsPowerOfTwo (n : ℤ) : Prop :=
    ∃ k : ℕ, 1 ≤ k ∧ n = (2 : ℤ) ^ k

  def IsComposite (n : ℤ) : Prop :=
    1 < n ∧ ∃ a b : ℤ, 1 < a ∧ a ≤ b ∧ b < n ∧ a * b = n

  /-- For every such num, the function returns a result r : Bool (it does not fail), and r = true if and only if num equals the sum of all integers d with 1 <= d < num and d divides num. Here 'd divides num' means there exists an integer k with num = d * k; the sum over no such d is 0. Equivalently, r = true exactly when num is a perfect number, i.e. num is the sum of its positive divisors excluding itself.
    Preconditions: 1 <= num <= 100000000, i.e. num is an i64 in the problem's constraint range. -/
  theorem spec_1 (num : Std.I64)
      (hlo : 1 ≤ num.val) (hhi : num.val ≤ 100000000) :
      ∃ r : Bool, Aegis.CheckPerfectNumber.check_perfect_number num = ok r ∧
        (r = true ↔ IsPerfect num.val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (num : Std.I64)
        (hlo : 1 ≤ num.val) (hhi : num.val ≤ 100000000), ∃ r : Bool, Aegis.CheckPerfectNumber.check_perfect_number num = ok r ∧
          (r = true ↔ IsPerfect num.val)) := by
    sorry

  /-- For every num with 1 <= num <= 100000000, the function returns Ok(true) or Ok(false); it never returns Err for such an input.
    Preconditions: 1 <= num <= 100000000. -/
  theorem spec_2 (num : Std.I64)
      (hlo : 1 ≤ num.val) (hhi : num.val ≤ 100000000) :
      ∃ r : Bool, Aegis.CheckPerfectNumber.check_perfect_number num = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (num : Std.I64)
        (hlo : 1 ≤ num.val) (hhi : num.val ≤ 100000000), ∃ r : Bool, Aegis.CheckPerfectNumber.check_perfect_number num = ok r) := by
    sorry

  /-- For every num with 1 <= num <= 100000000, if num equals the sum of all integers d with 1 <= d < num and d divides num (there exists an integer k with num = d * k), then the function returns Ok(true).
    Preconditions: 1 <= num <= 100000000. -/
  theorem spec_3 (num : Std.I64)
      (hlo : 1 ≤ num.val) (hhi : num.val ≤ 100000000) (hperf : IsPerfect num.val) :
      Aegis.CheckPerfectNumber.check_perfect_number num = ok true := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (num : Std.I64)
        (hlo : 1 ≤ num.val) (hhi : num.val ≤ 100000000) (hperf : IsPerfect num.val), Aegis.CheckPerfectNumber.check_perfect_number num = ok true) := by
    sorry

  /-- For every num with 1 <= num <= 100000000, whenever the function returns Ok(true), the sum of all integers d with 1 <= d < num and d dividing num (there exists an integer k with num = d * k) is exactly num.
    Preconditions: 1 <= num <= 100000000. -/
  theorem spec_4 (num : Std.I64)
      (hlo : 1 ≤ num.val) (hhi : num.val ≤ 100000000)
      (hres : Aegis.CheckPerfectNumber.check_perfect_number num = ok true) :
      sumProperDivisors num.val = num.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (num : Std.I64)
        (hlo : 1 ≤ num.val) (hhi : num.val ≤ 100000000)
        (hres : Aegis.CheckPerfectNumber.check_perfect_number num = ok true), sumProperDivisors num.val = num.val) := by
    sorry

  /-- For every num with 1 <= num <= 100000000, if num > 1 is prime (its only positive divisors are 1 and num), then the function returns Ok(false).
    Preconditions: 1 <= num <= 100000000. -/
  theorem spec_5 (num : Std.I64)
      (hlo : 1 ≤ num.val) (hhi : num.val ≤ 100000000) (hprime : IsPrime num.val) :
      Aegis.CheckPerfectNumber.check_perfect_number num = ok false := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (num : Std.I64)
        (hlo : 1 ≤ num.val) (hhi : num.val ≤ 100000000) (hprime : IsPrime num.val), Aegis.CheckPerfectNumber.check_perfect_number num = ok false) := by
    sorry

  /-- For every num with 1 <= num <= 100000000, if num = 2^k for some integer k with k >= 1, then the function returns Ok(false).
    Preconditions: 1 <= num <= 100000000. -/
  theorem spec_6 (num : Std.I64)
      (hlo : 1 ≤ num.val) (hhi : num.val ≤ 100000000) (hpow : IsPowerOfTwo num.val) :
      Aegis.CheckPerfectNumber.check_perfect_number num = ok false := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (num : Std.I64)
        (hlo : 1 ≤ num.val) (hhi : num.val ≤ 100000000) (hpow : IsPowerOfTwo num.val), Aegis.CheckPerfectNumber.check_perfect_number num = ok false) := by
    sorry

  /-- For num = 1, the function returns Ok(false).
    Preconditions: 1 <= num <= 100000000. -/
  theorem spec_7 (num : Std.I64)
      (hlo : 1 ≤ num.val) (hhi : num.val ≤ 100000000) (h1 : num.val = 1) :
      Aegis.CheckPerfectNumber.check_perfect_number num = ok false := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (num : Std.I64)
        (hlo : 1 ≤ num.val) (hhi : num.val ≤ 100000000) (h1 : num.val = 1), Aegis.CheckPerfectNumber.check_perfect_number num = ok false) := by
    sorry

  /-- For every num with 1 <= num <= 100000000, whenever the function returns Ok(true), it holds that num >= 6.
    Preconditions: 1 <= num <= 100000000. -/
  theorem spec_8 (num : Std.I64)
      (hlo : 1 ≤ num.val) (hhi : num.val ≤ 100000000)
      (hres : Aegis.CheckPerfectNumber.check_perfect_number num = ok true) :
      6 ≤ num.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (num : Std.I64)
        (hlo : 1 ≤ num.val) (hhi : num.val ≤ 100000000)
        (hres : Aegis.CheckPerfectNumber.check_perfect_number num = ok true), 6 ≤ num.val) := by
    sorry

  /-- For every num with 1 <= num <= 100000000, whenever the function returns Ok(true), num is composite: num > 1 and there exist integers a and b with 1 < a <= b < num and a*b = num.
    Preconditions: 1 <= num <= 100000000. -/
  theorem spec_9 (num : Std.I64)
      (hlo : 1 ≤ num.val) (hhi : num.val ≤ 100000000)
      (hres : Aegis.CheckPerfectNumber.check_perfect_number num = ok true) :
      IsComposite num.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (num : Std.I64)
        (hlo : 1 ≤ num.val) (hhi : num.val ≤ 100000000)
        (hres : Aegis.CheckPerfectNumber.check_perfect_number num = ok true), IsComposite num.val) := by
    sorry

  /-- For every num with 1 <= num <= 100000000, the function returns Ok(true) if and only if the sum of all positive divisors d of num with 1 <= d <= num (i.e. all d for which there exists an integer k with num = d*k) equals 2 * num.
    Preconditions: 1 <= num <= 100000000. -/
  theorem spec_10 (num : Std.I64)
      (hlo : 1 ≤ num.val) (hhi : num.val ≤ 100000000) :
      ∃ r : Bool, Aegis.CheckPerfectNumber.check_perfect_number num = ok r ∧
        (r = true ↔ sumDivisorsUpTo num.val = 2 * num.val) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (num : Std.I64)
        (hlo : 1 ≤ num.val) (hhi : num.val ≤ 100000000), ∃ r : Bool, Aegis.CheckPerfectNumber.check_perfect_number num = ok r ∧
          (r = true ↔ sumDivisorsUpTo num.val = 2 * num.val)) := by
    sorry

  end AegisSpec.CheckPerfectNumber
