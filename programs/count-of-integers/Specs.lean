import Aegis.Count.Code.Funs

/-!
# Specifications of `Aegis.Count.count`

LeetCode problem `count-of-integers`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.Count

  def modN : ℕ := 1000000007

  def digitSum : ℕ → ℕ
    | 0 => 0
    | n + 1 => (n + 1) % 10 + digitSum ((n + 1) / 10)
    termination_by n => n
    decreasing_by exact Nat.div_lt_self (Nat.succ_pos n) (by decide)

  def digitsVal : List ℕ → ℕ
    | [] => 0
    | d :: ds => d * 10 ^ ds.length + digitsVal ds

  def sliceVal (s : Slice Std.U8) : ℕ := digitsVal (s.val.map (fun b => b.val))

  def AllDigits (s : Slice Std.U8) : Prop := ∀ b ∈ s.val, 48 ≤ b.val ∧ b.val ≤ 57

  def IsDecimal (s : Slice Std.U8) : Prop :=
    s.val ≠ [] ∧ AllDigits s ∧
    (∀ (b : Std.U8) (rest : List Std.U8), s.val = b :: rest → b.val ≠ 0) ∧
    s.val.length ≤ 31

  def CommonPre (num1 num2 : Slice Std.U8) (minSum maxSum : Std.I64) : Prop :=
    IsDecimal num1 ∧ IsDecimal num2 ∧
    1 ≤ sliceVal num1 ∧ sliceVal num1 ≤ sliceVal num2 ∧
    1 ≤ minSum.val ∧ minSum.val ≤ maxSum.val ∧ maxSum.val ≤ 400

  def countIn (num1 num2 : Slice Std.U8) (minSum maxSum : Std.I64) : ℕ :=
    ((Finset.Icc (sliceVal num1) (sliceVal num2)).filter
        (fun x => minSum.val ≤ (digitSum x : ℤ) ∧ (digitSum x : ℤ) ≤ maxSum.val)).card

  def IsResidue (r n : ℤ) : Prop :=
    0 ≤ r ∧ r < (modN : ℤ) ∧ ∃ k : ℤ, n = r + k * (modN : ℤ)

  def powCount (lo hi : ℕ) : ℕ :=
    ((Finset.Icc 0 hi).filter (fun e => lo ≤ 10 ^ e ∧ 10 ^ e ≤ hi)).card

  def i64OfNat (n : ℕ) : Std.I64 := ⟨BitVec.ofNat 64 n⟩

  /-- The function returns a result r and r = N mod M, i.e. 0 <= r < M and r is congruent to N modulo M.
    Preconditions: Let M = 1000000007. For a byte slice s of ASCII decimal digits, let val(s) be the integer represented by s in base 10. For x >= 0, let digit_sum(x) be the sum of the decimal digits of x (digit_sum(0)=0). Assume: num1 and num2 are non-empty byte slices, every byte is an ASCII decimal digit (48..57), neither has a leading zero, len(num1) <= 31 and len(num2) <= 31, val(num1) >= 1, val(num1) <= val(num2), and 1 <= min_sum <= max_sum <= 400. Define N = |{ x in Z : val(num1) <= x <= val(num2) and min_sum <= digit_sum(x) <= max_sum }|. -/
  theorem spec_1 (num1 num2 : Slice Std.U8) (minSum maxSum : Std.I64)
      (h : CommonPre num1 num2 minSum maxSum) :
      ∃ r : Std.I64, Aegis.Count.count num1 num2 minSum maxSum = ok r ∧
        IsResidue r.val (countIn num1 num2 minSum maxSum) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (num1 num2 : Slice Std.U8) (minSum maxSum : Std.I64)
        (h : CommonPre num1 num2 minSum maxSum), ∃ r : Std.I64, Aegis.Count.count num1 num2 minSum maxSum = ok r ∧
          IsResidue r.val (countIn num1 num2 minSum maxSum)) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r (it does not fail, panic, or overflow).
    Preconditions: Let M = 1000000007. For a byte slice s of ASCII decimal digits, let val(s) be the integer represented by s in base 10. Assume: num1 and num2 are non-empty byte slices, every byte is an ASCII decimal digit (48..57), neither has a leading zero, len(num1) <= 31 and len(num2) <= 31, val(num1) >= 1, val(num1) <= val(num2), and 1 <= min_sum <= max_sum <= 400. -/
  theorem spec_2 (num1 num2 : Slice Std.U8) (minSum maxSum : Std.I64)
      (h : CommonPre num1 num2 minSum maxSum) :
      ∃ r : Std.I64, Aegis.Count.count num1 num2 minSum maxSum = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (num1 num2 : Slice Std.U8) (minSum maxSum : Std.I64)
        (h : CommonPre num1 num2 minSum maxSum), ∃ r : Std.I64, Aegis.Count.count num1 num2 minSum maxSum = ok r) := by
    sorry

  /-- The function returns a result r and r = 1 if min_sum <= digit_sum(val(num1)) <= max_sum, and r = 0 otherwise.
    Preconditions: Let M = 1000000007. For a byte slice s of ASCII decimal digits, let val(s) be the integer represented by s in base 10. For x >= 0, let digit_sum(x) be the sum of the decimal digits of x. Assume the common preconditions from spec_1, and additionally val(num1) = val(num2). -/
  theorem spec_3 (num1 num2 : Slice Std.U8) (minSum maxSum : Std.I64)
      (h : CommonPre num1 num2 minSum maxSum) (hval : sliceVal num1 = sliceVal num2) :
      ∃ r : Std.I64, Aegis.Count.count num1 num2 minSum maxSum = ok r ∧
        (if minSum.val ≤ (digitSum (sliceVal num1) : ℤ) ∧
            (digitSum (sliceVal num1) : ℤ) ≤ maxSum.val
         then r.val = 1 else r.val = 0) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (num1 num2 : Slice Std.U8) (minSum maxSum : Std.I64)
        (h : CommonPre num1 num2 minSum maxSum) (hval : sliceVal num1 = sliceVal num2), ∃ r : Std.I64, Aegis.Count.count num1 num2 minSum maxSum = ok r ∧
          (if minSum.val ≤ (digitSum (sliceVal num1) : ℤ) ∧
              (digitSum (sliceVal num1) : ℤ) ≤ maxSum.val
           then r.val = 1 else r.val = 0)) := by
    sorry

  /-- The function returns a result r and r is the unique integer with 0 <= r < M and r congruent to (val(num2) - val(num1) + 1) modulo M.
    Preconditions: Let M = 1000000007. For a byte slice s of ASCII decimal digits, let val(s) be the integer represented by s in base 10. For x >= 0, let digit_sum(x) be the sum of the decimal digits of x. Assume the common preconditions from spec_1, and additionally min_sum <= 1 and max_sum >= 9 * len(num2). -/
  theorem spec_4 (num1 num2 : Slice Std.U8) (minSum maxSum : Std.I64)
      (h : CommonPre num1 num2 minSum maxSum)
      (hmin : minSum.val ≤ 1) (hmax : (9 : ℤ) * (num2.val.length : ℤ) ≤ maxSum.val) :
      ∃ r : Std.I64, Aegis.Count.count num1 num2 minSum maxSum = ok r ∧
        IsResidue r.val ((sliceVal num2 : ℤ) - (sliceVal num1 : ℤ) + 1) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (num1 num2 : Slice Std.U8) (minSum maxSum : Std.I64)
        (h : CommonPre num1 num2 minSum maxSum)
        (hmin : minSum.val ≤ 1) (hmax : (9 : ℤ) * (num2.val.length : ℤ) ≤ maxSum.val), ∃ r : Std.I64, Aegis.Count.count num1 num2 minSum maxSum = ok r ∧
          IsResidue r.val ((sliceVal num2 : ℤ) - (sliceVal num1 : ℤ) + 1)) := by
    sorry

  /-- The function returns a result r and r = 0.
    Preconditions: Let M = 1000000007. For a byte slice s of ASCII decimal digits, let val(s) be the integer represented by s in base 10. For x >= 0, let digit_sum(x) be the sum of the decimal digits of x. Assume the common preconditions from spec_1, and additionally min_sum > 9 * len(num2). -/
  theorem spec_5 (num1 num2 : Slice Std.U8) (minSum maxSum : Std.I64)
      (h : CommonPre num1 num2 minSum maxSum)
      (hmin : (9 : ℤ) * (num2.val.length : ℤ) < minSum.val) :
      ∃ r : Std.I64, Aegis.Count.count num1 num2 minSum maxSum = ok r ∧ r.val = 0 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (num1 num2 : Slice Std.U8) (minSum maxSum : Std.I64)
        (h : CommonPre num1 num2 minSum maxSum)
        (hmin : (9 : ℤ) * (num2.val.length : ℤ) < minSum.val), ∃ r : Std.I64, Aegis.Count.count num1 num2 minSum maxSum = ok r ∧ r.val = 0) := by
    sorry

  /-- The function returns a result r and r is the unique integer with 0 <= r < M such that r is congruent modulo M to |{ e in Z : e >= 0 and val(num1) <= 10^e <= val(num2) }|.
    Preconditions: Let M = 1000000007. For a byte slice s of ASCII decimal digits, let val(s) be the integer represented by s in base 10. For x >= 0, let digit_sum(x) be the sum of the decimal digits of x. Assume the common preconditions from spec_1, and additionally min_sum = 1 and max_sum = 1. -/
  theorem spec_6 (num1 num2 : Slice Std.U8) (minSum maxSum : Std.I64)
      (h : CommonPre num1 num2 minSum maxSum)
      (hmin : minSum.val = 1) (hmax : maxSum.val = 1) :
      ∃ r : Std.I64, Aegis.Count.count num1 num2 minSum maxSum = ok r ∧
        IsResidue r.val (powCount (sliceVal num1) (sliceVal num2)) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (num1 num2 : Slice Std.U8) (minSum maxSum : Std.I64)
        (h : CommonPre num1 num2 minSum maxSum)
        (hmin : minSum.val = 1) (hmax : maxSum.val = 1), ∃ r : Std.I64, Aegis.Count.count num1 num2 minSum maxSum = ok r ∧
          IsResidue r.val (powCount (sliceVal num1) (sliceVal num2))) := by
    sorry

  /-- Whenever the function returns a result r, if r != 0 then N >= 1; equivalently, if r != 0 then there exists an integer x with val(num1) <= x <= val(num2) and min_sum <= digit_sum(x) <= max_sum.
    Preconditions: Let M = 1000000007. For a byte slice s of ASCII decimal digits, let val(s) be the integer represented by s in base 10. For x >= 0, let digit_sum(x) be the sum of the decimal digits of x. Assume the common preconditions from spec_1, and let N = |{ x in Z : val(num1) <= x <= val(num2) and min_sum <= digit_sum(x) <= max_sum }|. -/
  theorem spec_7 (num1 num2 : Slice Std.U8) (minSum maxSum : Std.I64)
      (h : CommonPre num1 num2 minSum maxSum) (r : Std.I64)
      (hres : Aegis.Count.count num1 num2 minSum maxSum = ok r) (hne : r.val ≠ 0) :
      1 ≤ countIn num1 num2 minSum maxSum ∧
        ∃ x : ℕ, sliceVal num1 ≤ x ∧ x ≤ sliceVal num2 ∧
          minSum.val ≤ (digitSum x : ℤ) ∧ (digitSum x : ℤ) ≤ maxSum.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (num1 num2 : Slice Std.U8) (minSum maxSum : Std.I64)
        (h : CommonPre num1 num2 minSum maxSum) (r : Std.I64)
        (hres : Aegis.Count.count num1 num2 minSum maxSum = ok r) (hne : r.val ≠ 0), 1 ≤ countIn num1 num2 minSum maxSum ∧
          ∃ x : ℕ, sliceVal num1 ≤ x ∧ x ≤ sliceVal num2 ∧
            minSum.val ≤ (digitSum x : ℤ) ∧ (digitSum x : ℤ) ≤ maxSum.val) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r <= val(num2) - val(num1) + 1.
    Preconditions: Let M = 1000000007. For a byte slice s of ASCII decimal digits, let val(s) be the integer represented by s in base 10. Assume the common preconditions from spec_1. -/
  theorem spec_8 (num1 num2 : Slice Std.U8) (minSum maxSum : Std.I64)
      (h : CommonPre num1 num2 minSum maxSum) (r : Std.I64)
      (hres : Aegis.Count.count num1 num2 minSum maxSum = ok r) :
      0 ≤ r.val ∧ r.val ≤ (sliceVal num2 : ℤ) - (sliceVal num1 : ℤ) + 1 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (num1 num2 : Slice Std.U8) (minSum maxSum : Std.I64)
        (h : CommonPre num1 num2 minSum maxSum) (r : Std.I64)
        (hres : Aegis.Count.count num1 num2 minSum maxSum = ok r), 0 ≤ r.val ∧ r.val ≤ (sliceVal num2 : ℤ) - (sliceVal num1 : ℤ) + 1) := by
    sorry

  /-- Let r be the result of the function on (num1, num2, min_sum, max_sum), and let r' be the result on (num1, num2, min_sum, L). Whenever both calls return results, r = r'.
    Preconditions: Let M = 1000000007. For a byte slice s of ASCII decimal digits, let val(s) be the integer represented by s in base 10. For x >= 0, let digit_sum(x) be the sum of the decimal digits of x. Assume the common preconditions from spec_1. Let L = 9 * len(num2), and assume min_sum <= L < max_sum. -/
  theorem spec_9 (num1 num2 : Slice Std.U8) (minSum maxSum : Std.I64)
      (h : CommonPre num1 num2 minSum maxSum)
      (hmin : minSum.val ≤ (9 : ℤ) * (num2.val.length : ℤ))
      (hLt : (9 : ℤ) * (num2.val.length : ℤ) < maxSum.val)
      (r r' : Std.I64)
      (hres : Aegis.Count.count num1 num2 minSum maxSum = ok r)
      (hres' : Aegis.Count.count num1 num2 minSum
        (i64OfNat (9 * num2.val.length)) = ok r') :
      r = r' := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (num1 num2 : Slice Std.U8) (minSum maxSum : Std.I64)
        (h : CommonPre num1 num2 minSum maxSum)
        (hmin : minSum.val ≤ (9 : ℤ) * (num2.val.length : ℤ))
        (hLt : (9 : ℤ) * (num2.val.length : ℤ) < maxSum.val)
        (r r' : Std.I64)
        (hres : Aegis.Count.count num1 num2 minSum maxSum = ok r)
        (hres' : Aegis.Count.count num1 num2 minSum
          (i64OfNat (9 * num2.val.length)) = ok r'), r = r') := by
    sorry

  /-- Whenever the function returns r on the first input and r' on the second input, r = N mod M, r' = N' mod M, and N <= N'.
    Preconditions: Let M = 1000000007. For a byte slice s of ASCII decimal digits, let val(s) be the integer represented by s in base 10. For x >= 0, let digit_sum(x) be the sum of the decimal digits of x. Assume the common preconditions from spec_1 hold for (num1, num2, min_sum, max_sum) and also for (num1, num2', min_sum, max_sum), with val(num2) <= val(num2'). Let N be the count for the first input and N' the count for the second input, defined as in spec_1. -/
  theorem spec_10 (num1 num2 num2' : Slice Std.U8) (minSum maxSum : Std.I64)
      (h : CommonPre num1 num2 minSum maxSum) (h' : CommonPre num1 num2' minSum maxSum)
      (hle : sliceVal num2 ≤ sliceVal num2') (r r' : Std.I64)
      (hres : Aegis.Count.count num1 num2 minSum maxSum = ok r)
      (hres' : Aegis.Count.count num1 num2' minSum maxSum = ok r') :
      IsResidue r.val (countIn num1 num2 minSum maxSum) ∧
        IsResidue r'.val (countIn num1 num2' minSum maxSum) ∧
        countIn num1 num2 minSum maxSum ≤ countIn num1 num2' minSum maxSum := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (num1 num2 num2' : Slice Std.U8) (minSum maxSum : Std.I64)
        (h : CommonPre num1 num2 minSum maxSum) (h' : CommonPre num1 num2' minSum maxSum)
        (hle : sliceVal num2 ≤ sliceVal num2') (r r' : Std.I64)
        (hres : Aegis.Count.count num1 num2 minSum maxSum = ok r)
        (hres' : Aegis.Count.count num1 num2' minSum maxSum = ok r'), IsResidue r.val (countIn num1 num2 minSum maxSum) ∧
          IsResidue r'.val (countIn num1 num2' minSum maxSum) ∧
          countIn num1 num2 minSum maxSum ≤ countIn num1 num2' minSum maxSum) := by
    sorry

  /-- Whenever the function returns r1 on the first input and r2 on the second input, r1 = N1 mod M, r2 = N2 mod M, and N1 <= N2.
    Preconditions: Let M = 1000000007. For a byte slice s of ASCII decimal digits, let val(s) be the integer represented by s in base 10. For x >= 0, let digit_sum(x) be the sum of the decimal digits of x. Assume the common preconditions from spec_1 hold for (num1, num2, min_sum, max_sum1) and for (num1, num2, min_sum, max_sum2), with max_sum1 <= max_sum2. For i in {1,2}, let Ni = |{ x in Z : val(num1) <= x <= val(num2) and min_sum <= digit_sum(x) <= max_sum_i }|. -/
  theorem spec_11 (num1 num2 : Slice Std.U8) (minSum maxSum1 maxSum2 : Std.I64)
      (h1 : CommonPre num1 num2 minSum maxSum1) (h2 : CommonPre num1 num2 minSum maxSum2)
      (hle : maxSum1.val ≤ maxSum2.val) (r1 r2 : Std.I64)
      (hres1 : Aegis.Count.count num1 num2 minSum maxSum1 = ok r1)
      (hres2 : Aegis.Count.count num1 num2 minSum maxSum2 = ok r2) :
      IsResidue r1.val (countIn num1 num2 minSum maxSum1) ∧
        IsResidue r2.val (countIn num1 num2 minSum maxSum2) ∧
        countIn num1 num2 minSum maxSum1 ≤ countIn num1 num2 minSum maxSum2 := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (num1 num2 : Slice Std.U8) (minSum maxSum1 maxSum2 : Std.I64)
        (h1 : CommonPre num1 num2 minSum maxSum1) (h2 : CommonPre num1 num2 minSum maxSum2)
        (hle : maxSum1.val ≤ maxSum2.val) (r1 r2 : Std.I64)
        (hres1 : Aegis.Count.count num1 num2 minSum maxSum1 = ok r1)
        (hres2 : Aegis.Count.count num1 num2 minSum maxSum2 = ok r2), IsResidue r1.val (countIn num1 num2 minSum maxSum1) ∧
          IsResidue r2.val (countIn num1 num2 minSum maxSum2) ∧
          countIn num1 num2 minSum maxSum1 ≤ countIn num1 num2 minSum maxSum2) := by
    sorry

  /-- Whenever the function returns r1 on the first input and r2 on the second input, r1 = N1 mod M, r2 = N2 mod M, and N2 <= N1.
    Preconditions: Let M = 1000000007. For a byte slice s of ASCII decimal digits, let val(s) be the integer represented by s in base 10. For x >= 0, let digit_sum(x) be the sum of the decimal digits of x. Assume the common preconditions from spec_1 hold for (num1, num2, min_sum1, max_sum) and for (num1, num2, min_sum2, max_sum), with min_sum1 <= min_sum2. For i in {1,2}, let Ni = |{ x in Z : val(num1) <= x <= val(num2) and min_sum_i <= digit_sum(x) <= max_sum }|. -/
  theorem spec_12 (num1 num2 : Slice Std.U8) (minSum1 minSum2 maxSum : Std.I64)
      (h1 : CommonPre num1 num2 minSum1 maxSum) (h2 : CommonPre num1 num2 minSum2 maxSum)
      (hle : minSum1.val ≤ minSum2.val) (r1 r2 : Std.I64)
      (hres1 : Aegis.Count.count num1 num2 minSum1 maxSum = ok r1)
      (hres2 : Aegis.Count.count num1 num2 minSum2 maxSum = ok r2) :
      IsResidue r1.val (countIn num1 num2 minSum1 maxSum) ∧
        IsResidue r2.val (countIn num1 num2 minSum2 maxSum) ∧
        countIn num1 num2 minSum2 maxSum ≤ countIn num1 num2 minSum1 maxSum := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (num1 num2 : Slice Std.U8) (minSum1 minSum2 maxSum : Std.I64)
        (h1 : CommonPre num1 num2 minSum1 maxSum) (h2 : CommonPre num1 num2 minSum2 maxSum)
        (hle : minSum1.val ≤ minSum2.val) (r1 r2 : Std.I64)
        (hres1 : Aegis.Count.count num1 num2 minSum1 maxSum = ok r1)
        (hres2 : Aegis.Count.count num1 num2 minSum2 maxSum = ok r2), IsResidue r1.val (countIn num1 num2 minSum1 maxSum) ∧
          IsResidue r2.val (countIn num1 num2 minSum2 maxSum) ∧
          countIn num1 num2 minSum2 maxSum ≤ countIn num1 num2 minSum1 maxSum) := by
    sorry

  /-- Whenever the function returns r on the first input and r' on the second input, r = N mod M, r' = N' mod M, and N' <= N.
    Preconditions: Let M = 1000000007. For a byte slice s of ASCII decimal digits, let val(s) be the integer represented by s in base 10. For x >= 0, let digit_sum(x) be the sum of the decimal digits of x. Assume the common preconditions from spec_1 hold for (num1, num2, min_sum, max_sum) and for (num1', num2, min_sum, max_sum), with val(num1) <= val(num1'). Let N be the count for the first input and N' the count for the second input, defined as in spec_1. -/
  theorem spec_13 (num1 num1' num2 : Slice Std.U8) (minSum maxSum : Std.I64)
      (h : CommonPre num1 num2 minSum maxSum) (h' : CommonPre num1' num2 minSum maxSum)
      (hle : sliceVal num1 ≤ sliceVal num1') (r r' : Std.I64)
      (hres : Aegis.Count.count num1 num2 minSum maxSum = ok r)
      (hres' : Aegis.Count.count num1' num2 minSum maxSum = ok r') :
      IsResidue r.val (countIn num1 num2 minSum maxSum) ∧
        IsResidue r'.val (countIn num1' num2 minSum maxSum) ∧
        countIn num1' num2 minSum maxSum ≤ countIn num1 num2 minSum maxSum := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (num1 num1' num2 : Slice Std.U8) (minSum maxSum : Std.I64)
        (h : CommonPre num1 num2 minSum maxSum) (h' : CommonPre num1' num2 minSum maxSum)
        (hle : sliceVal num1 ≤ sliceVal num1') (r r' : Std.I64)
        (hres : Aegis.Count.count num1 num2 minSum maxSum = ok r)
        (hres' : Aegis.Count.count num1' num2 minSum maxSum = ok r'), IsResidue r.val (countIn num1 num2 minSum maxSum) ∧
          IsResidue r'.val (countIn num1' num2 minSum maxSum) ∧
          countIn num1' num2 minSum maxSum ≤ countIn num1 num2 minSum maxSum) := by
    sorry

  end AegisSpec.Count
