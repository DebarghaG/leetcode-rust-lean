import Aegis.MaximumSwap.Code.Funs

/-!
# Specifications of `Aegis.MaximumSwap.maximum_swap`

LeetCode problem `maximum-swap`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaximumSwap

  def digitsNat (n : ℕ) : List ℕ :=
    (List.range (Nat.log 10 n + 1)).reverse.map (fun i => n / 10 ^ i % 10)

  def decDigits (n : ℤ) : List ℤ := (digitsNat n.toNat).map (fun d => (d : ℤ))

  def numDigits (n : ℤ) : ℕ := (decDigits n).length

  def digitAt (n : ℤ) (i : ℕ) : ℤ := (decDigits n).getD i 0

  def maxDigit (n : ℤ) : ℤ := (decDigits n).foldl max 0

  def digitsVal (ds : List ℤ) : ℤ := ds.foldl (fun acc d => acc * 10 + d) 0

  def swapDigits (n : ℤ) (i j : ℕ) : List ℤ :=
    ((decDigits n).set i (digitAt n j)).set j (digitAt n i)

  def swapVal (n : ℤ) (i j : ℕ) : ℤ := digitsVal (swapDigits n i j)

  def countDigit (n a : ℤ) : ℕ := (decDigits n).count a

  def IsNonincreasingDigits (n : ℤ) : Prop :=
    ∀ i, i + 1 < numDigits n → digitAt n (i + 1) ≤ digitAt n i

  def IsStrictlyIncreasingDigits (n : ℤ) : Prop :=
    ∀ i, i + 1 < numDigits n → digitAt n i < digitAt n (i + 1)

  def NoIncreasingPair (n : ℤ) : Prop :=
    ∀ i j, i < j → j < numDigits n → ¬ digitAt n i < digitAt n j

  def IsGreedySwap (n : ℤ) (i j : ℕ) : Prop :=
    (∃ j', i < j' ∧ j' < numDigits n ∧ digitAt n i < digitAt n j') ∧
    (∀ i', i' < i →
      ¬ ∃ j', i' < j' ∧ j' < numDigits n ∧ digitAt n i' < digitAt n j') ∧
    (i < j ∧ j < numDigits n) ∧
    (∀ j', i < j' → j' < numDigits n → digitAt n j' ≤ digitAt n j) ∧
    (∀ j', j < j' → j' < numDigits n → digitAt n j' < digitAt n j)

  /-- Let d_0, d_1, ..., d_{k-1} be the decimal digits of num, most significant first (so k >= 1, num = sum_{m=0}^{k-1} d_m * 10^{k-1-m}, and if num > 0 then d_0 != 0; for num = 0 take k = 1 and d_0 = 0). For 0 <= i <= j < k, let swap(num,i,j) be the integer value of the digit string obtained from d_0,...,d_{k-1} by exchanging d_i and d_j (if i=j this is the unchanged string; a leading zero created by the exchange is ignored in the integer value). The function returns a result r and r = max{ swap(num,i,j) : 0 <= i <= j < k }.
    Preconditions: 0 <= num <= 999999999. -/
  theorem spec_1 (num : Std.I64) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 999999999) :
      ∃ r, Aegis.MaximumSwap.maximum_swap num = ok r ∧
        (∀ i j, i ≤ j → j < numDigits num.val → swapVal num.val i j ≤ r.val) ∧
        (∃ i j, i ≤ j ∧ j < numDigits num.val ∧ swapVal num.val i j = r.val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (num : Std.I64) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 999999999), ∃ r, Aegis.MaximumSwap.maximum_swap num = ok r ∧
          (∀ i j, i ≤ j → j < numDigits num.val → swapVal num.val i j ≤ r.val) ∧
          (∃ i j, i ≤ j ∧ j < numDigits num.val ∧ swapVal num.val i j = r.val)) := by
    sorry

  /-- The function returns some result r; it does not fail (no overflow, panic, or out-of-bounds error).
    Preconditions: 0 <= num <= 999999999. -/
  theorem spec_2 (num : Std.I64) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 999999999) :
      ∃ r, Aegis.MaximumSwap.maximum_swap num = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (num : Std.I64) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 999999999), ∃ r, Aegis.MaximumSwap.maximum_swap num = ok r) := by
    sorry

  /-- The function returns a result r with r >= num.
    Preconditions: 0 <= num <= 999999999. -/
  theorem spec_3 (num : Std.I64) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 999999999) :
      ∃ r, Aegis.MaximumSwap.maximum_swap num = ok r ∧ num.val ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (num : Std.I64) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 999999999), ∃ r, Aegis.MaximumSwap.maximum_swap num = ok r ∧ num.val ≤ r.val) := by
    sorry

  /-- Let k be the number of decimal digits of num. The function returns a result r with 0 <= r <= 10^k - 1.
    Preconditions: 0 <= num <= 999999999. -/
  theorem spec_4 (num : Std.I64) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 999999999) :
      ∃ r, Aegis.MaximumSwap.maximum_swap num = ok r ∧
        0 ≤ r.val ∧ r.val ≤ 10 ^ numDigits num.val - 1 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (num : Std.I64) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 999999999), ∃ r, Aegis.MaximumSwap.maximum_swap num = ok r ∧
          0 ≤ r.val ∧ r.val ≤ 10 ^ numDigits num.val - 1) := by
    sorry

  /-- The function returns a result r, and if num > 0, then r has exactly the same number k of decimal digits as num, i.e. 10^(k-1) <= r <= 10^k - 1.
    Preconditions: 0 <= num <= 999999999. -/
  theorem spec_5 (num : Std.I64) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 999999999) :
      ∃ r, Aegis.MaximumSwap.maximum_swap num = ok r ∧
        (0 < num.val → 10 ^ (numDigits num.val - 1) ≤ r.val ∧
          r.val ≤ 10 ^ numDigits num.val - 1) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (num : Std.I64) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 999999999), ∃ r, Aegis.MaximumSwap.maximum_swap num = ok r ∧
          (0 < num.val → 10 ^ (numDigits num.val - 1) ≤ r.val ∧
            r.val ≤ 10 ^ numDigits num.val - 1)) := by
    sorry

  /-- The function returns a result r, and for every digit a with 0 <= a <= 9, the number of occurrences of a in the decimal representation of r equals the number of occurrences of a in the decimal representation of num.
    Preconditions: 0 <= num <= 999999999. -/
  theorem spec_6 (num : Std.I64) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 999999999) :
      ∃ r, Aegis.MaximumSwap.maximum_swap num = ok r ∧
        ∀ a, 0 ≤ a → a ≤ 9 → countDigit r.val a = countDigit num.val a := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (num : Std.I64) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 999999999), ∃ r, Aegis.MaximumSwap.maximum_swap num = ok r ∧
          ∀ a, 0 ≤ a → a ≤ 9 → countDigit r.val a = countDigit num.val a) := by
    sorry

  /-- Let k be the number of decimal digits of num. The function returns a result r, and there exist indices i and j with 0 <= i <= j < k such that r equals the value obtained by exchanging the i-th and j-th decimal digits of num (most significant digit index 0; i=j means no exchange; leading zeros in the exchanged string are ignored as usual).
    Preconditions: 0 <= num <= 999999999. -/
  theorem spec_7 (num : Std.I64) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 999999999) :
      ∃ r, Aegis.MaximumSwap.maximum_swap num = ok r ∧
        ∃ i j, i ≤ j ∧ j < numDigits num.val ∧ r.val = swapVal num.val i j := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (num : Std.I64) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 999999999), ∃ r, Aegis.MaximumSwap.maximum_swap num = ok r ∧
          ∃ i j, i ≤ j ∧ j < numDigits num.val ∧ r.val = swapVal num.val i j) := by
    sorry

  /-- Let k be the number of decimal digits of num. The function returns a result r, and for every pair of indices i and j with 0 <= i <= j < k, the value obtained from num by exchanging its i-th and j-th decimal digits (most significant digit index 0; i=j means no exchange; leading zeros in the exchanged string are ignored) is at most r.
    Preconditions: 0 <= num <= 999999999. -/
  theorem spec_8 (num : Std.I64) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 999999999) :
      ∃ r, Aegis.MaximumSwap.maximum_swap num = ok r ∧
        ∀ i j, i ≤ j → j < numDigits num.val → swapVal num.val i j ≤ r.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (num : Std.I64) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 999999999), ∃ r, Aegis.MaximumSwap.maximum_swap num = ok r ∧
          ∀ i j, i ≤ j → j < numDigits num.val → swapVal num.val i j ≤ r.val) := by
    sorry

  /-- The function returns a result r, and r > num if and only if there exist indices i and j with 0 <= i < j < k such that exchanging the i-th and j-th decimal digits of num (most significant digit index 0) gives a value strictly greater than num; here k is the number of decimal digits of num.
    Preconditions: 0 <= num <= 999999999. -/
  theorem spec_9 (num : Std.I64) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 999999999) :
      ∃ r, Aegis.MaximumSwap.maximum_swap num = ok r ∧
        (num.val < r.val ↔
          ∃ i j, i < j ∧ j < numDigits num.val ∧ num.val < swapVal num.val i j) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (num : Std.I64) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 999999999), ∃ r, Aegis.MaximumSwap.maximum_swap num = ok r ∧
          (num.val < r.val ↔
            ∃ i j, i < j ∧ j < numDigits num.val ∧ num.val < swapVal num.val i j)) := by
    sorry

  /-- The function returns a result r, and if the decimal digits d_0,...,d_{k-1} of num (most significant first) satisfy d_0 >= d_1 >= ... >= d_{k-1}, then r = num.
    Preconditions: 0 <= num <= 999999999. -/
  theorem spec_10 (num : Std.I64) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 999999999) :
      ∃ r, Aegis.MaximumSwap.maximum_swap num = ok r ∧
        (IsNonincreasingDigits num.val → r.val = num.val) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (num : Std.I64) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 999999999), ∃ r, Aegis.MaximumSwap.maximum_swap num = ok r ∧
          (IsNonincreasingDigits num.val → r.val = num.val)) := by
    sorry

  /-- The function returns a result r, and if the decimal digits d_0,...,d_{k-1} of num (most significant first) satisfy d_0 < d_1 < ... < d_{k-1}, then r equals the value obtained by exchanging d_0 and d_{k-1} (for k=1 this exchange leaves num unchanged).
    Preconditions: 0 <= num <= 999999999. -/
  theorem spec_11 (num : Std.I64) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 999999999) :
      ∃ r, Aegis.MaximumSwap.maximum_swap num = ok r ∧
        (IsStrictlyIncreasingDigits num.val →
          r.val = swapVal num.val 0 (numDigits num.val - 1)) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (num : Std.I64) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 999999999), ∃ r, Aegis.MaximumSwap.maximum_swap num = ok r ∧
          (IsStrictlyIncreasingDigits num.val →
            r.val = swapVal num.val 0 (numDigits num.val - 1))) := by
    sorry

  /-- The function returns a result r, and if num > 0 and d_0,...,d_{k-1} are the decimal digits of num (most significant first), then the most significant decimal digit of r is max{d_0,...,d_{k-1}}.
    Preconditions: 0 <= num <= 999999999. -/
  theorem spec_12 (num : Std.I64) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 999999999) :
      ∃ r, Aegis.MaximumSwap.maximum_swap num = ok r ∧
        (0 < num.val → digitAt r.val 0 = maxDigit num.val) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (num : Std.I64) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 999999999), ∃ r, Aegis.MaximumSwap.maximum_swap num = ok r ∧
          (0 < num.val → digitAt r.val 0 = maxDigit num.val)) := by
    sorry

  /-- Let k be the number of decimal digits of num. The function returns a result r, and if num > 0, then the decimal representations of num and r, both written with exactly k digits, are either identical or differ in exactly two positions i < j; in the latter case the i-th digit of r equals the j-th digit of num and the j-th digit of r equals the i-th digit of num (indices from 0 at the most significant digit).
    Preconditions: 0 <= num <= 999999999. -/
  theorem spec_13 (num : Std.I64) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 999999999) :
      ∃ r, Aegis.MaximumSwap.maximum_swap num = ok r ∧
        (0 < num.val →
          (decDigits r.val).length = numDigits num.val ∧
          ((∀ i, i < numDigits num.val → digitAt r.val i = digitAt num.val i) ∨
            ∃ i j, i < j ∧ j < numDigits num.val ∧
              digitAt r.val i = digitAt num.val j ∧
              digitAt r.val j = digitAt num.val i ∧
              ∀ m, m < numDigits num.val → m ≠ i → m ≠ j →
                digitAt r.val m = digitAt num.val m)) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (num : Std.I64) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 999999999), ∃ r, Aegis.MaximumSwap.maximum_swap num = ok r ∧
          (0 < num.val →
            (decDigits r.val).length = numDigits num.val ∧
            ((∀ i, i < numDigits num.val → digitAt r.val i = digitAt num.val i) ∨
              ∃ i j, i < j ∧ j < numDigits num.val ∧
                digitAt r.val i = digitAt num.val j ∧
                digitAt r.val j = digitAt num.val i ∧
                ∀ m, m < numDigits num.val → m ≠ i → m ≠ j →
                  digitAt r.val m = digitAt num.val m))) := by
    sorry

  /-- Let d_0,...,d_{k-1} be the decimal digits of num (most significant first), and let M = max{d_0,...,d_{k-1}}. The function returns a result r, and if num > 0 and d_0 < M, and j is the largest index with d_j = M, then r is obtained by exchanging d_0 and d_j.
    Preconditions: 0 <= num <= 999999999. -/
  theorem spec_14 (num : Std.I64) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 999999999) :
      ∃ r, Aegis.MaximumSwap.maximum_swap num = ok r ∧
        ∀ M j, 0 < num.val → M = maxDigit num.val → digitAt num.val 0 < M →
          j < numDigits num.val → digitAt num.val j = M →
          (∀ j', j' < numDigits num.val → digitAt num.val j' = M → j' ≤ j) →
          r.val = swapVal num.val 0 j := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (num : Std.I64) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 999999999), ∃ r, Aegis.MaximumSwap.maximum_swap num = ok r ∧
          ∀ M j, 0 < num.val → M = maxDigit num.val → digitAt num.val 0 < M →
            j < numDigits num.val → digitAt num.val j = M →
            (∀ j', j' < numDigits num.val → digitAt num.val j' = M → j' ≤ j) →
            r.val = swapVal num.val 0 j) := by
    sorry

  /-- Let d_0,...,d_{k-1} be the decimal digits of num (most significant first). If no pair i<j with d_i < d_j exists, then the function returns r = num. Otherwise let i be the smallest index for which some j>i has d_i < d_j; let M = max{d_j : i < j < k}; and let j be the largest index with i < j < k and d_j = M. Then the function returns r obtained from num by exchanging d_i and d_j.
    Preconditions: 0 <= num <= 999999999. -/
  theorem spec_15 (num : Std.I64) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 999999999) :
      ∃ r, Aegis.MaximumSwap.maximum_swap num = ok r ∧
        (NoIncreasingPair num.val → r.val = num.val) ∧
        (∀ i j, IsGreedySwap num.val i j → r.val = swapVal num.val i j) := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (num : Std.I64) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 999999999), ∃ r, Aegis.MaximumSwap.maximum_swap num = ok r ∧
          (NoIncreasingPair num.val → r.val = num.val) ∧
          (∀ i j, IsGreedySwap num.val i j → r.val = swapVal num.val i j)) := by
    sorry

  end AegisSpec.MaximumSwap
