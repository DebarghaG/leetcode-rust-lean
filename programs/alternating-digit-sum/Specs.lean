import Aegis.AlternateDigitSum.Code.Funs

/-!
# Specifications of `Aegis.AlternateDigitSum.alternate_digit_sum`

LeetCode problem `alternating-digit-sum`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.AlternateDigitSum

  def numDigits (n : ℕ) : ℕ :=
    if n = 0 then 1 else Nat.log 10 n + 1

  def digitAt (n : ℕ) (i : ℕ) : ℕ :=
    n / 10 ^ (numDigits n - 1 - i) % 10

  def decDigits (n : ℕ) : List ℕ :=
    (List.range (numDigits n)).map (fun i => digitAt n i)

  def altSum (m : ℕ) (d : ℕ → ℕ) : ℤ :=
    ∑ i ∈ Finset.range m, (if i % 2 = 0 then (d i : ℤ) else -((d i : ℤ)))

  def digitSum (m : ℕ) (d : ℕ → ℕ) : ℕ :=
    ∑ i ∈ Finset.range m, d i

  def IsDecimalRepr (n : ℤ) (m : ℕ) (d : ℕ → ℕ) : Prop :=
    1 ≤ m ∧ d 0 ≠ 0 ∧ (∀ i, i < m → d i ≤ 9) ∧
      n = ∑ i ∈ Finset.range m, (d i : ℤ) * 10 ^ (m - 1 - i)

  /-- The function returns a result r, and the following holds. Let m >= 1 and let d_0, d_1, ..., d_{m-1} be the decimal digits of n, where d_0 is the most significant digit and d_{m-1} is the least significant digit, so d_0 != 0, 0 <= d_i <= 9 for every i with 0 <= i < m, and n = sum_{i=0}^{m-1} d_i * 10^{m-1-i}. Then r = sum_{i=0}^{m-1} (-1)^i * d_i, where (-1)^i is 1 for even i and -1 for odd i.
    Preconditions: n is an integer with 1 <= n <= 1000000000. -/
  theorem spec_1 (n : I64) (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000000) :
      ∃ r : I64, Aegis.AlternateDigitSum.alternate_digit_sum n = ok r ∧
        ∀ (m : ℕ) (d : ℕ → ℕ), IsDecimalRepr n.val m d → r.val = altSum m d := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : I64) (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000000), ∃ r : I64, Aegis.AlternateDigitSum.alternate_digit_sum n = ok r ∧
          ∀ (m : ℕ) (d : ℕ → ℕ), IsDecimalRepr n.val m d → r.val = altSum m d) := by
    sorry

  /-- For every n with 1 <= n <= 1000000000, the function returns a result r; it does not fail, overflow, or panic.
    Preconditions: n is an integer with 1 <= n <= 1000000000. -/
  theorem spec_2 (n : I64) (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000000) :
      ∃ r : I64, Aegis.AlternateDigitSum.alternate_digit_sum n = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : I64) (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000000), ∃ r : I64, Aegis.AlternateDigitSum.alternate_digit_sum n = ok r) := by
    sorry

  /-- Whenever the function returns r, -n <= r <= n.
    Preconditions: n is an integer with 1 <= n <= 1000000000. -/
  theorem spec_3 (n : I64) (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000000) (r : I64)
      (hr : Aegis.AlternateDigitSum.alternate_digit_sum n = ok r) :
      -n.val ≤ r.val ∧ r.val ≤ n.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : I64) (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000000) (r : I64)
        (hr : Aegis.AlternateDigitSum.alternate_digit_sum n = ok r), -n.val ≤ r.val ∧ r.val ≤ n.val) := by
    sorry

  /-- Whenever the function returns r, let m >= 1 and let d_0, d_1, ..., d_{m-1} be the decimal digits of n with d_0 most significant. Then r ≡ sum_{i=0}^{m-1} d_i (mod 2); equivalently, r and the sum of the decimal digits of n have the same parity.
    Preconditions: n is an integer with 1 <= n <= 1000000000. -/
  theorem spec_4 (n : I64) (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000000) (r : I64)
      (hr : Aegis.AlternateDigitSum.alternate_digit_sum n = ok r) (m : ℕ) (d : ℕ → ℕ)
      (hd : IsDecimalRepr n.val m d) :
      r.val ≡ (digitSum m d : ℤ) [ZMOD 2] := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : I64) (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000000) (r : I64)
        (hr : Aegis.AlternateDigitSum.alternate_digit_sum n = ok r) (m : ℕ) (d : ℕ → ℕ)
        (hd : IsDecimalRepr n.val m d), r.val ≡ (digitSum m d : ℤ) [ZMOD 2]) := by
    sorry

  /-- Whenever the function returns r, let m be the number of decimal digits of n. If m is odd then r ≡ n (mod 11); if m is even then r ≡ -n (mod 11).
    Preconditions: n is an integer with 1 <= n <= 1000000000. -/
  theorem spec_5 (n : I64) (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000000) (r : I64)
      (hr : Aegis.AlternateDigitSum.alternate_digit_sum n = ok r) :
      (Odd (numDigits n.val.toNat) → r.val ≡ n.val [ZMOD 11]) ∧
        (Even (numDigits n.val.toNat) → r.val ≡ -n.val [ZMOD 11]) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : I64) (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000000) (r : I64)
        (hr : Aegis.AlternateDigitSum.alternate_digit_sum n = ok r), (Odd (numDigits n.val.toNat) → r.val ≡ n.val [ZMOD 11]) ∧
          (Even (numDigits n.val.toNat) → r.val ≡ -n.val [ZMOD 11])) := by
    sorry

  /-- Whenever the function returns r, let m be the number of decimal digits of n. Then 1 - 9*floor(m/2) <= r <= 9*ceil(m/2), where floor(m/2) is the greatest integer <= m/2 and ceil(m/2) is the least integer >= m/2.
    Preconditions: n is an integer with 1 <= n <= 1000000000. -/
  theorem spec_6 (n : I64) (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000000) (r : I64)
      (hr : Aegis.AlternateDigitSum.alternate_digit_sum n = ok r) :
      1 - 9 * ((numDigits n.val.toNat / 2 : ℕ) : ℤ) ≤ r.val ∧
        r.val ≤ 9 * (((numDigits n.val.toNat + 1) / 2 : ℕ) : ℤ) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n : I64) (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000000) (r : I64)
        (hr : Aegis.AlternateDigitSum.alternate_digit_sum n = ok r), 1 - 9 * ((numDigits n.val.toNat / 2 : ℕ) : ℤ) ≤ r.val ∧
          r.val ≤ 9 * (((numDigits n.val.toNat + 1) / 2 : ℕ) : ℤ)) := by
    sorry

  /-- The function returns r and r = n.
    Preconditions: n is an integer with 1 <= n <= 9. -/
  theorem spec_7 (n : I64) (hn : 1 ≤ n.val) (hn' : n.val ≤ 9) :
      ∃ r : I64, Aegis.AlternateDigitSum.alternate_digit_sum n = ok r ∧ r.val = n.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n : I64) (hn : 1 ≤ n.val) (hn' : n.val ≤ 9), ∃ r : I64, Aegis.AlternateDigitSum.alternate_digit_sum n = ok r ∧ r.val = n.val) := by
    sorry

  /-- Whenever the function returns r, if n = 10*a + b with 1 <= a <= 9 and 0 <= b <= 9, then r = a - b.
    Preconditions: n is an integer with 10 <= n <= 99. -/
  theorem spec_8 (n : I64) (hn : 10 ≤ n.val) (hn' : n.val ≤ 99) (r : I64)
      (hr : Aegis.AlternateDigitSum.alternate_digit_sum n = ok r) (a b : ℤ)
      (hab : n.val = 10 * a + b) (ha1 : 1 ≤ a) (ha9 : a ≤ 9) (hb0 : 0 ≤ b) (hb9 : b ≤ 9) :
      r.val = a - b := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n : I64) (hn : 10 ≤ n.val) (hn' : n.val ≤ 99) (r : I64)
        (hr : Aegis.AlternateDigitSum.alternate_digit_sum n = ok r) (a b : ℤ)
        (hab : n.val = 10 * a + b) (ha1 : 1 ≤ a) (ha9 : a ≤ 9) (hb0 : 0 ≤ b) (hb9 : b ≤ 9), r.val = a - b) := by
    sorry

  /-- The function returns r and r = 1.
    Preconditions: n = 1000000000. -/
  theorem spec_9 (n : I64) (hn : n.val = 1000000000) :
      ∃ r : I64, Aegis.AlternateDigitSum.alternate_digit_sum n = ok r ∧ r.val = 1 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n : I64) (hn : n.val = 1000000000), ∃ r : I64, Aegis.AlternateDigitSum.alternate_digit_sum n = ok r ∧ r.val = 1) := by
    sorry

  /-- The function returns r and r = 5.
    Preconditions: n = 987654321. -/
  theorem spec_10 (n : I64) (hn : n.val = 987654321) :
      ∃ r : I64, Aegis.AlternateDigitSum.alternate_digit_sum n = ok r ∧ r.val = 5 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n : I64) (hn : n.val = 987654321), ∃ r : I64, Aegis.AlternateDigitSum.alternate_digit_sum n = ok r ∧ r.val = 5) := by
    sorry

  /-- Whenever the function returns r for input n and R for input N, R = d - r.
    Preconditions: Let n be an integer with 1 <= n <= 1000000000, let m be the number of decimal digits of n, let d be an integer with 1 <= d <= 9, and let N = d * 10^m + n. Assume 1 <= N <= 1000000000. -/
  theorem spec_11 (n : I64) (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000000) (d : ℤ)
      (hd1 : 1 ≤ d) (hd9 : d ≤ 9) (N : I64)
      (hN : N.val = d * 10 ^ (numDigits n.val.toNat) + n.val) (hN1 : 1 ≤ N.val)
      (hN' : N.val ≤ 1000000000) (r R : I64)
      (hr : Aegis.AlternateDigitSum.alternate_digit_sum n = ok r)
      (hR : Aegis.AlternateDigitSum.alternate_digit_sum N = ok R) :
      R.val = d - r.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (n : I64) (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000000) (d : ℤ)
        (hd1 : 1 ≤ d) (hd9 : d ≤ 9) (N : I64)
        (hN : N.val = d * 10 ^ (numDigits n.val.toNat) + n.val) (hN1 : 1 ≤ N.val)
        (hN' : N.val ≤ 1000000000) (r R : I64)
        (hr : Aegis.AlternateDigitSum.alternate_digit_sum n = ok r)
        (hR : Aegis.AlternateDigitSum.alternate_digit_sum N = ok R), R.val = d - r.val) := by
    sorry

  /-- Whenever the function returns r for input n and R for input 10*n, R = r.
    Preconditions: Let n be an integer with 1 <= n <= 100000000. -/
  theorem spec_12 (n : I64) (hn : 1 ≤ n.val) (hn' : n.val ≤ 100000000) (N : I64)
      (hN : N.val = 10 * n.val) (r R : I64)
      (hr : Aegis.AlternateDigitSum.alternate_digit_sum n = ok r)
      (hR : Aegis.AlternateDigitSum.alternate_digit_sum N = ok R) :
      R.val = r.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (n : I64) (hn : 1 ≤ n.val) (hn' : n.val ≤ 100000000) (N : I64)
        (hN : N.val = 10 * n.val) (r R : I64)
        (hr : Aegis.AlternateDigitSum.alternate_digit_sum n = ok r)
        (hR : Aegis.AlternateDigitSum.alternate_digit_sum N = ok R), R.val = r.val) := by
    sorry

  /-- Whenever the function returns r, if n is divisible by 11, then r is divisible by 11.
    Preconditions: n is an integer with 1 <= n <= 1000000000. -/
  theorem spec_13 (n : I64) (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000000) (r : I64)
      (hr : Aegis.AlternateDigitSum.alternate_digit_sum n = ok r) :
      (11 : ℤ) ∣ n.val → (11 : ℤ) ∣ r.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (n : I64) (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000000) (r : I64)
        (hr : Aegis.AlternateDigitSum.alternate_digit_sum n = ok r), (11 : ℤ) ∣ n.val → (11 : ℤ) ∣ r.val) := by
    sorry

  /-- Whenever the function returns r, r = a if m is odd, and r = 0 if m is even.
    Preconditions: n is an integer with 1 <= n <= 1000000000 whose decimal representation consists of m >= 1 identical digits a, where 1 <= a <= 9. -/
  theorem spec_14 (n : I64) (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000000) (m : ℕ) (hm : 1 ≤ m)
      (a : ℤ) (ha1 : 1 ≤ a) (ha9 : a ≤ 9)
      (hrep : n.val = a * (∑ i ∈ Finset.range m, (10 : ℤ) ^ i)) (r : I64)
      (hr : Aegis.AlternateDigitSum.alternate_digit_sum n = ok r) :
      (Odd m → r.val = a) ∧ (Even m → r.val = 0) := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (n : I64) (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000000) (m : ℕ) (hm : 1 ≤ m)
        (a : ℤ) (ha1 : 1 ≤ a) (ha9 : a ≤ 9)
        (hrep : n.val = a * (∑ i ∈ Finset.range m, (10 : ℤ) ^ i)) (r : I64)
        (hr : Aegis.AlternateDigitSum.alternate_digit_sum n = ok r), (Odd m → r.val = a) ∧ (Even m → r.val = 0)) := by
    sorry

  /-- Whenever the function returns r for input n and R for input N, R = r + (-1)^m * d, where (-1)^m is 1 if m is even and -1 if m is odd.
    Preconditions: Let n be an integer with 1 <= n <= 100000000, let m be the number of decimal digits of n, let d be an integer with 0 <= d <= 9, and let N = 10*n + d. Assume 1 <= N <= 1000000000. -/
  theorem spec_15 (n : I64) (hn : 1 ≤ n.val) (hn' : n.val ≤ 100000000) (d : ℤ) (hd0 : 0 ≤ d)
      (hd9 : d ≤ 9) (N : I64) (hN : N.val = 10 * n.val + d) (hN1 : 1 ≤ N.val)
      (hN' : N.val ≤ 1000000000) (r R : I64)
      (hr : Aegis.AlternateDigitSum.alternate_digit_sum n = ok r)
      (hR : Aegis.AlternateDigitSum.alternate_digit_sum N = ok R) :
      R.val = r.val + (-1 : ℤ) ^ (numDigits n.val.toNat) * d := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (n : I64) (hn : 1 ≤ n.val) (hn' : n.val ≤ 100000000) (d : ℤ) (hd0 : 0 ≤ d)
        (hd9 : d ≤ 9) (N : I64) (hN : N.val = 10 * n.val + d) (hN1 : 1 ≤ N.val)
        (hN' : N.val ≤ 1000000000) (r R : I64)
        (hr : Aegis.AlternateDigitSum.alternate_digit_sum n = ok r)
        (hR : Aegis.AlternateDigitSum.alternate_digit_sum N = ok R), R.val = r.val + (-1 : ℤ) ^ (numDigits n.val.toNat) * d) := by
    sorry

  end AegisSpec.AlternateDigitSum
