import Aegis.FindNthDigit.Code.Funs

/-!
# Specifications of `Aegis.FindNthDigit.find_nth_digit`

LeetCode problem `nth-digit`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.FindNthDigit

  namespace AegisSpec.FindNthDigit

  def decDigits (k : ℕ) : List ℕ :=
    if k < 10 then [k]
    else decDigits (k / 10) ++ [k % 10]
  termination_by k
  decreasing_by exact Nat.div_lt_self (by omega) (by norm_num)

  def lenDec (k : ℕ) : ℕ := (decDigits k).length

  def startPos (m : ℕ) : ℕ := 1 + ∑ k ∈ Finset.Ico 1 m, lenDec k

  def endPos (m : ℕ) : ℕ := ∑ k ∈ Finset.Ico 1 (m + 1), lenDec k

  def digitAt (m i : ℕ) : ℕ := (decDigits m).getD (i - 1) 0

  def L (d : ℕ) : ℕ := ∑ i ∈ Finset.Ico 1 d, 9 * 10 ^ (i - 1) * i

  def blockLen (d : ℕ) : ℕ := 9 * 10 ^ (d - 1) * d

  def blockDigits (d : ℕ) : List ℕ :=
    (List.range (9 * 10 ^ (d - 1))).flatMap (fun k => decDigits (10 ^ (d - 1) + k))

  def concatPrefix (N : ℕ) : List ℕ :=
    (List.range N).flatMap (fun k => decDigits (k + 1))

  def IsNthDigitOfC (n r : ℕ) : Prop :=
    ∀ N : ℕ, n ≤ (concatPrefix N).length → (concatPrefix N).getD (n - 1) 0 = r

  /-- The function returns a result r and r is the nth digit (1-indexed) of the infinite concatenation C = dec(1) ++ dec(2) ++ dec(3) ++ ..., where dec(k) is the standard decimal representation of k with no leading zeros. Equivalently, C is the infinite sequence 123456789101112131415..., and r is the integer value, between 0 and 9, of the nth character of C.
    Preconditions: n is an integer satisfying 1 <= n <= 2147483647 (i.e. 2^31 - 1). -/
  theorem spec_1 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 2147483647) :
      ∃ r, find_nth_digit n = ok r ∧
        ∃ d : ℕ, IsNthDigitOfC n.val.toNat d ∧ r.val = (d : ℤ) ∧ d ≤ 9 := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 2147483647), ∃ r, find_nth_digit n = ok r ∧
          ∃ d : ℕ, IsNthDigitOfC n.val.toNat d ∧ r.val = (d : ℤ) ∧ d ≤ 9) := by
    sorry

  /-- For every n with 1 <= n <= 2147483647, the function returns a result r; it does not fail (no overflow, out-of-bounds, or panic).
    Preconditions: n is an integer satisfying 1 <= n <= 2147483647 (i.e. 2^31 - 1). -/
  theorem spec_2 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 2147483647) :
      ∃ r, find_nth_digit n = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 2147483647), ∃ r, find_nth_digit n = ok r) := by
    sorry

  /-- 0 <= r <= 9.
    Preconditions: n is an integer with 1 <= n <= 2147483647, and the function returns a result r. -/
  theorem spec_3 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 2147483647) :
      ∀ r, find_nth_digit n = ok r → 0 ≤ r.val ∧ r.val ≤ 9 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 2147483647), ∀ r, find_nth_digit n = ok r → 0 ≤ r.val ∧ r.val ≤ 9) := by
    sorry

  /-- The function returns a result r and r = n.
    Preconditions: n is an integer with 1 <= n <= 9. -/
  theorem spec_4 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 9) :
      ∃ r, find_nth_digit n = ok r ∧ r.val = n.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 9), ∃ r, find_nth_digit n = ok r ∧ r.val = n.val) := by
    sorry

  /-- If n = 10 then the function returns 1; if n = 11 then the function returns 0.
    Preconditions: n is 10 or 11. -/
  theorem spec_5 (n : Std.I64) (hn : n.val = 10 ∨ n.val = 11) :
      (n.val = 10 → ∃ r, find_nth_digit n = ok r ∧ r.val = 1) ∧
        (n.val = 11 → ∃ r, find_nth_digit n = ok r ∧ r.val = 0) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : Std.I64) (hn : n.val = 10 ∨ n.val = 11), (n.val = 10 → ∃ r, find_nth_digit n = ok r ∧ r.val = 1) ∧
          (n.val = 11 → ∃ r, find_nth_digit n = ok r ∧ r.val = 0)) := by
    sorry

  /-- Whenever the function returns a result r, there exists a positive integer m >= 1 such that, with len(dec(k)) denoting the number of decimal digits of k and start(m) = 1 + sum_{k=1}^{m-1} len(dec(k)), we have start(m) <= n <= start(m) + len(dec(m)) - 1, and r is the (n - start(m) + 1)-th digit from the left (1-indexed) of dec(m).
    Preconditions: n is an integer with 1 <= n <= 2147483647. -/
  theorem spec_6 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 2147483647) :
      ∀ r, find_nth_digit n = ok r →
        ∃ m : ℕ, 1 ≤ m ∧ (startPos m : ℤ) ≤ n.val ∧
          n.val ≤ (startPos m : ℤ) + (lenDec m : ℤ) - 1 ∧
          r.val = (digitAt m (n.val - (startPos m : ℤ) + 1).toNat : ℤ) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 2147483647), ∀ r, find_nth_digit n = ok r →
          ∃ m : ℕ, 1 ≤ m ∧ (startPos m : ℤ) ≤ n.val ∧
            n.val ≤ (startPos m : ℤ) + (lenDec m : ℤ) - 1 ∧
            r.val = (digitAt m (n.val - (startPos m : ℤ) + 1).toNat : ℤ)) := by
    sorry

  /-- Let L(d) = sum_{i=1}^{d-1} 9*10^{i-1}*i for d >= 1, so L(1) = 0. If d is the unique positive integer such that L(d) < n <= L(d) + 9*10^{d-1}*d, then the function returns a result r and r is the digit at position n - L(d) (1-indexed) of the concatenation of the decimal representations of 10^{d-1}, 10^{d-1}+1, ..., 10^d - 1.
    Preconditions: n is an integer with 1 <= n <= 2147483647. -/
  theorem spec_7 (n : Std.I64) (d : ℕ) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 2147483647)
      (hd : 1 ≤ d) (hlo : (L d : ℤ) < n.val) (hhi : n.val ≤ (L d : ℤ) + (blockLen d : ℤ))
      (huniq : ∀ d' : ℕ, 1 ≤ d' → (L d' : ℤ) < n.val →
        n.val ≤ (L d' : ℤ) + (blockLen d' : ℤ) → d' = d) :
      ∃ r, find_nth_digit n = ok r ∧
        r.val = ((blockDigits d).getD (n.val - (L d : ℤ) - 1).toNat 0 : ℤ) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n : Std.I64) (d : ℕ) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 2147483647)
        (hd : 1 ≤ d) (hlo : (L d : ℤ) < n.val) (hhi : n.val ≤ (L d : ℤ) + (blockLen d : ℤ))
        (huniq : ∀ d' : ℕ, 1 ≤ d' → (L d' : ℤ) < n.val →
          n.val ≤ (L d' : ℤ) + (blockLen d' : ℤ) → d' = d), ∃ r, find_nth_digit n = ok r ∧
          r.val = ((blockDigits d).getD (n.val - (L d : ℤ) - 1).toNat 0 : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, let d be the unique positive integer with L(d) < n <= L(d) + 9*10^{d-1}*d, where L(d) = sum_{i=1}^{d-1} 9*10^{i-1}*i. Let q = n - L(d) - 1, let m = 10^{d-1} + (q div d), and let p = q mod d. Then r = (m div 10^{d-1-p}) mod 10.
    Preconditions: n is an integer with 1 <= n <= 2147483647. -/
  theorem spec_8 (n : Std.I64) (d : ℕ) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 2147483647)
      (hd : 1 ≤ d) (hlo : (L d : ℤ) < n.val) (hhi : n.val ≤ (L d : ℤ) + (blockLen d : ℤ))
      (huniq : ∀ d' : ℕ, 1 ≤ d' → (L d' : ℤ) < n.val →
        n.val ≤ (L d' : ℤ) + (blockLen d' : ℤ) → d' = d) :
      ∀ r, find_nth_digit n = ok r →
        let q : ℕ := (n.val - (L d : ℤ) - 1).toNat
        let m : ℕ := 10 ^ (d - 1) + q / d
        let p : ℕ := q % d
        r.val = (((m / 10 ^ (d - 1 - p)) % 10 : ℕ) : ℤ) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n : Std.I64) (d : ℕ) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 2147483647)
        (hd : 1 ≤ d) (hlo : (L d : ℤ) < n.val) (hhi : n.val ≤ (L d : ℤ) + (blockLen d : ℤ))
        (huniq : ∀ d' : ℕ, 1 ≤ d' → (L d' : ℤ) < n.val →
          n.val ≤ (L d' : ℤ) + (blockLen d' : ℤ) → d' = d), ∀ r, find_nth_digit n = ok r →
          let q : ℕ := (n.val - (L d : ℤ) - 1).toNat
          let m : ℕ := 10 ^ (d - 1) + q / d
          let p : ℕ := q % d
          r.val = (((m / 10 ^ (d - 1 - p)) % 10 : ℕ) : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, r is the most significant decimal digit of m; in particular 1 <= r <= 9.
    Preconditions: n is an integer with 1 <= n <= 2147483647, and m is a positive integer such that n = 1 + sum_{k=1}^{m-1} len(dec(k)), where len(dec(k)) is the number of decimal digits of k (so n is the first position of dec(m) in C). -/
  theorem spec_9 (n : Std.I64) (m : ℕ) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 2147483647)
      (hm : 1 ≤ m) (hnm : n.val = (startPos m : ℤ)) :
      ∀ r, find_nth_digit n = ok r → r.val = (digitAt m 1 : ℤ) ∧ 1 ≤ r.val ∧ r.val ≤ 9 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n : Std.I64) (m : ℕ) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 2147483647)
        (hm : 1 ≤ m) (hnm : n.val = (startPos m : ℤ)), ∀ r, find_nth_digit n = ok r → r.val = (digitAt m 1 : ℤ) ∧ 1 ≤ r.val ∧ r.val ≤ 9) := by
    sorry

  /-- Whenever the function returns a result r, r = m mod 10.
    Preconditions: n is an integer with 1 <= n <= 2147483647, and m is a positive integer such that n = sum_{k=1}^{m} len(dec(k)), where len(dec(k)) is the number of decimal digits of k (so n is the last position of dec(m) in C). -/
  theorem spec_10 (n : Std.I64) (m : ℕ) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 2147483647)
      (hm : 1 ≤ m) (hnm : n.val = (endPos m : ℤ)) :
      ∀ r, find_nth_digit n = ok r → r.val = ((m % 10 : ℕ) : ℤ) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n : Std.I64) (m : ℕ) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 2147483647)
        (hm : 1 ≤ m) (hnm : n.val = (endPos m : ℤ)), ∀ r, find_nth_digit n = ok r → r.val = ((m % 10 : ℕ) : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r and r = 0, the nth position of C is not one of the first nine positions; equivalently n >= 10.
    Preconditions: n is an integer with 1 <= n <= 2147483647. -/
  theorem spec_11 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 2147483647) :
      ∀ r, find_nth_digit n = ok r → r.val = 0 → 10 ≤ n.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 2147483647), ∀ r, find_nth_digit n = ok r → r.val = 0 → 10 ≤ n.val) := by
    sorry

  /-- The function returns a result r and r = 2.
    Preconditions: n = 2147483647. -/
  theorem spec_12 (n : Std.I64) (hn : n.val = 2147483647) :
      ∃ r, find_nth_digit n = ok r ∧ r.val = 2 := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (n : Std.I64) (hn : n.val = 2147483647), ∃ r, find_nth_digit n = ok r ∧ r.val = 2) := by
    sorry

  end AegisSpec.FindNthDigit
