import Aegis.NumberOfSubstrings.Code.Funs

/-!
# Specifications of `Aegis.NumberOfSubstrings.number_of_substrings`

LeetCode problem `count-the-number-of-substrings-with-dominant-ones`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.NumberOfSubstrings

  namespace AegisSpec.NumberOfSubstrings

  def indicesFromTo (i j : Nat) : List Nat := (List.range (j + 1)).drop i

  def countByte (l : List Std.U8) (b : Std.U8) (i j : Nat) : Nat :=
    (indicesFromTo i j).countP (fun k => l[k]? == some b)

  def zerosIn (l : List Std.U8) (i j : Nat) : Nat := countByte l 48#u8 i j

  def onesIn (l : List Std.U8) (i j : Nat) : Nat := countByte l 49#u8 i j

  def IsBitString (l : List Std.U8) : Prop :=
    ∀ k, k < l.length → l[k]? = some 48#u8 ∨ l[k]? = some 49#u8

  def countedPairB (l : List Std.U8) (i j : Nat) : Bool :=
    decide (i ≤ j ∧ zerosIn l i j ^ 2 ≤ onesIn l i j)

  def countedPairCount (l : List Std.U8) : Nat :=
    ((List.range l.length).product (List.range l.length)).countP
      (fun p => countedPairB l p.1 p.2)

  def allOnesB (l : List Std.U8) (i j : Nat) : Bool :=
    (indicesFromTo i j).all (fun k => l[k]? == some 49#u8)

  def allOnesPairCount (l : List Std.U8) : Nat :=
    ((List.range l.length).product (List.range l.length)).countP
      (fun p => decide (p.1 ≤ p.2) && allOnesB l p.1 p.2)

  def extendByOneCount (l : List Std.U8) : Nat :=
    (List.range (l.length + 1)).countP
      (fun i => decide (zerosIn l i (l.length - 1) ^ 2 ≤ onesIn l i (l.length - 1) + 1))

  def extendByZeroCount (l : List Std.U8) : Nat :=
    (List.range (l.length + 1)).countP
      (fun i => decide ((zerosIn l i (l.length - 1) + 1) ^ 2 ≤ onesIn l i (l.length - 1)))

  /-- Let n = len(s). For 0 <= i <= j < n, let zeros(s,i,j) be the number of indices k with i <= k <= j and s[k] = 48, and let ones(s,i,j) be the number of indices k with i <= k <= j and s[k] = 49. The function returns a result r and r is exactly the number of pairs (i,j) such that 0 <= i <= j < n and ones(s,i,j) >= (zeros(s,i,j))^2. Equivalently, r counts all non-empty contiguous substrings of s that have at least as many '1' bytes as the square of their number of '0' bytes.
    Preconditions: len(s) >= 1 and len(s) <= 40000, and for every k with 0 <= k < len(s), s[k] is either 48 (the ASCII code for '0') or 49 (the ASCII code for '1'). -/
  theorem spec_1 (s : Slice Std.U8)
      (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 40000)
      (h_bits : IsBitString s.val) :
      ∃ r : Std.I64,
        number_of_substrings s = ok r ∧ r.val = (countedPairCount s.val : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s : Slice Std.U8)
        (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 40000)
        (h_bits : IsBitString s.val), ∃ r : Std.I64,
          number_of_substrings s = ok r ∧ r.val = (countedPairCount s.val : Int)) := by
    sorry

  /-- For every such s, the function returns a result r for some 64-bit integer r; it does not fail, panic, or overflow.
    Preconditions: len(s) >= 1 and len(s) <= 40000, and for every k with 0 <= k < len(s), s[k] is either 48 or 49. -/
  theorem spec_2 (s : Slice Std.U8)
      (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 40000)
      (h_bits : IsBitString s.val) :
      ∃ r : Std.I64, number_of_substrings s = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s : Slice Std.U8)
        (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 40000)
        (h_bits : IsBitString s.val), ∃ r : Std.I64, number_of_substrings s = ok r) := by
    sorry

  /-- Whenever the function returns a result r, r >= 0.
    Preconditions: len(s) >= 1 and len(s) <= 40000, and for every k with 0 <= k < len(s), s[k] is either 48 or 49. -/
  theorem spec_3 (s : Slice Std.U8)
      (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 40000)
      (h_bits : IsBitString s.val) :
      ∀ r : Std.I64, number_of_substrings s = ok r → 0 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s : Slice Std.U8)
        (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 40000)
        (h_bits : IsBitString s.val), ∀ r : Std.I64, number_of_substrings s = ok r → 0 ≤ r.val) := by
    sorry

  /-- Let n = len(s). Whenever the function returns a result r, r <= n * (n + 1) / 2.
    Preconditions: len(s) >= 1 and len(s) <= 40000, and for every k with 0 <= k < len(s), s[k] is either 48 or 49. -/
  theorem spec_4 (s : Slice Std.U8)
      (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 40000)
      (h_bits : IsBitString s.val) :
      ∀ r : Std.I64, number_of_substrings s = ok r →
        r.val ≤ (s.val.length : Int) * ((s.val.length : Int) + 1) / 2 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s : Slice Std.U8)
        (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 40000)
        (h_bits : IsBitString s.val), ∀ r : Std.I64, number_of_substrings s = ok r →
          r.val ≤ (s.val.length : Int) * ((s.val.length : Int) + 1) / 2) := by
    sorry

  /-- Let n = len(s), and let z be the number of indices k with 0 <= k < n and s[k] = 48. Whenever the function returns a result r, r <= n * (n + 1) / 2 - z.
    Preconditions: len(s) >= 1 and len(s) <= 40000, and for every k with 0 <= k < len(s), s[k] is either 48 or 49. -/
  theorem spec_5 (s : Slice Std.U8)
      (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 40000)
      (h_bits : IsBitString s.val) :
      ∀ r : Std.I64, number_of_substrings s = ok r →
        r.val ≤ (s.val.length : Int) * ((s.val.length : Int) + 1) / 2 -
          (zerosIn s.val 0 (s.val.length - 1) : Int) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s : Slice Std.U8)
        (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 40000)
        (h_bits : IsBitString s.val), ∀ r : Std.I64, number_of_substrings s = ok r →
          r.val ≤ (s.val.length : Int) * ((s.val.length : Int) + 1) / 2 -
            (zerosIn s.val 0 (s.val.length - 1) : Int)) := by
    sorry

  /-- Let A be the number of pairs (i,j) with 0 <= i <= j < len(s) such that for every k with i <= k <= j, s[k] = 49. Whenever the function returns a result r, r >= A.
    Preconditions: len(s) >= 1 and len(s) <= 40000, and for every k with 0 <= k < len(s), s[k] is either 48 or 49. -/
  theorem spec_6 (s : Slice Std.U8)
      (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 40000)
      (h_bits : IsBitString s.val) :
      ∀ r : Std.I64, number_of_substrings s = ok r → (allOnesPairCount s.val : Int) ≤ r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s : Slice Std.U8)
        (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 40000)
        (h_bits : IsBitString s.val), ∀ r : Std.I64, number_of_substrings s = ok r → (allOnesPairCount s.val : Int) ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r on input s and a result r' on input rev(s), we have r = r'.
    Preconditions: len(s) = n with 1 <= n <= 40000, and for every k with 0 <= k < n, s[k] is either 48 or 49. Let rev(s) be the byte array of length n with rev(s)[k] = s[n-1-k] for every k with 0 <= k < n. -/
  theorem spec_7 (s t : Slice Std.U8) (n : Nat)
      (h_len : s.val.length = n) (h_n_ge : 1 ≤ n) (h_n_le : n ≤ 40000)
      (h_bits : IsBitString s.val)
      (h_len_t : t.val.length = n)
      (h_rev : ∀ k, k < n → t.val[k]? = s.val[n - 1 - k]?) :
      ∀ r r' : Std.I64,
        number_of_substrings s = ok r → number_of_substrings t = ok r' → r = r' := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s t : Slice Std.U8) (n : Nat)
        (h_len : s.val.length = n) (h_n_ge : 1 ≤ n) (h_n_le : n ≤ 40000)
        (h_bits : IsBitString s.val)
        (h_len_t : t.val.length = n)
        (h_rev : ∀ k, k < n → t.val[k]? = s.val[n - 1 - k]?), ∀ r r' : Std.I64,
          number_of_substrings s = ok r → number_of_substrings t = ok r' → r = r') := by
    sorry

  /-- Whenever the function returns a result r on input s and a result r_t on input t, r_t = r + C, where C is the number of indices i with 0 <= i <= n such that ones_s(i,n-1) + 1 >= (zeros_s(i,n-1))^2. Here zeros_s(i,n-1) is the number of k with i <= k < n and s[k] = 48, and ones_s(i,n-1) is the number of k with i <= k < n and s[k] = 49 (both are 0 when i = n).
    Preconditions: len(s) = n with 1 <= n <= 39999, and for every k with 0 <= k < n, s[k] is either 48 or 49. Let t be the byte array of length n+1 with t[k] = s[k] for 0 <= k < n and t[n] = 49 (append a '1'). -/
  theorem spec_8 (s t : Slice Std.U8) (n : Nat)
      (h_len : s.val.length = n) (h_n_ge : 1 ≤ n) (h_n_le : n ≤ 39999)
      (h_bits : IsBitString s.val)
      (h_len_t : t.val.length = n + 1)
      (h_prefix : ∀ k, k < n → t.val[k]? = s.val[k]?)
      (h_last : t.val[n]? = some 49#u8) :
      ∀ r r_t : Std.I64,
        number_of_substrings s = ok r → number_of_substrings t = ok r_t →
        r_t.val = r.val + (extendByOneCount s.val : Int) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s t : Slice Std.U8) (n : Nat)
        (h_len : s.val.length = n) (h_n_ge : 1 ≤ n) (h_n_le : n ≤ 39999)
        (h_bits : IsBitString s.val)
        (h_len_t : t.val.length = n + 1)
        (h_prefix : ∀ k, k < n → t.val[k]? = s.val[k]?)
        (h_last : t.val[n]? = some 49#u8), ∀ r r_t : Std.I64,
          number_of_substrings s = ok r → number_of_substrings t = ok r_t →
          r_t.val = r.val + (extendByOneCount s.val : Int)) := by
    sorry

  /-- Whenever the function returns a result r on input s and a result r' on input s', we have r' >= r.
    Preconditions: len(s) = n with 1 <= n <= 40000, and for every k with 0 <= k < n, s[k] is either 48 or 49. Let p be an index with 0 <= p < n and s[p] = 48, and let s' be the byte array of length n with s'[p] = 49 and s'[k] = s[k] for every k with 0 <= k < n and k != p. -/
  theorem spec_9 (s s' : Slice Std.U8) (n p : Nat)
      (h_len : s.val.length = n) (h_n_ge : 1 ≤ n) (h_n_le : n ≤ 40000)
      (h_bits : IsBitString s.val)
      (h_p : p < n) (h_zero : s.val[p]? = some 48#u8)
      (h_len' : s'.val.length = n)
      (h_at_p : s'.val[p]? = some 49#u8)
      (h_other : ∀ k, k < n → k ≠ p → s'.val[k]? = s.val[k]?) :
      ∀ r r' : Std.I64,
        number_of_substrings s = ok r → number_of_substrings s' = ok r' → r.val ≤ r'.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s s' : Slice Std.U8) (n p : Nat)
        (h_len : s.val.length = n) (h_n_ge : 1 ≤ n) (h_n_le : n ≤ 40000)
        (h_bits : IsBitString s.val)
        (h_p : p < n) (h_zero : s.val[p]? = some 48#u8)
        (h_len' : s'.val.length = n)
        (h_at_p : s'.val[p]? = some 49#u8)
        (h_other : ∀ k, k < n → k ≠ p → s'.val[k]? = s.val[k]?), ∀ r r' : Std.I64,
          number_of_substrings s = ok r → number_of_substrings s' = ok r' → r.val ≤ r'.val) := by
    sorry

  /-- Whenever the function returns a result r on input s and a result r_t on input t, r_t = r + C, where C is the number of indices i with 0 <= i <= n such that ones_s(i,n-1) >= (zeros_s(i,n-1) + 1)^2. Here zeros_s(i,n-1) is the number of k with i <= k < n and s[k] = 48, and ones_s(i,n-1) is the number of k with i <= k < n and s[k] = 49 (both are 0 when i = n).
    Preconditions: len(s) = n with 1 <= n <= 39999, and for every k with 0 <= k < n, s[k] is either 48 or 49. Let t be the byte array of length n+1 with t[k] = s[k] for 0 <= k < n and t[n] = 48 (append a '0'). -/
  theorem spec_10 (s t : Slice Std.U8) (n : Nat)
      (h_len : s.val.length = n) (h_n_ge : 1 ≤ n) (h_n_le : n ≤ 39999)
      (h_bits : IsBitString s.val)
      (h_len_t : t.val.length = n + 1)
      (h_prefix : ∀ k, k < n → t.val[k]? = s.val[k]?)
      (h_last : t.val[n]? = some 48#u8) :
      ∀ r r_t : Std.I64,
        number_of_substrings s = ok r → number_of_substrings t = ok r_t →
        r_t.val = r.val + (extendByZeroCount s.val : Int) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (s t : Slice Std.U8) (n : Nat)
        (h_len : s.val.length = n) (h_n_ge : 1 ≤ n) (h_n_le : n ≤ 39999)
        (h_bits : IsBitString s.val)
        (h_len_t : t.val.length = n + 1)
        (h_prefix : ∀ k, k < n → t.val[k]? = s.val[k]?)
        (h_last : t.val[n]? = some 48#u8), ∀ r r_t : Std.I64,
          number_of_substrings s = ok r → number_of_substrings t = ok r_t →
          r_t.val = r.val + (extendByZeroCount s.val : Int)) := by
    sorry

  end AegisSpec.NumberOfSubstrings
