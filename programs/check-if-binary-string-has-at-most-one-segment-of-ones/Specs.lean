import Aegis.CheckOnesSegment.Code.Funs

/-!
# Specifications of `Aegis.CheckOnesSegment.check_ones_segment`

LeetCode problem `check-if-binary-string-has-at-most-one-segment-of-ones`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.CheckOnesSegment

  def byteAt (s : Slice U8) (i : Nat) : Option Nat := (s.val[i]?).map (fun b => b.val)

  def isOne (s : Slice U8) (i : Nat) : Prop := byteAt s i = some 49

  def isZero (s : Slice U8) (i : Nat) : Prop := byteAt s i = some 48

  def isBit (s : Slice U8) (i : Nat) : Prop := byteAt s i = some 48 ∨ byteAt s i = some 49

  instance instDecidableIsOne (s : Slice U8) (i : Nat) : Decidable (isOne s i) := by
    unfold isOne; infer_instance

  instance instDecidableIsZero (s : Slice U8) (i : Nat) : Decidable (isZero s i) := by
    unfold isZero; infer_instance

  instance instDecidableIsBit (s : Slice U8) (i : Nat) : Decidable (isBit s i) := by
    unfold isBit; infer_instance

  def IsMaximalOnesSegment (s : Slice U8) (l r : Nat) : Prop :=
    l ≤ r ∧ r < s.val.length ∧
      (∀ i, l ≤ i → i ≤ r → isOne s i) ∧
      (l = 0 ∨ isZero s (l - 1)) ∧
      (r = s.val.length - 1 ∨ isZero s (r + 1))

  def numOnesSegments (s : Slice U8) : Nat :=
    (List.range s.val.length).countP
      (fun i => decide (isOne s i ∧ (i = 0 ∨ isZero s (i - 1))))

  def numZeroOne (s : Slice U8) : Nat :=
    (List.range (s.val.length - 1)).countP
      (fun i => decide (isZero s i ∧ isOne s (i + 1)))

  def IsInsertZeros (s s' : Slice U8) : Prop :=
    ∃ φ : Nat → Nat,
      s.val.length < s'.val.length ∧
        φ 0 = 0 ∧
        (∀ i, i < s.val.length → φ i < s'.val.length ∧ byteAt s' (φ i) = byteAt s i) ∧
        (∀ i j, i < j → j < s.val.length → φ i < φ j) ∧
        (∀ i, i < s'.val.length → (∃ j, j < s.val.length ∧ φ j = i) ∨ isZero s' i)

  /-- Whenever check_ones_segment returns a result r, r = true if and only if s contains at most one maximal contiguous segment of ones. A maximal contiguous segment of ones is a pair (l, r) with 0 <= l <= r < len(s) such that s[i] = '1' for every i with l <= i <= r, l = 0 or s[l-1] = '0', and r = len(s)-1 or s[r+1] = '0'. Equivalently, r = false exactly when there are two distinct such maximal segments.
    Preconditions: s is a valid input: 1 <= len(s) <= 100; for every i with 0 <= i < len(s), s[i] is the ASCII byte 48 ('0') or 49 ('1'); and s[0] = 49 ('1'). -/
  theorem spec_1 (s : Slice U8)
      (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100)
      (hbits : ∀ i, i < s.val.length → isBit s i)
      (hfirst : isOne s 0) :
      ∀ r, Aegis.CheckOnesSegment.check_ones_segment s = ok r →
        (r = true ↔ numOnesSegments s ≤ 1) ∧
          (r = false ↔
            ∃ l₁ r₁ l₂ r₂,
              IsMaximalOnesSegment s l₁ r₁ ∧ IsMaximalOnesSegment s l₂ r₂ ∧
                (l₁, r₁) ≠ (l₂, r₂)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s : Slice U8)
        (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100)
        (hbits : ∀ i, i < s.val.length → isBit s i)
        (hfirst : isOne s 0), ∀ r, Aegis.CheckOnesSegment.check_ones_segment s = ok r →
          (r = true ↔ numOnesSegments s ≤ 1) ∧
            (r = false ↔
              ∃ l₁ r₁ l₂ r₂,
                IsMaximalOnesSegment s l₁ r₁ ∧ IsMaximalOnesSegment s l₂ r₂ ∧
                  (l₁, r₁) ≠ (l₂, r₂))) := by
    sorry

  /-- The function check_ones_segment returns a result r (it does not fail, overflow, or panic) for every s satisfying the preconditions.
    Preconditions: s is a valid input: 1 <= len(s) <= 100; every s[i] is '0' or '1'; and s[0] = '1'. -/
  theorem spec_2 (s : Slice U8)
      (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100)
      (hbits : ∀ i, i < s.val.length → isBit s i)
      (hfirst : isOne s 0) :
      ∃ r, Aegis.CheckOnesSegment.check_ones_segment s = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s : Slice U8)
        (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100)
        (hbits : ∀ i, i < s.val.length → isBit s i)
        (hfirst : isOne s 0), ∃ r, Aegis.CheckOnesSegment.check_ones_segment s = ok r) := by
    sorry

  /-- Whenever check_ones_segment returns true, there exists an integer m with 1 <= m <= len(s) such that s[i] = '1' for every i with 0 <= i < m, and s[i] = '0' for every i with m <= i < len(s).
    Preconditions: s is a valid input: 1 <= len(s) <= 100; every s[i] is '0' or '1'; and s[0] = '1'. -/
  theorem spec_3 (s : Slice U8)
      (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100)
      (hbits : ∀ i, i < s.val.length → isBit s i)
      (hfirst : isOne s 0) :
      ∀ r, Aegis.CheckOnesSegment.check_ones_segment s = ok r → r = true →
        ∃ m, 1 ≤ m ∧ m ≤ s.val.length ∧
          (∀ i, i < m → isOne s i) ∧
          (∀ i, m ≤ i → i < s.val.length → isZero s i) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s : Slice U8)
        (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100)
        (hbits : ∀ i, i < s.val.length → isBit s i)
        (hfirst : isOne s 0), ∀ r, Aegis.CheckOnesSegment.check_ones_segment s = ok r → r = true →
          ∃ m, 1 ≤ m ∧ m ≤ s.val.length ∧
            (∀ i, i < m → isOne s i) ∧
            (∀ i, m ≤ i → i < s.val.length → isZero s i)) := by
    sorry

  /-- Whenever check_ones_segment returns false, there exist indices j and k with 0 < j < k < len(s) such that s[j] = '0' and s[k] = '1'.
    Preconditions: s is a valid input: 1 <= len(s) <= 100; every s[i] is '0' or '1'; and s[0] = '1'. -/
  theorem spec_4 (s : Slice U8)
      (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100)
      (hbits : ∀ i, i < s.val.length → isBit s i)
      (hfirst : isOne s 0) :
      ∀ r, Aegis.CheckOnesSegment.check_ones_segment s = ok r → r = false →
        ∃ j k, 0 < j ∧ j < k ∧ k < s.val.length ∧ isZero s j ∧ isOne s k := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s : Slice U8)
        (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100)
        (hbits : ∀ i, i < s.val.length → isBit s i)
        (hfirst : isOne s 0), ∀ r, Aegis.CheckOnesSegment.check_ones_segment s = ok r → r = false →
          ∃ j k, 0 < j ∧ j < k ∧ k < s.val.length ∧ isZero s j ∧ isOne s k) := by
    sorry

  /-- If there exist indices j and k with 0 < j < k < len(s) such that s[j] = '0' and s[k] = '1', then whenever check_ones_segment returns a result r, r = false.
    Preconditions: s is a valid input: 1 <= len(s) <= 100; every s[i] is '0' or '1'; and s[0] = '1'. -/
  theorem spec_5 (s : Slice U8)
      (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100)
      (hbits : ∀ i, i < s.val.length → isBit s i)
      (hfirst : isOne s 0)
      (hwit : ∃ j k, 0 < j ∧ j < k ∧ k < s.val.length ∧ isZero s j ∧ isOne s k) :
      ∀ r, Aegis.CheckOnesSegment.check_ones_segment s = ok r → r = false := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s : Slice U8)
        (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100)
        (hbits : ∀ i, i < s.val.length → isBit s i)
        (hfirst : isOne s 0)
        (hwit : ∃ j k, 0 < j ∧ j < k ∧ k < s.val.length ∧ isZero s j ∧ isOne s k), ∀ r, Aegis.CheckOnesSegment.check_ones_segment s = ok r → r = false) := by
    sorry

  /-- Whenever check_ones_segment returns a result r: if no byte of s equals '0', then r = true; otherwise, letting z be the least index with s[z] = '0', r = true if and only if s[i] = '0' for every i with z <= i < len(s).
    Preconditions: s is a valid input: 1 <= len(s) <= 100; every s[i] is '0' or '1'; and s[0] = '1'. -/
  theorem spec_6 (s : Slice U8)
      (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100)
      (hbits : ∀ i, i < s.val.length → isBit s i)
      (hfirst : isOne s 0) :
      ∀ r, Aegis.CheckOnesSegment.check_ones_segment s = ok r →
        ((∀ i, i < s.val.length → ¬ isZero s i) → r = true) ∧
          (∀ z, isZero s z → (∀ i, i < z → ¬ isZero s i) →
            (r = true ↔ ∀ i, z ≤ i → i < s.val.length → isZero s i)) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s : Slice U8)
        (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100)
        (hbits : ∀ i, i < s.val.length → isBit s i)
        (hfirst : isOne s 0), ∀ r, Aegis.CheckOnesSegment.check_ones_segment s = ok r →
          ((∀ i, i < s.val.length → ¬ isZero s i) → r = true) ∧
            (∀ z, isZero s z → (∀ i, i < z → ¬ isZero s i) →
              (r = true ↔ ∀ i, z ≤ i → i < s.val.length → isZero s i))) := by
    sorry

  /-- Let s' be the string obtained by appending n bytes equal to '0' to s. If check_ones_segment returns r on s and r' on s', then r = r'.
    Preconditions: s is a valid input: 1 <= len(s) <= 100; every s[i] is '0' or '1'; and s[0] = '1'. Let n >= 0 be such that len(s)+n <= 100. -/
  theorem spec_7 (s s' : Slice U8) (n : Nat)
      (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100)
      (hbits : ∀ i, i < s.val.length → isBit s i)
      (hfirst : isOne s 0)
      (hn : s.val.length + n ≤ 100)
      (hs' : s'.val = s.val ++ List.replicate n 48#u8) :
      ∀ r r', Aegis.CheckOnesSegment.check_ones_segment s = ok r →
        Aegis.CheckOnesSegment.check_ones_segment s' = ok r' → r = r' := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s s' : Slice U8) (n : Nat)
        (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100)
        (hbits : ∀ i, i < s.val.length → isBit s i)
        (hfirst : isOne s 0)
        (hn : s.val.length + n ≤ 100)
        (hs' : s'.val = s.val ++ List.replicate n 48#u8), ∀ r r', Aegis.CheckOnesSegment.check_ones_segment s = ok r →
          Aegis.CheckOnesSegment.check_ones_segment s' = ok r' → r = r') := by
    sorry

  /-- Let s' be the string obtained by prepending one byte equal to '1' to s, so s'[0]='1' and s'[i+1]=s[i] for 0 <= i < len(s). If check_ones_segment returns r on s and r' on s', then r = r'.
    Preconditions: s is a valid input: 1 <= len(s) <= 100; every s[i] is '0' or '1'; and s[0] = '1'. Also len(s) <= 99. -/
  theorem spec_8 (s s' : Slice U8)
      (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100)
      (hbits : ∀ i, i < s.val.length → isBit s i)
      (hfirst : isOne s 0)
      (hlen99 : s.val.length ≤ 99)
      (hs' : s'.val = 49#u8 :: s.val) :
      ∀ r r', Aegis.CheckOnesSegment.check_ones_segment s = ok r →
        Aegis.CheckOnesSegment.check_ones_segment s' = ok r' → r = r' := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s s' : Slice U8)
        (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100)
        (hbits : ∀ i, i < s.val.length → isBit s i)
        (hfirst : isOne s 0)
        (hlen99 : s.val.length ≤ 99)
        (hs' : s'.val = 49#u8 :: s.val), ∀ r r', Aegis.CheckOnesSegment.check_ones_segment s = ok r →
          Aegis.CheckOnesSegment.check_ones_segment s' = ok r' → r = r') := by
    sorry

  /-- For the concatenation s ++ t, whenever check_ones_segment returns a result r, r = false.
    Preconditions: s is a valid input: 1 <= len(s) <= 100; every s[i] is '0' or '1'; s[0] = '1'; and check_ones_segment returns false on s. Let t be any byte sequence of length m with every byte '0' or '1' and len(s)+m <= 100. -/
  theorem spec_9 (s s' : Slice U8) (t : List U8) (m : Nat)
      (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100)
      (hbits : ∀ i, i < s.val.length → isBit s i)
      (hfirst : isOne s 0)
      (hfalse : Aegis.CheckOnesSegment.check_ones_segment s = ok false)
      (ht_len : t.length = m)
      (ht_bits : ∀ b, b ∈ t → b.val = 48 ∨ b.val = 49)
      (hlen : s.val.length + m ≤ 100)
      (hs' : s'.val = s.val ++ t) :
      ∀ r, Aegis.CheckOnesSegment.check_ones_segment s' = ok r → r = false := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s s' : Slice U8) (t : List U8) (m : Nat)
        (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100)
        (hbits : ∀ i, i < s.val.length → isBit s i)
        (hfirst : isOne s 0)
        (hfalse : Aegis.CheckOnesSegment.check_ones_segment s = ok false)
        (ht_len : t.length = m)
        (ht_bits : ∀ b, b ∈ t → b.val = 48 ∨ b.val = 49)
        (hlen : s.val.length + m ≤ 100)
        (hs' : s'.val = s.val ++ t), ∀ r, Aegis.CheckOnesSegment.check_ones_segment s' = ok r → r = false) := by
    sorry

  /-- Whenever check_ones_segment returns a result r on s', r = false.
    Preconditions: s is a valid input: 1 <= len(s) <= 100; every s[i] is '0' or '1'; s[0] = '1'; and check_ones_segment returns false on s. Let s' be any string obtained from s by inserting one or more bytes equal to '0' at positions strictly greater than 0, with len(s') <= 100. -/
  theorem spec_10 (s s' : Slice U8)
      (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100)
      (hbits : ∀ i, i < s.val.length → isBit s i)
      (hfirst : isOne s 0)
      (hfalse : Aegis.CheckOnesSegment.check_ones_segment s = ok false)
      (hlen' : s'.val.length ≤ 100)
      (hins : IsInsertZeros s s') :
      ∀ r, Aegis.CheckOnesSegment.check_ones_segment s' = ok r → r = false := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (s s' : Slice U8)
        (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100)
        (hbits : ∀ i, i < s.val.length → isBit s i)
        (hfirst : isOne s 0)
        (hfalse : Aegis.CheckOnesSegment.check_ones_segment s = ok false)
        (hlen' : s'.val.length ≤ 100)
        (hins : IsInsertZeros s s'), ∀ r, Aegis.CheckOnesSegment.check_ones_segment s' = ok r → r = false) := by
    sorry

  /-- Let s0 be the string obtained from s by deleting every byte equal to '0'. Then s0 is nonempty, every byte of s0 is '1', and whenever check_ones_segment returns a result r on s0, r = true.
    Preconditions: s is a valid input: 1 <= len(s) <= 100; every s[i] is '0' or '1'; s[0] = '1'; and check_ones_segment returns true on s. -/
  theorem spec_11 (s s0 : Slice U8)
      (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100)
      (hbits : ∀ i, i < s.val.length → isBit s i)
      (hfirst : isOne s 0)
      (htrue : Aegis.CheckOnesSegment.check_ones_segment s = ok true)
      (hs0 : s0.val = s.val.filter (fun b => b.val != 48)) :
      1 ≤ s0.val.length ∧
        (∀ i, i < s0.val.length → isOne s0 i) ∧
        (∀ r, Aegis.CheckOnesSegment.check_ones_segment s0 = ok r → r = true) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (s s0 : Slice U8)
        (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100)
        (hbits : ∀ i, i < s.val.length → isBit s i)
        (hfirst : isOne s 0)
        (htrue : Aegis.CheckOnesSegment.check_ones_segment s = ok true)
        (hs0 : s0.val = s.val.filter (fun b => b.val != 48)), 1 ≤ s0.val.length ∧
          (∀ i, i < s0.val.length → isOne s0 i) ∧
          (∀ r, Aegis.CheckOnesSegment.check_ones_segment s0 = ok r → r = true)) := by
    sorry

  /-- The function check_ones_segment returns true on s.
    Preconditions: m and n are integers with 1 <= m, 0 <= n, and m+n <= 100. s is the binary string of length m+n with s[i] = '1' for 0 <= i < m and s[i] = '0' for m <= i < m+n. -/
  theorem spec_12 (s : Slice U8) (m n : Nat)
      (hm : 1 ≤ m) (hn : 0 ≤ n) (hsum : m + n ≤ 100)
      (hlen : s.val.length = m + n)
      (hones : ∀ i, i < m → isOne s i)
      (hzeros : ∀ i, m ≤ i → i < m + n → isZero s i) :
      Aegis.CheckOnesSegment.check_ones_segment s = ok true := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (s : Slice U8) (m n : Nat)
        (hm : 1 ≤ m) (hn : 0 ≤ n) (hsum : m + n ≤ 100)
        (hlen : s.val.length = m + n)
        (hones : ∀ i, i < m → isOne s i)
        (hzeros : ∀ i, m ≤ i → i < m + n → isZero s i), Aegis.CheckOnesSegment.check_ones_segment s = ok true) := by
    sorry

  /-- The function check_ones_segment returns false on s.
    Preconditions: a, b, c are integers with 1 <= a, 1 <= b, 1 <= c, and a+b+c <= 100. s is the binary string of length a+b+c with s[i] = '1' for 0 <= i < a, s[i] = '0' for a <= i < a+b, and s[i] = '1' for a+b <= i < a+b+c. -/
  theorem spec_13 (s : Slice U8) (a b c : Nat)
      (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hsum : a + b + c ≤ 100)
      (hlen : s.val.length = a + b + c)
      (h₁ : ∀ i, i < a → isOne s i)
      (h₂ : ∀ i, a ≤ i → i < a + b → isZero s i)
      (h₃ : ∀ i, a + b ≤ i → i < a + b + c → isOne s i) :
      Aegis.CheckOnesSegment.check_ones_segment s = ok false := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (s : Slice U8) (a b c : Nat)
        (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hsum : a + b + c ≤ 100)
        (hlen : s.val.length = a + b + c)
        (h₁ : ∀ i, i < a → isOne s i)
        (h₂ : ∀ i, a ≤ i → i < a + b → isZero s i)
        (h₃ : ∀ i, a + b ≤ i → i < a + b + c → isOne s i), Aegis.CheckOnesSegment.check_ones_segment s = ok false) := by
    sorry

  /-- Whenever check_ones_segment returns a result r, the number of maximal contiguous segments of ones in s is exactly 1 if r = true, and is at least 2 if r = false.
    Preconditions: s is a valid input: 1 <= len(s) <= 100; every s[i] is '0' or '1'; and s[0] = '1'. -/
  theorem spec_14 (s : Slice U8)
      (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100)
      (hbits : ∀ i, i < s.val.length → isBit s i)
      (hfirst : isOne s 0) :
      ∀ r, Aegis.CheckOnesSegment.check_ones_segment s = ok r →
        (r = true → numOnesSegments s = 1) ∧ (r = false → 2 ≤ numOnesSegments s) := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (s : Slice U8)
        (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100)
        (hbits : ∀ i, i < s.val.length → isBit s i)
        (hfirst : isOne s 0), ∀ r, Aegis.CheckOnesSegment.check_ones_segment s = ok r →
          (r = true → numOnesSegments s = 1) ∧ (r = false → 2 ≤ numOnesSegments s)) := by
    sorry

  /-- Whenever check_ones_segment returns a result r, the number of maximal contiguous segments of ones in s is 1 + the number of indices i with 0 <= i < len(s)-1, s[i] = '0', and s[i+1] = '1'. In particular, r = true exactly when this number is 1, and r = false exactly when it is at least 2.
    Preconditions: s is a valid input: 1 <= len(s) <= 100; every s[i] is '0' or '1'; and s[0] = '1'. -/
  theorem spec_15 (s : Slice U8)
      (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100)
      (hbits : ∀ i, i < s.val.length → isBit s i)
      (hfirst : isOne s 0) :
      ∀ r, Aegis.CheckOnesSegment.check_ones_segment s = ok r →
        numOnesSegments s = 1 + numZeroOne s ∧
          (r = true ↔ numOnesSegments s = 1) ∧
          (r = false ↔ 2 ≤ numOnesSegments s) := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (s : Slice U8)
        (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100)
        (hbits : ∀ i, i < s.val.length → isBit s i)
        (hfirst : isOne s 0), ∀ r, Aegis.CheckOnesSegment.check_ones_segment s = ok r →
          numOnesSegments s = 1 + numZeroOne s ∧
            (r = true ↔ numOnesSegments s = 1) ∧
            (r = false ↔ 2 ≤ numOnesSegments s)) := by
    sorry

  end AegisSpec.CheckOnesSegment
