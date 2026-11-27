import Aegis.RepeatedStringMatch.Code.Funs

/-!
# Specifications of `Aegis.RepeatedStringMatch.repeated_string_match`

LeetCode problem `repeated-string-match`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.RepeatedStringMatch

  namespace AegisSpec.RepeatedStringMatch

  def byteAt (l : List Std.U8) (i : ℕ) : Std.U8 := l.getD i default

  def rep (a : List Std.U8) (k : ℕ) : List Std.U8 :=
    (List.range (k * a.length)).map (fun t => byteAt a (t % a.length))

  def Occurs (b s : List Std.U8) : Prop :=
    ∃ j : ℕ, j + b.length ≤ s.length ∧ ∀ i : ℕ, i < b.length → byteAt s (j + i) = byteAt b i

  def LeastElem (P : ℕ → Prop) (n : ℕ) : Prop := P n ∧ ∀ k : ℕ, P k → n ≤ k

  /-- Definitions: for k >= 0, let a^k be the byte string of length k*len(a) whose t-th byte is a[t mod len(a)] for every 0 <= t < k*len(a); say that b occurs in a byte string s when there exists j with 0 <= j and j + len(b) <= len(s) such that s[j+i] = b[i] for every i with 0 <= i < len(b). Let K = { k | k >= 0 and b occurs in a^k }. Whenever the function returns a result r: if K is nonempty, then r equals the least element of K (in particular r >= 1); if K is empty, then r = -1.
    Preconditions: len(a) >= 1, len(b) >= 1, len(a) <= 10000, len(b) <= 10000, and every byte of a and b lies in 97..122 (lowercase English letters). -/
  theorem spec_1 (a b : Slice Std.U8)
      (ha_len : 1 ≤ a.val.length) (hb_len : 1 ≤ b.val.length)
      (ha_le : a.val.length ≤ 10000) (hb_le : b.val.length ≤ 10000)
      (ha_bytes : ∀ c ∈ a.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (hb_bytes : ∀ c ∈ b.val, 97 ≤ c.val ∧ c.val ≤ 122) :
      ∀ r : Std.I64, repeated_string_match a b = ok r →
        ((∃ k : ℕ, Occurs b.val (rep a.val k)) →
          ∃ n : ℕ, r.val = (n : ℤ) ∧ 1 ≤ n ∧
            LeastElem (fun k => Occurs b.val (rep a.val k)) n) ∧
        ((¬ ∃ k : ℕ, Occurs b.val (rep a.val k)) → r.val = -1) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (a b : Slice Std.U8)
        (ha_len : 1 ≤ a.val.length) (hb_len : 1 ≤ b.val.length)
        (ha_le : a.val.length ≤ 10000) (hb_le : b.val.length ≤ 10000)
        (ha_bytes : ∀ c ∈ a.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (hb_bytes : ∀ c ∈ b.val, 97 ≤ c.val ∧ c.val ≤ 122), ∀ r : Std.I64, repeated_string_match a b = ok r →
          ((∃ k : ℕ, Occurs b.val (rep a.val k)) →
            ∃ n : ℕ, r.val = (n : ℤ) ∧ 1 ≤ n ∧
              LeastElem (fun k => Occurs b.val (rep a.val k)) n) ∧
          ((¬ ∃ k : ℕ, Occurs b.val (rep a.val k)) → r.val = -1)) := by
    sorry

  /-- The function returns a result r; it never fails (no panic, no arithmetic overflow, no out-of-bounds access).
    Preconditions: len(a) >= 1, len(b) >= 1, len(a) <= 10000, len(b) <= 10000, every byte of a and b lies in 97..122. -/
  theorem spec_2 (a b : Slice Std.U8)
      (ha_len : 1 ≤ a.val.length) (hb_len : 1 ≤ b.val.length)
      (ha_le : a.val.length ≤ 10000) (hb_le : b.val.length ≤ 10000)
      (ha_bytes : ∀ c ∈ a.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (hb_bytes : ∀ c ∈ b.val, 97 ≤ c.val ∧ c.val ≤ 122) :
      ∃ r : Std.I64, repeated_string_match a b = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (a b : Slice Std.U8)
        (ha_len : 1 ≤ a.val.length) (hb_len : 1 ≤ b.val.length)
        (ha_le : a.val.length ≤ 10000) (hb_le : b.val.length ≤ 10000)
        (ha_bytes : ∀ c ∈ a.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (hb_bytes : ∀ c ∈ b.val, 97 ≤ c.val ∧ c.val ≤ 122), ∃ r : Std.I64, repeated_string_match a b = ok r) := by
    sorry

  /-- Using a^k and 'b occurs' as in spec_1: whenever the function returns a result r with r >= 1, b occurs in a^r. Equivalently, there exists j with 0 <= j and j + len(b) <= r*len(a) such that a[(j+i) mod len(a)] = b[i] for every i with 0 <= i < len(b).
    Preconditions: len(a) >= 1, len(b) >= 1, len(a) <= 10000, len(b) <= 10000, every byte of a and b lies in 97..122. -/
  theorem spec_3 (a b : Slice Std.U8)
      (ha_len : 1 ≤ a.val.length) (hb_len : 1 ≤ b.val.length)
      (ha_le : a.val.length ≤ 10000) (hb_le : b.val.length ≤ 10000)
      (ha_bytes : ∀ c ∈ a.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (hb_bytes : ∀ c ∈ b.val, 97 ≤ c.val ∧ c.val ≤ 122) :
      ∀ r : Std.I64, repeated_string_match a b = ok r → 1 ≤ r.val →
        Occurs b.val (rep a.val r.val.toNat) ∧
          ∃ j : ℕ, j + b.val.length ≤ r.val.toNat * a.val.length ∧
            ∀ i : ℕ, i < b.val.length →
              byteAt a.val ((j + i) % a.val.length) = byteAt b.val i := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (a b : Slice Std.U8)
        (ha_len : 1 ≤ a.val.length) (hb_len : 1 ≤ b.val.length)
        (ha_le : a.val.length ≤ 10000) (hb_le : b.val.length ≤ 10000)
        (ha_bytes : ∀ c ∈ a.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (hb_bytes : ∀ c ∈ b.val, 97 ≤ c.val ∧ c.val ≤ 122), ∀ r : Std.I64, repeated_string_match a b = ok r → 1 ≤ r.val →
          Occurs b.val (rep a.val r.val.toNat) ∧
            ∃ j : ℕ, j + b.val.length ≤ r.val.toNat * a.val.length ∧
              ∀ i : ℕ, i < b.val.length →
                byteAt a.val ((j + i) % a.val.length) = byteAt b.val i) := by
    sorry

  /-- Using a^k and 'b occurs' as in spec_1: whenever the function returns a result r with r >= 1, for every k with 0 <= k < r, b does not occur in a^k.
    Preconditions: len(a) >= 1, len(b) >= 1, len(a) <= 10000, len(b) <= 10000, every byte of a and b lies in 97..122. -/
  theorem spec_4 (a b : Slice Std.U8)
      (ha_len : 1 ≤ a.val.length) (hb_len : 1 ≤ b.val.length)
      (ha_le : a.val.length ≤ 10000) (hb_le : b.val.length ≤ 10000)
      (ha_bytes : ∀ c ∈ a.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (hb_bytes : ∀ c ∈ b.val, 97 ≤ c.val ∧ c.val ≤ 122) :
      ∀ r : Std.I64, repeated_string_match a b = ok r → 1 ≤ r.val →
        ∀ k : ℕ, k < r.val.toNat → ¬ Occurs b.val (rep a.val k) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (a b : Slice Std.U8)
        (ha_len : 1 ≤ a.val.length) (hb_len : 1 ≤ b.val.length)
        (ha_le : a.val.length ≤ 10000) (hb_le : b.val.length ≤ 10000)
        (ha_bytes : ∀ c ∈ a.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (hb_bytes : ∀ c ∈ b.val, 97 ≤ c.val ∧ c.val ≤ 122), ∀ r : Std.I64, repeated_string_match a b = ok r → 1 ≤ r.val →
          ∀ k : ℕ, k < r.val.toNat → ¬ Occurs b.val (rep a.val k)) := by
    sorry

  /-- Using a^k and 'b occurs' as in spec_1: whenever the function returns a result r, r = -1 if and only if for every k >= 0, b does not occur in a^k.
    Preconditions: len(a) >= 1, len(b) >= 1, len(a) <= 10000, len(b) <= 10000, every byte of a and b lies in 97..122. -/
  theorem spec_5 (a b : Slice Std.U8)
      (ha_len : 1 ≤ a.val.length) (hb_len : 1 ≤ b.val.length)
      (ha_le : a.val.length ≤ 10000) (hb_le : b.val.length ≤ 10000)
      (ha_bytes : ∀ c ∈ a.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (hb_bytes : ∀ c ∈ b.val, 97 ≤ c.val ∧ c.val ≤ 122) :
      ∀ r : Std.I64, repeated_string_match a b = ok r →
        (r.val = -1 ↔ ∀ k : ℕ, ¬ Occurs b.val (rep a.val k)) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (a b : Slice Std.U8)
        (ha_len : 1 ≤ a.val.length) (hb_len : 1 ≤ b.val.length)
        (ha_le : a.val.length ≤ 10000) (hb_le : b.val.length ≤ 10000)
        (ha_bytes : ∀ c ∈ a.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (hb_bytes : ∀ c ∈ b.val, 97 ≤ c.val ∧ c.val ≤ 122), ∀ r : Std.I64, repeated_string_match a b = ok r →
          (r.val = -1 ↔ ∀ k : ℕ, ¬ Occurs b.val (rep a.val k))) := by
    sorry

  /-- Whenever the function returns a result r: either r = -1, or r <= floor(len(b)/len(a)) + 2, where the division is integer division on the natural lengths.
    Preconditions: len(a) >= 1, len(b) >= 1, len(a) <= 10000, len(b) <= 10000, every byte of a and b lies in 97..122. -/
  theorem spec_6 (a b : Slice Std.U8)
      (ha_len : 1 ≤ a.val.length) (hb_len : 1 ≤ b.val.length)
      (ha_le : a.val.length ≤ 10000) (hb_le : b.val.length ≤ 10000)
      (ha_bytes : ∀ c ∈ a.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (hb_bytes : ∀ c ∈ b.val, 97 ≤ c.val ∧ c.val ≤ 122) :
      ∀ r : Std.I64, repeated_string_match a b = ok r →
        r.val = -1 ∨ r.val ≤ ((b.val.length / a.val.length + 2 : ℕ) : ℤ) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (a b : Slice Std.U8)
        (ha_len : 1 ≤ a.val.length) (hb_len : 1 ≤ b.val.length)
        (ha_le : a.val.length ≤ 10000) (hb_le : b.val.length ≤ 10000)
        (ha_bytes : ∀ c ∈ a.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (hb_bytes : ∀ c ∈ b.val, 97 ≤ c.val ∧ c.val ≤ 122), ∀ r : Std.I64, repeated_string_match a b = ok r →
          r.val = -1 ∨ r.val ≤ ((b.val.length / a.val.length + 2 : ℕ) : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r: r = -1 or r >= 1; in particular the value 0 is never returned.
    Preconditions: len(a) >= 1, len(b) >= 1, len(a) <= 10000, len(b) <= 10000, every byte of a and b lies in 97..122. -/
  theorem spec_7 (a b : Slice Std.U8)
      (ha_len : 1 ≤ a.val.length) (hb_len : 1 ≤ b.val.length)
      (ha_le : a.val.length ≤ 10000) (hb_le : b.val.length ≤ 10000)
      (ha_bytes : ∀ c ∈ a.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (hb_bytes : ∀ c ∈ b.val, 97 ≤ c.val ∧ c.val ≤ 122) :
      ∀ r : Std.I64, repeated_string_match a b = ok r → r.val = -1 ∨ 1 ≤ r.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (a b : Slice Std.U8)
        (ha_len : 1 ≤ a.val.length) (hb_len : 1 ≤ b.val.length)
        (ha_le : a.val.length ≤ 10000) (hb_le : b.val.length ≤ 10000)
        (ha_bytes : ∀ c ∈ a.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (hb_bytes : ∀ c ∈ b.val, 97 ≤ c.val ∧ c.val ≤ 122), ∀ r : Std.I64, repeated_string_match a b = ok r → r.val = -1 ∨ 1 ≤ r.val) := by
    sorry

  /-- Using a^k as in spec_1: whenever the function returns a result r with r >= 1, len(b) <= r * len(a).
    Preconditions: len(a) >= 1, len(b) >= 1, len(a) <= 10000, len(b) <= 10000, every byte of a and b lies in 97..122. -/
  theorem spec_8 (a b : Slice Std.U8)
      (ha_len : 1 ≤ a.val.length) (hb_len : 1 ≤ b.val.length)
      (ha_le : a.val.length ≤ 10000) (hb_le : b.val.length ≤ 10000)
      (ha_bytes : ∀ c ∈ a.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (hb_bytes : ∀ c ∈ b.val, 97 ≤ c.val ∧ c.val ≤ 122) :
      ∀ r : Std.I64, repeated_string_match a b = ok r → 1 ≤ r.val →
        b.val.length ≤ r.val.toNat * a.val.length := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (a b : Slice Std.U8)
        (ha_len : 1 ≤ a.val.length) (hb_len : 1 ≤ b.val.length)
        (ha_le : a.val.length ≤ 10000) (hb_le : b.val.length ≤ 10000)
        (ha_bytes : ∀ c ∈ a.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (hb_bytes : ∀ c ∈ b.val, 97 ≤ c.val ∧ c.val ≤ 122), ∀ r : Std.I64, repeated_string_match a b = ok r → 1 ≤ r.val →
          b.val.length ≤ r.val.toNat * a.val.length) := by
    sorry

  /-- Whenever the function returns a result r: r = 1 if and only if b occurs as a contiguous substring of a, i.e. there exists j with 0 <= j and j + len(b) <= len(a) such that a[j+i] = b[i] for every i with 0 <= i < len(b).
    Preconditions: len(a) >= 1, len(b) >= 1, len(a) <= 10000, len(b) <= 10000, every byte of a and b lies in 97..122. -/
  theorem spec_9 (a b : Slice Std.U8)
      (ha_len : 1 ≤ a.val.length) (hb_len : 1 ≤ b.val.length)
      (ha_le : a.val.length ≤ 10000) (hb_le : b.val.length ≤ 10000)
      (ha_bytes : ∀ c ∈ a.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (hb_bytes : ∀ c ∈ b.val, 97 ≤ c.val ∧ c.val ≤ 122) :
      ∀ r : Std.I64, repeated_string_match a b = ok r →
        (r.val = 1 ↔ Occurs b.val a.val) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (a b : Slice Std.U8)
        (ha_len : 1 ≤ a.val.length) (hb_len : 1 ≤ b.val.length)
        (ha_le : a.val.length ≤ 10000) (hb_le : b.val.length ≤ 10000)
        (ha_bytes : ∀ c ∈ a.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (hb_bytes : ∀ c ∈ b.val, 97 ≤ c.val ∧ c.val ≤ 122), ∀ r : Std.I64, repeated_string_match a b = ok r →
          (r.val = 1 ↔ Occurs b.val a.val)) := by
    sorry

  /-- Using a^1 and a^2 as in S1 (a^1 = a, a^2 = a concatenated with a): whenever the function returns a result r, if b does not occur in a^1 but b does occur in a^2, then r = 2.
    Preconditions: len(a) >= 1, len(b) >= 1, len(a) <= 10000, len(b) <= 10000, every byte of a and b lies in 97..122. -/
  theorem spec_10 (a b : Slice Std.U8)
      (ha_len : 1 ≤ a.val.length) (hb_len : 1 ≤ b.val.length)
      (ha_le : a.val.length ≤ 10000) (hb_le : b.val.length ≤ 10000)
      (ha_bytes : ∀ c ∈ a.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (hb_bytes : ∀ c ∈ b.val, 97 ≤ c.val ∧ c.val ≤ 122) :
      ∀ r : Std.I64, repeated_string_match a b = ok r →
        ¬ Occurs b.val (rep a.val 1) → Occurs b.val (rep a.val 2) → r.val = 2 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (a b : Slice Std.U8)
        (ha_len : 1 ≤ a.val.length) (hb_len : 1 ≤ b.val.length)
        (ha_le : a.val.length ≤ 10000) (hb_le : b.val.length ≤ 10000)
        (ha_bytes : ∀ c ∈ a.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (hb_bytes : ∀ c ∈ b.val, 97 ≤ c.val ∧ c.val ≤ 122), ∀ r : Std.I64, repeated_string_match a b = ok r →
          ¬ Occurs b.val (rep a.val 1) → Occurs b.val (rep a.val 2) → r.val = 2) := by
    sorry

  /-- Whenever the function returns a result r: if len(a) = 1, writing c = a[0], then r = len(b) if b[i] = c for every i with 0 <= i < len(b), and r = -1 otherwise.
    Preconditions: len(a) >= 1, len(b) >= 1, len(a) <= 10000, len(b) <= 10000, every byte of a and b lies in 97..122. -/
  theorem spec_11 (a b : Slice Std.U8)
      (ha_len : 1 ≤ a.val.length) (hb_len : 1 ≤ b.val.length)
      (ha_le : a.val.length ≤ 10000) (hb_le : b.val.length ≤ 10000)
      (ha_bytes : ∀ c ∈ a.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (hb_bytes : ∀ c ∈ b.val, 97 ≤ c.val ∧ c.val ≤ 122) :
      ∀ r : Std.I64, repeated_string_match a b = ok r → a.val.length = 1 →
        ((∀ i : ℕ, i < b.val.length → byteAt b.val i = byteAt a.val 0) →
            r.val = ((b.val.length : ℕ) : ℤ)) ∧
          (¬ (∀ i : ℕ, i < b.val.length → byteAt b.val i = byteAt a.val 0) →
            r.val = -1) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (a b : Slice Std.U8)
        (ha_len : 1 ≤ a.val.length) (hb_len : 1 ≤ b.val.length)
        (ha_le : a.val.length ≤ 10000) (hb_le : b.val.length ≤ 10000)
        (ha_bytes : ∀ c ∈ a.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (hb_bytes : ∀ c ∈ b.val, 97 ≤ c.val ∧ c.val ≤ 122), ∀ r : Std.I64, repeated_string_match a b = ok r → a.val.length = 1 →
          ((∀ i : ℕ, i < b.val.length → byteAt b.val i = byteAt a.val 0) →
              r.val = ((b.val.length : ℕ) : ℤ)) ∧
            (¬ (∀ i : ℕ, i < b.val.length → byteAt b.val i = byteAt a.val 0) →
              r.val = -1)) := by
    sorry

  /-- Whenever the function returns a result r: if len(b) = len(a), then (i) if b[i] = a[i] for every 0 <= i < len(a), then r = 1; (ii) if b is not equal to a but b occurs in a^2, then r = 2; (iii) if b does not occur in a^2, then r = -1.
    Preconditions: len(a) >= 1, len(b) >= 1, len(a) <= 10000, len(b) <= 10000, every byte of a and b lies in 97..122. -/
  theorem spec_12 (a b : Slice Std.U8)
      (ha_len : 1 ≤ a.val.length) (hb_len : 1 ≤ b.val.length)
      (ha_le : a.val.length ≤ 10000) (hb_le : b.val.length ≤ 10000)
      (ha_bytes : ∀ c ∈ a.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (hb_bytes : ∀ c ∈ b.val, 97 ≤ c.val ∧ c.val ≤ 122) :
      ∀ r : Std.I64, repeated_string_match a b = ok r → b.val.length = a.val.length →
        ((∀ i : ℕ, i < a.val.length → byteAt b.val i = byteAt a.val i) → r.val = 1) ∧
          ((¬ ∀ i : ℕ, i < a.val.length → byteAt b.val i = byteAt a.val i) →
            Occurs b.val (rep a.val 2) → r.val = 2) ∧
          (¬ Occurs b.val (rep a.val 2) → r.val = -1) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (a b : Slice Std.U8)
        (ha_len : 1 ≤ a.val.length) (hb_len : 1 ≤ b.val.length)
        (ha_le : a.val.length ≤ 10000) (hb_le : b.val.length ≤ 10000)
        (ha_bytes : ∀ c ∈ a.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (hb_bytes : ∀ c ∈ b.val, 97 ≤ c.val ∧ c.val ≤ 122), ∀ r : Std.I64, repeated_string_match a b = ok r → b.val.length = a.val.length →
          ((∀ i : ℕ, i < a.val.length → byteAt b.val i = byteAt a.val i) → r.val = 1) ∧
            ((¬ ∀ i : ℕ, i < a.val.length → byteAt b.val i = byteAt a.val i) →
              Occurs b.val (rep a.val 2) → r.val = 2) ∧
            (¬ Occurs b.val (rep a.val 2) → r.val = -1)) := by
    sorry

  /-- Using a^k and 'b occurs' as in spec_1: whenever the function returns a result r with r >= 1, b occurs in a^(floor(len(b)/len(a)) + 2).
    Preconditions: len(a) >= 1, len(b) >= 1, len(a) <= 10000, len(b) <= 10000, every byte of a and b lies in 97..122. -/
  theorem spec_13 (a b : Slice Std.U8)
      (ha_len : 1 ≤ a.val.length) (hb_len : 1 ≤ b.val.length)
      (ha_le : a.val.length ≤ 10000) (hb_le : b.val.length ≤ 10000)
      (ha_bytes : ∀ c ∈ a.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (hb_bytes : ∀ c ∈ b.val, 97 ≤ c.val ∧ c.val ≤ 122) :
      ∀ r : Std.I64, repeated_string_match a b = ok r → 1 ≤ r.val →
        Occurs b.val (rep a.val (b.val.length / a.val.length + 2)) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (a b : Slice Std.U8)
        (ha_len : 1 ≤ a.val.length) (hb_len : 1 ≤ b.val.length)
        (ha_le : a.val.length ≤ 10000) (hb_le : b.val.length ≤ 10000)
        (ha_bytes : ∀ c ∈ a.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (hb_bytes : ∀ c ∈ b.val, 97 ≤ c.val ∧ c.val ≤ 122), ∀ r : Std.I64, repeated_string_match a b = ok r → 1 ≤ r.val →
          Occurs b.val (rep a.val (b.val.length / a.val.length + 2))) := by
    sorry

  /-- Using a^k and 'b occurs' as in spec_1: whenever the function returns a result r with r >= 1, for every k with k >= r, b occurs in a^k.
    Preconditions: len(a) >= 1, len(b) >= 1, len(a) <= 10000, len(b) <= 10000, every byte of a and b lies in 97..122. -/
  theorem spec_14 (a b : Slice Std.U8)
      (ha_len : 1 ≤ a.val.length) (hb_len : 1 ≤ b.val.length)
      (ha_le : a.val.length ≤ 10000) (hb_le : b.val.length ≤ 10000)
      (ha_bytes : ∀ c ∈ a.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (hb_bytes : ∀ c ∈ b.val, 97 ≤ c.val ∧ c.val ≤ 122) :
      ∀ r : Std.I64, repeated_string_match a b = ok r → 1 ≤ r.val →
        ∀ k : ℕ, r.val.toNat ≤ k → Occurs b.val (rep a.val k) := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (a b : Slice Std.U8)
        (ha_len : 1 ≤ a.val.length) (hb_len : 1 ≤ b.val.length)
        (ha_le : a.val.length ≤ 10000) (hb_le : b.val.length ≤ 10000)
        (ha_bytes : ∀ c ∈ a.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (hb_bytes : ∀ c ∈ b.val, 97 ≤ c.val ∧ c.val ≤ 122), ∀ r : Std.I64, repeated_string_match a b = ok r → 1 ≤ r.val →
          ∀ k : ℕ, r.val.toNat ≤ k → Occurs b.val (rep a.val k)) := by
    sorry

  end AegisSpec.RepeatedStringMatch
