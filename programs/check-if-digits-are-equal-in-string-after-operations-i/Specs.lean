import Aegis.HasSameDigits.Code.Funs

/-!
# Specifications of `Aegis.HasSameDigits.has_same_digits`

LeetCode problem `check-if-digits-are-equal-in-string-after-operations-i`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.HasSameDigits

  open Aegis Aeneas Aeneas.Std

  def IsAsciiDigit (b : Std.U8) : Prop := 48 ≤ b.val ∧ b.val ≤ 57

  def AllDigits (s : Slice Std.U8) : Prop :=
    ∀ (i : Nat) (_hi : i < s.val.length), IsAsciiDigit (s.val[i]'(by omega))

  def digitList (s : Slice Std.U8) : List Nat := s.val.map (fun b => b.val - 48)

  def reduceStep (l : List Nat) : List Nat :=
    (l.zip (l.drop 1)).map (fun p => (p.1 + p.2) % 10)

  def digitSeq (s : Slice Std.U8) (k : Nat) : List Nat :=
    Nat.iterate reduceStep k (digitList s)

  def firstTwoEq : List Nat → Prop
    | a :: b :: _ => a = b
    | _ => False

  /-- Let d(i) = s[i] - 48 for 0 ≤ i < n. Define sequences a_0, a_1, ..., a_{n-2} recursively: a_0 is the sequence (d(0), d(1), ..., d(n-1)); for each k with 0 ≤ k < n-2, a_{k+1} is the sequence of length n-k-1 defined by a_{k+1}[i] = (a_k[i] + a_k[i+1]) mod 10 for 0 ≤ i < n-k-1. Let A = a_{n-2}[0] and B = a_{n-2}[1]. Then the function returns a result r and r = true if and only if A = B.
    Preconditions: len(s) = n, 3 ≤ n ≤ 100, and for every i with 0 ≤ i < n, s[i] is an ASCII digit (48 ≤ s[i] ≤ 57). -/
  theorem spec_1 (s : Slice Std.U8) (n : Nat)
      (h_len : s.val.length = n) (h_lower : 3 ≤ n) (h_upper : n ≤ 100)
      (h_digits : AllDigits s) :
      ∃ r : Bool,
        Aegis.HasSameDigits.has_same_digits s = ok r ∧
          (r = true ↔ firstTwoEq (digitSeq s (n - 2))) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s : Slice Std.U8) (n : Nat)
        (h_len : s.val.length = n) (h_lower : 3 ≤ n) (h_upper : n ≤ 100)
        (h_digits : AllDigits s), ∃ r : Bool,
          Aegis.HasSameDigits.has_same_digits s = ok r ∧
            (r = true ↔ firstTwoEq (digitSeq s (n - 2)))) := by
    sorry

  /-- The function returns a result r (i.e., it does not panic, overflow, or fail) for every input satisfying the preconditions.
    Preconditions: len(s) = n, 3 ≤ n ≤ 100, and for every i with 0 ≤ i < n, s[i] is an ASCII digit (48 ≤ s[i] ≤ 57). -/
  theorem spec_2 (s : Slice Std.U8) (n : Nat)
      (h_len : s.val.length = n) (h_lower : 3 ≤ n) (h_upper : n ≤ 100)
      (h_digits : AllDigits s) :
      ∃ r : Bool, Aegis.HasSameDigits.has_same_digits s = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s : Slice Std.U8) (n : Nat)
        (h_len : s.val.length = n) (h_lower : 3 ≤ n) (h_upper : n ≤ 100)
        (h_digits : AllDigits s), ∃ r : Bool, Aegis.HasSameDigits.has_same_digits s = ok r) := by
    sorry

  /-- The function returns a result r and r = true if and only if s[0] = s[2].
    Preconditions: len(s) = 3 and s consists of ASCII digits (48 ≤ s[i] ≤ 57 for 0 ≤ i < 3). -/
  theorem spec_3 (s : Slice Std.U8)
      (h_len : s.val.length = 3) (h_digits : AllDigits s) :
      ∃ r : Bool,
        Aegis.HasSameDigits.has_same_digits s = ok r ∧
          (r = true ↔ s.val[0] = s.val[2]) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s : Slice Std.U8)
        (h_len : s.val.length = 3) (h_digits : AllDigits s), ∃ r : Bool,
          Aegis.HasSameDigits.has_same_digits s = ok r ∧
            (r = true ↔ s.val[0] = s.val[2])) := by
    sorry

  /-- Let d(i) = s[i] - 48 for 0 ≤ i < 4. The function returns a result r and r = true if and only if (d(0)+d(1)) mod 10 = (d(2)+d(3)) mod 10.
    Preconditions: len(s) = 4 and s consists of ASCII digits (48 ≤ s[i] ≤ 57 for 0 ≤ i < 4). -/
  theorem spec_4 (s : Slice Std.U8)
      (h_len : s.val.length = 4) (h_digits : AllDigits s) :
      ∃ r : Bool,
        Aegis.HasSameDigits.has_same_digits s = ok r ∧
          (r = true ↔ ((s.val[0]).val + (s.val[1]).val) % 10 =
            ((s.val[2]).val + (s.val[3]).val) % 10) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s : Slice Std.U8)
        (h_len : s.val.length = 4) (h_digits : AllDigits s), ∃ r : Bool,
          Aegis.HasSameDigits.has_same_digits s = ok r ∧
            (r = true ↔ ((s.val[0]).val + (s.val[1]).val) % 10 =
              ((s.val[2]).val + (s.val[3]).val) % 10)) := by
    sorry

  /-- Suppose that for every i with 0 ≤ i < n, t[i] = s[n-1-i]. Let r_s be the result of the function on s and r_t the result on t. Then r_s = r_t.
    Preconditions: len(s) = n, 3 ≤ n ≤ 100, and for every i with 0 ≤ i < n, s[i] is an ASCII digit (48 ≤ s[i] ≤ 57). Also let t be a slice of the same length n satisfying the same digit precondition. -/
  theorem spec_5 (s t : Slice Std.U8) (n : Nat)
      (h_len_s : s.val.length = n) (h_lower : 3 ≤ n) (h_upper : n ≤ 100)
      (h_digits_s : AllDigits s)
      (h_len_t : t.val.length = n) (h_digits_t : AllDigits t)
      (h_rev : ∀ (i : Nat) (_hi : i < n),
        t.val[i]'(by omega) = s.val[n - 1 - i]'(by omega)) :
      ∃ r_s r_t : Bool,
        Aegis.HasSameDigits.has_same_digits s = ok r_s ∧
          Aegis.HasSameDigits.has_same_digits t = ok r_t ∧ r_s = r_t := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s t : Slice Std.U8) (n : Nat)
        (h_len_s : s.val.length = n) (h_lower : 3 ≤ n) (h_upper : n ≤ 100)
        (h_digits_s : AllDigits s)
        (h_len_t : t.val.length = n) (h_digits_t : AllDigits t)
        (h_rev : ∀ (i : Nat) (_hi : i < n),
          t.val[i]'(by omega) = s.val[n - 1 - i]'(by omega)), ∃ r_s r_t : Bool,
          Aegis.HasSameDigits.has_same_digits s = ok r_s ∧
            Aegis.HasSameDigits.has_same_digits t = ok r_t ∧ r_s = r_t) := by
    sorry

  /-- Define t by t[i] = 48 + ((s[i] - 48 + c) mod 10) for 0 ≤ i < n. Let r_s be the result of the function on s and r_t the result on t. Then r_s = r_t.
    Preconditions: len(s) = n, 3 ≤ n ≤ 100, and for every i with 0 ≤ i < n, s[i] is an ASCII digit (48 ≤ s[i] ≤ 57). Let c be an integer with 0 ≤ c ≤ 9. -/
  theorem spec_6 (s t : Slice Std.U8) (n c : Nat)
      (h_len_s : s.val.length = n) (h_lower : 3 ≤ n) (h_upper : n ≤ 100)
      (h_digits_s : AllDigits s)
      (h_c_lower : 0 ≤ c) (h_c_upper : c ≤ 9)
      (h_len_t : t.val.length = n)
      (h_t : ∀ (i : Nat) (_hi : i < n),
        (t.val[i]'(by omega)).val = 48 + ((s.val[i]'(by omega)).val - 48 + c) % 10) :
      ∃ r_s r_t : Bool,
        Aegis.HasSameDigits.has_same_digits s = ok r_s ∧
          Aegis.HasSameDigits.has_same_digits t = ok r_t ∧ r_s = r_t := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s t : Slice Std.U8) (n c : Nat)
        (h_len_s : s.val.length = n) (h_lower : 3 ≤ n) (h_upper : n ≤ 100)
        (h_digits_s : AllDigits s)
        (h_c_lower : 0 ≤ c) (h_c_upper : c ≤ 9)
        (h_len_t : t.val.length = n)
        (h_t : ∀ (i : Nat) (_hi : i < n),
          (t.val[i]'(by omega)).val = 48 + ((s.val[i]'(by omega)).val - 48 + c) % 10), ∃ r_s r_t : Bool,
          Aegis.HasSameDigits.has_same_digits s = ok r_s ∧
            Aegis.HasSameDigits.has_same_digits t = ok r_t ∧ r_s = r_t) := by
    sorry

  /-- Define t by t[i] = 48 + (((s[i] - 48) * k) mod 10) for 0 ≤ i < n. Let r_s be the result of the function on s and r_t the result on t. Then r_s = r_t.
    Preconditions: len(s) = n, 3 ≤ n ≤ 100, and for every i with 0 ≤ i < n, s[i] is an ASCII digit (48 ≤ s[i] ≤ 57). Let k ∈ {1,3,7,9}. -/
  theorem spec_7 (s t : Slice Std.U8) (n k : Nat)
      (h_len_s : s.val.length = n) (h_lower : 3 ≤ n) (h_upper : n ≤ 100)
      (h_digits_s : AllDigits s)
      (h_k : k = 1 ∨ k = 3 ∨ k = 7 ∨ k = 9)
      (h_len_t : t.val.length = n)
      (h_t : ∀ (i : Nat) (_hi : i < n),
        (t.val[i]'(by omega)).val = 48 + ((s.val[i]'(by omega)).val - 48) * k % 10) :
      ∃ r_s r_t : Bool,
        Aegis.HasSameDigits.has_same_digits s = ok r_s ∧
          Aegis.HasSameDigits.has_same_digits t = ok r_t ∧ r_s = r_t := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s t : Slice Std.U8) (n k : Nat)
        (h_len_s : s.val.length = n) (h_lower : 3 ≤ n) (h_upper : n ≤ 100)
        (h_digits_s : AllDigits s)
        (h_k : k = 1 ∨ k = 3 ∨ k = 7 ∨ k = 9)
        (h_len_t : t.val.length = n)
        (h_t : ∀ (i : Nat) (_hi : i < n),
          (t.val[i]'(by omega)).val = 48 + ((s.val[i]'(by omega)).val - 48) * k % 10), ∃ r_s r_t : Bool,
          Aegis.HasSameDigits.has_same_digits s = ok r_s ∧
            Aegis.HasSameDigits.has_same_digits t = ok r_t ∧ r_s = r_t) := by
    sorry

  /-- Define t by t[i] = 48 + (9 - (s[i] - 48)) for 0 ≤ i < n (i.e., each digit d is replaced by 9-d). Let r_s be the result of the function on s and r_t the result on t. Then r_s = r_t.
    Preconditions: len(s) = n, 3 ≤ n ≤ 100, and for every i with 0 ≤ i < n, s[i] is an ASCII digit (48 ≤ s[i] ≤ 57). -/
  theorem spec_8 (s t : Slice Std.U8) (n : Nat)
      (h_len_s : s.val.length = n) (h_lower : 3 ≤ n) (h_upper : n ≤ 100)
      (h_digits_s : AllDigits s)
      (h_len_t : t.val.length = n)
      (h_t : ∀ (i : Nat) (_hi : i < n),
        (t.val[i]'(by omega)).val = 48 + (9 - ((s.val[i]'(by omega)).val - 48))) :
      ∃ r_s r_t : Bool,
        Aegis.HasSameDigits.has_same_digits s = ok r_s ∧
          Aegis.HasSameDigits.has_same_digits t = ok r_t ∧ r_s = r_t := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s t : Slice Std.U8) (n : Nat)
        (h_len_s : s.val.length = n) (h_lower : 3 ≤ n) (h_upper : n ≤ 100)
        (h_digits_s : AllDigits s)
        (h_len_t : t.val.length = n)
        (h_t : ∀ (i : Nat) (_hi : i < n),
          (t.val[i]'(by omega)).val = 48 + (9 - ((s.val[i]'(by omega)).val - 48))), ∃ r_s r_t : Bool,
          Aegis.HasSameDigits.has_same_digits s = ok r_s ∧
            Aegis.HasSameDigits.has_same_digits t = ok r_t ∧ r_s = r_t) := by
    sorry

  /-- The function returns a result r and r = true.
    Preconditions: len(s) = n, 3 ≤ n ≤ 100, for every i with 0 ≤ i < n, s[i] is an ASCII digit (48 ≤ s[i] ≤ 57), and for every i with 0 ≤ i < n, s[i] = s[n-1-i] (s is a palindrome). -/
  theorem spec_9 (s : Slice Std.U8) (n : Nat)
      (h_len : s.val.length = n) (h_lower : 3 ≤ n) (h_upper : n ≤ 100)
      (h_digits : AllDigits s)
      (h_palindrome : ∀ (i : Nat) (_hi : i < n),
        s.val[i]'(by omega) = s.val[n - 1 - i]'(by omega)) :
      ∃ r : Bool, Aegis.HasSameDigits.has_same_digits s = ok r ∧ r = true := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s : Slice Std.U8) (n : Nat)
        (h_len : s.val.length = n) (h_lower : 3 ≤ n) (h_upper : n ≤ 100)
        (h_digits : AllDigits s)
        (h_palindrome : ∀ (i : Nat) (_hi : i < n),
          s.val[i]'(by omega) = s.val[n - 1 - i]'(by omega)), ∃ r : Bool, Aegis.HasSameDigits.has_same_digits s = ok r ∧ r = true) := by
    sorry

  /-- Let d(i) = s[i] - 48 for 0 ≤ i < n. Define t to be the slice of length n-1 by t[i] = 48 + ((d(i) + d(i+1)) mod 10) for 0 ≤ i < n-1. Let r_s be the result of the function on s and r_t the result on t. Then r_s = r_t.
    Preconditions: len(s) = n, 4 ≤ n ≤ 100, and for every i with 0 ≤ i < n, s[i] is an ASCII digit (48 ≤ s[i] ≤ 57). -/
  theorem spec_10 (s t : Slice Std.U8) (n : Nat)
      (h_len_s : s.val.length = n) (h_lower : 4 ≤ n) (h_upper : n ≤ 100)
      (h_digits_s : AllDigits s)
      (h_len_t : t.val.length = n - 1)
      (h_t : ∀ (i : Nat) (_hi : i < n - 1),
        (t.val[i]'(by omega)).val =
          48 + (((s.val[i]'(by omega)).val - 48) +
            ((s.val[i + 1]'(by omega)).val - 48)) % 10) :
      ∃ r_s r_t : Bool,
        Aegis.HasSameDigits.has_same_digits s = ok r_s ∧
          Aegis.HasSameDigits.has_same_digits t = ok r_t ∧ r_s = r_t := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (s t : Slice Std.U8) (n : Nat)
        (h_len_s : s.val.length = n) (h_lower : 4 ≤ n) (h_upper : n ≤ 100)
        (h_digits_s : AllDigits s)
        (h_len_t : t.val.length = n - 1)
        (h_t : ∀ (i : Nat) (_hi : i < n - 1),
          (t.val[i]'(by omega)).val =
            48 + (((s.val[i]'(by omega)).val - 48) +
              ((s.val[i + 1]'(by omega)).val - 48)) % 10), ∃ r_s r_t : Bool,
          Aegis.HasSameDigits.has_same_digits s = ok r_s ∧
            Aegis.HasSameDigits.has_same_digits t = ok r_t ∧ r_s = r_t) := by
    sorry

  end AegisSpec.HasSameDigits
