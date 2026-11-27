import Aegis.IsStrictlyPalindromic.Code.Funs

/-!
# Specifications of `Aegis.IsStrictlyPalindromic.is_strictly_palindromic`

LeetCode problem `strictly-palindromic-number`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.IsStrictlyPalindromic

  namespace AegisSpec.IsStrictlyPalindromic

  def digitsRev (b : Nat) (x : Nat) : List Nat :=
    if h : 1 < b ∧ 0 < x then x % b :: digitsRev b (x / b) else []
  termination_by x
  decreasing_by exact Nat.div_lt_self h.2 h.1

  def baseDigits (b x : Nat) : List Nat := (digitsRev b x).reverse

  def IsPalindrome (l : List Nat) : Prop := l.reverse = l

  def BasePalindromic (b x : Nat) : Prop := IsPalindrome (baseDigits b x)

  def StrictlyPalindromic (x : Nat) : Prop :=
    ∀ b : Nat, 2 ≤ b → b ≤ x - 2 → BasePalindromic b x

  /-- The call is_strictly_palindromic(n) returns a result r (it does not fail), and r = true if and only if n is strictly palindromic. Here n is strictly palindromic means: for every integer base b with 2 <= b <= n-2, the standard base-b representation of n is a palindrome. For x > 0 and b >= 2, the standard base-b representation is the unique digit sequence d_0,...,d_{k-1} (most significant digit first) with k >= 1, d_0 != 0, 0 <= d_i < b for all i, and x = sum_{i=0}^{k-1} d_i * b^{k-1-i}; it is palindromic iff d_i = d_{k-1-i} for every 0 <= i < k.
    Preconditions: n is an integer (Lean type Std.I64) satisfying 4 <= n <= 100000. -/
  theorem spec_1 (n : I64) (h_lo : 4 ≤ n.val) (h_hi : n.val ≤ 100000) :
      ∃ r : Bool,
        is_strictly_palindromic n = ok r ∧
          (r = true ↔ StrictlyPalindromic n.val.toNat) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : I64) (h_lo : 4 ≤ n.val) (h_hi : n.val ≤ 100000), ∃ r : Bool,
          is_strictly_palindromic n = ok r ∧
            (r = true ↔ StrictlyPalindromic n.val.toNat)) := by
    sorry

  /-- The call is_strictly_palindromic(n) returns a result (Ok) rather than failing, panicking, overflowing, or accessing an invalid index.
    Preconditions: n is an integer (Lean type Std.I64) satisfying 4 <= n <= 100000. -/
  theorem spec_2 (n : I64) (h_lo : 4 ≤ n.val) (h_hi : n.val ≤ 100000) :
      ∃ r : Bool, is_strictly_palindromic n = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : I64) (h_lo : 4 ≤ n.val) (h_hi : n.val ≤ 100000), ∃ r : Bool, is_strictly_palindromic n = ok r) := by
    sorry

  /-- Whenever the call is_strictly_palindromic(n) returns a result r, if r = false then the standard base-(n-2) representation of n (as defined in spec_1) is not palindromic. In fact this representation is always non-palindromic on the precondition: for n = 4 it is the three digits 1,0,0 in base 2; for n >= 5, since n = 1*(n-2) + 2 and 0 <= 2 < n-2, it is the two-digit string 12 in base n-2, whose digits 1 and 2 differ.
    Preconditions: n is an integer (Lean type Std.I64) satisfying 4 <= n <= 100000. -/
  theorem spec_3 (n : I64) (h_lo : 4 ≤ n.val) (h_hi : n.val ≤ 100000) :
      (∀ r : Bool,
          is_strictly_palindromic n = ok r → r = false →
            ¬ BasePalindromic (n.val - 2).toNat n.val.toNat) ∧
        ¬ BasePalindromic (n.val - 2).toNat n.val.toNat := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : I64) (h_lo : 4 ≤ n.val) (h_hi : n.val ≤ 100000), (∀ r : Bool,
            is_strictly_palindromic n = ok r → r = false →
              ¬ BasePalindromic (n.val - 2).toNat n.val.toNat) ∧
          ¬ BasePalindromic (n.val - 2).toNat n.val.toNat) := by
    sorry

  /-- Whenever is_strictly_palindromic(n) returns r_n and is_strictly_palindromic(m) returns r_m, we have r_n = r_m.
    Preconditions: n and m are integers (Lean type Std.I64) satisfying 4 <= n <= 100000 and 4 <= m <= 100000. -/
  theorem spec_4 (n m : I64) (h_lo_n : 4 ≤ n.val) (h_hi_n : n.val ≤ 100000)
      (h_lo_m : 4 ≤ m.val) (h_hi_m : m.val ≤ 100000) :
      ∀ r_n r_m : Bool,
        is_strictly_palindromic n = ok r_n → is_strictly_palindromic m = ok r_m →
          r_n = r_m := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n m : I64) (h_lo_n : 4 ≤ n.val) (h_hi_n : n.val ≤ 100000)
        (h_lo_m : 4 ≤ m.val) (h_hi_m : m.val ≤ 100000), ∀ r_n r_m : Bool,
          is_strictly_palindromic n = ok r_n → is_strictly_palindromic m = ok r_m →
            r_n = r_m) := by
    sorry

  /-- The call is_strictly_palindromic(n) returns a result r (it does not fail) and r = false. Equivalently, no n in the precondition range is strictly palindromic.
    Preconditions: n is an integer (Lean type Std.I64) satisfying 4 <= n <= 100000. -/
  theorem spec_5 (n : I64) (h_lo : 4 ≤ n.val) (h_hi : n.val ≤ 100000) :
      (∃ r : Bool, is_strictly_palindromic n = ok r ∧ r = false) ∧
        ¬ StrictlyPalindromic n.val.toNat := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : I64) (h_lo : 4 ≤ n.val) (h_hi : n.val ≤ 100000), (∃ r : Bool, is_strictly_palindromic n = ok r ∧ r = false) ∧
          ¬ StrictlyPalindromic n.val.toNat) := by
    sorry

  end AegisSpec.IsStrictlyPalindromic
