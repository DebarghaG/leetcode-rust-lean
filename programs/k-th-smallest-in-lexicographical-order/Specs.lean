import Aegis.FindKthNumber.Code.Funs

/-!
# Specifications of `Aegis.FindKthNumber.find_kth_number`

LeetCode problem `k-th-smallest-in-lexicographical-order`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

open Aegis.FindKthNumber

namespace AegisSpec.FindKthNumber

def decDigits (n : ℕ) : List ℕ :=
  if _h : n = 0 then [] else decDigits (n / 10) ++ [n % 10]
termination_by n
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero _h) (by decide)

def lexLt (x y : ℤ) : Prop := decDigits x.natAbs < decDigits y.natAbs

instance decidableLexLt (x y : ℤ) : Decidable (lexLt x y) := by
  unfold lexLt
  infer_instance

def upTo (N : ℤ) : List ℤ := (List.range N.toNat).map (fun i => (i : ℤ) + 1)

def countUpTo (N : ℤ) (p : ℤ → Prop) [DecidablePred p] : ℕ := (upTo N).filter p |>.length

def countLexBelow (N r : ℤ) : ℕ := countUpTo N fun x => lexLt x r

def countLexAbove (N r : ℤ) : ℕ := countUpTo N fun x => lexLt r x

def IsKthLex (N k r : ℤ) : Prop := 1 ≤ r ∧ r ≤ N ∧ (countLexBelow N r : ℤ) = k - 1

instance decidableIsKthLex (N k r : ℤ) : Decidable (IsKthLex N k r) := by
  unfold IsKthLex
  infer_instance

/-- The function returns a result r (an I64, viewed as an integer) such that 1 <= r <= n and exactly k-1 integers x with 1 <= x <= n satisfy x <_lex r, where <_lex is the lexicographic order on ordinary decimal representations without leading zeros: a <_lex b iff dec(a) is a proper prefix of dec(b), or at the first position where dec(a) and dec(b) differ the digit of a is smaller. Equivalently, r is the k-th element of the list of all integers from 1 to n sorted increasingly by <_lex.
  Preconditions: The I64 parameters n and k, viewed as mathematical integers, satisfy 1 <= k <= n <= 10^9. -/
theorem spec_1 (n k : Std.I64)
    (hk : 1 ≤ k.val) (hkn : k.val ≤ n.val) (hn : n.val ≤ 10 ^ 9) :
    ∃ r : Std.I64,
      find_kth_number n k = ok r ∧ 1 ≤ r.val ∧ r.val ≤ n.val ∧
        (countLexBelow n.val r.val : ℤ) = k.val - 1 := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n k : Std.I64)
    (hk : 1 ≤ k.val) (hkn : k.val ≤ n.val) (hn : n.val ≤ 10 ^ 9), ∃ r : Std.I64,
      find_kth_number n k = ok r ∧ 1 ≤ r.val ∧ r.val ≤ n.val ∧
        (countLexBelow n.val r.val : ℤ) = k.val - 1) := by
  sorry

/-- For every such n and k, the call find_kth_number(n,k) returns a result; it does not fail due to overflow, panic, or any other error.
  Preconditions: The I64 parameters n and k, viewed as mathematical integers, satisfy 1 <= k <= n <= 10^9. -/
theorem spec_2 (n k : Std.I64)
    (hk : 1 ≤ k.val) (hkn : k.val ≤ n.val) (hn : n.val ≤ 10 ^ 9) :
    ∃ r : Std.I64, find_kth_number n k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n k : Std.I64)
    (hk : 1 ≤ k.val) (hkn : k.val ≤ n.val) (hn : n.val ≤ 10 ^ 9), ∃ r : Std.I64, find_kth_number n k = ok r) := by
  sorry

/-- Whenever the function returns a result r, interpreting r as an integer, 1 <= r <= n.
  Preconditions: The I64 parameters n and k, viewed as mathematical integers, satisfy 1 <= k <= n <= 10^9. -/
theorem spec_3 (n k : Std.I64)
    (hk : 1 ≤ k.val) (hkn : k.val ≤ n.val) (hn : n.val ≤ 10 ^ 9) :
    ∀ r : Std.I64, find_kth_number n k = ok r → 1 ≤ r.val ∧ r.val ≤ n.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n k : Std.I64)
    (hk : 1 ≤ k.val) (hkn : k.val ≤ n.val) (hn : n.val ≤ 10 ^ 9), ∀ r : Std.I64, find_kth_number n k = ok r → 1 ≤ r.val ∧ r.val ≤ n.val) := by
  sorry

/-- The function returns the result r = 1.
  Preconditions: The I64 parameters n and k, viewed as mathematical integers, satisfy 1 <= k <= n <= 10^9 and k = 1. -/
theorem spec_4 (n k : Std.I64)
    (hk : 1 ≤ k.val) (hkn : k.val ≤ n.val) (hn : n.val ≤ 10 ^ 9) (hk1 : k.val = 1) :
    ∃ r : Std.I64, find_kth_number n k = ok r ∧ r.val = 1 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n k : Std.I64)
    (hk : 1 ≤ k.val) (hkn : k.val ≤ n.val) (hn : n.val ≤ 10 ^ 9) (hk1 : k.val = 1), ∃ r : Std.I64, find_kth_number n k = ok r ∧ r.val = 1) := by
  sorry

/-- The function returns the result r = k.
  Preconditions: The I64 parameters n and k, viewed as mathematical integers, satisfy 1 <= k <= n <= 9. -/
theorem spec_5 (n k : Std.I64)
    (hk : 1 ≤ k.val) (hkn : k.val ≤ n.val) (hn : n.val ≤ 9) :
    ∃ r : Std.I64, find_kth_number n k = ok r ∧ r.val = k.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n k : Std.I64)
    (hk : 1 ≤ k.val) (hkn : k.val ≤ n.val) (hn : n.val ≤ 9), ∃ r : Std.I64, find_kth_number n k = ok r ∧ r.val = k.val) := by
  sorry

/-- The function returns a result r such that 1 <= r <= n and, for every x with 1 <= x <= n, it is not the case that r <_lex x, where <_lex is the lexicographic order on decimal representations without leading zeros (a <_lex b iff dec(a) is a proper prefix of dec(b), or at the first differing digit dec(a) has the smaller digit). In other words, r is the lexicographically greatest integer in [1,n].
  Preconditions: The I64 parameters n and k, viewed as mathematical integers, satisfy 1 <= k <= n <= 10^9 and k = n. -/
theorem spec_6 (n k : Std.I64)
    (hk : 1 ≤ k.val) (hkn : k.val ≤ n.val) (hn : n.val ≤ 10 ^ 9) (hkn' : k.val = n.val) :
    ∃ r : Std.I64,
      find_kth_number n k = ok r ∧ 1 ≤ r.val ∧ r.val ≤ n.val ∧
        ∀ x : ℤ, 1 ≤ x → x ≤ n.val → ¬ lexLt r.val x := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n k : Std.I64)
    (hk : 1 ≤ k.val) (hkn : k.val ≤ n.val) (hn : n.val ≤ 10 ^ 9) (hkn' : k.val = n.val), ∃ r : Std.I64,
      find_kth_number n k = ok r ∧ 1 ≤ r.val ∧ r.val ≤ n.val ∧
        ∀ x : ℤ, 1 ≤ x → x ≤ n.val → ¬ lexLt r.val x) := by
  sorry

/-- The function returns the result r = 10.
  Preconditions: The I64 parameters n and k, viewed as mathematical integers, satisfy 1 <= k <= n <= 10^9, k = 2, and n >= 10. -/
theorem spec_7 (n k : Std.I64)
    (hk : 1 ≤ k.val) (hkn : k.val ≤ n.val) (hn : n.val ≤ 10 ^ 9)
    (hk2 : k.val = 2) (hn10 : 10 ≤ n.val) :
    ∃ r : Std.I64, find_kth_number n k = ok r ∧ r.val = 10 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n k : Std.I64)
    (hk : 1 ≤ k.val) (hkn : k.val ≤ n.val) (hn : n.val ≤ 10 ^ 9)
    (hk2 : k.val = 2) (hn10 : 10 ≤ n.val), ∃ r : Std.I64, find_kth_number n k = ok r ∧ r.val = 10) := by
  sorry

/-- Whenever the function returns a result r, exactly n-k integers x with 1 <= x <= n satisfy r <_lex x, where <_lex is the lexicographic order on decimal representations without leading zeros (a <_lex b iff dec(a) is a proper prefix of dec(b), or at the first differing digit dec(a) has the smaller digit).
  Preconditions: The I64 parameters n and k, viewed as mathematical integers, satisfy 1 <= k <= n <= 10^9. -/
theorem spec_8 (n k : Std.I64)
    (hk : 1 ≤ k.val) (hkn : k.val ≤ n.val) (hn : n.val ≤ 10 ^ 9) :
    ∀ r : Std.I64, find_kth_number n k = ok r → (countLexAbove n.val r.val : ℤ) = n.val - k.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n k : Std.I64)
    (hk : 1 ≤ k.val) (hkn : k.val ≤ n.val) (hn : n.val ≤ 10 ^ 9), ∀ r : Std.I64, find_kth_number n k = ok r → (countLexAbove n.val r.val : ℤ) = n.val - k.val) := by
  sorry

/-- The function returns a result r and there exists an integer x with 1 <= x <= n such that x <_lex r and there is no integer y with 1 <= y <= n satisfying x <_lex y <_lex r, where <_lex is the lexicographic order on decimal representations without leading zeros (a <_lex b iff dec(a) is a proper prefix of dec(b), or at the first differing digit dec(a) has the smaller digit).
  Preconditions: The I64 parameters n and k, viewed as mathematical integers, satisfy 1 <= k <= n <= 10^9 and k > 1. -/
theorem spec_9 (n k : Std.I64)
    (hk : 1 ≤ k.val) (hkn : k.val ≤ n.val) (hn : n.val ≤ 10 ^ 9) (hk1 : 1 < k.val) :
    ∃ r : Std.I64,
      find_kth_number n k = ok r ∧
        ∃ x : ℤ,
          1 ≤ x ∧ x ≤ n.val ∧ lexLt x r.val ∧
            ¬ ∃ y : ℤ, 1 ≤ y ∧ y ≤ n.val ∧ lexLt x y ∧ lexLt y r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n k : Std.I64)
    (hk : 1 ≤ k.val) (hkn : k.val ≤ n.val) (hn : n.val ≤ 10 ^ 9) (hk1 : 1 < k.val), ∃ r : Std.I64,
      find_kth_number n k = ok r ∧
        ∃ x : ℤ,
          1 ≤ x ∧ x ≤ n.val ∧ lexLt x r.val ∧
            ¬ ∃ y : ℤ, 1 ≤ y ∧ y ≤ n.val ∧ lexLt x y ∧ lexLt y r.val) := by
  sorry

/-- The function returns a result r and there exists an integer x with 1 <= x <= n such that r <_lex x and there is no integer y with 1 <= y <= n satisfying r <_lex y <_lex x, where <_lex is the lexicographic order on decimal representations without leading zeros (a <_lex b iff dec(a) is a proper prefix of dec(b), or at the first differing digit dec(a) has the smaller digit).
  Preconditions: The I64 parameters n and k, viewed as mathematical integers, satisfy 1 <= k <= n <= 10^9 and k < n. -/
theorem spec_10 (n k : Std.I64)
    (hk : 1 ≤ k.val) (hkn : k.val ≤ n.val) (hn : n.val ≤ 10 ^ 9) (hkn' : k.val < n.val) :
    ∃ r : Std.I64,
      find_kth_number n k = ok r ∧
        ∃ x : ℤ,
          1 ≤ x ∧ x ≤ n.val ∧ lexLt r.val x ∧
            ¬ ∃ y : ℤ, 1 ≤ y ∧ y ≤ n.val ∧ lexLt r.val y ∧ lexLt y x := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n k : Std.I64)
    (hk : 1 ≤ k.val) (hkn : k.val ≤ n.val) (hn : n.val ≤ 10 ^ 9) (hkn' : k.val < n.val), ∃ r : Std.I64,
      find_kth_number n k = ok r ∧
        ∃ x : ℤ,
          1 ≤ x ∧ x ≤ n.val ∧ lexLt r.val x ∧
            ¬ ∃ y : ℤ, 1 ≤ y ∧ y ≤ n.val ∧ lexLt r.val y ∧ lexLt y x) := by
  sorry

/-- Whenever the function returns a result r and r = 1, then k = 1.
  Preconditions: The I64 parameters n and k, viewed as mathematical integers, satisfy 1 <= k <= n <= 10^9. -/
theorem spec_11 (n k : Std.I64)
    (hk : 1 ≤ k.val) (hkn : k.val ≤ n.val) (hn : n.val ≤ 10 ^ 9) :
    ∀ r : Std.I64, find_kth_number n k = ok r → r.val = 1 → k.val = 1 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (n k : Std.I64)
    (hk : 1 ≤ k.val) (hkn : k.val ≤ n.val) (hn : n.val ≤ 10 ^ 9), ∀ r : Std.I64, find_kth_number n k = ok r → r.val = 1 → k.val = 1) := by
  sorry

/-- Let s be the k-th integer of [1,n-1] in increasing lexicographic order <_lex, where <_lex is the lexicographic order on decimal representations without leading zeros (a <_lex b iff dec(a) is a proper prefix of dec(b), or at the first differing digit dec(a) has the smaller digit). If s <_lex n, then the function returns the result r = s.
  Preconditions: The I64 parameters n and k, viewed as mathematical integers, satisfy 1 <= k < n <= 10^9. -/
theorem spec_12 (n k : Std.I64)
    (hk : 1 ≤ k.val) (hkn : k.val < n.val) (hn : n.val ≤ 10 ^ 9) :
    ∀ s : ℤ, IsKthLex (n.val - 1) k.val s → lexLt s n.val →
      ∃ r : Std.I64, find_kth_number n k = ok r ∧ r.val = s := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (n k : Std.I64)
    (hk : 1 ≤ k.val) (hkn : k.val < n.val) (hn : n.val ≤ 10 ^ 9), ∀ s : ℤ, IsKthLex (n.val - 1) k.val s → lexLt s n.val →
      ∃ r : Std.I64, find_kth_number n k = ok r ∧ r.val = s) := by
  sorry

/-- Let r_k be the result returned by find_kth_number(n,k) and r_{k+1} the result returned by find_kth_number(n,k+1). Then r_k <_lex r_{k+1}, where <_lex is the lexicographic order on ordinary decimal representations without leading zeros: a <_lex b iff dec(a) is a proper prefix of dec(b), or at the first position where dec(a) and dec(b) differ the digit of a is smaller.
  Preconditions: The I64 parameters n and k, viewed as mathematical integers, satisfy 1 <= k < n <= 10^9. -/
theorem spec_13 (n k k1 : Std.I64)
    (hk : 1 ≤ k.val) (hkn : k.val < n.val) (hn : n.val ≤ 10 ^ 9) (hk1 : k1.val = k.val + 1) :
    ∀ rk rk1 : Std.I64,
      find_kth_number n k = ok rk → find_kth_number n k1 = ok rk1 → lexLt rk.val rk1.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (n k k1 : Std.I64)
    (hk : 1 ≤ k.val) (hkn : k.val < n.val) (hn : n.val ≤ 10 ^ 9) (hk1 : k1.val = k.val + 1), ∀ rk rk1 : Std.I64,
      find_kth_number n k = ok rk → find_kth_number n k1 = ok rk1 → lexLt rk.val rk1.val) := by
  sorry

end AegisSpec.FindKthNumber
