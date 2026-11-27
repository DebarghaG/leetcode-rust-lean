import Aegis.LexicalOrder.Code.Funs

/-!
# Specifications of `Aegis.LexicalOrder.lexical_order`

LeetCode problem `lexicographical-numbers`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

set_option autoImplicit false

namespace AegisSpec.LexicalOrder

def len (r : alloc.vec.Vec Std.I64) : ℕ := r.val.length

def elem (r : alloc.vec.Vec Std.I64) (i : ℕ) : ℤ := (r.val.getD i 0#i64).val

def dec (x : ℤ) : List ℕ := (Nat.toDigits 10 x.toNat).map (fun c => c.toNat - '0'.toNat)

def DigitsLt : List ℕ → List ℕ → Prop
  | [], [] => False
  | [], _ :: _ => True
  | _ :: _, [] => False
  | a :: l₁, b :: l₂ => a < b ∨ (a = b ∧ DigitsLt l₁ l₂)

def decLt (x y : ℤ) : Prop := DigitsLt (dec x) (dec y)

def firstDigit (x : ℤ) : ℕ := (dec x).headD 0

/-- Whenever lexical_order n returns a result r, r is the unique list of all integers k with 1 <= k <= n ordered by increasing lexicographic order of their canonical base-10 representations: r contains each such k exactly once, and for every i,j with 0 <= i < j < len(r), dec(r[i]) is lexicographically less than dec(r[j]). Here dec(x) is the decimal representation of the positive integer x without leading zeros; lexicographic comparison compares digit characters from left to right, and a proper prefix comes before any longer string.
  Preconditions: 1 <= n <= 50000. -/
theorem spec_1 (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 50000) :
    ∀ r : alloc.vec.Vec Std.I64, Aegis.LexicalOrder.lexical_order n = ok r →
      (∀ k : ℤ, 1 ≤ k → k ≤ n.val → ∃! i : ℕ, i < len r ∧ elem r i = k) ∧
      (∀ i j : ℕ, i < j → j < len r → decLt (elem r i) (elem r j)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 50000), ∀ r : alloc.vec.Vec Std.I64, Aegis.LexicalOrder.lexical_order n = ok r →
      (∀ k : ℤ, 1 ≤ k → k ≤ n.val → ∃! i : ℕ, i < len r ∧ elem r i = k) ∧
      (∀ i j : ℕ, i < j → j < len r → decLt (elem r i) (elem r j))) := by
  sorry

/-- Whenever lexical_order n returns a result r, len(r) = n, where n is interpreted as its natural-number value between 1 and 50000.
  Preconditions: 1 <= n <= 50000. -/
theorem spec_2 (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 50000) :
    ∀ r : alloc.vec.Vec Std.I64, Aegis.LexicalOrder.lexical_order n = ok r →
      len r = n.val.toNat := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 50000), ∀ r : alloc.vec.Vec Std.I64, Aegis.LexicalOrder.lexical_order n = ok r →
      len r = n.val.toNat) := by
  sorry

/-- Whenever lexical_order n returns a result r, for every i with 0 <= i < len(r), 1 <= r[i] <= n.
  Preconditions: 1 <= n <= 50000. -/
theorem spec_3 (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 50000) :
    ∀ r : alloc.vec.Vec Std.I64, Aegis.LexicalOrder.lexical_order n = ok r →
      ∀ i : ℕ, i < len r → 1 ≤ elem r i ∧ elem r i ≤ n.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 50000), ∀ r : alloc.vec.Vec Std.I64, Aegis.LexicalOrder.lexical_order n = ok r →
      ∀ i : ℕ, i < len r → 1 ≤ elem r i ∧ elem r i ≤ n.val) := by
  sorry

/-- Whenever lexical_order n returns a result r, for every i,j with 0 <= i < j < len(r), r[i] != r[j].
  Preconditions: 1 <= n <= 50000. -/
theorem spec_4 (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 50000) :
    ∀ r : alloc.vec.Vec Std.I64, Aegis.LexicalOrder.lexical_order n = ok r →
      ∀ i j : ℕ, i < j → j < len r → elem r i ≠ elem r j := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 50000), ∀ r : alloc.vec.Vec Std.I64, Aegis.LexicalOrder.lexical_order n = ok r →
      ∀ i j : ℕ, i < j → j < len r → elem r i ≠ elem r j) := by
  sorry

/-- Whenever lexical_order n returns a result r, for every k with 1 <= k <= n there exists an index i such that 0 <= i < len(r) and r[i] = k.
  Preconditions: 1 <= n <= 50000. -/
theorem spec_5 (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 50000) :
    ∀ r : alloc.vec.Vec Std.I64, Aegis.LexicalOrder.lexical_order n = ok r →
      ∀ k : ℤ, 1 ≤ k → k ≤ n.val → ∃ i : ℕ, i < len r ∧ elem r i = k := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 50000), ∀ r : alloc.vec.Vec Std.I64, Aegis.LexicalOrder.lexical_order n = ok r →
      ∀ k : ℤ, 1 ≤ k → k ≤ n.val → ∃ i : ℕ, i < len r ∧ elem r i = k) := by
  sorry

/-- Whenever lexical_order n returns a result r, for every i,j with 0 <= i < j < len(r), dec(r[i]) <lex dec(r[j]), where dec(x) is the canonical decimal representation without leading zeros and <lex compares digit characters left to right with a proper prefix first.
  Preconditions: 1 <= n <= 50000. -/
theorem spec_6 (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 50000) :
    ∀ r : alloc.vec.Vec Std.I64, Aegis.LexicalOrder.lexical_order n = ok r →
      ∀ i j : ℕ, i < j → j < len r → decLt (elem r i) (elem r j) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 50000), ∀ r : alloc.vec.Vec Std.I64, Aegis.LexicalOrder.lexical_order n = ok r →
      ∀ i j : ℕ, i < j → j < len r → decLt (elem r i) (elem r j)) := by
  sorry

/-- Whenever lexical_order n returns a result r, for every i with 0 <= i < len(r)-1, there is no integer k with 1 <= k <= n such that dec(r[i]) <lex dec(k) <lex dec(r[i+1]), using the same dec and <lex as in spec_1.
  Preconditions: 1 <= n <= 50000. -/
theorem spec_7 (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 50000) :
    ∀ r : alloc.vec.Vec Std.I64, Aegis.LexicalOrder.lexical_order n = ok r →
      ∀ i : ℕ, i < len r - 1 →
        ¬ ∃ k : ℤ, 1 ≤ k ∧ k ≤ n.val ∧ decLt (elem r i) k ∧ decLt k (elem r (i + 1)) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 50000), ∀ r : alloc.vec.Vec Std.I64, Aegis.LexicalOrder.lexical_order n = ok r →
      ∀ i : ℕ, i < len r - 1 →
        ¬ ∃ k : ℤ, 1 ≤ k ∧ k ≤ n.val ∧ decLt (elem r i) k ∧ decLt k (elem r (i + 1))) := by
  sorry

/-- Whenever lexical_order n returns a result r, len(r) > 0 and r[0] = 1.
  Preconditions: 1 <= n <= 50000. -/
theorem spec_8 (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 50000) :
    ∀ r : alloc.vec.Vec Std.I64, Aegis.LexicalOrder.lexical_order n = ok r →
      0 < len r ∧ elem r 0 = 1 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 50000), ∀ r : alloc.vec.Vec Std.I64, Aegis.LexicalOrder.lexical_order n = ok r →
      0 < len r ∧ elem r 0 = 1) := by
  sorry

/-- Whenever lexical_order n returns a result r, len(r) = n and for every i with 0 <= i < n, r[i] = i+1; hence r = [1,2,...,n].
  Preconditions: 1 <= n <= 9. -/
theorem spec_9 (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 9) :
    ∀ r : alloc.vec.Vec Std.I64, Aegis.LexicalOrder.lexical_order n = ok r →
      len r = n.val.toNat ∧
        ∀ i : ℕ, i < n.val.toNat → elem r i = (i : ℤ) + 1 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 9), ∀ r : alloc.vec.Vec Std.I64, Aegis.LexicalOrder.lexical_order n = ok r →
      len r = n.val.toNat ∧
        ∀ i : ℕ, i < n.val.toNat → elem r i = (i : ℤ) + 1) := by
  sorry

/-- Whenever lexical_order n returns a result r, for every k and every i such that 1 <= k <= n, 0 <= i < len(r), r[i] = k, and 10*k <= n, we have i+1 < len(r) and r[i+1] = 10*k.
  Preconditions: 1 <= n <= 50000. -/
theorem spec_10 (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 50000) :
    ∀ r : alloc.vec.Vec Std.I64, Aegis.LexicalOrder.lexical_order n = ok r →
      ∀ k : ℤ, 1 ≤ k → k ≤ n.val →
        ∀ i : ℕ, i < len r → elem r i = k → 10 * k ≤ n.val →
          i + 1 < len r ∧ elem r (i + 1) = 10 * k := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 50000), ∀ r : alloc.vec.Vec Std.I64, Aegis.LexicalOrder.lexical_order n = ok r →
      ∀ k : ℤ, 1 ≤ k → k ≤ n.val →
        ∀ i : ℕ, i < len r → elem r i = k → 10 * k ≤ n.val →
          i + 1 < len r ∧ elem r (i + 1) = 10 * k) := by
  sorry

/-- Whenever lexical_order n returns a result r, for every digit d in {1,...,9}, the set of indices i with 0 <= i < len(r) whose value r[i] has first decimal digit d is contiguous: if i < j < k and both r[i] and r[k] have first digit d, then r[j] also has first digit d.
  Preconditions: 1 <= n <= 50000. -/
theorem spec_11 (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 50000) :
    ∀ r : alloc.vec.Vec Std.I64, Aegis.LexicalOrder.lexical_order n = ok r →
      ∀ d : ℕ, 1 ≤ d → d ≤ 9 →
        ∀ i j m : ℕ, i < j → j < m → m < len r →
          firstDigit (elem r i) = d → firstDigit (elem r m) = d →
            firstDigit (elem r j) = d := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 50000), ∀ r : alloc.vec.Vec Std.I64, Aegis.LexicalOrder.lexical_order n = ok r →
      ∀ d : ℕ, 1 ≤ d → d ≤ 9 →
        ∀ i j m : ℕ, i < j → j < m → m < len r →
          firstDigit (elem r i) = d → firstDigit (elem r m) = d →
            firstDigit (elem r j) = d) := by
  sorry

/-- Whenever lexical_order n returns a result r, for every i,j with 0 <= i < j < len(r), if dec(r[i]) and dec(r[j]) have the same length, then r[i] < r[j] as integers.
  Preconditions: 1 <= n <= 50000. -/
theorem spec_12 (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 50000) :
    ∀ r : alloc.vec.Vec Std.I64, Aegis.LexicalOrder.lexical_order n = ok r →
      ∀ i j : ℕ, i < j → j < len r →
        (dec (elem r i)).length = (dec (elem r j)).length → elem r i < elem r j := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 50000), ∀ r : alloc.vec.Vec Std.I64, Aegis.LexicalOrder.lexical_order n = ok r →
      ∀ i j : ℕ, i < j → j < len r →
        (dec (elem r i)).length = (dec (elem r j)).length → elem r i < elem r j) := by
  sorry

/-- The function returns a result r for every n with 1 <= n <= 50000; it does not fail, overflow, panic, or access out of bounds.
  Preconditions: 1 <= n <= 50000. -/
theorem spec_13 (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 50000) :
    ∃ r : alloc.vec.Vec Std.I64, Aegis.LexicalOrder.lexical_order n = ok r := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 50000), ∃ r : alloc.vec.Vec Std.I64, Aegis.LexicalOrder.lexical_order n = ok r) := by
  sorry

end AegisSpec.LexicalOrder
