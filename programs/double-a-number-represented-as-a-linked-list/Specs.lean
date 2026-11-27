import Aegis.DoubleIt.Code.Funs

/-!
# Specifications of `Aegis.DoubleIt.double_it`

LeetCode problem `double-a-number-represented-as-a-linked-list`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.DoubleIt

def cI64 (n : Int) : Aeneas.Std.I64 := ⟨BitVec.ofInt 64 n⟩

def digitsOf : Aegis.DoubleIt.List → List Int
  | .Nil => []
  | .Cons d rest => d.val :: digitsOf rest

def ofDigits : List Int → Aegis.DoubleIt.List
  | [] => .Nil
  | d :: rest => .Cons (cI64 d) (ofDigits rest)

def numValue : List Int → Int
  | [] => 0
  | d :: rest => d * 10 ^ rest.length + numValue rest

def suffixValue (k : Nat) (ds : List Int) : Int :=
  numValue (ds.drop (ds.length - k))

def zerosFromStart : List Int → Nat
  | [] => 0
  | d :: rest => if d = 0 then zerosFromStart rest + 1 else 0

def trailingZeros (ds : List Int) : Nat := zerosFromStart ds.reverse

/-- The function returns a result r (it does not fail), and r is exactly the canonical decimal representation of 2*N. Explicitly, write r = Cons(e_0, Cons(e_1, ..., Cons(e_{m-1}, Nil))) with m = len(r); then m >= 1; for every j with 0 <= j < m, 0 <= e_j <= 9; if m > 1 then e_0 != 0; and sum_{j=0}^{m-1} e_j * 10^(m-1-j) = 2*N.
  Preconditions: Write head = Cons(d_0, Cons(d_1, ..., Cons(d_{n-1}, Nil))) with n = len(head), so there are exactly n Cons nodes, and let N = sum_{i=0}^{n-1} d_i * 10^(n-1-i). Assume: n >= 1; n <= 10000; for every i with 0 <= i < n, 0 <= d_i <= 9; and if n > 1 then d_0 != 0. Thus head represents a non-negative integer without leading zeroes, except the single digit 0. -/
theorem spec_1 (ds : List Int)
    (hn_pos : ds ≠ [])
    (hn_len : ds.length ≤ 10000)
    (hdigit : ∀ d ∈ ds, 0 ≤ d ∧ d ≤ 9)
    (hsignif : 1 < ds.length → ds.head? ≠ some 0) :
    ∃ r : Aegis.DoubleIt.List,
      Aegis.DoubleIt.double_it (ofDigits ds) = Aeneas.Std.Result.ok r ∧
        digitsOf r ≠ [] ∧
        (∀ d ∈ digitsOf r, 0 ≤ d ∧ d ≤ 9) ∧
        (1 < (digitsOf r).length → (digitsOf r).head? ≠ some 0) ∧
        numValue (digitsOf r) = 2 * numValue ds := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (ds : List Int)
    (hn_pos : ds ≠ [])
    (hn_len : ds.length ≤ 10000)
    (hdigit : ∀ d ∈ ds, 0 ≤ d ∧ d ≤ 9)
    (hsignif : 1 < ds.length → ds.head? ≠ some 0), ∃ r : Aegis.DoubleIt.List,
      Aegis.DoubleIt.double_it (ofDigits ds) = Aeneas.Std.Result.ok r ∧
        digitsOf r ≠ [] ∧
        (∀ d ∈ digitsOf r, 0 ≤ d ∧ d ≤ 9) ∧
        (1 < (digitsOf r).length → (digitsOf r).head? ≠ some 0) ∧
        numValue (digitsOf r) = 2 * numValue ds) := by
  sorry

/-- For every head satisfying the preconditions, the function returns a result r; in particular it does not fail due to overflow, out-of-bounds access, or panic.
  Preconditions: Write head = Cons(d_0, Cons(d_1, ..., Cons(d_{n-1}, Nil))) with n = len(head), so there are exactly n Cons nodes, and let N = sum_{i=0}^{n-1} d_i * 10^(n-1-i). Assume: n >= 1; n <= 10000; for every i with 0 <= i < n, 0 <= d_i <= 9; and if n > 1 then d_0 != 0. Thus head represents a non-negative integer without leading zeroes, except the single digit 0. -/
theorem spec_2 (ds : List Int)
    (hn_pos : ds ≠ [])
    (hn_len : ds.length ≤ 10000)
    (hdigit : ∀ d ∈ ds, 0 ≤ d ∧ d ≤ 9)
    (hsignif : 1 < ds.length → ds.head? ≠ some 0) :
    ∃ r : Aegis.DoubleIt.List, Aegis.DoubleIt.double_it (ofDigits ds) = Aeneas.Std.Result.ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (ds : List Int)
    (hn_pos : ds ≠ [])
    (hn_len : ds.length ≤ 10000)
    (hdigit : ∀ d ∈ ds, 0 ≤ d ∧ d ≤ 9)
    (hsignif : 1 < ds.length → ds.head? ≠ some 0), ∃ r : Aegis.DoubleIt.List, Aegis.DoubleIt.double_it (ofDigits ds) = Aeneas.Std.Result.ok r) := by
  sorry

/-- Whenever the function returns a result r, every integer stored in a node of r is between 0 and 9 inclusive. That is, if r = Cons(e_0, ..., Cons(e_{m-1}, Nil)), then for every j with 0 <= j < m, 0 <= e_j <= 9.
  Preconditions: Write head = Cons(d_0, Cons(d_1, ..., Cons(d_{n-1}, Nil))) with n = len(head), so there are exactly n Cons nodes, and let N = sum_{i=0}^{n-1} d_i * 10^(n-1-i). Assume: n >= 1; n <= 10000; for every i with 0 <= i < n, 0 <= d_i <= 9; and if n > 1 then d_0 != 0. Thus head represents a non-negative integer without leading zeroes, except the single digit 0. -/
theorem spec_3 (ds : List Int)
    (hn_pos : ds ≠ [])
    (hn_len : ds.length ≤ 10000)
    (hdigit : ∀ d ∈ ds, 0 ≤ d ∧ d ≤ 9)
    (hsignif : 1 < ds.length → ds.head? ≠ some 0) :
    ∀ r : Aegis.DoubleIt.List, Aegis.DoubleIt.double_it (ofDigits ds) = Aeneas.Std.Result.ok r →
      ∀ d ∈ digitsOf r, 0 ≤ d ∧ d ≤ 9 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (ds : List Int)
    (hn_pos : ds ≠ [])
    (hn_len : ds.length ≤ 10000)
    (hdigit : ∀ d ∈ ds, 0 ≤ d ∧ d ≤ 9)
    (hsignif : 1 < ds.length → ds.head? ≠ some 0), ∀ r : Aegis.DoubleIt.List, Aegis.DoubleIt.double_it (ofDigits ds) = Aeneas.Std.Result.ok r →
      ∀ d ∈ digitsOf r, 0 ≤ d ∧ d ≤ 9) := by
  sorry

/-- Whenever the function returns a result r, r is not Nil; it has at least one Cons node.
  Preconditions: Write head = Cons(d_0, Cons(d_1, ..., Cons(d_{n-1}, Nil))) with n = len(head), so there are exactly n Cons nodes, and let N = sum_{i=0}^{n-1} d_i * 10^(n-1-i). Assume: n >= 1; n <= 10000; for every i with 0 <= i < n, 0 <= d_i <= 9; and if n > 1 then d_0 != 0. Thus head represents a non-negative integer without leading zeroes, except the single digit 0. -/
theorem spec_4 (ds : List Int)
    (hn_pos : ds ≠ [])
    (hn_len : ds.length ≤ 10000)
    (hdigit : ∀ d ∈ ds, 0 ≤ d ∧ d ≤ 9)
    (hsignif : 1 < ds.length → ds.head? ≠ some 0) :
    ∀ r : Aegis.DoubleIt.List, Aegis.DoubleIt.double_it (ofDigits ds) = Aeneas.Std.Result.ok r →
      r ≠ Aegis.DoubleIt.List.Nil := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (ds : List Int)
    (hn_pos : ds ≠ [])
    (hn_len : ds.length ≤ 10000)
    (hdigit : ∀ d ∈ ds, 0 ≤ d ∧ d ≤ 9)
    (hsignif : 1 < ds.length → ds.head? ≠ some 0), ∀ r : Aegis.DoubleIt.List, Aegis.DoubleIt.double_it (ofDigits ds) = Aeneas.Std.Result.ok r →
      r ≠ Aegis.DoubleIt.List.Nil) := by
  sorry

/-- Whenever the function returns a result r, len(r) = n + 1 if and only if N >= 5 * 10^(n-1), where n = len(head). Equivalently, len(r) = n exactly when N < 5 * 10^(n-1).
  Preconditions: Write head = Cons(d_0, Cons(d_1, ..., Cons(d_{n-1}, Nil))) with n = len(head), so there are exactly n Cons nodes, and let N = sum_{i=0}^{n-1} d_i * 10^(n-1-i). Assume: n >= 1; n <= 10000; for every i with 0 <= i < n, 0 <= d_i <= 9; and if n > 1 then d_0 != 0. Thus head represents a non-negative integer without leading zeroes, except the single digit 0. -/
theorem spec_5 (ds : List Int)
    (hn_pos : ds ≠ [])
    (hn_len : ds.length ≤ 10000)
    (hdigit : ∀ d ∈ ds, 0 ≤ d ∧ d ≤ 9)
    (hsignif : 1 < ds.length → ds.head? ≠ some 0) :
    ∀ r : Aegis.DoubleIt.List, Aegis.DoubleIt.double_it (ofDigits ds) = Aeneas.Std.Result.ok r →
      ((digitsOf r).length = ds.length + 1 ↔ numValue ds ≥ 5 * 10 ^ (ds.length - 1)) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (ds : List Int)
    (hn_pos : ds ≠ [])
    (hn_len : ds.length ≤ 10000)
    (hdigit : ∀ d ∈ ds, 0 ≤ d ∧ d ≤ 9)
    (hsignif : 1 < ds.length → ds.head? ≠ some 0), ∀ r : Aegis.DoubleIt.List, Aegis.DoubleIt.double_it (ofDigits ds) = Aeneas.Std.Result.ok r →
      ((digitsOf r).length = ds.length + 1 ↔ numValue ds ≥ 5 * 10 ^ (ds.length - 1))) := by
  sorry

/-- Whenever the function returns a result r and len(r) = n + 1, the first digit of r is 1. Write r = Cons(e_0, ..., Cons(e_{m-1}, Nil)); then e_0 = 1.
  Preconditions: Write head = Cons(d_0, Cons(d_1, ..., Cons(d_{n-1}, Nil))) with n = len(head), so there are exactly n Cons nodes, and let N = sum_{i=0}^{n-1} d_i * 10^(n-1-i). Assume: n >= 1; n <= 10000; for every i with 0 <= i < n, 0 <= d_i <= 9; and if n > 1 then d_0 != 0. Thus head represents a non-negative integer without leading zeroes, except the single digit 0. -/
theorem spec_6 (ds : List Int)
    (hn_pos : ds ≠ [])
    (hn_len : ds.length ≤ 10000)
    (hdigit : ∀ d ∈ ds, 0 ≤ d ∧ d ≤ 9)
    (hsignif : 1 < ds.length → ds.head? ≠ some 0) :
    ∀ r : Aegis.DoubleIt.List, Aegis.DoubleIt.double_it (ofDigits ds) = Aeneas.Std.Result.ok r →
      (digitsOf r).length = ds.length + 1 → (digitsOf r).head? = some 1 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (ds : List Int)
    (hn_pos : ds ≠ [])
    (hn_len : ds.length ≤ 10000)
    (hdigit : ∀ d ∈ ds, 0 ≤ d ∧ d ≤ 9)
    (hsignif : 1 < ds.length → ds.head? ≠ some 0), ∀ r : Aegis.DoubleIt.List, Aegis.DoubleIt.double_it (ofDigits ds) = Aeneas.Std.Result.ok r →
      (digitsOf r).length = ds.length + 1 → (digitsOf r).head? = some 1) := by
  sorry

/-- Whenever the function returns a result r, if len(r) > 1 then the first digit of r is not 0. Write r = Cons(e_0, ..., Cons(e_{m-1}, Nil)); then m = len(r) > 1 implies e_0 != 0.
  Preconditions: Write head = Cons(d_0, Cons(d_1, ..., Cons(d_{n-1}, Nil))) with n = len(head), so there are exactly n Cons nodes, and let N = sum_{i=0}^{n-1} d_i * 10^(n-1-i). Assume: n >= 1; n <= 10000; for every i with 0 <= i < n, 0 <= d_i <= 9; and if n > 1 then d_0 != 0. Thus head represents a non-negative integer without leading zeroes, except the single digit 0. -/
theorem spec_7 (ds : List Int)
    (hn_pos : ds ≠ [])
    (hn_len : ds.length ≤ 10000)
    (hdigit : ∀ d ∈ ds, 0 ≤ d ∧ d ≤ 9)
    (hsignif : 1 < ds.length → ds.head? ≠ some 0) :
    ∀ r : Aegis.DoubleIt.List, Aegis.DoubleIt.double_it (ofDigits ds) = Aeneas.Std.Result.ok r →
      1 < (digitsOf r).length → (digitsOf r).head? ≠ some 0 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (ds : List Int)
    (hn_pos : ds ≠ [])
    (hn_len : ds.length ≤ 10000)
    (hdigit : ∀ d ∈ ds, 0 ≤ d ∧ d ≤ 9)
    (hsignif : 1 < ds.length → ds.head? ≠ some 0), ∀ r : Aegis.DoubleIt.List, Aegis.DoubleIt.double_it (ofDigits ds) = Aeneas.Std.Result.ok r →
      1 < (digitsOf r).length → (digitsOf r).head? ≠ some 0) := by
  sorry

/-- Whenever the function returns a non-Nil result r, write r = Cons(e_0, ..., Cons(e_{m-1}, Nil)) with m >= 1; then e_{m-1} = (2 * d_{n-1}) mod 10.
  Preconditions: Write head = Cons(d_0, Cons(d_1, ..., Cons(d_{n-1}, Nil))) with n = len(head), so there are exactly n Cons nodes, and let N = sum_{i=0}^{n-1} d_i * 10^(n-1-i). Assume: n >= 1; n <= 10000; for every i with 0 <= i < n, 0 <= d_i <= 9; and if n > 1 then d_0 != 0. Thus head represents a non-negative integer without leading zeroes, except the single digit 0. -/
theorem spec_8 (ds : List Int)
    (hn_pos : ds ≠ [])
    (hn_len : ds.length ≤ 10000)
    (hdigit : ∀ d ∈ ds, 0 ≤ d ∧ d ≤ 9)
    (hsignif : 1 < ds.length → ds.head? ≠ some 0) :
    ∀ r : Aegis.DoubleIt.List, Aegis.DoubleIt.double_it (ofDigits ds) = Aeneas.Std.Result.ok r →
      r ≠ Aegis.DoubleIt.List.Nil →
        ∀ e d : Int, (digitsOf r).getLast? = some e → ds.getLast? = some d → e = (2 * d) % 10 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (ds : List Int)
    (hn_pos : ds ≠ [])
    (hn_len : ds.length ≤ 10000)
    (hdigit : ∀ d ∈ ds, 0 ≤ d ∧ d ≤ 9)
    (hsignif : 1 < ds.length → ds.head? ≠ some 0), ∀ r : Aegis.DoubleIt.List, Aegis.DoubleIt.double_it (ofDigits ds) = Aeneas.Std.Result.ok r →
      r ≠ Aegis.DoubleIt.List.Nil →
        ∀ e d : Int, (digitsOf r).getLast? = some e → ds.getLast? = some d → e = (2 * d) % 10) := by
  sorry

/-- Whenever the function returns a result r whose length m = len(r) is at least n, write r = Cons(e_0, ..., Cons(e_{m-1}, Nil)). For every k with 2 <= k <= n, let A_k = sum_{i=n-k}^{n-1} d_i * 10^(n-1-i), the integer represented by the last k input digits, and let B_k = sum_{i=m-k}^{m-1} e_i * 10^(m-1-i), the integer represented by the last k output digits. Then B_k mod 10^k = (2 * A_k) mod 10^k.
  Preconditions: Write head = Cons(d_0, Cons(d_1, ..., Cons(d_{n-1}, Nil))) with n = len(head), so there are exactly n Cons nodes, and let N = sum_{i=0}^{n-1} d_i * 10^(n-1-i). Assume: n >= 1; n <= 10000; for every i with 0 <= i < n, 0 <= d_i <= 9; and if n > 1 then d_0 != 0. Thus head represents a non-negative integer without leading zeroes, except the single digit 0. -/
theorem spec_9 (ds : List Int)
    (hn_pos : ds ≠ [])
    (hn_len : ds.length ≤ 10000)
    (hdigit : ∀ d ∈ ds, 0 ≤ d ∧ d ≤ 9)
    (hsignif : 1 < ds.length → ds.head? ≠ some 0) :
    ∀ r : Aegis.DoubleIt.List, Aegis.DoubleIt.double_it (ofDigits ds) = Aeneas.Std.Result.ok r →
      ds.length ≤ (digitsOf r).length →
        ∀ k : Nat, 2 ≤ k → k ≤ ds.length →
          suffixValue k (digitsOf r) % (10 ^ k) = (2 * suffixValue k ds) % (10 ^ k) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (ds : List Int)
    (hn_pos : ds ≠ [])
    (hn_len : ds.length ≤ 10000)
    (hdigit : ∀ d ∈ ds, 0 ≤ d ∧ d ≤ 9)
    (hsignif : 1 < ds.length → ds.head? ≠ some 0), ∀ r : Aegis.DoubleIt.List, Aegis.DoubleIt.double_it (ofDigits ds) = Aeneas.Std.Result.ok r →
      ds.length ≤ (digitsOf r).length →
        ∀ k : Nat, 2 ≤ k → k ≤ ds.length →
          suffixValue k (digitsOf r) % (10 ^ k) = (2 * suffixValue k ds) % (10 ^ k)) := by
  sorry

/-- Whenever the function returns a result r: if 0 <= d_0 <= 4 then r = Cons(2 * d_0, Nil); if 5 <= d_0 <= 9 then r = Cons(1, Cons(2 * d_0 - 10, Nil)).
  Preconditions: Write head = Cons(d_0, Cons(d_1, ..., Cons(d_{n-1}, Nil))) with n = len(head), so there are exactly n Cons nodes, and let N = sum_{i=0}^{n-1} d_i * 10^(n-1-i). Assume: n >= 1; n <= 10000; for every i with 0 <= i < n, 0 <= d_i <= 9; and if n > 1 then d_0 != 0. Additionally, n = 1, so head = Cons(d_0, Nil). -/
theorem spec_10 (ds : List Int)
    (hn_pos : ds ≠ [])
    (hn_len : ds.length ≤ 10000)
    (hdigit : ∀ d ∈ ds, 0 ≤ d ∧ d ≤ 9)
    (hsignif : 1 < ds.length → ds.head? ≠ some 0)
    (hn_one : ds.length = 1) :
    ∀ d0 : Int, ds = [d0] →
      (d0 ≤ 4 → ∀ r : Aegis.DoubleIt.List,
          Aegis.DoubleIt.double_it (ofDigits ds) = Aeneas.Std.Result.ok r →
            r = ofDigits [2 * d0]) ∧
        (5 ≤ d0 → ∀ r : Aegis.DoubleIt.List,
          Aegis.DoubleIt.double_it (ofDigits ds) = Aeneas.Std.Result.ok r →
            r = ofDigits [1, 2 * d0 - 10]) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (ds : List Int)
    (hn_pos : ds ≠ [])
    (hn_len : ds.length ≤ 10000)
    (hdigit : ∀ d ∈ ds, 0 ≤ d ∧ d ≤ 9)
    (hsignif : 1 < ds.length → ds.head? ≠ some 0)
    (hn_one : ds.length = 1), ∀ d0 : Int, ds = [d0] →
      (d0 ≤ 4 → ∀ r : Aegis.DoubleIt.List,
          Aegis.DoubleIt.double_it (ofDigits ds) = Aeneas.Std.Result.ok r →
            r = ofDigits [2 * d0]) ∧
        (5 ≤ d0 → ∀ r : Aegis.DoubleIt.List,
          Aegis.DoubleIt.double_it (ofDigits ds) = Aeneas.Std.Result.ok r →
            r = ofDigits [1, 2 * d0 - 10])) := by
  sorry

/-- Whenever the function returns a non-Nil result r, write r = Cons(e_0, ..., Cons(e_{m-1}, Nil)); then 1 <= e_0 <= 9.
  Preconditions: Write head = Cons(d_0, Cons(d_1, ..., Cons(d_{n-1}, Nil))) with n = len(head), so there are exactly n Cons nodes, and let N = sum_{i=0}^{n-1} d_i * 10^(n-1-i). Assume: n >= 1; n <= 10000; for every i with 0 <= i < n, 0 <= d_i <= 9; and if n > 1 then d_0 != 0. Additionally, N > 0. -/
theorem spec_11 (ds : List Int)
    (hn_pos : ds ≠ [])
    (hn_len : ds.length ≤ 10000)
    (hdigit : ∀ d ∈ ds, 0 ≤ d ∧ d ≤ 9)
    (hsignif : 1 < ds.length → ds.head? ≠ some 0)
    (hN : 0 < numValue ds) :
    ∀ r : Aegis.DoubleIt.List, Aegis.DoubleIt.double_it (ofDigits ds) = Aeneas.Std.Result.ok r →
      r ≠ Aegis.DoubleIt.List.Nil →
        ∀ e : Int, (digitsOf r).head? = some e → 1 ≤ e ∧ e ≤ 9 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (ds : List Int)
    (hn_pos : ds ≠ [])
    (hn_len : ds.length ≤ 10000)
    (hdigit : ∀ d ∈ ds, 0 ≤ d ∧ d ≤ 9)
    (hsignif : 1 < ds.length → ds.head? ≠ some 0)
    (hN : 0 < numValue ds), ∀ r : Aegis.DoubleIt.List, Aegis.DoubleIt.double_it (ofDigits ds) = Aeneas.Std.Result.ok r →
      r ≠ Aegis.DoubleIt.List.Nil →
        ∀ e : Int, (digitsOf r).head? = some e → 1 ≤ e ∧ e ≤ 9) := by
  sorry

/-- Whenever the function returns a non-Nil result r, let t be the number of consecutive zero digits at the end of head (equivalently, the largest t such that the last t input digits are all 0; for t = 0 this means the last input digit is not 0), and let s be the analogous number of consecutive zero digits at the end of r, using m = len(r). Then s >= t.
  Preconditions: Write head = Cons(d_0, Cons(d_1, ..., Cons(d_{n-1}, Nil))) with n = len(head), so there are exactly n Cons nodes, and let N = sum_{i=0}^{n-1} d_i * 10^(n-1-i). Assume: n >= 1; n <= 10000; for every i with 0 <= i < n, 0 <= d_i <= 9; and if n > 1 then d_0 != 0. Additionally, N > 0. -/
theorem spec_12 (ds : List Int)
    (hn_pos : ds ≠ [])
    (hn_len : ds.length ≤ 10000)
    (hdigit : ∀ d ∈ ds, 0 ≤ d ∧ d ≤ 9)
    (hsignif : 1 < ds.length → ds.head? ≠ some 0)
    (hN : 0 < numValue ds) :
    ∀ r : Aegis.DoubleIt.List, Aegis.DoubleIt.double_it (ofDigits ds) = Aeneas.Std.Result.ok r →
      r ≠ Aegis.DoubleIt.List.Nil → trailingZeros ds ≤ trailingZeros (digitsOf r) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (ds : List Int)
    (hn_pos : ds ≠ [])
    (hn_len : ds.length ≤ 10000)
    (hdigit : ∀ d ∈ ds, 0 ≤ d ∧ d ≤ 9)
    (hsignif : 1 < ds.length → ds.head? ≠ some 0)
    (hN : 0 < numValue ds), ∀ r : Aegis.DoubleIt.List, Aegis.DoubleIt.double_it (ofDigits ds) = Aeneas.Std.Result.ok r →
      r ≠ Aegis.DoubleIt.List.Nil → trailingZeros ds ≤ trailingZeros (digitsOf r)) := by
  sorry

/-- Whenever the function returns a result r, r = Cons(1, Cons(9, ..., Cons(9, Cons(8, Nil)))) with exactly n-1 copies of 9 between the initial 1 and the final 8.
  Preconditions: Write head = Cons(d_0, Cons(d_1, ..., Cons(d_{n-1}, Nil))) with n = len(head), so there are exactly n Cons nodes, and let N = sum_{i=0}^{n-1} d_i * 10^(n-1-i). Assume: n >= 1; n <= 10000; for every i with 0 <= i < n, 0 <= d_i <= 9; and if n > 1 then d_0 != 0. Additionally, n >= 2 and d_i = 9 for every i with 0 <= i < n. -/
theorem spec_13 (ds : List Int)
    (hn_pos : ds ≠ [])
    (hn_len : ds.length ≤ 10000)
    (hdigit : ∀ d ∈ ds, 0 ≤ d ∧ d ≤ 9)
    (hsignif : 1 < ds.length → ds.head? ≠ some 0)
    (hn_two : 2 ≤ ds.length)
    (hall_nine : ∀ d ∈ ds, d = 9) :
    ∀ r : Aegis.DoubleIt.List, Aegis.DoubleIt.double_it (ofDigits ds) = Aeneas.Std.Result.ok r →
      r = ofDigits (1 :: (List.replicate (ds.length - 1) 9 ++ [8])) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (ds : List Int)
    (hn_pos : ds ≠ [])
    (hn_len : ds.length ≤ 10000)
    (hdigit : ∀ d ∈ ds, 0 ≤ d ∧ d ≤ 9)
    (hsignif : 1 < ds.length → ds.head? ≠ some 0)
    (hn_two : 2 ≤ ds.length)
    (hall_nine : ∀ d ∈ ds, d = 9), ∀ r : Aegis.DoubleIt.List, Aegis.DoubleIt.double_it (ofDigits ds) = Aeneas.Std.Result.ok r →
      r = ofDigits (1 :: (List.replicate (ds.length - 1) 9 ++ [8]))) := by
  sorry

end AegisSpec.DoubleIt
