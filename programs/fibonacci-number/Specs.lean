import Aegis.Fib.Code.Funs

/-!
# Specifications of `Aegis.Fib.fib`

LeetCode problem `fibonacci-number`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.Fib

def fibSeq : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | k + 2 => fibSeq (k + 1) + fibSeq k

def fibAt (k : ℤ) : ℤ := fibSeq k.toNat

def i64 (k : ℤ) : Aeneas.Std.I64 := ⟨BitVec.ofInt 64 k⟩

theorem fibSeq_zero : fibSeq 0 = 0 := rfl

theorem fibSeq_one : fibSeq 1 = 1 := rfl

theorem fibSeq_add_two (k : ℕ) : fibSeq (k + 2) = fibSeq (k + 1) + fibSeq k := rfl

/-- Let F be the Fibonacci sequence with F(0)=0, F(1)=1, and F(k)=F(k-1)+F(k-2) for every integer k >= 2. The function returns a result r and r = F(n).
  Preconditions: n is a 64-bit integer with 0 <= n <= 30. -/
theorem spec_1 (n : Aeneas.Std.I64) (hn : 0 ≤ n.val ∧ n.val ≤ 30) :
    ∃ r, Aegis.Fib.fib n = ok r ∧ r.val = fibAt n.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Aeneas.Std.I64) (hn : 0 ≤ n.val ∧ n.val ≤ 30), ∃ r, Aegis.Fib.fib n = ok r ∧ r.val = fibAt n.val) := by
  sorry

/-- The function returns a result r; it does not fail, panic, or overflow.
  Preconditions: 0 <= n <= 30. -/
theorem spec_2 (n : Aeneas.Std.I64) (hn : 0 ≤ n.val ∧ n.val ≤ 30) :
    ∃ r, Aegis.Fib.fib n = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Aeneas.Std.I64) (hn : 0 ≤ n.val ∧ n.val ≤ 30), ∃ r, Aegis.Fib.fib n = ok r) := by
  sorry

/-- When the function is called with n, n-1, and n-2, it returns results r, r1, and r2 respectively, and r = r1 + r2.
  Preconditions: 2 <= n <= 30. -/
theorem spec_3 (n : Aeneas.Std.I64) (hn : 2 ≤ n.val ∧ n.val ≤ 30) :
    ∃ r r1 r2,
      Aegis.Fib.fib n = ok r ∧
        Aegis.Fib.fib (i64 (n.val - 1)) = ok r1 ∧
          Aegis.Fib.fib (i64 (n.val - 2)) = ok r2 ∧ r.val = r1.val + r2.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : Aeneas.Std.I64) (hn : 2 ≤ n.val ∧ n.val ≤ 30), ∃ r r1 r2,
      Aegis.Fib.fib n = ok r ∧
        Aegis.Fib.fib (i64 (n.val - 1)) = ok r1 ∧
          Aegis.Fib.fib (i64 (n.val - 2)) = ok r2 ∧ r.val = r1.val + r2.val) := by
  sorry

/-- The function returns a result r with 0 <= r <= 832040.
  Preconditions: 0 <= n <= 30. -/
theorem spec_4 (n : Aeneas.Std.I64) (hn : 0 ≤ n.val ∧ n.val ≤ 30) :
    ∃ r, Aegis.Fib.fib n = ok r ∧ 0 ≤ r.val ∧ r.val ≤ 832040 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : Aeneas.Std.I64) (hn : 0 ≤ n.val ∧ n.val ≤ 30), ∃ r, Aegis.Fib.fib n = ok r ∧ 0 ≤ r.val ∧ r.val ≤ 832040) := by
  sorry

/-- The function returns a result r with r >= n - 1.
  Preconditions: 1 <= n <= 30. -/
theorem spec_5 (n : Aeneas.Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 30) :
    ∃ r, Aegis.Fib.fib n = ok r ∧ n.val - 1 ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : Aeneas.Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 30), ∃ r, Aegis.Fib.fib n = ok r ∧ n.val - 1 ≤ r.val) := by
  sorry

/-- When the function is called with n1 and n2, it returns results r1 and r2 respectively, and r1 <= r2.
  Preconditions: 0 <= n1 <= n2 <= 30. -/
theorem spec_6 (n1 n2 : Aeneas.Std.I64)
    (h : 0 ≤ n1.val ∧ n1.val ≤ n2.val ∧ n2.val ≤ 30) :
    ∃ r1 r2, Aegis.Fib.fib n1 = ok r1 ∧ Aegis.Fib.fib n2 = ok r2 ∧ r1.val ≤ r2.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n1 n2 : Aeneas.Std.I64)
    (h : 0 ≤ n1.val ∧ n1.val ≤ n2.val ∧ n2.val ≤ 30), ∃ r1 r2, Aegis.Fib.fib n1 = ok r1 ∧ Aegis.Fib.fib n2 = ok r2 ∧ r1.val ≤ r2.val) := by
  sorry

/-- The function returns a result r such that r is even if and only if n is divisible by 3.
  Preconditions: 0 <= n <= 30. -/
theorem spec_7 (n : Aeneas.Std.I64) (hn : 0 ≤ n.val ∧ n.val ≤ 30) :
    ∃ r, Aegis.Fib.fib n = ok r ∧ (Even r.val ↔ (3 : ℤ) ∣ n.val) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : Aeneas.Std.I64) (hn : 0 ≤ n.val ∧ n.val ≤ 30), ∃ r, Aegis.Fib.fib n = ok r ∧ (Even r.val ↔ (3 : ℤ) ∣ n.val)) := by
  sorry

/-- The function returns a result r, and r = 0 if and only if n = 0.
  Preconditions: 0 <= n <= 30. -/
theorem spec_8 (n : Aeneas.Std.I64) (hn : 0 ≤ n.val ∧ n.val ≤ 30) :
    ∃ r, Aegis.Fib.fib n = ok r ∧ (r.val = 0 ↔ n.val = 0) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n : Aeneas.Std.I64) (hn : 0 ≤ n.val ∧ n.val ≤ 30), ∃ r, Aegis.Fib.fib n = ok r ∧ (r.val = 0 ↔ n.val = 0)) := by
  sorry

/-- The function returns a result r, and r = 1 if and only if n = 1 or n = 2.
  Preconditions: 0 <= n <= 30. -/
theorem spec_9 (n : Aeneas.Std.I64) (hn : 0 ≤ n.val ∧ n.val ≤ 30) :
    ∃ r, Aegis.Fib.fib n = ok r ∧ (r.val = 1 ↔ (n.val = 1 ∨ n.val = 2)) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n : Aeneas.Std.I64) (hn : 0 ≤ n.val ∧ n.val ≤ 30), ∃ r, Aegis.Fib.fib n = ok r ∧ (r.val = 1 ↔ (n.val = 1 ∨ n.val = 2))) := by
  sorry

end AegisSpec.Fib
