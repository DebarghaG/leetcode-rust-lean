import Aegis.MemLeak.Code.Funs

/-!
# Specifications of `Aegis.MemLeak.mem_leak`

LeetCode problem `incremental-memory-leak`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MemLeak

def IsLeastT (n t : ℤ) : Prop :=
  (1 : ℤ) ≤ t ∧ n < t * (t + 1) / 2 ∧
    ∀ s : ℤ, (1 : ℤ) ≤ s → n < s * (s + 1) / 2 → t ≤ s

/-- Whenever mem_leak(memory1, memory2) returns a result r, there exist an integer t and integer sequences A_0,...,A_{t-1} and B_0,...,B_{t-1} such that: t = r[0] and t >= 1; A_0 = memory1 and B_0 = memory2; for every k with 1 <= k < t, if A_{k-1} >= B_{k-1} then A_k = A_{k-1} - k and B_k = B_{k-1}, while if A_{k-1} < B_{k-1} then A_k = A_{k-1} and B_k = B_{k-1} - k; for every k with 1 <= k < t, A_{k-1} >= k or B_{k-1} >= k; A_{t-1} < t and B_{t-1} < t; and r = [t, A_{t-1}, B_{t-1}].
  Preconditions: 0 <= memory1 <= 2147483647 and 0 <= memory2 <= 2147483647 -/
theorem spec_1 (memory1 memory2 : Std.I64)
    (h1 : (0 : ℤ) ≤ memory1.val) (h1' : memory1.val ≤ (2147483647 : ℤ))
    (h2 : (0 : ℤ) ≤ memory2.val) (h2' : memory2.val ≤ (2147483647 : ℤ)) :
    ∀ r, Aegis.MemLeak.mem_leak memory1 memory2 = ok r →
      ∃ (t a b : Std.I64) (A B : ℤ → ℤ),
        r.val = [t, a, b] ∧
        (1 : ℤ) ≤ t.val ∧
        A 0 = memory1.val ∧
        B 0 = memory2.val ∧
        (∀ k : ℤ, (1 : ℤ) ≤ k → k < t.val →
          ((A (k - 1) ≥ B (k - 1) → A k = A (k - 1) - k ∧ B k = B (k - 1)) ∧
           (A (k - 1) < B (k - 1) → A k = A (k - 1) ∧ B k = B (k - 1) - k))) ∧
        (∀ k : ℤ, (1 : ℤ) ≤ k → k < t.val → A (k - 1) ≥ k ∨ B (k - 1) ≥ k) ∧
        a.val = A (t.val - 1) ∧
        b.val = B (t.val - 1) ∧
        a.val < t.val ∧
        b.val < t.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (memory1 memory2 : Std.I64)
    (h1 : (0 : ℤ) ≤ memory1.val) (h1' : memory1.val ≤ (2147483647 : ℤ))
    (h2 : (0 : ℤ) ≤ memory2.val) (h2' : memory2.val ≤ (2147483647 : ℤ)), ∀ r, Aegis.MemLeak.mem_leak memory1 memory2 = ok r →
      ∃ (t a b : Std.I64) (A B : ℤ → ℤ),
        r.val = [t, a, b] ∧
        (1 : ℤ) ≤ t.val ∧
        A 0 = memory1.val ∧
        B 0 = memory2.val ∧
        (∀ k : ℤ, (1 : ℤ) ≤ k → k < t.val →
          ((A (k - 1) ≥ B (k - 1) → A k = A (k - 1) - k ∧ B k = B (k - 1)) ∧
           (A (k - 1) < B (k - 1) → A k = A (k - 1) ∧ B k = B (k - 1) - k))) ∧
        (∀ k : ℤ, (1 : ℤ) ≤ k → k < t.val → A (k - 1) ≥ k ∨ B (k - 1) ≥ k) ∧
        a.val = A (t.val - 1) ∧
        b.val = B (t.val - 1) ∧
        a.val < t.val ∧
        b.val < t.val) := by
  sorry

/-- For every memory1 and memory2 satisfying the preconditions, mem_leak(memory1, memory2) returns some result r; it does not overflow, panic, or otherwise fail.
  Preconditions: 0 <= memory1 <= 2147483647 and 0 <= memory2 <= 2147483647 -/
theorem spec_2 (memory1 memory2 : Std.I64)
    (h1 : (0 : ℤ) ≤ memory1.val) (h1' : memory1.val ≤ (2147483647 : ℤ))
    (h2 : (0 : ℤ) ≤ memory2.val) (h2' : memory2.val ≤ (2147483647 : ℤ)) :
    ∃ r, Aegis.MemLeak.mem_leak memory1 memory2 = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (memory1 memory2 : Std.I64)
    (h1 : (0 : ℤ) ≤ memory1.val) (h1' : memory1.val ≤ (2147483647 : ℤ))
    (h2 : (0 : ℤ) ≤ memory2.val) (h2' : memory2.val ≤ (2147483647 : ℤ)), ∃ r, Aegis.MemLeak.mem_leak memory1 memory2 = ok r) := by
  sorry

/-- Whenever mem_leak(memory1, memory2) returns a result r, the length of r is exactly 3.
  Preconditions: 0 <= memory1 <= 2147483647 and 0 <= memory2 <= 2147483647 -/
theorem spec_3 (memory1 memory2 : Std.I64)
    (h1 : (0 : ℤ) ≤ memory1.val) (h1' : memory1.val ≤ (2147483647 : ℤ))
    (h2 : (0 : ℤ) ≤ memory2.val) (h2' : memory2.val ≤ (2147483647 : ℤ)) :
    ∀ r, Aegis.MemLeak.mem_leak memory1 memory2 = ok r → r.val.length = 3 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (memory1 memory2 : Std.I64)
    (h1 : (0 : ℤ) ≤ memory1.val) (h1' : memory1.val ≤ (2147483647 : ℤ))
    (h2 : (0 : ℤ) ≤ memory2.val) (h2' : memory2.val ≤ (2147483647 : ℤ)), ∀ r, Aegis.MemLeak.mem_leak memory1 memory2 = ok r → r.val.length = 3) := by
  sorry

/-- Whenever mem_leak(memory1, memory2) returns a result r, r[0] >= 1.
  Preconditions: 0 <= memory1 <= 2147483647 and 0 <= memory2 <= 2147483647 -/
theorem spec_4 (memory1 memory2 : Std.I64)
    (h1 : (0 : ℤ) ≤ memory1.val) (h1' : memory1.val ≤ (2147483647 : ℤ))
    (h2 : (0 : ℤ) ≤ memory2.val) (h2' : memory2.val ≤ (2147483647 : ℤ)) :
    ∀ r, Aegis.MemLeak.mem_leak memory1 memory2 = ok r → (1 : ℤ) ≤ (r.val[0]!).val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (memory1 memory2 : Std.I64)
    (h1 : (0 : ℤ) ≤ memory1.val) (h1' : memory1.val ≤ (2147483647 : ℤ))
    (h2 : (0 : ℤ) ≤ memory2.val) (h2' : memory2.val ≤ (2147483647 : ℤ)), ∀ r, Aegis.MemLeak.mem_leak memory1 memory2 = ok r → (1 : ℤ) ≤ (r.val[0]!).val) := by
  sorry

/-- Whenever mem_leak(memory1, memory2) returns a result r, r[1] < r[0] and r[2] < r[0].
  Preconditions: 0 <= memory1 <= 2147483647 and 0 <= memory2 <= 2147483647 -/
theorem spec_5 (memory1 memory2 : Std.I64)
    (h1 : (0 : ℤ) ≤ memory1.val) (h1' : memory1.val ≤ (2147483647 : ℤ))
    (h2 : (0 : ℤ) ≤ memory2.val) (h2' : memory2.val ≤ (2147483647 : ℤ)) :
    ∀ r, Aegis.MemLeak.mem_leak memory1 memory2 = ok r →
      (r.val[1]!).val < (r.val[0]!).val ∧ (r.val[2]!).val < (r.val[0]!).val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (memory1 memory2 : Std.I64)
    (h1 : (0 : ℤ) ≤ memory1.val) (h1' : memory1.val ≤ (2147483647 : ℤ))
    (h2 : (0 : ℤ) ≤ memory2.val) (h2' : memory2.val ≤ (2147483647 : ℤ)), ∀ r, Aegis.MemLeak.mem_leak memory1 memory2 = ok r →
      (r.val[1]!).val < (r.val[0]!).val ∧ (r.val[2]!).val < (r.val[0]!).val) := by
  sorry

/-- Whenever mem_leak(memory1, memory2) returns a result r, r[1] + r[2] + r[0]*(r[0]-1)/2 = memory1 + memory2.
  Preconditions: 0 <= memory1 <= 2147483647 and 0 <= memory2 <= 2147483647 -/
theorem spec_6 (memory1 memory2 : Std.I64)
    (h1 : (0 : ℤ) ≤ memory1.val) (h1' : memory1.val ≤ (2147483647 : ℤ))
    (h2 : (0 : ℤ) ≤ memory2.val) (h2' : memory2.val ≤ (2147483647 : ℤ)) :
    ∀ r, Aegis.MemLeak.mem_leak memory1 memory2 = ok r →
      (r.val[1]!).val + (r.val[2]!).val + (r.val[0]!).val * ((r.val[0]!).val - 1) / 2
        = memory1.val + memory2.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (memory1 memory2 : Std.I64)
    (h1 : (0 : ℤ) ≤ memory1.val) (h1' : memory1.val ≤ (2147483647 : ℤ))
    (h2 : (0 : ℤ) ≤ memory2.val) (h2' : memory2.val ≤ (2147483647 : ℤ)), ∀ r, Aegis.MemLeak.mem_leak memory1 memory2 = ok r →
      (r.val[1]!).val + (r.val[2]!).val + (r.val[0]!).val * ((r.val[0]!).val - 1) / 2
        = memory1.val + memory2.val) := by
  sorry

/-- Whenever mem_leak(memory1, memory2) returns a result r, 0 <= r[1] <= memory1.
  Preconditions: 0 <= memory1 <= 2147483647 and 0 <= memory2 <= 2147483647 -/
theorem spec_7 (memory1 memory2 : Std.I64)
    (h1 : (0 : ℤ) ≤ memory1.val) (h1' : memory1.val ≤ (2147483647 : ℤ))
    (h2 : (0 : ℤ) ≤ memory2.val) (h2' : memory2.val ≤ (2147483647 : ℤ)) :
    ∀ r, Aegis.MemLeak.mem_leak memory1 memory2 = ok r →
      (0 : ℤ) ≤ (r.val[1]!).val ∧ (r.val[1]!).val ≤ memory1.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (memory1 memory2 : Std.I64)
    (h1 : (0 : ℤ) ≤ memory1.val) (h1' : memory1.val ≤ (2147483647 : ℤ))
    (h2 : (0 : ℤ) ≤ memory2.val) (h2' : memory2.val ≤ (2147483647 : ℤ)), ∀ r, Aegis.MemLeak.mem_leak memory1 memory2 = ok r →
      (0 : ℤ) ≤ (r.val[1]!).val ∧ (r.val[1]!).val ≤ memory1.val) := by
  sorry

/-- Whenever mem_leak(memory1, memory2) returns a result r, 0 <= r[2] <= memory2.
  Preconditions: 0 <= memory1 <= 2147483647 and 0 <= memory2 <= 2147483647 -/
theorem spec_8 (memory1 memory2 : Std.I64)
    (h1 : (0 : ℤ) ≤ memory1.val) (h1' : memory1.val ≤ (2147483647 : ℤ))
    (h2 : (0 : ℤ) ≤ memory2.val) (h2' : memory2.val ≤ (2147483647 : ℤ)) :
    ∀ r, Aegis.MemLeak.mem_leak memory1 memory2 = ok r →
      (0 : ℤ) ≤ (r.val[2]!).val ∧ (r.val[2]!).val ≤ memory2.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (memory1 memory2 : Std.I64)
    (h1 : (0 : ℤ) ≤ memory1.val) (h1' : memory1.val ≤ (2147483647 : ℤ))
    (h2 : (0 : ℤ) ≤ memory2.val) (h2' : memory2.val ≤ (2147483647 : ℤ)), ∀ r, Aegis.MemLeak.mem_leak memory1 memory2 = ok r →
      (0 : ℤ) ≤ (r.val[2]!).val ∧ (r.val[2]!).val ≤ memory2.val) := by
  sorry

/-- Whenever mem_leak(memory1, memory2) returns a result r, r[0]*(r[0]-1)/2 <= memory1 + memory2.
  Preconditions: 0 <= memory1 <= 2147483647 and 0 <= memory2 <= 2147483647 -/
theorem spec_9 (memory1 memory2 : Std.I64)
    (h1 : (0 : ℤ) ≤ memory1.val) (h1' : memory1.val ≤ (2147483647 : ℤ))
    (h2 : (0 : ℤ) ≤ memory2.val) (h2' : memory2.val ≤ (2147483647 : ℤ)) :
    ∀ r, Aegis.MemLeak.mem_leak memory1 memory2 = ok r →
      (r.val[0]!).val * ((r.val[0]!).val - 1) / 2 ≤ memory1.val + memory2.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (memory1 memory2 : Std.I64)
    (h1 : (0 : ℤ) ≤ memory1.val) (h1' : memory1.val ≤ (2147483647 : ℤ))
    (h2 : (0 : ℤ) ≤ memory2.val) (h2' : memory2.val ≤ (2147483647 : ℤ)), ∀ r, Aegis.MemLeak.mem_leak memory1 memory2 = ok r →
      (r.val[0]!).val * ((r.val[0]!).val - 1) / 2 ≤ memory1.val + memory2.val) := by
  sorry

/-- Whenever mem_leak(memory1, memory2) returns a result r, r[0] <= 92682.
  Preconditions: 0 <= memory1 <= 2147483647 and 0 <= memory2 <= 2147483647 -/
theorem spec_10 (memory1 memory2 : Std.I64)
    (h1 : (0 : ℤ) ≤ memory1.val) (h1' : memory1.val ≤ (2147483647 : ℤ))
    (h2 : (0 : ℤ) ≤ memory2.val) (h2' : memory2.val ≤ (2147483647 : ℤ)) :
    ∀ r, Aegis.MemLeak.mem_leak memory1 memory2 = ok r →
      (r.val[0]!).val ≤ (92682 : ℤ) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (memory1 memory2 : Std.I64)
    (h1 : (0 : ℤ) ≤ memory1.val) (h1' : memory1.val ≤ (2147483647 : ℤ))
    (h2 : (0 : ℤ) ≤ memory2.val) (h2' : memory2.val ≤ (2147483647 : ℤ)), ∀ r, Aegis.MemLeak.mem_leak memory1 memory2 = ok r →
      (r.val[0]!).val ≤ (92682 : ℤ)) := by
  sorry

/-- Whenever mem_leak(memory1, memory2) returns a result r, r[0] = 1 if and only if memory1 = 0 and memory2 = 0.
  Preconditions: 0 <= memory1 <= 2147483647 and 0 <= memory2 <= 2147483647 -/
theorem spec_11 (memory1 memory2 : Std.I64)
    (h1 : (0 : ℤ) ≤ memory1.val) (h1' : memory1.val ≤ (2147483647 : ℤ))
    (h2 : (0 : ℤ) ≤ memory2.val) (h2' : memory2.val ≤ (2147483647 : ℤ)) :
    ∀ r, Aegis.MemLeak.mem_leak memory1 memory2 = ok r →
      ((r.val[0]!).val = (1 : ℤ) ↔ memory1.val = 0 ∧ memory2.val = 0) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (memory1 memory2 : Std.I64)
    (h1 : (0 : ℤ) ≤ memory1.val) (h1' : memory1.val ≤ (2147483647 : ℤ))
    (h2 : (0 : ℤ) ≤ memory2.val) (h2' : memory2.val ≤ (2147483647 : ℤ)), ∀ r, Aegis.MemLeak.mem_leak memory1 memory2 = ok r →
      ((r.val[0]!).val = (1 : ℤ) ↔ memory1.val = 0 ∧ memory2.val = 0)) := by
  sorry

/-- Whenever mem_leak(memory1, memory2) returns a result r, r[1] = 0, r[0] is the least positive integer t such that memory2 < t*(t+1)/2, and r[2] = memory2 - r[0]*(r[0]-1)/2.
  Preconditions: memory1 = 0 and 0 <= memory2 <= 2147483647 -/
theorem spec_12 (memory1 memory2 : Std.I64)
    (h1 : memory1.val = 0)
    (h2 : (0 : ℤ) ≤ memory2.val) (h2' : memory2.val ≤ (2147483647 : ℤ)) :
    ∀ r, Aegis.MemLeak.mem_leak memory1 memory2 = ok r →
      (r.val[1]!).val = 0 ∧
      IsLeastT memory2.val (r.val[0]!).val ∧
      (r.val[2]!).val = memory2.val - (r.val[0]!).val * ((r.val[0]!).val - 1) / 2 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (memory1 memory2 : Std.I64)
    (h1 : memory1.val = 0)
    (h2 : (0 : ℤ) ≤ memory2.val) (h2' : memory2.val ≤ (2147483647 : ℤ)), ∀ r, Aegis.MemLeak.mem_leak memory1 memory2 = ok r →
      (r.val[1]!).val = 0 ∧
      IsLeastT memory2.val (r.val[0]!).val ∧
      (r.val[2]!).val = memory2.val - (r.val[0]!).val * ((r.val[0]!).val - 1) / 2) := by
  sorry

/-- Whenever mem_leak(memory1, memory2) returns a result r, r[2] = 0, r[0] is the least positive integer t such that memory1 < t*(t+1)/2, and r[1] = memory1 - r[0]*(r[0]-1)/2.
  Preconditions: memory2 = 0 and 0 <= memory1 <= 2147483647 -/
theorem spec_13 (memory1 memory2 : Std.I64)
    (h1 : (0 : ℤ) ≤ memory1.val) (h1' : memory1.val ≤ (2147483647 : ℤ))
    (h2 : memory2.val = 0) :
    ∀ r, Aegis.MemLeak.mem_leak memory1 memory2 = ok r →
      (r.val[2]!).val = 0 ∧
      IsLeastT memory1.val (r.val[0]!).val ∧
      (r.val[1]!).val = memory1.val - (r.val[0]!).val * ((r.val[0]!).val - 1) / 2 := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (memory1 memory2 : Std.I64)
    (h1 : (0 : ℤ) ≤ memory1.val) (h1' : memory1.val ≤ (2147483647 : ℤ))
    (h2 : memory2.val = 0), ∀ r, Aegis.MemLeak.mem_leak memory1 memory2 = ok r →
      (r.val[2]!).val = 0 ∧
      IsLeastT memory1.val (r.val[0]!).val ∧
      (r.val[1]!).val = memory1.val - (r.val[0]!).val * ((r.val[0]!).val - 1) / 2) := by
  sorry

/-- Whenever mem_leak(memory1, memory2) returns a result r, for every second k with 1 <= k < r[0] at which the two sticks have equal available memory immediately before that second, the k bits allocated at second k are taken from the first stick; that is, the first stick's available memory decreases by k and the second stick's available memory is unchanged.
  Preconditions: 0 <= memory1 <= 2147483647 and 0 <= memory2 <= 2147483647 -/
theorem spec_14 (memory1 memory2 : Std.I64)
    (h1 : (0 : ℤ) ≤ memory1.val) (h1' : memory1.val ≤ (2147483647 : ℤ))
    (h2 : (0 : ℤ) ≤ memory2.val) (h2' : memory2.val ≤ (2147483647 : ℤ)) :
    ∀ r, Aegis.MemLeak.mem_leak memory1 memory2 = ok r →
      ∃ (t a b : Std.I64) (A B : ℤ → ℤ),
        r.val = [t, a, b] ∧
        (1 : ℤ) ≤ t.val ∧
        A 0 = memory1.val ∧
        B 0 = memory2.val ∧
        a.val = A (t.val - 1) ∧
        b.val = B (t.val - 1) ∧
        (∀ k : ℤ, (1 : ℤ) ≤ k → k < t.val → A (k - 1) = B (k - 1) →
          A k = A (k - 1) - k ∧ B k = B (k - 1)) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (memory1 memory2 : Std.I64)
    (h1 : (0 : ℤ) ≤ memory1.val) (h1' : memory1.val ≤ (2147483647 : ℤ))
    (h2 : (0 : ℤ) ≤ memory2.val) (h2' : memory2.val ≤ (2147483647 : ℤ)), ∀ r, Aegis.MemLeak.mem_leak memory1 memory2 = ok r →
      ∃ (t a b : Std.I64) (A B : ℤ → ℤ),
        r.val = [t, a, b] ∧
        (1 : ℤ) ≤ t.val ∧
        A 0 = memory1.val ∧
        B 0 = memory2.val ∧
        a.val = A (t.val - 1) ∧
        b.val = B (t.val - 1) ∧
        (∀ k : ℤ, (1 : ℤ) ≤ k → k < t.val → A (k - 1) = B (k - 1) →
          A k = A (k - 1) - k ∧ B k = B (k - 1))) := by
  sorry

end AegisSpec.MemLeak
