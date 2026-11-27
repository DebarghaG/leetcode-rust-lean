import Aegis.MinChanges.Code.Funs

/-!
# Specifications of `Aegis.MinChanges.min_changes`

LeetCode problem `number-of-bit-changes-to-make-two-integers-equal`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MinChanges

namespace AegisSpec.MinChanges

def bit (x : ℤ) (i : ℕ) : ℕ := if x.natAbs.testBit i then 1 else 0

def popcount (x : ℤ) : ℕ := (Nat.bits x.natAbs).countP id

def Submask (k n : ℤ) : Prop := ∀ i : ℕ, bit k i = 1 → bit n i = 1

def oneZeroCount (n k : ℤ) : ℕ :=
  ((Finset.range (Nat.size n.natAbs)).filter (fun i => bit n i = 1 ∧ bit k i = 0)).card

def bitXor (x y : ℤ) : ℤ := (x.natAbs.xor y.natAbs : ℕ)

def step (x y : ℤ) : Prop := ∃ i : ℕ, bit x i = 1 ∧ y = x - 2 ^ i

def reach : ℕ → ℤ → ℤ → Prop
  | 0, x, y => x = y
  | m + 1, x, y => ∃ z : ℤ, reach m x z ∧ step z y

def i64Double (x : Std.I64) : Std.I64 := ⟨BitVec.ofInt 64 (2 * x.val)⟩

/-- Whenever min_changes returns a result r, the following holds: if for every i >= 0, bit_i(k)=1 implies bit_i(n)=1, then r is the number of i >= 0 such that bit_i(n)=1 and bit_i(k)=0; otherwise r = -1.
  Preconditions: 1 <= n <= 1000000 and 1 <= k <= 1000000. For an integer x and i >= 0, bit_i(x) denotes the i-th binary digit of x (0-indexed), and popcount(x) denotes the number of i >= 0 with bit_i(x)=1. -/
theorem spec_1 (n k r : Std.I64)
    (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000)
    (hk : 1 ≤ k.val) (hk' : k.val ≤ 1000000)
    (hr : min_changes n k = ok r) :
    (Submask k.val n.val → r.val = (oneZeroCount n.val k.val : ℤ)) ∧
      (¬ Submask k.val n.val → r.val = -1) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n k r : Std.I64)
    (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000)
    (hk : 1 ≤ k.val) (hk' : k.val ≤ 1000000)
    (hr : min_changes n k = ok r), (Submask k.val n.val → r.val = (oneZeroCount n.val k.val : ℤ)) ∧
      (¬ Submask k.val n.val → r.val = -1)) := by
  sorry

/-- For every n and k satisfying the preconditions, min_changes returns a result r; it does not fail (no overflow, out-of-bounds access, or panic).
  Preconditions: 1 <= n <= 1000000 and 1 <= k <= 1000000. -/
theorem spec_2 (n k : Std.I64)
    (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000)
    (hk : 1 ≤ k.val) (hk' : k.val ≤ 1000000) :
    ∃ r : Std.I64, min_changes n k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n k : Std.I64)
    (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000)
    (hk : 1 ≤ k.val) (hk' : k.val ≤ 1000000), ∃ r : Std.I64, min_changes n k = ok r) := by
  sorry

/-- Whenever min_changes returns a result r, either r = -1 or 0 <= r <= popcount(n).
  Preconditions: 1 <= n <= 1000000 and 1 <= k <= 1000000. For an integer x, popcount(x) is the number of bit positions i >= 0 whose i-th binary digit is 1. -/
theorem spec_3 (n k r : Std.I64)
    (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000)
    (hk : 1 ≤ k.val) (hk' : k.val ≤ 1000000)
    (hr : min_changes n k = ok r) :
    r.val = -1 ∨ (0 ≤ r.val ∧ r.val ≤ (popcount n.val : ℤ)) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n k r : Std.I64)
    (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000)
    (hk : 1 ≤ k.val) (hk' : k.val ≤ 1000000)
    (hr : min_changes n k = ok r), r.val = -1 ∨ (0 ≤ r.val ∧ r.val ≤ (popcount n.val : ℤ))) := by
  sorry

/-- Whenever min_changes returns a result r, r = -1 if and only if there exists an i >= 0 such that bit_i(k)=1 and bit_i(n)=0.
  Preconditions: 1 <= n <= 1000000 and 1 <= k <= 1000000. For an integer x and i >= 0, bit_i(x) denotes the i-th binary digit of x (0-indexed). -/
theorem spec_4 (n k r : Std.I64)
    (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000)
    (hk : 1 ≤ k.val) (hk' : k.val ≤ 1000000)
    (hr : min_changes n k = ok r) :
    r.val = -1 ↔ ∃ i : ℕ, bit k.val i = 1 ∧ bit n.val i = 0 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n k r : Std.I64)
    (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000)
    (hk : 1 ≤ k.val) (hk' : k.val ≤ 1000000)
    (hr : min_changes n k = ok r), r.val = -1 ↔ ∃ i : ℕ, bit k.val i = 1 ∧ bit n.val i = 0) := by
  sorry

/-- Whenever min_changes returns a result r and k is a submask of n (that is, bit_i(k)=1 implies bit_i(n)=1 for every i >= 0), then r = popcount(n) - popcount(k).
  Preconditions: 1 <= n <= 1000000 and 1 <= k <= 1000000. For an integer x and i >= 0, bit_i(x) denotes the i-th binary digit of x (0-indexed), and popcount(x) counts the number of i >= 0 with bit_i(x)=1. -/
theorem spec_5 (n k r : Std.I64)
    (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000)
    (hk : 1 ≤ k.val) (hk' : k.val ≤ 1000000)
    (hr : min_changes n k = ok r) (hsub : Submask k.val n.val) :
    r.val = (popcount n.val : ℤ) - (popcount k.val : ℤ) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n k r : Std.I64)
    (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000)
    (hk : 1 ≤ k.val) (hk' : k.val ≤ 1000000)
    (hr : min_changes n k = ok r) (hsub : Submask k.val n.val), r.val = (popcount n.val : ℤ) - (popcount k.val : ℤ)) := by
  sorry

/-- Whenever min_changes returns a result r and k is a submask of n, r = popcount(n XOR k), where XOR is bitwise exclusive-or on the binary representations and popcount counts the 1-bits.
  Preconditions: 1 <= n <= 1000000 and 1 <= k <= 1000000. For an integer x and i >= 0, bit_i(x) denotes the i-th binary digit of x (0-indexed), and popcount(x) counts the number of i >= 0 with bit_i(x)=1. -/
theorem spec_6 (n k r : Std.I64)
    (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000)
    (hk : 1 ≤ k.val) (hk' : k.val ≤ 1000000)
    (hr : min_changes n k = ok r) (hsub : Submask k.val n.val) :
    r.val = (popcount (bitXor n.val k.val) : ℤ) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n k r : Std.I64)
    (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000)
    (hk : 1 ≤ k.val) (hk' : k.val ≤ 1000000)
    (hr : min_changes n k = ok r) (hsub : Submask k.val n.val), r.val = (popcount (bitXor n.val k.val) : ℤ)) := by
  sorry

/-- Whenever min_changes returns a result r, r = 0 if and only if n = k.
  Preconditions: 1 <= n <= 1000000 and 1 <= k <= 1000000. -/
theorem spec_7 (n k r : Std.I64)
    (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000)
    (hk : 1 ≤ k.val) (hk' : k.val ≤ 1000000)
    (hr : min_changes n k = ok r) :
    r.val = 0 ↔ n = k := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n k r : Std.I64)
    (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000)
    (hk : 1 ≤ k.val) (hk' : k.val ≤ 1000000)
    (hr : min_changes n k = ok r), r.val = 0 ↔ n = k) := by
  sorry

/-- Whenever min_changes returns a result r and k > n, r = -1.
  Preconditions: 1 <= n <= 1000000 and 1 <= k <= 1000000. -/
theorem spec_8 (n k r : Std.I64)
    (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000)
    (hk : 1 ≤ k.val) (hk' : k.val ≤ 1000000)
    (hr : min_changes n k = ok r) (hkn : n.val < k.val) :
    r.val = -1 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n k r : Std.I64)
    (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000)
    (hk : 1 ≤ k.val) (hk' : k.val ≤ 1000000)
    (hr : min_changes n k = ok r) (hkn : n.val < k.val), r.val = -1) := by
  sorry

/-- Whenever min_changes returns a result r with r != -1, there exists a sequence of exactly r operations, each replacing one current 1-bit by 0, that transforms n into k; moreover no sequence of fewer than r such operations transforms n into k.
  Preconditions: 1 <= n <= 1000000 and 1 <= k <= 1000000. -/
theorem spec_9 (n k r : Std.I64)
    (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000)
    (hk : 1 ≤ k.val) (hk' : k.val ≤ 1000000)
    (hr : min_changes n k = ok r) (hne : r.val ≠ -1) :
    ∃ m : ℕ, (m : ℤ) = r.val ∧ reach m n.val k.val ∧
      ∀ m' : ℕ, reach m' n.val k.val → m ≤ m' := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n k r : Std.I64)
    (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000)
    (hk : 1 ≤ k.val) (hk' : k.val ≤ 1000000)
    (hr : min_changes n k = ok r) (hne : r.val ≠ -1), ∃ m : ℕ, (m : ℤ) = r.val ∧ reach m n.val k.val ∧
      ∀ m' : ℕ, reach m' n.val k.val → m ≤ m') := by
  sorry

/-- Whenever min_changes returns a result r and r = -1, there is no sequence of allowed operations (each replacing one current 1-bit by 0) that transforms n into k.
  Preconditions: 1 <= n <= 1000000 and 1 <= k <= 1000000. -/
theorem spec_10 (n k r : Std.I64)
    (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000)
    (hk : 1 ≤ k.val) (hk' : k.val ≤ 1000000)
    (hr : min_changes n k = ok r) (hm1 : r.val = -1) :
    ¬ ∃ m : ℕ, reach m n.val k.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n k r : Std.I64)
    (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000)
    (hk : 1 ≤ k.val) (hk' : k.val ≤ 1000000)
    (hr : min_changes n k = ok r) (hm1 : r.val = -1), ¬ ∃ m : ℕ, reach m n.val k.val) := by
  sorry

/-- Whenever min_changes(2*n, 2*k) returns a result r and min_changes(n, k) returns a result r', we have r = r'.
  Preconditions: 1 <= n <= 500000 and 1 <= k <= 500000. For an integer x and i >= 0, bit_i(x) denotes the i-th binary digit of x (0-indexed). -/
theorem spec_11 (n k r r' : Std.I64)
    (hn : 1 ≤ n.val) (hn' : n.val ≤ 500000)
    (hk : 1 ≤ k.val) (hk' : k.val ≤ 500000)
    (hr : min_changes (i64Double n) (i64Double k) = ok r)
    (hr' : min_changes n k = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (n k r r' : Std.I64)
    (hn : 1 ≤ n.val) (hn' : n.val ≤ 500000)
    (hk : 1 ≤ k.val) (hk' : k.val ≤ 500000)
    (hr : min_changes (i64Double n) (i64Double k) = ok r)
    (hr' : min_changes n k = ok r'), r.val = r'.val) := by
  sorry

end AegisSpec.MinChanges
