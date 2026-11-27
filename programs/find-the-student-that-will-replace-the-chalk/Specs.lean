import Aegis.ChalkReplacer.Code.Funs

/-!
# Specifications of `Aegis.ChalkReplacer.chalk_replacer`

LeetCode problem `find-the-student-that-will-replace-the-chalk`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.ChalkReplacer

def n (chalk : Slice I64) : Nat := chalk.val.length

def total (chalk : Slice I64) : Int :=
  (chalk.val.map (fun x => x.val)).sum

def prefixSum (chalk : Slice I64) (i : Int) : Int :=
  ((chalk.val.take (Int.toNat (i + 1))).map (fun x => x.val)).sum

def first (chalk : Slice I64) : Int :=
  (chalk.val.head?.map (fun x => x.val)).getD 0

def chalkBounds (chalk : Slice I64) : Prop :=
  ∀ (i : Nat) (h : i < chalk.val.length),
    1 ≤ (chalk.val.get ⟨i, h⟩).val ∧ (chalk.val.get ⟨i, h⟩).val ≤ 100000

def leastExceeding (chalk : Slice I64) (m r : Int) : Prop :=
  0 ≤ r ∧ r < (n chalk : Int) ∧ prefixSum chalk r > m ∧
    ∀ i : Int, 0 ≤ i → i < r → prefixSum chalk i ≤ m

/-- Let S = sum from j = 0 to n-1 of chalk[j], and let m be the unique integer such that 0 <= m < S and k = q*S + m for some integer q (so m = k mod S). The function returns a result r, and r is the least integer i with 0 <= i < n such that (sum from j = 0 to i of chalk[j]) > m.
  Preconditions: Let n = len(chalk). Assume 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= chalk[i] <= 100000; and 1 <= k <= 1000000000, all as mathematical integers. -/
theorem spec_1 (chalk : Slice I64) (k : I64)
    (hn1 : 1 ≤ n chalk) (hn2 : n chalk ≤ 100000)
    (hchalk : chalkBounds chalk)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000000000)
    (m : Int) (hm : m = k.val % total chalk) :
    ∃ r : I64, Aegis.ChalkReplacer.chalk_replacer chalk k = ok r ∧
      leastExceeding chalk m r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (chalk : Slice I64) (k : I64)
    (hn1 : 1 ≤ n chalk) (hn2 : n chalk ≤ 100000)
    (hchalk : chalkBounds chalk)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000000000)
    (m : Int) (hm : m = k.val % total chalk), ∃ r : I64, Aegis.ChalkReplacer.chalk_replacer chalk k = ok r ∧
      leastExceeding chalk m r.val) := by
  sorry

/-- The function returns a result r; in particular it does not fail, panic, or get stuck on any input satisfying the preconditions.
  Preconditions: Let n = len(chalk). Assume 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= chalk[i] <= 100000; and 1 <= k <= 1000000000. -/
theorem spec_2 (chalk : Slice I64) (k : I64)
    (hn1 : 1 ≤ n chalk) (hn2 : n chalk ≤ 100000)
    (hchalk : chalkBounds chalk)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000000000) :
    ∃ r : I64, Aegis.ChalkReplacer.chalk_replacer chalk k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (chalk : Slice I64) (k : I64)
    (hn1 : 1 ≤ n chalk) (hn2 : n chalk ≤ 100000)
    (hchalk : chalkBounds chalk)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000000000), ∃ r : I64, Aegis.ChalkReplacer.chalk_replacer chalk k = ok r) := by
  sorry

/-- Whenever the function returns a result r, r is a valid 0-based student index: 0 <= r < len(chalk).
  Preconditions: Let n = len(chalk). Assume 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= chalk[i] <= 100000; and 1 <= k <= 1000000000. -/
theorem spec_3 (chalk : Slice I64) (k : I64)
    (hn1 : 1 ≤ n chalk) (hn2 : n chalk ≤ 100000)
    (hchalk : chalkBounds chalk)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000000000)
    (r : I64) (hr : Aegis.ChalkReplacer.chalk_replacer chalk k = ok r) :
    0 ≤ r.val ∧ r.val < (n chalk : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (chalk : Slice I64) (k : I64)
    (hn1 : 1 ≤ n chalk) (hn2 : n chalk ≤ 100000)
    (hchalk : chalkBounds chalk)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000000000)
    (r : I64) (hr : Aegis.ChalkReplacer.chalk_replacer chalk k = ok r), 0 ≤ r.val ∧ r.val < (n chalk : Int)) := by
  sorry

/-- If len(chalk) = 1, the function returns r = 0.
  Preconditions: Let n = len(chalk). Assume 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= chalk[i] <= 100000; 1 <= k <= 1000000000; and len(chalk) = 1. -/
theorem spec_4 (chalk : Slice I64) (k : I64)
    (hn1 : 1 ≤ n chalk) (hn2 : n chalk ≤ 100000)
    (hchalk : chalkBounds chalk)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000000000)
    (h1 : n chalk = 1) :
    ∃ r : I64, Aegis.ChalkReplacer.chalk_replacer chalk k = ok r ∧ r.val = 0 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (chalk : Slice I64) (k : I64)
    (hn1 : 1 ≤ n chalk) (hn2 : n chalk ≤ 100000)
    (hchalk : chalkBounds chalk)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000000000)
    (h1 : n chalk = 1), ∃ r : I64, Aegis.ChalkReplacer.chalk_replacer chalk k = ok r ∧ r.val = 0) := by
  sorry

/-- If k = q*S for some positive integer q, then the function returns r = 0.
  Preconditions: Let n = len(chalk). Assume 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= chalk[i] <= 100000; and 1 <= k <= 1000000000. Let S = sum from j = 0 to n-1 of chalk[j]. -/
theorem spec_5 (chalk : Slice I64) (k : I64)
    (hn1 : 1 ≤ n chalk) (hn2 : n chalk ≤ 100000)
    (hchalk : chalkBounds chalk)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000000000)
    (q : Int) (hq : 0 < q) (hkq : k.val = q * total chalk) :
    ∃ r : I64, Aegis.ChalkReplacer.chalk_replacer chalk k = ok r ∧ r.val = 0 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (chalk : Slice I64) (k : I64)
    (hn1 : 1 ≤ n chalk) (hn2 : n chalk ≤ 100000)
    (hchalk : chalkBounds chalk)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000000000)
    (q : Int) (hq : 0 < q) (hkq : k.val = q * total chalk), ∃ r : I64, Aegis.ChalkReplacer.chalk_replacer chalk k = ok r ∧ r.val = 0) := by
  sorry

/-- If k < chalk[0], then the function returns r = 0.
  Preconditions: Let n = len(chalk). Assume 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= chalk[i] <= 100000; and 1 <= k <= 1000000000. -/
theorem spec_6 (chalk : Slice I64) (k : I64)
    (hn1 : 1 ≤ n chalk) (hn2 : n chalk ≤ 100000)
    (hchalk : chalkBounds chalk)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000000000)
    (hk : k.val < first chalk) :
    ∃ r : I64, Aegis.ChalkReplacer.chalk_replacer chalk k = ok r ∧ r.val = 0 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (chalk : Slice I64) (k : I64)
    (hn1 : 1 ≤ n chalk) (hn2 : n chalk ≤ 100000)
    (hchalk : chalkBounds chalk)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000000000)
    (hk : k.val < first chalk), ∃ r : I64, Aegis.ChalkReplacer.chalk_replacer chalk k = ok r ∧ r.val = 0) := by
  sorry

/-- Whenever the function returns a result r, then 0 <= r < n and (sum from j = 0 to r of chalk[j]) > m.
  Preconditions: Let n = len(chalk). Assume 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= chalk[i] <= 100000; and 1 <= k <= 1000000000. Let S = sum from j = 0 to n-1 of chalk[j] and m = k mod S. -/
theorem spec_7 (chalk : Slice I64) (k : I64)
    (hn1 : 1 ≤ n chalk) (hn2 : n chalk ≤ 100000)
    (hchalk : chalkBounds chalk)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000000000)
    (m : Int) (hm : m = k.val % total chalk)
    (r : I64) (hr : Aegis.ChalkReplacer.chalk_replacer chalk k = ok r) :
    0 ≤ r.val ∧ r.val < (n chalk : Int) ∧ prefixSum chalk r.val > m := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (chalk : Slice I64) (k : I64)
    (hn1 : 1 ≤ n chalk) (hn2 : n chalk ≤ 100000)
    (hchalk : chalkBounds chalk)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000000000)
    (m : Int) (hm : m = k.val % total chalk)
    (r : I64) (hr : Aegis.ChalkReplacer.chalk_replacer chalk k = ok r), 0 ≤ r.val ∧ r.val < (n chalk : Int) ∧ prefixSum chalk r.val > m) := by
  sorry

/-- Whenever the function returns a result r, for every integer i with 0 <= i < r, (sum from j = 0 to i of chalk[j]) <= m.
  Preconditions: Let n = len(chalk). Assume 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= chalk[i] <= 100000; and 1 <= k <= 1000000000. Let S = sum from j = 0 to n-1 of chalk[j] and m = k mod S. -/
theorem spec_8 (chalk : Slice I64) (k : I64)
    (hn1 : 1 ≤ n chalk) (hn2 : n chalk ≤ 100000)
    (hchalk : chalkBounds chalk)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000000000)
    (m : Int) (hm : m = k.val % total chalk)
    (r : I64) (hr : Aegis.ChalkReplacer.chalk_replacer chalk k = ok r) :
    ∀ i : Int, 0 ≤ i → i < r.val → prefixSum chalk i ≤ m := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (chalk : Slice I64) (k : I64)
    (hn1 : 1 ≤ n chalk) (hn2 : n chalk ≤ 100000)
    (hchalk : chalkBounds chalk)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000000000)
    (m : Int) (hm : m = k.val % total chalk)
    (r : I64) (hr : Aegis.ChalkReplacer.chalk_replacer chalk k = ok r), ∀ i : Int, 0 ≤ i → i < r.val → prefixSum chalk i ≤ m) := by
  sorry

/-- Whenever the function returns r, r = n-1 if and only if (sum from j = 0 to n-2 of chalk[j]) <= m, where the sum over an empty range is 0 when n = 1.
  Preconditions: Let n = len(chalk). Assume 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= chalk[i] <= 100000; and 1 <= k <= 1000000000. Let S = sum from j = 0 to n-1 of chalk[j] and m = k mod S. -/
theorem spec_9 (chalk : Slice I64) (k : I64)
    (hn1 : 1 ≤ n chalk) (hn2 : n chalk ≤ 100000)
    (hchalk : chalkBounds chalk)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000000000)
    (m : Int) (hm : m = k.val % total chalk)
    (r : I64) (hr : Aegis.ChalkReplacer.chalk_replacer chalk k = ok r) :
    r.val = (n chalk : Int) - 1 ↔ prefixSum chalk ((n chalk : Int) - 2) ≤ m := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (chalk : Slice I64) (k : I64)
    (hn1 : 1 ≤ n chalk) (hn2 : n chalk ≤ 100000)
    (hchalk : chalkBounds chalk)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000000000)
    (m : Int) (hm : m = k.val % total chalk)
    (r : I64) (hr : Aegis.ChalkReplacer.chalk_replacer chalk k = ok r), r.val = (n chalk : Int) - 1 ↔ prefixSum chalk ((n chalk : Int) - 2) ≤ m) := by
  sorry

/-- If k < S, then the function returns a result r, and r is the least integer i with 0 <= i < n such that (sum from j = 0 to i of chalk[j]) > k.
  Preconditions: Let n = len(chalk). Assume 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= chalk[i] <= 100000; and 1 <= k <= 1000000000. Let S = sum from j = 0 to n-1 of chalk[j]. -/
theorem spec_10 (chalk : Slice I64) (k : I64)
    (hn1 : 1 ≤ n chalk) (hn2 : n chalk ≤ 100000)
    (hchalk : chalkBounds chalk)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000000000)
    (hk : k.val < total chalk) :
    ∃ r : I64, Aegis.ChalkReplacer.chalk_replacer chalk k = ok r ∧
      leastExceeding chalk k.val r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (chalk : Slice I64) (k : I64)
    (hn1 : 1 ≤ n chalk) (hn2 : n chalk ≤ 100000)
    (hchalk : chalkBounds chalk)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000000000)
    (hk : k.val < total chalk), ∃ r : I64, Aegis.ChalkReplacer.chalk_replacer chalk k = ok r ∧
      leastExceeding chalk k.val r.val) := by
  sorry

/-- If there exists an integer i with 0 <= i < n-1 such that m = (sum from j = 0 to i of chalk[j]), then whenever the function returns r, r > i.
  Preconditions: Let n = len(chalk). Assume 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= chalk[i] <= 100000; and 1 <= k <= 1000000000. Let S = sum from j = 0 to n-1 of chalk[j] and m = k mod S. -/
theorem spec_11 (chalk : Slice I64) (k : I64)
    (hn1 : 1 ≤ n chalk) (hn2 : n chalk ≤ 100000)
    (hchalk : chalkBounds chalk)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000000000)
    (m : Int) (hm : m = k.val % total chalk) :
    ∀ i : Int, 0 ≤ i → i < (n chalk : Int) - 1 → m = prefixSum chalk i →
      ∀ r : I64, Aegis.ChalkReplacer.chalk_replacer chalk k = ok r → i < r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (chalk : Slice I64) (k : I64)
    (hn1 : 1 ≤ n chalk) (hn2 : n chalk ≤ 100000)
    (hchalk : chalkBounds chalk)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000000000)
    (m : Int) (hm : m = k.val % total chalk), ∀ i : Int, 0 ≤ i → i < (n chalk : Int) - 1 → m = prefixSum chalk i →
      ∀ r : I64, Aegis.ChalkReplacer.chalk_replacer chalk k = ok r → i < r.val) := by
  sorry

/-- If chalk_replacer(chalk, k0) returns r0 and chalk_replacer(chalk, k0 + S) returns r1, then r0 = r1.
  Preconditions: Let n = len(chalk). Assume 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= chalk[i] <= 100000. Let S = sum from j = 0 to n-1 of chalk[j]. For an integer k0, assume 1 <= k0 <= 1000000000 and k0 + S <= 1000000000. -/
theorem spec_12 (chalk : Slice I64) (k0 k1 r0 r1 : I64)
    (hn1 : 1 ≤ n chalk) (hn2 : n chalk ≤ 100000)
    (hchalk : chalkBounds chalk)
    (hk0 : 1 ≤ k0.val) (hk0S : k0.val + total chalk ≤ 1000000000)
    (hk1 : k1.val = k0.val + total chalk)
    (hr0 : Aegis.ChalkReplacer.chalk_replacer chalk k0 = ok r0)
    (hr1 : Aegis.ChalkReplacer.chalk_replacer chalk k1 = ok r1) :
    r0.val = r1.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (chalk : Slice I64) (k0 k1 r0 r1 : I64)
    (hn1 : 1 ≤ n chalk) (hn2 : n chalk ≤ 100000)
    (hchalk : chalkBounds chalk)
    (hk0 : 1 ≤ k0.val) (hk0S : k0.val + total chalk ≤ 1000000000)
    (hk1 : k1.val = k0.val + total chalk)
    (hr0 : Aegis.ChalkReplacer.chalk_replacer chalk k0 = ok r0)
    (hr1 : Aegis.ChalkReplacer.chalk_replacer chalk k1 = ok r1), r0.val = r1.val) := by
  sorry

end AegisSpec.ChalkReplacer
