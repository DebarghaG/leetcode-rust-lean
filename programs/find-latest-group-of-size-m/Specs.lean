import Aegis.FindLatestStep.Code.Funs

/-!
# Specifications of `Aegis.FindLatestStep.find_latest_step`

LeetCode problem `find-latest-group-of-size-m`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.FindLatestStep

def lenZ (arr : Slice Std.I64) : ℤ := (arr.val.length : ℤ)

def IsPerm (arr : Slice Std.I64) : Prop :=
  (∀ (i : ℕ) (_ : i < arr.val.length), 1 ≤ (arr.val[i]).val ∧ (arr.val[i]).val ≤ lenZ arr) ∧
    ∀ (i j : ℕ) (_ : i < j) (_ : j < arr.val.length), (arr.val[i]).val ≠ (arr.val[j]).val

def MemS (arr : Slice Std.I64) (k : ℤ) (q : ℤ) : Prop :=
  ∃ (j : ℕ) (_ : j < arr.val.length), (j : ℤ) < k ∧ (arr.val[j]).val = q

def IsMaxGroupAt (arr : Slice Std.I64) (m k p : ℤ) : Prop :=
  (∀ q : ℤ, p ≤ q → q ≤ p + m - 1 → MemS arr k q) ∧
    (p = 1 ∨ ¬ MemS arr k (p - 1)) ∧
      (p + m - 1 = lenZ arr ∨ ¬ MemS arr k (p + m))

def HasGroup (arr : Slice Std.I64) (m k : ℤ) : Prop :=
  ∃ p : ℤ, 1 ≤ p ∧ p ≤ lenZ arr - m + 1 ∧ IsMaxGroupAt arr m k p

def HasSomeGroup (arr : Slice Std.I64) (m : ℤ) : Prop :=
  ∃ k : ℤ, 1 ≤ k ∧ k ≤ lenZ arr ∧ HasGroup arr m k

/-- The function returns a result r. Let n = len(arr). For each integer k with 0 <= k <= n, define S_k = { arr[j] | 0 <= j < k } (the set of positions set to 1 after k steps). For 1 <= k <= n and 1 <= p <= n-m+1, say that [p, p+m-1] is a maximal group of ones of length m at step k iff: (a) for every q with p <= q <= p+m-1, q in S_k; (b) p = 1 or (p-1) not in S_k; (c) p+m-1 = n or (p+m) not in S_k. Say HasGroup(k) iff there exists p with 1 <= p <= n-m+1 satisfying (a)-(c). Then: if there exists an integer k with 1 <= k <= n and HasGroup(k), r is the maximum of { k | 1 <= k <= n and HasGroup(k) }; otherwise r = -1.
  Preconditions: Let n = len(arr). We assume n >= 1. We assume 1 <= m <= n. We assume arr is a permutation of the integers 1..n: for every i with 0 <= i < n, 1 <= arr[i] <= n; and for every i, j with 0 <= i < j < n, arr[i] != arr[j]. All arithmetic in the problem (indices, steps) fits in 64-bit signed integers. -/
theorem spec_1 (arr : Slice Std.I64) (m : Std.I64)
    (hn : 1 ≤ lenZ arr) (hm1 : 1 ≤ m.val) (hmn : m.val ≤ lenZ arr)
    (hperm : IsPerm arr) (hfit : lenZ arr ≤ Std.I64.max) :
    ∃ r : Std.I64,
      Aegis.FindLatestStep.find_latest_step arr m = ok r ∧
        (HasSomeGroup arr m.val →
            (1 ≤ r.val ∧ r.val ≤ lenZ arr ∧ HasGroup arr m.val r.val ∧
              ∀ k : ℤ, 1 ≤ k → k ≤ lenZ arr → HasGroup arr m.val k → k ≤ r.val)) ∧
          (¬ HasSomeGroup arr m.val → r.val = -1) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (arr : Slice Std.I64) (m : Std.I64)
    (hn : 1 ≤ lenZ arr) (hm1 : 1 ≤ m.val) (hmn : m.val ≤ lenZ arr)
    (hperm : IsPerm arr) (hfit : lenZ arr ≤ Std.I64.max), ∃ r : Std.I64,
      Aegis.FindLatestStep.find_latest_step arr m = ok r ∧
        (HasSomeGroup arr m.val →
            (1 ≤ r.val ∧ r.val ≤ lenZ arr ∧ HasGroup arr m.val r.val ∧
              ∀ k : ℤ, 1 ≤ k → k ≤ lenZ arr → HasGroup arr m.val k → k ≤ r.val)) ∧
          (¬ HasSomeGroup arr m.val → r.val = -1)) := by
  sorry

/-- The function returns a result r for every input satisfying the preconditions; it does not fail (no panic, no arithmetic overflow, no out-of-bounds access).
  Preconditions: Let n = len(arr). We assume n >= 1. We assume 1 <= m <= n. We assume arr is a permutation of the integers 1..n: for every i with 0 <= i < n, 1 <= arr[i] <= n; and for every i, j with 0 <= i < j < n, arr[i] != arr[j]. All arithmetic in the problem (indices, steps) fits in 64-bit signed integers. -/
theorem spec_2 (arr : Slice Std.I64) (m : Std.I64)
    (hn : 1 ≤ lenZ arr) (hm1 : 1 ≤ m.val) (hmn : m.val ≤ lenZ arr)
    (hperm : IsPerm arr) (hfit : lenZ arr ≤ Std.I64.max) :
    ∃ r : Std.I64, Aegis.FindLatestStep.find_latest_step arr m = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (arr : Slice Std.I64) (m : Std.I64)
    (hn : 1 ≤ lenZ arr) (hm1 : 1 ≤ m.val) (hmn : m.val ≤ lenZ arr)
    (hperm : IsPerm arr) (hfit : lenZ arr ≤ Std.I64.max), ∃ r : Std.I64, Aegis.FindLatestStep.find_latest_step arr m = ok r) := by
  sorry

/-- Whenever the function returns a result r, either r = -1 or 1 <= r <= n, where n = len(arr).
  Preconditions: Let n = len(arr). We assume n >= 1. We assume 1 <= m <= n. We assume arr is a permutation of the integers 1..n: for every i with 0 <= i < n, 1 <= arr[i] <= n; and for every i, j with 0 <= i < j < n, arr[i] != arr[j]. All arithmetic in the problem (indices, steps) fits in 64-bit signed integers. -/
theorem spec_3 (arr : Slice Std.I64) (m : Std.I64)
    (hn : 1 ≤ lenZ arr) (hm1 : 1 ≤ m.val) (hmn : m.val ≤ lenZ arr)
    (hperm : IsPerm arr) (hfit : lenZ arr ≤ Std.I64.max) :
    ∀ r : Std.I64,
      Aegis.FindLatestStep.find_latest_step arr m = ok r →
        r.val = -1 ∨ (1 ≤ r.val ∧ r.val ≤ lenZ arr) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (arr : Slice Std.I64) (m : Std.I64)
    (hn : 1 ≤ lenZ arr) (hm1 : 1 ≤ m.val) (hmn : m.val ≤ lenZ arr)
    (hperm : IsPerm arr) (hfit : lenZ arr ≤ Std.I64.max), ∀ r : Std.I64,
      Aegis.FindLatestStep.find_latest_step arr m = ok r →
        r.val = -1 ∨ (1 ≤ r.val ∧ r.val ≤ lenZ arr)) := by
  sorry

/-- Whenever the function returns a result r, either r = -1 or m <= r <= n-1, where n = len(arr).
  Preconditions: Let n = len(arr). We assume n >= 1. We assume 1 <= m <= n. We assume m < n. We assume arr is a permutation of the integers 1..n: for every i with 0 <= i < n, 1 <= arr[i] <= n; and for every i, j with 0 <= i < j < n, arr[i] != arr[j]. All arithmetic in the problem (indices, steps) fits in 64-bit signed integers. -/
theorem spec_4 (arr : Slice Std.I64) (m : Std.I64)
    (hn : 1 ≤ lenZ arr) (hm1 : 1 ≤ m.val) (hmn : m.val ≤ lenZ arr)
    (hmn' : m.val < lenZ arr) (hperm : IsPerm arr) (hfit : lenZ arr ≤ Std.I64.max) :
    ∀ r : Std.I64,
      Aegis.FindLatestStep.find_latest_step arr m = ok r →
        r.val = -1 ∨ (m.val ≤ r.val ∧ r.val ≤ lenZ arr - 1) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (arr : Slice Std.I64) (m : Std.I64)
    (hn : 1 ≤ lenZ arr) (hm1 : 1 ≤ m.val) (hmn : m.val ≤ lenZ arr)
    (hmn' : m.val < lenZ arr) (hperm : IsPerm arr) (hfit : lenZ arr ≤ Std.I64.max), ∀ r : Std.I64,
      Aegis.FindLatestStep.find_latest_step arr m = ok r →
        r.val = -1 ∨ (m.val ≤ r.val ∧ r.val ≤ lenZ arr - 1)) := by
  sorry

/-- The function returns r = n, where n = len(arr).
  Preconditions: Let n = len(arr). We assume n >= 1. We assume 1 <= m <= n. We assume m = n. We assume arr is a permutation of the integers 1..n: for every i with 0 <= i < n, 1 <= arr[i] <= n; and for every i, j with 0 <= i < j < n, arr[i] != arr[j]. All arithmetic in the problem (indices, steps) fits in 64-bit signed integers. -/
theorem spec_5 (arr : Slice Std.I64) (m : Std.I64)
    (hn : 1 ≤ lenZ arr) (hm1 : 1 ≤ m.val) (hmn : m.val ≤ lenZ arr)
    (hm : m.val = lenZ arr) (hperm : IsPerm arr) (hfit : lenZ arr ≤ Std.I64.max) :
    ∃ r : Std.I64,
      Aegis.FindLatestStep.find_latest_step arr m = ok r ∧ r.val = lenZ arr := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (arr : Slice Std.I64) (m : Std.I64)
    (hn : 1 ≤ lenZ arr) (hm1 : 1 ≤ m.val) (hmn : m.val ≤ lenZ arr)
    (hm : m.val = lenZ arr) (hperm : IsPerm arr) (hfit : lenZ arr ≤ Std.I64.max), ∃ r : Std.I64,
      Aegis.FindLatestStep.find_latest_step arr m = ok r ∧ r.val = lenZ arr) := by
  sorry

/-- The function returns r = -1 or r = n-1, where n = len(arr).
  Preconditions: Let n = len(arr). We assume n >= 2. We assume 1 <= m <= n. We assume m = n-1. We assume arr is a permutation of the integers 1..n: for every i with 0 <= i < n, 1 <= arr[i] <= n; and for every i, j with 0 <= i < j < n, arr[i] != arr[j]. All arithmetic in the problem (indices, steps) fits in 64-bit signed integers. -/
theorem spec_6 (arr : Slice Std.I64) (m : Std.I64)
    (hn : 2 ≤ lenZ arr) (hm1 : 1 ≤ m.val) (hmn : m.val ≤ lenZ arr)
    (hm : m.val = lenZ arr - 1) (hperm : IsPerm arr) (hfit : lenZ arr ≤ Std.I64.max) :
    ∃ r : Std.I64,
      Aegis.FindLatestStep.find_latest_step arr m = ok r ∧
        (r.val = -1 ∨ r.val = lenZ arr - 1) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (arr : Slice Std.I64) (m : Std.I64)
    (hn : 2 ≤ lenZ arr) (hm1 : 1 ≤ m.val) (hmn : m.val ≤ lenZ arr)
    (hm : m.val = lenZ arr - 1) (hperm : IsPerm arr) (hfit : lenZ arr ≤ Std.I64.max), ∃ r : Std.I64,
      Aegis.FindLatestStep.find_latest_step arr m = ok r ∧
        (r.val = -1 ∨ r.val = lenZ arr - 1)) := by
  sorry

/-- The function returns r with r >= 1 (in particular, r != -1).
  Preconditions: Let n = len(arr). We assume n >= 1. We assume 1 <= m <= n. We assume m = 1. We assume arr is a permutation of the integers 1..n: for every i with 0 <= i < n, 1 <= arr[i] <= n; and for every i, j with 0 <= i < j < n, arr[i] != arr[j]. All arithmetic in the problem (indices, steps) fits in 64-bit signed integers. -/
theorem spec_7 (arr : Slice Std.I64) (m : Std.I64)
    (hn : 1 ≤ lenZ arr) (hm1 : 1 ≤ m.val) (hmn : m.val ≤ lenZ arr)
    (hm : m.val = 1) (hperm : IsPerm arr) (hfit : lenZ arr ≤ Std.I64.max) :
    ∃ r : Std.I64,
      Aegis.FindLatestStep.find_latest_step arr m = ok r ∧ 1 ≤ r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (arr : Slice Std.I64) (m : Std.I64)
    (hn : 1 ≤ lenZ arr) (hm1 : 1 ≤ m.val) (hmn : m.val ≤ lenZ arr)
    (hm : m.val = 1) (hperm : IsPerm arr) (hfit : lenZ arr ≤ Std.I64.max), ∃ r : Std.I64,
      Aegis.FindLatestStep.find_latest_step arr m = ok r ∧ 1 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r with r >= 1, there exists an integer p such that 1 <= p <= n-m+1 and [p, p+m-1] is a maximal group of ones of length m at step r. More explicitly, with S_r = { arr[j] | 0 <= j < r }: (a) for every q with p <= q <= p+m-1, q in S_r; (b) p = 1 or (p-1) not in S_r; (c) p+m-1 = n or (p+m) not in S_r.
  Preconditions: Let n = len(arr). We assume n >= 1. We assume 1 <= m <= n. We assume arr is a permutation of the integers 1..n: for every i with 0 <= i < n, 1 <= arr[i] <= n; and for every i, j with 0 <= i < j < n, arr[i] != arr[j]. All arithmetic in the problem (indices, steps) fits in 64-bit signed integers. -/
theorem spec_8 (arr : Slice Std.I64) (m : Std.I64)
    (hn : 1 ≤ lenZ arr) (hm1 : 1 ≤ m.val) (hmn : m.val ≤ lenZ arr)
    (hperm : IsPerm arr) (hfit : lenZ arr ≤ Std.I64.max) :
    ∀ r : Std.I64,
      Aegis.FindLatestStep.find_latest_step arr m = ok r →
        1 ≤ r.val →
          ∃ p : ℤ, 1 ≤ p ∧ p ≤ lenZ arr - m.val + 1 ∧ IsMaxGroupAt arr m.val r.val p := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (arr : Slice Std.I64) (m : Std.I64)
    (hn : 1 ≤ lenZ arr) (hm1 : 1 ≤ m.val) (hmn : m.val ≤ lenZ arr)
    (hperm : IsPerm arr) (hfit : lenZ arr ≤ Std.I64.max), ∀ r : Std.I64,
      Aegis.FindLatestStep.find_latest_step arr m = ok r →
        1 ≤ r.val →
          ∃ p : ℤ, 1 ≤ p ∧ p ≤ lenZ arr - m.val + 1 ∧ IsMaxGroupAt arr m.val r.val p) := by
  sorry

/-- Whenever the function returns a result r with r >= 1, for every step k with r < k <= n there is no maximal group of ones of length m at step k. That is, with S_k = { arr[j] | 0 <= j < k }, for every p with 1 <= p <= n-m+1, at least one of the following fails: (a) all q in [p, p+m-1] are in S_k; (b) p = 1 or p-1 not in S_k; (c) p+m-1 = n or p+m not in S_k.
  Preconditions: Let n = len(arr). We assume n >= 1. We assume 1 <= m <= n. We assume arr is a permutation of the integers 1..n: for every i with 0 <= i < n, 1 <= arr[i] <= n; and for every i, j with 0 <= i < j < n, arr[i] != arr[j]. All arithmetic in the problem (indices, steps) fits in 64-bit signed integers. -/
theorem spec_9 (arr : Slice Std.I64) (m : Std.I64)
    (hn : 1 ≤ lenZ arr) (hm1 : 1 ≤ m.val) (hmn : m.val ≤ lenZ arr)
    (hperm : IsPerm arr) (hfit : lenZ arr ≤ Std.I64.max) :
    ∀ r : Std.I64,
      Aegis.FindLatestStep.find_latest_step arr m = ok r →
        1 ≤ r.val →
          ∀ k : ℤ, r.val < k → k ≤ lenZ arr → ¬ HasGroup arr m.val k := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (arr : Slice Std.I64) (m : Std.I64)
    (hn : 1 ≤ lenZ arr) (hm1 : 1 ≤ m.val) (hmn : m.val ≤ lenZ arr)
    (hperm : IsPerm arr) (hfit : lenZ arr ≤ Std.I64.max), ∀ r : Std.I64,
      Aegis.FindLatestStep.find_latest_step arr m = ok r →
        1 ≤ r.val →
          ∀ k : ℤ, r.val < k → k ≤ lenZ arr → ¬ HasGroup arr m.val k) := by
  sorry

/-- Whenever the function returns r = -1, for every step k with 1 <= k <= n there is no maximal group of ones of length m at step k. That is, with S_k = { arr[j] | 0 <= j < k }, for every p with 1 <= p <= n-m+1, at least one of the following fails: (a) all q in [p, p+m-1] are in S_k; (b) p = 1 or p-1 not in S_k; (c) p+m-1 = n or p+m not in S_k.
  Preconditions: Let n = len(arr). We assume n >= 1. We assume 1 <= m <= n. We assume arr is a permutation of the integers 1..n: for every i with 0 <= i < n, 1 <= arr[i] <= n; and for every i, j with 0 <= i < j < n, arr[i] != arr[j]. All arithmetic in the problem (indices, steps) fits in 64-bit signed integers. -/
theorem spec_10 (arr : Slice Std.I64) (m : Std.I64)
    (hn : 1 ≤ lenZ arr) (hm1 : 1 ≤ m.val) (hmn : m.val ≤ lenZ arr)
    (hperm : IsPerm arr) (hfit : lenZ arr ≤ Std.I64.max) :
    ∀ r : Std.I64,
      Aegis.FindLatestStep.find_latest_step arr m = ok r →
        r.val = -1 →
          ∀ k : ℤ, 1 ≤ k → k ≤ lenZ arr → ¬ HasGroup arr m.val k := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (arr : Slice Std.I64) (m : Std.I64)
    (hn : 1 ≤ lenZ arr) (hm1 : 1 ≤ m.val) (hmn : m.val ≤ lenZ arr)
    (hperm : IsPerm arr) (hfit : lenZ arr ≤ Std.I64.max), ∀ r : Std.I64,
      Aegis.FindLatestStep.find_latest_step arr m = ok r →
        r.val = -1 →
          ∀ k : ℤ, 1 ≤ k → k ≤ lenZ arr → ¬ HasGroup arr m.val k) := by
  sorry

/-- Whenever the function returns a result r, we have 1 <= r <= n-1, where n = len(arr).
  Preconditions: Let n = len(arr). We assume n >= 2. We assume 1 <= m <= n. We assume m = 1. We assume arr is a permutation of the integers 1..n: for every i with 0 <= i < n, 1 <= arr[i] <= n; and for every i, j with 0 <= i < j < n, arr[i] != arr[j]. All arithmetic in the problem (indices, steps) fits in 64-bit signed integers. -/
theorem spec_11 (arr : Slice Std.I64) (m : Std.I64)
    (hn : 2 ≤ lenZ arr) (hm1 : 1 ≤ m.val) (hmn : m.val ≤ lenZ arr)
    (hm : m.val = 1) (hperm : IsPerm arr) (hfit : lenZ arr ≤ Std.I64.max) :
    ∀ r : Std.I64,
      Aegis.FindLatestStep.find_latest_step arr m = ok r →
        1 ≤ r.val ∧ r.val ≤ lenZ arr - 1 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (arr : Slice Std.I64) (m : Std.I64)
    (hn : 2 ≤ lenZ arr) (hm1 : 1 ≤ m.val) (hmn : m.val ≤ lenZ arr)
    (hm : m.val = 1) (hperm : IsPerm arr) (hfit : lenZ arr ≤ Std.I64.max), ∀ r : Std.I64,
      Aegis.FindLatestStep.find_latest_step arr m = ok r →
        1 ≤ r.val ∧ r.val ≤ lenZ arr - 1) := by
  sorry

end AegisSpec.FindLatestStep
