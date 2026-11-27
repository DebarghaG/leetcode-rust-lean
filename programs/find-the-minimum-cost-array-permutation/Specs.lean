import Aegis.FindPermutation.Code.Funs

/-!
# Specifications of `Aegis.FindPermutation.find_permutation`

LeetCode problem `find-the-minimum-cost-array-permutation`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.FindPermutation

def ival (x : Std.I64) : ℤ := x.val

def entry (l : List Std.I64) (i : ℕ) : ℤ := ival (l.getD i default)

def IsPermOfRange (l : List Std.I64) (n : ℕ) : Prop :=
  l.length = n ∧
    (∀ i, i < n → 0 ≤ entry l i ∧ entry l i < (n : ℤ)) ∧
    (∀ i j, i < j → j < n → entry l i ≠ entry l j)

def score (perm nums : List Std.I64) (n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range n,
    |entry perm i - entry nums ((entry perm ((i + 1) % n)).toNat)|

def LexLE (p q : List Std.I64) : Prop :=
  p = q ∨
    ∃ k, k < p.length ∧ k < q.length ∧ p.take k = q.take k ∧ entry p k < entry q k

/-- The function returns a result r such that: (1) len(r) = n; (2) for every i with 0 <= i < n, 0 <= r[i] < n; (3) for every i,j with 0 <= i < j < n, r[i] != r[j]; (4) for every sequence p of length n that is a permutation of [0,1,...,n-1], score(r) <= score(p); (5) for every sequence p of length n that is a permutation of [0,1,...,n-1], if score(p) = score(r), then r is lexicographically less than or equal to p. Here score(perm) = Σ_{i=0}^{n-1} |perm[i] - nums[perm[(i+1) mod n]]|.
  Preconditions: n = len(nums), 2 <= n <= 14, and nums is a permutation of [0,1,...,n-1] (i.e., for every i with 0 <= i < n, 0 <= nums[i] < n, and for every i,j with 0 <= i < j < n, nums[i] != nums[j]). -/
theorem spec_1 (nums : Slice Std.I64) (n : ℕ) (hn : n = nums.val.length)
    (hn2 : 2 ≤ n) (hn14 : n ≤ 14) (hperm : IsPermOfRange nums.val n) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.FindPermutation.find_permutation nums = ok r ∧
        IsPermOfRange r.val n ∧
        (∀ p : List Std.I64,
          IsPermOfRange p n → score r.val nums.val n ≤ score p nums.val n) ∧
        (∀ p : List Std.I64,
          IsPermOfRange p n →
            score p nums.val n = score r.val nums.val n → LexLE r.val p) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : ℕ) (hn : n = nums.val.length)
    (hn2 : 2 ≤ n) (hn14 : n ≤ 14) (hperm : IsPermOfRange nums.val n), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.FindPermutation.find_permutation nums = ok r ∧
        IsPermOfRange r.val n ∧
        (∀ p : List Std.I64,
          IsPermOfRange p n → score r.val nums.val n ≤ score p nums.val n) ∧
        (∀ p : List Std.I64,
          IsPermOfRange p n →
            score p nums.val n = score r.val nums.val n → LexLE r.val p)) := by
  sorry

/-- The function returns a result r with len(r) = len(nums).
  Preconditions: n = len(nums), 2 <= n <= 14, and nums is a permutation of [0,1,...,n-1]. -/
theorem spec_2 (nums : Slice Std.I64) (n : ℕ) (hn : n = nums.val.length)
    (hn2 : 2 ≤ n) (hn14 : n ≤ 14) (hperm : IsPermOfRange nums.val n) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.FindPermutation.find_permutation nums = ok r ∧
        r.val.length = nums.val.length := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : ℕ) (hn : n = nums.val.length)
    (hn2 : 2 ≤ n) (hn14 : n ≤ 14) (hperm : IsPermOfRange nums.val n), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.FindPermutation.find_permutation nums = ok r ∧
        r.val.length = nums.val.length) := by
  sorry

/-- The function returns a result r such that for every index i with 0 <= i < len(r), 0 <= r[i] < len(nums).
  Preconditions: n = len(nums), 2 <= n <= 14, and nums is a permutation of [0,1,...,n-1]. -/
theorem spec_3 (nums : Slice Std.I64) (n : ℕ) (hn : n = nums.val.length)
    (hn2 : 2 ≤ n) (hn14 : n ≤ 14) (hperm : IsPermOfRange nums.val n) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.FindPermutation.find_permutation nums = ok r ∧
        ∀ i, i < r.val.length →
          0 ≤ entry r.val i ∧ entry r.val i < (nums.val.length : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : ℕ) (hn : n = nums.val.length)
    (hn2 : 2 ≤ n) (hn14 : n ≤ 14) (hperm : IsPermOfRange nums.val n), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.FindPermutation.find_permutation nums = ok r ∧
        ∀ i, i < r.val.length →
          0 ≤ entry r.val i ∧ entry r.val i < (nums.val.length : ℤ)) := by
  sorry

/-- The function returns a result r such that for every i,j with 0 <= i < j < len(r), r[i] != r[j].
  Preconditions: n = len(nums), 2 <= n <= 14, and nums is a permutation of [0,1,...,n-1]. -/
theorem spec_4 (nums : Slice Std.I64) (n : ℕ) (hn : n = nums.val.length)
    (hn2 : 2 ≤ n) (hn14 : n ≤ 14) (hperm : IsPermOfRange nums.val n) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.FindPermutation.find_permutation nums = ok r ∧
        ∀ i j, i < j → j < r.val.length → entry r.val i ≠ entry r.val j := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : ℕ) (hn : n = nums.val.length)
    (hn2 : 2 ≤ n) (hn14 : n ≤ 14) (hperm : IsPermOfRange nums.val n), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.FindPermutation.find_permutation nums = ok r ∧
        ∀ i j, i < j → j < r.val.length → entry r.val i ≠ entry r.val j) := by
  sorry

/-- The function returns a result r such that for every value v with 0 <= v < len(nums), there exists an index i with 0 <= i < len(r) such that r[i] = v.
  Preconditions: n = len(nums), 2 <= n <= 14, and nums is a permutation of [0,1,...,n-1]. -/
theorem spec_5 (nums : Slice Std.I64) (n : ℕ) (hn : n = nums.val.length)
    (hn2 : 2 ≤ n) (hn14 : n ≤ 14) (hperm : IsPermOfRange nums.val n) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.FindPermutation.find_permutation nums = ok r ∧
        ∀ v : ℤ,
          0 ≤ v → v < (nums.val.length : ℤ) →
            ∃ i, i < r.val.length ∧ entry r.val i = v := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : ℕ) (hn : n = nums.val.length)
    (hn2 : 2 ≤ n) (hn14 : n ≤ 14) (hperm : IsPermOfRange nums.val n), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.FindPermutation.find_permutation nums = ok r ∧
        ∀ v : ℤ,
          0 ≤ v → v < (nums.val.length : ℤ) →
            ∃ i, i < r.val.length ∧ entry r.val i = v) := by
  sorry

/-- Let score(perm) = Σ_{i=0}^{n-1} |perm[i] - nums[perm[(i+1) mod n]]| for any sequence perm of length n with elements in [0,n-1]. The function returns a result r such that for every sequence p of length n that is a permutation of [0,1,...,n-1], score(r) <= score(p).
  Preconditions: n = len(nums), 2 <= n <= 14, and nums is a permutation of [0,1,...,n-1]. -/
theorem spec_6 (nums : Slice Std.I64) (n : ℕ) (hn : n = nums.val.length)
    (hn2 : 2 ≤ n) (hn14 : n ≤ 14) (hperm : IsPermOfRange nums.val n) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.FindPermutation.find_permutation nums = ok r ∧
        ∀ p : List Std.I64,
          IsPermOfRange p n → score r.val nums.val n ≤ score p nums.val n := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : ℕ) (hn : n = nums.val.length)
    (hn2 : 2 ≤ n) (hn14 : n ≤ 14) (hperm : IsPermOfRange nums.val n), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.FindPermutation.find_permutation nums = ok r ∧
        ∀ p : List Std.I64,
          IsPermOfRange p n → score r.val nums.val n ≤ score p nums.val n) := by
  sorry

/-- Let score(perm) = Σ_{i=0}^{n-1} |perm[i] - nums[perm[(i+1) mod n]]| for any sequence perm of length n with elements in [0,n-1]. Let <=_lex denote lexicographic order on sequences of length n: p <=_lex q iff p = q or there exists k with 0 <= k < n such that p[0..k-1] = q[0..k-1] and p[k] < q[k]. The function returns a result r such that for every sequence p of length n that is a permutation of [0,1,...,n-1], if score(p) = score(r) then r <=_lex p.
  Preconditions: n = len(nums), 2 <= n <= 14, and nums is a permutation of [0,1,...,n-1]. -/
theorem spec_7 (nums : Slice Std.I64) (n : ℕ) (hn : n = nums.val.length)
    (hn2 : 2 ≤ n) (hn14 : n ≤ 14) (hperm : IsPermOfRange nums.val n) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.FindPermutation.find_permutation nums = ok r ∧
        ∀ p : List Std.I64,
          IsPermOfRange p n →
            score p nums.val n = score r.val nums.val n → LexLE r.val p := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : ℕ) (hn : n = nums.val.length)
    (hn2 : 2 ≤ n) (hn14 : n ≤ 14) (hperm : IsPermOfRange nums.val n), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.FindPermutation.find_permutation nums = ok r ∧
        ∀ p : List Std.I64,
          IsPermOfRange p n →
            score p nums.val n = score r.val nums.val n → LexLE r.val p) := by
  sorry

/-- The function returns a result r (i.e., it does not fail or panic).
  Preconditions: n = len(nums), 2 <= n <= 14, and nums is a permutation of [0,1,...,n-1]. -/
theorem spec_8 (nums : Slice Std.I64) (n : ℕ) (hn : n = nums.val.length)
    (hn2 : 2 ≤ n) (hn14 : n ≤ 14) (hperm : IsPermOfRange nums.val n) :
    ∃ r : alloc.vec.Vec Std.I64, Aegis.FindPermutation.find_permutation nums = ok r := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : ℕ) (hn : n = nums.val.length)
    (hn2 : 2 ≤ n) (hn14 : n ≤ 14) (hperm : IsPermOfRange nums.val n), ∃ r : alloc.vec.Vec Std.I64, Aegis.FindPermutation.find_permutation nums = ok r) := by
  sorry

/-- The function returns a result r with r[0] = 0.
  Preconditions: n = len(nums), 2 <= n <= 14, and nums is a permutation of [0,1,...,n-1]. -/
theorem spec_9 (nums : Slice Std.I64) (n : ℕ) (hn : n = nums.val.length)
    (hn2 : 2 ≤ n) (hn14 : n ≤ 14) (hperm : IsPermOfRange nums.val n) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.FindPermutation.find_permutation nums = ok r ∧ entry r.val 0 = 0 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : ℕ) (hn : n = nums.val.length)
    (hn2 : 2 ≤ n) (hn14 : n ≤ 14) (hperm : IsPermOfRange nums.val n), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.FindPermutation.find_permutation nums = ok r ∧ entry r.val 0 = 0) := by
  sorry

end AegisSpec.FindPermutation
