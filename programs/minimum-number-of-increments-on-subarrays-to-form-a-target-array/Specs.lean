import Aegis.MinNumberOperations.Code.Funs

/-!
# Specifications of `Aegis.MinNumberOperations.min_number_operations`

LeetCode problem `minimum-number-of-increments-on-subarrays-to-form-a-target-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.MinNumberOperations

  namespace AegisSpec.MinNumberOperations

  def vals (target : Slice Std.I64) : List ℤ := target.val.map (fun x => x.val)

  structure Op (n : ℕ) where

    L : ℕ

    R : ℕ

    hle : L ≤ R

    hlt : R < n

  def runOps {n : ℕ} (ops : List (Op n)) : List ℤ :=
    (List.range n).map fun i => ((ops.filter fun op => op.L ≤ i ∧ i ≤ op.R).length : ℤ)

  def reaches (n : ℕ) (k : ℕ) (t : List ℤ) : Prop :=
    ∃ ops : List (Op n), ops.length = k ∧ runOps ops = t

  def IsMinOps (n : ℕ) (t : List ℤ) (k : ℕ) : Prop :=
    reaches n k t ∧ ∀ k' : ℕ, reaches n k' t → k ≤ k'

  def maxVal (t : List ℤ) : ℤ := t.foldr max 0

  def risesSum : List ℤ → ℤ
    | [] => 0
    | [_] => 0
    | a :: b :: rest => max 0 (b - a) + risesSum (b :: rest)

  def formulaValue (t : List ℤ) : ℤ := t.headD 0 + risesSum t

  def lastVal (t : List ℤ) : ℤ := t.reverse.headD 0

  def minOpsPromised (target : Slice Std.I64) : Prop :=
    ∃ k : ℕ, IsMinOps target.val.length (vals target) k ∧ k ≤ 2 ^ 31 - 1

  /-- For every target satisfying the preconditions, whenever min_number_operations target returns Result.ok r, r is the least nonnegative integer k for which there exists a sequence of k operations, each operation choosing indices 0 <= L <= R < n and adding 1 to every position i with L <= i <= R, such that applying the sequence to the all-zero array of length n produces target.
    Preconditions: Let n = len(target). The slice target satisfies 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= target[i] <= 100000. The promised minimum number of operations for target is at most 2^31 - 1. -/
  theorem spec_1 (target : Slice Std.I64)
      (hlen_pos : 1 ≤ target.val.length) (hlen_le : target.val.length ≤ 100000)
      (hval : ∀ (i : ℕ) (_ : i < target.val.length),
        1 ≤ (target.val[i]).val ∧ (target.val[i]).val ≤ 100000)
      (hmin : minOpsPromised target) :
      ∀ r : Std.I64, min_number_operations target = ok r →
        ∃ k : ℕ, r.val = (k : ℤ) ∧ IsMinOps target.val.length (vals target) k := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (target : Slice Std.I64)
        (hlen_pos : 1 ≤ target.val.length) (hlen_le : target.val.length ≤ 100000)
        (hval : ∀ (i : ℕ) (_ : i < target.val.length),
          1 ≤ (target.val[i]).val ∧ (target.val[i]).val ≤ 100000)
        (hmin : minOpsPromised target), ∀ r : Std.I64, min_number_operations target = ok r →
          ∃ k : ℕ, r.val = (k : ℤ) ∧ IsMinOps target.val.length (vals target) k) := by
    sorry

  /-- For every target satisfying the preconditions, min_number_operations target returns Result.ok r for some integer r; it does not fail (no overflow, out-of-bounds access, or panic).
    Preconditions: Let n = len(target). The slice target satisfies 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= target[i] <= 100000. The promised minimum number of operations for target is at most 2^31 - 1. -/
  theorem spec_2 (target : Slice Std.I64)
      (hlen_pos : 1 ≤ target.val.length) (hlen_le : target.val.length ≤ 100000)
      (hval : ∀ (i : ℕ) (_ : i < target.val.length),
        1 ≤ (target.val[i]).val ∧ (target.val[i]).val ≤ 100000)
      (hmin : minOpsPromised target) :
      ∃ r : Std.I64, min_number_operations target = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (target : Slice Std.I64)
        (hlen_pos : 1 ≤ target.val.length) (hlen_le : target.val.length ≤ 100000)
        (hval : ∀ (i : ℕ) (_ : i < target.val.length),
          1 ≤ (target.val[i]).val ∧ (target.val[i]).val ≤ 100000)
        (hmin : minOpsPromised target), ∃ r : Std.I64, min_number_operations target = ok r) := by
    sorry

  /-- Whenever min_number_operations target returns Result.ok r, r >= max_{0 <= i < n} target[i].
    Preconditions: Let n = len(target). The slice target satisfies 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= target[i] <= 100000. The promised minimum number of operations for target is at most 2^31 - 1. -/
  theorem spec_3 (target : Slice Std.I64)
      (hlen_pos : 1 ≤ target.val.length) (hlen_le : target.val.length ≤ 100000)
      (hval : ∀ (i : ℕ) (_ : i < target.val.length),
        1 ≤ (target.val[i]).val ∧ (target.val[i]).val ≤ 100000)
      (hmin : minOpsPromised target) :
      ∀ r : Std.I64, min_number_operations target = ok r →
        maxVal (vals target) ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (target : Slice Std.I64)
        (hlen_pos : 1 ≤ target.val.length) (hlen_le : target.val.length ≤ 100000)
        (hval : ∀ (i : ℕ) (_ : i < target.val.length),
          1 ≤ (target.val[i]).val ∧ (target.val[i]).val ≤ 100000)
        (hmin : minOpsPromised target), ∀ r : Std.I64, min_number_operations target = ok r →
          maxVal (vals target) ≤ r.val) := by
    sorry

  /-- Whenever min_number_operations target returns Result.ok r, r <= sum_{i=0}^{n-1} target[i].
    Preconditions: Let n = len(target). The slice target satisfies 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= target[i] <= 100000. The promised minimum number of operations for target is at most 2^31 - 1. -/
  theorem spec_4 (target : Slice Std.I64)
      (hlen_pos : 1 ≤ target.val.length) (hlen_le : target.val.length ≤ 100000)
      (hval : ∀ (i : ℕ) (_ : i < target.val.length),
        1 ≤ (target.val[i]).val ∧ (target.val[i]).val ≤ 100000)
      (hmin : minOpsPromised target) :
      ∀ r : Std.I64, min_number_operations target = ok r →
        r.val ≤ (vals target).sum := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (target : Slice Std.I64)
        (hlen_pos : 1 ≤ target.val.length) (hlen_le : target.val.length ≤ 100000)
        (hval : ∀ (i : ℕ) (_ : i < target.val.length),
          1 ≤ (target.val[i]).val ∧ (target.val[i]).val ≤ 100000)
        (hmin : minOpsPromised target), ∀ r : Std.I64, min_number_operations target = ok r →
          r.val ≤ (vals target).sum) := by
    sorry

  /-- Let rev be the slice of length n with rev[i] = target[n-1-i] for every i with 0 <= i < n. If min_number_operations target returns Result.ok r and min_number_operations rev returns Result.ok r_rev, then r = r_rev.
    Preconditions: Let n = len(target). The slice target satisfies 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= target[i] <= 100000. The promised minimum number of operations for target is at most 2^31 - 1. -/
  theorem spec_5 (target rev : Slice Std.I64)
      (hlen_pos : 1 ≤ target.val.length) (hlen_le : target.val.length ≤ 100000)
      (hval : ∀ (i : ℕ) (_ : i < target.val.length),
        1 ≤ (target.val[i]).val ∧ (target.val[i]).val ≤ 100000)
      (hrev : rev.val = target.val.reverse) (hmin : minOpsPromised target) :
      ∀ r r_rev : Std.I64, min_number_operations target = ok r →
        min_number_operations rev = ok r_rev → r = r_rev := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (target rev : Slice Std.I64)
        (hlen_pos : 1 ≤ target.val.length) (hlen_le : target.val.length ≤ 100000)
        (hval : ∀ (i : ℕ) (_ : i < target.val.length),
          1 ≤ (target.val[i]).val ∧ (target.val[i]).val ≤ 100000)
        (hrev : rev.val = target.val.reverse) (hmin : minOpsPromised target), ∀ r r_rev : Std.I64, min_number_operations target = ok r →
          min_number_operations rev = ok r_rev → r = r_rev) := by
    sorry

  /-- If min_number_operations target returns Result.ok r and min_number_operations target' returns Result.ok r', then r' = r + c.
    Preconditions: Let n = len(target). The slice target satisfies 1 <= n <= 100000 and 1 <= target[i] <= 100000 for every i with 0 <= i < n. Let c be an integer with c >= 0. Define target'[i] = target[i] + c for 0 <= i < n. Assume target' also satisfies 1 <= target'[i] <= 100000 for every i and that its promised minimum number of operations is at most 2^31 - 1. -/
  theorem spec_6 (target target' : Slice Std.I64) (c : ℤ)
      (hlen_pos : 1 ≤ target.val.length) (hlen_le : target.val.length ≤ 100000)
      (hval : ∀ (i : ℕ) (_ : i < target.val.length),
        1 ≤ (target.val[i]).val ∧ (target.val[i]).val ≤ 100000)
      (hc : 0 ≤ c) (hT : vals target' = (vals target).map fun v => v + c)
      (hval' : ∀ (i : ℕ) (_ : i < target'.val.length),
        1 ≤ (target'.val[i]).val ∧ (target'.val[i]).val ≤ 100000)
      (hmin' : minOpsPromised target') (hmin : minOpsPromised target) :
      ∀ r r' : Std.I64, min_number_operations target = ok r →
        min_number_operations target' = ok r' → r'.val = r.val + c := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (target target' : Slice Std.I64) (c : ℤ)
        (hlen_pos : 1 ≤ target.val.length) (hlen_le : target.val.length ≤ 100000)
        (hval : ∀ (i : ℕ) (_ : i < target.val.length),
          1 ≤ (target.val[i]).val ∧ (target.val[i]).val ≤ 100000)
        (hc : 0 ≤ c) (hT : vals target' = (vals target).map fun v => v + c)
        (hval' : ∀ (i : ℕ) (_ : i < target'.val.length),
          1 ≤ (target'.val[i]).val ∧ (target'.val[i]).val ≤ 100000)
        (hmin' : minOpsPromised target') (hmin : minOpsPromised target), ∀ r r' : Std.I64, min_number_operations target = ok r →
          min_number_operations target' = ok r' → r'.val = r.val + c) := by
    sorry

  /-- If min_number_operations target returns Result.ok r and min_number_operations target' returns Result.ok r', then r' = r + max(0, x - target[n-1]).
    Preconditions: Let n = len(target). The slice target satisfies 1 <= n <= 100000 and 1 <= target[i] <= 100000 for every i with 0 <= i < n. Let x be an integer with 1 <= x <= 100000. Define target' of length n+1 by target'[i] = target[i] for 0 <= i < n and target'[n] = x. Assume n+1 <= 100000 and the promised minimum number of operations for target' is at most 2^31 - 1. -/
  theorem spec_7 (target target' : Slice Std.I64) (x : Std.I64)
      (hlen_pos : 1 ≤ target.val.length) (hlen_le : target.val.length ≤ 100000)
      (hval : ∀ (i : ℕ) (_ : i < target.val.length),
        1 ≤ (target.val[i]).val ∧ (target.val[i]).val ≤ 100000)
      (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 100000) (hT : target'.val = target.val ++ [x])
      (hlen : target.val.length + 1 ≤ 100000) (hmin' : minOpsPromised target')
      (hmin : minOpsPromised target) :
      ∀ r r' : Std.I64, min_number_operations target = ok r →
        min_number_operations target' = ok r' →
          r'.val = r.val + max 0 (x.val - lastVal (vals target)) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (target target' : Slice Std.I64) (x : Std.I64)
        (hlen_pos : 1 ≤ target.val.length) (hlen_le : target.val.length ≤ 100000)
        (hval : ∀ (i : ℕ) (_ : i < target.val.length),
          1 ≤ (target.val[i]).val ∧ (target.val[i]).val ≤ 100000)
        (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 100000) (hT : target'.val = target.val ++ [x])
        (hlen : target.val.length + 1 ≤ 100000) (hmin' : minOpsPromised target')
        (hmin : minOpsPromised target), ∀ r r' : Std.I64, min_number_operations target = ok r →
          min_number_operations target' = ok r' →
            r'.val = r.val + max 0 (x.val - lastVal (vals target))) := by
    sorry

  /-- Whenever min_number_operations target returns Result.ok r, there exists a sequence of exactly r subarray-increment operations (each choosing 0 <= L <= R < n and adding 1 to positions L through R) that transforms the all-zero array of length n into target.
    Preconditions: Let n = len(target). The slice target satisfies 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= target[i] <= 100000. The promised minimum number of operations for target is at most 2^31 - 1. -/
  theorem spec_8 (target : Slice Std.I64)
      (hlen_pos : 1 ≤ target.val.length) (hlen_le : target.val.length ≤ 100000)
      (hval : ∀ (i : ℕ) (_ : i < target.val.length),
        1 ≤ (target.val[i]).val ∧ (target.val[i]).val ≤ 100000)
      (hmin : minOpsPromised target) :
      ∀ r : Std.I64, min_number_operations target = ok r →
        ∃ k : ℕ, r.val = (k : ℤ) ∧ reaches target.val.length k (vals target) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (target : Slice Std.I64)
        (hlen_pos : 1 ≤ target.val.length) (hlen_le : target.val.length ≤ 100000)
        (hval : ∀ (i : ℕ) (_ : i < target.val.length),
          1 ≤ (target.val[i]).val ∧ (target.val[i]).val ≤ 100000)
        (hmin : minOpsPromised target), ∀ r : Std.I64, min_number_operations target = ok r →
          ∃ k : ℕ, r.val = (k : ℤ) ∧ reaches target.val.length k (vals target)) := by
    sorry

  /-- Whenever min_number_operations target returns Result.ok r, for every integer k with 0 <= k < r, there does not exist a sequence of k subarray-increment operations (each choosing 0 <= L <= R < n and adding 1 to positions L through R) that transforms the all-zero array of length n into target.
    Preconditions: Let n = len(target). The slice target satisfies 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= target[i] <= 100000. The promised minimum number of operations for target is at most 2^31 - 1. -/
  theorem spec_9 (target : Slice Std.I64)
      (hlen_pos : 1 ≤ target.val.length) (hlen_le : target.val.length ≤ 100000)
      (hval : ∀ (i : ℕ) (_ : i < target.val.length),
        1 ≤ (target.val[i]).val ∧ (target.val[i]).val ≤ 100000)
      (hmin : minOpsPromised target) :
      ∀ r : Std.I64, min_number_operations target = ok r →
        ∀ k : ℕ, (k : ℤ) < r.val → ¬ reaches target.val.length k (vals target) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (target : Slice Std.I64)
        (hlen_pos : 1 ≤ target.val.length) (hlen_le : target.val.length ≤ 100000)
        (hval : ∀ (i : ℕ) (_ : i < target.val.length),
          1 ≤ (target.val[i]).val ∧ (target.val[i]).val ≤ 100000)
        (hmin : minOpsPromised target), ∀ r : Std.I64, min_number_operations target = ok r →
          ∀ k : ℕ, (k : ℤ) < r.val → ¬ reaches target.val.length k (vals target)) := by
    sorry

  /-- Whenever min_number_operations target returns Result.ok r, r = target[0] + sum_{i=1}^{n-1} max(0, target[i] - target[i-1]).
    Preconditions: Let n = len(target). The slice target satisfies 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= target[i] <= 100000. The promised minimum number of operations for target is at most 2^31 - 1. -/
  theorem spec_10 (target : Slice Std.I64)
      (hlen_pos : 1 ≤ target.val.length) (hlen_le : target.val.length ≤ 100000)
      (hval : ∀ (i : ℕ) (_ : i < target.val.length),
        1 ≤ (target.val[i]).val ∧ (target.val[i]).val ≤ 100000)
      (hmin : minOpsPromised target) :
      ∀ r : Std.I64, min_number_operations target = ok r →
        r.val = formulaValue (vals target) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (target : Slice Std.I64)
        (hlen_pos : 1 ≤ target.val.length) (hlen_le : target.val.length ≤ 100000)
        (hval : ∀ (i : ℕ) (_ : i < target.val.length),
          1 ≤ (target.val[i]).val ∧ (target.val[i]).val ≤ 100000)
        (hmin : minOpsPromised target), ∀ r : Std.I64, min_number_operations target = ok r →
          r.val = formulaValue (vals target)) := by
    sorry

  end AegisSpec.MinNumberOperations
