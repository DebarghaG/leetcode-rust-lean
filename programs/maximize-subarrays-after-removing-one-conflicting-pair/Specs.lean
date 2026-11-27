import Aegis.MaxSubarrays.Code.Funs

/-!
# Specifications of `Aegis.MaxSubarrays.max_subarrays`

LeetCode problem `maximize-subarrays-after-removing-one-conflicting-pair`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaxSubarrays

  open Aegis.MaxSubarrays (max_subarrays)

  def pairEnds (v : alloc.vec.Vec Std.I64) : List ℤ := v.val.map (fun x => x.val)

  def pairAt? (P : Slice (alloc.vec.Vec Std.I64)) (i : ℕ) : Option (ℤ × ℤ) :=
    match (P.val[i]?).map pairEnds with
    | some [a, b] => some (a, b)
    | _ => none

  def pairAt (P : Slice (alloc.vec.Vec Std.I64)) (i : ℕ) : ℤ × ℤ :=
    (pairAt? P i).getD (0, 0)

  def containsBoth (L R a b : ℤ) : Bool :=
    decide (L ≤ a) && decide (a ≤ R) && decide (L ≤ b) && decide (b ≤ R)

  def intervalsUpTo (n : ℕ) : List (ℕ × ℕ) :=
    (List.range n).flatMap fun L => (List.range (n - L)).map fun R => (L + 1, L + 1 + R)

  def avoidsExcept (P : Slice (alloc.vec.Vec Std.I64)) (j L R : ℕ) : Bool :=
    (List.range P.val.length).all fun i =>
      i == j || !containsBoth (L : ℤ) (R : ℤ) (pairAt P i).1 (pairAt P i).2

  def countAvoidingExcept (n : ℕ) (P : Slice (alloc.vec.Vec Std.I64)) (j : ℕ) : ℤ :=
    Int.ofNat ((intervalsUpTo n).filter fun q => avoidsExcept P j q.1 q.2).length

  def countAvoidingAll (n : ℕ) (P : Slice (alloc.vec.Vec Std.I64)) : ℤ :=
    countAvoidingExcept n P P.val.length

  def maxCountAvoiding (n : ℕ) (P : Slice (alloc.vec.Vec Std.I64)) : ℤ :=
    ((List.range P.val.length).map fun j => countAvoidingExcept n P j).foldr max 0

  /-- The function returns a result r and r = max { C(j) | 0 <= j < len(conflictingPairs) }, where for each j, C(j) is the number of integer intervals [L,R] with 1 <= L <= R <= n such that for every i with 0 <= i < len(conflictingPairs) and i != j, it is not the case that both L <= conflictingPairs[i][0] <= R and L <= conflictingPairs[i][1] <= R. Equivalently, C(j) is the number of non-empty contiguous subarrays of nums=[1,2,...,n] that contain both endpoints of no remaining conflicting pair after deleting the single occurrence at index j.
    Preconditions: n is an integer with 2 <= n <= 100000. conflictingPairs is a slice of vectors of I64. len(conflictingPairs) is between 1 and 2*n inclusive. For every i with 0 <= i < len(conflictingPairs), conflictingPairs[i] has length 2, and its two entries are integers a_i,b_i with 1 <= a_i <= n, 1 <= b_i <= n, and a_i != b_i. The pairs are not assumed distinct and no ordering of them is assumed. -/
  theorem spec_1 (n : Std.I64) (P : Slice (alloc.vec.Vec Std.I64))
      (hn_low : 2 ≤ n.val) (hn_high : n.val ≤ 100000)
      (hlen_low : 1 ≤ (P.val.length : ℤ)) (hlen_high : (P.val.length : ℤ) ≤ 2 * n.val)
      (hpairs : ∀ i, i < P.val.length →
        ∃ a b : ℤ, pairAt? P i = some (a, b) ∧
          1 ≤ a ∧ a ≤ n.val ∧ 1 ≤ b ∧ b ≤ n.val ∧ a ≠ b) :
      ∃ r, max_subarrays n P = ok r ∧ r.val = maxCountAvoiding n.val.toNat P := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : Std.I64) (P : Slice (alloc.vec.Vec Std.I64))
        (hn_low : 2 ≤ n.val) (hn_high : n.val ≤ 100000)
        (hlen_low : 1 ≤ (P.val.length : ℤ)) (hlen_high : (P.val.length : ℤ) ≤ 2 * n.val)
        (hpairs : ∀ i, i < P.val.length →
          ∃ a b : ℤ, pairAt? P i = some (a, b) ∧
            1 ≤ a ∧ a ≤ n.val ∧ 1 ≤ b ∧ b ≤ n.val ∧ a ≠ b), ∃ r, max_subarrays n P = ok r ∧ r.val = maxCountAvoiding n.val.toNat P) := by
    sorry

  /-- The function returns a result r; it does not fail, overflow, access an out-of-bounds index, or panic on any input satisfying the preconditions.
    Preconditions: n is an integer with 2 <= n <= 100000. conflictingPairs is a slice of vectors of I64. len(conflictingPairs) is between 1 and 2*n inclusive. For every i with 0 <= i < len(conflictingPairs), conflictingPairs[i] has length 2, and its two entries are integers a_i,b_i with 1 <= a_i <= n, 1 <= b_i <= n, and a_i != b_i. -/
  theorem spec_2 (n : Std.I64) (P : Slice (alloc.vec.Vec Std.I64))
      (hn_low : 2 ≤ n.val) (hn_high : n.val ≤ 100000)
      (hlen_low : 1 ≤ (P.val.length : ℤ)) (hlen_high : (P.val.length : ℤ) ≤ 2 * n.val)
      (hpairs : ∀ i, i < P.val.length →
        ∃ a b : ℤ, pairAt? P i = some (a, b) ∧
          1 ≤ a ∧ a ≤ n.val ∧ 1 ≤ b ∧ b ≤ n.val ∧ a ≠ b) :
      ∃ r, max_subarrays n P = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : Std.I64) (P : Slice (alloc.vec.Vec Std.I64))
        (hn_low : 2 ≤ n.val) (hn_high : n.val ≤ 100000)
        (hlen_low : 1 ≤ (P.val.length : ℤ)) (hlen_high : (P.val.length : ℤ) ≤ 2 * n.val)
        (hpairs : ∀ i, i < P.val.length →
          ∃ a b : ℤ, pairAt? P i = some (a, b) ∧
            1 ≤ a ∧ a ≤ n.val ∧ 1 ≤ b ∧ b ≤ n.val ∧ a ≠ b), ∃ r, max_subarrays n P = ok r) := by
    sorry

  /-- The function returns a result r and r >= n.
    Preconditions: n is an integer with 2 <= n <= 100000. conflictingPairs is a slice of vectors of I64. len(conflictingPairs) is between 1 and 2*n inclusive. For every i with 0 <= i < len(conflictingPairs), conflictingPairs[i] has length 2, and its two entries are integers a_i,b_i with 1 <= a_i <= n, 1 <= b_i <= n, and a_i != b_i. -/
  theorem spec_3 (n : Std.I64) (P : Slice (alloc.vec.Vec Std.I64))
      (hn_low : 2 ≤ n.val) (hn_high : n.val ≤ 100000)
      (hlen_low : 1 ≤ (P.val.length : ℤ)) (hlen_high : (P.val.length : ℤ) ≤ 2 * n.val)
      (hpairs : ∀ i, i < P.val.length →
        ∃ a b : ℤ, pairAt? P i = some (a, b) ∧
          1 ≤ a ∧ a ≤ n.val ∧ 1 ≤ b ∧ b ≤ n.val ∧ a ≠ b) :
      ∃ r, max_subarrays n P = ok r ∧ n.val ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : Std.I64) (P : Slice (alloc.vec.Vec Std.I64))
        (hn_low : 2 ≤ n.val) (hn_high : n.val ≤ 100000)
        (hlen_low : 1 ≤ (P.val.length : ℤ)) (hlen_high : (P.val.length : ℤ) ≤ 2 * n.val)
        (hpairs : ∀ i, i < P.val.length →
          ∃ a b : ℤ, pairAt? P i = some (a, b) ∧
            1 ≤ a ∧ a ≤ n.val ∧ 1 ≤ b ∧ b ≤ n.val ∧ a ≠ b), ∃ r, max_subarrays n P = ok r ∧ n.val ≤ r.val) := by
    sorry

  /-- The function returns a result r and r <= n*(n+1)/2.
    Preconditions: n is an integer with 2 <= n <= 100000. conflictingPairs is a slice of vectors of I64. len(conflictingPairs) is between 1 and 2*n inclusive. For every i with 0 <= i < len(conflictingPairs), conflictingPairs[i] has length 2, and its two entries are integers a_i,b_i with 1 <= a_i <= n, 1 <= b_i <= n, and a_i != b_i. -/
  theorem spec_4 (n : Std.I64) (P : Slice (alloc.vec.Vec Std.I64))
      (hn_low : 2 ≤ n.val) (hn_high : n.val ≤ 100000)
      (hlen_low : 1 ≤ (P.val.length : ℤ)) (hlen_high : (P.val.length : ℤ) ≤ 2 * n.val)
      (hpairs : ∀ i, i < P.val.length →
        ∃ a b : ℤ, pairAt? P i = some (a, b) ∧
          1 ≤ a ∧ a ≤ n.val ∧ 1 ≤ b ∧ b ≤ n.val ∧ a ≠ b) :
      ∃ r, max_subarrays n P = ok r ∧ r.val ≤ n.val * (n.val + 1) / 2 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : Std.I64) (P : Slice (alloc.vec.Vec Std.I64))
        (hn_low : 2 ≤ n.val) (hn_high : n.val ≤ 100000)
        (hlen_low : 1 ≤ (P.val.length : ℤ)) (hlen_high : (P.val.length : ℤ) ≤ 2 * n.val)
        (hpairs : ∀ i, i < P.val.length →
          ∃ a b : ℤ, pairAt? P i = some (a, b) ∧
            1 ≤ a ∧ a ≤ n.val ∧ 1 ≤ b ∧ b ≤ n.val ∧ a ≠ b), ∃ r, max_subarrays n P = ok r ∧ r.val ≤ n.val * (n.val + 1) / 2) := by
    sorry

  /-- The function returns a result r and r = n*(n+1)/2.
    Preconditions: n is an integer with 2 <= n <= 100000. conflictingPairs is a slice of vectors of I64. len(conflictingPairs) is between 1 and 2*n inclusive, and additionally len(conflictingPairs) = 1. For every i with 0 <= i < len(conflictingPairs), conflictingPairs[i] has length 2, and its two entries are integers a_i,b_i with 1 <= a_i <= n, 1 <= b_i <= n, and a_i != b_i. -/
  theorem spec_5 (n : Std.I64) (P : Slice (alloc.vec.Vec Std.I64))
      (hn_low : 2 ≤ n.val) (hn_high : n.val ≤ 100000)
      (hlen_low : 1 ≤ (P.val.length : ℤ)) (hlen_high : (P.val.length : ℤ) ≤ 2 * n.val)
      (hlen_one : (P.val.length : ℤ) = 1)
      (hpairs : ∀ i, i < P.val.length →
        ∃ a b : ℤ, pairAt? P i = some (a, b) ∧
          1 ≤ a ∧ a ≤ n.val ∧ 1 ≤ b ∧ b ≤ n.val ∧ a ≠ b) :
      ∃ r, max_subarrays n P = ok r ∧ r.val = n.val * (n.val + 1) / 2 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : Std.I64) (P : Slice (alloc.vec.Vec Std.I64))
        (hn_low : 2 ≤ n.val) (hn_high : n.val ≤ 100000)
        (hlen_low : 1 ≤ (P.val.length : ℤ)) (hlen_high : (P.val.length : ℤ) ≤ 2 * n.val)
        (hlen_one : (P.val.length : ℤ) = 1)
        (hpairs : ∀ i, i < P.val.length →
          ∃ a b : ℤ, pairAt? P i = some (a, b) ∧
            1 ≤ a ∧ a ≤ n.val ∧ 1 ≤ b ∧ b ≤ n.val ∧ a ≠ b), ∃ r, max_subarrays n P = ok r ∧ r.val = n.val * (n.val + 1) / 2) := by
    sorry

  /-- The function returns a result r and r <= n*(n+1)/2 - 1.
    Preconditions: n is an integer with 2 <= n <= 100000. conflictingPairs is a slice of vectors of I64. len(conflictingPairs) is between 1 and 2*n inclusive, and additionally len(conflictingPairs) >= 2. For every i with 0 <= i < len(conflictingPairs), conflictingPairs[i] has length 2, and its two entries are integers a_i,b_i with 1 <= a_i <= n, 1 <= b_i <= n, and a_i != b_i. -/
  theorem spec_6 (n : Std.I64) (P : Slice (alloc.vec.Vec Std.I64))
      (hn_low : 2 ≤ n.val) (hn_high : n.val ≤ 100000)
      (hlen_low : 1 ≤ (P.val.length : ℤ)) (hlen_high : (P.val.length : ℤ) ≤ 2 * n.val)
      (hlen_two : 2 ≤ (P.val.length : ℤ))
      (hpairs : ∀ i, i < P.val.length →
        ∃ a b : ℤ, pairAt? P i = some (a, b) ∧
          1 ≤ a ∧ a ≤ n.val ∧ 1 ≤ b ∧ b ≤ n.val ∧ a ≠ b) :
      ∃ r, max_subarrays n P = ok r ∧ r.val ≤ n.val * (n.val + 1) / 2 - 1 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n : Std.I64) (P : Slice (alloc.vec.Vec Std.I64))
        (hn_low : 2 ≤ n.val) (hn_high : n.val ≤ 100000)
        (hlen_low : 1 ≤ (P.val.length : ℤ)) (hlen_high : (P.val.length : ℤ) ≤ 2 * n.val)
        (hlen_two : 2 ≤ (P.val.length : ℤ))
        (hpairs : ∀ i, i < P.val.length →
          ∃ a b : ℤ, pairAt? P i = some (a, b) ∧
            1 ≤ a ∧ a ≤ n.val ∧ 1 ≤ b ∧ b ≤ n.val ∧ a ≠ b), ∃ r, max_subarrays n P = ok r ∧ r.val ≤ n.val * (n.val + 1) / 2 - 1) := by
    sorry

  /-- For each j with 0 <= j < len(conflictingPairs), let C(j) be the number of integer intervals [L,R] with 1 <= L <= R <= n such that for every i with 0 <= i < len(conflictingPairs) and i != j, it is not the case that both L <= conflictingPairs[i][0] <= R and L <= conflictingPairs[i][1] <= R. The function returns a result r and for every j with 0 <= j < len(conflictingPairs), r >= C(j).
    Preconditions: n is an integer with 2 <= n <= 100000. conflictingPairs is a slice of vectors of I64. len(conflictingPairs) is between 1 and 2*n inclusive. For every i with 0 <= i < len(conflictingPairs), conflictingPairs[i] has length 2, and its two entries are integers a_i,b_i with 1 <= a_i <= n, 1 <= b_i <= n, and a_i != b_i. -/
  theorem spec_7 (n : Std.I64) (P : Slice (alloc.vec.Vec Std.I64))
      (hn_low : 2 ≤ n.val) (hn_high : n.val ≤ 100000)
      (hlen_low : 1 ≤ (P.val.length : ℤ)) (hlen_high : (P.val.length : ℤ) ≤ 2 * n.val)
      (hpairs : ∀ i, i < P.val.length →
        ∃ a b : ℤ, pairAt? P i = some (a, b) ∧
          1 ≤ a ∧ a ≤ n.val ∧ 1 ≤ b ∧ b ≤ n.val ∧ a ≠ b) :
      ∃ r, max_subarrays n P = ok r ∧
        ∀ j, j < P.val.length → countAvoidingExcept n.val.toNat P j ≤ r.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n : Std.I64) (P : Slice (alloc.vec.Vec Std.I64))
        (hn_low : 2 ≤ n.val) (hn_high : n.val ≤ 100000)
        (hlen_low : 1 ≤ (P.val.length : ℤ)) (hlen_high : (P.val.length : ℤ) ≤ 2 * n.val)
        (hpairs : ∀ i, i < P.val.length →
          ∃ a b : ℤ, pairAt? P i = some (a, b) ∧
            1 ≤ a ∧ a ≤ n.val ∧ 1 ≤ b ∧ b ≤ n.val ∧ a ≠ b), ∃ r, max_subarrays n P = ok r ∧
          ∀ j, j < P.val.length → countAvoidingExcept n.val.toNat P j ≤ r.val) := by
    sorry

  /-- For each j with 0 <= j < len(conflictingPairs), let C(j) be the number of integer intervals [L,R] with 1 <= L <= R <= n such that for every i with 0 <= i < len(conflictingPairs) and i != j, it is not the case that both L <= conflictingPairs[i][0] <= R and L <= conflictingPairs[i][1] <= R. The function returns a result r and there exists j with 0 <= j < len(conflictingPairs) such that r = C(j).
    Preconditions: n is an integer with 2 <= n <= 100000. conflictingPairs is a slice of vectors of I64. len(conflictingPairs) is between 1 and 2*n inclusive. For every i with 0 <= i < len(conflictingPairs), conflictingPairs[i] has length 2, and its two entries are integers a_i,b_i with 1 <= a_i <= n, 1 <= b_i <= n, and a_i != b_i. -/
  theorem spec_8 (n : Std.I64) (P : Slice (alloc.vec.Vec Std.I64))
      (hn_low : 2 ≤ n.val) (hn_high : n.val ≤ 100000)
      (hlen_low : 1 ≤ (P.val.length : ℤ)) (hlen_high : (P.val.length : ℤ) ≤ 2 * n.val)
      (hpairs : ∀ i, i < P.val.length →
        ∃ a b : ℤ, pairAt? P i = some (a, b) ∧
          1 ≤ a ∧ a ≤ n.val ∧ 1 ≤ b ∧ b ≤ n.val ∧ a ≠ b) :
      ∃ r, max_subarrays n P = ok r ∧
        ∃ j, j < P.val.length ∧ r.val = countAvoidingExcept n.val.toNat P j := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n : Std.I64) (P : Slice (alloc.vec.Vec Std.I64))
        (hn_low : 2 ≤ n.val) (hn_high : n.val ≤ 100000)
        (hlen_low : 1 ≤ (P.val.length : ℤ)) (hlen_high : (P.val.length : ℤ) ≤ 2 * n.val)
        (hpairs : ∀ i, i < P.val.length →
          ∃ a b : ℤ, pairAt? P i = some (a, b) ∧
            1 ≤ a ∧ a ≤ n.val ∧ 1 ≤ b ∧ b ≤ n.val ∧ a ≠ b), ∃ r, max_subarrays n P = ok r ∧
          ∃ j, j < P.val.length ∧ r.val = countAvoidingExcept n.val.toNat P j) := by
    sorry

  /-- For every permutation p of the index set {0,...,len(conflictingPairs)-1}, let P' be the list of length len(conflictingPairs) whose i-th element is conflictingPairs[p(i)]. Whenever the function on (n, conflictingPairs) returns r and the function on (n, P') returns r', we have r = r'.
    Preconditions: n is an integer with 2 <= n <= 100000. conflictingPairs is a slice of vectors of I64. len(conflictingPairs) is between 1 and 2*n inclusive. For every i with 0 <= i < len(conflictingPairs), conflictingPairs[i] has length 2, and its two entries are integers a_i,b_i with 1 <= a_i <= n, 1 <= b_i <= n, and a_i != b_i. -/
  theorem spec_9 (n : Std.I64) (P : Slice (alloc.vec.Vec Std.I64))
      (hn_low : 2 ≤ n.val) (hn_high : n.val ≤ 100000)
      (hlen_low : 1 ≤ (P.val.length : ℤ)) (hlen_high : (P.val.length : ℤ) ≤ 2 * n.val)
      (hpairs : ∀ i, i < P.val.length →
        ∃ a b : ℤ, pairAt? P i = some (a, b) ∧
          1 ≤ a ∧ a ≤ n.val ∧ 1 ≤ b ∧ b ≤ n.val ∧ a ≠ b)
      (p : Equiv.Perm (Fin P.val.length))
      (Q : Slice (alloc.vec.Vec Std.I64)) (hQ_len : Q.val.length = P.val.length)
      (hQ : ∀ i : Fin P.val.length,
        Q.val[i.val]? = P.val[(p i).val]?)
      (r r' : Std.I64) (hr : max_subarrays n P = ok r) (hr' : max_subarrays n Q = ok r') :
      r = r' := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n : Std.I64) (P : Slice (alloc.vec.Vec Std.I64))
        (hn_low : 2 ≤ n.val) (hn_high : n.val ≤ 100000)
        (hlen_low : 1 ≤ (P.val.length : ℤ)) (hlen_high : (P.val.length : ℤ) ≤ 2 * n.val)
        (hpairs : ∀ i, i < P.val.length →
          ∃ a b : ℤ, pairAt? P i = some (a, b) ∧
            1 ≤ a ∧ a ≤ n.val ∧ 1 ≤ b ∧ b ≤ n.val ∧ a ≠ b)
        (p : Equiv.Perm (Fin P.val.length))
        (Q : Slice (alloc.vec.Vec Std.I64)) (hQ_len : Q.val.length = P.val.length)
        (hQ : ∀ i : Fin P.val.length,
          Q.val[i.val]? = P.val[(p i).val]?)
        (r r' : Std.I64) (hr : max_subarrays n P = ok r) (hr' : max_subarrays n Q = ok r'), r = r') := by
    sorry

  /-- Let P' be the list with the same length as conflictingPairs such that for every i with 0 <= i < len(conflictingPairs), P'[i] = [conflictingPairs[i][1], conflictingPairs[i][0]]. Whenever the function on (n, conflictingPairs) returns r and the function on (n, P') returns r', we have r = r'.
    Preconditions: n is an integer with 2 <= n <= 100000. conflictingPairs is a slice of vectors of I64. len(conflictingPairs) is between 1 and 2*n inclusive. For every i with 0 <= i < len(conflictingPairs), conflictingPairs[i] has length 2, and its two entries are integers a_i,b_i with 1 <= a_i <= n, 1 <= b_i <= n, and a_i != b_i. -/
  theorem spec_10 (n : Std.I64) (P : Slice (alloc.vec.Vec Std.I64))
      (hn_low : 2 ≤ n.val) (hn_high : n.val ≤ 100000)
      (hlen_low : 1 ≤ (P.val.length : ℤ)) (hlen_high : (P.val.length : ℤ) ≤ 2 * n.val)
      (hpairs : ∀ i, i < P.val.length →
        ∃ a b : ℤ, pairAt? P i = some (a, b) ∧
          1 ≤ a ∧ a ≤ n.val ∧ 1 ≤ b ∧ b ≤ n.val ∧ a ≠ b)
      (Q : Slice (alloc.vec.Vec Std.I64)) (hQ_len : Q.val.length = P.val.length)
      (hQ : Q.val.map pairEnds = P.val.map fun v => (pairEnds v).reverse)
      (r r' : Std.I64) (hr : max_subarrays n P = ok r) (hr' : max_subarrays n Q = ok r') :
      r = r' := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n : Std.I64) (P : Slice (alloc.vec.Vec Std.I64))
        (hn_low : 2 ≤ n.val) (hn_high : n.val ≤ 100000)
        (hlen_low : 1 ≤ (P.val.length : ℤ)) (hlen_high : (P.val.length : ℤ) ≤ 2 * n.val)
        (hpairs : ∀ i, i < P.val.length →
          ∃ a b : ℤ, pairAt? P i = some (a, b) ∧
            1 ≤ a ∧ a ≤ n.val ∧ 1 ≤ b ∧ b ≤ n.val ∧ a ≠ b)
        (Q : Slice (alloc.vec.Vec Std.I64)) (hQ_len : Q.val.length = P.val.length)
        (hQ : Q.val.map pairEnds = P.val.map fun v => (pairEnds v).reverse)
        (r r' : Std.I64) (hr : max_subarrays n P = ok r) (hr' : max_subarrays n Q = ok r'), r = r') := by
    sorry

  /-- The function returns a result r and r = n*(n+1)/2 - a*(n-b+1).
    Preconditions: n is an integer with 2 <= n <= 100000. conflictingPairs is a slice of vectors of I64. len(conflictingPairs) is between 1 and 2*n inclusive, and additionally len(conflictingPairs) >= 2. For every i with 0 <= i < len(conflictingPairs), conflictingPairs[i] has length 2, and its two entries are integers in [1,n] and are distinct. There exist integers a,b with 1 <= a < b <= n such that for every i with 0 <= i < len(conflictingPairs), the unordered set {conflictingPairs[i][0], conflictingPairs[i][1]} equals {a,b}. -/
  theorem spec_11 (n : Std.I64) (P : Slice (alloc.vec.Vec Std.I64))
      (hn_low : 2 ≤ n.val) (hn_high : n.val ≤ 100000)
      (hlen_low : 1 ≤ (P.val.length : ℤ)) (hlen_high : (P.val.length : ℤ) ≤ 2 * n.val)
      (hlen_two : 2 ≤ (P.val.length : ℤ))
      (hpairs : ∀ i, i < P.val.length →
        ∃ a b : ℤ, pairAt? P i = some (a, b) ∧
          1 ≤ a ∧ a ≤ n.val ∧ 1 ≤ b ∧ b ≤ n.val ∧ a ≠ b)
      (a b : ℤ) (ha_low : 1 ≤ a) (hab : a < b) (hb_high : b ≤ n.val)
      (hall : ∀ i, i < P.val.length →
        ∃ x y : ℤ, pairAt? P i = some (x, y) ∧ ((x = a ∧ y = b) ∨ (x = b ∧ y = a))) :
      ∃ r, max_subarrays n P = ok r ∧
        r.val = n.val * (n.val + 1) / 2 - a * (n.val - b + 1) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (n : Std.I64) (P : Slice (alloc.vec.Vec Std.I64))
        (hn_low : 2 ≤ n.val) (hn_high : n.val ≤ 100000)
        (hlen_low : 1 ≤ (P.val.length : ℤ)) (hlen_high : (P.val.length : ℤ) ≤ 2 * n.val)
        (hlen_two : 2 ≤ (P.val.length : ℤ))
        (hpairs : ∀ i, i < P.val.length →
          ∃ a b : ℤ, pairAt? P i = some (a, b) ∧
            1 ≤ a ∧ a ≤ n.val ∧ 1 ≤ b ∧ b ≤ n.val ∧ a ≠ b)
        (a b : ℤ) (ha_low : 1 ≤ a) (hab : a < b) (hb_high : b ≤ n.val)
        (hall : ∀ i, i < P.val.length →
          ∃ x y : ℤ, pairAt? P i = some (x, y) ∧ ((x = a ∧ y = b) ∨ (x = b ∧ y = a))), ∃ r, max_subarrays n P = ok r ∧
          r.val = n.val * (n.val + 1) / 2 - a * (n.val - b + 1)) := by
    sorry

  /-- Whenever the function on (n, conflictingPairs) returns r and the function on (n, P') returns r', we have r' <= r.
    Preconditions: n is an integer with 2 <= n <= 100000. conflictingPairs is a slice of vectors of I64. len(conflictingPairs) is between 1 and 2*n inclusive, and additionally len(conflictingPairs) < 2*n. For every i with 0 <= i < len(conflictingPairs), conflictingPairs[i] has length 2, and its two entries are integers a_i,b_i with 1 <= a_i <= n, 1 <= b_i <= n, and a_i != b_i. Let a,b be integers with 1 <= a <= n, 1 <= b <= n, and a != b. Let P' be the slice obtained by appending the vector [a,b] to conflictingPairs. -/
  theorem spec_12 (n : Std.I64) (P : Slice (alloc.vec.Vec Std.I64))
      (hn_low : 2 ≤ n.val) (hn_high : n.val ≤ 100000)
      (hlen_low : 1 ≤ (P.val.length : ℤ)) (hlen_high : (P.val.length : ℤ) ≤ 2 * n.val)
      (hlen_lt : (P.val.length : ℤ) < 2 * n.val)
      (hpairs : ∀ i, i < P.val.length →
        ∃ a b : ℤ, pairAt? P i = some (a, b) ∧
          1 ≤ a ∧ a ≤ n.val ∧ 1 ≤ b ∧ b ≤ n.val ∧ a ≠ b)
      (v : alloc.vec.Vec Std.I64) (a b : ℤ) (hv : pairEnds v = [a, b])
      (ha_low : 1 ≤ a) (ha_high : a ≤ n.val) (hb_low : 1 ≤ b) (hb_high : b ≤ n.val)
      (hab : a ≠ b)
      (Q : Slice (alloc.vec.Vec Std.I64)) (hQ : Q.val = P.val ++ [v])
      (r r' : Std.I64) (hr : max_subarrays n P = ok r) (hr' : max_subarrays n Q = ok r') :
      r'.val ≤ r.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (n : Std.I64) (P : Slice (alloc.vec.Vec Std.I64))
        (hn_low : 2 ≤ n.val) (hn_high : n.val ≤ 100000)
        (hlen_low : 1 ≤ (P.val.length : ℤ)) (hlen_high : (P.val.length : ℤ) ≤ 2 * n.val)
        (hlen_lt : (P.val.length : ℤ) < 2 * n.val)
        (hpairs : ∀ i, i < P.val.length →
          ∃ a b : ℤ, pairAt? P i = some (a, b) ∧
            1 ≤ a ∧ a ≤ n.val ∧ 1 ≤ b ∧ b ≤ n.val ∧ a ≠ b)
        (v : alloc.vec.Vec Std.I64) (a b : ℤ) (hv : pairEnds v = [a, b])
        (ha_low : 1 ≤ a) (ha_high : a ≤ n.val) (hb_low : 1 ≤ b) (hb_high : b ≤ n.val)
        (hab : a ≠ b)
        (Q : Slice (alloc.vec.Vec Std.I64)) (hQ : Q.val = P.val ++ [v])
        (r r' : Std.I64) (hr : max_subarrays n P = ok r) (hr' : max_subarrays n Q = ok r'), r'.val ≤ r.val) := by
    sorry

  /-- Let D be the number of integer intervals [L,R] with 1 <= L <= R <= n such that for every i with 0 <= i < len(conflictingPairs), it is not the case that both L <= conflictingPairs[i][0] <= R and L <= conflictingPairs[i][1] <= R. The function returns a result r and r >= D.
    Preconditions: n is an integer with 2 <= n <= 100000. conflictingPairs is a slice of vectors of I64. len(conflictingPairs) is between 1 and 2*n inclusive. For every i with 0 <= i < len(conflictingPairs), conflictingPairs[i] has length 2, and its two entries are integers a_i,b_i with 1 <= a_i <= n, 1 <= b_i <= n, and a_i != b_i. -/
  theorem spec_13 (n : Std.I64) (P : Slice (alloc.vec.Vec Std.I64))
      (hn_low : 2 ≤ n.val) (hn_high : n.val ≤ 100000)
      (hlen_low : 1 ≤ (P.val.length : ℤ)) (hlen_high : (P.val.length : ℤ) ≤ 2 * n.val)
      (hpairs : ∀ i, i < P.val.length →
        ∃ a b : ℤ, pairAt? P i = some (a, b) ∧
          1 ≤ a ∧ a ≤ n.val ∧ 1 ≤ b ∧ b ≤ n.val ∧ a ≠ b) :
      ∃ r, max_subarrays n P = ok r ∧ countAvoidingAll n.val.toNat P ≤ r.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (n : Std.I64) (P : Slice (alloc.vec.Vec Std.I64))
        (hn_low : 2 ≤ n.val) (hn_high : n.val ≤ 100000)
        (hlen_low : 1 ≤ (P.val.length : ℤ)) (hlen_high : (P.val.length : ℤ) ≤ 2 * n.val)
        (hpairs : ∀ i, i < P.val.length →
          ∃ a b : ℤ, pairAt? P i = some (a, b) ∧
            1 ≤ a ∧ a ≤ n.val ∧ 1 ≤ b ∧ b ≤ n.val ∧ a ≠ b), ∃ r, max_subarrays n P = ok r ∧ countAvoidingAll n.val.toNat P ≤ r.val) := by
    sorry

  end AegisSpec.MaxSubarrays
