import Aegis.NumsSameConsecDiff.Code.Funs

/-!
# Specifications of `Aegis.NumsSameConsecDiff.nums_same_consec_diff`

LeetCode problem `numbers-with-same-consecutive-differences`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.NumsSameConsecDiff

def vals (r : alloc.vec.Vec Std.I64) : List ℤ := r.val.map (fun x => x.val)

def digit (n : ℕ) (x : ℤ) (i : ℕ) : ℤ := (x / (10 : ℤ) ^ (n - 1 - i)) % 10

def digits (n : ℕ) (x : ℤ) : List ℤ := (List.range n).map (fun i => digit n x i)

def ofDigits (ds : List ℤ) : ℤ := ds.foldl (fun acc d => acc * 10 + d) 0

def HasNDigits (n : ℕ) (x : ℤ) : Prop := (10 : ℤ) ^ (n - 1) ≤ x ∧ x ≤ (10 : ℤ) ^ n - 1

def ConsecDiff (n k : ℕ) (x : ℤ) : Prop :=
  ∀ i : ℕ, i + 1 < n → Int.natAbs (digit n x (i + 1) - digit n x i) = k

def IsValid (n k : ℕ) (x : ℤ) : Prop :=
  HasNDigits n x ∧ (∀ i : ℕ, i < n → 0 ≤ digit n x i ∧ digit n x i ≤ 9) ∧
    digit n x 0 ≠ 0 ∧ ConsecDiff n k x

noncomputable def validInts (n k : ℕ) : List ℤ :=
  letI := Classical.decPred (fun x : ℤ => IsValid n k x)
  ((List.range (10 ^ n)).map (fun i => (i : ℤ))).filter (fun x => IsValid n k x)

noncomputable def validCount (n k : ℕ) : ℕ := (validInts n k).length

def numOcc (l : List ℤ) (x : ℤ) : ℕ := (l.filter (fun y => y = x)).length

def repdigit (n : ℕ) (d : ℤ) : ℤ := ofDigits (List.replicate n d)

def repdigits (n : ℕ) : List ℤ := (List.range 9).map (fun i => repdigit n ((i : ℤ) + 1))

def ninesZeros (n : ℕ) : ℤ :=
  ofDigits ((List.range n).map (fun i => if i % 2 = 0 then (9 : ℤ) else 0))

def witnessDigits (n k : ℕ) : List ℤ :=
  if k = 0 then List.replicate n 1
  else if k = 9 then (List.range n).map (fun i => if i % 2 = 0 then 9 else 0)
  else (List.range n).map (fun i => if i % 2 = 0 then 1 else 1 + (k : ℤ))

def witness (n k : ℕ) : ℤ := ofDigits (witnessDigits n k)

def i64OfNat (m : ℕ) (hm : m ≤ 9) : Std.I64 :=
  Std.I64.ofInt (m : ℤ) (by
    rw [Aeneas.Std.IScalar.cMin_I64_eq, Aeneas.Std.IScalar.cMax_I64_eq]
    have hm' : (m : ℤ) ≤ 9 := by exact_mod_cast hm
    omega)

/-- The function returns a result r and r is a permutation of the strictly increasing list of all n,k-valid integers, where an integer x is n,k-valid exactly when 10^(n-1) <= x <= 10^n - 1 and, writing its n decimal digits from most significant to least significant as d_0,...,d_{n-1} (so x = sum_{i=0}^{n-1} d_i * 10^(n-1-i), 0 <= d_i <= 9, and d_0 != 0), we have |d_{i+1} - d_i| = k for every i with 0 <= i < n-1. Equivalently, for every integer x, the number of indices j with 0 <= j < len(r) and r[j] = x is exactly 1 if x is n,k-valid, and exactly 0 otherwise.
  Preconditions: n and k are integers satisfying 2 <= n <= 9 and 0 <= k <= 9. -/
theorem spec_1 (n k : ℕ) (hn : 2 ≤ n) (hn9 : n ≤ 9) (hk0 : 0 ≤ k) (hk9 : k ≤ 9) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.NumsSameConsecDiff.nums_same_consec_diff (i64OfNat n (by omega))
          (i64OfNat k (by omega)) = ok r ∧
        (vals r).Perm (validInts n k) ∧
        (∀ x : ℤ, IsValid n k x → numOcc (vals r) x = 1) ∧
        (∀ x : ℤ, ¬ IsValid n k x → numOcc (vals r) x = 0) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n k : ℕ) (hn : 2 ≤ n) (hn9 : n ≤ 9) (hk0 : 0 ≤ k) (hk9 : k ≤ 9), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.NumsSameConsecDiff.nums_same_consec_diff (i64OfNat n (by omega))
          (i64OfNat k (by omega)) = ok r ∧
        (vals r).Perm (validInts n k) ∧
        (∀ x : ℤ, IsValid n k x → numOcc (vals r) x = 1) ∧
        (∀ x : ℤ, ¬ IsValid n k x → numOcc (vals r) x = 0)) := by
  sorry

/-- For every n and k satisfying the preconditions, the function returns a result r; it does not fail, panic, or overflow.
  Preconditions: n and k are integers satisfying 2 <= n <= 9 and 0 <= k <= 9. -/
theorem spec_2 (n k : ℕ) (hn : 2 ≤ n) (hn9 : n ≤ 9) (hk0 : 0 ≤ k) (hk9 : k ≤ 9) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.NumsSameConsecDiff.nums_same_consec_diff (i64OfNat n (by omega))
        (i64OfNat k (by omega)) = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n k : ℕ) (hn : 2 ≤ n) (hn9 : n ≤ 9) (hk0 : 0 ≤ k) (hk9 : k ≤ 9), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.NumsSameConsecDiff.nums_same_consec_diff (i64OfNat n (by omega))
        (i64OfNat k (by omega)) = ok r) := by
  sorry

/-- Whenever the function returns a result r, every element of r is n,k-valid, where an integer x is n,k-valid exactly when 10^(n-1) <= x <= 10^n - 1 and its n decimal digits d_0,...,d_{n-1} (most significant first) satisfy d_0 != 0, 0 <= d_i <= 9 for all i, and |d_{i+1} - d_i| = k for every i with 0 <= i < n-1.
  Preconditions: n and k are integers satisfying 2 <= n <= 9 and 0 <= k <= 9. -/
theorem spec_3 (n k : ℕ) (hn : 2 ≤ n) (hn9 : n ≤ 9) (hk0 : 0 ≤ k) (hk9 : k ≤ 9) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.NumsSameConsecDiff.nums_same_consec_diff (i64OfNat n (by omega))
          (i64OfNat k (by omega)) = ok r →
        ∀ x : ℤ, x ∈ vals r → IsValid n k x := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n k : ℕ) (hn : 2 ≤ n) (hn9 : n ≤ 9) (hk0 : 0 ≤ k) (hk9 : k ≤ 9), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.NumsSameConsecDiff.nums_same_consec_diff (i64OfNat n (by omega))
          (i64OfNat k (by omega)) = ok r →
        ∀ x : ℤ, x ∈ vals r → IsValid n k x) := by
  sorry

/-- Whenever the function returns a result r, for every integer x that is n,k-valid (i.e. 10^(n-1) <= x <= 10^n - 1 and its n decimal digits d_0,...,d_{n-1}, most significant first, satisfy d_0 != 0, 0 <= d_i <= 9, and |d_{i+1} - d_i| = k for all 0 <= i < n-1), there exists an index j with 0 <= j < len(r) and r[j] = x.
  Preconditions: n and k are integers satisfying 2 <= n <= 9 and 0 <= k <= 9. -/
theorem spec_4 (n k : ℕ) (hn : 2 ≤ n) (hn9 : n ≤ 9) (hk0 : 0 ≤ k) (hk9 : k ≤ 9) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.NumsSameConsecDiff.nums_same_consec_diff (i64OfNat n (by omega))
          (i64OfNat k (by omega)) = ok r →
        ∀ x : ℤ, IsValid n k x → x ∈ vals r := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n k : ℕ) (hn : 2 ≤ n) (hn9 : n ≤ 9) (hk0 : 0 ≤ k) (hk9 : k ≤ 9), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.NumsSameConsecDiff.nums_same_consec_diff (i64OfNat n (by omega))
          (i64OfNat k (by omega)) = ok r →
        ∀ x : ℤ, IsValid n k x → x ∈ vals r) := by
  sorry

/-- Whenever the function returns a result r, for every i and j with 0 <= i < j < len(r), r[i] != r[j].
  Preconditions: n and k are integers satisfying 2 <= n <= 9 and 0 <= k <= 9. -/
theorem spec_5 (n k : ℕ) (hn : 2 ≤ n) (hn9 : n ≤ 9) (hk0 : 0 ≤ k) (hk9 : k ≤ 9) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.NumsSameConsecDiff.nums_same_consec_diff (i64OfNat n (by omega))
          (i64OfNat k (by omega)) = ok r →
        ∀ (i j : ℕ) (hi : i < (vals r).length) (hij : i < j) (hj : j < (vals r).length),
          (vals r)[i]'hi ≠ (vals r)[j]'hj := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n k : ℕ) (hn : 2 ≤ n) (hn9 : n ≤ 9) (hk0 : 0 ≤ k) (hk9 : k ≤ 9), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.NumsSameConsecDiff.nums_same_consec_diff (i64OfNat n (by omega))
          (i64OfNat k (by omega)) = ok r →
        ∀ (i j : ℕ) (hi : i < (vals r).length) (hij : i < j) (hj : j < (vals r).length),
          (vals r)[i]'hi ≠ (vals r)[j]'hj) := by
  sorry

/-- Whenever the function returns a result r, len(r) equals the number of integers x that are n,k-valid, where n,k-valid means 10^(n-1) <= x <= 10^n - 1 and the n decimal digits d_0,...,d_{n-1} of x (most significant first) satisfy d_0 != 0, 0 <= d_i <= 9, and |d_{i+1} - d_i| = k for all 0 <= i < n-1.
  Preconditions: n and k are integers satisfying 2 <= n <= 9 and 0 <= k <= 9. -/
theorem spec_6 (n k : ℕ) (hn : 2 ≤ n) (hn9 : n ≤ 9) (hk0 : 0 ≤ k) (hk9 : k ≤ 9) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.NumsSameConsecDiff.nums_same_consec_diff (i64OfNat n (by omega))
          (i64OfNat k (by omega)) = ok r →
        (vals r).length = validCount n k := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n k : ℕ) (hn : 2 ≤ n) (hn9 : n ≤ 9) (hk0 : 0 ≤ k) (hk9 : k ≤ 9), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.NumsSameConsecDiff.nums_same_consec_diff (i64OfNat n (by omega))
          (i64OfNat k (by omega)) = ok r →
        (vals r).length = validCount n k) := by
  sorry

/-- Whenever the function returns a result r, for every index i with 0 <= i < len(r), 10^(n-1) <= r[i] <= 10^n - 1.
  Preconditions: n and k are integers satisfying 2 <= n <= 9 and 0 <= k <= 9. -/
theorem spec_7 (n k : ℕ) (hn : 2 ≤ n) (hn9 : n ≤ 9) (hk0 : 0 ≤ k) (hk9 : k ≤ 9) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.NumsSameConsecDiff.nums_same_consec_diff (i64OfNat n (by omega))
          (i64OfNat k (by omega)) = ok r →
        ∀ (i : ℕ) (hi : i < (vals r).length),
          (10 : ℤ) ^ (n - 1) ≤ (vals r)[i]'hi ∧ (vals r)[i]'hi ≤ (10 : ℤ) ^ n - 1 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n k : ℕ) (hn : 2 ≤ n) (hn9 : n ≤ 9) (hk0 : 0 ≤ k) (hk9 : k ≤ 9), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.NumsSameConsecDiff.nums_same_consec_diff (i64OfNat n (by omega))
          (i64OfNat k (by omega)) = ok r →
        ∀ (i : ℕ) (hi : i < (vals r).length),
          (10 : ℤ) ^ (n - 1) ≤ (vals r)[i]'hi ∧ (vals r)[i]'hi ≤ (10 : ℤ) ^ n - 1) := by
  sorry

/-- Whenever the function returns a result r, the following concrete n,k-valid integer occurs in r: if k = 0, the n-digit integer 11...1 whose digits are all 1; if 1 <= k <= 8, the n-digit integer whose digits alternate 1, 1+k, 1, 1+k, ... starting with 1; if k = 9, the n-digit integer whose digits alternate 9, 0, 9, 0, ... starting with 9.
  Preconditions: n and k are integers satisfying 2 <= n <= 9 and 0 <= k <= 9. -/
theorem spec_8 (n k : ℕ) (hn : 2 ≤ n) (hn9 : n ≤ 9) (hk0 : 0 ≤ k) (hk9 : k ≤ 9) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.NumsSameConsecDiff.nums_same_consec_diff (i64OfNat n (by omega))
          (i64OfNat k (by omega)) = ok r →
        witness n k ∈ vals r := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n k : ℕ) (hn : 2 ≤ n) (hn9 : n ≤ 9) (hk0 : 0 ≤ k) (hk9 : k ≤ 9), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.NumsSameConsecDiff.nums_same_consec_diff (i64OfNat n (by omega))
          (i64OfNat k (by omega)) = ok r →
        witness n k ∈ vals r) := by
  sorry

/-- Whenever the function returns a result r, len(r) <= 9 * 2^(n-1).
  Preconditions: n and k are integers satisfying 2 <= n <= 9 and 0 <= k <= 9. -/
theorem spec_9 (n k : ℕ) (hn : 2 ≤ n) (hn9 : n ≤ 9) (hk0 : 0 ≤ k) (hk9 : k ≤ 9) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.NumsSameConsecDiff.nums_same_consec_diff (i64OfNat n (by omega))
          (i64OfNat k (by omega)) = ok r →
        (vals r).length ≤ 9 * 2 ^ (n - 1) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n k : ℕ) (hn : 2 ≤ n) (hn9 : n ≤ 9) (hk0 : 0 ≤ k) (hk9 : k ≤ 9), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.NumsSameConsecDiff.nums_same_consec_diff (i64OfNat n (by omega))
          (i64OfNat k (by omega)) = ok r →
        (vals r).length ≤ 9 * 2 ^ (n - 1)) := by
  sorry

/-- The function returns a result r and r is a permutation of the list of the nine n-digit repdigits R_1,...,R_9, where R_d is the integer whose n decimal digits are all d, for d = 1,...,9.
  Preconditions: n and k are integers satisfying 2 <= n <= 9 and k = 0. -/
theorem spec_10 (n k : ℕ) (hn : 2 ≤ n) (hn9 : n ≤ 9) (hk : k = 0) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.NumsSameConsecDiff.nums_same_consec_diff (i64OfNat n (by omega))
          (i64OfNat k (by omega)) = ok r ∧
        (vals r).Perm (repdigits n) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n k : ℕ) (hn : 2 ≤ n) (hn9 : n ≤ 9) (hk : k = 0), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.NumsSameConsecDiff.nums_same_consec_diff (i64OfNat n (by omega))
          (i64OfNat k (by omega)) = ok r ∧
        (vals r).Perm (repdigits n)) := by
  sorry

/-- The function returns a result r and r has length 1; its unique element is the n-digit integer whose digit in position i (0-based from the most significant digit) is 9 if i is even and 0 if i is odd.
  Preconditions: n and k are integers satisfying 2 <= n <= 9 and k = 9. -/
theorem spec_11 (n k : ℕ) (hn : 2 ≤ n) (hn9 : n ≤ 9) (hk : k = 9) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.NumsSameConsecDiff.nums_same_consec_diff (i64OfNat n (by omega))
          (i64OfNat k (by omega)) = ok r ∧
        (vals r).length = 1 ∧ vals r = [ninesZeros n] := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (n k : ℕ) (hn : 2 ≤ n) (hn9 : n ≤ 9) (hk : k = 9), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.NumsSameConsecDiff.nums_same_consec_diff (i64OfNat n (by omega))
          (i64OfNat k (by omega)) = ok r ∧
        (vals r).length = 1 ∧ vals r = [ninesZeros n]) := by
  sorry

/-- Whenever the function returns a result r, for every integer x occurring in r, if x has n decimal digits d_0,...,d_{n-1} (most significant first), d_0 <= 8, and |d_{i+1} - d_i| = k for every i with 0 <= i < n-1, then the integer y = sum_{i=0}^{n-1} (9 - d_i) * 10^(n-1-i) also occurs in r.
  Preconditions: n and k are integers satisfying 2 <= n <= 9 and 0 <= k <= 9. -/
theorem spec_12 (n k : ℕ) (hn : 2 ≤ n) (hn9 : n ≤ 9) (hk0 : 0 ≤ k) (hk9 : k ≤ 9) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.NumsSameConsecDiff.nums_same_consec_diff (i64OfNat n (by omega))
          (i64OfNat k (by omega)) = ok r →
        ∀ x : ℤ, x ∈ vals r → HasNDigits n x → digit n x 0 ≤ 8 → ConsecDiff n k x →
          ofDigits ((digits n x).map (fun d => 9 - d)) ∈ vals r := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (n k : ℕ) (hn : 2 ≤ n) (hn9 : n ≤ 9) (hk0 : 0 ≤ k) (hk9 : k ≤ 9), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.NumsSameConsecDiff.nums_same_consec_diff (i64OfNat n (by omega))
          (i64OfNat k (by omega)) = ok r →
        ∀ x : ℤ, x ∈ vals r → HasNDigits n x → digit n x 0 ≤ 8 → ConsecDiff n k x →
          ofDigits ((digits n x).map (fun d => 9 - d)) ∈ vals r) := by
  sorry

/-- Whenever the function returns a result r, for every integer x occurring in r, if x has n decimal digits d_0,...,d_{n-1} (most significant first), d_{n-1} != 0, and |d_{i+1} - d_i| = k for every i with 0 <= i < n-1, then the integer y = sum_{i=0}^{n-1} d_{n-1-i} * 10^(n-1-i) also occurs in r.
  Preconditions: n and k are integers satisfying 2 <= n <= 9 and 0 <= k <= 9. -/
theorem spec_13 (n k : ℕ) (hn : 2 ≤ n) (hn9 : n ≤ 9) (hk0 : 0 ≤ k) (hk9 : k ≤ 9) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.NumsSameConsecDiff.nums_same_consec_diff (i64OfNat n (by omega))
          (i64OfNat k (by omega)) = ok r →
        ∀ x : ℤ, x ∈ vals r → HasNDigits n x → digit n x (n - 1) ≠ 0 → ConsecDiff n k x →
          ofDigits (digits n x).reverse ∈ vals r := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (n k : ℕ) (hn : 2 ≤ n) (hn9 : n ≤ 9) (hk0 : 0 ≤ k) (hk9 : k ≤ 9), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.NumsSameConsecDiff.nums_same_consec_diff (i64OfNat n (by omega))
          (i64OfNat k (by omega)) = ok r →
        ∀ x : ℤ, x ∈ vals r → HasNDigits n x → digit n x (n - 1) ≠ 0 → ConsecDiff n k x →
          ofDigits (digits n x).reverse ∈ vals r) := by
  sorry

end AegisSpec.NumsSameConsecDiff
