import Aegis.AreSimilar.Code.Funs

/-!
# Specifications of `Aegis.AreSimilar.are_similar`

LeetCode problem `matrix-similarity-after-cyclic-shifts`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.AreSimilar

namespace AegisSpec.AreSimilar

def matAt (mat : Slice (alloc.vec.Vec I64)) (i j : Nat) : Int :=
  match mat.val[i]? with
  | some row =>
    match row.val[j]? with
    | some x => x.val
    | none => 0
  | none => 0

def modRes (a : Int) (n : Nat) : Nat := (a % (n : Int)).toNat

theorem matAt_eq (mat : Slice (alloc.vec.Vec I64)) (i j : Nat)
    (hi : i < mat.val.length) (hj : j < (mat.val[i]).val.length) :
    matAt mat i j = ((mat.val[i]).val[j]).val := by
  simp [matAt, hi, hj]

def colShiftL (n : Nat) (k : Int) (j : Nat) : Nat := modRes ((j : Int) + k) n

def colShiftR (n : Nat) (k : Int) (j : Nat) : Nat := modRes ((j : Int) - k) n

def gcdNK (n : Nat) (k : Int) : Nat := Nat.gcd n k.toNat

/-- The function returns a result r and r = true if and only if, for every row index i with 0 <= i < m and every column index j with 0 <= j < n: if i is even then mat[i][(j + k) mod n] = mat[i][j], and if i is odd then mat[i][(j - k) mod n] = mat[i][j], where 'mod n' denotes the least non-negative residue modulo n. Equivalently, r = true exactly when the matrix obtained by performing k rounds (each even-indexed row shifted cyclically left by one per round and each odd-indexed row shifted cyclically right by one per round) is identical to mat.
  Preconditions: Let m = len(mat) and n = len(mat[0]). Assume 1 <= m <= 25; every row of mat has length n with 1 <= n <= 25; 1 <= k <= 50; and 1 <= mat[i][j] <= 25 for every 0 <= i < m and 0 <= j < n. -/
theorem spec_1
    (mat : Slice (alloc.vec.Vec I64)) (k : I64) (n : Nat)
    (hm1 : 1 ≤ mat.val.length) (hm25 : mat.val.length ≤ 25)
    (hn1 : 1 ≤ n) (hn25 : n ≤ 25)
    (hrow_len : ∀ i, (hi : i < mat.val.length) → (mat.val[i]).val.length = n)
    (hk1 : 1 ≤ k.val) (hk50 : k.val ≤ 50)
    (hval : ∀ i j, i < mat.val.length → j < n → 1 ≤ matAt mat i j ∧ matAt mat i j ≤ 25) :
    ∃ r : Bool, are_similar mat k = ok r ∧
      (r = true ↔
        ∀ i, i < mat.val.length → ∀ j, j < n →
          ((i % 2 = 0 → matAt mat i (colShiftL n k.val j) = matAt mat i j) ∧
           (i % 2 = 1 → matAt mat i (colShiftR n k.val j) = matAt mat i j))) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (mat : Slice (alloc.vec.Vec I64)) (k : I64) (n : Nat)
    (hm1 : 1 ≤ mat.val.length) (hm25 : mat.val.length ≤ 25)
    (hn1 : 1 ≤ n) (hn25 : n ≤ 25)
    (hrow_len : ∀ i, (hi : i < mat.val.length) → (mat.val[i]).val.length = n)
    (hk1 : 1 ≤ k.val) (hk50 : k.val ≤ 50)
    (hval : ∀ i j, i < mat.val.length → j < n → 1 ≤ matAt mat i j ∧ matAt mat i j ≤ 25), ∃ r : Bool, are_similar mat k = ok r ∧
      (r = true ↔
        ∀ i, i < mat.val.length → ∀ j, j < n →
          ((i % 2 = 0 → matAt mat i (colShiftL n k.val j) = matAt mat i j) ∧
           (i % 2 = 1 → matAt mat i (colShiftR n k.val j) = matAt mat i j)))) := by
  sorry

/-- The function returns a result r; it does not fail, panic, divide by zero, access out of bounds, or overflow on any input satisfying the preconditions.
  Preconditions: Let m = len(mat) and n = len(mat[0]). Assume 1 <= m <= 25; every row of mat has length n with 1 <= n <= 25; 1 <= k <= 50; and 1 <= mat[i][j] <= 25 for every 0 <= i < m and 0 <= j < n. -/
theorem spec_2
    (mat : Slice (alloc.vec.Vec I64)) (k : I64) (n : Nat)
    (hm1 : 1 ≤ mat.val.length) (hm25 : mat.val.length ≤ 25)
    (hn1 : 1 ≤ n) (hn25 : n ≤ 25)
    (hrow_len : ∀ i, (hi : i < mat.val.length) → (mat.val[i]).val.length = n)
    (hk1 : 1 ≤ k.val) (hk50 : k.val ≤ 50)
    (hval : ∀ i j, i < mat.val.length → j < n → 1 ≤ matAt mat i j ∧ matAt mat i j ≤ 25) :
    ∃ r : Bool, are_similar mat k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (mat : Slice (alloc.vec.Vec I64)) (k : I64) (n : Nat)
    (hm1 : 1 ≤ mat.val.length) (hm25 : mat.val.length ≤ 25)
    (hn1 : 1 ≤ n) (hn25 : n ≤ 25)
    (hrow_len : ∀ i, (hi : i < mat.val.length) → (mat.val[i]).val.length = n)
    (hk1 : 1 ≤ k.val) (hk50 : k.val ≤ 50)
    (hval : ∀ i j, i < mat.val.length → j < n → 1 ≤ matAt mat i j ∧ matAt mat i j ≤ 25), ∃ r : Bool, are_similar mat k = ok r) := by
  sorry

/-- The function returns a result r and r = true.
  Preconditions: Let m = len(mat) and n = len(mat[0]). Assume 1 <= m <= 25; every row of mat has length n with 1 <= n <= 25; 1 <= k <= 50; 1 <= mat[i][j] <= 25 for every 0 <= i < m and 0 <= j < n; and k mod n = 0. -/
theorem spec_3
    (mat : Slice (alloc.vec.Vec I64)) (k : I64) (n : Nat)
    (hm1 : 1 ≤ mat.val.length) (hm25 : mat.val.length ≤ 25)
    (hn1 : 1 ≤ n) (hn25 : n ≤ 25)
    (hrow_len : ∀ i, (hi : i < mat.val.length) → (mat.val[i]).val.length = n)
    (hk1 : 1 ≤ k.val) (hk50 : k.val ≤ 50)
    (hval : ∀ i j, i < mat.val.length → j < n → 1 ≤ matAt mat i j ∧ matAt mat i j ≤ 25)
    (hkmod : modRes k.val n = 0) :
    ∃ r : Bool, are_similar mat k = ok r ∧ r = true := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (mat : Slice (alloc.vec.Vec I64)) (k : I64) (n : Nat)
    (hm1 : 1 ≤ mat.val.length) (hm25 : mat.val.length ≤ 25)
    (hn1 : 1 ≤ n) (hn25 : n ≤ 25)
    (hrow_len : ∀ i, (hi : i < mat.val.length) → (mat.val[i]).val.length = n)
    (hk1 : 1 ≤ k.val) (hk50 : k.val ≤ 50)
    (hval : ∀ i j, i < mat.val.length → j < n → 1 ≤ matAt mat i j ∧ matAt mat i j ≤ 25)
    (hkmod : modRes k.val n = 0), ∃ r : Bool, are_similar mat k = ok r ∧ r = true) := by
  sorry

/-- The function returns a result r and r = true if and only if every row of mat is constant, i.e., for every 0 <= i < m and every 0 <= j < n, mat[i][j] = mat[i][0].
  Preconditions: Let m = len(mat) and n = len(mat[0]). Assume 1 <= m <= 25; every row of mat has length n with 1 <= n <= 25; 1 <= k <= 50; 1 <= mat[i][j] <= 25 for every 0 <= i < m and 0 <= j < n; n > 1; and either k mod n = 1 or k mod n = n - 1. -/
theorem spec_4
    (mat : Slice (alloc.vec.Vec I64)) (k : I64) (n : Nat)
    (hm1 : 1 ≤ mat.val.length) (hm25 : mat.val.length ≤ 25)
    (hn1 : 1 ≤ n) (hn25 : n ≤ 25)
    (hrow_len : ∀ i, (hi : i < mat.val.length) → (mat.val[i]).val.length = n)
    (hk1 : 1 ≤ k.val) (hk50 : k.val ≤ 50)
    (hval : ∀ i j, i < mat.val.length → j < n → 1 ≤ matAt mat i j ∧ matAt mat i j ≤ 25)
    (hn_gt_one : 1 < n)
    (hkmod : modRes k.val n = 1 ∨ modRes k.val n = n - 1) :
    ∃ r : Bool, are_similar mat k = ok r ∧
      (r = true ↔ ∀ i, i < mat.val.length → ∀ j, j < n → matAt mat i j = matAt mat i 0) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (mat : Slice (alloc.vec.Vec I64)) (k : I64) (n : Nat)
    (hm1 : 1 ≤ mat.val.length) (hm25 : mat.val.length ≤ 25)
    (hn1 : 1 ≤ n) (hn25 : n ≤ 25)
    (hrow_len : ∀ i, (hi : i < mat.val.length) → (mat.val[i]).val.length = n)
    (hk1 : 1 ≤ k.val) (hk50 : k.val ≤ 50)
    (hval : ∀ i j, i < mat.val.length → j < n → 1 ≤ matAt mat i j ∧ matAt mat i j ≤ 25)
    (hn_gt_one : 1 < n)
    (hkmod : modRes k.val n = 1 ∨ modRes k.val n = n - 1), ∃ r : Bool, are_similar mat k = ok r ∧
      (r = true ↔ ∀ i, i < mat.val.length → ∀ j, j < n → matAt mat i j = matAt mat i 0)) := by
  sorry

/-- Whenever the function returns a result r with r = true, for every even row index i with 0 <= i < m and every column j with 0 <= j < n, mat[i][(j + k) mod n] = mat[i][j].
  Preconditions: Let m = len(mat) and n = len(mat[0]). Assume 1 <= m <= 25; every row of mat has length n with 1 <= n <= 25; 1 <= k <= 50; and 1 <= mat[i][j] <= 25 for every 0 <= i < m and 0 <= j < n. -/
theorem spec_5
    (mat : Slice (alloc.vec.Vec I64)) (k : I64) (n : Nat)
    (hm1 : 1 ≤ mat.val.length) (hm25 : mat.val.length ≤ 25)
    (hn1 : 1 ≤ n) (hn25 : n ≤ 25)
    (hrow_len : ∀ i, (hi : i < mat.val.length) → (mat.val[i]).val.length = n)
    (hk1 : 1 ≤ k.val) (hk50 : k.val ≤ 50)
    (hval : ∀ i j, i < mat.val.length → j < n → 1 ≤ matAt mat i j ∧ matAt mat i j ≤ 25) :
    ∀ r : Bool, are_similar mat k = ok r → r = true →
      ∀ i, i < mat.val.length → i % 2 = 0 → ∀ j, j < n →
        matAt mat i (colShiftL n k.val j) = matAt mat i j := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (mat : Slice (alloc.vec.Vec I64)) (k : I64) (n : Nat)
    (hm1 : 1 ≤ mat.val.length) (hm25 : mat.val.length ≤ 25)
    (hn1 : 1 ≤ n) (hn25 : n ≤ 25)
    (hrow_len : ∀ i, (hi : i < mat.val.length) → (mat.val[i]).val.length = n)
    (hk1 : 1 ≤ k.val) (hk50 : k.val ≤ 50)
    (hval : ∀ i j, i < mat.val.length → j < n → 1 ≤ matAt mat i j ∧ matAt mat i j ≤ 25), ∀ r : Bool, are_similar mat k = ok r → r = true →
      ∀ i, i < mat.val.length → i % 2 = 0 → ∀ j, j < n →
        matAt mat i (colShiftL n k.val j) = matAt mat i j) := by
  sorry

/-- Whenever the function returns a result r with r = true, for every odd row index i with 0 <= i < m and every column j with 0 <= j < n, mat[i][(j - k) mod n] = mat[i][j], where 'mod n' denotes the least non-negative residue modulo n.
  Preconditions: Let m = len(mat) and n = len(mat[0]). Assume 1 <= m <= 25; every row of mat has length n with 1 <= n <= 25; 1 <= k <= 50; and 1 <= mat[i][j] <= 25 for every 0 <= i < m and 0 <= j < n. -/
theorem spec_6
    (mat : Slice (alloc.vec.Vec I64)) (k : I64) (n : Nat)
    (hm1 : 1 ≤ mat.val.length) (hm25 : mat.val.length ≤ 25)
    (hn1 : 1 ≤ n) (hn25 : n ≤ 25)
    (hrow_len : ∀ i, (hi : i < mat.val.length) → (mat.val[i]).val.length = n)
    (hk1 : 1 ≤ k.val) (hk50 : k.val ≤ 50)
    (hval : ∀ i j, i < mat.val.length → j < n → 1 ≤ matAt mat i j ∧ matAt mat i j ≤ 25) :
    ∀ r : Bool, are_similar mat k = ok r → r = true →
      ∀ i, i < mat.val.length → i % 2 = 1 → ∀ j, j < n →
        matAt mat i (colShiftR n k.val j) = matAt mat i j := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (mat : Slice (alloc.vec.Vec I64)) (k : I64) (n : Nat)
    (hm1 : 1 ≤ mat.val.length) (hm25 : mat.val.length ≤ 25)
    (hn1 : 1 ≤ n) (hn25 : n ≤ 25)
    (hrow_len : ∀ i, (hi : i < mat.val.length) → (mat.val[i]).val.length = n)
    (hk1 : 1 ≤ k.val) (hk50 : k.val ≤ 50)
    (hval : ∀ i j, i < mat.val.length → j < n → 1 ≤ matAt mat i j ∧ matAt mat i j ≤ 25), ∀ r : Bool, are_similar mat k = ok r → r = true →
      ∀ i, i < mat.val.length → i % 2 = 1 → ∀ j, j < n →
        matAt mat i (colShiftR n k.val j) = matAt mat i j) := by
  sorry

/-- Whenever the function returns a result r with r = false, there exist a row index i with 0 <= i < m and a column index j with 0 <= j < n such that either (i is even and mat[i][(j + k) mod n] != mat[i][j]) or (i is odd and mat[i][(j - k) mod n] != mat[i][j]).
  Preconditions: Let m = len(mat) and n = len(mat[0]). Assume 1 <= m <= 25; every row of mat has length n with 1 <= n <= 25; 1 <= k <= 50; and 1 <= mat[i][j] <= 25 for every 0 <= i < m and 0 <= j < n. -/
theorem spec_7
    (mat : Slice (alloc.vec.Vec I64)) (k : I64) (n : Nat)
    (hm1 : 1 ≤ mat.val.length) (hm25 : mat.val.length ≤ 25)
    (hn1 : 1 ≤ n) (hn25 : n ≤ 25)
    (hrow_len : ∀ i, (hi : i < mat.val.length) → (mat.val[i]).val.length = n)
    (hk1 : 1 ≤ k.val) (hk50 : k.val ≤ 50)
    (hval : ∀ i j, i < mat.val.length → j < n → 1 ≤ matAt mat i j ∧ matAt mat i j ≤ 25) :
    ∀ r : Bool, are_similar mat k = ok r → r = false →
      ∃ i, i < mat.val.length ∧ ∃ j, j < n ∧
        ((i % 2 = 0 ∧ matAt mat i (colShiftL n k.val j) ≠ matAt mat i j) ∨
         (i % 2 = 1 ∧ matAt mat i (colShiftR n k.val j) ≠ matAt mat i j)) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (mat : Slice (alloc.vec.Vec I64)) (k : I64) (n : Nat)
    (hm1 : 1 ≤ mat.val.length) (hm25 : mat.val.length ≤ 25)
    (hn1 : 1 ≤ n) (hn25 : n ≤ 25)
    (hrow_len : ∀ i, (hi : i < mat.val.length) → (mat.val[i]).val.length = n)
    (hk1 : 1 ≤ k.val) (hk50 : k.val ≤ 50)
    (hval : ∀ i j, i < mat.val.length → j < n → 1 ≤ matAt mat i j ∧ matAt mat i j ≤ 25), ∀ r : Bool, are_similar mat k = ok r → r = false →
      ∃ i, i < mat.val.length ∧ ∃ j, j < n ∧
        ((i % 2 = 0 ∧ matAt mat i (colShiftL n k.val j) ≠ matAt mat i j) ∨
         (i % 2 = 1 ∧ matAt mat i (colShiftR n k.val j) ≠ matAt mat i j))) := by
  sorry

/-- The function returns a result r and r = false.
  Preconditions: Let m = len(mat) and n = len(mat[0]). Assume 1 <= m <= 25; every row of mat has length n with 1 <= n <= 25; 1 <= k <= 50; 1 <= mat[i][j] <= 25 for every 0 <= i < m and 0 <= j < n. Also assume there exist a row index i with 0 <= i < m and a column index j with 0 <= j < n such that either (i is even and mat[i][(j + k) mod n] != mat[i][j]) or (i is odd and mat[i][(j - k) mod n] != mat[i][j]). -/
theorem spec_8
    (mat : Slice (alloc.vec.Vec I64)) (k : I64) (n : Nat)
    (hm1 : 1 ≤ mat.val.length) (hm25 : mat.val.length ≤ 25)
    (hn1 : 1 ≤ n) (hn25 : n ≤ 25)
    (hrow_len : ∀ i, (hi : i < mat.val.length) → (mat.val[i]).val.length = n)
    (hk1 : 1 ≤ k.val) (hk50 : k.val ≤ 50)
    (hval : ∀ i j, i < mat.val.length → j < n → 1 ≤ matAt mat i j ∧ matAt mat i j ≤ 25)
    (hwit : ∃ i, i < mat.val.length ∧ ∃ j, j < n ∧
        ((i % 2 = 0 ∧ matAt mat i (colShiftL n k.val j) ≠ matAt mat i j) ∨
         (i % 2 = 1 ∧ matAt mat i (colShiftR n k.val j) ≠ matAt mat i j))) :
    ∃ r : Bool, are_similar mat k = ok r ∧ r = false := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (mat : Slice (alloc.vec.Vec I64)) (k : I64) (n : Nat)
    (hm1 : 1 ≤ mat.val.length) (hm25 : mat.val.length ≤ 25)
    (hn1 : 1 ≤ n) (hn25 : n ≤ 25)
    (hrow_len : ∀ i, (hi : i < mat.val.length) → (mat.val[i]).val.length = n)
    (hk1 : 1 ≤ k.val) (hk50 : k.val ≤ 50)
    (hval : ∀ i j, i < mat.val.length → j < n → 1 ≤ matAt mat i j ∧ matAt mat i j ≤ 25)
    (hwit : ∃ i, i < mat.val.length ∧ ∃ j, j < n ∧
        ((i % 2 = 0 ∧ matAt mat i (colShiftL n k.val j) ≠ matAt mat i j) ∨
         (i % 2 = 1 ∧ matAt mat i (colShiftR n k.val j) ≠ matAt mat i j))), ∃ r : Bool, are_similar mat k = ok r ∧ r = false) := by
  sorry

/-- Whenever the function returns a result r with r = true, for every row index i with 0 <= i < m and all column indices j and l with 0 <= j,l < n, if j ≡ l (mod gcd(n,k)), then mat[i][j] = mat[i][l], where gcd(n,k) is the greatest common divisor of n and k.
  Preconditions: Let m = len(mat) and n = len(mat[0]). Assume 1 <= m <= 25; every row of mat has length n with 1 <= n <= 25; 1 <= k <= 50; and 1 <= mat[i][j] <= 25 for every 0 <= i < m and 0 <= j < n. -/
theorem spec_9
    (mat : Slice (alloc.vec.Vec I64)) (k : I64) (n : Nat)
    (hm1 : 1 ≤ mat.val.length) (hm25 : mat.val.length ≤ 25)
    (hn1 : 1 ≤ n) (hn25 : n ≤ 25)
    (hrow_len : ∀ i, (hi : i < mat.val.length) → (mat.val[i]).val.length = n)
    (hk1 : 1 ≤ k.val) (hk50 : k.val ≤ 50)
    (hval : ∀ i j, i < mat.val.length → j < n → 1 ≤ matAt mat i j ∧ matAt mat i j ≤ 25) :
    ∀ r : Bool, are_similar mat k = ok r → r = true →
      ∀ i, i < mat.val.length → ∀ j l, j < n → l < n →
        j ≡ l [MOD gcdNK n k.val] → matAt mat i j = matAt mat i l := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (mat : Slice (alloc.vec.Vec I64)) (k : I64) (n : Nat)
    (hm1 : 1 ≤ mat.val.length) (hm25 : mat.val.length ≤ 25)
    (hn1 : 1 ≤ n) (hn25 : n ≤ 25)
    (hrow_len : ∀ i, (hi : i < mat.val.length) → (mat.val[i]).val.length = n)
    (hk1 : 1 ≤ k.val) (hk50 : k.val ≤ 50)
    (hval : ∀ i j, i < mat.val.length → j < n → 1 ≤ matAt mat i j ∧ matAt mat i j ≤ 25), ∀ r : Bool, are_similar mat k = ok r → r = true →
      ∀ i, i < mat.val.length → ∀ j l, j < n → l < n →
        j ≡ l [MOD gcdNK n k.val] → matAt mat i j = matAt mat i l) := by
  sorry

/-- The function returns a result r and r = true if and only if for every row index i with 0 <= i < m and all column indices j and l with 0 <= j,l < n, if j ≡ l (mod gcd(n,k)), then mat[i][j] = mat[i][l], where gcd(n,k) is the greatest common divisor of n and k.
  Preconditions: Let m = len(mat) and n = len(mat[0]). Assume 1 <= m <= 25; every row of mat has length n with 1 <= n <= 25; 1 <= k <= 50; and 1 <= mat[i][j] <= 25 for every 0 <= i < m and 0 <= j < n. -/
theorem spec_10
    (mat : Slice (alloc.vec.Vec I64)) (k : I64) (n : Nat)
    (hm1 : 1 ≤ mat.val.length) (hm25 : mat.val.length ≤ 25)
    (hn1 : 1 ≤ n) (hn25 : n ≤ 25)
    (hrow_len : ∀ i, (hi : i < mat.val.length) → (mat.val[i]).val.length = n)
    (hk1 : 1 ≤ k.val) (hk50 : k.val ≤ 50)
    (hval : ∀ i j, i < mat.val.length → j < n → 1 ≤ matAt mat i j ∧ matAt mat i j ≤ 25) :
    ∃ r : Bool, are_similar mat k = ok r ∧
      (r = true ↔
        ∀ i, i < mat.val.length → ∀ j l, j < n → l < n →
          j ≡ l [MOD gcdNK n k.val] → matAt mat i j = matAt mat i l) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (mat : Slice (alloc.vec.Vec I64)) (k : I64) (n : Nat)
    (hm1 : 1 ≤ mat.val.length) (hm25 : mat.val.length ≤ 25)
    (hn1 : 1 ≤ n) (hn25 : n ≤ 25)
    (hrow_len : ∀ i, (hi : i < mat.val.length) → (mat.val[i]).val.length = n)
    (hk1 : 1 ≤ k.val) (hk50 : k.val ≤ 50)
    (hval : ∀ i j, i < mat.val.length → j < n → 1 ≤ matAt mat i j ∧ matAt mat i j ≤ 25), ∃ r : Bool, are_similar mat k = ok r ∧
      (r = true ↔
        ∀ i, i < mat.val.length → ∀ j l, j < n → l < n →
          j ≡ l [MOD gcdNK n k.val] → matAt mat i j = matAt mat i l)) := by
  sorry

end AegisSpec.AreSimilar
