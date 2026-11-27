import Aegis.MinimumMoves.Code.Funs

/-!
# Specifications of `Aegis.MinimumMoves.minimum_moves`

LeetCode problem `palindrome-removal`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MinimumMoves

set_option autoImplicit false

namespace AegisSpec.MinimumMoves

def Palindrome (s : List I64) : Prop :=
  ∀ t : ℕ, t < s.length → s[t]? = s[s.length - 1 - t]?

def Move (s s' : List I64) : Prop :=
  ∃ i j : ℕ, i ≤ j ∧ j < s.length ∧
    Palindrome ((s.drop i).take (j + 1 - i)) ∧
    s' = s.take i ++ s.drop (j + 1)

inductive DeletedIn : List I64 → ℕ → Prop where
  | nil : DeletedIn [] 0
  | step {s s' : List I64} {k : ℕ} : Move s s' → DeletedIn s' k → DeletedIn s (k + 1)

def IsMinimumMoves (s : List I64) (k : ℕ) : Prop :=
  DeletedIn s k ∧ ∀ m : ℕ, DeletedIn s m → k ≤ m

def oddCount (s : List I64) : ℕ :=
  ((List.range 20).filter
    (fun k => (s.filter (fun v => v.val = (k : ℤ) + 1)).length % 2 = 1)).length

/-- Whenever the function returns a result r, r is the minimum number of moves needed to delete all elements of arr. A move is defined as follows: from a current sequence s, choose indices i,j with 0 <= i <= j < len(s) such that s[i],...,s[j] is a palindrome, meaning that for every t with 0 <= t <= j-i, s[i+t] = s[j-t]; replace s by the concatenation of s[0..i-1] and s[j+1..len(s)-1]. A complete deletion is a finite sequence of such replacements starting at arr and ending at the empty sequence; r is the least number of moves among all complete deletions of arr.
  Preconditions: arr is a slice of i64 with 1 <= len(arr) <= 100, and for every i with 0 <= i < len(arr), 1 <= arr[i] <= 20. -/
theorem spec_1 (arr : Slice I64) (hlen_lo : 1 ≤ arr.val.length)
    (hlen_hi : arr.val.length ≤ 100) (hrange : ∀ v ∈ arr.val, 1 ≤ v.val ∧ v.val ≤ 20) :
    ∀ r : I64, minimum_moves arr = ok r → ∃ k : ℕ, IsMinimumMoves arr.val k ∧ r.val = (k : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (arr : Slice I64) (hlen_lo : 1 ≤ arr.val.length)
    (hlen_hi : arr.val.length ≤ 100) (hrange : ∀ v ∈ arr.val, 1 ≤ v.val ∧ v.val ≤ 20), ∀ r : I64, minimum_moves arr = ok r → ∃ k : ℕ, IsMinimumMoves arr.val k ∧ r.val = (k : ℤ)) := by
  sorry

/-- For every arr satisfying the preconditions, the function returns a result r: it does not fail because of arithmetic overflow, out-of-bounds indexing, or panic.
  Preconditions: arr is a slice of i64 with 1 <= len(arr) <= 100, and for every i with 0 <= i < len(arr), 1 <= arr[i] <= 20. -/
theorem spec_2 (arr : Slice I64) (hlen_lo : 1 ≤ arr.val.length)
    (hlen_hi : arr.val.length ≤ 100) (hrange : ∀ v ∈ arr.val, 1 ≤ v.val ∧ v.val ≤ 20) :
    ∃ r : I64, minimum_moves arr = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (arr : Slice I64) (hlen_lo : 1 ≤ arr.val.length)
    (hlen_hi : arr.val.length ≤ 100) (hrange : ∀ v ∈ arr.val, 1 ≤ v.val ∧ v.val ≤ 20), ∃ r : I64, minimum_moves arr = ok r) := by
  sorry

/-- Whenever the function returns a result r, 1 <= r <= len(arr).
  Preconditions: arr is a slice of i64 with 1 <= len(arr) <= 100, and for every i with 0 <= i < len(arr), 1 <= arr[i] <= 20. -/
theorem spec_3 (arr : Slice I64) (hlen_lo : 1 ≤ arr.val.length)
    (hlen_hi : arr.val.length ≤ 100) (hrange : ∀ v ∈ arr.val, 1 ≤ v.val ∧ v.val ≤ 20) :
    ∀ r : I64, minimum_moves arr = ok r → 1 ≤ r.val ∧ r.val ≤ (arr.val.length : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (arr : Slice I64) (hlen_lo : 1 ≤ arr.val.length)
    (hlen_hi : arr.val.length ≤ 100) (hrange : ∀ v ∈ arr.val, 1 ≤ v.val ∧ v.val ≤ 20), ∀ r : I64, minimum_moves arr = ok r → 1 ≤ r.val ∧ r.val ≤ (arr.val.length : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, let odd_count be the number of values v with 1 <= v <= 20 for which the count of indices i satisfying 0 <= i < len(arr) and arr[i] = v is odd. Then r >= odd_count.
  Preconditions: arr is a slice of i64 with 1 <= len(arr) <= 100, and for every i with 0 <= i < len(arr), 1 <= arr[i] <= 20. -/
theorem spec_4 (arr : Slice I64) (hlen_lo : 1 ≤ arr.val.length)
    (hlen_hi : arr.val.length ≤ 100) (hrange : ∀ v ∈ arr.val, 1 ≤ v.val ∧ v.val ≤ 20) :
    ∀ r : I64, minimum_moves arr = ok r → (oddCount arr.val : ℤ) ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (arr : Slice I64) (hlen_lo : 1 ≤ arr.val.length)
    (hlen_hi : arr.val.length ≤ 100) (hrange : ∀ v ∈ arr.val, 1 ≤ v.val ∧ v.val ≤ 20), ∀ r : I64, minimum_moves arr = ok r → (oddCount arr.val : ℤ) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r = 1 if and only if arr is a palindrome, meaning that for every i with 0 <= i < len(arr), arr[i] = arr[len(arr)-1-i].
  Preconditions: arr is a slice of i64 with 1 <= len(arr) <= 100, and for every i with 0 <= i < len(arr), 1 <= arr[i] <= 20. -/
theorem spec_5 (arr : Slice I64) (hlen_lo : 1 ≤ arr.val.length)
    (hlen_hi : arr.val.length ≤ 100) (hrange : ∀ v ∈ arr.val, 1 ≤ v.val ∧ v.val ≤ 20) :
    ∀ r : I64, minimum_moves arr = ok r → (r.val = 1 ↔ Palindrome arr.val) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (arr : Slice I64) (hlen_lo : 1 ≤ arr.val.length)
    (hlen_hi : arr.val.length ≤ 100) (hrange : ∀ v ∈ arr.val, 1 ≤ v.val ∧ v.val ≤ 20), ∀ r : I64, minimum_moves arr = ok r → (r.val = 1 ↔ Palindrome arr.val)) := by
  sorry

/-- Whenever the function returns a result r, r = 1 if arr[0] = arr[1], and r = 2 otherwise.
  Preconditions: arr is a slice of i64 with len(arr) = 2, and for every i with 0 <= i < len(arr), 1 <= arr[i] <= 20. -/
theorem spec_6 (arr : Slice I64) (hlen : arr.val.length = 2)
    (hrange : ∀ v ∈ arr.val, 1 ≤ v.val ∧ v.val ≤ 20) :
    ∀ r : I64, minimum_moves arr = ok r →
      ((arr.val[0]? = arr.val[1]? → r.val = 1) ∧
        (arr.val[0]? ≠ arr.val[1]? → r.val = 2)) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (arr : Slice I64) (hlen : arr.val.length = 2)
    (hrange : ∀ v ∈ arr.val, 1 ≤ v.val ∧ v.val ≤ 20), ∀ r : I64, minimum_moves arr = ok r →
      ((arr.val[0]? = arr.val[1]? → r.val = 1) ∧
        (arr.val[0]? ≠ arr.val[1]? → r.val = 2))) := by
  sorry

/-- Whenever the function returns a result r, r = 1 if arr[0] = arr[2]; otherwise r = 2 if arr[0] = arr[1] or arr[1] = arr[2]; otherwise r = 3.
  Preconditions: arr is a slice of i64 with len(arr) = 3, and for every i with 0 <= i < len(arr), 1 <= arr[i] <= 20. -/
theorem spec_7 (arr : Slice I64) (hlen : arr.val.length = 3)
    (hrange : ∀ v ∈ arr.val, 1 ≤ v.val ∧ v.val ≤ 20) :
    ∀ r : I64, minimum_moves arr = ok r →
      ((arr.val[0]? = arr.val[2]? → r.val = 1) ∧
        (arr.val[0]? ≠ arr.val[2]? →
          (arr.val[0]? = arr.val[1]? ∨ arr.val[1]? = arr.val[2]? → r.val = 2)) ∧
        (arr.val[0]? ≠ arr.val[2]? → arr.val[0]? ≠ arr.val[1]? →
          arr.val[1]? ≠ arr.val[2]? → r.val = 3)) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (arr : Slice I64) (hlen : arr.val.length = 3)
    (hrange : ∀ v ∈ arr.val, 1 ≤ v.val ∧ v.val ≤ 20), ∀ r : I64, minimum_moves arr = ok r →
      ((arr.val[0]? = arr.val[2]? → r.val = 1) ∧
        (arr.val[0]? ≠ arr.val[2]? →
          (arr.val[0]? = arr.val[1]? ∨ arr.val[1]? = arr.val[2]? → r.val = 2)) ∧
        (arr.val[0]? ≠ arr.val[2]? → arr.val[0]? ≠ arr.val[1]? →
          arr.val[1]? ≠ arr.val[2]? → r.val = 3))) := by
  sorry

/-- Whenever the function returns a result r, r = len(arr).
  Preconditions: arr is a slice of i64 with 1 <= len(arr) <= 100, for every i with 0 <= i < len(arr), 1 <= arr[i] <= 20, and for every i,j with 0 <= i < j < len(arr), arr[i] != arr[j]. -/
theorem spec_8 (arr : Slice I64) (hlen_lo : 1 ≤ arr.val.length)
    (hlen_hi : arr.val.length ≤ 100) (hrange : ∀ v ∈ arr.val, 1 ≤ v.val ∧ v.val ≤ 20)
    (hnd : arr.val.Nodup) :
    ∀ r : I64, minimum_moves arr = ok r → r.val = (arr.val.length : ℤ) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (arr : Slice I64) (hlen_lo : 1 ≤ arr.val.length)
    (hlen_hi : arr.val.length ≤ 100) (hrange : ∀ v ∈ arr.val, 1 ≤ v.val ∧ v.val ≤ 20)
    (hnd : arr.val.Nodup), ∀ r : I64, minimum_moves arr = ok r → r.val = (arr.val.length : ℤ)) := by
  sorry

/-- Let rev(arr) be the slice of length len(arr) with rev(arr)[i] = arr[len(arr)-1-i] for every i with 0 <= i < len(arr). If minimum_moves(arr) = Ok r, then minimum_moves(rev(arr)) = Ok r.
  Preconditions: arr is a slice of i64 with 1 <= len(arr) <= 100, and for every i with 0 <= i < len(arr), 1 <= arr[i] <= 20. -/
theorem spec_9 (arr : Slice I64) (hlen_lo : 1 ≤ arr.val.length)
    (hlen_hi : arr.val.length ≤ 100) (hrange : ∀ v ∈ arr.val, 1 ≤ v.val ∧ v.val ≤ 20) :
    ∀ rev : Slice I64, rev.val = arr.val.reverse →
      ∀ r : I64, minimum_moves arr = ok r → minimum_moves rev = ok r := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (arr : Slice I64) (hlen_lo : 1 ≤ arr.val.length)
    (hlen_hi : arr.val.length ≤ 100) (hrange : ∀ v ∈ arr.val, 1 ≤ v.val ∧ v.val ≤ 20), ∀ rev : Slice I64, rev.val = arr.val.reverse →
      ∀ r : I64, minimum_moves arr = ok r → minimum_moves rev = ok r) := by
  sorry

/-- If minimum_moves(arr) = Ok r, then minimum_moves(arr2) = Ok (r+1).
  Preconditions: arr is a slice of i64 with 1 <= len(arr) <= 99, for every i with 0 <= i < len(arr), 1 <= arr[i] <= 20, x is an i64 with 1 <= x <= 20, and for every i with 0 <= i < len(arr), arr[i] != x. Let arr2 be the slice obtained by appending x to arr, so len(arr2) = len(arr)+1 and arr2[len(arr)] = x. -/
theorem spec_10 (arr : Slice I64) (hlen_lo : 1 ≤ arr.val.length)
    (hlen_hi : arr.val.length ≤ 99) (hrange : ∀ v ∈ arr.val, 1 ≤ v.val ∧ v.val ≤ 20)
    (x : I64) (hx_lo : 1 ≤ x.val) (hx_hi : x.val ≤ 20) (hx : ∀ v ∈ arr.val, v ≠ x) :
    ∀ r : I64, minimum_moves arr = ok r →
      ∀ arr2 : Slice I64, arr2.val = arr.val ++ [x] →
        ∃ r2 : I64, minimum_moves arr2 = ok r2 ∧ r2.val = r.val + 1 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (arr : Slice I64) (hlen_lo : 1 ≤ arr.val.length)
    (hlen_hi : arr.val.length ≤ 99) (hrange : ∀ v ∈ arr.val, 1 ≤ v.val ∧ v.val ≤ 20)
    (x : I64) (hx_lo : 1 ≤ x.val) (hx_hi : x.val ≤ 20) (hx : ∀ v ∈ arr.val, v ≠ x), ∀ r : I64, minimum_moves arr = ok r →
      ∀ arr2 : Slice I64, arr2.val = arr.val ++ [x] →
        ∃ r2 : I64, minimum_moves arr2 = ok r2 ∧ r2.val = r.val + 1) := by
  sorry

/-- If minimum_moves(arr) = Ok r and minimum_moves(arr2) = Ok r2, then r2 <= r+1.
  Preconditions: arr is a slice of i64 with 1 <= len(arr) <= 99, for every i with 0 <= i < len(arr), 1 <= arr[i] <= 20. Also x is an i64 with 1 <= x <= 20, p is an integer with 0 <= p <= len(arr), and arr2 is the slice obtained by inserting x at position p in arr. -/
theorem spec_11 (arr : Slice I64) (hlen_lo : 1 ≤ arr.val.length)
    (hlen_hi : arr.val.length ≤ 99) (hrange : ∀ v ∈ arr.val, 1 ≤ v.val ∧ v.val ≤ 20)
    (x : I64) (hx_lo : 1 ≤ x.val) (hx_hi : x.val ≤ 20)
    (p : ℕ) (hp : p ≤ arr.val.length) :
    ∀ r : I64, minimum_moves arr = ok r →
      ∀ arr2 : Slice I64, arr2.val = arr.val.take p ++ [x] ++ arr.val.drop p →
        ∀ r2 : I64, minimum_moves arr2 = ok r2 → r2.val ≤ r.val + 1 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (arr : Slice I64) (hlen_lo : 1 ≤ arr.val.length)
    (hlen_hi : arr.val.length ≤ 99) (hrange : ∀ v ∈ arr.val, 1 ≤ v.val ∧ v.val ≤ 20)
    (x : I64) (hx_lo : 1 ≤ x.val) (hx_hi : x.val ≤ 20)
    (p : ℕ) (hp : p ≤ arr.val.length), ∀ r : I64, minimum_moves arr = ok r →
      ∀ arr2 : Slice I64, arr2.val = arr.val.take p ++ [x] ++ arr.val.drop p →
        ∀ r2 : I64, minimum_moves arr2 = ok r2 → r2.val ≤ r.val + 1) := by
  sorry

/-- Whenever minimum_moves(arr) = Ok r, minimum_moves(L) = Ok rL, and minimum_moves(R) = Ok rR, it holds that r <= rL + rR.
  Preconditions: arr is a slice of i64 with 2 <= len(arr) <= 100, and for every i with 0 <= i < len(arr), 1 <= arr[i] <= 20. For an integer k with 0 <= k < len(arr)-1, let L = arr[0..k] and R = arr[k+1..len(arr)-1]. -/
theorem spec_12 (arr : Slice I64) (hlen_lo : 2 ≤ arr.val.length)
    (hlen_hi : arr.val.length ≤ 100) (hrange : ∀ v ∈ arr.val, 1 ≤ v.val ∧ v.val ≤ 20)
    (k : ℕ) (hk : k + 1 < arr.val.length) :
    ∀ r : I64, minimum_moves arr = ok r →
      ∀ L R : Slice I64, L.val = arr.val.take (k + 1) → R.val = arr.val.drop (k + 1) →
        ∀ rL rR : I64, minimum_moves L = ok rL → minimum_moves R = ok rR →
          r.val ≤ rL.val + rR.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (arr : Slice I64) (hlen_lo : 2 ≤ arr.val.length)
    (hlen_hi : arr.val.length ≤ 100) (hrange : ∀ v ∈ arr.val, 1 ≤ v.val ∧ v.val ≤ 20)
    (k : ℕ) (hk : k + 1 < arr.val.length), ∀ r : I64, minimum_moves arr = ok r →
      ∀ L R : Slice I64, L.val = arr.val.take (k + 1) → R.val = arr.val.drop (k + 1) →
        ∀ rL rR : I64, minimum_moves L = ok rL → minimum_moves R = ok rR →
          r.val ≤ rL.val + rR.val) := by
  sorry

/-- Whenever the function returns a result r with r > 1, there exist indices i,j with 0 <= i <= j < len(arr) such that arr[i],...,arr[j] is a palindrome, it is not the case that i = 0 and j = len(arr)-1, and if arr' is obtained from arr by deleting positions i through j and concatenating the remaining prefix and suffix, then minimum_moves(arr') = Ok (r-1).
  Preconditions: arr is a slice of i64 with 1 <= len(arr) <= 100, and for every i with 0 <= i < len(arr), 1 <= arr[i] <= 20. -/
theorem spec_13 (arr : Slice I64) (hlen_lo : 1 ≤ arr.val.length)
    (hlen_hi : arr.val.length ≤ 100) (hrange : ∀ v ∈ arr.val, 1 ≤ v.val ∧ v.val ≤ 20) :
    ∀ r : I64, minimum_moves arr = ok r → 1 < r.val →
      ∃ i j : ℕ, i ≤ j ∧ j < arr.val.length ∧
        Palindrome ((arr.val.drop i).take (j + 1 - i)) ∧
        ¬ (i = 0 ∧ j = arr.val.length - 1) ∧
        ∀ arr' : Slice I64, arr'.val = arr.val.take i ++ arr.val.drop (j + 1) →
          ∃ r' : I64, minimum_moves arr' = ok r' ∧ r'.val = r.val - 1 := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (arr : Slice I64) (hlen_lo : 1 ≤ arr.val.length)
    (hlen_hi : arr.val.length ≤ 100) (hrange : ∀ v ∈ arr.val, 1 ≤ v.val ∧ v.val ≤ 20), ∀ r : I64, minimum_moves arr = ok r → 1 < r.val →
      ∃ i j : ℕ, i ≤ j ∧ j < arr.val.length ∧
        Palindrome ((arr.val.drop i).take (j + 1 - i)) ∧
        ¬ (i = 0 ∧ j = arr.val.length - 1) ∧
        ∀ arr' : Slice I64, arr'.val = arr.val.take i ++ arr.val.drop (j + 1) →
          ∃ r' : I64, minimum_moves arr' = ok r' ∧ r'.val = r.val - 1) := by
  sorry

/-- The function returns a result r and r = 2.
  Preconditions: arr is a slice of i64 with 2 <= len(arr) <= 100, for every i with 0 <= i < len(arr), 1 <= arr[i] <= 20, arr is not a palindrome, and there exists k with 0 <= k < len(arr)-1 such that both L = arr[0..k] and R = arr[k+1..len(arr)-1] are palindromes. -/
theorem spec_14 (arr : Slice I64) (hlen_lo : 2 ≤ arr.val.length)
    (hlen_hi : arr.val.length ≤ 100) (hrange : ∀ v ∈ arr.val, 1 ≤ v.val ∧ v.val ≤ 20)
    (hnpal : ¬ Palindrome arr.val)
    (hsplit : ∃ k : ℕ, k + 1 < arr.val.length ∧ Palindrome (arr.val.take (k + 1)) ∧
      Palindrome (arr.val.drop (k + 1))) :
    ∃ r : I64, minimum_moves arr = ok r ∧ r.val = 2 := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (arr : Slice I64) (hlen_lo : 2 ≤ arr.val.length)
    (hlen_hi : arr.val.length ≤ 100) (hrange : ∀ v ∈ arr.val, 1 ≤ v.val ∧ v.val ≤ 20)
    (hnpal : ¬ Palindrome arr.val)
    (hsplit : ∃ k : ℕ, k + 1 < arr.val.length ∧ Palindrome (arr.val.take (k + 1)) ∧
      Palindrome (arr.val.drop (k + 1))), ∃ r : I64, minimum_moves arr = ok r ∧ r.val = 2) := by
  sorry

/-- If minimum_moves(arr) = Ok r and minimum_moves(arr2) = Ok r2, then r <= r2 <= r+1.
  Preconditions: arr is a slice of i64 with 1 <= len(arr) <= 99, for every i with 0 <= i < len(arr), 1 <= arr[i] <= 20. Also x is an i64 with 1 <= x <= 20, x does not occur in arr, p is an integer with 0 <= p <= len(arr), and arr2 is the slice obtained by inserting x at position p in arr, so len(arr2)=len(arr)+1 and arr2[p]=x. -/
theorem spec_15 (arr : Slice I64) (hlen_lo : 1 ≤ arr.val.length)
    (hlen_hi : arr.val.length ≤ 99) (hrange : ∀ v ∈ arr.val, 1 ≤ v.val ∧ v.val ≤ 20)
    (x : I64) (hx_lo : 1 ≤ x.val) (hx_hi : x.val ≤ 20) (hx : ∀ v ∈ arr.val, v ≠ x)
    (p : ℕ) (hp : p ≤ arr.val.length) :
    ∀ r : I64, minimum_moves arr = ok r →
      ∀ arr2 : Slice I64, arr2.val = arr.val.take p ++ [x] ++ arr.val.drop p →
        ∀ r2 : I64, minimum_moves arr2 = ok r2 → r.val ≤ r2.val ∧ r2.val ≤ r.val + 1 := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (arr : Slice I64) (hlen_lo : 1 ≤ arr.val.length)
    (hlen_hi : arr.val.length ≤ 99) (hrange : ∀ v ∈ arr.val, 1 ≤ v.val ∧ v.val ≤ 20)
    (x : I64) (hx_lo : 1 ≤ x.val) (hx_hi : x.val ≤ 20) (hx : ∀ v ∈ arr.val, v ≠ x)
    (p : ℕ) (hp : p ≤ arr.val.length), ∀ r : I64, minimum_moves arr = ok r →
      ∀ arr2 : Slice I64, arr2.val = arr.val.take p ++ [x] ++ arr.val.drop p →
        ∀ r2 : I64, minimum_moves arr2 = ok r2 → r.val ≤ r2.val ∧ r2.val ≤ r.val + 1) := by
  sorry

end AegisSpec.MinimumMoves
