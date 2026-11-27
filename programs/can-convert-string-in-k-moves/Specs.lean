import Aegis.CanConvertString.Code.Funs

/-!
# Specifications of `Aegis.CanConvertString.can_convert_string`

LeetCode problem `can-convert-string-in-k-moves`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.CanConvertString

namespace AegisSpec.CanConvertString

def byteAt (s : Slice Std.U8) (i : ℕ) : ℕ := (s.val.getD i 0#u8).val

def shift (a b : ℕ) : ℕ := (b + 26 - a) % 26

def shiftAt (s t : Slice Std.U8) (i : ℕ) : ℕ := shift (byteAt s i) (byteAt t i)

def shifts (s t : Slice Std.U8) : List ℕ :=
  List.zipWith (fun a b => shift a.val b.val) s.val t.val

def countShift (s t : Slice Std.U8) (d : ℕ) : ℕ := (shifts s t).count d

def numMoves (k : ℤ) (d : ℕ) : ℕ :=
  if (d : ℤ) ≤ k then ((k - (d : ℤ)) / 26 + 1).toNat else 0

def nonzeroCount (s t : Slice Std.U8) : ℕ := (shifts s t).countP (fun d => d != 0)

def IsPermOn (pi : ℕ → ℕ) (n : ℕ) : Prop :=
  (∀ i, i < n → pi i < n) ∧ ∀ j, j < n → ∃! i, i < n ∧ pi i = j

def permute (pi : ℕ → ℕ) (l : List Std.U8) : List Std.U8 :=
  (List.range l.length).map (fun i => l.getD (pi i) 0#u8)

/-- Let n = len(s). If len(t) != n, then whenever the function returns a result r, r = false. If len(t) = n, for each i with 0 <= i < n let d_i be the unique integer in {0,...,25} such that (s[i] - 97 + d_i) mod 26 = (t[i] - 97) mod 26. For each d in {1,...,25}, let C_d = |{i | 0 <= i < n and d_i = d}| and let A_d = |{m in Z | 1 <= m <= k and m mod 26 = d}|. Then whenever the function returns a result r, r = true if and only if C_d <= A_d for every d in {1,...,25}. Equivalently, for every d in {1,...,25} with C_d > 0, d + 26*(C_d - 1) <= k. Positions with d_i = 0 need no move and impose no condition.
  Preconditions: s and t are byte slices containing only lowercase English letters (bytes 97 through 122); 1 <= len(s), len(t) <= 10^5; 0 <= k <= 10^9. -/
theorem spec_1 (s t : Slice Std.U8) (k : Std.I64)
    (hs : ∀ x ∈ s.val, 97 ≤ x.val ∧ x.val ≤ 122)
    (ht : ∀ x ∈ t.val, 97 ≤ x.val ∧ x.val ≤ 122)
    (hsn : 1 ≤ s.val.length) (hsx : s.val.length ≤ 10 ^ 5)
    (htn : 1 ≤ t.val.length) (htx : t.val.length ≤ 10 ^ 5)
    (hk0 : 0 ≤ k.val) (hkx : k.val ≤ 10 ^ 9) :
    (s.val.length ≠ t.val.length →
        ∀ r, can_convert_string s t k = ok r → r = false) ∧
      (s.val.length = t.val.length →
        ∀ r, can_convert_string s t k = ok r →
          (r = true ↔ ∀ d, 1 ≤ d → d ≤ 25 → countShift s t d ≤ numMoves k.val d)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s t : Slice Std.U8) (k : Std.I64)
    (hs : ∀ x ∈ s.val, 97 ≤ x.val ∧ x.val ≤ 122)
    (ht : ∀ x ∈ t.val, 97 ≤ x.val ∧ x.val ≤ 122)
    (hsn : 1 ≤ s.val.length) (hsx : s.val.length ≤ 10 ^ 5)
    (htn : 1 ≤ t.val.length) (htx : t.val.length ≤ 10 ^ 5)
    (hk0 : 0 ≤ k.val) (hkx : k.val ≤ 10 ^ 9), (s.val.length ≠ t.val.length →
        ∀ r, can_convert_string s t k = ok r → r = false) ∧
      (s.val.length = t.val.length →
        ∀ r, can_convert_string s t k = ok r →
          (r = true ↔ ∀ d, 1 ≤ d → d ≤ 25 → countShift s t d ≤ numMoves k.val d))) := by
  sorry

/-- For every s, t, and k satisfying the preconditions, the function returns a result r; it does not fail, panic, or overflow.
  Preconditions: s and t are byte slices containing only lowercase English letters (bytes 97 through 122); 1 <= len(s), len(t) <= 10^5; 0 <= k <= 10^9. -/
theorem spec_2 (s t : Slice Std.U8) (k : Std.I64)
    (hs : ∀ x ∈ s.val, 97 ≤ x.val ∧ x.val ≤ 122)
    (ht : ∀ x ∈ t.val, 97 ≤ x.val ∧ x.val ≤ 122)
    (hsn : 1 ≤ s.val.length) (hsx : s.val.length ≤ 10 ^ 5)
    (htn : 1 ≤ t.val.length) (htx : t.val.length ≤ 10 ^ 5)
    (hk0 : 0 ≤ k.val) (hkx : k.val ≤ 10 ^ 9) :
    ∃ r : Bool, can_convert_string s t k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s t : Slice Std.U8) (k : Std.I64)
    (hs : ∀ x ∈ s.val, 97 ≤ x.val ∧ x.val ≤ 122)
    (ht : ∀ x ∈ t.val, 97 ≤ x.val ∧ x.val ≤ 122)
    (hsn : 1 ≤ s.val.length) (hsx : s.val.length ≤ 10 ^ 5)
    (htn : 1 ≤ t.val.length) (htx : t.val.length ≤ 10 ^ 5)
    (hk0 : 0 ≤ k.val) (hkx : k.val ≤ 10 ^ 9), ∃ r : Bool, can_convert_string s t k = ok r) := by
  sorry

/-- If len(s) != len(t), then the function returns false.
  Preconditions: s and t are byte slices containing only lowercase English letters (bytes 97 through 122); 1 <= len(s), len(t) <= 10^5; 0 <= k <= 10^9. -/
theorem spec_3 (s t : Slice Std.U8) (k : Std.I64)
    (hs : ∀ x ∈ s.val, 97 ≤ x.val ∧ x.val ≤ 122)
    (ht : ∀ x ∈ t.val, 97 ≤ x.val ∧ x.val ≤ 122)
    (hsn : 1 ≤ s.val.length) (hsx : s.val.length ≤ 10 ^ 5)
    (htn : 1 ≤ t.val.length) (htx : t.val.length ≤ 10 ^ 5)
    (hk0 : 0 ≤ k.val) (hkx : k.val ≤ 10 ^ 9)
    (hlen : s.val.length ≠ t.val.length) :
    can_convert_string s t k = ok false := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s t : Slice Std.U8) (k : Std.I64)
    (hs : ∀ x ∈ s.val, 97 ≤ x.val ∧ x.val ≤ 122)
    (ht : ∀ x ∈ t.val, 97 ≤ x.val ∧ x.val ≤ 122)
    (hsn : 1 ≤ s.val.length) (hsx : s.val.length ≤ 10 ^ 5)
    (htn : 1 ≤ t.val.length) (htx : t.val.length ≤ 10 ^ 5)
    (hk0 : 0 ≤ k.val) (hkx : k.val ≤ 10 ^ 9)
    (hlen : s.val.length ≠ t.val.length), can_convert_string s t k = ok false) := by
  sorry

/-- The function returns true if and only if len(s) = len(t) and s[i] = t[i] for every i with 0 <= i < len(s).
  Preconditions: s and t are byte slices containing only lowercase English letters (bytes 97 through 122); 1 <= len(s), len(t) <= 10^5; k = 0. -/
theorem spec_4 (s t : Slice Std.U8) (k : Std.I64)
    (hs : ∀ x ∈ s.val, 97 ≤ x.val ∧ x.val ≤ 122)
    (ht : ∀ x ∈ t.val, 97 ≤ x.val ∧ x.val ≤ 122)
    (hsn : 1 ≤ s.val.length) (hsx : s.val.length ≤ 10 ^ 5)
    (htn : 1 ≤ t.val.length) (htx : t.val.length ≤ 10 ^ 5)
    (hk0 : 0 ≤ k.val) (hkx : k.val ≤ 10 ^ 9)
    (hk : k.val = 0) :
    (can_convert_string s t k = ok true ↔
      s.val.length = t.val.length ∧
        ∀ i, i < s.val.length → byteAt s i = byteAt t i) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s t : Slice Std.U8) (k : Std.I64)
    (hs : ∀ x ∈ s.val, 97 ≤ x.val ∧ x.val ≤ 122)
    (ht : ∀ x ∈ t.val, 97 ≤ x.val ∧ x.val ≤ 122)
    (hsn : 1 ≤ s.val.length) (hsx : s.val.length ≤ 10 ^ 5)
    (htn : 1 ≤ t.val.length) (htx : t.val.length ≤ 10 ^ 5)
    (hk0 : 0 ≤ k.val) (hkx : k.val ≤ 10 ^ 9)
    (hk : k.val = 0), (can_convert_string s t k = ok true ↔
      s.val.length = t.val.length ∧
        ∀ i, i < s.val.length → byteAt s i = byteAt t i)) := by
  sorry

/-- Let d be the unique integer in {0,...,25} such that (s[0] - 97 + d) mod 26 = (t[0] - 97) mod 26. The function returns true if and only if d = 0 or k >= d.
  Preconditions: s and t are byte slices containing only lowercase English letters (bytes 97 through 122); len(s) = len(t) = 1; 0 <= k <= 10^9. -/
theorem spec_5 (s t : Slice Std.U8) (k : Std.I64)
    (hs : ∀ x ∈ s.val, 97 ≤ x.val ∧ x.val ≤ 122)
    (ht : ∀ x ∈ t.val, 97 ≤ x.val ∧ x.val ≤ 122)
    (hs1 : s.val.length = 1) (ht1 : t.val.length = 1)
    (hk0 : 0 ≤ k.val) (hkx : k.val ≤ 10 ^ 9) :
    (can_convert_string s t k = ok true ↔
      shiftAt s t 0 = 0 ∨ (shiftAt s t 0 : ℤ) ≤ k.val) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s t : Slice Std.U8) (k : Std.I64)
    (hs : ∀ x ∈ s.val, 97 ≤ x.val ∧ x.val ≤ 122)
    (ht : ∀ x ∈ t.val, 97 ≤ x.val ∧ x.val ≤ 122)
    (hs1 : s.val.length = 1) (ht1 : t.val.length = 1)
    (hk0 : 0 ≤ k.val) (hkx : k.val ≤ 10 ^ 9), (can_convert_string s t k = ok true ↔
      shiftAt s t 0 = 0 ∨ (shiftAt s t 0 : ℤ) ≤ k.val)) := by
  sorry

/-- For each i with 0 <= i < n let d_i be the unique integer in {0,...,25} such that (s[i] - 97 + d_i) mod 26 = (t[i] - 97) mod 26. The function returns true if and only if the nonzero values among d_0,...,d_{n-1} are pairwise distinct and each is at most k.
  Preconditions: s and t are byte slices containing only lowercase English letters (bytes 97 through 122); len(s) = len(t) = n with 1 <= n <= 10^5; 0 <= k < 26. -/
theorem spec_6 (s t : Slice Std.U8) (k : Std.I64)
    (hs : ∀ x ∈ s.val, 97 ≤ x.val ∧ x.val ≤ 122)
    (ht : ∀ x ∈ t.val, 97 ≤ x.val ∧ x.val ≤ 122)
    (hlen : s.val.length = t.val.length)
    (hsn : 1 ≤ s.val.length) (hsx : s.val.length ≤ 10 ^ 5)
    (hk0 : 0 ≤ k.val) (hk26 : k.val < 26) :
    (can_convert_string s t k = ok true ↔
      (∀ i j, i < s.val.length → j < s.val.length →
          shiftAt s t i = shiftAt s t j → shiftAt s t i ≠ 0 → i = j) ∧
        (∀ i, i < s.val.length → shiftAt s t i ≠ 0 → (shiftAt s t i : ℤ) ≤ k.val)) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s t : Slice Std.U8) (k : Std.I64)
    (hs : ∀ x ∈ s.val, 97 ≤ x.val ∧ x.val ≤ 122)
    (ht : ∀ x ∈ t.val, 97 ≤ x.val ∧ x.val ≤ 122)
    (hlen : s.val.length = t.val.length)
    (hsn : 1 ≤ s.val.length) (hsx : s.val.length ≤ 10 ^ 5)
    (hk0 : 0 ≤ k.val) (hk26 : k.val < 26), (can_convert_string s t k = ok true ↔
      (∀ i j, i < s.val.length → j < s.val.length →
          shiftAt s t i = shiftAt s t j → shiftAt s t i ≠ 0 → i = j) ∧
        (∀ i, i < s.val.length → shiftAt s t i ≠ 0 → (shiftAt s t i : ℤ) ≤ k.val))) := by
  sorry

/-- If the function returns true for (s, t, k1), then the function returns true for (s, t, k2).
  Preconditions: s and t are byte slices containing only lowercase English letters (bytes 97 through 122); 1 <= len(s), len(t) <= 10^5; 0 <= k1 <= k2 <= 10^9. -/
theorem spec_7 (s t : Slice Std.U8) (k1 k2 : Std.I64)
    (hs : ∀ x ∈ s.val, 97 ≤ x.val ∧ x.val ≤ 122)
    (ht : ∀ x ∈ t.val, 97 ≤ x.val ∧ x.val ≤ 122)
    (hsn : 1 ≤ s.val.length) (hsx : s.val.length ≤ 10 ^ 5)
    (htn : 1 ≤ t.val.length) (htx : t.val.length ≤ 10 ^ 5)
    (hk10 : 0 ≤ k1.val) (hk1x : k1.val ≤ 10 ^ 9)
    (hk20 : 0 ≤ k2.val) (hk2x : k2.val ≤ 10 ^ 9)
    (hkk : k1.val ≤ k2.val) :
    can_convert_string s t k1 = ok true → can_convert_string s t k2 = ok true := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s t : Slice Std.U8) (k1 k2 : Std.I64)
    (hs : ∀ x ∈ s.val, 97 ≤ x.val ∧ x.val ≤ 122)
    (ht : ∀ x ∈ t.val, 97 ≤ x.val ∧ x.val ≤ 122)
    (hsn : 1 ≤ s.val.length) (hsx : s.val.length ≤ 10 ^ 5)
    (htn : 1 ≤ t.val.length) (htx : t.val.length ≤ 10 ^ 5)
    (hk10 : 0 ≤ k1.val) (hk1x : k1.val ≤ 10 ^ 9)
    (hk20 : 0 ≤ k2.val) (hk2x : k2.val ≤ 10 ^ 9)
    (hkk : k1.val ≤ k2.val), can_convert_string s t k1 = ok true → can_convert_string s t k2 = ok true) := by
  sorry

/-- Let s' and t' be the byte slices defined by s'[i] = s[pi(i)] and t'[i] = t[pi(i)] for every i with 0 <= i < n. Then the function returns the same boolean on (s, t, k) and on (s', t', k).
  Preconditions: s and t are byte slices containing only lowercase English letters (bytes 97 through 122); len(s) = len(t) = n with 1 <= n <= 10^5; 0 <= k <= 10^9; pi is a permutation of {0,...,n-1}. -/
theorem spec_8 (s t s' t' : Slice Std.U8) (k : Std.I64) (n : ℕ) (pi : ℕ → ℕ)
    (hs : ∀ x ∈ s.val, 97 ≤ x.val ∧ x.val ≤ 122)
    (ht : ∀ x ∈ t.val, 97 ≤ x.val ∧ x.val ≤ 122)
    (hsn : s.val.length = n) (htn : t.val.length = n)
    (hn : 1 ≤ n) (hnx : n ≤ 10 ^ 5)
    (hk0 : 0 ≤ k.val) (hkx : k.val ≤ 10 ^ 9)
    (hpi : IsPermOn pi n)
    (hsp : s'.val = permute pi s.val) (htp : t'.val = permute pi t.val) :
    can_convert_string s t k = can_convert_string s' t' k := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s t s' t' : Slice Std.U8) (k : Std.I64) (n : ℕ) (pi : ℕ → ℕ)
    (hs : ∀ x ∈ s.val, 97 ≤ x.val ∧ x.val ≤ 122)
    (ht : ∀ x ∈ t.val, 97 ≤ x.val ∧ x.val ≤ 122)
    (hsn : s.val.length = n) (htn : t.val.length = n)
    (hn : 1 ≤ n) (hnx : n ≤ 10 ^ 5)
    (hk0 : 0 ≤ k.val) (hkx : k.val ≤ 10 ^ 9)
    (hpi : IsPermOn pi n)
    (hsp : s'.val = permute pi s.val) (htp : t'.val = permute pi t.val), can_convert_string s t k = can_convert_string s' t' k) := by
  sorry

/-- The function returns true.
  Preconditions: s and t are byte slices containing only lowercase English letters (bytes 97 through 122); len(s) = len(t) = n with 1 <= n <= 10^5; 0 <= k <= 10^9; k >= 26*n - 1. -/
theorem spec_9 (s t : Slice Std.U8) (k : Std.I64)
    (hs : ∀ x ∈ s.val, 97 ≤ x.val ∧ x.val ≤ 122)
    (ht : ∀ x ∈ t.val, 97 ≤ x.val ∧ x.val ≤ 122)
    (hlen : s.val.length = t.val.length)
    (hsn : 1 ≤ s.val.length) (hsx : s.val.length ≤ 10 ^ 5)
    (hk0 : 0 ≤ k.val) (hkx : k.val ≤ 10 ^ 9)
    (hk : 26 * (s.val.length : ℤ) - 1 ≤ k.val) :
    can_convert_string s t k = ok true := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s t : Slice Std.U8) (k : Std.I64)
    (hs : ∀ x ∈ s.val, 97 ≤ x.val ∧ x.val ≤ 122)
    (ht : ∀ x ∈ t.val, 97 ≤ x.val ∧ x.val ≤ 122)
    (hlen : s.val.length = t.val.length)
    (hsn : 1 ≤ s.val.length) (hsx : s.val.length ≤ 10 ^ 5)
    (hk0 : 0 ≤ k.val) (hkx : k.val ≤ 10 ^ 9)
    (hk : 26 * (s.val.length : ℤ) - 1 ≤ k.val), can_convert_string s t k = ok true) := by
  sorry

/-- If the function returns true, then len(s) = len(t) = n and, for every i with 0 <= i < n, if d_i > 0 then d_i <= k, where d_i is the unique integer in {0,...,25} such that (s[i] - 97 + d_i) mod 26 = (t[i] - 97) mod 26.
  Preconditions: s and t are byte slices containing only lowercase English letters (bytes 97 through 122); 1 <= len(s), len(t) <= 10^5; 0 <= k <= 10^9. -/
theorem spec_10 (s t : Slice Std.U8) (k : Std.I64)
    (hs : ∀ x ∈ s.val, 97 ≤ x.val ∧ x.val ≤ 122)
    (ht : ∀ x ∈ t.val, 97 ≤ x.val ∧ x.val ≤ 122)
    (hsn : 1 ≤ s.val.length) (hsx : s.val.length ≤ 10 ^ 5)
    (htn : 1 ≤ t.val.length) (htx : t.val.length ≤ 10 ^ 5)
    (hk0 : 0 ≤ k.val) (hkx : k.val ≤ 10 ^ 9) :
    can_convert_string s t k = ok true →
      s.val.length = t.val.length ∧
        ∀ i, i < s.val.length → shiftAt s t i ≠ 0 → (shiftAt s t i : ℤ) ≤ k.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s t : Slice Std.U8) (k : Std.I64)
    (hs : ∀ x ∈ s.val, 97 ≤ x.val ∧ x.val ≤ 122)
    (ht : ∀ x ∈ t.val, 97 ≤ x.val ∧ x.val ≤ 122)
    (hsn : 1 ≤ s.val.length) (hsx : s.val.length ≤ 10 ^ 5)
    (htn : 1 ≤ t.val.length) (htx : t.val.length ≤ 10 ^ 5)
    (hk0 : 0 ≤ k.val) (hkx : k.val ≤ 10 ^ 9), can_convert_string s t k = ok true →
      s.val.length = t.val.length ∧
        ∀ i, i < s.val.length → shiftAt s t i ≠ 0 → (shiftAt s t i : ℤ) ≤ k.val) := by
  sorry

/-- If the function returns true, then len(s) = len(t) = n and the number of indices i with 0 <= i < n and d_i > 0 is at most k, where d_i is the unique integer in {0,...,25} such that (s[i] - 97 + d_i) mod 26 = (t[i] - 97) mod 26.
  Preconditions: s and t are byte slices containing only lowercase English letters (bytes 97 through 122); 1 <= len(s), len(t) <= 10^5; 0 <= k <= 10^9. -/
theorem spec_11 (s t : Slice Std.U8) (k : Std.I64)
    (hs : ∀ x ∈ s.val, 97 ≤ x.val ∧ x.val ≤ 122)
    (ht : ∀ x ∈ t.val, 97 ≤ x.val ∧ x.val ≤ 122)
    (hsn : 1 ≤ s.val.length) (hsx : s.val.length ≤ 10 ^ 5)
    (htn : 1 ≤ t.val.length) (htx : t.val.length ≤ 10 ^ 5)
    (hk0 : 0 ≤ k.val) (hkx : k.val ≤ 10 ^ 9) :
    can_convert_string s t k = ok true →
      s.val.length = t.val.length ∧ (nonzeroCount s t : ℤ) ≤ k.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s t : Slice Std.U8) (k : Std.I64)
    (hs : ∀ x ∈ s.val, 97 ≤ x.val ∧ x.val ≤ 122)
    (ht : ∀ x ∈ t.val, 97 ≤ x.val ∧ x.val ≤ 122)
    (hsn : 1 ≤ s.val.length) (hsx : s.val.length ≤ 10 ^ 5)
    (htn : 1 ≤ t.val.length) (htx : t.val.length ≤ 10 ^ 5)
    (hk0 : 0 ≤ k.val) (hkx : k.val ≤ 10 ^ 9), can_convert_string s t k = ok true →
      s.val.length = t.val.length ∧ (nonzeroCount s t : ℤ) ≤ k.val) := by
  sorry

/-- For each i with 0 <= i < n let d_i be the unique integer in {0,...,25} such that (s[i] - 97 + d_i) mod 26 = (t[i] - 97) mod 26. If every nonzero d_i satisfies d_i <= k and no two indices i != j have the same nonzero d_i, then the function returns true.
  Preconditions: s and t are byte slices containing only lowercase English letters (bytes 97 through 122); len(s) = len(t) = n with 1 <= n <= 10^5; 0 <= k <= 10^9. -/
theorem spec_12 (s t : Slice Std.U8) (k : Std.I64)
    (hs : ∀ x ∈ s.val, 97 ≤ x.val ∧ x.val ≤ 122)
    (ht : ∀ x ∈ t.val, 97 ≤ x.val ∧ x.val ≤ 122)
    (hlen : s.val.length = t.val.length)
    (hsn : 1 ≤ s.val.length) (hsx : s.val.length ≤ 10 ^ 5)
    (hk0 : 0 ≤ k.val) (hkx : k.val ≤ 10 ^ 9)
    (hsmall : ∀ i, i < s.val.length → shiftAt s t i ≠ 0 → (shiftAt s t i : ℤ) ≤ k.val)
    (hdistinct : ∀ i j, i < s.val.length → j < s.val.length →
      shiftAt s t i = shiftAt s t j → shiftAt s t i ≠ 0 → i = j) :
    can_convert_string s t k = ok true := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (s t : Slice Std.U8) (k : Std.I64)
    (hs : ∀ x ∈ s.val, 97 ≤ x.val ∧ x.val ≤ 122)
    (ht : ∀ x ∈ t.val, 97 ≤ x.val ∧ x.val ≤ 122)
    (hlen : s.val.length = t.val.length)
    (hsn : 1 ≤ s.val.length) (hsx : s.val.length ≤ 10 ^ 5)
    (hk0 : 0 ≤ k.val) (hkx : k.val ≤ 10 ^ 9)
    (hsmall : ∀ i, i < s.val.length → shiftAt s t i ≠ 0 → (shiftAt s t i : ℤ) ≤ k.val)
    (hdistinct : ∀ i j, i < s.val.length → j < s.val.length →
      shiftAt s t i = shiftAt s t j → shiftAt s t i ≠ 0 → i = j), can_convert_string s t k = ok true) := by
  sorry

/-- Let c be the number of indices i with 0 <= i < n and d_i = d. The function returns true if and only if c = 0 or (k >= d and c <= floor((k - d)/26) + 1).
  Preconditions: s and t are byte slices containing only lowercase English letters (bytes 97 through 122); len(s) = len(t) = n with 1 <= n <= 10^5; 0 <= k <= 10^9; d is an integer with 1 <= d <= 25; for every i with 0 <= i < n, the unique d_i in {0,...,25} satisfying (s[i] - 97 + d_i) mod 26 = (t[i] - 97) mod 26 belongs to {0, d}. -/
theorem spec_13 (s t : Slice Std.U8) (k : Std.I64) (d : ℕ)
    (hs : ∀ x ∈ s.val, 97 ≤ x.val ∧ x.val ≤ 122)
    (ht : ∀ x ∈ t.val, 97 ≤ x.val ∧ x.val ≤ 122)
    (hlen : s.val.length = t.val.length)
    (hsn : 1 ≤ s.val.length) (hsx : s.val.length ≤ 10 ^ 5)
    (hk0 : 0 ≤ k.val) (hkx : k.val ≤ 10 ^ 9)
    (hd1 : 1 ≤ d) (hd25 : d ≤ 25)
    (hd : ∀ i, i < s.val.length → shiftAt s t i = 0 ∨ shiftAt s t i = d) :
    (can_convert_string s t k = ok true ↔
      countShift s t d = 0 ∨
        ((d : ℤ) ≤ k.val ∧
          (countShift s t d : ℤ) ≤ (k.val - (d : ℤ)) / 26 + 1)) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (s t : Slice Std.U8) (k : Std.I64) (d : ℕ)
    (hs : ∀ x ∈ s.val, 97 ≤ x.val ∧ x.val ≤ 122)
    (ht : ∀ x ∈ t.val, 97 ≤ x.val ∧ x.val ≤ 122)
    (hlen : s.val.length = t.val.length)
    (hsn : 1 ≤ s.val.length) (hsx : s.val.length ≤ 10 ^ 5)
    (hk0 : 0 ≤ k.val) (hkx : k.val ≤ 10 ^ 9)
    (hd1 : 1 ≤ d) (hd25 : d ≤ 25)
    (hd : ∀ i, i < s.val.length → shiftAt s t i = 0 ∨ shiftAt s t i = d), (can_convert_string s t k = ok true ↔
      countShift s t d = 0 ∨
        ((d : ℤ) ≤ k.val ∧
          (countShift s t d : ℤ) ≤ (k.val - (d : ℤ)) / 26 + 1))) := by
  sorry

/-- For each i with 0 <= i < n let d_i be the unique integer in {0,...,25} such that (s[i] - 97 + d_i) mod 26 = (t[i] - 97) mod 26. For each d in {1,...,25} let C_d be the number of i with d_i = d. For every d in {1,...,25} with C_d > 0, if k < d + 26*(C_d - 1), then the function returns false.
  Preconditions: s and t are byte slices containing only lowercase English letters (bytes 97 through 122); len(s) = len(t) = n with 1 <= n <= 10^5; 0 <= k <= 10^9. -/
theorem spec_14 (s t : Slice Std.U8) (k : Std.I64)
    (hs : ∀ x ∈ s.val, 97 ≤ x.val ∧ x.val ≤ 122)
    (ht : ∀ x ∈ t.val, 97 ≤ x.val ∧ x.val ≤ 122)
    (hlen : s.val.length = t.val.length)
    (hsn : 1 ≤ s.val.length) (hsx : s.val.length ≤ 10 ^ 5)
    (hk0 : 0 ≤ k.val) (hkx : k.val ≤ 10 ^ 9) :
    ∀ d, 1 ≤ d → d ≤ 25 → 0 < countShift s t d →
      k.val < (d : ℤ) + 26 * ((countShift s t d : ℤ) - 1) →
        can_convert_string s t k = ok false := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (s t : Slice Std.U8) (k : Std.I64)
    (hs : ∀ x ∈ s.val, 97 ≤ x.val ∧ x.val ≤ 122)
    (ht : ∀ x ∈ t.val, 97 ≤ x.val ∧ x.val ≤ 122)
    (hlen : s.val.length = t.val.length)
    (hsn : 1 ≤ s.val.length) (hsx : s.val.length ≤ 10 ^ 5)
    (hk0 : 0 ≤ k.val) (hkx : k.val ≤ 10 ^ 9), ∀ d, 1 ≤ d → d ≤ 25 → 0 < countShift s t d →
      k.val < (d : ℤ) + 26 * ((countShift s t d : ℤ) - 1) →
        can_convert_string s t k = ok false) := by
  sorry

end AegisSpec.CanConvertString
