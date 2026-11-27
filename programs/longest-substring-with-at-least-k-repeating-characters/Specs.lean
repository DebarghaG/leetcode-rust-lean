import Aegis.LongestSubstring.Code.Funs

/-!
# Specifications of `Aegis.LongestSubstring.longest_substring`

LeetCode problem `longest-substring-with-at-least-k-repeating-characters`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.LongestSubstring

  namespace AegisSpec.LongestSubstring

  def bytesOf (s : Slice U8) : List Nat := s.val.map (fun b => b.val)

  def seg (s : Slice U8) (i j : Nat) : List Nat := (bytesOf s).drop i |>.take (j - i)

  def segBytes (s : Slice U8) (i j : Nat) : List U8 := (s.val.drop i).take (j - i)

  def occ (c : Nat) (l : List Nat) : Nat := l.count c

  def KValid (s : Slice U8) (k : Nat) (i j : Nat) : Prop :=
    ∀ c : Nat, occ c (seg s i j) = 0 ∨ k ≤ occ c (seg s i j)

  noncomputable def validLengths (s : Slice U8) (k : Nat) : Finset Nat := by
    classical
    exact
      insert 0
        (((Finset.product (Finset.range (s.val.length + 1))
              (Finset.range (s.val.length + 1))).filter
            (fun p => p.1 < p.2 ∧ KValid s k p.1 p.2)).image (fun p => p.2 - p.1))

  noncomputable def bestLen (s : Slice U8) (k : Nat) : Nat := (validLengths s k).sup id

  def HasValidInterval (s : Slice U8) (k : Nat) : Prop :=
    ∃ i j : Nat, i < j ∧ j ≤ s.val.length ∧ KValid s k i j

  /-- The function returns a result r and r = max({0} union {j - i | 0 <= i < j <= len(s) and the interval s[i..j) is k-valid}). An interval s[i..j) is k-valid when, for every byte c, the number of indices t with i <= t < j and s[t] = c is either 0 or at least k. Equivalently, no character occurs in s[i..j) with a positive frequency smaller than k.
    Preconditions: 0 <= len(s) <= 10000; every byte of s is an ASCII lowercase letter, i.e. 97 <= s[i] <= 122 for every 0 <= i < len(s); and 1 <= k <= 100000. -/
  theorem spec_1 (s : Slice U8) (k : I64)
      (hlen1 : 0 ≤ s.val.length) (hlen2 : s.val.length ≤ 10000)
      (hbytes : ∀ (i : Nat) (hi : i < s.val.length),
        97 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 122)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000) :
      ∃ r : I64, longest_substring s k = ok r ∧ r.val = (bestLen s k.val.toNat : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s : Slice U8) (k : I64)
        (hlen1 : 0 ≤ s.val.length) (hlen2 : s.val.length ≤ 10000)
        (hbytes : ∀ (i : Nat) (hi : i < s.val.length),
          97 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 122)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000), ∃ r : I64, longest_substring s k = ok r ∧ r.val = (bestLen s k.val.toNat : Int)) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r; it does not fail by arithmetic overflow, panic, or out-of-bounds access.
    Preconditions: 0 <= len(s) <= 10000; every byte of s is an ASCII lowercase letter, i.e. 97 <= s[i] <= 122 for every 0 <= i < len(s); and 1 <= k <= 100000. -/
  theorem spec_2 (s : Slice U8) (k : I64)
      (hlen1 : 0 ≤ s.val.length) (hlen2 : s.val.length ≤ 10000)
      (hbytes : ∀ (i : Nat) (hi : i < s.val.length),
        97 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 122)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000) :
      ∃ r : I64, longest_substring s k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s : Slice U8) (k : I64)
        (hlen1 : 0 ≤ s.val.length) (hlen2 : s.val.length ≤ 10000)
        (hbytes : ∀ (i : Nat) (hi : i < s.val.length),
          97 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 122)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000), ∃ r : I64, longest_substring s k = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r <= len(s).
    Preconditions: 0 <= len(s) <= 10000; every byte of s is an ASCII lowercase letter, i.e. 97 <= s[i] <= 122 for every 0 <= i < len(s); and 1 <= k <= 100000. -/
  theorem spec_3 (s : Slice U8) (k : I64)
      (hlen1 : 0 ≤ s.val.length) (hlen2 : s.val.length ≤ 10000)
      (hbytes : ∀ (i : Nat) (hi : i < s.val.length),
        97 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 122)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000) :
      ∀ r : I64, longest_substring s k = ok r → 0 ≤ r.val ∧ r.val ≤ (s.val.length : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s : Slice U8) (k : I64)
        (hlen1 : 0 ≤ s.val.length) (hlen2 : s.val.length ≤ 10000)
        (hbytes : ∀ (i : Nat) (hi : i < s.val.length),
          97 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 122)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000), ∀ r : I64, longest_substring s k = ok r → 0 ≤ r.val ∧ r.val ≤ (s.val.length : Int)) := by
    sorry

  /-- Whenever the function returns a result r and r > 0, then r >= k.
    Preconditions: 0 <= len(s) <= 10000; every byte of s is an ASCII lowercase letter, i.e. 97 <= s[i] <= 122 for every 0 <= i < len(s); and 1 <= k <= 100000. -/
  theorem spec_4 (s : Slice U8) (k : I64)
      (hlen1 : 0 ≤ s.val.length) (hlen2 : s.val.length ≤ 10000)
      (hbytes : ∀ (i : Nat) (hi : i < s.val.length),
        97 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 122)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000) :
      ∀ r : I64, longest_substring s k = ok r → 0 < r.val → k.val ≤ r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s : Slice U8) (k : I64)
        (hlen1 : 0 ≤ s.val.length) (hlen2 : s.val.length ≤ 10000)
        (hbytes : ∀ (i : Nat) (hi : i < s.val.length),
          97 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 122)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000), ∀ r : I64, longest_substring s k = ok r → 0 < r.val → k.val ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r with r > 0, there exist indices i and j such that 0 <= i < j <= len(s), j - i = r, and s[i..j) is k-valid, meaning that for every byte c, the number of indices t with i <= t < j and s[t] = c is either 0 or at least k.
    Preconditions: 0 <= len(s) <= 10000; every byte of s is an ASCII lowercase letter, i.e. 97 <= s[i] <= 122 for every 0 <= i < len(s); and 1 <= k <= 100000. -/
  theorem spec_5 (s : Slice U8) (k : I64)
      (hlen1 : 0 ≤ s.val.length) (hlen2 : s.val.length ≤ 10000)
      (hbytes : ∀ (i : Nat) (hi : i < s.val.length),
        97 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 122)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000) :
      ∀ r : I64, longest_substring s k = ok r → 0 < r.val →
        ∃ i j : Nat, i < j ∧ j ≤ s.val.length ∧ r.val = ((j - i : Nat) : Int) ∧
          KValid s k.val.toNat i j := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s : Slice U8) (k : I64)
        (hlen1 : 0 ≤ s.val.length) (hlen2 : s.val.length ≤ 10000)
        (hbytes : ∀ (i : Nat) (hi : i < s.val.length),
          97 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 122)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000), ∀ r : I64, longest_substring s k = ok r → 0 < r.val →
          ∃ i j : Nat, i < j ∧ j ≤ s.val.length ∧ r.val = ((j - i : Nat) : Int) ∧
            KValid s k.val.toNat i j) := by
    sorry

  /-- Whenever the function returns a result r, for every interval [i,j) with 0 <= i < j <= len(s), if every byte occurring in s[i..j) occurs at least k times in that interval, then j - i <= r.
    Preconditions: 0 <= len(s) <= 10000; every byte of s is an ASCII lowercase letter, i.e. 97 <= s[i] <= 122 for every 0 <= i < len(s); and 1 <= k <= 100000. -/
  theorem spec_6 (s : Slice U8) (k : I64)
      (hlen1 : 0 ≤ s.val.length) (hlen2 : s.val.length ≤ 10000)
      (hbytes : ∀ (i : Nat) (hi : i < s.val.length),
        97 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 122)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000) :
      ∀ r : I64, longest_substring s k = ok r →
        ∀ i j : Nat, i < j → j ≤ s.val.length → KValid s k.val.toNat i j →
          ((j - i : Nat) : Int) ≤ r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s : Slice U8) (k : I64)
        (hlen1 : 0 ≤ s.val.length) (hlen2 : s.val.length ≤ 10000)
        (hbytes : ∀ (i : Nat) (hi : i < s.val.length),
          97 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 122)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000), ∀ r : I64, longest_substring s k = ok r →
          ∀ i j : Nat, i < j → j ≤ s.val.length → KValid s k.val.toNat i j →
            ((j - i : Nat) : Int) ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 if and only if there is no interval [i,j) with 0 <= i < j <= len(s) such that every byte occurring in s[i..j) occurs at least k times in that interval.
    Preconditions: 0 <= len(s) <= 10000; every byte of s is an ASCII lowercase letter, i.e. 97 <= s[i] <= 122 for every 0 <= i < len(s); and 1 <= k <= 100000. -/
  theorem spec_7 (s : Slice U8) (k : I64)
      (hlen1 : 0 ≤ s.val.length) (hlen2 : s.val.length ≤ 10000)
      (hbytes : ∀ (i : Nat) (hi : i < s.val.length),
        97 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 122)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000) :
      ∀ r : I64, longest_substring s k = ok r →
        (r.val = 0 ↔ ¬ HasValidInterval s k.val.toNat) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s : Slice U8) (k : I64)
        (hlen1 : 0 ≤ s.val.length) (hlen2 : s.val.length ≤ 10000)
        (hbytes : ∀ (i : Nat) (hi : i < s.val.length),
          97 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 122)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000), ∀ r : I64, longest_substring s k = ok r →
          (r.val = 0 ↔ ¬ HasValidInterval s k.val.toNat)) := by
    sorry

  /-- The function returns a result r and r = len(s).
    Preconditions: 0 <= len(s) <= 10000; every byte of s is an ASCII lowercase letter, i.e. 97 <= s[i] <= 122 for every 0 <= i < len(s); 1 <= k <= 100000; and k = 1. -/
  theorem spec_8 (s : Slice U8) (k : I64)
      (hlen1 : 0 ≤ s.val.length) (hlen2 : s.val.length ≤ 10000)
      (hbytes : ∀ (i : Nat) (hi : i < s.val.length),
        97 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 122)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000) (hk3 : k.val = 1) :
      ∃ r : I64, longest_substring s k = ok r ∧ r.val = (s.val.length : Int) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s : Slice U8) (k : I64)
        (hlen1 : 0 ≤ s.val.length) (hlen2 : s.val.length ≤ 10000)
        (hbytes : ∀ (i : Nat) (hi : i < s.val.length),
          97 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 122)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000) (hk3 : k.val = 1), ∃ r : I64, longest_substring s k = ok r ∧ r.val = (s.val.length : Int)) := by
    sorry

  /-- The function returns a result r and r = 0.
    Preconditions: 0 <= len(s) <= 10000; every byte of s is an ASCII lowercase letter, i.e. 97 <= s[i] <= 122 for every 0 <= i < len(s); 1 <= k <= 100000; and k > len(s). -/
  theorem spec_9 (s : Slice U8) (k : I64)
      (hlen1 : 0 ≤ s.val.length) (hlen2 : s.val.length ≤ 10000)
      (hbytes : ∀ (i : Nat) (hi : i < s.val.length),
        97 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 122)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000) (hk3 : (s.val.length : Int) < k.val) :
      ∃ r : I64, longest_substring s k = ok r ∧ r.val = 0 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s : Slice U8) (k : I64)
        (hlen1 : 0 ≤ s.val.length) (hlen2 : s.val.length ≤ 10000)
        (hbytes : ∀ (i : Nat) (hi : i < s.val.length),
          97 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 122)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000) (hk3 : (s.val.length : Int) < k.val), ∃ r : I64, longest_substring s k = ok r ∧ r.val = 0) := by
    sorry

  /-- Whenever the function returns a result r, if r = len(s), then the whole string s is k-valid, i.e. for every byte c, the number of indices t with 0 <= t < len(s) and s[t] = c is either 0 or at least k.
    Preconditions: 0 <= len(s) <= 10000; every byte of s is an ASCII lowercase letter, i.e. 97 <= s[i] <= 122 for every 0 <= i < len(s); and 1 <= k <= 100000. -/
  theorem spec_10 (s : Slice U8) (k : I64)
      (hlen1 : 0 ≤ s.val.length) (hlen2 : s.val.length ≤ 10000)
      (hbytes : ∀ (i : Nat) (hi : i < s.val.length),
        97 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 122)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000) :
      ∀ r : I64, longest_substring s k = ok r → r.val = (s.val.length : Int) →
        KValid s k.val.toNat 0 s.val.length := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (s : Slice U8) (k : I64)
        (hlen1 : 0 ≤ s.val.length) (hlen2 : s.val.length ≤ 10000)
        (hbytes : ∀ (i : Nat) (hi : i < s.val.length),
          97 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 122)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000), ∀ r : I64, longest_substring s k = ok r → r.val = (s.val.length : Int) →
          KValid s k.val.toNat 0 s.val.length) := by
    sorry

  /-- The function returns a result r and r = 1 if k = 1, while r = 0 if k > 1.
    Preconditions: 0 <= len(s) <= 10000; every byte of s is an ASCII lowercase letter, i.e. 97 <= s[i] <= 122 for every 0 <= i < len(s); 1 <= k <= 100000; and len(s) = 1. -/
  theorem spec_11 (s : Slice U8) (k : I64)
      (hlen1 : 0 ≤ s.val.length) (hlen2 : s.val.length ≤ 10000)
      (hbytes : ∀ (i : Nat) (hi : i < s.val.length),
        97 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 122)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000) (hlen3 : s.val.length = 1) :
      ∃ r : I64, longest_substring s k = ok r ∧
        (k.val = 1 → r.val = 1) ∧ (1 < k.val → r.val = 0) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (s : Slice U8) (k : I64)
        (hlen1 : 0 ≤ s.val.length) (hlen2 : s.val.length ≤ 10000)
        (hbytes : ∀ (i : Nat) (hi : i < s.val.length),
          97 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 122)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000) (hlen3 : s.val.length = 1), ∃ r : I64, longest_substring s k = ok r ∧
          (k.val = 1 → r.val = 1) ∧ (1 < k.val → r.val = 0)) := by
    sorry

  /-- The function returns a result r and r = len(s) if k <= len(s), while r = 0 if k > len(s).
    Preconditions: 0 <= len(s) <= 10000; every byte of s is an ASCII lowercase letter, i.e. 97 <= s[i] <= 122 for every 0 <= i < len(s); 1 <= k <= 100000; and all bytes of s are equal, i.e. for every i and j with 0 <= i < len(s) and 0 <= j < len(s), s[i] = s[j]. -/
  theorem spec_12 (s : Slice U8) (k : I64)
      (hlen1 : 0 ≤ s.val.length) (hlen2 : s.val.length ≤ 10000)
      (hbytes : ∀ (i : Nat) (hi : i < s.val.length),
        97 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 122)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
      (hconst : ∀ (i : Nat) (hi : i < s.val.length) (j : Nat) (hj : j < s.val.length),
        (s.val[i]).val = (s.val[j]).val) :
      ∃ r : I64, longest_substring s k = ok r ∧
        (k.val ≤ (s.val.length : Int) → r.val = (s.val.length : Int)) ∧
        ((s.val.length : Int) < k.val → r.val = 0) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (s : Slice U8) (k : I64)
        (hlen1 : 0 ≤ s.val.length) (hlen2 : s.val.length ≤ 10000)
        (hbytes : ∀ (i : Nat) (hi : i < s.val.length),
          97 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 122)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
        (hconst : ∀ (i : Nat) (hi : i < s.val.length) (j : Nat) (hj : j < s.val.length),
          (s.val[i]).val = (s.val[j]).val), ∃ r : I64, longest_substring s k = ok r ∧
          (k.val ≤ (s.val.length : Int) → r.val = (s.val.length : Int)) ∧
          ((s.val.length : Int) < k.val → r.val = 0)) := by
    sorry

  /-- For every slice s' of bytes such that len(s') = len(s), every byte of s' is an ASCII lowercase letter, and s' has the same equality pattern as s (for all 0 <= i < len(s) and 0 <= j < len(s), s[i] = s[j] if and only if s'[i] = s'[j]), if the function returns r on (s,k) and returns r' on (s',k), then r' = r.
    Preconditions: 0 <= len(s) <= 10000; every byte of s is an ASCII lowercase letter, i.e. 97 <= s[i] <= 122 for every 0 <= i < len(s); and 1 <= k <= 100000. -/
  theorem spec_13 (s : Slice U8) (k : I64)
      (hlen1 : 0 ≤ s.val.length) (hlen2 : s.val.length ≤ 10000)
      (hbytes : ∀ (i : Nat) (hi : i < s.val.length),
        97 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 122)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000) :
      ∀ (s' : Slice U8) (hle : s'.val.length = s.val.length),
        (∀ (i : Nat) (hi : i < s'.val.length),
          97 ≤ (s'.val[i]).val ∧ (s'.val[i]).val ≤ 122) →
        (∀ (i : Nat) (hi : i < s.val.length) (j : Nat) (hj : j < s.val.length),
          ((s.val[i]).val = (s.val[j]).val ↔
            (s'.val[i]'(by omega)).val = (s'.val[j]'(by omega)).val)) →
        ∀ r r' : I64, longest_substring s k = ok r → longest_substring s' k = ok r' →
          r' = r := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (s : Slice U8) (k : I64)
        (hlen1 : 0 ≤ s.val.length) (hlen2 : s.val.length ≤ 10000)
        (hbytes : ∀ (i : Nat) (hi : i < s.val.length),
          97 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 122)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000), ∀ (s' : Slice U8) (hle : s'.val.length = s.val.length),
          (∀ (i : Nat) (hi : i < s'.val.length),
            97 ≤ (s'.val[i]).val ∧ (s'.val[i]).val ≤ 122) →
          (∀ (i : Nat) (hi : i < s.val.length) (j : Nat) (hj : j < s.val.length),
            ((s.val[i]).val = (s.val[j]).val ↔
              (s'.val[i]'(by omega)).val = (s'.val[j]'(by omega)).val)) →
          ∀ r r' : I64, longest_substring s k = ok r → longest_substring s' k = ok r' →
            r' = r) := by
    sorry

  /-- For every k1 and k2 with 1 <= k1 <= k2 <= 100000, if longest_substring(s,k1) returns r1 and longest_substring(s,k2) returns r2, then r1 >= r2.
    Preconditions: 0 <= len(s) <= 10000; every byte of s is an ASCII lowercase letter, i.e. 97 <= s[i] <= 122 for every 0 <= i < len(s); and 1 <= k <= 100000. -/
  theorem spec_14 (s : Slice U8) (k : I64)
      (hlen1 : 0 ≤ s.val.length) (hlen2 : s.val.length ≤ 10000)
      (hbytes : ∀ (i : Nat) (hi : i < s.val.length),
        97 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 122)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000) :
      ∀ k1 k2 : I64, 1 ≤ k1.val → k1.val ≤ k2.val → k2.val ≤ 100000 →
        ∀ r1 r2 : I64, longest_substring s k1 = ok r1 → longest_substring s k2 = ok r2 →
          r2.val ≤ r1.val := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (s : Slice U8) (k : I64)
        (hlen1 : 0 ≤ s.val.length) (hlen2 : s.val.length ≤ 10000)
        (hbytes : ∀ (i : Nat) (hi : i < s.val.length),
          97 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 122)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000), ∀ k1 k2 : I64, 1 ≤ k1.val → k1.val ≤ k2.val → k2.val ≤ 100000 →
          ∀ r1 r2 : I64, longest_substring s k1 = ok r1 → longest_substring s k2 = ok r2 →
            r2.val ≤ r1.val) := by
    sorry

  /-- For every i and j with 0 <= i <= j <= len(s), let t be the slice of length j - i with t[p] = s[i + p] for 0 <= p < j - i. If longest_substring(t,k) returns r_t and longest_substring(s,k) returns r, then r_t <= r.
    Preconditions: 0 <= len(s) <= 10000; every byte of s is an ASCII lowercase letter, i.e. 97 <= s[i] <= 122 for every 0 <= i < len(s); and 1 <= k <= 100000. -/
  theorem spec_15 (s : Slice U8) (k : I64)
      (hlen1 : 0 ≤ s.val.length) (hlen2 : s.val.length ≤ 10000)
      (hbytes : ∀ (i : Nat) (hi : i < s.val.length),
        97 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 122)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000) :
      ∀ i j : Nat, i ≤ j → j ≤ s.val.length →
        ∀ t : Slice U8, t.val = segBytes s i j →
          ∀ r_t r : I64, longest_substring t k = ok r_t → longest_substring s k = ok r →
            r_t.val ≤ r.val := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (s : Slice U8) (k : I64)
        (hlen1 : 0 ≤ s.val.length) (hlen2 : s.val.length ≤ 10000)
        (hbytes : ∀ (i : Nat) (hi : i < s.val.length),
          97 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 122)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000), ∀ i j : Nat, i ≤ j → j ≤ s.val.length →
          ∀ t : Slice U8, t.val = segBytes s i j →
            ∀ r_t r : I64, longest_substring t k = ok r_t → longest_substring s k = ok r →
              r_t.val ≤ r.val) := by
    sorry

  /-- Let s_rev be the slice of length len(s) with s_rev[i] = s[len(s) - 1 - i] for 0 <= i < len(s). If longest_substring(s_rev,k) returns r_rev and longest_substring(s,k) returns r, then r_rev = r.
    Preconditions: 0 <= len(s) <= 10000; every byte of s is an ASCII lowercase letter, i.e. 97 <= s[i] <= 122 for every 0 <= i < len(s); and 1 <= k <= 100000. -/
  theorem spec_16 (s : Slice U8) (k : I64)
      (hlen1 : 0 ≤ s.val.length) (hlen2 : s.val.length ≤ 10000)
      (hbytes : ∀ (i : Nat) (hi : i < s.val.length),
        97 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 122)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000) :
      ∀ s_rev : Slice U8, s_rev.val = s.val.reverse →
        ∀ r_rev r : I64, longest_substring s_rev k = ok r_rev →
          longest_substring s k = ok r → r_rev.val = r.val := by
    sorry

  theorem spec_16_neg :
      ¬ (∀ (s : Slice U8) (k : I64)
        (hlen1 : 0 ≤ s.val.length) (hlen2 : s.val.length ≤ 10000)
        (hbytes : ∀ (i : Nat) (hi : i < s.val.length),
          97 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 122)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000), ∀ s_rev : Slice U8, s_rev.val = s.val.reverse →
          ∀ r_rev r : I64, longest_substring s_rev k = ok r_rev →
            longest_substring s k = ok r → r_rev.val = r.val) := by
    sorry

  end AegisSpec.LongestSubstring
