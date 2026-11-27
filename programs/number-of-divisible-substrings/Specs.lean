import Aegis.CountDivisibleSubstrings.Code.Funs

/-!
# Specifications of `Aegis.CountDivisibleSubstrings.count_divisible_substrings`

LeetCode problem `number-of-divisible-substrings`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.CountDivisibleSubstrings

namespace AegisSpec.CountDivisibleSubstrings

def letterDigit (c : ℕ) : ℕ := (c - 97 + 4) / 3

def digits (word : Slice Std.U8) : List ℕ := word.val.map (fun b => letterDigit b.val)

def windowSum (word : Slice Std.U8) (i j : ℕ) : ℕ :=
  (((digits word).drop i).take (j + 1 - i)).sum

def windowDivisible (word : Slice Std.U8) (i j : ℕ) : Prop :=
  (j + 1 - i) ∣ windowSum word i j

def windowDivisibleBool (word : Slice Std.U8) (i j : ℕ) : Bool :=
  decide ((j + 1 - i) ∣ windowSum word i j)

def substringPairs (n : ℕ) : List (ℕ × ℕ) :=
  (List.range n).flatMap (fun i => (List.range (n - i)).map (fun t => (i, i + t)))

def divisibleSubstringCount (word : Slice Std.U8) : ℕ :=
  ((substringPairs word.val.length).filter
    (fun p => windowDivisibleBool word p.1 p.2)).length

def endingDivisibleCount (word : Slice Std.U8) : ℕ :=
  ((List.range word.val.length).filter
    (fun i => windowDivisibleBool word i (word.val.length - 1))).length

def totalSubstrings (n : ℕ) : ℕ := n * (n + 1) / 2

/-- Let n = len(word). For a lowercase byte c, define digit(c) by a,b -> 1; c,d,e -> 2; f,g,h -> 3; i,j,k -> 4; l,m,n -> 5; o,p,q -> 6; r,s,t -> 7; u,v,w -> 8; x,y,z -> 9 (equivalently digit(c) = (c - 97 + 4) / 3 with integer division). Whenever count_divisible_substrings(word) returns a result r, r is exactly the number of pairs (i,j) with 0 <= i <= j < n such that digit(word[i]) + digit(word[i+1]) + ... + digit(word[j]) is divisible by j - i + 1. Each such pair denotes the non-empty contiguous substring word[i..j] of length j-i+1.
  Preconditions: 1 <= len(word) <= 2000 and every byte word[i] is a lowercase English letter (97 <= word[i] <= 122). -/
theorem spec_1 (word : Slice Std.U8)
    (hlen1 : 1 ≤ word.val.length) (hlen2 : word.val.length ≤ 2000)
    (hlower : ∀ (i : ℕ) (hi : i < word.val.length),
      97 ≤ (word.val[i]'hi).val ∧ (word.val[i]'hi).val ≤ 122) :
    ∀ r, count_divisible_substrings word = Result.ok r →
      r.val = (divisibleSubstringCount word : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (word : Slice Std.U8)
    (hlen1 : 1 ≤ word.val.length) (hlen2 : word.val.length ≤ 2000)
    (hlower : ∀ (i : ℕ) (hi : i < word.val.length),
      97 ≤ (word.val[i]'hi).val ∧ (word.val[i]'hi).val ≤ 122), ∀ r, count_divisible_substrings word = Result.ok r →
      r.val = (divisibleSubstringCount word : ℤ)) := by
  sorry

/-- For every such word, count_divisible_substrings(word) returns a result r; in particular, it does not fail, panic, or produce an out-of-range arithmetic result.
  Preconditions: 1 <= len(word) <= 2000 and every byte word[i] is a lowercase English letter (97 <= word[i] <= 122). -/
theorem spec_2 (word : Slice Std.U8)
    (hlen1 : 1 ≤ word.val.length) (hlen2 : word.val.length ≤ 2000)
    (hlower : ∀ (i : ℕ) (hi : i < word.val.length),
      97 ≤ (word.val[i]'hi).val ∧ (word.val[i]'hi).val ≤ 122) :
    ∃ r, count_divisible_substrings word = Result.ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (word : Slice Std.U8)
    (hlen1 : 1 ≤ word.val.length) (hlen2 : word.val.length ≤ 2000)
    (hlower : ∀ (i : ℕ) (hi : i < word.val.length),
      97 ≤ (word.val[i]'hi).val ∧ (word.val[i]'hi).val ≤ 122), ∃ r, count_divisible_substrings word = Result.ok r) := by
  sorry

/-- Let n = len(word). Whenever count_divisible_substrings(word) returns a result r, we have r >= n.
  Preconditions: 1 <= len(word) <= 2000 and every byte word[i] is a lowercase English letter (97 <= word[i] <= 122). -/
theorem spec_3 (word : Slice Std.U8)
    (hlen1 : 1 ≤ word.val.length) (hlen2 : word.val.length ≤ 2000)
    (hlower : ∀ (i : ℕ) (hi : i < word.val.length),
      97 ≤ (word.val[i]'hi).val ∧ (word.val[i]'hi).val ≤ 122) :
    ∀ r, count_divisible_substrings word = Result.ok r →
      (word.val.length : ℤ) ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (word : Slice Std.U8)
    (hlen1 : 1 ≤ word.val.length) (hlen2 : word.val.length ≤ 2000)
    (hlower : ∀ (i : ℕ) (hi : i < word.val.length),
      97 ≤ (word.val[i]'hi).val ∧ (word.val[i]'hi).val ≤ 122), ∀ r, count_divisible_substrings word = Result.ok r →
      (word.val.length : ℤ) ≤ r.val) := by
  sorry

/-- Let n = len(word). Whenever count_divisible_substrings(word) returns a result r, we have r <= n*(n+1)/2, the total number of non-empty contiguous substrings of word.
  Preconditions: 1 <= len(word) <= 2000 and every byte word[i] is a lowercase English letter (97 <= word[i] <= 122). -/
theorem spec_4 (word : Slice Std.U8)
    (hlen1 : 1 ≤ word.val.length) (hlen2 : word.val.length ≤ 2000)
    (hlower : ∀ (i : ℕ) (hi : i < word.val.length),
      97 ≤ (word.val[i]'hi).val ∧ (word.val[i]'hi).val ≤ 122) :
    ∀ r, count_divisible_substrings word = Result.ok r →
      r.val ≤ ((totalSubstrings word.val.length : ℕ) : ℤ) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (word : Slice Std.U8)
    (hlen1 : 1 ≤ word.val.length) (hlen2 : word.val.length ≤ 2000)
    (hlower : ∀ (i : ℕ) (hi : i < word.val.length),
      97 ≤ (word.val[i]'hi).val ∧ (word.val[i]'hi).val ≤ 122), ∀ r, count_divisible_substrings word = Result.ok r →
      r.val ≤ ((totalSubstrings word.val.length : ℕ) : ℤ)) := by
  sorry

/-- Whenever count_divisible_substrings(word) returns a result r, r = 1.
  Preconditions: len(word) = 1 and the byte word[0] is a lowercase English letter. -/
theorem spec_5 (word : Slice Std.U8) (hlen : word.val.length = 1)
    (hlower : 97 ≤ (word.val[0]'(by omega)).val ∧ (word.val[0]'(by omega)).val ≤ 122) :
    ∀ r, count_divisible_substrings word = Result.ok r → r.val = 1 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (word : Slice Std.U8) (hlen : word.val.length = 1)
    (hlower : 97 ≤ (word.val[0]'(by omega)).val ∧ (word.val[0]'(by omega)).val ≤ 122), ∀ r, count_divisible_substrings word = Result.ok r → r.val = 1) := by
  sorry

/-- Let n = len(word). Using the digit mapping a,b -> 1; c,d,e -> 2; f,g,h -> 3; i,j,k -> 4; l,m,n -> 5; o,p,q -> 6; r,s,t -> 7; u,v,w -> 8; x,y,z -> 9, if digit(word[i]) = digit(word[0]) for every 0 <= i < n, then whenever count_divisible_substrings(word) returns a result r, r = n*(n+1)/2.
  Preconditions: 1 <= len(word) <= 2000 and every byte word[i] is a lowercase English letter (97 <= word[i] <= 122). -/
theorem spec_6 (word : Slice Std.U8)
    (hlen1 : 1 ≤ word.val.length) (hlen2 : word.val.length ≤ 2000)
    (hlower : ∀ (i : ℕ) (hi : i < word.val.length),
      97 ≤ (word.val[i]'hi).val ∧ (word.val[i]'hi).val ≤ 122)
    (hdigit : ∀ (i : ℕ) (hi : i < word.val.length),
      letterDigit (word.val[i]'hi).val = letterDigit (word.val[0]'(by omega)).val) :
    ∀ r, count_divisible_substrings word = Result.ok r →
      r.val = ((totalSubstrings word.val.length : ℕ) : ℤ) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (word : Slice Std.U8)
    (hlen1 : 1 ≤ word.val.length) (hlen2 : word.val.length ≤ 2000)
    (hlower : ∀ (i : ℕ) (hi : i < word.val.length),
      97 ≤ (word.val[i]'hi).val ∧ (word.val[i]'hi).val ≤ 122)
    (hdigit : ∀ (i : ℕ) (hi : i < word.val.length),
      letterDigit (word.val[i]'hi).val = letterDigit (word.val[0]'(by omega)).val), ∀ r, count_divisible_substrings word = Result.ok r →
      r.val = ((totalSubstrings word.val.length : ℕ) : ℤ)) := by
  sorry

/-- Using the digit mapping a,b -> 1; c,d,e -> 2; f,g,h -> 3; i,j,k -> 4; l,m,n -> 5; o,p,q -> 6; r,s,t -> 7; u,v,w -> 8; x,y,z -> 9, whenever count_divisible_substrings(word) returns a result r, r = 3 if digit(word[0]) + digit(word[1]) is even, and r = 2 otherwise.
  Preconditions: len(word) = 2 and both bytes are lowercase English letters. -/
theorem spec_7 (word : Slice Std.U8) (hlen : word.val.length = 2)
    (hlower : ∀ (i : ℕ) (hi : i < word.val.length),
      97 ≤ (word.val[i]'hi).val ∧ (word.val[i]'hi).val ≤ 122) :
    ∀ r, count_divisible_substrings word = Result.ok r →
      r.val = if 2 ∣ (letterDigit (word.val[0]'(by omega)).val
          + letterDigit (word.val[1]'(by omega)).val) then 3 else 2 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (word : Slice Std.U8) (hlen : word.val.length = 2)
    (hlower : ∀ (i : ℕ) (hi : i < word.val.length),
      97 ≤ (word.val[i]'hi).val ∧ (word.val[i]'hi).val ≤ 122), ∀ r, count_divisible_substrings word = Result.ok r →
      r.val = if 2 ∣ (letterDigit (word.val[0]'(by omega)).val
          + letterDigit (word.val[1]'(by omega)).val) then 3 else 2) := by
  sorry

/-- Let n = len(word) and let rev(word) be the length-n word with rev(word)[i] = word[n-1-i] for every 0 <= i < n. If count_divisible_substrings(word) returns r and count_divisible_substrings(rev(word)) returns r', then r = r'.
  Preconditions: 1 <= len(word) <= 2000 and every byte word[i] is a lowercase English letter (97 <= word[i] <= 122). -/
theorem spec_8 (word wrev : Slice Std.U8)
    (hlen1 : 1 ≤ word.val.length) (hlen2 : word.val.length ≤ 2000)
    (hlower : ∀ (i : ℕ) (hi : i < word.val.length),
      97 ≤ (word.val[i]'hi).val ∧ (word.val[i]'hi).val ≤ 122)
    (hrev : wrev.val = word.val.reverse) :
    ∀ r r', count_divisible_substrings word = Result.ok r →
      count_divisible_substrings wrev = Result.ok r' → r.val = r'.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (word wrev : Slice Std.U8)
    (hlen1 : 1 ≤ word.val.length) (hlen2 : word.val.length ≤ 2000)
    (hlower : ∀ (i : ℕ) (hi : i < word.val.length),
      97 ≤ (word.val[i]'hi).val ∧ (word.val[i]'hi).val ≤ 122)
    (hrev : wrev.val = word.val.reverse), ∀ r r', count_divisible_substrings word = Result.ok r →
      count_divisible_substrings wrev = Result.ok r' → r.val = r'.val) := by
  sorry

/-- Using the digit mapping a,b -> 1; c,d,e -> 2; f,g,h -> 3; i,j,k -> 4; l,m,n -> 5; o,p,q -> 6; r,s,t -> 7; u,v,w -> 8; x,y,z -> 9, if len(u) = len(v) and digit(u[i]) = digit(v[i]) for every 0 <= i < len(u), then whenever count_divisible_substrings(u) returns r_u and count_divisible_substrings(v) returns r_v, r_u = r_v.
  Preconditions: u and v are words with 1 <= len(u), len(v) <= 2000 and all bytes lowercase English letters. -/
theorem spec_9 (u v : Slice Std.U8)
    (hlu1 : 1 ≤ u.val.length) (hlu2 : u.val.length ≤ 2000)
    (hlv1 : 1 ≤ v.val.length) (hlv2 : v.val.length ≤ 2000)
    (hlu : ∀ (i : ℕ) (hi : i < u.val.length),
      97 ≤ (u.val[i]'hi).val ∧ (u.val[i]'hi).val ≤ 122)
    (hlv : ∀ (i : ℕ) (hi : i < v.val.length),
      97 ≤ (v.val[i]'hi).val ∧ (v.val[i]'hi).val ≤ 122)
    (hlen : u.val.length = v.val.length)
    (hdigit : ∀ (i : ℕ) (hi : i < u.val.length),
      letterDigit (u.val[i]'hi).val = letterDigit (v.val[i]'(by omega)).val) :
    ∀ r_u r_v, count_divisible_substrings u = Result.ok r_u →
      count_divisible_substrings v = Result.ok r_v → r_u.val = r_v.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (u v : Slice Std.U8)
    (hlu1 : 1 ≤ u.val.length) (hlu2 : u.val.length ≤ 2000)
    (hlv1 : 1 ≤ v.val.length) (hlv2 : v.val.length ≤ 2000)
    (hlu : ∀ (i : ℕ) (hi : i < u.val.length),
      97 ≤ (u.val[i]'hi).val ∧ (u.val[i]'hi).val ≤ 122)
    (hlv : ∀ (i : ℕ) (hi : i < v.val.length),
      97 ≤ (v.val[i]'hi).val ∧ (v.val[i]'hi).val ≤ 122)
    (hlen : u.val.length = v.val.length)
    (hdigit : ∀ (i : ℕ) (hi : i < u.val.length),
      letterDigit (u.val[i]'hi).val = letterDigit (v.val[i]'(by omega)).val), ∀ r_u r_v, count_divisible_substrings u = Result.ok r_u →
      count_divisible_substrings v = Result.ok r_v → r_u.val = r_v.val) := by
  sorry

/-- Let n = len(word). Using the digit mapping a,b -> 1; c,d,e -> 2; f,g,h -> 3; i,j,k -> 4; l,m,n -> 5; o,p,q -> 6; r,s,t -> 7; u,v,w -> 8; x,y,z -> 9, whenever count_divisible_substrings(word) returns a result r, r = n if and only if for every pair (i,j) with 0 <= i < j < n, digit(word[i]) + ... + digit(word[j]) is not divisible by j - i + 1.
  Preconditions: 1 <= len(word) <= 2000 and every byte word[i] is a lowercase English letter (97 <= word[i] <= 122). -/
theorem spec_10 (word : Slice Std.U8)
    (hlen1 : 1 ≤ word.val.length) (hlen2 : word.val.length ≤ 2000)
    (hlower : ∀ (i : ℕ) (hi : i < word.val.length),
      97 ≤ (word.val[i]'hi).val ∧ (word.val[i]'hi).val ≤ 122) :
    ∀ r, count_divisible_substrings word = Result.ok r →
      (r.val = (word.val.length : ℤ) ↔
        ∀ (i j : ℕ) (hi : i < j) (hj : j < word.val.length),
          ¬ windowDivisible word i j) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (word : Slice Std.U8)
    (hlen1 : 1 ≤ word.val.length) (hlen2 : word.val.length ≤ 2000)
    (hlower : ∀ (i : ℕ) (hi : i < word.val.length),
      97 ≤ (word.val[i]'hi).val ∧ (word.val[i]'hi).val ≤ 122), ∀ r, count_divisible_substrings word = Result.ok r →
      (r.val = (word.val.length : ℤ) ↔
        ∀ (i j : ℕ) (hi : i < j) (hj : j < word.val.length),
          ¬ windowDivisible word i j)) := by
  sorry

/-- Let n = len(word) and let w' be the length n+1 word with w'[i] = word[i] for every 0 <= i < n and w'[n] = c. Using the digit mapping a,b -> 1; c,d,e -> 2; f,g,h -> 3; i,j,k -> 4; l,m,n -> 5; o,p,q -> 6; r,s,t -> 7; u,v,w -> 8; x,y,z -> 9, whenever count_divisible_substrings(word) returns r and count_divisible_substrings(w') returns r', we have r' = r + m, where m is the number of indices i with 0 <= i <= n such that the substring w'[i..n] is divisible, i.e. digit(w'[i]) + ... + digit(w'[n]) is divisible by n - i + 1.
  Preconditions: 1 <= len(word) <= 1999 and every byte word[i] is a lowercase English letter (97 <= word[i] <= 122); c is a lowercase English letter. -/
theorem spec_11 (word : Slice Std.U8) (c : Std.U8) (w' : Slice Std.U8)
    (hlen1 : 1 ≤ word.val.length) (hlen2 : word.val.length ≤ 1999)
    (hlower : ∀ (i : ℕ) (hi : i < word.val.length),
      97 ≤ (word.val[i]'hi).val ∧ (word.val[i]'hi).val ≤ 122)
    (hc : 97 ≤ c.val ∧ c.val ≤ 122)
    (hw' : w'.val = word.val ++ [c]) :
    ∀ r r', count_divisible_substrings word = Result.ok r →
      count_divisible_substrings w' = Result.ok r' →
      r'.val = r.val + (endingDivisibleCount w' : ℤ) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (word : Slice Std.U8) (c : Std.U8) (w' : Slice Std.U8)
    (hlen1 : 1 ≤ word.val.length) (hlen2 : word.val.length ≤ 1999)
    (hlower : ∀ (i : ℕ) (hi : i < word.val.length),
      97 ≤ (word.val[i]'hi).val ∧ (word.val[i]'hi).val ≤ 122)
    (hc : 97 ≤ c.val ∧ c.val ≤ 122)
    (hw' : w'.val = word.val ++ [c]), ∀ r r', count_divisible_substrings word = Result.ok r →
      count_divisible_substrings w' = Result.ok r' →
      r'.val = r.val + (endingDivisibleCount w' : ℤ)) := by
  sorry

/-- Let n = len(word). Using the digit mapping a,b -> 1; c,d,e -> 2; f,g,h -> 3; i,j,k -> 4; l,m,n -> 5; o,p,q -> 6; r,s,t -> 7; u,v,w -> 8; x,y,z -> 9, whenever count_divisible_substrings(word) returns a result r, r = n*(n+1)/2 if and only if every non-empty contiguous substring of word is divisible, i.e. for every 0 <= i <= j < n, digit(word[i]) + ... + digit(word[j]) is divisible by j - i + 1.
  Preconditions: 1 <= len(word) <= 2000 and every byte word[i] is a lowercase English letter (97 <= word[i] <= 122). -/
theorem spec_12 (word : Slice Std.U8)
    (hlen1 : 1 ≤ word.val.length) (hlen2 : word.val.length ≤ 2000)
    (hlower : ∀ (i : ℕ) (hi : i < word.val.length),
      97 ≤ (word.val[i]'hi).val ∧ (word.val[i]'hi).val ≤ 122) :
    ∀ r, count_divisible_substrings word = Result.ok r →
      (r.val = ((totalSubstrings word.val.length : ℕ) : ℤ) ↔
        ∀ (i j : ℕ) (hi : i ≤ j) (hj : j < word.val.length), windowDivisible word i j) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (word : Slice Std.U8)
    (hlen1 : 1 ≤ word.val.length) (hlen2 : word.val.length ≤ 2000)
    (hlower : ∀ (i : ℕ) (hi : i < word.val.length),
      97 ≤ (word.val[i]'hi).val ∧ (word.val[i]'hi).val ≤ 122), ∀ r, count_divisible_substrings word = Result.ok r →
      (r.val = ((totalSubstrings word.val.length : ℕ) : ℤ) ↔
        ∀ (i j : ℕ) (hi : i ≤ j) (hj : j < word.val.length), windowDivisible word i j)) := by
  sorry

/-- Whenever count_divisible_substrings(u) returns r_u and count_divisible_substrings(v) returns r_v, we have r_u = r_v. For any substring length L, adding the constant k to every digit adds k*L to the digit sum, which preserves divisibility by L.
  Preconditions: 1 <= len(u) = len(v) <= 2000, all bytes of u and v are lowercase English letters, and there exists an integer k such that digit(v[i]) = digit(u[i]) + k for every 0 <= i < len(u), where digit is the mapping a,b -> 1; c,d,e -> 2; f,g,h -> 3; i,j,k -> 4; l,m,n -> 5; o,p,q -> 6; r,s,t -> 7; u,v,w -> 8; x,y,z -> 9. -/
theorem spec_13 (u v : Slice Std.U8)
    (hlu1 : 1 ≤ u.val.length) (hlu2 : u.val.length ≤ 2000)
    (hlv1 : 1 ≤ v.val.length) (hlv2 : v.val.length ≤ 2000)
    (hlen : u.val.length = v.val.length)
    (hlu : ∀ (i : ℕ) (hi : i < u.val.length),
      97 ≤ (u.val[i]'hi).val ∧ (u.val[i]'hi).val ≤ 122)
    (hlv : ∀ (i : ℕ) (hi : i < v.val.length),
      97 ≤ (v.val[i]'hi).val ∧ (v.val[i]'hi).val ≤ 122)
    (hk : ∃ k : ℤ, ∀ (i : ℕ) (hi : i < u.val.length),
      (letterDigit (v.val[i]'(by omega)).val : ℤ) = (letterDigit (u.val[i]'hi).val : ℤ) + k) :
    ∀ r_u r_v, count_divisible_substrings u = Result.ok r_u →
      count_divisible_substrings v = Result.ok r_v → r_u.val = r_v.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (u v : Slice Std.U8)
    (hlu1 : 1 ≤ u.val.length) (hlu2 : u.val.length ≤ 2000)
    (hlv1 : 1 ≤ v.val.length) (hlv2 : v.val.length ≤ 2000)
    (hlen : u.val.length = v.val.length)
    (hlu : ∀ (i : ℕ) (hi : i < u.val.length),
      97 ≤ (u.val[i]'hi).val ∧ (u.val[i]'hi).val ≤ 122)
    (hlv : ∀ (i : ℕ) (hi : i < v.val.length),
      97 ≤ (v.val[i]'hi).val ∧ (v.val[i]'hi).val ≤ 122)
    (hk : ∃ k : ℤ, ∀ (i : ℕ) (hi : i < u.val.length),
      (letterDigit (v.val[i]'(by omega)).val : ℤ) = (letterDigit (u.val[i]'hi).val : ℤ) + k), ∀ r_u r_v, count_divisible_substrings u = Result.ok r_u →
      count_divisible_substrings v = Result.ok r_v → r_u.val = r_v.val) := by
  sorry

end AegisSpec.CountDivisibleSubstrings
