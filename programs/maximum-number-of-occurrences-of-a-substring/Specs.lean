import Aegis.MaxFreq.Code.Funs

/-!
# Specifications of `Aegis.MaxFreq.max_freq`

LeetCode problem `maximum-number-of-occurrences-of-a-substring`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxFreq

def toBytes (s : Slice Std.U8) : List Nat := s.val.map (fun b => b.val)

def slen (s : Slice Std.U8) : Nat := s.val.length

def window (s : Slice Std.U8) (i L : Nat) : List Nat := (toBytes s).drop i |>.take L

def distinct (t : List Nat) : Nat := t.dedup.length

def occ (s : Slice Std.U8) (t : List Nat) : Nat :=
  ((List.range (slen s + 1)).filter
      (fun i => decide (i + t.length ≤ slen s ∧ window s i t.length = t))).length

def candidates (s : Slice Std.U8) : List (List Nat) := (toBytes s).sublists

def bestOcc (s : Slice Std.U8) (maxLetters minSize maxSize : Nat) : Nat :=
  ((candidates s).filter
        (fun t => decide (minSize ≤ t.length ∧ t.length ≤ maxSize ∧ distinct t ≤ maxLetters))
      |>.map (occ s)).foldr max 0

def bestOccFixedLen (s : Slice Std.U8) (maxLetters minSize : Nat) : Nat :=
  ((candidates s).filter (fun t => decide (t.length = minSize ∧ distinct t ≤ maxLetters))
      |>.map (occ s)).foldr max 0

def bestOccMinSize (s : Slice Std.U8) (minSize : Nat) : Nat :=
  ((List.range (slen s + 1)).filter (fun i => decide (i + minSize ≤ slen s))
      |>.map (fun i => occ s (window s i minSize))).foldr max 0

def byteValueCount (s : Slice Std.U8) (b : Nat) : Nat :=
  ((toBytes s).filter (fun x => decide (x = b))).length

def maxByteValueCount (s : Slice Std.U8) : Nat :=
  ((List.range 256).map (byteValueCount s)).foldr max 0

def blockLengthsAux (b : Nat) : Nat → List Nat → List Nat → List Nat
  | cur, acc, [] => (if cur = 0 then acc else cur :: acc).reverse
  | cur, acc, x :: xs =>
    if x = b then blockLengthsAux b (cur + 1) acc xs
    else blockLengthsAux b 0 (if cur = 0 then acc else cur :: acc) xs

def blockLengths (b : Nat) (l : List Nat) : List Nat := blockLengthsAux b 0 [] l

def blockScore (b minSize : Nat) (l : List Nat) : Nat :=
  ((blockLengths b l).map (fun R => R + 1 - minSize)).foldr (· + ·) 0

def maxBlockScore (s : Slice Std.U8) (minSize : Nat) : Nat :=
  ((List.range 256).map (fun b => blockScore b minSize (toBytes s))).foldr max 0

/-- Let distinct(t) be the number of distinct byte values in a byte string t. Let occ(t) be the number of indices i with 0 <= i <= len(s)-len(t) such that s[i+j] = t[j] for every j with 0 <= j < len(t). The function returns a result r and r = max { occ(t) | t is a byte string, minSize <= len(t) <= maxSize, distinct(t) <= maxLetters }. This maximum is taken over a finite set; if no valid substring occurs in s, it is 0.
  Preconditions: len(s) is between 1 and 100000 inclusive; 1 <= maxLetters <= 26; 1 <= minSize <= maxSize <= 26; maxSize <= len(s); every byte of s is an ASCII lowercase letter. -/
theorem spec_1 (s : Slice Std.U8) (maxLetters minSize maxSize : Std.I64)
    (h_len_lo : 1 ≤ slen s) (h_len_hi : slen s ≤ 100000)
    (h_maxLetters_lo : 1 ≤ maxLetters.val) (h_maxLetters_hi : maxLetters.val ≤ 26)
    (h_minSize_lo : 1 ≤ minSize.val) (h_minSize_le : minSize.val ≤ maxSize.val)
    (h_maxSize_hi : maxSize.val ≤ 26) (h_maxSize_le : maxSize.val ≤ (slen s : Int))
    (h_lower : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122) :
    ∃ r : Std.I64,
      Aegis.MaxFreq.max_freq s maxLetters minSize maxSize = ok r ∧
      r.val = (bestOcc s maxLetters.val.toNat minSize.val.toNat maxSize.val.toNat : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice Std.U8) (maxLetters minSize maxSize : Std.I64)
    (h_len_lo : 1 ≤ slen s) (h_len_hi : slen s ≤ 100000)
    (h_maxLetters_lo : 1 ≤ maxLetters.val) (h_maxLetters_hi : maxLetters.val ≤ 26)
    (h_minSize_lo : 1 ≤ minSize.val) (h_minSize_le : minSize.val ≤ maxSize.val)
    (h_maxSize_hi : maxSize.val ≤ 26) (h_maxSize_le : maxSize.val ≤ (slen s : Int))
    (h_lower : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122), ∃ r : Std.I64,
      Aegis.MaxFreq.max_freq s maxLetters minSize maxSize = ok r ∧
      r.val = (bestOcc s maxLetters.val.toNat minSize.val.toNat maxSize.val.toNat : Int)) := by
  sorry

/-- The function returns a result r; it does not fail with arithmetic overflow, out-of-bounds access, or panic.
  Preconditions: len(s) is between 1 and 100000 inclusive; 1 <= maxLetters <= 26; 1 <= minSize <= maxSize <= 26; maxSize <= len(s); every byte of s is an ASCII lowercase letter. -/
theorem spec_2 (s : Slice Std.U8) (maxLetters minSize maxSize : Std.I64)
    (h_len_lo : 1 ≤ slen s) (h_len_hi : slen s ≤ 100000)
    (h_maxLetters_lo : 1 ≤ maxLetters.val) (h_maxLetters_hi : maxLetters.val ≤ 26)
    (h_minSize_lo : 1 ≤ minSize.val) (h_minSize_le : minSize.val ≤ maxSize.val)
    (h_maxSize_hi : maxSize.val ≤ 26) (h_maxSize_le : maxSize.val ≤ (slen s : Int))
    (h_lower : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122) :
    ∃ r : Std.I64, Aegis.MaxFreq.max_freq s maxLetters minSize maxSize = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice Std.U8) (maxLetters minSize maxSize : Std.I64)
    (h_len_lo : 1 ≤ slen s) (h_len_hi : slen s ≤ 100000)
    (h_maxLetters_lo : 1 ≤ maxLetters.val) (h_maxLetters_hi : maxLetters.val ≤ 26)
    (h_minSize_lo : 1 ≤ minSize.val) (h_minSize_le : minSize.val ≤ maxSize.val)
    (h_maxSize_hi : maxSize.val ≤ 26) (h_maxSize_le : maxSize.val ≤ (slen s : Int))
    (h_lower : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122), ∃ r : Std.I64, Aegis.MaxFreq.max_freq s maxLetters minSize maxSize = ok r) := by
  sorry

/-- The function returns a result r and 0 <= r <= len(s) - minSize + 1.
  Preconditions: len(s) is between 1 and 100000 inclusive; 1 <= maxLetters <= 26; 1 <= minSize <= maxSize <= 26; maxSize <= len(s); every byte of s is an ASCII lowercase letter. -/
theorem spec_3 (s : Slice Std.U8) (maxLetters minSize maxSize : Std.I64)
    (h_len_lo : 1 ≤ slen s) (h_len_hi : slen s ≤ 100000)
    (h_maxLetters_lo : 1 ≤ maxLetters.val) (h_maxLetters_hi : maxLetters.val ≤ 26)
    (h_minSize_lo : 1 ≤ minSize.val) (h_minSize_le : minSize.val ≤ maxSize.val)
    (h_maxSize_hi : maxSize.val ≤ 26) (h_maxSize_le : maxSize.val ≤ (slen s : Int))
    (h_lower : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122) :
    ∃ r : Std.I64,
      Aegis.MaxFreq.max_freq s maxLetters minSize maxSize = ok r ∧
      0 ≤ r.val ∧ r.val ≤ (slen s : Int) - minSize.val + 1 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice Std.U8) (maxLetters minSize maxSize : Std.I64)
    (h_len_lo : 1 ≤ slen s) (h_len_hi : slen s ≤ 100000)
    (h_maxLetters_lo : 1 ≤ maxLetters.val) (h_maxLetters_hi : maxLetters.val ≤ 26)
    (h_minSize_lo : 1 ≤ minSize.val) (h_minSize_le : minSize.val ≤ maxSize.val)
    (h_maxSize_hi : maxSize.val ≤ 26) (h_maxSize_le : maxSize.val ≤ (slen s : Int))
    (h_lower : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122), ∃ r : Std.I64,
      Aegis.MaxFreq.max_freq s maxLetters minSize maxSize = ok r ∧
      0 ≤ r.val ∧ r.val ≤ (slen s : Int) - minSize.val + 1) := by
  sorry

/-- The function returns a result r. Whenever r > 0, there exist an integer L and a start i such that minSize <= L <= maxSize, 0 <= i <= len(s)-L, the substring s[i..i+L) has at most maxLetters distinct byte values, and r equals the number of starts j with 0 <= j <= len(s)-L for which s[j..j+L) = s[i..i+L).
  Preconditions: len(s) is between 1 and 100000 inclusive; 1 <= maxLetters <= 26; 1 <= minSize <= maxSize <= 26; maxSize <= len(s); every byte of s is an ASCII lowercase letter. -/
theorem spec_4 (s : Slice Std.U8) (maxLetters minSize maxSize : Std.I64)
    (h_len_lo : 1 ≤ slen s) (h_len_hi : slen s ≤ 100000)
    (h_maxLetters_lo : 1 ≤ maxLetters.val) (h_maxLetters_hi : maxLetters.val ≤ 26)
    (h_minSize_lo : 1 ≤ minSize.val) (h_minSize_le : minSize.val ≤ maxSize.val)
    (h_maxSize_hi : maxSize.val ≤ 26) (h_maxSize_le : maxSize.val ≤ (slen s : Int))
    (h_lower : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122) :
    ∃ r : Std.I64,
      Aegis.MaxFreq.max_freq s maxLetters minSize maxSize = ok r ∧
      ∀ (_hr : 0 < r.val), ∃ L i : Nat,
        minSize.val.toNat ≤ L ∧ L ≤ maxSize.val.toNat ∧ i + L ≤ slen s ∧
        distinct (window s i L) ≤ maxLetters.val.toNat ∧
        r.val = (occ s (window s i L) : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice Std.U8) (maxLetters minSize maxSize : Std.I64)
    (h_len_lo : 1 ≤ slen s) (h_len_hi : slen s ≤ 100000)
    (h_maxLetters_lo : 1 ≤ maxLetters.val) (h_maxLetters_hi : maxLetters.val ≤ 26)
    (h_minSize_lo : 1 ≤ minSize.val) (h_minSize_le : minSize.val ≤ maxSize.val)
    (h_maxSize_hi : maxSize.val ≤ 26) (h_maxSize_le : maxSize.val ≤ (slen s : Int))
    (h_lower : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122), ∃ r : Std.I64,
      Aegis.MaxFreq.max_freq s maxLetters minSize maxSize = ok r ∧
      ∀ (_hr : 0 < r.val), ∃ L i : Nat,
        minSize.val.toNat ≤ L ∧ L ≤ maxSize.val.toNat ∧ i + L ≤ slen s ∧
        distinct (window s i L) ≤ maxLetters.val.toNat ∧
        r.val = (occ s (window s i L) : Int)) := by
  sorry

/-- The function returns a result r and r = max { count(b) | b is a byte value }, where count(b) is the number of indices i with 0 <= i < len(s) and s[i] = b.
  Preconditions: len(s) is between 1 and 100000 inclusive; 1 <= maxLetters <= 26; minSize = 1; 1 <= maxSize <= 26; maxSize <= len(s); every byte of s is an ASCII lowercase letter. -/
theorem spec_5 (s : Slice Std.U8) (maxLetters minSize maxSize : Std.I64)
    (h_len_lo : 1 ≤ slen s) (h_len_hi : slen s ≤ 100000)
    (h_maxLetters_lo : 1 ≤ maxLetters.val) (h_maxLetters_hi : maxLetters.val ≤ 26)
    (h_minSize_one : minSize.val = 1) (h_minSize_le : minSize.val ≤ maxSize.val)
    (h_maxSize_hi : maxSize.val ≤ 26) (h_maxSize_le : maxSize.val ≤ (slen s : Int))
    (h_lower : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122) :
    ∃ r : Std.I64,
      Aegis.MaxFreq.max_freq s maxLetters minSize maxSize = ok r ∧
      r.val = (maxByteValueCount s : Int) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice Std.U8) (maxLetters minSize maxSize : Std.I64)
    (h_len_lo : 1 ≤ slen s) (h_len_hi : slen s ≤ 100000)
    (h_maxLetters_lo : 1 ≤ maxLetters.val) (h_maxLetters_hi : maxLetters.val ≤ 26)
    (h_minSize_one : minSize.val = 1) (h_minSize_le : minSize.val ≤ maxSize.val)
    (h_maxSize_hi : maxSize.val ≤ 26) (h_maxSize_le : maxSize.val ≤ (slen s : Int))
    (h_lower : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122), ∃ r : Std.I64,
      Aegis.MaxFreq.max_freq s maxLetters minSize maxSize = ok r ∧
      r.val = (maxByteValueCount s : Int)) := by
  sorry

/-- The function returns a result r and r = len(s) - minSize + 1.
  Preconditions: len(s) is between 1 and 100000 inclusive; 1 <= maxLetters <= 26; 1 <= minSize <= maxSize <= 26; maxSize <= len(s); every byte of s is an ASCII lowercase letter; there exists a byte b such that s[i] = b for every i with 0 <= i < len(s). -/
theorem spec_6 (s : Slice Std.U8) (maxLetters minSize maxSize : Std.I64)
    (h_len_lo : 1 ≤ slen s) (h_len_hi : slen s ≤ 100000)
    (h_maxLetters_lo : 1 ≤ maxLetters.val) (h_maxLetters_hi : maxLetters.val ≤ 26)
    (h_minSize_lo : 1 ≤ minSize.val) (h_minSize_le : minSize.val ≤ maxSize.val)
    (h_maxSize_hi : maxSize.val ≤ 26) (h_maxSize_le : maxSize.val ≤ (slen s : Int))
    (h_lower : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (h_const : ∃ b : Nat, ∀ i : Nat, i < slen s → window s i 1 = [b]) :
    ∃ r : Std.I64,
      Aegis.MaxFreq.max_freq s maxLetters minSize maxSize = ok r ∧
      r.val = (slen s : Int) - minSize.val + 1 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice Std.U8) (maxLetters minSize maxSize : Std.I64)
    (h_len_lo : 1 ≤ slen s) (h_len_hi : slen s ≤ 100000)
    (h_maxLetters_lo : 1 ≤ maxLetters.val) (h_maxLetters_hi : maxLetters.val ≤ 26)
    (h_minSize_lo : 1 ≤ minSize.val) (h_minSize_le : minSize.val ≤ maxSize.val)
    (h_maxSize_hi : maxSize.val ≤ 26) (h_maxSize_le : maxSize.val ≤ (slen s : Int))
    (h_lower : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (h_const : ∃ b : Nat, ∀ i : Nat, i < slen s → window s i 1 = [b]), ∃ r : Std.I64,
      Aegis.MaxFreq.max_freq s maxLetters minSize maxSize = ok r ∧
      r.val = (slen s : Int) - minSize.val + 1) := by
  sorry

/-- The function returns a result r. Let d be the number of distinct byte values in s. Then r = 1 if d <= maxLetters, and r = 0 otherwise.
  Preconditions: len(s) is between 1 and 26 inclusive; 1 <= maxLetters <= 26; minSize = maxSize = len(s); every byte of s is an ASCII lowercase letter. -/
theorem spec_7 (s : Slice Std.U8) (maxLetters minSize maxSize : Std.I64)
    (h_len_lo : 1 ≤ slen s) (h_len_hi : slen s ≤ 26)
    (h_maxLetters_lo : 1 ≤ maxLetters.val) (h_maxLetters_hi : maxLetters.val ≤ 26)
    (h_minSize : minSize.val = (slen s : Int)) (h_maxSize : maxSize.val = (slen s : Int)) :
    ∃ r : Std.I64,
      Aegis.MaxFreq.max_freq s maxLetters minSize maxSize = ok r ∧
      (if distinct (toBytes s) ≤ maxLetters.val.toNat then r.val = 1 else r.val = 0) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice Std.U8) (maxLetters minSize maxSize : Std.I64)
    (h_len_lo : 1 ≤ slen s) (h_len_hi : slen s ≤ 26)
    (h_maxLetters_lo : 1 ≤ maxLetters.val) (h_maxLetters_hi : maxLetters.val ≤ 26)
    (h_minSize : minSize.val = (slen s : Int)) (h_maxSize : maxSize.val = (slen s : Int)), ∃ r : Std.I64,
      Aegis.MaxFreq.max_freq s maxLetters minSize maxSize = ok r ∧
      (if distinct (toBytes s) ≤ maxLetters.val.toNat then r.val = 1 else r.val = 0)) := by
  sorry

/-- For a byte b, let R_1,...,R_k be the lengths of the maximal contiguous blocks of positions in s all equal to b, where a block is a maximal interval [p,q) with s[i] = b for all p <= i < q. Let score(b) = sum over these blocks of max(0, R_j - minSize + 1). The function returns a result r and r = max over all byte values b of score(b).
  Preconditions: len(s) is between 1 and 100000 inclusive; maxLetters = 1; 1 <= minSize <= maxSize <= 26; maxSize <= len(s); every byte of s is an ASCII lowercase letter. -/
theorem spec_8 (s : Slice Std.U8) (maxLetters minSize maxSize : Std.I64)
    (h_len_lo : 1 ≤ slen s) (h_len_hi : slen s ≤ 100000)
    (h_maxLetters_one : maxLetters.val = 1)
    (h_minSize_lo : 1 ≤ minSize.val) (h_minSize_le : minSize.val ≤ maxSize.val)
    (h_maxSize_hi : maxSize.val ≤ 26) (h_maxSize_le : maxSize.val ≤ (slen s : Int))
    (h_lower : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122) :
    ∃ r : Std.I64,
      Aegis.MaxFreq.max_freq s maxLetters minSize maxSize = ok r ∧
      r.val = (maxBlockScore s minSize.val.toNat : Int) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s : Slice Std.U8) (maxLetters minSize maxSize : Std.I64)
    (h_len_lo : 1 ≤ slen s) (h_len_hi : slen s ≤ 100000)
    (h_maxLetters_one : maxLetters.val = 1)
    (h_minSize_lo : 1 ≤ minSize.val) (h_minSize_le : minSize.val ≤ maxSize.val)
    (h_maxSize_hi : maxSize.val ≤ 26) (h_maxSize_le : maxSize.val ≤ (slen s : Int))
    (h_lower : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122), ∃ r : Std.I64,
      Aegis.MaxFreq.max_freq s maxLetters minSize maxSize = ok r ∧
      r.val = (maxBlockScore s minSize.val.toNat : Int)) := by
  sorry

/-- Let r1 be the result of max_freq(s, maxLetters1, minSize, maxSize) and r2 be the result of max_freq(s, maxLetters2, minSize, maxSize). Both calls return results, and r1 <= r2.
  Preconditions: For each of the two calls, len(s) is between 1 and 100000 inclusive; 1 <= maxLetters_i <= 26; 1 <= minSize <= maxSize <= 26; maxSize <= len(s); every byte of s is an ASCII lowercase letter; and maxLetters1 <= maxLetters2. -/
theorem spec_9 (s : Slice Std.U8) (maxLetters1 maxLetters2 minSize maxSize : Std.I64)
    (h_len_lo : 1 ≤ slen s) (h_len_hi : slen s ≤ 100000)
    (h_maxLetters1_lo : 1 ≤ maxLetters1.val) (h_maxLetters1_hi : maxLetters1.val ≤ 26)
    (h_maxLetters2_lo : 1 ≤ maxLetters2.val) (h_maxLetters2_hi : maxLetters2.val ≤ 26)
    (h_maxLetters_le : maxLetters1.val ≤ maxLetters2.val)
    (h_minSize_lo : 1 ≤ minSize.val) (h_minSize_le : minSize.val ≤ maxSize.val)
    (h_maxSize_hi : maxSize.val ≤ 26) (h_maxSize_le : maxSize.val ≤ (slen s : Int))
    (h_lower : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122) :
    ∃ r1 r2 : Std.I64,
      Aegis.MaxFreq.max_freq s maxLetters1 minSize maxSize = ok r1 ∧
      Aegis.MaxFreq.max_freq s maxLetters2 minSize maxSize = ok r2 ∧
      r1.val ≤ r2.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s : Slice Std.U8) (maxLetters1 maxLetters2 minSize maxSize : Std.I64)
    (h_len_lo : 1 ≤ slen s) (h_len_hi : slen s ≤ 100000)
    (h_maxLetters1_lo : 1 ≤ maxLetters1.val) (h_maxLetters1_hi : maxLetters1.val ≤ 26)
    (h_maxLetters2_lo : 1 ≤ maxLetters2.val) (h_maxLetters2_hi : maxLetters2.val ≤ 26)
    (h_maxLetters_le : maxLetters1.val ≤ maxLetters2.val)
    (h_minSize_lo : 1 ≤ minSize.val) (h_minSize_le : minSize.val ≤ maxSize.val)
    (h_maxSize_hi : maxSize.val ≤ 26) (h_maxSize_le : maxSize.val ≤ (slen s : Int))
    (h_lower : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122), ∃ r1 r2 : Std.I64,
      Aegis.MaxFreq.max_freq s maxLetters1 minSize maxSize = ok r1 ∧
      Aegis.MaxFreq.max_freq s maxLetters2 minSize maxSize = ok r2 ∧
      r1.val ≤ r2.val) := by
  sorry

/-- Let r1 be the result of max_freq(s, maxLetters, minSize, maxSize1) and r2 be the result of max_freq(s, maxLetters, minSize, maxSize2). Both calls return results, and r1 <= r2.
  Preconditions: len(s) is between 1 and 100000 inclusive; 1 <= maxLetters <= 26; 1 <= minSize <= maxSize1 <= maxSize2 <= 26; maxSize2 <= len(s); every byte of s is an ASCII lowercase letter. -/
theorem spec_10 (s : Slice Std.U8) (maxLetters minSize maxSize1 maxSize2 : Std.I64)
    (h_len_lo : 1 ≤ slen s) (h_len_hi : slen s ≤ 100000)
    (h_maxLetters_lo : 1 ≤ maxLetters.val) (h_maxLetters_hi : maxLetters.val ≤ 26)
    (h_minSize_lo : 1 ≤ minSize.val) (h_minSize_le : minSize.val ≤ maxSize1.val)
    (h_maxSize_le : maxSize1.val ≤ maxSize2.val) (h_maxSize2_hi : maxSize2.val ≤ 26)
    (h_maxSize2_len : maxSize2.val ≤ (slen s : Int))
    (h_lower : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122) :
    ∃ r1 r2 : Std.I64,
      Aegis.MaxFreq.max_freq s maxLetters minSize maxSize1 = ok r1 ∧
      Aegis.MaxFreq.max_freq s maxLetters minSize maxSize2 = ok r2 ∧
      r1.val ≤ r2.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s : Slice Std.U8) (maxLetters minSize maxSize1 maxSize2 : Std.I64)
    (h_len_lo : 1 ≤ slen s) (h_len_hi : slen s ≤ 100000)
    (h_maxLetters_lo : 1 ≤ maxLetters.val) (h_maxLetters_hi : maxLetters.val ≤ 26)
    (h_minSize_lo : 1 ≤ minSize.val) (h_minSize_le : minSize.val ≤ maxSize1.val)
    (h_maxSize_le : maxSize1.val ≤ maxSize2.val) (h_maxSize2_hi : maxSize2.val ≤ 26)
    (h_maxSize2_len : maxSize2.val ≤ (slen s : Int))
    (h_lower : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122), ∃ r1 r2 : Std.I64,
      Aegis.MaxFreq.max_freq s maxLetters minSize maxSize1 = ok r1 ∧
      Aegis.MaxFreq.max_freq s maxLetters minSize maxSize2 = ok r2 ∧
      r1.val ≤ r2.val) := by
  sorry

/-- Let r1 be the result of max_freq(s, maxLetters, minSize1, maxSize) and r2 be the result of max_freq(s, maxLetters, minSize2, maxSize). Both calls return results, and r2 <= r1.
  Preconditions: len(s) is between 1 and 100000 inclusive; 1 <= maxLetters <= 26; 1 <= minSize1 <= minSize2 <= maxSize <= 26; maxSize <= len(s); every byte of s is an ASCII lowercase letter. -/
theorem spec_11 (s : Slice Std.U8) (maxLetters minSize1 minSize2 maxSize : Std.I64)
    (h_len_lo : 1 ≤ slen s) (h_len_hi : slen s ≤ 100000)
    (h_maxLetters_lo : 1 ≤ maxLetters.val) (h_maxLetters_hi : maxLetters.val ≤ 26)
    (h_minSize1_lo : 1 ≤ minSize1.val) (h_minSize_le : minSize1.val ≤ minSize2.val)
    (h_minSize2_le : minSize2.val ≤ maxSize.val) (h_maxSize_hi : maxSize.val ≤ 26)
    (h_maxSize_le : maxSize.val ≤ (slen s : Int))
    (h_lower : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122) :
    ∃ r1 r2 : Std.I64,
      Aegis.MaxFreq.max_freq s maxLetters minSize1 maxSize = ok r1 ∧
      Aegis.MaxFreq.max_freq s maxLetters minSize2 maxSize = ok r2 ∧
      r2.val ≤ r1.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s : Slice Std.U8) (maxLetters minSize1 minSize2 maxSize : Std.I64)
    (h_len_lo : 1 ≤ slen s) (h_len_hi : slen s ≤ 100000)
    (h_maxLetters_lo : 1 ≤ maxLetters.val) (h_maxLetters_hi : maxLetters.val ≤ 26)
    (h_minSize1_lo : 1 ≤ minSize1.val) (h_minSize_le : minSize1.val ≤ minSize2.val)
    (h_minSize2_le : minSize2.val ≤ maxSize.val) (h_maxSize_hi : maxSize.val ≤ 26)
    (h_maxSize_le : maxSize.val ≤ (slen s : Int))
    (h_lower : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122), ∃ r1 r2 : Std.I64,
      Aegis.MaxFreq.max_freq s maxLetters minSize1 maxSize = ok r1 ∧
      Aegis.MaxFreq.max_freq s maxLetters minSize2 maxSize = ok r2 ∧
      r2.val ≤ r1.val) := by
  sorry

/-- Let occ(p) be the number of starts j with 0 <= j <= len(s)-len(p) and s[j..j+len(p)) = p. The function returns a result r and r = max { occ(p) | p is a substring of s with len(p) = minSize }.
  Preconditions: len(s) is between 1 and 100000 inclusive; 1 <= maxLetters <= 26; 1 <= minSize <= maxSize <= 26; maxSize <= len(s); every byte of s is an ASCII lowercase letter; maxLetters >= d, where d is the number of distinct byte values in s. -/
theorem spec_12 (s : Slice Std.U8) (maxLetters minSize maxSize : Std.I64)
    (h_len_lo : 1 ≤ slen s) (h_len_hi : slen s ≤ 100000)
    (h_maxLetters_lo : 1 ≤ maxLetters.val) (h_maxLetters_hi : maxLetters.val ≤ 26)
    (h_minSize_lo : 1 ≤ minSize.val) (h_minSize_le : minSize.val ≤ maxSize.val)
    (h_maxSize_hi : maxSize.val ≤ 26) (h_maxSize_le : maxSize.val ≤ (slen s : Int))
    (h_lower : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (h_distinct : (distinct (toBytes s) : Int) ≤ maxLetters.val) :
    ∃ r : Std.I64,
      Aegis.MaxFreq.max_freq s maxLetters minSize maxSize = ok r ∧
      r.val = (bestOccMinSize s minSize.val.toNat : Int) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (s : Slice Std.U8) (maxLetters minSize maxSize : Std.I64)
    (h_len_lo : 1 ≤ slen s) (h_len_hi : slen s ≤ 100000)
    (h_maxLetters_lo : 1 ≤ maxLetters.val) (h_maxLetters_hi : maxLetters.val ≤ 26)
    (h_minSize_lo : 1 ≤ minSize.val) (h_minSize_le : minSize.val ≤ maxSize.val)
    (h_maxSize_hi : maxSize.val ≤ 26) (h_maxSize_le : maxSize.val ≤ (slen s : Int))
    (h_lower : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (h_distinct : (distinct (toBytes s) : Int) ≤ maxLetters.val), ∃ r : Std.I64,
      Aegis.MaxFreq.max_freq s maxLetters minSize maxSize = ok r ∧
      r.val = (bestOccMinSize s minSize.val.toNat : Int)) := by
  sorry

/-- Both calls return results and max_freq(s1, maxLetters, minSize, maxSize) = max_freq(s2, maxLetters, minSize, maxSize).
  Preconditions: Let s1 and s2 be byte strings and phi a bijection from the set of ASCII lowercase letters to itself. Both parameter sets (s1,maxLetters,minSize,maxSize) and (s2,maxLetters,minSize,maxSize) satisfy: len(s1) = len(s2) is between 1 and 100000 inclusive; 1 <= maxLetters <= 26; 1 <= minSize <= maxSize <= 26; maxSize <= len(s1); every byte of s1 and s2 is an ASCII lowercase letter; and s2[i] = phi(s1[i]) for every i with 0 <= i < len(s1). -/
theorem spec_13 (s1 s2 : Slice Std.U8) (phi : Nat → Nat)
    (maxLetters minSize maxSize : Std.I64)
    (h_len_lo : 1 ≤ slen s1) (h_len_hi : slen s1 ≤ 100000) (h_len_eq : slen s2 = slen s1)
    (h_maxLetters_lo : 1 ≤ maxLetters.val) (h_maxLetters_hi : maxLetters.val ≤ 26)
    (h_minSize_lo : 1 ≤ minSize.val) (h_minSize_le : minSize.val ≤ maxSize.val)
    (h_maxSize_hi : maxSize.val ≤ 26) (h_maxSize_le : maxSize.val ≤ (slen s1 : Int))
    (h_lower1 : ∀ b ∈ s1.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (h_lower2 : ∀ b ∈ s2.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (h_phi_maps : ∀ x : Nat, 97 ≤ x → x ≤ 122 → 97 ≤ phi x ∧ phi x ≤ 122)
    (h_phi_inj : ∀ x y : Nat, 97 ≤ x → x ≤ 122 → 97 ≤ y → y ≤ 122 → phi x = phi y → x = y)
    (h_map : toBytes s2 = (toBytes s1).map phi) :
    ∃ r1 r2 : Std.I64,
      Aegis.MaxFreq.max_freq s1 maxLetters minSize maxSize = ok r1 ∧
      Aegis.MaxFreq.max_freq s2 maxLetters minSize maxSize = ok r2 ∧
      r1.val = r2.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (s1 s2 : Slice Std.U8) (phi : Nat → Nat)
    (maxLetters minSize maxSize : Std.I64)
    (h_len_lo : 1 ≤ slen s1) (h_len_hi : slen s1 ≤ 100000) (h_len_eq : slen s2 = slen s1)
    (h_maxLetters_lo : 1 ≤ maxLetters.val) (h_maxLetters_hi : maxLetters.val ≤ 26)
    (h_minSize_lo : 1 ≤ minSize.val) (h_minSize_le : minSize.val ≤ maxSize.val)
    (h_maxSize_hi : maxSize.val ≤ 26) (h_maxSize_le : maxSize.val ≤ (slen s1 : Int))
    (h_lower1 : ∀ b ∈ s1.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (h_lower2 : ∀ b ∈ s2.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (h_phi_maps : ∀ x : Nat, 97 ≤ x → x ≤ 122 → 97 ≤ phi x ∧ phi x ≤ 122)
    (h_phi_inj : ∀ x y : Nat, 97 ≤ x → x ≤ 122 → 97 ≤ y → y ≤ 122 → phi x = phi y → x = y)
    (h_map : toBytes s2 = (toBytes s1).map phi), ∃ r1 r2 : Std.I64,
      Aegis.MaxFreq.max_freq s1 maxLetters minSize maxSize = ok r1 ∧
      Aegis.MaxFreq.max_freq s2 maxLetters minSize maxSize = ok r2 ∧
      r1.val = r2.val) := by
  sorry

/-- The function returns a result r and r = 0 if and only if for every start i and every length L with minSize <= L <= maxSize and 0 <= i <= len(s)-L, the substring s[i..i+L) contains more than maxLetters distinct byte values.
  Preconditions: len(s) is between 1 and 100000 inclusive; 1 <= maxLetters <= 26; 1 <= minSize <= maxSize <= 26; maxSize <= len(s); every byte of s is an ASCII lowercase letter. -/
theorem spec_14 (s : Slice Std.U8) (maxLetters minSize maxSize : Std.I64)
    (h_len_lo : 1 ≤ slen s) (h_len_hi : slen s ≤ 100000)
    (h_maxLetters_lo : 1 ≤ maxLetters.val) (h_maxLetters_hi : maxLetters.val ≤ 26)
    (h_minSize_lo : 1 ≤ minSize.val) (h_minSize_le : minSize.val ≤ maxSize.val)
    (h_maxSize_hi : maxSize.val ≤ 26) (h_maxSize_le : maxSize.val ≤ (slen s : Int))
    (h_lower : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122) :
    ∃ r : Std.I64,
      Aegis.MaxFreq.max_freq s maxLetters minSize maxSize = ok r ∧
      (r.val = 0 ↔ ∀ (i L : Nat), minSize.val.toNat ≤ L → L ≤ maxSize.val.toNat →
        i + L ≤ slen s → maxLetters.val.toNat < distinct (window s i L)) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (s : Slice Std.U8) (maxLetters minSize maxSize : Std.I64)
    (h_len_lo : 1 ≤ slen s) (h_len_hi : slen s ≤ 100000)
    (h_maxLetters_lo : 1 ≤ maxLetters.val) (h_maxLetters_hi : maxLetters.val ≤ 26)
    (h_minSize_lo : 1 ≤ minSize.val) (h_minSize_le : minSize.val ≤ maxSize.val)
    (h_maxSize_hi : maxSize.val ≤ 26) (h_maxSize_le : maxSize.val ≤ (slen s : Int))
    (h_lower : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122), ∃ r : Std.I64,
      Aegis.MaxFreq.max_freq s maxLetters minSize maxSize = ok r ∧
      (r.val = 0 ↔ ∀ (i L : Nat), minSize.val.toNat ≤ L → L ≤ maxSize.val.toNat →
        i + L ≤ slen s → maxLetters.val.toNat < distinct (window s i L))) := by
  sorry

/-- Let distinct(t) be the number of distinct byte values in t, and let occ(t) be the number of starts i with 0 <= i <= len(s)-len(t) and s[i+j] = t[j] for every 0 <= j < len(t). The function returns a result r and r = max { occ(t) | t is a byte string, len(t) = minSize, distinct(t) <= maxLetters }. Equivalently, the maximum over all valid substrings is always attained at length minSize.
  Preconditions: len(s) is between 1 and 100000 inclusive; 1 <= maxLetters <= 26; 1 <= minSize <= maxSize <= 26; maxSize <= len(s); every byte of s is an ASCII lowercase letter. -/
theorem spec_15 (s : Slice Std.U8) (maxLetters minSize maxSize : Std.I64)
    (h_len_lo : 1 ≤ slen s) (h_len_hi : slen s ≤ 100000)
    (h_maxLetters_lo : 1 ≤ maxLetters.val) (h_maxLetters_hi : maxLetters.val ≤ 26)
    (h_minSize_lo : 1 ≤ minSize.val) (h_minSize_le : minSize.val ≤ maxSize.val)
    (h_maxSize_hi : maxSize.val ≤ 26) (h_maxSize_le : maxSize.val ≤ (slen s : Int))
    (h_lower : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122) :
    ∃ r : Std.I64,
      Aegis.MaxFreq.max_freq s maxLetters minSize maxSize = ok r ∧
      r.val = (bestOccFixedLen s maxLetters.val.toNat minSize.val.toNat : Int) := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (s : Slice Std.U8) (maxLetters minSize maxSize : Std.I64)
    (h_len_lo : 1 ≤ slen s) (h_len_hi : slen s ≤ 100000)
    (h_maxLetters_lo : 1 ≤ maxLetters.val) (h_maxLetters_hi : maxLetters.val ≤ 26)
    (h_minSize_lo : 1 ≤ minSize.val) (h_minSize_le : minSize.val ≤ maxSize.val)
    (h_maxSize_hi : maxSize.val ≤ 26) (h_maxSize_le : maxSize.val ≤ (slen s : Int))
    (h_lower : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122), ∃ r : Std.I64,
      Aegis.MaxFreq.max_freq s maxLetters minSize maxSize = ok r ∧
      r.val = (bestOccFixedLen s maxLetters.val.toNat minSize.val.toNat : Int)) := by
  sorry

/-- Let r1 = max_freq(s, maxLetters, minSize, maxSize1) and r2 = max_freq(s, maxLetters, minSize, maxSize2). Both calls return results and r1 = r2.
  Preconditions: len(s) is between 1 and 100000 inclusive; 1 <= maxLetters <= 26; 1 <= minSize <= maxSize1 <= maxSize2 <= 26; maxSize2 <= len(s); every byte of s is an ASCII lowercase letter. -/
theorem spec_16 (s : Slice Std.U8) (maxLetters minSize maxSize1 maxSize2 : Std.I64)
    (h_len_lo : 1 ≤ slen s) (h_len_hi : slen s ≤ 100000)
    (h_maxLetters_lo : 1 ≤ maxLetters.val) (h_maxLetters_hi : maxLetters.val ≤ 26)
    (h_minSize_lo : 1 ≤ minSize.val) (h_minSize_le : minSize.val ≤ maxSize1.val)
    (h_maxSize_le : maxSize1.val ≤ maxSize2.val) (h_maxSize2_hi : maxSize2.val ≤ 26)
    (h_maxSize2_len : maxSize2.val ≤ (slen s : Int))
    (h_lower : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122) :
    ∃ r1 r2 : Std.I64,
      Aegis.MaxFreq.max_freq s maxLetters minSize maxSize1 = ok r1 ∧
      Aegis.MaxFreq.max_freq s maxLetters minSize maxSize2 = ok r2 ∧
      r1.val = r2.val := by
  sorry

theorem spec_16_neg :
    ¬ (∀ (s : Slice Std.U8) (maxLetters minSize maxSize1 maxSize2 : Std.I64)
    (h_len_lo : 1 ≤ slen s) (h_len_hi : slen s ≤ 100000)
    (h_maxLetters_lo : 1 ≤ maxLetters.val) (h_maxLetters_hi : maxLetters.val ≤ 26)
    (h_minSize_lo : 1 ≤ minSize.val) (h_minSize_le : minSize.val ≤ maxSize1.val)
    (h_maxSize_le : maxSize1.val ≤ maxSize2.val) (h_maxSize2_hi : maxSize2.val ≤ 26)
    (h_maxSize2_len : maxSize2.val ≤ (slen s : Int))
    (h_lower : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122), ∃ r1 r2 : Std.I64,
      Aegis.MaxFreq.max_freq s maxLetters minSize maxSize1 = ok r1 ∧
      Aegis.MaxFreq.max_freq s maxLetters minSize maxSize2 = ok r2 ∧
      r1.val = r2.val) := by
  sorry

end AegisSpec.MaxFreq
