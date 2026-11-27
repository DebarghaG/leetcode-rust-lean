import Aegis.NumDecodings.Code.Funs

/-!
# Specifications of `Aegis.NumDecodings.num_decodings`

LeetCode problem `decode-ways-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.NumDecodings

def M : ℕ := 1000000007

def residue (a : ℕ) : ℤ := ((a % M : ℕ) : ℤ)

def IsDigitByte (b : U8) : Prop := 48 ≤ b.val ∧ b.val ≤ 57

def IsStarByte (b : U8) : Prop := b.val = 42

def IsNonzeroDigitByte (b : U8) : Prop := 49 ≤ b.val ∧ b.val ≤ 57

def byteAt (s : List U8) (i : ℕ) : ℕ := ((s[i]?).map (fun b => b.val)).getD 0

def blockDigits (v : ℕ) : List ℕ := if v ≤ 9 then [v] else [v / 10, v % 10]

def ValidBlockValue (v : ℕ) : Prop := 1 ≤ v ∧ v ≤ 26

def blockLen (v : ℕ) : ℕ := (blockDigits v).length

def digits (bs : List ℕ) : List ℕ := bs.flatMap blockDigits

def digitAt (bs : List ℕ) (i : ℕ) : Option ℕ := (digits bs)[i]?

def byteMatchesDigit (d : ℕ) (b : U8) : Bool :=
  if b.val = 42 then decide (1 ≤ d ∧ d ≤ 9)
  else if 48 ≤ b.val ∧ b.val ≤ 57 then decide (d = b.val - 48)
  else false

def matchesDigits (ds : List ℕ) (s : List U8) : Bool :=
  ds.length == s.length && (ds.zipWith byteMatchesDigit s).all id

def validBlocks (bs : List ℕ) : Bool := bs.all (fun v => decide (1 ≤ v ∧ v ≤ 26))

def ValidDecoding (s : List U8) (bs : List ℕ) : Prop :=
  validBlocks bs = true ∧ matchesDigits (digits bs) s = true

def blockListsOfLen : ℕ → List (List ℕ)
  | 0 => [[]]
  | k + 1 =>
    (blockListsOfLen k).flatMap (fun bs => (List.range 26).map (fun j => (j + 1) :: bs))

def blockListsUpTo (n : ℕ) : List (List ℕ) :=
  (List.range (n + 1)).flatMap blockListsOfLen

def W (s : List U8) : ℕ :=
  ((blockListsUpTo s.length).filter (fun bs => validBlocks bs && matchesDigits (digits bs) s)).length

def D (t : List ℕ) : ℕ :=
  ((blockListsUpTo t.length).filter (fun bs => validBlocks bs && (digits bs == t))).length

def wildcardExpansions : List U8 → List (List ℕ)
  | [] => [[]]
  | b :: rest =>
    (if b.val = 42 then (List.range 9).map (fun k => k + 1)
     else if 48 ≤ b.val ∧ b.val ≤ 57 then [b.val - 48]
     else []).flatMap (fun d => (wildcardExpansions rest).map (fun t => d :: t))

def Fib : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | k + 2 => Fib (k + 1) + Fib k

def AllStarCount : ℕ → ℕ
  | 0 => 1
  | 1 => 9
  | k + 2 => 9 * AllStarCount (k + 1) + 15 * AllStarCount k

/-- Whenever num_decodings(s) returns a result r, r is the canonical residue modulo M = 1000000007 of the number W(s) of valid decodings of s: 0 <= r < M and r ≡ W(s) (mod M). A valid decoding consists of a wildcard assignment replacing every '*' byte by a digit in {1,...,9}, keeping every literal digit byte unchanged, together with a partition of the index range 0..len(s)-1 into consecutive blocks of length 1 or 2 such that every length-1 block [i,i] has chosen digit in {1,...,9}, and every length-2 block [i,i+1] has chosen two-digit value 10*d_i+d_{i+1} in {10,...,26} (so the first digit is 1 or 2; a 0 can occur only as a literal second digit of 10 or 20). W(s) is the total number of such pairs of wildcard assignment and partition; this is exactly the number of decoded letter strings, since a block value 1..26 determines its letter A..Z.
  Preconditions: 1 <= len(s) <= 100000; for every i with 0 <= i < len(s), s[i] is the ASCII code of a digit '0'..'9' or of '*'. -/
theorem spec_1 (s : Slice U8)
    (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 100000)
    (hbytes : ∀ b ∈ s.val, IsDigitByte b ∨ IsStarByte b) :
    ∀ r : I64, Aegis.NumDecodings.num_decodings s = Result.ok r →
      0 ≤ r.val ∧ r.val < (M : ℤ) ∧ r.val ≡ (W s.val : ℤ) [ZMOD (M : ℤ)] := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice U8)
    (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 100000)
    (hbytes : ∀ b ∈ s.val, IsDigitByte b ∨ IsStarByte b), ∀ r : I64, Aegis.NumDecodings.num_decodings s = Result.ok r →
      0 ≤ r.val ∧ r.val < (M : ℤ) ∧ r.val ≡ (W s.val : ℤ) [ZMOD (M : ℤ)]) := by
  sorry

/-- For every s satisfying the preconditions, num_decodings(s) returns a result (Result.ok r) and does not fail: there is no overflow, out-of-bounds access, or panic.
  Preconditions: 1 <= len(s) <= 100000; for every i with 0 <= i < len(s), s[i] is the ASCII code of a digit '0'..'9' or of '*'. -/
theorem spec_2 (s : Slice U8)
    (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 100000)
    (hbytes : ∀ b ∈ s.val, IsDigitByte b ∨ IsStarByte b) :
    ∃ r : I64, Aegis.NumDecodings.num_decodings s = Result.ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice U8)
    (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 100000)
    (hbytes : ∀ b ∈ s.val, IsDigitByte b ∨ IsStarByte b), ∃ r : I64, Aegis.NumDecodings.num_decodings s = Result.ok r) := by
  sorry

/-- Whenever num_decodings(s) returns a result r, the returned integer satisfies 0 <= r < 1000000007.
  Preconditions: 1 <= len(s) <= 100000; for every i with 0 <= i < len(s), s[i] is the ASCII code of a digit '0'..'9' or of '*'. -/
theorem spec_3 (s : Slice U8)
    (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 100000)
    (hbytes : ∀ b ∈ s.val, IsDigitByte b ∨ IsStarByte b) :
    ∀ r : I64, Aegis.NumDecodings.num_decodings s = Result.ok r →
      0 ≤ r.val ∧ r.val < (M : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice U8)
    (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 100000)
    (hbytes : ∀ b ∈ s.val, IsDigitByte b ∨ IsStarByte b), ∀ r : I64, Aegis.NumDecodings.num_decodings s = Result.ok r →
      0 ≤ r.val ∧ r.val < (M : ℤ)) := by
  sorry

/-- The function returns r = 1.
  Preconditions: 1 <= len(s) <= 100000; for every i with 0 <= i < len(s), s[i] is the ASCII code of a digit '0'..'9' or of '*'; len(s) = 1; s[0] is the ASCII code of a digit '1'..'9'. -/
theorem spec_4 (s : Slice U8)
    (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 100000)
    (hbytes : ∀ b ∈ s.val, IsDigitByte b ∨ IsStarByte b)
    (hlen : s.val.length = 1) (hs0 : 49 ≤ byteAt s.val 0 ∧ byteAt s.val 0 ≤ 57) :
    ∃ r : I64, Aegis.NumDecodings.num_decodings s = Result.ok r ∧ r.val = 1 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice U8)
    (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 100000)
    (hbytes : ∀ b ∈ s.val, IsDigitByte b ∨ IsStarByte b)
    (hlen : s.val.length = 1) (hs0 : 49 ≤ byteAt s.val 0 ∧ byteAt s.val 0 ≤ 57), ∃ r : I64, Aegis.NumDecodings.num_decodings s = Result.ok r ∧ r.val = 1) := by
  sorry

/-- The function returns r = 9.
  Preconditions: 1 <= len(s) <= 100000; for every i with 0 <= i < len(s), s[i] is the ASCII code of a digit '0'..'9' or of '*'; len(s) = 1; s[0] is the ASCII code of '*'. -/
theorem spec_5 (s : Slice U8)
    (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 100000)
    (hbytes : ∀ b ∈ s.val, IsDigitByte b ∨ IsStarByte b)
    (hlen : s.val.length = 1) (hs0 : byteAt s.val 0 = 42) :
    ∃ r : I64, Aegis.NumDecodings.num_decodings s = Result.ok r ∧ r.val = 9 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice U8)
    (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 100000)
    (hbytes : ∀ b ∈ s.val, IsDigitByte b ∨ IsStarByte b)
    (hlen : s.val.length = 1) (hs0 : byteAt s.val 0 = 42), ∃ r : I64, Aegis.NumDecodings.num_decodings s = Result.ok r ∧ r.val = 9) := by
  sorry

/-- The function returns r = 0.
  Preconditions: 1 <= len(s) <= 100000; for every i with 0 <= i < len(s), s[i] is the ASCII code of a digit '0'..'9' or of '*'; len(s) >= 1; s[0] is the ASCII code of '0'. -/
theorem spec_6 (s : Slice U8)
    (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 100000)
    (hbytes : ∀ b ∈ s.val, IsDigitByte b ∨ IsStarByte b)
    (hs0 : byteAt s.val 0 = 48) :
    ∃ r : I64, Aegis.NumDecodings.num_decodings s = Result.ok r ∧ r.val = 0 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice U8)
    (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 100000)
    (hbytes : ∀ b ∈ s.val, IsDigitByte b ∨ IsStarByte b)
    (hs0 : byteAt s.val 0 = 48), ∃ r : I64, Aegis.NumDecodings.num_decodings s = Result.ok r ∧ r.val = 0) := by
  sorry

/-- The function returns r = 1 if s[0] is the ASCII code of '1' or '2'; returns r = 2 if s[0] is the ASCII code of '*'; and returns r = 0 if s[0] is the ASCII code of '0' or of a digit '3'..'9'.
  Preconditions: 1 <= len(s) <= 100000; for every i with 0 <= i < len(s), s[i] is the ASCII code of a digit '0'..'9' or of '*'; len(s) = 2; s[1] is the ASCII code of '0'. -/
theorem spec_7 (s : Slice U8)
    (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 100000)
    (hbytes : ∀ b ∈ s.val, IsDigitByte b ∨ IsStarByte b)
    (hlen : s.val.length = 2) (hs1 : byteAt s.val 1 = 48) :
    ∀ r : I64, Aegis.NumDecodings.num_decodings s = Result.ok r →
      ((byteAt s.val 0 = 49 ∨ byteAt s.val 0 = 50) → r.val = 1) ∧
      (byteAt s.val 0 = 42 → r.val = 2) ∧
      ((byteAt s.val 0 = 48 ∨ (51 ≤ byteAt s.val 0 ∧ byteAt s.val 0 ≤ 57)) → r.val = 0) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice U8)
    (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 100000)
    (hbytes : ∀ b ∈ s.val, IsDigitByte b ∨ IsStarByte b)
    (hlen : s.val.length = 2) (hs1 : byteAt s.val 1 = 48), ∀ r : I64, Aegis.NumDecodings.num_decodings s = Result.ok r →
      ((byteAt s.val 0 = 49 ∨ byteAt s.val 0 = 50) → r.val = 1) ∧
      (byteAt s.val 0 = 42 → r.val = 2) ∧
      ((byteAt s.val 0 = 48 ∨ (51 ≤ byteAt s.val 0 ∧ byteAt s.val 0 ≤ 57)) → r.val = 0)) := by
  sorry

/-- Let E(s) be the set of digit strings obtained from s by replacing each '*' byte independently by one of the digits '1'..'9' and keeping all literal digits fixed. For a digit string t, let D(t) be the ordinary number of decodings of t: the number of partitions of t's indices into consecutive blocks of length 1 or 2 such that each length-1 block is a digit 1..9 and each length-2 block has value 10..26. Then whenever num_decodings(s) returns r, r is the canonical residue modulo 1000000007 of the sum over all t in E(s) of D(t).
  Preconditions: 1 <= len(s) <= 100000; for every i with 0 <= i < len(s), s[i] is the ASCII code of a digit '0'..'9' or of '*'. -/
theorem spec_8 (s : Slice U8)
    (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 100000)
    (hbytes : ∀ b ∈ s.val, IsDigitByte b ∨ IsStarByte b) :
    ∀ r : I64, Aegis.NumDecodings.num_decodings s = Result.ok r →
      r.val ≡ (((wildcardExpansions s.val).map D).sum : ℤ) [ZMOD (M : ℤ)] := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s : Slice U8)
    (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 100000)
    (hbytes : ∀ b ∈ s.val, IsDigitByte b ∨ IsStarByte b), ∀ r : I64, Aegis.NumDecodings.num_decodings s = Result.ok r →
      r.val ≡ (((wildcardExpansions s.val).map D).sum : ℤ) [ZMOD (M : ℤ)]) := by
  sorry

/-- Whenever num_decodings(s) returns r, r = F_{n+1} mod 1000000007, where F_1 = 1, F_2 = 1, and F_k = F_{k-1} + F_{k-2} for k >= 3, and the right side is the canonical residue in [0,1000000007).
  Preconditions: 1 <= len(s) <= 100000; for every i with 0 <= i < len(s), s[i] is the ASCII code of a digit '0'..'9' or of '*'; len(s) = n >= 1; for every i with 0 <= i < n, s[i] is the ASCII code of '1'. -/
theorem spec_9 (s : Slice U8) (n : ℕ)
    (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 100000)
    (hbytes : ∀ b ∈ s.val, IsDigitByte b ∨ IsStarByte b)
    (hlen : s.val.length = n) (hn : 1 ≤ n)
    (hones : ∀ b ∈ s.val, b.val = 49) :
    ∀ r : I64, Aegis.NumDecodings.num_decodings s = Result.ok r →
      r.val = residue (Fib (n + 1)) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s : Slice U8) (n : ℕ)
    (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 100000)
    (hbytes : ∀ b ∈ s.val, IsDigitByte b ∨ IsStarByte b)
    (hlen : s.val.length = n) (hn : 1 ≤ n)
    (hones : ∀ b ∈ s.val, b.val = 49), ∀ r : I64, Aegis.NumDecodings.num_decodings s = Result.ok r →
      r.val = residue (Fib (n + 1))) := by
  sorry

/-- Whenever num_decodings(s) returns a result r with r != 0, there exists at least one valid decoding of s, equivalently W(s) > 0. In particular, if s has no valid decoding then r = 0.
  Preconditions: 1 <= len(s) <= 100000; for every i with 0 <= i < len(s), s[i] is the ASCII code of a digit '0'..'9' or of '*'. -/
theorem spec_10 (s : Slice U8)
    (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 100000)
    (hbytes : ∀ b ∈ s.val, IsDigitByte b ∨ IsStarByte b) :
    (∀ r : I64, Aegis.NumDecodings.num_decodings s = Result.ok r → r.val ≠ 0 → 0 < W s.val) ∧
    (∀ r : I64, Aegis.NumDecodings.num_decodings s = Result.ok r → W s.val = 0 → r.val = 0) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s : Slice U8)
    (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 100000)
    (hbytes : ∀ b ∈ s.val, IsDigitByte b ∨ IsStarByte b), (∀ r : I64, Aegis.NumDecodings.num_decodings s = Result.ok r → r.val ≠ 0 → 0 < W s.val) ∧
    (∀ r : I64, Aegis.NumDecodings.num_decodings s = Result.ok r → W s.val = 0 → r.val = 0)) := by
  sorry

/-- Let W_0 = 1 and W_1 = 9, and for k >= 2 let W_k = 9*W_{k-1} + 15*W_{k-2}. Whenever num_decodings(s) returns r, r = W_n mod 1000000007 in canonical form.
  Preconditions: 1 <= len(s) <= 100000; for every i with 0 <= i < len(s), s[i] is the ASCII code of '*'; len(s) = n >= 1. -/
theorem spec_11 (s : Slice U8) (n : ℕ)
    (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 100000)
    (hbytes : ∀ b ∈ s.val, IsStarByte b)
    (hlen : s.val.length = n) (hn : 1 ≤ n) :
    ∀ r : I64, Aegis.NumDecodings.num_decodings s = Result.ok r →
      r.val = residue (AllStarCount n) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s : Slice U8) (n : ℕ)
    (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 100000)
    (hbytes : ∀ b ∈ s.val, IsStarByte b)
    (hlen : s.val.length = n) (hn : 1 ≤ n), ∀ r : I64, Aegis.NumDecodings.num_decodings s = Result.ok r →
      r.val = residue (AllStarCount n)) := by
  sorry

end AegisSpec.NumDecodings
