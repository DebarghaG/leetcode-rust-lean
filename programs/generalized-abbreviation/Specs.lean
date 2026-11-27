import Aegis.GenerateAbbreviations.Code.Funs

/-!
# Specifications of `Aegis.GenerateAbbreviations.generate_abbreviations`

LeetCode problem `generalized-abbreviation`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.GenerateAbbreviations

def isDigitByte (b : Nat) : Bool := decide (48 ≤ b ∧ b ≤ 57)

def isLowerByte (b : Nat) : Bool := decide (97 ≤ b ∧ b ≤ 122)

def digitsOf (n : Nat) : List Nat := (Nat.toDigits 10 n).map (fun c => c.toNat)

def bytes (l : List Std.U8) : List Nat := l.map (fun b => b.val)

def entry (v : List (alloc.vec.Vec Std.U8)) (j : Nat) : List Nat :=
  match v[j]? with
  | none => []
  | some w => bytes w.val

def abbrevScan (w : List Nat) (mask : Nat → Bool) : List Nat :=
  let step : List Nat × Nat → Nat → List Nat × Nat := fun acc i =>
    if mask i then
      (acc.1, acc.2 + 1)
    else
      (acc.1 ++ (if acc.2 = 0 then [] else digitsOf acc.2) ++ [w.getD i 0], 0)
  let final : List Nat × Nat := (List.range w.length).foldl step ([], 0)
  final.1 ++ (if final.2 = 0 then [] else digitsOf final.2)

def IsGenAbbrev (w s : List Nat) : Prop :=
  ∃ mask : Nat → Bool, abbrevScan w mask = s

def sliceAbbrev (w : List Nat) (a b : Nat) : List Nat :=
  w.take a ++ digitsOf (b - a) ++ w.drop b

def startsDigitRun (l : List Nat) (k : Nat) : Bool :=
  decide (k < l.length ∧ isDigitByte (l[k]!) = true ∧
    (k = 0 ∨ isDigitByte (l[k - 1]!) = false))

def digitRuns (l : List Nat) : List (List Nat) :=
  (List.range l.length).filterMap fun k =>
    if startsDigitRun l k then some ((l.drop k).takeWhile isDigitByte) else none

def digitValue (l : List Nat) : Nat := l.foldl (fun acc b => acc * 10 + (b - 48)) 0

def countLetters (l : List Nat) : Nat := (l.filter isLowerByte).length

def sumDigitRuns (l : List Nat) : Nat := ((digitRuns l).map digitValue).sum

def removeDigits (l : List Nat) : List Nat := l.filter (fun b => !isDigitByte b)

/-- Whenever the function returns a result r, let n = len(word). Then r is a duplicate-free list whose entries are exactly all valid generalized abbreviations of word, in any order. Formally: (1) for every byte vector s, there exists j with 0 <= j < len(r) and r[j] = s if and only if there exists a Boolean mask m on the indices 0,...,n-1 such that s is obtained by scanning i = 0,...,n-1, writing word[i] when m(i) is false, and writing the ASCII decimal representation of the length of each maximal consecutive run of true indices once at the start of that run; (2) for all j,k with 0 <= j < len(r) and 0 <= k < len(r), if r[j] = r[k] then j = k.
  Preconditions: word is a byte array with 1 <= len(word) <= 15, and for every i with 0 <= i < len(word), word[i] is an ASCII lowercase English letter (97 <= word[i] <= 122). -/
theorem spec_1 (word : Slice Std.U8) (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (h1 : 1 ≤ word.val.length) (h2 : word.val.length ≤ 15)
    (h3 : ∀ (i : Nat) (hi : i < word.val.length),
      97 ≤ (word.val[i]'hi).val ∧ (word.val[i]'hi).val ≤ 122)
    (hr : Aegis.GenerateAbbreviations.generate_abbreviations word = ok r) :
    (∀ s : List Nat,
        (∃ j, j < r.val.length ∧ entry r.val j = s) ↔ IsGenAbbrev (bytes word.val) s) ∧
      (∀ j k, j < r.val.length → k < r.val.length →
        entry r.val j = entry r.val k → j = k) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (word : Slice Std.U8) (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (h1 : 1 ≤ word.val.length) (h2 : word.val.length ≤ 15)
    (h3 : ∀ (i : Nat) (hi : i < word.val.length),
      97 ≤ (word.val[i]'hi).val ∧ (word.val[i]'hi).val ≤ 122)
    (hr : Aegis.GenerateAbbreviations.generate_abbreviations word = ok r), (∀ s : List Nat,
        (∃ j, j < r.val.length ∧ entry r.val j = s) ↔ IsGenAbbrev (bytes word.val) s) ∧
      (∀ j k, j < r.val.length → k < r.val.length →
        entry r.val j = entry r.val k → j = k)) := by
  sorry

/-- For every input word satisfying the preconditions, the function returns a result r; it does not panic, overflow, access out of bounds, or otherwise fail.
  Preconditions: word is a byte array with 1 <= len(word) <= 15, and for every i with 0 <= i < len(word), word[i] is an ASCII lowercase English letter (97 <= word[i] <= 122). -/
theorem spec_2 (word : Slice Std.U8)
    (h1 : 1 ≤ word.val.length) (h2 : word.val.length ≤ 15)
    (h3 : ∀ (i : Nat) (hi : i < word.val.length),
      97 ≤ (word.val[i]'hi).val ∧ (word.val[i]'hi).val ≤ 122) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      Aegis.GenerateAbbreviations.generate_abbreviations word = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (word : Slice Std.U8)
    (h1 : 1 ≤ word.val.length) (h2 : word.val.length ≤ 15)
    (h3 : ∀ (i : Nat) (hi : i < word.val.length),
      97 ≤ (word.val[i]'hi).val ∧ (word.val[i]'hi).val ≤ 122), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      Aegis.GenerateAbbreviations.generate_abbreviations word = ok r) := by
  sorry

/-- Whenever the function returns a result r, let n = len(word). Then len(r) = 2^n.
  Preconditions: word is a byte array with 1 <= len(word) <= 15, and for every i with 0 <= i < len(word), word[i] is an ASCII lowercase English letter (97 <= word[i] <= 122). -/
theorem spec_3 (word : Slice Std.U8) (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (h1 : 1 ≤ word.val.length) (h2 : word.val.length ≤ 15)
    (h3 : ∀ (i : Nat) (hi : i < word.val.length),
      97 ≤ (word.val[i]'hi).val ∧ (word.val[i]'hi).val ≤ 122)
    (hr : Aegis.GenerateAbbreviations.generate_abbreviations word = ok r) :
    r.val.length = 2 ^ word.val.length := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (word : Slice Std.U8) (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (h1 : 1 ≤ word.val.length) (h2 : word.val.length ≤ 15)
    (h3 : ∀ (i : Nat) (hi : i < word.val.length),
      97 ≤ (word.val[i]'hi).val ∧ (word.val[i]'hi).val ≤ 122)
    (hr : Aegis.GenerateAbbreviations.generate_abbreviations word = ok r), r.val.length = 2 ^ word.val.length) := by
  sorry

/-- Whenever the function returns a result r, let n = len(word). For every j with 0 <= j < len(r), the byte vector r[j] is a valid generalized abbreviation of word. Here this means there exists a Boolean mask m on the indices 0,...,n-1 such that r[j] is obtained by scanning i = 0,...,n-1, writing word[i] when m(i) is false, and writing the ASCII decimal representation of the length of each maximal consecutive run of true indices once at the start of that run.
  Preconditions: word is a byte array with 1 <= len(word) <= 15, and for every i with 0 <= i < len(word), word[i] is an ASCII lowercase English letter (97 <= word[i] <= 122). -/
theorem spec_4 (word : Slice Std.U8) (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (h1 : 1 ≤ word.val.length) (h2 : word.val.length ≤ 15)
    (h3 : ∀ (i : Nat) (hi : i < word.val.length),
      97 ≤ (word.val[i]'hi).val ∧ (word.val[i]'hi).val ≤ 122)
    (hr : Aegis.GenerateAbbreviations.generate_abbreviations word = ok r) :
    ∀ j, j < r.val.length → IsGenAbbrev (bytes word.val) (entry r.val j) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (word : Slice Std.U8) (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (h1 : 1 ≤ word.val.length) (h2 : word.val.length ≤ 15)
    (h3 : ∀ (i : Nat) (hi : i < word.val.length),
      97 ≤ (word.val[i]'hi).val ∧ (word.val[i]'hi).val ≤ 122)
    (hr : Aegis.GenerateAbbreviations.generate_abbreviations word = ok r), ∀ j, j < r.val.length → IsGenAbbrev (bytes word.val) (entry r.val j)) := by
  sorry

/-- Whenever the function returns a result r, let n = len(word). For every byte vector s, if there exists a Boolean mask m on the indices 0,...,n-1 such that s is obtained by scanning i = 0,...,n-1, writing word[i] when m(i) is false, and writing the ASCII decimal representation of the length of each maximal consecutive run of true indices once at the start of that run, then there exists j with 0 <= j < len(r) such that r[j] = s.
  Preconditions: word is a byte array with 1 <= len(word) <= 15, and for every i with 0 <= i < len(word), word[i] is an ASCII lowercase English letter (97 <= word[i] <= 122). -/
theorem spec_5 (word : Slice Std.U8) (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (h1 : 1 ≤ word.val.length) (h2 : word.val.length ≤ 15)
    (h3 : ∀ (i : Nat) (hi : i < word.val.length),
      97 ≤ (word.val[i]'hi).val ∧ (word.val[i]'hi).val ≤ 122)
    (hr : Aegis.GenerateAbbreviations.generate_abbreviations word = ok r) :
    ∀ s : List Nat, IsGenAbbrev (bytes word.val) s →
      ∃ j, j < r.val.length ∧ entry r.val j = s := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (word : Slice Std.U8) (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (h1 : 1 ≤ word.val.length) (h2 : word.val.length ≤ 15)
    (h3 : ∀ (i : Nat) (hi : i < word.val.length),
      97 ≤ (word.val[i]'hi).val ∧ (word.val[i]'hi).val ≤ 122)
    (hr : Aegis.GenerateAbbreviations.generate_abbreviations word = ok r), ∀ s : List Nat, IsGenAbbrev (bytes word.val) s →
      ∃ j, j < r.val.length ∧ entry r.val j = s) := by
  sorry

/-- Whenever the function returns a result r, for all j,k with 0 <= j < len(r) and 0 <= k < len(r), if r[j] = r[k] then j = k. Equivalently, the list r contains no repeated byte vector.
  Preconditions: word is a byte array with 1 <= len(word) <= 15, and for every i with 0 <= i < len(word), word[i] is an ASCII lowercase English letter (97 <= word[i] <= 122). -/
theorem spec_6 (word : Slice Std.U8) (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (h1 : 1 ≤ word.val.length) (h2 : word.val.length ≤ 15)
    (h3 : ∀ (i : Nat) (hi : i < word.val.length),
      97 ≤ (word.val[i]'hi).val ∧ (word.val[i]'hi).val ≤ 122)
    (hr : Aegis.GenerateAbbreviations.generate_abbreviations word = ok r) :
    ∀ j k, j < r.val.length → k < r.val.length →
      entry r.val j = entry r.val k → j = k := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (word : Slice Std.U8) (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (h1 : 1 ≤ word.val.length) (h2 : word.val.length ≤ 15)
    (h3 : ∀ (i : Nat) (hi : i < word.val.length),
      97 ≤ (word.val[i]'hi).val ∧ (word.val[i]'hi).val ≤ 122)
    (hr : Aegis.GenerateAbbreviations.generate_abbreviations word = ok r), ∀ j k, j < r.val.length → k < r.val.length →
      entry r.val j = entry r.val k → j = k) := by
  sorry

/-- Whenever the function returns a result r, for every j with 0 <= j < len(r), the byte length of r[j] satisfies 1 <= len(r[j]) <= len(word).
  Preconditions: word is a byte array with 1 <= len(word) <= 15, and for every i with 0 <= i < len(word), word[i] is an ASCII lowercase English letter (97 <= word[i] <= 122). -/
theorem spec_7 (word : Slice Std.U8) (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (h1 : 1 ≤ word.val.length) (h2 : word.val.length ≤ 15)
    (h3 : ∀ (i : Nat) (hi : i < word.val.length),
      97 ≤ (word.val[i]'hi).val ∧ (word.val[i]'hi).val ≤ 122)
    (hr : Aegis.GenerateAbbreviations.generate_abbreviations word = ok r) :
    ∀ j, j < r.val.length →
      1 ≤ (entry r.val j).length ∧ (entry r.val j).length ≤ word.val.length := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (word : Slice Std.U8) (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (h1 : 1 ≤ word.val.length) (h2 : word.val.length ≤ 15)
    (h3 : ∀ (i : Nat) (hi : i < word.val.length),
      97 ≤ (word.val[i]'hi).val ∧ (word.val[i]'hi).val ≤ 122)
    (hr : Aegis.GenerateAbbreviations.generate_abbreviations word = ok r), ∀ j, j < r.val.length →
      1 ≤ (entry r.val j).length ∧ (entry r.val j).length ≤ word.val.length) := by
  sorry

/-- Whenever the function returns a result r, for every j with 0 <= j < len(r) and every k with 0 <= k < len(r[j]), the byte r[j][k] is either an ASCII lowercase English letter (97 <= r[j][k] <= 122) or an ASCII digit (48 <= r[j][k] <= 57).
  Preconditions: word is a byte array with 1 <= len(word) <= 15, and for every i with 0 <= i < len(word), word[i] is an ASCII lowercase English letter (97 <= word[i] <= 122). -/
theorem spec_8 (word : Slice Std.U8) (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (h1 : 1 ≤ word.val.length) (h2 : word.val.length ≤ 15)
    (h3 : ∀ (i : Nat) (hi : i < word.val.length),
      97 ≤ (word.val[i]'hi).val ∧ (word.val[i]'hi).val ≤ 122)
    (hr : Aegis.GenerateAbbreviations.generate_abbreviations word = ok r) :
    ∀ (j : Nat), j < r.val.length →
      ∀ (k : Nat) (hk : k < (entry r.val j).length),
        (97 ≤ (entry r.val j)[k]'hk ∧ (entry r.val j)[k]'hk ≤ 122) ∨
          (48 ≤ (entry r.val j)[k]'hk ∧ (entry r.val j)[k]'hk ≤ 57) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (word : Slice Std.U8) (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (h1 : 1 ≤ word.val.length) (h2 : word.val.length ≤ 15)
    (h3 : ∀ (i : Nat) (hi : i < word.val.length),
      97 ≤ (word.val[i]'hi).val ∧ (word.val[i]'hi).val ≤ 122)
    (hr : Aegis.GenerateAbbreviations.generate_abbreviations word = ok r), ∀ (j : Nat), j < r.val.length →
      ∀ (k : Nat) (hk : k < (entry r.val j).length),
        (97 ≤ (entry r.val j)[k]'hk ∧ (entry r.val j)[k]'hk ≤ 122) ∨
          (48 ≤ (entry r.val j)[k]'hk ∧ (entry r.val j)[k]'hk ≤ 57)) := by
  sorry

/-- Whenever the function returns a result r, let n = len(word). For every j with 0 <= j < len(r), each maximal contiguous run of ASCII digit bytes in r[j] is the standard decimal representation, without leading zeros, of an integer L with 1 <= L <= n.
  Preconditions: word is a byte array with 1 <= len(word) <= 15, and for every i with 0 <= i < len(word), word[i] is an ASCII lowercase English letter (97 <= word[i] <= 122). -/
theorem spec_9 (word : Slice Std.U8) (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (h1 : 1 ≤ word.val.length) (h2 : word.val.length ≤ 15)
    (h3 : ∀ (i : Nat) (hi : i < word.val.length),
      97 ≤ (word.val[i]'hi).val ∧ (word.val[i]'hi).val ≤ 122)
    (hr : Aegis.GenerateAbbreviations.generate_abbreviations word = ok r) :
    ∀ j, j < r.val.length →
      ∀ u ∈ digitRuns (entry r.val j),
        ∃ L : Nat, 1 ≤ L ∧ L ≤ word.val.length ∧ u = digitsOf L := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (word : Slice Std.U8) (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (h1 : 1 ≤ word.val.length) (h2 : word.val.length ≤ 15)
    (h3 : ∀ (i : Nat) (hi : i < word.val.length),
      97 ≤ (word.val[i]'hi).val ∧ (word.val[i]'hi).val ≤ 122)
    (hr : Aegis.GenerateAbbreviations.generate_abbreviations word = ok r), ∀ j, j < r.val.length →
      ∀ u ∈ digitRuns (entry r.val j),
        ∃ L : Nat, 1 ≤ L ∧ L ≤ word.val.length ∧ u = digitsOf L) := by
  sorry

/-- Whenever the function returns a result r, let n = len(word). The byte vector word itself occurs in r: there exists j with 0 <= j < len(r) such that len(r[j]) = n and r[j][i] = word[i] for every i with 0 <= i < n.
  Preconditions: word is a byte array with 1 <= len(word) <= 15, and for every i with 0 <= i < len(word), word[i] is an ASCII lowercase English letter (97 <= word[i] <= 122). -/
theorem spec_10 (word : Slice Std.U8) (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (h1 : 1 ≤ word.val.length) (h2 : word.val.length ≤ 15)
    (h3 : ∀ (i : Nat) (hi : i < word.val.length),
      97 ≤ (word.val[i]'hi).val ∧ (word.val[i]'hi).val ≤ 122)
    (hr : Aegis.GenerateAbbreviations.generate_abbreviations word = ok r) :
    ∃ j, j < r.val.length ∧
      (entry r.val j).length = word.val.length ∧ entry r.val j = bytes word.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (word : Slice Std.U8) (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (h1 : 1 ≤ word.val.length) (h2 : word.val.length ≤ 15)
    (h3 : ∀ (i : Nat) (hi : i < word.val.length),
      97 ≤ (word.val[i]'hi).val ∧ (word.val[i]'hi).val ≤ 122)
    (hr : Aegis.GenerateAbbreviations.generate_abbreviations word = ok r), ∃ j, j < r.val.length ∧
      (entry r.val j).length = word.val.length ∧ entry r.val j = bytes word.val) := by
  sorry

/-- Whenever the function returns a result r, let n = len(word). For every pair of integers a,b with 0 <= a < b <= n, let s be the concatenation of the bytes word[0],...,word[a-1] (empty if a = 0), followed by the standard decimal representation of b-a without leading zeros, followed by the bytes word[b],...,word[n-1] (empty if b = n). Then s occurs in r: there exists j with 0 <= j < len(r) such that r[j] = s.
  Preconditions: word is a byte array with 1 <= len(word) <= 15, and for every i with 0 <= i < len(word), word[i] is an ASCII lowercase English letter (97 <= word[i] <= 122). -/
theorem spec_11 (word : Slice Std.U8) (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (h1 : 1 ≤ word.val.length) (h2 : word.val.length ≤ 15)
    (h3 : ∀ (i : Nat) (hi : i < word.val.length),
      97 ≤ (word.val[i]'hi).val ∧ (word.val[i]'hi).val ≤ 122)
    (hr : Aegis.GenerateAbbreviations.generate_abbreviations word = ok r) :
    ∀ a b : Nat, a < b → b ≤ word.val.length →
      ∃ j, j < r.val.length ∧ entry r.val j = sliceAbbrev (bytes word.val) a b := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (word : Slice Std.U8) (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (h1 : 1 ≤ word.val.length) (h2 : word.val.length ≤ 15)
    (h3 : ∀ (i : Nat) (hi : i < word.val.length),
      97 ≤ (word.val[i]'hi).val ∧ (word.val[i]'hi).val ≤ 122)
    (hr : Aegis.GenerateAbbreviations.generate_abbreviations word = ok r), ∀ a b : Nat, a < b → b ≤ word.val.length →
      ∃ j, j < r.val.length ∧ entry r.val j = sliceAbbrev (bytes word.val) a b) := by
  sorry

/-- Whenever the function returns a result r, let n = len(word). For every j with 0 <= j < len(r), parse s = r[j] into its maximal contiguous runs of ASCII digit bytes and its remaining bytes. Let C be the number of bytes of s that are ASCII lowercase English letters, and let L_1,...,L_k be the integer values represented by the digit runs. Then C + L_1 + ... + L_k = n, with the sum over an empty list of digit runs equal to 0.
  Preconditions: word is a byte array with 1 <= len(word) <= 15, and for every i with 0 <= i < len(word), word[i] is an ASCII lowercase English letter (97 <= word[i] <= 122). -/
theorem spec_12 (word : Slice Std.U8) (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (h1 : 1 ≤ word.val.length) (h2 : word.val.length ≤ 15)
    (h3 : ∀ (i : Nat) (hi : i < word.val.length),
      97 ≤ (word.val[i]'hi).val ∧ (word.val[i]'hi).val ≤ 122)
    (hr : Aegis.GenerateAbbreviations.generate_abbreviations word = ok r) :
    ∀ j, j < r.val.length →
      countLetters (entry r.val j) + sumDigitRuns (entry r.val j) = word.val.length := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (word : Slice Std.U8) (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (h1 : 1 ≤ word.val.length) (h2 : word.val.length ≤ 15)
    (h3 : ∀ (i : Nat) (hi : i < word.val.length),
      97 ≤ (word.val[i]'hi).val ∧ (word.val[i]'hi).val ≤ 122)
    (hr : Aegis.GenerateAbbreviations.generate_abbreviations word = ok r), ∀ j, j < r.val.length →
      countLetters (entry r.val j) + sumDigitRuns (entry r.val j) = word.val.length) := by
  sorry

/-- Whenever the function returns a result r, let n = len(word). For every j with 0 <= j < len(r), let t be the byte vector obtained from r[j] by deleting all ASCII digit bytes. Then t is a subsequence of word: there exist indices 0 <= i_1 < i_2 < ... < i_m < n with m = len(t) such that t[q] = word[i_{q+1}] for every q with 0 <= q < m. If m = 0, t is allowed to be the empty subsequence.
  Preconditions: word is a byte array with 1 <= len(word) <= 15, and for every i with 0 <= i < len(word), word[i] is an ASCII lowercase English letter (97 <= word[i] <= 122). -/
theorem spec_13 (word : Slice Std.U8) (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (h1 : 1 ≤ word.val.length) (h2 : word.val.length ≤ 15)
    (h3 : ∀ (i : Nat) (hi : i < word.val.length),
      97 ≤ (word.val[i]'hi).val ∧ (word.val[i]'hi).val ≤ 122)
    (hr : Aegis.GenerateAbbreviations.generate_abbreviations word = ok r) :
    ∀ j, j < r.val.length →
      List.Sublist (removeDigits (entry r.val j)) (bytes word.val) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (word : Slice Std.U8) (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (h1 : 1 ≤ word.val.length) (h2 : word.val.length ≤ 15)
    (h3 : ∀ (i : Nat) (hi : i < word.val.length),
      97 ≤ (word.val[i]'hi).val ∧ (word.val[i]'hi).val ≤ 122)
    (hr : Aegis.GenerateAbbreviations.generate_abbreviations word = ok r), ∀ j, j < r.val.length →
      List.Sublist (removeDigits (entry r.val j)) (bytes word.val)) := by
  sorry

/-- Whenever the function returns a result r, let n = len(word). For every j with 0 <= j < len(r), the number k of maximal contiguous runs of ASCII digit bytes in r[j] satisfies k <= ceil(n/2), where ceil(x) is the least integer greater than or equal to x.
  Preconditions: word is a byte array with 1 <= len(word) <= 15, and for every i with 0 <= i < len(word), word[i] is an ASCII lowercase English letter (97 <= word[i] <= 122). -/
theorem spec_14 (word : Slice Std.U8) (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (h1 : 1 ≤ word.val.length) (h2 : word.val.length ≤ 15)
    (h3 : ∀ (i : Nat) (hi : i < word.val.length),
      97 ≤ (word.val[i]'hi).val ∧ (word.val[i]'hi).val ≤ 122)
    (hr : Aegis.GenerateAbbreviations.generate_abbreviations word = ok r) :
    ∀ j, j < r.val.length →
      (digitRuns (entry r.val j)).length ≤ (word.val.length + 1) / 2 := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (word : Slice Std.U8) (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (h1 : 1 ≤ word.val.length) (h2 : word.val.length ≤ 15)
    (h3 : ∀ (i : Nat) (hi : i < word.val.length),
      97 ≤ (word.val[i]'hi).val ∧ (word.val[i]'hi).val ≤ 122)
    (hr : Aegis.GenerateAbbreviations.generate_abbreviations word = ok r), ∀ j, j < r.val.length →
      (digitRuns (entry r.val j)).length ≤ (word.val.length + 1) / 2) := by
  sorry

end AegisSpec.GenerateAbbreviations
