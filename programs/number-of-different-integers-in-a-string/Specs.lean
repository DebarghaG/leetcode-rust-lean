import Aegis.NumDifferentIntegers.Code.Funs

/-!
# Specifications of `Aegis.NumDifferentIntegers.num_different_integers`

LeetCode problem `number-of-different-integers-in-a-string`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.NumDifferentIntegers

def IsDigitByte (b : Std.U8) : Prop := 48 ≤ b.val ∧ b.val ≤ 57

def IsLowerByte (b : Std.U8) : Prop := 97 ≤ b.val ∧ b.val ≤ 122

def byteAt (l : List Std.U8) (i : Nat) : Std.U8 := l.getD i default

def isDigitByteB (b : Std.U8) : Bool := decide (48 ≤ b.val) && decide (b.val ≤ 57)

def digitPrefix (l : List Std.U8) : List Std.U8 := l.takeWhile isDigitByteB

def WordInv (l : List Std.U8) : Prop :=
  1 ≤ l.length ∧ l.length ≤ 1000 ∧
    ∀ i, i < l.length → IsDigitByte (byteAt l i) ∨ IsLowerByte (byteAt l i)

def IsMaximalDigitRun (l : List Std.U8) (lo hi : Nat) : Prop :=
  lo ≤ hi ∧ hi < l.length ∧
    (∀ i, lo ≤ i → i ≤ hi → IsDigitByte (byteAt l i)) ∧
    (lo = 0 ∨ ¬ IsDigitByte (byteAt l (lo - 1))) ∧
    (hi + 1 = l.length ∨ ¬ IsDigitByte (byteAt l (hi + 1)))

def segment (l : List Std.U8) (lo hi : Nat) : List Std.U8 := (l.drop lo).take (hi + 1 - lo)

def stripLeadingZeros : List Std.U8 → List Std.U8
  | [] => []
  | b :: t => if b.val = 48 then stripLeadingZeros t else b :: t

def canonical (s : List Std.U8) : List Std.U8 :=
  match stripLeadingZeros s with
  | [] => [48#u8]
  | t => t

def canonicalOfSeg (l : List Std.U8) (lo hi : Nat) : List Std.U8 := canonical (segment l lo hi)

def IsRunStart (l : List Std.U8) (i : Nat) : Prop :=
  i < l.length ∧ IsDigitByte (byteAt l i) ∧ (i = 0 ∨ ¬ IsDigitByte (byteAt l (i - 1)))

def isRunStartB (l : List Std.U8) (i : Nat) : Bool :=
  decide (i < l.length) && isDigitByteB (byteAt l i) &&
    (decide (i = 0) || !isDigitByteB (byteAt l (i - 1)))

def RunStarts (l : List Std.U8) : List Nat :=
  (List.range l.length).filter (isRunStartB l)

def NumRuns (l : List Std.U8) : Nat := (RunStarts l).length

def runEndFrom (l : List Std.U8) (st : Nat) : Nat := st + (digitPrefix (l.drop st)).length - 1

def canonicalOfRunFrom (l : List Std.U8) (st : Nat) : List Std.U8 :=
  canonical (digitPrefix (l.drop st))

def RunValues (l : List Std.U8) : Finset (List Std.U8) :=
  ((RunStarts l).map (fun st => canonicalOfRunFrom l st)).toFinset

def NumDistinctRunValues (l : List Std.U8) : Nat := (RunValues l).card

def RunSegmentSet (l : List Std.U8) : Finset (List Std.U8) :=
  ((RunStarts l).map (fun st => segment l st (runEndFrom l st))).toFinset

def ContainsDigitByte (l : List Std.U8) : Prop := ∃ i, i < l.length ∧ IsDigitByte (byteAt l i)

def DigitValues (l : List Std.U8) : Finset Nat :=
  (l.map (fun b => b.val)).toFinset.filter (fun d => 48 ≤ d ∧ d ≤ 57)

def insertAt (l : List Std.U8) (p : Nat) (c : Std.U8) : List Std.U8 :=
  l.take p ++ [c] ++ l.drop p

def replaceSeg (l : List Std.U8) (lo hi : Nat) (s : List Std.U8) : List Std.U8 :=
  l.take lo ++ s ++ l.drop (hi + 1)

/-- The call num_different_integers(word) returns Result.ok r (it does not fail), and r equals the number of distinct integer values represented by the maximal digit runs of word. A digit byte is a byte b with 48 <= b <= 57. A maximal digit run is a nonempty contiguous segment word[l..u] (0 <= l <= u < len(word)) consisting entirely of digit bytes such that either l=0 or word[l-1] is not a digit byte, and either u=len(word)-1 or word[u+1] is not a digit byte. The integer value of a run is obtained by deleting all leading bytes equal to 48 ('0'); if nothing remains, the value is represented by the single byte 48 ('0'); otherwise by the remaining digit bytes. Two runs represent the same integer exactly when these canonical representations are equal. If word has no digit bytes there are no runs and r=0.
  Preconditions: 1 <= len(word) <= 1000 and for every i with 0 <= i < len(word), word[i] is either a digit byte (48 <= word[i] <= 57) or a lowercase English letter (97 <= word[i] <= 122). -/
theorem spec_1 (word : Slice Std.U8)
    (h_len : 1 ≤ word.val.length) (h_len' : word.val.length ≤ 1000)
    (h_bytes : ∀ i, i < word.val.length →
      IsDigitByte (byteAt word.val i) ∨ IsLowerByte (byteAt word.val i)) :
    ∃ r : Std.I64,
      Aegis.NumDifferentIntegers.num_different_integers word = ok r ∧
        r.val = (NumDistinctRunValues word.val : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (word : Slice Std.U8)
    (h_len : 1 ≤ word.val.length) (h_len' : word.val.length ≤ 1000)
    (h_bytes : ∀ i, i < word.val.length →
      IsDigitByte (byteAt word.val i) ∨ IsLowerByte (byteAt word.val i)), ∃ r : Std.I64,
      Aegis.NumDifferentIntegers.num_different_integers word = ok r ∧
        r.val = (NumDistinctRunValues word.val : Int)) := by
  sorry

/-- For every word satisfying the preconditions, the call num_different_integers(word) returns Result.ok r for some Std.I64 r; it does not fail by overflow, out-of-bounds access, or panic.
  Preconditions: 1 <= len(word) <= 1000 and for every i with 0 <= i < len(word), word[i] is either a digit byte (48 <= word[i] <= 57) or a lowercase English letter (97 <= word[i] <= 122). -/
theorem spec_2 (word : Slice Std.U8)
    (h_len : 1 ≤ word.val.length) (h_len' : word.val.length ≤ 1000)
    (h_bytes : ∀ i, i < word.val.length →
      IsDigitByte (byteAt word.val i) ∨ IsLowerByte (byteAt word.val i)) :
    ∃ r : Std.I64, Aegis.NumDifferentIntegers.num_different_integers word = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (word : Slice Std.U8)
    (h_len : 1 ≤ word.val.length) (h_len' : word.val.length ≤ 1000)
    (h_bytes : ∀ i, i < word.val.length →
      IsDigitByte (byteAt word.val i) ∨ IsLowerByte (byteAt word.val i)), ∃ r : Std.I64, Aegis.NumDifferentIntegers.num_different_integers word = ok r) := by
  sorry

/-- Let m be the number of maximal digit runs of word (the nonempty maximal contiguous segments consisting of digit bytes, where a digit byte is in 48..57). Whenever num_different_integers(word) returns Result.ok r, r <= m.
  Preconditions: 1 <= len(word) <= 1000 and for every i with 0 <= i < len(word), word[i] is either a digit byte (48 <= word[i] <= 57) or a lowercase English letter (97 <= word[i] <= 122). -/
theorem spec_3 (word : Slice Std.U8)
    (h_len : 1 ≤ word.val.length) (h_len' : word.val.length ≤ 1000)
    (h_bytes : ∀ i, i < word.val.length →
      IsDigitByte (byteAt word.val i) ∨ IsLowerByte (byteAt word.val i)) :
    ∀ r : Std.I64,
      Aegis.NumDifferentIntegers.num_different_integers word = ok r →
        r.val ≤ (NumRuns word.val : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (word : Slice Std.U8)
    (h_len : 1 ≤ word.val.length) (h_len' : word.val.length ≤ 1000)
    (h_bytes : ∀ i, i < word.val.length →
      IsDigitByte (byteAt word.val i) ∨ IsLowerByte (byteAt word.val i)), ∀ r : Std.I64,
      Aegis.NumDifferentIntegers.num_different_integers word = ok r →
        r.val ≤ (NumRuns word.val : Int)) := by
  sorry

/-- Whenever num_different_integers(word) returns Result.ok r, r = 0 if and only if word contains no digit byte (no i with 0 <= i < len(word) and 48 <= word[i] <= 57).
  Preconditions: 1 <= len(word) <= 1000 and for every i with 0 <= i < len(word), word[i] is either a digit byte (48 <= word[i] <= 57) or a lowercase English letter (97 <= word[i] <= 122). -/
theorem spec_4 (word : Slice Std.U8)
    (h_len : 1 ≤ word.val.length) (h_len' : word.val.length ≤ 1000)
    (h_bytes : ∀ i, i < word.val.length →
      IsDigitByte (byteAt word.val i) ∨ IsLowerByte (byteAt word.val i)) :
    ∀ r : Std.I64,
      Aegis.NumDifferentIntegers.num_different_integers word = ok r →
        (r.val = 0 ↔ ¬ ContainsDigitByte word.val) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (word : Slice Std.U8)
    (h_len : 1 ≤ word.val.length) (h_len' : word.val.length ≤ 1000)
    (h_bytes : ∀ i, i < word.val.length →
      IsDigitByte (byteAt word.val i) ∨ IsLowerByte (byteAt word.val i)), ∀ r : Std.I64,
      Aegis.NumDifferentIntegers.num_different_integers word = ok r →
        (r.val = 0 ↔ ¬ ContainsDigitByte word.val)) := by
  sorry

/-- Whenever num_different_integers(word) returns Result.ok r, if word contains at least one digit byte and every maximal digit run of word has the same canonical decimal representation (after deleting leading 48 bytes, with an all-zero run represented by the single byte 48), then r = 1.
  Preconditions: 1 <= len(word) <= 1000 and for every i with 0 <= i < len(word), word[i] is either a digit byte (48 <= word[i] <= 57) or a lowercase English letter (97 <= word[i] <= 122). -/
theorem spec_5 (word : Slice Std.U8)
    (h_len : 1 ≤ word.val.length) (h_len' : word.val.length ≤ 1000)
    (h_bytes : ∀ i, i < word.val.length →
      IsDigitByte (byteAt word.val i) ∨ IsLowerByte (byteAt word.val i)) :
    ∀ r : Std.I64,
      Aegis.NumDifferentIntegers.num_different_integers word = ok r →
        ContainsDigitByte word.val →
          (∀ lo hi lo' hi', IsMaximalDigitRun word.val lo hi →
              IsMaximalDigitRun word.val lo' hi' →
                canonicalOfSeg word.val lo hi = canonicalOfSeg word.val lo' hi') →
            r.val = 1 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (word : Slice Std.U8)
    (h_len : 1 ≤ word.val.length) (h_len' : word.val.length ≤ 1000)
    (h_bytes : ∀ i, i < word.val.length →
      IsDigitByte (byteAt word.val i) ∨ IsLowerByte (byteAt word.val i)), ∀ r : Std.I64,
      Aegis.NumDifferentIntegers.num_different_integers word = ok r →
        ContainsDigitByte word.val →
          (∀ lo hi lo' hi', IsMaximalDigitRun word.val lo hi →
              IsMaximalDigitRun word.val lo' hi' →
                canonicalOfSeg word.val lo hi = canonicalOfSeg word.val lo' hi') →
            r.val = 1) := by
  sorry

/-- Whenever num_different_integers(word) returns Result.ok r and r = 1, all maximal digit runs of word have the same canonical decimal representation (after deleting leading 48 bytes, with an all-zero run represented by the single byte 48).
  Preconditions: 1 <= len(word) <= 1000 and for every i with 0 <= i < len(word), word[i] is either a digit byte (48 <= word[i] <= 57) or a lowercase English letter (97 <= word[i] <= 122). -/
theorem spec_6 (word : Slice Std.U8)
    (h_len : 1 ≤ word.val.length) (h_len' : word.val.length ≤ 1000)
    (h_bytes : ∀ i, i < word.val.length →
      IsDigitByte (byteAt word.val i) ∨ IsLowerByte (byteAt word.val i)) :
    ∀ r : Std.I64,
      Aegis.NumDifferentIntegers.num_different_integers word = ok r → r.val = 1 →
        ∀ lo hi lo' hi', IsMaximalDigitRun word.val lo hi →
          IsMaximalDigitRun word.val lo' hi' →
            canonicalOfSeg word.val lo hi = canonicalOfSeg word.val lo' hi' := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (word : Slice Std.U8)
    (h_len : 1 ≤ word.val.length) (h_len' : word.val.length ≤ 1000)
    (h_bytes : ∀ i, i < word.val.length →
      IsDigitByte (byteAt word.val i) ∨ IsLowerByte (byteAt word.val i)), ∀ r : Std.I64,
      Aegis.NumDifferentIntegers.num_different_integers word = ok r → r.val = 1 →
        ∀ lo hi lo' hi', IsMaximalDigitRun word.val lo hi →
          IsMaximalDigitRun word.val lo' hi' →
            canonicalOfSeg word.val lo hi = canonicalOfSeg word.val lo' hi') := by
  sorry

/-- Whenever num_different_integers(word) returns Result.ok r, r equals the number of distinct byte sequences that occur as maximal digit runs of word; two runs are considered the same here exactly when they have the same length and the same bytes in the same order.
  Preconditions: 1 <= len(word) <= 1000, every byte of word is either a digit byte (48..57) or a lowercase English letter (97..122), and for every i with 0 <= i < len(word), word[i] != 48. -/
theorem spec_7 (word : Slice Std.U8)
    (h_len : 1 ≤ word.val.length) (h_len' : word.val.length ≤ 1000)
    (h_bytes : ∀ i, i < word.val.length →
      IsDigitByte (byteAt word.val i) ∨ IsLowerByte (byteAt word.val i))
    (h_no_zero : ∀ i, i < word.val.length → (byteAt word.val i).val ≠ 48) :
    ∀ r : Std.I64,
      Aegis.NumDifferentIntegers.num_different_integers word = ok r →
        r.val = (RunSegmentSet word.val).card := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (word : Slice Std.U8)
    (h_len : 1 ≤ word.val.length) (h_len' : word.val.length ≤ 1000)
    (h_bytes : ∀ i, i < word.val.length →
      IsDigitByte (byteAt word.val i) ∨ IsLowerByte (byteAt word.val i))
    (h_no_zero : ∀ i, i < word.val.length → (byteAt word.val i).val ≠ 48), ∀ r : Std.I64,
      Aegis.NumDifferentIntegers.num_different_integers word = ok r →
        r.val = (RunSegmentSet word.val).card) := by
  sorry

/-- Whenever num_different_integers(word) returns Result.ok r, r equals the number of distinct byte values d with 48 <= d <= 57 such that d occurs in word.
  Preconditions: 1 <= len(word) <= 1000, every byte of word is either a digit byte (48..57) or a lowercase English letter (97..122), and for every i with 0 <= i + 1 < len(word), it is not the case that both word[i] and word[i+1] are digit bytes (48..57). -/
theorem spec_8 (word : Slice Std.U8)
    (h_len : 1 ≤ word.val.length) (h_len' : word.val.length ≤ 1000)
    (h_bytes : ∀ i, i < word.val.length →
      IsDigitByte (byteAt word.val i) ∨ IsLowerByte (byteAt word.val i))
    (h_no_adjacent : ∀ i, i + 1 < word.val.length →
      ¬ (IsDigitByte (byteAt word.val i) ∧ IsDigitByte (byteAt word.val (i + 1)))) :
    ∀ r : Std.I64,
      Aegis.NumDifferentIntegers.num_different_integers word = ok r →
        r.val = ((DigitValues word.val).card : Int) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (word : Slice Std.U8)
    (h_len : 1 ≤ word.val.length) (h_len' : word.val.length ≤ 1000)
    (h_bytes : ∀ i, i < word.val.length →
      IsDigitByte (byteAt word.val i) ∨ IsLowerByte (byteAt word.val i))
    (h_no_adjacent : ∀ i, i + 1 < word.val.length →
      ¬ (IsDigitByte (byteAt word.val i) ∧ IsDigitByte (byteAt word.val (i + 1)))), ∀ r : Std.I64,
      Aegis.NumDifferentIntegers.num_different_integers word = ok r →
        r.val = ((DigitValues word.val).card : Int)) := by
  sorry

/-- Whenever num_different_integers(word) returns Result.ok r and num_different_integers(other) returns Result.ok r', r = r'.
  Preconditions: word and other are two byte arrays, each satisfying: 1 <= len <= 1000 and every byte is either a digit byte (48..57) or a lowercase English letter (97..122). Also len(word) = len(other), and for every i with 0 <= i < len(word): if word[i] is a digit byte (48..57) then other[i] = word[i], and if word[i] is not a digit byte then other[i] is not a digit byte. -/
theorem spec_9 (word other : Slice Std.U8)
    (h_len : 1 ≤ word.val.length) (h_len' : word.val.length ≤ 1000)
    (h_bytes : ∀ i, i < word.val.length →
      IsDigitByte (byteAt word.val i) ∨ IsLowerByte (byteAt word.val i))
    (h_len_o : 1 ≤ other.val.length) (h_len_o' : other.val.length ≤ 1000)
    (h_bytes_o : ∀ i, i < other.val.length →
      IsDigitByte (byteAt other.val i) ∨ IsLowerByte (byteAt other.val i))
    (h_same_len : word.val.length = other.val.length)
    (h_pres : ∀ i, i < word.val.length →
      (IsDigitByte (byteAt word.val i) → byteAt other.val i = byteAt word.val i) ∧
        (¬ IsDigitByte (byteAt word.val i) → ¬ IsDigitByte (byteAt other.val i))) :
    ∀ r r' : Std.I64,
      Aegis.NumDifferentIntegers.num_different_integers word = ok r →
        Aegis.NumDifferentIntegers.num_different_integers other = ok r' → r.val = r'.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (word other : Slice Std.U8)
    (h_len : 1 ≤ word.val.length) (h_len' : word.val.length ≤ 1000)
    (h_bytes : ∀ i, i < word.val.length →
      IsDigitByte (byteAt word.val i) ∨ IsLowerByte (byteAt word.val i))
    (h_len_o : 1 ≤ other.val.length) (h_len_o' : other.val.length ≤ 1000)
    (h_bytes_o : ∀ i, i < other.val.length →
      IsDigitByte (byteAt other.val i) ∨ IsLowerByte (byteAt other.val i))
    (h_same_len : word.val.length = other.val.length)
    (h_pres : ∀ i, i < word.val.length →
      (IsDigitByte (byteAt word.val i) → byteAt other.val i = byteAt word.val i) ∧
        (¬ IsDigitByte (byteAt word.val i) → ¬ IsDigitByte (byteAt other.val i))), ∀ r r' : Std.I64,
      Aegis.NumDifferentIntegers.num_different_integers word = ok r →
        Aegis.NumDifferentIntegers.num_different_integers other = ok r' → r.val = r'.val) := by
  sorry

/-- Whenever num_different_integers(word) returns Result.ok r and num_different_integers(inserted) returns Result.ok r', r = r'.
  Preconditions: word satisfies: 1 <= len(word) <= 1000 and every byte is either a digit byte (48..57) or a lowercase English letter (97..122). Also len(word) < 1000, c is a byte with 97 <= c <= 122, and p is an integer with 0 <= p <= len(word). It is not the case that 0 < p < len(word) and word[p-1] is a digit byte (48..57) and word[p] is a digit byte. Let inserted be the byte array of length len(word)+1 with inserted[i]=word[i] for 0 <= i < p, inserted[p]=c, and inserted[i]=word[i-1] for p < i <= len(word). -/
theorem spec_10 (word inserted : Slice Std.U8) (c : Std.U8) (p : Nat)
    (h_len : 1 ≤ word.val.length) (h_len' : word.val.length ≤ 1000)
    (h_bytes : ∀ i, i < word.val.length →
      IsDigitByte (byteAt word.val i) ∨ IsLowerByte (byteAt word.val i))
    (h_lt : word.val.length < 1000)
    (h_c : 97 ≤ c.val ∧ c.val ≤ 122)
    (h_p : p ≤ word.val.length)
    (h_not_split : ¬ (0 < p ∧ p < word.val.length ∧
      IsDigitByte (byteAt word.val (p - 1)) ∧ IsDigitByte (byteAt word.val p)))
    (h_inserted : inserted.val = insertAt word.val p c) :
    ∀ r r' : Std.I64,
      Aegis.NumDifferentIntegers.num_different_integers word = ok r →
        Aegis.NumDifferentIntegers.num_different_integers inserted = ok r' → r.val = r'.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (word inserted : Slice Std.U8) (c : Std.U8) (p : Nat)
    (h_len : 1 ≤ word.val.length) (h_len' : word.val.length ≤ 1000)
    (h_bytes : ∀ i, i < word.val.length →
      IsDigitByte (byteAt word.val i) ∨ IsLowerByte (byteAt word.val i))
    (h_lt : word.val.length < 1000)
    (h_c : 97 ≤ c.val ∧ c.val ≤ 122)
    (h_p : p ≤ word.val.length)
    (h_not_split : ¬ (0 < p ∧ p < word.val.length ∧
      IsDigitByte (byteAt word.val (p - 1)) ∧ IsDigitByte (byteAt word.val p)))
    (h_inserted : inserted.val = insertAt word.val p c), ∀ r r' : Std.I64,
      Aegis.NumDifferentIntegers.num_different_integers word = ok r →
        Aegis.NumDifferentIntegers.num_different_integers inserted = ok r' → r.val = r'.val) := by
  sorry

/-- Whenever num_different_integers(word) returns Result.ok r and num_different_integers(modified) returns Result.ok r', r = r'.
  Preconditions: word satisfies: 1 <= len(word) <= 1000 and every byte is either a digit byte (48..57) or a lowercase English letter (97..122). Let l,u be indices of a maximal digit run of word, so all word[l..u] are digit bytes (48..57), and the run is maximal (l=0 or word[l-1] is not a digit byte; u=len(word)-1 or word[u+1] is not a digit byte). Let s be a nonempty byte sequence of digit bytes. Assume s and word[l..u] have the same canonical decimal representation: delete all leading 48 bytes from each, and if the result is empty replace it by the single byte 48; the two resulting sequences are equal. Let modified be the byte array obtained by replacing the segment word[l..u] with s and leaving all other bytes in order. Assume len(modified) <= 1000. -/
theorem spec_11 (word modified : Slice Std.U8) (l u : Nat) (s : List Std.U8)
    (h_len : 1 ≤ word.val.length) (h_len' : word.val.length ≤ 1000)
    (h_bytes : ∀ i, i < word.val.length →
      IsDigitByte (byteAt word.val i) ∨ IsLowerByte (byteAt word.val i))
    (h_run : IsMaximalDigitRun word.val l u)
    (h_s_ne : s ≠ [])
    (h_s_digits : ∀ b ∈ s, IsDigitByte b)
    (h_canon : canonical s = canonicalOfSeg word.val l u)
    (h_mod_len : modified.val.length ≤ 1000)
    (h_modified : modified.val = replaceSeg word.val l u s) :
    ∀ r r' : Std.I64,
      Aegis.NumDifferentIntegers.num_different_integers word = ok r →
        Aegis.NumDifferentIntegers.num_different_integers modified = ok r' → r.val = r'.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (word modified : Slice Std.U8) (l u : Nat) (s : List Std.U8)
    (h_len : 1 ≤ word.val.length) (h_len' : word.val.length ≤ 1000)
    (h_bytes : ∀ i, i < word.val.length →
      IsDigitByte (byteAt word.val i) ∨ IsLowerByte (byteAt word.val i))
    (h_run : IsMaximalDigitRun word.val l u)
    (h_s_ne : s ≠ [])
    (h_s_digits : ∀ b ∈ s, IsDigitByte b)
    (h_canon : canonical s = canonicalOfSeg word.val l u)
    (h_mod_len : modified.val.length ≤ 1000)
    (h_modified : modified.val = replaceSeg word.val l u s), ∀ r r' : Std.I64,
      Aegis.NumDifferentIntegers.num_different_integers word = ok r →
        Aegis.NumDifferentIntegers.num_different_integers modified = ok r' → r.val = r'.val) := by
  sorry

/-- Whenever num_different_integers(word) returns Result.ok r, if r is a nonnegative integer k (so r = k), then there exist k maximal digit runs R_1,...,R_k of word such that for every i and j with 1 <= i < j <= k, the canonical decimal representations of R_i and R_j are different. For k=0 the list is empty. A canonical representation is obtained by deleting leading 48 bytes, with an all-zero run represented by the single byte 48.
  Preconditions: 1 <= len(word) <= 1000 and for every i with 0 <= i < len(word), word[i] is either a digit byte (48 <= word[i] <= 57) or a lowercase English letter (97 <= word[i] <= 122). -/
theorem spec_12 (word : Slice Std.U8)
    (h_len : 1 ≤ word.val.length) (h_len' : word.val.length ≤ 1000)
    (h_bytes : ∀ i, i < word.val.length →
      IsDigitByte (byteAt word.val i) ∨ IsLowerByte (byteAt word.val i)) :
    ∀ r : Std.I64,
      Aegis.NumDifferentIntegers.num_different_integers word = ok r →
        ∃ k : Nat, r.val = (k : Int) ∧
          ∃ runs : List (Nat × Nat),
            runs.length = k ∧
              (∀ q ∈ runs, IsMaximalDigitRun word.val q.1 q.2) ∧
                (runs.map (fun q => canonicalOfSeg word.val q.1 q.2)).Nodup := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (word : Slice Std.U8)
    (h_len : 1 ≤ word.val.length) (h_len' : word.val.length ≤ 1000)
    (h_bytes : ∀ i, i < word.val.length →
      IsDigitByte (byteAt word.val i) ∨ IsLowerByte (byteAt word.val i)), ∀ r : Std.I64,
      Aegis.NumDifferentIntegers.num_different_integers word = ok r →
        ∃ k : Nat, r.val = (k : Int) ∧
          ∃ runs : List (Nat × Nat),
            runs.length = k ∧
              (∀ q ∈ runs, IsMaximalDigitRun word.val q.1 q.2) ∧
                (runs.map (fun q => canonicalOfSeg word.val q.1 q.2)).Nodup) := by
  sorry

end AegisSpec.NumDifferentIntegers
