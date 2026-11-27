import Aegis.FindRelativeRanks.Code.Funs

/-!
# Specifications of `Aegis.FindRelativeRanks.find_relative_ranks`

LeetCode problem `relative-ranks`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.FindRelativeRanks

namespace AegisSpec.FindRelativeRanks

def countGreater (xs : List Std.I64) (x : Int) : Nat :=
  (xs.filter (fun y => decide (x < y.val))).length

def scoreAt (score : Slice Std.I64) (i : Nat) : Int :=
  (score.val.getD i 0#i64).val

def higherCount (score : Slice Std.I64) (i : Nat) : Nat :=
  countGreater score.val (scoreAt score i)

def Pre (score : Slice Std.I64) : Prop :=
  1 ≤ score.val.length ∧
  score.val.length ≤ 10000 ∧
  (∀ i, i < score.val.length → 0 ≤ scoreAt score i ∧ scoreAt score i ≤ 1000000) ∧
  (∀ i j, i < j → j < score.val.length → scoreAt score i ≠ scoreAt score j)

def goldMedal : List Std.U8 :=
  [71#u8, 111#u8, 108#u8, 100#u8, 32#u8, 77#u8, 101#u8, 100#u8, 97#u8, 108#u8]

def silverMedal : List Std.U8 :=
  [83#u8, 105#u8, 108#u8, 118#u8, 101#u8, 114#u8, 32#u8, 77#u8, 101#u8, 100#u8, 97#u8, 108#u8]

def bronzeMedal : List Std.U8 :=
  [66#u8, 114#u8, 111#u8, 110#u8, 122#u8, 101#u8, 32#u8, 77#u8, 101#u8, 100#u8, 97#u8, 108#u8]

def IsDigit (b : Std.U8) : Prop :=
  48 ≤ b.val ∧ b.val ≤ 57

def allDigits (l : List Std.U8) : Prop :=
  ∀ b ∈ l, IsDigit b

def digitsValue : List Std.U8 → Nat
  | [] => 0
  | b :: rest => (b.val - 48) * 10 ^ rest.length + digitsValue rest

def noLeadingZero (l : List Std.U8) : Prop :=
  ∀ b rest, l = b :: rest → 49 ≤ b.val

def IsDecimalRep (l : List Std.U8) (n : Nat) : Prop :=
  l ≠ [] ∧ allDigits l ∧ noLeadingZero l ∧ digitsValue l = n

def expectedEntry (k : Nat) (b : List Std.U8) : Prop :=
  (k = 0 → b = goldMedal) ∧
  (k = 1 → b = silverMedal) ∧
  (k = 2 → b = bronzeMedal) ∧
  (3 ≤ k → IsDecimalRep b (k + 1))

def entryAt (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)) (i : Nat) : Option (List Std.U8) :=
  Option.map (fun v => v.val) r.val[i]?

def countEntry (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)) (b : List Std.U8) : Nat :=
  (r.val.filter (fun v => decide (v.val = b))).length

/-- For each index i, let k(i) be the number of indices j with 0 <= j < len(score) and score[j] > score[i]. The function returns a result r and: len(r) = len(score); and for every i with 0 <= i < len(score), r[i] is the ASCII byte sequence for 'Gold Medal' if k(i)=0, for 'Silver Medal' if k(i)=1, for 'Bronze Medal' if k(i)=2, and if k(i)>=3 then r[i] is the standard base-10 ASCII representation of k(i)+1 with no leading zero, meaning the unique byte vector b of length m>=1 such that b[0] is one of the ASCII codes 49,...,57, every b[t] for 0 <= t < m is one of the ASCII codes 48,...,57, and k(i)+1 = sum_{t=0}^{m-1} (b[t]-48) * 10^(m-1-t).
  Preconditions: 1 <= len(score) <= 10000; for every i with 0 <= i < len(score), 0 <= score[i] <= 1000000; and for every i,j with 0 <= i < j < len(score), score[i] != score[j]. -/
theorem spec_1 (score : Slice Std.I64) (h : Pre score) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      find_relative_ranks score = ok r ∧
      r.val.length = score.val.length ∧
      (∀ i, i < score.val.length →
        ∃ b : List Std.U8, entryAt r i = some b ∧ expectedEntry (higherCount score i) b) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (score : Slice Std.I64) (h : Pre score), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      find_relative_ranks score = ok r ∧
      r.val.length = score.val.length ∧
      (∀ i, i < score.val.length →
        ∃ b : List Std.U8, entryAt r i = some b ∧ expectedEntry (higherCount score i) b)) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r; it does not fail, panic, overflow, or go out of bounds.
  Preconditions: 1 <= len(score) <= 10000; for every i with 0 <= i < len(score), 0 <= score[i] <= 1000000; and for every i,j with 0 <= i < j < len(score), score[i] != score[j]. -/
theorem spec_2 (score : Slice Std.I64) (h : Pre score) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.U8), find_relative_ranks score = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (score : Slice Std.I64) (h : Pre score), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.U8), find_relative_ranks score = ok r) := by
  sorry

/-- Whenever the function returns a result r, len(r) = len(score).
  Preconditions: 1 <= len(score) <= 10000; for every i with 0 <= i < len(score), 0 <= score[i] <= 1000000; and for every i,j with 0 <= i < j < len(score), score[i] != score[j]. -/
theorem spec_3 (score : Slice Std.I64) (h : Pre score) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      find_relative_ranks score = ok r → r.val.length = score.val.length := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (score : Slice Std.I64) (h : Pre score), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      find_relative_ranks score = ok r → r.val.length = score.val.length) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(score), 1 <= len(r[i]) <= 12.
  Preconditions: 1 <= len(score) <= 10000; for every i with 0 <= i < len(score), 0 <= score[i] <= 1000000; and for every i,j with 0 <= i < j < len(score), score[i] != score[j]. -/
theorem spec_4 (score : Slice Std.I64) (h : Pre score) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      find_relative_ranks score = ok r →
      ∀ i, i < score.val.length →
        ∀ b : List Std.U8, entryAt r i = some b → 1 ≤ b.length ∧ b.length ≤ 12 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (score : Slice Std.I64) (h : Pre score), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      find_relative_ranks score = ok r →
      ∀ i, i < score.val.length →
        ∀ b : List Std.U8, entryAt r i = some b → 1 ≤ b.length ∧ b.length ≤ 12) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(score), r[i] is the ASCII byte sequence for 'Gold Medal' if and only if for every j with 0 <= j < len(score) and j != i, score[i] > score[j].
  Preconditions: 1 <= len(score) <= 10000; for every i with 0 <= i < len(score), 0 <= score[i] <= 1000000; and for every i,j with 0 <= i < j < len(score), score[i] != score[j]. -/
theorem spec_5 (score : Slice Std.I64) (h : Pre score) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      find_relative_ranks score = ok r →
      ∀ i, i < score.val.length →
        (entryAt r i = some goldMedal ↔
          ∀ j, j < score.val.length → j ≠ i → scoreAt score j < scoreAt score i) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (score : Slice Std.I64) (h : Pre score), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      find_relative_ranks score = ok r →
      ∀ i, i < score.val.length →
        (entryAt r i = some goldMedal ↔
          ∀ j, j < score.val.length → j ≠ i → scoreAt score j < scoreAt score i)) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(score), r[i] is the ASCII byte sequence for 'Silver Medal' if and only if the number of indices j with 0 <= j < len(score) and score[j] > score[i] is exactly 1.
  Preconditions: 1 <= len(score) <= 10000; for every i with 0 <= i < len(score), 0 <= score[i] <= 1000000; and for every i,j with 0 <= i < j < len(score), score[i] != score[j]. -/
theorem spec_6 (score : Slice Std.I64) (h : Pre score) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      find_relative_ranks score = ok r →
      ∀ i, i < score.val.length →
        (entryAt r i = some silverMedal ↔ higherCount score i = 1) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (score : Slice Std.I64) (h : Pre score), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      find_relative_ranks score = ok r →
      ∀ i, i < score.val.length →
        (entryAt r i = some silverMedal ↔ higherCount score i = 1)) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(score), r[i] is the ASCII byte sequence for 'Bronze Medal' if and only if the number of indices j with 0 <= j < len(score) and score[j] > score[i] is exactly 2.
  Preconditions: 1 <= len(score) <= 10000; for every i with 0 <= i < len(score), 0 <= score[i] <= 1000000; and for every i,j with 0 <= i < j < len(score), score[i] != score[j]. -/
theorem spec_7 (score : Slice Std.I64) (h : Pre score) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      find_relative_ranks score = ok r →
      ∀ i, i < score.val.length →
        (entryAt r i = some bronzeMedal ↔ higherCount score i = 2) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (score : Slice Std.I64) (h : Pre score), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      find_relative_ranks score = ok r →
      ∀ i, i < score.val.length →
        (entryAt r i = some bronzeMedal ↔ higherCount score i = 2)) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(score), if the number of indices j with 0 <= j < len(score) and score[j] > score[i] is at least 3, then r[i] is the standard base-10 ASCII representation, with no leading zero, of that number plus 1.
  Preconditions: 1 <= len(score) <= 10000; for every i with 0 <= i < len(score), 0 <= score[i] <= 1000000; and for every i,j with 0 <= i < j < len(score), score[i] != score[j]. -/
theorem spec_8 (score : Slice Std.I64) (h : Pre score) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      find_relative_ranks score = ok r →
      ∀ i, i < score.val.length →
        3 ≤ higherCount score i →
          ∀ b : List Std.U8, entryAt r i = some b → IsDecimalRep b (higherCount score i + 1) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (score : Slice Std.I64) (h : Pre score), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      find_relative_ranks score = ok r →
      ∀ i, i < score.val.length →
        3 ≤ higherCount score i →
          ∀ b : List Std.U8, entryAt r i = some b → IsDecimalRep b (higherCount score i + 1)) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(score), if the number of indices j with 0 <= j < len(score) and score[j] > score[i] is at least 3, then every byte of r[i] is an ASCII digit (48 through 57), r[i][0] is not ASCII 48, and len(r[i]) <= 5.
  Preconditions: 1 <= len(score) <= 10000; for every i with 0 <= i < len(score), 0 <= score[i] <= 1000000; and for every i,j with 0 <= i < j < len(score), score[i] != score[j]. -/
theorem spec_9 (score : Slice Std.I64) (h : Pre score) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      find_relative_ranks score = ok r →
      ∀ i, i < score.val.length →
        3 ≤ higherCount score i →
          ∀ b : List Std.U8, entryAt r i = some b →
            allDigits b ∧ b ≠ [] ∧ noLeadingZero b ∧ b.length ≤ 5 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (score : Slice Std.I64) (h : Pre score), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      find_relative_ranks score = ok r →
      ∀ i, i < score.val.length →
        3 ≤ higherCount score i →
          ∀ b : List Std.U8, entryAt r i = some b →
            allDigits b ∧ b ≠ [] ∧ noLeadingZero b ∧ b.length ≤ 5) := by
  sorry

/-- Whenever the function returns a result r, for every i,j with 0 <= i < j < len(score), r[i] != r[j].
  Preconditions: 1 <= len(score) <= 10000; for every i with 0 <= i < len(score), 0 <= score[i] <= 1000000; and for every i,j with 0 <= i < j < len(score), score[i] != score[j]. -/
theorem spec_10 (score : Slice Std.I64) (h : Pre score) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      find_relative_ranks score = ok r →
      ∀ i j, i < j → j < score.val.length →
        ∀ a b : List Std.U8, entryAt r i = some a → entryAt r j = some b → a ≠ b := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (score : Slice Std.I64) (h : Pre score), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      find_relative_ranks score = ok r →
      ∀ i j, i < j → j < score.val.length →
        ∀ a b : List Std.U8, entryAt r i = some a → entryAt r j = some b → a ≠ b) := by
  sorry

/-- Whenever the function returns a result r, exactly one entry of r is the ASCII byte sequence for 'Gold Medal'; if len(score) >= 2, exactly one entry of r is the ASCII byte sequence for 'Silver Medal'; and if len(score) >= 3, exactly one entry of r is the ASCII byte sequence for 'Bronze Medal'.
  Preconditions: 1 <= len(score) <= 10000; for every i with 0 <= i < len(score), 0 <= score[i] <= 1000000; and for every i,j with 0 <= i < j < len(score), score[i] != score[j]. -/
theorem spec_11 (score : Slice Std.I64) (h : Pre score) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      find_relative_ranks score = ok r →
      countEntry r goldMedal = 1 ∧
      (2 ≤ score.val.length → countEntry r silverMedal = 1) ∧
      (3 ≤ score.val.length → countEntry r bronzeMedal = 1) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (score : Slice Std.I64) (h : Pre score), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      find_relative_ranks score = ok r →
      countEntry r goldMedal = 1 ∧
      (2 ≤ score.val.length → countEntry r silverMedal = 1) ∧
      (3 ≤ score.val.length → countEntry r bronzeMedal = 1)) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(score), r[i] is one of the ASCII byte sequences for 'Gold Medal', 'Silver Medal', 'Bronze Medal', or r[i] is a nonempty byte vector whose bytes are all ASCII digits (48 through 57) and whose first byte is not ASCII 48.
  Preconditions: 1 <= len(score) <= 10000; for every i with 0 <= i < len(score), 0 <= score[i] <= 1000000; and for every i,j with 0 <= i < j < len(score), score[i] != score[j]. -/
theorem spec_12 (score : Slice Std.I64) (h : Pre score) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      find_relative_ranks score = ok r →
      ∀ i, i < score.val.length →
        ∀ b : List Std.U8, entryAt r i = some b →
          b = goldMedal ∨ b = silverMedal ∨ b = bronzeMedal ∨
            (b ≠ [] ∧ allDigits b ∧ noLeadingZero b) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (score : Slice Std.I64) (h : Pre score), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      find_relative_ranks score = ok r →
      ∀ i, i < score.val.length →
        ∀ b : List Std.U8, entryAt r i = some b →
          b = goldMedal ∨ b = silverMedal ∨ b = bronzeMedal ∨
            (b ≠ [] ∧ allDigits b ∧ noLeadingZero b)) := by
  sorry

end AegisSpec.FindRelativeRanks
