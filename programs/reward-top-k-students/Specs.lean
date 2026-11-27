import Aegis.TopStudents.Code.Funs

/-!
# Specifications of `Aegis.TopStudents.top_students`

LeetCode problem `reward-top-k-students`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.TopStudents

abbrev Word := List Std.U8

def IsLowerByte (b : Std.U8) : Prop := 97 ≤ b.val ∧ b.val ≤ 122

def IsSpaceByte (b : Std.U8) : Prop := b.val = 32

def wordsAux : List Std.U8 → List Std.U8 → List Word
  | [], cur => if cur.isEmpty then [] else [cur.reverse]
  | b :: rest, cur =>
    if b.val = 32 then
      (if cur.isEmpty then [] else [cur.reverse]) ++ wordsAux rest []
    else wordsAux rest (b :: cur)

def words (bs : List Std.U8) : List Word := wordsAux bs []

def joinWords (ws : List Word) : List Std.U8 :=
  match ws with
  | [] => []
  | w :: rest => w ++ rest.flatMap (fun x => 32#u8 :: x)

def entryBytes (l : List (alloc.vec.Vec Std.U8)) (i : ℕ) : List Std.U8 :=
  match l[i]? with
  | some v => v.val
  | none => []

def reportWords (report : Slice (alloc.vec.Vec Std.U8)) (i : ℕ) : List Word :=
  words (entryBytes report.val i)

def dictWords (d : Slice (alloc.vec.Vec Std.U8)) : List Word := d.val.map (fun v => v.val)

def countIn (dict ws : List Word) : ℕ := (ws.filter (fun w => decide (w ∈ dict))).length

def pointsAt (pos neg : Slice (alloc.vec.Vec Std.U8)) (report : Slice (alloc.vec.Vec Std.U8))
    (i : ℕ) : ℤ :=
  (3 : ℤ) * (countIn (dictWords pos) (reportWords report i) : ℤ) -
    (countIn (dictWords neg) (reportWords report i) : ℤ)

def indexOfId : List Std.I64 → Std.I64 → Option ℕ
  | [], _ => none
  | x :: xs, s => if x = s then some 0 else (indexOfId xs s).map (fun i => i + 1)

def Points (pos neg : Slice (alloc.vec.Vec Std.U8)) (report : Slice (alloc.vec.Vec Std.U8))
    (ids : Slice Std.I64) (s : Std.I64) : ℤ :=
  match indexOfId ids.val s with
  | some i => pointsAt pos neg report i
  | none => 0

def Outranks (pos neg : Slice (alloc.vec.Vec Std.U8)) (report : Slice (alloc.vec.Vec Std.U8))
    (ids : Slice Std.I64) (s t : Std.I64) : Prop :=
  Points pos neg report ids s > Points pos neg report ids t ∨
    (Points pos neg report ids s = Points pos neg report ids t ∧ s.val < t.val)

def ReportBytes (bs : List Std.U8) : Prop :=
  bs ≠ [] ∧ bs.length ≤ 100 ∧ joinWords (words bs) = bs ∧
    ∀ b ∈ bs, IsLowerByte b ∨ IsSpaceByte b

structure InputInv (pos neg : Slice (alloc.vec.Vec Std.U8)) (report : Slice (alloc.vec.Vec Std.U8))
    (ids : Slice Std.I64) (k : Std.I64) : Prop where

  len_eq : report.val.length = ids.val.length

  len_pos : 1 ≤ report.val.length

  len_le : report.val.length ≤ 10 ^ 4

  pos_nonempty : 1 ≤ pos.val.length

  neg_nonempty : 1 ≤ neg.val.length

  pos_words : ∀ w ∈ dictWords pos, w ≠ [] ∧ w.length ≤ 100 ∧ ∀ b ∈ w, IsLowerByte b

  neg_words : ∀ w ∈ dictWords neg, w ≠ [] ∧ w.length ≤ 100 ∧ ∀ b ∈ w, IsLowerByte b

  disjoint : ∀ w, w ∈ dictWords pos → w ∈ dictWords neg → False

  report_wf : ∀ (i : ℕ) (hi : i < report.val.length), ReportBytes (report.val[i]'hi).val

  id_bounds : ∀ (i : ℕ) (hi : i < ids.val.length),
    (1 : ℤ) ≤ (ids.val[i]'hi).val ∧ (ids.val[i]'hi).val ≤ (10 : ℤ) ^ 9

  ids_nodup : ids.val.Nodup

  k_pos : (1 : ℤ) ≤ k.val

  k_le : k.val ≤ (report.val.length : ℤ)

def IsTopK (pos neg : Slice (alloc.vec.Vec Std.U8)) (report : Slice (alloc.vec.Vec Std.U8))
    (ids : Slice Std.I64) (k : ℤ) (r : alloc.vec.Vec Std.I64) : Prop :=

  (r.val.length : ℤ) = k ∧

  (∀ (j : ℕ) (hj : j < r.val.length),
    ∃ (i : ℕ) (hi : i < ids.val.length), r.val[j]'hj = ids.val[i]'hi) ∧

  r.val.Nodup ∧

  (∀ (a b : ℕ) (ha : a < b) (hb : b < r.val.length),
    Outranks pos neg report ids (r.val[a]'(Nat.lt_trans ha hb)) (r.val[b]'hb)) ∧

  (∀ (a : ℕ) (ha : a < r.val.length), ∀ s, s ∈ ids.val → s ∉ r.val →
    Outranks pos neg report ids (r.val[a]'ha) s)

/-- Define a word of report[i] to be a maximal contiguous run of non-space bytes. For each student ID s = student_id[i], define points(s) = 3 * (number of words of report[i] that are byte-equal to some element of positive_feedback) - (number of words of report[i] that are byte-equal to some element of negative_feedback); this is well-defined because the student_id values are pairwise distinct. Say that a student ID s outranks a student ID t iff points(s) > points(t), or points(s) = points(t) and s < t. Whenever top_students returns a result r, all of the following hold: (1) len(r) = k; (2) every entry r[j] equals student_id[i] for some i with 0 <= i < n; (3) the entries r[0..k-1] are pairwise distinct; (4) for all 0 <= a < b < k, r[a] outranks r[b]; (5) for every 0 <= a < k and every student ID s that occurs among student_id[0..n-1] but does not occur among r[0..k-1], r[a] outranks s. These conditions uniquely determine r: it is exactly the sequence of the k highest-ranked students, ordered by non-increasing points with ties broken by smaller student ID.
  Preconditions: Let n = len(report) = len(student_id). Constraints: 1 <= n <= 10^4; 1 <= len(positive_feedback) and 1 <= len(negative_feedback); every word in positive_feedback and negative_feedback is a non-empty byte string of lowercase ASCII letters of length <= 100; no byte string occurs in both positive_feedback and negative_feedback; every report[i] is a non-empty byte string of lowercase letters and spaces of length <= 100, with exactly one space between consecutive words and no leading or trailing space; every student_id[i] satisfies 1 <= student_id[i] <= 10^9; the values student_id[0..n-1] are pairwise distinct; 1 <= k <= n. -/
theorem spec_1
    (pos neg : Slice (alloc.vec.Vec Std.U8)) (report : Slice (alloc.vec.Vec Std.U8))
    (ids : Slice Std.I64) (k : Std.I64) (h : InputInv pos neg report ids k) :
    ∀ r, Aegis.TopStudents.top_students pos neg report ids k = ok r →
      (IsTopK pos neg report ids k.val r ∧
        ∀ r' : alloc.vec.Vec Std.I64, IsTopK pos neg report ids k.val r' → r'.val = r.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (pos neg : Slice (alloc.vec.Vec Std.U8)) (report : Slice (alloc.vec.Vec Std.U8))
    (ids : Slice Std.I64) (k : Std.I64) (h : InputInv pos neg report ids k), ∀ r, Aegis.TopStudents.top_students pos neg report ids k = ok r →
      (IsTopK pos neg report ids k.val r ∧
        ∀ r' : alloc.vec.Vec Std.I64, IsTopK pos neg report ids k.val r' → r'.val = r.val)) := by
  sorry

/-- For every input satisfying the preconditions, top_students returns a result r and does not fail: no 64-bit integer overflow, no out-of-bounds indexing or slicing, and no panic occur.
  Preconditions: Let n = len(report) = len(student_id). Constraints: 1 <= n <= 10^4; 1 <= len(positive_feedback) and 1 <= len(negative_feedback); every word in positive_feedback and negative_feedback is a non-empty byte string of lowercase ASCII letters of length <= 100; no byte string occurs in both positive_feedback and negative_feedback; every report[i] is a non-empty byte string of lowercase letters and spaces of length <= 100, with exactly one space between consecutive words and no leading or trailing space; every student_id[i] satisfies 1 <= student_id[i] <= 10^9; the values student_id[0..n-1] are pairwise distinct; 1 <= k <= n. -/
theorem spec_2
    (pos neg : Slice (alloc.vec.Vec Std.U8)) (report : Slice (alloc.vec.Vec Std.U8))
    (ids : Slice Std.I64) (k : Std.I64) (h : InputInv pos neg report ids k) :
    ∃ r, Aegis.TopStudents.top_students pos neg report ids k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (pos neg : Slice (alloc.vec.Vec Std.U8)) (report : Slice (alloc.vec.Vec Std.U8))
    (ids : Slice Std.I64) (k : Std.I64) (h : InputInv pos neg report ids k), ∃ r, Aegis.TopStudents.top_students pos neg report ids k = ok r) := by
  sorry

/-- Whenever top_students returns a result r, len(r) = k. Since 1 <= k <= len(student_id), it also follows that 1 <= len(r) <= len(student_id).
  Preconditions: Let n = len(report) = len(student_id). Constraints: 1 <= n <= 10^4; 1 <= len(positive_feedback) and 1 <= len(negative_feedback); every word in positive_feedback and negative_feedback is a non-empty byte string of lowercase ASCII letters of length <= 100; no byte string occurs in both positive_feedback and negative_feedback; every report[i] is a non-empty byte string of lowercase letters and spaces of length <= 100, with exactly one space between consecutive words and no leading or trailing space; every student_id[i] satisfies 1 <= student_id[i] <= 10^9; the values student_id[0..n-1] are pairwise distinct; 1 <= k <= n. -/
theorem spec_3
    (pos neg : Slice (alloc.vec.Vec Std.U8)) (report : Slice (alloc.vec.Vec Std.U8))
    (ids : Slice Std.I64) (k : Std.I64) (h : InputInv pos neg report ids k) :
    ∀ r, Aegis.TopStudents.top_students pos neg report ids k = ok r →
      (r.val.length : ℤ) = k.val ∧ 1 ≤ r.val.length ∧ r.val.length ≤ ids.val.length := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (pos neg : Slice (alloc.vec.Vec Std.U8)) (report : Slice (alloc.vec.Vec Std.U8))
    (ids : Slice Std.I64) (k : Std.I64) (h : InputInv pos neg report ids k), ∀ r, Aegis.TopStudents.top_students pos neg report ids k = ok r →
      (r.val.length : ℤ) = k.val ∧ 1 ≤ r.val.length ∧ r.val.length ≤ ids.val.length) := by
  sorry

/-- Whenever top_students returns a result r, for every j with 0 <= j < len(r) there exists an index i with 0 <= i < len(student_id) such that r[j] = student_id[i]. In other words, each returned value is one of the input student IDs and has a witnessing index in student_id.
  Preconditions: Let n = len(report) = len(student_id). Constraints: 1 <= n <= 10^4; 1 <= len(positive_feedback) and 1 <= len(negative_feedback); every word in positive_feedback and negative_feedback is a non-empty byte string of lowercase ASCII letters of length <= 100; no byte string occurs in both positive_feedback and negative_feedback; every report[i] is a non-empty byte string of lowercase letters and spaces of length <= 100, with exactly one space between consecutive words and no leading or trailing space; every student_id[i] satisfies 1 <= student_id[i] <= 10^9; the values student_id[0..n-1] are pairwise distinct; 1 <= k <= n. -/
theorem spec_4
    (pos neg : Slice (alloc.vec.Vec Std.U8)) (report : Slice (alloc.vec.Vec Std.U8))
    (ids : Slice Std.I64) (k : Std.I64) (h : InputInv pos neg report ids k) :
    ∀ r, Aegis.TopStudents.top_students pos neg report ids k = ok r →
      ∀ (j : ℕ) (hj : j < r.val.length),
        ∃ (i : ℕ) (hi : i < ids.val.length), r.val[j]'hj = ids.val[i]'hi := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (pos neg : Slice (alloc.vec.Vec Std.U8)) (report : Slice (alloc.vec.Vec Std.U8))
    (ids : Slice Std.I64) (k : Std.I64) (h : InputInv pos neg report ids k), ∀ r, Aegis.TopStudents.top_students pos neg report ids k = ok r →
      ∀ (j : ℕ) (hj : j < r.val.length),
        ∃ (i : ℕ) (hi : i < ids.val.length), r.val[j]'hj = ids.val[i]'hi) := by
  sorry

/-- Whenever top_students returns a result r, for all a and b with 0 <= a < b < len(r), r[a] != r[b]. That is, the returned vector has no repeated entry.
  Preconditions: Let n = len(report) = len(student_id). Constraints: 1 <= n <= 10^4; 1 <= len(positive_feedback) and 1 <= len(negative_feedback); every word in positive_feedback and negative_feedback is a non-empty byte string of lowercase ASCII letters of length <= 100; no byte string occurs in both positive_feedback and negative_feedback; every report[i] is a non-empty byte string of lowercase letters and spaces of length <= 100, with exactly one space between consecutive words and no leading or trailing space; every student_id[i] satisfies 1 <= student_id[i] <= 10^9; the values student_id[0..n-1] are pairwise distinct; 1 <= k <= n. -/
theorem spec_5
    (pos neg : Slice (alloc.vec.Vec Std.U8)) (report : Slice (alloc.vec.Vec Std.U8))
    (ids : Slice Std.I64) (k : Std.I64) (h : InputInv pos neg report ids k) :
    ∀ r, Aegis.TopStudents.top_students pos neg report ids k = ok r → r.val.Nodup := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (pos neg : Slice (alloc.vec.Vec Std.U8)) (report : Slice (alloc.vec.Vec Std.U8))
    (ids : Slice Std.I64) (k : Std.I64) (h : InputInv pos neg report ids k), ∀ r, Aegis.TopStudents.top_students pos neg report ids k = ok r → r.val.Nodup) := by
  sorry

/-- Whenever top_students returns a result r, for all a and b with 0 <= a < b < len(r), points(r[a]) >= points(r[b]), where for a student ID s = student_id[i], points(s) = 3 * (number of words of report[i] that are byte-equal to some element of positive_feedback) - (number of words of report[i] that are byte-equal to some element of negative_feedback), a word being a maximal contiguous run of non-space bytes.
  Preconditions: Let n = len(report) = len(student_id). Constraints: 1 <= n <= 10^4; 1 <= len(positive_feedback) and 1 <= len(negative_feedback); every word in positive_feedback and negative_feedback is a non-empty byte string of lowercase ASCII letters of length <= 100; no byte string occurs in both positive_feedback and negative_feedback; every report[i] is a non-empty byte string of lowercase letters and spaces of length <= 100, with exactly one space between consecutive words and no leading or trailing space; every student_id[i] satisfies 1 <= student_id[i] <= 10^9; the values student_id[0..n-1] are pairwise distinct; 1 <= k <= n. -/
theorem spec_6
    (pos neg : Slice (alloc.vec.Vec Std.U8)) (report : Slice (alloc.vec.Vec Std.U8))
    (ids : Slice Std.I64) (k : Std.I64) (h : InputInv pos neg report ids k) :
    ∀ r, Aegis.TopStudents.top_students pos neg report ids k = ok r →
      ∀ (a b : ℕ) (ha : a < b) (hb : b < r.val.length),
        Points pos neg report ids (r.val[b]'hb) ≤
          Points pos neg report ids (r.val[a]'(Nat.lt_trans ha hb)) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (pos neg : Slice (alloc.vec.Vec Std.U8)) (report : Slice (alloc.vec.Vec Std.U8))
    (ids : Slice Std.I64) (k : Std.I64) (h : InputInv pos neg report ids k), ∀ r, Aegis.TopStudents.top_students pos neg report ids k = ok r →
      ∀ (a b : ℕ) (ha : a < b) (hb : b < r.val.length),
        Points pos neg report ids (r.val[b]'hb) ≤
          Points pos neg report ids (r.val[a]'(Nat.lt_trans ha hb))) := by
  sorry

/-- Whenever top_students returns a result r, for all a and b with 0 <= a < b < len(r), if points(r[a]) = points(r[b]) then r[a] < r[b], where for a student ID s = student_id[i], points(s) = 3 * (number of words of report[i] that are byte-equal to some element of positive_feedback) - (number of words of report[i] that are byte-equal to some element of negative_feedback), a word being a maximal contiguous run of non-space bytes.
  Preconditions: Let n = len(report) = len(student_id). Constraints: 1 <= n <= 10^4; 1 <= len(positive_feedback) and 1 <= len(negative_feedback); every word in positive_feedback and negative_feedback is a non-empty byte string of lowercase ASCII letters of length <= 100; no byte string occurs in both positive_feedback and negative_feedback; every report[i] is a non-empty byte string of lowercase letters and spaces of length <= 100, with exactly one space between consecutive words and no leading or trailing space; every student_id[i] satisfies 1 <= student_id[i] <= 10^9; the values student_id[0..n-1] are pairwise distinct; 1 <= k <= n. -/
theorem spec_7
    (pos neg : Slice (alloc.vec.Vec Std.U8)) (report : Slice (alloc.vec.Vec Std.U8))
    (ids : Slice Std.I64) (k : Std.I64) (h : InputInv pos neg report ids k) :
    ∀ r, Aegis.TopStudents.top_students pos neg report ids k = ok r →
      ∀ (a b : ℕ) (ha : a < b) (hb : b < r.val.length),
        Points pos neg report ids (r.val[a]'(Nat.lt_trans ha hb)) =
          Points pos neg report ids (r.val[b]'hb) →
          (r.val[a]'(Nat.lt_trans ha hb)).val < (r.val[b]'hb).val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (pos neg : Slice (alloc.vec.Vec Std.U8)) (report : Slice (alloc.vec.Vec Std.U8))
    (ids : Slice Std.I64) (k : Std.I64) (h : InputInv pos neg report ids k), ∀ r, Aegis.TopStudents.top_students pos neg report ids k = ok r →
      ∀ (a b : ℕ) (ha : a < b) (hb : b < r.val.length),
        Points pos neg report ids (r.val[a]'(Nat.lt_trans ha hb)) =
          Points pos neg report ids (r.val[b]'hb) →
          (r.val[a]'(Nat.lt_trans ha hb)).val < (r.val[b]'hb).val) := by
  sorry

/-- Whenever top_students returns a result r, for every a with 0 <= a < len(r) and every i with 0 <= i < len(student_id) such that student_id[i] does not occur among the entries of r, r[a] outranks student_id[i], where outranks(s, t) means points(s) > points(t), or points(s) = points(t) and s < t, and for a student ID s = student_id[j], points(s) = 3 * (number of words of report[j] that are byte-equal to some element of positive_feedback) - (number of words of report[j] that are byte-equal to some element of negative_feedback), with words being maximal contiguous runs of non-space bytes.
  Preconditions: Let n = len(report) = len(student_id). Constraints: 1 <= n <= 10^4; 1 <= len(positive_feedback) and 1 <= len(negative_feedback); every word in positive_feedback and negative_feedback is a non-empty byte string of lowercase ASCII letters of length <= 100; no byte string occurs in both positive_feedback and negative_feedback; every report[i] is a non-empty byte string of lowercase letters and spaces of length <= 100, with exactly one space between consecutive words and no leading or trailing space; every student_id[i] satisfies 1 <= student_id[i] <= 10^9; the values student_id[0..n-1] are pairwise distinct; 1 <= k <= n. -/
theorem spec_8
    (pos neg : Slice (alloc.vec.Vec Std.U8)) (report : Slice (alloc.vec.Vec Std.U8))
    (ids : Slice Std.I64) (k : Std.I64) (h : InputInv pos neg report ids k) :
    ∀ r, Aegis.TopStudents.top_students pos neg report ids k = ok r →
      ∀ (a : ℕ) (ha : a < r.val.length) (i : ℕ) (hi : i < ids.val.length),
        ids.val[i]'hi ∉ r.val →
          Outranks pos neg report ids (r.val[a]'ha) (ids.val[i]'hi) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (pos neg : Slice (alloc.vec.Vec Std.U8)) (report : Slice (alloc.vec.Vec Std.U8))
    (ids : Slice Std.I64) (k : Std.I64) (h : InputInv pos neg report ids k), ∀ r, Aegis.TopStudents.top_students pos neg report ids k = ok r →
      ∀ (a : ℕ) (ha : a < r.val.length) (i : ℕ) (hi : i < ids.val.length),
        ids.val[i]'hi ∉ r.val →
          Outranks pos neg report ids (r.val[a]'ha) (ids.val[i]'hi)) := by
  sorry

/-- Whenever top_students returns a result r and k = len(student_id) = n, the entries r[0..len(r)-1] are exactly the n pairwise-distinct values student_id[0..n-1]: the map j |-> r[j] is a bijection from {0, ..., n-1} onto the set of student IDs, and len(r) = n.
  Preconditions: Let n = len(report) = len(student_id). Constraints: 1 <= n <= 10^4; 1 <= len(positive_feedback) and 1 <= len(negative_feedback); every word in positive_feedback and negative_feedback is a non-empty byte string of lowercase ASCII letters of length <= 100; no byte string occurs in both positive_feedback and negative_feedback; every report[i] is a non-empty byte string of lowercase letters and spaces of length <= 100, with exactly one space between consecutive words and no leading or trailing space; every student_id[i] satisfies 1 <= student_id[i] <= 10^9; the values student_id[0..n-1] are pairwise distinct; 1 <= k <= n. -/
theorem spec_9
    (pos neg : Slice (alloc.vec.Vec Std.U8)) (report : Slice (alloc.vec.Vec Std.U8))
    (ids : Slice Std.I64) (k : Std.I64) (h : InputInv pos neg report ids k) :
    ∀ r, Aegis.TopStudents.top_students pos neg report ids k = ok r →
      k.val = (ids.val.length : ℤ) →
        r.val.length = ids.val.length ∧ r.val.Nodup ∧
          ∀ s, s ∈ r.val ↔ s ∈ ids.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (pos neg : Slice (alloc.vec.Vec Std.U8)) (report : Slice (alloc.vec.Vec Std.U8))
    (ids : Slice Std.I64) (k : Std.I64) (h : InputInv pos neg report ids k), ∀ r, Aegis.TopStudents.top_students pos neg report ids k = ok r →
      k.val = (ids.val.length : ℤ) →
        r.val.length = ids.val.length ∧ r.val.Nodup ∧
          ∀ s, s ∈ r.val ↔ s ∈ ids.val) := by
  sorry

/-- Whenever top_students returns a result r, if all student IDs occurring in student_id have the same points, where for a student ID s = student_id[i], points(s) = 3 * (number of words of report[i] that are byte-equal to some element of positive_feedback) - (number of words of report[i] that are byte-equal to some element of negative_feedback) (words are maximal contiguous runs of non-space bytes), then r is strictly increasing, r[0] < r[1] < ... < r[k-1], and every entry of r is strictly smaller than every student ID that does not occur among the entries of r.
  Preconditions: Let n = len(report) = len(student_id). Constraints: 1 <= n <= 10^4; 1 <= len(positive_feedback) and 1 <= len(negative_feedback); every word in positive_feedback and negative_feedback is a non-empty byte string of lowercase ASCII letters of length <= 100; no byte string occurs in both positive_feedback and negative_feedback; every report[i] is a non-empty byte string of lowercase letters and spaces of length <= 100, with exactly one space between consecutive words and no leading or trailing space; every student_id[i] satisfies 1 <= student_id[i] <= 10^9; the values student_id[0..n-1] are pairwise distinct; 1 <= k <= n. -/
theorem spec_10
    (pos neg : Slice (alloc.vec.Vec Std.U8)) (report : Slice (alloc.vec.Vec Std.U8))
    (ids : Slice Std.I64) (k : Std.I64) (h : InputInv pos neg report ids k) :
    ∀ r, Aegis.TopStudents.top_students pos neg report ids k = ok r →
      (∀ s, s ∈ ids.val → ∀ t, t ∈ ids.val →
        Points pos neg report ids s = Points pos neg report ids t) →
        (∀ (a b : ℕ) (ha : a < b) (hb : b < r.val.length),
          (r.val[a]'(Nat.lt_trans ha hb)).val < (r.val[b]'hb).val) ∧
          (∀ (a : ℕ) (ha : a < r.val.length), ∀ s, s ∈ ids.val → s ∉ r.val →
            (r.val[a]'ha).val < s.val) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (pos neg : Slice (alloc.vec.Vec Std.U8)) (report : Slice (alloc.vec.Vec Std.U8))
    (ids : Slice Std.I64) (k : Std.I64) (h : InputInv pos neg report ids k), ∀ r, Aegis.TopStudents.top_students pos neg report ids k = ok r →
      (∀ s, s ∈ ids.val → ∀ t, t ∈ ids.val →
        Points pos neg report ids s = Points pos neg report ids t) →
        (∀ (a b : ℕ) (ha : a < b) (hb : b < r.val.length),
          (r.val[a]'(Nat.lt_trans ha hb)).val < (r.val[b]'hb).val) ∧
          (∀ (a : ℕ) (ha : a < r.val.length), ∀ s, s ∈ ids.val → s ∉ r.val →
            (r.val[a]'ha).val < s.val)) := by
  sorry

/-- For every reordering positive_feedback' of positive_feedback and every reordering negative_feedback' of negative_feedback (i.e., the same elements in a possibly different order), the call top_students(positive_feedback', negative_feedback', report, student_id, k) and the call top_students(positive_feedback, negative_feedback, report, student_id, k) both return and return the same vector.
  Preconditions: Let n = len(report) = len(student_id). Constraints: 1 <= n <= 10^4; 1 <= len(positive_feedback) and 1 <= len(negative_feedback); every word in positive_feedback and negative_feedback is a non-empty byte string of lowercase ASCII letters of length <= 100; no byte string occurs in both positive_feedback and negative_feedback; every report[i] is a non-empty byte string of lowercase letters and spaces of length <= 100, with exactly one space between consecutive words and no leading or trailing space; every student_id[i] satisfies 1 <= student_id[i] <= 10^9; the values student_id[0..n-1] are pairwise distinct; 1 <= k <= n. -/
theorem spec_11
    (pos neg : Slice (alloc.vec.Vec Std.U8)) (report : Slice (alloc.vec.Vec Std.U8))
    (ids : Slice Std.I64) (k : Std.I64) (h : InputInv pos neg report ids k)
    (pos' neg' : Slice (alloc.vec.Vec Std.U8))
    (hpos : (dictWords pos').Perm (dictWords pos))
    (hneg : (dictWords neg').Perm (dictWords neg)) :
    ∃ r, Aegis.TopStudents.top_students pos neg report ids k = ok r ∧
      Aegis.TopStudents.top_students pos' neg' report ids k = ok r := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (pos neg : Slice (alloc.vec.Vec Std.U8)) (report : Slice (alloc.vec.Vec Std.U8))
    (ids : Slice Std.I64) (k : Std.I64) (h : InputInv pos neg report ids k)
    (pos' neg' : Slice (alloc.vec.Vec Std.U8))
    (hpos : (dictWords pos').Perm (dictWords pos))
    (hneg : (dictWords neg').Perm (dictWords neg)), ∃ r, Aegis.TopStudents.top_students pos neg report ids k = ok r ∧
      Aegis.TopStudents.top_students pos' neg' report ids k = ok r) := by
  sorry

/-- For every permutation pi of {0, ..., n-1}, let report' and student_id' satisfy report'[i] = report[pi(i)] and student_id'[i] = student_id[pi(i)] for 0 <= i < n. Then top_students(positive_feedback, negative_feedback, report', student_id', k) and top_students(positive_feedback, negative_feedback, report, student_id, k) both return and return the same vector.
  Preconditions: Let n = len(report) = len(student_id). Constraints: 1 <= n <= 10^4; 1 <= len(positive_feedback) and 1 <= len(negative_feedback); every word in positive_feedback and negative_feedback is a non-empty byte string of lowercase ASCII letters of length <= 100; no byte string occurs in both positive_feedback and negative_feedback; every report[i] is a non-empty byte string of lowercase letters and spaces of length <= 100, with exactly one space between consecutive words and no leading or trailing space; every student_id[i] satisfies 1 <= student_id[i] <= 10^9; the values student_id[0..n-1] are pairwise distinct; 1 <= k <= n. -/
theorem spec_12
    (pos neg : Slice (alloc.vec.Vec Std.U8)) (report : Slice (alloc.vec.Vec Std.U8))
    (ids : Slice Std.I64) (k : Std.I64) (h : InputInv pos neg report ids k)
    (report' : Slice (alloc.vec.Vec Std.U8)) (ids' : Slice Std.I64)
    (hperm : (report'.val.zip ids'.val).Perm (report.val.zip ids.val)) :
    ∃ r, Aegis.TopStudents.top_students pos neg report ids k = ok r ∧
      Aegis.TopStudents.top_students pos neg report' ids' k = ok r := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (pos neg : Slice (alloc.vec.Vec Std.U8)) (report : Slice (alloc.vec.Vec Std.U8))
    (ids : Slice Std.I64) (k : Std.I64) (h : InputInv pos neg report ids k)
    (report' : Slice (alloc.vec.Vec Std.U8)) (ids' : Slice Std.I64)
    (hperm : (report'.val.zip ids'.val).Perm (report.val.zip ids.val)), ∃ r, Aegis.TopStudents.top_students pos neg report ids k = ok r ∧
      Aegis.TopStudents.top_students pos neg report' ids' k = ok r) := by
  sorry

/-- Whenever top_students returns a result r (which is non-empty because len(r) = k and k >= 1), the first entry r[0] is a student ID attaining the maximum points over all student IDs occurring in student_id, and among all students attaining that maximum, r[0] is the smallest ID; equivalently, r[0] outranks every other student, where for a student ID s = student_id[i], points(s) = 3 * (number of words of report[i] that are byte-equal to some element of positive_feedback) - (number of words of report[i] that are byte-equal to some element of negative_feedback) (words are maximal contiguous runs of non-space bytes) and outranks(s, t) means points(s) > points(t) or (points(s) = points(t) and s < t).
  Preconditions: Let n = len(report) = len(student_id). Constraints: 1 <= n <= 10^4; 1 <= len(positive_feedback) and 1 <= len(negative_feedback); every word in positive_feedback and negative_feedback is a non-empty byte string of lowercase ASCII letters of length <= 100; no byte string occurs in both positive_feedback and negative_feedback; every report[i] is a non-empty byte string of lowercase letters and spaces of length <= 100, with exactly one space between consecutive words and no leading or trailing space; every student_id[i] satisfies 1 <= student_id[i] <= 10^9; the values student_id[0..n-1] are pairwise distinct; 1 <= k <= n. -/
theorem spec_13
    (pos neg : Slice (alloc.vec.Vec Std.U8)) (report : Slice (alloc.vec.Vec Std.U8))
    (ids : Slice Std.I64) (k : Std.I64) (h : InputInv pos neg report ids k) :
    ∀ r, Aegis.TopStudents.top_students pos neg report ids k = ok r →
      ∀ x, r.val.head? = some x →
        x ∈ ids.val ∧
          (∀ s, s ∈ ids.val → Points pos neg report ids s ≤ Points pos neg report ids x) ∧
          (∀ s, s ∈ ids.val →
            Points pos neg report ids s = Points pos neg report ids x → x.val ≤ s.val) ∧
          (∀ s, s ∈ ids.val → s ≠ x → Outranks pos neg report ids x s) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (pos neg : Slice (alloc.vec.Vec Std.U8)) (report : Slice (alloc.vec.Vec Std.U8))
    (ids : Slice Std.I64) (k : Std.I64) (h : InputInv pos neg report ids k), ∀ r, Aegis.TopStudents.top_students pos neg report ids k = ok r →
      ∀ x, r.val.head? = some x →
        x ∈ ids.val ∧
          (∀ s, s ∈ ids.val → Points pos neg report ids s ≤ Points pos neg report ids x) ∧
          (∀ s, s ∈ ids.val →
            Points pos neg report ids s = Points pos neg report ids x → x.val ≤ s.val) ∧
          (∀ s, s ∈ ids.val → s ≠ x → Outranks pos neg report ids x s)) := by
  sorry

/-- Whenever top_students(..., k) returns r and top_students(..., k') returns r', then len(r) = k, len(r') = k', and r[j] = r'[j] for all 0 <= j < k. Equivalently, increasing k only appends the next students in rank order.
  Preconditions: Same as spec_1, with 1 <= k <= k' <= n. -/
theorem spec_14
    (pos neg : Slice (alloc.vec.Vec Std.U8)) (report : Slice (alloc.vec.Vec Std.U8))
    (ids : Slice Std.I64) (k k' : Std.I64) (h : InputInv pos neg report ids k)
    (hk : k.val ≤ k'.val) (hk' : k'.val ≤ (report.val.length : ℤ)) :
    ∀ r r', Aegis.TopStudents.top_students pos neg report ids k = ok r →
      Aegis.TopStudents.top_students pos neg report ids k' = ok r' →
        (r.val.length : ℤ) = k.val ∧ (r'.val.length : ℤ) = k'.val ∧
          List.IsPrefix r.val r'.val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (pos neg : Slice (alloc.vec.Vec Std.U8)) (report : Slice (alloc.vec.Vec Std.U8))
    (ids : Slice Std.I64) (k k' : Std.I64) (h : InputInv pos neg report ids k)
    (hk : k.val ≤ k'.val) (hk' : k'.val ≤ (report.val.length : ℤ)), ∀ r r', Aegis.TopStudents.top_students pos neg report ids k = ok r →
      Aegis.TopStudents.top_students pos neg report ids k' = ok r' →
        (r.val.length : ℤ) = k.val ∧ (r'.val.length : ℤ) = k'.val ∧
          List.IsPrefix r.val r'.val) := by
  sorry

/-- Whenever top_students returns r, for every returned student r[j] with 0 <= j < len(r), -50 <= points(r[j]) <= 150, where points is defined as in spec_1.
  Preconditions: Same as spec_1. -/
theorem spec_15
    (pos neg : Slice (alloc.vec.Vec Std.U8)) (report : Slice (alloc.vec.Vec Std.U8))
    (ids : Slice Std.I64) (k : Std.I64) (h : InputInv pos neg report ids k) :
    ∀ r, Aegis.TopStudents.top_students pos neg report ids k = ok r →
      ∀ (j : ℕ) (hj : j < r.val.length),
        (-50 : ℤ) ≤ Points pos neg report ids (r.val[j]'hj) ∧
          Points pos neg report ids (r.val[j]'hj) ≤ 150 := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (pos neg : Slice (alloc.vec.Vec Std.U8)) (report : Slice (alloc.vec.Vec Std.U8))
    (ids : Slice Std.I64) (k : Std.I64) (h : InputInv pos neg report ids k), ∀ r, Aegis.TopStudents.top_students pos neg report ids k = ok r →
      ∀ (j : ℕ) (hj : j < r.val.length),
        (-50 : ℤ) ≤ Points pos neg report ids (r.val[j]'hj) ∧
          Points pos neg report ids (r.val[j]'hj) ≤ 150) := by
  sorry

end AegisSpec.TopStudents
