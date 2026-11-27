import Aegis.EntityParser.Code.Funs

/-!
# Specifications of `Aegis.EntityParser.entity_parser`

LeetCode problem `html-entity-parser`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.EntityParser

def bytes (l : List Std.U8) : List ℕ := l.map fun b => b.val

def byteAt (l : List ℕ) (i : ℕ) : Option ℕ := (l.drop i).head?

def tok_quot : List ℕ := [38, 113, 117, 111, 116, 59]

def tok_apos : List ℕ := [38, 97, 112, 111, 115, 59]

def tok_amp : List ℕ := [38, 97, 109, 112, 59]

def tok_gt : List ℕ := [38, 103, 116, 59]

def tok_lt : List ℕ := [38, 108, 116, 59]

def tok_frasl : List ℕ := [38, 102, 114, 97, 115, 108, 59]

def tokens : List (List ℕ) := [tok_quot, tok_apos, tok_amp, tok_gt, tok_lt, tok_frasl]

def decode : List ℕ → List ℕ
  | [] => []
  | 38 :: 113 :: 117 :: 111 :: 116 :: 59 :: rest => 34 :: decode rest
  | 38 :: 97 :: 112 :: 111 :: 115 :: 59 :: rest => 39 :: decode rest
  | 38 :: 97 :: 109 :: 112 :: 59 :: rest => 38 :: decode rest
  | 38 :: 103 :: 116 :: 59 :: rest => 62 :: decode rest
  | 38 :: 108 :: 116 :: 59 :: rest => 60 :: decode rest
  | 38 :: 102 :: 114 :: 97 :: 115 :: 108 :: 59 :: rest => 47 :: decode rest
  | x :: rest => x :: decode rest

abbrev OccursAt (pat txt : List ℕ) (i : ℕ) : Prop :=
  i + pat.length ≤ txt.length ∧ (txt.drop i).take pat.length = pat

def OccursIn (pat txt : List ℕ) : Prop := ∃ i, OccursAt pat txt i

def countOcc (pat txt : List ℕ) : ℕ :=
  ((List.range (txt.length + 1)).filter fun i => decide (OccursAt pat txt i)).length

def countByte (c : ℕ) (l : List ℕ) : ℕ := (l.filter fun b => b = c).length

/-- The function returns a byte vector r equal to the unique result of replacing, in the original text, every contiguous occurrence of each of these six tokens by the indicated byte: `&quot;` -> byte 34 (quotation mark), `&apos;` -> byte 39 (apostrophe), `&amp;` -> byte 38 (ampersand), `&gt;` -> byte 62 (greater-than sign), `&lt;` -> byte 60 (less-than sign), `&frasl;` -> byte 47 (slash). Every byte of text not covered by such an occurrence is copied unchanged in its original order. Occurrences are those in the original text; a replacement byte that would form a new token is not rescanned or replaced. No two listed token occurrences can overlap (each token begins with byte 38 and contains no other byte 38), so r is well-defined and unique.
  Preconditions: 1 <= len(text) <= 100000. The bytes may be any values 0..255. -/
theorem spec_1 (text : Slice Std.U8)
    (h_len_lo : 1 ≤ text.val.length) (h_len_hi : text.val.length ≤ 100000) :
    ∃ r : alloc.vec.Vec Std.U8,
      Aegis.EntityParser.entity_parser text = ok r ∧
        bytes r.val = decode (bytes text.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (text : Slice Std.U8)
    (h_len_lo : 1 ≤ text.val.length) (h_len_hi : text.val.length ≤ 100000), ∃ r : alloc.vec.Vec Std.U8,
      Aegis.EntityParser.entity_parser text = ok r ∧
        bytes r.val = decode (bytes text.val)) := by
  sorry

/-- The function returns some result r (a successful Result); it does not panic, fail, go out of bounds, or overflow on any input satisfying these preconditions.
  Preconditions: 1 <= len(text) <= 100000. -/
theorem spec_2 (text : Slice Std.U8)
    (h_len_lo : 1 ≤ text.val.length) (h_len_hi : text.val.length ≤ 100000) :
    ∃ r : alloc.vec.Vec Std.U8, Aegis.EntityParser.entity_parser text = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (text : Slice Std.U8)
    (h_len_lo : 1 ≤ text.val.length) (h_len_hi : text.val.length ≤ 100000), ∃ r : alloc.vec.Vec Std.U8, Aegis.EntityParser.entity_parser text = ok r) := by
  sorry

/-- Let Nq, Na, Nm, Ng, Nl, Nf be the numbers of contiguous occurrences in text of `&quot;`, `&apos;`, `&amp;`, `&gt;`, `&lt;`, and `&frasl;`, respectively. Whenever the function returns r, len(r) = len(text) - 5*Nq - 5*Na - 4*Nm - 3*Ng - 3*Nl - 6*Nf.
  Preconditions: 1 <= len(text) <= 100000. -/
theorem spec_3 (text : Slice Std.U8)
    (h_len_lo : 1 ≤ text.val.length) (h_len_hi : text.val.length ≤ 100000) :
    ∀ r : alloc.vec.Vec Std.U8,
      Aegis.EntityParser.entity_parser text = ok r →
        r.val.length
          = text.val.length
            - 5 * countOcc tok_quot (bytes text.val)
            - 5 * countOcc tok_apos (bytes text.val)
            - 4 * countOcc tok_amp (bytes text.val)
            - 3 * countOcc tok_gt (bytes text.val)
            - 3 * countOcc tok_lt (bytes text.val)
            - 6 * countOcc tok_frasl (bytes text.val) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (text : Slice Std.U8)
    (h_len_lo : 1 ≤ text.val.length) (h_len_hi : text.val.length ≤ 100000), ∀ r : alloc.vec.Vec Std.U8,
      Aegis.EntityParser.entity_parser text = ok r →
        r.val.length
          = text.val.length
            - 5 * countOcc tok_quot (bytes text.val)
            - 5 * countOcc tok_apos (bytes text.val)
            - 4 * countOcc tok_amp (bytes text.val)
            - 3 * countOcc tok_gt (bytes text.val)
            - 3 * countOcc tok_lt (bytes text.val)
            - 6 * countOcc tok_frasl (bytes text.val)) := by
  sorry

/-- The function returns r with len(r) = len(text) and r[i] = text[i] for every i with 0 <= i < len(text).
  Preconditions: 1 <= len(text) <= 100000, and none of `&quot;`, `&apos;`, `&amp;`, `&gt;`, `&lt;`, `&frasl;` occurs as a contiguous substring of text. -/
theorem spec_4 (text : Slice Std.U8)
    (h_len_lo : 1 ≤ text.val.length) (h_len_hi : text.val.length ≤ 100000)
    (h_no_tok : ∀ p ∈ tokens, ¬ OccursIn p (bytes text.val)) :
    ∃ r : alloc.vec.Vec Std.U8,
      Aegis.EntityParser.entity_parser text = ok r ∧
        r.val.length = text.val.length ∧
          ∀ i : ℕ, i < text.val.length →
            byteAt (bytes r.val) i = byteAt (bytes text.val) i := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (text : Slice Std.U8)
    (h_len_lo : 1 ≤ text.val.length) (h_len_hi : text.val.length ≤ 100000)
    (h_no_tok : ∀ p ∈ tokens, ¬ OccursIn p (bytes text.val)), ∃ r : alloc.vec.Vec Std.U8,
      Aegis.EntityParser.entity_parser text = ok r ∧
        r.val.length = text.val.length ∧
          ∀ i : ℕ, i < text.val.length →
            byteAt (bytes r.val) i = byteAt (bytes text.val) i) := by
  sorry

/-- Whenever the function returns r, the subcalls entity_parser(A) and entity_parser(B) also return, and r = entity_parser(A) ++ entity_parser(B) as byte-vector concatenation.
  Preconditions: 1 <= len(text) <= 100000. Let A and B be byte sequences with text = A ++ B and 1 <= len(A) < len(text). Assume that no contiguous occurrence of any of the six tokens in text starts at an index < len(A) and ends at an index >= len(A) (no token occurrence crosses the split between A and B). -/
theorem spec_5 (text : Slice Std.U8)
    (h_len_lo : 1 ≤ text.val.length) (h_len_hi : text.val.length ≤ 100000)
    (A B : Slice Std.U8) (h_split : text.val = A.val ++ B.val)
    (h_A_lo : 1 ≤ A.val.length) (h_A_hi : A.val.length < text.val.length)
    (h_no_cross : ∀ p ∈ tokens, ∀ i : ℕ, OccursAt p (bytes text.val) i →
      ¬ (i < A.val.length ∧ A.val.length ≤ i + p.length)) :
    ∀ r : alloc.vec.Vec Std.U8,
      Aegis.EntityParser.entity_parser text = ok r →
        ∃ ra rb : alloc.vec.Vec Std.U8,
          Aegis.EntityParser.entity_parser A = ok ra ∧
            Aegis.EntityParser.entity_parser B = ok rb ∧ r.val = ra.val ++ rb.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (text : Slice Std.U8)
    (h_len_lo : 1 ≤ text.val.length) (h_len_hi : text.val.length ≤ 100000)
    (A B : Slice Std.U8) (h_split : text.val = A.val ++ B.val)
    (h_A_lo : 1 ≤ A.val.length) (h_A_hi : A.val.length < text.val.length)
    (h_no_cross : ∀ p ∈ tokens, ∀ i : ℕ, OccursAt p (bytes text.val) i →
      ¬ (i < A.val.length ∧ A.val.length ≤ i + p.length)), ∀ r : alloc.vec.Vec Std.U8,
      Aegis.EntityParser.entity_parser text = ok r →
        ∃ ra rb : alloc.vec.Vec Std.U8,
          Aegis.EntityParser.entity_parser A = ok ra ∧
            Aegis.EntityParser.entity_parser B = ok rb ∧ r.val = ra.val ++ rb.val) := by
  sorry

/-- Let Nq, Na, Ng, Nl, Nf be the numbers of contiguous occurrences in text of `&quot;`, `&apos;`, `&gt;`, `&lt;`, and `&frasl;`, respectively, and let camps(x) be the number of bytes equal to 38 in byte sequence x. Whenever the function returns r, camps(r) = camps(text) - Nq - Na - Ng - Nl - Nf.
  Preconditions: 1 <= len(text) <= 100000. -/
theorem spec_6 (text : Slice Std.U8)
    (h_len_lo : 1 ≤ text.val.length) (h_len_hi : text.val.length ≤ 100000) :
    ∀ r : alloc.vec.Vec Std.U8,
      Aegis.EntityParser.entity_parser text = ok r →
        countByte 38 (bytes r.val)
          = countByte 38 (bytes text.val)
            - countOcc tok_quot (bytes text.val)
            - countOcc tok_apos (bytes text.val)
            - countOcc tok_gt (bytes text.val)
            - countOcc tok_lt (bytes text.val)
            - countOcc tok_frasl (bytes text.val) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (text : Slice Std.U8)
    (h_len_lo : 1 ≤ text.val.length) (h_len_hi : text.val.length ≤ 100000), ∀ r : alloc.vec.Vec Std.U8,
      Aegis.EntityParser.entity_parser text = ok r →
        countByte 38 (bytes r.val)
          = countByte 38 (bytes text.val)
            - countOcc tok_quot (bytes text.val)
            - countOcc tok_apos (bytes text.val)
            - countOcc tok_gt (bytes text.val)
            - countOcc tok_lt (bytes text.val)
            - countOcc tok_frasl (bytes text.val)) := by
  sorry

/-- Let Nq, Na, Ng, Nl, Nf be the numbers of contiguous occurrences in text of `&quot;`, `&apos;`, `&gt;`, `&lt;`, and `&frasl;`, respectively. Let c34, c39, c62, c60, c47 count bytes equal to 34, 39, 62, 60, 47 in a byte sequence. Whenever the function returns r: c34(r) = c34(text) + Nq, c39(r) = c39(text) + Na, c62(r) = c62(text) + Ng, c60(r) = c60(text) + Nl, and c47(r) = c47(text) + Nf.
  Preconditions: 1 <= len(text) <= 100000. -/
theorem spec_7 (text : Slice Std.U8)
    (h_len_lo : 1 ≤ text.val.length) (h_len_hi : text.val.length ≤ 100000) :
    ∀ r : alloc.vec.Vec Std.U8,
      Aegis.EntityParser.entity_parser text = ok r →
        countByte 34 (bytes r.val) = countByte 34 (bytes text.val)
            + countOcc tok_quot (bytes text.val) ∧
          countByte 39 (bytes r.val) = countByte 39 (bytes text.val)
            + countOcc tok_apos (bytes text.val) ∧
          countByte 62 (bytes r.val) = countByte 62 (bytes text.val)
            + countOcc tok_gt (bytes text.val) ∧
          countByte 60 (bytes r.val) = countByte 60 (bytes text.val)
            + countOcc tok_lt (bytes text.val) ∧
          countByte 47 (bytes r.val) = countByte 47 (bytes text.val)
            + countOcc tok_frasl (bytes text.val) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (text : Slice Std.U8)
    (h_len_lo : 1 ≤ text.val.length) (h_len_hi : text.val.length ≤ 100000), ∀ r : alloc.vec.Vec Std.U8,
      Aegis.EntityParser.entity_parser text = ok r →
        countByte 34 (bytes r.val) = countByte 34 (bytes text.val)
            + countOcc tok_quot (bytes text.val) ∧
          countByte 39 (bytes r.val) = countByte 39 (bytes text.val)
            + countOcc tok_apos (bytes text.val) ∧
          countByte 62 (bytes r.val) = countByte 62 (bytes text.val)
            + countOcc tok_gt (bytes text.val) ∧
          countByte 60 (bytes r.val) = countByte 60 (bytes text.val)
            + countOcc tok_lt (bytes text.val) ∧
          countByte 47 (bytes r.val) = countByte 47 (bytes text.val)
            + countOcc tok_frasl (bytes text.val)) := by
  sorry

/-- Let Nq, Na, Nm, Ng, Nl, Nf be the numbers of contiguous occurrences in text of `&quot;`, `&apos;`, `&amp;`, `&gt;`, `&lt;`, and `&frasl;`, respectively, and let csemi(x) be the number of bytes equal to 59 in byte sequence x. Whenever the function returns r, csemi(r) = csemi(text) - (Nq + Na + Nm + Ng + Nl + Nf).
  Preconditions: 1 <= len(text) <= 100000. -/
theorem spec_8 (text : Slice Std.U8)
    (h_len_lo : 1 ≤ text.val.length) (h_len_hi : text.val.length ≤ 100000) :
    ∀ r : alloc.vec.Vec Std.U8,
      Aegis.EntityParser.entity_parser text = ok r →
        countByte 59 (bytes r.val)
          = countByte 59 (bytes text.val)
            - (countOcc tok_quot (bytes text.val)
              + countOcc tok_apos (bytes text.val)
              + countOcc tok_amp (bytes text.val)
              + countOcc tok_gt (bytes text.val)
              + countOcc tok_lt (bytes text.val)
              + countOcc tok_frasl (bytes text.val)) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (text : Slice Std.U8)
    (h_len_lo : 1 ≤ text.val.length) (h_len_hi : text.val.length ≤ 100000), ∀ r : alloc.vec.Vec Std.U8,
      Aegis.EntityParser.entity_parser text = ok r →
        countByte 59 (bytes r.val)
          = countByte 59 (bytes text.val)
            - (countOcc tok_quot (bytes text.val)
              + countOcc tok_apos (bytes text.val)
              + countOcc tok_amp (bytes text.val)
              + countOcc tok_gt (bytes text.val)
              + countOcc tok_lt (bytes text.val)
              + countOcc tok_frasl (bytes text.val))) := by
  sorry

end AegisSpec.EntityParser
