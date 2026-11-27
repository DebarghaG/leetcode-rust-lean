import Aegis.IsValid.Code.Funs

/-!
# Specifications of `Aegis.IsValid.is_valid`

LeetCode problem `tag-validator`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.IsValid

def isUpper (b : Aeneas.Std.U8) : Prop := 65 ≤ b.val ∧ b.val ≤ 90

def inAlphabet (b : Aeneas.Std.U8) : Prop :=
  (97 ≤ b.val ∧ b.val ≤ 122) ∨ (65 ≤ b.val ∧ b.val ≤ 90) ∨ (48 ≤ b.val ∧ b.val ≤ 57) ∨
    b.val = 60 ∨ b.val = 62 ∨ b.val = 47 ∨ b.val = 33 ∨ b.val = 91 ∨ b.val = 93 ∨
      b.val = 46 ∨ b.val = 32

def IsValidInput (code : Aeneas.Std.Slice Aeneas.Std.U8) : Prop :=
  1 ≤ code.val.length ∧ code.val.length ≤ 500 ∧ ∀ b, b ∈ code.val → inAlphabet b

def IsTagName (t : List Aeneas.Std.U8) : Prop :=
  1 ≤ t.length ∧ t.length ≤ 9 ∧ ∀ b, b ∈ t → isUpper b

def ltByte : Aeneas.Std.U8 := 60#u8

def gtByte : Aeneas.Std.U8 := 62#u8

def slashByte : Aeneas.Std.U8 := 47#u8

def cdataOpen : List Aeneas.Std.U8 :=
  [60#u8, 33#u8, 91#u8, 67#u8, 68#u8, 65#u8, 84#u8, 65#u8, 91#u8]

def cdataClose : List Aeneas.Std.U8 := [93#u8, 93#u8, 62#u8]

def Occurs (p l : List Aeneas.Std.U8) : Prop := ∃ pre post, l = pre ++ p ++ post

def NoCdataClose (l : List Aeneas.Std.U8) : Prop := ¬ Occurs cdataClose l

mutual

  inductive ValidContent : List Aeneas.Std.U8 → Prop where

    | nil : ValidContent []

    | cons {p rest : List Aeneas.Std.U8} :
        ValidPiece p → ValidContent rest → ValidContent (p ++ rest)

  inductive ValidPiece : List Aeneas.Std.U8 → Prop where

    | byte {b : Aeneas.Std.U8} : b.val ≠ 60 → ValidPiece [b]

    | tag {s : List Aeneas.Std.U8} : ValidClosedTag s → ValidPiece s

    | cdata {d : List Aeneas.Std.U8} :
        ¬ Occurs cdataClose d → ValidPiece (cdataOpen ++ d ++ cdataClose)

  inductive ValidClosedTag : List Aeneas.Std.U8 → Prop where
    | mk {t c : List Aeneas.Std.U8} (ht : IsTagName t) (hc : ValidContent c) :
        ValidClosedTag
          ([60#u8] ++ t ++ [62#u8] ++ c ++ [60#u8, 47#u8] ++ t ++ [62#u8])
end

/-- Let isUpper(b) mean 65 <= b <= 90. A byte sequence t is a tag name iff 1 <= len(t) <= 9 and for every i with 0 <= i < len(t), isUpper(t[i]). Define valid content and valid closed tag mutually recursively as follows. A byte sequence c is a valid content iff there exist an integer k >= 0 and byte sequences p_1, ..., p_k such that c = p_1 ++ ... ++ p_k (with k = 0 meaning c is empty) and for each i in 1..k, p_i satisfies exactly one of: (a) p_i is a single byte b with b != 60; (b) p_i is a valid closed tag; (c) p_i is of the form `<![CDATA[` ++ d ++ `]]>` where d is any byte sequence that does not contain the contiguous subsequence `]]>` (i.e., there is no j with 0 <= j <= len(d)-3 such that d[j]=93, d[j+1]=93, d[j+2]=62). A byte sequence s is a valid closed tag iff there exist a tag name t and a byte sequence c such that s = `<` ++ t ++ `>` ++ c ++ `</` ++ t ++ `>` and c is a valid content. (Here `<`, `>`, `/`, `!`, `[`, `]` denote the single bytes 60, 62, 47, 33, 91, 93, and the 9-byte string `<![CDATA[` is 60,33,91,67,68,65,84,65,91; the 3-byte string `]]>` is 93,93,62.) Then the function returns a result r and r = true if and only if code is a valid closed tag.
  Preconditions: code is a byte slice (slice of 8-bit unsigned integers) with 1 <= len(code) <= 500, and every byte of code is one of the following ASCII codes: 97-122 (a-z), 65-90 (A-Z), 48-57 (0-9), 60 ('<'), 62 ('>'), 47 ('/'), 33 ('!'), 91 ('['), 93 (']'), 46 ('.'), or 32 (' '). -/
theorem spec_1 (code : Aeneas.Std.Slice Aeneas.Std.U8) (hcode : IsValidInput code) :
    ∃ r, Aegis.IsValid.is_valid code = ok r ∧ (r = true ↔ ValidClosedTag code.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (code : Aeneas.Std.Slice Aeneas.Std.U8) (hcode : IsValidInput code), ∃ r, Aegis.IsValid.is_valid code = ok r ∧ (r = true ↔ ValidClosedTag code.val)) := by
  sorry

/-- The function returns a result r (i.e., it does not fail).
  Preconditions: code is a byte slice (slice of 8-bit unsigned integers) with 1 <= len(code) <= 500, and every byte of code is one of the following ASCII codes: 97-122 (a-z), 65-90 (A-Z), 48-57 (0-9), 60 ('<'), 62 ('>'), 47 ('/'), 33 ('!'), 91 ('['), 93 (']'), 46 ('.'), or 32 (' '). -/
theorem spec_2 (code : Aeneas.Std.Slice Aeneas.Std.U8) (hcode : IsValidInput code) :
    ∃ r, Aegis.IsValid.is_valid code = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (code : Aeneas.Std.Slice Aeneas.Std.U8) (hcode : IsValidInput code), ∃ r, Aegis.IsValid.is_valid code = ok r) := by
  sorry

/-- Whenever the function returns a result r with r = true, we have len(code) >= 7.
  Preconditions: code is a byte slice (slice of 8-bit unsigned integers) with 1 <= len(code) <= 500, and every byte of code is one of the following ASCII codes: 97-122 (a-z), 65-90 (A-Z), 48-57 (0-9), 60 ('<'), 62 ('>'), 47 ('/'), 33 ('!'), 91 ('['), 93 (']'), 46 ('.'), or 32 (' '). -/
theorem spec_3 (code : Aeneas.Std.Slice Aeneas.Std.U8) (hcode : IsValidInput code) :
    ∀ r, Aegis.IsValid.is_valid code = ok r → r = true → 7 ≤ code.val.length := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (code : Aeneas.Std.Slice Aeneas.Std.U8) (hcode : IsValidInput code), ∀ r, Aegis.IsValid.is_valid code = ok r → r = true → 7 ≤ code.val.length) := by
  sorry

/-- Whenever the function returns a result r with r = true, code[0] = 60 and code[len(code)-1] = 62.
  Preconditions: code is a byte slice (slice of 8-bit unsigned integers) with 1 <= len(code) <= 500, and every byte of code is one of the following ASCII codes: 97-122 (a-z), 65-90 (A-Z), 48-57 (0-9), 60 ('<'), 62 ('>'), 47 ('/'), 33 ('!'), 91 ('['), 93 (']'), 46 ('.'), or 32 (' '). -/
theorem spec_4 (code : Aeneas.Std.Slice Aeneas.Std.U8) (hcode : IsValidInput code) :
    ∀ r, Aegis.IsValid.is_valid code = ok r → r = true →
      code.val[0]? = some 60#u8 ∧ code.val.getLast? = some 62#u8 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (code : Aeneas.Std.Slice Aeneas.Std.U8) (hcode : IsValidInput code), ∀ r, Aegis.IsValid.is_valid code = ok r → r = true →
      code.val[0]? = some 60#u8 ∧ code.val.getLast? = some 62#u8) := by
  sorry

/-- If code[0] != 60, then whenever the function returns a result r, r = false.
  Preconditions: code is a byte slice (slice of 8-bit unsigned integers) with 1 <= len(code) <= 500, and every byte of code is one of the following ASCII codes: 97-122 (a-z), 65-90 (A-Z), 48-57 (0-9), 60 ('<'), 62 ('>'), 47 ('/'), 33 ('!'), 91 ('['), 93 (']'), 46 ('.'), or 32 (' '). -/
theorem spec_5 (code : Aeneas.Std.Slice Aeneas.Std.U8) (hcode : IsValidInput code)
    (hfirst : code.val[0]? ≠ some 60#u8) :
    ∀ r, Aegis.IsValid.is_valid code = ok r → r = false := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (code : Aeneas.Std.Slice Aeneas.Std.U8) (hcode : IsValidInput code)
    (hfirst : code.val[0]? ≠ some 60#u8), ∀ r, Aegis.IsValid.is_valid code = ok r → r = false) := by
  sorry

/-- If code[len(code)-1] != 62, then whenever the function returns a result r, r = false.
  Preconditions: code is a byte slice (slice of 8-bit unsigned integers) with 1 <= len(code) <= 500, and every byte of code is one of the following ASCII codes: 97-122 (a-z), 65-90 (A-Z), 48-57 (0-9), 60 ('<'), 62 ('>'), 47 ('/'), 33 ('!'), 91 ('['), 93 (']'), 46 ('.'), or 32 (' '). -/
theorem spec_6 (code : Aeneas.Std.Slice Aeneas.Std.U8) (hcode : IsValidInput code)
    (hlast : code.val.getLast? ≠ some 62#u8) :
    ∀ r, Aegis.IsValid.is_valid code = ok r → r = false := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (code : Aeneas.Std.Slice Aeneas.Std.U8) (hcode : IsValidInput code)
    (hlast : code.val.getLast? ≠ some 62#u8), ∀ r, Aegis.IsValid.is_valid code = ok r → r = false) := by
  sorry

/-- The function returns a result r and r = false.
  Preconditions: The parameter code is the specific 18-byte sequence for the ASCII string `<A><B></C></B></A>`. -/
theorem spec_7 (code : Aeneas.Std.Slice Aeneas.Std.U8)
    (hcode : code.val = [60#u8, 65#u8, 62#u8, 60#u8, 66#u8, 62#u8, 60#u8, 47#u8, 67#u8, 62#u8,
      60#u8, 47#u8, 66#u8, 62#u8, 60#u8, 47#u8, 65#u8, 62#u8]) :
    ∃ r, Aegis.IsValid.is_valid code = ok r ∧ r = false := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (code : Aeneas.Std.Slice Aeneas.Std.U8)
    (hcode : code.val = [60#u8, 65#u8, 62#u8, 60#u8, 66#u8, 62#u8, 60#u8, 47#u8, 67#u8, 62#u8,
      60#u8, 47#u8, 66#u8, 62#u8, 60#u8, 47#u8, 65#u8, 62#u8]), ∃ r, Aegis.IsValid.is_valid code = ok r ∧ r = false) := by
  sorry

/-- For every tag name t (i.e., every byte sequence t with 1 <= len(t) <= 9 and every byte in 65..90), the function returns a result r and r = true for code = `<` ++ t ++ `></` ++ t ++ `>` (i.e., byte 60, then t, then byte 62, then byte 60, then byte 47, then t, then byte 62).
  Preconditions: code is a byte slice (slice of 8-bit unsigned integers) with 1 <= len(code) <= 500, and every byte of code is one of the following ASCII codes: 97-122 (a-z), 65-90 (A-Z), 48-57 (0-9), 60 ('<'), 62 ('>'), 47 ('/'), 33 ('!'), 91 ('['), 93 (']'), 46 ('.'), or 32 (' '). -/
theorem spec_8 (t : List Aeneas.Std.U8) (code : Aeneas.Std.Slice Aeneas.Std.U8)
    (ht : IsTagName t) (hinput : IsValidInput code)
    (hcode : code.val = [60#u8] ++ t ++ [62#u8] ++ [60#u8, 47#u8] ++ t ++ [62#u8]) :
    ∃ r, Aegis.IsValid.is_valid code = ok r ∧ r = true := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (t : List Aeneas.Std.U8) (code : Aeneas.Std.Slice Aeneas.Std.U8)
    (ht : IsTagName t) (hinput : IsValidInput code)
    (hcode : code.val = [60#u8] ++ t ++ [62#u8] ++ [60#u8, 47#u8] ++ t ++ [62#u8]), ∃ r, Aegis.IsValid.is_valid code = ok r ∧ r = true) := by
  sorry

/-- Let t be any tag name (1 <= len(t) <= 9 and every byte of t is in 65..90). Let c be any byte sequence that is a valid closed tag as defined in spec_1 and consists only of bytes from the allowed alphabet, and assume 2*len(t) + 5 + len(c) <= 500. Then the function returns a result r and r = true for code = `<` ++ t ++ `>` ++ c ++ `</` ++ t ++ `>`.
  Preconditions: code is a byte slice (slice of 8-bit unsigned integers) with 1 <= len(code) <= 500, and every byte of code is one of the following ASCII codes: 97-122 (a-z), 65-90 (A-Z), 48-57 (0-9), 60 ('<'), 62 ('>'), 47 ('/'), 33 ('!'), 91 ('['), 93 (']'), 46 ('.'), or 32 (' '). -/
theorem spec_9 (t c : List Aeneas.Std.U8) (code : Aeneas.Std.Slice Aeneas.Std.U8)
    (ht : IsTagName t) (hc : ValidClosedTag c) (hcalpha : ∀ b, b ∈ c → inAlphabet b)
    (hlen : 2 * t.length + 5 + c.length ≤ 500) (hinput : IsValidInput code)
    (hcode : code.val = [60#u8] ++ t ++ [62#u8] ++ c ++ [60#u8, 47#u8] ++ t ++ [62#u8]) :
    ∃ r, Aegis.IsValid.is_valid code = ok r ∧ r = true := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (t c : List Aeneas.Std.U8) (code : Aeneas.Std.Slice Aeneas.Std.U8)
    (ht : IsTagName t) (hc : ValidClosedTag c) (hcalpha : ∀ b, b ∈ c → inAlphabet b)
    (hlen : 2 * t.length + 5 + c.length ≤ 500) (hinput : IsValidInput code)
    (hcode : code.val = [60#u8] ++ t ++ [62#u8] ++ c ++ [60#u8, 47#u8] ++ t ++ [62#u8]), ∃ r, Aegis.IsValid.is_valid code = ok r ∧ r = true) := by
  sorry

/-- Let t be any tag name (1 <= len(t) <= 9 and every byte of t is in 65..90). Let d be any byte sequence over the allowed alphabet that does not contain the contiguous three-byte subsequence `]]>` (93,93,62), and assume 2*len(t) + 17 + len(d) <= 500. Then the function returns a result r and r = true for code = `<` ++ t ++ `><![CDATA[` ++ d ++ `]]></` ++ t ++ `>`.
  Preconditions: code is a byte slice (slice of 8-bit unsigned integers) with 1 <= len(code) <= 500, and every byte of code is one of the following ASCII codes: 97-122 (a-z), 65-90 (A-Z), 48-57 (0-9), 60 ('<'), 62 ('>'), 47 ('/'), 33 ('!'), 91 ('['), 93 (']'), 46 ('.'), or 32 (' '). -/
theorem spec_10 (t d : List Aeneas.Std.U8) (code : Aeneas.Std.Slice Aeneas.Std.U8)
    (ht : IsTagName t) (hdalpha : ∀ b, b ∈ d → inAlphabet b) (hd : NoCdataClose d)
    (hlen : 2 * t.length + 17 + d.length ≤ 500) (hinput : IsValidInput code)
    (hcode : code.val =
      [60#u8] ++ t ++ [62#u8] ++ cdataOpen ++ d ++ cdataClose ++
        [60#u8, 47#u8] ++ t ++ [62#u8]) :
    ∃ r, Aegis.IsValid.is_valid code = ok r ∧ r = true := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (t d : List Aeneas.Std.U8) (code : Aeneas.Std.Slice Aeneas.Std.U8)
    (ht : IsTagName t) (hdalpha : ∀ b, b ∈ d → inAlphabet b) (hd : NoCdataClose d)
    (hlen : 2 * t.length + 17 + d.length ≤ 500) (hinput : IsValidInput code)
    (hcode : code.val =
      [60#u8] ++ t ++ [62#u8] ++ cdataOpen ++ d ++ cdataClose ++
        [60#u8, 47#u8] ++ t ++ [62#u8]), ∃ r, Aegis.IsValid.is_valid code = ok r ∧ r = true) := by
  sorry

/-- If there exists an index i with 0 <= i < len(code) such that code[i] = 60 and there is no index j with i < j < len(code) and code[j] = 62, then whenever the function returns a result r, r = false.
  Preconditions: code is a byte slice (slice of 8-bit unsigned integers) with 1 <= len(code) <= 500, and every byte of code is one of the following ASCII codes: 97-122 (a-z), 65-90 (A-Z), 48-57 (0-9), 60 ('<'), 62 ('>'), 47 ('/'), 33 ('!'), 91 ('['), 93 (']'), 46 ('.'), or 32 (' '). -/
theorem spec_11 (code : Aeneas.Std.Slice Aeneas.Std.U8) (hcode : IsValidInput code)
    (hunclosed : ∃ i, i < code.val.length ∧ code.val[i]? = some 60#u8 ∧
      ∀ j, i < j → j < code.val.length → code.val[j]? ≠ some 62#u8) :
    ∀ r, Aegis.IsValid.is_valid code = ok r → r = false := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (code : Aeneas.Std.Slice Aeneas.Std.U8) (hcode : IsValidInput code)
    (hunclosed : ∃ i, i < code.val.length ∧ code.val[i]? = some 60#u8 ∧
      ∀ j, i < j → j < code.val.length → code.val[j]? ≠ some 62#u8), ∀ r, Aegis.IsValid.is_valid code = ok r → r = false) := by
  sorry

/-- For every byte sequence t of length 10 consisting only of uppercase letters (65..90), the function returns a result r and r = false for code = `<` ++ t ++ `></` ++ t ++ `>`.
  Preconditions: code is a byte slice (slice of 8-bit unsigned integers) with 1 <= len(code) <= 500, and every byte of code is one of the following ASCII codes: 97-122 (a-z), 65-90 (A-Z), 48-57 (0-9), 60 ('<'), 62 ('>'), 47 ('/'), 33 ('!'), 91 ('['), 93 (']'), 46 ('.'), or 32 (' '). -/
theorem spec_12 (t : List Aeneas.Std.U8) (code : Aeneas.Std.Slice Aeneas.Std.U8)
    (ht : t.length = 10 ∧ ∀ b, b ∈ t → isUpper b) (hinput : IsValidInput code)
    (hcode : code.val = [60#u8] ++ t ++ [62#u8] ++ [60#u8, 47#u8] ++ t ++ [62#u8]) :
    ∃ r, Aegis.IsValid.is_valid code = ok r ∧ r = false := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (t : List Aeneas.Std.U8) (code : Aeneas.Std.Slice Aeneas.Std.U8)
    (ht : t.length = 10 ∧ ∀ b, b ∈ t → isUpper b) (hinput : IsValidInput code)
    (hcode : code.val = [60#u8] ++ t ++ [62#u8] ++ [60#u8, 47#u8] ++ t ++ [62#u8]), ∃ r, Aegis.IsValid.is_valid code = ok r ∧ r = false) := by
  sorry

/-- For every byte sequence t of length 1 consisting of the byte 97 ('a'), the function returns a result r and r = false for code = `<` ++ t ++ `></` ++ t ++ `>`.
  Preconditions: code is a byte slice (slice of 8-bit unsigned integers) with 1 <= len(code) <= 500, and every byte of code is one of the following ASCII codes: 97-122 (a-z), 65-90 (A-Z), 48-57 (0-9), 60 ('<'), 62 ('>'), 47 ('/'), 33 ('!'), 91 ('['), 93 (']'), 46 ('.'), or 32 (' '). -/
theorem spec_13 (t : List Aeneas.Std.U8) (code : Aeneas.Std.Slice Aeneas.Std.U8)
    (ht : t.length = 1 ∧ ∀ b, b ∈ t → b.val = 97) (hinput : IsValidInput code)
    (hcode : code.val = [60#u8] ++ t ++ [62#u8] ++ [60#u8, 47#u8] ++ t ++ [62#u8]) :
    ∃ r, Aegis.IsValid.is_valid code = ok r ∧ r = false := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (t : List Aeneas.Std.U8) (code : Aeneas.Std.Slice Aeneas.Std.U8)
    (ht : t.length = 1 ∧ ∀ b, b ∈ t → b.val = 97) (hinput : IsValidInput code)
    (hcode : code.val = [60#u8] ++ t ++ [62#u8] ++ [60#u8, 47#u8] ++ t ++ [62#u8]), ∃ r, Aegis.IsValid.is_valid code = ok r ∧ r = false) := by
  sorry

end AegisSpec.IsValid
