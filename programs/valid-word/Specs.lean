import Aegis.IsValid.Code.Funs

/-!
# Specifications of `Aegis.IsValid.is_valid`

LeetCode problem `valid-word`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.IsValid

namespace AegisSpec.IsValid

def codes (word : Slice Std.U8) : List ℕ := word.val.map (fun c => c.val)

def forallBytes (word : Slice Std.U8) (p : ℕ → Prop) : Prop :=
  ∀ (i : ℕ) (hi : i < word.val.length), p (word.val[i]'hi).val

def existsByte (word : Slice Std.U8) (p : ℕ → Prop) : Prop :=
  ∃ (i : ℕ) (hi : i < word.val.length), p (word.val[i]'hi).val

theorem forallBytes_iff {word : Slice Std.U8} {p : ℕ → Prop} :
    forallBytes word p ↔ ∀ b ∈ codes word, p b := by
  unfold forallBytes codes
  simp only [List.mem_map]
  constructor
  · rintro h b ⟨a, ha, rfl⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
    exact h i hi
  · intro h i hi
    exact h _ ⟨_, List.getElem_mem hi, rfl⟩

theorem existsByte_iff {word : Slice Std.U8} {p : ℕ → Prop} :
    existsByte word p ↔ ∃ b ∈ codes word, p b := by
  unfold existsByte codes
  simp only [List.mem_map]
  constructor
  · rintro ⟨i, hi, hp⟩
    exact ⟨_, ⟨_, List.getElem_mem hi, rfl⟩, hp⟩
  · rintro ⟨b, ⟨a, ha, rfl⟩, hp⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
    exact ⟨i, hi, hp⟩

def byteCount (word : Slice Std.U8) (b : ℕ) : ℕ := (codes word).count b

def isUpper (b : ℕ) : Prop := 65 ≤ b ∧ b ≤ 90

def isLower (b : ℕ) : Prop := 97 ≤ b ∧ b ≤ 122

def isLetter (b : ℕ) : Prop := isUpper b ∨ isLower b

def isDigit (b : ℕ) : Prop := 48 ≤ b ∧ b ≤ 57

def isVowel (b : ℕ) : Prop :=
  b = 97 ∨ b = 101 ∨ b = 105 ∨ b = 111 ∨ b = 117 ∨
    b = 65 ∨ b = 69 ∨ b = 73 ∨ b = 79 ∨ b = 85

def isConsonant (b : ℕ) : Prop := isLetter b ∧ ¬ isVowel b

def isAllowed (b : ℕ) : Prop := isLetter b ∨ isDigit b ∨ b = 64 ∨ b = 35 ∨ b = 36

def isLetterOrDigit (b : ℕ) : Prop := isLetter b ∨ isDigit b

def swapCase (b : ℕ) : ℕ :=
  if 65 ≤ b ∧ b ≤ 90 then b + 32 else if 97 ≤ b ∧ b ≤ 122 then b - 32 else b

def caseSwapRel (l₁ l₂ : List ℕ) : Prop :=
  List.Forall₂ (fun a b => b = a ∨ (isLetter a ∧ b = swapCase a)) l₁ l₂

/-- The function returns a result r and r = true if and only if all four conditions hold: (a) len(word) >= 3; (b) for every i with 0 <= i < len(word), word[i] is the ASCII code of an ASCII digit '0' through '9' or an English letter 'A' through 'Z' or 'a' through 'z'; (c) there exists i with 0 <= i < len(word) such that word[i] is the ASCII code of one of 'a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'; (d) there exists i with 0 <= i < len(word) such that word[i] is the ASCII code of an English letter (one of 'A' through 'Z' or 'a' through 'z') that is not one of 'a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'. If these four conditions do not all hold, then r = false.
  Preconditions: 1 <= len(word) <= 20 and for every i with 0 <= i < len(word), word[i] is the ASCII code of an English uppercase or lowercase letter, an ASCII digit '0' through '9', '@', '#', or '$'. -/
theorem spec_1 {word : Slice Std.U8}
    (hlen_lo : 1 ≤ word.val.length) (hlen_hi : word.val.length ≤ 20)
    (hbytes : forallBytes word isAllowed) :
    ∃ r : Bool,
      is_valid word = ok r ∧
      (r = true ↔
        (3 ≤ word.val.length ∧
          forallBytes word isLetterOrDigit ∧
          existsByte word isVowel ∧
          existsByte word isConsonant)) ∧
      (¬ (3 ≤ word.val.length ∧
            forallBytes word isLetterOrDigit ∧
            existsByte word isVowel ∧
            existsByte word isConsonant) → r = false) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ {word : Slice Std.U8}
    (hlen_lo : 1 ≤ word.val.length) (hlen_hi : word.val.length ≤ 20)
    (hbytes : forallBytes word isAllowed), ∃ r : Bool,
      is_valid word = ok r ∧
      (r = true ↔
        (3 ≤ word.val.length ∧
          forallBytes word isLetterOrDigit ∧
          existsByte word isVowel ∧
          existsByte word isConsonant)) ∧
      (¬ (3 ≤ word.val.length ∧
            forallBytes word isLetterOrDigit ∧
            existsByte word isVowel ∧
            existsByte word isConsonant) → r = false)) := by
  sorry

/-- For every word satisfying the precondition, the function returns a result r and does not fail, overflow, or panic.
  Preconditions: 1 <= len(word) <= 20 and for every i with 0 <= i < len(word), word[i] is the ASCII code of an English uppercase or lowercase letter, an ASCII digit '0' through '9', '@', '#', or '$'. -/
theorem spec_2 {word : Slice Std.U8}
    (hlen_lo : 1 ≤ word.val.length) (hlen_hi : word.val.length ≤ 20)
    (hbytes : forallBytes word isAllowed) :
    ∃ r : Bool, is_valid word = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ {word : Slice Std.U8}
    (hlen_lo : 1 ≤ word.val.length) (hlen_hi : word.val.length ≤ 20)
    (hbytes : forallBytes word isAllowed), ∃ r : Bool, is_valid word = ok r) := by
  sorry

/-- If for every byte value b, the number of indices i with 0 <= i < len(word) and word[i] = b equals the number of indices j with 0 <= j < len(other) and other[j] = b, then whenever the function returns result r on word and result s on other, r = s.
  Preconditions: word and other are byte slices, each satisfying 1 <= len <= 20 and every byte being the ASCII code of an English uppercase or lowercase letter, an ASCII digit '0' through '9', '@', '#', or '$'. -/
theorem spec_3 {word other : Slice Std.U8}
    (hlen_lo : 1 ≤ word.val.length) (hlen_hi : word.val.length ≤ 20)
    (hbytes : forallBytes word isAllowed)
    (hlen_lo' : 1 ≤ other.val.length) (hlen_hi' : other.val.length ≤ 20)
    (hbytes' : forallBytes other isAllowed)
    (hcount : ∀ b : ℕ, byteCount word b = byteCount other b)
    {r s : Bool} (hr : is_valid word = ok r) (hs : is_valid other = ok s) :
    r = s := by
  sorry

theorem spec_3_neg :
    ¬ (∀ {word other : Slice Std.U8}
    (hlen_lo : 1 ≤ word.val.length) (hlen_hi : word.val.length ≤ 20)
    (hbytes : forallBytes word isAllowed)
    (hlen_lo' : 1 ≤ other.val.length) (hlen_hi' : other.val.length ≤ 20)
    (hbytes' : forallBytes other isAllowed)
    (hcount : ∀ b : ℕ, byteCount word b = byteCount other b)
    {r s : Bool} (hr : is_valid word = ok r) (hs : is_valid other = ok s), r = s) := by
  sorry

/-- If len(word) = len(other) and for every i with 0 <= i < len(word), other[i] is obtained from word[i] by either leaving it unchanged or, when word[i] is the ASCII code of an English letter, replacing it by the ASCII code of the opposite-case version of that letter, then whenever the function returns result r on word and result s on other, r = s.
  Preconditions: word and other are byte slices, each satisfying 1 <= len <= 20 and every byte being the ASCII code of an English uppercase or lowercase letter, an ASCII digit '0' through '9', '@', '#', or '$'. -/
theorem spec_4 {word other : Slice Std.U8}
    (hlen_lo : 1 ≤ word.val.length) (hlen_hi : word.val.length ≤ 20)
    (hbytes : forallBytes word isAllowed)
    (hlen_lo' : 1 ≤ other.val.length) (hlen_hi' : other.val.length ≤ 20)
    (hbytes' : forallBytes other isAllowed)
    (hlen : word.val.length = other.val.length)
    (hrel : caseSwapRel (codes word) (codes other))
    {r s : Bool} (hr : is_valid word = ok r) (hs : is_valid other = ok s) :
    r = s := by
  sorry

theorem spec_4_neg :
    ¬ (∀ {word other : Slice Std.U8}
    (hlen_lo : 1 ≤ word.val.length) (hlen_hi : word.val.length ≤ 20)
    (hbytes : forallBytes word isAllowed)
    (hlen_lo' : 1 ≤ other.val.length) (hlen_hi' : other.val.length ≤ 20)
    (hbytes' : forallBytes other isAllowed)
    (hlen : word.val.length = other.val.length)
    (hrel : caseSwapRel (codes word) (codes other))
    {r s : Bool} (hr : is_valid word = ok r) (hs : is_valid other = ok s), r = s) := by
  sorry

/-- For every byte d that is the ASCII code of a digit '0' through '9', let word2 be the slice of length len(word)+1 whose first len(word) bytes equal word and whose last byte is d. Whenever the function returns true on word, the function returns true on word2.
  Preconditions: 1 <= len(word) <= 19 and for every i with 0 <= i < len(word), word[i] is the ASCII code of an English uppercase or lowercase letter, an ASCII digit '0' through '9', '@', '#', or '$'. -/
theorem spec_5 {word word2 : Slice Std.U8} {d : ℕ}
    (hlen_lo : 1 ≤ word.val.length) (hlen_hi : word.val.length ≤ 19)
    (hbytes : forallBytes word isAllowed)
    (hd : isDigit d)
    (hword2 : codes word2 = codes word ++ [d])
    (hr : is_valid word = ok true) :
    is_valid word2 = ok true := by
  sorry

theorem spec_5_neg :
    ¬ (∀ {word word2 : Slice Std.U8} {d : ℕ}
    (hlen_lo : 1 ≤ word.val.length) (hlen_hi : word.val.length ≤ 19)
    (hbytes : forallBytes word isAllowed)
    (hd : isDigit d)
    (hword2 : codes word2 = codes word ++ [d])
    (hr : is_valid word = ok true), is_valid word2 = ok true) := by
  sorry

end AegisSpec.IsValid
