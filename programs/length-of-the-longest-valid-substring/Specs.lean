import Aegis.LongestValidSubstring.Code.Funs

/-!
# Specifications of `Aegis.LongestValidSubstring.longest_valid_substring`

LeetCode problem `length-of-the-longest-valid-substring`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.LongestValidSubstring

open Aegis.LongestValidSubstring

def IsLowerByte (b : Std.U8) : Prop := 97 ≤ b.val ∧ b.val ≤ 122

def patterns (forbidden : Slice (alloc.vec.Vec Std.U8)) : List (List Std.U8) :=
  forbidden.val.map (fun v => v.val)

def WordOk (w : List Std.U8) : Prop :=
  1 ≤ w.length ∧ w.length ≤ 100000 ∧ ∀ b ∈ w, IsLowerByte b

def PatternsOk (pats : List (List Std.U8)) : Prop :=
  ∀ pat ∈ pats, 1 ≤ pat.length ∧ pat.length ≤ 10 ∧ ∀ b ∈ pat, IsLowerByte b

def ForbiddenOk (forbidden : Slice (alloc.vec.Vec Std.U8)) : Prop :=
  1 ≤ forbidden.val.length ∧ forbidden.val.length ≤ 100000 ∧ PatternsOk (patterns forbidden)

def OccursIn (pat : List Std.U8) (w : List Std.U8) (a b : ℕ) : Prop :=
  ∃ p : ℕ, a ≤ p ∧ p + pat.length ≤ b ∧ ∀ k : ℕ, k < pat.length → w[p + k]? = pat[k]?

def ValidSubstring (w : List Std.U8) (pats : List (List Std.U8)) (a b : ℕ) : Prop :=
  ∀ pat ∈ pats, ¬ OccursIn pat w a b

def IsMaxValidLen (w : List Std.U8) (pats : List (List Std.U8)) (r : ℤ) : Prop :=
  (∃ a b : ℕ, a ≤ b ∧ b ≤ w.length ∧ ValidSubstring w pats a b ∧ ((b - a : ℕ) : ℤ) = r) ∧
    (∀ a b : ℕ, a ≤ b → b ≤ w.length → ValidSubstring w pats a b → ((b - a : ℕ) : ℤ) ≤ r)

def SingleLetterFree (w : List Std.U8) (pats : List (List Std.U8)) : Prop :=
  ∀ pat ∈ pats, pat.length = 1 → w[0]? ≠ pat[0]?

/-- The function returns a result r and r is the maximum of the set of all integers b-a such that 0 <= a <= b <= len(word) and word[a..b) is valid, where word[a..b) is valid iff there do not exist j,p with 0 <= j < len(forbidden), a <= p, p + len(forbidden[j]) <= b, and for every k with 0 <= k < len(forbidden[j]), word[p+k] = forbidden[j][k]. The empty substring a=b is included and is valid because every forbidden[j] has positive length.
  Preconditions: 1 <= len(word) <= 100000; every byte of word is an ASCII lowercase letter (97 <= word[i] <= 122 for 0 <= i < len(word)). 1 <= len(forbidden) <= 100000; for every j with 0 <= j < len(forbidden), 1 <= len(forbidden[j]) <= 10 and every byte of forbidden[j] is an ASCII lowercase letter (97 <= forbidden[j][k] <= 122 for 0 <= k < len(forbidden[j])). -/
theorem spec_1 (word : Slice Std.U8) (forbidden : Slice (alloc.vec.Vec Std.U8))
    (hw : WordOk word.val) (hf : ForbiddenOk forbidden) :
    ∃ r : Std.I64,
      longest_valid_substring word forbidden = ok r ∧
        IsMaxValidLen word.val (patterns forbidden) r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (word : Slice Std.U8) (forbidden : Slice (alloc.vec.Vec Std.U8))
    (hw : WordOk word.val) (hf : ForbiddenOk forbidden), ∃ r : Std.I64,
      longest_valid_substring word forbidden = ok r ∧
        IsMaxValidLen word.val (patterns forbidden) r.val) := by
  sorry

/-- For every word and forbidden satisfying the preconditions, the function returns a result r; it does not fail, panic, or overflow.
  Preconditions: 1 <= len(word) <= 100000; every byte of word is an ASCII lowercase letter. 1 <= len(forbidden) <= 100000; for every j with 0 <= j < len(forbidden), 1 <= len(forbidden[j]) <= 10 and every byte of forbidden[j] is an ASCII lowercase letter. -/
theorem spec_2 (word : Slice Std.U8) (forbidden : Slice (alloc.vec.Vec Std.U8))
    (hw : WordOk word.val) (hf : ForbiddenOk forbidden) :
    ∃ r : Std.I64, longest_valid_substring word forbidden = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (word : Slice Std.U8) (forbidden : Slice (alloc.vec.Vec Std.U8))
    (hw : WordOk word.val) (hf : ForbiddenOk forbidden), ∃ r : Std.I64, longest_valid_substring word forbidden = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r.
  Preconditions: 1 <= len(word) <= 100000; every byte of word is an ASCII lowercase letter. 1 <= len(forbidden) <= 100000; for every j with 0 <= j < len(forbidden), 1 <= len(forbidden[j]) <= 10 and every byte of forbidden[j] is an ASCII lowercase letter. -/
theorem spec_3 (word : Slice Std.U8) (forbidden : Slice (alloc.vec.Vec Std.U8))
    (hw : WordOk word.val) (hf : ForbiddenOk forbidden) :
    ∀ r : Std.I64, longest_valid_substring word forbidden = ok r → 0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (word : Slice Std.U8) (forbidden : Slice (alloc.vec.Vec Std.U8))
    (hw : WordOk word.val) (hf : ForbiddenOk forbidden), ∀ r : Std.I64, longest_valid_substring word forbidden = ok r → 0 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= len(word) as integers.
  Preconditions: 1 <= len(word) <= 100000; every byte of word is an ASCII lowercase letter. 1 <= len(forbidden) <= 100000; for every j with 0 <= j < len(forbidden), 1 <= len(forbidden[j]) <= 10 and every byte of forbidden[j] is an ASCII lowercase letter. -/
theorem spec_4 (word : Slice Std.U8) (forbidden : Slice (alloc.vec.Vec Std.U8))
    (hw : WordOk word.val) (hf : ForbiddenOk forbidden) :
    ∀ r : Std.I64,
      longest_valid_substring word forbidden = ok r → r.val ≤ ((word.val.length : ℕ) : ℤ) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (word : Slice Std.U8) (forbidden : Slice (alloc.vec.Vec Std.U8))
    (hw : WordOk word.val) (hf : ForbiddenOk forbidden), ∀ r : Std.I64,
      longest_valid_substring word forbidden = ok r → r.val ≤ ((word.val.length : ℕ) : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, there exist integers a,b with 0 <= a <= b <= len(word) and b-a = r such that word[a..b) is valid, meaning there do not exist j,p with 0 <= j < len(forbidden), a <= p, p + len(forbidden[j]) <= b, and for every k with 0 <= k < len(forbidden[j]), word[p+k] = forbidden[j][k].
  Preconditions: 1 <= len(word) <= 100000; every byte of word is an ASCII lowercase letter. 1 <= len(forbidden) <= 100000; for every j with 0 <= j < len(forbidden), 1 <= len(forbidden[j]) <= 10 and every byte of forbidden[j] is an ASCII lowercase letter. -/
theorem spec_5 (word : Slice Std.U8) (forbidden : Slice (alloc.vec.Vec Std.U8))
    (hw : WordOk word.val) (hf : ForbiddenOk forbidden) :
    ∀ r : Std.I64,
      longest_valid_substring word forbidden = ok r →
        ∃ a b : ℕ,
          a ≤ b ∧ b ≤ word.val.length ∧ ((b - a : ℕ) : ℤ) = r.val ∧
            ValidSubstring word.val (patterns forbidden) a b := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (word : Slice Std.U8) (forbidden : Slice (alloc.vec.Vec Std.U8))
    (hw : WordOk word.val) (hf : ForbiddenOk forbidden), ∀ r : Std.I64,
      longest_valid_substring word forbidden = ok r →
        ∃ a b : ℕ,
          a ≤ b ∧ b ≤ word.val.length ∧ ((b - a : ℕ) : ℤ) = r.val ∧
            ValidSubstring word.val (patterns forbidden) a b) := by
  sorry

/-- Whenever the function returns a result r, for every a,b with 0 <= a <= b <= len(word), if word[a..b) is valid (there do not exist j,p with 0 <= j < len(forbidden), a <= p, p + len(forbidden[j]) <= b, and for every k with 0 <= k < len(forbidden[j]), word[p+k] = forbidden[j][k]), then b-a <= r.
  Preconditions: 1 <= len(word) <= 100000; every byte of word is an ASCII lowercase letter. 1 <= len(forbidden) <= 100000; for every j with 0 <= j < len(forbidden), 1 <= len(forbidden[j]) <= 10 and every byte of forbidden[j] is an ASCII lowercase letter. -/
theorem spec_6 (word : Slice Std.U8) (forbidden : Slice (alloc.vec.Vec Std.U8))
    (hw : WordOk word.val) (hf : ForbiddenOk forbidden) :
    ∀ r : Std.I64,
      longest_valid_substring word forbidden = ok r →
        ∀ a b : ℕ,
          a ≤ b → b ≤ word.val.length → ValidSubstring word.val (patterns forbidden) a b →
            ((b - a : ℕ) : ℤ) ≤ r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (word : Slice Std.U8) (forbidden : Slice (alloc.vec.Vec Std.U8))
    (hw : WordOk word.val) (hf : ForbiddenOk forbidden), ∀ r : Std.I64,
      longest_valid_substring word forbidden = ok r →
        ∀ a b : ℕ,
          a ≤ b → b ≤ word.val.length → ValidSubstring word.val (patterns forbidden) a b →
            ((b - a : ℕ) : ℤ) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r = len(word) if and only if the whole word word[0..len(word)) is valid, meaning there do not exist j,p with 0 <= j < len(forbidden), 0 <= p, p + len(forbidden[j]) <= len(word), and for every k with 0 <= k < len(forbidden[j]), word[p+k] = forbidden[j][k].
  Preconditions: 1 <= len(word) <= 100000; every byte of word is an ASCII lowercase letter. 1 <= len(forbidden) <= 100000; for every j with 0 <= j < len(forbidden), 1 <= len(forbidden[j]) <= 10 and every byte of forbidden[j] is an ASCII lowercase letter. -/
theorem spec_7 (word : Slice Std.U8) (forbidden : Slice (alloc.vec.Vec Std.U8))
    (hw : WordOk word.val) (hf : ForbiddenOk forbidden) :
    ∀ r : Std.I64,
      longest_valid_substring word forbidden = ok r →
        (r.val = ((word.val.length : ℕ) : ℤ) ↔
          ValidSubstring word.val (patterns forbidden) 0 word.val.length) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (word : Slice Std.U8) (forbidden : Slice (alloc.vec.Vec Std.U8))
    (hw : WordOk word.val) (hf : ForbiddenOk forbidden), ∀ r : Std.I64,
      longest_valid_substring word forbidden = ok r →
        (r.val = ((word.val.length : ℕ) : ℤ) ↔
          ValidSubstring word.val (patterns forbidden) 0 word.val.length)) := by
  sorry

/-- Whenever the function returns a result r under these preconditions, r = len(word).
  Preconditions: 1 <= len(word) <= 100000; every byte of word is an ASCII lowercase letter. 1 <= len(forbidden) <= 100000; for every j with 0 <= j < len(forbidden), 1 <= len(forbidden[j]) <= 10 and every byte of forbidden[j] is an ASCII lowercase letter. Additionally, no forbidden[j] occurs anywhere in word: for every j with 0 <= j < len(forbidden) and every p with 0 <= p and p + len(forbidden[j]) <= len(word), there exists k with 0 <= k < len(forbidden[j]) and word[p+k] != forbidden[j][k]. -/
theorem spec_8 (word : Slice Std.U8) (forbidden : Slice (alloc.vec.Vec Std.U8))
    (hw : WordOk word.val) (hf : ForbiddenOk forbidden)
    (hnone : ∀ pat ∈ patterns forbidden, ¬ OccursIn pat word.val 0 word.val.length) :
    ∀ r : Std.I64,
      longest_valid_substring word forbidden = ok r → r.val = ((word.val.length : ℕ) : ℤ) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (word : Slice Std.U8) (forbidden : Slice (alloc.vec.Vec Std.U8))
    (hw : WordOk word.val) (hf : ForbiddenOk forbidden)
    (hnone : ∀ pat ∈ patterns forbidden, ¬ OccursIn pat word.val 0 word.val.length), ∀ r : Std.I64,
      longest_valid_substring word forbidden = ok r → r.val = ((word.val.length : ℕ) : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if every nonempty substring word[a..b) with 0 <= a < b <= len(word) is invalid, meaning for every such a,b there exist j,p with 0 <= j < len(forbidden), a <= p, p + len(forbidden[j]) <= b, and for every k with 0 <= k < len(forbidden[j]), word[p+k] = forbidden[j][k].
  Preconditions: 1 <= len(word) <= 100000; every byte of word is an ASCII lowercase letter. 1 <= len(forbidden) <= 100000; for every j with 0 <= j < len(forbidden), 1 <= len(forbidden[j]) <= 10 and every byte of forbidden[j] is an ASCII lowercase letter. -/
theorem spec_9 (word : Slice Std.U8) (forbidden : Slice (alloc.vec.Vec Std.U8))
    (hw : WordOk word.val) (hf : ForbiddenOk forbidden) :
    ∀ r : Std.I64,
      longest_valid_substring word forbidden = ok r →
        (r.val = 0 ↔
          ∀ a b : ℕ,
            a < b → b ≤ word.val.length → ¬ ValidSubstring word.val (patterns forbidden) a b) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (word : Slice Std.U8) (forbidden : Slice (alloc.vec.Vec Std.U8))
    (hw : WordOk word.val) (hf : ForbiddenOk forbidden), ∀ r : Std.I64,
      longest_valid_substring word forbidden = ok r →
        (r.val = 0 ↔
          ∀ a b : ℕ,
            a < b → b ≤ word.val.length → ¬ ValidSubstring word.val (patterns forbidden) a b)) := by
  sorry

/-- Whenever the function returns a result r, r = 1 if for every j with 0 <= j < len(forbidden) and len(forbidden[j]) = 1 we have word[0] != forbidden[j][0]; otherwise r = 0.
  Preconditions: 1 <= len(word) <= 100000; every byte of word is an ASCII lowercase letter. 1 <= len(forbidden) <= 100000; for every j with 0 <= j < len(forbidden), 1 <= len(forbidden[j]) <= 10 and every byte of forbidden[j] is an ASCII lowercase letter. Additionally len(word) = 1. -/
theorem spec_10 (word : Slice Std.U8) (forbidden : Slice (alloc.vec.Vec Std.U8))
    (hw : WordOk word.val) (hf : ForbiddenOk forbidden) (hword : word.val.length = 1) :
    ∀ r : Std.I64,
      longest_valid_substring word forbidden = ok r →
        ((SingleLetterFree word.val (patterns forbidden) → r.val = 1) ∧
          (¬ SingleLetterFree word.val (patterns forbidden) → r.val = 0)) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (word : Slice Std.U8) (forbidden : Slice (alloc.vec.Vec Std.U8))
    (hw : WordOk word.val) (hf : ForbiddenOk forbidden) (hword : word.val.length = 1), ∀ r : Std.I64,
      longest_valid_substring word forbidden = ok r →
        ((SingleLetterFree word.val (patterns forbidden) → r.val = 1) ∧
          (¬ SingleLetterFree word.val (patterns forbidden) → r.val = 0))) := by
  sorry

/-- If longest_valid_substring(word, forbidden) returns r and longest_valid_substring(word, forbidden') returns r', then r = r'.
  Preconditions: 1 <= len(word) <= 100000; every byte of word is an ASCII lowercase letter. 1 <= len(forbidden) <= 100000; for every j with 0 <= j < len(forbidden), 1 <= len(forbidden[j]) <= 10 and every byte of forbidden[j] is an ASCII lowercase letter. Let forbidden' be any slice of Vec U8 with len(forbidden') = len(forbidden) for which there exists a bijection pi from {0,...,len(forbidden)-1} to itself such that forbidden'[i] = forbidden[pi(i)] for every i. -/
theorem spec_11 (word : Slice Std.U8) (forbidden forbidden' : Slice (alloc.vec.Vec Std.U8))
    (hw : WordOk word.val) (hf : ForbiddenOk forbidden) (hf' : ForbiddenOk forbidden')
    (hperm : (patterns forbidden).Perm (patterns forbidden')) :
    ∀ r r' : Std.I64,
      longest_valid_substring word forbidden = ok r →
        longest_valid_substring word forbidden' = ok r' → r.val = r'.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (word : Slice Std.U8) (forbidden forbidden' : Slice (alloc.vec.Vec Std.U8))
    (hw : WordOk word.val) (hf : ForbiddenOk forbidden) (hf' : ForbiddenOk forbidden')
    (hperm : (patterns forbidden).Perm (patterns forbidden')), ∀ r r' : Std.I64,
      longest_valid_substring word forbidden = ok r →
        longest_valid_substring word forbidden' = ok r' → r.val = r'.val) := by
  sorry

/-- If longest_valid_substring(word, forbidden) returns r and longest_valid_substring(word, forbidden') returns r', then r' <= r.
  Preconditions: 1 <= len(word) <= 100000; every byte of word is an ASCII lowercase letter. 1 <= len(forbidden) <= 100000; for every j with 0 <= j < len(forbidden), 1 <= len(forbidden[j]) <= 10 and every byte of forbidden[j] is an ASCII lowercase letter. Let forbidden' be another slice of Vec U8 satisfying the same constraints such that for every j with 0 <= j < len(forbidden) there exists j' with 0 <= j' < len(forbidden') and forbidden'[j'] = forbidden[j]. -/
theorem spec_12 (word : Slice Std.U8) (forbidden forbidden' : Slice (alloc.vec.Vec Std.U8))
    (hw : WordOk word.val) (hf : ForbiddenOk forbidden) (hf' : ForbiddenOk forbidden')
    (hsub : ∀ pat ∈ patterns forbidden, pat ∈ patterns forbidden') :
    ∀ r r' : Std.I64,
      longest_valid_substring word forbidden = ok r →
        longest_valid_substring word forbidden' = ok r' → r'.val ≤ r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (word : Slice Std.U8) (forbidden forbidden' : Slice (alloc.vec.Vec Std.U8))
    (hw : WordOk word.val) (hf : ForbiddenOk forbidden) (hf' : ForbiddenOk forbidden')
    (hsub : ∀ pat ∈ patterns forbidden, pat ∈ patterns forbidden'), ∀ r r' : Std.I64,
      longest_valid_substring word forbidden = ok r →
        longest_valid_substring word forbidden' = ok r' → r'.val ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, if r > 0 then there exists an index a with 0 <= a < len(word) such that the one-character substring word[a..a+1) is valid, meaning there do not exist j,p with 0 <= j < len(forbidden), a <= p, p + len(forbidden[j]) <= a+1, and for every k with 0 <= k < len(forbidden[j]), word[p+k] = forbidden[j][k].
  Preconditions: 1 <= len(word) <= 100000; every byte of word is an ASCII lowercase letter. 1 <= len(forbidden) <= 100000; for every j with 0 <= j < len(forbidden), 1 <= len(forbidden[j]) <= 10 and every byte of forbidden[j] is an ASCII lowercase letter. -/
theorem spec_13 (word : Slice Std.U8) (forbidden : Slice (alloc.vec.Vec Std.U8))
    (hw : WordOk word.val) (hf : ForbiddenOk forbidden) :
    ∀ r : Std.I64,
      longest_valid_substring word forbidden = ok r → 0 < r.val →
        ∃ a : ℕ, a < word.val.length ∧ ValidSubstring word.val (patterns forbidden) a (a + 1) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (word : Slice Std.U8) (forbidden : Slice (alloc.vec.Vec Std.U8))
    (hw : WordOk word.val) (hf : ForbiddenOk forbidden), ∀ r : Std.I64,
      longest_valid_substring word forbidden = ok r → 0 < r.val →
        ∃ a : ℕ, a < word.val.length ∧ ValidSubstring word.val (patterns forbidden) a (a + 1)) := by
  sorry

end AegisSpec.LongestValidSubstring
