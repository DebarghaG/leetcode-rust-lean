import Aegis.FindWordsContaining.Code.Funs

/-!
# Specifications of `Aegis.FindWordsContaining.find_words_containing`

LeetCode problem `find-words-containing-character`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.FindWordsContaining (find_words_containing)

namespace AegisSpec.FindWordsContaining

def targetByte (x : Slice Std.U8) : Std.U8 := x.val.getD 0 0#u8

def occurs (b : Std.U8) (w : List Std.U8) : Prop := b ∈ w

instance instDecidableOccurs (b : Std.U8) (w : List Std.U8) : Decidable (occurs b w) :=
  decidable_of_iff (b ∈ w) Iff.rfl

def wordBytes (words : Slice (alloc.vec.Vec Std.U8)) : List (List Std.U8) :=
  words.val.map fun w => w.val

def wordAt (words : Slice (alloc.vec.Vec Std.U8)) (v : ℤ) : List Std.U8 :=
  (wordBytes words).getD v.toNat []

def countVal (l : List Std.I64) (v : ℤ) : ℕ := l.countP fun e => decide (e.val = v)

def numContaining (words : Slice (alloc.vec.Vec Std.U8)) (b : Std.U8) : ℕ :=
  (wordBytes words).countP fun w => decide (occurs b w)

def resultContains (l : List Std.I64) (i : ℕ) : Prop := (i : ℤ) ∈ l.map fun e => e.val

theorem occurs_iff (b : Std.U8) (w : List Std.U8) :
    occurs b w ↔ ∃ k : ℕ, k < w.length ∧ w[k]? = some b := by
  rw [occurs, List.mem_iff_getElem?]
  exact ⟨fun ⟨i, hi⟩ => let ⟨h, _⟩ := List.getElem?_eq_some_iff.mp hi; ⟨i, h, hi⟩,
    fun ⟨k, _, hk⟩ => ⟨k, hk⟩⟩

theorem wordAt_eq (words : Slice (alloc.vec.Vec Std.U8)) (i : ℕ)
    (h : i < words.val.length) :
    wordAt words (i : ℤ) = (words.val[i]'h).val := by
  rw [wordAt, wordBytes, Int.toNat_natCast, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_some_iff.mpr ⟨h, rfl⟩]
  simp

theorem targetByte_eq (x : Slice Std.U8) (h : 0 < x.val.length) :
    targetByte x = x.val[0]'h := by
  rw [targetByte, List.getD_eq_getElem?_getD, List.getElem?_eq_some_iff.mpr ⟨h, rfl⟩]
  simp

/-- The function returns a result r and does not fail. For every integer value v, the number of positions j with 0 <= j < len(r) and r[j] = v is exactly 1 if 0 <= v < len(words) and there exists k with 0 <= k < len(words[v]) such that words[v][k] = x[0], and is exactly 0 otherwise.
  Preconditions: words has length between 1 and 50 inclusive; for every i with 0 <= i < len(words), len(words[i]) is between 1 and 50 inclusive, and every byte words[i][k] with 0 <= k < len(words[i]) is an ASCII lowercase English letter (97..122); x has length exactly 1, and x[0] is an ASCII lowercase English letter (97..122). -/
theorem spec_1 (words : Slice (alloc.vec.Vec Std.U8)) (x : Slice Std.U8)
    (hw_len : 1 ≤ words.val.length ∧ words.val.length ≤ 50)
    (hw_elems : ∀ w ∈ words.val, 1 ≤ w.val.length ∧ w.val.length ≤ 50)
    (hw_bytes : ∀ w ∈ words.val, ∀ b ∈ w.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (hx_len : x.val.length = 1)
    (hx_byte : 97 ≤ (targetByte x).val ∧ (targetByte x).val ≤ 122) :
    ∃ r : alloc.vec.Vec Std.I64,
      find_words_containing words x = ok r ∧
        ∀ v : ℤ,
          countVal r.val v =
            (if 0 ≤ v ∧ v < (words.val.length : ℤ) ∧
                occurs (targetByte x) (wordAt words v) then 1 else 0) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (x : Slice Std.U8)
    (hw_len : 1 ≤ words.val.length ∧ words.val.length ≤ 50)
    (hw_elems : ∀ w ∈ words.val, 1 ≤ w.val.length ∧ w.val.length ≤ 50)
    (hw_bytes : ∀ w ∈ words.val, ∀ b ∈ w.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (hx_len : x.val.length = 1)
    (hx_byte : 97 ≤ (targetByte x).val ∧ (targetByte x).val ≤ 122), ∃ r : alloc.vec.Vec Std.I64,
      find_words_containing words x = ok r ∧
        ∀ v : ℤ,
          countVal r.val v =
            (if 0 ≤ v ∧ v < (words.val.length : ℤ) ∧
                occurs (targetByte x) (wordAt words v) then 1 else 0)) := by
  sorry

/-- For every input satisfying the preconditions, find_words_containing returns a result r; it does not return a failure, panic, out-of-bounds access, or arithmetic overflow.
  Preconditions: words has length between 1 and 50 inclusive; for every i with 0 <= i < len(words), len(words[i]) is between 1 and 50 inclusive, and every byte words[i][k] with 0 <= k < len(words[i]) is an ASCII lowercase English letter (97..122); x has length exactly 1, and x[0] is an ASCII lowercase English letter (97..122). -/
theorem spec_2 (words : Slice (alloc.vec.Vec Std.U8)) (x : Slice Std.U8)
    (hw_len : 1 ≤ words.val.length ∧ words.val.length ≤ 50)
    (hw_elems : ∀ w ∈ words.val, 1 ≤ w.val.length ∧ w.val.length ≤ 50)
    (hw_bytes : ∀ w ∈ words.val, ∀ b ∈ w.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (hx_len : x.val.length = 1)
    (hx_byte : 97 ≤ (targetByte x).val ∧ (targetByte x).val ≤ 122) :
    ∃ r : alloc.vec.Vec Std.I64, find_words_containing words x = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (x : Slice Std.U8)
    (hw_len : 1 ≤ words.val.length ∧ words.val.length ≤ 50)
    (hw_elems : ∀ w ∈ words.val, 1 ≤ w.val.length ∧ w.val.length ≤ 50)
    (hw_bytes : ∀ w ∈ words.val, ∀ b ∈ w.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (hx_len : x.val.length = 1)
    (hx_byte : 97 ≤ (targetByte x).val ∧ (targetByte x).val ≤ 122), ∃ r : alloc.vec.Vec Std.I64, find_words_containing words x = ok r) := by
  sorry

/-- Whenever the function returns a result r, for every j with 0 <= j < len(r), the integer r[j] satisfies 0 <= r[j] < len(words).
  Preconditions: words has length between 1 and 50 inclusive; for every i with 0 <= i < len(words), len(words[i]) is between 1 and 50 inclusive, and every byte words[i][k] with 0 <= k < len(words[i]) is an ASCII lowercase English letter (97..122); x has length exactly 1, and x[0] is an ASCII lowercase English letter (97..122). -/
theorem spec_3 (words : Slice (alloc.vec.Vec Std.U8)) (x : Slice Std.U8)
    (hw_len : 1 ≤ words.val.length ∧ words.val.length ≤ 50)
    (hw_elems : ∀ w ∈ words.val, 1 ≤ w.val.length ∧ w.val.length ≤ 50)
    (hw_bytes : ∀ w ∈ words.val, ∀ b ∈ w.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (hx_len : x.val.length = 1)
    (hx_byte : 97 ≤ (targetByte x).val ∧ (targetByte x).val ≤ 122) :
    ∀ (r : alloc.vec.Vec Std.I64), find_words_containing words x = ok r →
      ∀ (j : ℕ) (hj : j < r.val.length),
        0 ≤ (r.val[j]'hj).val ∧ (r.val[j]'hj).val < (words.val.length : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (x : Slice Std.U8)
    (hw_len : 1 ≤ words.val.length ∧ words.val.length ≤ 50)
    (hw_elems : ∀ w ∈ words.val, 1 ≤ w.val.length ∧ w.val.length ≤ 50)
    (hw_bytes : ∀ w ∈ words.val, ∀ b ∈ w.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (hx_len : x.val.length = 1)
    (hx_byte : 97 ≤ (targetByte x).val ∧ (targetByte x).val ≤ 122), ∀ (r : alloc.vec.Vec Std.I64), find_words_containing words x = ok r →
      ∀ (j : ℕ) (hj : j < r.val.length),
        0 ≤ (r.val[j]'hj).val ∧ (r.val[j]'hj).val < (words.val.length : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, len(r) <= len(words).
  Preconditions: words has length between 1 and 50 inclusive; for every i with 0 <= i < len(words), len(words[i]) is between 1 and 50 inclusive, and every byte words[i][k] with 0 <= k < len(words[i]) is an ASCII lowercase English letter (97..122); x has length exactly 1, and x[0] is an ASCII lowercase English letter (97..122). -/
theorem spec_4 (words : Slice (alloc.vec.Vec Std.U8)) (x : Slice Std.U8)
    (hw_len : 1 ≤ words.val.length ∧ words.val.length ≤ 50)
    (hw_elems : ∀ w ∈ words.val, 1 ≤ w.val.length ∧ w.val.length ≤ 50)
    (hw_bytes : ∀ w ∈ words.val, ∀ b ∈ w.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (hx_len : x.val.length = 1)
    (hx_byte : 97 ≤ (targetByte x).val ∧ (targetByte x).val ≤ 122) :
    ∀ (r : alloc.vec.Vec Std.I64), find_words_containing words x = ok r →
      r.val.length ≤ words.val.length := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (x : Slice Std.U8)
    (hw_len : 1 ≤ words.val.length ∧ words.val.length ≤ 50)
    (hw_elems : ∀ w ∈ words.val, 1 ≤ w.val.length ∧ w.val.length ≤ 50)
    (hw_bytes : ∀ w ∈ words.val, ∀ b ∈ w.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (hx_len : x.val.length = 1)
    (hx_byte : 97 ≤ (targetByte x).val ∧ (targetByte x).val ≤ 122), ∀ (r : alloc.vec.Vec Std.I64), find_words_containing words x = ok r →
      r.val.length ≤ words.val.length) := by
  sorry

/-- Whenever the function returns a result r, for every j with 0 <= j < len(r), there exists k with 0 <= k < len(words[r[j]]) such that words[r[j]][k] = x[0].
  Preconditions: words has length between 1 and 50 inclusive; for every i with 0 <= i < len(words), len(words[i]) is between 1 and 50 inclusive, and every byte words[i][k] with 0 <= k < len(words[i]) is an ASCII lowercase English letter (97..122); x has length exactly 1, and x[0] is an ASCII lowercase English letter (97..122). -/
theorem spec_5 (words : Slice (alloc.vec.Vec Std.U8)) (x : Slice Std.U8)
    (hw_len : 1 ≤ words.val.length ∧ words.val.length ≤ 50)
    (hw_elems : ∀ w ∈ words.val, 1 ≤ w.val.length ∧ w.val.length ≤ 50)
    (hw_bytes : ∀ w ∈ words.val, ∀ b ∈ w.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (hx_len : x.val.length = 1)
    (hx_byte : 97 ≤ (targetByte x).val ∧ (targetByte x).val ≤ 122) :
    ∀ (r : alloc.vec.Vec Std.I64), find_words_containing words x = ok r →
      ∀ (j : ℕ) (hj : j < r.val.length),
        occurs (targetByte x) (wordAt words (r.val[j]'hj).val) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (x : Slice Std.U8)
    (hw_len : 1 ≤ words.val.length ∧ words.val.length ≤ 50)
    (hw_elems : ∀ w ∈ words.val, 1 ≤ w.val.length ∧ w.val.length ≤ 50)
    (hw_bytes : ∀ w ∈ words.val, ∀ b ∈ w.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (hx_len : x.val.length = 1)
    (hx_byte : 97 ≤ (targetByte x).val ∧ (targetByte x).val ≤ 122), ∀ (r : alloc.vec.Vec Std.I64), find_words_containing words x = ok r →
      ∀ (j : ℕ) (hj : j < r.val.length),
        occurs (targetByte x) (wordAt words (r.val[j]'hj).val)) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(words), if there exists k with 0 <= k < len(words[i]) such that words[i][k] = x[0], then there exists j with 0 <= j < len(r) such that r[j] = i.
  Preconditions: words has length between 1 and 50 inclusive; for every i with 0 <= i < len(words), len(words[i]) is between 1 and 50 inclusive, and every byte words[i][k] with 0 <= k < len(words[i]) is an ASCII lowercase English letter (97..122); x has length exactly 1, and x[0] is an ASCII lowercase English letter (97..122). -/
theorem spec_6 (words : Slice (alloc.vec.Vec Std.U8)) (x : Slice Std.U8)
    (hw_len : 1 ≤ words.val.length ∧ words.val.length ≤ 50)
    (hw_elems : ∀ w ∈ words.val, 1 ≤ w.val.length ∧ w.val.length ≤ 50)
    (hw_bytes : ∀ w ∈ words.val, ∀ b ∈ w.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (hx_len : x.val.length = 1)
    (hx_byte : 97 ≤ (targetByte x).val ∧ (targetByte x).val ≤ 122) :
    ∀ (r : alloc.vec.Vec Std.I64), find_words_containing words x = ok r →
      ∀ (i : ℕ), i < words.val.length →
        occurs (targetByte x) (wordAt words (i : ℤ)) →
          ∃ (j : ℕ) (hj : j < r.val.length), (r.val[j]'hj).val = (i : ℤ) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (x : Slice Std.U8)
    (hw_len : 1 ≤ words.val.length ∧ words.val.length ≤ 50)
    (hw_elems : ∀ w ∈ words.val, 1 ≤ w.val.length ∧ w.val.length ≤ 50)
    (hw_bytes : ∀ w ∈ words.val, ∀ b ∈ w.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (hx_len : x.val.length = 1)
    (hx_byte : 97 ≤ (targetByte x).val ∧ (targetByte x).val ≤ 122), ∀ (r : alloc.vec.Vec Std.I64), find_words_containing words x = ok r →
      ∀ (i : ℕ), i < words.val.length →
        occurs (targetByte x) (wordAt words (i : ℤ)) →
          ∃ (j : ℕ) (hj : j < r.val.length), (r.val[j]'hj).val = (i : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, for all j and k with 0 <= j < len(r) and 0 <= k < len(r), if r[j] = r[k] then j = k.
  Preconditions: words has length between 1 and 50 inclusive; for every i with 0 <= i < len(words), len(words[i]) is between 1 and 50 inclusive, and every byte words[i][k] with 0 <= k < len(words[i]) is an ASCII lowercase English letter (97..122); x has length exactly 1, and x[0] is an ASCII lowercase English letter (97..122). -/
theorem spec_7 (words : Slice (alloc.vec.Vec Std.U8)) (x : Slice Std.U8)
    (hw_len : 1 ≤ words.val.length ∧ words.val.length ≤ 50)
    (hw_elems : ∀ w ∈ words.val, 1 ≤ w.val.length ∧ w.val.length ≤ 50)
    (hw_bytes : ∀ w ∈ words.val, ∀ b ∈ w.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (hx_len : x.val.length = 1)
    (hx_byte : 97 ≤ (targetByte x).val ∧ (targetByte x).val ≤ 122) :
    ∀ (r : alloc.vec.Vec Std.I64), find_words_containing words x = ok r →
      ∀ (j k : ℕ) (hj : j < r.val.length) (hk : k < r.val.length),
        (r.val[j]'hj).val = (r.val[k]'hk).val → j = k := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (x : Slice Std.U8)
    (hw_len : 1 ≤ words.val.length ∧ words.val.length ≤ 50)
    (hw_elems : ∀ w ∈ words.val, 1 ≤ w.val.length ∧ w.val.length ≤ 50)
    (hw_bytes : ∀ w ∈ words.val, ∀ b ∈ w.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (hx_len : x.val.length = 1)
    (hx_byte : 97 ≤ (targetByte x).val ∧ (targetByte x).val ≤ 122), ∀ (r : alloc.vec.Vec Std.I64), find_words_containing words x = ok r →
      ∀ (j k : ℕ) (hj : j < r.val.length) (hk : k < r.val.length),
        (r.val[j]'hj).val = (r.val[k]'hk).val → j = k) := by
  sorry

/-- Whenever the function returns a result r, len(r) is exactly the number of indices i with 0 <= i < len(words) for which there exists k with 0 <= k < len(words[i]) such that words[i][k] = x[0].
  Preconditions: words has length between 1 and 50 inclusive; for every i with 0 <= i < len(words), len(words[i]) is between 1 and 50 inclusive, and every byte words[i][k] with 0 <= k < len(words[i]) is an ASCII lowercase English letter (97..122); x has length exactly 1, and x[0] is an ASCII lowercase English letter (97..122). -/
theorem spec_8 (words : Slice (alloc.vec.Vec Std.U8)) (x : Slice Std.U8)
    (hw_len : 1 ≤ words.val.length ∧ words.val.length ≤ 50)
    (hw_elems : ∀ w ∈ words.val, 1 ≤ w.val.length ∧ w.val.length ≤ 50)
    (hw_bytes : ∀ w ∈ words.val, ∀ b ∈ w.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (hx_len : x.val.length = 1)
    (hx_byte : 97 ≤ (targetByte x).val ∧ (targetByte x).val ≤ 122) :
    ∀ (r : alloc.vec.Vec Std.I64), find_words_containing words x = ok r →
      r.val.length = numContaining words (targetByte x) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (x : Slice Std.U8)
    (hw_len : 1 ≤ words.val.length ∧ words.val.length ≤ 50)
    (hw_elems : ∀ w ∈ words.val, 1 ≤ w.val.length ∧ w.val.length ≤ 50)
    (hw_bytes : ∀ w ∈ words.val, ∀ b ∈ w.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (hx_len : x.val.length = 1)
    (hx_byte : 97 ≤ (targetByte x).val ∧ (targetByte x).val ≤ 122), ∀ (r : alloc.vec.Vec Std.I64), find_words_containing words x = ok r →
      r.val.length = numContaining words (targetByte x)) := by
  sorry

/-- Whenever the function returns a result r, for all i and j with 0 <= i < len(words) and 0 <= j < len(words), if len(words[i]) = len(words[j]) and words[i][k] = words[j][k] for every k with 0 <= k < len(words[i]), then i occurs in r if and only if j occurs in r.
  Preconditions: words has length between 1 and 50 inclusive; for every i with 0 <= i < len(words), len(words[i]) is between 1 and 50 inclusive, and every byte words[i][k] with 0 <= k < len(words[i]) is an ASCII lowercase English letter (97..122); x has length exactly 1, and x[0] is an ASCII lowercase English letter (97..122). -/
theorem spec_9 (words : Slice (alloc.vec.Vec Std.U8)) (x : Slice Std.U8)
    (hw_len : 1 ≤ words.val.length ∧ words.val.length ≤ 50)
    (hw_elems : ∀ w ∈ words.val, 1 ≤ w.val.length ∧ w.val.length ≤ 50)
    (hw_bytes : ∀ w ∈ words.val, ∀ b ∈ w.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (hx_len : x.val.length = 1)
    (hx_byte : 97 ≤ (targetByte x).val ∧ (targetByte x).val ≤ 122) :
    ∀ (r : alloc.vec.Vec Std.I64), find_words_containing words x = ok r →
      ∀ (i j : ℕ), i < words.val.length → j < words.val.length →
        wordAt words (i : ℤ) = wordAt words (j : ℤ) →
          (resultContains r.val i ↔ resultContains r.val j) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (x : Slice Std.U8)
    (hw_len : 1 ≤ words.val.length ∧ words.val.length ≤ 50)
    (hw_elems : ∀ w ∈ words.val, 1 ≤ w.val.length ∧ w.val.length ≤ 50)
    (hw_bytes : ∀ w ∈ words.val, ∀ b ∈ w.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (hx_len : x.val.length = 1)
    (hx_byte : 97 ≤ (targetByte x).val ∧ (targetByte x).val ≤ 122), ∀ (r : alloc.vec.Vec Std.I64), find_words_containing words x = ok r →
      ∀ (i j : ℕ), i < words.val.length → j < words.val.length →
        wordAt words (i : ℤ) = wordAt words (j : ℤ) →
          (resultContains r.val i ↔ resultContains r.val j)) := by
  sorry

end AegisSpec.FindWordsContaining
