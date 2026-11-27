import Aegis.MinValidStrings.Code.Funs

/-!
# Specifications of `Aegis.MinValidStrings.min_valid_strings`

LeetCode problem `minimum-number-of-valid-strings-to-form-target-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinValidStrings

def wordBytes (w : alloc.vec.Vec U8) : List ℕ := w.val.map (fun b => b.val)

def wordsBytes (words : Slice (alloc.vec.Vec U8)) : List (List ℕ) :=
  words.val.map wordBytes

def targetBytes (target : Slice U8) : List ℕ := target.val.map (fun b => b.val)

def IsPrefix (x y : List ℕ) : Prop := ∃ z, y = x ++ z

def IsValidString (words : Slice (alloc.vec.Vec U8)) (x : List ℕ) : Prop :=
  x ≠ [] ∧ ∃ w ∈ wordsBytes words, IsPrefix x w

def IsDecomposition (words : Slice (alloc.vec.Vec U8)) (xs : List (List ℕ))
    (z : List ℕ) : Prop :=
  (∀ x ∈ xs, IsValidString words x) ∧ z = xs.flatten

def Decomposable (words : Slice (alloc.vec.Vec U8)) (m : ℕ) (z : List ℕ) : Prop :=
  ∃ xs : List (List ℕ), xs.length = m ∧ IsDecomposition words xs z

def subBytes (l : List ℕ) (a b : ℕ) : List ℕ := (l.drop a).take (b - a)

def byteAt (l : List ℕ) (i : ℕ) : Option ℕ := l[i]?

def wordAt (words : Slice (alloc.vec.Vec U8)) (j : ℕ) : Option (List ℕ) :=
  (wordsBytes words)[j]?

noncomputable def minParts (words : Slice (alloc.vec.Vec U8)) (z : List ℕ) : ℤ :=
  by
  classical
  exact
    if h : ∃ m : ℕ, Decomposable words m z then
      ((Nat.find (p := fun m => Decomposable words m z) h : ℕ) : ℤ)
    else -1

def NoValidStringCrosses (words : Slice (alloc.vec.Vec U8)) (z : List ℕ) (p : ℕ) : Prop :=
  ∀ (x : List ℕ), IsValidString words x →
    ∀ a b : ℕ, a < p → p < b → b ≤ z.length → subBytes z a b ≠ x

def InputsValid (words : Slice (alloc.vec.Vec U8)) (target : Slice U8) : Prop :=
  1 ≤ (wordsBytes words).length ∧
  (wordsBytes words).length ≤ 100 ∧
  (∀ w ∈ wordsBytes words, 1 ≤ w.length ∧ w.length ≤ 50000) ∧
  ((wordsBytes words).map (fun w => w.length)).sum ≤ 100000 ∧
  (∀ w ∈ wordsBytes words, ∀ b ∈ w, 97 ≤ b ∧ b ≤ 122) ∧
  1 ≤ (targetBytes target).length ∧
  (targetBytes target).length ≤ 50000 ∧
  (∀ b ∈ targetBytes target, 97 ≤ b ∧ b ≤ 122)

/-- Let a valid string be a nonempty byte string x such that for some j with 0 <= j < len(words), len(x) <= len(words[j]) and x[t] = words[j][t] for every 0 <= t < len(x). Whenever min_valid_strings returns a result r, r is the minimum number m >= 1 for which there exist valid strings x_1, ..., x_m with target = x_1 ++ ... ++ x_m, where ++ is byte-string concatenation; if no such finite sequence exists, r = -1. Equivalently, r = -1 if and only if target is not a concatenation of one or more valid strings, and if r != -1 then target has a decomposition into exactly r valid strings and none into fewer than r valid strings.
  Preconditions: All inputs satisfy the problem constraints: 1 <= len(words) <= 100; every words[j] has length between 1 and 50000; sum of lengths of all words is at most 100000; each byte of each word is lowercase ASCII; 1 <= len(target) <= 50000; each byte of target is lowercase ASCII. -/
theorem spec_1 (words : Slice (alloc.vec.Vec U8)) (target : Slice U8)
    (hvalid : InputsValid words target) :
    ∀ r : I64, Aegis.MinValidStrings.min_valid_strings words target = ok r →
      (r.val = -1 ∧ ¬ ∃ m : ℕ, 1 ≤ m ∧ Decomposable words m (targetBytes target)) ∨
      (∃ m : ℕ, r.val = (m : ℤ) ∧ 1 ≤ m ∧ Decomposable words m (targetBytes target) ∧
        ∀ m' : ℕ, Decomposable words m' (targetBytes target) → m ≤ m') := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec U8)) (target : Slice U8)
    (hvalid : InputsValid words target), ∀ r : I64, Aegis.MinValidStrings.min_valid_strings words target = ok r →
      (r.val = -1 ∧ ¬ ∃ m : ℕ, 1 ≤ m ∧ Decomposable words m (targetBytes target)) ∨
      (∃ m : ℕ, r.val = (m : ℤ) ∧ 1 ≤ m ∧ Decomposable words m (targetBytes target) ∧
        ∀ m' : ℕ, Decomposable words m' (targetBytes target) → m ≤ m')) := by
  sorry

/-- Whenever the function is called with such inputs, it returns a result r and does not fail: there is no arithmetic overflow, indexing failure, panic, or out-of-bounds access.
  Preconditions: All inputs satisfy the problem constraints: 1 <= len(words) <= 100; every words[j] has length between 1 and 50000; sum of lengths of all words is at most 100000; each byte of each word is lowercase ASCII; 1 <= len(target) <= 50000; each byte of target is lowercase ASCII. -/
theorem spec_2 (words : Slice (alloc.vec.Vec U8)) (target : Slice U8)
    (hvalid : InputsValid words target) :
    ∃ r : I64, Aegis.MinValidStrings.min_valid_strings words target = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec U8)) (target : Slice U8)
    (hvalid : InputsValid words target), ∃ r : I64, Aegis.MinValidStrings.min_valid_strings words target = ok r) := by
  sorry

/-- Whenever the function returns a result r, either r = -1 or 1 <= r <= len(target).
  Preconditions: All inputs satisfy the problem constraints: 1 <= len(words) <= 100; every words[j] has length between 1 and 50000; sum of lengths of all words is at most 100000; each byte of each word is lowercase ASCII; 1 <= len(target) <= 50000; each byte of target is lowercase ASCII. -/
theorem spec_3 (words : Slice (alloc.vec.Vec U8)) (target : Slice U8)
    (hvalid : InputsValid words target) :
    ∀ r : I64, Aegis.MinValidStrings.min_valid_strings words target = ok r →
      r.val = -1 ∨ (1 ≤ r.val ∧ r.val ≤ ((targetBytes target).length : ℤ)) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec U8)) (target : Slice U8)
    (hvalid : InputsValid words target), ∀ r : I64, Aegis.MinValidStrings.min_valid_strings words target = ok r →
      r.val = -1 ∨ (1 ≤ r.val ∧ r.val ≤ ((targetBytes target).length : ℤ))) := by
  sorry

/-- Whenever the function returns a result r with r != -1, for every integer m >= 1 and every sequence x_1, ..., x_m of nonempty prefixes of strings in words such that target = x_1 ++ ... ++ x_m, one has r <= m.
  Preconditions: All inputs satisfy the problem constraints: 1 <= len(words) <= 100; every words[j] has length between 1 and 50000; sum of lengths of all words is at most 100000; each byte of each word is lowercase ASCII; 1 <= len(target) <= 50000; each byte of target is lowercase ASCII. -/
theorem spec_4 (words : Slice (alloc.vec.Vec U8)) (target : Slice U8)
    (hvalid : InputsValid words target) :
    ∀ r : I64, Aegis.MinValidStrings.min_valid_strings words target = ok r → r.val ≠ -1 →
      ∀ (m : ℕ), 1 ≤ m → ∀ xs : List (List ℕ), xs.length = m →
        IsDecomposition words xs (targetBytes target) → r.val ≤ (m : ℤ) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec U8)) (target : Slice U8)
    (hvalid : InputsValid words target), ∀ r : I64, Aegis.MinValidStrings.min_valid_strings words target = ok r → r.val ≠ -1 →
      ∀ (m : ℕ), 1 ≤ m → ∀ xs : List (List ℕ), xs.length = m →
        IsDecomposition words xs (targetBytes target) → r.val ≤ (m : ℤ)) := by
  sorry

/-- Whenever the function returns a result r with r != -1, there exist exactly r nonempty prefixes x_1, ..., x_r of strings in words such that target = x_1 ++ ... ++ x_r.
  Preconditions: All inputs satisfy the problem constraints: 1 <= len(words) <= 100; every words[j] has length between 1 and 50000; sum of lengths of all words is at most 100000; each byte of each word is lowercase ASCII; 1 <= len(target) <= 50000; each byte of target is lowercase ASCII. -/
theorem spec_5 (words : Slice (alloc.vec.Vec U8)) (target : Slice U8)
    (hvalid : InputsValid words target) :
    ∀ r : I64, Aegis.MinValidStrings.min_valid_strings words target = ok r → r.val ≠ -1 →
      ∃ (m : ℕ) (xs : List (List ℕ)),
        r.val = (m : ℤ) ∧ xs.length = m ∧ IsDecomposition words xs (targetBytes target) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec U8)) (target : Slice U8)
    (hvalid : InputsValid words target), ∀ r : I64, Aegis.MinValidStrings.min_valid_strings words target = ok r → r.val ≠ -1 →
      ∃ (m : ℕ) (xs : List (List ℕ)),
        r.val = (m : ℤ) ∧ xs.length = m ∧ IsDecomposition words xs (targetBytes target)) := by
  sorry

/-- Whenever the function returns a result r, r = 1 if and only if target itself is a nonempty prefix of some word in words, i.e. there exists j with 0 <= j < len(words), len(target) <= len(words[j]), and target[t] = words[j][t] for all 0 <= t < len(target).
  Preconditions: All inputs satisfy the problem constraints: 1 <= len(words) <= 100; every words[j] has length between 1 and 50000; sum of lengths of all words is at most 100000; each byte of each word is lowercase ASCII; 1 <= len(target) <= 50000; each byte of target is lowercase ASCII. -/
theorem spec_6 (words : Slice (alloc.vec.Vec U8)) (target : Slice U8)
    (hvalid : InputsValid words target) :
    ∀ r : I64, Aegis.MinValidStrings.min_valid_strings words target = ok r →
      (r.val = 1 ↔ IsValidString words (targetBytes target)) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec U8)) (target : Slice U8)
    (hvalid : InputsValid words target), ∀ r : I64, Aegis.MinValidStrings.min_valid_strings words target = ok r →
      (r.val = 1 ↔ IsValidString words (targetBytes target))) := by
  sorry

/-- Whenever the function returns a result r with r != -1, there exists j with 0 <= j < len(words) and words[j][0] = target[0].
  Preconditions: All inputs satisfy the problem constraints: 1 <= len(words) <= 100; every words[j] has length between 1 and 50000; sum of lengths of all words is at most 100000; each byte of each word is lowercase ASCII; 1 <= len(target) <= 50000; each byte of target is lowercase ASCII. -/
theorem spec_7 (words : Slice (alloc.vec.Vec U8)) (target : Slice U8)
    (hvalid : InputsValid words target) :
    ∀ r : I64, Aegis.MinValidStrings.min_valid_strings words target = ok r → r.val ≠ -1 →
      ∃ (j : ℕ) (w : List ℕ) (b : ℕ),
        wordAt words j = some w ∧ byteAt w 0 = some b ∧ byteAt (targetBytes target) 0 = some b := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec U8)) (target : Slice U8)
    (hvalid : InputsValid words target), ∀ r : I64, Aegis.MinValidStrings.min_valid_strings words target = ok r → r.val ≠ -1 →
      ∃ (j : ℕ) (w : List ℕ) (b : ℕ),
        wordAt words j = some w ∧ byteAt w 0 = some b ∧ byteAt (targetBytes target) 0 = some b) := by
  sorry

/-- Whenever the function returns a result r, r != -1 and r <= k + 1.
  Preconditions: All inputs satisfy the problem constraints: 1 <= len(words) <= 100; every words[j] has length between 1 and 50000; sum of lengths of all words is at most 100000; each byte of each word is lowercase ASCII; 1 <= len(target) <= 50000; each byte of target is lowercase ASCII. Suppose target = x ++ y, where x is a nonempty prefix of some word in words, and there exist k >= 0 and nonempty prefixes y_1, ..., y_k of words in words such that y = y_1 ++ ... ++ y_k (the case k = 0 means y is empty). -/
theorem spec_8 (words : Slice (alloc.vec.Vec U8)) (target : Slice U8)
    (hvalid : InputsValid words target) (x y : List ℕ) (k : ℕ) (ys : List (List ℕ))
    (hsplit : targetBytes target = x ++ y) (hx : IsValidString words x)
    (hk : ys.length = k) (hy : IsDecomposition words ys y) :
    ∀ r : I64, Aegis.MinValidStrings.min_valid_strings words target = ok r →
      r.val ≠ -1 ∧ r.val ≤ (k : ℤ) + 1 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec U8)) (target : Slice U8)
    (hvalid : InputsValid words target) (x y : List ℕ) (k : ℕ) (ys : List (List ℕ))
    (hsplit : targetBytes target = x ++ y) (hx : IsValidString words x)
    (hk : ys.length = k) (hy : IsDecomposition words ys y), ∀ r : I64, Aegis.MinValidStrings.min_valid_strings words target = ok r →
      r.val ≠ -1 ∧ r.val ≤ (k : ℤ) + 1) := by
  sorry

/-- Let n = len(target), and for any byte string z let M(z) be the least m >= 0 such that z = z_1 ++ ... ++ z_m for some nonempty prefixes z_1, ..., z_m of words in words, or M(z) = -1 if no such m exists; thus M(empty) = 0. Suppose 0 < p < n and no nonempty prefix of any word in words is equal to the substring target[a..b) for any a, b with 0 <= a < p < b <= n. Then whenever the function returns r, if M(target[0..p)) != -1 and M(target[p..n)) != -1 then r = M(target[0..p)) + M(target[p..n)); otherwise r = -1.
  Preconditions: All inputs satisfy the problem constraints: 1 <= len(words) <= 100; every words[j] has length between 1 and 50000; sum of lengths of all words is at most 100000; each byte of each word is lowercase ASCII; 1 <= len(target) <= 50000; each byte of target is lowercase ASCII. -/
theorem spec_9 (words : Slice (alloc.vec.Vec U8)) (target : Slice U8)
    (hvalid : InputsValid words target) (p : ℕ)
    (hp_pos : 0 < p) (hp_lt : p < (targetBytes target).length)
    (hcut : NoValidStringCrosses words (targetBytes target) p) :
    ∀ r : I64, Aegis.MinValidStrings.min_valid_strings words target = ok r →
      let L := minParts words (subBytes (targetBytes target) 0 p)
      let R := minParts words (subBytes (targetBytes target) p (targetBytes target).length)
      ((L ≠ -1 → R ≠ -1 → r.val = L + R) ∧ ((L = -1 ∨ R = -1) → r.val = -1)) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec U8)) (target : Slice U8)
    (hvalid : InputsValid words target) (p : ℕ)
    (hp_pos : 0 < p) (hp_lt : p < (targetBytes target).length)
    (hcut : NoValidStringCrosses words (targetBytes target) p), ∀ r : I64, Aegis.MinValidStrings.min_valid_strings words target = ok r →
      let L := minParts words (subBytes (targetBytes target) 0 p)
      let R := minParts words (subBytes (targetBytes target) p (targetBytes target).length)
      ((L ≠ -1 → R ≠ -1 → r.val = L + R) ∧ ((L = -1 ∨ R = -1) → r.val = -1))) := by
  sorry

/-- Whenever the function returns r on (words, target) and returns r' on (words', target), one has r = r'.
  Preconditions: Inputs (words, target) and (words', target) both satisfy the problem constraints, and words' contains the same multiset of byte strings as words, in any order. -/
theorem spec_10 (words words' : Slice (alloc.vec.Vec U8)) (target : Slice U8)
    (hvalid : InputsValid words target) (hvalid' : InputsValid words' target)
    (hperm : (wordsBytes words).Perm (wordsBytes words')) :
    ∀ r r' : I64,
      Aegis.MinValidStrings.min_valid_strings words target = ok r →
      Aegis.MinValidStrings.min_valid_strings words' target = ok r' → r.val = r'.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (words words' : Slice (alloc.vec.Vec U8)) (target : Slice U8)
    (hvalid : InputsValid words target) (hvalid' : InputsValid words' target)
    (hperm : (wordsBytes words).Perm (wordsBytes words')), ∀ r r' : I64,
      Aegis.MinValidStrings.min_valid_strings words target = ok r →
      Aegis.MinValidStrings.min_valid_strings words' target = ok r' → r.val = r'.val) := by
  sorry

/-- Whenever the function returns r = -1, for every k with 0 < k <= len(target) such that target[0..k) is a nonempty prefix of some word in words, the suffix target[k..len(target)) is not a concatenation of zero or more nonempty prefixes of words in words.
  Preconditions: All inputs satisfy the problem constraints: 1 <= len(words) <= 100; every words[j] has length between 1 and 50000; sum of lengths of all words is at most 100000; each byte of each word is lowercase ASCII; 1 <= len(target) <= 50000; each byte of target is lowercase ASCII. -/
theorem spec_11 (words : Slice (alloc.vec.Vec U8)) (target : Slice U8)
    (hvalid : InputsValid words target) :
    ∀ r : I64, Aegis.MinValidStrings.min_valid_strings words target = ok r → r.val = -1 →
      ∀ k : ℕ, 0 < k → k ≤ (targetBytes target).length →
        IsValidString words (subBytes (targetBytes target) 0 k) →
          ¬ ∃ m : ℕ,
              Decomposable words m (subBytes (targetBytes target) k (targetBytes target).length) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec U8)) (target : Slice U8)
    (hvalid : InputsValid words target), ∀ r : I64, Aegis.MinValidStrings.min_valid_strings words target = ok r → r.val = -1 →
      ∀ k : ℕ, 0 < k → k ≤ (targetBytes target).length →
        IsValidString words (subBytes (targetBytes target) 0 k) →
          ¬ ∃ m : ℕ,
              Decomposable words m (subBytes (targetBytes target) k (targetBytes target).length)) := by
  sorry

/-- Whenever the function returns a result r with r = len(target), for every i with 0 <= i < len(target) there exists j with 0 <= j < len(words) and words[j][0] = target[i].
  Preconditions: All inputs satisfy the problem constraints: 1 <= len(words) <= 100; every words[j] has length between 1 and 50000; sum of lengths of all words is at most 100000; each byte of each word is lowercase ASCII; 1 <= len(target) <= 50000; each byte of target is lowercase ASCII. -/
theorem spec_12 (words : Slice (alloc.vec.Vec U8)) (target : Slice U8)
    (hvalid : InputsValid words target) :
    ∀ r : I64, Aegis.MinValidStrings.min_valid_strings words target = ok r →
      r.val = ((targetBytes target).length : ℤ) →
        ∀ i : ℕ, i < (targetBytes target).length →
          ∃ (j : ℕ) (w : List ℕ) (b : ℕ),
            wordAt words j = some w ∧ byteAt w 0 = some b ∧
              byteAt (targetBytes target) i = some b := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec U8)) (target : Slice U8)
    (hvalid : InputsValid words target), ∀ r : I64, Aegis.MinValidStrings.min_valid_strings words target = ok r →
      r.val = ((targetBytes target).length : ℤ) →
        ∀ i : ℕ, i < (targetBytes target).length →
          ∃ (j : ℕ) (w : List ℕ) (b : ℕ),
            wordAt words j = some w ∧ byteAt w 0 = some b ∧
              byteAt (targetBytes target) i = some b) := by
  sorry

end AegisSpec.MinValidStrings
