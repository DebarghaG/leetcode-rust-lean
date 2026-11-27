import Aegis.MinimumDistance.Code.Funs

/-!
# Specifications of `Aegis.MinimumDistance.minimum_distance`

LeetCode problem `minimum-distance-to-type-a-word-using-two-fingers`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MinimumDistance

namespace AegisSpec.MinimumDistance

def wordBytes (word : Slice Std.U8) : List ℕ := word.val.map (fun b => b.val)

def byteAt (w : List ℕ) (i : ℕ) : ℕ := w.getD i 0

def keyRow (c : ℕ) : ℕ := (c - 65) / 6

def keyCol (c : ℕ) : ℕ := (c - 65) % 6

def keyDist (c₁ c₂ : ℕ) : ℕ :=
  ((keyRow c₁ - keyRow c₂) + (keyRow c₂ - keyRow c₁)) +
    ((keyCol c₁ - keyCol c₂) + (keyCol c₂ - keyCol c₁))

def pathCost : List ℕ → ℕ
  | [] => 0
  | [_] => 0
  | c₁ :: c₂ :: rest => keyDist c₁ c₂ + pathCost (c₂ :: rest)

def IsAssignment (n : ℕ) (f : ℕ → ℕ) : Prop := ∀ i, i < n → f i = 1 ∨ f i = 2

def fingerCost (w : List ℕ) (f : ℕ → ℕ) (t : ℕ) : ℕ :=
  pathCost (((List.range w.length).filter (fun i => f i = t)).map (fun i => byteAt w i))

def totalCost (w : List ℕ) (f : ℕ → ℕ) : ℕ := fingerCost w f 1 + fingerCost w f 2

def splitCost (w : List ℕ) (k : ℕ) : ℕ :=
  pathCost (w.take (k + 1)) + pathCost (w.drop (k + 1))

noncomputable def minPairDist (w : List ℕ) : ℕ :=
  sInf {m : ℕ | ∃ c₁ ∈ w, ∃ c₂ ∈ w, c₁ ≠ c₂ ∧ m = keyDist c₁ c₂}

/-- Let n = len(word). For an uppercase byte c, define idx(c) = c - 65, row(c) = floor(idx(c)/6), col(c) = idx(c) mod 6, and d(c1,c2) = |row(c1)-row(c2)| + |col(c1)-col(c2)|. An assignment is any function f from {0,...,n-1} to {1,2}. For a finger t, let i_1 < ... < i_m be the indices i with f(i)=t, and define cost_t(f) = sum_{j=1}^{m-1} d(word[i_j], word[i_{j+1}]) (empty sum 0 if m <= 1). Let totalCost(f) = cost_1(f) + cost_2(f). Whenever minimum_distance(word) returns a result r, r = min over all assignments f of totalCost(f).
  Preconditions: len(word) is an integer with 2 <= len(word) <= 300, and every byte word[i] for 0 <= i < len(word) is an ASCII uppercase letter (code 65 through 90). -/
theorem spec_1 (word : Slice Std.U8)
    (hlen_low : 2 ≤ word.val.length) (hlen_high : word.val.length ≤ 300)
    (hup : ∀ b ∈ word.val, 65 ≤ b.val ∧ b.val ≤ 90) :
    ∀ r, minimum_distance word = ok r →
      (∀ f : ℕ → ℕ, IsAssignment word.val.length f →
        r.val ≤ (totalCost (wordBytes word) f : ℤ)) ∧
      (∃ f : ℕ → ℕ, IsAssignment word.val.length f ∧
        r.val = (totalCost (wordBytes word) f : ℤ)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (word : Slice Std.U8)
    (hlen_low : 2 ≤ word.val.length) (hlen_high : word.val.length ≤ 300)
    (hup : ∀ b ∈ word.val, 65 ≤ b.val ∧ b.val ≤ 90), ∀ r, minimum_distance word = ok r →
      (∀ f : ℕ → ℕ, IsAssignment word.val.length f →
        r.val ≤ (totalCost (wordBytes word) f : ℤ)) ∧
      (∃ f : ℕ → ℕ, IsAssignment word.val.length f ∧
        r.val = (totalCost (wordBytes word) f : ℤ))) := by
  sorry

/-- The function returns a result r (that is, it does not fail, panic, overflow, or access an out-of-bounds index) for every word satisfying the preconditions.
  Preconditions: len(word) is an integer with 2 <= len(word) <= 300, and every byte word[i] for 0 <= i < len(word) is an ASCII uppercase letter (code 65 through 90). -/
theorem spec_2 (word : Slice Std.U8)
    (hlen_low : 2 ≤ word.val.length) (hlen_high : word.val.length ≤ 300)
    (hup : ∀ b ∈ word.val, 65 ≤ b.val ∧ b.val ≤ 90) :
    ∃ r, minimum_distance word = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (word : Slice Std.U8)
    (hlen_low : 2 ≤ word.val.length) (hlen_high : word.val.length ≤ 300)
    (hup : ∀ b ∈ word.val, 65 ≤ b.val ∧ b.val ≤ 90), ∃ r, minimum_distance word = ok r) := by
  sorry

/-- Whenever minimum_distance(word) returns a result r, r >= 0.
  Preconditions: len(word) is an integer with 2 <= len(word) <= 300, and every byte word[i] for 0 <= i < len(word) is an ASCII uppercase letter (code 65 through 90). -/
theorem spec_3 (word : Slice Std.U8)
    (hlen_low : 2 ≤ word.val.length) (hlen_high : word.val.length ≤ 300)
    (hup : ∀ b ∈ word.val, 65 ≤ b.val ∧ b.val ≤ 90) :
    ∀ r, minimum_distance word = ok r → 0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (word : Slice Std.U8)
    (hlen_low : 2 ≤ word.val.length) (hlen_high : word.val.length ≤ 300)
    (hup : ∀ b ∈ word.val, 65 ≤ b.val ∧ b.val ≤ 90), ∀ r, minimum_distance word = ok r → 0 ≤ r.val) := by
  sorry

/-- Let n = len(word). For uppercase bytes c1,c2 define row(c)=floor((c-65)/6), col(c)=(c-65) mod 6, and d(c1,c2)=|row(c1)-row(c2)|+|col(c1)-col(c2)|. Whenever minimum_distance(word) returns a result r, for every integer k with 0 <= k <= n-1 we have r <= C_k, where C_k = (sum_{i=0}^{k-1} d(word[i],word[i+1])) + (sum_{i=k+1}^{n-2} d(word[i],word[i+1])), and an empty sum is 0.
  Preconditions: len(word) is an integer with 2 <= len(word) <= 300, and every byte word[i] for 0 <= i < len(word) is an ASCII uppercase letter (code 65 through 90). -/
theorem spec_4 (word : Slice Std.U8)
    (hlen_low : 2 ≤ word.val.length) (hlen_high : word.val.length ≤ 300)
    (hup : ∀ b ∈ word.val, 65 ≤ b.val ∧ b.val ≤ 90) :
    ∀ r, minimum_distance word = ok r →
      ∀ k : ℕ, k ≤ word.val.length - 1 →
        r.val ≤ (splitCost (wordBytes word) k : ℤ) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (word : Slice Std.U8)
    (hlen_low : 2 ≤ word.val.length) (hlen_high : word.val.length ≤ 300)
    (hup : ∀ b ∈ word.val, 65 ≤ b.val ∧ b.val ≤ 90), ∀ r, minimum_distance word = ok r →
      ∀ k : ℕ, k ≤ word.val.length - 1 →
        r.val ≤ (splitCost (wordBytes word) k : ℤ)) := by
  sorry

/-- Whenever minimum_distance(word) returns a result r, r = 0 if and only if the set { word[i] | 0 <= i < len(word) } has at most 2 elements.
  Preconditions: len(word) is an integer with 2 <= len(word) <= 300, and every byte word[i] for 0 <= i < len(word) is an ASCII uppercase letter (code 65 through 90). -/
theorem spec_5 (word : Slice Std.U8)
    (hlen_low : 2 ≤ word.val.length) (hlen_high : word.val.length ≤ 300)
    (hup : ∀ b ∈ word.val, 65 ≤ b.val ∧ b.val ≤ 90) :
    ∀ r, minimum_distance word = ok r →
      (r.val = 0 ↔ (wordBytes word).toFinset.card ≤ 2) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (word : Slice Std.U8)
    (hlen_low : 2 ≤ word.val.length) (hlen_high : word.val.length ≤ 300)
    (hup : ∀ b ∈ word.val, 65 ≤ b.val ∧ b.val ≤ 90), ∀ r, minimum_distance word = ok r →
      (r.val = 0 ↔ (wordBytes word).toFinset.card ≤ 2)) := by
  sorry

/-- Let n = len(word) and let rev(word) be the byte sequence of length n with rev(word)[i] = word[n-1-i] for 0 <= i < n. Whenever minimum_distance(word) returns r and minimum_distance(rev(word)) returns r_rev, r = r_rev.
  Preconditions: len(word) is an integer with 2 <= len(word) <= 300, and every byte word[i] for 0 <= i < len(word) is an ASCII uppercase letter (code 65 through 90). -/
theorem spec_6 (word rword : Slice Std.U8)
    (hlen_low : 2 ≤ word.val.length) (hlen_high : word.val.length ≤ 300)
    (hup : ∀ b ∈ word.val, 65 ≤ b.val ∧ b.val ≤ 90)
    (hrev : rword.val = word.val.reverse) :
    ∀ r r', minimum_distance word = ok r → minimum_distance rword = ok r' → r = r' := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (word rword : Slice Std.U8)
    (hlen_low : 2 ≤ word.val.length) (hlen_high : word.val.length ≤ 300)
    (hup : ∀ b ∈ word.val, 65 ≤ b.val ∧ b.val ≤ 90)
    (hrev : rword.val = word.val.reverse), ∀ r r', minimum_distance word = ok r → minimum_distance rword = ok r' → r = r') := by
  sorry

/-- Let word' be the sequence of length n-1 obtained by deleting the occurrence at index i+1. Whenever minimum_distance(word) returns r and minimum_distance(word') returns r', r = r'.
  Preconditions: len(word) is an integer with 2 <= len(word) <= 300, every byte word[i] for 0 <= i < len(word) is an ASCII uppercase letter (code 65 through 90), n = len(word) >= 3, i is an integer with 0 <= i < n-1, and word[i] = word[i+1]. -/
theorem spec_7 (word w' : Slice Std.U8) (i : ℕ)
    (hlen_low : 3 ≤ word.val.length) (hlen_high : word.val.length ≤ 300)
    (hup : ∀ b ∈ word.val, 65 ≤ b.val ∧ b.val ≤ 90)
    (hi : i < word.val.length - 1)
    (hsame : byteAt (wordBytes word) i = byteAt (wordBytes word) (i + 1))
    (hdel : w'.val = word.val.eraseIdx (i + 1)) :
    ∀ r r', minimum_distance word = ok r → minimum_distance w' = ok r' → r = r' := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (word w' : Slice Std.U8) (i : ℕ)
    (hlen_low : 3 ≤ word.val.length) (hlen_high : word.val.length ≤ 300)
    (hup : ∀ b ∈ word.val, 65 ≤ b.val ∧ b.val ≤ 90)
    (hi : i < word.val.length - 1)
    (hsame : byteAt (wordBytes word) i = byteAt (wordBytes word) (i + 1))
    (hdel : w'.val = word.val.eraseIdx (i + 1)), ∀ r r', minimum_distance word = ok r → minimum_distance w' = ok r' → r = r') := by
  sorry

/-- Let word' be the sequence of length n-1 obtained by deleting the occurrence at index i. Whenever minimum_distance(word) returns r and minimum_distance(word') returns r', r >= r'.
  Preconditions: len(word) is an integer with 2 <= len(word) <= 300, every byte word[i] for 0 <= i < len(word) is an ASCII uppercase letter (code 65 through 90), n = len(word) >= 3, and i is an integer with 0 <= i < n. -/
theorem spec_8 (word w' : Slice Std.U8) (i : ℕ)
    (hlen_low : 3 ≤ word.val.length) (hlen_high : word.val.length ≤ 300)
    (hup : ∀ b ∈ word.val, 65 ≤ b.val ∧ b.val ≤ 90)
    (hi : i < word.val.length)
    (hdel : w'.val = word.val.eraseIdx i) :
    ∀ r r', minimum_distance word = ok r → minimum_distance w' = ok r' → r' ≤ r := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (word w' : Slice Std.U8) (i : ℕ)
    (hlen_low : 3 ≤ word.val.length) (hlen_high : word.val.length ≤ 300)
    (hup : ∀ b ∈ word.val, 65 ≤ b.val ∧ b.val ≤ 90)
    (hi : i < word.val.length)
    (hdel : w'.val = word.val.eraseIdx i), ∀ r r', minimum_distance word = ok r → minimum_distance w' = ok r' → r' ≤ r) := by
  sorry

/-- Let n = len(word). Whenever minimum_distance(word) returns a result r, there exists an assignment f from {0,...,n-1} to {1,2} such that f(0)=1 and, using the keyboard-cost definition from spec_1, totalCost(f) = r.
  Preconditions: len(word) is an integer with 2 <= len(word) <= 300, and every byte word[i] for 0 <= i < len(word) is an ASCII uppercase letter (code 65 through 90). -/
theorem spec_9 (word : Slice Std.U8)
    (hlen_low : 2 ≤ word.val.length) (hlen_high : word.val.length ≤ 300)
    (hup : ∀ b ∈ word.val, 65 ≤ b.val ∧ b.val ≤ 90) :
    ∀ r, minimum_distance word = ok r →
      ∃ f : ℕ → ℕ, IsAssignment word.val.length f ∧ f 0 = 1 ∧
        r.val = (totalCost (wordBytes word) f : ℤ) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (word : Slice Std.U8)
    (hlen_low : 2 ≤ word.val.length) (hlen_high : word.val.length ≤ 300)
    (hup : ∀ b ∈ word.val, 65 ≤ b.val ∧ b.val ≤ 90), ∀ r, minimum_distance word = ok r →
      ∃ f : ℕ → ℕ, IsAssignment word.val.length f ∧ f 0 = 1 ∧
        r.val = (totalCost (wordBytes word) f : ℤ)) := by
  sorry

/-- For uppercase bytes c1,c2 define row(c)=floor((c-65)/6), col(c)=(c-65) mod 6, and d(c1,c2)=|row(c1)-row(c2)|+|col(c1)-col(c2)|. Whenever minimum_distance(word) returns a result r, r = min( d(word[0],word[1]), d(word[1],word[2]), d(word[0],word[2]) ).
  Preconditions: len(word) is an integer with 2 <= len(word) <= 300, every byte word[i] for 0 <= i < len(word) is an ASCII uppercase letter (code 65 through 90), and n = len(word) = 3. -/
theorem spec_10 (word : Slice Std.U8)
    (hlen_low : 2 ≤ word.val.length) (hlen_high : word.val.length ≤ 300)
    (hup : ∀ b ∈ word.val, 65 ≤ b.val ∧ b.val ≤ 90)
    (hlen : word.val.length = 3) :
    ∀ r, minimum_distance word = ok r →
      r.val = ((min (keyDist (byteAt (wordBytes word) 0) (byteAt (wordBytes word) 1))
        (min (keyDist (byteAt (wordBytes word) 1) (byteAt (wordBytes word) 2))
          (keyDist (byteAt (wordBytes word) 0) (byteAt (wordBytes word) 2))) : ℕ) : ℤ) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (word : Slice Std.U8)
    (hlen_low : 2 ≤ word.val.length) (hlen_high : word.val.length ≤ 300)
    (hup : ∀ b ∈ word.val, 65 ≤ b.val ∧ b.val ≤ 90)
    (hlen : word.val.length = 3), ∀ r, minimum_distance word = ok r →
      r.val = ((min (keyDist (byteAt (wordBytes word) 0) (byteAt (wordBytes word) 1))
        (min (keyDist (byteAt (wordBytes word) 1) (byteAt (wordBytes word) 2))
          (keyDist (byteAt (wordBytes word) 0) (byteAt (wordBytes word) 2))) : ℕ) : ℤ)) := by
  sorry

/-- For uppercase bytes c1,c2 define row(c)=floor((c-65)/6), col(c)=(c-65) mod 6, and d(c1,c2)=|row(c1)-row(c2)|+|col(c1)-col(c2)|. Whenever minimum_distance(word) returns a result r, r >= M, where M = min{ d(c1,c2) | c1 and c2 are bytes occurring in word and c1 != c2 }.
  Preconditions: len(word) is an integer with 2 <= len(word) <= 300, every byte word[i] for 0 <= i < len(word) is an ASCII uppercase letter (code 65 through 90), and the set of bytes occurring in word has at least 3 elements. -/
theorem spec_11 (word : Slice Std.U8)
    (hlen_low : 2 ≤ word.val.length) (hlen_high : word.val.length ≤ 300)
    (hup : ∀ b ∈ word.val, 65 ≤ b.val ∧ b.val ≤ 90)
    (hcard : 3 ≤ (wordBytes word).toFinset.card) :
    ∀ r, minimum_distance word = ok r →
      (minPairDist (wordBytes word) : ℤ) ≤ r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (word : Slice Std.U8)
    (hlen_low : 2 ≤ word.val.length) (hlen_high : word.val.length ≤ 300)
    (hup : ∀ b ∈ word.val, 65 ≤ b.val ∧ b.val ≤ 90)
    (hcard : 3 ≤ (wordBytes word).toFinset.card), ∀ r, minimum_distance word = ok r →
      (minPairDist (wordBytes word) : ℤ) ≤ r.val) := by
  sorry

end AegisSpec.MinimumDistance
