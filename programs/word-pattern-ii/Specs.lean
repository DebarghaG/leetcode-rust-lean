import Aegis.WordPatternMatch.Code.Funs

/-!
# Specifications of `Aegis.WordPatternMatch.word_pattern_match`

LeetCode problem `word-pattern-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.WordPatternMatch

  open Aegis.WordPatternMatch

  def sliceBytes (p : Slice Std.U8) : List Std.U8 := p.list.toList

  def byteAt (p : Slice Std.U8) (i : ℕ) : Std.U8 := (sliceBytes p).getD i 0#u8

  def byteSeg (p : Slice Std.U8) (x y : ℕ) : List Std.U8 :=
    (sliceBytes p).extract x y

  def isLowerAscii (b : Std.U8) : Prop := 97 ≤ b.val ∧ b.val ≤ 122

  def allLowerAscii (p : Slice Std.U8) : Prop := ∀ b ∈ sliceBytes p, isLowerAscii b

  def OccursIn (b : Std.U8) (p : Slice Std.U8) : Prop := b ∈ sliceBytes p

  def IsPatternWitness (pattern : Slice Std.U8) (f : Std.U8 → List Std.U8) : Prop :=
    (∀ b, OccursIn b pattern → f b ≠ []) ∧
      (∀ b₁, OccursIn b₁ pattern → ∀ b₂, OccursIn b₂ pattern →
        f b₁ = f b₂ → b₁ = b₂)

  def concatImage (pattern : Slice Std.U8) (f : Std.U8 → List Std.U8) : List Std.U8 :=
    (sliceBytes pattern).map f |>.flatten

  def IsCutPattern (pattern s : Slice Std.U8) (idx : ℕ → ℕ) : Prop :=
    idx 0 = 0 ∧
      idx (sliceBytes pattern).length = (sliceBytes s).length ∧
        (∀ a, a < (sliceBytes pattern).length → idx a < idx (a + 1))

  /-- Whenever word_pattern_match pattern s returns Result.ok r, r = true if and only if there exist natural numbers i_0, i_1, ..., i_{len(pattern)} with 0 = i_0 < i_1 < ... < i_{len(pattern)} = len(s) such that, for every 0 <= a < len(pattern) and 0 <= b < len(pattern), pattern[a] = pattern[b] if and only if the contiguous byte slices s[i_a .. i_{a+1}) and s[i_b .. i_{b+1}) are equal. Here s[x..y) denotes the bytes s[x], s[x+1], ..., s[y-1].
    Preconditions: 1 <= len(pattern) <= 20, 1 <= len(s) <= 20, and every byte of pattern and s is an ASCII lowercase letter (97..122). -/
  theorem spec_1 (pattern s : Slice Std.U8)
      (hn1 : 1 ≤ (sliceBytes pattern).length) (hn2 : (sliceBytes pattern).length ≤ 20)
      (hm1 : 1 ≤ (sliceBytes s).length) (hm2 : (sliceBytes s).length ≤ 20)
      (hp : allLowerAscii pattern) (hs : allLowerAscii s)
      (r : Bool) (hr : word_pattern_match pattern s = ok r) :
      (r = true ↔
        ∃ idx : ℕ → ℕ, IsCutPattern pattern s idx ∧
          ∀ a, a < (sliceBytes pattern).length → ∀ b, b < (sliceBytes pattern).length →
            (byteAt pattern a = byteAt pattern b ↔
              byteSeg s (idx a) (idx (a + 1)) = byteSeg s (idx b) (idx (b + 1)))) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (pattern s : Slice Std.U8)
        (hn1 : 1 ≤ (sliceBytes pattern).length) (hn2 : (sliceBytes pattern).length ≤ 20)
        (hm1 : 1 ≤ (sliceBytes s).length) (hm2 : (sliceBytes s).length ≤ 20)
        (hp : allLowerAscii pattern) (hs : allLowerAscii s)
        (r : Bool) (hr : word_pattern_match pattern s = ok r), (r = true ↔
          ∃ idx : ℕ → ℕ, IsCutPattern pattern s idx ∧
            ∀ a, a < (sliceBytes pattern).length → ∀ b, b < (sliceBytes pattern).length →
              (byteAt pattern a = byteAt pattern b ↔
                byteSeg s (idx a) (idx (a + 1)) = byteSeg s (idx b) (idx (b + 1))))) := by
    sorry

  /-- The function does not fail: for every such pattern and s there exists a boolean r such that word_pattern_match pattern s = Result.ok r.
    Preconditions: 1 <= len(pattern) <= 20, 1 <= len(s) <= 20, and every byte of pattern and s is an ASCII lowercase letter (97..122). -/
  theorem spec_2 (pattern s : Slice Std.U8)
      (hn1 : 1 ≤ (sliceBytes pattern).length) (hn2 : (sliceBytes pattern).length ≤ 20)
      (hm1 : 1 ≤ (sliceBytes s).length) (hm2 : (sliceBytes s).length ≤ 20)
      (hp : allLowerAscii pattern) (hs : allLowerAscii s) :
      ∃ r : Bool, word_pattern_match pattern s = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (pattern s : Slice Std.U8)
        (hn1 : 1 ≤ (sliceBytes pattern).length) (hn2 : (sliceBytes pattern).length ≤ 20)
        (hm1 : 1 ≤ (sliceBytes s).length) (hm2 : (sliceBytes s).length ≤ 20)
        (hp : allLowerAscii pattern) (hs : allLowerAscii s), ∃ r : Bool, word_pattern_match pattern s = ok r) := by
    sorry

  /-- Whenever word_pattern_match pattern s returns Result.ok r, r = false.
    Preconditions: 1 <= len(pattern) <= 20, 1 <= len(s) <= 20, every byte is an ASCII lowercase letter, and len(s) < len(pattern). -/
  theorem spec_3 (pattern s : Slice Std.U8)
      (hn1 : 1 ≤ (sliceBytes pattern).length) (hn2 : (sliceBytes pattern).length ≤ 20)
      (hm1 : 1 ≤ (sliceBytes s).length) (hm2 : (sliceBytes s).length ≤ 20)
      (hp : allLowerAscii pattern) (hs : allLowerAscii s)
      (hlen : (sliceBytes s).length < (sliceBytes pattern).length)
      (r : Bool) (hr : word_pattern_match pattern s = ok r) :
      r = false := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (pattern s : Slice Std.U8)
        (hn1 : 1 ≤ (sliceBytes pattern).length) (hn2 : (sliceBytes pattern).length ≤ 20)
        (hm1 : 1 ≤ (sliceBytes s).length) (hm2 : (sliceBytes s).length ≤ 20)
        (hp : allLowerAscii pattern) (hs : allLowerAscii s)
        (hlen : (sliceBytes s).length < (sliceBytes pattern).length)
        (r : Bool) (hr : word_pattern_match pattern s = ok r), r = false) := by
    sorry

  /-- Whenever word_pattern_match pattern s returns Result.ok r, r = true.
    Preconditions: 1 <= len(pattern) <= 20, 1 <= len(s) <= 20, every byte is an ASCII lowercase letter, and len(pattern) = 1. -/
  theorem spec_4 (pattern s : Slice Std.U8)
      (hn1 : 1 ≤ (sliceBytes pattern).length) (hn2 : (sliceBytes pattern).length ≤ 20)
      (hm1 : 1 ≤ (sliceBytes s).length) (hm2 : (sliceBytes s).length ≤ 20)
      (hp : allLowerAscii pattern) (hs : allLowerAscii s)
      (hlen : (sliceBytes pattern).length = 1)
      (r : Bool) (hr : word_pattern_match pattern s = ok r) :
      r = true := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (pattern s : Slice Std.U8)
        (hn1 : 1 ≤ (sliceBytes pattern).length) (hn2 : (sliceBytes pattern).length ≤ 20)
        (hm1 : 1 ≤ (sliceBytes s).length) (hm2 : (sliceBytes s).length ≤ 20)
        (hp : allLowerAscii pattern) (hs : allLowerAscii s)
        (hlen : (sliceBytes pattern).length = 1)
        (r : Bool) (hr : word_pattern_match pattern s = ok r), r = true) := by
    sorry

  /-- Whenever word_pattern_match pattern s returns Result.ok r, r = true if and only if len(pattern) = 1.
    Preconditions: 1 <= len(pattern) <= 20, 1 <= len(s) <= 20, every byte is an ASCII lowercase letter, and len(s) = 1. -/
  theorem spec_5 (pattern s : Slice Std.U8)
      (hn1 : 1 ≤ (sliceBytes pattern).length) (hn2 : (sliceBytes pattern).length ≤ 20)
      (hm1 : 1 ≤ (sliceBytes s).length) (hm2 : (sliceBytes s).length ≤ 20)
      (hp : allLowerAscii pattern) (hs : allLowerAscii s)
      (hlen : (sliceBytes s).length = 1)
      (r : Bool) (hr : word_pattern_match pattern s = ok r) :
      (r = true ↔ (sliceBytes pattern).length = 1) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (pattern s : Slice Std.U8)
        (hn1 : 1 ≤ (sliceBytes pattern).length) (hn2 : (sliceBytes pattern).length ≤ 20)
        (hm1 : 1 ≤ (sliceBytes s).length) (hm2 : (sliceBytes s).length ≤ 20)
        (hp : allLowerAscii pattern) (hs : allLowerAscii s)
        (hlen : (sliceBytes s).length = 1)
        (r : Bool) (hr : word_pattern_match pattern s = ok r), (r = true ↔ (sliceBytes pattern).length = 1)) := by
    sorry

  /-- Whenever word_pattern_match pattern s returns Result.ok r, r = true if and only if for every 0 <= i < len(pattern) and 0 <= j < len(pattern), pattern[i] = pattern[j] if and only if s[i] = s[j].
    Preconditions: 1 <= len(pattern) <= 20, 1 <= len(s) <= 20, every byte is an ASCII lowercase letter, and len(pattern) = len(s). -/
  theorem spec_6 (pattern s : Slice Std.U8)
      (hn1 : 1 ≤ (sliceBytes pattern).length) (hn2 : (sliceBytes pattern).length ≤ 20)
      (hm1 : 1 ≤ (sliceBytes s).length) (hm2 : (sliceBytes s).length ≤ 20)
      (hp : allLowerAscii pattern) (hs : allLowerAscii s)
      (hlen : (sliceBytes pattern).length = (sliceBytes s).length)
      (r : Bool) (hr : word_pattern_match pattern s = ok r) :
      (r = true ↔
        ∀ i, i < (sliceBytes pattern).length → ∀ j, j < (sliceBytes pattern).length →
          (byteAt pattern i = byteAt pattern j ↔ byteAt s i = byteAt s j)) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (pattern s : Slice Std.U8)
        (hn1 : 1 ≤ (sliceBytes pattern).length) (hn2 : (sliceBytes pattern).length ≤ 20)
        (hm1 : 1 ≤ (sliceBytes s).length) (hm2 : (sliceBytes s).length ≤ 20)
        (hp : allLowerAscii pattern) (hs : allLowerAscii s)
        (hlen : (sliceBytes pattern).length = (sliceBytes s).length)
        (r : Bool) (hr : word_pattern_match pattern s = ok r), (r = true ↔
          ∀ i, i < (sliceBytes pattern).length → ∀ j, j < (sliceBytes pattern).length →
            (byteAt pattern i = byteAt pattern j ↔ byteAt s i = byteAt s j))) := by
    sorry

  /-- Whenever word_pattern_match pattern s returns Result.ok r, r = true if and only if there exists an integer L with 1 <= L <= len(s) such that len(s) = len(pattern) * L and for every 0 <= i < len(pattern) and 0 <= j < L, s[i*L + j] = s[j].
    Preconditions: 1 <= len(pattern) <= 20, 1 <= len(s) <= 20, every byte is an ASCII lowercase letter, and all bytes of pattern are equal: for every 0 <= i < len(pattern) and 0 <= j < len(pattern), pattern[i] = pattern[j]. -/
  theorem spec_7 (pattern s : Slice Std.U8)
      (hn1 : 1 ≤ (sliceBytes pattern).length) (hn2 : (sliceBytes pattern).length ≤ 20)
      (hm1 : 1 ≤ (sliceBytes s).length) (hm2 : (sliceBytes s).length ≤ 20)
      (hp : allLowerAscii pattern) (hs : allLowerAscii s)
      (hconst : ∀ i, i < (sliceBytes pattern).length →
        ∀ j, j < (sliceBytes pattern).length → byteAt pattern i = byteAt pattern j)
      (r : Bool) (hr : word_pattern_match pattern s = ok r) :
      (r = true ↔
        ∃ L : ℕ, 1 ≤ L ∧ L ≤ (sliceBytes s).length ∧
          (sliceBytes s).length = (sliceBytes pattern).length * L ∧
            ∀ i, i < (sliceBytes pattern).length → ∀ j, j < L →
              byteAt s (i * L + j) = byteAt s j) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (pattern s : Slice Std.U8)
        (hn1 : 1 ≤ (sliceBytes pattern).length) (hn2 : (sliceBytes pattern).length ≤ 20)
        (hm1 : 1 ≤ (sliceBytes s).length) (hm2 : (sliceBytes s).length ≤ 20)
        (hp : allLowerAscii pattern) (hs : allLowerAscii s)
        (hconst : ∀ i, i < (sliceBytes pattern).length →
          ∀ j, j < (sliceBytes pattern).length → byteAt pattern i = byteAt pattern j)
        (r : Bool) (hr : word_pattern_match pattern s = ok r), (r = true ↔
          ∃ L : ℕ, 1 ≤ L ∧ L ≤ (sliceBytes s).length ∧
            (sliceBytes s).length = (sliceBytes pattern).length * L ∧
              ∀ i, i < (sliceBytes pattern).length → ∀ j, j < L →
                byteAt s (i * L + j) = byteAt s j)) := by
    sorry

  /-- Whenever word_pattern_match pattern s returns Result.ok r, r = true if and only if there exist natural numbers i_0, i_1, ..., i_{len(pattern)} with 0 = i_0 < i_1 < ... < i_{len(pattern)} = len(s) such that the len(pattern) non-empty byte slices s[i_a .. i_{a+1}) for 0 <= a < len(pattern) are pairwise distinct: for all 0 <= a < b < len(pattern), s[i_a .. i_{a+1}) != s[i_b .. i_{b+1}).
    Preconditions: 1 <= len(pattern) <= 20, 1 <= len(s) <= 20, every byte is an ASCII lowercase letter, and all pattern characters are pairwise distinct: for every 0 <= i < j < len(pattern), pattern[i] != pattern[j]. -/
  theorem spec_8 (pattern s : Slice Std.U8)
      (hn1 : 1 ≤ (sliceBytes pattern).length) (hn2 : (sliceBytes pattern).length ≤ 20)
      (hm1 : 1 ≤ (sliceBytes s).length) (hm2 : (sliceBytes s).length ≤ 20)
      (hp : allLowerAscii pattern) (hs : allLowerAscii s)
      (hdist : ∀ i, i < (sliceBytes pattern).length → ∀ j, i < j →
        j < (sliceBytes pattern).length → byteAt pattern i ≠ byteAt pattern j)
      (r : Bool) (hr : word_pattern_match pattern s = ok r) :
      (r = true ↔
        ∃ idx : ℕ → ℕ, IsCutPattern pattern s idx ∧
          ∀ a, a < (sliceBytes pattern).length → ∀ b, a < b →
            b < (sliceBytes pattern).length →
              byteSeg s (idx a) (idx (a + 1)) ≠ byteSeg s (idx b) (idx (b + 1))) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (pattern s : Slice Std.U8)
        (hn1 : 1 ≤ (sliceBytes pattern).length) (hn2 : (sliceBytes pattern).length ≤ 20)
        (hm1 : 1 ≤ (sliceBytes s).length) (hm2 : (sliceBytes s).length ≤ 20)
        (hp : allLowerAscii pattern) (hs : allLowerAscii s)
        (hdist : ∀ i, i < (sliceBytes pattern).length → ∀ j, i < j →
          j < (sliceBytes pattern).length → byteAt pattern i ≠ byteAt pattern j)
        (r : Bool) (hr : word_pattern_match pattern s = ok r), (r = true ↔
          ∃ idx : ℕ → ℕ, IsCutPattern pattern s idx ∧
            ∀ a, a < (sliceBytes pattern).length → ∀ b, a < b →
              b < (sliceBytes pattern).length →
                byteSeg s (idx a) (idx (a + 1)) ≠ byteSeg s (idx b) (idx (b + 1)))) := by
    sorry

  /-- Whenever word_pattern_match pattern s returns Result.ok true, there exists a function f from the set of bytes occurring in pattern to non-empty byte strings such that f is injective on that set and the concatenation f(pattern[0]) f(pattern[1]) ... f(pattern[len(pattern)-1]) is exactly the byte string s.
    Preconditions: 1 <= len(pattern) <= 20, 1 <= len(s) <= 20, and every byte of pattern and s is an ASCII lowercase letter (97..122). -/
  theorem spec_9 (pattern s : Slice Std.U8)
      (hn1 : 1 ≤ (sliceBytes pattern).length) (hn2 : (sliceBytes pattern).length ≤ 20)
      (hm1 : 1 ≤ (sliceBytes s).length) (hm2 : (sliceBytes s).length ≤ 20)
      (hp : allLowerAscii pattern) (hs : allLowerAscii s)
      (hr : word_pattern_match pattern s = ok true) :
      ∃ f : Std.U8 → List Std.U8,
        IsPatternWitness pattern f ∧ concatImage pattern f = sliceBytes s := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (pattern s : Slice Std.U8)
        (hn1 : 1 ≤ (sliceBytes pattern).length) (hn2 : (sliceBytes pattern).length ≤ 20)
        (hm1 : 1 ≤ (sliceBytes s).length) (hm2 : (sliceBytes s).length ≤ 20)
        (hp : allLowerAscii pattern) (hs : allLowerAscii s)
        (hr : word_pattern_match pattern s = ok true), ∃ f : Std.U8 → List Std.U8,
          IsPatternWitness pattern f ∧ concatImage pattern f = sliceBytes s) := by
    sorry

  /-- Whenever word_pattern_match pattern s returns Result.ok false, there does not exist a function f from the set of bytes occurring in pattern to non-empty byte strings such that f is injective on that set and the concatenation f(pattern[0]) f(pattern[1]) ... f(pattern[len(pattern)-1]) is exactly s.
    Preconditions: 1 <= len(pattern) <= 20, 1 <= len(s) <= 20, and every byte of pattern and s is an ASCII lowercase letter (97..122). -/
  theorem spec_10 (pattern s : Slice Std.U8)
      (hn1 : 1 ≤ (sliceBytes pattern).length) (hn2 : (sliceBytes pattern).length ≤ 20)
      (hm1 : 1 ≤ (sliceBytes s).length) (hm2 : (sliceBytes s).length ≤ 20)
      (hp : allLowerAscii pattern) (hs : allLowerAscii s)
      (hr : word_pattern_match pattern s = ok false) :
      ¬ ∃ f : Std.U8 → List Std.U8,
        IsPatternWitness pattern f ∧ concatImage pattern f = sliceBytes s := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (pattern s : Slice Std.U8)
        (hn1 : 1 ≤ (sliceBytes pattern).length) (hn2 : (sliceBytes pattern).length ≤ 20)
        (hm1 : 1 ≤ (sliceBytes s).length) (hm2 : (sliceBytes s).length ≤ 20)
        (hp : allLowerAscii pattern) (hs : allLowerAscii s)
        (hr : word_pattern_match pattern s = ok false), ¬ ∃ f : Std.U8 → List Std.U8,
          IsPatternWitness pattern f ∧ concatImage pattern f = sliceBytes s) := by
    sorry

  /-- Whenever word_pattern_match pattern1 s returns Result.ok r1 and word_pattern_match pattern2 s returns Result.ok r2, we have r1 = r2.
    Preconditions: Let pattern1 and pattern2 be byte slices satisfying the same input constraints as the problem, with len(pattern1) = len(pattern2); let s satisfy 1 <= len(s) <= 20 and all bytes are ASCII lowercase. Assume the equality relations of pattern1 and pattern2 agree: for every 0 <= i < len(pattern1) and 0 <= j < len(pattern1), pattern1[i] = pattern1[j] if and only if pattern2[i] = pattern2[j]. -/
  theorem spec_11 (pattern₁ pattern₂ s : Slice Std.U8)
      (hn1 : 1 ≤ (sliceBytes pattern₁).length)
      (hn2 : (sliceBytes pattern₁).length ≤ 20)
      (hn1' : 1 ≤ (sliceBytes pattern₂).length)
      (hn2' : (sliceBytes pattern₂).length ≤ 20)
      (hm1 : 1 ≤ (sliceBytes s).length) (hm2 : (sliceBytes s).length ≤ 20)
      (hp₁ : allLowerAscii pattern₁) (hp₂ : allLowerAscii pattern₂)
      (hs : allLowerAscii s)
      (hlen : (sliceBytes pattern₁).length = (sliceBytes pattern₂).length)
      (heq : ∀ i, i < (sliceBytes pattern₁).length → ∀ j, j < (sliceBytes pattern₁).length →
        (byteAt pattern₁ i = byteAt pattern₁ j ↔ byteAt pattern₂ i = byteAt pattern₂ j))
      (r₁ r₂ : Bool)
      (hr₁ : word_pattern_match pattern₁ s = ok r₁)
      (hr₂ : word_pattern_match pattern₂ s = ok r₂) :
      r₁ = r₂ := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (pattern₁ pattern₂ s : Slice Std.U8)
        (hn1 : 1 ≤ (sliceBytes pattern₁).length)
        (hn2 : (sliceBytes pattern₁).length ≤ 20)
        (hn1' : 1 ≤ (sliceBytes pattern₂).length)
        (hn2' : (sliceBytes pattern₂).length ≤ 20)
        (hm1 : 1 ≤ (sliceBytes s).length) (hm2 : (sliceBytes s).length ≤ 20)
        (hp₁ : allLowerAscii pattern₁) (hp₂ : allLowerAscii pattern₂)
        (hs : allLowerAscii s)
        (hlen : (sliceBytes pattern₁).length = (sliceBytes pattern₂).length)
        (heq : ∀ i, i < (sliceBytes pattern₁).length → ∀ j, j < (sliceBytes pattern₁).length →
          (byteAt pattern₁ i = byteAt pattern₁ j ↔ byteAt pattern₂ i = byteAt pattern₂ j))
        (r₁ r₂ : Bool)
        (hr₁ : word_pattern_match pattern₁ s = ok r₁)
        (hr₂ : word_pattern_match pattern₂ s = ok r₂), r₁ = r₂) := by
    sorry

  /-- Whenever word_pattern_match pattern s returns Result.ok r, r = true if and only if there exists a function L from the set of bytes occurring in pattern to positive integers such that L is injective on that set and sum_{i=0}^{len(pattern)-1} L(pattern[i]) = len(s).
    Preconditions: 1 <= len(pattern) <= 20, 1 <= len(s) <= 20, every byte is an ASCII lowercase letter, and all bytes of s are equal: there exists a byte b such that for every 0 <= i < len(s), s[i] = b. -/
  theorem spec_12 (pattern s : Slice Std.U8)
      (hn1 : 1 ≤ (sliceBytes pattern).length) (hn2 : (sliceBytes pattern).length ≤ 20)
      (hm1 : 1 ≤ (sliceBytes s).length) (hm2 : (sliceBytes s).length ≤ 20)
      (hp : allLowerAscii pattern) (hs : allLowerAscii s)
      (hconst : ∃ b : Std.U8, ∀ i, i < (sliceBytes s).length → byteAt s i = b)
      (r : Bool) (hr : word_pattern_match pattern s = ok r) :
      (r = true ↔
        ∃ L : Std.U8 → ℕ,
          (∀ b, OccursIn b pattern → 1 ≤ L b) ∧
            (∀ b₁, OccursIn b₁ pattern → ∀ b₂, OccursIn b₂ pattern →
              L b₁ = L b₂ → b₁ = b₂) ∧
              ((sliceBytes pattern).map L).sum = (sliceBytes s).length) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (pattern s : Slice Std.U8)
        (hn1 : 1 ≤ (sliceBytes pattern).length) (hn2 : (sliceBytes pattern).length ≤ 20)
        (hm1 : 1 ≤ (sliceBytes s).length) (hm2 : (sliceBytes s).length ≤ 20)
        (hp : allLowerAscii pattern) (hs : allLowerAscii s)
        (hconst : ∃ b : Std.U8, ∀ i, i < (sliceBytes s).length → byteAt s i = b)
        (r : Bool) (hr : word_pattern_match pattern s = ok r), (r = true ↔
          ∃ L : Std.U8 → ℕ,
            (∀ b, OccursIn b pattern → 1 ≤ L b) ∧
              (∀ b₁, OccursIn b₁ pattern → ∀ b₂, OccursIn b₂ pattern →
                L b₁ = L b₂ → b₁ = b₂) ∧
                ((sliceBytes pattern).map L).sum = (sliceBytes s).length)) := by
    sorry

  end AegisSpec.WordPatternMatch
