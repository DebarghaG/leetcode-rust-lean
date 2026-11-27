import Aegis.RotateString.Code.Funs

/-!
# Specifications of `Aegis.RotateString.rotate_string`

LeetCode problem `rotate-string`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.RotateString

  def byteLen (t : Slice U8) : ℕ := (Slice.len t).val

  def listAt (l : List U8) (i : ℕ) : ℕ := ((l[i]?).map (fun x => x.val)).getD 0

  def byteAt (t : Slice U8) (i : ℕ) : ℕ := listAt t.val i

  def Lowercase (t : Slice U8) : Prop := ∀ x ∈ t.val, 97 ≤ x.val ∧ x.val ≤ 122

  def IsRotation (s goal : Slice U8) : Prop :=
    ∃ k, k < byteLen s ∧ ∀ i, i < byteLen s → byteAt goal i = byteAt s ((i + k) % byteLen s)

  def countByte (t : Slice U8) (b : ℕ) : ℕ :=
    (t.val.filter (fun x => x.val = b)).length

  def countBigram (t : Slice U8) (n a b : ℕ) : ℕ :=
    ((List.range n).filter (fun i => byteAt t i = a && byteAt t ((i + 1) % n) = b)).length

  /-- Whenever rotate_string s goal returns a result r, r = true if and only if len(s) = len(goal) and there exists an integer k with 0 <= k < len(s) such that for every integer i with 0 <= i < len(s), goal[i] = s[(i + k) mod len(s)]. Here s[j] denotes the byte at 0-based index j, and (i + k) mod len(s) is the remainder in [0, len(s)).
    Preconditions: len(s) >= 1, len(goal) >= 1, len(s) <= 100, len(goal) <= 100, and every byte of s and of goal is a lowercase English letter (ASCII code between 97 and 122 inclusive). -/
  theorem spec_1 (s goal : Slice U8)
      (hs1 : 1 ≤ byteLen s) (hg1 : 1 ≤ byteLen goal)
      (hs100 : byteLen s ≤ 100) (hg100 : byteLen goal ≤ 100)
      (hsl : Lowercase s) (hgl : Lowercase goal) :
      ∀ r, Aegis.RotateString.rotate_string s goal = ok r →
        (r = true ↔ byteLen s = byteLen goal ∧ IsRotation s goal) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s goal : Slice U8)
        (hs1 : 1 ≤ byteLen s) (hg1 : 1 ≤ byteLen goal)
        (hs100 : byteLen s ≤ 100) (hg100 : byteLen goal ≤ 100)
        (hsl : Lowercase s) (hgl : Lowercase goal), ∀ r, Aegis.RotateString.rotate_string s goal = ok r →
          (r = true ↔ byteLen s = byteLen goal ∧ IsRotation s goal)) := by
    sorry

  /-- For every s and goal satisfying the preconditions, rotate_string s goal returns a result (it does not fail, panic, overflow, or perform an out-of-bounds access).
    Preconditions: len(s) >= 1, len(goal) >= 1, len(s) <= 100, len(goal) <= 100, and every byte of s and of goal is a lowercase English letter (ASCII code between 97 and 122 inclusive). -/
  theorem spec_2 (s goal : Slice U8)
      (hs1 : 1 ≤ byteLen s) (hg1 : 1 ≤ byteLen goal)
      (hs100 : byteLen s ≤ 100) (hg100 : byteLen goal ≤ 100)
      (hsl : Lowercase s) (hgl : Lowercase goal) :
      ∃ r, Aegis.RotateString.rotate_string s goal = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s goal : Slice U8)
        (hs1 : 1 ≤ byteLen s) (hg1 : 1 ≤ byteLen goal)
        (hs100 : byteLen s ≤ 100) (hg100 : byteLen goal ≤ 100)
        (hsl : Lowercase s) (hgl : Lowercase goal), ∃ r, Aegis.RotateString.rotate_string s goal = ok r) := by
    sorry

  /-- Whenever rotate_string s goal returns a result r with r = true, then for every byte b with 0 <= b <= 255, the number of indices i with 0 <= i < len(s) and s[i] = b equals the number of indices j with 0 <= j < len(goal) and goal[j] = b.
    Preconditions: len(s) >= 1, len(goal) >= 1, len(s) <= 100, len(goal) <= 100, and every byte of s and of goal is a lowercase English letter (ASCII code between 97 and 122 inclusive). -/
  theorem spec_3 (s goal : Slice U8)
      (hs1 : 1 ≤ byteLen s) (hg1 : 1 ≤ byteLen goal)
      (hs100 : byteLen s ≤ 100) (hg100 : byteLen goal ≤ 100)
      (hsl : Lowercase s) (hgl : Lowercase goal) :
      ∀ r, Aegis.RotateString.rotate_string s goal = ok r → r = true →
        ∀ b, b ≤ 255 → countByte s b = countByte goal b := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s goal : Slice U8)
        (hs1 : 1 ≤ byteLen s) (hg1 : 1 ≤ byteLen goal)
        (hs100 : byteLen s ≤ 100) (hg100 : byteLen goal ≤ 100)
        (hsl : Lowercase s) (hgl : Lowercase goal), ∀ r, Aegis.RotateString.rotate_string s goal = ok r → r = true →
          ∀ b, b ≤ 255 → countByte s b = countByte goal b) := by
    sorry

  /-- Whenever rotate_string s goal returns a result r with r = true, let n = len(s). Then for every pair of bytes (a,b) with 0 <= a <= 255 and 0 <= b <= 255, the number of indices i with 0 <= i < n such that s[i] = a and s[(i + 1) mod n] = b equals the number of indices j with 0 <= j < n such that goal[j] = a and goal[(j + 1) mod n] = b.
    Preconditions: len(s) >= 1, len(goal) >= 1, len(s) <= 100, len(goal) <= 100, and every byte of s and of goal is a lowercase English letter (ASCII code between 97 and 122 inclusive). -/
  theorem spec_4 (s goal : Slice U8)
      (hs1 : 1 ≤ byteLen s) (hg1 : 1 ≤ byteLen goal)
      (hs100 : byteLen s ≤ 100) (hg100 : byteLen goal ≤ 100)
      (hsl : Lowercase s) (hgl : Lowercase goal) :
      ∀ r, Aegis.RotateString.rotate_string s goal = ok r → r = true →
        ∀ a b, a ≤ 255 → b ≤ 255 →
          countBigram s (byteLen s) a b = countBigram goal (byteLen s) a b := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s goal : Slice U8)
        (hs1 : 1 ≤ byteLen s) (hg1 : 1 ≤ byteLen goal)
        (hs100 : byteLen s ≤ 100) (hg100 : byteLen goal ≤ 100)
        (hsl : Lowercase s) (hgl : Lowercase goal), ∀ r, Aegis.RotateString.rotate_string s goal = ok r → r = true →
          ∀ a b, a ≤ 255 → b ≤ 255 →
            countBigram s (byteLen s) a b = countBigram goal (byteLen s) a b) := by
    sorry

  /-- For every s and goal satisfying the preconditions, rotate_string s goal and rotate_string goal s both return results, and the two returned booleans are equal.
    Preconditions: len(s) >= 1, len(goal) >= 1, len(s) <= 100, len(goal) <= 100, and every byte of s and of goal is a lowercase English letter (ASCII code between 97 and 122 inclusive). -/
  theorem spec_5 (s goal : Slice U8)
      (hs1 : 1 ≤ byteLen s) (hg1 : 1 ≤ byteLen goal)
      (hs100 : byteLen s ≤ 100) (hg100 : byteLen goal ≤ 100)
      (hsl : Lowercase s) (hgl : Lowercase goal) :
      ∃ r₁ r₂, Aegis.RotateString.rotate_string s goal = ok r₁ ∧
        Aegis.RotateString.rotate_string goal s = ok r₂ ∧ r₁ = r₂ := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s goal : Slice U8)
        (hs1 : 1 ≤ byteLen s) (hg1 : 1 ≤ byteLen goal)
        (hs100 : byteLen s ≤ 100) (hg100 : byteLen goal ≤ 100)
        (hsl : Lowercase s) (hgl : Lowercase goal), ∃ r₁ r₂, Aegis.RotateString.rotate_string s goal = ok r₁ ∧
          Aegis.RotateString.rotate_string goal s = ok r₂ ∧ r₁ = r₂) := by
    sorry

  /-- For every integer k with 0 <= k < len(s), let s' be the slice of length len(s) defined by s'[i] = s[(i + k) mod len(s)] for every integer i with 0 <= i < len(s). Then rotate_string s' goal and rotate_string s goal both return results, and their returned booleans are equal.
    Preconditions: len(s) >= 1, len(goal) >= 1, len(s) <= 100, len(goal) <= 100, and every byte of s and of goal is a lowercase English letter (ASCII code between 97 and 122 inclusive). -/
  theorem spec_6 (s goal : Slice U8)
      (hs1 : 1 ≤ byteLen s) (hg1 : 1 ≤ byteLen goal)
      (hs100 : byteLen s ≤ 100) (hg100 : byteLen goal ≤ 100)
      (hsl : Lowercase s) (hgl : Lowercase goal) :
      ∀ k, k < byteLen s → ∃ s' : Slice U8,
        byteLen s' = byteLen s ∧
        (∀ i, i < byteLen s → byteAt s' i = byteAt s ((i + k) % byteLen s)) ∧
        ∃ r r', Aegis.RotateString.rotate_string s' goal = ok r ∧
          Aegis.RotateString.rotate_string s goal = ok r' ∧ r = r' := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s goal : Slice U8)
        (hs1 : 1 ≤ byteLen s) (hg1 : 1 ≤ byteLen goal)
        (hs100 : byteLen s ≤ 100) (hg100 : byteLen goal ≤ 100)
        (hsl : Lowercase s) (hgl : Lowercase goal), ∀ k, k < byteLen s → ∃ s' : Slice U8,
          byteLen s' = byteLen s ∧
          (∀ i, i < byteLen s → byteAt s' i = byteAt s ((i + k) % byteLen s)) ∧
          ∃ r r', Aegis.RotateString.rotate_string s' goal = ok r ∧
            Aegis.RotateString.rotate_string s goal = ok r' ∧ r = r') := by
    sorry

  /-- For every integer k with 0 <= k < len(goal), let goal' be the slice of length len(goal) defined by goal'[i] = goal[(i + k) mod len(goal)] for every integer i with 0 <= i < len(goal). Then rotate_string s goal' and rotate_string s goal both return results, and their returned booleans are equal.
    Preconditions: len(s) >= 1, len(goal) >= 1, len(s) <= 100, len(goal) <= 100, and every byte of s and of goal is a lowercase English letter (ASCII code between 97 and 122 inclusive). -/
  theorem spec_7 (s goal : Slice U8)
      (hs1 : 1 ≤ byteLen s) (hg1 : 1 ≤ byteLen goal)
      (hs100 : byteLen s ≤ 100) (hg100 : byteLen goal ≤ 100)
      (hsl : Lowercase s) (hgl : Lowercase goal) :
      ∀ k, k < byteLen goal → ∃ goal' : Slice U8,
        byteLen goal' = byteLen goal ∧
        (∀ i, i < byteLen goal → byteAt goal' i = byteAt goal ((i + k) % byteLen goal)) ∧
        ∃ r r', Aegis.RotateString.rotate_string s goal' = ok r ∧
          Aegis.RotateString.rotate_string s goal = ok r' ∧ r = r' := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s goal : Slice U8)
        (hs1 : 1 ≤ byteLen s) (hg1 : 1 ≤ byteLen goal)
        (hs100 : byteLen s ≤ 100) (hg100 : byteLen goal ≤ 100)
        (hsl : Lowercase s) (hgl : Lowercase goal), ∀ k, k < byteLen goal → ∃ goal' : Slice U8,
          byteLen goal' = byteLen goal ∧
          (∀ i, i < byteLen goal → byteAt goal' i = byteAt goal ((i + k) % byteLen goal)) ∧
          ∃ r r', Aegis.RotateString.rotate_string s goal' = ok r ∧
            Aegis.RotateString.rotate_string s goal = ok r' ∧ r = r') := by
    sorry

  /-- Whenever rotate_string s goal returns a result r with r = true, we have len(s) = len(goal), and there exists an integer k with 0 <= k < len(s) such that for every integer i with 0 <= i < len(goal), goal[i] = (s ++ s)[k + i]. Here s ++ s is the concatenation of s with itself, indexed from 0, and the index k + i is less than 2 * len(s).
    Preconditions: len(s) >= 1, len(goal) >= 1, len(s) <= 100, len(goal) <= 100, and every byte of s and of goal is a lowercase English letter (ASCII code between 97 and 122 inclusive). -/
  theorem spec_8 (s goal : Slice U8)
      (hs1 : 1 ≤ byteLen s) (hg1 : 1 ≤ byteLen goal)
      (hs100 : byteLen s ≤ 100) (hg100 : byteLen goal ≤ 100)
      (hsl : Lowercase s) (hgl : Lowercase goal) :
      ∀ r, Aegis.RotateString.rotate_string s goal = ok r → r = true →
        byteLen s = byteLen goal ∧
        ∃ k, k < byteLen s ∧
          ∀ i, i < byteLen goal → byteAt goal i = listAt (s.val ++ s.val) (k + i) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s goal : Slice U8)
        (hs1 : 1 ≤ byteLen s) (hg1 : 1 ≤ byteLen goal)
        (hs100 : byteLen s ≤ 100) (hg100 : byteLen goal ≤ 100)
        (hsl : Lowercase s) (hgl : Lowercase goal), ∀ r, Aegis.RotateString.rotate_string s goal = ok r → r = true →
          byteLen s = byteLen goal ∧
          ∃ k, k < byteLen s ∧
            ∀ i, i < byteLen goal → byteAt goal i = listAt (s.val ++ s.val) (k + i)) := by
    sorry

  /-- Whenever rotate_string s goal returns a result r with r = false and len(s) = len(goal), then for every integer k with 0 <= k < len(s), there exists an integer i with 0 <= i < len(s) such that goal[i] != s[(i + k) mod len(s)].
    Preconditions: len(s) >= 1, len(goal) >= 1, len(s) <= 100, len(goal) <= 100, and every byte of s and of goal is a lowercase English letter (ASCII code between 97 and 122 inclusive). -/
  theorem spec_9 (s goal : Slice U8)
      (hs1 : 1 ≤ byteLen s) (hg1 : 1 ≤ byteLen goal)
      (hs100 : byteLen s ≤ 100) (hg100 : byteLen goal ≤ 100)
      (hsl : Lowercase s) (hgl : Lowercase goal) :
      ∀ r, Aegis.RotateString.rotate_string s goal = ok r → r = false →
        byteLen s = byteLen goal →
        ∀ k, k < byteLen s →
          ∃ i, i < byteLen s ∧ byteAt goal i ≠ byteAt s ((i + k) % byteLen s) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s goal : Slice U8)
        (hs1 : 1 ≤ byteLen s) (hg1 : 1 ≤ byteLen goal)
        (hs100 : byteLen s ≤ 100) (hg100 : byteLen goal ≤ 100)
        (hsl : Lowercase s) (hgl : Lowercase goal), ∀ r, Aegis.RotateString.rotate_string s goal = ok r → r = false →
          byteLen s = byteLen goal →
          ∀ k, k < byteLen s →
            ∃ i, i < byteLen s ∧ byteAt goal i ≠ byteAt s ((i + k) % byteLen s)) := by
    sorry

  end AegisSpec.RotateString
