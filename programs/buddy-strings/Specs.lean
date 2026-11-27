import Aegis.BuddyStrings.Code.Funs

/-!
# Specifications of `Aegis.BuddyStrings.buddy_strings`

LeetCode problem `buddy-strings`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.BuddyStrings

  open Aeneas.Std

  open Aegis.BuddyStrings

  def byte (s : Slice U8) (i : ℕ) : ℕ :=
    (s.val.map (fun b : U8 => b.val)).getD i 0

  def IsAsciiLower (s : Slice U8) : Prop :=
    ∀ i, i < s.val.length → 97 ≤ byte s i ∧ byte s i ≤ 122

  def DiffOnlyAt (s goal : Slice U8) (i j : ℕ) : Prop :=
    i < s.val.length ∧ j < s.val.length ∧ i < j ∧
      ∀ k, k < s.val.length → (byte s k ≠ byte goal k ↔ k = i ∨ k = j)

  def diffCount (s goal : Slice U8) : ℕ :=
    ((List.range s.val.length).filter (fun k => byte s k ≠ byte goal k)).length

  def countByte (s : Slice U8) (c : ℕ) : ℕ :=
    ((s.val.map (fun b : U8 => b.val)).filter (fun x => x = c)).length

  /-- Whenever the function returns a result r, r = true if and only if len(s) = len(goal) and there exist indices i and j such that 0 <= i < len(s), 0 <= j < len(s), i != j, and for every k with 0 <= k < len(s), (if k = i then s[j] else if k = j then s[i] else s[k]) = goal[k]. In other words, r = true exactly when some swap of two distinct positions in s produces goal.
    Preconditions: len(s) >= 1, len(goal) >= 1, len(s) <= 20000, len(goal) <= 20000, and every byte of s and goal is in the inclusive range 97..122 (ASCII lowercase). -/
  theorem spec_1 (s goal : Slice U8)
      (hs_len : 1 ≤ s.val.length) (hg_len : 1 ≤ goal.val.length)
      (hs_max : s.val.length ≤ 20000) (hg_max : goal.val.length ≤ 20000)
      (hs_low : IsAsciiLower s) (hg_low : IsAsciiLower goal) :
      ∀ r : Bool, buddy_strings s goal = ok r →
        (r = true ↔
          s.val.length = goal.val.length ∧
            ∃ i j, i < s.val.length ∧ j < s.val.length ∧ i ≠ j ∧
              ∀ k, k < s.val.length →
                (if k = i then byte s j else if k = j then byte s i else byte s k)
                  = byte goal k) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s goal : Slice U8)
        (hs_len : 1 ≤ s.val.length) (hg_len : 1 ≤ goal.val.length)
        (hs_max : s.val.length ≤ 20000) (hg_max : goal.val.length ≤ 20000)
        (hs_low : IsAsciiLower s) (hg_low : IsAsciiLower goal), ∀ r : Bool, buddy_strings s goal = ok r →
          (r = true ↔
            s.val.length = goal.val.length ∧
              ∃ i j, i < s.val.length ∧ j < s.val.length ∧ i ≠ j ∧
                ∀ k, k < s.val.length →
                  (if k = i then byte s j else if k = j then byte s i else byte s k)
                    = byte goal k)) := by
    sorry

  /-- For every s and goal satisfying the preconditions, the function returns a result r; it does not fail due to overflow, out-of-bounds access, or panic.
    Preconditions: len(s) >= 1, len(goal) >= 1, len(s) <= 20000, len(goal) <= 20000, and every byte of s and goal is in the inclusive range 97..122 (ASCII lowercase). -/
  theorem spec_2 (s goal : Slice U8)
      (hs_len : 1 ≤ s.val.length) (hg_len : 1 ≤ goal.val.length)
      (hs_max : s.val.length ≤ 20000) (hg_max : goal.val.length ≤ 20000)
      (hs_low : IsAsciiLower s) (hg_low : IsAsciiLower goal) :
      ∃ r : Bool, buddy_strings s goal = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s goal : Slice U8)
        (hs_len : 1 ≤ s.val.length) (hg_len : 1 ≤ goal.val.length)
        (hs_max : s.val.length ≤ 20000) (hg_max : goal.val.length ≤ 20000)
        (hs_low : IsAsciiLower s) (hg_low : IsAsciiLower goal), ∃ r : Bool, buddy_strings s goal = ok r) := by
    sorry

  /-- Whenever the function returns a result r, if len(s) != len(goal), then r = false.
    Preconditions: len(s) >= 1, len(goal) >= 1, len(s) <= 20000, len(goal) <= 20000, and every byte of s and goal is in the inclusive range 97..122 (ASCII lowercase). -/
  theorem spec_3 (s goal : Slice U8)
      (hs_len : 1 ≤ s.val.length) (hg_len : 1 ≤ goal.val.length)
      (hs_max : s.val.length ≤ 20000) (hg_max : goal.val.length ≤ 20000)
      (hs_low : IsAsciiLower s) (hg_low : IsAsciiLower goal) :
      ∀ r : Bool, buddy_strings s goal = ok r →
        s.val.length ≠ goal.val.length → r = false := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s goal : Slice U8)
        (hs_len : 1 ≤ s.val.length) (hg_len : 1 ≤ goal.val.length)
        (hs_max : s.val.length ≤ 20000) (hg_max : goal.val.length ≤ 20000)
        (hs_low : IsAsciiLower s) (hg_low : IsAsciiLower goal), ∀ r : Bool, buddy_strings s goal = ok r →
          s.val.length ≠ goal.val.length → r = false) := by
    sorry

  /-- Whenever the function returns a result r, if s = goal, then r = true if and only if there exist indices i and j such that 0 <= i < len(s), 0 <= j < len(s), i != j, and s[i] = s[j].
    Preconditions: len(s) >= 1, len(goal) >= 1, len(s) <= 20000, len(goal) <= 20000, and every byte of s and goal is in the inclusive range 97..122 (ASCII lowercase). -/
  theorem spec_4 (s goal : Slice U8)
      (hs_len : 1 ≤ s.val.length) (hg_len : 1 ≤ goal.val.length)
      (hs_max : s.val.length ≤ 20000) (hg_max : goal.val.length ≤ 20000)
      (hs_low : IsAsciiLower s) (hg_low : IsAsciiLower goal) :
      ∀ r : Bool, buddy_strings s goal = ok r → s.val = goal.val →
        (r = true ↔
          ∃ i j, i < s.val.length ∧ j < s.val.length ∧ i ≠ j ∧ byte s i = byte s j) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s goal : Slice U8)
        (hs_len : 1 ≤ s.val.length) (hg_len : 1 ≤ goal.val.length)
        (hs_max : s.val.length ≤ 20000) (hg_max : goal.val.length ≤ 20000)
        (hs_low : IsAsciiLower s) (hg_low : IsAsciiLower goal), ∀ r : Bool, buddy_strings s goal = ok r → s.val = goal.val →
          (r = true ↔
            ∃ i j, i < s.val.length ∧ j < s.val.length ∧ i ≠ j ∧ byte s i = byte s j)) := by
    sorry

  /-- Whenever the function returns a result r, r = false.
    Preconditions: len(s) = 1, len(goal) >= 1, len(goal) <= 20000, and every byte of s and goal is in the inclusive range 97..122 (ASCII lowercase). -/
  theorem spec_5 (s goal : Slice U8)
      (hs_len : s.val.length = 1) (hg_len : 1 ≤ goal.val.length)
      (hg_max : goal.val.length ≤ 20000)
      (hs_low : IsAsciiLower s) (hg_low : IsAsciiLower goal) :
      ∀ r : Bool, buddy_strings s goal = ok r → r = false := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s goal : Slice U8)
        (hs_len : s.val.length = 1) (hg_len : 1 ≤ goal.val.length)
        (hg_max : goal.val.length ≤ 20000)
        (hs_low : IsAsciiLower s) (hg_low : IsAsciiLower goal), ∀ r : Bool, buddy_strings s goal = ok r → r = false) := by
    sorry

  /-- Whenever the function returns a result r, if r = true and s != goal, then len(s) = len(goal) and the set D = { k | 0 <= k < len(s) and s[k] != goal[k] } has exactly two elements.
    Preconditions: len(s) >= 1, len(goal) >= 1, len(s) <= 20000, len(goal) <= 20000, and every byte of s and goal is in the inclusive range 97..122 (ASCII lowercase). -/
  theorem spec_6 (s goal : Slice U8)
      (hs_len : 1 ≤ s.val.length) (hg_len : 1 ≤ goal.val.length)
      (hs_max : s.val.length ≤ 20000) (hg_max : goal.val.length ≤ 20000)
      (hs_low : IsAsciiLower s) (hg_low : IsAsciiLower goal) :
      ∀ r : Bool, buddy_strings s goal = ok r → r = true → s.val ≠ goal.val →
        s.val.length = goal.val.length ∧ ∃ i j, DiffOnlyAt s goal i j := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s goal : Slice U8)
        (hs_len : 1 ≤ s.val.length) (hg_len : 1 ≤ goal.val.length)
        (hs_max : s.val.length ≤ 20000) (hg_max : goal.val.length ≤ 20000)
        (hs_low : IsAsciiLower s) (hg_low : IsAsciiLower goal), ∀ r : Bool, buddy_strings s goal = ok r → r = true → s.val ≠ goal.val →
          s.val.length = goal.val.length ∧ ∃ i j, DiffOnlyAt s goal i j) := by
    sorry

  /-- Whenever the function returns a result r, if r = true, len(s) = len(goal), and the set D = { k | 0 <= k < len(s) and s[k] != goal[k] } has exactly two elements i and j with i < j, then s[i] = goal[j] and s[j] = goal[i].
    Preconditions: len(s) >= 1, len(goal) >= 1, len(s) <= 20000, len(goal) <= 20000, and every byte of s and goal is in the inclusive range 97..122 (ASCII lowercase). -/
  theorem spec_7 (s goal : Slice U8)
      (hs_len : 1 ≤ s.val.length) (hg_len : 1 ≤ goal.val.length)
      (hs_max : s.val.length ≤ 20000) (hg_max : goal.val.length ≤ 20000)
      (hs_low : IsAsciiLower s) (hg_low : IsAsciiLower goal) :
      ∀ (r : Bool) (i j : ℕ), buddy_strings s goal = ok r → r = true →
        s.val.length = goal.val.length → DiffOnlyAt s goal i j →
        byte s i = byte goal j ∧ byte s j = byte goal i := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s goal : Slice U8)
        (hs_len : 1 ≤ s.val.length) (hg_len : 1 ≤ goal.val.length)
        (hs_max : s.val.length ≤ 20000) (hg_max : goal.val.length ≤ 20000)
        (hs_low : IsAsciiLower s) (hg_low : IsAsciiLower goal), ∀ (r : Bool) (i j : ℕ), buddy_strings s goal = ok r → r = true →
          s.val.length = goal.val.length → DiffOnlyAt s goal i j →
          byte s i = byte goal j ∧ byte s j = byte goal i) := by
    sorry

  /-- Whenever the function returns a result r, if len(s) = len(goal), the set D = { k | 0 <= k < len(s) and s[k] != goal[k] } has exactly two elements i and j with i < j, and s[i] = goal[j] and s[j] = goal[i], then r = true.
    Preconditions: len(s) >= 1, len(goal) >= 1, len(s) <= 20000, len(goal) <= 20000, and every byte of s and goal is in the inclusive range 97..122 (ASCII lowercase). -/
  theorem spec_8 (s goal : Slice U8)
      (hs_len : 1 ≤ s.val.length) (hg_len : 1 ≤ goal.val.length)
      (hs_max : s.val.length ≤ 20000) (hg_max : goal.val.length ≤ 20000)
      (hs_low : IsAsciiLower s) (hg_low : IsAsciiLower goal) :
      ∀ (r : Bool) (i j : ℕ), buddy_strings s goal = ok r →
        s.val.length = goal.val.length → DiffOnlyAt s goal i j →
        byte s i = byte goal j → byte s j = byte goal i → r = true := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s goal : Slice U8)
        (hs_len : 1 ≤ s.val.length) (hg_len : 1 ≤ goal.val.length)
        (hs_max : s.val.length ≤ 20000) (hg_max : goal.val.length ≤ 20000)
        (hs_low : IsAsciiLower s) (hg_low : IsAsciiLower goal), ∀ (r : Bool) (i j : ℕ), buddy_strings s goal = ok r →
          s.val.length = goal.val.length → DiffOnlyAt s goal i j →
          byte s i = byte goal j → byte s j = byte goal i → r = true) := by
    sorry

  /-- Whenever the function returns a result r, if len(s) = len(goal) and the number of indices k with 0 <= k < len(s) and s[k] != goal[k] is greater than 2, then r = false.
    Preconditions: len(s) >= 1, len(goal) >= 1, len(s) <= 20000, len(goal) <= 20000, and every byte of s and goal is in the inclusive range 97..122 (ASCII lowercase). -/
  theorem spec_9 (s goal : Slice U8)
      (hs_len : 1 ≤ s.val.length) (hg_len : 1 ≤ goal.val.length)
      (hs_max : s.val.length ≤ 20000) (hg_max : goal.val.length ≤ 20000)
      (hs_low : IsAsciiLower s) (hg_low : IsAsciiLower goal) :
      ∀ r : Bool, buddy_strings s goal = ok r →
        s.val.length = goal.val.length → 2 < diffCount s goal → r = false := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s goal : Slice U8)
        (hs_len : 1 ≤ s.val.length) (hg_len : 1 ≤ goal.val.length)
        (hs_max : s.val.length ≤ 20000) (hg_max : goal.val.length ≤ 20000)
        (hs_low : IsAsciiLower s) (hg_low : IsAsciiLower goal), ∀ r : Bool, buddy_strings s goal = ok r →
          s.val.length = goal.val.length → 2 < diffCount s goal → r = false) := by
    sorry

  /-- Whenever the function returns a result r, if len(s) = len(goal) and the number of indices k with 0 <= k < len(s) and s[k] != goal[k] is exactly 1, then r = false.
    Preconditions: len(s) >= 1, len(goal) >= 1, len(s) <= 20000, len(goal) <= 20000, and every byte of s and goal is in the inclusive range 97..122 (ASCII lowercase). -/
  theorem spec_10 (s goal : Slice U8)
      (hs_len : 1 ≤ s.val.length) (hg_len : 1 ≤ goal.val.length)
      (hs_max : s.val.length ≤ 20000) (hg_max : goal.val.length ≤ 20000)
      (hs_low : IsAsciiLower s) (hg_low : IsAsciiLower goal) :
      ∀ r : Bool, buddy_strings s goal = ok r →
        s.val.length = goal.val.length → diffCount s goal = 1 → r = false := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (s goal : Slice U8)
        (hs_len : 1 ≤ s.val.length) (hg_len : 1 ≤ goal.val.length)
        (hs_max : s.val.length ≤ 20000) (hg_max : goal.val.length ≤ 20000)
        (hs_low : IsAsciiLower s) (hg_low : IsAsciiLower goal), ∀ r : Bool, buddy_strings s goal = ok r →
          s.val.length = goal.val.length → diffCount s goal = 1 → r = false) := by
    sorry

  /-- Whenever the function returns a result r, if r = true, then for every byte value c with 0 <= c <= 255, the number of indices k with 0 <= k < len(s) and s[k] = c equals the number of indices k with 0 <= k < len(goal) and goal[k] = c.
    Preconditions: len(s) >= 1, len(goal) >= 1, len(s) <= 20000, len(goal) <= 20000, and every byte of s and goal is in the inclusive range 97..122 (ASCII lowercase). -/
  theorem spec_11 (s goal : Slice U8)
      (hs_len : 1 ≤ s.val.length) (hg_len : 1 ≤ goal.val.length)
      (hs_max : s.val.length ≤ 20000) (hg_max : goal.val.length ≤ 20000)
      (hs_low : IsAsciiLower s) (hg_low : IsAsciiLower goal) :
      ∀ r : Bool, buddy_strings s goal = ok r → r = true →
        ∀ c : ℕ, c ≤ 255 → countByte s c = countByte goal c := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (s goal : Slice U8)
        (hs_len : 1 ≤ s.val.length) (hg_len : 1 ≤ goal.val.length)
        (hs_max : s.val.length ≤ 20000) (hg_max : goal.val.length ≤ 20000)
        (hs_low : IsAsciiLower s) (hg_low : IsAsciiLower goal), ∀ r : Bool, buddy_strings s goal = ok r → r = true →
          ∀ c : ℕ, c ≤ 255 → countByte s c = countByte goal c) := by
    sorry

  /-- Whenever the function returns a result r, if s = goal and for every i and j with 0 <= i < j < len(s) we have s[i] != s[j], then r = false.
    Preconditions: len(s) >= 1, len(goal) >= 1, len(s) <= 20000, len(goal) <= 20000, and every byte of s and goal is in the inclusive range 97..122 (ASCII lowercase). -/
  theorem spec_12 (s goal : Slice U8)
      (hs_len : 1 ≤ s.val.length) (hg_len : 1 ≤ goal.val.length)
      (hs_max : s.val.length ≤ 20000) (hg_max : goal.val.length ≤ 20000)
      (hs_low : IsAsciiLower s) (hg_low : IsAsciiLower goal) :
      ∀ r : Bool, buddy_strings s goal = ok r → s.val = goal.val →
        (∀ i j, i < j → j < s.val.length → byte s i ≠ byte s j) → r = false := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (s goal : Slice U8)
        (hs_len : 1 ≤ s.val.length) (hg_len : 1 ≤ goal.val.length)
        (hs_max : s.val.length ≤ 20000) (hg_max : goal.val.length ≤ 20000)
        (hs_low : IsAsciiLower s) (hg_low : IsAsciiLower goal), ∀ r : Bool, buddy_strings s goal = ok r → s.val = goal.val →
          (∀ i j, i < j → j < s.val.length → byte s i ≠ byte s j) → r = false) := by
    sorry

  /-- Whenever the function returns a result r, r = true if and only if ((s[0] = s[1]) and (goal[0] = s[0]) and (goal[1] = s[1])) or ((s[0] != s[1]) and (goal[0] = s[1]) and (goal[1] = s[0])).
    Preconditions: len(s) = 2, len(goal) = 2, and every byte of s and goal is in the inclusive range 97..122 (ASCII lowercase). -/
  theorem spec_13 (s goal : Slice U8)
      (hs_len : s.val.length = 2) (hg_len : goal.val.length = 2)
      (hs_low : IsAsciiLower s) (hg_low : IsAsciiLower goal) :
      ∀ r : Bool, buddy_strings s goal = ok r →
        (r = true ↔
          (byte s 0 = byte s 1 ∧ byte goal 0 = byte s 0 ∧ byte goal 1 = byte s 1) ∨
            (byte s 0 ≠ byte s 1 ∧ byte goal 0 = byte s 1 ∧
              byte goal 1 = byte s 0)) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (s goal : Slice U8)
        (hs_len : s.val.length = 2) (hg_len : goal.val.length = 2)
        (hs_low : IsAsciiLower s) (hg_low : IsAsciiLower goal), ∀ r : Bool, buddy_strings s goal = ok r →
          (r = true ↔
            (byte s 0 = byte s 1 ∧ byte goal 0 = byte s 0 ∧ byte goal 1 = byte s 1) ∨
              (byte s 0 ≠ byte s 1 ∧ byte goal 0 = byte s 1 ∧
                byte goal 1 = byte s 0))) := by
    sorry

  end AegisSpec.BuddyStrings
