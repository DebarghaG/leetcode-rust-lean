import Aegis.LongestValidParentheses.Code.Funs

/-!
# Specifications of `Aegis.LongestValidParentheses.longest_valid_parentheses`

LeetCode problem `longest-valid-parentheses`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.LongestValidParentheses

  open Aegis.LongestValidParentheses (longest_valid_parentheses)

  def bytes (s : Slice Std.U8) : List Std.U8 := Slice.val s

  def slen (s : Slice Std.U8) : Nat := (Slice.val s).length

  def byte (s : Slice Std.U8) (i : Nat) : Option Nat := (bytes s)[i]?.map (fun b => b.val)

  def isOpenByte (s : Slice Std.U8) (i : Nat) : Prop := byte s i = some 40

  def isCloseByte (s : Slice Std.U8) (i : Nat) : Prop := byte s i = some 41

  def subBytes (s : Slice Std.U8) (l u : Nat) : List Std.U8 :=
    ((bytes s).drop l).take (u - l)

  def step (b : Std.U8) : Int := if b.val = 40 then 1 else if b.val = 41 then -1 else 0

  def balance (bs : List Std.U8) : Int := (bs.map step).sum

  def prefixBalances (bs : List Std.U8) : List Int := bs.scanl (fun acc b => acc + step b) 0

  def validParens (bs : List Std.U8) : Prop :=
    balance bs = 0 ∧ ∀ b ∈ prefixBalances bs, 0 ≤ b

  def validInterval (s : Slice Std.U8) (l u : Nat) : Prop :=
    l ≤ u ∧ u ≤ slen s ∧ validParens (subBytes s l u)

  def IsMaxValidLen (s : Slice Std.U8) (lo hi : Nat) (r : Int) : Prop :=
    (∃ l u, lo ≤ l ∧ u ≤ hi ∧ validInterval s l u ∧ r = ((u - l : Nat) : Int)) ∧
      (∀ l u, lo ≤ l → u ≤ hi → validInterval s l u → ((u - l : Nat) : Int) ≤ r)

  def countByte (s : Slice Std.U8) (c : Nat) : Nat :=
    ((bytes s).filter (fun b => b.val == c)).length

  def openCount (s : Slice Std.U8) : Nat := countByte s 40

  def closeCount (s : Slice Std.U8) : Nat := countByte s 41

  lemma slen_eq_len (s : Slice Std.U8) : slen s = (Slice.len s).val := by
    simp [slen]

  lemma validInterval_self (s : Slice Std.U8) (l : Nat) (h : l ≤ slen s) :
      validInterval s l l := by
    refine ⟨le_rfl, h, ?_⟩
    simp [validParens, subBytes, balance, prefixBalances]

  /-- The function returns a result r and r is exactly the maximum length of a valid contiguous substring of s: (1) there exist integers l and u with 0 <= l <= u <= len(s) such that s[l..u) is valid and u - l = r, and (2) for every l and u with 0 <= l <= u <= len(s), if s[l..u) is valid then u - l <= r. Here a contiguous substring s[l..u) is valid iff it contains equally many '(' and ')' and every prefix s[l..t) with l <= t <= u contains at least as many '(' as ')'; the empty substring is valid.
    Preconditions: 0 <= len(s) <= 30000, and for every i with 0 <= i < len(s), s[i] is the ASCII byte for '(' or ')'. -/
  theorem spec_1 (s : Slice Std.U8)
      (h_len : slen s ≤ 30000)
      (h_bytes : ∀ i, i < slen s → isOpenByte s i ∨ isCloseByte s i) :
      ∃ r : Std.I64, longest_valid_parentheses s = ok r ∧ IsMaxValidLen s 0 (slen s) r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s : Slice Std.U8)
        (h_len : slen s ≤ 30000)
        (h_bytes : ∀ i, i < slen s → isOpenByte s i ∨ isCloseByte s i), ∃ r : Std.I64, longest_valid_parentheses s = ok r ∧ IsMaxValidLen s 0 (slen s) r.val) := by
    sorry

  /-- The function returns a result r (it does not fail) for every input s satisfying the preconditions.
    Preconditions: 0 <= len(s) <= 30000, and for every i with 0 <= i < len(s), s[i] is the ASCII byte for '(' or ')'. -/
  theorem spec_2 (s : Slice Std.U8)
      (h_len : slen s ≤ 30000)
      (h_bytes : ∀ i, i < slen s → isOpenByte s i ∨ isCloseByte s i) :
      ∃ r : Std.I64, longest_valid_parentheses s = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s : Slice Std.U8)
        (h_len : slen s ≤ 30000)
        (h_bytes : ∀ i, i < slen s → isOpenByte s i ∨ isCloseByte s i), ∃ r : Std.I64, longest_valid_parentheses s = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r <= len(s).
    Preconditions: 0 <= len(s) <= 30000, and for every i with 0 <= i < len(s), s[i] is the ASCII byte for '(' or ')'. -/
  theorem spec_3 (s : Slice Std.U8)
      (h_len : slen s ≤ 30000)
      (h_bytes : ∀ i, i < slen s → isOpenByte s i ∨ isCloseByte s i) :
      ∀ r : Std.I64, longest_valid_parentheses s = ok r →
        0 ≤ r.val ∧ r.val ≤ (slen s : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s : Slice Std.U8)
        (h_len : slen s ≤ 30000)
        (h_bytes : ∀ i, i < slen s → isOpenByte s i ∨ isCloseByte s i), ∀ r : Std.I64, longest_valid_parentheses s = ok r →
          0 ≤ r.val ∧ r.val ≤ (slen s : Int)) := by
    sorry

  /-- Whenever the function returns a result r, r is even, meaning there exists an integer k such that r = 2*k.
    Preconditions: 0 <= len(s) <= 30000, and for every i with 0 <= i < len(s), s[i] is the ASCII byte for '(' or ')'. -/
  theorem spec_4 (s : Slice Std.U8)
      (h_len : slen s ≤ 30000)
      (h_bytes : ∀ i, i < slen s → isOpenByte s i ∨ isCloseByte s i) :
      ∀ r : Std.I64, longest_valid_parentheses s = ok r → ∃ k : Int, r.val = 2 * k := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s : Slice Std.U8)
        (h_len : slen s ≤ 30000)
        (h_bytes : ∀ i, i < slen s → isOpenByte s i ∨ isCloseByte s i), ∀ r : Std.I64, longest_valid_parentheses s = ok r → ∃ k : Int, r.val = 2 * k) := by
    sorry

  /-- Whenever the function returns a result r and the whole string s[0..len(s)) is valid (it has equally many '(' and ')' and every prefix s[0..t) with 0 <= t <= len(s) has at least as many '(' as ')'), r = len(s).
    Preconditions: 0 <= len(s) <= 30000, and for every i with 0 <= i < len(s), s[i] is the ASCII byte for '(' or ')'. -/
  theorem spec_5 (s : Slice Std.U8)
      (h_len : slen s ≤ 30000)
      (h_bytes : ∀ i, i < slen s → isOpenByte s i ∨ isCloseByte s i) :
      ∀ r : Std.I64, longest_valid_parentheses s = ok r →
        validInterval s 0 (slen s) → r.val = (slen s : Int) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s : Slice Std.U8)
        (h_len : slen s ≤ 30000)
        (h_bytes : ∀ i, i < slen s → isOpenByte s i ∨ isCloseByte s i), ∀ r : Std.I64, longest_valid_parentheses s = ok r →
          validInterval s 0 (slen s) → r.val = (slen s : Int)) := by
    sorry

  /-- Whenever the function returns a result r, there exist integers l and u with 0 <= l <= u <= len(s) such that s[l..u) is valid (it has equally many '(' and ')' and every prefix s[l..t) with l <= t <= u has at least as many '(' as ')') and u - l = r.
    Preconditions: 0 <= len(s) <= 30000, and for every i with 0 <= i < len(s), s[i] is the ASCII byte for '(' or ')'. -/
  theorem spec_6 (s : Slice Std.U8)
      (h_len : slen s ≤ 30000)
      (h_bytes : ∀ i, i < slen s → isOpenByte s i ∨ isCloseByte s i) :
      ∀ r : Std.I64, longest_valid_parentheses s = ok r →
        ∃ l u : Nat, validInterval s l u ∧ r.val = ((u - l : Nat) : Int) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s : Slice Std.U8)
        (h_len : slen s ≤ 30000)
        (h_bytes : ∀ i, i < slen s → isOpenByte s i ∨ isCloseByte s i), ∀ r : Std.I64, longest_valid_parentheses s = ok r →
          ∃ l u : Nat, validInterval s l u ∧ r.val = ((u - l : Nat) : Int)) := by
    sorry

  /-- Whenever the function returns a result r, for every l and u with 0 <= l <= u <= len(s), if s[l..u) is valid (it has equally many '(' and ')' and every prefix s[l..t) with l <= t <= u has at least as many '(' as ')'), then u - l <= r.
    Preconditions: 0 <= len(s) <= 30000, and for every i with 0 <= i < len(s), s[i] is the ASCII byte for '(' or ')'. -/
  theorem spec_7 (s : Slice Std.U8)
      (h_len : slen s ≤ 30000)
      (h_bytes : ∀ i, i < slen s → isOpenByte s i ∨ isCloseByte s i) :
      ∀ r : Std.I64, longest_valid_parentheses s = ok r →
        ∀ l u : Nat, validInterval s l u → ((u - l : Nat) : Int) ≤ r.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s : Slice Std.U8)
        (h_len : slen s ≤ 30000)
        (h_bytes : ∀ i, i < slen s → isOpenByte s i ∨ isCloseByte s i), ∀ r : Std.I64, longest_valid_parentheses s = ok r →
          ∀ l u : Nat, validInterval s l u → ((u - l : Nat) : Int) ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 if and only if there do not exist integers l and u with 0 <= l < u <= len(s) such that s[l..u) is valid (it has equally many '(' and ')' and every prefix s[l..t) with l <= t <= u has at least as many '(' as ')').
    Preconditions: 0 <= len(s) <= 30000, and for every i with 0 <= i < len(s), s[i] is the ASCII byte for '(' or ')'. -/
  theorem spec_8 (s : Slice Std.U8)
      (h_len : slen s ≤ 30000)
      (h_bytes : ∀ i, i < slen s → isOpenByte s i ∨ isCloseByte s i) :
      ∀ r : Std.I64, longest_valid_parentheses s = ok r →
        (r.val = 0 ↔ ¬ ∃ l u : Nat, l < u ∧ validInterval s l u) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s : Slice Std.U8)
        (h_len : slen s ≤ 30000)
        (h_bytes : ∀ i, i < slen s → isOpenByte s i ∨ isCloseByte s i), ∀ r : Std.I64, longest_valid_parentheses s = ok r →
          (r.val = 0 ↔ ¬ ∃ l u : Nat, l < u ∧ validInterval s l u)) := by
    sorry

  /-- Whenever the function returns a result r and there exists an index i with 0 <= i and i+1 < len(s) such that s[i] is '(' and s[i+1] is ')', we have r >= 2.
    Preconditions: 0 <= len(s) <= 30000, and for every i with 0 <= i < len(s), s[i] is the ASCII byte for '(' or ')'. -/
  theorem spec_9 (s : Slice Std.U8)
      (h_len : slen s ≤ 30000)
      (h_bytes : ∀ i, i < slen s → isOpenByte s i ∨ isCloseByte s i) :
      ∀ r : Std.I64, longest_valid_parentheses s = ok r →
        (∃ i : Nat, i + 1 < slen s ∧ isOpenByte s i ∧ isCloseByte s (i + 1)) →
        2 ≤ r.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s : Slice Std.U8)
        (h_len : slen s ≤ 30000)
        (h_bytes : ∀ i, i < slen s → isOpenByte s i ∨ isCloseByte s i), ∀ r : Std.I64, longest_valid_parentheses s = ok r →
          (∃ i : Nat, i + 1 < slen s ∧ isOpenByte s i ∧ isCloseByte s (i + 1)) →
          2 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r and there is no index i with 0 <= i and i+1 < len(s) such that s[i] is '(' and s[i+1] is ')', we have r = 0.
    Preconditions: 0 <= len(s) <= 30000, and for every i with 0 <= i < len(s), s[i] is the ASCII byte for '(' or ')'. -/
  theorem spec_10 (s : Slice Std.U8)
      (h_len : slen s ≤ 30000)
      (h_bytes : ∀ i, i < slen s → isOpenByte s i ∨ isCloseByte s i) :
      ∀ r : Std.I64, longest_valid_parentheses s = ok r →
        (¬ ∃ i : Nat, i + 1 < slen s ∧ isOpenByte s i ∧ isCloseByte s (i + 1)) →
        r.val = 0 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (s : Slice Std.U8)
        (h_len : slen s ≤ 30000)
        (h_bytes : ∀ i, i < slen s → isOpenByte s i ∨ isCloseByte s i), ∀ r : Std.I64, longest_valid_parentheses s = ok r →
          (¬ ∃ i : Nat, i + 1 < slen s ∧ isOpenByte s i ∧ isCloseByte s (i + 1)) →
          r.val = 0) := by
    sorry

  /-- Whenever the function returns a result r, r <= 2 * min(open_count, close_count), where open_count is the number of indices i with 0 <= i < len(s) and s[i] is '(', and close_count is the number of indices i with 0 <= i < len(s) and s[i] is ')'.
    Preconditions: 0 <= len(s) <= 30000, and for every i with 0 <= i < len(s), s[i] is the ASCII byte for '(' or ')'. -/
  theorem spec_11 (s : Slice Std.U8)
      (h_len : slen s ≤ 30000)
      (h_bytes : ∀ i, i < slen s → isOpenByte s i ∨ isCloseByte s i) :
      ∀ r : Std.I64, longest_valid_parentheses s = ok r →
        r.val ≤ 2 * ((min (openCount s) (closeCount s) : Nat) : Int) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (s : Slice Std.U8)
        (h_len : slen s ≤ 30000)
        (h_bytes : ∀ i, i < slen s → isOpenByte s i ∨ isCloseByte s i), ∀ r : Std.I64, longest_valid_parentheses s = ok r →
          r.val ≤ 2 * ((min (openCount s) (closeCount s) : Nat) : Int)) := by
    sorry

  /-- Whenever the function returns a result r and len(s) > 0 and s[0] is ')', r is the maximum length of a valid contiguous substring of the suffix s[1..len(s)); here a contiguous substring of that suffix is valid iff it has equally many '(' and ')' and every prefix of it has at least as many '(' as ')', and the maximum is 0 if only the empty substring is valid.
    Preconditions: 0 <= len(s) <= 30000, and for every i with 0 <= i < len(s), s[i] is the ASCII byte for '(' or ')'. -/
  theorem spec_12 (s : Slice Std.U8)
      (h_len : slen s ≤ 30000)
      (h_bytes : ∀ i, i < slen s → isOpenByte s i ∨ isCloseByte s i) :
      ∀ r : Std.I64, longest_valid_parentheses s = ok r →
        0 < slen s → isCloseByte s 0 → IsMaxValidLen s 1 (slen s) r.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (s : Slice Std.U8)
        (h_len : slen s ≤ 30000)
        (h_bytes : ∀ i, i < slen s → isOpenByte s i ∨ isCloseByte s i), ∀ r : Std.I64, longest_valid_parentheses s = ok r →
          0 < slen s → isCloseByte s 0 → IsMaxValidLen s 1 (slen s) r.val) := by
    sorry

  /-- Whenever the function returns a result r and len(s) > 0 and s[len(s)-1] is '(', r is the maximum length of a valid contiguous substring of the prefix s[0..len(s)-1); here a contiguous substring of that prefix is valid iff it has equally many '(' and ')' and every prefix of it has at least as many '(' as ')', and the maximum is 0 if only the empty substring is valid.
    Preconditions: 0 <= len(s) <= 30000, and for every i with 0 <= i < len(s), s[i] is the ASCII byte for '(' or ')'. -/
  theorem spec_13 (s : Slice Std.U8)
      (h_len : slen s ≤ 30000)
      (h_bytes : ∀ i, i < slen s → isOpenByte s i ∨ isCloseByte s i) :
      ∀ r : Std.I64, longest_valid_parentheses s = ok r →
        0 < slen s → isOpenByte s (slen s - 1) → IsMaxValidLen s 0 (slen s - 1) r.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (s : Slice Std.U8)
        (h_len : slen s ≤ 30000)
        (h_bytes : ∀ i, i < slen s → isOpenByte s i ∨ isCloseByte s i), ∀ r : Std.I64, longest_valid_parentheses s = ok r →
          0 < slen s → isOpenByte s (slen s - 1) → IsMaxValidLen s 0 (slen s - 1) r.val) := by
    sorry

  end AegisSpec.LongestValidParentheses
