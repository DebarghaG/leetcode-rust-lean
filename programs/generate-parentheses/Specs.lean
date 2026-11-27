import Aegis.GenerateParenthesis.Code.Funs

/-!
# Specifications of `Aegis.GenerateParenthesis.generate_parenthesis`

LeetCode problem `generate-parentheses`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.GenerateParenthesis

  def countByte (s : List Std.U8) (c : Nat) : Nat :=
    s.countP (fun b => decide (b.val = c))

  def countMatches (r : List (alloc.vec.Vec Std.U8)) (s : List Std.U8) : Nat :=
    r.countP (fun v => decide (v.val = s))

  def isWellFormed (s : List Std.U8) (n : Nat) : Prop :=
    s.length = 2 * n ∧
      (∀ b ∈ s, b.val = 40 ∨ b.val = 41) ∧
      (∀ k, k ≤ 2 * n → countByte (s.take k) 41 ≤ countByte (s.take k) 40) ∧
      countByte s 40 = n ∧
      countByte s 41 = n

  def catalan (n : Nat) : Nat :=
    (2 * n).factorial / (n.factorial * (n + 1).factorial)

  /-- Call a byte sequence s a well-formed parentheses string with n pairs if: len(s) = 2*n; every byte of s is either 40 (the ASCII code of '(') or 41 (the ASCII code of ')'); for every k with 0 <= k <= 2*n, the number of indices j with 0 <= j < k and s[j] = 40 is at least the number of indices j with 0 <= j < k and s[j] = 41; and s contains exactly n bytes equal to 40 and exactly n bytes equal to 41. Whenever the function returns a result r, for every byte sequence s, the number of indices i with 0 <= i < len(r) and r[i] = s is exactly 1 if s is a well-formed parentheses string with n pairs, and exactly 0 otherwise.
    Preconditions: 1 <= n <= 8. -/
  theorem spec_1 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 8) :
      ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
        Aegis.GenerateParenthesis.generate_parenthesis n = ok r →
        ∀ s : List Std.U8,
          (isWellFormed s n.val.toNat → countMatches r.val s = 1) ∧
            (¬ isWellFormed s n.val.toNat → countMatches r.val s = 0) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 8), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
          Aegis.GenerateParenthesis.generate_parenthesis n = ok r →
          ∀ s : List Std.U8,
            (isWellFormed s n.val.toNat → countMatches r.val s = 1) ∧
              (¬ isWellFormed s n.val.toNat → countMatches r.val s = 0)) := by
    sorry

  /-- Whenever the function returns a result r, every entry r[i] with 0 <= i < len(r) is a well-formed parentheses string with n pairs: len(r[i]) = 2*n, every byte r[i][j] is 40 or 41, every prefix of r[i] has at least as many 40s as 41s, and r[i] contains exactly n 40s and exactly n 41s.
    Preconditions: 1 <= n <= 8. -/
  theorem spec_2 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 8) :
      ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
        Aegis.GenerateParenthesis.generate_parenthesis n = ok r →
        ∀ (i : Nat) (hi : i < r.val.length), isWellFormed r.val[i].val n.val.toNat := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 8), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
          Aegis.GenerateParenthesis.generate_parenthesis n = ok r →
          ∀ (i : Nat) (hi : i < r.val.length), isWellFormed r.val[i].val n.val.toNat) := by
    sorry

  /-- Whenever the function returns a result r, for every byte sequence s that is a well-formed parentheses string with n pairs, there exists an index i with 0 <= i < len(r) such that r[i] = s.
    Preconditions: 1 <= n <= 8. -/
  theorem spec_3 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 8) :
      ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
        Aegis.GenerateParenthesis.generate_parenthesis n = ok r →
        ∀ s : List Std.U8, isWellFormed s n.val.toNat →
          ∃ (i : Nat) (_ : i < r.val.length), r.val[i].val = s := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 8), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
          Aegis.GenerateParenthesis.generate_parenthesis n = ok r →
          ∀ s : List Std.U8, isWellFormed s n.val.toNat →
            ∃ (i : Nat) (_ : i < r.val.length), r.val[i].val = s) := by
    sorry

  /-- Whenever the function returns a result r, the entries of r are pairwise distinct: for all i and j with 0 <= i < j < len(r), r[i] != r[j].
    Preconditions: 1 <= n <= 8. -/
  theorem spec_4 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 8) :
      ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
        Aegis.GenerateParenthesis.generate_parenthesis n = ok r →
        ∀ (i : Nat) (hi : i < r.val.length) (j : Nat) (hj : j < r.val.length),
          i < j → r.val[i].val ≠ r.val[j].val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 8), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
          Aegis.GenerateParenthesis.generate_parenthesis n = ok r →
          ∀ (i : Nat) (hi : i < r.val.length) (j : Nat) (hj : j < r.val.length),
            i < j → r.val[i].val ≠ r.val[j].val) := by
    sorry

  /-- Whenever the function returns a result r, len(r) = C_n, where C_n = (2*n)! / (n! * (n+1)!) is the n-th Catalan number (equivalently, the number of well-formed parentheses strings with n pairs).
    Preconditions: 1 <= n <= 8. -/
  theorem spec_5 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 8) :
      ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
        Aegis.GenerateParenthesis.generate_parenthesis n = ok r →
        r.val.length = catalan n.val.toNat := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 8), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
          Aegis.GenerateParenthesis.generate_parenthesis n = ok r →
          r.val.length = catalan n.val.toNat) := by
    sorry

  /-- Whenever the function returns a result r, every entry r[i] with 0 <= i < len(r) has length exactly 2*n.
    Preconditions: 1 <= n <= 8. -/
  theorem spec_6 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 8) :
      ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
        Aegis.GenerateParenthesis.generate_parenthesis n = ok r →
        ∀ (i : Nat) (hi : i < r.val.length), r.val[i].val.length = 2 * n.val.toNat := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 8), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
          Aegis.GenerateParenthesis.generate_parenthesis n = ok r →
          ∀ (i : Nat) (hi : i < r.val.length), r.val[i].val.length = 2 * n.val.toNat) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(r) and every j with 0 <= j < len(r[i]), the byte r[i][j] is either 40 or 41.
    Preconditions: 1 <= n <= 8. -/
  theorem spec_7 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 8) :
      ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
        Aegis.GenerateParenthesis.generate_parenthesis n = ok r →
        ∀ (i : Nat) (hi : i < r.val.length), ∀ (j : Nat) (hj : j < r.val[i].val.length),
          r.val[i].val[j].val = 40 ∨ r.val[i].val[j].val = 41 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 8), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
          Aegis.GenerateParenthesis.generate_parenthesis n = ok r →
          ∀ (i : Nat) (hi : i < r.val.length), ∀ (j : Nat) (hj : j < r.val[i].val.length),
            r.val[i].val[j].val = 40 ∨ r.val[i].val[j].val = 41) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(r), the number of indices j with 0 <= j < len(r[i]) and r[i][j] = 40 is exactly n, and the number of such indices with r[i][j] = 41 is exactly n.
    Preconditions: 1 <= n <= 8. -/
  theorem spec_8 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 8) :
      ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
        Aegis.GenerateParenthesis.generate_parenthesis n = ok r →
        ∀ (i : Nat) (hi : i < r.val.length),
          countByte r.val[i].val 40 = n.val.toNat ∧
            countByte r.val[i].val 41 = n.val.toNat := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 8), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
          Aegis.GenerateParenthesis.generate_parenthesis n = ok r →
          ∀ (i : Nat) (hi : i < r.val.length),
            countByte r.val[i].val 40 = n.val.toNat ∧
              countByte r.val[i].val 41 = n.val.toNat) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(r) and every k with 0 <= k <= len(r[i]), among the first k bytes of r[i], the number of bytes equal to 40 is at least the number of bytes equal to 41.
    Preconditions: 1 <= n <= 8. -/
  theorem spec_9 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 8) :
      ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
        Aegis.GenerateParenthesis.generate_parenthesis n = ok r →
        ∀ (i : Nat) (hi : i < r.val.length), ∀ k, k ≤ r.val[i].val.length →
          countByte (r.val[i].val.take k) 41 ≤ countByte (r.val[i].val.take k) 40 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 8), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
          Aegis.GenerateParenthesis.generate_parenthesis n = ok r →
          ∀ (i : Nat) (hi : i < r.val.length), ∀ k, k ≤ r.val[i].val.length →
            countByte (r.val[i].val.take k) 41 ≤ countByte (r.val[i].val.take k) 40) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(r), len(r[i]) >= 2, r[i][0] = 40, and r[i][len(r[i]) - 1] = 41.
    Preconditions: 1 <= n <= 8. -/
  theorem spec_10 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 8) :
      ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
        Aegis.GenerateParenthesis.generate_parenthesis n = ok r →
        ∀ (i : Nat) (hi : i < r.val.length),
          2 ≤ r.val[i].val.length ∧
            r.val[i].val.head? = some 40#u8 ∧
            r.val[i].val.getLast? = some 41#u8 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 8), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
          Aegis.GenerateParenthesis.generate_parenthesis n = ok r →
          ∀ (i : Nat) (hi : i < r.val.length),
            2 ≤ r.val[i].val.length ∧
              r.val[i].val.head? = some 40#u8 ∧
              r.val[i].val.getLast? = some 41#u8) := by
    sorry

  /-- For every n with 1 <= n <= 8, the function returns a result r; it does not fail, panic, overflow, or go out of bounds.
    Preconditions: 1 <= n <= 8. -/
  theorem spec_11 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 8) :
      ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
        Aegis.GenerateParenthesis.generate_parenthesis n = ok r := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 8), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
          Aegis.GenerateParenthesis.generate_parenthesis n = ok r) := by
    sorry

  end AegisSpec.GenerateParenthesis
