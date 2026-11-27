import Aegis.AddMinimum.Code.Funs

/-!
# Specifications of `Aegis.AddMinimum.add_minimum`

LeetCode problem `minimum-additions-to-make-valid-string`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.AddMinimum

  open Aegis.AddMinimum (add_minimum)

  def slen (word : Slice Std.U8) : Nat := word.val.length

  def byteAt (word : Slice Std.U8) (i : Nat) : Option Nat := (word.val[i]?).map (fun b => b.val)

  def content (word : Slice Std.U8) : List Nat := word.val.map (fun b => b.val)

  def V (k : Nat) : List Nat := (List.range (3 * k)).map (fun j => 97 + j % 3)

  def IsSubseq (p v : List Nat) : Prop :=
    ∃ idx : Nat → Nat,
      (∀ t, t < p.length → idx t < v.length) ∧
      (∀ t, t + 1 < p.length → idx t < idx (t + 1)) ∧
      (∀ t, t < p.length → p[t]? = v[idx t]?)

  def countByte (word : Slice Std.U8) (x : Nat) : Nat :=
    (word.val.filter (fun b => b.val = x)).length

  /-- For each integer k >= 0, let V_k be the byte sequence of length 3k defined by V_k[j] = 97 + (j mod 3) for 0 <= j < 3k, so V_k is (abc)^k with byte values 97, 98, 99. Say that word is a subsequence of V_k if there exist indices 0 <= j_0 < j_1 < ... < j_{n-1} < 3k such that word[t] = V_k[j_t] for every t with 0 <= t < n. Whenever add_minimum word returns a result r, the integer r is the minimum of the set {3k - n | k >= 0 and word is a subsequence of V_k}.
    Preconditions: Let n = len(word). The slice satisfies 1 <= n <= 50, and for every i with 0 <= i < n, word[i] is 97 ('a'), 98 ('b'), or 99 ('c'). -/
  theorem spec_1 (word : Slice Std.U8)
      (hn1 : 1 ≤ slen word) (hn50 : slen word ≤ 50)
      (hbytes : ∀ i, i < slen word →
        byteAt word i = some 97 ∨ byteAt word i = some 98 ∨ byteAt word i = some 99) :
      ∀ r : Std.I64, add_minimum word = ok r →
        IsLeast
          {m : Int | ∃ k : Nat, m = 3 * (k : Int) - (slen word : Int) ∧
            IsSubseq (content word) (V k)}
          r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (word : Slice Std.U8)
        (hn1 : 1 ≤ slen word) (hn50 : slen word ≤ 50)
        (hbytes : ∀ i, i < slen word →
          byteAt word i = some 97 ∨ byteAt word i = some 98 ∨ byteAt word i = some 99), ∀ r : Std.I64, add_minimum word = ok r →
          IsLeast
            {m : Int | ∃ k : Nat, m = 3 * (k : Int) - (slen word : Int) ∧
              IsSubseq (content word) (V k)}
            r.val) := by
    sorry

  /-- The call add_minimum word returns a result r and does not fail (no arithmetic overflow, panic, or out-of-bounds access).
    Preconditions: Let n = len(word). The slice satisfies 1 <= n <= 50, and for every i with 0 <= i < n, word[i] is 97 ('a'), 98 ('b'), or 99 ('c'). -/
  theorem spec_2 (word : Slice Std.U8)
      (hn1 : 1 ≤ slen word) (hn50 : slen word ≤ 50)
      (hbytes : ∀ i, i < slen word →
        byteAt word i = some 97 ∨ byteAt word i = some 98 ∨ byteAt word i = some 99) :
      ∃ r : Std.I64, add_minimum word = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (word : Slice Std.U8)
        (hn1 : 1 ≤ slen word) (hn50 : slen word ≤ 50)
        (hbytes : ∀ i, i < slen word →
          byteAt word i = some 97 ∨ byteAt word i = some 98 ∨ byteAt word i = some 99), ∃ r : Std.I64, add_minimum word = ok r) := by
    sorry

  /-- Whenever add_minimum word returns a result r, we have 0 <= r.
    Preconditions: Let n = len(word). The slice satisfies 1 <= n <= 50, and for every i with 0 <= i < n, word[i] is 97 ('a'), 98 ('b'), or 99 ('c'). -/
  theorem spec_3 (word : Slice Std.U8)
      (hn1 : 1 ≤ slen word) (hn50 : slen word ≤ 50)
      (hbytes : ∀ i, i < slen word →
        byteAt word i = some 97 ∨ byteAt word i = some 98 ∨ byteAt word i = some 99) :
      ∀ r : Std.I64, add_minimum word = ok r → 0 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (word : Slice Std.U8)
        (hn1 : 1 ≤ slen word) (hn50 : slen word ≤ 50)
        (hbytes : ∀ i, i < slen word →
          byteAt word i = some 97 ∨ byteAt word i = some 98 ∨ byteAt word i = some 99), ∀ r : Std.I64, add_minimum word = ok r → 0 ≤ r.val) := by
    sorry

  /-- Whenever add_minimum word returns a result r, we have r <= 2 * n.
    Preconditions: Let n = len(word). The slice satisfies 1 <= n <= 50, and for every i with 0 <= i < n, word[i] is 97 ('a'), 98 ('b'), or 99 ('c'). -/
  theorem spec_4 (word : Slice Std.U8)
      (hn1 : 1 ≤ slen word) (hn50 : slen word ≤ 50)
      (hbytes : ∀ i, i < slen word →
        byteAt word i = some 97 ∨ byteAt word i = some 98 ∨ byteAt word i = some 99) :
      ∀ r : Std.I64, add_minimum word = ok r → r.val ≤ 2 * (slen word : Int) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (word : Slice Std.U8)
        (hn1 : 1 ≤ slen word) (hn50 : slen word ≤ 50)
        (hbytes : ∀ i, i < slen word →
          byteAt word i = some 97 ∨ byteAt word i = some 98 ∨ byteAt word i = some 99), ∀ r : Std.I64, add_minimum word = ok r → r.val ≤ 2 * (slen word : Int)) := by
    sorry

  /-- Whenever add_minimum word returns a result r, the integer n + r is divisible by 3; equivalently, there exists an integer k >= 0 such that n + r = 3k.
    Preconditions: Let n = len(word). The slice satisfies 1 <= n <= 50, and for every i with 0 <= i < n, word[i] is 97 ('a'), 98 ('b'), or 99 ('c'). -/
  theorem spec_5 (word : Slice Std.U8)
      (hn1 : 1 ≤ slen word) (hn50 : slen word ≤ 50)
      (hbytes : ∀ i, i < slen word →
        byteAt word i = some 97 ∨ byteAt word i = some 98 ∨ byteAt word i = some 99) :
      ∀ r : Std.I64, add_minimum word = ok r →
        ∃ k : Int, 0 ≤ k ∧ (slen word : Int) + r.val = 3 * k := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (word : Slice Std.U8)
        (hn1 : 1 ≤ slen word) (hn50 : slen word ≤ 50)
        (hbytes : ∀ i, i < slen word →
          byteAt word i = some 97 ∨ byteAt word i = some 98 ∨ byteAt word i = some 99), ∀ r : Std.I64, add_minimum word = ok r →
          ∃ k : Int, 0 ≤ k ∧ (slen word : Int) + r.val = 3 * k) := by
    sorry

  /-- Whenever add_minimum word returns a result r, we have r >= 3 * max(c97, c98, c99) - n.
    Preconditions: Let n = len(word). The slice satisfies 1 <= n <= 50, and for every i with 0 <= i < n, word[i] is 97 ('a'), 98 ('b'), or 99 ('c'). Let c97 be the number of indices i with 0 <= i < n and word[i] = 97, let c98 be the number of indices i with word[i] = 98, and let c99 be the number of indices i with word[i] = 99. -/
  theorem spec_6 (word : Slice Std.U8)
      (hn1 : 1 ≤ slen word) (hn50 : slen word ≤ 50)
      (hbytes : ∀ i, i < slen word →
        byteAt word i = some 97 ∨ byteAt word i = some 98 ∨ byteAt word i = some 99) :
      ∀ r : Std.I64, add_minimum word = ok r →
        3 * ((max (countByte word 97) (max (countByte word 98) (countByte word 99)) : Nat) : Int)
          - (slen word : Int) ≤ r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (word : Slice Std.U8)
        (hn1 : 1 ≤ slen word) (hn50 : slen word ≤ 50)
        (hbytes : ∀ i, i < slen word →
          byteAt word i = some 97 ∨ byteAt word i = some 98 ∨ byteAt word i = some 99), ∀ r : Std.I64, add_minimum word = ok r →
          3 * ((max (countByte word 97) (max (countByte word 98) (countByte word 99)) : Nat) : Int)
            - (slen word : Int) ≤ r.val) := by
    sorry

  /-- Whenever add_minimum word returns a result r, r = 0 if and only if n is divisible by 3 and word[i] = 97 + (i mod 3) for every i with 0 <= i < n.
    Preconditions: Let n = len(word). The slice satisfies 1 <= n <= 50, and for every i with 0 <= i < n, word[i] is 97 ('a'), 98 ('b'), or 99 ('c'). -/
  theorem spec_7 (word : Slice Std.U8)
      (hn1 : 1 ≤ slen word) (hn50 : slen word ≤ 50)
      (hbytes : ∀ i, i < slen word →
        byteAt word i = some 97 ∨ byteAt word i = some 98 ∨ byteAt word i = some 99) :
      ∀ r : Std.I64, add_minimum word = ok r →
        (r.val = 0 ↔ (∃ k : Nat, slen word = 3 * k) ∧
          ∀ i, i < slen word → byteAt word i = some (97 + i % 3)) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (word : Slice Std.U8)
        (hn1 : 1 ≤ slen word) (hn50 : slen word ≤ 50)
        (hbytes : ∀ i, i < slen word →
          byteAt word i = some 97 ∨ byteAt word i = some 98 ∨ byteAt word i = some 99), ∀ r : Std.I64, add_minimum word = ok r →
          (r.val = 0 ↔ (∃ k : Nat, slen word = 3 * k) ∧
            ∀ i, i < slen word → byteAt word i = some (97 + i % 3))) := by
    sorry

  /-- Whenever add_minimum word returns a result r, we have r = 2 * n.
    Preconditions: Let n = len(word). The slice satisfies 1 <= n <= 50, and for every i with 0 <= i < n, word[i] is 97 ('a'), 98 ('b'), or 99 ('c'). Additionally, there exists x in {97,98,99} such that word[i] = x for every i with 0 <= i < n. -/
  theorem spec_8 (word : Slice Std.U8)
      (hn1 : 1 ≤ slen word) (hn50 : slen word ≤ 50)
      (hbytes : ∀ i, i < slen word →
        byteAt word i = some 97 ∨ byteAt word i = some 98 ∨ byteAt word i = some 99)
      (hconst : ∃ x : Nat, (x = 97 ∨ x = 98 ∨ x = 99) ∧
        ∀ i, i < slen word → byteAt word i = some x) :
      ∀ r : Std.I64, add_minimum word = ok r → r.val = 2 * (slen word : Int) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (word : Slice Std.U8)
        (hn1 : 1 ≤ slen word) (hn50 : slen word ≤ 50)
        (hbytes : ∀ i, i < slen word →
          byteAt word i = some 97 ∨ byteAt word i = some 98 ∨ byteAt word i = some 99)
        (hconst : ∃ x : Nat, (x = 97 ∨ x = 98 ∨ x = 99) ∧
          ∀ i, i < slen word → byteAt word i = some x), ∀ r : Std.I64, add_minimum word = ok r → r.val = 2 * (slen word : Int)) := by
    sorry

  /-- Whenever add_minimum word returns a result r, we have r = 3 - n.
    Preconditions: Let n = len(word). The slice satisfies 1 <= n <= 50, and for every i with 0 <= i < n, word[i] is 97 ('a'), 98 ('b'), or 99 ('c'). Also, word is a subsequence of the byte sequence (97,98,99). -/
  theorem spec_9 (word : Slice Std.U8)
      (hn1 : 1 ≤ slen word) (hn50 : slen word ≤ 50)
      (hbytes : ∀ i, i < slen word →
        byteAt word i = some 97 ∨ byteAt word i = some 98 ∨ byteAt word i = some 99)
      (hsub : IsSubseq (content word) [97, 98, 99]) :
      ∀ r : Std.I64, add_minimum word = ok r → r.val = 3 - (slen word : Int) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (word : Slice Std.U8)
        (hn1 : 1 ≤ slen word) (hn50 : slen word ≤ 50)
        (hbytes : ∀ i, i < slen word →
          byteAt word i = some 97 ∨ byteAt word i = some 98 ∨ byteAt word i = some 99)
        (hsub : IsSubseq (content word) [97, 98, 99]), ∀ r : Std.I64, add_minimum word = ok r → r.val = 3 - (slen word : Int)) := by
    sorry

  /-- Whenever add_minimum word returns a result r, we have r = 6 - n.
    Preconditions: Let n = len(word). The slice satisfies 1 <= n <= 50, and for every i with 0 <= i < n, word[i] is 97 ('a'), 98 ('b'), or 99 ('c'). Let V_1 = (97,98,99) and V_2 = (97,98,99,97,98,99). Also, word is a subsequence of V_2 and word is not a subsequence of V_1. -/
  theorem spec_10 (word : Slice Std.U8)
      (hn1 : 1 ≤ slen word) (hn50 : slen word ≤ 50)
      (hbytes : ∀ i, i < slen word →
        byteAt word i = some 97 ∨ byteAt word i = some 98 ∨ byteAt word i = some 99)
      (hsub2 : IsSubseq (content word) [97, 98, 99, 97, 98, 99])
      (hsub1 : ¬ IsSubseq (content word) [97, 98, 99]) :
      ∀ r : Std.I64, add_minimum word = ok r → r.val = 6 - (slen word : Int) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (word : Slice Std.U8)
        (hn1 : 1 ≤ slen word) (hn50 : slen word ≤ 50)
        (hbytes : ∀ i, i < slen word →
          byteAt word i = some 97 ∨ byteAt word i = some 98 ∨ byteAt word i = some 99)
        (hsub2 : IsSubseq (content word) [97, 98, 99, 97, 98, 99])
        (hsub1 : ¬ IsSubseq (content word) [97, 98, 99]), ∀ r : Std.I64, add_minimum word = ok r → r.val = 6 - (slen word : Int)) := by
    sorry

  /-- Whenever add_minimum word returns a result r, we have r = 2 * n - 3.
    Preconditions: Let n = len(word). The slice satisfies 1 <= n <= 50, and for every i with 0 <= i < n, word[i] is 97 ('a'), 98 ('b'), or 99 ('c'). Additionally, there exist integers i >= 1 and j >= 1 such that n = i + j, word[t] = 97 for every t with 0 <= t < i, and word[t] = 98 for every t with i <= t < i + j. -/
  theorem spec_11 (word : Slice Std.U8)
      (hn1 : 1 ≤ slen word) (hn50 : slen word ≤ 50)
      (hbytes : ∀ i, i < slen word →
        byteAt word i = some 97 ∨ byteAt word i = some 98 ∨ byteAt word i = some 99)
      (hab : ∃ i j : Nat, 1 ≤ i ∧ 1 ≤ j ∧ slen word = i + j ∧
        (∀ t, t < i → byteAt word t = some 97) ∧
        (∀ t, i ≤ t → t < i + j → byteAt word t = some 98)) :
      ∀ r : Std.I64, add_minimum word = ok r → r.val = 2 * (slen word : Int) - 3 := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (word : Slice Std.U8)
        (hn1 : 1 ≤ slen word) (hn50 : slen word ≤ 50)
        (hbytes : ∀ i, i < slen word →
          byteAt word i = some 97 ∨ byteAt word i = some 98 ∨ byteAt word i = some 99)
        (hab : ∃ i j : Nat, 1 ≤ i ∧ 1 ≤ j ∧ slen word = i + j ∧
          (∀ t, t < i → byteAt word t = some 97) ∧
          (∀ t, i ≤ t → t < i + j → byteAt word t = some 98)), ∀ r : Std.I64, add_minimum word = ok r → r.val = 2 * (slen word : Int) - 3) := by
    sorry

  /-- Whenever add_minimum word returns a result r, we have r = 2 * n - 6.
    Preconditions: Let n = len(word). The slice satisfies 1 <= n <= 50, and for every i with 0 <= i < n, word[i] is 97 ('a'), 98 ('b'), or 99 ('c'). Additionally, there exist integers i >= 1, j >= 1, and l >= 1 such that n = i + j + l, word[t] = 97 for every t with 0 <= t < i, word[t] = 98 for every t with i <= t < i + j, and word[t] = 99 for every t with i + j <= t < n. -/
  theorem spec_12 (word : Slice Std.U8)
      (hn1 : 1 ≤ slen word) (hn50 : slen word ≤ 50)
      (hbytes : ∀ i, i < slen word →
        byteAt word i = some 97 ∨ byteAt word i = some 98 ∨ byteAt word i = some 99)
      (habc : ∃ i j l : Nat, 1 ≤ i ∧ 1 ≤ j ∧ 1 ≤ l ∧ slen word = i + j + l ∧
        (∀ t, t < i → byteAt word t = some 97) ∧
        (∀ t, i ≤ t → t < i + j → byteAt word t = some 98) ∧
        (∀ t, i + j ≤ t → t < slen word → byteAt word t = some 99)) :
      ∀ r : Std.I64, add_minimum word = ok r → r.val = 2 * (slen word : Int) - 6 := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (word : Slice Std.U8)
        (hn1 : 1 ≤ slen word) (hn50 : slen word ≤ 50)
        (hbytes : ∀ i, i < slen word →
          byteAt word i = some 97 ∨ byteAt word i = some 98 ∨ byteAt word i = some 99)
        (habc : ∃ i j l : Nat, 1 ≤ i ∧ 1 ≤ j ∧ 1 ≤ l ∧ slen word = i + j + l ∧
          (∀ t, t < i → byteAt word t = some 97) ∧
          (∀ t, i ≤ t → t < i + j → byteAt word t = some 98) ∧
          (∀ t, i + j ≤ t → t < slen word → byteAt word t = some 99)), ∀ r : Std.I64, add_minimum word = ok r → r.val = 2 * (slen word : Int) - 6) := by
    sorry

  /-- Whenever add_minimum word returns a result r, r = 2 * n if and only if word is not a subsequence of V_{n-1}.
    Preconditions: Let n = len(word). The slice satisfies 1 <= n <= 50, and for every i with 0 <= i < n, word[i] is 97 ('a'), 98 ('b'), or 99 ('c'). For m >= 0, let V_m be the byte sequence of length 3m with V_m[j] = 97 + (j mod 3) for 0 <= j < 3m. -/
  theorem spec_13 (word : Slice Std.U8)
      (hn1 : 1 ≤ slen word) (hn50 : slen word ≤ 50)
      (hbytes : ∀ i, i < slen word →
        byteAt word i = some 97 ∨ byteAt word i = some 98 ∨ byteAt word i = some 99) :
      ∀ r : Std.I64, add_minimum word = ok r →
        (r.val = 2 * (slen word : Int) ↔
          ¬ IsSubseq (content word) (V (slen word - 1))) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (word : Slice Std.U8)
        (hn1 : 1 ≤ slen word) (hn50 : slen word ≤ 50)
        (hbytes : ∀ i, i < slen word →
          byteAt word i = some 97 ∨ byteAt word i = some 98 ∨ byteAt word i = some 99), ∀ r : Std.I64, add_minimum word = ok r →
          (r.val = 2 * (slen word : Int) ↔
            ¬ IsSubseq (content word) (V (slen word - 1)))) := by
    sorry

  end AegisSpec.AddMinimum
