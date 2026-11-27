import Aegis.ScoreOfParentheses.Code.Funs

/-!
# Specifications of `Aegis.ScoreOfParentheses.score_of_parentheses`

LeetCode problem `score-of-parentheses`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.ScoreOfParentheses

  namespace AegisSpec.ScoreOfParentheses

  def byteAt (l : List Std.U8) (i : ℕ) : ℕ := (l.getD i ⟨0⟩).val

  def countByte (l : List Std.U8) (n : ℕ) : ℕ := (l.filter (fun b => b.val == n)).length

  def openPrefix (l : List Std.U8) (k : ℕ) : ℕ := countByte (l.take k) 40

  def closePrefix (l : List Std.U8) (k : ℕ) : ℕ := countByte (l.take k) 41

  def countOpen (l : List Std.U8) : ℕ := openPrefix l l.length

  def countClose (l : List Std.U8) : ℕ := closePrefix l l.length

  def onlyParens (l : List Std.U8) : Prop :=
    ∀ i, i < l.length → byteAt l i = 40 ∨ byteAt l i = 41

  def Balanced (l : List Std.U8) : Prop :=
    countOpen l = countClose l ∧
      ∀ k ∈ List.range (l.length + 1), closePrefix l k ≤ openPrefix l k

  def isBalancedPrefix (l : List Std.U8) (k : ℕ) : Bool :=
    (openPrefix l k == closePrefix l k) &&
      (List.range (k + 1)).all (fun j => closePrefix l j ≤ openPrefix l j)

  def firstBalancedPrefix (l : List Std.U8) : Option ℕ :=
    (List.range (l.length + 1)).find?
      (fun k => decide (1 ≤ k) && isBalancedPrefix l k)

  def scoreAux (l : List Std.U8) : ℕ → ℤ
    | 0 => 0
    | fuel + 1 =>
      match l with
      | [] => 0
      | _ =>
        match firstBalancedPrefix l with
        | none => 0
        | some k =>
          if k = 2 then 1 + scoreAux (l.drop k) fuel
          else 2 * scoreAux (((l.take k).drop 1).dropLast) fuel + scoreAux (l.drop k) fuel

  def score (l : List Std.U8) : ℤ := scoreAux l l.length

  def depthAt (l : List Std.U8) (i : ℕ) : ℤ :=
    (openPrefix l i : ℤ) - (closePrefix l i : ℤ)

  def witnessSum (l : List Std.U8) : ℤ :=
    (List.range l.length).foldl
      (fun acc i =>
        if i + 1 < l.length ∧ byteAt l i = 40 ∧ byteAt l (i + 1) = 41 then
          acc + (2 : ℤ) ^ (depthAt l i).toNat
        else acc)
      0

  def mirror (l : List Std.U8) : List Std.U8 :=
    l.reverse.map (fun b => if b.val = 40 then ⟨41⟩ else if b.val = 41 then ⟨40⟩ else b)

  /-- Whenever the function returns a result r, r = score(s), where score is defined on balanced parentheses strings by: score(empty) = 0; for nonempty x, let p be the shortest nonempty balanced prefix of x and write x = p ++ rest (rest may be empty); if p = '()' then score(x) = 1 + score(rest); otherwise p has length at least 4 and p = '(' ++ t ++ ')' for a nonempty balanced t, and score(x) = 2 * score(t) + score(rest).
    Preconditions: s is a byte slice whose length is between 2 and 50 inclusive; every byte s[i] (0 <= i < len(s)) is either 40 (ASCII '(') or 41 (ASCII ')'); and s is balanced: the number of '(' bytes in s equals the number of ')' bytes in s, and for every k with 0 <= k <= len(s), the number of '(' bytes among s[0],...,s[k-1] is at least the number of ')' bytes among s[0],...,s[k-1] (the prefix is empty when k=0). -/
  theorem spec_1 (s : Slice Std.U8)
      (hlen_ge : 2 ≤ s.val.length) (hlen_le : s.val.length ≤ 50)
      (hbytes : onlyParens s.val) (hbal : Balanced s.val) :
      ∀ r, score_of_parentheses s = ok r → r.val = score s.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_ge : 2 ≤ s.val.length) (hlen_le : s.val.length ≤ 50)
        (hbytes : onlyParens s.val) (hbal : Balanced s.val), ∀ r, score_of_parentheses s = ok r → r.val = score s.val) := by
    sorry

  /-- The function returns a result r (that is, it does not fail, panic, overflow, or access an index outside 0..len(s)-1) for every s satisfying the preconditions.
    Preconditions: s is a byte slice whose length is between 2 and 50 inclusive; every byte of s is either 40 (ASCII '(') or 41 (ASCII ')'); and s is balanced: total '(' count equals total ')' count and every prefix has at least as many '(' as ')'. -/
  theorem spec_2 (s : Slice Std.U8)
      (hlen_ge : 2 ≤ s.val.length) (hlen_le : s.val.length ≤ 50)
      (hbytes : onlyParens s.val) (hbal : Balanced s.val) :
      ∃ r, score_of_parentheses s = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_ge : 2 ≤ s.val.length) (hlen_le : s.val.length ≤ 50)
        (hbytes : onlyParens s.val) (hbal : Balanced s.val), ∃ r, score_of_parentheses s = ok r) := by
    sorry

  /-- Whenever the function returns a result r, r >= n, where n is the number of '(' bytes in s (equivalently n = len(s)/2 is the number of matched pairs).
    Preconditions: s is a byte slice whose length is between 2 and 50 inclusive; every byte of s is either 40 (ASCII '(') or 41 (ASCII ')'); and s is balanced: total '(' count equals total ')' count and every prefix has at least as many '(' as ')'. -/
  theorem spec_3 (s : Slice Std.U8)
      (hlen_ge : 2 ≤ s.val.length) (hlen_le : s.val.length ≤ 50)
      (hbytes : onlyParens s.val) (hbal : Balanced s.val) :
      ∀ r, score_of_parentheses s = ok r → (countOpen s.val : ℤ) ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_ge : 2 ≤ s.val.length) (hlen_le : s.val.length ≤ 50)
        (hbytes : onlyParens s.val) (hbal : Balanced s.val), ∀ r, score_of_parentheses s = ok r → (countOpen s.val : ℤ) ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r <= 2 to the power (n-1), where n is the number of '(' bytes in s.
    Preconditions: s is a byte slice whose length is between 2 and 50 inclusive; every byte of s is either 40 (ASCII '(') or 41 (ASCII ')'); and s is balanced: total '(' count equals total ')' count and every prefix has at least as many '(' as ')'. -/
  theorem spec_4 (s : Slice Std.U8)
      (hlen_ge : 2 ≤ s.val.length) (hlen_le : s.val.length ≤ 50)
      (hbytes : onlyParens s.val) (hbal : Balanced s.val) :
      ∀ r, score_of_parentheses s = ok r → r.val ≤ (2 : ℤ) ^ (countOpen s.val - 1) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_ge : 2 ≤ s.val.length) (hlen_le : s.val.length ≤ 50)
        (hbytes : onlyParens s.val) (hbal : Balanced s.val), ∀ r, score_of_parentheses s = ok r → r.val ≤ (2 : ℤ) ^ (countOpen s.val - 1)) := by
    sorry

  /-- Whenever the function returns a result r, r = n.
    Preconditions: s is balanced and, for some integer n with 1 <= n <= 25, len(s) = 2*n and for every i with 0 <= i < n, s[2*i] = '(' and s[2*i+1] = ')'. Thus s is '()' repeated n times. -/
  theorem spec_5 (s : Slice Std.U8) (n : ℕ)
      (hn_ge : 1 ≤ n) (hn_le : n ≤ 25)
      (hlen : s.val.length = 2 * n)
      (hopen : ∀ i, i < n → byteAt s.val (2 * i) = 40)
      (hclose : ∀ i, i < n → byteAt s.val (2 * i + 1) = 41)
      (hbal : Balanced s.val) :
      ∀ r, score_of_parentheses s = ok r → r.val = (n : ℤ) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s : Slice Std.U8) (n : ℕ)
        (hn_ge : 1 ≤ n) (hn_le : n ≤ 25)
        (hlen : s.val.length = 2 * n)
        (hopen : ∀ i, i < n → byteAt s.val (2 * i) = 40)
        (hclose : ∀ i, i < n → byteAt s.val (2 * i + 1) = 41)
        (hbal : Balanced s.val), ∀ r, score_of_parentheses s = ok r → r.val = (n : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, r = 2 to the power (n-1).
    Preconditions: s is balanced and, for some integer n with 1 <= n <= 25, len(s) = 2*n, s[i] = '(' for every i with 0 <= i < n, and s[i] = ')' for every i with n <= i < 2*n. Thus s = '(' repeated n times followed by ')' repeated n times. -/
  theorem spec_6 (s : Slice Std.U8) (n : ℕ)
      (hn_ge : 1 ≤ n) (hn_le : n ≤ 25)
      (hlen : s.val.length = 2 * n)
      (hopen : ∀ i, i < n → byteAt s.val i = 40)
      (hclose : ∀ i, n ≤ i → i < 2 * n → byteAt s.val i = 41)
      (hbal : Balanced s.val) :
      ∀ r, score_of_parentheses s = ok r → r.val = (2 : ℤ) ^ (n - 1) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s : Slice Std.U8) (n : ℕ)
        (hn_ge : 1 ≤ n) (hn_le : n ≤ 25)
        (hlen : s.val.length = 2 * n)
        (hopen : ∀ i, i < n → byteAt s.val i = 40)
        (hclose : ∀ i, n ≤ i → i < 2 * n → byteAt s.val i = 41)
        (hbal : Balanced s.val), ∀ r, score_of_parentheses s = ok r → r.val = (2 : ℤ) ^ (n - 1)) := by
    sorry

  /-- Whenever the function returns r on s, r_u on u, and r_v on v, it holds that r = r_u + r_v.
    Preconditions: s satisfies the main preconditions. There is an integer k with 0 < k < len(s) such that u is the prefix s[0..k) (bytes at indices 0 through k-1) and v is the suffix s[k..len(s)) (bytes at indices k through len(s)-1); both u and v are nonempty and consist only of bytes 40 ('(') and 41 (')'), and both are balanced parentheses strings. -/
  theorem spec_7 (s u v : Slice Std.U8) (k : ℕ)
      (hlen_ge : 2 ≤ s.val.length) (hlen_le : s.val.length ≤ 50)
      (hbytes : onlyParens s.val) (hbal : Balanced s.val)
      (hk_pos : 0 < k) (hk_lt : k < s.val.length)
      (hu : u.val = s.val.take k) (hv : v.val = s.val.drop k)
      (hu_ne : u.val ≠ []) (hv_ne : v.val ≠ [])
      (hu_bytes : onlyParens u.val) (hv_bytes : onlyParens v.val)
      (hu_bal : Balanced u.val) (hv_bal : Balanced v.val) :
      ∀ r ru rv, score_of_parentheses s = ok r →
        score_of_parentheses u = ok ru →
        score_of_parentheses v = ok rv → r.val = ru.val + rv.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s u v : Slice Std.U8) (k : ℕ)
        (hlen_ge : 2 ≤ s.val.length) (hlen_le : s.val.length ≤ 50)
        (hbytes : onlyParens s.val) (hbal : Balanced s.val)
        (hk_pos : 0 < k) (hk_lt : k < s.val.length)
        (hu : u.val = s.val.take k) (hv : v.val = s.val.drop k)
        (hu_ne : u.val ≠ []) (hv_ne : v.val ≠ [])
        (hu_bytes : onlyParens u.val) (hv_bytes : onlyParens v.val)
        (hu_bal : Balanced u.val) (hv_bal : Balanced v.val), ∀ r ru rv, score_of_parentheses s = ok r →
          score_of_parentheses u = ok ru →
          score_of_parentheses v = ok rv → r.val = ru.val + rv.val) := by
    sorry

  /-- Whenever the function returns r on s and r_t on t, it holds that r = 2 * r_t.
    Preconditions: s satisfies the main preconditions, and there is a nonempty balanced parentheses string t such that s = '(' ++ t ++ ')'; thus s is a single primitive balanced block with nonempty inside. -/
  theorem spec_8 (s t : Slice Std.U8)
      (hlen_ge : 2 ≤ s.val.length) (hlen_le : s.val.length ≤ 50)
      (hbytes : onlyParens s.val) (hbal : Balanced s.val)
      (ht_ne : t.val ≠ [])
      (ht_bytes : onlyParens t.val) (ht_bal : Balanced t.val)
      (hs : s.val = (⟨40⟩ :: (t.val ++ [⟨41⟩]))) :
      ∀ r rt, score_of_parentheses s = ok r → score_of_parentheses t = ok rt →
        r.val = 2 * rt.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s t : Slice Std.U8)
        (hlen_ge : 2 ≤ s.val.length) (hlen_le : s.val.length ≤ 50)
        (hbytes : onlyParens s.val) (hbal : Balanced s.val)
        (ht_ne : t.val ≠ [])
        (ht_bytes : onlyParens t.val) (ht_bal : Balanced t.val)
        (hs : s.val = (⟨40⟩ :: (t.val ++ [⟨41⟩]))), ∀ r rt, score_of_parentheses s = ok r → score_of_parentheses t = ok rt →
          r.val = 2 * rt.val) := by
    sorry

  /-- Whenever the function returns r on s and r' on mirror(s), it holds that r = r'.
    Preconditions: s satisfies the main preconditions. Define mirror(s) to be the byte array of length len(s) with mirror(s)[i] = '(' if s[len(s)-1-i] = ')' and mirror(s)[i] = ')' if s[len(s)-1-i] = '(' (indices are 0-based). Then mirror(s) is also balanced and has the same length. -/
  theorem spec_9 (s m : Slice Std.U8)
      (hlen_ge : 2 ≤ s.val.length) (hlen_le : s.val.length ≤ 50)
      (hbytes : onlyParens s.val) (hbal : Balanced s.val)
      (hm : m.val = mirror s.val) :
      ∀ r r', score_of_parentheses s = ok r → score_of_parentheses m = ok r' →
        r.val = r'.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s m : Slice Std.U8)
        (hlen_ge : 2 ≤ s.val.length) (hlen_le : s.val.length ≤ 50)
        (hbytes : onlyParens s.val) (hbal : Balanced s.val)
        (hm : m.val = mirror s.val), ∀ r r', score_of_parentheses s = ok r → score_of_parentheses m = ok r' →
          r.val = r'.val) := by
    sorry

  /-- Whenever the function returns r on s and r' on t, it holds that r = r'.
    Preconditions: s satisfies the main preconditions, and s = u ++ v where u and v are nonempty balanced parentheses strings. Let t = v ++ u. -/
  theorem spec_10 (s u v t : Slice Std.U8)
      (hlen_ge : 2 ≤ s.val.length) (hlen_le : s.val.length ≤ 50)
      (hbytes : onlyParens s.val) (hbal : Balanced s.val)
      (hu_ne : u.val ≠ []) (hv_ne : v.val ≠ [])
      (hu_bytes : onlyParens u.val) (hv_bytes : onlyParens v.val)
      (hu_bal : Balanced u.val) (hv_bal : Balanced v.val)
      (hs : s.val = u.val ++ v.val) (ht : t.val = v.val ++ u.val) :
      ∀ r r', score_of_parentheses s = ok r → score_of_parentheses t = ok r' →
        r.val = r'.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (s u v t : Slice Std.U8)
        (hlen_ge : 2 ≤ s.val.length) (hlen_le : s.val.length ≤ 50)
        (hbytes : onlyParens s.val) (hbal : Balanced s.val)
        (hu_ne : u.val ≠ []) (hv_ne : v.val ≠ [])
        (hu_bytes : onlyParens u.val) (hv_bytes : onlyParens v.val)
        (hu_bal : Balanced u.val) (hv_bal : Balanced v.val)
        (hs : s.val = u.val ++ v.val) (ht : t.val = v.val ++ u.val), ∀ r r', score_of_parentheses s = ok r → score_of_parentheses t = ok r' →
          r.val = r'.val) := by
    sorry

  /-- Whenever the function returns a result r, r = the sum over all indices i with 0 <= i < len(s)-1, s[i] = '(' and s[i+1] = ')' of 2 to the power d(i), where d(i) is the number of '(' bytes among s[0],...,s[i-1] minus the number of ')' bytes among s[0],...,s[i-1].
    Preconditions: s satisfies the main preconditions. -/
  theorem spec_11 (s : Slice Std.U8)
      (hlen_ge : 2 ≤ s.val.length) (hlen_le : s.val.length ≤ 50)
      (hbytes : onlyParens s.val) (hbal : Balanced s.val) :
      ∀ r, score_of_parentheses s = ok r → r.val = witnessSum s.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_ge : 2 ≤ s.val.length) (hlen_le : s.val.length ≤ 50)
        (hbytes : onlyParens s.val) (hbal : Balanced s.val), ∀ r, score_of_parentheses s = ok r → r.val = witnessSum s.val) := by
    sorry

  end AegisSpec.ScoreOfParentheses
