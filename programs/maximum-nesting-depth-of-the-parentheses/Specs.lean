import Aegis.MaxDepth.Code.Funs

/-!
# Specifications of `Aegis.MaxDepth.max_depth`

LeetCode problem `maximum-nesting-depth-of-the-parentheses`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxDepth

def openByte : Nat := 40

def closeByte : Nat := 41

def numByte (l : List Std.U8) (b : Nat) : Nat :=
  (l.filter (fun c => c.val = b)).length

def numByteUpto (s : Slice Std.U8) (b : Nat) (k : Nat) : Nat :=
  numByte (s.val.take k) b

def bal (s : Slice Std.U8) (k : Nat) : Int :=
  (numByteUpto s openByte k : Int) - (numByteUpto s closeByte k : Int)

def IsValidParens (s : Slice Std.U8) : Prop :=
  (∀ k : Nat, k ≤ s.val.length → numByteUpto s closeByte k ≤ numByteUpto s openByte k) ∧
    numByteUpto s closeByte s.val.length = numByteUpto s openByte s.val.length

def IsMaxBal (s : Slice Std.U8) (r : Int) : Prop :=
  (∀ k : Nat, k ≤ s.val.length → bal s k ≤ r) ∧
    ∃ k : Nat, k ≤ s.val.length ∧ bal s k = r

def Occurs (s : Slice Std.U8) (b : Nat) : Prop :=
  ∃ i : Fin s.val.length, (s.val.get i).val = b

def parensOnly (s : Slice Std.U8) : List Std.U8 :=
  s.val.filter (fun c => c.val = openByte ∨ c.val = closeByte)

/-- The function returns a result r, and r is the nesting depth of s: if for each k with 0 <= k <= len(s) we define bal(k) to be the number of i with 0 <= i < k and s[i] = '(' minus the number of i with 0 <= i < k and s[i] = ')', then r = max { bal(k) | 0 <= k <= len(s) }.
  Preconditions: len(s) >= 1 and len(s) <= 100. The bytes of s that are '(' or ')' form a valid parentheses sequence: for every k with 0 <= k <= len(s), the number of ')' among s[0],...,s[k-1] is at most the number of '(' among them, and for k = len(s) the two counts are equal. -/
theorem spec_1 (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen100 : s.val.length ≤ 100)
    (hvalid : IsValidParens s) :
    ∃ r : Std.I64, Aegis.MaxDepth.max_depth s = ok r ∧ IsMaxBal s r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen100 : s.val.length ≤ 100)
    (hvalid : IsValidParens s), ∃ r : Std.I64, Aegis.MaxDepth.max_depth s = ok r ∧ IsMaxBal s r.val) := by
  sorry

/-- The function returns a result r; it does not panic, go out of bounds, overflow, or otherwise fail.
  Preconditions: len(s) >= 1 and len(s) <= 100. The bytes of s that are '(' or ')' form a valid parentheses sequence: for every k with 0 <= k <= len(s), the number of ')' among s[0],...,s[k-1] is at most the number of '(' among them, and for k = len(s) the two counts are equal. -/
theorem spec_2 (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen100 : s.val.length ≤ 100)
    (hvalid : IsValidParens s) :
    ∃ r : Std.I64, Aegis.MaxDepth.max_depth s = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen100 : s.val.length ≤ 100)
    (hvalid : IsValidParens s), ∃ r : Std.I64, Aegis.MaxDepth.max_depth s = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r.
  Preconditions: len(s) >= 1 and len(s) <= 100. The bytes of s that are '(' or ')' form a valid parentheses sequence: for every k with 0 <= k <= len(s), the number of ')' among s[0],...,s[k-1] is at most the number of '(' among them, and for k = len(s) the two counts are equal. -/
theorem spec_3 (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen100 : s.val.length ≤ 100)
    (hvalid : IsValidParens s) :
    ∀ r : Std.I64, Aegis.MaxDepth.max_depth s = ok r → 0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen100 : s.val.length ≤ 100)
    (hvalid : IsValidParens s), ∀ r : Std.I64, Aegis.MaxDepth.max_depth s = ok r → 0 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= floor(len(s) / 2).
  Preconditions: len(s) >= 1 and len(s) <= 100. The bytes of s that are '(' or ')' form a valid parentheses sequence: for every k with 0 <= k <= len(s), the number of ')' among s[0],...,s[k-1] is at most the number of '(' among them, and for k = len(s) the two counts are equal. -/
theorem spec_4 (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen100 : s.val.length ≤ 100)
    (hvalid : IsValidParens s) :
    ∀ r : Std.I64, Aegis.MaxDepth.max_depth s = ok r → r.val ≤ ((s.val.length / 2 : Nat) : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen100 : s.val.length ≤ 100)
    (hvalid : IsValidParens s), ∀ r : Std.I64, Aegis.MaxDepth.max_depth s = ok r → r.val ≤ ((s.val.length / 2 : Nat) : Int)) := by
  sorry

/-- Whenever the function returns a result r, r <= the number of indices i with 0 <= i < len(s) and s[i] = '('.
  Preconditions: len(s) >= 1 and len(s) <= 100. The bytes of s that are '(' or ')' form a valid parentheses sequence: for every k with 0 <= k <= len(s), the number of ')' among s[0],...,s[k-1] is at most the number of '(' among them, and for k = len(s) the two counts are equal. -/
theorem spec_5 (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen100 : s.val.length ≤ 100)
    (hvalid : IsValidParens s) :
    ∀ r : Std.I64, Aegis.MaxDepth.max_depth s = ok r → r.val ≤ (numByte s.val openByte : Int) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen100 : s.val.length ≤ 100)
    (hvalid : IsValidParens s), ∀ r : Std.I64, Aegis.MaxDepth.max_depth s = ok r → r.val ≤ (numByte s.val openByte : Int)) := by
  sorry

/-- Whenever the function returns a result r, there exists an index k with 0 <= k <= len(s) such that bal(k) = r, where bal(k) is the number of i with 0 <= i < k and s[i] = '(' minus the number of i with 0 <= i < k and s[i] = ')'.
  Preconditions: len(s) >= 1 and len(s) <= 100. The bytes of s that are '(' or ')' form a valid parentheses sequence: for every k with 0 <= k <= len(s), the number of ')' among s[0],...,s[k-1] is at most the number of '(' among them, and for k = len(s) the two counts are equal. -/
theorem spec_6 (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen100 : s.val.length ≤ 100)
    (hvalid : IsValidParens s) :
    ∀ r : Std.I64, Aegis.MaxDepth.max_depth s = ok r →
      ∃ k : Nat, k ≤ s.val.length ∧ bal s k = r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen100 : s.val.length ≤ 100)
    (hvalid : IsValidParens s), ∀ r : Std.I64, Aegis.MaxDepth.max_depth s = ok r →
      ∃ k : Nat, k ≤ s.val.length ∧ bal s k = r.val) := by
  sorry

/-- Whenever the function returns a result r, for every k with 0 <= k <= len(s), bal(k) <= r, where bal(k) is the number of i with 0 <= i < k and s[i] = '(' minus the number of i with 0 <= i < k and s[i] = ')'.
  Preconditions: len(s) >= 1 and len(s) <= 100. The bytes of s that are '(' or ')' form a valid parentheses sequence: for every k with 0 <= k <= len(s), the number of ')' among s[0],...,s[k-1] is at most the number of '(' among them, and for k = len(s) the two counts are equal. -/
theorem spec_7 (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen100 : s.val.length ≤ 100)
    (hvalid : IsValidParens s) :
    ∀ r : Std.I64, Aegis.MaxDepth.max_depth s = ok r →
      ∀ k : Nat, k ≤ s.val.length → bal s k ≤ r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen100 : s.val.length ≤ 100)
    (hvalid : IsValidParens s), ∀ r : Std.I64, Aegis.MaxDepth.max_depth s = ok r →
      ∀ k : Nat, k ≤ s.val.length → bal s k ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r = 0.
  Preconditions: len(s) >= 1 and len(s) <= 100. The bytes of s that are '(' or ')' form a valid parentheses sequence: for every k with 0 <= k <= len(s), the number of ')' among s[0],...,s[k-1] is at most the number of '(' among them, and for k = len(s) the two counts are equal. Additionally, s contains no byte equal to '(' and no byte equal to ')'. -/
theorem spec_8 (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen100 : s.val.length ≤ 100)
    (hvalid : IsValidParens s)
    (hnoOpen : numByte s.val openByte = 0) (hnoClose : numByte s.val closeByte = 0) :
    ∀ r : Std.I64, Aegis.MaxDepth.max_depth s = ok r → r.val = 0 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen100 : s.val.length ≤ 100)
    (hvalid : IsValidParens s)
    (hnoOpen : numByte s.val openByte = 0) (hnoClose : numByte s.val closeByte = 0), ∀ r : Std.I64, Aegis.MaxDepth.max_depth s = ok r → r.val = 0) := by
  sorry

/-- Whenever the function returns a result r, r = 1.
  Preconditions: len(s) >= 1 and len(s) <= 100. The bytes of s that are '(' or ')' form a valid parentheses sequence: for every k with 0 <= k <= len(s), the number of ')' among s[0],...,s[k-1] is at most the number of '(' among them, and for k = len(s) the two counts are equal. Additionally, s contains exactly one byte equal to '(' and exactly one byte equal to ')'. -/
theorem spec_9 (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen100 : s.val.length ≤ 100)
    (hvalid : IsValidParens s)
    (honeOpen : numByte s.val openByte = 1) (honeClose : numByte s.val closeByte = 1) :
    ∀ r : Std.I64, Aegis.MaxDepth.max_depth s = ok r → r.val = 1 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen100 : s.val.length ≤ 100)
    (hvalid : IsValidParens s)
    (honeOpen : numByte s.val openByte = 1) (honeClose : numByte s.val closeByte = 1), ∀ r : Std.I64, Aegis.MaxDepth.max_depth s = ok r → r.val = 1) := by
  sorry

/-- Whenever max_depth(s) returns r_s and max_depth(t) returns r_t, r_s = r_t.
  Preconditions: Both s and t are byte slices with 1 <= len(s) <= 100 and 1 <= len(t) <= 100, and each has its '(' and ')' bytes forming a valid parentheses sequence as in spec_1. Deleting all bytes other than '(' and ')' from s gives exactly the same byte sequence as deleting all bytes other than '(' and ')' from t. -/
theorem spec_10 (s t : Slice Std.U8)
    (hs1 : 1 ≤ s.val.length) (hs100 : s.val.length ≤ 100)
    (ht1 : 1 ≤ t.val.length) (ht100 : t.val.length ≤ 100)
    (hsvalid : IsValidParens s) (htvalid : IsValidParens t)
    (hsame : parensOnly s = parensOnly t) :
    ∀ r_s r_t : Std.I64,
      Aegis.MaxDepth.max_depth s = ok r_s → Aegis.MaxDepth.max_depth t = ok r_t →
        r_s.val = r_t.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s t : Slice Std.U8)
    (hs1 : 1 ≤ s.val.length) (hs100 : s.val.length ≤ 100)
    (ht1 : 1 ≤ t.val.length) (ht100 : t.val.length ≤ 100)
    (hsvalid : IsValidParens s) (htvalid : IsValidParens t)
    (hsame : parensOnly s = parensOnly t), ∀ r_s r_t : Std.I64,
      Aegis.MaxDepth.max_depth s = ok r_s → Aegis.MaxDepth.max_depth t = ok r_t →
        r_s.val = r_t.val) := by
  sorry

/-- Whenever max_depth(s) returns r_s, max_depth(t) returns r_t, and max_depth(u) returns r_u, we have r_u = max(r_s, r_t).
  Preconditions: s and t are byte slices with 1 <= len(s) <= 100, 1 <= len(t) <= 100, len(s) + len(t) <= 100, and each has its '(' and ')' bytes forming a valid parentheses sequence as in spec_1. Let u be the byte slice obtained by concatenating s followed by t. -/
theorem spec_11 (s t u : Slice Std.U8)
    (hs1 : 1 ≤ s.val.length) (hs100 : s.val.length ≤ 100)
    (ht1 : 1 ≤ t.val.length) (ht100 : t.val.length ≤ 100)
    (hlen : s.val.length + t.val.length ≤ 100)
    (hsvalid : IsValidParens s) (htvalid : IsValidParens t)
    (hu : u.val = s.val ++ t.val) :
    ∀ r_s r_t r_u : Std.I64,
      Aegis.MaxDepth.max_depth s = ok r_s → Aegis.MaxDepth.max_depth t = ok r_t →
        Aegis.MaxDepth.max_depth u = ok r_u → r_u.val = max r_s.val r_t.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s t u : Slice Std.U8)
    (hs1 : 1 ≤ s.val.length) (hs100 : s.val.length ≤ 100)
    (ht1 : 1 ≤ t.val.length) (ht100 : t.val.length ≤ 100)
    (hlen : s.val.length + t.val.length ≤ 100)
    (hsvalid : IsValidParens s) (htvalid : IsValidParens t)
    (hu : u.val = s.val ++ t.val), ∀ r_s r_t r_u : Std.I64,
      Aegis.MaxDepth.max_depth s = ok r_s → Aegis.MaxDepth.max_depth t = ok r_t →
        Aegis.MaxDepth.max_depth u = ok r_u → r_u.val = max r_s.val r_t.val) := by
  sorry

/-- Whenever max_depth(s) returns r_s and max_depth(t) returns r_t, r_s = r_t + 1.
  Preconditions: s is a byte slice with 1 <= len(s) <= 100 whose '(' and ')' bytes form a valid parentheses sequence as in spec_1, with s[0] = '(' and s[len(s)-1] = ')'. Let t be the slice obtained by deleting the first and last bytes of s; assume t is nonempty and also has its '(' and ')' bytes forming a valid parentheses sequence. -/
theorem spec_12 (s t : Slice Std.U8) (c d : Std.U8)
    (hs1 : 1 ≤ s.val.length) (hs100 : s.val.length ≤ 100)
    (ht1 : 1 ≤ t.val.length) (ht100 : t.val.length ≤ 100)
    (hsvalid : IsValidParens s) (htvalid : IsValidParens t)
    (hfirst : s.val.head? = some c) (hlast : s.val.getLast? = some d)
    (hc : c.val = openByte) (hd : d.val = closeByte)
    (hshape : s.val = c :: (t.val ++ [d])) :
    ∀ r_s r_t : Std.I64,
      Aegis.MaxDepth.max_depth s = ok r_s → Aegis.MaxDepth.max_depth t = ok r_t →
        r_s.val = r_t.val + 1 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (s t : Slice Std.U8) (c d : Std.U8)
    (hs1 : 1 ≤ s.val.length) (hs100 : s.val.length ≤ 100)
    (ht1 : 1 ≤ t.val.length) (ht100 : t.val.length ≤ 100)
    (hsvalid : IsValidParens s) (htvalid : IsValidParens t)
    (hfirst : s.val.head? = some c) (hlast : s.val.getLast? = some d)
    (hc : c.val = openByte) (hd : d.val = closeByte)
    (hshape : s.val = c :: (t.val ++ [d])), ∀ r_s r_t : Std.I64,
      Aegis.MaxDepth.max_depth s = ok r_s → Aegis.MaxDepth.max_depth t = ok r_t →
        r_s.val = r_t.val + 1) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if there is no index i with 0 <= i < len(s) and s[i] = '('.
  Preconditions: len(s) >= 1 and len(s) <= 100. The bytes of s that are '(' or ')' form a valid parentheses sequence: for every k with 0 <= k <= len(s), the number of ')' among s[0],...,s[k-1] is at most the number of '(' among them, and for k = len(s) the two counts are equal. -/
theorem spec_13 (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen100 : s.val.length ≤ 100)
    (hvalid : IsValidParens s) :
    ∀ r : Std.I64, Aegis.MaxDepth.max_depth s = ok r → (r.val = 0 ↔ ¬ Occurs s openByte) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen100 : s.val.length ≤ 100)
    (hvalid : IsValidParens s), ∀ r : Std.I64, Aegis.MaxDepth.max_depth s = ok r → (r.val = 0 ↔ ¬ Occurs s openByte)) := by
  sorry

end AegisSpec.MaxDepth
