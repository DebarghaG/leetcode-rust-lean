import Aegis.RomanToInt.Code.Funs

/-!
# Specifications of `Aegis.RomanToInt.roman_to_int`

LeetCode problem `roman-to-integer`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.RomanToInt

def bI : U8 := 73#u8

def bV : U8 := 86#u8

def bX : U8 := 88#u8

def bL : U8 := 76#u8

def bC : U8 := 67#u8

def bD : U8 := 68#u8

def bM : U8 := 77#u8

def romanValue (c : U8) : ℕ :=
  if c = bI then 1
  else if c = bV then 5
  else if c = bX then 10
  else if c = bL then 50
  else if c = bC then 100
  else if c = bD then 500
  else if c = bM then 1000
  else 0

@[reducible] def IsRomanByte (c : U8) : Prop :=
  c = bI ∨ c = bV ∨ c = bX ∨ c = bL ∨ c = bC ∨ c = bD ∨ c = bM

@[reducible] def IsSubtractivePair (a b : U8) : Prop :=
  (a = bI ∧ b = bV) ∨ (a = bI ∧ b = bX) ∨ (a = bX ∧ b = bL) ∨
    (a = bX ∧ b = bC) ∨ (a = bC ∧ b = bD) ∨ (a = bC ∧ b = bM)

def value : List U8 → ℤ
  | [] => 0
  | [c] => (romanValue c : ℤ)
  | c :: c' :: rest =>
    (if romanValue c < romanValue c' then -((romanValue c : ℤ)) else (romanValue c : ℤ)) +
      value (c' :: rest)

def plainSum (L : List U8) : ℤ := ((L.map romanValue).sum : ℤ)

def subtractiveSum : List U8 → ℕ
  | [] => 0
  | [_] => 0
  | c :: c' :: rest =>
    (if romanValue c < romanValue c' then romanValue c else 0) + subtractiveSum (c' :: rest)

def romanTable : List (ℕ × List U8) :=
  [(1000, [bM]), (900, [bC, bM]), (500, [bD]), (400, [bC, bD]), (100, [bC]),
   (90, [bX, bC]), (50, [bL]), (40, [bX, bL]), (10, [bX]), (9, [bI, bX]), (5, [bV]),
   (4, [bI, bV]), (1, [bI])]

def toRomanAux : List (ℕ × List U8) → ℕ → List U8
  | [], _ => []
  | (k, bs) :: rest, n => (List.replicate (n / k) bs).flatten ++ toRomanAux rest (n % k)

def toRoman (n : ℕ) : List U8 := toRomanAux romanTable n

def IsStandardRoman (L : List U8) : Prop :=
  ∃ n, 1 ≤ n ∧ n ≤ 3999 ∧ toRoman n = L

/-- Whenever the function returns a result r, r equals the integer represented by s under the standard Roman rule: r = sum_{i=0}^{len(s)-1} c_i, where c_i = -v(s[i]) if i+1 < len(s) and v(s[i]) < v(s[i+1]), and c_i = v(s[i]) otherwise; v is defined by v('I')=1, v('V')=5, v('X')=10, v('L')=50, v('C')=100, v('D')=500, v('M')=1000.
  Preconditions: 1 <= len(s) <= 15; every byte s[i] with 0 <= i < len(s) is the ASCII code of one of 'I','V','X','L','C','D','M'; and s is a valid standard Roman numeral in [1,3999] (canonical representation, allowing only the usual additive forms and the six subtractive pairs IV, IX, XL, XC, CD, CM). -/
theorem spec_1 (s : Slice U8)
    (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 15)
    (h_bytes : ∀ c ∈ s.val, IsRomanByte c)
    (h_valid : IsStandardRoman s.val)
    (r : I64) (hr : Aegis.RomanToInt.roman_to_int s = ok r) :
    r.val = value s.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice U8)
    (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 15)
    (h_bytes : ∀ c ∈ s.val, IsRomanByte c)
    (h_valid : IsStandardRoman s.val)
    (r : I64) (hr : Aegis.RomanToInt.roman_to_int s = ok r), r.val = value s.val) := by
  sorry

/-- For every s satisfying the preconditions, the function returns a result r and does not fail (no panic, overflow, out-of-bounds access, or other failure).
  Preconditions: 1 <= len(s) <= 15; every byte s[i] with 0 <= i < len(s) is the ASCII code of one of 'I','V','X','L','C','D','M'; and s is a valid standard Roman numeral in [1,3999] (canonical representation, allowing only the usual additive forms and the six subtractive pairs IV, IX, XL, XC, CD, CM). -/
theorem spec_2 (s : Slice U8)
    (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 15)
    (h_bytes : ∀ c ∈ s.val, IsRomanByte c)
    (h_valid : IsStandardRoman s.val) :
    ∃ r, Aegis.RomanToInt.roman_to_int s = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice U8)
    (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 15)
    (h_bytes : ∀ c ∈ s.val, IsRomanByte c)
    (h_valid : IsStandardRoman s.val), ∃ r, Aegis.RomanToInt.roman_to_int s = ok r) := by
  sorry

/-- Whenever the function returns a result r, 1 <= r <= 3999.
  Preconditions: 1 <= len(s) <= 15; every byte s[i] with 0 <= i < len(s) is the ASCII code of one of 'I','V','X','L','C','D','M'; and s is a valid standard Roman numeral in [1,3999] (canonical representation, allowing only the usual additive forms and the six subtractive pairs IV, IX, XL, XC, CD, CM). -/
theorem spec_3 (s : Slice U8)
    (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 15)
    (h_bytes : ∀ c ∈ s.val, IsRomanByte c)
    (h_valid : IsStandardRoman s.val)
    (r : I64) (hr : Aegis.RomanToInt.roman_to_int s = ok r) :
    1 ≤ r.val ∧ r.val ≤ 3999 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice U8)
    (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 15)
    (h_bytes : ∀ c ∈ s.val, IsRomanByte c)
    (h_valid : IsStandardRoman s.val)
    (r : I64) (hr : Aegis.RomanToInt.roman_to_int s = ok r), 1 ≤ r.val ∧ r.val ≤ 3999) := by
  sorry

/-- Whenever the function returns a result r, s is exactly the standard Roman numeral of r; equivalently, the standard greedy construction for r from the values 1000,900,500,400,100,90,50,40,10,9,5,4,1 (using M,CM,D,CD,C,XC,L,XL,X,IX,V,IV,I respectively) produces the byte string s.
  Preconditions: 1 <= len(s) <= 15; every byte s[i] with 0 <= i < len(s) is the ASCII code of one of 'I','V','X','L','C','D','M'; and s is a valid standard Roman numeral in [1,3999] (canonical representation, allowing only the usual additive forms and the six subtractive pairs IV, IX, XL, XC, CD, CM). -/
theorem spec_4 (s : Slice U8)
    (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 15)
    (h_bytes : ∀ c ∈ s.val, IsRomanByte c)
    (h_valid : IsStandardRoman s.val)
    (r : I64) (hr : Aegis.RomanToInt.roman_to_int s = ok r) :
    s.val = toRoman r.val.toNat := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice U8)
    (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 15)
    (h_bytes : ∀ c ∈ s.val, IsRomanByte c)
    (h_valid : IsStandardRoman s.val)
    (r : I64) (hr : Aegis.RomanToInt.roman_to_int s = ok r), s.val = toRoman r.val.toNat) := by
  sorry

/-- Whenever the function returns a result r and s has no subtractive adjacent pair, i.e. for every i with 0 <= i < len(s)-1 we have v(s[i]) >= v(s[i+1]), then r = sum_{i=0}^{len(s)-1} v(s[i]), where v('I')=1, v('V')=5, v('X')=10, v('L')=50, v('C')=100, v('D')=500, v('M')=1000.
  Preconditions: 1 <= len(s) <= 15; every byte s[i] with 0 <= i < len(s) is the ASCII code of one of 'I','V','X','L','C','D','M'; and s is a valid standard Roman numeral in [1,3999] (canonical representation, allowing only the usual additive forms and the six subtractive pairs IV, IX, XL, XC, CD, CM). -/
theorem spec_5 (s : Slice U8)
    (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 15)
    (h_bytes : ∀ c ∈ s.val, IsRomanByte c)
    (h_valid : IsStandardRoman s.val)
    (h_no_sub : ∀ (i : ℕ) (hi : i + 1 < s.val.length),
      romanValue (s.val[i]'(Nat.lt_of_succ_lt hi)) ≥ romanValue (s.val[i+1]'hi))
    (r : I64) (hr : Aegis.RomanToInt.roman_to_int s = ok r) :
    r.val = plainSum s.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice U8)
    (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 15)
    (h_bytes : ∀ c ∈ s.val, IsRomanByte c)
    (h_valid : IsStandardRoman s.val)
    (h_no_sub : ∀ (i : ℕ) (hi : i + 1 < s.val.length),
      romanValue (s.val[i]'(Nat.lt_of_succ_lt hi)) ≥ romanValue (s.val[i+1]'hi))
    (r : I64) (hr : Aegis.RomanToInt.roman_to_int s = ok r), r.val = plainSum s.val) := by
  sorry

/-- Whenever the function returns a result r, let S = sum_{i=0}^{len(s)-1} v(s[i]) and let T = sum over all i with 0 <= i < len(s)-1 and v(s[i]) < v(s[i+1]) of v(s[i]); then r = S - 2*T, where v('I')=1, v('V')=5, v('X')=10, v('L')=50, v('C')=100, v('D')=500, v('M')=1000.
  Preconditions: 1 <= len(s) <= 15; every byte s[i] with 0 <= i < len(s) is the ASCII code of one of 'I','V','X','L','C','D','M'; and s is a valid standard Roman numeral in [1,3999] (canonical representation, allowing only the usual additive forms and the six subtractive pairs IV, IX, XL, XC, CD, CM). -/
theorem spec_6 (s : Slice U8)
    (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 15)
    (h_bytes : ∀ c ∈ s.val, IsRomanByte c)
    (h_valid : IsStandardRoman s.val)
    (r : I64) (hr : Aegis.RomanToInt.roman_to_int s = ok r) :
    r.val = plainSum s.val - 2 * (subtractiveSum s.val : ℤ) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice U8)
    (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 15)
    (h_bytes : ∀ c ∈ s.val, IsRomanByte c)
    (h_valid : IsStandardRoman s.val)
    (r : I64) (hr : Aegis.RomanToInt.roman_to_int s = ok r), r.val = plainSum s.val - 2 * (subtractiveSum s.val : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, for every j with 0 <= j <= len(s), let p_j be the value of the prefix s[0..j) computed by the same sign rule: p_0 = 0; for j > 0, p_j = sum_{i=0}^{j-1} d_i where d_i = -v(s[i]) if i+1 < j and v(s[i]) < v(s[i+1]), and d_i = v(s[i]) otherwise; v('I')=1, v('V')=5, v('X')=10, v('L')=50, v('C')=100, v('D')=500, v('M')=1000. Then p_j <= r.
  Preconditions: 1 <= len(s) <= 15; every byte s[i] with 0 <= i < len(s) is the ASCII code of one of 'I','V','X','L','C','D','M'; and s is a valid standard Roman numeral in [1,3999] (canonical representation, allowing only the usual additive forms and the six subtractive pairs IV, IX, XL, XC, CD, CM). -/
theorem spec_7 (s : Slice U8)
    (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 15)
    (h_bytes : ∀ c ∈ s.val, IsRomanByte c)
    (h_valid : IsStandardRoman s.val)
    (r : I64) (hr : Aegis.RomanToInt.roman_to_int s = ok r) :
    ∀ j, j ≤ s.val.length → value (s.val.take j) ≤ r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice U8)
    (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 15)
    (h_bytes : ∀ c ∈ s.val, IsRomanByte c)
    (h_valid : IsStandardRoman s.val)
    (r : I64) (hr : Aegis.RomanToInt.roman_to_int s = ok r), ∀ j, j ≤ s.val.length → value (s.val.take j) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, if s = u ++ v for byte slices u and v (possibly empty) such that every symbol of u has value at least every symbol of v, i.e. for all i < len(u) and j < len(v), v(u[i]) >= v(v[j]), then r = value(u) + value(v), where value(t) is the sign-sum value of t defined as sum_{i=0}^{len(t)-1} c_i with c_i = -v(t[i]) if i+1 < len(t) and v(t[i]) < v(t[i+1]), and c_i = v(t[i]) otherwise; v('I')=1, v('V')=5, v('X')=10, v('L')=50, v('C')=100, v('D')=500, v('M')=1000, and value(empty)=0.
  Preconditions: 1 <= len(s) <= 15; every byte s[i] with 0 <= i < len(s) is the ASCII code of one of 'I','V','X','L','C','D','M'; and s is a valid standard Roman numeral in [1,3999] (canonical representation, allowing only the usual additive forms and the six subtractive pairs IV, IX, XL, XC, CD, CM). -/
theorem spec_8 (s : Slice U8)
    (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 15)
    (h_bytes : ∀ c ∈ s.val, IsRomanByte c)
    (h_valid : IsStandardRoman s.val)
    (u w : List U8) (h_split : s.val = u ++ w)
    (h_cross : ∀ (i : ℕ) (hi : i < u.length) (j : ℕ) (hj : j < w.length),
      romanValue (u[i]'hi) ≥ romanValue (w[j]'hj))
    (r : I64) (hr : Aegis.RomanToInt.roman_to_int s = ok r) :
    r.val = value u + value w := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s : Slice U8)
    (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 15)
    (h_bytes : ∀ c ∈ s.val, IsRomanByte c)
    (h_valid : IsStandardRoman s.val)
    (u w : List U8) (h_split : s.val = u ++ w)
    (h_cross : ∀ (i : ℕ) (hi : i < u.length) (j : ℕ) (hj : j < w.length),
      romanValue (u[i]'hi) ≥ romanValue (w[j]'hj))
    (r : I64) (hr : Aegis.RomanToInt.roman_to_int s = ok r), r.val = value u + value w) := by
  sorry

/-- Whenever the function returns a result r and the last two bytes of s are one of 'IV','IX','XL','XC','CD','CM', writing p = s[0..len(s)-2) and value(p) for the sign-sum value of p (with value(empty)=0), we have r = value(p) + (v(s[len(s)-1]) - v(s[len(s)-2])), where v('I')=1, v('V')=5, v('X')=10, v('L')=50, v('C')=100, v('D')=500, v('M')=1000.
  Preconditions: 1 <= len(s) <= 15; every byte s[i] with 0 <= i < len(s) is the ASCII code of one of 'I','V','X','L','C','D','M'; and s is a valid standard Roman numeral in [1,3999] (canonical representation, allowing only the usual additive forms and the six subtractive pairs IV, IX, XL, XC, CD, CM). -/
theorem spec_9 (s : Slice U8)
    (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 15)
    (h_bytes : ∀ c ∈ s.val, IsRomanByte c)
    (h_valid : IsStandardRoman s.val)
    (p : List U8) (a b : U8) (h_last : s.val = p ++ [a, b]) (h_pair : IsSubtractivePair a b)
    (r : I64) (hr : Aegis.RomanToInt.roman_to_int s = ok r) :
    r.val = value p + ((romanValue b : ℤ) - (romanValue a : ℤ)) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s : Slice U8)
    (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 15)
    (h_bytes : ∀ c ∈ s.val, IsRomanByte c)
    (h_valid : IsStandardRoman s.val)
    (p : List U8) (a b : U8) (h_last : s.val = p ++ [a, b]) (h_pair : IsSubtractivePair a b)
    (r : I64) (hr : Aegis.RomanToInt.roman_to_int s = ok r), r.val = value p + ((romanValue b : ℤ) - (romanValue a : ℤ))) := by
  sorry

end AegisSpec.RomanToInt
