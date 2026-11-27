import Aegis.MinAddToMakeValid.Code.Funs

/-!
# Specifications of `Aegis.MinAddToMakeValid.min_add_to_make_valid`

LeetCode problem `minimum-add-to-make-parentheses-valid`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinAddToMakeValid

open Aegis.MinAddToMakeValid (min_add_to_make_valid)

def bytes (s : Slice Std.U8) : List Nat := s.val.map (fun b => b.val)

def slen (s : Slice Std.U8) : Nat := s.val.length

def ParenBytes (l : List Nat) : Prop := ∀ c, c ∈ l → c = 40 ∨ c = 41

def countByte (c : Nat) (l : List Nat) : Nat := (l.filter (fun d => d = c)).length

def countOpen (l : List Nat) : Nat := countByte 40 l

def countClose (l : List Nat) : Nat := countByte 41 l

def balStep (c : Nat) : Int := if c = 40 then 1 else if c = 41 then -1 else 0

def balance (l : List Nat) : Nat → Int
  | 0 => 0
  | n + 1 => balance l n + balStep (l.getD n 0)

def minBalance (l : List Nat) : Int :=
  (List.range (l.length + 1)).foldl (fun acc k => min acc (balance l k)) 0

def deficit (l : List Nat) (k : Nat) : Int :=
  (countClose (l.take k) : Int) - (countOpen (l.take k) : Int)

def maxDeficit (l : List Nat) : Int :=
  (List.range (l.length + 1)).foldl (fun acc k => max acc (deficit l k)) 0

def IsValid (l : List Nat) : Prop :=
  ParenBytes l ∧
    (∀ k, k ≤ l.length → countClose (l.take k) ≤ countOpen (l.take k)) ∧
    countOpen l = countClose l

def Subseq (u l : List Nat) : Prop := u.Sublist l

/-- The function returns a result r (it does not fail), and r = B(len(s)) - 2*m, where B(0)=0; for every k with 0 <= k < len(s), B(k+1)=B(k)+1 if s[k]=40 and B(k+1)=B(k)-1 if s[k]=41; and m = min { B(k) : 0 <= k <= len(s) }.
  Preconditions: 1 <= len(s) <= 1000, and for every i with 0 <= i < len(s), s[i] = 40 or s[i] = 41 (ASCII '(' or ')'). -/
theorem spec_1 (s : Slice Std.U8)
    (hlen1 : 1 ≤ slen s) (hlen : slen s ≤ 1000)
    (hpar : ParenBytes (bytes s)) :
    ∃ r : Std.I64,
      min_add_to_make_valid s = ok r ∧
        r.val = balance (bytes s) (slen s) - 2 * minBalance (bytes s) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen1 : 1 ≤ slen s) (hlen : slen s ≤ 1000)
    (hpar : ParenBytes (bytes s)), ∃ r : Std.I64,
      min_add_to_make_valid s = ok r ∧
        r.val = balance (bytes s) (slen s) - 2 * minBalance (bytes s)) := by
  sorry

/-- For every s satisfying the preconditions, the function returns a result r; it does not fail.
  Preconditions: 1 <= len(s) <= 1000, and for every i with 0 <= i < len(s), s[i] = 40 or s[i] = 41 (ASCII '(' or ')'). -/
theorem spec_2 (s : Slice Std.U8)
    (hlen1 : 1 ≤ slen s) (hlen : slen s ≤ 1000)
    (hpar : ParenBytes (bytes s)) :
    ∃ r : Std.I64, min_add_to_make_valid s = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen1 : 1 ≤ slen s) (hlen : slen s ≤ 1000)
    (hpar : ParenBytes (bytes s)), ∃ r : Std.I64, min_add_to_make_valid s = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r <= len(s).
  Preconditions: 1 <= len(s) <= 1000, and for every i with 0 <= i < len(s), s[i] = 40 or s[i] = 41 (ASCII '(' or ')'). -/
theorem spec_3 (s : Slice Std.U8)
    (hlen1 : 1 ≤ slen s) (hlen : slen s ≤ 1000)
    (hpar : ParenBytes (bytes s)) :
    ∀ r : Std.I64, min_add_to_make_valid s = ok r → 0 ≤ r.val ∧ r.val ≤ (slen s : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen1 : 1 ≤ slen s) (hlen : slen s ≤ 1000)
    (hpar : ParenBytes (bytes s)), ∀ r : Std.I64, min_add_to_make_valid s = ok r → 0 ≤ r.val ∧ r.val ≤ (slen s : Int)) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if s is a valid parentheses string. Here s is valid means: for every k with 0 <= k <= len(s), the number of indices i with 0 <= i < k and s[i]=40 is at least the number of indices i with 0 <= i < k and s[i]=41, and these two counts are equal when k = len(s).
  Preconditions: 1 <= len(s) <= 1000, and for every i with 0 <= i < len(s), s[i] = 40 or s[i] = 41 (ASCII '(' or ')'). -/
theorem spec_4 (s : Slice Std.U8)
    (hlen1 : 1 ≤ slen s) (hlen : slen s ≤ 1000)
    (hpar : ParenBytes (bytes s)) :
    ∀ r : Std.I64,
      min_add_to_make_valid s = ok r → (r.val = 0 ↔ IsValid (bytes s)) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen1 : 1 ≤ slen s) (hlen : slen s ≤ 1000)
    (hpar : ParenBytes (bytes s)), ∀ r : Std.I64,
      min_add_to_make_valid s = ok r → (r.val = 0 ↔ IsValid (bytes s))) := by
  sorry

/-- If len(s)=1, then whenever the function returns a result r, r=1.
  Preconditions: 1 <= len(s) <= 1000, and for every i with 0 <= i < len(s), s[i] = 40 or s[i] = 41 (ASCII '(' or ')'). -/
theorem spec_5 (s : Slice Std.U8)
    (hlen1 : 1 ≤ slen s) (hlen : slen s ≤ 1000)
    (hpar : ParenBytes (bytes s))
    (hlen_eq : slen s = 1) :
    ∀ r : Std.I64, min_add_to_make_valid s = ok r → r.val = 1 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen1 : 1 ≤ slen s) (hlen : slen s ≤ 1000)
    (hpar : ParenBytes (bytes s))
    (hlen_eq : slen s = 1), ∀ r : Std.I64, min_add_to_make_valid s = ok r → r.val = 1) := by
  sorry

/-- If s[i]=40 for every i with 0 <= i < len(s), then whenever the function returns a result r, r=len(s).
  Preconditions: 1 <= len(s) <= 1000, and for every i with 0 <= i < len(s), s[i] = 40 or s[i] = 41 (ASCII '(' or ')'). -/
theorem spec_6 (s : Slice Std.U8)
    (hlen1 : 1 ≤ slen s) (hlen : slen s ≤ 1000)
    (hpar : ParenBytes (bytes s))
    (hall : ∀ c, c ∈ bytes s → c = 40) :
    ∀ r : Std.I64, min_add_to_make_valid s = ok r → r.val = (slen s : Int) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen1 : 1 ≤ slen s) (hlen : slen s ≤ 1000)
    (hpar : ParenBytes (bytes s))
    (hall : ∀ c, c ∈ bytes s → c = 40), ∀ r : Std.I64, min_add_to_make_valid s = ok r → r.val = (slen s : Int)) := by
  sorry

/-- If s[i]=41 for every i with 0 <= i < len(s), then whenever the function returns a result r, r=len(s).
  Preconditions: 1 <= len(s) <= 1000, and for every i with 0 <= i < len(s), s[i] = 40 or s[i] = 41 (ASCII '(' or ')'). -/
theorem spec_7 (s : Slice Std.U8)
    (hlen1 : 1 ≤ slen s) (hlen : slen s ≤ 1000)
    (hpar : ParenBytes (bytes s))
    (hall : ∀ c, c ∈ bytes s → c = 41) :
    ∀ r : Std.I64, min_add_to_make_valid s = ok r → r.val = (slen s : Int) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen1 : 1 ≤ slen s) (hlen : slen s ≤ 1000)
    (hpar : ParenBytes (bytes s))
    (hall : ∀ c, c ∈ bytes s → c = 41), ∀ r : Std.I64, min_add_to_make_valid s = ok r → r.val = (slen s : Int)) := by
  sorry

/-- Whenever the function returns a result r, r and len(s) have the same parity; equivalently, len(s)+r is even.
  Preconditions: 1 <= len(s) <= 1000, and for every i with 0 <= i < len(s), s[i] = 40 or s[i] = 41 (ASCII '(' or ')'). -/
theorem spec_8 (s : Slice Std.U8)
    (hlen1 : 1 ≤ slen s) (hlen : slen s ≤ 1000)
    (hpar : ParenBytes (bytes s)) :
    ∀ r : Std.I64,
      min_add_to_make_valid s = ok r → ∃ k : Int, (slen s : Int) + r.val = 2 * k := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen1 : 1 ≤ slen s) (hlen : slen s ≤ 1000)
    (hpar : ParenBytes (bytes s)), ∀ r : Std.I64,
      min_add_to_make_valid s = ok r → ∃ k : Int, (slen s : Int) + r.val = 2 * k) := by
  sorry

/-- Whenever the function returns a result r, r >= |O - C|, where O is the number of indices i with 0 <= i < len(s) and s[i]=40, and C is the number of indices i with 0 <= i < len(s) and s[i]=41.
  Preconditions: 1 <= len(s) <= 1000, and for every i with 0 <= i < len(s), s[i] = 40 or s[i] = 41 (ASCII '(' or ')'). -/
theorem spec_9 (s : Slice Std.U8)
    (hlen1 : 1 ≤ slen s) (hlen : slen s ≤ 1000)
    (hpar : ParenBytes (bytes s)) :
    ∀ r : Std.I64,
      min_add_to_make_valid s = ok r →
        r.val ≥ |(countOpen (bytes s) : Int) - (countClose (bytes s) : Int)| := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen1 : 1 ≤ slen s) (hlen : slen s ≤ 1000)
    (hpar : ParenBytes (bytes s)), ∀ r : Std.I64,
      min_add_to_make_valid s = ok r →
        r.val ≥ |(countOpen (bytes s) : Int) - (countClose (bytes s) : Int)|) := by
  sorry

/-- Whenever the function returns a result r, there exists a parentheses string t of length len(s)+r such that t is valid (every prefix has at least as many '(' as ')' and the total numbers of '(' and ')' in t are equal) and s is a subsequence of t (there exist indices 0 <= i_0 < i_1 < ... < i_{len(s)-1} < len(t) with t[i_j]=s[j] for every j).
  Preconditions: 1 <= len(s) <= 1000, and for every i with 0 <= i < len(s), s[i] = 40 or s[i] = 41 (ASCII '(' or ')'). -/
theorem spec_10 (s : Slice Std.U8)
    (hlen1 : 1 ≤ slen s) (hlen : slen s ≤ 1000)
    (hpar : ParenBytes (bytes s)) :
    ∀ r : Std.I64,
      min_add_to_make_valid s = ok r →
        ∃ t : List Nat,
          IsValid t ∧ Subseq (bytes s) t ∧ (t.length : Int) = (slen s : Int) + r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen1 : 1 ≤ slen s) (hlen : slen s ≤ 1000)
    (hpar : ParenBytes (bytes s)), ∀ r : Std.I64,
      min_add_to_make_valid s = ok r →
        ∃ t : List Nat,
          IsValid t ∧ Subseq (bytes s) t ∧ (t.length : Int) = (slen s : Int) + r.val) := by
  sorry

/-- Whenever the function returns a result r, for every parentheses string t such that t is valid (every prefix has at least as many '(' as ')' and total counts are equal) and s is a subsequence of t (there exist indices 0 <= i_0 < ... < i_{len(s)-1} < len(t) with t[i_j]=s[j] for every j), we have len(t) - len(s) >= r.
  Preconditions: 1 <= len(s) <= 1000, and for every i with 0 <= i < len(s), s[i] = 40 or s[i] = 41 (ASCII '(' or ')'). -/
theorem spec_11 (s : Slice Std.U8)
    (hlen1 : 1 ≤ slen s) (hlen : slen s ≤ 1000)
    (hpar : ParenBytes (bytes s)) :
    ∀ r : Std.I64,
      min_add_to_make_valid s = ok r →
        ∀ t : List Nat,
          IsValid t → Subseq (bytes s) t → r.val ≤ (t.length : Int) - (slen s : Int) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen1 : 1 ≤ slen s) (hlen : slen s ≤ 1000)
    (hpar : ParenBytes (bytes s)), ∀ r : Std.I64,
      min_add_to_make_valid s = ok r →
        ∀ t : List Nat,
          IsValid t → Subseq (bytes s) t → r.val ≤ (t.length : Int) - (slen s : Int)) := by
  sorry

/-- Let s' be the slice of length len(s)+2 with s'[i]=s[i] for 0 <= i < len(s), s'[len(s)]=40, and s'[len(s)+1]=41. If the function returns r for s and r' for s', then r = r'.
  Preconditions: 1 <= len(s) <= 998, and for every i with 0 <= i < len(s), s[i] = 40 or s[i] = 41 (ASCII '(' or ')'). -/
theorem spec_12 (s s' : Slice Std.U8)
    (hlen1 : 1 ≤ slen s) (hlen : slen s ≤ 998)
    (hpar : ParenBytes (bytes s))
    (hs' : bytes s' = bytes s ++ [40, 41]) :
    ∀ r r' : Std.I64,
      min_add_to_make_valid s = ok r →
        min_add_to_make_valid s' = ok r' → r.val = r'.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (s s' : Slice Std.U8)
    (hlen1 : 1 ≤ slen s) (hlen : slen s ≤ 998)
    (hpar : ParenBytes (bytes s))
    (hs' : bytes s' = bytes s ++ [40, 41]), ∀ r r' : Std.I64,
      min_add_to_make_valid s = ok r →
        min_add_to_make_valid s' = ok r' → r.val = r'.val) := by
  sorry

/-- Let s' be the slice of length len(s) defined by s'[i] = 41 if s[len(s)-1-i] = 40, and s'[i] = 40 if s[len(s)-1-i] = 41, for 0 <= i < len(s). If the function returns r for s and r' for s', then r = r'.
  Preconditions: 1 <= len(s) <= 1000, and for every i with 0 <= i < len(s), s[i] = 40 or s[i] = 41 (ASCII '(' or ')'). -/
theorem spec_13 (s s' : Slice Std.U8)
    (hlen1 : 1 ≤ slen s) (hlen : slen s ≤ 1000)
    (hpar : ParenBytes (bytes s))
    (hs' : bytes s' = (bytes s).reverse.map (fun c => if c = 40 then 41 else if c = 41 then 40 else c)) :
    ∀ r r' : Std.I64,
      min_add_to_make_valid s = ok r →
        min_add_to_make_valid s' = ok r' → r.val = r'.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (s s' : Slice Std.U8)
    (hlen1 : 1 ≤ slen s) (hlen : slen s ≤ 1000)
    (hpar : ParenBytes (bytes s))
    (hs' : bytes s' = (bytes s).reverse.map (fun c => if c = 40 then 41 else if c = 41 then 40 else c)), ∀ r r' : Std.I64,
      min_add_to_make_valid s = ok r →
        min_add_to_make_valid s' = ok r' → r.val = r'.val) := by
  sorry

/-- Whenever the function returns a result r, r >= D, where D = max { deficit(k) : 0 <= k <= len(s) } and deficit(k) is the number of indices i with 0 <= i < k and s[i]=41 minus the number of indices i with 0 <= i < k and s[i]=40.
  Preconditions: 1 <= len(s) <= 1000, and for every i with 0 <= i < len(s), s[i] = 40 or s[i] = 41 (ASCII '(' or ')'). -/
theorem spec_14 (s : Slice Std.U8)
    (hlen1 : 1 ≤ slen s) (hlen : slen s ≤ 1000)
    (hpar : ParenBytes (bytes s)) :
    ∀ r : Std.I64, min_add_to_make_valid s = ok r → r.val ≥ maxDeficit (bytes s) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen1 : 1 ≤ slen s) (hlen : slen s ≤ 1000)
    (hpar : ParenBytes (bytes s)), ∀ r : Std.I64, min_add_to_make_valid s = ok r → r.val ≥ maxDeficit (bytes s)) := by
  sorry

/-- Let s' be the slice of length len(s)+2 with s'[0]=40, s'[1]=41, and s'[i+2]=s[i] for 0 <= i < len(s). If the function returns r for s and r' for s', then r = r'.
  Preconditions: 1 <= len(s) <= 998, and for every i with 0 <= i < len(s), s[i] = 40 or s[i] = 41 (ASCII '(' or ')'). -/
theorem spec_15 (s s' : Slice Std.U8)
    (hlen1 : 1 ≤ slen s) (hlen : slen s ≤ 998)
    (hpar : ParenBytes (bytes s))
    (hs' : bytes s' = [40, 41] ++ bytes s) :
    ∀ r r' : Std.I64,
      min_add_to_make_valid s = ok r →
        min_add_to_make_valid s' = ok r' → r.val = r'.val := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (s s' : Slice Std.U8)
    (hlen1 : 1 ≤ slen s) (hlen : slen s ≤ 998)
    (hpar : ParenBytes (bytes s))
    (hs' : bytes s' = [40, 41] ++ bytes s), ∀ r r' : Std.I64,
      min_add_to_make_valid s = ok r →
        min_add_to_make_valid s' = ok r' → r.val = r'.val) := by
  sorry

end AegisSpec.MinAddToMakeValid
