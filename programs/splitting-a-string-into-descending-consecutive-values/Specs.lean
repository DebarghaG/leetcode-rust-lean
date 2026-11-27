import Aegis.SplitString.Code.Funs

/-!
# Specifications of `Aegis.SplitString.split_string`

LeetCode problem `splitting-a-string-into-descending-consecutive-values`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Aeneas.Std.Result
open Aegis.SplitString

namespace AegisSpec.SplitString

def IsDigitByte (c : Std.U8) : Prop := 48 ≤ c.val ∧ c.val ≤ 57

def IsDigitString (s : Slice Std.U8) : Prop := ∀ c ∈ s.val, IsDigitByte c

def NoLeadingZero (s : Slice Std.U8) : Prop := s.val[0]? ≠ some 48#u8

def digits (s : Slice Std.U8) : List Nat := s.val.map (fun c => c.val - 48)

def numVal (s : Slice Std.U8) (l r : Nat) : Nat :=
  List.foldl (fun acc d => acc * 10 + d) 0 (((digits s).drop l).take (r - l))

def StepCond (s : Slice Std.U8) : List Nat → Prop
  | a :: b :: c :: rest => numVal s a b = numVal s b c + 1 ∧ StepCond s (b :: c :: rest)
  | _ => True

def IsValidSplit (s : Slice Std.U8) (p : List Nat) : Prop :=
  p.head? = some 0 ∧ p.getLast? = some s.val.length ∧ 3 ≤ p.length ∧
    p.Pairwise (· < ·) ∧ StepCond s p

def HasValidSplit (s : Slice Std.U8) : Prop := ∃ p, IsValidSplit s p

def cutAt (p : List Nat) (j : Nat) : Nat := p.getD j 0

/-- The function returns a result r (i.e., split_string s = ok r for some Boolean r) and r = true if and only if there exists a valid split of s; otherwise r = false.
  Preconditions: Let n = len(s). We have 1 <= n <= 20. For every i with 0 <= i < n, s[i] is an ASCII digit (48 <= s[i] <= 57). For 0 <= l < r <= n, let V(l,r) = sum_{i=l}^{r-1} (s[i]-48) * 10^{r-1-i}. A valid split of s is a sequence of indices 0 = p_0 < p_1 < ... < p_k = n with k >= 2 such that for every j with 1 <= j < k, V(p_{j-1}, p_j) = V(p_j, p_{j+1}) + 1. -/
theorem spec_1 (s : Slice Std.U8)
    (hpos : 1 ≤ s.val.length) (hle : s.val.length ≤ 20) (hdig : IsDigitString s) :
    ∃ r, split_string s = ok r ∧ (r = true ↔ HasValidSplit s) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hpos : 1 ≤ s.val.length) (hle : s.val.length ≤ 20) (hdig : IsDigitString s), ∃ r, split_string s = ok r ∧ (r = true ↔ HasValidSplit s)) := by
  sorry

/-- There exists a Boolean b such that split_string s = ok b.
  Preconditions: Let n = len(s). We have 1 <= n <= 20. For every i with 0 <= i < n, s[i] is an ASCII digit (48 <= s[i] <= 57). -/
theorem spec_2 (s : Slice Std.U8)
    (hpos : 1 ≤ s.val.length) (hle : s.val.length ≤ 20) (hdig : IsDigitString s) :
    ∃ b, split_string s = ok b := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hpos : 1 ≤ s.val.length) (hle : s.val.length ≤ 20) (hdig : IsDigitString s), ∃ b, split_string s = ok b) := by
  sorry

/-- split_string s = ok false.
  Preconditions: n = len(s) = 1 and s[0] is an ASCII digit. -/
theorem spec_3 (s : Slice Std.U8)
    (hlen : s.val.length = 1) (hdig : IsDigitString s) :
    split_string s = ok false := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen : s.val.length = 1) (hdig : IsDigitString s), split_string s = ok false) := by
  sorry

/-- split_string s = ok (a = b + 1).
  Preconditions: n = len(s) = 2. Let a = s[0]-48 and b = s[1]-48. Both are digits. -/
theorem spec_4 (s : Slice Std.U8)
    (hlen : s.val.length = 2) (hdig : IsDigitString s) :
    split_string s = ok (decide (numVal s 0 1 = numVal s 1 2 + 1)) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen : s.val.length = 2) (hdig : IsDigitString s), split_string s = ok (decide (numVal s 0 1 = numVal s 1 2 + 1))) := by
  sorry

/-- For every Boolean b, split_string t = ok b if and only if split_string s = ok b.
  Preconditions: Let s be a digit string with 1 <= len(s) <= 20. Let k be an integer with 0 <= k and len(s) + k <= 20. Let t be the string of length len(s)+k such that for 0 <= i < k, t[i] = 48 (the ASCII code for '0'), and for 0 <= i < len(s), t[k+i] = s[i]. -/
theorem spec_5 (s t : Slice Std.U8) (k : Nat)
    (hpos : 1 ≤ s.val.length) (hle : s.val.length ≤ 20) (hdig : IsDigitString s)
    (hk : s.val.length + k ≤ 20)
    (htlen : t.val.length = s.val.length + k)
    (htzero : ∀ i c, i < k → t.val[i]? = some c → c.val = 48)
    (htshift : ∀ i, i < s.val.length → t.val[k + i]? = s.val[i]?) :
    ∀ b, split_string t = ok b ↔ split_string s = ok b := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s t : Slice Std.U8) (k : Nat)
    (hpos : 1 ≤ s.val.length) (hle : s.val.length ≤ 20) (hdig : IsDigitString s)
    (hk : s.val.length + k ≤ 20)
    (htlen : t.val.length = s.val.length + k)
    (htzero : ∀ i c, i < k → t.val[i]? = some c → c.val = 48)
    (htshift : ∀ i, i < s.val.length → t.val[k + i]? = s.val[i]?), ∀ b, split_string t = ok b ↔ split_string s = ok b) := by
  sorry

/-- For every valid split of s (with cut indices 0 = p_0 < p_1 < ... < p_k = n, k >= 2, and V(p_{j-1}, p_j) = V(p_j, p_{j+1}) + 1 for 1 <= j < k), the numerical value of the first segment satisfies V(p_0, p_1) >= 1.
  Preconditions: Let n = len(s), 1 <= n <= 20, all s[i] digits. For 0 <= l < r <= n, let V(l,r) = sum_{i=l}^{r-1} (s[i]-48) * 10^{r-1-i}. Assume split_string s = ok true. -/
theorem spec_6 (s : Slice Std.U8)
    (hpos : 1 ≤ s.val.length) (hle : s.val.length ≤ 20) (hdig : IsDigitString s)
    (hres : split_string s = ok true)
    (p : List Nat) (hp : IsValidSplit s p) :
    1 ≤ numVal s (cutAt p 0) (cutAt p 1) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hpos : 1 ≤ s.val.length) (hle : s.val.length ≤ 20) (hdig : IsDigitString s)
    (hres : split_string s = ok true)
    (p : List Nat) (hp : IsValidSplit s p), 1 ≤ numVal s (cutAt p 0) (cutAt p 1)) := by
  sorry

/-- For every valid split of s with k parts and numerical values v_j = V(p_{j-1}, p_j) for 1 <= j <= k, we have v_1 = v_k + (k - 1).
  Preconditions: Let n = len(s), 1 <= n <= 20, all s[i] digits. For 0 <= l < r <= n, let V(l,r) = sum_{i=l}^{r-1} (s[i]-48) * 10^{r-1-i}. Assume split_string s = ok true. -/
theorem spec_7 (s : Slice Std.U8)
    (hpos : 1 ≤ s.val.length) (hle : s.val.length ≤ 20) (hdig : IsDigitString s)
    (hres : split_string s = ok true)
    (p : List Nat) (hp : IsValidSplit s p) :
    numVal s (cutAt p 0) (cutAt p 1) =
      numVal s (cutAt p (p.length - 2)) (cutAt p (p.length - 1)) + (p.length - 2) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hpos : 1 ≤ s.val.length) (hle : s.val.length ≤ 20) (hdig : IsDigitString s)
    (hres : split_string s = ok true)
    (p : List Nat) (hp : IsValidSplit s p), numVal s (cutAt p 0) (cutAt p 1) =
      numVal s (cutAt p (p.length - 2)) (cutAt p (p.length - 1)) + (p.length - 2)) := by
  sorry

/-- For every valid split of s with k parts, the numerical value v_1 of the first segment satisfies v_1 >= k - 1.
  Preconditions: Let n = len(s), 1 <= n <= 20, all s[i] digits. For 0 <= l < r <= n, let V(l,r) = sum_{i=l}^{r-1} (s[i]-48) * 10^{r-1-i}. Assume split_string s = ok true. -/
theorem spec_8 (s : Slice Std.U8)
    (hpos : 1 ≤ s.val.length) (hle : s.val.length ≤ 20) (hdig : IsDigitString s)
    (hres : split_string s = ok true)
    (p : List Nat) (hp : IsValidSplit s p) :
    p.length - 2 ≤ numVal s (cutAt p 0) (cutAt p 1) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hpos : 1 ≤ s.val.length) (hle : s.val.length ≤ 20) (hdig : IsDigitString s)
    (hres : split_string s = ok true)
    (p : List Nat) (hp : IsValidSplit s p), p.length - 2 ≤ numVal s (cutAt p 0) (cutAt p 1)) := by
  sorry

/-- split_string s = ok true.
  Preconditions: Let n = len(s), 1 <= n <= 20, all s[i] digits. For 0 <= l < r <= n, let V(l,r) = sum_{i=l}^{r-1} (s[i]-48) * 10^{r-1-i}. Suppose there exists an integer p with 0 < p < n such that V(0,p) = V(p,n) + 1. -/
theorem spec_9 (s : Slice Std.U8)
    (hpos : 1 ≤ s.val.length) (hle : s.val.length ≤ 20) (hdig : IsDigitString s)
    (hwit : ∃ p, 0 < p ∧ p < s.val.length ∧ numVal s 0 p = numVal s p s.val.length + 1) :
    split_string s = ok true := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hpos : 1 ≤ s.val.length) (hle : s.val.length ≤ 20) (hdig : IsDigitString s)
    (hwit : ∃ p, 0 < p ∧ p < s.val.length ∧ numVal s 0 p = numVal s p s.val.length + 1), split_string s = ok true) := by
  sorry

/-- split_string s = ok ((10*a + b = c + 1) or (a = 10*b + c + 1) or (a = b + 1 and b = c + 1)).
  Preconditions: n = len(s) = 3. Let a = s[0]-48, b = s[1]-48, c = s[2]-48. All are digits. -/
theorem spec_10 (s : Slice Std.U8)
    (hlen : s.val.length = 3) (hdig : IsDigitString s) :
    split_string s = ok
      (decide (numVal s 0 2 = numVal s 2 3 + 1 ∨
        numVal s 0 1 = numVal s 1 3 + 1 ∨
        (numVal s 0 1 = numVal s 1 2 + 1 ∧ numVal s 1 2 = numVal s 2 3 + 1))) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen : s.val.length = 3) (hdig : IsDigitString s), split_string s = ok
      (decide (numVal s 0 2 = numVal s 2 3 + 1 ∨
        numVal s 0 1 = numVal s 1 3 + 1 ∨
        (numVal s 0 1 = numVal s 1 2 + 1 ∧ numVal s 1 2 = numVal s 2 3 + 1)))) := by
  sorry

/-- For every valid split of s with cut indices 0 = p_0 < p_1 < ... < p_k = n (k >= 2) and V(p_{j-1},p_j) = V(p_j,p_{j+1}) + 1 for 1 <= j < k, the first segment length satisfies 2*p_1 <= n + 1 (equivalently p_1 <= (n+1)/2).
  Preconditions: Let n = len(s), 1 <= n <= 20, and all s[i] are ASCII digits. For 0 <= l < r <= n, let V(l,r) = sum_{i=l}^{r-1} (s[i]-48) * 10^{r-1-i}. Assume split_string s = ok true. -/
theorem spec_11 (s : Slice Std.U8)
    (hpos : 1 ≤ s.val.length) (hle : s.val.length ≤ 20) (hdig : IsDigitString s)
    (hres : split_string s = ok true)
    (p : List Nat) (hp : IsValidSplit s p) :
    2 * cutAt p 1 ≤ s.val.length + 1 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hpos : 1 ≤ s.val.length) (hle : s.val.length ≤ 20) (hdig : IsDigitString s)
    (hres : split_string s = ok true)
    (p : List Nat) (hp : IsValidSplit s p), 2 * cutAt p 1 ≤ s.val.length + 1) := by
  sorry

end AegisSpec.SplitString
