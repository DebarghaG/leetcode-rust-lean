import Aegis.FixedRatio.Code.Funs

/-!
# Specifications of `Aegis.FixedRatio.fixed_ratio`

LeetCode problem `number-of-substrings-with-fixed-ratio`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.FixedRatio

abbrev U8 := Aeneas.Std.U8

abbrev ByteSlice := Aeneas.Std.Slice Aeneas.Std.U8

abbrev I64 := Aeneas.Std.I64

abbrev byte0 : ℕ := 48

abbrev byte1 : ℕ := 49

def byteAt (s : ByteSlice) (p : ℕ) : ℕ :=
  match s.val[p]? with
  | some b => b.val
  | none => 0

def IsBinary (s : ByteSlice) : Prop :=
  ∀ b ∈ s.val, b.val = byte0 ∨ b.val = byte1

def zeroCount (s : ByteSlice) (i j : ℕ) : ℕ :=
  ((Finset.Ico i j).filter (fun p => byteAt s p = byte0)).card

def oneCount (s : ByteSlice) (i j : ℕ) : ℕ :=
  ((Finset.Ico i j).filter (fun p => byteAt s p = byte1)).card

def ratioEq (s : ByteSlice) (num1 num2 : I64) (i j : ℕ) : Prop :=
  (zeroCount s i j : ℤ) * num2.val = (oneCount s i j : ℤ) * num1.val

instance decidableRatioEq (s : ByteSlice) (num1 num2 : I64) (i j : ℕ) :
    Decidable (ratioEq s num1 num2 i j) := by
  unfold ratioEq
  infer_instance

def allPairs (s : ByteSlice) : Finset (ℕ × ℕ) :=
  Finset.product (Finset.range (s.val.length + 1)) (Finset.range (s.val.length + 1))

def goodPairs (s : ByteSlice) (num1 num2 : I64) : Finset (ℕ × ℕ) :=
  (allPairs s).filter (fun q => q.1 < q.2 ∧ ratioEq s num1 num2 q.1 q.2)

def balancedPairs (s : ByteSlice) : Finset (ℕ × ℕ) :=
  (allPairs s).filter (fun q => q.1 < q.2 ∧ zeroCount s q.1 q.2 = oneCount s q.1 q.2)

def crossPairs (s : ByteSlice) (num1 num2 : I64) (k : ℕ) : Finset (ℕ × ℕ) :=
  (allPairs s).filter (fun q => q.1 < k ∧ k < q.2 ∧ ratioEq s num1 num2 q.1 q.2)

def gcdn (num1 num2 : I64) : ℕ :=
  Nat.gcd num1.val.natAbs num2.val.natAbs

def reducedNum1 (num1 num2 : I64) : ℕ :=
  num1.val.natAbs / gcdn num1 num2

def reducedNum2 (num1 num2 : I64) : ℕ :=
  num2.val.natAbs / gcdn num1 num2

def period (num1 num2 : I64) : ℕ :=
  reducedNum1 num1 num2 + reducedNum2 num1 num2

def shapeBound (s : ByteSlice) (num1 num2 : I64) : ℕ :=
  (Finset.Icc 1 (s.val.length / period num1 num2)).sum
    (fun k => s.val.length - k * period num1 num2 + 1)

def threshold (num1 num2 : I64) : ℕ :=
  max num1.val.natAbs num2.val.natAbs

def revSlice (s : ByteSlice) : ByteSlice :=
  Aeneas.Std.Slice.from s.val.reverse (by simp)

def flipByte (b : U8) : U8 :=
  if b.val = byte0 then 49#u8 else if b.val = byte1 then 48#u8 else b

def compSlice (s : ByteSlice) : ByteSlice :=
  Aeneas.Std.Slice.from (s.val.map flipByte) (by simp)

def takeSlice (s : ByteSlice) (k : ℕ) : ByteSlice :=
  Aeneas.Std.Slice.from (s.val.take k) (by simp)

def dropSlice (s : ByteSlice) (k : ℕ) : ByteSlice :=
  Aeneas.Std.Slice.from (s.val.drop k) (by
    have h : s.val.length ≤ Aeneas.Std.Usize.max := by simp
    have hdrop : (s.val.drop k).length = s.val.length - k := List.length_drop
    omega)

/-- Whenever fixed_ratio(s,num1,num2) returns a result r, r equals the number of pairs (i,j) of integers with 0 <= i < j <= n such that, letting z(i,j) = #{p | i <= p < j and s[p] = 48} and o(i,j) = #{p | i <= p < j and s[p] = 49}, we have z(i,j) * num2 = o(i,j) * num1. Equivalently, r is the number of non-empty contiguous substrings s[i..j-1] whose number of 0-bytes and number of 1-bytes are in the ratio num1 : num2.
  Preconditions: Let n = len(s). The string s is binary: for every p with 0 <= p < n, s[p] is either 48 ('0') or 49 ('1'). Also 1 <= n <= 100000, 1 <= num1 <= n, and 1 <= num2 <= n. (No coprimality assumption is made in this specification; the ratio is expressed by cross multiplication.) -/
theorem spec_1 (s : ByteSlice) (num1 num2 : I64)
    (hbin : IsBinary s) (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100000)
    (hnum1a : 1 ≤ num1.val) (hnum1b : num1.val ≤ (s.val.length : ℤ))
    (hnum2a : 1 ≤ num2.val) (hnum2b : num2.val ≤ (s.val.length : ℤ)) :
    ∀ r, Aegis.FixedRatio.fixed_ratio s num1 num2 = ok r →
      r.val = ((goodPairs s num1 num2).card : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : ByteSlice) (num1 num2 : I64)
    (hbin : IsBinary s) (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100000)
    (hnum1a : 1 ≤ num1.val) (hnum1b : num1.val ≤ (s.val.length : ℤ))
    (hnum2a : 1 ≤ num2.val) (hnum2b : num2.val ≤ (s.val.length : ℤ)), ∀ r, Aegis.FixedRatio.fixed_ratio s num1 num2 = ok r →
      r.val = ((goodPairs s num1 num2).card : ℤ)) := by
  sorry

/-- For every s, num1, num2 satisfying the preconditions, fixed_ratio(s,num1,num2) returns a result (it does not panic or overflow).
  Preconditions: Let n = len(s). s is binary: every byte is 48 ('0') or 49 ('1'). Also 1 <= n <= 100000, 1 <= num1 <= n, and 1 <= num2 <= n. -/
theorem spec_2 (s : ByteSlice) (num1 num2 : I64)
    (hbin : IsBinary s) (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100000)
    (hnum1a : 1 ≤ num1.val) (hnum1b : num1.val ≤ (s.val.length : ℤ))
    (hnum2a : 1 ≤ num2.val) (hnum2b : num2.val ≤ (s.val.length : ℤ)) :
    ∃ r, Aegis.FixedRatio.fixed_ratio s num1 num2 = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : ByteSlice) (num1 num2 : I64)
    (hbin : IsBinary s) (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100000)
    (hnum1a : 1 ≤ num1.val) (hnum1b : num1.val ≤ (s.val.length : ℤ))
    (hnum2a : 1 ≤ num2.val) (hnum2b : num2.val ≤ (s.val.length : ℤ)), ∃ r, Aegis.FixedRatio.fixed_ratio s num1 num2 = ok r) := by
  sorry

/-- Whenever fixed_ratio(s,num1,num2) returns r, 0 <= r <= n * (n + 1) / 2, where n = len(s).
  Preconditions: Let n = len(s). s is binary, 1 <= n <= 100000, 1 <= num1 <= n, and 1 <= num2 <= n. -/
theorem spec_3 (s : ByteSlice) (num1 num2 : I64)
    (hbin : IsBinary s) (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100000)
    (hnum1a : 1 ≤ num1.val) (hnum1b : num1.val ≤ (s.val.length : ℤ))
    (hnum2a : 1 ≤ num2.val) (hnum2b : num2.val ≤ (s.val.length : ℤ)) :
    ∀ r, Aegis.FixedRatio.fixed_ratio s num1 num2 = ok r →
      0 ≤ r.val ∧ r.val ≤ ((s.val.length * (s.val.length + 1) / 2 : ℕ) : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : ByteSlice) (num1 num2 : I64)
    (hbin : IsBinary s) (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100000)
    (hnum1a : 1 ≤ num1.val) (hnum1b : num1.val ≤ (s.val.length : ℤ))
    (hnum2a : 1 ≤ num2.val) (hnum2b : num2.val ≤ (s.val.length : ℤ)), ∀ r, Aegis.FixedRatio.fixed_ratio s num1 num2 = ok r →
      0 ≤ r.val ∧ r.val ≤ ((s.val.length * (s.val.length + 1) / 2 : ℕ) : ℤ)) := by
  sorry

/-- Whenever fixed_ratio(s,num1,num2) returns r, r = 0.
  Preconditions: Let n = len(s). s is binary, 1 <= n <= 100000, 1 <= num1 <= n, and 1 <= num2 <= n. Additionally, s contains no byte equal to 48 ('0') or s contains no byte equal to 49 ('1'). -/
theorem spec_4 (s : ByteSlice) (num1 num2 : I64)
    (hbin : IsBinary s) (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100000)
    (hnum1a : 1 ≤ num1.val) (hnum1b : num1.val ≤ (s.val.length : ℤ))
    (hnum2a : 1 ≤ num2.val) (hnum2b : num2.val ≤ (s.val.length : ℤ))
    (hno0 : (∀ b ∈ s.val, b.val ≠ byte0) ∨ (∀ b ∈ s.val, b.val ≠ byte1)) :
    ∀ r, Aegis.FixedRatio.fixed_ratio s num1 num2 = ok r → r.val = 0 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : ByteSlice) (num1 num2 : I64)
    (hbin : IsBinary s) (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100000)
    (hnum1a : 1 ≤ num1.val) (hnum1b : num1.val ≤ (s.val.length : ℤ))
    (hnum2a : 1 ≤ num2.val) (hnum2b : num2.val ≤ (s.val.length : ℤ))
    (hno0 : (∀ b ∈ s.val, b.val ≠ byte0) ∨ (∀ b ∈ s.val, b.val ≠ byte1)), ∀ r, Aegis.FixedRatio.fixed_ratio s num1 num2 = ok r → r.val = 0) := by
  sorry

/-- Let g = gcd(num1,num2), a = num1 / g, b = num2 / g, and L = a + b. Whenever fixed_ratio(s,num1,num2) returns r, r <= sum_{k=1}^{floor(n/L)} (n - k*L + 1). If floor(n/L) = 0, the sum is 0.
  Preconditions: Let n = len(s). s is binary, 1 <= n <= 100000, 1 <= num1 <= n, and 1 <= num2 <= n. -/
theorem spec_5 (s : ByteSlice) (num1 num2 : I64)
    (hbin : IsBinary s) (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100000)
    (hnum1a : 1 ≤ num1.val) (hnum1b : num1.val ≤ (s.val.length : ℤ))
    (hnum2a : 1 ≤ num2.val) (hnum2b : num2.val ≤ (s.val.length : ℤ)) :
    ∀ r, Aegis.FixedRatio.fixed_ratio s num1 num2 = ok r →
      r.val ≤ ((shapeBound s num1 num2 : ℕ) : ℤ) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : ByteSlice) (num1 num2 : I64)
    (hbin : IsBinary s) (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100000)
    (hnum1a : 1 ≤ num1.val) (hnum1b : num1.val ≤ (s.val.length : ℤ))
    (hnum2a : 1 ≤ num2.val) (hnum2b : num2.val ≤ (s.val.length : ℤ)), ∀ r, Aegis.FixedRatio.fixed_ratio s num1 num2 = ok r →
      r.val ≤ ((shapeBound s num1 num2 : ℕ) : ℤ)) := by
  sorry

/-- Whenever fixed_ratio(s,num1,num2) returns r, r = 1 if s has exactly a bytes equal to 48 ('0') and exactly b bytes equal to 49 ('1'), and r = 0 otherwise.
  Preconditions: Let n = len(s). s is binary, 1 <= n <= 100000, 1 <= num1 <= n, and 1 <= num2 <= n. Let g = gcd(num1,num2), a = num1 / g, b = num2 / g, and assume n = a + b. -/
theorem spec_6 (s : ByteSlice) (num1 num2 : I64)
    (hbin : IsBinary s) (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100000)
    (hnum1a : 1 ≤ num1.val) (hnum1b : num1.val ≤ (s.val.length : ℤ))
    (hnum2a : 1 ≤ num2.val) (hnum2b : num2.val ≤ (s.val.length : ℤ))
    (hn : s.val.length = period num1 num2) :
    ∀ r, Aegis.FixedRatio.fixed_ratio s num1 num2 = ok r →
      r.val = (if zeroCount s 0 s.val.length = reducedNum1 num1 num2 ∧
         oneCount s 0 s.val.length = reducedNum2 num1 num2 then (1 : ℤ) else 0) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : ByteSlice) (num1 num2 : I64)
    (hbin : IsBinary s) (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100000)
    (hnum1a : 1 ≤ num1.val) (hnum1b : num1.val ≤ (s.val.length : ℤ))
    (hnum2a : 1 ≤ num2.val) (hnum2b : num2.val ≤ (s.val.length : ℤ))
    (hn : s.val.length = period num1 num2), ∀ r, Aegis.FixedRatio.fixed_ratio s num1 num2 = ok r →
      r.val = (if zeroCount s 0 s.val.length = reducedNum1 num1 num2 ∧
         oneCount s 0 s.val.length = reducedNum2 num1 num2 then (1 : ℤ) else 0)) := by
  sorry

/-- Whenever fixed_ratio(s,num1,num2) returns r, r equals the number of pairs (i,j) with 0 <= i < j <= n such that the substring s[i..j-1] contains the same number of '0' bytes and '1' bytes.
  Preconditions: Let n = len(s). s is binary, 1 <= n <= 100000, 1 <= num1 <= n, 1 <= num2 <= n, and num1 = num2. -/
theorem spec_7 (s : ByteSlice) (num1 num2 : I64)
    (hbin : IsBinary s) (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100000)
    (hnum1a : 1 ≤ num1.val) (hnum1b : num1.val ≤ (s.val.length : ℤ))
    (hnum2a : 1 ≤ num2.val) (hnum2b : num2.val ≤ (s.val.length : ℤ))
    (heq : num1.val = num2.val) :
    ∀ r, Aegis.FixedRatio.fixed_ratio s num1 num2 = ok r →
      r.val = ((balancedPairs s).card : ℤ) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : ByteSlice) (num1 num2 : I64)
    (hbin : IsBinary s) (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100000)
    (hnum1a : 1 ≤ num1.val) (hnum1b : num1.val ≤ (s.val.length : ℤ))
    (hnum2a : 1 ≤ num2.val) (hnum2b : num2.val ≤ (s.val.length : ℤ))
    (heq : num1.val = num2.val), ∀ r, Aegis.FixedRatio.fixed_ratio s num1 num2 = ok r →
      r.val = ((balancedPairs s).card : ℤ)) := by
  sorry

/-- Whenever fixed_ratio(s,num1,num2) returns r and fixed_ratio(s,c*num1,c*num2) returns r_c, we have r = r_c.
  Preconditions: Let n = len(s). s is binary, 1 <= n <= 100000, 1 <= num1 <= n, 1 <= num2 <= n. Also c is a positive integer with c*num1 <= n and c*num2 <= n. -/
theorem spec_8 (s : ByteSlice) (num1 num2 num1' num2' : I64) (c : ℤ)
    (hbin : IsBinary s) (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100000)
    (hnum1a : 1 ≤ num1.val) (hnum1b : num1.val ≤ (s.val.length : ℤ))
    (hnum2a : 1 ≤ num2.val) (hnum2b : num2.val ≤ (s.val.length : ℤ))
    (hc : 1 ≤ c)
    (hcnum1 : c * num1.val ≤ (s.val.length : ℤ))
    (hcnum2 : c * num2.val ≤ (s.val.length : ℤ))
    (hnum1' : num1'.val = c * num1.val) (hnum2' : num2'.val = c * num2.val) :
    ∀ r r_c, Aegis.FixedRatio.fixed_ratio s num1 num2 = ok r →
      Aegis.FixedRatio.fixed_ratio s num1' num2' = ok r_c → r.val = r_c.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s : ByteSlice) (num1 num2 num1' num2' : I64) (c : ℤ)
    (hbin : IsBinary s) (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100000)
    (hnum1a : 1 ≤ num1.val) (hnum1b : num1.val ≤ (s.val.length : ℤ))
    (hnum2a : 1 ≤ num2.val) (hnum2b : num2.val ≤ (s.val.length : ℤ))
    (hc : 1 ≤ c)
    (hcnum1 : c * num1.val ≤ (s.val.length : ℤ))
    (hcnum2 : c * num2.val ≤ (s.val.length : ℤ))
    (hnum1' : num1'.val = c * num1.val) (hnum2' : num2'.val = c * num2.val), ∀ r r_c, Aegis.FixedRatio.fixed_ratio s num1 num2 = ok r →
      Aegis.FixedRatio.fixed_ratio s num1' num2' = ok r_c → r.val = r_c.val) := by
  sorry

/-- Let rev(s) be the length-n byte array t with t[i] = s[n-1-i] for 0 <= i < n. Whenever fixed_ratio(s,num1,num2) returns r and fixed_ratio(rev(s),num1,num2) returns r_rev, we have r = r_rev.
  Preconditions: Let n = len(s). s is binary, 1 <= n <= 100000, 1 <= num1 <= n, and 1 <= num2 <= n. -/
theorem spec_9 (s : ByteSlice) (num1 num2 : I64)
    (hbin : IsBinary s) (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100000)
    (hnum1a : 1 ≤ num1.val) (hnum1b : num1.val ≤ (s.val.length : ℤ))
    (hnum2a : 1 ≤ num2.val) (hnum2b : num2.val ≤ (s.val.length : ℤ)) :
    ∀ r r_rev, Aegis.FixedRatio.fixed_ratio s num1 num2 = ok r →
      Aegis.FixedRatio.fixed_ratio (revSlice s) num1 num2 = ok r_rev →
      r.val = r_rev.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s : ByteSlice) (num1 num2 : I64)
    (hbin : IsBinary s) (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100000)
    (hnum1a : 1 ≤ num1.val) (hnum1b : num1.val ≤ (s.val.length : ℤ))
    (hnum2a : 1 ≤ num2.val) (hnum2b : num2.val ≤ (s.val.length : ℤ)), ∀ r r_rev, Aegis.FixedRatio.fixed_ratio s num1 num2 = ok r →
      Aegis.FixedRatio.fixed_ratio (revSlice s) num1 num2 = ok r_rev →
      r.val = r_rev.val) := by
  sorry

/-- Let comp(s) be the length-n byte array obtained from s by replacing every '0' (48) with '1' (49) and every '1' (49) with '0' (48). Whenever fixed_ratio(s,num1,num2) returns r and fixed_ratio(comp(s),num2,num1) returns r_comp, we have r = r_comp.
  Preconditions: Let n = len(s). s is binary, 1 <= n <= 100000, 1 <= num1 <= n, and 1 <= num2 <= n. -/
theorem spec_10 (s : ByteSlice) (num1 num2 : I64)
    (hbin : IsBinary s) (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100000)
    (hnum1a : 1 ≤ num1.val) (hnum1b : num1.val ≤ (s.val.length : ℤ))
    (hnum2a : 1 ≤ num2.val) (hnum2b : num2.val ≤ (s.val.length : ℤ)) :
    ∀ r r_comp, Aegis.FixedRatio.fixed_ratio s num1 num2 = ok r →
      Aegis.FixedRatio.fixed_ratio (compSlice s) num2 num1 = ok r_comp →
      r.val = r_comp.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s : ByteSlice) (num1 num2 : I64)
    (hbin : IsBinary s) (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100000)
    (hnum1a : 1 ≤ num1.val) (hnum1b : num1.val ≤ (s.val.length : ℤ))
    (hnum2a : 1 ≤ num2.val) (hnum2b : num2.val ≤ (s.val.length : ℤ)), ∀ r r_comp, Aegis.FixedRatio.fixed_ratio s num1 num2 = ok r →
      Aegis.FixedRatio.fixed_ratio (compSlice s) num2 num1 = ok r_comp →
      r.val = r_comp.val) := by
  sorry

/-- Let M = max(num1,num2). For every integer k with M <= k <= n, let P_k = s[0..k). If fixed_ratio(P_k,num1,num2) returns r_p and fixed_ratio(s,num1,num2) returns r, then r_p <= r. For every integer k with 0 <= k <= n - M, let S_k = s[k..n). If fixed_ratio(S_k,num1,num2) returns r_s and fixed_ratio(s,num1,num2) returns r, then r_s <= r.
  Preconditions: Let n = len(s). The string s is binary: for every p with 0 <= p < n, s[p] is either 48 ('0') or 49 ('1'). Also 1 <= n <= 100000, 1 <= num1 <= n, and 1 <= num2 <= n. -/
theorem spec_11 (s : ByteSlice) (num1 num2 : I64)
    (hbin : IsBinary s) (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100000)
    (hnum1a : 1 ≤ num1.val) (hnum1b : num1.val ≤ (s.val.length : ℤ))
    (hnum2a : 1 ≤ num2.val) (hnum2b : num2.val ≤ (s.val.length : ℤ)) :
    (∀ k, threshold num1 num2 ≤ k → k ≤ s.val.length →
      ∀ r_p r, Aegis.FixedRatio.fixed_ratio (takeSlice s k) num1 num2 = ok r_p →
        Aegis.FixedRatio.fixed_ratio s num1 num2 = ok r → r_p.val ≤ r.val) ∧
    (∀ k, k ≤ s.val.length - threshold num1 num2 →
      ∀ r_s r, Aegis.FixedRatio.fixed_ratio (dropSlice s k) num1 num2 = ok r_s →
        Aegis.FixedRatio.fixed_ratio s num1 num2 = ok r → r_s.val ≤ r.val) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s : ByteSlice) (num1 num2 : I64)
    (hbin : IsBinary s) (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100000)
    (hnum1a : 1 ≤ num1.val) (hnum1b : num1.val ≤ (s.val.length : ℤ))
    (hnum2a : 1 ≤ num2.val) (hnum2b : num2.val ≤ (s.val.length : ℤ)), (∀ k, threshold num1 num2 ≤ k → k ≤ s.val.length →
      ∀ r_p r, Aegis.FixedRatio.fixed_ratio (takeSlice s k) num1 num2 = ok r_p →
        Aegis.FixedRatio.fixed_ratio s num1 num2 = ok r → r_p.val ≤ r.val) ∧
    (∀ k, k ≤ s.val.length - threshold num1 num2 →
      ∀ r_s r, Aegis.FixedRatio.fixed_ratio (dropSlice s k) num1 num2 = ok r_s →
        Aegis.FixedRatio.fixed_ratio s num1 num2 = ok r → r_s.val ≤ r.val)) := by
  sorry

/-- For every integer k with max(num1,num2) <= k <= n - max(num1,num2), let A = s[0..k) and B = s[k..n). Let C(k) be the number of pairs (i,j) with 0 <= i < k < j <= n such that, with z_s(i,j) and o_s(i,j) computed in s, z_s(i,j) * num2 = o_s(i,j) * num1. Whenever fixed_ratio(A,num1,num2) returns r_A, fixed_ratio(B,num1,num2) returns r_B, and fixed_ratio(s,num1,num2) returns r, we have r = r_A + r_B + C(k).
  Preconditions: Let n = len(s). s is binary, 1 <= n <= 100000, 1 <= num1 <= n, and 1 <= num2 <= n. -/
theorem spec_12 (s : ByteSlice) (num1 num2 : I64)
    (hbin : IsBinary s) (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100000)
    (hnum1a : 1 ≤ num1.val) (hnum1b : num1.val ≤ (s.val.length : ℤ))
    (hnum2a : 1 ≤ num2.val) (hnum2b : num2.val ≤ (s.val.length : ℤ)) :
    ∀ k, threshold num1 num2 ≤ k → k ≤ s.val.length - threshold num1 num2 →
      ∀ r_A r_B r,
        Aegis.FixedRatio.fixed_ratio (takeSlice s k) num1 num2 = ok r_A →
        Aegis.FixedRatio.fixed_ratio (dropSlice s k) num1 num2 = ok r_B →
        Aegis.FixedRatio.fixed_ratio s num1 num2 = ok r →
        r.val = r_A.val + r_B.val + ((crossPairs s num1 num2 k).card : ℤ) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (s : ByteSlice) (num1 num2 : I64)
    (hbin : IsBinary s) (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100000)
    (hnum1a : 1 ≤ num1.val) (hnum1b : num1.val ≤ (s.val.length : ℤ))
    (hnum2a : 1 ≤ num2.val) (hnum2b : num2.val ≤ (s.val.length : ℤ)), ∀ k, threshold num1 num2 ≤ k → k ≤ s.val.length - threshold num1 num2 →
      ∀ r_A r_B r,
        Aegis.FixedRatio.fixed_ratio (takeSlice s k) num1 num2 = ok r_A →
        Aegis.FixedRatio.fixed_ratio (dropSlice s k) num1 num2 = ok r_B →
        Aegis.FixedRatio.fixed_ratio s num1 num2 = ok r →
        r.val = r_A.val + r_B.val + ((crossPairs s num1 num2 k).card : ℤ)) := by
  sorry

end AegisSpec.FixedRatio
