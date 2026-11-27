import Aegis.MaxOperations.Code.Funs

/-!
# Specifications of `Aegis.MaxOperations.max_operations`

LeetCode problem `maximum-number-of-operations-to-move-ones-to-the-end`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxOperations

abbrev byteZero : Std.U8 := 48#u8

abbrev byteOne : Std.U8 := 49#u8

abbrev IsBit (b : Std.U8) : Prop := b.val = 48 ∨ b.val = 49

def AllBits (s : Slice Std.U8) : Prop := ∀ b ∈ s.val, IsBit b

abbrev byteAt (l : List Std.U8) (i : ℕ) : Option ℕ := (l[i]?).map (fun b => b.val)

abbrev HasOneAt (l : List Std.U8) (i : ℕ) : Prop := byteAt l i = some 49

abbrev HasZeroAt (l : List Std.U8) (i : ℕ) : Prop := byteAt l i = some 48

def isOneByte (b : Std.U8) : Bool := b.val == 49

def isZeroByte (b : Std.U8) : Bool := b.val == 48

def onesCount (l : List Std.U8) : ℕ := (l.filter isOneByte).length

def zerosCount (l : List Std.U8) : ℕ := (l.filter isZeroByte).length

def onesBefore (l : List Std.U8) (a : ℕ) : ℕ := onesCount (l.take a)

def zeroRunSumFrom (prevIsOne : Bool) (ones ans : ℕ) : List Std.U8 → ℕ
  | [] => ans
  | b :: rest =>
      if isOneByte b then
        zeroRunSumFrom true (ones + 1) ans rest
      else
        zeroRunSumFrom false ones (ans + (if prevIsOne then ones else 0)) rest

def zeroRunSum (l : List Std.U8) : ℕ := zeroRunSumFrom false 0 0 l

def onesZeroPairs : List Std.U8 → ℕ
  | [] => 0
  | b :: rest => onesZeroPairs rest + (if isOneByte b then zerosCount rest else 0)

def positiveZeroRunCountFrom (prevIsOne : Bool) : List Std.U8 → ℕ
  | [] => 0
  | b :: rest =>
      if isZeroByte b then
        (if prevIsOne then 1 else 0) + positiveZeroRunCountFrom false rest
      else
        positiveZeroRunCountFrom true rest

def positiveZeroRunCount (l : List Std.U8) : ℕ := positiveZeroRunCountFrom false l

def startsWithZero : List Std.U8 → Bool
  | [] => false
  | b :: _ => isZeroByte b

def zeroRunCount (l : List Std.U8) : ℕ :=
  positiveZeroRunCount l + (if startsWithZero l then 1 else 0)

abbrev IsZeroRunStart (l : List Std.U8) (a : ℕ) : Prop :=
  HasZeroAt l a ∧ (a = 0 ∨ HasOneAt l (a - 1))

def AllowedStep (x y : List Std.U8) : Prop :=
  ∃ (p zs tl : List Std.U8) (b1 b0 : Std.U8),
    b1.val = 49 ∧
      b0.val = 48 ∧
      (∀ b ∈ zs, b.val = 48) ∧
      (∀ b, tl.head? = some b → b.val = 49) ∧
      x = p ++ (b1 :: (b0 :: (zs ++ tl))) ∧
      y = p ++ (b0 :: (zs ++ (b1 :: tl)))

def ReachesIn : ℕ → List Std.U8 → List Std.U8 → Prop
  | 0, x, y => y = x
  | n + 1, x, y => ∃ z, AllowedStep x z ∧ ReachesIn n z y

/-- The function returns a result r, and the integer value of r is exactly the maximum number of allowed operations that can be performed on s. Equivalently, it is the sum, over every maximal contiguous block of '0' bytes in s, of the number of '1' bytes strictly before the start of that block. Formally, for each such zero-run let a be its start index and let c(a) = |{ j | 0 ≤ j < a and s[j] = '1' }|; then r = Σ c(a), with the empty sum equal to 0 if s contains no '0'. An allowed operation chooses an index i with i+1 < len(s), s[i] = '1', and s[i+1] = '0', and moves that '1' to the right across the maximal block of zeros starting at i+1, stopping immediately before the next '1' if one exists or at the end of the string if none exists.
  Preconditions: len(s) ≥ 1 and len(s) ≤ 100000, and for every i with 0 ≤ i < len(s), s[i] is either '0' (byte 48) or '1' (byte 49). -/
theorem spec_1 (s : Slice Std.U8) (h1 : 1 ≤ s.length) (h2 : s.length ≤ 100000)
    (h3 : AllBits s) :
    ∃ r, Aegis.MaxOperations.max_operations s = ok r ∧ r.val = (zeroRunSum s.val : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice Std.U8) (h1 : 1 ≤ s.length) (h2 : s.length ≤ 100000)
    (h3 : AllBits s), ∃ r, Aegis.MaxOperations.max_operations s = ok r ∧ r.val = (zeroRunSum s.val : ℤ)) := by
  sorry

/-- For every s satisfying the preconditions, the evaluation of max_operations s returns a result r and does not fail: there is no arithmetic overflow, no out-of-bounds slice access, and no panic.
  Preconditions: len(s) ≥ 1 and len(s) ≤ 100000, and for every i with 0 ≤ i < len(s), s[i] is either '0' (byte 48) or '1' (byte 49). -/
theorem spec_2 (s : Slice Std.U8) (h1 : 1 ≤ s.length) (h2 : s.length ≤ 100000)
    (h3 : AllBits s) :
    ∃ r, Aegis.MaxOperations.max_operations s = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice Std.U8) (h1 : 1 ≤ s.length) (h2 : s.length ≤ 100000)
    (h3 : AllBits s), ∃ r, Aegis.MaxOperations.max_operations s = ok r) := by
  sorry

/-- Whenever max_operations s returns a result r, the integer value of r is at most I(s), where I(s) is the number of pairs (i,j) such that 0 ≤ i < j < len(s), s[i] = '1', and s[j] = '0'.
  Preconditions: len(s) ≥ 1 and len(s) ≤ 100000, and for every i with 0 ≤ i < len(s), s[i] is either '0' (byte 48) or '1' (byte 49). -/
theorem spec_3 (s : Slice Std.U8) (h1 : 1 ≤ s.length) (h2 : s.length ≤ 100000)
    (h3 : AllBits s) :
    ∀ r, Aegis.MaxOperations.max_operations s = ok r → r.val ≤ (onesZeroPairs s.val : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice Std.U8) (h1 : 1 ≤ s.length) (h2 : s.length ≤ 100000)
    (h3 : AllBits s), ∀ r, Aegis.MaxOperations.max_operations s = ok r → r.val ≤ (onesZeroPairs s.val : ℤ)) := by
  sorry

/-- Whenever max_operations s returns a result r, the integer value of r is at least Zplus(s), where Zplus(s) is the number of maximal contiguous blocks of '0' bytes whose start index a satisfies a > 0.
  Preconditions: len(s) ≥ 1 and len(s) ≤ 100000, and for every i with 0 ≤ i < len(s), s[i] is either '0' (byte 48) or '1' (byte 49). -/
theorem spec_4 (s : Slice Std.U8) (h1 : 1 ≤ s.length) (h2 : s.length ≤ 100000)
    (h3 : AllBits s) :
    ∀ r, Aegis.MaxOperations.max_operations s = ok r → (positiveZeroRunCount s.val : ℤ) ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice Std.U8) (h1 : 1 ≤ s.length) (h2 : s.length ≤ 100000)
    (h3 : AllBits s), ∀ r, Aegis.MaxOperations.max_operations s = ok r → (positiveZeroRunCount s.val : ℤ) ≤ r.val) := by
  sorry

/-- Whenever max_operations s returns a result r, the integer value of r is 0 if and only if there is no index i with 0 ≤ i < len(s)-1 such that s[i] = '1' and s[i+1] = '0'.
  Preconditions: len(s) ≥ 1 and len(s) ≤ 100000, and for every i with 0 ≤ i < len(s), s[i] is either '0' (byte 48) or '1' (byte 49). -/
theorem spec_5 (s : Slice Std.U8) (h1 : 1 ≤ s.length) (h2 : s.length ≤ 100000)
    (h3 : AllBits s) :
    ∀ r, Aegis.MaxOperations.max_operations s = ok r →
      (r.val = 0 ↔
        ¬ ∃ i : ℕ, i + 1 < s.length ∧ HasOneAt s.val i ∧ HasZeroAt s.val (i + 1)) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice Std.U8) (h1 : 1 ≤ s.length) (h2 : s.length ≤ 100000)
    (h3 : AllBits s), ∀ r, Aegis.MaxOperations.max_operations s = ok r →
      (r.val = 0 ↔
        ¬ ∃ i : ℕ, i + 1 < s.length ∧ HasOneAt s.val i ∧ HasZeroAt s.val (i + 1))) := by
  sorry

/-- Whenever max_operations s returns a result r, the integer value of r equals c.
  Preconditions: len(s) ≥ 1 and len(s) ≤ 100000, every byte of s is '0' or '1', and s has exactly one maximal contiguous block of '0' bytes. Let a be the start index of that block and let c be the number of indices j with 0 ≤ j < a and s[j] = '1'. -/
theorem spec_6 (s : Slice Std.U8) (h1 : 1 ≤ s.length) (h2 : s.length ≤ 100000)
    (h3 : AllBits s) (a : ℕ) (hstart : IsZeroRunStart s.val a)
    (huniq : ∀ b : ℕ, IsZeroRunStart s.val b → b = a) :
    ∀ r, Aegis.MaxOperations.max_operations s = ok r → r.val = (onesBefore s.val a : ℤ) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice Std.U8) (h1 : 1 ≤ s.length) (h2 : s.length ≤ 100000)
    (h3 : AllBits s) (a : ℕ) (hstart : IsZeroRunStart s.val a)
    (huniq : ∀ b : ℕ, IsZeroRunStart s.val b → b = a), ∀ r, Aegis.MaxOperations.max_operations s = ok r → r.val = (onesBefore s.val a : ℤ)) := by
  sorry

/-- Whenever max_operations s returns a result r, the integer value of r is 1.
  Preconditions: len(s) ≥ 1 and len(s) ≤ 100000, every byte of s is '0' or '1', s contains exactly one '1' byte, and the index i of that byte satisfies i < len(s)-1. -/
theorem spec_7 (s : Slice Std.U8) (h1 : 1 ≤ s.length) (h2 : s.length ≤ 100000)
    (h3 : AllBits s) (i : ℕ) (hone : HasOneAt s.val i)
    (huniq : ∀ j : ℕ, HasOneAt s.val j → j = i) (hlast : i + 1 < s.length) :
    ∀ r, Aegis.MaxOperations.max_operations s = ok r → r.val = 1 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice Std.U8) (h1 : 1 ≤ s.length) (h2 : s.length ≤ 100000)
    (h3 : AllBits s) (i : ℕ) (hone : HasOneAt s.val i)
    (huniq : ∀ j : ℕ, HasOneAt s.val j → j = i) (hlast : i + 1 < s.length), ∀ r, Aegis.MaxOperations.max_operations s = ok r → r.val = 1) := by
  sorry

/-- Whenever max_operations s returns a result r_s and max_operations t returns a result r_t, the integer values are equal: r_t = r_s.
  Preconditions: s satisfies len(s) ≥ 1 and len(s) ≤ 100000, and every byte of s is '0' or '1'. k is a nonnegative integer. t is the slice consisting of k copies of '0' followed by s. t satisfies len(t) ≤ 100000. -/
theorem spec_8 (s t : Slice Std.U8) (k : ℕ) (hs1 : 1 ≤ s.length) (hs2 : s.length ≤ 100000)
    (h3 : AllBits s) (ht : t.val = List.replicate k byteZero ++ s.val)
    (htlen : t.length ≤ 100000) :
    ∀ r_s r_t, Aegis.MaxOperations.max_operations s = ok r_s →
      Aegis.MaxOperations.max_operations t = ok r_t → r_t.val = r_s.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s t : Slice Std.U8) (k : ℕ) (hs1 : 1 ≤ s.length) (hs2 : s.length ≤ 100000)
    (h3 : AllBits s) (ht : t.val = List.replicate k byteZero ++ s.val)
    (htlen : t.length ≤ 100000), ∀ r_s r_t, Aegis.MaxOperations.max_operations s = ok r_s →
      Aegis.MaxOperations.max_operations t = ok r_t → r_t.val = r_s.val) := by
  sorry

/-- Whenever max_operations s returns a result r_s and max_operations t returns a result r_t, if the last byte of s is '1' then r_t = r_s + o(s), and if the last byte of s is '0' then r_t = r_s, where o(s) is the number of '1' bytes in s.
  Preconditions: s satisfies len(s) ≥ 1 and len(s) ≤ 100000, and every byte of s is '0' or '1'. k is an integer with k ≥ 1. t is the slice consisting of s followed by k copies of '0'. t satisfies len(t) ≤ 100000. -/
theorem spec_9 (s t : Slice Std.U8) (k : ℕ) (hk : 1 ≤ k) (hs1 : 1 ≤ s.length)
    (hs2 : s.length ≤ 100000) (h3 : AllBits s) (ht : t.val = s.val ++ List.replicate k byteZero)
    (htlen : t.length ≤ 100000) :
    ∀ r_s r_t, Aegis.MaxOperations.max_operations s = ok r_s →
      Aegis.MaxOperations.max_operations t = ok r_t →
      (byteAt s.val (s.val.length - 1) = some 49 →
          r_t.val = r_s.val + (onesCount s.val : ℤ)) ∧
        (byteAt s.val (s.val.length - 1) = some 48 → r_t.val = r_s.val) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s t : Slice Std.U8) (k : ℕ) (hk : 1 ≤ k) (hs1 : 1 ≤ s.length)
    (hs2 : s.length ≤ 100000) (h3 : AllBits s) (ht : t.val = s.val ++ List.replicate k byteZero)
    (htlen : t.length ≤ 100000), ∀ r_s r_t, Aegis.MaxOperations.max_operations s = ok r_s →
      Aegis.MaxOperations.max_operations t = ok r_t →
      (byteAt s.val (s.val.length - 1) = some 49 →
          r_t.val = r_s.val + (onesCount s.val : ℤ)) ∧
        (byteAt s.val (s.val.length - 1) = some 48 → r_t.val = r_s.val)) := by
  sorry

/-- Whenever max_operations s returns a result r_s and max_operations t returns a result r_t, r_t = r_s + k * z(s), where z(s) is the number of maximal contiguous blocks of '0' bytes in s.
  Preconditions: s satisfies len(s) ≥ 1 and len(s) ≤ 100000, and every byte of s is '0' or '1'. k is an integer with k ≥ 1. t is the slice consisting of k copies of '1' followed by s. t satisfies len(t) ≤ 100000. -/
theorem spec_10 (s t : Slice Std.U8) (k : ℕ) (hk : 1 ≤ k) (hs1 : 1 ≤ s.length)
    (hs2 : s.length ≤ 100000) (h3 : AllBits s) (ht : t.val = List.replicate k byteOne ++ s.val)
    (htlen : t.length ≤ 100000) :
    ∀ r_s r_t, Aegis.MaxOperations.max_operations s = ok r_s →
      Aegis.MaxOperations.max_operations t = ok r_t →
      r_t.val = r_s.val + (k : ℤ) * (zeroRunCount s.val : ℤ) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s t : Slice Std.U8) (k : ℕ) (hk : 1 ≤ k) (hs1 : 1 ≤ s.length)
    (hs2 : s.length ≤ 100000) (h3 : AllBits s) (ht : t.val = List.replicate k byteOne ++ s.val)
    (htlen : t.length ≤ 100000), ∀ r_s r_t, Aegis.MaxOperations.max_operations s = ok r_s →
      Aegis.MaxOperations.max_operations t = ok r_t →
      r_t.val = r_s.val + (k : ℤ) * (zeroRunCount s.val : ℤ)) := by
  sorry

/-- Whenever max_operations s returns a result r, there exists a finite sequence of exactly r allowed operations that can be applied to s. Here an allowed operation on a current string x chooses i with i+1 < len(x), x[i] = '1', and x[i+1] = '0', and moves that '1' right across the following zero block until the end or the next '1'.
  Preconditions: len(s) ≥ 1 and len(s) ≤ 100000, and for every i with 0 ≤ i < len(s), s[i] is either '0' (byte 48) or '1' (byte 49). -/
theorem spec_11 (s : Slice Std.U8) (h1 : 1 ≤ s.length) (h2 : s.length ≤ 100000)
    (h3 : AllBits s) :
    ∀ r, Aegis.MaxOperations.max_operations s = ok r →
      ∃ (n : ℕ) (y : List Std.U8), (n : ℤ) = r.val ∧ ReachesIn n s.val y := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s : Slice Std.U8) (h1 : 1 ≤ s.length) (h2 : s.length ≤ 100000)
    (h3 : AllBits s), ∀ r, Aegis.MaxOperations.max_operations s = ok r →
      ∃ (n : ℕ) (y : List Std.U8), (n : ℤ) = r.val ∧ ReachesIn n s.val y) := by
  sorry

/-- Whenever max_operations s returns a result r, there is no finite sequence of allowed operations applied to s whose length is greater than r. Here an allowed operation on a current string x chooses i with i+1 < len(x), x[i] = '1', and x[i+1] = '0', and moves that '1' right across the following zero block until the end or the next '1'.
  Preconditions: len(s) ≥ 1 and len(s) ≤ 100000, and for every i with 0 ≤ i < len(s), s[i] is either '0' (byte 48) or '1' (byte 49). -/
theorem spec_12 (s : Slice Std.U8) (h1 : 1 ≤ s.length) (h2 : s.length ≤ 100000)
    (h3 : AllBits s) :
    ∀ r, Aegis.MaxOperations.max_operations s = ok r →
      ∀ (n : ℕ) (y : List Std.U8), ReachesIn n s.val y → (n : ℤ) ≤ r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (s : Slice Std.U8) (h1 : 1 ≤ s.length) (h2 : s.length ≤ 100000)
    (h3 : AllBits s), ∀ r, Aegis.MaxOperations.max_operations s = ok r →
      ∀ (n : ℕ) (y : List Std.U8), ReachesIn n s.val y → (n : ℤ) ≤ r.val) := by
  sorry

end AegisSpec.MaxOperations
