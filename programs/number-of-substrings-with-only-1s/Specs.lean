import Aegis.NumSub.Code.Funs

/-!
# Specifications of `Aegis.NumSub.num_sub`

LeetCode problem `number-of-substrings-with-only-1s`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.NumSub

def IsUniqueMod (m c x : ℤ) : Prop :=
  0 ≤ x ∧ x < m ∧ m ∣ (c - x) ∧ ∀ y : ℤ, 0 ≤ y → y < m → m ∣ (c - y) → y = x

def isOneByte (b : Std.U8) : Bool := b.val == 49

def allOneBytes (l : List Std.U8) : Bool := l.all isOneByte

def onesIntervalCount (l : List Std.U8) : Nat :=
  (((List.range l.length).flatMap (fun i => (List.range l.length).map (fun j => (i, j)))).countP
    (fun p => decide (p.1 ≤ p.2) && allOneBytes ((l.drop p.1).take (p.2 + 1 - p.1))))

def onesBlockLengthsAux (cur : Nat) : List Std.U8 → List Nat
  | [] => if cur = 0 then [] else [cur]
  | b :: rest =>
    if isOneByte b then
      onesBlockLengthsAux (cur + 1) rest
    else if cur = 0 then
      onesBlockLengthsAux 0 rest
    else
      cur :: onesBlockLengthsAux 0 rest

def onesBlockLengths (l : List Std.U8) : List Nat := onesBlockLengthsAux 0 l

def blockTriangularSum (l : List Std.U8) : Nat :=
  ((onesBlockLengths l).map (fun L => L * (L + 1) / 2)).sum

def onesRunEndingAt (l : List Std.U8) (i : Nat) : Nat :=
  ((l.take (i + 1)).reverse.takeWhile isOneByte).length

def runLengthSum (l : List Std.U8) : Nat :=
  ((List.range l.length).map (fun i => onesRunEndingAt l i)).sum

def countOneBytes (l : List Std.U8) : Nat := (l.filter isOneByte).length

def sliceWith (s : Slice Std.U8) (l : List Std.U8) (h : l.length ≤ s.val.length) : Slice Std.U8 :=
  ⟨l.length, Aeneas.Data.ListN.ListN.fromList l, by
    have hs : s.val.length ≤ Std.Usize.max := by
      simpa [Slice.val, Aeneas.Data.ListN.ListN_length] using s.bound
    omega⟩

def revSlice (s : Slice Std.U8) : Slice Std.U8 :=
  sliceWith s s.val.reverse (by simp)

def dropLastSlice (s : Slice Std.U8) : Slice Std.U8 :=
  sliceWith s (s.val.take (s.val.length - 1)) (by
    rw [List.length_take]
    exact Nat.min_le_right _ _)

def dropFirstSlice (s : Slice Std.U8) : Slice Std.U8 :=
  sliceWith s (s.val.drop 1) (by
    rw [List.length_drop]
    exact Nat.sub_le _ _)

def prefixSlice (s : Slice Std.U8) (p : Nat) : Slice Std.U8 :=
  sliceWith s (s.val.take p) (by
    rw [List.length_take]
    exact Nat.min_le_right _ _)

def suffixSlice (s : Slice Std.U8) (p : Nat) : Slice Std.U8 :=
  sliceWith s (s.val.drop (p + 1)) (by
    rw [List.length_drop]
    exact Nat.sub_le _ _)

@[simp]
theorem sliceWith_val (s : Slice Std.U8) (l : List Std.U8) (h : l.length ≤ s.val.length) :
    (sliceWith s l h).val = l := by
  simp [sliceWith, Slice.val, Aeneas.Data.ListN.ListN.from_to_inverse]

@[simp]
theorem revSlice_val (s : Slice Std.U8) : (revSlice s).val = s.val.reverse := by
  simp [revSlice]

@[simp]
theorem dropLastSlice_val (s : Slice Std.U8) :
    (dropLastSlice s).val = s.val.take (s.val.length - 1) := by
  simp [dropLastSlice]

@[simp]
theorem dropFirstSlice_val (s : Slice Std.U8) : (dropFirstSlice s).val = s.val.drop 1 := by
  simp [dropFirstSlice]

@[simp]
theorem prefixSlice_val (s : Slice Std.U8) (p : Nat) : (prefixSlice s p).val = s.val.take p := by
  simp [prefixSlice]

@[simp]
theorem suffixSlice_val (s : Slice Std.U8) (p : Nat) :
    (suffixSlice s p).val = s.val.drop (p + 1) := by
  simp [suffixSlice]

/-- Let C(s) be the number of pairs (i, j) such that 0 <= i <= j < len(s) and s[k] = 49 for every k with i <= k <= j. The function returns a result r and r is the unique integer satisfying 0 <= r < 1000000007 and C(s) - r is divisible by 1000000007.
  Preconditions: 1 <= len(s) <= 100000 and for every i with 0 <= i < len(s), s[i] = 48 ('0') or s[i] = 49 ('1'). -/
theorem spec_1 (s : Slice Std.U8)
    (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
    (hbits : ∀ b ∈ s.val, b.val = 48 ∨ b.val = 49) :
    ∃ r : Std.I64,
      Aegis.NumSub.num_sub s = ok r ∧
        IsUniqueMod 1000000007 (onesIntervalCount s.val : ℤ) r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
    (hbits : ∀ b ∈ s.val, b.val = 48 ∨ b.val = 49), ∃ r : Std.I64,
      Aegis.NumSub.num_sub s = ok r ∧
        IsUniqueMod 1000000007 (onesIntervalCount s.val : ℤ) r.val) := by
  sorry

/-- For every input s satisfying the preconditions, the function returns a result r (it does not fail, panic, or overflow).
  Preconditions: 1 <= len(s) <= 100000 and for every i with 0 <= i < len(s), s[i] = 48 ('0') or s[i] = 49 ('1'). -/
theorem spec_2 (s : Slice Std.U8)
    (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
    (hbits : ∀ b ∈ s.val, b.val = 48 ∨ b.val = 49) :
    ∃ r : Std.I64, Aegis.NumSub.num_sub s = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
    (hbits : ∀ b ∈ s.val, b.val = 48 ∨ b.val = 49), ∃ r : Std.I64, Aegis.NumSub.num_sub s = ok r) := by
  sorry

/-- Whenever the function returns a result r on an input satisfying the preconditions, 0 <= r <= 1000000006.
  Preconditions: 1 <= len(s) <= 100000 and for every i with 0 <= i < len(s), s[i] = 48 ('0') or s[i] = 49 ('1'). -/
theorem spec_3 (s : Slice Std.U8)
    (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
    (hbits : ∀ b ∈ s.val, b.val = 48 ∨ b.val = 49) :
    ∀ r : Std.I64, Aegis.NumSub.num_sub s = ok r → 0 ≤ r.val ∧ r.val ≤ 1000000006 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
    (hbits : ∀ b ∈ s.val, b.val = 48 ∨ b.val = 49), ∀ r : Std.I64, Aegis.NumSub.num_sub s = ok r → 0 ≤ r.val ∧ r.val ≤ 1000000006) := by
  sorry

/-- The function returns a result r and r = 0.
  Preconditions: 1 <= len(s) <= 100000 and for every i with 0 <= i < len(s), s[i] = 48 ('0'). -/
theorem spec_4 (s : Slice Std.U8)
    (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
    (hbytes : ∀ b ∈ s.val, b.val = 48) :
    ∃ r : Std.I64, Aegis.NumSub.num_sub s = ok r ∧ r.val = 0 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
    (hbytes : ∀ b ∈ s.val, b.val = 48), ∃ r : Std.I64, Aegis.NumSub.num_sub s = ok r ∧ r.val = 0) := by
  sorry

/-- The function returns a result r and r is the unique integer satisfying 0 <= r < 1000000007 and n(n+1)/2 - r is divisible by 1000000007.
  Preconditions: 1 <= len(s) <= 100000 and for every i with 0 <= i < len(s), s[i] = 49 ('1'). Let n = len(s). -/
theorem spec_5 (s : Slice Std.U8)
    (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
    (hbytes : ∀ b ∈ s.val, b.val = 49) :
    ∃ r : Std.I64,
      Aegis.NumSub.num_sub s = ok r ∧
        IsUniqueMod 1000000007 (((s.val.length : ℤ) * ((s.val.length : ℤ) + 1)) / 2) r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
    (hbytes : ∀ b ∈ s.val, b.val = 49), ∃ r : Std.I64,
      Aegis.NumSub.num_sub s = ok r ∧
        IsUniqueMod 1000000007 (((s.val.length : ℤ) * ((s.val.length : ℤ) + 1)) / 2) r.val) := by
  sorry

/-- Let L_1, ..., L_m be the lengths of the maximal contiguous blocks of bytes equal to 49 in s, in left-to-right order; if no such block exists then m = 0. The function returns a result r such that r is the unique integer satisfying 0 <= r < 1000000007 and (sum_{t=1..m} L_t(L_t+1)/2) - r is divisible by 1000000007.
  Preconditions: 1 <= len(s) <= 100000 and for every i with 0 <= i < len(s), s[i] = 48 ('0') or s[i] = 49 ('1'). -/
theorem spec_6 (s : Slice Std.U8)
    (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
    (hbits : ∀ b ∈ s.val, b.val = 48 ∨ b.val = 49) :
    ∃ r : Std.I64,
      Aegis.NumSub.num_sub s = ok r ∧
        IsUniqueMod 1000000007 (blockTriangularSum s.val : ℤ) r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
    (hbits : ∀ b ∈ s.val, b.val = 48 ∨ b.val = 49), ∃ r : Std.I64,
      Aegis.NumSub.num_sub s = ok r ∧
        IsUniqueMod 1000000007 (blockTriangularSum s.val : ℤ) r.val) := by
  sorry

/-- For each i with 0 <= i < len(s), define e_i = 0 if s[i] != 49, and otherwise let e_i be the largest l such that 1 <= l <= i+1 and s[k] = 49 for every k with i-l+1 <= k <= i. The function returns a result r such that r is the unique integer satisfying 0 <= r < 1000000007 and (sum_{i=0..len(s)-1} e_i) - r is divisible by 1000000007.
  Preconditions: 1 <= len(s) <= 100000 and for every i with 0 <= i < len(s), s[i] = 48 ('0') or s[i] = 49 ('1'). -/
theorem spec_7 (s : Slice Std.U8)
    (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
    (hbits : ∀ b ∈ s.val, b.val = 48 ∨ b.val = 49) :
    ∃ r : Std.I64,
      Aegis.NumSub.num_sub s = ok r ∧
        IsUniqueMod 1000000007 (runLengthSum s.val : ℤ) r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
    (hbits : ∀ b ∈ s.val, b.val = 48 ∨ b.val = 49), ∃ r : Std.I64,
      Aegis.NumSub.num_sub s = ok r ∧
        IsUniqueMod 1000000007 (runLengthSum s.val : ℤ) r.val) := by
  sorry

/-- Let rev(s) be the byte slice of length len(s) with rev(s)[i] = s[len(s)-1-i] for 0 <= i < len(s). For every valid input s, if r is the result returned for s and r_rev is the result returned for rev(s), then r = r_rev.
  Preconditions: 1 <= len(s) <= 100000 and for every i with 0 <= i < len(s), s[i] = 48 ('0') or s[i] = 49 ('1'). -/
theorem spec_8 (s : Slice Std.U8)
    (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
    (hbits : ∀ b ∈ s.val, b.val = 48 ∨ b.val = 49) :
    ∃ r r_rev : Std.I64,
      Aegis.NumSub.num_sub s = ok r ∧ Aegis.NumSub.num_sub (revSlice s) = ok r_rev ∧
        r = r_rev := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
    (hbits : ∀ b ∈ s.val, b.val = 48 ∨ b.val = 49), ∃ r r_rev : Std.I64,
      Aegis.NumSub.num_sub s = ok r ∧ Aegis.NumSub.num_sub (revSlice s) = ok r_rev ∧
        r = r_rev) := by
  sorry

/-- Let t be the slice of length len(s)-1 with t[i] = s[i] for 0 <= i < len(s)-1. The function returns a result r for s, the function returns a result r_t for t, and r = r_t.
  Preconditions: 1 <= len(s) <= 100000, for every i with 0 <= i < len(s), s[i] = 48 ('0') or s[i] = 49 ('1'), len(s) >= 2, and s[len(s)-1] = 48 ('0'). -/
theorem spec_9 (s : Slice Std.U8)
    (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
    (hbits : ∀ b ∈ s.val, b.val = 48 ∨ b.val = 49)
    (hlen_two : 2 ≤ s.val.length)
    (hlast : (s.val[s.val.length - 1]'(by omega)).val = 48) :
    ∃ r r_t : Std.I64,
      Aegis.NumSub.num_sub s = ok r ∧ Aegis.NumSub.num_sub (dropLastSlice s) = ok r_t ∧
        r = r_t := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
    (hbits : ∀ b ∈ s.val, b.val = 48 ∨ b.val = 49)
    (hlen_two : 2 ≤ s.val.length)
    (hlast : (s.val[s.val.length - 1]'(by omega)).val = 48), ∃ r r_t : Std.I64,
      Aegis.NumSub.num_sub s = ok r ∧ Aegis.NumSub.num_sub (dropLastSlice s) = ok r_t ∧
        r = r_t) := by
  sorry

/-- Let t be the slice of length len(s)-1 with t[i] = s[i+1] for 0 <= i < len(s)-1. The function returns a result r for s, the function returns a result r_t for t, and r = r_t.
  Preconditions: 1 <= len(s) <= 100000, for every i with 0 <= i < len(s), s[i] = 48 ('0') or s[i] = 49 ('1'), len(s) >= 2, and s[0] = 48 ('0'). -/
theorem spec_10 (s : Slice Std.U8)
    (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
    (hbits : ∀ b ∈ s.val, b.val = 48 ∨ b.val = 49)
    (hlen_two : 2 ≤ s.val.length)
    (hfirst : (s.val[0]'(by omega)).val = 48) :
    ∃ r r_t : Std.I64,
      Aegis.NumSub.num_sub s = ok r ∧ Aegis.NumSub.num_sub (dropFirstSlice s) = ok r_t ∧
        r = r_t := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
    (hbits : ∀ b ∈ s.val, b.val = 48 ∨ b.val = 49)
    (hlen_two : 2 ≤ s.val.length)
    (hfirst : (s.val[0]'(by omega)).val = 48), ∃ r r_t : Std.I64,
      Aegis.NumSub.num_sub s = ok r ∧ Aegis.NumSub.num_sub (dropFirstSlice s) = ok r_t ∧
        r = r_t) := by
  sorry

/-- For every integer p with 0 < p < len(s)-1 and s[p] = 48 ('0'), let left be the slice of length p with left[i] = s[i] for 0 <= i < p, and let right be the slice of length len(s)-p-1 with right[i] = s[p+1+i] for 0 <= i < len(s)-p-1. Let r, r_L, r_R be the results returned for s, left, right respectively. Then r = (r_L + r_R) mod 1000000007.
  Preconditions: 1 <= len(s) <= 100000 and for every i with 0 <= i < len(s), s[i] = 48 ('0') or s[i] = 49 ('1'). -/
theorem spec_11 (s : Slice Std.U8)
    (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
    (hbits : ∀ b ∈ s.val, b.val = 48 ∨ b.val = 49)
    (p : Nat) (hp_pos : 0 < p) (hp_len : p < s.val.length - 1)
    (hp_val : (s.val[p]'(by omega)).val = 48) :
    ∃ r r_L r_R : Std.I64,
      Aegis.NumSub.num_sub s = ok r ∧
        Aegis.NumSub.num_sub (prefixSlice s p) = ok r_L ∧
          Aegis.NumSub.num_sub (suffixSlice s p) = ok r_R ∧
            r.val = (r_L.val + r_R.val) % 1000000007 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
    (hbits : ∀ b ∈ s.val, b.val = 48 ∨ b.val = 49)
    (p : Nat) (hp_pos : 0 < p) (hp_len : p < s.val.length - 1)
    (hp_val : (s.val[p]'(by omega)).val = 48), ∃ r r_L r_R : Std.I64,
      Aegis.NumSub.num_sub s = ok r ∧
        Aegis.NumSub.num_sub (prefixSlice s p) = ok r_L ∧
          Aegis.NumSub.num_sub (suffixSlice s p) = ok r_R ∧
            r.val = (r_L.val + r_R.val) % 1000000007) := by
  sorry

/-- The function returns a result r and r = the number of indices i with 0 <= i < len(s) and s[i] = 49 ('1').
  Preconditions: 1 <= len(s) <= 100000, for every i with 0 <= i < len(s), s[i] = 48 ('0') or s[i] = 49 ('1'), and for every i with 0 <= i < len(s)-1, it is not the case that s[i] = 49 and s[i+1] = 49. -/
theorem spec_12 (s : Slice Std.U8)
    (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
    (hbits : ∀ b ∈ s.val, b.val = 48 ∨ b.val = 49)
    (hsep : ∀ (i : Nat) (_hi : i < s.val.length - 1),
      ¬((s.val[i]'(by omega)).val = 49 ∧ (s.val[i + 1]'(by omega)).val = 49)) :
    ∃ r : Std.I64,
      Aegis.NumSub.num_sub s = ok r ∧ r.val = (countOneBytes s.val : ℤ) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
    (hbits : ∀ b ∈ s.val, b.val = 48 ∨ b.val = 49)
    (hsep : ∀ (i : Nat) (_hi : i < s.val.length - 1),
      ¬((s.val[i]'(by omega)).val = 49 ∧ (s.val[i + 1]'(by omega)).val = 49)), ∃ r : Std.I64,
      Aegis.NumSub.num_sub s = ok r ∧ r.val = (countOneBytes s.val : ℤ)) := by
  sorry

/-- Let C(s) be the number of pairs (i, j) such that 0 <= i <= j < len(s) and s[k] = 49 for every k with i <= k <= j. If len(s) <= 44720, then the function returns a result r and r = C(s) exactly.
  Preconditions: 1 <= len(s) <= 100000 and for every i with 0 <= i < len(s), s[i] = 48 ('0') or s[i] = 49 ('1'). -/
theorem spec_13 (s : Slice Std.U8)
    (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
    (hbits : ∀ b ∈ s.val, b.val = 48 ∨ b.val = 49)
    (hsmall : s.val.length ≤ 44720) :
    ∃ r : Std.I64,
      Aegis.NumSub.num_sub s = ok r ∧ r.val = (onesIntervalCount s.val : ℤ) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
    (hbits : ∀ b ∈ s.val, b.val = 48 ∨ b.val = 49)
    (hsmall : s.val.length ≤ 44720), ∃ r : Std.I64,
      Aegis.NumSub.num_sub s = ok r ∧ r.val = (onesIntervalCount s.val : ℤ)) := by
  sorry

/-- Whenever the function returns a result r on an input satisfying the preconditions, r <= len(s)(len(s)+1)/2.
  Preconditions: 1 <= len(s) <= 100000 and for every i with 0 <= i < len(s), s[i] = 48 ('0') or s[i] = 49 ('1'). -/
theorem spec_14 (s : Slice Std.U8)
    (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
    (hbits : ∀ b ∈ s.val, b.val = 48 ∨ b.val = 49) :
    ∀ r : Std.I64, Aegis.NumSub.num_sub s = ok r →
      r.val ≤ ((s.val.length : ℤ) * ((s.val.length : ℤ) + 1)) / 2 := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
    (hbits : ∀ b ∈ s.val, b.val = 48 ∨ b.val = 49), ∀ r : Std.I64, Aegis.NumSub.num_sub s = ok r →
      r.val ≤ ((s.val.length : ℤ) * ((s.val.length : ℤ) + 1)) / 2) := by
  sorry

end AegisSpec.NumSub
