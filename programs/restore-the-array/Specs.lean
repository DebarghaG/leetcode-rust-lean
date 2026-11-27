import Aegis.NumberOfArrays.Code.Funs

/-!
# Specifications of `Aegis.NumberOfArrays.number_of_arrays`

LeetCode problem `restore-the-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.NumberOfArrays

def MODULUS : Nat := 1000000007

def IsResidue (r : Int) (c : Nat) : Prop :=
  0 ≤ r ∧ r < (MODULUS : Int) ∧ r ≡ (c : Int) [ZMOD (MODULUS : Int)]

def digitsVal (ds : List Nat) : Nat := ds.foldl (fun acc d => acc * 10 + d) 0

def countArrays (ds : List Nat) (k : Nat) : Nat :=
  match ds with
  | [] => 1
  | d :: ds' =>
    if d = 0 then 0
    else
      ((List.range (ds'.length + 1)).map (fun i =>
        let v := digitsVal ((d :: ds').take (i + 1))
        if 1 ≤ v ∧ v ≤ k then countArrays ((d :: ds').drop (i + 1)) k else 0)).sum
  termination_by ds.length
  decreasing_by
    simp [List.length_drop]

def digits (s : Slice U8) : List Nat := s.val.map (fun b => b.val - 48)

def digit (s : Slice U8) (i : Nat) : Nat := (s.val.getD i default).val - 48

def numArrays (s : Slice U8) (k : Int) : Nat := countArrays (digits s) k.toNat

def nonzeroTailCount (s : Slice U8) : Nat :=
  ((List.range s.val.length).filter (fun p => 1 ≤ p ∧ (s.val.getD p default).val ≠ 48)).length

/-- Whenever the function returns a result r, r is the unique integer such that 0 <= r < 1000000007 and r is congruent modulo 1000000007 to C(s,k), where C(s,k) is the number of finite sequences A = (a_1, ..., a_m) with m >= 1, each a_j an integer satisfying 1 <= a_j <= k, such that the concatenation of the standard decimal representations of a_1, ..., a_m (each written without leading zeros) is exactly s.
  Preconditions: 1 <= len(s) <= 100000; for every i with 0 <= i < len(s), s[i] is an ASCII digit (48 <= s[i] <= 57); s[0] != 48 (no leading zero); 1 <= k <= 1000000000. -/
theorem spec_1 (s : Slice U8) (k : I64)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 100000)
    (hdig : ∀ (i : Nat) (hi : i < s.val.length),
      48 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 57)
    (hlead : (s.val.get ⟨0, by omega⟩).val ≠ 48)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 1000000000) :
    ∀ r, Aegis.NumberOfArrays.number_of_arrays s k = ok r →
      IsResidue r.val (numArrays s k.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice U8) (k : I64)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 100000)
    (hdig : ∀ (i : Nat) (hi : i < s.val.length),
      48 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 57)
    (hlead : (s.val.get ⟨0, by omega⟩).val ≠ 48)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 1000000000), ∀ r, Aegis.NumberOfArrays.number_of_arrays s k = ok r →
      IsResidue r.val (numArrays s k.val)) := by
  sorry

/-- The function returns a result r; it does not fail (no overflow, out-of-bounds access, or panic) for every input satisfying the preconditions.
  Preconditions: 1 <= len(s) <= 100000; for every i with 0 <= i < len(s), s[i] is an ASCII digit (48 <= s[i] <= 57); s[0] != 48 (no leading zero); 1 <= k <= 1000000000. -/
theorem spec_2 (s : Slice U8) (k : I64)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 100000)
    (hdig : ∀ (i : Nat) (hi : i < s.val.length),
      48 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 57)
    (hlead : (s.val.get ⟨0, by omega⟩).val ≠ 48)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 1000000000) :
    ∃ r, Aegis.NumberOfArrays.number_of_arrays s k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice U8) (k : I64)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 100000)
    (hdig : ∀ (i : Nat) (hi : i < s.val.length),
      48 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 57)
    (hlead : (s.val.get ⟨0, by omega⟩).val ≠ 48)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 1000000000), ∃ r, Aegis.NumberOfArrays.number_of_arrays s k = ok r) := by
  sorry

/-- Whenever the function returns a result r, r = 1 if (s[0] - 48) <= k, and r = 0 otherwise.
  Preconditions: 1 <= len(s) <= 100000; for every i with 0 <= i < len(s), s[i] is an ASCII digit (48 <= s[i] <= 57); s[0] != 48 (no leading zero); 1 <= k <= 1000000000; len(s) = 1. -/
theorem spec_3 (s : Slice U8) (k : I64)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 100000)
    (hdig : ∀ (i : Nat) (hi : i < s.val.length),
      48 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 57)
    (hlead : (s.val.get ⟨0, by omega⟩).val ≠ 48)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 1000000000)
    (hlen : s.val.length = 1) :
    ∀ r, Aegis.NumberOfArrays.number_of_arrays s k = ok r →
      r.val = if (digit s 0 : Int) ≤ k.val then 1 else 0 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice U8) (k : I64)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 100000)
    (hdig : ∀ (i : Nat) (hi : i < s.val.length),
      48 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 57)
    (hlead : (s.val.get ⟨0, by omega⟩).val ≠ 48)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 1000000000)
    (hlen : s.val.length = 1), ∀ r, Aegis.NumberOfArrays.number_of_arrays s k = ok r →
      r.val = if (digit s 0 : Int) ≤ k.val then 1 else 0) := by
  sorry

/-- Whenever the function returns a result r, r = 1 if for every i with 0 <= i < len(s) we have 1 <= (s[i] - 48) <= k; otherwise r = 0.
  Preconditions: 1 <= len(s) <= 100000; for every i with 0 <= i < len(s), s[i] is an ASCII digit (48 <= s[i] <= 57); s[0] != 48 (no leading zero); 1 <= k <= 9. -/
theorem spec_4 (s : Slice U8) (k : I64)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 100000)
    (hdig : ∀ (i : Nat) (hi : i < s.val.length),
      48 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 57)
    (hlead : (s.val.get ⟨0, by omega⟩).val ≠ 48)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 1000000000) (hk9 : k.val ≤ 9) :
    ∀ r, Aegis.NumberOfArrays.number_of_arrays s k = ok r →
      r.val = if (∀ (i : Nat) (hi : i < s.val.length),
          1 ≤ (digit s i : Int) ∧ (digit s i : Int) ≤ k.val) then 1 else 0 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice U8) (k : I64)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 100000)
    (hdig : ∀ (i : Nat) (hi : i < s.val.length),
      48 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 57)
    (hlead : (s.val.get ⟨0, by omega⟩).val ≠ 48)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 1000000000) (hk9 : k.val ≤ 9), ∀ r, Aegis.NumberOfArrays.number_of_arrays s k = ok r →
      r.val = if (∀ (i : Nat) (hi : i < s.val.length),
          1 ≤ (digit s i : Int) ∧ (digit s i : Int) ≤ k.val) then 1 else 0) := by
  sorry

/-- Whenever the function returns a result r, let d0 = s[0] - 48 and d1 = s[1] - 48. Then r = A + B, where A = 1 if 10*d0 + d1 <= k and A = 0 otherwise, and B = 1 if d0 <= k and 1 <= d1 <= k and B = 0 otherwise.
  Preconditions: 1 <= len(s) <= 100000; for every i with 0 <= i < len(s), s[i] is an ASCII digit (48 <= s[i] <= 57); s[0] != 48 (no leading zero); 1 <= k <= 1000000000; len(s) = 2. -/
theorem spec_5 (s : Slice U8) (k : I64)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 100000)
    (hdig : ∀ (i : Nat) (hi : i < s.val.length),
      48 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 57)
    (hlead : (s.val.get ⟨0, by omega⟩).val ≠ 48)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 1000000000)
    (hlen : s.val.length = 2) :
    ∀ r, Aegis.NumberOfArrays.number_of_arrays s k = ok r →
      r.val = (if (10 * digit s 0 + digit s 1 : Int) ≤ k.val then 1 else 0) +
        (if (digit s 0 : Int) ≤ k.val ∧ 1 ≤ (digit s 1 : Int) ∧ (digit s 1 : Int) ≤ k.val
         then 1 else 0) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice U8) (k : I64)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 100000)
    (hdig : ∀ (i : Nat) (hi : i < s.val.length),
      48 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 57)
    (hlead : (s.val.get ⟨0, by omega⟩).val ≠ 48)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 1000000000)
    (hlen : s.val.length = 2), ∀ r, Aegis.NumberOfArrays.number_of_arrays s k = ok r →
      r.val = (if (10 * digit s 0 + digit s 1 : Int) ≤ k.val then 1 else 0) +
        (if (digit s 0 : Int) ≤ k.val ∧ 1 ≤ (digit s 1 : Int) ∧ (digit s 1 : Int) ≤ k.val
         then 1 else 0)) := by
  sorry

/-- Whenever the function returns a result r, r = (2^z) mod 1000000007, where z is the number of indices p with 1 <= p < len(s) and s[p] != 48.
  Preconditions: 1 <= len(s) <= 100000; for every i with 0 <= i < len(s), s[i] is an ASCII digit (48 <= s[i] <= 57); s[0] != 48 (no leading zero); 1 <= k <= 1000000000; len(s) <= 9 and k >= 10^len(s) - 1. -/
theorem spec_6 (s : Slice U8) (k : I64)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 100000)
    (hdig : ∀ (i : Nat) (hi : i < s.val.length),
      48 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 57)
    (hlead : (s.val.get ⟨0, by omega⟩).val ≠ 48)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 1000000000)
    (hlen9 : s.val.length ≤ 9)
    (hk_big : ((10 ^ s.val.length - 1 : Nat) : Int) ≤ k.val) :
    ∀ r, Aegis.NumberOfArrays.number_of_arrays s k = ok r →
      r.val = (((2 ^ nonzeroTailCount s) % MODULUS : Nat) : Int) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice U8) (k : I64)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 100000)
    (hdig : ∀ (i : Nat) (hi : i < s.val.length),
      48 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 57)
    (hlead : (s.val.get ⟨0, by omega⟩).val ≠ 48)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 1000000000)
    (hlen9 : s.val.length ≤ 9)
    (hk_big : ((10 ^ s.val.length - 1 : Nat) : Int) ≤ k.val), ∀ r, Aegis.NumberOfArrays.number_of_arrays s k = ok r →
      r.val = (((2 ^ nonzeroTailCount s) % MODULUS : Nat) : Int)) := by
  sorry

/-- Let C(s,k) be the number of valid arrays, i.e. finite sequences of integers in [1,k] whose standard decimal representations concatenate to s. Whenever the function returns a result r, 0 <= C(s,k) <= 2^(len(s)-1), and r is the residue of C(s,k) modulo 1000000007.
  Preconditions: 1 <= len(s) <= 100000; for every i with 0 <= i < len(s), s[i] is an ASCII digit (48 <= s[i] <= 57); s[0] != 48 (no leading zero); 1 <= k <= 1000000000. -/
theorem spec_7 (s : Slice U8) (k : I64)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 100000)
    (hdig : ∀ (i : Nat) (hi : i < s.val.length),
      48 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 57)
    (hlead : (s.val.get ⟨0, by omega⟩).val ≠ 48)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 1000000000) :
    ∀ r, Aegis.NumberOfArrays.number_of_arrays s k = ok r →
      0 ≤ numArrays s k.val ∧
        numArrays s k.val ≤ 2 ^ (s.val.length - 1) ∧
        IsResidue r.val (numArrays s k.val) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice U8) (k : I64)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 100000)
    (hdig : ∀ (i : Nat) (hi : i < s.val.length),
      48 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 57)
    (hlead : (s.val.get ⟨0, by omega⟩).val ≠ 48)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 1000000000), ∀ r, Aegis.NumberOfArrays.number_of_arrays s k = ok r →
      0 ≤ numArrays s k.val ∧
        numArrays s k.val ≤ 2 ^ (s.val.length - 1) ∧
        IsResidue r.val (numArrays s k.val)) := by
  sorry

/-- Let C(s,k) be the number of valid arrays for the same string s. If the function returns r1 on input (s,k1) and r2 on input (s,k2), then r1 and r2 are residues modulo 1000000007 of C(s,k1) and C(s,k2), and C(s,k1) <= C(s,k2).
  Preconditions: 1 <= len(s) <= 100000; for every i with 0 <= i < len(s), s[i] is an ASCII digit (48 <= s[i] <= 57); s[0] != 48 (no leading zero); 1 <= k1 <= k2 <= 1000000000. -/
theorem spec_8 (s : Slice U8) (k1 : I64) (k2 : I64)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 100000)
    (hdig : ∀ (i : Nat) (hi : i < s.val.length),
      48 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 57)
    (hlead : (s.val.get ⟨0, by omega⟩).val ≠ 48)
    (hk1_lo : 1 ≤ k1.val) (hk12 : k1.val ≤ k2.val) (hk2_hi : k2.val ≤ 1000000000) :
    ∀ r1 r2, Aegis.NumberOfArrays.number_of_arrays s k1 = ok r1 →
      Aegis.NumberOfArrays.number_of_arrays s k2 = ok r2 →
      IsResidue r1.val (numArrays s k1.val) ∧
        IsResidue r2.val (numArrays s k2.val) ∧
        numArrays s k1.val ≤ numArrays s k2.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s : Slice U8) (k1 : I64) (k2 : I64)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 100000)
    (hdig : ∀ (i : Nat) (hi : i < s.val.length),
      48 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 57)
    (hlead : (s.val.get ⟨0, by omega⟩).val ≠ 48)
    (hk1_lo : 1 ≤ k1.val) (hk12 : k1.val ≤ k2.val) (hk2_hi : k2.val ≤ 1000000000), ∀ r1 r2, Aegis.NumberOfArrays.number_of_arrays s k1 = ok r1 →
      Aegis.NumberOfArrays.number_of_arrays s k2 = ok r2 →
      IsResidue r1.val (numArrays s k1.val) ∧
        IsResidue r2.val (numArrays s k2.val) ∧
        numArrays s k1.val ≤ numArrays s k2.val) := by
  sorry

end AegisSpec.NumberOfArrays
