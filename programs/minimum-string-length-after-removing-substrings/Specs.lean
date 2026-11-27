import Aegis.MinLength.Code.Funs

/-!
# Specifications of `Aegis.MinLength.min_length`

LeetCode problem `minimum-string-length-after-removing-substrings`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinLength

def IsAllowedPair (a b : Std.U8) : Prop :=
  (a.val = 65 ∧ b.val = 66) ∨ (a.val = 67 ∧ b.val = 68)

def Deletes1 (l t : List Std.U8) : Prop :=
  ∃ (p : List Std.U8) (a b : Std.U8) (q : List Std.U8),
    l = p ++ a :: b :: q ∧ t = p ++ q ∧ IsAllowedPair a b

inductive DeletesIn : ℕ → List Std.U8 → List Std.U8 → Prop where
  | refl (l : List Std.U8) : DeletesIn 0 l l
  | step {k : ℕ} {l m t : List Std.U8} :
      Deletes1 l m → DeletesIn k m t → DeletesIn (k + 1) l t

def Obtainable (l t : List Std.U8) : Prop := Relation.ReflTransGen Deletes1 l t

def IsMinLen (l : List Std.U8) (n : ℤ) : Prop :=
  (∃ t, Obtainable l t ∧ (t.length : ℤ) = n) ∧
    ∀ t, Obtainable l t → n ≤ (t.length : ℤ)

def Irreducible (l : List Std.U8) : Prop :=
  ∀ (i : ℕ) (h : i + 1 < l.length),
    ¬ IsAllowedPair (l.get ⟨i, Nat.lt_of_succ_lt h⟩) (l.get ⟨i + 1, h⟩)

def countByte (l : List Std.U8) (v : ℕ) : ℕ := (l.filter (fun b => b.val == v)).length

def isSpecialByte (b : Std.U8) : Bool :=
  b.val == 65 || b.val == 66 || b.val == 67 || b.val == 68

def IsSpecial (b : Std.U8) : Prop := isSpecialByte b = true

def neutralCount (l : List Std.U8) : ℕ := (l.filter (fun b => !isSpecialByte b)).length

def nonSpecial (l : List Std.U8) : List Std.U8 := l.filter (fun b => !isSpecialByte b)

def balanceAB (l : List Std.U8) : ℤ := (countByte l 65 : ℤ) - (countByte l 66 : ℤ)

def balanceCD (l : List Std.U8) : ℤ := (countByte l 67 : ℤ) - (countByte l 68 : ℤ)

def InsertsPair (l u : List Std.U8) : Prop :=
  ∃ (p q : List Std.U8) (a b : Std.U8),
    l = p ++ q ∧ u = p ++ a :: b :: q ∧ IsAllowedPair a b

/-- For any byte string t, say that t is obtainable from s if there are k >= 0 and byte strings s0, s1, ..., sk with s0 = s, sk = t, and for each j < k, s(j+1) is obtained from sj by deleting two adjacent bytes that are either (65,66) or (67,68), then concatenating the part before them with the part after them. The function returns a result r such that, viewing r as an integer, r = min{ len(t) | t is obtainable from s }. Consequently some obtainable t has len(t) = r, and no obtainable t has len(t) < r.
  Preconditions: 1 <= len(s) <= 100; for every i with 0 <= i < len(s), 65 <= s[i] <= 90. -/
theorem spec_1 (s : Slice Std.U8)
    (hlen_low : 1 ≤ s.val.length) (hlen_high : s.val.length ≤ 100)
    (hbytes : ∀ b ∈ s.val, 65 ≤ b.val ∧ b.val ≤ 90) :
    ∃ r : Std.I64,
      Aegis.MinLength.min_length s = ok r ∧
        IsMinLen s.val r.val ∧
        (∃ t, Obtainable s.val t ∧ (t.length : ℤ) = r.val) ∧
        (∀ t, Obtainable s.val t → r.val ≤ (t.length : ℤ)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_low : 1 ≤ s.val.length) (hlen_high : s.val.length ≤ 100)
    (hbytes : ∀ b ∈ s.val, 65 ≤ b.val ∧ b.val ≤ 90), ∃ r : Std.I64,
      Aegis.MinLength.min_length s = ok r ∧
        IsMinLen s.val r.val ∧
        (∃ t, Obtainable s.val t ∧ (t.length : ℤ) = r.val) ∧
        (∀ t, Obtainable s.val t → r.val ≤ (t.length : ℤ))) := by
  sorry

/-- For every s satisfying the preconditions, the function returns a result r and does not fail: there is no panic, no arithmetic overflow, and no out-of-bounds access.
  Preconditions: 1 <= len(s) <= 100; for every i with 0 <= i < len(s), 65 <= s[i] <= 90. -/
theorem spec_2 (s : Slice Std.U8)
    (hlen_low : 1 ≤ s.val.length) (hlen_high : s.val.length ≤ 100)
    (hbytes : ∀ b ∈ s.val, 65 ≤ b.val ∧ b.val ≤ 90) :
    ∃ r : Std.I64, Aegis.MinLength.min_length s = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_low : 1 ≤ s.val.length) (hlen_high : s.val.length ≤ 100)
    (hbytes : ∀ b ∈ s.val, 65 ≤ b.val ∧ b.val ≤ 90), ∃ r : Std.I64, Aegis.MinLength.min_length s = ok r) := by
  sorry

/-- The function returns a result r, and 0 <= r <= len(s).
  Preconditions: 1 <= len(s) <= 100; for every i with 0 <= i < len(s), 65 <= s[i] <= 90. -/
theorem spec_3 (s : Slice Std.U8)
    (hlen_low : 1 ≤ s.val.length) (hlen_high : s.val.length ≤ 100)
    (hbytes : ∀ b ∈ s.val, 65 ≤ b.val ∧ b.val ≤ 90) :
    ∃ r : Std.I64,
      Aegis.MinLength.min_length s = ok r ∧ 0 ≤ r.val ∧ r.val ≤ (s.val.length : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_low : 1 ≤ s.val.length) (hlen_high : s.val.length ≤ 100)
    (hbytes : ∀ b ∈ s.val, 65 ≤ b.val ∧ b.val ≤ 90), ∃ r : Std.I64,
      Aegis.MinLength.min_length s = ok r ∧ 0 ≤ r.val ∧ r.val ≤ (s.val.length : ℤ)) := by
  sorry

/-- The function returns a result r, and len(s) - r is even; equivalently, r and len(s) have the same parity.
  Preconditions: 1 <= len(s) <= 100; for every i with 0 <= i < len(s), 65 <= s[i] <= 90. -/
theorem spec_4 (s : Slice Std.U8)
    (hlen_low : 1 ≤ s.val.length) (hlen_high : s.val.length ≤ 100)
    (hbytes : ∀ b ∈ s.val, 65 ≤ b.val ∧ b.val ≤ 90) :
    ∃ r : Std.I64,
      Aegis.MinLength.min_length s = ok r ∧ ∃ k : ℤ, (s.val.length : ℤ) = r.val + 2 * k := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_low : 1 ≤ s.val.length) (hlen_high : s.val.length ≤ 100)
    (hbytes : ∀ b ∈ s.val, 65 ≤ b.val ∧ b.val ≤ 90), ∃ r : Std.I64,
      Aegis.MinLength.min_length s = ok r ∧ ∃ k : ℤ, (s.val.length : ℤ) = r.val + 2 * k) := by
  sorry

/-- The function returns a result r, and for every byte string t obtainable from s by zero or more allowed deletions, if t contains no adjacent pair (65,66) and no adjacent pair (67,68), then len(t) = r.
  Preconditions: 1 <= len(s) <= 100; for every i with 0 <= i < len(s), 65 <= s[i] <= 90. -/
theorem spec_5 (s : Slice Std.U8)
    (hlen_low : 1 ≤ s.val.length) (hlen_high : s.val.length ≤ 100)
    (hbytes : ∀ b ∈ s.val, 65 ≤ b.val ∧ b.val ≤ 90) :
    ∃ r : Std.I64,
      Aegis.MinLength.min_length s = ok r ∧
        ∀ t, Obtainable s.val t → Irreducible t → (t.length : ℤ) = r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_low : 1 ≤ s.val.length) (hlen_high : s.val.length ≤ 100)
    (hbytes : ∀ b ∈ s.val, 65 ≤ b.val ∧ b.val ≤ 90), ∃ r : Std.I64,
      Aegis.MinLength.min_length s = ok r ∧
        ∀ t, Obtainable s.val t → Irreducible t → (t.length : ℤ) = r.val) := by
  sorry

/-- The function returns a result r, and for every byte string t obtained from s by exactly one allowed deletion, the minimum possible length over all byte strings obtainable from t by zero or more allowed deletions is also r.
  Preconditions: 1 <= len(s) <= 100; for every i with 0 <= i < len(s), 65 <= s[i] <= 90. -/
theorem spec_6 (s : Slice Std.U8)
    (hlen_low : 1 ≤ s.val.length) (hlen_high : s.val.length ≤ 100)
    (hbytes : ∀ b ∈ s.val, 65 ≤ b.val ∧ b.val ≤ 90) :
    ∃ r : Std.I64,
      Aegis.MinLength.min_length s = ok r ∧ ∀ t, Deletes1 s.val t → IsMinLen t r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_low : 1 ≤ s.val.length) (hlen_high : s.val.length ≤ 100)
    (hbytes : ∀ b ∈ s.val, 65 ≤ b.val ∧ b.val ≤ 90), ∃ r : Std.I64,
      Aegis.MinLength.min_length s = ok r ∧ ∀ t, Deletes1 s.val t → IsMinLen t r.val) := by
  sorry

/-- The function returns a result r, and r = len(s) if and only if for every i with 0 <= i < len(s)-1 it is not the case that (s[i] = 65 and s[i+1] = 66) or (s[i] = 67 and s[i+1] = 68).
  Preconditions: 1 <= len(s) <= 100; for every i with 0 <= i < len(s), 65 <= s[i] <= 90. -/
theorem spec_7 (s : Slice Std.U8)
    (hlen_low : 1 ≤ s.val.length) (hlen_high : s.val.length ≤ 100)
    (hbytes : ∀ b ∈ s.val, 65 ≤ b.val ∧ b.val ≤ 90) :
    ∃ r : Std.I64,
      Aegis.MinLength.min_length s = ok r ∧
        (r.val = (s.val.length : ℤ) ↔ Irreducible s.val) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_low : 1 ≤ s.val.length) (hlen_high : s.val.length ≤ 100)
    (hbytes : ∀ b ∈ s.val, 65 ≤ b.val ∧ b.val ≤ 90), ∃ r : Std.I64,
      Aegis.MinLength.min_length s = ok r ∧
        (r.val = (s.val.length : ℤ) ↔ Irreducible s.val)) := by
  sorry

/-- The function returns a result r, and r = 0 if and only if there exists a finite sequence of zero or more allowed deletions reducing s to the empty byte string.
  Preconditions: 1 <= len(s) <= 100; for every i with 0 <= i < len(s), 65 <= s[i] <= 90. -/
theorem spec_8 (s : Slice Std.U8)
    (hlen_low : 1 ≤ s.val.length) (hlen_high : s.val.length ≤ 100)
    (hbytes : ∀ b ∈ s.val, 65 ≤ b.val ∧ b.val ≤ 90) :
    ∃ r : Std.I64,
      Aegis.MinLength.min_length s = ok r ∧ (r.val = 0 ↔ Obtainable s.val []) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_low : 1 ≤ s.val.length) (hlen_high : s.val.length ≤ 100)
    (hbytes : ∀ b ∈ s.val, 65 ≤ b.val ∧ b.val ≤ 90), ∃ r : Std.I64,
      Aegis.MinLength.min_length s = ok r ∧ (r.val = 0 ↔ Obtainable s.val [])) := by
  sorry

/-- Let N be the number of indices i with 0 <= i < len(s) such that s[i] is not one of 65, 66, 67, 68. Let a = (number of occurrences of 65 in s) - (number of occurrences of 66 in s), and let c = (number of occurrences of 67 in s) - (number of occurrences of 68 in s). The function returns a result r, and r >= N + abs(a) + abs(c).
  Preconditions: 1 <= len(s) <= 100; for every i with 0 <= i < len(s), 65 <= s[i] <= 90. -/
theorem spec_9 (s : Slice Std.U8)
    (hlen_low : 1 ≤ s.val.length) (hlen_high : s.val.length ≤ 100)
    (hbytes : ∀ b ∈ s.val, 65 ≤ b.val ∧ b.val ≤ 90) :
    ∃ r : Std.I64,
      Aegis.MinLength.min_length s = ok r ∧
        (neutralCount s.val : ℤ) + |balanceAB s.val| + |balanceCD s.val| ≤ r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_low : 1 ≤ s.val.length) (hlen_high : s.val.length ≤ 100)
    (hbytes : ∀ b ∈ s.val, 65 ≤ b.val ∧ b.val ≤ 90), ∃ r : Std.I64,
      Aegis.MinLength.min_length s = ok r ∧
        (neutralCount s.val : ℤ) + |balanceAB s.val| + |balanceCD s.val| ≤ r.val) := by
  sorry

/-- The function returns a result r, and for every byte string t obtainable from s by zero or more allowed deletions, the difference (number of occurrences of 65 in t) - (number of occurrences of 66 in t) equals the same difference in s, and the difference (number of occurrences of 67 in t) - (number of occurrences of 68 in t) equals the same difference in s.
  Preconditions: 1 <= len(s) <= 100; for every i with 0 <= i < len(s), 65 <= s[i] <= 90. -/
theorem spec_10 (s : Slice Std.U8)
    (hlen_low : 1 ≤ s.val.length) (hlen_high : s.val.length ≤ 100)
    (hbytes : ∀ b ∈ s.val, 65 ≤ b.val ∧ b.val ≤ 90) :
    ∃ r : Std.I64,
      Aegis.MinLength.min_length s = ok r ∧
        ∀ t, Obtainable s.val t →
          balanceAB t = balanceAB s.val ∧ balanceCD t = balanceCD s.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_low : 1 ≤ s.val.length) (hlen_high : s.val.length ≤ 100)
    (hbytes : ∀ b ∈ s.val, 65 ≤ b.val ∧ b.val ≤ 90), ∃ r : Std.I64,
      Aegis.MinLength.min_length s = ok r ∧
        ∀ t, Obtainable s.val t →
          balanceAB t = balanceAB s.val ∧ balanceCD t = balanceCD s.val) := by
  sorry

/-- The function returns a result r, and for every byte string t obtainable from s by zero or more allowed deletions, every byte of s whose value is not one of 65, 66, 67, 68 occurs in t in the same relative order as in s.
  Preconditions: 1 <= len(s) <= 100; for every i with 0 <= i < len(s), 65 <= s[i] <= 90. -/
theorem spec_11 (s : Slice Std.U8)
    (hlen_low : 1 ≤ s.val.length) (hlen_high : s.val.length ≤ 100)
    (hbytes : ∀ b ∈ s.val, 65 ≤ b.val ∧ b.val ≤ 90) :
    ∃ r : Std.I64,
      Aegis.MinLength.min_length s = ok r ∧ ∀ t, Obtainable s.val t → nonSpecial t = nonSpecial s.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_low : 1 ≤ s.val.length) (hlen_high : s.val.length ≤ 100)
    (hbytes : ∀ b ∈ s.val, 65 ≤ b.val ∧ b.val ≤ 90), ∃ r : Std.I64,
      Aegis.MinLength.min_length s = ok r ∧ ∀ t, Obtainable s.val t → nonSpecial t = nonSpecial s.val) := by
  sorry

/-- The function returns a result r. For any byte string u formed by inserting the contiguous pair (65,66) or the contiguous pair (67,68) at any position of s, the minimum possible length over all byte strings obtainable from u by zero or more allowed deletions is also r.
  Preconditions: 1 <= len(s) <= 100; for every i with 0 <= i < len(s), 65 <= s[i] <= 90. -/
theorem spec_12 (s : Slice Std.U8)
    (hlen_low : 1 ≤ s.val.length) (hlen_high : s.val.length ≤ 100)
    (hbytes : ∀ b ∈ s.val, 65 ≤ b.val ∧ b.val ≤ 90) :
    ∃ r : Std.I64,
      Aegis.MinLength.min_length s = ok r ∧ ∀ u, InsertsPair s.val u → IsMinLen u r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_low : 1 ≤ s.val.length) (hlen_high : s.val.length ≤ 100)
    (hbytes : ∀ b ∈ s.val, 65 ≤ b.val ∧ b.val ≤ 90), ∃ r : Std.I64,
      Aegis.MinLength.min_length s = ok r ∧ ∀ u, InsertsPair s.val u → IsMinLen u r.val) := by
  sorry

/-- The function returns a result r, and there exists a finite sequence of exactly (len(s)-r)/2 allowed deletions that starts from s and ends at a byte string t with len(t) = r.
  Preconditions: 1 <= len(s) <= 100; for every i with 0 <= i < len(s), 65 <= s[i] <= 90. -/
theorem spec_13 (s : Slice Std.U8)
    (hlen_low : 1 ≤ s.val.length) (hlen_high : s.val.length ≤ 100)
    (hbytes : ∀ b ∈ s.val, 65 ≤ b.val ∧ b.val ≤ 90) :
    ∃ r : Std.I64,
      Aegis.MinLength.min_length s = ok r ∧
        ∃ t, DeletesIn ((s.val.length - r.val.toNat) / 2) s.val t ∧ (t.length : ℤ) = r.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_low : 1 ≤ s.val.length) (hlen_high : s.val.length ≤ 100)
    (hbytes : ∀ b ∈ s.val, 65 ≤ b.val ∧ b.val ≤ 90), ∃ r : Std.I64,
      Aegis.MinLength.min_length s = ok r ∧
        ∃ t, DeletesIn ((s.val.length - r.val.toNat) / 2) s.val t ∧ (t.length : ℤ) = r.val) := by
  sorry

end AegisSpec.MinLength
