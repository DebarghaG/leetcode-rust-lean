import Aegis.HasAllCodes.Code.Funs

/-!
# Specifications of `Aegis.HasAllCodes.has_all_codes`

LeetCode problem `check-if-a-string-contains-all-binary-codes-of-size-k`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.HasAllCodes

open Aegis.HasAllCodes (has_all_codes)

def IsBitWord {k : ℕ} (w : Fin k → ℕ) : Prop := ∀ i, w i = 0 ∨ w i = 1

def OccursAt (u : List U8) (k : ℕ) (w : Fin k → ℕ) (j : ℕ) : Prop :=
  ∃ (_ : j + k ≤ u.length),
    ∀ i : Fin k, (u[j + i.val]'(by have := i.isLt; omega)).val = 48 + w i

def Occurs (u : List U8) (k : ℕ) (w : Fin k → ℕ) : Prop := ∃ j, OccursAt u k w j

def HasAllWords (s : Slice U8) (k : ℕ) : Prop :=
  ∀ w : Fin k → ℕ, IsBitWord w → Occurs s.val k w

def OccursInSlice (s t : Slice U8) : Prop :=
  ∃ d, ∃ (_ : d + s.val.length ≤ t.val.length),
    ∀ i : Fin s.val.length,
      (t.val[d + i.val]'(by have := i.isLt; omega)).val = (s.val[i.val]).val

def sliceOfList (l : List U8) (h : l.length ≤ Usize.max) : Slice U8 :=
  ⟨l.length, Aeneas.Data.ListN.ListN.fromList l, h⟩

def flipByte (b : U8) : U8 := if b.val = 48 then 49#u8 else 48#u8

def revSlice (s : Slice U8) : Slice U8 :=
  sliceOfList s.val.reverse (by
    have hval : s.val.length = s.leng := by
      simp [Slice.val, Aeneas.Data.ListN.ListN_length]
    rw [List.length_reverse, hval]
    exact s.bound)

def compSlice (s : Slice U8) : Slice U8 :=
  sliceOfList (s.val.map flipByte) (by
    have hval : s.val.length = s.leng := by
      simp [Slice.val, Aeneas.Data.ListN.ListN_length]
    rw [List.length_map, hval]
    exact s.bound)

theorem revSlice_val (s : Slice U8) : (revSlice s).val = s.val.reverse := by
  simp [revSlice, sliceOfList, Slice.val, Aeneas.Data.ListN.ListN.from_to_inverse]

theorem compSlice_val (s : Slice U8) : (compSlice s).val = s.val.map flipByte := by
  simp [compSlice, sliceOfList, Slice.val, Aeneas.Data.ListN.ListN.from_to_inverse]

/-- Write P(s,k) for: for every sequence w_0,...,w_{k-1} with each w_i in {0,1}, there exists an index j with 0 <= j <= len(s)-k such that for every i with 0 <= i < k, s[j+i] = 48 + w_i. The function returns a result r, and r = true if and only if P(s,k) holds; otherwise r = false.
  Preconditions: len(s) >= 1 and len(s) <= 500000; for every i with 0 <= i < len(s), s[i] is 48 or 49; and 1 <= k <= 20. -/
theorem spec_1 (s : Slice U8) (k : I64)
    (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 500000)
    (hbytes : ∀ (i : ℕ) (_ : i < s.val.length),
      (s.val[i]).val = 48 ∨ (s.val[i]).val = 49)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 20) :
    ∃ r, has_all_codes s k = ok r ∧ (r = true ↔ HasAllWords s k.val.toNat) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice U8) (k : I64)
    (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 500000)
    (hbytes : ∀ (i : ℕ) (_ : i < s.val.length),
      (s.val[i]).val = 48 ∨ (s.val[i]).val = 49)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 20), ∃ r, has_all_codes s k = ok r ∧ (r = true ↔ HasAllWords s k.val.toNat)) := by
  sorry

/-- The function returns a result r (it does not fail) for these inputs.
  Preconditions: len(s) >= 1 and len(s) <= 500000; for every i with 0 <= i < len(s), s[i] is 48 or 49; and 1 <= k <= 20. -/
theorem spec_2 (s : Slice U8) (k : I64)
    (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 500000)
    (hbytes : ∀ (i : ℕ) (_ : i < s.val.length),
      (s.val[i]).val = 48 ∨ (s.val[i]).val = 49)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 20) :
    ∃ r, has_all_codes s k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice U8) (k : I64)
    (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 500000)
    (hbytes : ∀ (i : ℕ) (_ : i < s.val.length),
      (s.val[i]).val = 48 ∨ (s.val[i]).val = 49)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 20), ∃ r, has_all_codes s k = ok r) := by
  sorry

/-- If len(s) < 2^k + k - 1, then the function returns a result r and r = false.
  Preconditions: len(s) >= 1 and len(s) <= 500000; for every i with 0 <= i < len(s), s[i] is 48 or 49; and 1 <= k <= 20. -/
theorem spec_3 (s : Slice U8) (k : I64)
    (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 500000)
    (hbytes : ∀ (i : ℕ) (_ : i < s.val.length),
      (s.val[i]).val = 48 ∨ (s.val[i]).val = 49)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 20)
    (hshort : (s.val.length : ℤ) < 2 ^ k.val.toNat + k.val - 1) :
    ∃ r, has_all_codes s k = ok r ∧ r = false := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice U8) (k : I64)
    (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 500000)
    (hbytes : ∀ (i : ℕ) (_ : i < s.val.length),
      (s.val[i]).val = 48 ∨ (s.val[i]).val = 49)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 20)
    (hshort : (s.val.length : ℤ) < 2 ^ k.val.toNat + k.val - 1), ∃ r, has_all_codes s k = ok r ∧ r = false) := by
  sorry

/-- If k = 1, then the function returns a result r, and r = true if and only if there exist indices i and j with 0 <= i < len(s), 0 <= j < len(s), s[i] = 48, and s[j] = 49.
  Preconditions: len(s) >= 1 and len(s) <= 500000; for every i with 0 <= i < len(s), s[i] is 48 or 49; and k = 1. -/
theorem spec_4 (s : Slice U8) (k : I64)
    (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 500000)
    (hbytes : ∀ (i : ℕ) (_ : i < s.val.length),
      (s.val[i]).val = 48 ∨ (s.val[i]).val = 49)
    (hk : k.val = 1) :
    ∃ r, has_all_codes s k = ok r ∧
      (r = true ↔ ∃ i j : Fin s.val.length,
        (s.val[i.val]).val = 48 ∧ (s.val[j.val]).val = 49) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice U8) (k : I64)
    (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 500000)
    (hbytes : ∀ (i : ℕ) (_ : i < s.val.length),
      (s.val[i]).val = 48 ∨ (s.val[i]).val = 49)
    (hk : k.val = 1), ∃ r, has_all_codes s k = ok r ∧
      (r = true ↔ ∃ i j : Fin s.val.length,
        (s.val[i.val]).val = 48 ∧ (s.val[j.val]).val = 49)) := by
  sorry

/-- If every byte of s equals 48, or if every byte of s equals 49, then the function returns a result r and r = false.
  Preconditions: len(s) >= 1 and len(s) <= 500000; for every i with 0 <= i < len(s), s[i] is 48 or 49; and 1 <= k <= 20. -/
theorem spec_5 (s : Slice U8) (k : I64)
    (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 500000)
    (hbytes : ∀ (i : ℕ) (_ : i < s.val.length),
      (s.val[i]).val = 48 ∨ (s.val[i]).val = 49)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 20)
    (hconst : (∀ (i : ℕ) (_ : i < s.val.length), (s.val[i]).val = 48) ∨
      (∀ (i : ℕ) (_ : i < s.val.length), (s.val[i]).val = 49)) :
    ∃ r, has_all_codes s k = ok r ∧ r = false := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice U8) (k : I64)
    (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 500000)
    (hbytes : ∀ (i : ℕ) (_ : i < s.val.length),
      (s.val[i]).val = 48 ∨ (s.val[i]).val = 49)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 20)
    (hconst : (∀ (i : ℕ) (_ : i < s.val.length), (s.val[i]).val = 48) ∨
      (∀ (i : ℕ) (_ : i < s.val.length), (s.val[i]).val = 49)), ∃ r, has_all_codes s k = ok r ∧ r = false) := by
  sorry

/-- Write P(s,m) for: for every sequence w_0,...,w_{m-1} with each w_i in {0,1}, there exists an index j with 0 <= j <= len(s)-m such that for every i with 0 <= i < m, s[j+i] = 48 + w_i. If the function returns r and r = true, then for every integer m with 1 <= m <= k, P(s,m) holds.
  Preconditions: len(s) >= 1 and len(s) <= 500000; for every i with 0 <= i < len(s), s[i] is 48 or 49; and 1 <= k <= 20. -/
theorem spec_6 (s : Slice U8) (k : I64)
    (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 500000)
    (hbytes : ∀ (i : ℕ) (_ : i < s.val.length),
      (s.val[i]).val = 48 ∨ (s.val[i]).val = 49)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 20) :
    ∀ r, has_all_codes s k = ok r → r = true →
      ∀ m : ℤ, 1 ≤ m → m ≤ k.val → HasAllWords s m.toNat := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice U8) (k : I64)
    (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 500000)
    (hbytes : ∀ (i : ℕ) (_ : i < s.val.length),
      (s.val[i]).val = 48 ∨ (s.val[i]).val = 49)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 20), ∀ r, has_all_codes s k = ok r → r = true →
      ∀ m : ℤ, 1 ≤ m → m ≤ k.val → HasAllWords s m.toNat) := by
  sorry

/-- For every byte slice t with 1 <= len(t) <= 500000 and every byte of t equal to 48 or 49, if there exists an index d with 0 <= d and d + len(s) <= len(t) and t[d+i] = s[i] for every 0 <= i < len(s), then the call has_all_codes(s,k) returns a result r_s, the call has_all_codes(t,k) returns a result r_t, and r_s = true implies r_t = true.
  Preconditions: len(s) >= 1 and len(s) <= 500000; for every i with 0 <= i < len(s), s[i] is 48 or 49; and 1 <= k <= 20. -/
theorem spec_7 (s t : Slice U8) (k : I64)
    (hslen1 : 1 ≤ s.val.length) (hslen2 : s.val.length ≤ 500000)
    (hsbytes : ∀ (i : ℕ) (_ : i < s.val.length),
      (s.val[i]).val = 48 ∨ (s.val[i]).val = 49)
    (htlen1 : 1 ≤ t.val.length) (htlen2 : t.val.length ≤ 500000)
    (htbytes : ∀ (i : ℕ) (_ : i < t.val.length),
      (t.val[i]).val = 48 ∨ (t.val[i]).val = 49)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 20)
    (hsub : OccursInSlice s t) :
    ∃ r_s r_t, has_all_codes s k = ok r_s ∧ has_all_codes t k = ok r_t ∧
      (r_s = true → r_t = true) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s t : Slice U8) (k : I64)
    (hslen1 : 1 ≤ s.val.length) (hslen2 : s.val.length ≤ 500000)
    (hsbytes : ∀ (i : ℕ) (_ : i < s.val.length),
      (s.val[i]).val = 48 ∨ (s.val[i]).val = 49)
    (htlen1 : 1 ≤ t.val.length) (htlen2 : t.val.length ≤ 500000)
    (htbytes : ∀ (i : ℕ) (_ : i < t.val.length),
      (t.val[i]).val = 48 ∨ (t.val[i]).val = 49)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 20)
    (hsub : OccursInSlice s t), ∃ r_s r_t, has_all_codes s k = ok r_s ∧ has_all_codes t k = ok r_t ∧
      (r_s = true → r_t = true)) := by
  sorry

/-- Let rev(s) be the slice of length len(s) with rev(s)[i] = s[len(s)-1-i] for 0 <= i < len(s). The call on s returns a result r, the call on rev(s) with the same k returns a result r_rev, and r = r_rev.
  Preconditions: len(s) >= 1 and len(s) <= 500000; for every i with 0 <= i < len(s), s[i] is 48 or 49; and 1 <= k <= 20. -/
theorem spec_8 (s : Slice U8) (k : I64)
    (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 500000)
    (hbytes : ∀ (i : ℕ) (_ : i < s.val.length),
      (s.val[i]).val = 48 ∨ (s.val[i]).val = 49)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 20) :
    ∃ r r_rev, has_all_codes s k = ok r ∧ has_all_codes (revSlice s) k = ok r_rev ∧
      r = r_rev := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s : Slice U8) (k : I64)
    (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 500000)
    (hbytes : ∀ (i : ℕ) (_ : i < s.val.length),
      (s.val[i]).val = 48 ∨ (s.val[i]).val = 49)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 20), ∃ r r_rev, has_all_codes s k = ok r ∧ has_all_codes (revSlice s) k = ok r_rev ∧
      r = r_rev) := by
  sorry

/-- Let comp(s) be the slice of length len(s) with comp(s)[i] = 49 if s[i] = 48, and comp(s)[i] = 48 if s[i] = 49. The call on s returns a result r, the call on comp(s) with the same k returns a result r_comp, and r = r_comp.
  Preconditions: len(s) >= 1 and len(s) <= 500000; for every i with 0 <= i < len(s), s[i] is 48 or 49; and 1 <= k <= 20. -/
theorem spec_9 (s : Slice U8) (k : I64)
    (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 500000)
    (hbytes : ∀ (i : ℕ) (_ : i < s.val.length),
      (s.val[i]).val = 48 ∨ (s.val[i]).val = 49)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 20) :
    ∃ r r_comp, has_all_codes s k = ok r ∧ has_all_codes (compSlice s) k = ok r_comp ∧
      r = r_comp := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s : Slice U8) (k : I64)
    (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 500000)
    (hbytes : ∀ (i : ℕ) (_ : i < s.val.length),
      (s.val[i]).val = 48 ∨ (s.val[i]).val = 49)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 20), ∃ r r_comp, has_all_codes s k = ok r ∧ has_all_codes (compSlice s) k = ok r_comp ∧
      r = r_comp) := by
  sorry

/-- If the function returns r and r = false, then there exists a sequence w_0,...,w_{k-1} with each w_i in {0,1} such that for every index j with 0 <= j <= len(s)-k, there is some i with 0 <= i < k and s[j+i] != 48 + w_i. Equivalently, some binary word of length k does not occur in s.
  Preconditions: len(s) >= 1 and len(s) <= 500000; for every i with 0 <= i < len(s), s[i] is 48 or 49; and 1 <= k <= 20. -/
theorem spec_10 (s : Slice U8) (k : I64)
    (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 500000)
    (hbytes : ∀ (i : ℕ) (_ : i < s.val.length),
      (s.val[i]).val = 48 ∨ (s.val[i]).val = 49)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 20) :
    ∀ r, has_all_codes s k = ok r → r = false →
      ∃ w : Fin k.val.toNat → ℕ, IsBitWord w ∧
        ∀ j (hj : j + k.val.toNat ≤ s.val.length), ∃ i : Fin k.val.toNat,
          (s.val[j + i.val]'(by have h1 := i.isLt; omega)).val ≠ 48 + w i := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s : Slice U8) (k : I64)
    (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 500000)
    (hbytes : ∀ (i : ℕ) (_ : i < s.val.length),
      (s.val[i]).val = 48 ∨ (s.val[i]).val = 49)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 20), ∀ r, has_all_codes s k = ok r → r = false →
      ∃ w : Fin k.val.toNat → ℕ, IsBitWord w ∧
        ∀ j (hj : j + k.val.toNat ≤ s.val.length), ∃ i : Fin k.val.toNat,
          (s.val[j + i.val]'(by have h1 := i.isLt; omega)).val ≠ 48 + w i) := by
  sorry

/-- For every byte slice t with 1 <= len(t) <= 500000 and every byte of t equal to 48 or 49, if for every binary word w_0,...,w_{k-1} with w_i in {0,1}, w occurs in s if and only if w occurs in t (where w occurs in a slice u iff there is j with 0 <= j <= len(u)-k and u[j+i] = 48 + w_i for all 0 <= i < k), then the call on s and the call on t return the same Boolean result.
  Preconditions: len(s) >= 1 and len(s) <= 500000; for every i with 0 <= i < len(s), s[i] is 48 or 49; and 1 <= k <= 20. -/
theorem spec_11 (s t : Slice U8) (k : I64)
    (hslen1 : 1 ≤ s.val.length) (hslen2 : s.val.length ≤ 500000)
    (hsbytes : ∀ (i : ℕ) (_ : i < s.val.length),
      (s.val[i]).val = 48 ∨ (s.val[i]).val = 49)
    (htlen1 : 1 ≤ t.val.length) (htlen2 : t.val.length ≤ 500000)
    (htbytes : ∀ (i : ℕ) (_ : i < t.val.length),
      (t.val[i]).val = 48 ∨ (t.val[i]).val = 49)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 20)
    (hsame : ∀ w : Fin k.val.toNat → ℕ, IsBitWord w →
      (Occurs s.val k.val.toNat w ↔ Occurs t.val k.val.toNat w)) :
    ∃ r_s r_t, has_all_codes s k = ok r_s ∧ has_all_codes t k = ok r_t ∧ r_s = r_t := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s t : Slice U8) (k : I64)
    (hslen1 : 1 ≤ s.val.length) (hslen2 : s.val.length ≤ 500000)
    (hsbytes : ∀ (i : ℕ) (_ : i < s.val.length),
      (s.val[i]).val = 48 ∨ (s.val[i]).val = 49)
    (htlen1 : 1 ≤ t.val.length) (htlen2 : t.val.length ≤ 500000)
    (htbytes : ∀ (i : ℕ) (_ : i < t.val.length),
      (t.val[i]).val = 48 ∨ (t.val[i]).val = 49)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 20)
    (hsame : ∀ w : Fin k.val.toNat → ℕ, IsBitWord w →
      (Occurs s.val k.val.toNat w ↔ Occurs t.val k.val.toNat w)), ∃ r_s r_t, has_all_codes s k = ok r_s ∧ has_all_codes t k = ok r_t ∧ r_s = r_t) := by
  sorry

end AegisSpec.HasAllCodes
