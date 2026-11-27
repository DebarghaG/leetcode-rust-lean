import Aegis.IsOneEditDistance.Code.Funs

/-!
# Specifications of `Aegis.IsOneEditDistance.is_one_edit_distance`

LeetCode problem `one-edit-distance`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.IsOneEditDistance

  def IsAlnumByte (b : Std.U8) : Prop :=
    (48 ≤ b.val ∧ b.val ≤ 57) ∨ (65 ≤ b.val ∧ b.val ≤ 90) ∨
      (97 ≤ b.val ∧ b.val ≤ 122)

  def byteAt (l : List Std.U8) (i : ℕ) : Option Std.U8 := l[i]?

  def listNOfList {α : Type} : (l : List α) → Aeneas.Data.ListN.ListN α l.length
    | [] => Aeneas.Data.ListN.ListN.nil
    | a :: l => Aeneas.Data.ListN.ListN.cons a (listNOfList l)

  theorem listN_toList_length {α : Type} :
      ∀ {n : ℕ}, ∀ l : Aeneas.Data.ListN.ListN α n, l.toList.length = n
    | _, .nil => rfl
    | _, .cons a l => by
        show (a :: l.toList).length = _
        simp [listN_toList_length l]

  theorem slice_val_length (s : Slice Std.U8) : s.val.length = s.leng :=
    listN_toList_length s.list

  theorem slice_val_length_le_max (s : Slice Std.U8) : s.val.length ≤ Usize.max := by
    rw [slice_val_length]
    exact s.bound

  def sliceOfList (l : List Std.U8) (h : l.length ≤ Usize.max) : Slice Std.U8 :=
    ⟨l.length, listNOfList l, h⟩

  def suffixSlice (s : Slice Std.U8) (k : ℕ) : Slice Std.U8 :=
    sliceOfList (s.val.drop k) (by
      rw [List.length_drop]
      exact le_trans (Nat.sub_le _ _) (slice_val_length_le_max s))

  def prefixSlice (s : Slice Std.U8) (k : ℕ) : Slice Std.U8 :=
    sliceOfList (s.val.take (s.length - k)) (by
      rw [List.length_take]
      exact le_trans (Nat.min_le_right _ _) (slice_val_length_le_max s))

  def reverseSlice (s : Slice Std.U8) : Slice Std.U8 :=
    sliceOfList s.val.reverse (by
      rw [List.length_reverse]
      exact slice_val_length_le_max s)

  theorem listNOfList_toList {α : Type} : ∀ l : List α, (listNOfList l).toList = l
    | [] => rfl
    | a :: l => by
        show a :: (listNOfList l).toList = a :: l
        rw [listNOfList_toList l]

  theorem sliceOfList_val (l : List Std.U8) (h : l.length ≤ Usize.max) :
      (sliceOfList l h).val = l :=
    listNOfList_toList l

  theorem suffixSlice_val (s : Slice Std.U8) (k : ℕ) :
      (suffixSlice s k).val = s.val.drop k :=
    sliceOfList_val _ _

  theorem prefixSlice_val (s : Slice Std.U8) (k : ℕ) :
      (prefixSlice s k).val = s.val.take (s.length - k) :=
    sliceOfList_val _ _

  theorem reverseSlice_val (s : Slice Std.U8) :
      (reverseSlice s).val = s.val.reverse :=
    sliceOfList_val _ _

  theorem reverseSlice_byteAt (s : Slice Std.U8) {i : ℕ} (hi : i < s.val.length) :
      byteAt (reverseSlice s).val i = byteAt s.val (s.length - 1 - i) := by
    rw [reverseSlice_val]
    simpa [byteAt] using List.getElem?_reverse (l := s.val) hi

  def AgreeBelow (a b : List Std.U8) (i : ℕ) : Prop :=
    ∀ j : ℕ, j < i → byteAt a j = byteAt b j

  def AgreeShifted (a b : List Std.U8) (i : ℕ) : Prop :=
    ∀ j : ℕ, i ≤ j → j < b.length → byteAt a (j + 1) = byteAt b j

  def AgreeExceptAt (a b : List Std.U8) (i : ℕ) : Prop :=
    ∀ j : ℕ, j < a.length → j ≠ i → byteAt a j = byteAt b j

  def OneInsertion (s t : List Std.U8) : Prop :=
    t.length = s.length + 1 ∧
      ∃ i : ℕ, i < t.length ∧ AgreeBelow t s i ∧ AgreeShifted t s i

  def OneDeletion (s t : List Std.U8) : Prop :=
    s.length = t.length + 1 ∧
      ∃ i : ℕ, i < s.length ∧ AgreeBelow s t i ∧ AgreeShifted s t i

  def OneSubstitution (s t : List Std.U8) : Prop :=
    s.length = t.length ∧
      ∃ i : ℕ, i < s.length ∧ byteAt s i ≠ byteAt t i ∧ AgreeExceptAt s t i

  /-- Whenever the function returns a result r on (s,t), r is true if and only if at least one of the following three conditions holds: (A) len(t) = len(s) + 1 and there exists an index i with 0 <= i < len(t) such that, for every j with 0 <= j < i, t[j] = s[j], and for every j with i <= j < len(s), t[j+1] = s[j] (so deleting t[i] from t yields s, equivalently t is obtained by inserting exactly one byte into s); (B) len(s) = len(t) + 1 and there exists an index i with 0 <= i < len(s) such that, for every j with 0 <= j < i, s[j] = t[j], and for every j with i <= j < len(t), s[j+1] = t[j] (so deleting s[i] from s yields t); or (C) len(s) = len(t) and there exists an index i with 0 <= i < len(s) such that s[i] != t[i] and, for every j with 0 <= j < len(s) and j != i, s[j] = t[j] (so replacing the single character s[i] by t[i] yields t). Consequently r is false exactly when none of (A), (B), (C) holds.
    Preconditions: len(s) <= 10000 and len(t) <= 10000, and every byte of s and t is an ASCII code for a lowercase letter, an uppercase letter, or a digit. -/
  theorem spec_1 (s t : Slice Std.U8)
      (hs_bound : s.length ≤ 10000) (ht_bound : t.length ≤ 10000)
      (hs_alnum : ∀ c, c ∈ s.val → IsAlnumByte c)
      (ht_alnum : ∀ c, c ∈ t.val → IsAlnumByte c) :
      ∀ r : Bool, Aegis.IsOneEditDistance.is_one_edit_distance s t = ok r →
        (r = true ↔
          (OneInsertion s.val t.val ∨ OneDeletion s.val t.val ∨
            OneSubstitution s.val t.val)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s t : Slice Std.U8)
        (hs_bound : s.length ≤ 10000) (ht_bound : t.length ≤ 10000)
        (hs_alnum : ∀ c, c ∈ s.val → IsAlnumByte c)
        (ht_alnum : ∀ c, c ∈ t.val → IsAlnumByte c), ∀ r : Bool, Aegis.IsOneEditDistance.is_one_edit_distance s t = ok r →
          (r = true ↔
            (OneInsertion s.val t.val ∨ OneDeletion s.val t.val ∨
              OneSubstitution s.val t.val))) := by
    sorry

  /-- For every s and t satisfying the preconditions, the function returns a result r; it does not fail (in particular, it does not overflow, access out of bounds, or panic).
    Preconditions: len(s) <= 10000 and len(t) <= 10000, and every byte of s and t is an ASCII code for a lowercase letter, an uppercase letter, or a digit. -/
  theorem spec_2 (s t : Slice Std.U8)
      (hs_bound : s.length ≤ 10000) (ht_bound : t.length ≤ 10000)
      (hs_alnum : ∀ c, c ∈ s.val → IsAlnumByte c)
      (ht_alnum : ∀ c, c ∈ t.val → IsAlnumByte c) :
      ∃ r : Bool, Aegis.IsOneEditDistance.is_one_edit_distance s t = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s t : Slice Std.U8)
        (hs_bound : s.length ≤ 10000) (ht_bound : t.length ≤ 10000)
        (hs_alnum : ∀ c, c ∈ s.val → IsAlnumByte c)
        (ht_alnum : ∀ c, c ∈ t.val → IsAlnumByte c), ∃ r : Bool, Aegis.IsOneEditDistance.is_one_edit_distance s t = ok r) := by
    sorry

  /-- For every s and t satisfying the preconditions, whenever the function returns r on (s,t) and returns r' on (t,s), we have r = r'. Equivalently, the function's answer is symmetric in its two arguments.
    Preconditions: len(s) <= 10000 and len(t) <= 10000, and every byte of s and t is an ASCII code for a lowercase letter, an uppercase letter, or a digit. -/
  theorem spec_3 (s t : Slice Std.U8)
      (hs_bound : s.length ≤ 10000) (ht_bound : t.length ≤ 10000)
      (hs_alnum : ∀ c, c ∈ s.val → IsAlnumByte c)
      (ht_alnum : ∀ c, c ∈ t.val → IsAlnumByte c) :
      ∀ r r' : Bool,
        Aegis.IsOneEditDistance.is_one_edit_distance s t = ok r →
        Aegis.IsOneEditDistance.is_one_edit_distance t s = ok r' →
        r = r' := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s t : Slice Std.U8)
        (hs_bound : s.length ≤ 10000) (ht_bound : t.length ≤ 10000)
        (hs_alnum : ∀ c, c ∈ s.val → IsAlnumByte c)
        (ht_alnum : ∀ c, c ∈ t.val → IsAlnumByte c), ∀ r r' : Bool,
          Aegis.IsOneEditDistance.is_one_edit_distance s t = ok r →
          Aegis.IsOneEditDistance.is_one_edit_distance t s = ok r' →
          r = r') := by
    sorry

  /-- Let r be the value returned by the function on (s,t), and let r' be the value returned by the function on the pair of suffix slices s[k..] and t[k..] (the suffixes starting at index k). Whenever both calls return results, r = r'.
    Preconditions: len(s) <= 10000 and len(t) <= 10000, every byte of s and t is an ASCII code for a lowercase letter, an uppercase letter, or a digit, 0 <= k <= min(len(s), len(t)), and for every j with 0 <= j < k, s[j] = t[j]. -/
  theorem spec_4 (s t : Slice Std.U8) (k : ℕ)
      (hs_bound : s.length ≤ 10000) (ht_bound : t.length ≤ 10000)
      (hs_alnum : ∀ c, c ∈ s.val → IsAlnumByte c)
      (ht_alnum : ∀ c, c ∈ t.val → IsAlnumByte c)
      (hk : k ≤ min s.length t.length)
      (hpref : ∀ j : ℕ, j < k → byteAt s.val j = byteAt t.val j) :
      ∀ r r' : Bool,
        Aegis.IsOneEditDistance.is_one_edit_distance s t = ok r →
        Aegis.IsOneEditDistance.is_one_edit_distance (suffixSlice s k) (suffixSlice t k)
          = ok r' →
        r = r' := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s t : Slice Std.U8) (k : ℕ)
        (hs_bound : s.length ≤ 10000) (ht_bound : t.length ≤ 10000)
        (hs_alnum : ∀ c, c ∈ s.val → IsAlnumByte c)
        (ht_alnum : ∀ c, c ∈ t.val → IsAlnumByte c)
        (hk : k ≤ min s.length t.length)
        (hpref : ∀ j : ℕ, j < k → byteAt s.val j = byteAt t.val j), ∀ r r' : Bool,
          Aegis.IsOneEditDistance.is_one_edit_distance s t = ok r →
          Aegis.IsOneEditDistance.is_one_edit_distance (suffixSlice s k) (suffixSlice t k)
            = ok r' →
          r = r') := by
    sorry

  /-- Let r be the value returned by the function on (s,t). Let s' be the prefix of s of length len(s)-k (the first len(s)-k bytes of s), and let t' be the prefix of t of length len(t)-k. Let r' be the value returned by the function on (s',t'). Whenever both calls return results, r = r'.
    Preconditions: len(s) <= 10000 and len(t) <= 10000, every byte of s and t is an ASCII code for a lowercase letter, an uppercase letter, or a digit, 0 <= k <= min(len(s), len(t)), and for every j with 0 <= j < k, s[len(s)-k+j] = t[len(t)-k+j]. -/
  theorem spec_5 (s t : Slice Std.U8) (k : ℕ)
      (hs_bound : s.length ≤ 10000) (ht_bound : t.length ≤ 10000)
      (hs_alnum : ∀ c, c ∈ s.val → IsAlnumByte c)
      (ht_alnum : ∀ c, c ∈ t.val → IsAlnumByte c)
      (hk : k ≤ min s.length t.length)
      (hsuf : ∀ j : ℕ, j < k →
        byteAt s.val (s.length - k + j) = byteAt t.val (t.length - k + j)) :
      ∀ r r' : Bool,
        Aegis.IsOneEditDistance.is_one_edit_distance s t = ok r →
        Aegis.IsOneEditDistance.is_one_edit_distance (prefixSlice s k) (prefixSlice t k)
          = ok r' →
        r = r' := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s t : Slice Std.U8) (k : ℕ)
        (hs_bound : s.length ≤ 10000) (ht_bound : t.length ≤ 10000)
        (hs_alnum : ∀ c, c ∈ s.val → IsAlnumByte c)
        (ht_alnum : ∀ c, c ∈ t.val → IsAlnumByte c)
        (hk : k ≤ min s.length t.length)
        (hsuf : ∀ j : ℕ, j < k →
          byteAt s.val (s.length - k + j) = byteAt t.val (t.length - k + j)), ∀ r r' : Bool,
          Aegis.IsOneEditDistance.is_one_edit_distance s t = ok r →
          Aegis.IsOneEditDistance.is_one_edit_distance (prefixSlice s k) (prefixSlice t k)
            = ok r' →
          r = r') := by
    sorry

  /-- For every s and t satisfying the preconditions, let rs be the byte slice of length len(s) with rs[i] = s[len(s)-1-i] for every 0 <= i < len(s), and let rt be the byte slice of length len(t) with rt[i] = t[len(t)-1-i] for every 0 <= i < len(t). Whenever the function returns r on (s,t) and r' on (rs,rt), we have r = r'.
    Preconditions: len(s) <= 10000 and len(t) <= 10000, and every byte of s and t is an ASCII code for a lowercase letter, an uppercase letter, or a digit. -/
  theorem spec_6 (s t : Slice Std.U8)
      (hs_bound : s.length ≤ 10000) (ht_bound : t.length ≤ 10000)
      (hs_alnum : ∀ c, c ∈ s.val → IsAlnumByte c)
      (ht_alnum : ∀ c, c ∈ t.val → IsAlnumByte c) :
      ∀ r r' : Bool,
        Aegis.IsOneEditDistance.is_one_edit_distance s t = ok r →
        Aegis.IsOneEditDistance.is_one_edit_distance (reverseSlice s) (reverseSlice t)
          = ok r' →
        r = r' := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s t : Slice Std.U8)
        (hs_bound : s.length ≤ 10000) (ht_bound : t.length ≤ 10000)
        (hs_alnum : ∀ c, c ∈ s.val → IsAlnumByte c)
        (ht_alnum : ∀ c, c ∈ t.val → IsAlnumByte c), ∀ r r' : Bool,
          Aegis.IsOneEditDistance.is_one_edit_distance s t = ok r →
          Aegis.IsOneEditDistance.is_one_edit_distance (reverseSlice s) (reverseSlice t)
            = ok r' →
          r = r') := by
    sorry

  end AegisSpec.IsOneEditDistance
