import Aegis.StrStr.Code.Funs

/-!
# Specifications of `Aegis.StrStr.str_str`

LeetCode problem `find-the-index-of-the-first-occurrence-in-a-string`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.StrStr

namespace AegisSpec.StrStr

def IsLowerByte (b : Std.U8) : Prop := 97 ≤ b.val ∧ b.val ≤ 122

def OccursAt (haystack needle : List Std.U8) (i : Int) : Prop :=
  0 ≤ i ∧ i ≤ (haystack.length : Int) - (needle.length : Int) ∧
    ∀ (j : Int), 0 ≤ j → j < (needle.length : Int) →
      haystack[(i + j).toNat]? = needle[j.toNat]?

def listNOfList : (l : List Std.U8) → Aeneas.Data.ListN.ListN Std.U8 l.length
  | [] => .nil
  | a :: l => .cons a (listNOfList l)

def sliceOfList (l : List Std.U8) (h : l.length ≤ Usize.max) : Slice Std.U8 :=
  Slice.mk l.length (listNOfList l) h

theorem sliceOfList_val (l : List Std.U8) : ∀ (h : l.length ≤ Usize.max),
    (sliceOfList l h).val = l := by
  induction l with
  | nil => intro h; rfl
  | cons a l ih =>
    intro h
    have h' : l.length ≤ Usize.max := by
      have hh : l.length + 1 ≤ Usize.max := h
      omega
    show a :: (sliceOfList l h').val = a :: l
    rw [ih h']

/-- Let r be the signed integer value of the returned I64. Whenever the function returns a result r, the following holds. If there exists an integer i such that 0 <= i <= len(haystack) - len(needle) and for every integer j with 0 <= j < len(needle), haystack[i+j] = needle[j], then r is the least such i (as an integer value); otherwise r = -1.
  Preconditions: len(haystack) >= 1, len(needle) >= 1, len(haystack) <= 10000, len(needle) <= 10000, and every byte of haystack and needle is between 97 and 122 inclusive (lowercase ASCII). -/
theorem spec_1
    (haystack needle : Slice Std.U8)
    (hlen_pos : 1 ≤ haystack.val.length) (nlen_pos : 1 ≤ needle.val.length)
    (hlen_le : haystack.val.length ≤ 10000) (nlen_le : needle.val.length ≤ 10000)
    (hlower : ∀ b ∈ haystack.val, IsLowerByte b)
    (nlower : ∀ b ∈ needle.val, IsLowerByte b) :
    ∀ r : Std.I64, str_str haystack needle = ok r →
      (((∃ i : Int, OccursAt haystack.val needle.val i) →
          (OccursAt haystack.val needle.val r.val ∧
            ∀ i : Int, OccursAt haystack.val needle.val i → r.val ≤ i)) ∧
        ((¬ (∃ i : Int, OccursAt haystack.val needle.val i)) → r.val = -1)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (haystack needle : Slice Std.U8)
    (hlen_pos : 1 ≤ haystack.val.length) (nlen_pos : 1 ≤ needle.val.length)
    (hlen_le : haystack.val.length ≤ 10000) (nlen_le : needle.val.length ≤ 10000)
    (hlower : ∀ b ∈ haystack.val, IsLowerByte b)
    (nlower : ∀ b ∈ needle.val, IsLowerByte b), ∀ r : Std.I64, str_str haystack needle = ok r →
      (((∃ i : Int, OccursAt haystack.val needle.val i) →
          (OccursAt haystack.val needle.val r.val ∧
            ∀ i : Int, OccursAt haystack.val needle.val i → r.val ≤ i)) ∧
        ((¬ (∃ i : Int, OccursAt haystack.val needle.val i)) → r.val = -1))) := by
  sorry

/-- The function returns a result r (it does not fail) for every input satisfying the preconditions.
  Preconditions: len(haystack) >= 1, len(needle) >= 1, len(haystack) <= 10000, len(needle) <= 10000, and every byte of haystack and needle is between 97 and 122 inclusive (lowercase ASCII). -/
theorem spec_2
    (haystack needle : Slice Std.U8)
    (hlen_pos : 1 ≤ haystack.val.length) (nlen_pos : 1 ≤ needle.val.length)
    (hlen_le : haystack.val.length ≤ 10000) (nlen_le : needle.val.length ≤ 10000)
    (hlower : ∀ b ∈ haystack.val, IsLowerByte b)
    (nlower : ∀ b ∈ needle.val, IsLowerByte b) :
    ∃ r : Std.I64, str_str haystack needle = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (haystack needle : Slice Std.U8)
    (hlen_pos : 1 ≤ haystack.val.length) (nlen_pos : 1 ≤ needle.val.length)
    (hlen_le : haystack.val.length ≤ 10000) (nlen_le : needle.val.length ≤ 10000)
    (hlower : ∀ b ∈ haystack.val, IsLowerByte b)
    (nlower : ∀ b ∈ needle.val, IsLowerByte b), ∃ r : Std.I64, str_str haystack needle = ok r) := by
  sorry

/-- Let r be the signed integer value of the returned I64. Whenever the function returns a result r, either r = -1 or 0 <= r <= len(haystack) - len(needle).
  Preconditions: len(haystack) >= 1, len(needle) >= 1, len(haystack) <= 10000, len(needle) <= 10000, and every byte of haystack and needle is between 97 and 122 inclusive (lowercase ASCII). -/
theorem spec_3
    (haystack needle : Slice Std.U8)
    (hlen_pos : 1 ≤ haystack.val.length) (nlen_pos : 1 ≤ needle.val.length)
    (hlen_le : haystack.val.length ≤ 10000) (nlen_le : needle.val.length ≤ 10000)
    (hlower : ∀ b ∈ haystack.val, IsLowerByte b)
    (nlower : ∀ b ∈ needle.val, IsLowerByte b) :
    ∀ r : Std.I64, str_str haystack needle = ok r →
      (r.val = -1 ∨
        (0 ≤ r.val ∧ r.val ≤ (haystack.val.length : Int) - (needle.val.length : Int))) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (haystack needle : Slice Std.U8)
    (hlen_pos : 1 ≤ haystack.val.length) (nlen_pos : 1 ≤ needle.val.length)
    (hlen_le : haystack.val.length ≤ 10000) (nlen_le : needle.val.length ≤ 10000)
    (hlower : ∀ b ∈ haystack.val, IsLowerByte b)
    (nlower : ∀ b ∈ needle.val, IsLowerByte b), ∀ r : Std.I64, str_str haystack needle = ok r →
      (r.val = -1 ∨
        (0 ≤ r.val ∧ r.val ≤ (haystack.val.length : Int) - (needle.val.length : Int)))) := by
  sorry

/-- Let r be the signed integer value of the returned I64. Whenever the function returns a result r with r >= 0, then 0 <= r <= len(haystack) - len(needle) and for every integer j with 0 <= j < len(needle), haystack[r+j] = needle[j].
  Preconditions: len(haystack) >= 1, len(needle) >= 1, len(haystack) <= 10000, len(needle) <= 10000, and every byte of haystack and needle is between 97 and 122 inclusive (lowercase ASCII). -/
theorem spec_4
    (haystack needle : Slice Std.U8)
    (hlen_pos : 1 ≤ haystack.val.length) (nlen_pos : 1 ≤ needle.val.length)
    (hlen_le : haystack.val.length ≤ 10000) (nlen_le : needle.val.length ≤ 10000)
    (hlower : ∀ b ∈ haystack.val, IsLowerByte b)
    (nlower : ∀ b ∈ needle.val, IsLowerByte b) :
    ∀ r : Std.I64, str_str haystack needle = ok r → 0 ≤ r.val →
      OccursAt haystack.val needle.val r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (haystack needle : Slice Std.U8)
    (hlen_pos : 1 ≤ haystack.val.length) (nlen_pos : 1 ≤ needle.val.length)
    (hlen_le : haystack.val.length ≤ 10000) (nlen_le : needle.val.length ≤ 10000)
    (hlower : ∀ b ∈ haystack.val, IsLowerByte b)
    (nlower : ∀ b ∈ needle.val, IsLowerByte b), ∀ r : Std.I64, str_str haystack needle = ok r → 0 ≤ r.val →
      OccursAt haystack.val needle.val r.val) := by
  sorry

/-- Let r be the signed integer value of the returned I64. Whenever the function returns a result r with r >= 0, for every integer i with 0 <= i < r, it is not the case that (0 <= i <= len(haystack) - len(needle) and for every integer j with 0 <= j < len(needle), haystack[i+j] = needle[j]).
  Preconditions: len(haystack) >= 1, len(needle) >= 1, len(haystack) <= 10000, len(needle) <= 10000, and every byte of haystack and needle is between 97 and 122 inclusive (lowercase ASCII). -/
theorem spec_5
    (haystack needle : Slice Std.U8)
    (hlen_pos : 1 ≤ haystack.val.length) (nlen_pos : 1 ≤ needle.val.length)
    (hlen_le : haystack.val.length ≤ 10000) (nlen_le : needle.val.length ≤ 10000)
    (hlower : ∀ b ∈ haystack.val, IsLowerByte b)
    (nlower : ∀ b ∈ needle.val, IsLowerByte b) :
    ∀ r : Std.I64, str_str haystack needle = ok r → 0 ≤ r.val →
      ∀ i : Int, 0 ≤ i → i < r.val → ¬ OccursAt haystack.val needle.val i := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (haystack needle : Slice Std.U8)
    (hlen_pos : 1 ≤ haystack.val.length) (nlen_pos : 1 ≤ needle.val.length)
    (hlen_le : haystack.val.length ≤ 10000) (nlen_le : needle.val.length ≤ 10000)
    (hlower : ∀ b ∈ haystack.val, IsLowerByte b)
    (nlower : ∀ b ∈ needle.val, IsLowerByte b), ∀ r : Std.I64, str_str haystack needle = ok r → 0 ≤ r.val →
      ∀ i : Int, 0 ≤ i → i < r.val → ¬ OccursAt haystack.val needle.val i) := by
  sorry

/-- Let r be the signed integer value of the returned I64. Whenever the function returns a result r with r = -1, there is no integer i such that 0 <= i <= len(haystack) - len(needle) and for every integer j with 0 <= j < len(needle), haystack[i+j] = needle[j].
  Preconditions: len(haystack) >= 1, len(needle) >= 1, len(haystack) <= 10000, len(needle) <= 10000, and every byte of haystack and needle is between 97 and 122 inclusive (lowercase ASCII). -/
theorem spec_6
    (haystack needle : Slice Std.U8)
    (hlen_pos : 1 ≤ haystack.val.length) (nlen_pos : 1 ≤ needle.val.length)
    (hlen_le : haystack.val.length ≤ 10000) (nlen_le : needle.val.length ≤ 10000)
    (hlower : ∀ b ∈ haystack.val, IsLowerByte b)
    (nlower : ∀ b ∈ needle.val, IsLowerByte b) :
    ∀ r : Std.I64, str_str haystack needle = ok r → r.val = -1 →
      ¬ (∃ i : Int, OccursAt haystack.val needle.val i) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (haystack needle : Slice Std.U8)
    (hlen_pos : 1 ≤ haystack.val.length) (nlen_pos : 1 ≤ needle.val.length)
    (hlen_le : haystack.val.length ≤ 10000) (nlen_le : needle.val.length ≤ 10000)
    (hlower : ∀ b ∈ haystack.val, IsLowerByte b)
    (nlower : ∀ b ∈ needle.val, IsLowerByte b), ∀ r : Std.I64, str_str haystack needle = ok r → r.val = -1 →
      ¬ (∃ i : Int, OccursAt haystack.val needle.val i)) := by
  sorry

/-- If there is no integer i such that 0 <= i <= len(haystack) - len(needle) and for every integer j with 0 <= j < len(needle), haystack[i+j] = needle[j], then whenever the function returns a result r, r = -1.
  Preconditions: len(haystack) >= 1, len(needle) >= 1, len(haystack) <= 10000, len(needle) <= 10000, and every byte of haystack and needle is between 97 and 122 inclusive (lowercase ASCII). -/
theorem spec_7
    (haystack needle : Slice Std.U8)
    (hlen_pos : 1 ≤ haystack.val.length) (nlen_pos : 1 ≤ needle.val.length)
    (hlen_le : haystack.val.length ≤ 10000) (nlen_le : needle.val.length ≤ 10000)
    (hlower : ∀ b ∈ haystack.val, IsLowerByte b)
    (nlower : ∀ b ∈ needle.val, IsLowerByte b)
    (hno_occ : ¬ (∃ i : Int, OccursAt haystack.val needle.val i)) :
    ∀ r : Std.I64, str_str haystack needle = ok r → r.val = -1 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (haystack needle : Slice Std.U8)
    (hlen_pos : 1 ≤ haystack.val.length) (nlen_pos : 1 ≤ needle.val.length)
    (hlen_le : haystack.val.length ≤ 10000) (nlen_le : needle.val.length ≤ 10000)
    (hlower : ∀ b ∈ haystack.val, IsLowerByte b)
    (nlower : ∀ b ∈ needle.val, IsLowerByte b)
    (hno_occ : ¬ (∃ i : Int, OccursAt haystack.val needle.val i)), ∀ r : Std.I64, str_str haystack needle = ok r → r.val = -1) := by
  sorry

/-- Let r be the signed integer value of the returned I64. For every integer k, if 0 <= k <= len(haystack) - len(needle), and for every integer j with 0 <= j < len(needle) we have haystack[k+j] = needle[j], and for every integer i with 0 <= i < k it is not the case that (0 <= i <= len(haystack) - len(needle) and for every integer j with 0 <= j < len(needle) we have haystack[i+j] = needle[j]), then whenever the function returns a result r, r = k.
  Preconditions: len(haystack) >= 1, len(needle) >= 1, len(haystack) <= 10000, len(needle) <= 10000, and every byte of haystack and needle is between 97 and 122 inclusive (lowercase ASCII). -/
theorem spec_8
    (haystack needle : Slice Std.U8)
    (hlen_pos : 1 ≤ haystack.val.length) (nlen_pos : 1 ≤ needle.val.length)
    (hlen_le : haystack.val.length ≤ 10000) (nlen_le : needle.val.length ≤ 10000)
    (hlower : ∀ b ∈ haystack.val, IsLowerByte b)
    (nlower : ∀ b ∈ needle.val, IsLowerByte b) :
    ∀ r : Std.I64, str_str haystack needle = ok r →
      ∀ k : Int, OccursAt haystack.val needle.val k →
        (∀ i : Int, 0 ≤ i → i < k → ¬ OccursAt haystack.val needle.val i) →
          r.val = k := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (haystack needle : Slice Std.U8)
    (hlen_pos : 1 ≤ haystack.val.length) (nlen_pos : 1 ≤ needle.val.length)
    (hlen_le : haystack.val.length ≤ 10000) (nlen_le : needle.val.length ≤ 10000)
    (hlower : ∀ b ∈ haystack.val, IsLowerByte b)
    (nlower : ∀ b ∈ needle.val, IsLowerByte b), ∀ r : Std.I64, str_str haystack needle = ok r →
      ∀ k : Int, OccursAt haystack.val needle.val k →
        (∀ i : Int, 0 ≤ i → i < k → ¬ OccursAt haystack.val needle.val i) →
          r.val = k) := by
  sorry

/-- For every integer k such that 0 <= k <= len(haystack) - len(needle) and for every integer j with 0 <= j < len(needle), haystack[k+j] = needle[j], whenever the function returns a result r, r >= 0 and r <= k.
  Preconditions: len(haystack) >= 1, len(needle) >= 1, len(haystack) <= 10000, len(needle) <= 10000, and every byte of haystack and needle is between 97 and 122 inclusive (lowercase ASCII). -/
theorem spec_9
    (haystack needle : Slice Std.U8)
    (hlen_pos : 1 ≤ haystack.val.length) (nlen_pos : 1 ≤ needle.val.length)
    (hlen_le : haystack.val.length ≤ 10000) (nlen_le : needle.val.length ≤ 10000)
    (hlower : ∀ b ∈ haystack.val, IsLowerByte b)
    (nlower : ∀ b ∈ needle.val, IsLowerByte b) :
    ∀ r : Std.I64, str_str haystack needle = ok r →
      ∀ k : Int, OccursAt haystack.val needle.val k → (0 ≤ r.val ∧ r.val ≤ k) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (haystack needle : Slice Std.U8)
    (hlen_pos : 1 ≤ haystack.val.length) (nlen_pos : 1 ≤ needle.val.length)
    (hlen_le : haystack.val.length ≤ 10000) (nlen_le : needle.val.length ≤ 10000)
    (hlower : ∀ b ∈ haystack.val, IsLowerByte b)
    (nlower : ∀ b ∈ needle.val, IsLowerByte b), ∀ r : Std.I64, str_str haystack needle = ok r →
      ∀ k : Int, OccursAt haystack.val needle.val k → (0 ≤ r.val ∧ r.val ≤ k)) := by
  sorry

/-- Let r be the signed integer value returned by str_str(haystack, needle) and r' be the signed integer value returned by str_str(haystack ++ [b], needle). For every byte b with 97 <= b <= 122, if there exists an integer i such that 0 <= i <= len(haystack) - len(needle) and for every integer j with 0 <= j < len(needle), haystack[i+j] = needle[j], then whenever both calls return results, r' = r.
  Preconditions: len(haystack) >= 1, len(needle) >= 1, len(haystack) <= 9999, len(needle) <= 10000, and every byte of haystack and needle is between 97 and 122 inclusive (lowercase ASCII). -/
theorem spec_10
    (haystack needle : Slice Std.U8)
    (hlen_pos : 1 ≤ haystack.val.length) (nlen_pos : 1 ≤ needle.val.length)
    (hlen_le : haystack.val.length ≤ 9999) (nlen_le : needle.val.length ≤ 10000)
    (hlower : ∀ b ∈ haystack.val, IsLowerByte b)
    (nlower : ∀ b ∈ needle.val, IsLowerByte b)
    (hocc : ∃ i : Int, OccursAt haystack.val needle.val i) :
    ∀ (b : Std.U8), IsLowerByte b →
      ∀ (hb : (haystack.val ++ [b]).length ≤ Usize.max) (r r' : Std.I64),
        str_str haystack needle = ok r →
        str_str (sliceOfList (haystack.val ++ [b]) hb) needle = ok r' → r' = r := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (haystack needle : Slice Std.U8)
    (hlen_pos : 1 ≤ haystack.val.length) (nlen_pos : 1 ≤ needle.val.length)
    (hlen_le : haystack.val.length ≤ 9999) (nlen_le : needle.val.length ≤ 10000)
    (hlower : ∀ b ∈ haystack.val, IsLowerByte b)
    (nlower : ∀ b ∈ needle.val, IsLowerByte b)
    (hocc : ∃ i : Int, OccursAt haystack.val needle.val i), ∀ (b : Std.U8), IsLowerByte b →
      ∀ (hb : (haystack.val ++ [b]).length ≤ Usize.max) (r r' : Std.I64),
        str_str haystack needle = ok r →
        str_str (sliceOfList (haystack.val ++ [b]) hb) needle = ok r' → r' = r) := by
  sorry

end AegisSpec.StrStr
