import Aegis.BeautifulIndices.Code.Funs

/-!
# Specifications of `Aegis.BeautifulIndices.beautiful_indices`

LeetCode problem `find-beautiful-indices-in-the-given-array-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.BeautifulIndices

  def lowerASCII (x : List Std.U8) : Prop := ∀ c ∈ x, 97 ≤ c.val ∧ c.val ≤ 122

  def Occ (x t : List Std.U8) (p : ℤ) : Prop :=
    0 ≤ p ∧ p + (t.length : ℤ) ≤ (x.length : ℤ) ∧
      ∀ q : ℕ, q < t.length → x[p.toNat + q]? = t[q]?

  def beautifulSet (s a b : List Std.U8) (k : ℤ) : Set ℤ :=
    {i | Occ s a i ∧ ∃ j : ℤ, Occ s b j ∧ |j - i| ≤ k}

  /-- Whenever the function returns a result r, let B be the set of all integers i such that Occ(s,a,i) and there exists an integer j with Occ(s,b,j) and |j - i| <= k. Then r, viewed as a sequence of mathematical integers, is exactly the elements of B in strictly increasing order: len(r) = |B|, and for every t with 0 <= t < len(r), r[t] is the unique element of B having exactly t elements of B smaller than it. Here Occ(x,t,p) means 0 <= p, p + len(t) <= len(x), and for every q with 0 <= q < len(t), x[p+q] = t[q].
    Preconditions: Let len(x) be the byte length of slice x and x[p] its p-th byte. s, a, and b contain only lowercase ASCII letters. 1 <= len(s) <= 500000, 1 <= len(a) <= 500000, 1 <= len(b) <= 500000, and k is an i64 representing a mathematical integer with 1 <= k <= len(s). No assumption is made that len(a) <= len(s) or len(b) <= len(s). -/
  theorem spec_1 (s a b : Slice Std.U8) (k : Std.I64)
      (hs_lower : lowerASCII s.val) (ha_lower : lowerASCII a.val)
      (hb_lower : lowerASCII b.val)
      (hs_len : 1 ≤ s.val.length ∧ s.val.length ≤ 500000)
      (ha_len : 1 ≤ a.val.length ∧ a.val.length ≤ 500000)
      (hb_len : 1 ≤ b.val.length ∧ b.val.length ≤ 500000)
      (hk : 1 ≤ k.val ∧ k.val ≤ (s.val.length : ℤ))
      (r : alloc.vec.Vec Std.I64)
      (hres : Aegis.BeautifulIndices.beautiful_indices s a b k = ok r) :
      r.val.length = (beautifulSet s.val a.val b.val k.val).ncard ∧
        ∀ (t : ℕ) (ht : t < r.val.length),
          r.val[t].val ∈ beautifulSet s.val a.val b.val k.val ∧
            (beautifulSet s.val a.val b.val k.val ∩ Set.Iio r.val[t].val).ncard = t ∧
              ∀ i ∈ beautifulSet s.val a.val b.val k.val,
                (beautifulSet s.val a.val b.val k.val ∩ Set.Iio i).ncard = t →
                  i = r.val[t].val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s a b : Slice Std.U8) (k : Std.I64)
        (hs_lower : lowerASCII s.val) (ha_lower : lowerASCII a.val)
        (hb_lower : lowerASCII b.val)
        (hs_len : 1 ≤ s.val.length ∧ s.val.length ≤ 500000)
        (ha_len : 1 ≤ a.val.length ∧ a.val.length ≤ 500000)
        (hb_len : 1 ≤ b.val.length ∧ b.val.length ≤ 500000)
        (hk : 1 ≤ k.val ∧ k.val ≤ (s.val.length : ℤ))
        (r : alloc.vec.Vec Std.I64)
        (hres : Aegis.BeautifulIndices.beautiful_indices s a b k = ok r), r.val.length = (beautifulSet s.val a.val b.val k.val).ncard ∧
          ∀ (t : ℕ) (ht : t < r.val.length),
            r.val[t].val ∈ beautifulSet s.val a.val b.val k.val ∧
              (beautifulSet s.val a.val b.val k.val ∩ Set.Iio r.val[t].val).ncard = t ∧
                ∀ i ∈ beautifulSet s.val a.val b.val k.val,
                  (beautifulSet s.val a.val b.val k.val ∩ Set.Iio i).ncard = t →
                    i = r.val[t].val) := by
    sorry

  /-- The function returns a result r; it does not fail, overflow, panic, or go out of bounds for any input satisfying the preconditions.
    Preconditions: Let len(x) be the byte length of slice x. s, a, and b contain only lowercase ASCII letters. 1 <= len(s) <= 500000, 1 <= len(a) <= 500000, 1 <= len(b) <= 500000, and k is an i64 representing a mathematical integer with 1 <= k <= len(s). No assumption is made that len(a) <= len(s) or len(b) <= len(s). -/
  theorem spec_2 (s a b : Slice Std.U8) (k : Std.I64)
      (hs_lower : lowerASCII s.val) (ha_lower : lowerASCII a.val)
      (hb_lower : lowerASCII b.val)
      (hs_len : 1 ≤ s.val.length ∧ s.val.length ≤ 500000)
      (ha_len : 1 ≤ a.val.length ∧ a.val.length ≤ 500000)
      (hb_len : 1 ≤ b.val.length ∧ b.val.length ≤ 500000)
      (hk : 1 ≤ k.val ∧ k.val ≤ (s.val.length : ℤ)) :
      ∃ r : alloc.vec.Vec Std.I64, Aegis.BeautifulIndices.beautiful_indices s a b k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s a b : Slice Std.U8) (k : Std.I64)
        (hs_lower : lowerASCII s.val) (ha_lower : lowerASCII a.val)
        (hb_lower : lowerASCII b.val)
        (hs_len : 1 ≤ s.val.length ∧ s.val.length ≤ 500000)
        (ha_len : 1 ≤ a.val.length ∧ a.val.length ≤ 500000)
        (hb_len : 1 ≤ b.val.length ∧ b.val.length ≤ 500000)
        (hk : 1 ≤ k.val ∧ k.val ≤ (s.val.length : ℤ)), ∃ r : alloc.vec.Vec Std.I64, Aegis.BeautifulIndices.beautiful_indices s a b k = ok r) := by
    sorry

  /-- Whenever the function returns a result r, every element v of r satisfies 0 <= v and v + len(a) <= len(s). Thus every returned value is in the allowed range of starting indices for an occurrence of a in s.
    Preconditions: Let len(x) be the byte length of slice x. s, a, and b contain only lowercase ASCII letters. 1 <= len(s) <= 500000, 1 <= len(a) <= 500000, 1 <= len(b) <= 500000, and k is an i64 representing a mathematical integer with 1 <= k <= len(s). No assumption is made that len(a) <= len(s) or len(b) <= len(s). -/
  theorem spec_3 (s a b : Slice Std.U8) (k : Std.I64)
      (hs_lower : lowerASCII s.val) (ha_lower : lowerASCII a.val)
      (hb_lower : lowerASCII b.val)
      (hs_len : 1 ≤ s.val.length ∧ s.val.length ≤ 500000)
      (ha_len : 1 ≤ a.val.length ∧ a.val.length ≤ 500000)
      (hb_len : 1 ≤ b.val.length ∧ b.val.length ≤ 500000)
      (hk : 1 ≤ k.val ∧ k.val ≤ (s.val.length : ℤ))
      (r : alloc.vec.Vec Std.I64)
      (hres : Aegis.BeautifulIndices.beautiful_indices s a b k = ok r) :
      ∀ v ∈ r.val, 0 ≤ v.val ∧ v.val + (a.val.length : ℤ) ≤ (s.val.length : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s a b : Slice Std.U8) (k : Std.I64)
        (hs_lower : lowerASCII s.val) (ha_lower : lowerASCII a.val)
        (hb_lower : lowerASCII b.val)
        (hs_len : 1 ≤ s.val.length ∧ s.val.length ≤ 500000)
        (ha_len : 1 ≤ a.val.length ∧ a.val.length ≤ 500000)
        (hb_len : 1 ≤ b.val.length ∧ b.val.length ≤ 500000)
        (hk : 1 ≤ k.val ∧ k.val ≤ (s.val.length : ℤ))
        (r : alloc.vec.Vec Std.I64)
        (hres : Aegis.BeautifulIndices.beautiful_indices s a b k = ok r), ∀ v ∈ r.val, 0 ≤ v.val ∧ v.val + (a.val.length : ℤ) ≤ (s.val.length : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, for every t with 0 <= t < len(r) - 1, r[t] < r[t+1]. Hence the returned vector is strictly increasing and contains no duplicate values.
    Preconditions: Let len(x) be the byte length of slice x. s, a, and b contain only lowercase ASCII letters. 1 <= len(s) <= 500000, 1 <= len(a) <= 500000, 1 <= len(b) <= 500000, and k is an i64 representing a mathematical integer with 1 <= k <= len(s). No assumption is made that len(a) <= len(s) or len(b) <= len(s). -/
  theorem spec_4 (s a b : Slice Std.U8) (k : Std.I64)
      (hs_lower : lowerASCII s.val) (ha_lower : lowerASCII a.val)
      (hb_lower : lowerASCII b.val)
      (hs_len : 1 ≤ s.val.length ∧ s.val.length ≤ 500000)
      (ha_len : 1 ≤ a.val.length ∧ a.val.length ≤ 500000)
      (hb_len : 1 ≤ b.val.length ∧ b.val.length ≤ 500000)
      (hk : 1 ≤ k.val ∧ k.val ≤ (s.val.length : ℤ))
      (r : alloc.vec.Vec Std.I64)
      (hres : Aegis.BeautifulIndices.beautiful_indices s a b k = ok r) :
      ∀ (t : ℕ) (ht : t < r.val.length - 1), r.val[t].val < r.val[t + 1].val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s a b : Slice Std.U8) (k : Std.I64)
        (hs_lower : lowerASCII s.val) (ha_lower : lowerASCII a.val)
        (hb_lower : lowerASCII b.val)
        (hs_len : 1 ≤ s.val.length ∧ s.val.length ≤ 500000)
        (ha_len : 1 ≤ a.val.length ∧ a.val.length ≤ 500000)
        (hb_len : 1 ≤ b.val.length ∧ b.val.length ≤ 500000)
        (hk : 1 ≤ k.val ∧ k.val ≤ (s.val.length : ℤ))
        (r : alloc.vec.Vec Std.I64)
        (hres : Aegis.BeautifulIndices.beautiful_indices s a b k = ok r), ∀ (t : ℕ) (ht : t < r.val.length - 1), r.val[t].val < r.val[t + 1].val) := by
    sorry

  /-- Whenever the function returns a result r, for every element v of r, Occ(s,a,v) holds, where Occ(x,t,p) means 0 <= p, p + len(t) <= len(x), and for every q with 0 <= q < len(t), x[p+q] = t[q]. Thus every returned index starts an occurrence of a in s.
    Preconditions: Let len(x) be the byte length of slice x. s, a, and b contain only lowercase ASCII letters. 1 <= len(s) <= 500000, 1 <= len(a) <= 500000, 1 <= len(b) <= 500000, and k is an i64 representing a mathematical integer with 1 <= k <= len(s). No assumption is made that len(a) <= len(s) or len(b) <= len(s). -/
  theorem spec_5 (s a b : Slice Std.U8) (k : Std.I64)
      (hs_lower : lowerASCII s.val) (ha_lower : lowerASCII a.val)
      (hb_lower : lowerASCII b.val)
      (hs_len : 1 ≤ s.val.length ∧ s.val.length ≤ 500000)
      (ha_len : 1 ≤ a.val.length ∧ a.val.length ≤ 500000)
      (hb_len : 1 ≤ b.val.length ∧ b.val.length ≤ 500000)
      (hk : 1 ≤ k.val ∧ k.val ≤ (s.val.length : ℤ))
      (r : alloc.vec.Vec Std.I64)
      (hres : Aegis.BeautifulIndices.beautiful_indices s a b k = ok r) :
      ∀ v ∈ r.val, Occ s.val a.val v.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s a b : Slice Std.U8) (k : Std.I64)
        (hs_lower : lowerASCII s.val) (ha_lower : lowerASCII a.val)
        (hb_lower : lowerASCII b.val)
        (hs_len : 1 ≤ s.val.length ∧ s.val.length ≤ 500000)
        (ha_len : 1 ≤ a.val.length ∧ a.val.length ≤ 500000)
        (hb_len : 1 ≤ b.val.length ∧ b.val.length ≤ 500000)
        (hk : 1 ≤ k.val ∧ k.val ≤ (s.val.length : ℤ))
        (r : alloc.vec.Vec Std.I64)
        (hres : Aegis.BeautifulIndices.beautiful_indices s a b k = ok r), ∀ v ∈ r.val, Occ s.val a.val v.val) := by
    sorry

  /-- Whenever the function returns a result r, for every element v of r there exists an integer j such that Occ(s,b,j) and |j - v| <= k, where Occ(x,t,p) means 0 <= p, p + len(t) <= len(x), and for every q with 0 <= q < len(t), x[p+q] = t[q]. Thus every returned index has a valid b-occurrence within distance k.
    Preconditions: Let len(x) be the byte length of slice x. s, a, and b contain only lowercase ASCII letters. 1 <= len(s) <= 500000, 1 <= len(a) <= 500000, 1 <= len(b) <= 500000, and k is an i64 representing a mathematical integer with 1 <= k <= len(s). No assumption is made that len(a) <= len(s) or len(b) <= len(s). -/
  theorem spec_6 (s a b : Slice Std.U8) (k : Std.I64)
      (hs_lower : lowerASCII s.val) (ha_lower : lowerASCII a.val)
      (hb_lower : lowerASCII b.val)
      (hs_len : 1 ≤ s.val.length ∧ s.val.length ≤ 500000)
      (ha_len : 1 ≤ a.val.length ∧ a.val.length ≤ 500000)
      (hb_len : 1 ≤ b.val.length ∧ b.val.length ≤ 500000)
      (hk : 1 ≤ k.val ∧ k.val ≤ (s.val.length : ℤ))
      (r : alloc.vec.Vec Std.I64)
      (hres : Aegis.BeautifulIndices.beautiful_indices s a b k = ok r) :
      ∀ v ∈ r.val, ∃ j : ℤ, Occ s.val b.val j ∧ |j - v.val| ≤ k.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s a b : Slice Std.U8) (k : Std.I64)
        (hs_lower : lowerASCII s.val) (ha_lower : lowerASCII a.val)
        (hb_lower : lowerASCII b.val)
        (hs_len : 1 ≤ s.val.length ∧ s.val.length ≤ 500000)
        (ha_len : 1 ≤ a.val.length ∧ a.val.length ≤ 500000)
        (hb_len : 1 ≤ b.val.length ∧ b.val.length ≤ 500000)
        (hk : 1 ≤ k.val ∧ k.val ≤ (s.val.length : ℤ))
        (r : alloc.vec.Vec Std.I64)
        (hres : Aegis.BeautifulIndices.beautiful_indices s a b k = ok r), ∀ v ∈ r.val, ∃ j : ℤ, Occ s.val b.val j ∧ |j - v.val| ≤ k.val) := by
    sorry

  /-- Whenever the function returns a result r, for every integer i, if Occ(s,a,i) and there exists an integer j with Occ(s,b,j) and |j - i| <= k, then there exists an index t with 0 <= t < len(r) and r[t] = i. Here Occ(x,t,p) means 0 <= p, p + len(t) <= len(x), and for every q with 0 <= q < len(t), x[p+q] = t[q]. Thus every beautiful index is present in the result.
    Preconditions: Let len(x) be the byte length of slice x. s, a, and b contain only lowercase ASCII letters. 1 <= len(s) <= 500000, 1 <= len(a) <= 500000, 1 <= len(b) <= 500000, and k is an i64 representing a mathematical integer with 1 <= k <= len(s). No assumption is made that len(a) <= len(s) or len(b) <= len(s). -/
  theorem spec_7 (s a b : Slice Std.U8) (k : Std.I64)
      (hs_lower : lowerASCII s.val) (ha_lower : lowerASCII a.val)
      (hb_lower : lowerASCII b.val)
      (hs_len : 1 ≤ s.val.length ∧ s.val.length ≤ 500000)
      (ha_len : 1 ≤ a.val.length ∧ a.val.length ≤ 500000)
      (hb_len : 1 ≤ b.val.length ∧ b.val.length ≤ 500000)
      (hk : 1 ≤ k.val ∧ k.val ≤ (s.val.length : ℤ))
      (r : alloc.vec.Vec Std.I64)
      (hres : Aegis.BeautifulIndices.beautiful_indices s a b k = ok r) :
      ∀ i : ℤ, Occ s.val a.val i →
        (∃ j : ℤ, Occ s.val b.val j ∧ |j - i| ≤ k.val) →
          ∃ (t : ℕ) (ht : t < r.val.length), r.val[t].val = i := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s a b : Slice Std.U8) (k : Std.I64)
        (hs_lower : lowerASCII s.val) (ha_lower : lowerASCII a.val)
        (hb_lower : lowerASCII b.val)
        (hs_len : 1 ≤ s.val.length ∧ s.val.length ≤ 500000)
        (ha_len : 1 ≤ a.val.length ∧ a.val.length ≤ 500000)
        (hb_len : 1 ≤ b.val.length ∧ b.val.length ≤ 500000)
        (hk : 1 ≤ k.val ∧ k.val ≤ (s.val.length : ℤ))
        (r : alloc.vec.Vec Std.I64)
        (hres : Aegis.BeautifulIndices.beautiful_indices s a b k = ok r), ∀ i : ℤ, Occ s.val a.val i →
          (∃ j : ℤ, Occ s.val b.val j ∧ |j - i| ≤ k.val) →
            ∃ (t : ℕ) (ht : t < r.val.length), r.val[t].val = i) := by
    sorry

  /-- Whenever the function returns a result r, len(r) = 0 if and only if there is no integer i such that Occ(s,a,i) and there exists an integer j with Occ(s,b,j) and |j - i| <= k. Here Occ(x,t,p) means 0 <= p, p + len(t) <= len(x), and for every q with 0 <= q < len(t), x[p+q] = t[q]. Thus the result is empty exactly when there are no beautiful indices.
    Preconditions: Let len(x) be the byte length of slice x. s, a, and b contain only lowercase ASCII letters. 1 <= len(s) <= 500000, 1 <= len(a) <= 500000, 1 <= len(b) <= 500000, and k is an i64 representing a mathematical integer with 1 <= k <= len(s). No assumption is made that len(a) <= len(s) or len(b) <= len(s). -/
  theorem spec_8 (s a b : Slice Std.U8) (k : Std.I64)
      (hs_lower : lowerASCII s.val) (ha_lower : lowerASCII a.val)
      (hb_lower : lowerASCII b.val)
      (hs_len : 1 ≤ s.val.length ∧ s.val.length ≤ 500000)
      (ha_len : 1 ≤ a.val.length ∧ a.val.length ≤ 500000)
      (hb_len : 1 ≤ b.val.length ∧ b.val.length ≤ 500000)
      (hk : 1 ≤ k.val ∧ k.val ≤ (s.val.length : ℤ))
      (r : alloc.vec.Vec Std.I64)
      (hres : Aegis.BeautifulIndices.beautiful_indices s a b k = ok r) :
      r.val.length = 0 ↔
        ¬ ∃ i : ℤ, Occ s.val a.val i ∧
          ∃ j : ℤ, Occ s.val b.val j ∧ |j - i| ≤ k.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s a b : Slice Std.U8) (k : Std.I64)
        (hs_lower : lowerASCII s.val) (ha_lower : lowerASCII a.val)
        (hb_lower : lowerASCII b.val)
        (hs_len : 1 ≤ s.val.length ∧ s.val.length ≤ 500000)
        (ha_len : 1 ≤ a.val.length ∧ a.val.length ≤ 500000)
        (hb_len : 1 ≤ b.val.length ∧ b.val.length ≤ 500000)
        (hk : 1 ≤ k.val ∧ k.val ≤ (s.val.length : ℤ))
        (r : alloc.vec.Vec Std.I64)
        (hres : Aegis.BeautifulIndices.beautiful_indices s a b k = ok r), r.val.length = 0 ↔
          ¬ ∃ i : ℤ, Occ s.val a.val i ∧
            ∃ j : ℤ, Occ s.val b.val j ∧ |j - i| ≤ k.val) := by
    sorry

  /-- Whenever the function returns a result r, if len(a) <= len(s) then len(r) <= len(s) - len(a) + 1; otherwise len(r) = 0. This bounds the number of returned indices by the number of possible starting positions for an occurrence of a in s.
    Preconditions: Let len(x) be the byte length of slice x. s, a, and b contain only lowercase ASCII letters. 1 <= len(s) <= 500000, 1 <= len(a) <= 500000, 1 <= len(b) <= 500000, and k is an i64 representing a mathematical integer with 1 <= k <= len(s). No assumption is made that len(a) <= len(s) or len(b) <= len(s). -/
  theorem spec_9 (s a b : Slice Std.U8) (k : Std.I64)
      (hs_lower : lowerASCII s.val) (ha_lower : lowerASCII a.val)
      (hb_lower : lowerASCII b.val)
      (hs_len : 1 ≤ s.val.length ∧ s.val.length ≤ 500000)
      (ha_len : 1 ≤ a.val.length ∧ a.val.length ≤ 500000)
      (hb_len : 1 ≤ b.val.length ∧ b.val.length ≤ 500000)
      (hk : 1 ≤ k.val ∧ k.val ≤ (s.val.length : ℤ))
      (r : alloc.vec.Vec Std.I64)
      (hres : Aegis.BeautifulIndices.beautiful_indices s a b k = ok r) :
      (a.val.length ≤ s.val.length → r.val.length ≤ s.val.length - a.val.length + 1) ∧
        (s.val.length < a.val.length → r.val.length = 0) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s a b : Slice Std.U8) (k : Std.I64)
        (hs_lower : lowerASCII s.val) (ha_lower : lowerASCII a.val)
        (hb_lower : lowerASCII b.val)
        (hs_len : 1 ≤ s.val.length ∧ s.val.length ≤ 500000)
        (ha_len : 1 ≤ a.val.length ∧ a.val.length ≤ 500000)
        (hb_len : 1 ≤ b.val.length ∧ b.val.length ≤ 500000)
        (hk : 1 ≤ k.val ∧ k.val ≤ (s.val.length : ℤ))
        (r : alloc.vec.Vec Std.I64)
        (hres : Aegis.BeautifulIndices.beautiful_indices s a b k = ok r), (a.val.length ≤ s.val.length → r.val.length ≤ s.val.length - a.val.length + 1) ∧
          (s.val.length < a.val.length → r.val.length = 0)) := by
    sorry

  end AegisSpec.BeautifulIndices
