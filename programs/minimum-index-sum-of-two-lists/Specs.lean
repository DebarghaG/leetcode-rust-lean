import Aegis.FindRestaurant.Code.Funs

/-!
# Specifications of `Aegis.FindRestaurant.find_restaurant`

LeetCode problem `minimum-index-sum-of-two-lists`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open scoped Classical
open Aegis.FindRestaurant

namespace AegisSpec.FindRestaurant

abbrev ByteStr : Type := List Std.U8

def strsOf (l : List (alloc.vec.Vec Std.U8)) : List ByteStr := l.map (fun v => v.val)

def HoldsAt (l : List ByteStr) (i : Nat) (x : ByteStr) : Prop :=
  ∃ (h : i < l.length), l[i]'h = x

def isAlphaByte (b : Std.U8) : Prop :=
  b.val = 32 ∨ (65 ≤ b.val ∧ b.val ≤ 90) ∨ (97 ≤ b.val ∧ b.val ≤ 122)

def IsMinCommonSum (l1 l2 : List ByteStr) (m : Nat) : Prop :=
  (∃ (i j : Nat) (x : ByteStr), HoldsAt l1 i x ∧ HoldsAt l2 j x ∧ i + j = m) ∧
  ∀ (i j : Nat) (x : ByteStr), HoldsAt l1 i x → HoldsAt l2 j x → m ≤ i + j

def AtMinCommonSum (l1 l2 : List ByteStr) (m : Nat) (x : ByteStr) : Prop :=
  ∃ (i j : Nat), HoldsAt l1 i x ∧ HoldsAt l2 j x ∧ i + j = m

def countEq (l : List ByteStr) (x : ByteStr) : Nat :=
  l.countP (fun y => decide (y = x))

noncomputable def numAtMinCommonSum (l1 l2 : List ByteStr) (m : Nat) : Nat :=
  ((l1.filter (fun x => decide (AtMinCommonSum l1 l2 m x))).dedup).length

structure Pre (list1 list2 : Slice (alloc.vec.Vec Std.U8)) : Prop where
  len1_ge : 1 ≤ (strsOf list1.val).length
  len1_le : (strsOf list1.val).length ≤ 1000
  len2_ge : 1 ≤ (strsOf list2.val).length
  len2_le : (strsOf list2.val).length ≤ 1000
  elem1_len : ∀ x ∈ strsOf list1.val, 1 ≤ x.length ∧ x.length ≤ 30
  elem2_len : ∀ x ∈ strsOf list2.val, 1 ≤ x.length ∧ x.length ≤ 30
  elem1_alpha : ∀ x ∈ strsOf list1.val, ∀ b ∈ x, isAlphaByte b
  elem2_alpha : ∀ x ∈ strsOf list2.val, ∀ b ∈ x, isAlphaByte b
  nodup1 : (strsOf list1.val).Nodup
  nodup2 : (strsOf list2.val).Nodup
  common : ∃ (i j : Nat) (x : ByteStr),
    HoldsAt (strsOf list1.val) i x ∧ HoldsAt (strsOf list2.val) j x

/-- Whenever the function returns a result r, let m be the least value of i+j over all pairs (i,j) with 0 <= i < len(list1), 0 <= j < len(list2), and list1[i] = list2[j] (this minimum exists by the precondition). Then for every byte string x, the number of indices k with 0 <= k < len(r) and r[k] = x is 1 if there exist i,j with 0 <= i < len(list1), 0 <= j < len(list2), list1[i] = x, list2[j] = x, and i+j = m, and is 0 otherwise.
  Preconditions: len(list1) and len(list2) are each between 1 and 1000; every element of list1 and every element of list2 has length between 1 and 30; every byte of every element is either 32 (space), an uppercase English letter (byte 65..90), or a lowercase English letter (byte 97..122); the elements of list1 are pairwise unequal and the elements of list2 are pairwise unequal; and there is at least one common string, i.e. there exist i with 0 <= i < len(list1) and j with 0 <= j < len(list2) such that list1[i] = list2[j]. -/
theorem spec_1
    (list1 list2 : Slice (alloc.vec.Vec Std.U8)) (h : Pre list1 list2)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (hr : find_restaurant list1 list2 = ok r)
    (m : Nat) (hm : IsMinCommonSum (strsOf list1.val) (strsOf list2.val) m)
    (x : ByteStr) :
    countEq (strsOf r.val) x =
      if AtMinCommonSum (strsOf list1.val) (strsOf list2.val) m x then 1 else 0 := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (list1 list2 : Slice (alloc.vec.Vec Std.U8)) (h : Pre list1 list2)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (hr : find_restaurant list1 list2 = ok r)
    (m : Nat) (hm : IsMinCommonSum (strsOf list1.val) (strsOf list2.val) m)
    (x : ByteStr), countEq (strsOf r.val) x =
      if AtMinCommonSum (strsOf list1.val) (strsOf list2.val) m x then 1 else 0) := by
  sorry

/-- The function returns a result r and does not fail: there exists a vector r of byte strings such that find_restaurant list1 list2 = Result.ok r. No overflow, out-of-bounds access, panic, or error result occurs.
  Preconditions: len(list1) and len(list2) are each between 1 and 1000; every element of list1 and every element of list2 has length between 1 and 30; every byte of every element is either 32 (space), an uppercase English letter (byte 65..90), or a lowercase English letter (byte 97..122); the elements of list1 are pairwise unequal and the elements of list2 are pairwise unequal; and there is at least one common string, i.e. there exist i with 0 <= i < len(list1) and j with 0 <= j < len(list2) such that list1[i] = list2[j]. -/
theorem spec_2
    (list1 list2 : Slice (alloc.vec.Vec Std.U8)) (h : Pre list1 list2) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.U8), find_restaurant list1 list2 = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (list1 list2 : Slice (alloc.vec.Vec Std.U8)) (h : Pre list1 list2), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.U8), find_restaurant list1 list2 = ok r) := by
  sorry

/-- Whenever the function returns a result r, len(r) >= 1.
  Preconditions: len(list1) and len(list2) are each between 1 and 1000; every element of list1 and every element of list2 has length between 1 and 30; every byte of every element is either 32 (space), an uppercase English letter (byte 65..90), or a lowercase English letter (byte 97..122); the elements of list1 are pairwise unequal and the elements of list2 are pairwise unequal; and there is at least one common string, i.e. there exist i with 0 <= i < len(list1) and j with 0 <= j < len(list2) such that list1[i] = list2[j]. -/
theorem spec_3
    (list1 list2 : Slice (alloc.vec.Vec Std.U8)) (h : Pre list1 list2)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (hr : find_restaurant list1 list2 = ok r) :
    1 ≤ (strsOf r.val).length := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (list1 list2 : Slice (alloc.vec.Vec Std.U8)) (h : Pre list1 list2)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (hr : find_restaurant list1 list2 = ok r), 1 ≤ (strsOf r.val).length) := by
  sorry

/-- Whenever the function returns a result r, len(r) <= min(len(list1), len(list2)).
  Preconditions: len(list1) and len(list2) are each between 1 and 1000; every element of list1 and every element of list2 has length between 1 and 30; every byte of every element is either 32 (space), an uppercase English letter (byte 65..90), or a lowercase English letter (byte 97..122); the elements of list1 are pairwise unequal and the elements of list2 are pairwise unequal; and there is at least one common string, i.e. there exist i with 0 <= i < len(list1) and j with 0 <= j < len(list2) such that list1[i] = list2[j]. -/
theorem spec_4
    (list1 list2 : Slice (alloc.vec.Vec Std.U8)) (h : Pre list1 list2)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (hr : find_restaurant list1 list2 = ok r) :
    (strsOf r.val).length ≤ min (strsOf list1.val).length (strsOf list2.val).length := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (list1 list2 : Slice (alloc.vec.Vec Std.U8)) (h : Pre list1 list2)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (hr : find_restaurant list1 list2 = ok r), (strsOf r.val).length ≤ min (strsOf list1.val).length (strsOf list2.val).length) := by
  sorry

/-- Whenever the function returns a result r, for every k with 0 <= k < len(r), 1 <= len(r[k]) <= 30.
  Preconditions: len(list1) and len(list2) are each between 1 and 1000; every element of list1 and every element of list2 has length between 1 and 30; every byte of every element is either 32 (space), an uppercase English letter (byte 65..90), or a lowercase English letter (byte 97..122); the elements of list1 are pairwise unequal and the elements of list2 are pairwise unequal; and there is at least one common string, i.e. there exist i with 0 <= i < len(list1) and j with 0 <= j < len(list2) such that list1[i] = list2[j]. -/
theorem spec_5
    (list1 list2 : Slice (alloc.vec.Vec Std.U8)) (h : Pre list1 list2)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (hr : find_restaurant list1 list2 = ok r) :
    ∀ (k : Nat) (x : ByteStr), HoldsAt (strsOf r.val) k x → 1 ≤ x.length ∧ x.length ≤ 30 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (list1 list2 : Slice (alloc.vec.Vec Std.U8)) (h : Pre list1 list2)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (hr : find_restaurant list1 list2 = ok r), ∀ (k : Nat) (x : ByteStr), HoldsAt (strsOf r.val) k x → 1 ≤ x.length ∧ x.length ≤ 30) := by
  sorry

/-- Whenever the function returns a result r, for all k,l with 0 <= k < l < len(r), r[k] != r[l].
  Preconditions: len(list1) and len(list2) are each between 1 and 1000; every element of list1 and every element of list2 has length between 1 and 30; every byte of every element is either 32 (space), an uppercase English letter (byte 65..90), or a lowercase English letter (byte 97..122); the elements of list1 are pairwise unequal and the elements of list2 are pairwise unequal; and there is at least one common string, i.e. there exist i with 0 <= i < len(list1) and j with 0 <= j < len(list2) such that list1[i] = list2[j]. -/
theorem spec_6
    (list1 list2 : Slice (alloc.vec.Vec Std.U8)) (h : Pre list1 list2)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (hr : find_restaurant list1 list2 = ok r) :
    ∀ (k l : Nat) (x y : ByteStr), HoldsAt (strsOf r.val) k x →
      HoldsAt (strsOf r.val) l y → k < l → x ≠ y := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (list1 list2 : Slice (alloc.vec.Vec Std.U8)) (h : Pre list1 list2)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (hr : find_restaurant list1 list2 = ok r), ∀ (k l : Nat) (x y : ByteStr), HoldsAt (strsOf r.val) k x →
      HoldsAt (strsOf r.val) l y → k < l → x ≠ y) := by
  sorry

/-- Whenever the function returns a result r, for every k with 0 <= k < len(r), there exist i,j such that 0 <= i < len(list1), 0 <= j < len(list2), list1[i] = r[k], and list2[j] = r[k].
  Preconditions: len(list1) and len(list2) are each between 1 and 1000; every element of list1 and every element of list2 has length between 1 and 30; every byte of every element is either 32 (space), an uppercase English letter (byte 65..90), or a lowercase English letter (byte 97..122); the elements of list1 are pairwise unequal and the elements of list2 are pairwise unequal; and there is at least one common string, i.e. there exist i with 0 <= i < len(list1) and j with 0 <= j < len(list2) such that list1[i] = list2[j]. -/
theorem spec_7
    (list1 list2 : Slice (alloc.vec.Vec Std.U8)) (h : Pre list1 list2)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (hr : find_restaurant list1 list2 = ok r) :
    ∀ (k : Nat) (x : ByteStr), HoldsAt (strsOf r.val) k x →
      ∃ (i j : Nat), HoldsAt (strsOf list1.val) i x ∧ HoldsAt (strsOf list2.val) j x := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (list1 list2 : Slice (alloc.vec.Vec Std.U8)) (h : Pre list1 list2)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (hr : find_restaurant list1 list2 = ok r), ∀ (k : Nat) (x : ByteStr), HoldsAt (strsOf r.val) k x →
      ∃ (i j : Nat), HoldsAt (strsOf list1.val) i x ∧ HoldsAt (strsOf list2.val) j x) := by
  sorry

/-- Whenever the function returns a result r, let m be the least value of i+j over all pairs (i,j) with 0 <= i < len(list1), 0 <= j < len(list2), and list1[i] = list2[j]. For every pair (i,j) with those three conditions and i+j = m, there exists k with 0 <= k < len(r) and r[k] = list1[i].
  Preconditions: len(list1) and len(list2) are each between 1 and 1000; every element of list1 and every element of list2 has length between 1 and 30; every byte of every element is either 32 (space), an uppercase English letter (byte 65..90), or a lowercase English letter (byte 97..122); the elements of list1 are pairwise unequal and the elements of list2 are pairwise unequal; and there is at least one common string, i.e. there exist i with 0 <= i < len(list1) and j with 0 <= j < len(list2) such that list1[i] = list2[j]. -/
theorem spec_8
    (list1 list2 : Slice (alloc.vec.Vec Std.U8)) (h : Pre list1 list2)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (hr : find_restaurant list1 list2 = ok r)
    (m : Nat) (hm : IsMinCommonSum (strsOf list1.val) (strsOf list2.val) m) :
    ∀ (i j : Nat) (x : ByteStr), HoldsAt (strsOf list1.val) i x →
      HoldsAt (strsOf list2.val) j x → i + j = m →
      ∃ (k : Nat), HoldsAt (strsOf r.val) k x := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (list1 list2 : Slice (alloc.vec.Vec Std.U8)) (h : Pre list1 list2)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (hr : find_restaurant list1 list2 = ok r)
    (m : Nat) (hm : IsMinCommonSum (strsOf list1.val) (strsOf list2.val) m), ∀ (i j : Nat) (x : ByteStr), HoldsAt (strsOf list1.val) i x →
      HoldsAt (strsOf list2.val) j x → i + j = m →
      ∃ (k : Nat), HoldsAt (strsOf r.val) k x) := by
  sorry

/-- Whenever the function returns a result r, let m be the least value of i+j over all pairs (i,j) with 0 <= i < len(list1), 0 <= j < len(list2), and list1[i] = list2[j]. For every k with 0 <= k < len(r), and for every i,j with 0 <= i < len(list1), 0 <= j < len(list2), list1[i] = r[k], and list2[j] = r[k], we have i+j = m.
  Preconditions: len(list1) and len(list2) are each between 1 and 1000; every element of list1 and every element of list2 has length between 1 and 30; every byte of every element is either 32 (space), an uppercase English letter (byte 65..90), or a lowercase English letter (byte 97..122); the elements of list1 are pairwise unequal and the elements of list2 are pairwise unequal; and there is at least one common string, i.e. there exist i with 0 <= i < len(list1) and j with 0 <= j < len(list2) such that list1[i] = list2[j]. -/
theorem spec_9
    (list1 list2 : Slice (alloc.vec.Vec Std.U8)) (h : Pre list1 list2)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (hr : find_restaurant list1 list2 = ok r)
    (m : Nat) (hm : IsMinCommonSum (strsOf list1.val) (strsOf list2.val) m) :
    ∀ (k : Nat) (x : ByteStr), HoldsAt (strsOf r.val) k x →
      ∀ (i j : Nat), HoldsAt (strsOf list1.val) i x → HoldsAt (strsOf list2.val) j x →
        i + j = m := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (list1 list2 : Slice (alloc.vec.Vec Std.U8)) (h : Pre list1 list2)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (hr : find_restaurant list1 list2 = ok r)
    (m : Nat) (hm : IsMinCommonSum (strsOf list1.val) (strsOf list2.val) m), ∀ (k : Nat) (x : ByteStr), HoldsAt (strsOf r.val) k x →
      ∀ (i j : Nat), HoldsAt (strsOf list1.val) i x → HoldsAt (strsOf list2.val) j x →
        i + j = m) := by
  sorry

/-- Whenever the function returns a result r, for all k,l with 0 <= k < len(r) and 0 <= l < len(r), for all i,j,i',j' with 0 <= i < len(list1), 0 <= i' < len(list1), 0 <= j < len(list2), and 0 <= j' < len(list2), if list1[i] = r[k], list2[j] = r[k], list1[i'] = r[l], and list2[j'] = r[l], then i+j = i'+j'.
  Preconditions: len(list1) and len(list2) are each between 1 and 1000; every element of list1 and every element of list2 has length between 1 and 30; every byte of every element is either 32 (space), an uppercase English letter (byte 65..90), or a lowercase English letter (byte 97..122); the elements of list1 are pairwise unequal and the elements of list2 are pairwise unequal; and there is at least one common string, i.e. there exist i with 0 <= i < len(list1) and j with 0 <= j < len(list2) such that list1[i] = list2[j]. -/
theorem spec_10
    (list1 list2 : Slice (alloc.vec.Vec Std.U8)) (h : Pre list1 list2)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (hr : find_restaurant list1 list2 = ok r) :
    ∀ (k l : Nat) (x y : ByteStr), HoldsAt (strsOf r.val) k x →
      HoldsAt (strsOf r.val) l y →
      ∀ (i j i' j' : Nat), HoldsAt (strsOf list1.val) i x →
        HoldsAt (strsOf list2.val) j x → HoldsAt (strsOf list1.val) i' y →
        HoldsAt (strsOf list2.val) j' y → i + j = i' + j' := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (list1 list2 : Slice (alloc.vec.Vec Std.U8)) (h : Pre list1 list2)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (hr : find_restaurant list1 list2 = ok r), ∀ (k l : Nat) (x y : ByteStr), HoldsAt (strsOf r.val) k x →
      HoldsAt (strsOf r.val) l y →
      ∀ (i j i' j' : Nat), HoldsAt (strsOf list1.val) i x →
        HoldsAt (strsOf list2.val) j x → HoldsAt (strsOf list1.val) i' y →
        HoldsAt (strsOf list2.val) j' y → i + j = i' + j') := by
  sorry

/-- Whenever the function returns a result r, let m be the least value of i+j over all pairs (i,j) with 0 <= i < len(list1), 0 <= j < len(list2), and list1[i] = list2[j]. Then len(r) equals the number of byte strings x for which there exist i,j with 0 <= i < len(list1), 0 <= j < len(list2), list1[i] = x, list2[j] = x, and i+j = m.
  Preconditions: len(list1) and len(list2) are each between 1 and 1000; every element of list1 and every element of list2 has length between 1 and 30; every byte of every element is either 32 (space), an uppercase English letter (byte 65..90), or a lowercase English letter (byte 97..122); the elements of list1 are pairwise unequal and the elements of list2 are pairwise unequal; and there is at least one common string, i.e. there exist i with 0 <= i < len(list1) and j with 0 <= j < len(list2) such that list1[i] = list2[j]. -/
theorem spec_11
    (list1 list2 : Slice (alloc.vec.Vec Std.U8)) (h : Pre list1 list2)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (hr : find_restaurant list1 list2 = ok r)
    (m : Nat) (hm : IsMinCommonSum (strsOf list1.val) (strsOf list2.val) m) :
    (strsOf r.val).length = numAtMinCommonSum (strsOf list1.val) (strsOf list2.val) m := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (list1 list2 : Slice (alloc.vec.Vec Std.U8)) (h : Pre list1 list2)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (hr : find_restaurant list1 list2 = ok r)
    (m : Nat) (hm : IsMinCommonSum (strsOf list1.val) (strsOf list2.val) m), (strsOf r.val).length = numAtMinCommonSum (strsOf list1.val) (strsOf list2.val) m) := by
  sorry

end AegisSpec.FindRestaurant
