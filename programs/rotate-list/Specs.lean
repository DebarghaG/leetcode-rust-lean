import Aegis.RotateRight.Code.Funs

/-!
# Specifications of `Aegis.RotateRight.rotate_right`

LeetCode problem `rotate-list`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace Aegis.RotateRight

def List.val : List → _root_.List ℤ
  | List.Nil => []
  | List.Cons v next => v.val :: List.val next

def List.length (l : List) : Nat := (List.val l).length

end Aegis.RotateRight

namespace AegisSpec.RotateRight

open Aegis.RotateRight

def shift (n : Nat) (k : Int) : Nat := if n = 0 then 0 else (k % (n : Int)).toNat

def countOcc (v : Int) : _root_.List Int → Nat
  | [] => 0
  | x :: xs => (if x = v then 1 else 0) + countOcc v xs

def subseq (xs : _root_.List Int) (a b : Nat) : _root_.List Int := (xs.drop a).take (b - a)

def i64OfNat (m : Nat) : Std.I64 :=
  UScalar.hcast .I64 ⟨BitVec.ofNat (UScalarTy.numBits .Usize) m⟩

/-- Let xs be the sequence of values stored in head from front to back, and let n = len(head). Put r = 0 if n = 0, and r = k mod n if n > 0. The function returns a result res. Let ys be the sequence of values stored in res from front to back. Then len(ys) = n, and: (1) if n = 0, ys = [] (so res = Nil); (2) if n > 0, for every i with 0 <= i < n, ys[i] = xs[(i + n - r) mod n]. This is exactly the right rotation of the list by r places, where r is the unique integer in [0,n) congruent to k modulo n.
  Preconditions: len(head) <= 500; every value in head is between -100 and 100 inclusive; 0 <= k <= 2000000000 (k interpreted as an integer). -/
theorem spec_1 (head : Aegis.RotateRight.List) (k : Std.I64)
    (hlen : head.length ≤ 500)
    (hbounds : ∀ v ∈ head.val, -100 ≤ v ∧ v ≤ 100)
    (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ 2000000000) :
    ∃ res : Aegis.RotateRight.List,
      rotate_right head k = ok res ∧
      res.length = head.length ∧
      (head.length = 0 → res.val = []) ∧
      (∀ i : Nat, i < head.length →
        res.val[i]? =
          head.val[(i + head.length - shift head.length k.val) % head.length]?) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (head : Aegis.RotateRight.List) (k : Std.I64)
    (hlen : head.length ≤ 500)
    (hbounds : ∀ v ∈ head.val, -100 ≤ v ∧ v ≤ 100)
    (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ 2000000000), ∃ res : Aegis.RotateRight.List,
      rotate_right head k = ok res ∧
      res.length = head.length ∧
      (head.length = 0 → res.val = []) ∧
      (∀ i : Nat, i < head.length →
        res.val[i]? =
          head.val[(i + head.length - shift head.length k.val) % head.length]?)) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result res; it does not fail, overflow, panic, or go out of bounds.
  Preconditions: len(head) <= 500; every value in head is between -100 and 100 inclusive; 0 <= k <= 2000000000 (k interpreted as an integer). -/
theorem spec_2 (head : Aegis.RotateRight.List) (k : Std.I64)
    (hlen : head.length ≤ 500)
    (hbounds : ∀ v ∈ head.val, -100 ≤ v ∧ v ≤ 100)
    (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ 2000000000) :
    ∃ res : Aegis.RotateRight.List, rotate_right head k = ok res := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (head : Aegis.RotateRight.List) (k : Std.I64)
    (hlen : head.length ≤ 500)
    (hbounds : ∀ v ∈ head.val, -100 ≤ v ∧ v ≤ 100)
    (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ 2000000000), ∃ res : Aegis.RotateRight.List, rotate_right head k = ok res) := by
  sorry

/-- Whenever the function returns a result res, the number of Cons nodes in res equals the number of Cons nodes in head, i.e. len(res) = len(head).
  Preconditions: len(head) <= 500; every value in head is between -100 and 100 inclusive; 0 <= k <= 2000000000 (k interpreted as an integer). -/
theorem spec_3 (head : Aegis.RotateRight.List) (k : Std.I64)
    (hlen : head.length ≤ 500)
    (hbounds : ∀ v ∈ head.val, -100 ≤ v ∧ v ≤ 100)
    (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ 2000000000) :
    ∀ res : Aegis.RotateRight.List, rotate_right head k = ok res → res.length = head.length := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (head : Aegis.RotateRight.List) (k : Std.I64)
    (hlen : head.length ≤ 500)
    (hbounds : ∀ v ∈ head.val, -100 ≤ v ∧ v ≤ 100)
    (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ 2000000000), ∀ res : Aegis.RotateRight.List, rotate_right head k = ok res → res.length = head.length) := by
  sorry

/-- Let xs be the sequence of values in head and ys the sequence of values in res. Whenever the function returns a result res, for every integer v, the number of indices i with ys[i] = v equals the number of indices j with xs[j] = v.
  Preconditions: len(head) <= 500; every value in head is between -100 and 100 inclusive; 0 <= k <= 2000000000 (k interpreted as an integer). -/
theorem spec_4 (head : Aegis.RotateRight.List) (k : Std.I64)
    (hlen : head.length ≤ 500)
    (hbounds : ∀ v ∈ head.val, -100 ≤ v ∧ v ≤ 100)
    (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ 2000000000) :
    ∀ res : Aegis.RotateRight.List, rotate_right head k = ok res →
      ∀ v : Int, countOcc v res.val = countOcc v head.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (head : Aegis.RotateRight.List) (k : Std.I64)
    (hlen : head.length ≤ 500)
    (hbounds : ∀ v ∈ head.val, -100 ≤ v ∧ v ≤ 100)
    (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ 2000000000), ∀ res : Aegis.RotateRight.List, rotate_right head k = ok res →
      ∀ v : Int, countOcc v res.val = countOcc v head.val) := by
  sorry

/-- Whenever the function returns a result res, every value v occurring in res satisfies -100 <= v <= 100.
  Preconditions: len(head) <= 500; every value in head is between -100 and 100 inclusive; 0 <= k <= 2000000000 (k interpreted as an integer). -/
theorem spec_5 (head : Aegis.RotateRight.List) (k : Std.I64)
    (hlen : head.length ≤ 500)
    (hbounds : ∀ v ∈ head.val, -100 ≤ v ∧ v ≤ 100)
    (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ 2000000000) :
    ∀ res : Aegis.RotateRight.List, rotate_right head k = ok res →
      ∀ v : Int, v ∈ res.val → -100 ≤ v ∧ v ≤ 100 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (head : Aegis.RotateRight.List) (k : Std.I64)
    (hlen : head.length ≤ 500)
    (hbounds : ∀ v ∈ head.val, -100 ≤ v ∧ v ≤ 100)
    (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ 2000000000), ∀ res : Aegis.RotateRight.List, rotate_right head k = ok res →
      ∀ v : Int, v ∈ res.val → -100 ≤ v ∧ v ≤ 100) := by
  sorry

/-- If rotate_right(head,k1) returns res1 and rotate_right(head,k2) returns res2, then res1 and res2 have the same sequence of node values (equivalently, res1 = res2 as List values).
  Preconditions: len(head) <= 500; every value in head is between -100 and 100 inclusive; n = len(head) > 0; k1 and k2 are integers with 0 <= k1 <= 2000000000, 0 <= k2 <= 2000000000, and k1 mod n = k2 mod n. -/
theorem spec_6 (head : Aegis.RotateRight.List) (k1 k2 : Std.I64)
    (hlen : head.length ≤ 500)
    (hbounds : ∀ v ∈ head.val, -100 ≤ v ∧ v ≤ 100)
    (hn : 0 < head.length)
    (hk1_nonneg : 0 ≤ k1.val) (hk1_le : k1.val ≤ 2000000000)
    (hk2_nonneg : 0 ≤ k2.val) (hk2_le : k2.val ≤ 2000000000)
    (hmod : k1.val % (head.length : Int) = k2.val % (head.length : Int)) :
    ∀ res1 res2 : Aegis.RotateRight.List,
      rotate_right head k1 = ok res1 → rotate_right head k2 = ok res2 →
      res1.val = res2.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (head : Aegis.RotateRight.List) (k1 k2 : Std.I64)
    (hlen : head.length ≤ 500)
    (hbounds : ∀ v ∈ head.val, -100 ≤ v ∧ v ≤ 100)
    (hn : 0 < head.length)
    (hk1_nonneg : 0 ≤ k1.val) (hk1_le : k1.val ≤ 2000000000)
    (hk2_nonneg : 0 ≤ k2.val) (hk2_le : k2.val ≤ 2000000000)
    (hmod : k1.val % (head.length : Int) = k2.val % (head.length : Int)), ∀ res1 res2 : Aegis.RotateRight.List,
      rotate_right head k1 = ok res1 → rotate_right head k2 = ok res2 →
      res1.val = res2.val) := by
  sorry

/-- Whenever the function returns a result res, res = head (the same sequence of node values, hence the same List).
  Preconditions: len(head) <= 500; every value in head is between -100 and 100 inclusive; k = 0. -/
theorem spec_7 (head : Aegis.RotateRight.List) (k : Std.I64)
    (hlen : head.length ≤ 500)
    (hbounds : ∀ v ∈ head.val, -100 ≤ v ∧ v ≤ 100)
    (hk : k.val = 0) :
    ∀ res : Aegis.RotateRight.List, rotate_right head k = ok res → res = head := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (head : Aegis.RotateRight.List) (k : Std.I64)
    (hlen : head.length ≤ 500)
    (hbounds : ∀ v ∈ head.val, -100 ≤ v ∧ v ≤ 100)
    (hk : k.val = 0), ∀ res : Aegis.RotateRight.List, rotate_right head k = ok res → res = head) := by
  sorry

/-- Whenever the function returns a result res, res = Nil.
  Preconditions: head = Nil; 0 <= k <= 2000000000 (k interpreted as an integer). -/
theorem spec_8 (head : Aegis.RotateRight.List) (k : Std.I64)
    (hhead : head = Aegis.RotateRight.List.Nil)
    (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ 2000000000) :
    ∀ res : Aegis.RotateRight.List,
      rotate_right head k = ok res → res = Aegis.RotateRight.List.Nil := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (head : Aegis.RotateRight.List) (k : Std.I64)
    (hhead : head = Aegis.RotateRight.List.Nil)
    (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ 2000000000), ∀ res : Aegis.RotateRight.List,
      rotate_right head k = ok res → res = Aegis.RotateRight.List.Nil) := by
  sorry

/-- Whenever the function returns a result res, res = head.
  Preconditions: len(head) = 1; every value in head is between -100 and 100 inclusive; 0 <= k <= 2000000000 (k interpreted as an integer). -/
theorem spec_9 (head : Aegis.RotateRight.List) (k : Std.I64)
    (hlen : head.length = 1)
    (hbounds : ∀ v ∈ head.val, -100 ≤ v ∧ v ≤ 100)
    (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ 2000000000) :
    ∀ res : Aegis.RotateRight.List, rotate_right head k = ok res → res = head := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (head : Aegis.RotateRight.List) (k : Std.I64)
    (hlen : head.length = 1)
    (hbounds : ∀ v ∈ head.val, -100 ≤ v ∧ v ≤ 100)
    (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ 2000000000), ∀ res : Aegis.RotateRight.List, rotate_right head k = ok res → res = head) := by
  sorry

/-- Let n = len(head), and let xs and ys be the value sequences of head and res respectively. Put r = 0 if n = 0, and r = k mod n if n > 0. Whenever the function returns a result res: if n = 0 then ys = []; if n > 0 then ys = xs[n-r .. n] ++ xs[0 .. n-r], where xs[a .. b] denotes the contiguous subsequence from index a inclusive to index b exclusive, and ++ denotes concatenation.
  Preconditions: len(head) <= 500; every value in head is between -100 and 100 inclusive; 0 <= k <= 2000000000 (k interpreted as an integer). -/
theorem spec_10 (head : Aegis.RotateRight.List) (k : Std.I64)
    (hlen : head.length ≤ 500)
    (hbounds : ∀ v ∈ head.val, -100 ≤ v ∧ v ≤ 100)
    (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ 2000000000) :
    ∀ res : Aegis.RotateRight.List, rotate_right head k = ok res →
      (head.length = 0 → res.val = []) ∧
      (0 < head.length →
        res.val =
          subseq head.val (head.length - shift head.length k.val) head.length ++
            subseq head.val 0 (head.length - shift head.length k.val)) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (head : Aegis.RotateRight.List) (k : Std.I64)
    (hlen : head.length ≤ 500)
    (hbounds : ∀ v ∈ head.val, -100 ≤ v ∧ v ≤ 100)
    (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ 2000000000), ∀ res : Aegis.RotateRight.List, rotate_right head k = ok res →
      (head.length = 0 → res.val = []) ∧
      (0 < head.length →
        res.val =
          subseq head.val (head.length - shift head.length k.val) head.length ++
            subseq head.val 0 (head.length - shift head.length k.val))) := by
  sorry

/-- Let n = len(head) and r = 0 if n = 0 else k mod n. If the function returns a result res, then for n > 0 the further call rotate_right(res, (n - r) mod n) returns a list whose value sequence equals the value sequence of head (i.e. the rotation is invertible: a right rotation by r followed by a right rotation by n - r restores the original list).
  Preconditions: len(head) <= 500; every value in head is between -100 and 100 inclusive; 0 <= k <= 2000000000 (k interpreted as an integer). -/
theorem spec_11 (head : Aegis.RotateRight.List) (k : Std.I64)
    (hlen : head.length ≤ 500)
    (hbounds : ∀ v ∈ head.val, -100 ≤ v ∧ v ≤ 100)
    (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ 2000000000) :
    ∀ res : Aegis.RotateRight.List, rotate_right head k = ok res → 0 < head.length →
      ∃ res2 : Aegis.RotateRight.List,
        rotate_right res
            (i64OfNat ((head.length - shift head.length k.val) % head.length)) = ok res2 ∧
          res2.val = head.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (head : Aegis.RotateRight.List) (k : Std.I64)
    (hlen : head.length ≤ 500)
    (hbounds : ∀ v ∈ head.val, -100 ≤ v ∧ v ≤ 100)
    (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ 2000000000), ∀ res : Aegis.RotateRight.List, rotate_right head k = ok res → 0 < head.length →
      ∃ res2 : Aegis.RotateRight.List,
        rotate_right res
            (i64OfNat ((head.length - shift head.length k.val) % head.length)) = ok res2 ∧
          res2.val = head.val) := by
  sorry

end AegisSpec.RotateRight
