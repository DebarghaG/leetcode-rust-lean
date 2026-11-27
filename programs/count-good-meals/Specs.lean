import Aegis.CountPairs.Code.Funs

/-!
# Specifications of `Aegis.CountPairs.count_pairs`

LeetCode problem `count-good-meals`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.CountPairs

  def IsPowerOfTwo (x : ℤ) : Prop := ∃ k : ℕ, x = 2 ^ k

  def values (s : Slice Std.I64) : List ℤ := s.val.map (fun x => x.val)

  noncomputable def pairCount (l : List ℤ) : ℕ := by
    classical
    exact (Finset.univ.filter (fun p : Fin l.length × Fin l.length =>
      p.1 < p.2 ∧ IsPowerOfTwo (l.get p.1 + l.get p.2))).card

  noncomputable def partnerCount (l : List ℤ) (x : ℤ) : ℕ := by
    classical
    exact (Finset.univ.filter (fun i : Fin l.length => IsPowerOfTwo (l.get i + x))).card

  /-- Let n = len(deliciousness). Let C be the number of pairs of indices (i,j) with 0 <= i < j < n such that deliciousness[i] + deliciousness[j] = 2^k for some integer k >= 0 (equivalently, the sum is one of 1, 2, 4, 8, ...). The function returns a result r with r = C mod 1000000007 and 0 <= r < 1000000007, and the call does not fail.
    Preconditions: 1 <= len(deliciousness) <= 100000; for every index i with 0 <= i < len(deliciousness), 0 <= deliciousness[i] <= 1048576 (= 2^20). -/
  theorem spec_1 (deliciousness : Slice Std.I64)
      (hne : 1 ≤ deliciousness.val.length)
      (hle : deliciousness.val.length ≤ 100000)
      (hrange : ∀ x ∈ deliciousness.val, 0 ≤ x.val ∧ x.val ≤ 1048576) :
      ∃ r : Std.I64, Aegis.CountPairs.count_pairs deliciousness = ok r ∧
        r.val = (((pairCount (values deliciousness) : ℤ)) % 1000000007) ∧
        0 ≤ r.val ∧ r.val < 1000000007 := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (deliciousness : Slice Std.I64)
        (hne : 1 ≤ deliciousness.val.length)
        (hle : deliciousness.val.length ≤ 100000)
        (hrange : ∀ x ∈ deliciousness.val, 0 ≤ x.val ∧ x.val ≤ 1048576), ∃ r : Std.I64, Aegis.CountPairs.count_pairs deliciousness = ok r ∧
          r.val = (((pairCount (values deliciousness) : ℤ)) % 1000000007) ∧
          0 ≤ r.val ∧ r.val < 1000000007) := by
    sorry

  /-- For every slice deliciousness satisfying the preconditions, the function returns a result r; it does not fail, panic, overflow, or access out of bounds.
    Preconditions: 1 <= len(deliciousness) <= 100000; for every index i with 0 <= i < len(deliciousness), 0 <= deliciousness[i] <= 1048576 (= 2^20). -/
  theorem spec_2 (deliciousness : Slice Std.I64)
      (hne : 1 ≤ deliciousness.val.length)
      (hle : deliciousness.val.length ≤ 100000)
      (hrange : ∀ x ∈ deliciousness.val, 0 ≤ x.val ∧ x.val ≤ 1048576) :
      ∃ r : Std.I64, Aegis.CountPairs.count_pairs deliciousness = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (deliciousness : Slice Std.I64)
        (hne : 1 ≤ deliciousness.val.length)
        (hle : deliciousness.val.length ≤ 100000)
        (hrange : ∀ x ∈ deliciousness.val, 0 ≤ x.val ∧ x.val ≤ 1048576), ∃ r : Std.I64, Aegis.CountPairs.count_pairs deliciousness = ok r) := by
    sorry

  /-- Whenever the function returns a result r on an input satisfying the preconditions, 0 <= r < 1000000007.
    Preconditions: 1 <= len(deliciousness) <= 100000; for every index i with 0 <= i < len(deliciousness), 0 <= deliciousness[i] <= 1048576 (= 2^20). -/
  theorem spec_3 (deliciousness : Slice Std.I64)
      (hne : 1 ≤ deliciousness.val.length)
      (hle : deliciousness.val.length ≤ 100000)
      (hrange : ∀ x ∈ deliciousness.val, 0 ≤ x.val ∧ x.val ≤ 1048576) :
      ∀ r : Std.I64, Aegis.CountPairs.count_pairs deliciousness = ok r →
        0 ≤ r.val ∧ r.val < 1000000007 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (deliciousness : Slice Std.I64)
        (hne : 1 ≤ deliciousness.val.length)
        (hle : deliciousness.val.length ≤ 100000)
        (hrange : ∀ x ∈ deliciousness.val, 0 ≤ x.val ∧ x.val ≤ 1048576), ∀ r : Std.I64, Aegis.CountPairs.count_pairs deliciousness = ok r →
          0 ≤ r.val ∧ r.val < 1000000007) := by
    sorry

  /-- Let r be the result returned by count_pairs(deliciousness) and s be the result returned by count_pairs(other). Then r = s.
    Preconditions: deliciousness and other are slices, each satisfying 1 <= len <= 100000 and entries in [0, 1048576]; other is a permutation of deliciousness (same length and same multiset of entries). -/
  theorem spec_4 (deliciousness other : Slice Std.I64)
      (hne₁ : 1 ≤ deliciousness.val.length)
      (hle₁ : deliciousness.val.length ≤ 100000)
      (hrange₁ : ∀ x ∈ deliciousness.val, 0 ≤ x.val ∧ x.val ≤ 1048576)
      (hne₂ : 1 ≤ other.val.length)
      (hle₂ : other.val.length ≤ 100000)
      (hrange₂ : ∀ x ∈ other.val, 0 ≤ x.val ∧ x.val ≤ 1048576)
      (hperm : deliciousness.val.Perm other.val) :
      ∀ r s : Std.I64, Aegis.CountPairs.count_pairs deliciousness = ok r →
        Aegis.CountPairs.count_pairs other = ok s → r = s := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (deliciousness other : Slice Std.I64)
        (hne₁ : 1 ≤ deliciousness.val.length)
        (hle₁ : deliciousness.val.length ≤ 100000)
        (hrange₁ : ∀ x ∈ deliciousness.val, 0 ≤ x.val ∧ x.val ≤ 1048576)
        (hne₂ : 1 ≤ other.val.length)
        (hle₂ : other.val.length ≤ 100000)
        (hrange₂ : ∀ x ∈ other.val, 0 ≤ x.val ∧ x.val ≤ 1048576)
        (hperm : deliciousness.val.Perm other.val), ∀ r s : Std.I64, Aegis.CountPairs.count_pairs deliciousness = ok r →
          Aegis.CountPairs.count_pairs other = ok s → r = s) := by
    sorry

  /-- Let k be the number of indices i with 0 <= i < len(p) such that p[i] + x = 2^t for some integer t >= 0. Let r_p be the result of count_pairs(p) and r_x be the result of count_pairs(xs). Then r_x and r_p + k have the same residue modulo 1000000007.
    Preconditions: p is a slice with 1 <= len(p) <= 99999 and 0 <= p[i] <= 1048576 for every 0 <= i < len(p); x is an integer with 0 <= x <= 1048576. Let xs be the slice p followed by the single element x, so len(xs) = len(p)+1. -/
  theorem spec_5 (p xs : Slice Std.I64) (x : Std.I64)
      (hne : 1 ≤ p.val.length)
      (hle : p.val.length ≤ 99999)
      (hrange : ∀ y ∈ p.val, 0 ≤ y.val ∧ y.val ≤ 1048576)
      (hx0 : 0 ≤ x.val)
      (hx1 : x.val ≤ 1048576)
      (hxs : xs.val = p.val ++ [x]) :
      ∀ r_p r_x : Std.I64,
        Aegis.CountPairs.count_pairs p = ok r_p →
        Aegis.CountPairs.count_pairs xs = ok r_x →
        Int.ModEq 1000000007 r_x.val
          (r_p.val + ((partnerCount (values p) x.val : ℤ))) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (p xs : Slice Std.I64) (x : Std.I64)
        (hne : 1 ≤ p.val.length)
        (hle : p.val.length ≤ 99999)
        (hrange : ∀ y ∈ p.val, 0 ≤ y.val ∧ y.val ≤ 1048576)
        (hx0 : 0 ≤ x.val)
        (hx1 : x.val ≤ 1048576)
        (hxs : xs.val = p.val ++ [x]), ∀ r_p r_x : Std.I64,
          Aegis.CountPairs.count_pairs p = ok r_p →
          Aegis.CountPairs.count_pairs xs = ok r_x →
          Int.ModEq 1000000007 r_x.val
            (r_p.val + ((partnerCount (values p) x.val : ℤ)))) := by
    sorry

  /-- Whenever the function returns a nonzero result r (r != 0), there exist indices i,j with 0 <= i < j < len(deliciousness) such that deliciousness[i] + deliciousness[j] = 2^k for some integer k >= 0.
    Preconditions: 1 <= len(deliciousness) <= 100000; for every index i with 0 <= i < len(deliciousness), 0 <= deliciousness[i] <= 1048576 (= 2^20). -/
  theorem spec_6 (deliciousness : Slice Std.I64)
      (hne : 1 ≤ deliciousness.val.length)
      (hle : deliciousness.val.length ≤ 100000)
      (hrange : ∀ x ∈ deliciousness.val, 0 ≤ x.val ∧ x.val ≤ 1048576) :
      ∀ r : Std.I64, Aegis.CountPairs.count_pairs deliciousness = ok r → r.val ≠ 0 →
        ∃ i j : Fin deliciousness.val.length, i < j ∧
          IsPowerOfTwo ((deliciousness.val.get i).val + (deliciousness.val.get j).val) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (deliciousness : Slice Std.I64)
        (hne : 1 ≤ deliciousness.val.length)
        (hle : deliciousness.val.length ≤ 100000)
        (hrange : ∀ x ∈ deliciousness.val, 0 ≤ x.val ∧ x.val ≤ 1048576), ∀ r : Std.I64, Aegis.CountPairs.count_pairs deliciousness = ok r → r.val ≠ 0 →
          ∃ i j : Fin deliciousness.val.length, i < j ∧
            IsPowerOfTwo ((deliciousness.val.get i).val + (deliciousness.val.get j).val)) := by
    sorry

  /-- Whenever the function returns a result r, r <= min(len(deliciousness) * (len(deliciousness) - 1) / 2, 1000000006), where the division is exact integer division of the product of consecutive nonnegative integers.
    Preconditions: 1 <= len(deliciousness) <= 100000; for every index i with 0 <= i < len(deliciousness), 0 <= deliciousness[i] <= 1048576 (= 2^20). -/
  theorem spec_7 (deliciousness : Slice Std.I64)
      (hne : 1 ≤ deliciousness.val.length)
      (hle : deliciousness.val.length ≤ 100000)
      (hrange : ∀ x ∈ deliciousness.val, 0 ≤ x.val ∧ x.val ≤ 1048576) :
      ∀ r : Std.I64, Aegis.CountPairs.count_pairs deliciousness = ok r →
        r.val ≤ min (((deliciousness.val.length : ℤ) *
          (((deliciousness.val.length : ℤ)) - 1)) / 2) 1000000006 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (deliciousness : Slice Std.I64)
        (hne : 1 ≤ deliciousness.val.length)
        (hle : deliciousness.val.length ≤ 100000)
        (hrange : ∀ x ∈ deliciousness.val, 0 ≤ x.val ∧ x.val ≤ 1048576), ∀ r : Std.I64, Aegis.CountPairs.count_pairs deliciousness = ok r →
          r.val ≤ min (((deliciousness.val.length : ℤ) *
            (((deliciousness.val.length : ℤ)) - 1)) / 2) 1000000006) := by
    sorry

  end AegisSpec.CountPairs
