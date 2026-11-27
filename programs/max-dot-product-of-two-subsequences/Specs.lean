import Aegis.MaxDotProduct.Code.Funs

/-!
# Specifications of `Aegis.MaxDotProduct.max_dot_product`

LeetCode problem `max-dot-product-of-two-subsequences`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.MaxDotProduct

  namespace AegisSpec.MaxDotProduct

  def vals (s : Slice Std.I64) : List Int := s.val.map (fun x => x.val)

  def InRange (s : Slice Std.I64) : Prop :=
    1 ≤ s.val.length ∧ s.val.length ≤ 500 ∧
      ∀ (i : Nat) (hi : i < s.val.length), -1000 ≤ (s.val[i]'hi).val ∧ (s.val[i]'hi).val ≤ 1000

  def IsMaxOf (S : Int → Prop) (r : Int) : Prop := S r ∧ ∀ v, S v → v ≤ r

  noncomputable def selSum (n1 n2 : Slice Std.I64) (k : Nat) (f g : Fin k → Nat)
      (hf : ∀ t, f t < n1.val.length) (hg : ∀ t, g t < n2.val.length) : Int :=
    ∑ t : Fin k, (n1.val[f t]'(hf t)).val * (n2.val[g t]'(hg t)).val

  def achievableSums (n1 n2 : Slice Std.I64) : Int → Prop :=
    fun v =>
      ∃ (k : Nat) (f g : Fin k → Nat)
        (hf : ∀ t, f t < n1.val.length) (hg : ∀ t, g t < n2.val.length),
        1 ≤ k ∧ k ≤ Nat.min n1.val.length n2.val.length ∧ StrictMono f ∧ StrictMono g ∧
          v = selSum n1 n2 k f g hf hg

  def pairProducts (n1 n2 : Slice Std.I64) : Int → Prop :=
    fun v =>
      ∃ (i : Nat) (hi : i < n1.val.length) (j : Nat) (hj : j < n2.val.length),
        v = (n1.val[i]'hi).val * (n2.val[j]'hj).val

  noncomputable def alignSum (n1 n2 : Slice Std.I64) (n : Nat) (h1 : n ≤ n1.val.length)
      (h2 : n ≤ n2.val.length) : Int :=
    ∑ i : Fin n,
      (n1.val[i.val]'(Nat.lt_of_lt_of_le i.isLt h1)).val *
        (n2.val[i.val]'(Nat.lt_of_lt_of_le i.isLt h2)).val

  def iabs (x : Int) : Int := if x < 0 then -x else x

  def IsNegOf (t s : Slice Std.I64) : Prop := vals t = (vals s).map (fun x => -x)

  def IsRevOf (t s : Slice Std.I64) : Prop := vals t = (vals s).reverse

  def IsScaledOf (c : Int) (t s : Slice Std.I64) : Prop := vals t = (vals s).map (fun x => c * x)

  def IsAbsOf (t s : Slice Std.I64) : Prop := vals t = (vals s).map iabs

  def IsSubseqOf (t s : Slice Std.I64) : Prop := List.Sublist (vals t) (vals s)

  /-- Whenever max_dot_product(nums1, nums2) returns a result r, r equals the maximum of the set of all sums sum_{t=1}^{k} nums1[i_t] * nums2[j_t], where k is an integer with 1 <= k <= min(len(nums1), len(nums2)), 0 <= i_1 < i_2 < ... < i_k < len(nums1), and 0 <= j_1 < j_2 < ... < j_k < len(nums2).
    Preconditions: len(nums1) and len(nums2) are each between 1 and 500 inclusive; for every i with 0 <= i < len(nums1), -1000 <= nums1[i] <= 1000; for every j with 0 <= j < len(nums2), -1000 <= nums2[j] <= 1000. -/
  theorem spec_1 (nums1 nums2 : Slice Std.I64) (h1 : InRange nums1) (h2 : InRange nums2)
      (r : Std.I64) (hr : max_dot_product nums1 nums2 = ok r) :
      IsMaxOf (achievableSums nums1 nums2) r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64) (h1 : InRange nums1) (h2 : InRange nums2)
        (r : Std.I64) (hr : max_dot_product nums1 nums2 = ok r), IsMaxOf (achievableSums nums1 nums2) r.val) := by
    sorry

  /-- For every nums1 and nums2 satisfying the preconditions, the call max_dot_product(nums1, nums2) returns a result r and does not fail, panic, or overflow.
    Preconditions: len(nums1) and len(nums2) are each between 1 and 500 inclusive; for every i with 0 <= i < len(nums1), -1000 <= nums1[i] <= 1000; for every j with 0 <= j < len(nums2), -1000 <= nums2[j] <= 1000. -/
  theorem spec_2 (nums1 nums2 : Slice Std.I64) (h1 : InRange nums1) (h2 : InRange nums2) :
      ∃ r : Std.I64, max_dot_product nums1 nums2 = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64) (h1 : InRange nums1) (h2 : InRange nums2), ∃ r : Std.I64, max_dot_product nums1 nums2 = ok r) := by
    sorry

  /-- Whenever max_dot_product(nums1, nums2) returns a result r, there exist an integer k with 1 <= k <= min(len(nums1), len(nums2)) and strictly increasing 0-based index sequences 0 <= i_1 < ... < i_k < len(nums1) and 0 <= j_1 < ... < j_k < len(nums2) such that r = sum_{t=1}^{k} nums1[i_t] * nums2[j_t].
    Preconditions: len(nums1) and len(nums2) are each between 1 and 500 inclusive; for every i with 0 <= i < len(nums1), -1000 <= nums1[i] <= 1000; for every j with 0 <= j < len(nums2), -1000 <= nums2[j] <= 1000. -/
  theorem spec_3 (nums1 nums2 : Slice Std.I64) (h1 : InRange nums1) (h2 : InRange nums2)
      (r : Std.I64) (hr : max_dot_product nums1 nums2 = ok r) :
      ∃ (k : Nat) (f g : Fin k → Nat)
        (hf : ∀ t, f t < nums1.val.length) (hg : ∀ t, g t < nums2.val.length),
        1 ≤ k ∧ k ≤ Nat.min nums1.val.length nums2.val.length ∧ StrictMono f ∧ StrictMono g ∧
          r.val = selSum nums1 nums2 k f g hf hg := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64) (h1 : InRange nums1) (h2 : InRange nums2)
        (r : Std.I64) (hr : max_dot_product nums1 nums2 = ok r), ∃ (k : Nat) (f g : Fin k → Nat)
          (hf : ∀ t, f t < nums1.val.length) (hg : ∀ t, g t < nums2.val.length),
          1 ≤ k ∧ k ≤ Nat.min nums1.val.length nums2.val.length ∧ StrictMono f ∧ StrictMono g ∧
            r.val = selSum nums1 nums2 k f g hf hg) := by
    sorry

  /-- Whenever max_dot_product(nums1, nums2) returns a result r, for every i with 0 <= i < len(nums1) and every j with 0 <= j < len(nums2), r >= nums1[i] * nums2[j].
    Preconditions: len(nums1) and len(nums2) are each between 1 and 500 inclusive; for every i with 0 <= i < len(nums1), -1000 <= nums1[i] <= 1000; for every j with 0 <= j < len(nums2), -1000 <= nums2[j] <= 1000. -/
  theorem spec_4 (nums1 nums2 : Slice Std.I64) (h1 : InRange nums1) (h2 : InRange nums2)
      (r : Std.I64) (hr : max_dot_product nums1 nums2 = ok r) :
      ∀ (i : Nat) (hi : i < nums1.val.length) (j : Nat) (hj : j < nums2.val.length),
        r.val ≥ (nums1.val[i]'hi).val * (nums2.val[j]'hj).val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64) (h1 : InRange nums1) (h2 : InRange nums2)
        (r : Std.I64) (hr : max_dot_product nums1 nums2 = ok r), ∀ (i : Nat) (hi : i < nums1.val.length) (j : Nat) (hj : j < nums2.val.length),
          r.val ≥ (nums1.val[i]'hi).val * (nums2.val[j]'hj).val) := by
    sorry

  /-- Whenever max_dot_product(nums1, nums2) returns a result r, -1000000 <= r <= 500000000.
    Preconditions: len(nums1) and len(nums2) are each between 1 and 500 inclusive; for every i with 0 <= i < len(nums1), -1000 <= nums1[i] <= 1000; for every j with 0 <= j < len(nums2), -1000 <= nums2[j] <= 1000. -/
  theorem spec_5 (nums1 nums2 : Slice Std.I64) (h1 : InRange nums1) (h2 : InRange nums2)
      (r : Std.I64) (hr : max_dot_product nums1 nums2 = ok r) :
      -1000000 ≤ r.val ∧ r.val ≤ 500000000 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64) (h1 : InRange nums1) (h2 : InRange nums2)
        (r : Std.I64) (hr : max_dot_product nums1 nums2 = ok r), -1000000 ≤ r.val ∧ r.val ≤ 500000000) := by
    sorry

  /-- Whenever max_dot_product(nums1, nums2) returns a result r, r equals the maximum of the set { nums1[i] * nums2[j] | 0 <= i < len(nums1) and 0 <= j < len(nums2) }.
    Preconditions: len(nums1) and len(nums2) are each between 1 and 500 inclusive; for every i with 0 <= i < len(nums1), -1000 <= nums1[i] <= 1000; for every j with 0 <= j < len(nums2), -1000 <= nums2[j] <= 1000; min(len(nums1), len(nums2)) = 1. -/
  theorem spec_6 (nums1 nums2 : Slice Std.I64) (h1 : InRange nums1) (h2 : InRange nums2)
      (hmin : Nat.min nums1.val.length nums2.val.length = 1)
      (r : Std.I64) (hr : max_dot_product nums1 nums2 = ok r) :
      IsMaxOf (pairProducts nums1 nums2) r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64) (h1 : InRange nums1) (h2 : InRange nums2)
        (hmin : Nat.min nums1.val.length nums2.val.length = 1)
        (r : Std.I64) (hr : max_dot_product nums1 nums2 = ok r), IsMaxOf (pairProducts nums1 nums2) r.val) := by
    sorry

  /-- Whenever max_dot_product(nums1, nums2) returns a result r, r >= sum_{i=0}^{n-1} nums1[i] * nums2[i].
    Preconditions: len(nums1) = len(nums2) = n for some integer n with 1 <= n <= 500; for every i with 0 <= i < n, -1000 <= nums1[i] <= 1000 and -1000 <= nums2[i] <= 1000. -/
  theorem spec_7 (nums1 nums2 : Slice Std.I64) (n : Nat) (h1 : InRange nums1)
      (h2 : InRange nums2) (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
      (hn : 1 ≤ n ∧ n ≤ 500) (r : Std.I64) (hr : max_dot_product nums1 nums2 = ok r) :
      r.val ≥ alignSum nums1 nums2 n (le_of_eq hn1.symm) (le_of_eq hn2.symm) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64) (n : Nat) (h1 : InRange nums1)
        (h2 : InRange nums2) (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
        (hn : 1 ≤ n ∧ n ≤ 500) (r : Std.I64) (hr : max_dot_product nums1 nums2 = ok r), r.val ≥ alignSum nums1 nums2 n (le_of_eq hn1.symm) (le_of_eq hn2.symm)) := by
    sorry

  /-- Whenever max_dot_product(nums1, nums2) returns a result r and max_dot_product(nums2, nums1) returns a result s, r = s.
    Preconditions: len(nums1) and len(nums2) are each between 1 and 500 inclusive; for every i with 0 <= i < len(nums1), -1000 <= nums1[i] <= 1000; for every j with 0 <= j < len(nums2), -1000 <= nums2[j] <= 1000. -/
  theorem spec_8 (nums1 nums2 : Slice Std.I64) (h1 : InRange nums1) (h2 : InRange nums2)
      (r s : Std.I64) (hr : max_dot_product nums1 nums2 = ok r)
      (hs : max_dot_product nums2 nums1 = ok s) :
      r.val = s.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64) (h1 : InRange nums1) (h2 : InRange nums2)
        (r s : Std.I64) (hr : max_dot_product nums1 nums2 = ok r)
        (hs : max_dot_product nums2 nums1 = ok s), r.val = s.val) := by
    sorry

  /-- Let neg1 and neg2 be the arrays with neg1[i] = -nums1[i] and neg2[j] = -nums2[j]. Whenever max_dot_product(nums1, nums2) returns a result r and max_dot_product(neg1, neg2) returns a result s, r = s.
    Preconditions: len(nums1) and len(nums2) are each between 1 and 500 inclusive; for every i with 0 <= i < len(nums1), -1000 <= nums1[i] <= 1000; for every j with 0 <= j < len(nums2), -1000 <= nums2[j] <= 1000. -/
  theorem spec_9 (nums1 nums2 neg1 neg2 : Slice Std.I64) (h1 : InRange nums1)
      (h2 : InRange nums2) (hn1 : IsNegOf neg1 nums1) (hn2 : IsNegOf neg2 nums2)
      (r s : Std.I64) (hr : max_dot_product nums1 nums2 = ok r)
      (hs : max_dot_product neg1 neg2 = ok s) :
      r.val = s.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums1 nums2 neg1 neg2 : Slice Std.I64) (h1 : InRange nums1)
        (h2 : InRange nums2) (hn1 : IsNegOf neg1 nums1) (hn2 : IsNegOf neg2 nums2)
        (r s : Std.I64) (hr : max_dot_product nums1 nums2 = ok r)
        (hs : max_dot_product neg1 neg2 = ok s), r.val = s.val) := by
    sorry

  /-- Let rev1 and rev2 be the arrays with rev1[i] = nums1[len(nums1)-1-i] and rev2[j] = nums2[len(nums2)-1-j]. Whenever max_dot_product(nums1, nums2) returns a result r and max_dot_product(rev1, rev2) returns a result s, r = s.
    Preconditions: len(nums1) and len(nums2) are each between 1 and 500 inclusive; for every i with 0 <= i < len(nums1), -1000 <= nums1[i] <= 1000; for every j with 0 <= j < len(nums2), -1000 <= nums2[j] <= 1000. -/
  theorem spec_10 (nums1 nums2 rev1 rev2 : Slice Std.I64) (h1 : InRange nums1)
      (h2 : InRange nums2) (hrv1 : IsRevOf rev1 nums1) (hrv2 : IsRevOf rev2 nums2)
      (r s : Std.I64) (hr : max_dot_product nums1 nums2 = ok r)
      (hs : max_dot_product rev1 rev2 = ok s) :
      r.val = s.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums1 nums2 rev1 rev2 : Slice Std.I64) (h1 : InRange nums1)
        (h2 : InRange nums2) (hrv1 : IsRevOf rev1 nums1) (hrv2 : IsRevOf rev2 nums2)
        (r s : Std.I64) (hr : max_dot_product nums1 nums2 = ok r)
        (hs : max_dot_product rev1 rev2 = ok s), r.val = s.val) := by
    sorry

  /-- Let scaled1 be the array with scaled1[i] = c * nums1[i] for every i. Whenever max_dot_product(nums1, nums2) returns a result r and max_dot_product(scaled1, nums2) returns a result s, s = c * r.
    Preconditions: len(nums1) and len(nums2) are each between 1 and 500 inclusive; for every i with 0 <= i < len(nums1), -1000 <= nums1[i] <= 1000; for every j with 0 <= j < len(nums2), -1000 <= nums2[j] <= 1000; c is a positive integer and for every i with 0 <= i < len(nums1), -1000 <= c * nums1[i] <= 1000. -/
  theorem spec_11 (nums1 nums2 scaled1 : Slice Std.I64) (c : Int) (h1 : InRange nums1)
      (h2 : InRange nums2) (hc : 0 < c) (hsc : IsScaledOf c scaled1 nums1)
      (hbnd : ∀ (i : Nat) (hi : i < nums1.val.length),
        -1000 ≤ c * (nums1.val[i]'hi).val ∧ c * (nums1.val[i]'hi).val ≤ 1000)
      (r s : Std.I64) (hr : max_dot_product nums1 nums2 = ok r)
      (hs : max_dot_product scaled1 nums2 = ok s) :
      s.val = c * r.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums1 nums2 scaled1 : Slice Std.I64) (c : Int) (h1 : InRange nums1)
        (h2 : InRange nums2) (hc : 0 < c) (hsc : IsScaledOf c scaled1 nums1)
        (hbnd : ∀ (i : Nat) (hi : i < nums1.val.length),
          -1000 ≤ c * (nums1.val[i]'hi).val ∧ c * (nums1.val[i]'hi).val ≤ 1000)
        (r s : Std.I64) (hr : max_dot_product nums1 nums2 = ok r)
        (hs : max_dot_product scaled1 nums2 = ok s), s.val = c * r.val) := by
    sorry

  /-- Let M be the maximum of the set { nums1[i] * nums2[j] | 0 <= i < len(nums1) and 0 <= j < len(nums2) }. If M > 0, then whenever max_dot_product(nums1, nums2) returns a result r, r <= min(len(nums1), len(nums2)) * M.
    Preconditions: len(nums1) and len(nums2) are each between 1 and 500 inclusive; for every i with 0 <= i < len(nums1), -1000 <= nums1[i] <= 1000; for every j with 0 <= j < len(nums2), -1000 <= nums2[j] <= 1000. -/
  theorem spec_12 (nums1 nums2 : Slice Std.I64) (h1 : InRange nums1) (h2 : InRange nums2)
      (M : Int) (hM : IsMaxOf (pairProducts nums1 nums2) M) (hMpos : 0 < M)
      (r : Std.I64) (hr : max_dot_product nums1 nums2 = ok r) :
      r.val ≤ ((Nat.min nums1.val.length nums2.val.length : Nat) : Int) * M := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64) (h1 : InRange nums1) (h2 : InRange nums2)
        (M : Int) (hM : IsMaxOf (pairProducts nums1 nums2) M) (hMpos : 0 < M)
        (r : Std.I64) (hr : max_dot_product nums1 nums2 = ok r), r.val ≤ ((Nat.min nums1.val.length nums2.val.length : Nat) : Int) * M) := by
    sorry

  /-- Whenever max_dot_product(nums1, nums2) returns a result r and max_dot_product(nums1', nums2') returns a result s, r <= s.
    Preconditions: All four arrays nums1, nums2, nums1', nums2' have lengths between 1 and 500 inclusive and entries between -1000 and 1000. The array nums1 is a subsequence of nums1' (there exist strictly increasing indices p_1 < ... < p_len(nums1) in nums1' with nums1'[p_t] = nums1[t] for all t), and nums2 is a subsequence of nums2' (similarly). -/
  theorem spec_13 (nums1 nums2 nums1' nums2' : Slice Std.I64) (h1 : InRange nums1)
      (h2 : InRange nums2) (h1' : InRange nums1') (h2' : InRange nums2')
      (hs1 : IsSubseqOf nums1 nums1') (hs2 : IsSubseqOf nums2 nums2')
      (r s : Std.I64) (hr : max_dot_product nums1 nums2 = ok r)
      (hs : max_dot_product nums1' nums2' = ok s) :
      r.val ≤ s.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums1 nums2 nums1' nums2' : Slice Std.I64) (h1 : InRange nums1)
        (h2 : InRange nums2) (h1' : InRange nums1') (h2' : InRange nums2')
        (hs1 : IsSubseqOf nums1 nums1') (hs2 : IsSubseqOf nums2 nums2')
        (r s : Std.I64) (hr : max_dot_product nums1 nums2 = ok r)
        (hs : max_dot_product nums1' nums2' = ok s), r.val ≤ s.val) := by
    sorry

  /-- Let abs1 and abs2 be the arrays with abs1[i] = |nums1[i]| and abs2[j] = |nums2[j]|. Whenever max_dot_product(nums1, nums2) returns a result r and max_dot_product(abs1, abs2) returns a result s, r <= s.
    Preconditions: len(nums1) and len(nums2) are each between 1 and 500 inclusive; for every i with 0 <= i < len(nums1), -1000 <= nums1[i] <= 1000; for every j with 0 <= j < len(nums2), -1000 <= nums2[j] <= 1000. -/
  theorem spec_14 (nums1 nums2 abs1 abs2 : Slice Std.I64) (h1 : InRange nums1)
      (h2 : InRange nums2) (ha1 : IsAbsOf abs1 nums1) (ha2 : IsAbsOf abs2 nums2)
      (r s : Std.I64) (hr : max_dot_product nums1 nums2 = ok r)
      (hs : max_dot_product abs1 abs2 = ok s) :
      r.val ≤ s.val := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (nums1 nums2 abs1 abs2 : Slice Std.I64) (h1 : InRange nums1)
        (h2 : InRange nums2) (ha1 : IsAbsOf abs1 nums1) (ha2 : IsAbsOf abs2 nums2)
        (r s : Std.I64) (hr : max_dot_product nums1 nums2 = ok r)
        (hs : max_dot_product abs1 abs2 = ok s), r.val ≤ s.val) := by
    sorry

  end AegisSpec.MaxDotProduct
