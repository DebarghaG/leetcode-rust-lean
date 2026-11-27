import Aegis.FourSumCount.Code.Funs

/-!
# Specifications of `Aegis.FourSumCount.four_sum_count`

LeetCode problem `4sum-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.FourSumCount

  namespace AegisSpec.FourSumCount

  def IX (s : Slice I64) (i : Nat) : Int :=
    match s.val[i]? with
    | some x => x.val
    | none => 0

  def InBound (x : Int) : Prop := -268435456 ≤ x ∧ x ≤ 268435456

  def EntryBounded (s : Slice I64) : Prop :=
    ∀ i (_ : i < s.val.length), InBound (IX s i)

  def nPow4 (n : Nat) : Int := (n : Int) * (n : Int) * (n : Int) * (n : Int)

  def quadCount (nums1 nums2 nums3 nums4 : Slice I64) (n : Nat) : Nat :=
    ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n,
      ∑ l ∈ Finset.range n,
        if IX nums1 i + IX nums2 j + IX nums3 k + IX nums4 l = 0 then 1 else 0

  def HasZeroQuadruple (nums1 nums2 nums3 nums4 : Slice I64) (n : Nat) : Prop :=
    ∃ i j k l : Nat, i < n ∧ j < n ∧ k < n ∧ l < n ∧
      IX nums1 i + IX nums2 j + IX nums3 k + IX nums4 l = 0

  def AllZeroQuadruple (nums1 nums2 nums3 nums4 : Slice I64) (n : Nat) : Prop :=
    ∀ i j k l : Nat, i < n → j < n → k < n → l < n →
      IX nums1 i + IX nums2 j + IX nums3 k + IX nums4 l = 0

  def Precond (nums1 nums2 nums3 nums4 : Slice I64) : Prop :=
    nums2.val.length = nums1.val.length ∧
    nums3.val.length = nums1.val.length ∧
    nums4.val.length = nums1.val.length ∧
    1 ≤ nums1.val.length ∧ nums1.val.length ≤ 200 ∧
    EntryBounded nums1 ∧ EntryBounded nums2 ∧
    EntryBounded nums3 ∧ EntryBounded nums4

  def IsShift (d : Int) (s t : Slice I64) : Prop :=
    t.val.length = s.val.length ∧ ∀ i (_ : i < s.val.length), IX t i = IX s i + d

  def IsScaled (c : Int) (s t : Slice I64) : Prop :=
    t.val.length = s.val.length ∧ ∀ i (_ : i < s.val.length), IX t i = c * IX s i

  def IsPermuted (n : Nat) (s t : Slice I64) (π : Equiv.Perm (Fin n)) : Prop :=
    s.val.length = n ∧ t.val.length = n ∧
      ∀ i (h : i < n), IX t i = IX s (π ⟨i, h⟩)

  def at4 (s1 s2 s3 s4 : Slice I64) (k : Fin 4) : Slice I64 :=
    match k.val with
    | 0 => s1
    | 1 => s2
    | 2 => s3
    | _ => s4

  def call4 (s1 s2 s3 s4 : Slice I64) (k : Fin 4) (s : Slice I64) : Result I64 :=
    match k.val with
    | 0 => four_sum_count s s2 s3 s4
    | 1 => four_sum_count s1 s s3 s4
    | 2 => four_sum_count s1 s2 s s4
    | _ => four_sum_count s1 s2 s3 s

  /-- The function returns Result.ok r, and the integer value represented by r is exactly the number of ordered quadruples (i,j,k,l) such that 0 <= i < n, 0 <= j < n, 0 <= k < n, 0 <= l < n, and nums1[i] + nums2[j] + nums3[k] + nums4[l] = 0.
    Preconditions: Let n = len(nums1). Assume len(nums1) = len(nums2) = len(nums3) = len(nums4) = n, 1 <= n <= 200, and for every i with 0 <= i < n and every X in {nums1,nums2,nums3,nums4}, -268435456 <= X[i] <= 268435456. -/
  theorem spec_1 (nums1 nums2 nums3 nums4 : Slice I64)
      (hpre : Precond nums1 nums2 nums3 nums4) :
      ∃ r : I64, four_sum_count nums1 nums2 nums3 nums4 = ok r ∧
        r.val = (quadCount nums1 nums2 nums3 nums4 nums1.val.length : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums1 nums2 nums3 nums4 : Slice I64)
        (hpre : Precond nums1 nums2 nums3 nums4), ∃ r : I64, four_sum_count nums1 nums2 nums3 nums4 = ok r ∧
          r.val = (quadCount nums1 nums2 nums3 nums4 nums1.val.length : Int)) := by
    sorry

  /-- The function returns Result.ok r for some r for every input satisfying the preconditions; in particular, it never returns an error, panics, or fails because of integer overflow.
    Preconditions: Let n = len(nums1). Assume len(nums1) = len(nums2) = len(nums3) = len(nums4) = n, 1 <= n <= 200, and for every i with 0 <= i < n and every X in {nums1,nums2,nums3,nums4}, -268435456 <= X[i] <= 268435456. -/
  theorem spec_2 (nums1 nums2 nums3 nums4 : Slice I64)
      (hpre : Precond nums1 nums2 nums3 nums4) :
      ∃ r : I64, four_sum_count nums1 nums2 nums3 nums4 = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums1 nums2 nums3 nums4 : Slice I64)
        (hpre : Precond nums1 nums2 nums3 nums4), ∃ r : I64, four_sum_count nums1 nums2 nums3 nums4 = ok r) := by
    sorry

  /-- Whenever the function returns Result.ok r, the integer value represented by r is at least 0.
    Preconditions: Let n = len(nums1). Assume len(nums1) = len(nums2) = len(nums3) = len(nums4) = n, 1 <= n <= 200, and for every i with 0 <= i < n and every X in {nums1,nums2,nums3,nums4}, -268435456 <= X[i] <= 268435456. -/
  theorem spec_3 (nums1 nums2 nums3 nums4 : Slice I64)
      (hpre : Precond nums1 nums2 nums3 nums4) (r : I64)
      (hr : four_sum_count nums1 nums2 nums3 nums4 = ok r) :
      0 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums1 nums2 nums3 nums4 : Slice I64)
        (hpre : Precond nums1 nums2 nums3 nums4) (r : I64)
        (hr : four_sum_count nums1 nums2 nums3 nums4 = ok r), 0 ≤ r.val) := by
    sorry

  /-- Whenever the function returns Result.ok r, the integer value represented by r is at most n * n * n * n.
    Preconditions: Let n = len(nums1). Assume len(nums1) = len(nums2) = len(nums3) = len(nums4) = n, 1 <= n <= 200, and for every i with 0 <= i < n and every X in {nums1,nums2,nums3,nums4}, -268435456 <= X[i] <= 268435456. -/
  theorem spec_4 (nums1 nums2 nums3 nums4 : Slice I64)
      (hpre : Precond nums1 nums2 nums3 nums4) (r : I64)
      (hr : four_sum_count nums1 nums2 nums3 nums4 = ok r) :
      r.val ≤ nPow4 nums1.val.length := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums1 nums2 nums3 nums4 : Slice I64)
        (hpre : Precond nums1 nums2 nums3 nums4) (r : I64)
        (hr : four_sum_count nums1 nums2 nums3 nums4 = ok r), r.val ≤ nPow4 nums1.val.length) := by
    sorry

  /-- The function returns Result.ok r, and the integer value represented by r is greater than 0 if and only if there exists an ordered quadruple (i,j,k,l) with 0 <= i,j,k,l < n and nums1[i] + nums2[j] + nums3[k] + nums4[l] = 0.
    Preconditions: Let n = len(nums1). Assume len(nums1) = len(nums2) = len(nums3) = len(nums4) = n, 1 <= n <= 200, and for every i with 0 <= i < n and every X in {nums1,nums2,nums3,nums4}, -268435456 <= X[i] <= 268435456. -/
  theorem spec_5 (nums1 nums2 nums3 nums4 : Slice I64)
      (hpre : Precond nums1 nums2 nums3 nums4) :
      ∃ r : I64, four_sum_count nums1 nums2 nums3 nums4 = ok r ∧
        (0 < r.val ↔ HasZeroQuadruple nums1 nums2 nums3 nums4 nums1.val.length) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums1 nums2 nums3 nums4 : Slice I64)
        (hpre : Precond nums1 nums2 nums3 nums4), ∃ r : I64, four_sum_count nums1 nums2 nums3 nums4 = ok r ∧
          (0 < r.val ↔ HasZeroQuadruple nums1 nums2 nums3 nums4 nums1.val.length)) := by
    sorry

  /-- The function returns Result.ok r, and the integer value represented by r equals n * n * n * n if and only if every ordered quadruple (i,j,k,l) with 0 <= i,j,k,l < n satisfies nums1[i] + nums2[j] + nums3[k] + nums4[l] = 0.
    Preconditions: Let n = len(nums1). Assume len(nums1) = len(nums2) = len(nums3) = len(nums4) = n, 1 <= n <= 200, and for every i with 0 <= i < n and every X in {nums1,nums2,nums3,nums4}, -268435456 <= X[i] <= 268435456. -/
  theorem spec_6 (nums1 nums2 nums3 nums4 : Slice I64)
      (hpre : Precond nums1 nums2 nums3 nums4) :
      ∃ r : I64, four_sum_count nums1 nums2 nums3 nums4 = ok r ∧
        (r.val = nPow4 nums1.val.length ↔
          AllZeroQuadruple nums1 nums2 nums3 nums4 nums1.val.length) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums1 nums2 nums3 nums4 : Slice I64)
        (hpre : Precond nums1 nums2 nums3 nums4), ∃ r : I64, four_sum_count nums1 nums2 nums3 nums4 = ok r ∧
          (r.val = nPow4 nums1.val.length ↔
            AllZeroQuadruple nums1 nums2 nums3 nums4 nums1.val.length)) := by
    sorry

  /-- For every permutation sigma of the set {1,2,3,4}, if the four arrays are passed in the order (nums_{sigma(1)}, nums_{sigma(2)}, nums_{sigma(3)}, nums_{sigma(4)}), then whenever the function returns Result.ok r_sigma for that order and Result.ok r for the original order (nums1,nums2,nums3,nums4), the integer value represented by r_sigma equals the integer value represented by r.
    Preconditions: Let n = len(nums1). Assume len(nums1) = len(nums2) = len(nums3) = len(nums4) = n, 1 <= n <= 200, and for every i with 0 <= i < n and every X in {nums1,nums2,nums3,nums4}, -268435456 <= X[i] <= 268435456. -/
  theorem spec_7 (nums1 nums2 nums3 nums4 : Slice I64)
      (hpre : Precond nums1 nums2 nums3 nums4) (σ : Equiv.Perm (Fin 4))
      (r rσ : I64)
      (hr : four_sum_count nums1 nums2 nums3 nums4 = ok r)
      (hrσ : four_sum_count (at4 nums1 nums2 nums3 nums4 (σ (0 : Fin 4)))
          (at4 nums1 nums2 nums3 nums4 (σ (1 : Fin 4)))
          (at4 nums1 nums2 nums3 nums4 (σ (2 : Fin 4)))
          (at4 nums1 nums2 nums3 nums4 (σ (3 : Fin 4))) = ok rσ) :
      rσ.val = r.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums1 nums2 nums3 nums4 : Slice I64)
        (hpre : Precond nums1 nums2 nums3 nums4) (σ : Equiv.Perm (Fin 4))
        (r rσ : I64)
        (hr : four_sum_count nums1 nums2 nums3 nums4 = ok r)
        (hrσ : four_sum_count (at4 nums1 nums2 nums3 nums4 (σ (0 : Fin 4)))
            (at4 nums1 nums2 nums3 nums4 (σ (1 : Fin 4)))
            (at4 nums1 nums2 nums3 nums4 (σ (2 : Fin 4)))
            (at4 nums1 nums2 nums3 nums4 (σ (3 : Fin 4))) = ok rσ), rσ.val = r.val) := by
    sorry

  /-- For each k in {1,2,3,4} and each permutation pi of {0,...,n-1}, let nums_k' be the slice defined by nums_k'[i] = nums_k[pi(i)] for 0 <= i < n. Then whenever the function returns Result.ok r' for the four arrays with nums_k replaced by nums_k' and Result.ok r for the original four arrays, the integer value represented by r' equals the integer value represented by r.
    Preconditions: Let n = len(nums1). Assume len(nums1) = len(nums2) = len(nums3) = len(nums4) = n, 1 <= n <= 200, and for every i with 0 <= i < n and every X in {nums1,nums2,nums3,nums4}, -268435456 <= X[i] <= 268435456. -/
  theorem spec_8 (nums1 nums2 nums3 nums4 : Slice I64)
      (hpre : Precond nums1 nums2 nums3 nums4) (k : Fin 4)
      (π : Equiv.Perm (Fin nums1.val.length)) (s' : Slice I64)
      (hs' : IsPermuted nums1.val.length (at4 nums1 nums2 nums3 nums4 k) s' π)
      (r r' : I64)
      (hr : four_sum_count nums1 nums2 nums3 nums4 = ok r)
      (hr' : call4 nums1 nums2 nums3 nums4 k s' = ok r') :
      r'.val = r.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums1 nums2 nums3 nums4 : Slice I64)
        (hpre : Precond nums1 nums2 nums3 nums4) (k : Fin 4)
        (π : Equiv.Perm (Fin nums1.val.length)) (s' : Slice I64)
        (hs' : IsPermuted nums1.val.length (at4 nums1 nums2 nums3 nums4 k) s' π)
        (r r' : I64)
        (hr : four_sum_count nums1 nums2 nums3 nums4 = ok r)
        (hr' : call4 nums1 nums2 nums3 nums4 k s' = ok r'), r'.val = r.val) := by
    sorry

  /-- For every nonzero integer c such that the four slices c*nums1, c*nums2, c*nums3, c*nums4, with entrywise multiplication, also satisfy the element bound -268435456 <= value <= 268435456, whenever the function returns Result.ok r_c for these scaled slices and Result.ok r for the original slices, the integer value represented by r_c equals the integer value represented by r.
    Preconditions: Let n = len(nums1). Assume len(nums1) = len(nums2) = len(nums3) = len(nums4) = n, 1 <= n <= 200, and for every i with 0 <= i < n and every X in {nums1,nums2,nums3,nums4}, -268435456 <= X[i] <= 268435456. -/
  theorem spec_9 (nums1 nums2 nums3 nums4 : Slice I64)
      (hpre : Precond nums1 nums2 nums3 nums4) (c : Int) (hc : c ≠ 0)
      (s1 s2 s3 s4 : Slice I64)
      (hs1 : IsScaled c nums1 s1) (hs2 : IsScaled c nums2 s2)
      (hs3 : IsScaled c nums3 s3) (hs4 : IsScaled c nums4 s4)
      (hb1 : EntryBounded s1) (hb2 : EntryBounded s2)
      (hb3 : EntryBounded s3) (hb4 : EntryBounded s4)
      (r rc : I64)
      (hr : four_sum_count nums1 nums2 nums3 nums4 = ok r)
      (hrc : four_sum_count s1 s2 s3 s4 = ok rc) :
      rc.val = r.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums1 nums2 nums3 nums4 : Slice I64)
        (hpre : Precond nums1 nums2 nums3 nums4) (c : Int) (hc : c ≠ 0)
        (s1 s2 s3 s4 : Slice I64)
        (hs1 : IsScaled c nums1 s1) (hs2 : IsScaled c nums2 s2)
        (hs3 : IsScaled c nums3 s3) (hs4 : IsScaled c nums4 s4)
        (hb1 : EntryBounded s1) (hb2 : EntryBounded s2)
        (hb3 : EntryBounded s3) (hb4 : EntryBounded s4)
        (r rc : I64)
        (hr : four_sum_count nums1 nums2 nums3 nums4 = ok r)
        (hrc : four_sum_count s1 s2 s3 s4 = ok rc), rc.val = r.val) := by
    sorry

  /-- For every integer c such that -268435456 <= nums1[i] + c <= 268435456 and -268435456 <= nums2[i] - c <= 268435456 for all i with 0 <= i < n, define nums1'[i] = nums1[i] + c and nums2'[i] = nums2[i] - c. Then whenever the function returns Result.ok r' for (nums1',nums2',nums3,nums4) and Result.ok r for (nums1,nums2,nums3,nums4), the integer value represented by r' equals the integer value represented by r.
    Preconditions: Let n = len(nums1). Assume len(nums1) = len(nums2) = len(nums3) = len(nums4) = n, 1 <= n <= 200, and for every i with 0 <= i < n and every X in {nums1,nums2,nums3,nums4}, -268435456 <= X[i] <= 268435456. -/
  theorem spec_10 (nums1 nums2 nums3 nums4 : Slice I64)
      (hpre : Precond nums1 nums2 nums3 nums4) (c : Int)
      (hb1 : ∀ i (hi : i < nums1.val.length), InBound (IX nums1 i + c))
      (hb2 : ∀ i (hi : i < nums2.val.length), InBound (IX nums2 i - c))
      (s1 s2 : Slice I64)
      (hs1 : IsShift c nums1 s1) (hs2 : IsShift (-c) nums2 s2)
      (r r' : I64)
      (hr : four_sum_count nums1 nums2 nums3 nums4 = ok r)
      (hr' : four_sum_count s1 s2 nums3 nums4 = ok r') :
      r'.val = r.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums1 nums2 nums3 nums4 : Slice I64)
        (hpre : Precond nums1 nums2 nums3 nums4) (c : Int)
        (hb1 : ∀ i (hi : i < nums1.val.length), InBound (IX nums1 i + c))
        (hb2 : ∀ i (hi : i < nums2.val.length), InBound (IX nums2 i - c))
        (s1 s2 : Slice I64)
        (hs1 : IsShift c nums1 s1) (hs2 : IsShift (-c) nums2 s2)
        (r r' : I64)
        (hr : four_sum_count nums1 nums2 nums3 nums4 = ok r)
        (hr' : four_sum_count s1 s2 nums3 nums4 = ok r'), r'.val = r.val) := by
    sorry

  /-- Whenever the function returns Result.ok r' for the four arrays obtained by adding d1 to every entry of nums1, d2 to every entry of nums2, d3 to every entry of nums3, and d4 to every entry of nums4, and returns Result.ok r for the original four arrays, the integer value represented by r' equals the integer value represented by r. This generalizes S11 to arbitrary zero-sum shifts of the four arrays.
    Preconditions: Let n = len(nums1). Assume len(nums1) = len(nums2) = len(nums3) = len(nums4) = n, 1 <= n <= 200, and for every i with 0 <= i < n and every X in {nums1,nums2,nums3,nums4}, -268435456 <= X[i] <= 268435456. Let d1,d2,d3,d4 be integers with d1 + d2 + d3 + d4 = 0 such that for every i with 0 <= i < n, each of nums1[i]+d1, nums2[i]+d2, nums3[i]+d3, nums4[i]+d4 lies in [-268435456, 268435456]. -/
  theorem spec_11 (nums1 nums2 nums3 nums4 : Slice I64)
      (hpre : Precond nums1 nums2 nums3 nums4)
      (d1 d2 d3 d4 : Int) (hd : d1 + d2 + d3 + d4 = 0)
      (hb1 : ∀ i (hi : i < nums1.val.length), InBound (IX nums1 i + d1))
      (hb2 : ∀ i (hi : i < nums2.val.length), InBound (IX nums2 i + d2))
      (hb3 : ∀ i (hi : i < nums3.val.length), InBound (IX nums3 i + d3))
      (hb4 : ∀ i (hi : i < nums4.val.length), InBound (IX nums4 i + d4))
      (s1 s2 s3 s4 : Slice I64)
      (hs1 : IsShift d1 nums1 s1) (hs2 : IsShift d2 nums2 s2)
      (hs3 : IsShift d3 nums3 s3) (hs4 : IsShift d4 nums4 s4)
      (r r' : I64)
      (hr : four_sum_count nums1 nums2 nums3 nums4 = ok r)
      (hr' : four_sum_count s1 s2 s3 s4 = ok r') :
      r'.val = r.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums1 nums2 nums3 nums4 : Slice I64)
        (hpre : Precond nums1 nums2 nums3 nums4)
        (d1 d2 d3 d4 : Int) (hd : d1 + d2 + d3 + d4 = 0)
        (hb1 : ∀ i (hi : i < nums1.val.length), InBound (IX nums1 i + d1))
        (hb2 : ∀ i (hi : i < nums2.val.length), InBound (IX nums2 i + d2))
        (hb3 : ∀ i (hi : i < nums3.val.length), InBound (IX nums3 i + d3))
        (hb4 : ∀ i (hi : i < nums4.val.length), InBound (IX nums4 i + d4))
        (s1 s2 s3 s4 : Slice I64)
        (hs1 : IsShift d1 nums1 s1) (hs2 : IsShift d2 nums2 s2)
        (hs3 : IsShift d3 nums3 s3) (hs4 : IsShift d4 nums4 s4)
        (r r' : I64)
        (hr : four_sum_count nums1 nums2 nums3 nums4 = ok r)
        (hr' : four_sum_count s1 s2 s3 s4 = ok r'), r'.val = r.val) := by
    sorry

  end AegisSpec.FourSumCount
