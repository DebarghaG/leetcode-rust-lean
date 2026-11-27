import Aegis.SumCounts.Code.Funs

/-!
# Specifications of `Aegis.SumCounts.sum_counts`

LeetCode problem `subarrays-distinct-element-sum-of-squares-i`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  open Aegis.SumCounts
  open scoped BigOperators

  namespace AegisSpec.SumCounts

  def contents (nums : Slice Std.I64) : List Int := (nums : List Std.I64).map (fun x => x.val)

  def distinctCount (l : List Int) : Nat := l.dedup.length

  def window (l : List Int) (i j : Nat) : List Int := (l.drop i).take (j + 1 - i)

  def D (l : List Int) (i j : Nat) : Nat := distinctCount (window l i j)

  def sumD (l : List Int) : Nat :=
    ∑ i ∈ Finset.range l.length, ∑ j ∈ Finset.range l.length,
      if i ≤ j then D l i j ^ 2 else 0

  def revContents (nums : Slice Std.I64) : List Int := (contents nums).reverse

  def C (l : List Int) (a b : Int) : Nat :=
    ((Finset.range l.length).product (Finset.range l.length)).filter
      (fun p => p.1 ≤ p.2 ∧ a ∈ window l p.1 p.2 ∧ b ∈ window l p.1 p.2) |>.card

  def sumC (l : List Int) : Nat :=
    ∑ a ∈ l.toFinset, ∑ b ∈ l.toFinset, C l a b

  /-- Let n = len(nums). For every i,j with 0 <= i <= j < n, let D(i,j) be the number of distinct values among nums[i], nums[i+1], ..., nums[j]. Whenever sum_counts(nums) returns a result r, r = sum_{i=0}^{n-1} sum_{j=i}^{n-1} D(i,j)^2.
    Preconditions: Let n = len(nums). The preconditions are: 1 <= n <= 100; and for every i with 0 <= i < n, 1 <= nums[i] <= 100. -/
  theorem spec_1 (nums : Slice Std.I64)
      (hn_pos : 1 ≤ (contents nums).length) (hn_le : (contents nums).length ≤ 100)
      (helem : ∀ (i : Nat) (hi : i < (contents nums).length),
        1 ≤ (contents nums)[i]'hi ∧ (contents nums)[i]'hi ≤ 100)
      (r : Std.I64) (hr : sum_counts nums = ok r) :
      r.val = (sumD (contents nums) : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn_pos : 1 ≤ (contents nums).length) (hn_le : (contents nums).length ≤ 100)
        (helem : ∀ (i : Nat) (hi : i < (contents nums).length),
          1 ≤ (contents nums)[i]'hi ∧ (contents nums)[i]'hi ≤ 100)
        (r : Std.I64) (hr : sum_counts nums = ok r), r.val = (sumD (contents nums) : Int)) := by
    sorry

  /-- Under these preconditions, sum_counts(nums) returns a result r; it does not fail, panic, or overflow.
    Preconditions: Let n = len(nums). The preconditions are: 1 <= n <= 100; and for every i with 0 <= i < n, 1 <= nums[i] <= 100. -/
  theorem spec_2 (nums : Slice Std.I64)
      (hn_pos : 1 ≤ (contents nums).length) (hn_le : (contents nums).length ≤ 100)
      (helem : ∀ (i : Nat) (hi : i < (contents nums).length),
        1 ≤ (contents nums)[i]'hi ∧ (contents nums)[i]'hi ≤ 100) :
      ∃ r : Std.I64, sum_counts nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn_pos : 1 ≤ (contents nums).length) (hn_le : (contents nums).length ≤ 100)
        (helem : ∀ (i : Nat) (hi : i < (contents nums).length),
          1 ≤ (contents nums)[i]'hi ∧ (contents nums)[i]'hi ≤ 100), ∃ r : Std.I64, sum_counts nums = ok r) := by
    sorry

  /-- Whenever sum_counts(nums) returns a result r, r >= n*(n+1)/2, where n = len(nums).
    Preconditions: Let n = len(nums). The preconditions are: 1 <= n <= 100; and for every i with 0 <= i < n, 1 <= nums[i] <= 100. -/
  theorem spec_3 (nums : Slice Std.I64)
      (hn_pos : 1 ≤ (contents nums).length) (hn_le : (contents nums).length ≤ 100)
      (helem : ∀ (i : Nat) (hi : i < (contents nums).length),
        1 ≤ (contents nums)[i]'hi ∧ (contents nums)[i]'hi ≤ 100)
      (r : Std.I64) (hr : sum_counts nums = ok r) :
      r.val ≥ (((contents nums).length * ((contents nums).length + 1) / 2 : Nat) : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn_pos : 1 ≤ (contents nums).length) (hn_le : (contents nums).length ≤ 100)
        (helem : ∀ (i : Nat) (hi : i < (contents nums).length),
          1 ≤ (contents nums)[i]'hi ∧ (contents nums)[i]'hi ≤ 100)
        (r : Std.I64) (hr : sum_counts nums = ok r), r.val ≥ (((contents nums).length * ((contents nums).length + 1) / 2 : Nat) : Int)) := by
    sorry

  /-- Whenever sum_counts(nums) returns a result r, r <= n*(n+1)^2*(n+2)/12, where n = len(nums).
    Preconditions: Let n = len(nums). The preconditions are: 1 <= n <= 100; and for every i with 0 <= i < n, 1 <= nums[i] <= 100. -/
  theorem spec_4 (nums : Slice Std.I64)
      (hn_pos : 1 ≤ (contents nums).length) (hn_le : (contents nums).length ≤ 100)
      (helem : ∀ (i : Nat) (hi : i < (contents nums).length),
        1 ≤ (contents nums)[i]'hi ∧ (contents nums)[i]'hi ≤ 100)
      (r : Std.I64) (hr : sum_counts nums = ok r) :
      r.val ≤ (((contents nums).length * ((contents nums).length + 1) ^ 2 *
        ((contents nums).length + 2) / 12 : Nat) : Int) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn_pos : 1 ≤ (contents nums).length) (hn_le : (contents nums).length ≤ 100)
        (helem : ∀ (i : Nat) (hi : i < (contents nums).length),
          1 ≤ (contents nums)[i]'hi ∧ (contents nums)[i]'hi ≤ 100)
        (r : Std.I64) (hr : sum_counts nums = ok r), r.val ≤ (((contents nums).length * ((contents nums).length + 1) ^ 2 *
          ((contents nums).length + 2) / 12 : Nat) : Int)) := by
    sorry

  /-- Whenever sum_counts(nums) returns a result r, r = n*(n+1)/2 if and only if all elements of nums are equal, i.e. for every i,k with 0 <= i < n and 0 <= k < n, nums[i] = nums[k].
    Preconditions: Let n = len(nums). The preconditions are: 1 <= n <= 100; and for every i with 0 <= i < n, 1 <= nums[i] <= 100. -/
  theorem spec_5 (nums : Slice Std.I64)
      (hn_pos : 1 ≤ (contents nums).length) (hn_le : (contents nums).length ≤ 100)
      (helem : ∀ (i : Nat) (hi : i < (contents nums).length),
        1 ≤ (contents nums)[i]'hi ∧ (contents nums)[i]'hi ≤ 100)
      (r : Std.I64) (hr : sum_counts nums = ok r) :
      (r.val = (((contents nums).length * ((contents nums).length + 1) / 2 : Nat) : Int)) ↔
        ∀ (i k : Nat) (hi : i < (contents nums).length) (hk : k < (contents nums).length),
          (contents nums)[i]'hi = (contents nums)[k]'hk := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn_pos : 1 ≤ (contents nums).length) (hn_le : (contents nums).length ≤ 100)
        (helem : ∀ (i : Nat) (hi : i < (contents nums).length),
          1 ≤ (contents nums)[i]'hi ∧ (contents nums)[i]'hi ≤ 100)
        (r : Std.I64) (hr : sum_counts nums = ok r), (r.val = (((contents nums).length * ((contents nums).length + 1) / 2 : Nat) : Int)) ↔
          ∀ (i k : Nat) (hi : i < (contents nums).length) (hk : k < (contents nums).length),
            (contents nums)[i]'hi = (contents nums)[k]'hk) := by
    sorry

  /-- Whenever sum_counts(nums) returns a result r, r = n*(n+1)^2*(n+2)/12 if and only if the elements of nums are pairwise distinct, i.e. for every i,k with 0 <= i < k < n, nums[i] != nums[k].
    Preconditions: Let n = len(nums). The preconditions are: 1 <= n <= 100; and for every i with 0 <= i < n, 1 <= nums[i] <= 100. -/
  theorem spec_6 (nums : Slice Std.I64)
      (hn_pos : 1 ≤ (contents nums).length) (hn_le : (contents nums).length ≤ 100)
      (helem : ∀ (i : Nat) (hi : i < (contents nums).length),
        1 ≤ (contents nums)[i]'hi ∧ (contents nums)[i]'hi ≤ 100)
      (r : Std.I64) (hr : sum_counts nums = ok r) :
      (r.val = (((contents nums).length * ((contents nums).length + 1) ^ 2 *
        ((contents nums).length + 2) / 12 : Nat) : Int)) ↔
        ∀ (i k : Nat) (hi : i < (contents nums).length) (hk : k < (contents nums).length),
          i < k → (contents nums)[i]'hi ≠ (contents nums)[k]'hk := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn_pos : 1 ≤ (contents nums).length) (hn_le : (contents nums).length ≤ 100)
        (helem : ∀ (i : Nat) (hi : i < (contents nums).length),
          1 ≤ (contents nums)[i]'hi ∧ (contents nums)[i]'hi ≤ 100)
        (r : Std.I64) (hr : sum_counts nums = ok r), (r.val = (((contents nums).length * ((contents nums).length + 1) ^ 2 *
          ((contents nums).length + 2) / 12 : Nat) : Int)) ↔
          ∀ (i k : Nat) (hi : i < (contents nums).length) (hk : k < (contents nums).length),
            i < k → (contents nums)[i]'hi ≠ (contents nums)[k]'hk) := by
    sorry

  /-- Let n = len(nums). For every i,j with 0 <= i <= j < n, let D(i,j) be the number of distinct values among nums[i], ..., nums[j]. Whenever sum_counts(nums) returns a result r, r >= D(i,j)^2.
    Preconditions: Let n = len(nums). The preconditions are: 1 <= n <= 100; and for every i with 0 <= i < n, 1 <= nums[i] <= 100. -/
  theorem spec_7 (nums : Slice Std.I64)
      (hn_pos : 1 ≤ (contents nums).length) (hn_le : (contents nums).length ≤ 100)
      (helem : ∀ (i : Nat) (hi : i < (contents nums).length),
        1 ≤ (contents nums)[i]'hi ∧ (contents nums)[i]'hi ≤ 100)
      (r : Std.I64) (hr : sum_counts nums = ok r) :
      ∀ (i j : Nat), i ≤ j → j < (contents nums).length →
        r.val ≥ (D (contents nums) i j : Int) ^ 2 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn_pos : 1 ≤ (contents nums).length) (hn_le : (contents nums).length ≤ 100)
        (helem : ∀ (i : Nat) (hi : i < (contents nums).length),
          1 ≤ (contents nums)[i]'hi ∧ (contents nums)[i]'hi ≤ 100)
        (r : Std.I64) (hr : sum_counts nums = ok r), ∀ (i j : Nat), i ≤ j → j < (contents nums).length →
          r.val ≥ (D (contents nums) i j : Int) ^ 2) := by
    sorry

  /-- Let alt be any integer array of length n such that for all p,q with 0 <= p < n and 0 <= q < n, nums[p] = nums[q] if and only if alt[p] = alt[q]. For every i,j let D_alt(i,j) be the number of distinct values among alt[i], ..., alt[j]. Whenever sum_counts(nums) returns a result r, r = sum_{i=0}^{n-1} sum_{j=i}^{n-1} D_alt(i,j)^2.
    Preconditions: Let n = len(nums). The preconditions are: 1 <= n <= 100; and for every i with 0 <= i < n, 1 <= nums[i] <= 100. -/
  theorem spec_8 (nums alt : Slice Std.I64)
      (hn_pos : 1 ≤ (contents nums).length) (hn_le : (contents nums).length ≤ 100)
      (helem : ∀ (i : Nat) (hi : i < (contents nums).length),
        1 ≤ (contents nums)[i]'hi ∧ (contents nums)[i]'hi ≤ 100)
      (halt_len : (contents alt).length = (contents nums).length)
      (halt : ∀ (p q : Nat) (hp : p < (contents nums).length) (hq : q < (contents nums).length),
        ((contents nums)[p]'hp = (contents nums)[q]'hq) ↔
          ((contents alt)[p]'(halt_len ▸ hp) = (contents alt)[q]'(halt_len ▸ hq)))
      (r : Std.I64) (hr : sum_counts nums = ok r) :
      r.val = (sumD (contents alt) : Int) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums alt : Slice Std.I64)
        (hn_pos : 1 ≤ (contents nums).length) (hn_le : (contents nums).length ≤ 100)
        (helem : ∀ (i : Nat) (hi : i < (contents nums).length),
          1 ≤ (contents nums)[i]'hi ∧ (contents nums)[i]'hi ≤ 100)
        (halt_len : (contents alt).length = (contents nums).length)
        (halt : ∀ (p q : Nat) (hp : p < (contents nums).length) (hq : q < (contents nums).length),
          ((contents nums)[p]'hp = (contents nums)[q]'hq) ↔
            ((contents alt)[p]'(halt_len ▸ hp) = (contents alt)[q]'(halt_len ▸ hq)))
        (r : Std.I64) (hr : sum_counts nums = ok r), r.val = (sumD (contents alt) : Int)) := by
    sorry

  /-- Let n = len(nums), and let rev be the array of length n with rev[k] = nums[n-1-k] for 0 <= k < n. For every i,j let D_rev(i,j) be the number of distinct values among rev[i], ..., rev[j]. Whenever sum_counts(nums) returns a result r, r = sum_{i=0}^{n-1} sum_{j=i}^{n-1} D_rev(i,j)^2.
    Preconditions: Let n = len(nums). The preconditions are: 1 <= n <= 100; and for every i with 0 <= i < n, 1 <= nums[i] <= 100. -/
  theorem spec_9 (nums : Slice Std.I64)
      (hn_pos : 1 ≤ (contents nums).length) (hn_le : (contents nums).length ≤ 100)
      (helem : ∀ (i : Nat) (hi : i < (contents nums).length),
        1 ≤ (contents nums)[i]'hi ∧ (contents nums)[i]'hi ≤ 100)
      (r : Std.I64) (hr : sum_counts nums = ok r) :
      r.val = (sumD (revContents nums) : Int) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn_pos : 1 ≤ (contents nums).length) (hn_le : (contents nums).length ≤ 100)
        (helem : ∀ (i : Nat) (hi : i < (contents nums).length),
          1 ≤ (contents nums)[i]'hi ∧ (contents nums)[i]'hi ≤ 100)
        (r : Std.I64) (hr : sum_counts nums = ok r), r.val = (sumD (revContents nums) : Int)) := by
    sorry

  /-- Let n = len(nums) and let V = {v : there exists k with 0 <= k < n and nums[k] = v}. For each ordered pair (a,b) in V x V, let C(a,b) be the number of pairs (i,j) with 0 <= i <= j < n such that a occurs among nums[i], ..., nums[j] and b occurs among nums[i], ..., nums[j]. Whenever sum_counts(nums) returns a result r, r = sum_{a in V} sum_{b in V} C(a,b).
    Preconditions: Let n = len(nums). The preconditions are: 1 <= n <= 100; and for every i with 0 <= i < n, 1 <= nums[i] <= 100. -/
  theorem spec_10 (nums : Slice Std.I64)
      (hn_pos : 1 ≤ (contents nums).length) (hn_le : (contents nums).length ≤ 100)
      (helem : ∀ (i : Nat) (hi : i < (contents nums).length),
        1 ≤ (contents nums)[i]'hi ∧ (contents nums)[i]'hi ≤ 100)
      (r : Std.I64) (hr : sum_counts nums = ok r) :
      r.val = (sumC (contents nums) : Int) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn_pos : 1 ≤ (contents nums).length) (hn_le : (contents nums).length ≤ 100)
        (helem : ∀ (i : Nat) (hi : i < (contents nums).length),
          1 ≤ (contents nums)[i]'hi ∧ (contents nums)[i]'hi ≤ 100)
        (r : Std.I64) (hr : sum_counts nums = ok r), r.val = (sumC (contents nums) : Int)) := by
    sorry

  end AegisSpec.SumCounts
