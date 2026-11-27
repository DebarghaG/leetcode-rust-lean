import Aegis.MinCost.Code.Funs

/-!
# Specifications of `Aegis.MinCost.min_cost`

LeetCode problem `minimum-cost-to-split-an-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.MinCost (min_cost)

  namespace AegisSpec.MinCost

  def toList (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

  def entry (nums : Slice Std.I64) (i : Nat) : Int := (toList nums).getD i 0

  abbrev OccursTwice (l : List Int) (v : Int) : Prop := 2 ≤ l.countP (fun x => decide (x = v))

  def TLOf (l : List Int) : Nat :=
    (l.filter (fun v => decide (OccursTwice l v))).length

  def seg (l : List Int) (a b : Nat) : List Int := (l.drop a).take (b - a)

  def TL (l : List Int) (a b : Nat) : Nat := TLOf (seg l a b)

  abbrev StrictIncr (p : List Nat) : Prop := ∀ i, i + 1 < p.length → p[i]! < p[i+1]!

  abbrev IsSplit (n : Nat) (p : List Nat) : Prop :=
    2 ≤ p.length ∧ p.head? = some 0 ∧ p.getLast? = some n ∧ StrictIncr p

  def splitCostFrom (l : List Int) (k : Int) : List Nat → Int
    | a :: b :: rest => (k + (TL l a b : Int)) + splitCostFrom l k (b :: rest)
    | _ => 0

  def splitCost (l : List Int) (k : Int) (p : List Nat) : Int := splitCostFrom l k p

  abbrev IsMinCost (l : List Int) (k r : Int) : Prop :=
    (∀ p, IsSplit l.length p → r ≤ splitCost l k p) ∧
      ∃ p, IsSplit l.length p ∧ splitCost l k p = r

  /-- Let n = len(nums). For any integers l,r with 0 <= l < r <= n, define TL(l,r) to be the number of indices i with l <= i < r such that the value nums[i] occurs at least twice among nums[l], nums[l+1], ..., nums[r-1]. A split of nums is a choice of cut positions 0 = p0 < p1 < ... < pm = n for some m >= 1; its j-th part is the subarray nums[p_{j-1}], ..., nums[p_j - 1], and its cost is the sum over j = 1..m of (k + TL(p_{j-1}, p_j)). The function returns a result r, and r is the minimum cost among all splits of nums.
    Preconditions: len(nums) >= 1; len(nums) <= 1000; for every i with 0 <= i < len(nums), 0 <= nums[i] < len(nums); and 1 <= k <= 10^9. -/
  theorem spec_1 (nums : Slice Std.I64) (k : Std.I64)
      (h_len_ge : 1 ≤ nums.length) (h_len_le : nums.length ≤ 1000)
      (h_vals : ∀ i, i < nums.length → 0 ≤ entry nums i ∧ entry nums i < (nums.length : Int))
      (h_k_ge : 1 ≤ k.val) (h_k_le : k.val ≤ (10 ^ 9 : Int)) :
      ∃ r, min_cost nums k = ok r ∧ IsMinCost (toList nums) k.val r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (h_len_ge : 1 ≤ nums.length) (h_len_le : nums.length ≤ 1000)
        (h_vals : ∀ i, i < nums.length → 0 ≤ entry nums i ∧ entry nums i < (nums.length : Int))
        (h_k_ge : 1 ≤ k.val) (h_k_le : k.val ≤ (10 ^ 9 : Int)), ∃ r, min_cost nums k = ok r ∧ IsMinCost (toList nums) k.val r.val) := by
    sorry

  /-- For every nums and k satisfying the preconditions, the function returns a result r and does not fail.
    Preconditions: len(nums) >= 1; len(nums) <= 1000; for every i with 0 <= i < len(nums), 0 <= nums[i] < len(nums); and 1 <= k <= 10^9. -/
  theorem spec_2 (nums : Slice Std.I64) (k : Std.I64)
      (h_len_ge : 1 ≤ nums.length) (h_len_le : nums.length ≤ 1000)
      (h_vals : ∀ i, i < nums.length → 0 ≤ entry nums i ∧ entry nums i < (nums.length : Int))
      (h_k_ge : 1 ≤ k.val) (h_k_le : k.val ≤ (10 ^ 9 : Int)) :
      ∃ r, min_cost nums k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (h_len_ge : 1 ≤ nums.length) (h_len_le : nums.length ≤ 1000)
        (h_vals : ∀ i, i < nums.length → 0 ≤ entry nums i ∧ entry nums i < (nums.length : Int))
        (h_k_ge : 1 ≤ k.val) (h_k_le : k.val ≤ (10 ^ 9 : Int)), ∃ r, min_cost nums k = ok r) := by
    sorry

  /-- Let r be the returned result. For every split of nums into contiguous non-empty subarrays covering nums in order, let C be the sum over its parts P of (k + TL(P)), where TL(P) is the number of positions in P whose value occurs at least twice in P. Then r <= C.
    Preconditions: len(nums) >= 1; len(nums) <= 1000; for every i with 0 <= i < len(nums), 0 <= nums[i] < len(nums); and 1 <= k <= 10^9. -/
  theorem spec_3 (nums : Slice Std.I64) (k : Std.I64)
      (h_len_ge : 1 ≤ nums.length) (h_len_le : nums.length ≤ 1000)
      (h_vals : ∀ i, i < nums.length → 0 ≤ entry nums i ∧ entry nums i < (nums.length : Int))
      (h_k_ge : 1 ≤ k.val) (h_k_le : k.val ≤ (10 ^ 9 : Int)) :
      ∀ r, min_cost nums k = ok r →
        ∀ p, IsSplit (toList nums).length p →
          r.val ≤ splitCost (toList nums) k.val p := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (h_len_ge : 1 ≤ nums.length) (h_len_le : nums.length ≤ 1000)
        (h_vals : ∀ i, i < nums.length → 0 ≤ entry nums i ∧ entry nums i < (nums.length : Int))
        (h_k_ge : 1 ≤ k.val) (h_k_le : k.val ≤ (10 ^ 9 : Int)), ∀ r, min_cost nums k = ok r →
          ∀ p, IsSplit (toList nums).length p →
            r.val ≤ splitCost (toList nums) k.val p) := by
    sorry

  /-- Let r be the returned result. There exists a split of nums into contiguous non-empty subarrays covering nums in order such that its cost, defined as the sum over its parts P of (k + TL(P)) with TL(P) the number of positions in P whose value occurs at least twice in P, is exactly r.
    Preconditions: len(nums) >= 1; len(nums) <= 1000; for every i with 0 <= i < len(nums), 0 <= nums[i] < len(nums); and 1 <= k <= 10^9. -/
  theorem spec_4 (nums : Slice Std.I64) (k : Std.I64)
      (h_len_ge : 1 ≤ nums.length) (h_len_le : nums.length ≤ 1000)
      (h_vals : ∀ i, i < nums.length → 0 ≤ entry nums i ∧ entry nums i < (nums.length : Int))
      (h_k_ge : 1 ≤ k.val) (h_k_le : k.val ≤ (10 ^ 9 : Int)) :
      ∀ r, min_cost nums k = ok r →
        ∃ p, IsSplit (toList nums).length p ∧ splitCost (toList nums) k.val p = r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (h_len_ge : 1 ≤ nums.length) (h_len_le : nums.length ≤ 1000)
        (h_vals : ∀ i, i < nums.length → 0 ≤ entry nums i ∧ entry nums i < (nums.length : Int))
        (h_k_ge : 1 ≤ k.val) (h_k_le : k.val ≤ (10 ^ 9 : Int)), ∀ r, min_cost nums k = ok r →
          ∃ p, IsSplit (toList nums).length p ∧ splitCost (toList nums) k.val p = r.val) := by
    sorry

  /-- Let r be the returned result. Then r >= k.
    Preconditions: len(nums) >= 1; len(nums) <= 1000; for every i with 0 <= i < len(nums), 0 <= nums[i] < len(nums); and 1 <= k <= 10^9. -/
  theorem spec_5 (nums : Slice Std.I64) (k : Std.I64)
      (h_len_ge : 1 ≤ nums.length) (h_len_le : nums.length ≤ 1000)
      (h_vals : ∀ i, i < nums.length → 0 ≤ entry nums i ∧ entry nums i < (nums.length : Int))
      (h_k_ge : 1 ≤ k.val) (h_k_le : k.val ≤ (10 ^ 9 : Int)) :
      ∀ r, min_cost nums k = ok r → k.val ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (h_len_ge : 1 ≤ nums.length) (h_len_le : nums.length ≤ 1000)
        (h_vals : ∀ i, i < nums.length → 0 ≤ entry nums i ∧ entry nums i < (nums.length : Int))
        (h_k_ge : 1 ≤ k.val) (h_k_le : k.val ≤ (10 ^ 9 : Int)), ∀ r, min_cost nums k = ok r → k.val ≤ r.val) := by
    sorry

  /-- Under this additional precondition, the returned result r satisfies r = k.
    Preconditions: len(nums) >= 1; len(nums) <= 1000; for every i with 0 <= i < len(nums), 0 <= nums[i] < len(nums); 1 <= k <= 10^9; and for every i,j with 0 <= i < j < len(nums), nums[i] != nums[j]. -/
  theorem spec_6 (nums : Slice Std.I64) (k : Std.I64)
      (h_len_ge : 1 ≤ nums.length) (h_len_le : nums.length ≤ 1000)
      (h_vals : ∀ i, i < nums.length → 0 ≤ entry nums i ∧ entry nums i < (nums.length : Int))
      (h_k_ge : 1 ≤ k.val) (h_k_le : k.val ≤ (10 ^ 9 : Int))
      (h_distinct : ∀ i j, i < j → j < nums.length → entry nums i ≠ entry nums j) :
      ∀ r, min_cost nums k = ok r → r.val = k.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (h_len_ge : 1 ≤ nums.length) (h_len_le : nums.length ≤ 1000)
        (h_vals : ∀ i, i < nums.length → 0 ≤ entry nums i ∧ entry nums i < (nums.length : Int))
        (h_k_ge : 1 ≤ k.val) (h_k_le : k.val ≤ (10 ^ 9 : Int))
        (h_distinct : ∀ i j, i < j → j < nums.length → entry nums i ≠ entry nums j), ∀ r, min_cost nums k = ok r → r.val = k.val) := by
    sorry

  /-- Under this additional precondition, the returned result r satisfies r = len(nums) when k = 1, and r = len(nums) + k when k >= 2.
    Preconditions: len(nums) >= 1; len(nums) <= 1000; for every i with 0 <= i < len(nums), 0 <= nums[i] < len(nums); 1 <= k <= 10^9; len(nums) >= 2; and nums[0] = nums[1] = ... = nums[len(nums)-1]. -/
  theorem spec_7 (nums : Slice Std.I64) (k : Std.I64)
      (h_len_ge : 1 ≤ nums.length) (h_len_le : nums.length ≤ 1000)
      (h_vals : ∀ i, i < nums.length → 0 ≤ entry nums i ∧ entry nums i < (nums.length : Int))
      (h_k_ge : 1 ≤ k.val) (h_k_le : k.val ≤ (10 ^ 9 : Int))
      (h_len_ge2 : 2 ≤ nums.length)
      (h_const : ∀ i, i < nums.length → entry nums i = entry nums 0) :
      ∀ r, min_cost nums k = ok r →
        (k.val = 1 → r.val = (nums.length : Int)) ∧
          (2 ≤ k.val → r.val = (nums.length : Int) + k.val) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (h_len_ge : 1 ≤ nums.length) (h_len_le : nums.length ≤ 1000)
        (h_vals : ∀ i, i < nums.length → 0 ≤ entry nums i ∧ entry nums i < (nums.length : Int))
        (h_k_ge : 1 ≤ k.val) (h_k_le : k.val ≤ (10 ^ 9 : Int))
        (h_len_ge2 : 2 ≤ nums.length)
        (h_const : ∀ i, i < nums.length → entry nums i = entry nums 0), ∀ r, min_cost nums k = ok r →
          (k.val = 1 → r.val = (nums.length : Int)) ∧
            (2 ≤ k.val → r.val = (nums.length : Int) + k.val)) := by
    sorry

  /-- Under this additional precondition, the returned result r satisfies r = min(2*k, k + (2 if nums[0] = nums[1] else 0)), where min is the smaller of the two integers.
    Preconditions: len(nums) >= 1; len(nums) <= 1000; for every i with 0 <= i < len(nums), 0 <= nums[i] < len(nums); 1 <= k <= 10^9; and len(nums) = 2. -/
  theorem spec_8 (nums : Slice Std.I64) (k : Std.I64)
      (h_len_ge : 1 ≤ nums.length) (h_len_le : nums.length ≤ 1000)
      (h_vals : ∀ i, i < nums.length → 0 ≤ entry nums i ∧ entry nums i < (nums.length : Int))
      (h_k_ge : 1 ≤ k.val) (h_k_le : k.val ≤ (10 ^ 9 : Int))
      (h_len_eq2 : nums.length = 2) :
      ∀ r, min_cost nums k = ok r →
        r.val = min (2 * k.val) (k.val + (if entry nums 0 = entry nums 1 then 2 else 0)) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (h_len_ge : 1 ≤ nums.length) (h_len_le : nums.length ≤ 1000)
        (h_vals : ∀ i, i < nums.length → 0 ≤ entry nums i ∧ entry nums i < (nums.length : Int))
        (h_k_ge : 1 ≤ k.val) (h_k_le : k.val ≤ (10 ^ 9 : Int))
        (h_len_eq2 : nums.length = 2), ∀ r, min_cost nums k = ok r →
          r.val = min (2 * k.val) (k.val + (if entry nums 0 = entry nums 1 then 2 else 0))) := by
    sorry

  /-- Under this additional precondition, the returned result r satisfies r = k + T, where T is the number of indices i with 0 <= i < len(nums) such that nums[i] occurs at least twice in the whole array nums.
    Preconditions: len(nums) >= 1; len(nums) <= 1000; for every i with 0 <= i < len(nums), 0 <= nums[i] < len(nums); 1 <= k <= 10^9; and k >= len(nums). -/
  theorem spec_9 (nums : Slice Std.I64) (k : Std.I64)
      (h_len_ge : 1 ≤ nums.length) (h_len_le : nums.length ≤ 1000)
      (h_vals : ∀ i, i < nums.length → 0 ≤ entry nums i ∧ entry nums i < (nums.length : Int))
      (h_k_ge : 1 ≤ k.val) (h_k_le : k.val ≤ (10 ^ 9 : Int))
      (h_k_len : (nums.length : Int) ≤ k.val) :
      ∀ r, min_cost nums k = ok r → r.val = k.val + (TLOf (toList nums) : Int) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (h_len_ge : 1 ≤ nums.length) (h_len_le : nums.length ≤ 1000)
        (h_vals : ∀ i, i < nums.length → 0 ≤ entry nums i ∧ entry nums i < (nums.length : Int))
        (h_k_ge : 1 ≤ k.val) (h_k_le : k.val ≤ (10 ^ 9 : Int))
        (h_k_len : (nums.length : Int) ≤ k.val), ∀ r, min_cost nums k = ok r → r.val = k.val + (TLOf (toList nums) : Int)) := by
    sorry

  /-- Let n = len(nums). Define rev to be the array of length n with rev[i] = nums[n-1-i] for every 0 <= i < n. Whenever the function returns a result r for nums and k, and a result r_rev for rev and k, we have r = r_rev.
    Preconditions: len(nums) >= 1; len(nums) <= 1000; for every i with 0 <= i < len(nums), 0 <= nums[i] < len(nums); and 1 <= k <= 10^9. -/
  theorem spec_10 (nums : Slice Std.I64) (k : Std.I64)
      (h_len_ge : 1 ≤ nums.length) (h_len_le : nums.length ≤ 1000)
      (h_vals : ∀ i, i < nums.length → 0 ≤ entry nums i ∧ entry nums i < (nums.length : Int))
      (h_k_ge : 1 ≤ k.val) (h_k_le : k.val ≤ (10 ^ 9 : Int))
      (rev : Slice Std.I64)
      (h_rev_len : rev.length = nums.length)
      (h_rev : ∀ i, i < rev.length → entry rev i = entry nums (nums.length - 1 - i)) :
      ∀ r r_rev, min_cost nums k = ok r → min_cost rev k = ok r_rev → r.val = r_rev.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (h_len_ge : 1 ≤ nums.length) (h_len_le : nums.length ≤ 1000)
        (h_vals : ∀ i, i < nums.length → 0 ≤ entry nums i ∧ entry nums i < (nums.length : Int))
        (h_k_ge : 1 ≤ k.val) (h_k_le : k.val ≤ (10 ^ 9 : Int))
        (rev : Slice Std.I64)
        (h_rev_len : rev.length = nums.length)
        (h_rev : ∀ i, i < rev.length → entry rev i = entry nums (nums.length - 1 - i)), ∀ r r_rev, min_cost nums k = ok r → min_cost rev k = ok r_rev → r.val = r_rev.val) := by
    sorry

  /-- Under this additional precondition, whenever the function returns a result r for nums and k, and a result r2 for nums2 and k, we have r = r2.
    Preconditions: len(nums) >= 1; len(nums) <= 1000; for every i with 0 <= i < len(nums), 0 <= nums[i] < len(nums); 1 <= k <= 10^9; let nums2 be any array of 64-bit integers with len(nums2) = len(nums), 0 <= nums2[i] < len(nums2) for all i, and for all i,j with 0 <= i,j < len(nums), nums[i] = nums[j] iff nums2[i] = nums2[j]. -/
  theorem spec_11 (nums : Slice Std.I64) (k : Std.I64)
      (h_len_ge : 1 ≤ nums.length) (h_len_le : nums.length ≤ 1000)
      (h_vals : ∀ i, i < nums.length → 0 ≤ entry nums i ∧ entry nums i < (nums.length : Int))
      (h_k_ge : 1 ≤ k.val) (h_k_le : k.val ≤ (10 ^ 9 : Int))
      (nums2 : Slice Std.I64)
      (h_len2 : nums2.length = nums.length)
      (h_vals2 : ∀ i, i < nums2.length → 0 ≤ entry nums2 i ∧ entry nums2 i < (nums2.length : Int))
      (h_pattern : ∀ i j, i < nums.length → j < nums.length →
        (entry nums i = entry nums j ↔ entry nums2 i = entry nums2 j)) :
      ∀ r r2, min_cost nums k = ok r → min_cost nums2 k = ok r2 → r.val = r2.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (h_len_ge : 1 ≤ nums.length) (h_len_le : nums.length ≤ 1000)
        (h_vals : ∀ i, i < nums.length → 0 ≤ entry nums i ∧ entry nums i < (nums.length : Int))
        (h_k_ge : 1 ≤ k.val) (h_k_le : k.val ≤ (10 ^ 9 : Int))
        (nums2 : Slice Std.I64)
        (h_len2 : nums2.length = nums.length)
        (h_vals2 : ∀ i, i < nums2.length → 0 ≤ entry nums2 i ∧ entry nums2 i < (nums2.length : Int))
        (h_pattern : ∀ i j, i < nums.length → j < nums.length →
          (entry nums i = entry nums j ↔ entry nums2 i = entry nums2 j)), ∀ r r2, min_cost nums k = ok r → min_cost nums2 k = ok r2 → r.val = r2.val) := by
    sorry

  /-- Whenever the function returns a result r1 for nums and k1, and a result r2 for nums and k2, we have r1 <= r2.
    Preconditions: len(nums) >= 1; len(nums) <= 1000; for every i with 0 <= i < len(nums), 0 <= nums[i] < len(nums); and let k1 and k2 be integers with 1 <= k1 <= k2 <= 10^9. -/
  theorem spec_12 (nums : Slice Std.I64) (k1 k2 : Std.I64)
      (h_len_ge : 1 ≤ nums.length) (h_len_le : nums.length ≤ 1000)
      (h_vals : ∀ i, i < nums.length → 0 ≤ entry nums i ∧ entry nums i < (nums.length : Int))
      (h_k1_ge : 1 ≤ k1.val) (h_k1_le : k1.val ≤ k2.val) (h_k2_le : k2.val ≤ (10 ^ 9 : Int)) :
      ∀ r1 r2, min_cost nums k1 = ok r1 → min_cost nums k2 = ok r2 → r1.val ≤ r2.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice Std.I64) (k1 k2 : Std.I64)
        (h_len_ge : 1 ≤ nums.length) (h_len_le : nums.length ≤ 1000)
        (h_vals : ∀ i, i < nums.length → 0 ≤ entry nums i ∧ entry nums i < (nums.length : Int))
        (h_k1_ge : 1 ≤ k1.val) (h_k1_le : k1.val ≤ k2.val) (h_k2_le : k2.val ≤ (10 ^ 9 : Int)), ∀ r1 r2, min_cost nums k1 = ok r1 → min_cost nums k2 = ok r2 → r1.val ≤ r2.val) := by
    sorry

  end AegisSpec.MinCost
