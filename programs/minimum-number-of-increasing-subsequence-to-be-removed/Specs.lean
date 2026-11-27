import Aegis.MinOperations.Code.Funs

/-!
# Specifications of `Aegis.MinOperations.min_operations`

LeetCode problem `minimum-number-of-increasing-subsequence-to-be-removed`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinOperations

  def getInt (l : List Std.I64) (i : Nat) : Int :=
    match l[i]? with
    | some x => x.val
    | none => 0

  def IsIncSubseq (l : List Std.I64) (idx : List Nat) : Prop :=
    (∀ i ∈ idx, i < l.length) ∧
      idx.Pairwise (· < ·) ∧
      (idx.map (getInt l)).Pairwise (· < ·)

  def IsNonIncSubseq (l : List Std.I64) (idx : List Nat) : Prop :=
    (∀ i ∈ idx, i < l.length) ∧
      idx.Pairwise (· < ·) ∧
      (idx.map (getInt l)).Pairwise (· ≥ ·)

  def PairwiseDisjoint (parts : List (List Nat)) : Prop :=
    ∀ p ∈ parts, ∀ q ∈ parts, p ≠ q → ∀ i, i ∈ p → i ∉ q

  def CoversAll (l : List Std.I64) (parts : List (List Nat)) : Prop :=
    ∀ i, i < l.length → ∃ p ∈ parts, i ∈ p

  def IsIncPartition (l : List Std.I64) (parts : List (List Nat)) : Prop :=
    (∀ p ∈ parts, IsIncSubseq l p) ∧ PairwiseDisjoint parts ∧ CoversAll l parts

  def HasIncPartition (l : List Std.I64) (k : Nat) : Prop :=
    ∃ parts : List (List Nat), parts.length = k ∧ IsIncPartition l parts

  def HasNonemptyIncPartition (l : List Std.I64) (k : Nat) : Prop :=
    ∃ parts : List (List Nat),
      parts.length = k ∧ IsIncPartition l parts ∧ ∀ p ∈ parts, p ≠ []

  def IsMinIncCover (l : List Std.I64) (m : Nat) : Prop :=
    HasNonemptyIncPartition l m ∧ ∀ k, HasNonemptyIncPartition l k → m ≤ k

  def IsMaxNonIncSubseqLen (l : List Std.I64) (m : Nat) : Prop :=
    (∃ idx : List Nat, IsNonIncSubseq l idx ∧ idx.length = m) ∧
      ∀ idx : List Nat, IsNonIncSubseq l idx → idx.length ≤ m

  def IsMaxIncSubseqLen (l : List Std.I64) (m : Nat) : Prop :=
    (∃ idx : List Nat, IsIncSubseq l idx ∧ idx.length = m) ∧
      ∀ idx : List Nat, IsIncSubseq l idx → idx.length ≤ m

  def countVal (l : List Std.I64) (v : Int) : Nat :=
    (l.filter fun x => x.val = v).length

  /-- The function returns a result r (it does not fail), and r is the least integer k >= 0 for which there exist k nonempty, pairwise disjoint index sets S_1,...,S_k whose union is {0,1,...,len(nums)-1} and such that, for each j, if the elements of S_j are written in increasing order i_0 < i_1 < ... < i_{m-1}, then nums[i_0] < nums[i_1] < ... < nums[i_{m-1}]. Equivalently, r is the minimum number of operations required to delete all elements when each operation deletes a strictly increasing subsequence of the current array.
    Preconditions: len(nums) >= 1 and len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000. -/
  theorem spec_1 (nums : Slice Std.I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
      (hrange : ∀ i, i < nums.val.length → 1 ≤ getInt nums.val i ∧ getInt nums.val i ≤ 100000) :
      ∃ r : Std.I64,
        Aegis.MinOperations.min_operations nums = ok r ∧
          0 ≤ r.val ∧
            HasNonemptyIncPartition nums.val r.val.toNat ∧
              ∀ k : Nat, HasNonemptyIncPartition nums.val k → r.val ≤ (k : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
        (hrange : ∀ i, i < nums.val.length → 1 ≤ getInt nums.val i ∧ getInt nums.val i ≤ 100000), ∃ r : Std.I64,
          Aegis.MinOperations.min_operations nums = ok r ∧
            0 ≤ r.val ∧
              HasNonemptyIncPartition nums.val r.val.toNat ∧
                ∀ k : Nat, HasNonemptyIncPartition nums.val k → r.val ≤ (k : Int)) := by
    sorry

  /-- Whenever the function returns a result r, r equals the maximum length m of a non-increasing subsequence of nums, defined as indices i_0 < i_1 < ... < i_{m-1} with 0 <= i_0, i_{m-1} < len(nums), and nums[i_0] >= nums[i_1] >= ... >= nums[i_{m-1]}. Since nums is nonempty, this maximum is at least 1.
    Preconditions: len(nums) >= 1 and len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000. -/
  theorem spec_2 (nums : Slice Std.I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
      (hrange : ∀ i, i < nums.val.length → 1 ≤ getInt nums.val i ∧ getInt nums.val i ≤ 100000) :
      ∀ r : Std.I64, Aegis.MinOperations.min_operations nums = ok r →
        ∃ m : Nat, IsMaxNonIncSubseqLen nums.val m ∧ r.val = (m : Int) := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
        (hrange : ∀ i, i < nums.val.length → 1 ≤ getInt nums.val i ∧ getInt nums.val i ≤ 100000), ∀ r : Std.I64, Aegis.MinOperations.min_operations nums = ok r →
          ∃ m : Nat, IsMaxNonIncSubseqLen nums.val m ∧ r.val = (m : Int)) := by
    sorry

  /-- Whenever the function returns a result r, 1 <= r <= len(nums).
    Preconditions: len(nums) >= 1 and len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000. -/
  theorem spec_3 (nums : Slice Std.I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
      (hrange : ∀ i, i < nums.val.length → 1 ≤ getInt nums.val i ∧ getInt nums.val i ≤ 100000) :
      ∀ r : Std.I64, Aegis.MinOperations.min_operations nums = ok r →
        1 ≤ r.val ∧ r.val ≤ (nums.val.length : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
        (hrange : ∀ i, i < nums.val.length → 1 ≤ getInt nums.val i ∧ getInt nums.val i ≤ 100000), ∀ r : Std.I64, Aegis.MinOperations.min_operations nums = ok r →
          1 ≤ r.val ∧ r.val ≤ (nums.val.length : Int)) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r (an i64) and does not fail; there is no overflow, out-of-bounds access, or panic.
    Preconditions: len(nums) >= 1 and len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000. -/
  theorem spec_4 (nums : Slice Std.I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
      (hrange : ∀ i, i < nums.val.length → 1 ≤ getInt nums.val i ∧ getInt nums.val i ≤ 100000) :
      ∃ r : Std.I64, Aegis.MinOperations.min_operations nums = ok r := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
        (hrange : ∀ i, i < nums.val.length → 1 ≤ getInt nums.val i ∧ getInt nums.val i ≤ 100000), ∃ r : Std.I64, Aegis.MinOperations.min_operations nums = ok r) := by
    sorry

  /-- Whenever the function returns a result r, r = 1 if and only if for every i with 0 <= i < len(nums)-1, nums[i] < nums[i+1], equivalently the entire array is strictly increasing.
    Preconditions: len(nums) >= 1 and len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000. -/
  theorem spec_5 (nums : Slice Std.I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
      (hrange : ∀ i, i < nums.val.length → 1 ≤ getInt nums.val i ∧ getInt nums.val i ≤ 100000) :
      ∀ r : Std.I64, Aegis.MinOperations.min_operations nums = ok r →
        (r.val = 1 ↔
          ∀ i, i + 1 < nums.val.length → getInt nums.val i < getInt nums.val (i + 1)) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
        (hrange : ∀ i, i < nums.val.length → 1 ≤ getInt nums.val i ∧ getInt nums.val i ≤ 100000), ∀ r : Std.I64, Aegis.MinOperations.min_operations nums = ok r →
          (r.val = 1 ↔
            ∀ i, i + 1 < nums.val.length → getInt nums.val i < getInt nums.val (i + 1))) := by
    sorry

  /-- Whenever the function returns a result r, r = len(nums) if and only if for every i with 0 <= i < len(nums)-1, nums[i] >= nums[i+1], equivalently nums is non-increasing so that for all i < j, nums[i] >= nums[j].
    Preconditions: len(nums) >= 1 and len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000. -/
  theorem spec_6 (nums : Slice Std.I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
      (hrange : ∀ i, i < nums.val.length → 1 ≤ getInt nums.val i ∧ getInt nums.val i ≤ 100000) :
      ∀ r : Std.I64, Aegis.MinOperations.min_operations nums = ok r →
        (r.val = (nums.val.length : Int) ↔
          ∀ i, i + 1 < nums.val.length →
            getInt nums.val (i + 1) ≤ getInt nums.val i) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
        (hrange : ∀ i, i < nums.val.length → 1 ≤ getInt nums.val i ∧ getInt nums.val i ≤ 100000), ∀ r : Std.I64, Aegis.MinOperations.min_operations nums = ok r →
          (r.val = (nums.val.length : Int) ↔
            ∀ i, i + 1 < nums.val.length →
              getInt nums.val (i + 1) ≤ getInt nums.val i)) := by
    sorry

  /-- Whenever the function returns a result r, for every integer v, r >= count(v), where count(v) is the number of indices i with 0 <= i < len(nums) and nums[i] = v.
    Preconditions: len(nums) >= 1 and len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000. -/
  theorem spec_7 (nums : Slice Std.I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
      (hrange : ∀ i, i < nums.val.length → 1 ≤ getInt nums.val i ∧ getInt nums.val i ≤ 100000) :
      ∀ r : Std.I64, Aegis.MinOperations.min_operations nums = ok r →
        ∀ v : Int, (countVal nums.val v : Int) ≤ r.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
        (hrange : ∀ i, i < nums.val.length → 1 ≤ getInt nums.val i ∧ getInt nums.val i ≤ 100000), ∀ r : Std.I64, Aegis.MinOperations.min_operations nums = ok r →
          ∀ v : Int, (countVal nums.val v : Int) ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, there exist indices i_0 < i_1 < ... < i_{r-1} with 0 <= i_0, i_{r-1} < len(nums), and nums[i_0] >= nums[i_1] >= ... >= nums[i_{r-1}]; that is, nums has a non-increasing subsequence of length exactly r.
    Preconditions: len(nums) >= 1 and len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000. -/
  theorem spec_8 (nums : Slice Std.I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
      (hrange : ∀ i, i < nums.val.length → 1 ≤ getInt nums.val i ∧ getInt nums.val i ≤ 100000) :
      ∀ r : Std.I64, Aegis.MinOperations.min_operations nums = ok r →
        ∃ idx : List Nat, IsNonIncSubseq nums.val idx ∧ (idx.length : Int) = r.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
        (hrange : ∀ i, i < nums.val.length → 1 ≤ getInt nums.val i ∧ getInt nums.val i ≤ 100000), ∀ r : Std.I64, Aegis.MinOperations.min_operations nums = ok r →
          ∃ idx : List Nat, IsNonIncSubseq nums.val idx ∧ (idx.length : Int) = r.val) := by
    sorry

  /-- Whenever the function returns a result r, there exist r strictly increasing subsequences of nums whose index sets are pairwise disjoint and whose union is {0,1,...,len(nums)-1}.
    Preconditions: len(nums) >= 1 and len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000. -/
  theorem spec_9 (nums : Slice Std.I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
      (hrange : ∀ i, i < nums.val.length → 1 ≤ getInt nums.val i ∧ getInt nums.val i ≤ 100000) :
      ∀ r : Std.I64, Aegis.MinOperations.min_operations nums = ok r →
        ∃ parts : List (List Nat),
          parts.length = r.val.toNat ∧ IsIncPartition nums.val parts := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
        (hrange : ∀ i, i < nums.val.length → 1 ≤ getInt nums.val i ∧ getInt nums.val i ≤ 100000), ∀ r : Std.I64, Aegis.MinOperations.min_operations nums = ok r →
          ∃ parts : List (List Nat),
            parts.length = r.val.toNat ∧ IsIncPartition nums.val parts) := by
    sorry

  /-- Whenever the function returns a result r, for every integer k with 0 <= k < r, there does not exist a partition of {0,1,...,len(nums)-1} into k nonempty index sets each of which, when sorted, gives a strictly increasing subsequence of nums.
    Preconditions: len(nums) >= 1 and len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000. -/
  theorem spec_10 (nums : Slice Std.I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
      (hrange : ∀ i, i < nums.val.length → 1 ≤ getInt nums.val i ∧ getInt nums.val i ≤ 100000) :
      ∀ r : Std.I64, Aegis.MinOperations.min_operations nums = ok r →
        ∀ k : Nat, (k : Int) < r.val → ¬ HasNonemptyIncPartition nums.val k := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
        (hrange : ∀ i, i < nums.val.length → 1 ≤ getInt nums.val i ∧ getInt nums.val i ≤ 100000), ∀ r : Std.I64, Aegis.MinOperations.min_operations nums = ok r →
          ∀ k : Nat, (k : Int) < r.val → ¬ HasNonemptyIncPartition nums.val k) := by
    sorry

  /-- Whenever the function returns a result r, for every p with 1 <= p <= len(nums), the minimum number of strictly increasing subsequences needed to cover the prefix nums[0], nums[1], ..., nums[p-1] is at most r.
    Preconditions: len(nums) >= 1 and len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000. -/
  theorem spec_11 (nums : Slice Std.I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
      (hrange : ∀ i, i < nums.val.length → 1 ≤ getInt nums.val i ∧ getInt nums.val i ≤ 100000) :
      ∀ r : Std.I64, Aegis.MinOperations.min_operations nums = ok r →
        ∀ p : Nat, 1 ≤ p → p ≤ nums.val.length →
          ∃ m : Nat, IsMinIncCover (nums.val.take p) m ∧ (m : Int) ≤ r.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
        (hrange : ∀ i, i < nums.val.length → 1 ≤ getInt nums.val i ∧ getInt nums.val i ≤ 100000), ∀ r : Std.I64, Aegis.MinOperations.min_operations nums = ok r →
          ∀ p : Nat, 1 ≤ p → p ≤ nums.val.length →
            ∃ m : Nat, IsMinIncCover (nums.val.take p) m ∧ (m : Int) ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, for every s with 0 <= s < len(nums), the minimum number of strictly increasing subsequences needed to cover the suffix nums[s], nums[s+1], ..., nums[len(nums)-1] is at most r.
    Preconditions: len(nums) >= 1 and len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000. -/
  theorem spec_12 (nums : Slice Std.I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
      (hrange : ∀ i, i < nums.val.length → 1 ≤ getInt nums.val i ∧ getInt nums.val i ≤ 100000) :
      ∀ r : Std.I64, Aegis.MinOperations.min_operations nums = ok r →
        ∀ s : Nat, s < nums.val.length →
          ∃ m : Nat, IsMinIncCover (nums.val.drop s) m ∧ (m : Int) ≤ r.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
        (hrange : ∀ i, i < nums.val.length → 1 ≤ getInt nums.val i ∧ getInt nums.val i ≤ 100000), ∀ r : Std.I64, Aegis.MinOperations.min_operations nums = ok r →
          ∀ s : Nat, s < nums.val.length →
            ∃ m : Nat, IsMinIncCover (nums.val.drop s) m ∧ (m : Int) ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, let m be the minimum number of strictly increasing subsequences needed to cover the proper prefix nums[0], nums[1], ..., nums[len(nums)-2]. Then r <= m + 1.
    Preconditions: 2 <= len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000. -/
  theorem spec_13 (nums : Slice Std.I64)
      (hlen1 : 2 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
      (hrange : ∀ i, i < nums.val.length → 1 ≤ getInt nums.val i ∧ getInt nums.val i ≤ 100000) :
      ∀ r : Std.I64, Aegis.MinOperations.min_operations nums = ok r →
        ∃ m : Nat,
          IsMinIncCover (nums.val.take (nums.val.length - 1)) m ∧ r.val ≤ (m : Int) + 1 := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen1 : 2 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
        (hrange : ∀ i, i < nums.val.length → 1 ≤ getInt nums.val i ∧ getInt nums.val i ≤ 100000), ∀ r : Std.I64, Aegis.MinOperations.min_operations nums = ok r →
          ∃ m : Nat,
            IsMinIncCover (nums.val.take (nums.val.length - 1)) m ∧ r.val ≤ (m : Int) + 1) := by
    sorry

  /-- Whenever the function returns a result r, let L be the maximum length of a strictly increasing subsequence of nums, i.e. the maximum m for which there exist indices i_0 < i_1 < ... < i_{m-1} with 0 <= i_0, i_{m-1} < len(nums) and nums[i_0] < nums[i_1] < ... < nums[i_{m-1}]. Then r <= len(nums) - L + 1.
    Preconditions: len(nums) >= 1 and len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000. -/
  theorem spec_14 (nums : Slice Std.I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
      (hrange : ∀ i, i < nums.val.length → 1 ≤ getInt nums.val i ∧ getInt nums.val i ≤ 100000) :
      ∀ r : Std.I64, Aegis.MinOperations.min_operations nums = ok r →
        ∀ L : Nat, IsMaxIncSubseqLen nums.val L →
          r.val ≤ (nums.val.length : Int) - (L : Int) + 1 := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
        (hrange : ∀ i, i < nums.val.length → 1 ≤ getInt nums.val i ∧ getInt nums.val i ≤ 100000), ∀ r : Std.I64, Aegis.MinOperations.min_operations nums = ok r →
          ∀ L : Nat, IsMaxIncSubseqLen nums.val L →
            r.val ≤ (nums.val.length : Int) - (L : Int) + 1) := by
    sorry

  end AegisSpec.MinOperations
