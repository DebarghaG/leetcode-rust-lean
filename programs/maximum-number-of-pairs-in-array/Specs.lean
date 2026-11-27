import Aegis.NumberOfPairs.Code.Funs

/-!
# Specifications of `Aegis.NumberOfPairs.number_of_pairs`

LeetCode problem `maximum-number-of-pairs-in-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.NumberOfPairs

  def elem (nums : Slice Std.I64) (i : ℕ) : ℤ :=
    ((nums.val[i]?).map (fun x => x.val)).getD 0

  def rget (r : alloc.vec.Vec Std.I64) (i : ℕ) : ℤ :=
    ((r.val[i]?).map (fun x => x.val)).getD 0

  def count (nums : Slice Std.I64) (v : ℤ) : ℕ :=
    (nums.val.filter (fun x => x.val = v)).length

  def pairsTotal (nums : Slice Std.I64) : ℕ :=
    ∑ v ∈ Finset.Icc (0 : ℕ) 100, count nums (v : ℤ) / 2

  def leftoversTotal (nums : Slice Std.I64) : ℕ :=
    ∑ v ∈ Finset.Icc (0 : ℕ) 100, count nums (v : ℤ) % 2

  def oddTotal (nums : Slice Std.I64) : ℕ :=
    ((Finset.Icc (0 : ℕ) 100).filter (fun v : ℕ => count nums (v : ℤ) % 2 = 1)).card

  def IsEqualPair (nums : Slice Std.I64) (p : ℕ × ℕ) : Prop :=
    p.1 < p.2 ∧ p.2 < nums.val.length ∧ elem nums p.1 = elem nums p.2

  def IsEqualPairSet (nums : Slice Std.I64) (P : Finset (ℕ × ℕ)) : Prop :=
    ∀ p ∈ P, IsEqualPair nums p

  def PairwiseDisjointPairs (P : Finset (ℕ × ℕ)) : Prop :=
    ∀ p ∈ P, ∀ q ∈ P, p ≠ q → p.1 ≠ q.1 ∧ p.1 ≠ q.2 ∧ p.2 ≠ q.1 ∧ p.2 ≠ q.2

  def covered (P : Finset (ℕ × ℕ)) : Finset ℕ :=
    P.biUnion (fun p => {p.1, p.2})

  def uncoveredCount (nums : Slice Std.I64) (P : Finset (ℕ × ℕ)) : ℕ :=
    (Finset.range nums.val.length \ covered P).card

  def SameFrequencies (nums nums' : Slice Std.I64) : Prop :=
    ∀ v : ℤ, count nums v = count nums' v

  /-- The function returns a result r (it does not fail) such that len(r) = 2, and for every integer v with 0 <= v <= 100, letting c_v = #{i | 0 <= i < len(nums) and nums[i] = v}, we have r[0] = Σ_{v=0}^{100} (c_v / 2) and r[1] = Σ_{v=0}^{100} (c_v mod 2), where / denotes integer division and mod denotes the remainder.
    Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100, and for every index i with 0 <= i < len(nums), 0 <= nums[i] <= 100. -/
  theorem spec_1 (nums : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
      (hval : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 100) :
      ∃ r : alloc.vec.Vec Std.I64,
        Aegis.NumberOfPairs.number_of_pairs nums = ok r ∧
        r.val.length = 2 ∧
        rget r 0 = (pairsTotal nums : ℤ) ∧
        rget r 1 = (leftoversTotal nums : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
        (hval : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 100), ∃ r : alloc.vec.Vec Std.I64,
          Aegis.NumberOfPairs.number_of_pairs nums = ok r ∧
          r.val.length = 2 ∧
          rget r 0 = (pairsTotal nums : ℤ) ∧
          rget r 1 = (leftoversTotal nums : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, len(r) = 2.
    Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100, and for every index i with 0 <= i < len(nums), 0 <= nums[i] <= 100. -/
  theorem spec_2 (nums : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
      (hval : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 100) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.NumberOfPairs.number_of_pairs nums = ok r → r.val.length = 2 := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
        (hval : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 100), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.NumberOfPairs.number_of_pairs nums = ok r → r.val.length = 2) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r (it does not fail).
    Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100, and for every index i with 0 <= i < len(nums), 0 <= nums[i] <= 100. -/
  theorem spec_3 (nums : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
      (hval : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 100) :
      ∃ r : alloc.vec.Vec Std.I64, Aegis.NumberOfPairs.number_of_pairs nums = ok r := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
        (hval : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 100), ∃ r : alloc.vec.Vec Std.I64, Aegis.NumberOfPairs.number_of_pairs nums = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r[0] <= len(nums) / 2, where / is integer division.
    Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100, and for every index i with 0 <= i < len(nums), 0 <= nums[i] <= 100. -/
  theorem spec_4 (nums : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
      (hval : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 100) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.NumberOfPairs.number_of_pairs nums = ok r →
        0 ≤ rget r 0 ∧ rget r 0 ≤ (nums.val.length : ℤ) / 2 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
        (hval : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 100), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.NumberOfPairs.number_of_pairs nums = ok r →
          0 ≤ rget r 0 ∧ rget r 0 ≤ (nums.val.length : ℤ) / 2) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r[1] <= len(nums).
    Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100, and for every index i with 0 <= i < len(nums), 0 <= nums[i] <= 100. -/
  theorem spec_5 (nums : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
      (hval : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 100) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.NumberOfPairs.number_of_pairs nums = ok r →
        0 ≤ rget r 1 ∧ rget r 1 ≤ (nums.val.length : ℤ) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
        (hval : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 100), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.NumberOfPairs.number_of_pairs nums = ok r →
          0 ≤ rget r 1 ∧ rget r 1 ≤ (nums.val.length : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, len(nums) = 2 * r[0] + r[1].
    Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100, and for every index i with 0 <= i < len(nums), 0 <= nums[i] <= 100. -/
  theorem spec_6 (nums : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
      (hval : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 100) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.NumberOfPairs.number_of_pairs nums = ok r →
        (nums.val.length : ℤ) = 2 * rget r 0 + rget r 1 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
        (hval : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 100), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.NumberOfPairs.number_of_pairs nums = ok r →
          (nums.val.length : ℤ) = 2 * rget r 0 + rget r 1) := by
    sorry

  /-- Whenever the function returns a result r, r[1] mod 2 = len(nums) mod 2.
    Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100, and for every index i with 0 <= i < len(nums), 0 <= nums[i] <= 100. -/
  theorem spec_7 (nums : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
      (hval : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 100) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.NumberOfPairs.number_of_pairs nums = ok r →
        rget r 1 % 2 = (nums.val.length : ℤ) % 2 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
        (hval : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 100), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.NumberOfPairs.number_of_pairs nums = ok r →
          rget r 1 % 2 = (nums.val.length : ℤ) % 2) := by
    sorry

  /-- Whenever the function returns a result r, r[1] = #{v | 0 <= v <= 100 and c_v is odd}, where c_v = #{i | 0 <= i < len(nums) and nums[i] = v}.
    Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100, and for every index i with 0 <= i < len(nums), 0 <= nums[i] <= 100. -/
  theorem spec_8 (nums : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
      (hval : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 100) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.NumberOfPairs.number_of_pairs nums = ok r →
        rget r 1 = (oddTotal nums : ℤ) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
        (hval : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 100), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.NumberOfPairs.number_of_pairs nums = ok r →
          rget r 1 = (oddTotal nums : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, r[0] = 0 if and only if c_v <= 1 for every integer v with 0 <= v <= 100, where c_v = #{i | 0 <= i < len(nums) and nums[i] = v}.
    Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100, and for every index i with 0 <= i < len(nums), 0 <= nums[i] <= 100. -/
  theorem spec_9 (nums : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
      (hval : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 100) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.NumberOfPairs.number_of_pairs nums = ok r →
        (rget r 0 = 0 ↔ ∀ v ∈ Finset.Icc (0 : ℕ) 100, count nums (v : ℤ) ≤ 1) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
        (hval : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 100), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.NumberOfPairs.number_of_pairs nums = ok r →
          (rget r 0 = 0 ↔ ∀ v ∈ Finset.Icc (0 : ℕ) 100, count nums (v : ℤ) ≤ 1)) := by
    sorry

  /-- Whenever the function returns a result r, r[1] = 0 if and only if c_v is even for every integer v with 0 <= v <= 100, where c_v = #{i | 0 <= i < len(nums) and nums[i] = v}.
    Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100, and for every index i with 0 <= i < len(nums), 0 <= nums[i] <= 100. -/
  theorem spec_10 (nums : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
      (hval : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 100) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.NumberOfPairs.number_of_pairs nums = ok r →
        (rget r 1 = 0 ↔ ∀ v ∈ Finset.Icc (0 : ℕ) 100, Even (count nums (v : ℤ))) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
        (hval : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 100), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.NumberOfPairs.number_of_pairs nums = ok r →
          (rget r 1 = 0 ↔ ∀ v ∈ Finset.Icc (0 : ℕ) 100, Even (count nums (v : ℤ)))) := by
    sorry

  /-- Whenever the function returns a result r, there exists a set P of unordered pairs {i,j} of indices such that: for every {i,j} in P, 0 <= i < j < len(nums) and nums[i] = nums[j]; no two distinct pairs in P share an index; |P| = r[0]; the number of indices i with 0 <= i < len(nums) that belong to no pair in P is r[1]; and no set of pairwise disjoint equal-value index pairs has cardinality greater than r[0].
    Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100, and for every index i with 0 <= i < len(nums), 0 <= nums[i] <= 100. -/
  theorem spec_11 (nums : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
      (hval : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 100) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.NumberOfPairs.number_of_pairs nums = ok r →
        ∃ P : Finset (ℕ × ℕ),
          IsEqualPairSet nums P ∧
          PairwiseDisjointPairs P ∧
          (P.card : ℤ) = rget r 0 ∧
          (uncoveredCount nums P : ℤ) = rget r 1 ∧
          ∀ Q : Finset (ℕ × ℕ),
            IsEqualPairSet nums Q → PairwiseDisjointPairs Q → Q.card ≤ P.card := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
        (hval : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 100), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.NumberOfPairs.number_of_pairs nums = ok r →
          ∃ P : Finset (ℕ × ℕ),
            IsEqualPairSet nums P ∧
            PairwiseDisjointPairs P ∧
            (P.card : ℤ) = rget r 0 ∧
            (uncoveredCount nums P : ℤ) = rget r 1 ∧
            ∀ Q : Finset (ℕ × ℕ),
              IsEqualPairSet nums Q → PairwiseDisjointPairs Q → Q.card ≤ P.card) := by
    sorry

  /-- Whenever the function returns a result r on nums, for every slice nums' of 64-bit integers with len(nums') = len(nums) and with the same value frequencies as nums (that is, for every integer v, #{i | 0 <= i < len(nums) and nums[i] = v} = #{j | 0 <= j < len(nums') and nums'[j] = v}), if the function returns a result r' on nums', then r' = r (in particular len(r') = len(r) = 2, r'[0] = r[0], and r'[1] = r[1]).
    Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100, and for every index i with 0 <= i < len(nums), 0 <= nums[i] <= 100. -/
  theorem spec_12 (nums : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
      (hval : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 100) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.NumberOfPairs.number_of_pairs nums = ok r →
        ∀ nums' : Slice Std.I64,
          nums'.val.length = nums.val.length →
          SameFrequencies nums nums' →
          ∀ r' : alloc.vec.Vec Std.I64,
            Aegis.NumberOfPairs.number_of_pairs nums' = ok r' → r' = r := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
        (hval : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 100), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.NumberOfPairs.number_of_pairs nums = ok r →
          ∀ nums' : Slice Std.I64,
            nums'.val.length = nums.val.length →
            SameFrequencies nums nums' →
            ∀ r' : alloc.vec.Vec Std.I64,
              Aegis.NumberOfPairs.number_of_pairs nums' = ok r' → r' = r) := by
    sorry

  end AegisSpec.NumberOfPairs
