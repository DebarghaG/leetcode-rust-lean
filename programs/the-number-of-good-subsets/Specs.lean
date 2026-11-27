import Aegis.NumberOfGoodSubsets.Code.Funs

/-!
# Specifications of `Aegis.NumberOfGoodSubsets.number_of_good_subsets`

LeetCode problem `the-number-of-good-subsets`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.NumberOfGoodSubsets

  noncomputable section

  def M : ℤ := 1000000007

  def PrimeZ (p : ℤ) : Prop := 0 < p ∧ Nat.Prime p.natAbs

  def supp (v : ℤ) : Set ℤ := {p : ℤ | PrimeZ p ∧ p ∣ v}

  def SquarefreeZ (v : ℤ) : Prop := ∀ p : ℤ, PrimeZ p → ¬ (p ^ 2 ∣ v)

  def vals (nums : Slice Std.I64) : List ℤ := nums.val.map (fun x => x.val)

  def entry? (nums : Slice Std.I64) (i : ℕ) : Option ℤ := (nums.val[i]?).map (fun x => x.val)

  def countOf (nums : Slice Std.I64) (v : ℤ) : ℕ := (vals nums).countP (fun x => x = v)

  def onesCount (nums : Slice Std.I64) : ℕ := countOf nums 1

  def nonOneIndices (nums : Slice Std.I64) : Finset ℕ :=
    (Finset.range nums.val.length).filter (fun i => entry? nums i ≠ some 1)

  def ValidInput (nums : Slice Std.I64) : Prop :=
    1 ≤ nums.val.length ∧ nums.val.length ≤ 100000 ∧ ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 30

  def ValidInputLt (nums : Slice Std.I64) : Prop :=
    1 ≤ nums.val.length ∧ nums.val.length < 100000 ∧ ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 30

  def GoodSet (nums : Slice Std.I64) (S : Finset ℕ) : Prop :=
    (∀ i ∈ S, i < nums.val.length) ∧
    (∃ i ∈ S, entry? nums i ≠ some 1) ∧
    (∀ i ∈ S, ∀ a : ℤ, entry? nums i = some a → a ≠ 1 → SquarefreeZ a) ∧
    (∀ i ∈ S, ∀ j ∈ S, i ≠ j → ∀ a b : ℤ,
      entry? nums i = some a → entry? nums j = some b → a ≠ 1 → b ≠ 1 →
      ∀ p : ℤ, p ∈ supp a → p ∈ supp b → False)

  def goodSetCount (nums : Slice Std.I64) : ℕ :=
    letI := Classical.decPred (GoodSet nums)
    ((Finset.range nums.val.length).powerset.filter (GoodSet nums)).card

  def GoodSubset (nums : Slice Std.I64) (T : Finset ℕ) : Prop :=
    T ⊆ nonOneIndices nums ∧
    T.Nonempty ∧
    (∀ i ∈ T, ∀ a : ℤ, entry? nums i = some a → SquarefreeZ a) ∧
    (∀ i ∈ T, ∀ j ∈ T, i ≠ j → ∀ a b : ℤ,
      entry? nums i = some a → entry? nums j = some b →
      ∀ p : ℤ, p ∈ supp a → p ∈ supp b → False)

  def goodSubsetCount (nums : Slice Std.I64) : ℕ :=
    letI := Classical.decPred (GoodSubset nums)
    ((nonOneIndices nums).powerset.filter (GoodSubset nums)).card

  def P30 : Finset ℤ := {2, 3, 5, 7, 11, 13, 17, 19, 23, 29}

  def P30Term (nums : Slice Std.I64) : ℤ :=
    (P30.prod (fun p => (countOf nums p : ℤ) + 1)) - 1

  /-- Whenever the function returns a result r, r is the unique integer such that 0 <= r < M and r is congruent to N modulo M.
    Preconditions: Let M = 1000000007. nums is a slice of 64-bit integers with 1 <= len(nums) <= 100000 and, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 30. For v > 0, let supp(v) be the set of primes p such that p divides v, and call v squarefree if no prime p satisfies p^2 divides v. Call a set S of indices with 0 <= i < len(nums) good when: (1) S contains at least one index i with nums[i] != 1; (2) every i in S with nums[i] != 1 has nums[i] squarefree; and (3) for distinct i,j in S with nums[i] != 1 and nums[j] != 1, supp(nums[i]) and supp(nums[j]) are disjoint. Let N be the number of good index sets S. -/
  theorem spec_1 (nums : Slice Std.I64) (h : ValidInput nums) :
      ∀ r, Aegis.NumberOfGoodSubsets.number_of_good_subsets nums = ok r →
        (0 ≤ r.val ∧ r.val < M ∧ Int.ModEq M (goodSetCount nums : ℤ) r.val) ∧
        (∀ r' : ℤ, 0 ≤ r' → r' < M → Int.ModEq M (goodSetCount nums : ℤ) r' → r' = r.val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (h : ValidInput nums), ∀ r, Aegis.NumberOfGoodSubsets.number_of_good_subsets nums = ok r →
          (0 ≤ r.val ∧ r.val < M ∧ Int.ModEq M (goodSetCount nums : ℤ) r.val) ∧
          (∀ r' : ℤ, 0 ≤ r' → r' < M → Int.ModEq M (goodSetCount nums : ℤ) r' → r' = r.val)) := by
    sorry

  /-- The function returns a result r (it does not fail, panic, or overflow) for every nums satisfying these constraints.
    Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100000 and, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 30. -/
  theorem spec_2 (nums : Slice Std.I64) (h : ValidInput nums) :
      ∃ r, Aegis.NumberOfGoodSubsets.number_of_good_subsets nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (h : ValidInput nums), ∃ r, Aegis.NumberOfGoodSubsets.number_of_good_subsets nums = ok r) := by
    sorry

  /-- Whenever the function returns a result r, r = 0.
    Preconditions: Let M = 1000000007. nums is a slice of 64-bit integers with 1 <= len(nums) <= 100000 and 1 <= nums[i] <= 30 for every index i. A positive integer v is squarefree if no prime p satisfies p^2 divides v. Suppose that for every i with 0 <= i < len(nums), either nums[i] = 1 or (nums[i] > 1 and nums[i] is not squarefree). -/
  theorem spec_3 (nums : Slice Std.I64) (h : ValidInput nums)
      (hval : ∀ x ∈ vals nums, x = 1 ∨ (1 < x ∧ ¬ SquarefreeZ x)) :
      ∀ r, Aegis.NumberOfGoodSubsets.number_of_good_subsets nums = ok r → r.val = 0 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (h : ValidInput nums)
        (hval : ∀ x ∈ vals nums, x = 1 ∨ (1 < x ∧ ¬ SquarefreeZ x)), ∀ r, Aegis.NumberOfGoodSubsets.number_of_good_subsets nums = ok r → r.val = 0) := by
    sorry

  /-- Whenever the function returns a result r, r is congruent to m * 2^c modulo M.
    Preconditions: Let M = 1000000007. nums is a slice of 64-bit integers with 1 <= len(nums) <= 100000 and 1 <= nums[i] <= 30 for every index i. Let v be an integer with 1 < v <= 30 that is squarefree (no prime p satisfies p^2 divides v). Suppose every nums[i] is either 1 or v. Let c be the number of indices i with nums[i] = 1, and let m be the number of indices i with nums[i] = v. -/
  theorem spec_4 (nums : Slice Std.I64) (v : ℤ) (h : ValidInput nums)
      (hv : 1 < v ∧ v ≤ 30) (hsf : SquarefreeZ v)
      (hval : ∀ x ∈ vals nums, x = 1 ∨ x = v) :
      ∀ r, Aegis.NumberOfGoodSubsets.number_of_good_subsets nums = ok r →
        Int.ModEq M r.val ((countOf nums v : ℤ) * (2 : ℤ) ^ onesCount nums) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (v : ℤ) (h : ValidInput nums)
        (hv : 1 < v ∧ v ≤ 30) (hsf : SquarefreeZ v)
        (hval : ∀ x ∈ vals nums, x = 1 ∨ x = v), ∀ r, Aegis.NumberOfGoodSubsets.number_of_good_subsets nums = ok r →
          Int.ModEq M r.val ((countOf nums v : ℤ) * (2 : ℤ) ^ onesCount nums)) := by
    sorry

  /-- Whenever the function returns a result r, r is congruent to (2^k - 1) * 2^c modulo M.
    Preconditions: Let M = 1000000007. nums is a slice of 64-bit integers with 1 <= len(nums) <= 100000 and 1 <= nums[i] <= 30 for every index i. For v > 0, supp(v) is the set of primes dividing v, and v is squarefree if no prime p satisfies p^2 divides v. Let J be the set of indices i with nums[i] != 1, let k = len(J), and let c be the number of indices i with nums[i] = 1. Suppose that for every i in J, nums[i] is squarefree and nums[i] > 1, and that for distinct i,j in J, supp(nums[i]) and supp(nums[j]) are disjoint. -/
  theorem spec_5 (nums : Slice Std.I64) (h : ValidInput nums)
      (hJ : ∀ i ∈ nonOneIndices nums, ∀ a : ℤ, entry? nums i = some a → 1 < a ∧ SquarefreeZ a)
      (hdisj : ∀ i ∈ nonOneIndices nums, ∀ j ∈ nonOneIndices nums, i ≠ j →
        ∀ a b : ℤ, entry? nums i = some a → entry? nums j = some b →
        ∀ p : ℤ, p ∈ supp a → p ∈ supp b → False) :
      ∀ r, Aegis.NumberOfGoodSubsets.number_of_good_subsets nums = ok r →
        Int.ModEq M r.val
          (((2 : ℤ) ^ (nonOneIndices nums).card - 1) * (2 : ℤ) ^ onesCount nums) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (h : ValidInput nums)
        (hJ : ∀ i ∈ nonOneIndices nums, ∀ a : ℤ, entry? nums i = some a → 1 < a ∧ SquarefreeZ a)
        (hdisj : ∀ i ∈ nonOneIndices nums, ∀ j ∈ nonOneIndices nums, i ≠ j →
          ∀ a b : ℤ, entry? nums i = some a → entry? nums j = some b →
          ∀ p : ℤ, p ∈ supp a → p ∈ supp b → False), ∀ r, Aegis.NumberOfGoodSubsets.number_of_good_subsets nums = ok r →
          Int.ModEq M r.val
            (((2 : ℤ) ^ (nonOneIndices nums).card - 1) * (2 : ℤ) ^ onesCount nums)) := by
    sorry

  /-- Whenever the function returns a result r, r is congruent to ((product over p in P30 of (m_p + 1)) - 1) * 2^c modulo M.
    Preconditions: Let M = 1000000007. nums is a slice of 64-bit integers with 1 <= len(nums) <= 100000 and 1 <= nums[i] <= 30 for every index i. Let P30 = {2,3,5,7,11,13,17,19,23,29}. Suppose every nums[i] is either 1 or one of the primes in P30. For each p in P30, let m_p be the number of indices i with nums[i] = p, and let c be the number of indices i with nums[i] = 1. -/
  theorem spec_6 (nums : Slice Std.I64) (h : ValidInput nums)
      (hval : ∀ x ∈ vals nums, x = 1 ∨ x ∈ P30) :
      ∀ r, Aegis.NumberOfGoodSubsets.number_of_good_subsets nums = ok r →
        Int.ModEq M r.val (P30Term nums * (2 : ℤ) ^ onesCount nums) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (h : ValidInput nums)
        (hval : ∀ x ∈ vals nums, x = 1 ∨ x ∈ P30), ∀ r, Aegis.NumberOfGoodSubsets.number_of_good_subsets nums = ok r →
          Int.ModEq M r.val (P30Term nums * (2 : ℤ) ^ onesCount nums)) := by
    sorry

  /-- Whenever the function returns a result r, r is congruent to K * 2^c modulo M.
    Preconditions: Let M = 1000000007. nums is a slice of 64-bit integers with 1 <= len(nums) <= 100000 and 1 <= nums[i] <= 30 for every index i. Let c be the number of indices i with nums[i] = 1. Let K be the number of subsets T of {i | nums[i] != 1} such that T is nonempty, every i in T has nums[i] squarefree, and for distinct i,j in T the prime supports supp(nums[i]) and supp(nums[j]) are disjoint. -/
  theorem spec_7 (nums : Slice Std.I64) (h : ValidInput nums) :
      ∀ r, Aegis.NumberOfGoodSubsets.number_of_good_subsets nums = ok r →
        Int.ModEq M r.val ((goodSubsetCount nums : ℤ) * (2 : ℤ) ^ onesCount nums) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (h : ValidInput nums), ∀ r, Aegis.NumberOfGoodSubsets.number_of_good_subsets nums = ok r →
          Int.ModEq M r.val ((goodSubsetCount nums : ℤ) * (2 : ℤ) ^ onesCount nums)) := by
    sorry

  /-- Whenever the function returns r1 on nums1 and r2 on nums2, r2 is congruent to 2*r1 modulo M.
    Preconditions: Let M = 1000000007. nums1 is a slice of 64-bit integers with 1 <= len(nums1) < 100000 and 1 <= nums1[i] <= 30 for every index i. Let nums2 be obtained from nums1 by inserting one additional entry equal to 1 at any position, so nums2 also satisfies the original constraints. Let r1 be the result on nums1 and r2 the result on nums2. -/
  theorem spec_8 (nums1 nums2 : Slice Std.I64) (h1 : ValidInputLt nums1) (h2 : ValidInput nums2)
      (hins : ∃ l₁ l₂ : List ℤ, vals nums1 = l₁ ++ l₂ ∧ vals nums2 = l₁ ++ [1] ++ l₂) :
      ∀ r1 r2, Aegis.NumberOfGoodSubsets.number_of_good_subsets nums1 = ok r1 →
        Aegis.NumberOfGoodSubsets.number_of_good_subsets nums2 = ok r2 →
        Int.ModEq M r2.val (2 * r1.val) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64) (h1 : ValidInputLt nums1) (h2 : ValidInput nums2)
        (hins : ∃ l₁ l₂ : List ℤ, vals nums1 = l₁ ++ l₂ ∧ vals nums2 = l₁ ++ [1] ++ l₂), ∀ r1 r2, Aegis.NumberOfGoodSubsets.number_of_good_subsets nums1 = ok r1 →
          Aegis.NumberOfGoodSubsets.number_of_good_subsets nums2 = ok r2 →
          Int.ModEq M r2.val (2 * r1.val)) := by
    sorry

  /-- Whenever the function returns r1 on nums1 and r2 on nums2, r1 = r2.
    Preconditions: Let M = 1000000007. nums1 is a slice of 64-bit integers with 1 <= len(nums1) < 100000 and 1 <= nums1[i] <= 30 for every index i. Let v be an integer with 1 < v <= 30 such that v is not squarefree (some prime p satisfies p^2 divides v). Let nums2 be obtained from nums1 by inserting one additional entry equal to v at any position, so nums2 also satisfies the original constraints. Let r1 be the result on nums1 and r2 the result on nums2. -/
  theorem spec_9 (nums1 nums2 : Slice Std.I64) (v : ℤ) (h1 : ValidInputLt nums1)
      (h2 : ValidInput nums2) (hv : 1 < v ∧ v ≤ 30) (hnsf : ¬ SquarefreeZ v)
      (hins : ∃ l₁ l₂ : List ℤ, vals nums1 = l₁ ++ l₂ ∧ vals nums2 = l₁ ++ [v] ++ l₂) :
      ∀ r1 r2, Aegis.NumberOfGoodSubsets.number_of_good_subsets nums1 = ok r1 →
        Aegis.NumberOfGoodSubsets.number_of_good_subsets nums2 = ok r2 → r1 = r2 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64) (v : ℤ) (h1 : ValidInputLt nums1)
        (h2 : ValidInput nums2) (hv : 1 < v ∧ v ≤ 30) (hnsf : ¬ SquarefreeZ v)
        (hins : ∃ l₁ l₂ : List ℤ, vals nums1 = l₁ ++ l₂ ∧ vals nums2 = l₁ ++ [v] ++ l₂), ∀ r1 r2, Aegis.NumberOfGoodSubsets.number_of_good_subsets nums1 = ok r1 →
          Aegis.NumberOfGoodSubsets.number_of_good_subsets nums2 = ok r2 → r1 = r2) := by
    sorry

  /-- Whenever the function returns a result r, r is congruent to 2^c modulo M.
    Preconditions: Let M = 1000000007. nums is a slice of 64-bit integers with 1 <= len(nums) <= 100000 and 1 <= nums[i] <= 30 for every index i. Let c be the number of indices i with nums[i] = 1. Suppose there is exactly one index j such that nums[j] > 1 and nums[j] is squarefree, and for every index i != j either nums[i] = 1 or (nums[i] > 1 and nums[i] is not squarefree). -/
  theorem spec_10 (nums : Slice Std.I64) (h : ValidInput nums)
      (hunique : ∃ j : ℕ, j < nums.val.length ∧
        (∀ a : ℤ, entry? nums j = some a → 1 < a ∧ SquarefreeZ a) ∧
        (∀ i : ℕ, i < nums.val.length → i ≠ j →
          ∀ a : ℤ, entry? nums i = some a → a = 1 ∨ (1 < a ∧ ¬ SquarefreeZ a))) :
      ∀ r, Aegis.NumberOfGoodSubsets.number_of_good_subsets nums = ok r →
        Int.ModEq M r.val ((2 : ℤ) ^ onesCount nums) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64) (h : ValidInput nums)
        (hunique : ∃ j : ℕ, j < nums.val.length ∧
          (∀ a : ℤ, entry? nums j = some a → 1 < a ∧ SquarefreeZ a) ∧
          (∀ i : ℕ, i < nums.val.length → i ≠ j →
            ∀ a : ℤ, entry? nums i = some a → a = 1 ∨ (1 < a ∧ ¬ SquarefreeZ a))), ∀ r, Aegis.NumberOfGoodSubsets.number_of_good_subsets nums = ok r →
          Int.ModEq M r.val ((2 : ℤ) ^ onesCount nums)) := by
    sorry

  end

  end AegisSpec.NumberOfGoodSubsets
