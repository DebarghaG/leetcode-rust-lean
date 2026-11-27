import Aegis.SumFourDivisors.Code.Funs

/-!
# Specifications of `Aegis.SumFourDivisors.sum_four_divisors`

LeetCode problem `four-divisors`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.SumFourDivisors

  open Aegis.SumFourDivisors (sum_four_divisors)

  def values (nums : Slice Std.I64) : List ℤ := nums.val.map (fun x => x.val)

  def posDivisors (n : ℤ) : Finset ℕ := n.natAbs.divisors

  def numDivisors (n : ℤ) : ℕ := (posDivisors n).card

  def sumDivisors (n : ℤ) : ℤ := ∑ d ∈ posDivisors n, (d : ℤ)

  def hasFourDivisors (n : ℤ) : Prop := numDivisors n = 4

  instance instDecidableHasFourDivisors (n : ℤ) : Decidable (hasFourDivisors n) := by
    unfold hasFourDivisors
    infer_instance

  def contribution (n : ℤ) : ℤ := if hasFourDivisors n then sumDivisors n else 0

  def countOf (v : ℤ) (l : List ℤ) : ℕ := (l.filter (fun x => decide (x = v))).length

  /-- Let τ(n) be the number of positive divisors of n and σ(n) be their sum. The function sum_four_divisors(nums) returns a result r and r = Σ_{i=0}^{len(nums)-1} c(nums[i]), where c(n) = σ(n) if τ(n) = 4 and c(n) = 0 otherwise. The sum is over all indices, so equal values at different positions are counted separately.
    Preconditions: 1 ≤ len(nums) ≤ 10000 and for every i with 0 ≤ i < len(nums), 1 ≤ nums[i] ≤ 100000. -/
  theorem spec_1 (nums : Slice Std.I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 10000)
      (hval : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 100000) :
      ∃ r, sum_four_divisors nums = ok r ∧
        r.val = ((values nums).map contribution).sum := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 10000)
        (hval : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 100000), ∃ r, sum_four_divisors nums = ok r ∧
          r.val = ((values nums).map contribution).sum) := by
    sorry

  /-- The function sum_four_divisors(nums) returns a result (it does not fail, overflow, or panic).
    Preconditions: 1 ≤ len(nums) ≤ 10000 and for every i with 0 ≤ i < len(nums), 1 ≤ nums[i] ≤ 100000. -/
  theorem spec_2 (nums : Slice Std.I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 10000)
      (hval : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 100000) :
      ∃ r, sum_four_divisors nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 10000)
        (hval : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 100000), ∃ r, sum_four_divisors nums = ok r) := by
    sorry

  /-- Whenever sum_four_divisors(nums) returns r, we have 0 ≤ r.
    Preconditions: 1 ≤ len(nums) ≤ 10000 and for every i with 0 ≤ i < len(nums), 1 ≤ nums[i] ≤ 100000. -/
  theorem spec_3 (nums : Slice Std.I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 10000)
      (hval : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 100000) :
      ∀ r, sum_four_divisors nums = ok r → 0 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 10000)
        (hval : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 100000), ∀ r, sum_four_divisors nums = ok r → 0 ≤ r.val) := by
    sorry

  /-- Whenever sum_four_divisors(nums) returns r, r = 0 if and only if for every i with 0 ≤ i < len(nums), nums[i] has a number of positive divisors different from 4.
    Preconditions: 1 ≤ len(nums) ≤ 10000 and for every i with 0 ≤ i < len(nums), 1 ≤ nums[i] ≤ 100000. -/
  theorem spec_4 (nums : Slice Std.I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 10000)
      (hval : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 100000) :
      ∀ r, sum_four_divisors nums = ok r →
        (r.val = 0 ↔ ∀ x ∈ nums.val, ¬ hasFourDivisors x.val) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 10000)
        (hval : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 100000), ∀ r, sum_four_divisors nums = ok r →
          (r.val = 0 ↔ ∀ x ∈ nums.val, ¬ hasFourDivisors x.val)) := by
    sorry

  /-- Whenever sum_four_divisors(nums) returns r, for every i with 0 ≤ i < len(nums) such that nums[i] has exactly four positive divisors, σ(nums[i]) ≤ r, where σ(n) is the sum of the positive divisors of n.
    Preconditions: 1 ≤ len(nums) ≤ 10000 and for every i with 0 ≤ i < len(nums), 1 ≤ nums[i] ≤ 100000. -/
  theorem spec_5 (nums : Slice Std.I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 10000)
      (hval : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 100000) :
      ∀ r, sum_four_divisors nums = ok r →
        ∀ x ∈ nums.val, hasFourDivisors x.val → sumDivisors x.val ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 10000)
        (hval : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 100000), ∀ r, sum_four_divisors nums = ok r →
          ∀ x ∈ nums.val, hasFourDivisors x.val → sumDivisors x.val ≤ r.val) := by
    sorry

  /-- Whenever sum_four_divisors(nums) returns r, then for every slice nums' with the same length and the same multiset of entries as nums, every result r' returned by sum_four_divisors(nums') satisfies r' = r.
    Preconditions: 1 ≤ len(nums) ≤ 10000 and for every i with 0 ≤ i < len(nums), 1 ≤ nums[i] ≤ 100000. -/
  theorem spec_6 (nums : Slice Std.I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 10000)
      (hval : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 100000)
      (nums' : Slice Std.I64)
      (hn1 : 1 ≤ nums'.val.length) (hn2 : nums'.val.length ≤ 10000)
      (hnval : ∀ x ∈ nums'.val, 1 ≤ x.val ∧ x.val ≤ 100000)
      (hnlen : nums'.val.length = nums.val.length)
      (hperm : nums'.val.Perm nums.val) :
      ∀ r, sum_four_divisors nums = ok r →
        ∀ r', sum_four_divisors nums' = ok r' → r' = r := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 10000)
        (hval : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 100000)
        (nums' : Slice Std.I64)
        (hn1 : 1 ≤ nums'.val.length) (hn2 : nums'.val.length ≤ 10000)
        (hnval : ∀ x ∈ nums'.val, 1 ≤ x.val ∧ x.val ≤ 100000)
        (hnlen : nums'.val.length = nums.val.length)
        (hperm : nums'.val.Perm nums.val), ∀ r, sum_four_divisors nums = ok r →
          ∀ r', sum_four_divisors nums' = ok r' → r' = r) := by
    sorry

  /-- Fix an index i with 0 ≤ i < len(nums) such that nums[i] does not have exactly four positive divisors. Let nums' be any slice satisfying the same preconditions with len(nums') = len(nums), nums'[j] = nums[j] for every j ≠ i, and nums'[i] also not having exactly four positive divisors. Whenever sum_four_divisors(nums) returns r and sum_four_divisors(nums') returns r', we have r' = r.
    Preconditions: 1 ≤ len(nums) ≤ 10000 and for every i with 0 ≤ i < len(nums), 1 ≤ nums[i] ≤ 100000. -/
  theorem spec_7 (nums : Slice Std.I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 10000)
      (hval : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 100000)
      (i : ℕ) (hi : i < nums.val.length)
      (hnot4 : ¬ hasFourDivisors (nums.val.get ⟨i, hi⟩).val)
      (nums' : Slice Std.I64)
      (hn1 : 1 ≤ nums'.val.length) (hn2 : nums'.val.length ≤ 10000)
      (hnval : ∀ x ∈ nums'.val, 1 ≤ x.val ∧ x.val ≤ 100000)
      (hnlen : nums'.val.length = nums.val.length)
      (hagree : ∀ j, j ≠ i → nums'.val[j]? = nums.val[j]?)
      (hnot4' : ¬ hasFourDivisors (nums'.val.get ⟨i, by omega⟩).val) :
      ∀ r, sum_four_divisors nums = ok r →
        ∀ r', sum_four_divisors nums' = ok r' → r' = r := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 10000)
        (hval : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 100000)
        (i : ℕ) (hi : i < nums.val.length)
        (hnot4 : ¬ hasFourDivisors (nums.val.get ⟨i, hi⟩).val)
        (nums' : Slice Std.I64)
        (hn1 : 1 ≤ nums'.val.length) (hn2 : nums'.val.length ≤ 10000)
        (hnval : ∀ x ∈ nums'.val, 1 ≤ x.val ∧ x.val ≤ 100000)
        (hnlen : nums'.val.length = nums.val.length)
        (hagree : ∀ j, j ≠ i → nums'.val[j]? = nums.val[j]?)
        (hnot4' : ¬ hasFourDivisors (nums'.val.get ⟨i, by omega⟩).val), ∀ r, sum_four_divisors nums = ok r →
          ∀ r', sum_four_divisors nums' = ok r' → r' = r) := by
    sorry

  /-- Fix an index i with 0 ≤ i < len(nums) such that nums[i] has exactly four positive divisors. Let nums' be any slice satisfying the same preconditions with len(nums') = len(nums), nums'[j] = nums[j] for every j ≠ i, and nums'[i] having exactly four positive divisors and the same divisor sum σ(nums'[i]) = σ(nums[i]). Whenever sum_four_divisors(nums) returns r and sum_four_divisors(nums') returns r', we have r' = r.
    Preconditions: 1 ≤ len(nums) ≤ 10000 and for every i with 0 ≤ i < len(nums), 1 ≤ nums[i] ≤ 100000. -/
  theorem spec_8 (nums : Slice Std.I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 10000)
      (hval : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 100000)
      (i : ℕ) (hi : i < nums.val.length)
      (h4 : hasFourDivisors (nums.val.get ⟨i, hi⟩).val)
      (nums' : Slice Std.I64)
      (hn1 : 1 ≤ nums'.val.length) (hn2 : nums'.val.length ≤ 10000)
      (hnval : ∀ x ∈ nums'.val, 1 ≤ x.val ∧ x.val ≤ 100000)
      (hnlen : nums'.val.length = nums.val.length)
      (hagree : ∀ j, j ≠ i → nums'.val[j]? = nums.val[j]?)
      (h4' : hasFourDivisors (nums'.val.get ⟨i, by omega⟩).val)
      (hσ : sumDivisors (nums'.val.get ⟨i, by omega⟩).val =
        sumDivisors (nums.val.get ⟨i, hi⟩).val) :
      ∀ r, sum_four_divisors nums = ok r →
        ∀ r', sum_four_divisors nums' = ok r' → r' = r := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 10000)
        (hval : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 100000)
        (i : ℕ) (hi : i < nums.val.length)
        (h4 : hasFourDivisors (nums.val.get ⟨i, hi⟩).val)
        (nums' : Slice Std.I64)
        (hn1 : 1 ≤ nums'.val.length) (hn2 : nums'.val.length ≤ 10000)
        (hnval : ∀ x ∈ nums'.val, 1 ≤ x.val ∧ x.val ≤ 100000)
        (hnlen : nums'.val.length = nums.val.length)
        (hagree : ∀ j, j ≠ i → nums'.val[j]? = nums.val[j]?)
        (h4' : hasFourDivisors (nums'.val.get ⟨i, by omega⟩).val)
        (hσ : sumDivisors (nums'.val.get ⟨i, by omega⟩).val =
          sumDivisors (nums.val.get ⟨i, hi⟩).val), ∀ r, sum_four_divisors nums = ok r →
          ∀ r', sum_four_divisors nums' = ok r' → r' = r) := by
    sorry

  /-- Whenever sum_four_divisors(nums) returns r, let V be the set of distinct values appearing in nums, and for each v in V let k_v be the number of indices i with nums[i] = v. Then r = Σ_{v in V} (if τ(v) = 4 then k_v · σ(v) else 0), where τ(v) is the number of positive divisors of v and σ(v) is their sum.
    Preconditions: 1 ≤ len(nums) ≤ 10000 and for every i with 0 ≤ i < len(nums), 1 ≤ nums[i] ≤ 100000. -/
  theorem spec_9 (nums : Slice Std.I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 10000)
      (hval : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 100000) :
      ∀ r, sum_four_divisors nums = ok r →
        r.val = ∑ v ∈ (values nums).toFinset,
          (if hasFourDivisors v then (countOf v (values nums) : ℤ) * sumDivisors v else 0) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 10000)
        (hval : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 100000), ∀ r, sum_four_divisors nums = ok r →
          r.val = ∑ v ∈ (values nums).toFinset,
            (if hasFourDivisors v then (countOf v (values nums) : ℤ) * sumDivisors v else 0)) := by
    sorry

  /-- Whenever sum_four_divisors(a) returns r_a, sum_four_divisors(b) returns r_b, and sum_four_divisors(nums) returns r, we have r = r_a + r_b.
    Preconditions: 1 ≤ len(nums) ≤ 10000 and for every i with 0 ≤ i < len(nums), 1 ≤ nums[i] ≤ 100000. Let a and b be nonempty slices with nums = a ++ b. -/
  theorem spec_10 (nums : Slice Std.I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 10000)
      (hval : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 100000)
      (a b : Slice Std.I64) (ha : a.val ≠ []) (hb : b.val ≠ [])
      (hnums : nums.val = a.val ++ b.val) :
      ∀ r_a r_b r, sum_four_divisors a = ok r_a → sum_four_divisors b = ok r_b →
        sum_four_divisors nums = ok r → r.val = r_a.val + r_b.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 10000)
        (hval : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 100000)
        (a b : Slice Std.I64) (ha : a.val ≠ []) (hb : b.val ≠ [])
        (hnums : nums.val = a.val ++ b.val), ∀ r_a r_b r, sum_four_divisors a = ok r_a → sum_four_divisors b = ok r_b →
          sum_four_divisors nums = ok r → r.val = r_a.val + r_b.val) := by
    sorry

  /-- Whenever sum_four_divisors(nums) returns r, we have r ≤ 2000020000.
    Preconditions: 1 ≤ len(nums) ≤ 10000 and for every i with 0 ≤ i < len(nums), 1 ≤ nums[i] ≤ 100000. -/
  theorem spec_11 (nums : Slice Std.I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 10000)
      (hval : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 100000) :
      ∀ r, sum_four_divisors nums = ok r → r.val ≤ 2000020000 := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 10000)
        (hval : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 100000), ∀ r, sum_four_divisors nums = ok r → r.val ≤ 2000020000) := by
    sorry

  end AegisSpec.SumFourDivisors
