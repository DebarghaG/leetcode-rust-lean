import Aegis.MaxFrequency.Code.Funs

/-!
# Specifications of `Aegis.MaxFrequency.max_frequency`

LeetCode problem `maximum-frequency-of-an-element-after-performing-operations-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxFrequency

def countOfEq (nums : List Std.I64) (t : Int) : Nat :=
  (nums.filter (fun x => x.val = t)).length

def countOfNearNe (nums : List Std.I64) (k t : Int) : Nat :=
  (nums.filter (fun x => x.val ≠ t ∧ |x.val - t| ≤ k)).length

def countOfClose (nums : List Std.I64) (k t : Int) : Nat :=
  (nums.filter (fun x => |x.val - t| ≤ k)).length

def score (nums : List Std.I64) (k numOperations t : Int) : Int :=
  (countOfEq nums t : Int) + min numOperations (countOfNearNe nums k t : Int)

def finalValue (nums : List Std.I64) (S : Finset (Fin nums.length))
    (d : Fin nums.length → Int) (i : Fin nums.length) : Int :=
  if i ∈ S then (nums.get i).val + d i else (nums.get i).val

/-- The function returns a result r, and with E(t) = #{i | 0 <= i < n and nums[i] = t} and N(t) = #{i | 0 <= i < n and nums[i] != t and |nums[i] - t| <= k}, r = max_{t in Z} (E(t) + min(numOperations, N(t))).
  Preconditions: Let n = len(nums). Assume 1 <= n <= 10^5; for every i with 0 <= i < n, 1 <= nums[i] <= 10^9; 0 <= k <= 10^9; and 0 <= numOperations <= n. -/
theorem spec_1 (nums : Slice Std.I64) (k numOperations : Std.I64)
    (h_len_pos : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000)
    (h_elems : ∀ i : Fin nums.val.length,
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 1000000000)
    (h_k : 0 ≤ k.val ∧ k.val ≤ 1000000000)
    (h_ops : 0 ≤ numOperations.val ∧ numOperations.val ≤ (nums.val.length : Int)) :
    ∃ r : Std.I64,
      Aegis.MaxFrequency.max_frequency nums k numOperations = ok r ∧
      (∀ t : Int, score nums.val k.val numOperations.val t ≤ r.val) ∧
      (∃ t : Int, score nums.val k.val numOperations.val t = r.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (k numOperations : Std.I64)
    (h_len_pos : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000)
    (h_elems : ∀ i : Fin nums.val.length,
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 1000000000)
    (h_k : 0 ≤ k.val ∧ k.val ≤ 1000000000)
    (h_ops : 0 ≤ numOperations.val ∧ numOperations.val ≤ (nums.val.length : Int)), ∃ r : Std.I64,
      Aegis.MaxFrequency.max_frequency nums k numOperations = ok r ∧
      (∀ t : Int, score nums.val k.val numOperations.val t ≤ r.val) ∧
      (∃ t : Int, score nums.val k.val numOperations.val t = r.val)) := by
  sorry

/-- The function returns a result r for every input satisfying the constraints; it does not fail, panic, or overflow.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 10^5; for every i with 0 <= i < n, 1 <= nums[i] <= 10^9; 0 <= k <= 10^9; and 0 <= numOperations <= n. -/
theorem spec_2 (nums : Slice Std.I64) (k numOperations : Std.I64)
    (h_len_pos : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000)
    (h_elems : ∀ i : Fin nums.val.length,
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 1000000000)
    (h_k : 0 ≤ k.val ∧ k.val ≤ 1000000000)
    (h_ops : 0 ≤ numOperations.val ∧ numOperations.val ≤ (nums.val.length : Int)) :
    ∃ r : Std.I64, Aegis.MaxFrequency.max_frequency nums k numOperations = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (k numOperations : Std.I64)
    (h_len_pos : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000)
    (h_elems : ∀ i : Fin nums.val.length,
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 1000000000)
    (h_k : 0 ≤ k.val ∧ k.val ≤ 1000000000)
    (h_ops : 0 ≤ numOperations.val ∧ numOperations.val ≤ (nums.val.length : Int)), ∃ r : Std.I64, Aegis.MaxFrequency.max_frequency nums k numOperations = ok r) := by
  sorry

/-- Whenever the function returns a result r, 1 <= r <= len(nums).
  Preconditions: Let n = len(nums). Assume 1 <= n <= 10^5; for every i with 0 <= i < n, 1 <= nums[i] <= 10^9; 0 <= k <= 10^9; and 0 <= numOperations <= n. -/
theorem spec_3 (nums : Slice Std.I64) (k numOperations : Std.I64)
    (h_len_pos : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000)
    (h_elems : ∀ i : Fin nums.val.length,
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 1000000000)
    (h_k : 0 ≤ k.val ∧ k.val ≤ 1000000000)
    (h_ops : 0 ≤ numOperations.val ∧ numOperations.val ≤ (nums.val.length : Int)) :
    ∀ r : Std.I64, Aegis.MaxFrequency.max_frequency nums k numOperations = ok r →
      1 ≤ r.val ∧ r.val ≤ (nums.val.length : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (k numOperations : Std.I64)
    (h_len_pos : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000)
    (h_elems : ∀ i : Fin nums.val.length,
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 1000000000)
    (h_k : 0 ≤ k.val ∧ k.val ≤ 1000000000)
    (h_ops : 0 ≤ numOperations.val ∧ numOperations.val ≤ (nums.val.length : Int)), ∀ r : Std.I64, Aegis.MaxFrequency.max_frequency nums k numOperations = ok r →
      1 ≤ r.val ∧ r.val ≤ (nums.val.length : Int)) := by
  sorry

/-- Whenever the function returns a result r, r >= M, where M = max_{t in Z} #{i | 0 <= i < n and nums[i] = t}.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 10^5; for every i with 0 <= i < n, 1 <= nums[i] <= 10^9; 0 <= k <= 10^9; and 0 <= numOperations <= n. -/
theorem spec_4 (nums : Slice Std.I64) (k numOperations : Std.I64)
    (h_len_pos : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000)
    (h_elems : ∀ i : Fin nums.val.length,
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 1000000000)
    (h_k : 0 ≤ k.val ∧ k.val ≤ 1000000000)
    (h_ops : 0 ≤ numOperations.val ∧ numOperations.val ≤ (nums.val.length : Int)) :
    ∀ r : Std.I64, Aegis.MaxFrequency.max_frequency nums k numOperations = ok r →
      ∀ t : Int, (countOfEq nums.val t : Int) ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (k numOperations : Std.I64)
    (h_len_pos : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000)
    (h_elems : ∀ i : Fin nums.val.length,
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 1000000000)
    (h_k : 0 ≤ k.val ∧ k.val ≤ 1000000000)
    (h_ops : 0 ≤ numOperations.val ∧ numOperations.val ≤ (nums.val.length : Int)), ∀ r : Std.I64, Aegis.MaxFrequency.max_frequency nums k numOperations = ok r →
      ∀ t : Int, (countOfEq nums.val t : Int) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= W, where W = max_{t in Z} #{i | 0 <= i < n and |nums[i] - t| <= k}.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 10^5; for every i with 0 <= i < n, 1 <= nums[i] <= 10^9; 0 <= k <= 10^9; and 0 <= numOperations <= n. -/
theorem spec_5 (nums : Slice Std.I64) (k numOperations : Std.I64)
    (h_len_pos : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000)
    (h_elems : ∀ i : Fin nums.val.length,
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 1000000000)
    (h_k : 0 ≤ k.val ∧ k.val ≤ 1000000000)
    (h_ops : 0 ≤ numOperations.val ∧ numOperations.val ≤ (nums.val.length : Int)) :
    ∀ r : Std.I64, Aegis.MaxFrequency.max_frequency nums k numOperations = ok r →
      ∃ t : Int, r.val ≤ (countOfClose nums.val k.val t : Int) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (k numOperations : Std.I64)
    (h_len_pos : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000)
    (h_elems : ∀ i : Fin nums.val.length,
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 1000000000)
    (h_k : 0 ≤ k.val ∧ k.val ≤ 1000000000)
    (h_ops : 0 ≤ numOperations.val ∧ numOperations.val ≤ (nums.val.length : Int)), ∀ r : Std.I64, Aegis.MaxFrequency.max_frequency nums k numOperations = ok r →
      ∃ t : Int, r.val ≤ (countOfClose nums.val k.val t : Int)) := by
  sorry

/-- Whenever the function returns a result r, there is a set S of exactly numOperations indices with 0 <= i < n, and for each i in S an integer d_i with -k <= d_i <= k, such that after defining final[i] = nums[i] + d_i for i in S and final[i] = nums[i] for i not in S, some integer t occurs exactly r times in final.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 10^5; for every i with 0 <= i < n, 1 <= nums[i] <= 10^9; 0 <= k <= 10^9; and 0 <= numOperations <= n. -/
theorem spec_6 (nums : Slice Std.I64) (k numOperations : Std.I64)
    (h_len_pos : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000)
    (h_elems : ∀ i : Fin nums.val.length,
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 1000000000)
    (h_k : 0 ≤ k.val ∧ k.val ≤ 1000000000)
    (h_ops : 0 ≤ numOperations.val ∧ numOperations.val ≤ (nums.val.length : Int)) :
    ∀ r : Std.I64, Aegis.MaxFrequency.max_frequency nums k numOperations = ok r →
      ∃ (S : Finset (Fin nums.val.length)) (d : Fin nums.val.length → Int),
        (S.card : Int) = numOperations.val ∧
        (∀ i, i ∈ S → -k.val ≤ d i ∧ d i ≤ k.val) ∧
        ∃ t : Int,
          ((Finset.univ.filter
            (fun i => finalValue nums.val S d i = t)).card : Int) = r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (k numOperations : Std.I64)
    (h_len_pos : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000)
    (h_elems : ∀ i : Fin nums.val.length,
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 1000000000)
    (h_k : 0 ≤ k.val ∧ k.val ≤ 1000000000)
    (h_ops : 0 ≤ numOperations.val ∧ numOperations.val ≤ (nums.val.length : Int)), ∀ r : Std.I64, Aegis.MaxFrequency.max_frequency nums k numOperations = ok r →
      ∃ (S : Finset (Fin nums.val.length)) (d : Fin nums.val.length → Int),
        (S.card : Int) = numOperations.val ∧
        (∀ i, i ∈ S → -k.val ≤ d i ∧ d i ≤ k.val) ∧
        ∃ t : Int,
          ((Finset.univ.filter
            (fun i => finalValue nums.val S d i = t)).card : Int) = r.val) := by
  sorry

/-- Whenever the function returns a result r, for every integer t, with E(t) = #{i | 0 <= i < n and nums[i] = t} and N(t) = #{i | 0 <= i < n and nums[i] != t and |nums[i] - t| <= k}, we have E(t) + min(numOperations, N(t)) <= r.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 10^5; for every i with 0 <= i < n, 1 <= nums[i] <= 10^9; 0 <= k <= 10^9; and 0 <= numOperations <= n. -/
theorem spec_7 (nums : Slice Std.I64) (k numOperations : Std.I64)
    (h_len_pos : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000)
    (h_elems : ∀ i : Fin nums.val.length,
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 1000000000)
    (h_k : 0 ≤ k.val ∧ k.val ≤ 1000000000)
    (h_ops : 0 ≤ numOperations.val ∧ numOperations.val ≤ (nums.val.length : Int)) :
    ∀ r : Std.I64, Aegis.MaxFrequency.max_frequency nums k numOperations = ok r →
      ∀ t : Int, score nums.val k.val numOperations.val t ≤ r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (k numOperations : Std.I64)
    (h_len_pos : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000)
    (h_elems : ∀ i : Fin nums.val.length,
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 1000000000)
    (h_k : 0 ≤ k.val ∧ k.val ≤ 1000000000)
    (h_ops : 0 ≤ numOperations.val ∧ numOperations.val ≤ (nums.val.length : Int)), ∀ r : Std.I64, Aegis.MaxFrequency.max_frequency nums k numOperations = ok r →
      ∀ t : Int, score nums.val k.val numOperations.val t ≤ r.val) := by
  sorry

/-- Whenever both calls return a result, r1 <= r2.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 10^5; for every i with 0 <= i < n, 1 <= nums[i] <= 10^9; and 0 <= k <= 10^9. Fix integers m1 and m2 with 0 <= m1 <= m2 <= n. Let r1 and r2 be the results returned by max_frequency(nums, k, m1) and max_frequency(nums, k, m2), respectively. -/
theorem spec_8 (nums : Slice Std.I64) (k m1 m2 : Std.I64)
    (h_len_pos : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000)
    (h_elems : ∀ i : Fin nums.val.length,
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 1000000000)
    (h_k : 0 ≤ k.val ∧ k.val ≤ 1000000000)
    (h_m1 : 0 ≤ m1.val)
    (h_m12 : m1.val ≤ m2.val)
    (h_m2 : m2.val ≤ (nums.val.length : Int)) :
    ∀ r1 r2 : Std.I64,
      Aegis.MaxFrequency.max_frequency nums k m1 = ok r1 →
      Aegis.MaxFrequency.max_frequency nums k m2 = ok r2 →
      r1.val ≤ r2.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (k m1 m2 : Std.I64)
    (h_len_pos : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000)
    (h_elems : ∀ i : Fin nums.val.length,
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 1000000000)
    (h_k : 0 ≤ k.val ∧ k.val ≤ 1000000000)
    (h_m1 : 0 ≤ m1.val)
    (h_m12 : m1.val ≤ m2.val)
    (h_m2 : m2.val ≤ (nums.val.length : Int)), ∀ r1 r2 : Std.I64,
      Aegis.MaxFrequency.max_frequency nums k m1 = ok r1 →
      Aegis.MaxFrequency.max_frequency nums k m2 = ok r2 →
      r1.val ≤ r2.val) := by
  sorry

end AegisSpec.MaxFrequency
