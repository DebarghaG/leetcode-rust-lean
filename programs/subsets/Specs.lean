import Aegis.Subsets.Code.Funs

/-!
# Specifications of `Aegis.Subsets.subsets`

LeetCode problem `subsets`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.Subsets

  def ivec (v : alloc.vec.Vec Std.I64) : List Int := v.val.map (fun x => x.val)

  def eset (v : alloc.vec.Vec Std.I64) : Finset Int := (ivec v).toFinset

  def iat (v : alloc.vec.Vec Std.I64) (j : Fin v.val.length) : Int := (v.val.get j).val

  def inums (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

  def uset (nums : Slice Std.I64) : Finset Int := (inums nums).toFinset

  /-- Whenever the function returns a result r, let n = len(nums) and U = { nums[i] | 0 <= i < n }. Then: (1) every entry v of r has pairwise distinct elements, and every element of v belongs to U; and (2) for every subset S of U, there is exactly one entry v of r such that the set of elements of v is S. The entries of r may be in any order, and the elements inside each entry v may be in any order.
    Preconditions: len(nums) >= 1 and len(nums) <= 10; for every i with 0 <= i < len(nums), -10 <= nums[i] <= 10; for every i and j with 0 <= i < j < len(nums), nums[i] != nums[j]. -/
  theorem spec_1 (nums : Slice Std.I64) (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 10)
      (h_range : ∀ i : Fin nums.val.length,
        -10 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10)
      (h_distinct : ∀ i j : Fin nums.val.length, i < j →
        (nums.val.get i).val ≠ (nums.val.get j).val)
      (h_ret : Aegis.Subsets.subsets nums = Result.ok r) :
      (∀ v ∈ r.val, (ivec v).Nodup ∧ eset v ⊆ uset nums) ∧
      (∀ S : Finset Int, S ⊆ uset nums →
        ∃! v : alloc.vec.Vec Std.I64, v ∈ r.val ∧ eset v = S) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
        (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 10)
        (h_range : ∀ i : Fin nums.val.length,
          -10 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10)
        (h_distinct : ∀ i j : Fin nums.val.length, i < j →
          (nums.val.get i).val ≠ (nums.val.get j).val)
        (h_ret : Aegis.Subsets.subsets nums = Result.ok r), (∀ v ∈ r.val, (ivec v).Nodup ∧ eset v ⊆ uset nums) ∧
        (∀ S : Finset Int, S ⊆ uset nums →
          ∃! v : alloc.vec.Vec Std.I64, v ∈ r.val ∧ eset v = S)) := by
    sorry

  /-- The function returns a result r (it does not fail).
    Preconditions: len(nums) >= 1 and len(nums) <= 10; for every i with 0 <= i < len(nums), -10 <= nums[i] <= 10; for every i and j with 0 <= i < j < len(nums), nums[i] != nums[j]. -/
  theorem spec_2 (nums : Slice Std.I64)
      (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 10)
      (h_range : ∀ i : Fin nums.val.length,
        -10 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10)
      (h_distinct : ∀ i j : Fin nums.val.length, i < j →
        (nums.val.get i).val ≠ (nums.val.get j).val) :
      ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
        Aegis.Subsets.subsets nums = Result.ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 10)
        (h_range : ∀ i : Fin nums.val.length,
          -10 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10)
        (h_distinct : ∀ i j : Fin nums.val.length, i < j →
          (nums.val.get i).val ≠ (nums.val.get j).val), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
          Aegis.Subsets.subsets nums = Result.ok r) := by
    sorry

  /-- Whenever the function returns a result r, let n = len(nums). Then len(r) = 2^n.
    Preconditions: len(nums) >= 1 and len(nums) <= 10; for every i with 0 <= i < len(nums), -10 <= nums[i] <= 10; for every i and j with 0 <= i < j < len(nums), nums[i] != nums[j]. -/
  theorem spec_3 (nums : Slice Std.I64) (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 10)
      (h_range : ∀ i : Fin nums.val.length,
        -10 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10)
      (h_distinct : ∀ i j : Fin nums.val.length, i < j →
        (nums.val.get i).val ≠ (nums.val.get j).val)
      (h_ret : Aegis.Subsets.subsets nums = Result.ok r) :
      r.val.length = 2 ^ nums.val.length := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
        (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 10)
        (h_range : ∀ i : Fin nums.val.length,
          -10 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10)
        (h_distinct : ∀ i j : Fin nums.val.length, i < j →
          (nums.val.get i).val ≠ (nums.val.get j).val)
        (h_ret : Aegis.Subsets.subsets nums = Result.ok r), r.val.length = 2 ^ nums.val.length) := by
    sorry

  /-- Whenever the function returns a result r, let n = len(nums). For every entry v of r, 0 <= len(v) <= n.
    Preconditions: len(nums) >= 1 and len(nums) <= 10; for every i with 0 <= i < len(nums), -10 <= nums[i] <= 10; for every i and j with 0 <= i < j < len(nums), nums[i] != nums[j]. -/
  theorem spec_4 (nums : Slice Std.I64) (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 10)
      (h_range : ∀ i : Fin nums.val.length,
        -10 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10)
      (h_distinct : ∀ i j : Fin nums.val.length, i < j →
        (nums.val.get i).val ≠ (nums.val.get j).val)
      (h_ret : Aegis.Subsets.subsets nums = Result.ok r) :
      ∀ v ∈ r.val, v.val.length ≤ nums.val.length := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
        (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 10)
        (h_range : ∀ i : Fin nums.val.length,
          -10 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10)
        (h_distinct : ∀ i j : Fin nums.val.length, i < j →
          (nums.val.get i).val ≠ (nums.val.get j).val)
        (h_ret : Aegis.Subsets.subsets nums = Result.ok r), ∀ v ∈ r.val, v.val.length ≤ nums.val.length) := by
    sorry

  /-- Whenever the function returns a result r, let U = { nums[i] | 0 <= i < len(nums) }. For every entry v of r and every j with 0 <= j < len(v), v[j] belongs to U.
    Preconditions: len(nums) >= 1 and len(nums) <= 10; for every i with 0 <= i < len(nums), -10 <= nums[i] <= 10; for every i and j with 0 <= i < j < len(nums), nums[i] != nums[j]. -/
  theorem spec_5 (nums : Slice Std.I64) (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 10)
      (h_range : ∀ i : Fin nums.val.length,
        -10 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10)
      (h_distinct : ∀ i j : Fin nums.val.length, i < j →
        (nums.val.get i).val ≠ (nums.val.get j).val)
      (h_ret : Aegis.Subsets.subsets nums = Result.ok r) :
      ∀ v ∈ r.val, ∀ j : Fin v.val.length, iat v j ∈ uset nums := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
        (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 10)
        (h_range : ∀ i : Fin nums.val.length,
          -10 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10)
        (h_distinct : ∀ i j : Fin nums.val.length, i < j →
          (nums.val.get i).val ≠ (nums.val.get j).val)
        (h_ret : Aegis.Subsets.subsets nums = Result.ok r), ∀ v ∈ r.val, ∀ j : Fin v.val.length, iat v j ∈ uset nums) := by
    sorry

  /-- Whenever the function returns a result r, for every entry v of r, for every a and b with 0 <= a < b < len(v), v[a] != v[b].
    Preconditions: len(nums) >= 1 and len(nums) <= 10; for every i with 0 <= i < len(nums), -10 <= nums[i] <= 10; for every i and j with 0 <= i < j < len(nums), nums[i] != nums[j]. -/
  theorem spec_6 (nums : Slice Std.I64) (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 10)
      (h_range : ∀ i : Fin nums.val.length,
        -10 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10)
      (h_distinct : ∀ i j : Fin nums.val.length, i < j →
        (nums.val.get i).val ≠ (nums.val.get j).val)
      (h_ret : Aegis.Subsets.subsets nums = Result.ok r) :
      ∀ v ∈ r.val, ∀ a b : Fin v.val.length, a < b → iat v a ≠ iat v b := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
        (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 10)
        (h_range : ∀ i : Fin nums.val.length,
          -10 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10)
        (h_distinct : ∀ i j : Fin nums.val.length, i < j →
          (nums.val.get i).val ≠ (nums.val.get j).val)
        (h_ret : Aegis.Subsets.subsets nums = Result.ok r), ∀ v ∈ r.val, ∀ a b : Fin v.val.length, a < b → iat v a ≠ iat v b) := by
    sorry

  /-- Whenever the function returns a result r, for every i and j with 0 <= i < len(r) and 0 <= j < len(r), if the set of elements of r[i] equals the set of elements of r[j], then i = j.
    Preconditions: len(nums) >= 1 and len(nums) <= 10; for every i with 0 <= i < len(nums), -10 <= nums[i] <= 10; for every i and j with 0 <= i < j < len(nums), nums[i] != nums[j]. -/
  theorem spec_7 (nums : Slice Std.I64) (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 10)
      (h_range : ∀ i : Fin nums.val.length,
        -10 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10)
      (h_distinct : ∀ i j : Fin nums.val.length, i < j →
        (nums.val.get i).val ≠ (nums.val.get j).val)
      (h_ret : Aegis.Subsets.subsets nums = Result.ok r) :
      ∀ i j : Fin r.val.length,
        eset (r.val.get i) = eset (r.val.get j) → i = j := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
        (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 10)
        (h_range : ∀ i : Fin nums.val.length,
          -10 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10)
        (h_distinct : ∀ i j : Fin nums.val.length, i < j →
          (nums.val.get i).val ≠ (nums.val.get j).val)
        (h_ret : Aegis.Subsets.subsets nums = Result.ok r), ∀ i j : Fin r.val.length,
          eset (r.val.get i) = eset (r.val.get j) → i = j) := by
    sorry

  /-- Whenever the function returns a result r, let U = { nums[i] | 0 <= i < len(nums) }. For every subset S of U, there exists an entry v of r such that v has pairwise distinct elements and the set of elements of v is exactly S.
    Preconditions: len(nums) >= 1 and len(nums) <= 10; for every i with 0 <= i < len(nums), -10 <= nums[i] <= 10; for every i and j with 0 <= i < j < len(nums), nums[i] != nums[j]. -/
  theorem spec_8 (nums : Slice Std.I64) (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 10)
      (h_range : ∀ i : Fin nums.val.length,
        -10 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10)
      (h_distinct : ∀ i j : Fin nums.val.length, i < j →
        (nums.val.get i).val ≠ (nums.val.get j).val)
      (h_ret : Aegis.Subsets.subsets nums = Result.ok r) :
      ∀ S : Finset Int, S ⊆ uset nums →
        ∃ v ∈ r.val, (ivec v).Nodup ∧ eset v = S := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
        (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 10)
        (h_range : ∀ i : Fin nums.val.length,
          -10 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10)
        (h_distinct : ∀ i j : Fin nums.val.length, i < j →
          (nums.val.get i).val ≠ (nums.val.get j).val)
        (h_ret : Aegis.Subsets.subsets nums = Result.ok r), ∀ S : Finset Int, S ⊆ uset nums →
          ∃ v ∈ r.val, (ivec v).Nodup ∧ eset v = S) := by
    sorry

  /-- Whenever the function returns a result r, let U = { nums[i] | 0 <= i < len(nums) }. For every entry v of r, there exists an entry w of r such that w has pairwise distinct elements and the set of elements of w is U minus set(v).
    Preconditions: len(nums) >= 1 and len(nums) <= 10; for every i with 0 <= i < len(nums), -10 <= nums[i] <= 10; for every i and j with 0 <= i < j < len(nums), nums[i] != nums[j]. -/
  theorem spec_9 (nums : Slice Std.I64) (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 10)
      (h_range : ∀ i : Fin nums.val.length,
        -10 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10)
      (h_distinct : ∀ i j : Fin nums.val.length, i < j →
        (nums.val.get i).val ≠ (nums.val.get j).val)
      (h_ret : Aegis.Subsets.subsets nums = Result.ok r) :
      ∀ v ∈ r.val,
        ∃ w ∈ r.val, (ivec w).Nodup ∧ eset w = uset nums \ eset v := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
        (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 10)
        (h_range : ∀ i : Fin nums.val.length,
          -10 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10)
        (h_distinct : ∀ i j : Fin nums.val.length, i < j →
          (nums.val.get i).val ≠ (nums.val.get j).val)
        (h_ret : Aegis.Subsets.subsets nums = Result.ok r), ∀ v ∈ r.val,
          ∃ w ∈ r.val, (ivec w).Nodup ∧ eset w = uset nums \ eset v) := by
    sorry

  /-- Whenever the function returns a result r, let n = len(nums). For every k with 0 <= k <= n, the number of indices i with 0 <= i < len(r) and len(r[i]) = k is exactly C(n, k), where C(n, k) = n! / (k! * (n-k)!).
    Preconditions: len(nums) >= 1 and len(nums) <= 10; for every i with 0 <= i < len(nums), -10 <= nums[i] <= 10; for every i and j with 0 <= i < j < len(nums), nums[i] != nums[j]. -/
  theorem spec_10 (nums : Slice Std.I64) (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 10)
      (h_range : ∀ i : Fin nums.val.length,
        -10 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10)
      (h_distinct : ∀ i j : Fin nums.val.length, i < j →
        (nums.val.get i).val ≠ (nums.val.get j).val)
      (h_ret : Aegis.Subsets.subsets nums = Result.ok r) :
      ∀ k : ℕ, k ≤ nums.val.length →
        (r.val.filter (fun v => v.val.length = k)).length
          = nums.val.length.choose k := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
        (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 10)
        (h_range : ∀ i : Fin nums.val.length,
          -10 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10)
        (h_distinct : ∀ i j : Fin nums.val.length, i < j →
          (nums.val.get i).val ≠ (nums.val.get j).val)
        (h_ret : Aegis.Subsets.subsets nums = Result.ok r), ∀ k : ℕ, k ≤ nums.val.length →
          (r.val.filter (fun v => v.val.length = k)).length
            = nums.val.length.choose k) := by
    sorry

  /-- Whenever the function returns a result r, let U = { nums[i] | 0 <= i < len(nums) }. For every entry v of r, let S be the set of elements of v. The number of entries w of r such that the set of elements of w is a subset of S is exactly 2^{|S|}.
    Preconditions: len(nums) >= 1 and len(nums) <= 10; for every i with 0 <= i < len(nums), -10 <= nums[i] <= 10; for every i and j with 0 <= i < j < len(nums), nums[i] != nums[j]. -/
  theorem spec_11 (nums : Slice Std.I64) (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 10)
      (h_range : ∀ i : Fin nums.val.length,
        -10 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10)
      (h_distinct : ∀ i j : Fin nums.val.length, i < j →
        (nums.val.get i).val ≠ (nums.val.get j).val)
      (h_ret : Aegis.Subsets.subsets nums = Result.ok r) :
      ∀ v ∈ r.val,
        (r.val.filter (fun w => eset w ⊆ eset v)).length = 2 ^ (eset v).card := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
        (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 10)
        (h_range : ∀ i : Fin nums.val.length,
          -10 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10)
        (h_distinct : ∀ i j : Fin nums.val.length, i < j →
          (nums.val.get i).val ≠ (nums.val.get j).val)
        (h_ret : Aegis.Subsets.subsets nums = Result.ok r), ∀ v ∈ r.val,
          (r.val.filter (fun w => eset w ⊆ eset v)).length = 2 ^ (eset v).card) := by
    sorry

  end AegisSpec.Subsets
