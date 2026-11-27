import Aegis.MinOperations.Code.Funs

/-!
# Specifications of `Aegis.MinOperations.min_operations`

LeetCode problem `minimum-operations-to-collect-elements`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinOperations

  def size (nums : Slice Std.I64) : ℤ := (nums.val.length : ℤ)

  def elem (nums : Slice Std.I64) (i : ℤ) : ℤ :=
    ((nums.val[i.toNat]?).map (fun x => x.val)).getD 0

  def occurs (nums : Slice Std.I64) (v : ℤ) : Prop :=
    ∃ i : ℤ, 0 ≤ i ∧ i < size nums ∧ elem nums i = v

  def lastOcc (nums : Slice Std.I64) (v : ℤ) : ℕ :=
    ((List.range nums.val.length).filter (fun i : ℕ => decide (elem nums (i : ℤ) = v))).foldr max 0

  def minLastOcc (nums : Slice Std.I64) (k : ℤ) : ℕ :=
    ((List.range k.toNat).map (fun j => lastOcc nums ((j : ℤ) + 1))).foldr min
      (lastOcc nums 1)

  theorem elem_eq_getElem {nums : Slice Std.I64} {i : ℕ} (h : i < nums.val.length) :
      elem nums (i : ℤ) = (nums.val[i]).val := by
    have htoNat : ((i : ℤ)).toNat = i := Int.toNat_natCast i
    simp only [elem, htoNat, List.getElem?_eq_getElem h, Option.map_some, Option.getD_some]

  private theorem list_le_foldr_max : ∀ (l : List ℕ) (a : ℕ), a ∈ l → a ≤ l.foldr max 0
    | [], _, ha => absurd ha (by simp)
    | b :: t, a, ha => by
        rw [List.foldr_cons]
        rcases List.mem_cons.1 ha with rfl | ha
        · exact le_max_left _ _
        · exact le_trans (list_le_foldr_max t a ha) (le_max_right _ _)

  private theorem foldr_max_mem : ∀ (l : List ℕ), l ≠ [] → l.foldr max 0 ∈ l
    | [], h => absurd rfl h
    | [_], _ => by simp
    | b :: c :: t, _ => by
        rw [List.foldr_cons]
        have hmem : (c :: t).foldr max 0 ∈ c :: t := foldr_max_mem (c :: t) (by simp)
        rcases le_total b ((c :: t).foldr max 0) with hle | hle
        · rw [max_eq_right hle]
          exact List.mem_cons_of_mem b hmem
        · rw [max_eq_left hle]
          exact List.mem_cons_self

  theorem lastOcc_eq (nums : Slice Std.I64) (v : ℤ) (h : occurs nums v) :
      (lastOcc nums v : ℤ) < size nums ∧ elem nums (lastOcc nums v : ℤ) = v ∧
        ∀ j : ℤ, (lastOcc nums v : ℤ) < j → j < size nums → elem nums j ≠ v := by
    obtain ⟨i0, hi0nn, hi0lt, hi0e⟩ := h
    have hi0lt' : i0 < (nums.val.length : ℤ) := hi0lt
    have htoNat : ((i0.toNat : ℕ) : ℤ) = i0 := Int.toNat_of_nonneg hi0nn
    have hmem : i0.toNat ∈
        (List.range nums.val.length).filter (fun i : ℕ => decide (elem nums (i : ℤ) = v)) := by
      rw [List.mem_filter]
      refine ⟨?_, ?_⟩
      · rw [List.mem_range]; omega
      · rw [decide_eq_true_eq]; rwa [htoNat]
    have hne : (List.range nums.val.length).filter
        (fun i : ℕ => decide (elem nums (i : ℤ) = v)) ≠ [] := by
      intro h'
      rw [h'] at hmem
      exact absurd hmem (by simp)
    have hm_mem : lastOcc nums v ∈
        (List.range nums.val.length).filter (fun i : ℕ => decide (elem nums (i : ℤ) = v)) := by
      rw [lastOcc]
      exact foldr_max_mem _ hne
    obtain ⟨hm_range, hm_eq⟩ := List.mem_filter.1 hm_mem
    have hm_lt : (lastOcc nums v : ℤ) < size nums := by
      have hlen : lastOcc nums v < nums.val.length := by
        have := hm_range; rwa [List.mem_range] at this
      have : (lastOcc nums v : ℤ) < (nums.val.length : ℤ) := by omega
      exact this
    have hm_e : elem nums (lastOcc nums v : ℤ) = v := by
      rw [decide_eq_true_eq] at hm_eq; exact hm_eq
    refine ⟨hm_lt, hm_e, ?_⟩
    intro j hj hjlt hej
    have hjlt' : j < (nums.val.length : ℤ) := hjlt
    have hj_nonneg : 0 ≤ j := by
      have : (0 : ℤ) ≤ (lastOcc nums v : ℤ) := Int.natCast_nonneg _
      omega
    have hj_nat : ((j.toNat : ℕ) : ℤ) = j := Int.toNat_of_nonneg hj_nonneg
    have hj_mem : j.toNat ∈
        (List.range nums.val.length).filter (fun i : ℕ => decide (elem nums (i : ℤ) = v)) := by
      rw [List.mem_filter]
      refine ⟨?_, ?_⟩
      · rw [List.mem_range]; omega
      · rw [decide_eq_true_eq]; rwa [hj_nat]
    have hle : j.toNat ≤ lastOcc nums v := by
      rw [lastOcc]
      exact list_le_foldr_max _ _ hj_mem
    omega

  /-- The function returns a result r such that 0 <= r <= n and: (1) the suffix of length r contains every required value, i.e. for every v with 1 <= v <= k there exists i with n - r <= i < n and nums[i] = v; (2) no shorter suffix contains all required values, i.e. for every t with 0 <= t < r there exists v with 1 <= v <= k such that for every i with n - t <= i < n, nums[i] != v. Equivalently, r is exactly the minimum number of operations (successive removals of the last element) needed to have 1, 2, ..., k in the collection.
    Preconditions: Let n = len(nums). n >= 1, n <= 50, 1 <= k <= n, for every i with 0 <= i < n we have 1 <= nums[i] <= n, and for every v with 1 <= v <= k there exists i with 0 <= i < n and nums[i] = v. -/
  theorem spec_1 (nums : Slice Std.I64) (k : Std.I64)
      (h_len_ge_one : 1 ≤ size nums) (h_len_le_fifty : size nums ≤ 50)
      (h_k_ge_one : 1 ≤ k.val) (h_k_le_len : k.val ≤ size nums)
      (h_entries_bounded :
        ∀ i : ℤ, 0 ≤ i → i < size nums → 1 ≤ elem nums i ∧ elem nums i ≤ size nums)
      (h_covers : ∀ v : ℤ, 1 ≤ v → v ≤ k.val → occurs nums v) :
      ∃ r : Std.I64, Aegis.MinOperations.min_operations nums k = ok r ∧
        0 ≤ r.val ∧ r.val ≤ size nums ∧
        (∀ v : ℤ, 1 ≤ v → v ≤ k.val →
          ∃ i : ℤ, size nums - r.val ≤ i ∧ i < size nums ∧ elem nums i = v) ∧
        (∀ t : ℤ, 0 ≤ t → t < r.val →
          ∃ v : ℤ, 1 ≤ v ∧ v ≤ k.val ∧
            ∀ i : ℤ, size nums - t ≤ i → i < size nums → elem nums i ≠ v) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (h_len_ge_one : 1 ≤ size nums) (h_len_le_fifty : size nums ≤ 50)
        (h_k_ge_one : 1 ≤ k.val) (h_k_le_len : k.val ≤ size nums)
        (h_entries_bounded :
          ∀ i : ℤ, 0 ≤ i → i < size nums → 1 ≤ elem nums i ∧ elem nums i ≤ size nums)
        (h_covers : ∀ v : ℤ, 1 ≤ v → v ≤ k.val → occurs nums v), ∃ r : Std.I64, Aegis.MinOperations.min_operations nums k = ok r ∧
          0 ≤ r.val ∧ r.val ≤ size nums ∧
          (∀ v : ℤ, 1 ≤ v → v ≤ k.val →
            ∃ i : ℤ, size nums - r.val ≤ i ∧ i < size nums ∧ elem nums i = v) ∧
          (∀ t : ℤ, 0 ≤ t → t < r.val →
            ∃ v : ℤ, 1 ≤ v ∧ v ≤ k.val ∧
              ∀ i : ℤ, size nums - t ≤ i → i < size nums → elem nums i ≠ v)) := by
    sorry

  /-- The function returns a result r with 1 <= r <= n.
    Preconditions: Let n = len(nums). n >= 1, n <= 50, 1 <= k <= n, for every i with 0 <= i < n we have 1 <= nums[i] <= n, and for every v with 1 <= v <= k there exists i with 0 <= i < n and nums[i] = v. -/
  theorem spec_2 (nums : Slice Std.I64) (k : Std.I64)
      (h_len_ge_one : 1 ≤ size nums) (h_len_le_fifty : size nums ≤ 50)
      (h_k_ge_one : 1 ≤ k.val) (h_k_le_len : k.val ≤ size nums)
      (h_entries_bounded :
        ∀ i : ℤ, 0 ≤ i → i < size nums → 1 ≤ elem nums i ∧ elem nums i ≤ size nums)
      (h_covers : ∀ v : ℤ, 1 ≤ v → v ≤ k.val → occurs nums v) :
      ∃ r : Std.I64, Aegis.MinOperations.min_operations nums k = ok r ∧
        1 ≤ r.val ∧ r.val ≤ size nums := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (h_len_ge_one : 1 ≤ size nums) (h_len_le_fifty : size nums ≤ 50)
        (h_k_ge_one : 1 ≤ k.val) (h_k_le_len : k.val ≤ size nums)
        (h_entries_bounded :
          ∀ i : ℤ, 0 ≤ i → i < size nums → 1 ≤ elem nums i ∧ elem nums i ≤ size nums)
        (h_covers : ∀ v : ℤ, 1 ≤ v → v ≤ k.val → occurs nums v), ∃ r : Std.I64, Aegis.MinOperations.min_operations nums k = ok r ∧
          1 ≤ r.val ∧ r.val ≤ size nums) := by
    sorry

  /-- Whenever the function returns a result r, the suffix of length r contains every v with 1 <= v <= k: for every v with 1 <= v <= k there exists i with n - r <= i < n and nums[i] = v.
    Preconditions: Let n = len(nums). n >= 1, n <= 50, 1 <= k <= n, for every i with 0 <= i < n we have 1 <= nums[i] <= n, and for every v with 1 <= v <= k there exists i with 0 <= i < n and nums[i] = v. -/
  theorem spec_3 (nums : Slice Std.I64) (k : Std.I64)
      (h_len_ge_one : 1 ≤ size nums) (h_len_le_fifty : size nums ≤ 50)
      (h_k_ge_one : 1 ≤ k.val) (h_k_le_len : k.val ≤ size nums)
      (h_entries_bounded :
        ∀ i : ℤ, 0 ≤ i → i < size nums → 1 ≤ elem nums i ∧ elem nums i ≤ size nums)
      (h_covers : ∀ v : ℤ, 1 ≤ v → v ≤ k.val → occurs nums v) :
      ∀ r : Std.I64, Aegis.MinOperations.min_operations nums k = ok r →
        ∀ v : ℤ, 1 ≤ v → v ≤ k.val →
          ∃ i : ℤ, size nums - r.val ≤ i ∧ i < size nums ∧ elem nums i = v := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (h_len_ge_one : 1 ≤ size nums) (h_len_le_fifty : size nums ≤ 50)
        (h_k_ge_one : 1 ≤ k.val) (h_k_le_len : k.val ≤ size nums)
        (h_entries_bounded :
          ∀ i : ℤ, 0 ≤ i → i < size nums → 1 ≤ elem nums i ∧ elem nums i ≤ size nums)
        (h_covers : ∀ v : ℤ, 1 ≤ v → v ≤ k.val → occurs nums v), ∀ r : Std.I64, Aegis.MinOperations.min_operations nums k = ok r →
          ∀ v : ℤ, 1 ≤ v → v ≤ k.val →
            ∃ i : ℤ, size nums - r.val ≤ i ∧ i < size nums ∧ elem nums i = v) := by
    sorry

  /-- Whenever the function returns a result r, for every t with 0 <= t < r the suffix of length t is missing at least one required value: there exists v with 1 <= v <= k such that for every i with n - t <= i < n, nums[i] != v.
    Preconditions: Let n = len(nums). n >= 1, n <= 50, 1 <= k <= n, for every i with 0 <= i < n we have 1 <= nums[i] <= n, and for every v with 1 <= v <= k there exists i with 0 <= i < n and nums[i] = v. -/
  theorem spec_4 (nums : Slice Std.I64) (k : Std.I64)
      (h_len_ge_one : 1 ≤ size nums) (h_len_le_fifty : size nums ≤ 50)
      (h_k_ge_one : 1 ≤ k.val) (h_k_le_len : k.val ≤ size nums)
      (h_entries_bounded :
        ∀ i : ℤ, 0 ≤ i → i < size nums → 1 ≤ elem nums i ∧ elem nums i ≤ size nums)
      (h_covers : ∀ v : ℤ, 1 ≤ v → v ≤ k.val → occurs nums v) :
      ∀ r : Std.I64, Aegis.MinOperations.min_operations nums k = ok r →
        ∀ t : ℤ, 0 ≤ t → t < r.val →
          ∃ v : ℤ, 1 ≤ v ∧ v ≤ k.val ∧
            ∀ i : ℤ, size nums - t ≤ i → i < size nums → elem nums i ≠ v := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (h_len_ge_one : 1 ≤ size nums) (h_len_le_fifty : size nums ≤ 50)
        (h_k_ge_one : 1 ≤ k.val) (h_k_le_len : k.val ≤ size nums)
        (h_entries_bounded :
          ∀ i : ℤ, 0 ≤ i → i < size nums → 1 ≤ elem nums i ∧ elem nums i ≤ size nums)
        (h_covers : ∀ v : ℤ, 1 ≤ v → v ≤ k.val → occurs nums v), ∀ r : Std.I64, Aegis.MinOperations.min_operations nums k = ok r →
          ∀ t : ℤ, 0 ≤ t → t < r.val →
            ∃ v : ℤ, 1 ≤ v ∧ v ≤ k.val ∧
              ∀ i : ℤ, size nums - t ≤ i → i < size nums → elem nums i ≠ v) := by
    sorry

  /-- Whenever the function returns a result r, let s = n - r. Then s is a valid index (0 <= s < n), nums[s] is a required value (1 <= nums[s] <= k), and this value does not occur after s: for every i with s < i < n, nums[i] != nums[s].
    Preconditions: Let n = len(nums). n >= 1, n <= 50, 1 <= k <= n, for every i with 0 <= i < n we have 1 <= nums[i] <= n, and for every v with 1 <= v <= k there exists i with 0 <= i < n and nums[i] = v. -/
  theorem spec_5 (nums : Slice Std.I64) (k : Std.I64)
      (h_len_ge_one : 1 ≤ size nums) (h_len_le_fifty : size nums ≤ 50)
      (h_k_ge_one : 1 ≤ k.val) (h_k_le_len : k.val ≤ size nums)
      (h_entries_bounded :
        ∀ i : ℤ, 0 ≤ i → i < size nums → 1 ≤ elem nums i ∧ elem nums i ≤ size nums)
      (h_covers : ∀ v : ℤ, 1 ≤ v → v ≤ k.val → occurs nums v) :
      ∀ r : Std.I64, Aegis.MinOperations.min_operations nums k = ok r →
        0 ≤ size nums - r.val ∧ size nums - r.val < size nums ∧
        1 ≤ elem nums (size nums - r.val) ∧ elem nums (size nums - r.val) ≤ k.val ∧
        (∀ i : ℤ, size nums - r.val < i → i < size nums →
          elem nums i ≠ elem nums (size nums - r.val)) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (h_len_ge_one : 1 ≤ size nums) (h_len_le_fifty : size nums ≤ 50)
        (h_k_ge_one : 1 ≤ k.val) (h_k_le_len : k.val ≤ size nums)
        (h_entries_bounded :
          ∀ i : ℤ, 0 ≤ i → i < size nums → 1 ≤ elem nums i ∧ elem nums i ≤ size nums)
        (h_covers : ∀ v : ℤ, 1 ≤ v → v ≤ k.val → occurs nums v), ∀ r : Std.I64, Aegis.MinOperations.min_operations nums k = ok r →
          0 ≤ size nums - r.val ∧ size nums - r.val < size nums ∧
          1 ≤ elem nums (size nums - r.val) ∧ elem nums (size nums - r.val) ≤ k.val ∧
          (∀ i : ℤ, size nums - r.val < i → i < size nums →
            elem nums i ≠ elem nums (size nums - r.val))) := by
    sorry

  /-- Whenever the function returns a result r, for every v with 1 <= v <= k, let L(v) be the largest index i with nums[i] = v (it exists by the guarantee). Then r >= n - L(v).
    Preconditions: Let n = len(nums). n >= 1, n <= 50, 1 <= k <= n, for every i with 0 <= i < n we have 1 <= nums[i] <= n, and for every v with 1 <= v <= k there exists i with 0 <= i < n and nums[i] = v. -/
  theorem spec_6 (nums : Slice Std.I64) (k : Std.I64)
      (h_len_ge_one : 1 ≤ size nums) (h_len_le_fifty : size nums ≤ 50)
      (h_k_ge_one : 1 ≤ k.val) (h_k_le_len : k.val ≤ size nums)
      (h_entries_bounded :
        ∀ i : ℤ, 0 ≤ i → i < size nums → 1 ≤ elem nums i ∧ elem nums i ≤ size nums)
      (h_covers : ∀ v : ℤ, 1 ≤ v → v ≤ k.val → occurs nums v) :
      ∀ r : Std.I64, Aegis.MinOperations.min_operations nums k = ok r →
        ∀ v : ℤ, 1 ≤ v → v ≤ k.val →
          size nums - (lastOcc nums v : ℤ) ≤ r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (h_len_ge_one : 1 ≤ size nums) (h_len_le_fifty : size nums ≤ 50)
        (h_k_ge_one : 1 ≤ k.val) (h_k_le_len : k.val ≤ size nums)
        (h_entries_bounded :
          ∀ i : ℤ, 0 ≤ i → i < size nums → 1 ≤ elem nums i ∧ elem nums i ≤ size nums)
        (h_covers : ∀ v : ℤ, 1 ≤ v → v ≤ k.val → occurs nums v), ∀ r : Std.I64, Aegis.MinOperations.min_operations nums k = ok r →
          ∀ v : ℤ, 1 ≤ v → v ≤ k.val →
            size nums - (lastOcc nums v : ℤ) ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, let m = min { L(v) | 1 <= v <= k }, where L(v) is the largest index i with nums[i] = v. Then r <= n - m.
    Preconditions: Let n = len(nums). n >= 1, n <= 50, 1 <= k <= n, for every i with 0 <= i < n we have 1 <= nums[i] <= n, and for every v with 1 <= v <= k there exists i with 0 <= i < n and nums[i] = v. -/
  theorem spec_7 (nums : Slice Std.I64) (k : Std.I64)
      (h_len_ge_one : 1 ≤ size nums) (h_len_le_fifty : size nums ≤ 50)
      (h_k_ge_one : 1 ≤ k.val) (h_k_le_len : k.val ≤ size nums)
      (h_entries_bounded :
        ∀ i : ℤ, 0 ≤ i → i < size nums → 1 ≤ elem nums i ∧ elem nums i ≤ size nums)
      (h_covers : ∀ v : ℤ, 1 ≤ v → v ≤ k.val → occurs nums v) :
      ∀ r : Std.I64, Aegis.MinOperations.min_operations nums k = ok r →
        r.val ≤ size nums - (minLastOcc nums k.val : ℤ) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (h_len_ge_one : 1 ≤ size nums) (h_len_le_fifty : size nums ≤ 50)
        (h_k_ge_one : 1 ≤ k.val) (h_k_le_len : k.val ≤ size nums)
        (h_entries_bounded :
          ∀ i : ℤ, 0 ≤ i → i < size nums → 1 ≤ elem nums i ∧ elem nums i ≤ size nums)
        (h_covers : ∀ v : ℤ, 1 ≤ v → v ≤ k.val → occurs nums v), ∀ r : Std.I64, Aegis.MinOperations.min_operations nums k = ok r →
          r.val ≤ size nums - (minLastOcc nums k.val : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, r = 1 if and only if k = 1 and nums[n - 1] = 1.
    Preconditions: Let n = len(nums). n >= 1, n <= 50, 1 <= k <= n, for every i with 0 <= i < n we have 1 <= nums[i] <= n, and for every v with 1 <= v <= k there exists i with 0 <= i < n and nums[i] = v. -/
  theorem spec_8 (nums : Slice Std.I64) (k : Std.I64)
      (h_len_ge_one : 1 ≤ size nums) (h_len_le_fifty : size nums ≤ 50)
      (h_k_ge_one : 1 ≤ k.val) (h_k_le_len : k.val ≤ size nums)
      (h_entries_bounded :
        ∀ i : ℤ, 0 ≤ i → i < size nums → 1 ≤ elem nums i ∧ elem nums i ≤ size nums)
      (h_covers : ∀ v : ℤ, 1 ≤ v → v ≤ k.val → occurs nums v) :
      ∀ r : Std.I64, Aegis.MinOperations.min_operations nums k = ok r →
        (r.val = 1 ↔ k.val = 1 ∧ elem nums (size nums - 1) = 1) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (h_len_ge_one : 1 ≤ size nums) (h_len_le_fifty : size nums ≤ 50)
        (h_k_ge_one : 1 ≤ k.val) (h_k_le_len : k.val ≤ size nums)
        (h_entries_bounded :
          ∀ i : ℤ, 0 ≤ i → i < size nums → 1 ≤ elem nums i ∧ elem nums i ≤ size nums)
        (h_covers : ∀ v : ℤ, 1 ≤ v → v ≤ k.val → occurs nums v), ∀ r : Std.I64, Aegis.MinOperations.min_operations nums k = ok r →
          (r.val = 1 ↔ k.val = 1 ∧ elem nums (size nums - 1) = 1)) := by
    sorry

  /-- Whenever the function returns a result r, r = n if and only if nums[0] is a required value (1 <= nums[0] <= k) and it occurs nowhere else: for every i with 0 < i < n, nums[i] != nums[0].
    Preconditions: Let n = len(nums). n >= 1, n <= 50, 1 <= k <= n, for every i with 0 <= i < n we have 1 <= nums[i] <= n, and for every v with 1 <= v <= k there exists i with 0 <= i < n and nums[i] = v. -/
  theorem spec_9 (nums : Slice Std.I64) (k : Std.I64)
      (h_len_ge_one : 1 ≤ size nums) (h_len_le_fifty : size nums ≤ 50)
      (h_k_ge_one : 1 ≤ k.val) (h_k_le_len : k.val ≤ size nums)
      (h_entries_bounded :
        ∀ i : ℤ, 0 ≤ i → i < size nums → 1 ≤ elem nums i ∧ elem nums i ≤ size nums)
      (h_covers : ∀ v : ℤ, 1 ≤ v → v ≤ k.val → occurs nums v) :
      ∀ r : Std.I64, Aegis.MinOperations.min_operations nums k = ok r →
        (r.val = size nums ↔
          (1 ≤ elem nums 0 ∧ elem nums 0 ≤ k.val) ∧
            ∀ i : ℤ, 0 < i → i < size nums → elem nums i ≠ elem nums 0) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (h_len_ge_one : 1 ≤ size nums) (h_len_le_fifty : size nums ≤ 50)
        (h_k_ge_one : 1 ≤ k.val) (h_k_le_len : k.val ≤ size nums)
        (h_entries_bounded :
          ∀ i : ℤ, 0 ≤ i → i < size nums → 1 ≤ elem nums i ∧ elem nums i ≤ size nums)
        (h_covers : ∀ v : ℤ, 1 ≤ v → v ≤ k.val → occurs nums v), ∀ r : Std.I64, Aegis.MinOperations.min_operations nums k = ok r →
          (r.val = size nums ↔
            (1 ≤ elem nums 0 ∧ elem nums 0 ≤ k.val) ∧
              ∀ i : ℤ, 0 < i → i < size nums → elem nums i ≠ elem nums 0)) := by
    sorry

  /-- Whenever the function returns a result r, for every index i with 0 <= i < n - r, if nums[i] is a required value (1 <= nums[i] <= k), then nums[i] occurs again later: there exists j with i < j < n and nums[j] = nums[i].
    Preconditions: Let n = len(nums). n >= 1, n <= 50, 1 <= k <= n, for every i with 0 <= i < n we have 1 <= nums[i] <= n, and for every v with 1 <= v <= k there exists i with 0 <= i < n and nums[i] = v. -/
  theorem spec_10 (nums : Slice Std.I64) (k : Std.I64)
      (h_len_ge_one : 1 ≤ size nums) (h_len_le_fifty : size nums ≤ 50)
      (h_k_ge_one : 1 ≤ k.val) (h_k_le_len : k.val ≤ size nums)
      (h_entries_bounded :
        ∀ i : ℤ, 0 ≤ i → i < size nums → 1 ≤ elem nums i ∧ elem nums i ≤ size nums)
      (h_covers : ∀ v : ℤ, 1 ≤ v → v ≤ k.val → occurs nums v) :
      ∀ r : Std.I64, Aegis.MinOperations.min_operations nums k = ok r →
        ∀ i : ℤ, 0 ≤ i → i < size nums - r.val →
          (1 ≤ elem nums i ∧ elem nums i ≤ k.val) →
            ∃ j : ℤ, i < j ∧ j < size nums ∧ elem nums j = elem nums i := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (h_len_ge_one : 1 ≤ size nums) (h_len_le_fifty : size nums ≤ 50)
        (h_k_ge_one : 1 ≤ k.val) (h_k_le_len : k.val ≤ size nums)
        (h_entries_bounded :
          ∀ i : ℤ, 0 ≤ i → i < size nums → 1 ≤ elem nums i ∧ elem nums i ≤ size nums)
        (h_covers : ∀ v : ℤ, 1 ≤ v → v ≤ k.val → occurs nums v), ∀ r : Std.I64, Aegis.MinOperations.min_operations nums k = ok r →
          ∀ i : ℤ, 0 ≤ i → i < size nums - r.val →
            (1 ≤ elem nums i ∧ elem nums i ≤ k.val) →
              ∃ j : ℤ, i < j ∧ j < size nums ∧ elem nums j = elem nums i) := by
    sorry

  /-- The function returns a result r and does not fail: no panic, out-of-bounds access, or arithmetic overflow occurs.
    Preconditions: Let n = len(nums). n >= 1, n <= 50, 1 <= k <= n, for every i with 0 <= i < n we have 1 <= nums[i] <= n, and for every v with 1 <= v <= k there exists i with 0 <= i < n and nums[i] = v. -/
  theorem spec_11 (nums : Slice Std.I64) (k : Std.I64)
      (h_len_ge_one : 1 ≤ size nums) (h_len_le_fifty : size nums ≤ 50)
      (h_k_ge_one : 1 ≤ k.val) (h_k_le_len : k.val ≤ size nums)
      (h_entries_bounded :
        ∀ i : ℤ, 0 ≤ i → i < size nums → 1 ≤ elem nums i ∧ elem nums i ≤ size nums)
      (h_covers : ∀ v : ℤ, 1 ≤ v → v ≤ k.val → occurs nums v) :
      ∃ r : Std.I64, Aegis.MinOperations.min_operations nums k = ok r := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (h_len_ge_one : 1 ≤ size nums) (h_len_le_fifty : size nums ≤ 50)
        (h_k_ge_one : 1 ≤ k.val) (h_k_le_len : k.val ≤ size nums)
        (h_entries_bounded :
          ∀ i : ℤ, 0 ≤ i → i < size nums → 1 ≤ elem nums i ∧ elem nums i ≤ size nums)
        (h_covers : ∀ v : ℤ, 1 ≤ v → v ≤ k.val → occurs nums v), ∃ r : Std.I64, Aegis.MinOperations.min_operations nums k = ok r) := by
    sorry

  end AegisSpec.MinOperations
