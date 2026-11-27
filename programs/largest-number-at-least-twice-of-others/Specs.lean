import Aegis.DominantIndex.Code.Funs

/-!
# Specifications of `Aegis.DominantIndex.dominant_index`

LeetCode problem `largest-number-at-least-twice-of-others`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.DominantIndex

  def atv (nums : Slice Std.I64) (i : ℕ) : ℤ :=
    ((nums.val[i]?).map (fun v : Std.I64 => v.val)).getD 0

  def atInt (nums : Slice Std.I64) (k : ℤ) : ℤ :=
    if 0 ≤ k then atv nums k.toNat else 0

  def IsStrictMax (nums : Slice Std.I64) (m : ℕ) : Prop :=
    m < nums.val.length ∧ ∀ (i : ℕ), i < nums.val.length → i ≠ m → atv nums i < atv nums m

  def IsDominant (nums : Slice Std.I64) (j : ℕ) : Prop :=
    j < nums.val.length ∧
      (∀ (i : ℕ), i < nums.val.length → i ≠ j → atv nums i < atv nums j) ∧
      (∀ (i : ℕ), i < nums.val.length → i ≠ j → 2 * atv nums i ≤ atv nums j)

  def HasDoubleOther (nums : Slice Std.I64) (m : ℕ) : Prop :=
    ∃ (i : ℕ), i < nums.val.length ∧ i ≠ m ∧ atv nums m < 2 * atv nums i

  @[simp]
  theorem atv_of_lt (nums : Slice Std.I64) {i : ℕ} (h : i < nums.val.length) :
      atv nums i = (nums.val[i]).val := by
    simp [atv, List.getElem?_eq_getElem h]

  theorem IsStrictMax.unique {nums : Slice Std.I64} {m₁ m₂ : ℕ}
      (h₁ : IsStrictMax nums m₁) (h₂ : IsStrictMax nums m₂) : m₁ = m₂ := by
    obtain ⟨hm₁, hmax₁⟩ := h₁
    obtain ⟨hm₂, hmax₂⟩ := h₂
    by_contra hne
    have hlt₁ : atv nums m₁ < atv nums m₂ := hmax₂ m₁ hm₁ (by omega)
    have hlt₂ : atv nums m₂ < atv nums m₁ := hmax₁ m₂ hm₂ (by omega)
    omega

  /-- The function returns a result r and the following holds. If there exists an index j with 0 <= j < len(nums) such that (i) nums[j] > nums[i] for every i with 0 <= i < len(nums) and i != j, and (ii) 2 * nums[i] <= nums[j] for every i with 0 <= i < len(nums) and i != j, then r = j. Otherwise r = -1.
    Preconditions: 2 <= len(nums) <= 50; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100; and the largest value in nums is unique, i.e. there exists exactly one index m with 0 <= m < len(nums) and, for every i with 0 <= i < len(nums) and i != m, nums[i] < nums[m]. -/
  theorem spec_1 (nums : Slice Std.I64)
      (h_len_lo : 2 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 50)
      (h_range : ∀ (i : ℕ), i < nums.val.length → 0 ≤ atv nums i ∧ atv nums i ≤ 100)
      (h_max : ∃! m, IsStrictMax nums m) :
      ∃ r, Aegis.DominantIndex.dominant_index nums = ok r ∧
        ((∃ j, IsDominant nums j) →
          ∀ j, IsDominant nums j → r.val = (j : ℤ)) ∧
        (¬ (∃ j, IsDominant nums j) → r.val = -1) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len_lo : 2 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 50)
        (h_range : ∀ (i : ℕ), i < nums.val.length → 0 ≤ atv nums i ∧ atv nums i ≤ 100)
        (h_max : ∃! m, IsStrictMax nums m), ∃ r, Aegis.DominantIndex.dominant_index nums = ok r ∧
          ((∃ j, IsDominant nums j) →
            ∀ j, IsDominant nums j → r.val = (j : ℤ)) ∧
          (¬ (∃ j, IsDominant nums j) → r.val = -1)) := by
    sorry

  /-- The function returns a result r; it does not fail, panic, overflow, or access an index outside the slice.
    Preconditions: 2 <= len(nums) <= 50; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100; and the largest value in nums is unique, i.e. there exists exactly one index m with 0 <= m < len(nums) and, for every i with 0 <= i < len(nums) and i != m, nums[i] < nums[m]. -/
  theorem spec_2 (nums : Slice Std.I64)
      (h_len_lo : 2 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 50)
      (h_range : ∀ (i : ℕ), i < nums.val.length → 0 ≤ atv nums i ∧ atv nums i ≤ 100)
      (h_max : ∃! m, IsStrictMax nums m) :
      ∃ r, Aegis.DominantIndex.dominant_index nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len_lo : 2 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 50)
        (h_range : ∀ (i : ℕ), i < nums.val.length → 0 ≤ atv nums i ∧ atv nums i ≤ 100)
        (h_max : ∃! m, IsStrictMax nums m), ∃ r, Aegis.DominantIndex.dominant_index nums = ok r) := by
    sorry

  /-- Whenever the function returns a result r, either r = -1 or 0 <= r < len(nums).
    Preconditions: 2 <= len(nums) <= 50; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100; and the largest value in nums is unique, i.e. there exists exactly one index m with 0 <= m < len(nums) and, for every i with 0 <= i < len(nums) and i != m, nums[i] < nums[m]. -/
  theorem spec_3 (nums : Slice Std.I64)
      (h_len_lo : 2 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 50)
      (h_range : ∀ (i : ℕ), i < nums.val.length → 0 ≤ atv nums i ∧ atv nums i ≤ 100)
      (h_max : ∃! m, IsStrictMax nums m) :
      ∀ r, Aegis.DominantIndex.dominant_index nums = ok r →
        r.val = -1 ∨ (0 ≤ r.val ∧ r.val < (nums.val.length : ℤ)) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len_lo : 2 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 50)
        (h_range : ∀ (i : ℕ), i < nums.val.length → 0 ≤ atv nums i ∧ atv nums i ≤ 100)
        (h_max : ∃! m, IsStrictMax nums m), ∀ r, Aegis.DominantIndex.dominant_index nums = ok r →
          r.val = -1 ∨ (0 ≤ r.val ∧ r.val < (nums.val.length : ℤ))) := by
    sorry

  /-- Whenever the function returns a result r with r >= 0, the value nums[r] is the largest value in nums: for every i with 0 <= i < len(nums), nums[i] <= nums[r].
    Preconditions: 2 <= len(nums) <= 50; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100; and the largest value in nums is unique, i.e. there exists exactly one index m with 0 <= m < len(nums) and, for every i with 0 <= i < len(nums) and i != m, nums[i] < nums[m]. -/
  theorem spec_4 (nums : Slice Std.I64)
      (h_len_lo : 2 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 50)
      (h_range : ∀ (i : ℕ), i < nums.val.length → 0 ≤ atv nums i ∧ atv nums i ≤ 100)
      (h_max : ∃! m, IsStrictMax nums m) :
      ∀ r, Aegis.DominantIndex.dominant_index nums = ok r → 0 ≤ r.val →
        ∀ (i : ℕ), i < nums.val.length → atv nums i ≤ atInt nums r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len_lo : 2 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 50)
        (h_range : ∀ (i : ℕ), i < nums.val.length → 0 ≤ atv nums i ∧ atv nums i ≤ 100)
        (h_max : ∃! m, IsStrictMax nums m), ∀ r, Aegis.DominantIndex.dominant_index nums = ok r → 0 ≤ r.val →
          ∀ (i : ℕ), i < nums.val.length → atv nums i ≤ atInt nums r.val) := by
    sorry

  /-- Whenever the function returns a result r with r >= 0, nums[r] is the unique largest value: for every i with 0 <= i < len(nums) and i != r, nums[i] < nums[r].
    Preconditions: 2 <= len(nums) <= 50; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100; and the largest value in nums is unique, i.e. there exists exactly one index m with 0 <= m < len(nums) and, for every i with 0 <= i < len(nums) and i != m, nums[i] < nums[m]. -/
  theorem spec_5 (nums : Slice Std.I64)
      (h_len_lo : 2 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 50)
      (h_range : ∀ (i : ℕ), i < nums.val.length → 0 ≤ atv nums i ∧ atv nums i ≤ 100)
      (h_max : ∃! m, IsStrictMax nums m) :
      ∀ r, Aegis.DominantIndex.dominant_index nums = ok r → 0 ≤ r.val →
        ∀ (i : ℕ), i < nums.val.length → (i : ℤ) ≠ r.val → atv nums i < atInt nums r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len_lo : 2 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 50)
        (h_range : ∀ (i : ℕ), i < nums.val.length → 0 ≤ atv nums i ∧ atv nums i ≤ 100)
        (h_max : ∃! m, IsStrictMax nums m), ∀ r, Aegis.DominantIndex.dominant_index nums = ok r → 0 ≤ r.val →
          ∀ (i : ℕ), i < nums.val.length → (i : ℤ) ≠ r.val → atv nums i < atInt nums r.val) := by
    sorry

  /-- Whenever the function returns a result r with r >= 0, nums[r] is at least twice every other element: for every i with 0 <= i < len(nums) and i != r, 2 * nums[i] <= nums[r].
    Preconditions: 2 <= len(nums) <= 50; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100; and the largest value in nums is unique, i.e. there exists exactly one index m with 0 <= m < len(nums) and, for every i with 0 <= i < len(nums) and i != m, nums[i] < nums[m]. -/
  theorem spec_6 (nums : Slice Std.I64)
      (h_len_lo : 2 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 50)
      (h_range : ∀ (i : ℕ), i < nums.val.length → 0 ≤ atv nums i ∧ atv nums i ≤ 100)
      (h_max : ∃! m, IsStrictMax nums m) :
      ∀ r, Aegis.DominantIndex.dominant_index nums = ok r → 0 ≤ r.val →
        ∀ (i : ℕ), i < nums.val.length → (i : ℤ) ≠ r.val → 2 * atv nums i ≤ atInt nums r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len_lo : 2 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 50)
        (h_range : ∀ (i : ℕ), i < nums.val.length → 0 ≤ atv nums i ∧ atv nums i ≤ 100)
        (h_max : ∃! m, IsStrictMax nums m), ∀ r, Aegis.DominantIndex.dominant_index nums = ok r → 0 ≤ r.val →
          ∀ (i : ℕ), i < nums.val.length → (i : ℤ) ≠ r.val → 2 * atv nums i ≤ atInt nums r.val) := by
    sorry

  /-- Whenever the function returns r = -1, for every j with 0 <= j < len(nums), it is not the case that both (a) nums[j] > nums[i] for every i with 0 <= i < len(nums) and i != j, and (b) 2 * nums[i] <= nums[j] for every i with 0 <= i < len(nums) and i != j.
    Preconditions: 2 <= len(nums) <= 50; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100; and the largest value in nums is unique, i.e. there exists exactly one index m with 0 <= m < len(nums) and, for every i with 0 <= i < len(nums) and i != m, nums[i] < nums[m]. -/
  theorem spec_7 (nums : Slice Std.I64)
      (h_len_lo : 2 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 50)
      (h_range : ∀ (i : ℕ), i < nums.val.length → 0 ≤ atv nums i ∧ atv nums i ≤ 100)
      (h_max : ∃! m, IsStrictMax nums m) :
      ∀ r, Aegis.DominantIndex.dominant_index nums = ok r → r.val = -1 →
        ∀ (j : ℕ), j < nums.val.length → ¬ IsDominant nums j := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len_lo : 2 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 50)
        (h_range : ∀ (i : ℕ), i < nums.val.length → 0 ≤ atv nums i ∧ atv nums i ≤ 100)
        (h_max : ∃! m, IsStrictMax nums m), ∀ r, Aegis.DominantIndex.dominant_index nums = ok r → r.val = -1 →
          ∀ (j : ℕ), j < nums.val.length → ¬ IsDominant nums j) := by
    sorry

  /-- Let m be the unique index with 0 <= m < len(nums) and nums[m] > nums[i] for every i with 0 <= i < len(nums) and i != m. Whenever the function returns r = -1, there exists an index i with 0 <= i < len(nums), i != m, and nums[m] < 2 * nums[i].
    Preconditions: 2 <= len(nums) <= 50; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100; and the largest value in nums is unique, i.e. there exists exactly one index m with 0 <= m < len(nums) and, for every i with 0 <= i < len(nums) and i != m, nums[i] < nums[m]. -/
  theorem spec_8 (nums : Slice Std.I64)
      (h_len_lo : 2 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 50)
      (h_range : ∀ (i : ℕ), i < nums.val.length → 0 ≤ atv nums i ∧ atv nums i ≤ 100)
      (h_max : ∃! m, IsStrictMax nums m) :
      ∀ m, IsStrictMax nums m →
        ∀ r, Aegis.DominantIndex.dominant_index nums = ok r → r.val = -1 →
          HasDoubleOther nums m := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len_lo : 2 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 50)
        (h_range : ∀ (i : ℕ), i < nums.val.length → 0 ≤ atv nums i ∧ atv nums i ≤ 100)
        (h_max : ∃! m, IsStrictMax nums m), ∀ m, IsStrictMax nums m →
          ∀ r, Aegis.DominantIndex.dominant_index nums = ok r → r.val = -1 →
            HasDoubleOther nums m) := by
    sorry

  /-- Let m be the unique index with 0 <= m < len(nums) and nums[m] > nums[i] for every i with 0 <= i < len(nums) and i != m. Whenever the function returns a result r, r = -1 if and only if there exists an index i with 0 <= i < len(nums), i != m, and nums[m] < 2 * nums[i].
    Preconditions: 2 <= len(nums) <= 50; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100; and the largest value in nums is unique, i.e. there exists exactly one index m with 0 <= m < len(nums) and, for every i with 0 <= i < len(nums) and i != m, nums[i] < nums[m]. -/
  theorem spec_9 (nums : Slice Std.I64)
      (h_len_lo : 2 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 50)
      (h_range : ∀ (i : ℕ), i < nums.val.length → 0 ≤ atv nums i ∧ atv nums i ≤ 100)
      (h_max : ∃! m, IsStrictMax nums m) :
      ∀ m, IsStrictMax nums m →
        ∀ r, Aegis.DominantIndex.dominant_index nums = ok r →
          (r.val = -1 ↔ HasDoubleOther nums m) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len_lo : 2 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 50)
        (h_range : ∀ (i : ℕ), i < nums.val.length → 0 ≤ atv nums i ∧ atv nums i ≤ 100)
        (h_max : ∃! m, IsStrictMax nums m), ∀ m, IsStrictMax nums m →
          ∀ r, Aegis.DominantIndex.dominant_index nums = ok r →
            (r.val = -1 ↔ HasDoubleOther nums m)) := by
    sorry

  /-- Whenever the function returns a result r with r >= 0, r is the only index that is at least twice every other element: for every j with 0 <= j < len(nums) and j != r, there exists an index i with 0 <= i < len(nums), i != j, such that 2 * nums[i] > nums[j].
    Preconditions: 2 <= len(nums) <= 50; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100; and the largest value in nums is unique, i.e. there exists exactly one index m with 0 <= m < len(nums) and, for every i with 0 <= i < len(nums) and i != m, nums[i] < nums[m]. -/
  theorem spec_10 (nums : Slice Std.I64)
      (h_len_lo : 2 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 50)
      (h_range : ∀ (i : ℕ), i < nums.val.length → 0 ≤ atv nums i ∧ atv nums i ≤ 100)
      (h_max : ∃! m, IsStrictMax nums m) :
      ∀ r, Aegis.DominantIndex.dominant_index nums = ok r → 0 ≤ r.val →
        ∀ (j : ℕ), j < nums.val.length → (j : ℤ) ≠ r.val →
          ∃ (i : ℕ), i < nums.val.length ∧ i ≠ j ∧ 2 * atv nums i > atv nums j := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len_lo : 2 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 50)
        (h_range : ∀ (i : ℕ), i < nums.val.length → 0 ≤ atv nums i ∧ atv nums i ≤ 100)
        (h_max : ∃! m, IsStrictMax nums m), ∀ r, Aegis.DominantIndex.dominant_index nums = ok r → 0 ≤ r.val →
          ∀ (j : ℕ), j < nums.val.length → (j : ℤ) ≠ r.val →
            ∃ (i : ℕ), i < nums.val.length ∧ i ≠ j ∧ 2 * atv nums i > atv nums j) := by
    sorry

  end AegisSpec.DominantIndex
