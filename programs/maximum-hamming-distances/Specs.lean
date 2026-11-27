import Aegis.MaxHammingDistances.Code.Funs

/-!
# Specifications of `Aegis.MaxHammingDistances.max_hamming_distances`

LeetCode problem `maximum-hamming-distances`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaxHammingDistances

  def bit (k : Nat) (x : Int) : Int := (x / (2 : Int) ^ k) % 2

  def hd (m : Nat) (a b : Int) : Nat :=
    ((List.range m).filter (fun k => decide (bit k a ≠ bit k b))).length

  def elem (nums : Slice Std.I64) (i : Nat) : Int := (nums.val[i]!).val

  def maxHdAway (nums : Slice Std.I64) (m : Nat) (i : Nat) : Nat :=
    ((Finset.range nums.val.length).filter (fun j => j ≠ i)).sup
      (fun j => hd m (elem nums i) (elem nums j))

  def maxHdAll (nums : Slice Std.I64) (m : Nat) (i : Nat) : Nat :=
    (Finset.range nums.val.length).sup (fun j => hd m (elem nums i) (elem nums j))

  /-- The function returns a result r such that len(r) = len(nums), and for every i with 0 <= i < len(nums), r[i] = max { hd(nums[i], nums[j]) | 0 <= j < len(nums) and j != i }, where hd(a,b) is the number of bit positions k with 0 <= k < m such that the k-th bits of a and b differ (the k-th bit of x is floor(x / 2^k) mod 2).
    Preconditions: m is an integer with 1 <= m <= 17; len(nums) is an integer with 2 <= len(nums) <= 2^m; for every i with 0 <= i < len(nums), nums[i] is an integer with 0 <= nums[i] < 2^m. -/
  theorem spec_1 (nums : Slice Std.I64) (m : Std.I64)
      (hm_pos : 1 ≤ m.val) (hm_le : m.val ≤ 17)
      (hlen_ge : 2 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2 ^ m.val.toNat)
      (hval : ∀ i, i < nums.val.length →
        0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val < (2 : Int) ^ m.val.toNat) :
      ∃ r, Aegis.MaxHammingDistances.max_hamming_distances nums m = ok r ∧
        r.val.length = nums.val.length ∧
        (∀ i, i < nums.val.length → (r.val[i]!).val = (maxHdAway nums m.val.toNat i : Int)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (m : Std.I64)
        (hm_pos : 1 ≤ m.val) (hm_le : m.val ≤ 17)
        (hlen_ge : 2 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2 ^ m.val.toNat)
        (hval : ∀ i, i < nums.val.length →
          0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val < (2 : Int) ^ m.val.toNat), ∃ r, Aegis.MaxHammingDistances.max_hamming_distances nums m = ok r ∧
          r.val.length = nums.val.length ∧
          (∀ i, i < nums.val.length → (r.val[i]!).val = (maxHdAway nums m.val.toNat i : Int))) := by
    sorry

  /-- The function returns a result r; it does not fail, overflow, access out of bounds, or panic.
    Preconditions: m is an integer with 1 <= m <= 17; len(nums) is an integer with 2 <= len(nums) <= 2^m; for every i with 0 <= i < len(nums), nums[i] is an integer with 0 <= nums[i] < 2^m. -/
  theorem spec_2 (nums : Slice Std.I64) (m : Std.I64)
      (hm_pos : 1 ≤ m.val) (hm_le : m.val ≤ 17)
      (hlen_ge : 2 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2 ^ m.val.toNat)
      (hval : ∀ i, i < nums.val.length →
        0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val < (2 : Int) ^ m.val.toNat) :
      ∃ r, Aegis.MaxHammingDistances.max_hamming_distances nums m = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (m : Std.I64)
        (hm_pos : 1 ≤ m.val) (hm_le : m.val ≤ 17)
        (hlen_ge : 2 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2 ^ m.val.toNat)
        (hval : ∀ i, i < nums.val.length →
          0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val < (2 : Int) ^ m.val.toNat), ∃ r, Aegis.MaxHammingDistances.max_hamming_distances nums m = ok r) := by
    sorry

  /-- Whenever the function returns a result r, len(r) = len(nums).
    Preconditions: m is an integer with 1 <= m <= 17; len(nums) is an integer with 2 <= len(nums) <= 2^m; for every i with 0 <= i < len(nums), nums[i] is an integer with 0 <= nums[i] < 2^m. -/
  theorem spec_3 (nums : Slice Std.I64) (m : Std.I64)
      (hm_pos : 1 ≤ m.val) (hm_le : m.val ≤ 17)
      (hlen_ge : 2 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2 ^ m.val.toNat)
      (hval : ∀ i, i < nums.val.length →
        0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val < (2 : Int) ^ m.val.toNat) :
      ∀ r, Aegis.MaxHammingDistances.max_hamming_distances nums m = ok r →
        r.val.length = nums.val.length := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (m : Std.I64)
        (hm_pos : 1 ≤ m.val) (hm_le : m.val ≤ 17)
        (hlen_ge : 2 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2 ^ m.val.toNat)
        (hval : ∀ i, i < nums.val.length →
          0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val < (2 : Int) ^ m.val.toNat), ∀ r, Aegis.MaxHammingDistances.max_hamming_distances nums m = ok r →
          r.val.length = nums.val.length) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(nums), 0 <= r[i] <= m.
    Preconditions: m is an integer with 1 <= m <= 17; len(nums) is an integer with 2 <= len(nums) <= 2^m; for every i with 0 <= i < len(nums), nums[i] is an integer with 0 <= nums[i] < 2^m. -/
  theorem spec_4 (nums : Slice Std.I64) (m : Std.I64)
      (hm_pos : 1 ≤ m.val) (hm_le : m.val ≤ 17)
      (hlen_ge : 2 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2 ^ m.val.toNat)
      (hval : ∀ i, i < nums.val.length →
        0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val < (2 : Int) ^ m.val.toNat) :
      ∀ r, Aegis.MaxHammingDistances.max_hamming_distances nums m = ok r →
        ∀ i, i < nums.val.length → 0 ≤ (r.val[i]!).val ∧ (r.val[i]!).val ≤ m.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (m : Std.I64)
        (hm_pos : 1 ≤ m.val) (hm_le : m.val ≤ 17)
        (hlen_ge : 2 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2 ^ m.val.toNat)
        (hval : ∀ i, i < nums.val.length →
          0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val < (2 : Int) ^ m.val.toNat), ∀ r, Aegis.MaxHammingDistances.max_hamming_distances nums m = ok r →
          ∀ i, i < nums.val.length → 0 ≤ (r.val[i]!).val ∧ (r.val[i]!).val ≤ m.val) := by
    sorry

  /-- Whenever the function returns a result r, for every i and j with 0 <= i < len(nums), 0 <= j < len(nums), and i != j, hd(nums[i], nums[j]) <= r[i], where hd(a,b) is the number of bit positions k with 0 <= k < m such that the k-th bits of a and b differ.
    Preconditions: m is an integer with 1 <= m <= 17; len(nums) is an integer with 2 <= len(nums) <= 2^m; for every i with 0 <= i < len(nums), nums[i] is an integer with 0 <= nums[i] < 2^m. -/
  theorem spec_5 (nums : Slice Std.I64) (m : Std.I64)
      (hm_pos : 1 ≤ m.val) (hm_le : m.val ≤ 17)
      (hlen_ge : 2 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2 ^ m.val.toNat)
      (hval : ∀ i, i < nums.val.length →
        0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val < (2 : Int) ^ m.val.toNat) :
      ∀ r, Aegis.MaxHammingDistances.max_hamming_distances nums m = ok r →
        ∀ i j, i < nums.val.length → j < nums.val.length → i ≠ j →
          (hd m.val.toNat (elem nums i) (elem nums j) : Int) ≤ (r.val[i]!).val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (m : Std.I64)
        (hm_pos : 1 ≤ m.val) (hm_le : m.val ≤ 17)
        (hlen_ge : 2 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2 ^ m.val.toNat)
        (hval : ∀ i, i < nums.val.length →
          0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val < (2 : Int) ^ m.val.toNat), ∀ r, Aegis.MaxHammingDistances.max_hamming_distances nums m = ok r →
          ∀ i j, i < nums.val.length → j < nums.val.length → i ≠ j →
            (hd m.val.toNat (elem nums i) (elem nums j) : Int) ≤ (r.val[i]!).val) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(nums), there exists j with 0 <= j < len(nums) and j != i such that r[i] = hd(nums[i], nums[j]), where hd(a,b) is the number of bit positions k with 0 <= k < m such that the k-th bits of a and b differ.
    Preconditions: m is an integer with 1 <= m <= 17; len(nums) is an integer with 2 <= len(nums) <= 2^m; for every i with 0 <= i < len(nums), nums[i] is an integer with 0 <= nums[i] < 2^m. -/
  theorem spec_6 (nums : Slice Std.I64) (m : Std.I64)
      (hm_pos : 1 ≤ m.val) (hm_le : m.val ≤ 17)
      (hlen_ge : 2 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2 ^ m.val.toNat)
      (hval : ∀ i, i < nums.val.length →
        0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val < (2 : Int) ^ m.val.toNat) :
      ∀ r, Aegis.MaxHammingDistances.max_hamming_distances nums m = ok r →
        ∀ i, i < nums.val.length →
          ∃ j, j < nums.val.length ∧ j ≠ i ∧
            (r.val[i]!).val = (hd m.val.toNat (elem nums i) (elem nums j) : Int) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (m : Std.I64)
        (hm_pos : 1 ≤ m.val) (hm_le : m.val ≤ 17)
        (hlen_ge : 2 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2 ^ m.val.toNat)
        (hval : ∀ i, i < nums.val.length →
          0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val < (2 : Int) ^ m.val.toNat), ∀ r, Aegis.MaxHammingDistances.max_hamming_distances nums m = ok r →
          ∀ i, i < nums.val.length →
            ∃ j, j < nums.val.length ∧ j ≠ i ∧
              (r.val[i]!).val = (hd m.val.toNat (elem nums i) (elem nums j) : Int)) := by
    sorry

  /-- Whenever the function returns a result r, for every i and k with 0 <= i < len(nums) and 0 <= k < len(nums), if nums[i] = nums[k], then r[i] = r[k].
    Preconditions: m is an integer with 1 <= m <= 17; len(nums) is an integer with 2 <= len(nums) <= 2^m; for every i with 0 <= i < len(nums), nums[i] is an integer with 0 <= nums[i] < 2^m. -/
  theorem spec_7 (nums : Slice Std.I64) (m : Std.I64)
      (hm_pos : 1 ≤ m.val) (hm_le : m.val ≤ 17)
      (hlen_ge : 2 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2 ^ m.val.toNat)
      (hval : ∀ i, i < nums.val.length →
        0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val < (2 : Int) ^ m.val.toNat) :
      ∀ r, Aegis.MaxHammingDistances.max_hamming_distances nums m = ok r →
        ∀ i k, i < nums.val.length → k < nums.val.length → elem nums i = elem nums k →
          (r.val[i]!).val = (r.val[k]!).val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (m : Std.I64)
        (hm_pos : 1 ≤ m.val) (hm_le : m.val ≤ 17)
        (hlen_ge : 2 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2 ^ m.val.toNat)
        (hval : ∀ i, i < nums.val.length →
          0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val < (2 : Int) ^ m.val.toNat), ∀ r, Aegis.MaxHammingDistances.max_hamming_distances nums m = ok r →
          ∀ i k, i < nums.val.length → k < nums.val.length → elem nums i = elem nums k →
            (r.val[i]!).val = (r.val[k]!).val) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(nums), r[i] = 0 if and only if for every j with 0 <= j < len(nums), nums[j] = nums[i].
    Preconditions: m is an integer with 1 <= m <= 17; len(nums) is an integer with 2 <= len(nums) <= 2^m; for every i with 0 <= i < len(nums), nums[i] is an integer with 0 <= nums[i] < 2^m. -/
  theorem spec_8 (nums : Slice Std.I64) (m : Std.I64)
      (hm_pos : 1 ≤ m.val) (hm_le : m.val ≤ 17)
      (hlen_ge : 2 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2 ^ m.val.toNat)
      (hval : ∀ i, i < nums.val.length →
        0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val < (2 : Int) ^ m.val.toNat) :
      ∀ r, Aegis.MaxHammingDistances.max_hamming_distances nums m = ok r →
        ∀ i, i < nums.val.length →
          ((r.val[i]!).val = 0 ↔ ∀ j, j < nums.val.length → elem nums j = elem nums i) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (m : Std.I64)
        (hm_pos : 1 ≤ m.val) (hm_le : m.val ≤ 17)
        (hlen_ge : 2 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2 ^ m.val.toNat)
        (hval : ∀ i, i < nums.val.length →
          0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val < (2 : Int) ^ m.val.toNat), ∀ r, Aegis.MaxHammingDistances.max_hamming_distances nums m = ok r →
          ∀ i, i < nums.val.length →
            ((r.val[i]!).val = 0 ↔ ∀ j, j < nums.val.length → elem nums j = elem nums i)) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(nums), r[i] = m if and only if there exists j with 0 <= j < len(nums), j != i, such that nums[j] = (2^m - 1) - nums[i].
    Preconditions: m is an integer with 1 <= m <= 17; len(nums) is an integer with 2 <= len(nums) <= 2^m; for every i with 0 <= i < len(nums), nums[i] is an integer with 0 <= nums[i] < 2^m. -/
  theorem spec_9 (nums : Slice Std.I64) (m : Std.I64)
      (hm_pos : 1 ≤ m.val) (hm_le : m.val ≤ 17)
      (hlen_ge : 2 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2 ^ m.val.toNat)
      (hval : ∀ i, i < nums.val.length →
        0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val < (2 : Int) ^ m.val.toNat) :
      ∀ r, Aegis.MaxHammingDistances.max_hamming_distances nums m = ok r →
        ∀ i, i < nums.val.length →
          ((r.val[i]!).val = m.val ↔
            ∃ j, j < nums.val.length ∧ j ≠ i ∧
              elem nums j = (2 : Int) ^ m.val.toNat - 1 - elem nums i) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64) (m : Std.I64)
        (hm_pos : 1 ≤ m.val) (hm_le : m.val ≤ 17)
        (hlen_ge : 2 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2 ^ m.val.toNat)
        (hval : ∀ i, i < nums.val.length →
          0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val < (2 : Int) ^ m.val.toNat), ∀ r, Aegis.MaxHammingDistances.max_hamming_distances nums m = ok r →
          ∀ i, i < nums.val.length →
            ((r.val[i]!).val = m.val ↔
              ∃ j, j < nums.val.length ∧ j ≠ i ∧
                elem nums j = (2 : Int) ^ m.val.toNat - 1 - elem nums i)) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(nums), r[i] > 0 if and only if there exists j with 0 <= j < len(nums), j != i, and nums[j] != nums[i].
    Preconditions: m is an integer with 1 <= m <= 17; len(nums) is an integer with 2 <= len(nums) <= 2^m; for every i with 0 <= i < len(nums), nums[i] is an integer with 0 <= nums[i] < 2^m. -/
  theorem spec_10 (nums : Slice Std.I64) (m : Std.I64)
      (hm_pos : 1 ≤ m.val) (hm_le : m.val ≤ 17)
      (hlen_ge : 2 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2 ^ m.val.toNat)
      (hval : ∀ i, i < nums.val.length →
        0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val < (2 : Int) ^ m.val.toNat) :
      ∀ r, Aegis.MaxHammingDistances.max_hamming_distances nums m = ok r →
        ∀ i, i < nums.val.length →
          (0 < (r.val[i]!).val ↔
            ∃ j, j < nums.val.length ∧ j ≠ i ∧ elem nums j ≠ elem nums i) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64) (m : Std.I64)
        (hm_pos : 1 ≤ m.val) (hm_le : m.val ≤ 17)
        (hlen_ge : 2 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2 ^ m.val.toNat)
        (hval : ∀ i, i < nums.val.length →
          0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val < (2 : Int) ^ m.val.toNat), ∀ r, Aegis.MaxHammingDistances.max_hamming_distances nums m = ok r →
          ∀ i, i < nums.val.length →
            (0 < (r.val[i]!).val ↔
              ∃ j, j < nums.val.length ∧ j ≠ i ∧ elem nums j ≠ elem nums i)) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(nums), r[i] = max { hd(nums[i], nums[j]) | 0 <= j < len(nums) }, where hd(a,b) is the number of bit positions k with 0 <= k < m such that the k-th bits of a and b differ.
    Preconditions: m is an integer with 1 <= m <= 17; len(nums) is an integer with 2 <= len(nums) <= 2^m; for every i with 0 <= i < len(nums), nums[i] is an integer with 0 <= nums[i] < 2^m. -/
  theorem spec_11 (nums : Slice Std.I64) (m : Std.I64)
      (hm_pos : 1 ≤ m.val) (hm_le : m.val ≤ 17)
      (hlen_ge : 2 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2 ^ m.val.toNat)
      (hval : ∀ i, i < nums.val.length →
        0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val < (2 : Int) ^ m.val.toNat) :
      ∀ r, Aegis.MaxHammingDistances.max_hamming_distances nums m = ok r →
        ∀ i, i < nums.val.length → (r.val[i]!).val = (maxHdAll nums m.val.toNat i : Int) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64) (m : Std.I64)
        (hm_pos : 1 ≤ m.val) (hm_le : m.val ≤ 17)
        (hlen_ge : 2 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2 ^ m.val.toNat)
        (hval : ∀ i, i < nums.val.length →
          0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val < (2 : Int) ^ m.val.toNat), ∀ r, Aegis.MaxHammingDistances.max_hamming_distances nums m = ok r →
          ∀ i, i < nums.val.length → (r.val[i]!).val = (maxHdAll nums m.val.toNat i : Int)) := by
    sorry

  end AegisSpec.MaxHammingDistances
