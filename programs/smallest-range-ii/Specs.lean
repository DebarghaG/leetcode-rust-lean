import Aegis.SmallestRangeIi.Code.Funs

/-!
# Specifications of `Aegis.SmallestRangeIi.smallest_range_ii`

LeetCode problem `smallest-range-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.SmallestRangeIi

  open Aegis.SmallestRangeIi

  def ivals (nums : Slice Std.I64) : List ℤ := nums.val.map (fun x => x.val)

  def listMax : List ℤ → ℤ
    | [] => 0
    | x :: xs => xs.foldl (fun a b => max a b) x

  def listMin : List ℤ → ℤ
    | [] => 0
    | x :: xs => xs.foldl (fun a b => min a b) x

  def Constraints (nums : Slice Std.I64) (k : Std.I64) : Prop :=
    1 ≤ nums.val.length ∧
      nums.val.length ≤ 10000 ∧
      (∀ i : Fin nums.val.length,
        0 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 10000) ∧
      0 ≤ k.val ∧ k.val ≤ 10000

  def IsSign {n : ℕ} (ε : Fin n → ℤ) : Prop := ∀ i, ε i = 1 ∨ ε i = -1

  def tval (nums : Slice Std.I64) (k : Std.I64) (ε : Fin nums.val.length → ℤ)
      (i : Fin nums.val.length) : ℤ :=
    (nums.val.get i).val + ε i * k.val

  def score (nums : Slice Std.I64) (k : Std.I64) (ε : Fin nums.val.length → ℤ) : ℤ :=
    listMax (List.ofFn (tval nums k ε)) - listMin (List.ofFn (tval nums k ε))

  def scoreSet (nums : Slice Std.I64) (k : Std.I64) : Set ℤ :=
    { s | ∃ ε : Fin nums.val.length → ℤ, IsSign ε ∧ score nums k ε = s }

  def sortedVals (nums : Slice Std.I64) : List ℤ :=
    (ivals nums).insertionSort (fun a b => decide (a ≤ b))

  def Uj (s : List ℤ) (k : ℤ) (j : ℕ) : List ℤ :=
    ((List.finRange s.length).filter (fun (i : Fin s.length) => decide (i.val < j))).map
        (fun (i : Fin s.length) => s.get i + k) ++
      ((List.finRange s.length).filter (fun (i : Fin s.length) => decide (j ≤ i.val))).map
        (fun (i : Fin s.length) => s.get i - k)

  def UjScore (s : List ℤ) (k : ℤ) (j : ℕ) : ℤ :=
    listMax (Uj s k j) - listMin (Uj s k j)

  def sortedScanMin (nums : Slice Std.I64) (k : Std.I64) : ℤ :=
    listMin ((List.range (nums.val.length + 1)).map (fun j => UjScore (sortedVals nums) k.val j))

  /-- Let n = len(nums). A sign choice is a function epsilon from {0,...,n-1} to {1,-1}. For a sign choice, define t_epsilon(i) = nums[i] + epsilon(i)*k for 0 <= i < n, and define score(epsilon) = max_{0<=i<n} t_epsilon(i) - min_{0<=i<n} t_epsilon(i). Whenever the function returns a result r, r = min { score(epsilon) | epsilon is a sign choice }.
    Preconditions: The input satisfies the problem constraints: 1 <= len(nums) <= 10000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 10000; and 0 <= k <= 10000. -/
  theorem spec_1 (nums : Slice Std.I64) (k : Std.I64) (h : Constraints nums k) :
      ∀ r : Std.I64, smallest_range_ii nums k = ok r →
        (∀ ε : Fin nums.val.length → ℤ, IsSign ε → r.val ≤ score nums k ε) ∧
          (∃ ε : Fin nums.val.length → ℤ, IsSign ε ∧ score nums k ε = r.val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (h : Constraints nums k), ∀ r : Std.I64, smallest_range_ii nums k = ok r →
          (∀ ε : Fin nums.val.length → ℤ, IsSign ε → r.val ≤ score nums k ε) ∧
            (∃ ε : Fin nums.val.length → ℤ, IsSign ε ∧ score nums k ε = r.val)) := by
    sorry

  /-- The function returns a result r; it does not fail, panic, overflow, or access memory out of bounds.
    Preconditions: The input satisfies the problem constraints: 1 <= len(nums) <= 10000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 10000; and 0 <= k <= 10000. -/
  theorem spec_2 (nums : Slice Std.I64) (k : Std.I64) (h : Constraints nums k) :
      ∃ r : Std.I64, smallest_range_ii nums k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (h : Constraints nums k), ∃ r : Std.I64, smallest_range_ii nums k = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r.
    Preconditions: The input satisfies the problem constraints: 1 <= len(nums) <= 10000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 10000; and 0 <= k <= 10000. -/
  theorem spec_3 (nums : Slice Std.I64) (k : Std.I64) (h : Constraints nums k) :
      ∀ r : Std.I64, smallest_range_ii nums k = ok r → 0 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (h : Constraints nums k), ∀ r : Std.I64, smallest_range_ii nums k = ok r → 0 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r <= max(nums) - min(nums), where max(nums) and min(nums) are the maximum and minimum entries of nums.
    Preconditions: The input satisfies the problem constraints: 1 <= len(nums) <= 10000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 10000; and 0 <= k <= 10000. -/
  theorem spec_4 (nums : Slice Std.I64) (k : Std.I64) (h : Constraints nums k) :
      ∀ r : Std.I64, smallest_range_ii nums k = ok r →
        r.val ≤ listMax (ivals nums) - listMin (ivals nums) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (h : Constraints nums k), ∀ r : Std.I64, smallest_range_ii nums k = ok r →
          r.val ≤ listMax (ivals nums) - listMin (ivals nums)) := by
    sorry

  /-- Let D = |nums[0] - nums[1]|. Whenever the function returns a result r, r = min(D, |D - 2*k|).
    Preconditions: The input satisfies the problem constraints and len(nums) = 2. -/
  theorem spec_5 (nums : Slice Std.I64) (k : Std.I64) (h : Constraints nums k)
      (hlen : nums.val.length = 2) :
      ∀ r : Std.I64, smallest_range_ii nums k = ok r →
        r.val = min
          |(nums.val.get ⟨0, by have h1 : 1 ≤ nums.val.length := h.1; omega⟩).val -
            (nums.val.get ⟨1, by have h1 : 1 ≤ nums.val.length := h.1; omega⟩).val|
          |((nums.val.get ⟨0, by have h1 : 1 ≤ nums.val.length := h.1; omega⟩).val -
            (nums.val.get ⟨1, by have h1 : 1 ≤ nums.val.length := h.1; omega⟩).val) -
              2 * k.val| := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (h : Constraints nums k)
        (hlen : nums.val.length = 2), ∀ r : Std.I64, smallest_range_ii nums k = ok r →
          r.val = min
            |(nums.val.get ⟨0, by have h1 : 1 ≤ nums.val.length := h.1; omega⟩).val -
              (nums.val.get ⟨1, by have h1 : 1 ≤ nums.val.length := h.1; omega⟩).val|
            |((nums.val.get ⟨0, by have h1 : 1 ≤ nums.val.length := h.1; omega⟩).val -
              (nums.val.get ⟨1, by have h1 : 1 ≤ nums.val.length := h.1; omega⟩).val) -
                2 * k.val|) := by
    sorry

  /-- Let n = len(nums). Whenever the function returns a result r, there exists a sign choice epsilon from {0,...,n-1} to {1,-1} such that max_{0<=i<n} (nums[i] + epsilon(i)*k) - min_{0<=i<n} (nums[i] + epsilon(i)*k) = r.
    Preconditions: The input satisfies the problem constraints: 1 <= len(nums) <= 10000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 10000; and 0 <= k <= 10000. -/
  theorem spec_6 (nums : Slice Std.I64) (k : Std.I64) (h : Constraints nums k) :
      ∀ r : Std.I64, smallest_range_ii nums k = ok r →
        ∃ ε : Fin nums.val.length → ℤ, IsSign ε ∧ score nums k ε = r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (h : Constraints nums k), ∀ r : Std.I64, smallest_range_ii nums k = ok r →
          ∃ ε : Fin nums.val.length → ℤ, IsSign ε ∧ score nums k ε = r.val) := by
    sorry

  /-- Whenever smallest_range_ii(nums1,k) returns r1 and smallest_range_ii(nums2,k) returns r2, r1 = r2.
    Preconditions: Let nums1 and nums2 be slices and let k and c be integers. Both inputs (nums1,k) and (nums2,k) satisfy the problem constraints, len(nums1) = len(nums2), and for every i with 0 <= i < len(nums1), nums2[i] = nums1[i] + c. -/
  theorem spec_7 (nums1 nums2 : Slice Std.I64) (k c : Std.I64)
      (h1 : Constraints nums1 k) (h2 : Constraints nums2 k)
      (hlen : nums1.val.length = nums2.val.length)
      (hshift : ∀ i : Fin nums1.val.length,
        (nums2.val.get ⟨i.val, hlen ▸ i.isLt⟩).val = (nums1.val.get i).val + c.val) :
      ∀ r1 r2 : Std.I64,
        smallest_range_ii nums1 k = ok r1 → smallest_range_ii nums2 k = ok r2 →
          r1.val = r2.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64) (k c : Std.I64)
        (h1 : Constraints nums1 k) (h2 : Constraints nums2 k)
        (hlen : nums1.val.length = nums2.val.length)
        (hshift : ∀ i : Fin nums1.val.length,
          (nums2.val.get ⟨i.val, hlen ▸ i.isLt⟩).val = (nums1.val.get i).val + c.val), ∀ r1 r2 : Std.I64,
          smallest_range_ii nums1 k = ok r1 → smallest_range_ii nums2 k = ok r2 →
            r1.val = r2.val) := by
    sorry

  /-- Whenever smallest_range_ii(nums1,k1) returns r1 and smallest_range_ii(nums2,k2) returns r2, r2 = a*r1.
    Preconditions: Let nums1, nums2 be slices and k1, k2, a be integers with a >= 0. Both inputs (nums1,k1) and (nums2,k2) satisfy the problem constraints, len(nums1) = len(nums2), k2 = a*k1, and for every i with 0 <= i < len(nums1), nums2[i] = a*nums1[i]. -/
  theorem spec_8 (nums1 nums2 : Slice Std.I64) (k1 k2 a : Std.I64)
      (h1 : Constraints nums1 k1) (h2 : Constraints nums2 k2)
      (ha : 0 ≤ a.val)
      (hlen : nums1.val.length = nums2.val.length)
      (hk : k2.val = a.val * k1.val)
      (hscale : ∀ i : Fin nums1.val.length,
        (nums2.val.get ⟨i.val, hlen ▸ i.isLt⟩).val = a.val * (nums1.val.get i).val) :
      ∀ r1 r2 : Std.I64,
        smallest_range_ii nums1 k1 = ok r1 → smallest_range_ii nums2 k2 = ok r2 →
          r2.val = a.val * r1.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64) (k1 k2 a : Std.I64)
        (h1 : Constraints nums1 k1) (h2 : Constraints nums2 k2)
        (ha : 0 ≤ a.val)
        (hlen : nums1.val.length = nums2.val.length)
        (hk : k2.val = a.val * k1.val)
        (hscale : ∀ i : Fin nums1.val.length,
          (nums2.val.get ⟨i.val, hlen ▸ i.isLt⟩).val = a.val * (nums1.val.get i).val), ∀ r1 r2 : Std.I64,
          smallest_range_ii nums1 k1 = ok r1 → smallest_range_ii nums2 k2 = ok r2 →
            r2.val = a.val * r1.val) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 if and only if there exists an integer v such that for every i with 0 <= i < len(nums), v = nums[i] + k or v = nums[i] - k.
    Preconditions: The input satisfies the problem constraints: 1 <= len(nums) <= 10000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 10000; and 0 <= k <= 10000. -/
  theorem spec_9 (nums : Slice Std.I64) (k : Std.I64) (h : Constraints nums k) :
      ∀ r : Std.I64, smallest_range_ii nums k = ok r →
        (r.val = 0 ↔
          ∃ v : ℤ, ∀ i : Fin nums.val.length,
            v = (nums.val.get i).val + k.val ∨ v = (nums.val.get i).val - k.val) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (h : Constraints nums k), ∀ r : Std.I64, smallest_range_ii nums k = ok r →
          (r.val = 0 ↔
            ∃ v : ℤ, ∀ i : Fin nums.val.length,
              v = (nums.val.get i).val + k.val ∨ v = (nums.val.get i).val - k.val)) := by
    sorry

  /-- Let n = len(nums) and let s be the nondecreasing sort of nums. For each j with 0 <= j <= n, let U_j = { s[i] + k | 0 <= i < j } ∪ { s[i] - k | j <= i < n }. Whenever the function returns a result r, r = min_{0 <= j <= n} (max U_j - min U_j), where the max and min are over the nonempty set U_j.
    Preconditions: The input satisfies the problem constraints: 1 <= len(nums) <= 10000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 10000; and 0 <= k <= 10000. -/
  theorem spec_10 (nums : Slice Std.I64) (k : Std.I64) (h : Constraints nums k) :
      ∀ r : Std.I64, smallest_range_ii nums k = ok r → r.val = sortedScanMin nums k := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (h : Constraints nums k), ∀ r : Std.I64, smallest_range_ii nums k = ok r → r.val = sortedScanMin nums k) := by
    sorry

  end AegisSpec.SmallestRangeIi
