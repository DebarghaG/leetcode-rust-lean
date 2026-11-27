import Aegis.ValidSubarraySplit.Code.Funs

/-!
# Specifications of `Aegis.ValidSubarraySplit.valid_subarray_split`

LeetCode problem `minimum-subarrays-in-a-valid-split`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.ValidSubarraySplit

  open Aeneas Aeneas.Std Result

  def vals (nums : Slice I64) : List ℤ := nums.val.map (fun x => x.val)

  def EntryEq (l : List ℤ) (i : ℕ) (v : ℤ) : Prop := l[i]? = some v

  def EntryGt (l : List ℤ) (i : ℕ) : Prop := ∃ v : ℤ, l[i]? = some v ∧ 1 < v

  def EntriesBounds (l : List ℤ) : Prop :=
    ∀ (i : ℕ) (v : ℤ), l[i]? = some v → 1 ≤ v ∧ v ≤ 100000

  def EntriesGtOne (l : List ℤ) : Prop :=
    ∀ (i : ℕ) (v : ℤ), l[i]? = some v → 1 < v

  def InputBounds (l : List ℤ) : Prop :=
    1 ≤ l.length ∧ l.length ≤ 1000 ∧ EntriesBounds l

  def GcdStep (l : List ℤ) (i j : ℕ) : Prop :=
    ∃ a b : ℤ, l[i]? = some a ∧ l[j]? = some b ∧ 1 < Int.gcd a b

  def GcdStepLE (l : List ℤ) (i j : ℕ) : Prop :=
    ∃ a b : ℤ, l[i]? = some a ∧ l[j]? = some b ∧ Int.gcd a b ≤ 1

  def GcdEqOne (l : List ℤ) (i j : ℕ) : Prop :=
    ∃ a b : ℤ, l[i]? = some a ∧ l[j]? = some b ∧ Int.gcd a b = 1

  def IsSplitChain (l : List ℤ) (k : ℕ) (c : ℕ → ℕ) : Prop :=
    c 0 = 0 ∧ c k = l.length ∧
      (∀ j, 1 ≤ j → j ≤ k → c (j - 1) < c j) ∧
      (∀ j, 1 ≤ j → j ≤ k → GcdStep l (c (j - 1)) (c j - 1))

  def HasChain (l : List ℤ) (k : ℕ) : Prop := ∃ c : ℕ → ℕ, IsSplitChain l k c

  def HasSomeChain (l : List ℤ) : Prop := ∃ k : ℕ, 1 ≤ k ∧ HasChain l k

  def IsLeastChain (l : List ℤ) (r : ℤ) : Prop :=
    ∃ k : ℕ, (k : ℤ) = r ∧ 1 ≤ k ∧ HasChain l k ∧
      ∀ k' : ℕ, 1 ≤ k' → k' < k → ¬ HasChain l k'

  /-- The function returns a result r and: if there exist an integer k with k >= 1 and indices 0 = c_0 < c_1 < ... < c_k = n such that gcd(nums[c_{j-1}], nums[c_j - 1]) > 1 for every j with 1 <= j <= k, then r is the least such k; otherwise r = -1.
    Preconditions: Let n = len(nums). The input satisfies 1 <= n <= 1000 and, for every i with 0 <= i < n, 1 <= nums[i] <= 100000. -/
  theorem spec_1 (nums : Slice I64) (hb : InputBounds (vals nums)) :
      ∃ rv : I64, Aegis.ValidSubarraySplit.valid_subarray_split nums = ok rv ∧
        (HasSomeChain (vals nums) → IsLeastChain (vals nums) rv.val) ∧
        (¬ HasSomeChain (vals nums) → rv.val = -1) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice I64) (hb : InputBounds (vals nums)), ∃ rv : I64, Aegis.ValidSubarraySplit.valid_subarray_split nums = ok rv ∧
          (HasSomeChain (vals nums) → IsLeastChain (vals nums) rv.val) ∧
          (¬ HasSomeChain (vals nums) → rv.val = -1)) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r; it does not fail (no overflow, out-of-bounds access, or panic).
    Preconditions: Let n = len(nums). The input satisfies 1 <= n <= 1000 and, for every i with 0 <= i < n, 1 <= nums[i] <= 100000. -/
  theorem spec_2 (nums : Slice I64) (hb : InputBounds (vals nums)) :
      ∃ rv : I64, Aegis.ValidSubarraySplit.valid_subarray_split nums = ok rv := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice I64) (hb : InputBounds (vals nums)), ∃ rv : I64, Aegis.ValidSubarraySplit.valid_subarray_split nums = ok rv) := by
    sorry

  /-- Whenever the function returns a result r, either r = -1 or 1 <= r <= n.
    Preconditions: Let n = len(nums). The input satisfies 1 <= n <= 1000 and, for every i with 0 <= i < n, 1 <= nums[i] <= 100000. -/
  theorem spec_3 (nums : Slice I64) (hb : InputBounds (vals nums)) (rv : I64)
      (hres : Aegis.ValidSubarraySplit.valid_subarray_split nums = ok rv) :
      rv.val = -1 ∨ (1 ≤ rv.val ∧ rv.val ≤ ((vals nums).length : ℤ)) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice I64) (hb : InputBounds (vals nums)) (rv : I64)
        (hres : Aegis.ValidSubarraySplit.valid_subarray_split nums = ok rv), rv.val = -1 ∨ (1 ≤ rv.val ∧ rv.val ≤ ((vals nums).length : ℤ))) := by
    sorry

  /-- Whenever the function returns a result r, r = 1 if and only if gcd(nums[0], nums[n-1]) > 1.
    Preconditions: Let n = len(nums). The input satisfies 1 <= n <= 1000 and, for every i with 0 <= i < n, 1 <= nums[i] <= 100000. -/
  theorem spec_4 (nums : Slice I64) (hb : InputBounds (vals nums)) (rv : I64)
      (hres : Aegis.ValidSubarraySplit.valid_subarray_split nums = ok rv) :
      (rv.val = 1 ↔ GcdStep (vals nums) 0 ((vals nums).length - 1)) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice I64) (hb : InputBounds (vals nums)) (rv : I64)
        (hres : Aegis.ValidSubarraySplit.valid_subarray_split nums = ok rv), (rv.val = 1 ↔ GcdStep (vals nums) 0 ((vals nums).length - 1))) := by
    sorry

  /-- Whenever the function returns a result r, if nums[0] > 1 then r = 1, and if nums[0] = 1 then r = -1.
    Preconditions: Let n = len(nums). The input satisfies n = 1 and, for the unique index 0, 1 <= nums[0] <= 100000. -/
  theorem spec_5 (nums : Slice I64) (hlen : (vals nums).length = 1)
      (hb : EntriesBounds (vals nums)) (rv : I64)
      (hres : Aegis.ValidSubarraySplit.valid_subarray_split nums = ok rv) :
      (EntryGt (vals nums) 0 → rv.val = 1) ∧ (EntryEq (vals nums) 0 1 → rv.val = -1) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice I64) (hlen : (vals nums).length = 1)
        (hb : EntriesBounds (vals nums)) (rv : I64)
        (hres : Aegis.ValidSubarraySplit.valid_subarray_split nums = ok rv), (EntryGt (vals nums) 0 → rv.val = 1) ∧ (EntryEq (vals nums) 0 1 → rv.val = -1)) := by
    sorry

  /-- Whenever the function returns a result r, if nums[0] = 1 or nums[n-1] = 1, then r = -1.
    Preconditions: Let n = len(nums). The input satisfies 1 <= n <= 1000 and, for every i with 0 <= i < n, 1 <= nums[i] <= 100000. -/
  theorem spec_6 (nums : Slice I64) (hb : InputBounds (vals nums)) (rv : I64)
      (hres : Aegis.ValidSubarraySplit.valid_subarray_split nums = ok rv)
      (hone : EntryEq (vals nums) 0 1 ∨ EntryEq (vals nums) ((vals nums).length - 1) 1) :
      rv.val = -1 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice I64) (hb : InputBounds (vals nums)) (rv : I64)
        (hres : Aegis.ValidSubarraySplit.valid_subarray_split nums = ok rv)
        (hone : EntryEq (vals nums) 0 1 ∨ EntryEq (vals nums) ((vals nums).length - 1) 1), rv.val = -1) := by
    sorry

  /-- Whenever the function returns a result r, r != -1.
    Preconditions: Let n = len(nums). The input satisfies 1 <= n <= 1000 and, for every i with 0 <= i < n, 1 <= nums[i] <= 100000, and moreover nums[i] > 1 for every i with 0 <= i < n. -/
  theorem spec_7 (nums : Slice I64) (hb : InputBounds (vals nums))
      (hgt : EntriesGtOne (vals nums)) (rv : I64)
      (hres : Aegis.ValidSubarraySplit.valid_subarray_split nums = ok rv) :
      rv.val ≠ -1 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice I64) (hb : InputBounds (vals nums))
        (hgt : EntriesGtOne (vals nums)) (rv : I64)
        (hres : Aegis.ValidSubarraySplit.valid_subarray_split nums = ok rv), rv.val ≠ -1) := by
    sorry

  /-- Whenever the function returns a result r with r >= 1, there exist indices 0 = c_0 < c_1 < ... < c_r = n such that gcd(nums[c_{j-1}], nums[c_j - 1]) > 1 for every j with 1 <= j <= r.
    Preconditions: Let n = len(nums). The input satisfies 1 <= n <= 1000 and, for every i with 0 <= i < n, 1 <= nums[i] <= 100000. -/
  theorem spec_8 (nums : Slice I64) (hb : InputBounds (vals nums)) (rv : I64)
      (hres : Aegis.ValidSubarraySplit.valid_subarray_split nums = ok rv) (hr : 1 ≤ rv.val) :
      ∃ k : ℕ, (k : ℤ) = rv.val ∧ HasChain (vals nums) k := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice I64) (hb : InputBounds (vals nums)) (rv : I64)
        (hres : Aegis.ValidSubarraySplit.valid_subarray_split nums = ok rv) (hr : 1 ≤ rv.val), ∃ k : ℕ, (k : ℤ) = rv.val ∧ HasChain (vals nums) k) := by
    sorry

  /-- Whenever the function returns a result r with r >= 1, for every integer k with 1 <= k < r, there do not exist indices 0 = c_0 < c_1 < ... < c_k = n such that gcd(nums[c_{j-1}], nums[c_j - 1]) > 1 for every j with 1 <= j <= k.
    Preconditions: Let n = len(nums). The input satisfies 1 <= n <= 1000 and, for every i with 0 <= i < n, 1 <= nums[i] <= 100000. -/
  theorem spec_9 (nums : Slice I64) (hb : InputBounds (vals nums)) (rv : I64)
      (hres : Aegis.ValidSubarraySplit.valid_subarray_split nums = ok rv) (hr : 1 ≤ rv.val) :
      ∀ k : ℕ, 1 ≤ k → (k : ℤ) < rv.val → ¬ HasChain (vals nums) k := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice I64) (hb : InputBounds (vals nums)) (rv : I64)
        (hres : Aegis.ValidSubarraySplit.valid_subarray_split nums = ok rv) (hr : 1 ≤ rv.val), ∀ k : ℕ, 1 ≤ k → (k : ℤ) < rv.val → ¬ HasChain (vals nums) k) := by
    sorry

  /-- Whenever the function returns r = -1, for every integer k >= 1 and every choice of indices 0 = c_0 < c_1 < ... < c_k = n, there exists j with 1 <= j <= k such that gcd(nums[c_{j-1}], nums[c_j - 1]) <= 1.
    Preconditions: Let n = len(nums). The input satisfies 1 <= n <= 1000 and, for every i with 0 <= i < n, 1 <= nums[i] <= 100000. -/
  theorem spec_10 (nums : Slice I64) (hb : InputBounds (vals nums)) (rv : I64)
      (hres : Aegis.ValidSubarraySplit.valid_subarray_split nums = ok rv) (hr : rv.val = -1) :
      ∀ (k : ℕ) (c : ℕ → ℕ), 1 ≤ k → IsSplitChain (vals nums) k c →
        ∃ j, 1 ≤ j ∧ j ≤ k ∧ GcdStepLE (vals nums) (c (j - 1)) (c j - 1) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice I64) (hb : InputBounds (vals nums)) (rv : I64)
        (hres : Aegis.ValidSubarraySplit.valid_subarray_split nums = ok rv) (hr : rv.val = -1), ∀ (k : ℕ) (c : ℕ → ℕ), 1 ≤ k → IsSplitChain (vals nums) k c →
          ∃ j, 1 ≤ j ∧ j ≤ k ∧ GcdStepLE (vals nums) (c (j - 1)) (c j - 1)) := by
    sorry

  /-- Whenever the function returns a result r, if there exist an integer k >= 1 and indices 0 = c_0 < c_1 < ... < c_k = n such that gcd(nums[c_{j-1}], nums[c_j - 1]) > 1 for every j with 1 <= j <= k, then r != -1 and r <= k.
    Preconditions: Let n = len(nums). The input satisfies 1 <= n <= 1000 and, for every i with 0 <= i < n, 1 <= nums[i] <= 100000. -/
  theorem spec_11 (nums : Slice I64) (hb : InputBounds (vals nums)) (rv : I64)
      (hres : Aegis.ValidSubarraySplit.valid_subarray_split nums = ok rv)
      (hex : HasSomeChain (vals nums)) :
      rv.val ≠ -1 ∧ ∃ k : ℕ, 1 ≤ k ∧ HasChain (vals nums) k ∧ rv.val ≤ (k : ℤ) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice I64) (hb : InputBounds (vals nums)) (rv : I64)
        (hres : Aegis.ValidSubarraySplit.valid_subarray_split nums = ok rv)
        (hex : HasSomeChain (vals nums)), rv.val ≠ -1 ∧ ∃ k : ℕ, 1 ≤ k ∧ HasChain (vals nums) k ∧ rv.val ≤ (k : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, r = 1 if gcd(nums[0], nums[1]) > 1; r = 2 if gcd(nums[0], nums[1]) = 1 and nums[0] > 1 and nums[1] > 1; and r = -1 otherwise.
    Preconditions: Let n = len(nums). The input satisfies n = 2 and, for every i with 0 <= i < 2, 1 <= nums[i] <= 100000. -/
  theorem spec_12 (nums : Slice I64) (hlen : (vals nums).length = 2)
      (hb : EntriesBounds (vals nums)) (rv : I64)
      (hres : Aegis.ValidSubarraySplit.valid_subarray_split nums = ok rv) :
      (GcdStep (vals nums) 0 1 → rv.val = 1) ∧
        (¬ GcdStep (vals nums) 0 1 → GcdEqOne (vals nums) 0 1 →
          EntryGt (vals nums) 0 → EntryGt (vals nums) 1 → rv.val = 2) ∧
        (¬ GcdStep (vals nums) 0 1 →
          ¬ (GcdEqOne (vals nums) 0 1 ∧ EntryGt (vals nums) 0 ∧ EntryGt (vals nums) 1) →
            rv.val = -1) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice I64) (hlen : (vals nums).length = 2)
        (hb : EntriesBounds (vals nums)) (rv : I64)
        (hres : Aegis.ValidSubarraySplit.valid_subarray_split nums = ok rv), (GcdStep (vals nums) 0 1 → rv.val = 1) ∧
          (¬ GcdStep (vals nums) 0 1 → GcdEqOne (vals nums) 0 1 →
            EntryGt (vals nums) 0 → EntryGt (vals nums) 1 → rv.val = 2) ∧
          (¬ GcdStep (vals nums) 0 1 →
            ¬ (GcdEqOne (vals nums) 0 1 ∧ EntryGt (vals nums) 0 ∧ EntryGt (vals nums) 1) →
              rv.val = -1)) := by
    sorry

  /-- Whenever the function returns a result r, if there exists an index i with 0 <= i < n and nums[i] = 1, then r != n.
    Preconditions: Let n = len(nums). The input satisfies 1 <= n <= 1000 and, for every i with 0 <= i < n, 1 <= nums[i] <= 100000. -/
  theorem spec_13 (nums : Slice I64) (hb : InputBounds (vals nums)) (rv : I64)
      (hres : Aegis.ValidSubarraySplit.valid_subarray_split nums = ok rv)
      (hone : ∃ i : ℕ, EntryEq (vals nums) i 1) :
      rv.val ≠ ((vals nums).length : ℤ) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums : Slice I64) (hb : InputBounds (vals nums)) (rv : I64)
        (hres : Aegis.ValidSubarraySplit.valid_subarray_split nums = ok rv)
        (hone : ∃ i : ℕ, EntryEq (vals nums) i 1), rv.val ≠ ((vals nums).length : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, r != -1 and 2 <= r <= n.
    Preconditions: Let n = len(nums). The input satisfies 1 <= n <= 1000 and, for every i with 0 <= i < n, 1 <= nums[i] <= 100000; moreover nums[i] > 1 for every i with 0 <= i < n, and gcd(nums[0], nums[n-1]) = 1. -/
  theorem spec_14 (nums : Slice I64) (hb : InputBounds (vals nums))
      (hgt : EntriesGtOne (vals nums)) (hgcd : GcdEqOne (vals nums) 0 ((vals nums).length - 1))
      (rv : I64) (hres : Aegis.ValidSubarraySplit.valid_subarray_split nums = ok rv) :
      rv.val ≠ -1 ∧ 2 ≤ rv.val ∧ rv.val ≤ ((vals nums).length : ℤ) := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (nums : Slice I64) (hb : InputBounds (vals nums))
        (hgt : EntriesGtOne (vals nums)) (hgcd : GcdEqOne (vals nums) 0 ((vals nums).length - 1))
        (rv : I64) (hres : Aegis.ValidSubarraySplit.valid_subarray_split nums = ok rv), rv.val ≠ -1 ∧ 2 ≤ rv.val ∧ rv.val ≤ ((vals nums).length : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r with r >= 1, there exist indices 0 = c_0 < c_1 < ... < c_r = n such that (i) for every j with 1 <= j <= r, gcd(nums[c_{j-1}], nums[c_j - 1]) > 1, and (ii) for every i with 0 <= i < n and nums[i] = 1, there exists j with 1 <= j <= r such that c_{j-1} < i < c_j - 1.
    Preconditions: Let n = len(nums). The input satisfies 1 <= n <= 1000 and, for every i with 0 <= i < n, 1 <= nums[i] <= 100000. -/
  theorem spec_15 (nums : Slice I64) (hb : InputBounds (vals nums)) (rv : I64)
      (hres : Aegis.ValidSubarraySplit.valid_subarray_split nums = ok rv) (hr : 1 ≤ rv.val) :
      ∃ k : ℕ, (k : ℤ) = rv.val ∧ ∃ c : ℕ → ℕ,
        IsSplitChain (vals nums) k c ∧
          ∀ i : ℕ, EntryEq (vals nums) i 1 →
            ∃ j, 1 ≤ j ∧ j ≤ k ∧ c (j - 1) < i ∧ i < c j - 1 := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (nums : Slice I64) (hb : InputBounds (vals nums)) (rv : I64)
        (hres : Aegis.ValidSubarraySplit.valid_subarray_split nums = ok rv) (hr : 1 ≤ rv.val), ∃ k : ℕ, (k : ℤ) = rv.val ∧ ∃ c : ℕ → ℕ,
          IsSplitChain (vals nums) k c ∧
            ∀ i : ℕ, EntryEq (vals nums) i 1 →
              ∃ j, 1 ≤ j ∧ j ≤ k ∧ c (j - 1) < i ∧ i < c j - 1) := by
    sorry

  end AegisSpec.ValidSubarraySplit
