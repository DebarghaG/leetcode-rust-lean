import Aegis.MinimumSeconds.Code.Funs

/-!
# Specifications of `Aegis.MinimumSeconds.minimum_seconds`

LeetCode problem `minimum-seconds-to-equalize-a-circular-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinimumSeconds

theorem val_length_eq_leng (nums : Slice Std.I64) : nums.val.length = nums.leng := by
  obtain ⟨l, ls, _⟩ := nums
  have h : ∀ (n : ℕ) (ls : Aeneas.Data.ListN.ListN Std.I64 n), ls.toList.length = n := by
    intro n ls
    induction ls with
    | nil => rfl
    | cons x l ih => simp [Aeneas.Data.ListN.ListN.toList, ih]
  exact h l ls

def valueAt (nums : Slice Std.I64) (i : ℕ) : Option ℤ :=
  (nums.val[i]?).map (fun x => x.val)

def cdist (n a b : ℕ) : ℕ :=
  min ((b + n - a) % n) ((a + n - b) % n)

def values (nums : Slice Std.I64) : Finset ℤ :=
  (nums.val.map (fun x => x.val)).toFinset

def occIdx (nums : Slice Std.I64) (v : ℤ) : Set ℕ :=
  {j | valueAt nums j = some v}

noncomputable def minCdist (nums : Slice Std.I64) (v : ℤ) (i : ℕ) : ℕ :=
  sInf {d | ∃ j ∈ occIdx nums v, d = cdist nums.val.length i j}

noncomputable def spread (nums : Slice Std.I64) (v : ℤ) : ℕ :=
  (Finset.range nums.val.length).sup (fun i => minCdist nums v i)

noncomputable def answer (nums : Slice Std.I64) : ℕ :=
  sInf {d | ∃ v ∈ values nums, d = spread nums v}

def freq (nums : Slice Std.I64) (v : ℤ) : ℕ :=
  (nums.val.filter (fun x => x.val = v)).length

def fmax (nums : Slice Std.I64) : ℕ :=
  (values nums).sup (fun v => freq nums v)

def ValBounds (nums : Slice Std.I64) : Prop :=
  ∀ i v, valueAt nums i = some v → 1 ≤ v ∧ v ≤ 1000000000

/-- The function returns a result r and r = min_{v in V} max_{0 <= i < n} min_{0 <= j < n, nums[j]=v} cdist(i,j), where n = len(nums), V is the set of integers v for which there exists j with 0 <= j < n and nums[j]=v, and cdist(a,b) = min(((b-a) mod n), ((a-b) mod n)) with x mod n the least nonnegative residue in [0,n-1]. The outer minimum is over the nonempty finite set V, and each inner minimum is over the nonempty set of indices j with nums[j]=v.
  Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
theorem spec_1 (nums : Slice Std.I64)
    (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hval : ValBounds nums) :
    ∃ r : Std.I64, Aegis.MinimumSeconds.minimum_seconds nums = ok r ∧
      r.val = (answer nums : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hval : ValBounds nums), ∃ r : Std.I64, Aegis.MinimumSeconds.minimum_seconds nums = ok r ∧
      r.val = (answer nums : ℤ)) := by
  sorry

/-- The function returns a result r (that is, it does not fail, panic, or return an error) for every input satisfying the preconditions.
  Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
theorem spec_2 (nums : Slice Std.I64)
    (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hval : ValBounds nums) :
    ∃ r : Std.I64, Aegis.MinimumSeconds.minimum_seconds nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hval : ValBounds nums), ∃ r : Std.I64, Aegis.MinimumSeconds.minimum_seconds nums = ok r) := by
  sorry

/-- The function returns a result r and 0 <= r <= floor(len(nums)/2).
  Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
theorem spec_3 (nums : Slice Std.I64)
    (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hval : ValBounds nums) :
    ∃ r : Std.I64, Aegis.MinimumSeconds.minimum_seconds nums = ok r ∧
      0 ≤ r.val ∧ r.val ≤ ((nums.val.length / 2 : ℕ) : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hval : ValBounds nums), ∃ r : Std.I64, Aegis.MinimumSeconds.minimum_seconds nums = ok r ∧
      0 ≤ r.val ∧ r.val ≤ ((nums.val.length / 2 : ℕ) : ℤ)) := by
  sorry

/-- The function returns a result r and r = 0 if and only if for every i with 0 <= i < len(nums), nums[i] = nums[0].
  Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
theorem spec_4 (nums : Slice Std.I64)
    (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hval : ValBounds nums) :
    ∃ r : Std.I64, Aegis.MinimumSeconds.minimum_seconds nums = ok r ∧
      (r.val = 0 ↔ ∀ i, i < nums.val.length → valueAt nums i = valueAt nums 0) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hval : ValBounds nums), ∃ r : Std.I64, Aegis.MinimumSeconds.minimum_seconds nums = ok r ∧
      (r.val = 0 ↔ ∀ i, i < nums.val.length → valueAt nums i = valueAt nums 0)) := by
  sorry

/-- The function returns a result r and r = 0 if nums[0] = nums[1], and r = 1 if nums[0] != nums[1].
  Preconditions: len(nums) = 2, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
theorem spec_5 (nums : Slice Std.I64) (a b : Std.I64)
    (hlen : nums.val = [a, b])
    (ha_ge : 1 ≤ a.val) (ha_le : a.val ≤ 1000000000)
    (hb_ge : 1 ≤ b.val) (hb_le : b.val ≤ 1000000000) :
    ∃ r : Std.I64, Aegis.MinimumSeconds.minimum_seconds nums = ok r ∧
      (a.val = b.val → r.val = 0) ∧ (a.val ≠ b.val → r.val = 1) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (a b : Std.I64)
    (hlen : nums.val = [a, b])
    (ha_ge : 1 ≤ a.val) (ha_le : a.val ≤ 1000000000)
    (hb_ge : 1 ≤ b.val) (hb_le : b.val ≤ 1000000000), ∃ r : Std.I64, Aegis.MinimumSeconds.minimum_seconds nums = ok r ∧
      (a.val = b.val → r.val = 0) ∧ (a.val ≠ b.val → r.val = 1)) := by
  sorry

/-- The function returns a result r and r = 1.
  Preconditions: len(nums) is even, len(nums) >= 2, len(nums) <= 100000, and there exist distinct integers a and b such that for every i with 0 <= i < len(nums), nums[i] = a when i is even and nums[i] = b when i is odd. -/
theorem spec_6 (nums : Slice Std.I64)
    (hlen_even : nums.val.length % 2 = 0) (hlen_ge : 2 ≤ nums.val.length)
    (hlen_le : nums.val.length ≤ 100000)
    (halt : ∃ a b : ℤ, a ≠ b ∧
      ∀ i, i < nums.val.length → valueAt nums i = some (if i % 2 = 0 then a else b)) :
    ∃ r : Std.I64, Aegis.MinimumSeconds.minimum_seconds nums = ok r ∧ r.val = 1 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_even : nums.val.length % 2 = 0) (hlen_ge : 2 ≤ nums.val.length)
    (hlen_le : nums.val.length ≤ 100000)
    (halt : ∃ a b : ℤ, a ≠ b ∧
      ∀ i, i < nums.val.length → valueAt nums i = some (if i % 2 = 0 then a else b)), ∃ r : Std.I64, Aegis.MinimumSeconds.minimum_seconds nums = ok r ∧ r.val = 1) := by
  sorry

/-- The function returns a result r and there exists an index j with 0 <= j < len(nums) such that r = max_{0 <= i < n} min_{0 <= k < n, nums[k]=nums[j]} cdist(i,k), where n = len(nums) and cdist(a,b) = min(((b-a) mod n), ((a-b) mod n)) with x mod n the least nonnegative residue in [0,n-1].
  Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
theorem spec_7 (nums : Slice Std.I64)
    (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hval : ValBounds nums) :
    ∃ r : Std.I64, Aegis.MinimumSeconds.minimum_seconds nums = ok r ∧
      ∃ (j : ℕ) (v : ℤ), valueAt nums j = some v ∧ r.val = (spread nums v : ℤ) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hval : ValBounds nums), ∃ r : Std.I64, Aegis.MinimumSeconds.minimum_seconds nums = ok r ∧
      ∃ (j : ℕ) (v : ℤ), valueAt nums j = some v ∧ r.val = (spread nums v : ℤ)) := by
  sorry

/-- The function returns a result r and for every index j with 0 <= j < len(nums), r <= max_{0 <= i < n} min_{0 <= k < n, nums[k]=nums[j]} cdist(i,k), where n = len(nums) and cdist(a,b) = min(((b-a) mod n), ((a-b) mod n)) with x mod n the least nonnegative residue in [0,n-1].
  Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
theorem spec_8 (nums : Slice Std.I64)
    (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hval : ValBounds nums) :
    ∃ r : Std.I64, Aegis.MinimumSeconds.minimum_seconds nums = ok r ∧
      ∀ (j : ℕ) (v : ℤ), valueAt nums j = some v → r.val ≤ (spread nums v : ℤ) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hval : ValBounds nums), ∃ r : Std.I64, Aegis.MinimumSeconds.minimum_seconds nums = ok r ∧
      ∀ (j : ℕ) (v : ℤ), valueAt nums j = some v → r.val ≤ (spread nums v : ℤ)) := by
  sorry

/-- Let fmax be the maximum, over all integers v, of the number of indices i with 0 <= i < len(nums) and nums[i] = v. The function returns a result r and r <= floor((len(nums) - fmax + 1)/2).
  Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
theorem spec_9 (nums : Slice Std.I64)
    (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hval : ValBounds nums) :
    ∃ r : Std.I64, Aegis.MinimumSeconds.minimum_seconds nums = ok r ∧
      r.val ≤ (((nums.val.length - fmax nums + 1) / 2 : ℕ) : ℤ) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hval : ValBounds nums), ∃ r : Std.I64, Aegis.MinimumSeconds.minimum_seconds nums = ok r ∧
      r.val ≤ (((nums.val.length - fmax nums + 1) / 2 : ℕ) : ℤ)) := by
  sorry

/-- Let fmax be the maximum, over all integers v, of the number of indices i with 0 <= i < len(nums) and nums[i] = v. The function returns a result r and r >= floor(ceil(len(nums)/fmax)/2), where ceil(x/y) = (x + y - 1)/y for positive integers x and y.
  Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
theorem spec_10 (nums : Slice Std.I64)
    (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hval : ValBounds nums) :
    ∃ r : Std.I64, Aegis.MinimumSeconds.minimum_seconds nums = ok r ∧
      (((nums.val.length + fmax nums - 1) / fmax nums / 2 : ℕ) : ℤ) ≤ r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hval : ValBounds nums), ∃ r : Std.I64, Aegis.MinimumSeconds.minimum_seconds nums = ok r ∧
      (((nums.val.length + fmax nums - 1) / fmax nums / 2 : ℕ) : ℤ) ≤ r.val) := by
  sorry

/-- For every integer k, let nums' be the slice of length len(nums) defined by nums'[i] = nums[(i+k) mod len(nums)] for every i with 0 <= i < len(nums). Whenever minimum_seconds(nums) returns r and minimum_seconds(nums') returns r', we have r' = r.
  Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
theorem spec_11 (nums nums' : Slice Std.I64)
    (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hval : ValBounds nums)
    (hrot : ∃ k : ℕ, nums'.val = nums.val.rotate k) :
    ∀ (r r' : Std.I64), Aegis.MinimumSeconds.minimum_seconds nums = ok r →
      Aegis.MinimumSeconds.minimum_seconds nums' = ok r' → r' = r := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums nums' : Slice Std.I64)
    (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hval : ValBounds nums)
    (hrot : ∃ k : ℕ, nums'.val = nums.val.rotate k), ∀ (r r' : Std.I64), Aegis.MinimumSeconds.minimum_seconds nums = ok r →
      Aegis.MinimumSeconds.minimum_seconds nums' = ok r' → r' = r) := by
  sorry

/-- Whenever minimum_seconds(nums) returns r and minimum_seconds(nums') returns r', we have r' = r.
  Preconditions: nums and nums' are slices of the same length n with n >= 1, n <= 100000, and for every i with 0 <= i < n, both nums[i] and nums'[i] lie in [1, 1000000000]. Moreover, for every i and j with 0 <= i < n and 0 <= j < n, nums[i] = nums[j] if and only if nums'[i] = nums'[j]. -/
theorem spec_12 (nums nums' : Slice Std.I64)
    (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hlen_eq : nums'.val.length = nums.val.length)
    (hval : ValBounds nums) (hval' : ValBounds nums')
    (hpat : ∀ i j, i < nums.val.length → j < nums.val.length →
      (valueAt nums i = valueAt nums j ↔ valueAt nums' i = valueAt nums' j)) :
    ∀ (r r' : Std.I64), Aegis.MinimumSeconds.minimum_seconds nums = ok r →
      Aegis.MinimumSeconds.minimum_seconds nums' = ok r' → r' = r := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums nums' : Slice Std.I64)
    (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hlen_eq : nums'.val.length = nums.val.length)
    (hval : ValBounds nums) (hval' : ValBounds nums')
    (hpat : ∀ i j, i < nums.val.length → j < nums.val.length →
      (valueAt nums i = valueAt nums j ↔ valueAt nums' i = valueAt nums' j)), ∀ (r r' : Std.I64), Aegis.MinimumSeconds.minimum_seconds nums = ok r →
      Aegis.MinimumSeconds.minimum_seconds nums' = ok r' → r' = r) := by
  sorry

end AegisSpec.MinimumSeconds
