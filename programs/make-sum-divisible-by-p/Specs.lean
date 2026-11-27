import Aegis.MinSubarray.Code.Funs

/-!
# Specifications of `Aegis.MinSubarray.min_subarray`

LeetCode problem `make-sum-divisible-by-p`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinSubarray

def vals (nums : Slice I64) : List ℤ := nums.val.map (fun x => x.val)

def total (nums : Slice I64) : ℤ := (vals nums).sum

def winSum (nums : Slice I64) (i l : ℕ) : ℤ := (((vals nums).drop i).take l).sum

def WinOK (nums : Slice I64) (p : ℤ) (i l : ℕ) : Prop :=
  i + l ≤ nums.val.length ∧ (total nums - winSum nums i l) % p = 0

def ExistsWin (nums : Slice I64) (p : ℤ) (l : ℕ) : Prop :=
  l < nums.val.length ∧ ∃ i : ℕ, WinOK nums p i l

def Pre (nums : Slice I64) (p : I64) : Prop :=
  1 ≤ nums.val.length ∧ nums.val.length ≤ 100000 ∧
    (∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000000) ∧
    1 ≤ p.val ∧ p.val ≤ 1000000000

/-- Let T = sum_{i=0}^{n-1} nums[i]. For 0 <= l < n and 0 <= i <= n - l, let S(i,l) = sum_{j=0}^{l-1} nums[i+j], with the empty sum S(i,0) = 0. The function returns a result r and: if there exists l with 0 <= l < n such that for some i with 0 <= i <= n - l we have (T - S(i,l)) mod p = 0, then r is the least such l; if no such l exists, then r = -1.
  Preconditions: Let n = len(nums). The input satisfies 1 <= n <= 100000, for every i with 0 <= i < n we have 1 <= nums[i] <= 1000000000, and 1 <= p <= 1000000000. -/
theorem spec_1 (nums : Slice I64) (p : I64) (hpre : Pre nums p) :
    ∃ r : I64, Aegis.MinSubarray.min_subarray nums p = ok r ∧
      ((∃ l : ℕ, ExistsWin nums p.val l) →
        ∃ l : ℕ, ExistsWin nums p.val l ∧ r.val = (l : ℤ) ∧
          ∀ l' : ℕ, l' < l → ¬ ExistsWin nums p.val l') ∧
      ((¬ ∃ l : ℕ, ExistsWin nums p.val l) → r.val = -1) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice I64) (p : I64) (hpre : Pre nums p), ∃ r : I64, Aegis.MinSubarray.min_subarray nums p = ok r ∧
      ((∃ l : ℕ, ExistsWin nums p.val l) →
        ∃ l : ℕ, ExistsWin nums p.val l ∧ r.val = (l : ℤ) ∧
          ∀ l' : ℕ, l' < l → ¬ ExistsWin nums p.val l') ∧
      ((¬ ∃ l : ℕ, ExistsWin nums p.val l) → r.val = -1)) := by
  sorry

/-- Under the preconditions, the function returns a result r; no failure (panic, overflow, out-of-bounds access, or error result) occurs.
  Preconditions: Let n = len(nums). The input satisfies 1 <= n <= 100000, for every i with 0 <= i < n we have 1 <= nums[i] <= 1000000000, and 1 <= p <= 1000000000. -/
theorem spec_2 (nums : Slice I64) (p : I64) (hpre : Pre nums p) :
    ∃ r : I64, Aegis.MinSubarray.min_subarray nums p = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice I64) (p : I64) (hpre : Pre nums p), ∃ r : I64, Aegis.MinSubarray.min_subarray nums p = ok r) := by
  sorry

/-- Whenever the function returns a result r, -1 <= r < len(nums).
  Preconditions: Let n = len(nums). The input satisfies 1 <= n <= 100000, for every i with 0 <= i < n we have 1 <= nums[i] <= 1000000000, and 1 <= p <= 1000000000. -/
theorem spec_3 (nums : Slice I64) (p : I64) (hpre : Pre nums p) :
    ∀ r : I64, Aegis.MinSubarray.min_subarray nums p = ok r →
      -1 ≤ r.val ∧ r.val < (nums.val.length : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice I64) (p : I64) (hpre : Pre nums p), ∀ r : I64, Aegis.MinSubarray.min_subarray nums p = ok r →
      -1 ≤ r.val ∧ r.val < (nums.val.length : ℤ)) := by
  sorry

/-- Let T = sum_{i=0}^{len(nums)-1} nums[i]. The function returns r and r = 0 if and only if T mod p = 0.
  Preconditions: Let n = len(nums). The input satisfies 1 <= n <= 100000, for every i with 0 <= i < n we have 1 <= nums[i] <= 1000000000, and 1 <= p <= 1000000000. -/
theorem spec_4 (nums : Slice I64) (p : I64) (hpre : Pre nums p) :
    ∃ r : I64, Aegis.MinSubarray.min_subarray nums p = ok r ∧
      (r.val = 0 ↔ total nums % p.val = 0) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice I64) (p : I64) (hpre : Pre nums p), ∃ r : I64, Aegis.MinSubarray.min_subarray nums p = ok r ∧
      (r.val = 0 ↔ total nums % p.val = 0)) := by
  sorry

/-- If len(nums) = 1, then the function returns r with r = 0 exactly when nums[0] mod p = 0, and r = -1 otherwise.
  Preconditions: Let n = len(nums). The input satisfies 1 <= n <= 100000, for every i with 0 <= i < n we have 1 <= nums[i] <= 1000000000, and 1 <= p <= 1000000000. -/
theorem spec_5 (nums : Slice I64) (p : I64) (hpre : Pre nums p)
    (hn : nums.val.length = 1) :
    ∃ r : I64, Aegis.MinSubarray.min_subarray nums p = ok r ∧
      (r.val = 0 ↔ (nums.val[0]'(by omega)).val % p.val = 0) ∧
      ((nums.val[0]'(by omega)).val % p.val ≠ 0 → r.val = -1) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice I64) (p : I64) (hpre : Pre nums p)
    (hn : nums.val.length = 1), ∃ r : I64, Aegis.MinSubarray.min_subarray nums p = ok r ∧
      (r.val = 0 ↔ (nums.val[0]'(by omega)).val % p.val = 0) ∧
      ((nums.val[0]'(by omega)).val % p.val ≠ 0 → r.val = -1)) := by
  sorry

/-- Whenever the function returns r with r >= 0, there exists an integer i with 0 <= i <= len(nums) - r such that (T - sum_{j=0}^{r-1} nums[i+j]) mod p = 0, where T = sum_{k=0}^{len(nums)-1} nums[k].
  Preconditions: Let n = len(nums). The input satisfies 1 <= n <= 100000, for every i with 0 <= i < n we have 1 <= nums[i] <= 1000000000, and 1 <= p <= 1000000000. -/
theorem spec_6 (nums : Slice I64) (p : I64) (hpre : Pre nums p) :
    ∀ r : I64, Aegis.MinSubarray.min_subarray nums p = ok r → 0 ≤ r.val →
      ∃ i : ℕ, i + r.val.toNat ≤ nums.val.length ∧
        (total nums - winSum nums i r.val.toNat) % p.val = 0 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice I64) (p : I64) (hpre : Pre nums p), ∀ r : I64, Aegis.MinSubarray.min_subarray nums p = ok r → 0 ≤ r.val →
      ∃ i : ℕ, i + r.val.toNat ≤ nums.val.length ∧
        (total nums - winSum nums i r.val.toNat) % p.val = 0) := by
  sorry

/-- Whenever the function returns r with r >= 0, for every l with 0 <= l < r and every i with 0 <= i <= len(nums) - l, we have (T - sum_{j=0}^{l-1} nums[i+j]) mod p != 0, where T = sum_{k=0}^{len(nums)-1} nums[k].
  Preconditions: Let n = len(nums). The input satisfies 1 <= n <= 100000, for every i with 0 <= i < n we have 1 <= nums[i] <= 1000000000, and 1 <= p <= 1000000000. -/
theorem spec_7 (nums : Slice I64) (p : I64) (hpre : Pre nums p) :
    ∀ r : I64, Aegis.MinSubarray.min_subarray nums p = ok r → 0 ≤ r.val →
      ∀ (l i : ℕ), (l : ℤ) < r.val → i + l ≤ nums.val.length →
        (total nums - winSum nums i l) % p.val ≠ 0 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice I64) (p : I64) (hpre : Pre nums p), ∀ r : I64, Aegis.MinSubarray.min_subarray nums p = ok r → 0 ≤ r.val →
      ∀ (l i : ℕ), (l : ℤ) < r.val → i + l ≤ nums.val.length →
        (total nums - winSum nums i l) % p.val ≠ 0) := by
  sorry

/-- The function returns r and r = -1 if and only if for every l with 0 <= l < len(nums) and every i with 0 <= i <= len(nums) - l, we have (T - sum_{j=0}^{l-1} nums[i+j]) mod p != 0, where T = sum_{k=0}^{len(nums)-1} nums[k].
  Preconditions: Let n = len(nums). The input satisfies 1 <= n <= 100000, for every i with 0 <= i < n we have 1 <= nums[i] <= 1000000000, and 1 <= p <= 1000000000. -/
theorem spec_8 (nums : Slice I64) (p : I64) (hpre : Pre nums p) :
    ∃ r : I64, Aegis.MinSubarray.min_subarray nums p = ok r ∧
      (r.val = -1 ↔ ¬ ∃ l : ℕ, ExistsWin nums p.val l) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice I64) (p : I64) (hpre : Pre nums p), ∃ r : I64, Aegis.MinSubarray.min_subarray nums p = ok r ∧
      (r.val = -1 ↔ ¬ ∃ l : ℕ, ExistsWin nums p.val l)) := by
  sorry

/-- Let T = sum_{i=0}^{len(nums)-1} nums[i]. If T mod p != 0, then the function returns r and r = 1 if and only if there exists an index i with 0 <= i < len(nums) and (T - nums[i]) mod p = 0.
  Preconditions: Let n = len(nums). The input satisfies 1 <= n <= 100000, for every i with 0 <= i < n we have 1 <= nums[i] <= 1000000000, 1 <= p <= 1000000000, and n >= 2. -/
theorem spec_9 (nums : Slice I64) (p : I64) (hpre : Pre nums p)
    (hn : 2 ≤ nums.val.length) (hT : total nums % p.val ≠ 0) :
    ∃ r : I64, Aegis.MinSubarray.min_subarray nums p = ok r ∧
      (r.val = 1 ↔ ∃ (i : ℕ) (hi : i < nums.val.length),
        (total nums - (nums.val[i]'hi).val) % p.val = 0) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice I64) (p : I64) (hpre : Pre nums p)
    (hn : 2 ≤ nums.val.length) (hT : total nums % p.val ≠ 0), ∃ r : I64, Aegis.MinSubarray.min_subarray nums p = ok r ∧
      (r.val = 1 ↔ ∃ (i : ℕ) (hi : i < nums.val.length),
        (total nums - (nums.val[i]'hi).val) % p.val = 0)) := by
  sorry

/-- Whenever the function returns r with len(nums) >= 2 and r = len(nums) - 1, we have nums[0] mod p = 0 or nums[len(nums)-1] mod p = 0.
  Preconditions: Let n = len(nums). The input satisfies 1 <= n <= 100000, for every i with 0 <= i < n we have 1 <= nums[i] <= 1000000000, and 1 <= p <= 1000000000. -/
theorem spec_10 (nums : Slice I64) (p : I64) (hpre : Pre nums p) :
    ∀ r : I64, Aegis.MinSubarray.min_subarray nums p = ok r → 2 ≤ nums.val.length →
      r.val = (nums.val.length : ℤ) - 1 →
        winSum nums 0 1 % p.val = 0 ∨ winSum nums (nums.val.length - 1) 1 % p.val = 0 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice I64) (p : I64) (hpre : Pre nums p), ∀ r : I64, Aegis.MinSubarray.min_subarray nums p = ok r → 2 ≤ nums.val.length →
      r.val = (nums.val.length : ℤ) - 1 →
        winSum nums 0 1 % p.val = 0 ∨ winSum nums (nums.val.length - 1) 1 % p.val = 0) := by
  sorry

end AegisSpec.MinSubarray
