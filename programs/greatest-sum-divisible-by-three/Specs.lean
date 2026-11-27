import Aegis.MaxSumDivThree.Code.Funs

/-!
# Specifications of `Aegis.MaxSumDivThree.max_sum_div_three`

LeetCode problem `greatest-sum-divisible-by-three`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxSumDivThree

def vals (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

def idxSet (nums : Slice Std.I64) : Finset ℕ := Finset.range (vals nums).length

def elemAt (nums : Slice Std.I64) (i : ℕ) : Int :=
  if h : i < (vals nums).length then (vals nums).get ⟨i, h⟩ else 0

def idxSum (nums : Slice Std.I64) (I : Finset ℕ) : Int := I.sum (fun i => elemAt nums i)

def total (nums : Slice Std.I64) : Int := idxSum nums (idxSet nums)

def idxSetDivThree (nums : Slice Std.I64) : Finset ℕ :=
  (idxSet nums).filter (fun i => (3 : Int) ∣ elemAt nums i)

def Pre (nums : Slice Std.I64) : Prop :=
  1 ≤ (vals nums).length ∧ (vals nums).length ≤ 40000 ∧
    ∀ i ∈ idxSet nums, 1 ≤ elemAt nums i ∧ elemAt nums i ≤ 10000

/-- The function returns a result r that is the maximum possible sum of selected elements of nums with the constraint that the selected sum is divisible by 3. Formally, using subsets of indices: r is divisible by 3; there exists a subset I of {0,...,len(nums)-1} with Σ_{i∈I} nums[i] = r; and for every subset J of {0,...,len(nums)-1} with Σ_{j∈J} nums[j] divisible by 3, Σ_{j∈J} nums[j] <= r. The empty subset is allowed, so the value 0 is always available.
  Preconditions: len(nums) >= 1 and len(nums) <= 40000, and for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. -/
theorem spec_1 (nums : Slice Std.I64) (hpre : Pre nums) :
    ∃ r : Std.I64,
      Aegis.MaxSumDivThree.max_sum_div_three nums = ok r ∧
        (3 : Int) ∣ r.val ∧
        (∃ I : Finset ℕ, I ⊆ idxSet nums ∧ idxSum nums I = r.val) ∧
        (∀ J : Finset ℕ, J ⊆ idxSet nums → (3 : Int) ∣ idxSum nums J → idxSum nums J ≤ r.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (hpre : Pre nums), ∃ r : Std.I64,
      Aegis.MaxSumDivThree.max_sum_div_three nums = ok r ∧
        (3 : Int) ∣ r.val ∧
        (∃ I : Finset ℕ, I ⊆ idxSet nums ∧ idxSum nums I = r.val) ∧
        (∀ J : Finset ℕ, J ⊆ idxSet nums → (3 : Int) ∣ idxSum nums J → idxSum nums J ≤ r.val)) := by
  sorry

/-- The function returns a result r (it does not fail, panic, or overflow) for every input satisfying the preconditions.
  Preconditions: len(nums) >= 1 and len(nums) <= 40000, and for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. -/
theorem spec_2 (nums : Slice Std.I64) (hpre : Pre nums) :
    ∃ r : Std.I64, Aegis.MaxSumDivThree.max_sum_div_three nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (hpre : Pre nums), ∃ r : Std.I64, Aegis.MaxSumDivThree.max_sum_div_three nums = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r <= Σ_{i=0}^{len(nums)-1} nums[i].
  Preconditions: len(nums) >= 1 and len(nums) <= 40000, and for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. -/
theorem spec_3 (nums : Slice Std.I64) (hpre : Pre nums) (r : Std.I64)
    (hr : Aegis.MaxSumDivThree.max_sum_div_three nums = ok r) :
    0 ≤ r.val ∧ r.val ≤ total nums := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (hpre : Pre nums) (r : Std.I64)
    (hr : Aegis.MaxSumDivThree.max_sum_div_three nums = ok r), 0 ≤ r.val ∧ r.val ≤ total nums) := by
  sorry

/-- Whenever the function returns a result r, r is divisible by 3 (there exists an integer k with r = 3*k).
  Preconditions: len(nums) >= 1 and len(nums) <= 40000, and for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. -/
theorem spec_4 (nums : Slice Std.I64) (hpre : Pre nums) (r : Std.I64)
    (hr : Aegis.MaxSumDivThree.max_sum_div_three nums = ok r) :
    ∃ k : Int, r.val = 3 * k := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (hpre : Pre nums) (r : Std.I64)
    (hr : Aegis.MaxSumDivThree.max_sum_div_three nums = ok r), ∃ k : Int, r.val = 3 * k) := by
  sorry

/-- Whenever the function returns a result r, there exists a subset I of {0,...,len(nums)-1} such that Σ_{i∈I} nums[i] = r. The empty subset is allowed.
  Preconditions: len(nums) >= 1 and len(nums) <= 40000, and for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. -/
theorem spec_5 (nums : Slice Std.I64) (hpre : Pre nums) (r : Std.I64)
    (hr : Aegis.MaxSumDivThree.max_sum_div_three nums = ok r) :
    ∃ I : Finset ℕ, I ⊆ idxSet nums ∧ idxSum nums I = r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (hpre : Pre nums) (r : Std.I64)
    (hr : Aegis.MaxSumDivThree.max_sum_div_three nums = ok r), ∃ I : Finset ℕ, I ⊆ idxSet nums ∧ idxSum nums I = r.val) := by
  sorry

/-- Whenever the function returns a result r, for every subset J of {0,...,len(nums)-1} whose sum Σ_{j∈J} nums[j] is divisible by 3, we have Σ_{j∈J} nums[j] <= r.
  Preconditions: len(nums) >= 1 and len(nums) <= 40000, and for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. -/
theorem spec_6 (nums : Slice Std.I64) (hpre : Pre nums) (r : Std.I64)
    (hr : Aegis.MaxSumDivThree.max_sum_div_three nums = ok r) :
    ∀ J : Finset ℕ, J ⊆ idxSet nums → (3 : Int) ∣ idxSum nums J → idxSum nums J ≤ r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (hpre : Pre nums) (r : Std.I64)
    (hr : Aegis.MaxSumDivThree.max_sum_div_three nums = ok r), ∀ J : Finset ℕ, J ⊆ idxSet nums → (3 : Int) ∣ idxSum nums J → idxSum nums J ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if there is no nonempty subset I of {0,...,len(nums)-1} whose sum Σ_{i∈I} nums[i] is divisible by 3.
  Preconditions: len(nums) >= 1 and len(nums) <= 40000, and for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. -/
theorem spec_7 (nums : Slice Std.I64) (hpre : Pre nums) (r : Std.I64)
    (hr : Aegis.MaxSumDivThree.max_sum_div_three nums = ok r) :
    r.val = 0 ↔ ∀ I : Finset ℕ, I ⊆ idxSet nums → I.Nonempty → ¬ (3 : Int) ∣ idxSum nums I := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (hpre : Pre nums) (r : Std.I64)
    (hr : Aegis.MaxSumDivThree.max_sum_div_three nums = ok r), r.val = 0 ↔ ∀ I : Finset ℕ, I ⊆ idxSet nums → I.Nonempty → ¬ (3 : Int) ∣ idxSum nums I) := by
  sorry

/-- Whenever the function returns a result r, if Σ_{i=0}^{len(nums)-1} nums[i] is divisible by 3, then r = Σ_{i=0}^{len(nums)-1} nums[i].
  Preconditions: len(nums) >= 1 and len(nums) <= 40000, and for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. -/
theorem spec_8 (nums : Slice Std.I64) (hpre : Pre nums) (r : Std.I64)
    (hr : Aegis.MaxSumDivThree.max_sum_div_three nums = ok r)
    (hT : (3 : Int) ∣ total nums) :
    r.val = total nums := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (hpre : Pre nums) (r : Std.I64)
    (hr : Aegis.MaxSumDivThree.max_sum_div_three nums = ok r)
    (hT : (3 : Int) ∣ total nums), r.val = total nums) := by
  sorry

/-- Let T = Σ_{i=0}^{len(nums)-1} nums[i], and let d be the integer in {0,1,2} such that T is congruent to d modulo 3. Let m be the minimum value of Σ_{i∈R} nums[i] over all subsets R of {0,...,len(nums)-1} for which Σ_{i∈R} nums[i] is congruent to d modulo 3; when d=0 the empty subset is allowed and gives m=0. Whenever the function returns a result r, r = T - m.
  Preconditions: len(nums) >= 1 and len(nums) <= 40000, and for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. -/
theorem spec_9 (nums : Slice Std.I64) (hpre : Pre nums) (r : Std.I64)
    (hr : Aegis.MaxSumDivThree.max_sum_div_three nums = ok r) :
    ∀ d m : Int,
      (d = 0 ∨ d = 1 ∨ d = 2) →
        (3 : Int) ∣ total nums - d →
          (∃ R : Finset ℕ, R ⊆ idxSet nums ∧ idxSum nums R = m ∧ (3 : Int) ∣ idxSum nums R - d) →
            (∀ R : Finset ℕ, R ⊆ idxSet nums → (3 : Int) ∣ idxSum nums R - d → m ≤ idxSum nums R) →
              r.val = total nums - m := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64) (hpre : Pre nums) (r : Std.I64)
    (hr : Aegis.MaxSumDivThree.max_sum_div_three nums = ok r), ∀ d m : Int,
      (d = 0 ∨ d = 1 ∨ d = 2) →
        (3 : Int) ∣ total nums - d →
          (∃ R : Finset ℕ, R ⊆ idxSet nums ∧ idxSum nums R = m ∧ (3 : Int) ∣ idxSum nums R - d) →
            (∀ R : Finset ℕ, R ⊆ idxSet nums → (3 : Int) ∣ idxSum nums R - d → m ≤ idxSum nums R) →
              r.val = total nums - m) := by
  sorry

/-- Whenever the function returns a result r, r >= Σ_{i with 0 <= i < len(nums) and nums[i] is divisible by 3} nums[i].
  Preconditions: len(nums) >= 1 and len(nums) <= 40000, and for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. -/
theorem spec_10 (nums : Slice Std.I64) (hpre : Pre nums) (r : Std.I64)
    (hr : Aegis.MaxSumDivThree.max_sum_div_three nums = ok r) :
    idxSum nums (idxSetDivThree nums) ≤ r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64) (hpre : Pre nums) (r : Std.I64)
    (hr : Aegis.MaxSumDivThree.max_sum_div_three nums = ok r), idxSum nums (idxSetDivThree nums) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, if T = Σ_{i=0}^{len(nums)-1} nums[i] is not divisible by 3, then r < T.
  Preconditions: len(nums) >= 1 and len(nums) <= 40000, and for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. -/
theorem spec_11 (nums : Slice Std.I64) (hpre : Pre nums) (r : Std.I64)
    (hr : Aegis.MaxSumDivThree.max_sum_div_three nums = ok r)
    (hT : ¬ (3 : Int) ∣ total nums) :
    r.val < total nums := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64) (hpre : Pre nums) (r : Std.I64)
    (hr : Aegis.MaxSumDivThree.max_sum_div_three nums = ok r)
    (hT : ¬ (3 : Int) ∣ total nums), r.val < total nums) := by
  sorry

/-- Whenever the function returns a result r, if len(nums) = 1, then r = nums[0] when nums[0] is divisible by 3, and r = 0 otherwise.
  Preconditions: len(nums) >= 1 and len(nums) <= 40000, and for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. -/
theorem spec_12 (nums : Slice Std.I64) (hpre : Pre nums) (r : Std.I64)
    (hr : Aegis.MaxSumDivThree.max_sum_div_three nums = ok r)
    (hlen : (vals nums).length = 1) :
    r.val = if (3 : Int) ∣ elemAt nums 0 then elemAt nums 0 else 0 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64) (hpre : Pre nums) (r : Std.I64)
    (hr : Aegis.MaxSumDivThree.max_sum_div_three nums = ok r)
    (hlen : (vals nums).length = 1), r.val = if (3 : Int) ∣ elemAt nums 0 then elemAt nums 0 else 0) := by
  sorry

/-- Whenever the function returns a result r, for every subset I of {0,...,len(nums)-1} with Σ_{i∈I} nums[i] = r and for every index j with 0 <= j < len(nums) such that nums[j] is divisible by 3, we have j ∈ I.
  Preconditions: len(nums) >= 1 and len(nums) <= 40000, and for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. -/
theorem spec_13 (nums : Slice Std.I64) (hpre : Pre nums) (r : Std.I64)
    (hr : Aegis.MaxSumDivThree.max_sum_div_three nums = ok r) :
    ∀ I : Finset ℕ, I ⊆ idxSet nums → idxSum nums I = r.val →
      ∀ j : ℕ, j ∈ idxSet nums → (3 : Int) ∣ elemAt nums j → j ∈ I := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums : Slice Std.I64) (hpre : Pre nums) (r : Std.I64)
    (hr : Aegis.MaxSumDivThree.max_sum_div_three nums = ok r), ∀ I : Finset ℕ, I ⊆ idxSet nums → idxSum nums I = r.val →
      ∀ j : ℕ, j ∈ idxSet nums → (3 : Int) ∣ elemAt nums j → j ∈ I) := by
  sorry

/-- Whenever the function returns a result r, for every subset I of {0,...,len(nums)-1} with Σ_{i∈I} nums[i] = r, there is no nonempty subset J of the complement {0,...,len(nums)-1} \ I such that Σ_{j∈J} nums[j] is divisible by 3.
  Preconditions: len(nums) >= 1 and len(nums) <= 40000, and for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. -/
theorem spec_14 (nums : Slice Std.I64) (hpre : Pre nums) (r : Std.I64)
    (hr : Aegis.MaxSumDivThree.max_sum_div_three nums = ok r) :
    ∀ I : Finset ℕ, I ⊆ idxSet nums → idxSum nums I = r.val →
      ∀ J : Finset ℕ, J ⊆ idxSet nums \ I → J.Nonempty → ¬ (3 : Int) ∣ idxSum nums J := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (nums : Slice Std.I64) (hpre : Pre nums) (r : Std.I64)
    (hr : Aegis.MaxSumDivThree.max_sum_div_three nums = ok r), ∀ I : Finset ℕ, I ⊆ idxSet nums → idxSum nums I = r.val →
      ∀ J : Finset ℕ, J ⊆ idxSet nums \ I → J.Nonempty → ¬ (3 : Int) ∣ idxSum nums J) := by
  sorry

/-- For every permutation p of {0,...,len(nums)-1}, let nums' be the slice of length len(nums) with nums'[i] = nums[p(i)] for all i. Whenever the function returns r on nums and r' on nums', we have r = r'.
  Preconditions: len(nums) >= 1 and len(nums) <= 40000, and for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. -/
theorem spec_15 (nums : Slice Std.I64) (hpre : Pre nums) :
    ∀ (p : Equiv.Perm (Fin (vals nums).length)) (nums' : Slice Std.I64),
      vals nums' = List.ofFn (fun i : Fin (vals nums).length => (vals nums).get (p i)) →
        ∀ r r' : Std.I64,
          Aegis.MaxSumDivThree.max_sum_div_three nums = ok r →
            Aegis.MaxSumDivThree.max_sum_div_three nums' = ok r' → r = r' := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (nums : Slice Std.I64) (hpre : Pre nums), ∀ (p : Equiv.Perm (Fin (vals nums).length)) (nums' : Slice Std.I64),
      vals nums' = List.ofFn (fun i : Fin (vals nums).length => (vals nums).get (p i)) →
        ∀ r r' : Std.I64,
          Aegis.MaxSumDivThree.max_sum_div_three nums = ok r →
            Aegis.MaxSumDivThree.max_sum_div_three nums' = ok r' → r = r') := by
  sorry

end AegisSpec.MaxSumDivThree
