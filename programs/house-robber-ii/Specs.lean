import Aegis.Rob.Code.Funs

/-!
# Specifications of `Aegis.Rob.rob`

LeetCode problem `house-robber-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.Rob

namespace AegisSpec.Rob

def valAt (nums : Slice Std.I64) (i : Int) : Int :=
  match nums.val[i.toNat]? with
  | some x => x.val
  | none => 0

theorem valAt_eq_getElem (nums : Slice Std.I64) (i : Nat) (h : i < nums.val.length) :
    valAt nums (i : Int) = (nums.val[i]'h).val := by
  simp [valAt, List.getElem?_eq_getElem h]

def IsCycleIndep (n : Int) (S : Finset Int) : Prop :=
  (∀ i ∈ S, 0 ≤ i ∧ i < n) ∧
    ∀ i ∈ S, ∀ j ∈ S, i ≠ j → j ≠ (i + 1) % n ∧ i ≠ (j + 1) % n

theorem isCycleIndep_empty (n : Int) : IsCycleIndep n ∅ := by
  simp [IsCycleIndep]

def cycleSum (nums : Slice Std.I64) (S : Finset Int) : Int := S.sum (fun i => valAt nums i)

instance decidableIsCycleIndep (n : Int) (S : Finset Int) : Decidable (IsCycleIndep n S) := by
  unfold IsCycleIndep
  infer_instance

def cycleCandidates (n : Nat) : Finset (Finset Int) :=
  ((Finset.range n).image (fun k : Nat => (k : Int))).powerset.filter
    (fun S => IsCycleIndep (n : Nat) S)

theorem mem_cycleCandidates {n : Nat} {S : Finset Int} :
    S ∈ cycleCandidates n ↔ IsCycleIndep (n : Int) S := by
  unfold cycleCandidates
  rw [Finset.mem_filter, Finset.mem_powerset]
  constructor
  · rintro ⟨-, h⟩
    exact h
  · intro h
    refine ⟨?_, h⟩
    intro x hx
    obtain ⟨h0, hn⟩ := h.1 x hx
    refine Finset.mem_image.mpr ⟨x.toNat, Finset.mem_range.mpr (by omega), ?_⟩
    simp [Int.toNat_of_nonneg h0]

def bestCycleSum (nums : Slice Std.I64) : Int :=
  (cycleCandidates nums.val.length).sup'
    ⟨∅, by
      refine Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset _, ?_⟩
      simp [IsCycleIndep]⟩
    (fun S => cycleSum nums S)

theorem cycleSum_le_bestCycleSum (nums : Slice Std.I64) {S : Finset Int}
    (h : IsCycleIndep (nums.val.length : Int) S) : cycleSum nums S ≤ bestCycleSum nums := by
  unfold bestCycleSum
  exact Finset.le_sup' _ (mem_cycleCandidates.mpr h)

theorem bestCycleSum_le (nums : Slice Std.I64) {m : Int}
    (h : ∀ S : Finset Int, IsCycleIndep (nums.val.length : Int) S → cycleSum nums S ≤ m) :
    bestCycleSum nums ≤ m := by
  unfold bestCycleSum
  exact Finset.sup'_le _ _ (fun S hS => h S (mem_cycleCandidates.mp hS))

theorem exists_isCycleIndep_cycleSum_eq_bestCycleSum (nums : Slice Std.I64) :
    ∃ S : Finset Int, IsCycleIndep (nums.val.length : Int) S ∧ bestCycleSum nums = cycleSum nums S := by
  unfold bestCycleSum
  obtain ⟨S, hS, hEq⟩ := Finset.exists_mem_eq_sup' (s := cycleCandidates nums.val.length)
    ⟨∅, by
      refine Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset _, ?_⟩
      simp [IsCycleIndep]⟩ (fun S => cycleSum nums S)
  exact ⟨S, mem_cycleCandidates.mp hS, hEq⟩

def listMax : List Int → Int
  | [] => 0
  | a :: l => l.foldr max a

def sliceMax (nums : Slice Std.I64) : Int := listMax (nums.val.map fun x => x.val)

def fiveCyclePairMax (nums : Slice Std.I64) : Int :=
  (Finset.range 5).sup' ⟨0, by decide⟩
    (fun i => valAt nums (i : Int) + valAt nums (((i : Int) + 2) % 5))

/-- Whenever the function returns a result r, r equals the maximum of the set of all sums sum_{i in S} nums[i], where S is a finite set of integers such that (a) every i in S satisfies 0 <= i < len(nums), and (b) for every i in S and j in S with i != j, neither j = (i + 1) mod len(nums) nor i = (j + 1) mod len(nums). The empty set S is allowed and gives sum 0. Thus S selects pairwise non-adjacent houses on the cycle with indices 0,...,len(nums)-1, where the first and last indices are adjacent; for len(nums)=1 condition (b) is vacuous.
  Preconditions: len(nums) is an integer with 1 <= len(nums) <= 100, and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000. -/
theorem spec_1 (nums : Slice Std.I64)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100)
    (hval : ∀ i : Nat, i < nums.val.length → 0 ≤ valAt nums i ∧ valAt nums i ≤ 1000)
    (r : Std.I64) (hr : rob nums = ok r) :
    r.val = bestCycleSum nums := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100)
    (hval : ∀ i : Nat, i < nums.val.length → 0 ≤ valAt nums i ∧ valAt nums i ≤ 1000)
    (r : Std.I64) (hr : rob nums = ok r), r.val = bestCycleSum nums) := by
  sorry

/-- For every nums satisfying the preconditions, the function returns a result r; it does not fail, panic, or overflow.
  Preconditions: len(nums) is an integer with 1 <= len(nums) <= 100, and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000. -/
theorem spec_2 (nums : Slice Std.I64)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100)
    (hval : ∀ i : Nat, i < nums.val.length → 0 ≤ valAt nums i ∧ valAt nums i ≤ 1000) :
    ∃ r : Std.I64, rob nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100)
    (hval : ∀ i : Nat, i < nums.val.length → 0 ≤ valAt nums i ∧ valAt nums i ≤ 1000), ∃ r : Std.I64, rob nums = ok r) := by
  sorry

/-- Whenever the function returns a result r, r <= sum_{i=0}^{len(nums)-1} nums[i].
  Preconditions: len(nums) is an integer with 1 <= len(nums) <= 100, and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000. -/
theorem spec_3 (nums : Slice Std.I64)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100)
    (hval : ∀ i : Nat, i < nums.val.length → 0 ≤ valAt nums i ∧ valAt nums i ≤ 1000)
    (r : Std.I64) (hr : rob nums = ok r) :
    r.val ≤ (nums.val.map fun x => x.val).sum := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100)
    (hval : ∀ i : Nat, i < nums.val.length → 0 ≤ valAt nums i ∧ valAt nums i ≤ 1000)
    (r : Std.I64) (hr : rob nums = ok r), r.val ≤ (nums.val.map fun x => x.val).sum) := by
  sorry

/-- Whenever the function returns a result r, r >= max{ nums[i] | 0 <= i < len(nums) }.
  Preconditions: len(nums) is an integer with 1 <= len(nums) <= 100, and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000. -/
theorem spec_4 (nums : Slice Std.I64)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100)
    (hval : ∀ i : Nat, i < nums.val.length → 0 ≤ valAt nums i ∧ valAt nums i ≤ 1000)
    (r : Std.I64) (hr : rob nums = ok r) :
    sliceMax nums ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100)
    (hval : ∀ i : Nat, i < nums.val.length → 0 ≤ valAt nums i ∧ valAt nums i ≤ 1000)
    (r : Std.I64) (hr : rob nums = ok r), sliceMax nums ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r = nums[0].
  Preconditions: len(nums) = 1, and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000. -/
theorem spec_5 (nums : Slice Std.I64)
    (hlen : nums.val.length = 1)
    (hval : ∀ i : Nat, i < nums.val.length → 0 ≤ valAt nums i ∧ valAt nums i ≤ 1000)
    (r : Std.I64) (hr : rob nums = ok r) :
    r.val = valAt nums 0 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : nums.val.length = 1)
    (hval : ∀ i : Nat, i < nums.val.length → 0 ≤ valAt nums i ∧ valAt nums i ≤ 1000)
    (r : Std.I64) (hr : rob nums = ok r), r.val = valAt nums 0) := by
  sorry

/-- Whenever the function returns a result r, r = max(nums[0], nums[1]).
  Preconditions: len(nums) = 2, and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000. -/
theorem spec_6 (nums : Slice Std.I64)
    (hlen : nums.val.length = 2)
    (hval : ∀ i : Nat, i < nums.val.length → 0 ≤ valAt nums i ∧ valAt nums i ≤ 1000)
    (r : Std.I64) (hr : rob nums = ok r) :
    r.val = max (valAt nums 0) (valAt nums 1) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : nums.val.length = 2)
    (hval : ∀ i : Nat, i < nums.val.length → 0 ≤ valAt nums i ∧ valAt nums i ≤ 1000)
    (r : Std.I64) (hr : rob nums = ok r), r.val = max (valAt nums 0) (valAt nums 1)) := by
  sorry

/-- Whenever the function returns a result r, r = max(nums[0], nums[1], nums[2]).
  Preconditions: len(nums) = 3, and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000. -/
theorem spec_7 (nums : Slice Std.I64)
    (hlen : nums.val.length = 3)
    (hval : ∀ i : Nat, i < nums.val.length → 0 ≤ valAt nums i ∧ valAt nums i ≤ 1000)
    (r : Std.I64) (hr : rob nums = ok r) :
    r.val = max (valAt nums 0) (max (valAt nums 1) (valAt nums 2)) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : nums.val.length = 3)
    (hval : ∀ i : Nat, i < nums.val.length → 0 ≤ valAt nums i ∧ valAt nums i ≤ 1000)
    (r : Std.I64) (hr : rob nums = ok r), r.val = max (valAt nums 0) (max (valAt nums 1) (valAt nums 2))) := by
  sorry

/-- Whenever the function returns a result r, r = max(nums[0] + nums[2], nums[1] + nums[3]).
  Preconditions: len(nums) = 4, and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000. -/
theorem spec_8 (nums : Slice Std.I64)
    (hlen : nums.val.length = 4)
    (hval : ∀ i : Nat, i < nums.val.length → 0 ≤ valAt nums i ∧ valAt nums i ≤ 1000)
    (r : Std.I64) (hr : rob nums = ok r) :
    r.val = max (valAt nums 0 + valAt nums 2) (valAt nums 1 + valAt nums 3) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : nums.val.length = 4)
    (hval : ∀ i : Nat, i < nums.val.length → 0 ≤ valAt nums i ∧ valAt nums i ≤ 1000)
    (r : Std.I64) (hr : rob nums = ok r), r.val = max (valAt nums 0 + valAt nums 2) (valAt nums 1 + valAt nums 3)) := by
  sorry

/-- Whenever the function returns a result r, there exists a finite set S of integers such that (a) every i in S satisfies 0 <= i < len(nums), (b) for every i in S and j in S with i != j, neither j = (i + 1) mod len(nums) nor i = (j + 1) mod len(nums), and (c) r = sum_{i in S} nums[i]. The empty set S is allowed.
  Preconditions: len(nums) is an integer with 1 <= len(nums) <= 100, and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000. -/
theorem spec_9 (nums : Slice Std.I64)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100)
    (hval : ∀ i : Nat, i < nums.val.length → 0 ≤ valAt nums i ∧ valAt nums i ≤ 1000)
    (r : Std.I64) (hr : rob nums = ok r) :
    ∃ S : Finset Int, IsCycleIndep (nums.val.length : Int) S ∧ r.val = cycleSum nums S := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100)
    (hval : ∀ i : Nat, i < nums.val.length → 0 ≤ valAt nums i ∧ valAt nums i ≤ 1000)
    (r : Std.I64) (hr : rob nums = ok r), ∃ S : Finset Int, IsCycleIndep (nums.val.length : Int) S ∧ r.val = cycleSum nums S) := by
  sorry

/-- Whenever the function returns r on nums and returns r' on nums', r = r'.
  Preconditions: Let n = len(nums) = len(nums'). Both n and the values satisfy 1 <= n <= 100 and, for every i with 0 <= i < n, 0 <= nums[i] <= 1000 and 0 <= nums'[i] <= 1000. There is an integer k with 0 <= k < n such that for every i with 0 <= i < n, nums'[i] = nums[(i + k) mod n]. -/
theorem spec_10 (nums nums' : Slice Std.I64) (k : Nat)
    (hlen : nums'.val.length = nums.val.length)
    (hn : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100)
    (hval : ∀ i : Nat, i < nums.val.length → 0 ≤ valAt nums i ∧ valAt nums i ≤ 1000)
    (hval' : ∀ i : Nat, i < nums'.val.length → 0 ≤ valAt nums' i ∧ valAt nums' i ≤ 1000)
    (hk : k < nums.val.length)
    (hrot : ∀ i : Nat, i < nums.val.length →
      valAt nums' i = valAt nums ((i + k) % nums.val.length : Nat))
    (r r' : Std.I64) (hr : rob nums = ok r) (hr' : rob nums' = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (k : Nat)
    (hlen : nums'.val.length = nums.val.length)
    (hn : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100)
    (hval : ∀ i : Nat, i < nums.val.length → 0 ≤ valAt nums i ∧ valAt nums i ≤ 1000)
    (hval' : ∀ i : Nat, i < nums'.val.length → 0 ≤ valAt nums' i ∧ valAt nums' i ≤ 1000)
    (hk : k < nums.val.length)
    (hrot : ∀ i : Nat, i < nums.val.length →
      valAt nums' i = valAt nums ((i + k) % nums.val.length : Nat))
    (r r' : Std.I64) (hr : rob nums = ok r) (hr' : rob nums' = ok r'), r.val = r'.val) := by
  sorry

/-- Whenever the function returns r on nums and returns r' on nums', r <= r'.
  Preconditions: Let n = len(nums) = len(nums'). Both n and the values satisfy 1 <= n <= 100 and, for every i with 0 <= i < n, 0 <= nums[i] <= 1000 and 0 <= nums'[i] <= 1000. For every i with 0 <= i < n, nums[i] <= nums'[i]. -/
theorem spec_11 (nums nums' : Slice Std.I64)
    (hlen : nums'.val.length = nums.val.length)
    (hn : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100)
    (hval : ∀ i : Nat, i < nums.val.length → 0 ≤ valAt nums i ∧ valAt nums i ≤ 1000)
    (hval' : ∀ i : Nat, i < nums'.val.length → 0 ≤ valAt nums' i ∧ valAt nums' i ≤ 1000)
    (hle : ∀ i : Nat, i < nums.val.length → valAt nums i ≤ valAt nums' i)
    (r r' : Std.I64) (hr : rob nums = ok r) (hr' : rob nums' = ok r') :
    r.val ≤ r'.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums nums' : Slice Std.I64)
    (hlen : nums'.val.length = nums.val.length)
    (hn : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100)
    (hval : ∀ i : Nat, i < nums.val.length → 0 ≤ valAt nums i ∧ valAt nums i ≤ 1000)
    (hval' : ∀ i : Nat, i < nums'.val.length → 0 ≤ valAt nums' i ∧ valAt nums' i ≤ 1000)
    (hle : ∀ i : Nat, i < nums.val.length → valAt nums i ≤ valAt nums' i)
    (r r' : Std.I64) (hr : rob nums = ok r) (hr' : rob nums' = ok r'), r.val ≤ r'.val) := by
  sorry

/-- Whenever the function returns a result r, if n = 1 then r = v; if n >= 2 then r = floor(n/2) * v.
  Preconditions: Let n = len(nums). 1 <= n <= 100, and there is an integer v with 0 <= v <= 1000 such that for every i with 0 <= i < n, nums[i] = v. -/
theorem spec_12 (nums : Slice Std.I64) (v : Int)
    (hn : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100)
    (hv : 0 ≤ v ∧ v ≤ 1000)
    (hconst : ∀ i : Nat, i < nums.val.length → valAt nums i = v)
    (r : Std.I64) (hr : rob nums = ok r) :
    (nums.val.length = 1 → r.val = v) ∧
      (2 ≤ nums.val.length → r.val = ((nums.val.length / 2 : Nat) : Int) * v) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64) (v : Int)
    (hn : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100)
    (hv : 0 ≤ v ∧ v ≤ 1000)
    (hconst : ∀ i : Nat, i < nums.val.length → valAt nums i = v)
    (r : Std.I64) (hr : rob nums = ok r), (nums.val.length = 1 → r.val = v) ∧
      (2 ≤ nums.val.length → r.val = ((nums.val.length / 2 : Nat) : Int) * v)) := by
  sorry

/-- Whenever the function returns a result r, r = max(nums[i] + nums[(i + 2) mod 5] | 0 <= i < 5).
  Preconditions: len(nums) = 5, and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000. -/
theorem spec_13 (nums : Slice Std.I64)
    (hlen : nums.val.length = 5)
    (hval : ∀ i : Nat, i < nums.val.length → 0 ≤ valAt nums i ∧ valAt nums i ≤ 1000)
    (r : Std.I64) (hr : rob nums = ok r) :
    r.val = fiveCyclePairMax nums := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : nums.val.length = 5)
    (hval : ∀ i : Nat, i < nums.val.length → 0 ≤ valAt nums i ∧ valAt nums i ≤ 1000)
    (r : Std.I64) (hr : rob nums = ok r), r.val = fiveCyclePairMax nums) := by
  sorry

end AegisSpec.Rob
