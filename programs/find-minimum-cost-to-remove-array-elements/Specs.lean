import Aegis.MinCost.Code.Funs

/-!
# Specifications of `Aegis.MinCost.min_cost`

LeetCode problem `find-minimum-cost-to-remove-array-elements`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MinCost (min_cost)

namespace AegisSpec.MinCost

def vals (s : Slice Std.I64) : List ℤ := s.val.map (fun x => x.val)

def entry (l : List ℤ) (i : ℕ) : ℤ := l.getD i 0

def listMax (l : List ℤ) : ℤ := l.maximum.unbotD 0

def listMin (l : List ℤ) : ℤ := l.minimum.untopD 0

def halfUp (n : ℕ) : ℤ := ((n + 1) / 2 : ℕ)

def min3 (a b c : ℤ) : ℤ := min a (min b c)

def max3 (a b c : ℤ) : ℤ := max a (max b c)

def C : List ℤ → ℤ
  | [] => 0
  | [x] => x
  | [x, y] => max x y
  | x :: y :: z :: rest =>
      min (min (max x y + C (z :: rest)) (max x z + C (y :: rest)))
          (max y z + C (x :: rest))
termination_by l => l.length
decreasing_by all_goals simp_wf

inductive Removable : List ℤ → ℤ → Prop where
  | nil : Removable [] 0
  | single (x : ℤ) : Removable [x] x
  | double (x y : ℤ) : Removable [x, y] (max x y)
  | stepFst {x y z c : ℤ} {rest : List ℤ} :
      Removable (z :: rest) c → Removable (x :: y :: z :: rest) (max x y + c)
  | stepSnd {x y z c : ℤ} {rest : List ℤ} :
      Removable (y :: rest) c → Removable (x :: y :: z :: rest) (max x z + c)
  | stepThd {x y z c : ℤ} {rest : List ℤ} :
      Removable (x :: rest) c → Removable (x :: y :: z :: rest) (max y z + c)

/-- Let C be the following function on finite integer lists L: C([])=0; C([x])=x; C([x,y])=max(x,y); and for every list L with len(L)>=3, C(L)=min over all pairs (i,j) with 0<=i<j<3 of ( max(L[i],L[j]) + C(L with positions i and j deleted, preserving the order of remaining elements) ). The function returns a result r and r = C(nums).
  Preconditions: 1 <= len(nums) <= 1000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
theorem spec_1 (nums : Slice Std.I64)
    (hlen_lower : 1 ≤ nums.length) (hlen_upper : nums.length ≤ 1000)
    (hbounds : ∀ i : ℕ, i < nums.length →
      1 ≤ entry (vals nums) i ∧ entry (vals nums) i ≤ 1000000) :
    ∃ r : Std.I64, min_cost nums = ok r ∧ r.val = C (vals nums) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lower : 1 ≤ nums.length) (hlen_upper : nums.length ≤ 1000)
    (hbounds : ∀ i : ℕ, i < nums.length →
      1 ≤ entry (vals nums) i ∧ entry (vals nums) i ≤ 1000000), ∃ r : Std.I64, min_cost nums = ok r ∧ r.val = C (vals nums)) := by
  sorry

/-- The function returns a result r for every nums satisfying the preconditions; it does not fail, panic, or overflow.
  Preconditions: 1 <= len(nums) <= 1000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
theorem spec_2 (nums : Slice Std.I64)
    (hlen_lower : 1 ≤ nums.length) (hlen_upper : nums.length ≤ 1000)
    (hbounds : ∀ i : ℕ, i < nums.length →
      1 ≤ entry (vals nums) i ∧ entry (vals nums) i ≤ 1000000) :
    ∃ r : Std.I64, min_cost nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lower : 1 ≤ nums.length) (hlen_upper : nums.length ≤ 1000)
    (hbounds : ∀ i : ℕ, i < nums.length →
      1 ≤ entry (vals nums) i ∧ entry (vals nums) i ≤ 1000000), ∃ r : Std.I64, min_cost nums = ok r) := by
  sorry

/-- Let M = max over 0 <= i < len(nums) of nums[i]. Whenever the function returns a result r, r >= M.
  Preconditions: 1 <= len(nums) <= 1000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
theorem spec_3 (nums : Slice Std.I64)
    (hlen_lower : 1 ≤ nums.length) (hlen_upper : nums.length ≤ 1000)
    (hbounds : ∀ i : ℕ, i < nums.length →
      1 ≤ entry (vals nums) i ∧ entry (vals nums) i ≤ 1000000) :
    ∀ r : Std.I64, min_cost nums = ok r → listMax (vals nums) ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lower : 1 ≤ nums.length) (hlen_upper : nums.length ≤ 1000)
    (hbounds : ∀ i : ℕ, i < nums.length →
      1 ≤ entry (vals nums) i ∧ entry (vals nums) i ≤ 1000000), ∀ r : Std.I64, min_cost nums = ok r → listMax (vals nums) ≤ r.val) := by
  sorry

/-- Let m = min over 0 <= i < len(nums) of nums[i] and let t = (len(nums)+1) div 2, so t = ceil(len(nums)/2). Whenever the function returns a result r, r >= m * t.
  Preconditions: 1 <= len(nums) <= 1000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
theorem spec_4 (nums : Slice Std.I64)
    (hlen_lower : 1 ≤ nums.length) (hlen_upper : nums.length ≤ 1000)
    (hbounds : ∀ i : ℕ, i < nums.length →
      1 ≤ entry (vals nums) i ∧ entry (vals nums) i ≤ 1000000) :
    ∀ r : Std.I64,
      min_cost nums = ok r → listMin (vals nums) * halfUp nums.length ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lower : 1 ≤ nums.length) (hlen_upper : nums.length ≤ 1000)
    (hbounds : ∀ i : ℕ, i < nums.length →
      1 ≤ entry (vals nums) i ∧ entry (vals nums) i ≤ 1000000), ∀ r : Std.I64,
      min_cost nums = ok r → listMin (vals nums) * halfUp nums.length ≤ r.val) := by
  sorry

/-- Let M = max over 0 <= i < len(nums) of nums[i] and let t = (len(nums)+1) div 2, so t = ceil(len(nums)/2). Whenever the function returns a result r, r <= M * t.
  Preconditions: 1 <= len(nums) <= 1000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
theorem spec_5 (nums : Slice Std.I64)
    (hlen_lower : 1 ≤ nums.length) (hlen_upper : nums.length ≤ 1000)
    (hbounds : ∀ i : ℕ, i < nums.length →
      1 ≤ entry (vals nums) i ∧ entry (vals nums) i ≤ 1000000) :
    ∀ r : Std.I64,
      min_cost nums = ok r → r.val ≤ listMax (vals nums) * halfUp nums.length := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lower : 1 ≤ nums.length) (hlen_upper : nums.length ≤ 1000)
    (hbounds : ∀ i : ℕ, i < nums.length →
      1 ≤ entry (vals nums) i ∧ entry (vals nums) i ≤ 1000000), ∀ r : Std.I64,
      min_cost nums = ok r → r.val ≤ listMax (vals nums) * halfUp nums.length) := by
  sorry

/-- Whenever the function returns a result r, r <= sum over 0 <= i < len(nums) of nums[i].
  Preconditions: 1 <= len(nums) <= 1000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
theorem spec_6 (nums : Slice Std.I64)
    (hlen_lower : 1 ≤ nums.length) (hlen_upper : nums.length ≤ 1000)
    (hbounds : ∀ i : ℕ, i < nums.length →
      1 ≤ entry (vals nums) i ∧ entry (vals nums) i ≤ 1000000) :
    ∀ r : Std.I64, min_cost nums = ok r → r.val ≤ (vals nums).sum := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lower : 1 ≤ nums.length) (hlen_upper : nums.length ≤ 1000)
    (hbounds : ∀ i : ℕ, i < nums.length →
      1 ≤ entry (vals nums) i ∧ entry (vals nums) i ≤ 1000000), ∀ r : Std.I64, min_cost nums = ok r → r.val ≤ (vals nums).sum) := by
  sorry

/-- Whenever the function returns a result r, r = nums[0].
  Preconditions: 1 <= len(nums) <= 1000, len(nums) = 1, and 1 <= nums[0] <= 1000000. -/
theorem spec_7 (nums : Slice Std.I64)
    (hlen_lower : 1 ≤ nums.length) (hlen_upper : nums.length ≤ 1000)
    (hlen : nums.length = 1)
    (hbound0 : 1 ≤ entry (vals nums) 0 ∧ entry (vals nums) 0 ≤ 1000000) :
    ∀ r : Std.I64, min_cost nums = ok r → r.val = entry (vals nums) 0 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lower : 1 ≤ nums.length) (hlen_upper : nums.length ≤ 1000)
    (hlen : nums.length = 1)
    (hbound0 : 1 ≤ entry (vals nums) 0 ∧ entry (vals nums) 0 ≤ 1000000), ∀ r : Std.I64, min_cost nums = ok r → r.val = entry (vals nums) 0) := by
  sorry

/-- Whenever the function returns a result r, r = max(nums[0], nums[1]).
  Preconditions: 1 <= len(nums) <= 1000, len(nums) = 2, and for every i with 0 <= i < 2, 1 <= nums[i] <= 1000000. -/
theorem spec_8 (nums : Slice Std.I64)
    (hlen_lower : 1 ≤ nums.length) (hlen_upper : nums.length ≤ 1000)
    (hlen : nums.length = 2)
    (hbounds : ∀ i : ℕ, i < 2 →
      1 ≤ entry (vals nums) i ∧ entry (vals nums) i ≤ 1000000) :
    ∀ r : Std.I64,
      min_cost nums = ok r → r.val = max (entry (vals nums) 0) (entry (vals nums) 1) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lower : 1 ≤ nums.length) (hlen_upper : nums.length ≤ 1000)
    (hlen : nums.length = 2)
    (hbounds : ∀ i : ℕ, i < 2 →
      1 ≤ entry (vals nums) i ∧ entry (vals nums) i ≤ 1000000), ∀ r : Std.I64,
      min_cost nums = ok r → r.val = max (entry (vals nums) 0) (entry (vals nums) 1)) := by
  sorry

/-- Let lo = min(nums[0], nums[1], nums[2]) and hi = max(nums[0], nums[1], nums[2]). Whenever the function returns a result r, r = lo + hi.
  Preconditions: 1 <= len(nums) <= 1000, len(nums) = 3, and for every i with 0 <= i < 3, 1 <= nums[i] <= 1000000. -/
theorem spec_9 (nums : Slice Std.I64)
    (hlen_lower : 1 ≤ nums.length) (hlen_upper : nums.length ≤ 1000)
    (hlen : nums.length = 3)
    (hbounds : ∀ i : ℕ, i < 3 →
      1 ≤ entry (vals nums) i ∧ entry (vals nums) i ≤ 1000000) :
    ∀ r : Std.I64, min_cost nums = ok r → r.val =
      min3 (entry (vals nums) 0) (entry (vals nums) 1) (entry (vals nums) 2) +
        max3 (entry (vals nums) 0) (entry (vals nums) 1) (entry (vals nums) 2) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lower : 1 ≤ nums.length) (hlen_upper : nums.length ≤ 1000)
    (hlen : nums.length = 3)
    (hbounds : ∀ i : ℕ, i < 3 →
      1 ≤ entry (vals nums) i ∧ entry (vals nums) i ≤ 1000000), ∀ r : Std.I64, min_cost nums = ok r → r.val =
      min3 (entry (vals nums) 0) (entry (vals nums) 1) (entry (vals nums) 2) +
        max3 (entry (vals nums) 0) (entry (vals nums) 1) (entry (vals nums) 2)) := by
  sorry

/-- Let a=nums[0], b=nums[1], c=nums[2], d=nums[3]. Whenever the function returns a result r, r = min( max(b,c)+max(a,d), max(a,c)+max(b,d), max(a,b)+max(c,d) ).
  Preconditions: 1 <= len(nums) <= 1000, len(nums) = 4, and for every i with 0 <= i < 4, 1 <= nums[i] <= 1000000. -/
theorem spec_10 (nums : Slice Std.I64)
    (hlen_lower : 1 ≤ nums.length) (hlen_upper : nums.length ≤ 1000)
    (hlen : nums.length = 4)
    (hbounds : ∀ i : ℕ, i < 4 →
      1 ≤ entry (vals nums) i ∧ entry (vals nums) i ≤ 1000000) :
    ∀ r : Std.I64, min_cost nums = ok r → r.val =
      let a := entry (vals nums) 0
      let b := entry (vals nums) 1
      let c := entry (vals nums) 2
      let d := entry (vals nums) 3
      min3 (max b c + max a d) (max a c + max b d) (max a b + max c d) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lower : 1 ≤ nums.length) (hlen_upper : nums.length ≤ 1000)
    (hlen : nums.length = 4)
    (hbounds : ∀ i : ℕ, i < 4 →
      1 ≤ entry (vals nums) i ∧ entry (vals nums) i ≤ 1000000), ∀ r : Std.I64, min_cost nums = ok r → r.val =
      let a := entry (vals nums) 0
      let b := entry (vals nums) 1
      let c := entry (vals nums) 2
      let d := entry (vals nums) 3
      min3 (max b c + max a d) (max a c + max b d) (max a b + max c d)) := by
  sorry

/-- Whenever the function returns a result r, r = c * ((len(nums)+1) div 2).
  Preconditions: 1 <= len(nums) <= 1000 and there is an integer c with 1 <= c <= 1000000 such that for every i with 0 <= i < len(nums), nums[i] = c. -/
theorem spec_11 (nums : Slice Std.I64) (c : ℤ)
    (hlen_lower : 1 ≤ nums.length) (hlen_upper : nums.length ≤ 1000)
    (hc_lower : 1 ≤ c) (hc_upper : c ≤ 1000000)
    (hconst : ∀ i : ℕ, i < nums.length → entry (vals nums) i = c) :
    ∀ r : Std.I64, min_cost nums = ok r → r.val = c * halfUp nums.length := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64) (c : ℤ)
    (hlen_lower : 1 ≤ nums.length) (hlen_upper : nums.length ≤ 1000)
    (hc_lower : 1 ≤ c) (hc_upper : c ≤ 1000000)
    (hconst : ∀ i : ℕ, i < nums.length → entry (vals nums) i = c), ∀ r : Std.I64, min_cost nums = ok r → r.val = c * halfUp nums.length) := by
  sorry

/-- Let nums+c denote the slice of the same length with (nums+c)[i] = nums[i]+c. Whenever the function returns r on nums and returns r_c on nums+c, r_c = r + c * ((len(nums)+1) div 2).
  Preconditions: 1 <= len(nums) <= 1000, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000, and c is an integer such that for every i with 0 <= i < len(nums), 1 <= nums[i]+c <= 1000000. -/
theorem spec_12 (nums nums' : Slice Std.I64) (c : ℤ)
    (hlen_lower : 1 ≤ nums.length) (hlen_upper : nums.length ≤ 1000)
    (hbounds : ∀ i : ℕ, i < nums.length →
      1 ≤ entry (vals nums) i ∧ entry (vals nums) i ≤ 1000000)
    (hshift_bounds : ∀ i : ℕ, i < nums.length →
      1 ≤ entry (vals nums) i + c ∧ entry (vals nums) i + c ≤ 1000000)
    (hlen_shift : nums'.length = nums.length)
    (hvals_shift : ∀ i : ℕ, i < nums.length → entry (vals nums') i = entry (vals nums) i + c) :
    ∀ r r' : Std.I64, min_cost nums = ok r → min_cost nums' = ok r' →
      r'.val = r.val + c * halfUp nums.length := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (c : ℤ)
    (hlen_lower : 1 ≤ nums.length) (hlen_upper : nums.length ≤ 1000)
    (hbounds : ∀ i : ℕ, i < nums.length →
      1 ≤ entry (vals nums) i ∧ entry (vals nums) i ≤ 1000000)
    (hshift_bounds : ∀ i : ℕ, i < nums.length →
      1 ≤ entry (vals nums) i + c ∧ entry (vals nums) i + c ≤ 1000000)
    (hlen_shift : nums'.length = nums.length)
    (hvals_shift : ∀ i : ℕ, i < nums.length → entry (vals nums') i = entry (vals nums) i + c), ∀ r r' : Std.I64, min_cost nums = ok r → min_cost nums' = ok r' →
      r'.val = r.val + c * halfUp nums.length) := by
  sorry

/-- Let k*nums denote the slice with (k*nums)[i] = k*nums[i]. Whenever the function returns r on nums and returns r_k on k*nums, r_k = k * r.
  Preconditions: 1 <= len(nums) <= 1000, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000, and k is a positive integer such that for every i with 0 <= i < len(nums), 1 <= k*nums[i] <= 1000000. -/
theorem spec_13 (nums nums' : Slice Std.I64) (k : ℤ)
    (hlen_lower : 1 ≤ nums.length) (hlen_upper : nums.length ≤ 1000)
    (hbounds : ∀ i : ℕ, i < nums.length →
      1 ≤ entry (vals nums) i ∧ entry (vals nums) i ≤ 1000000)
    (hk_pos : 1 ≤ k)
    (hscale_bounds : ∀ i : ℕ, i < nums.length →
      1 ≤ k * entry (vals nums) i ∧ k * entry (vals nums) i ≤ 1000000)
    (hlen_scale : nums'.length = nums.length)
    (hvals_scale : ∀ i : ℕ, i < nums.length → entry (vals nums') i = k * entry (vals nums) i) :
    ∀ r r' : Std.I64, min_cost nums = ok r → min_cost nums' = ok r' →
      r'.val = k * r.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (k : ℤ)
    (hlen_lower : 1 ≤ nums.length) (hlen_upper : nums.length ≤ 1000)
    (hbounds : ∀ i : ℕ, i < nums.length →
      1 ≤ entry (vals nums) i ∧ entry (vals nums) i ≤ 1000000)
    (hk_pos : 1 ≤ k)
    (hscale_bounds : ∀ i : ℕ, i < nums.length →
      1 ≤ k * entry (vals nums) i ∧ k * entry (vals nums) i ≤ 1000000)
    (hlen_scale : nums'.length = nums.length)
    (hvals_scale : ∀ i : ℕ, i < nums.length → entry (vals nums') i = k * entry (vals nums) i), ∀ r r' : Std.I64, min_cost nums = ok r → min_cost nums' = ok r' →
      r'.val = k * r.val) := by
  sorry

/-- Whenever the function returns r on nums and returns r_other on other, r <= r_other.
  Preconditions: 1 <= len(nums) <= 1000, 1 <= len(other) <= 1000, len(nums)=len(other), for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000 and 1 <= other[i] <= 1000000, and for every i with 0 <= i < len(nums), nums[i] <= other[i]. -/
theorem spec_14 (nums other : Slice Std.I64)
    (hlen_lower : 1 ≤ nums.length) (hlen_upper : nums.length ≤ 1000)
    (holen_lower : 1 ≤ other.length) (holen_upper : other.length ≤ 1000)
    (hlen_eq : nums.length = other.length)
    (hbounds : ∀ i : ℕ, i < nums.length →
      1 ≤ entry (vals nums) i ∧ entry (vals nums) i ≤ 1000000)
    (hobounds : ∀ i : ℕ, i < other.length →
      1 ≤ entry (vals other) i ∧ entry (vals other) i ≤ 1000000)
    (hle : ∀ i : ℕ, i < nums.length → entry (vals nums) i ≤ entry (vals other) i) :
    ∀ r r' : Std.I64, min_cost nums = ok r → min_cost other = ok r' → r.val ≤ r'.val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (nums other : Slice Std.I64)
    (hlen_lower : 1 ≤ nums.length) (hlen_upper : nums.length ≤ 1000)
    (holen_lower : 1 ≤ other.length) (holen_upper : other.length ≤ 1000)
    (hlen_eq : nums.length = other.length)
    (hbounds : ∀ i : ℕ, i < nums.length →
      1 ≤ entry (vals nums) i ∧ entry (vals nums) i ≤ 1000000)
    (hobounds : ∀ i : ℕ, i < other.length →
      1 ≤ entry (vals other) i ∧ entry (vals other) i ≤ 1000000)
    (hle : ∀ i : ℕ, i < nums.length → entry (vals nums) i ≤ entry (vals other) i), ∀ r r' : Std.I64, min_cost nums = ok r → min_cost other = ok r' → r.val ≤ r'.val) := by
  sorry

/-- Whenever the function returns a result r, there exists a finite complete removal process for nums, following exactly the allowed operations of the problem statement, whose total cost is r.
  Preconditions: 1 <= len(nums) <= 1000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
theorem spec_15 (nums : Slice Std.I64)
    (hlen_lower : 1 ≤ nums.length) (hlen_upper : nums.length ≤ 1000)
    (hbounds : ∀ i : ℕ, i < nums.length →
      1 ≤ entry (vals nums) i ∧ entry (vals nums) i ≤ 1000000) :
    ∀ r : Std.I64, min_cost nums = ok r → Removable (vals nums) r.val := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lower : 1 ≤ nums.length) (hlen_upper : nums.length ≤ 1000)
    (hbounds : ∀ i : ℕ, i < nums.length →
      1 ≤ entry (vals nums) i ∧ entry (vals nums) i ≤ 1000000), ∀ r : Std.I64, min_cost nums = ok r → Removable (vals nums) r.val) := by
  sorry

end AegisSpec.MinCost
