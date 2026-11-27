import Aegis.GetSum.Code.Funs

/-!
# Specifications of `Aegis.GetSum.get_sum`

LeetCode problem `sum-of-consecutive-subarrays`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.GetSum

def vals (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

def nth (x : List Int) (k : Nat) : Int := x.getD k 0

def M : Int := 1000000007

def modM (n : Int) : Int := Int.emod n M

def modEq (a b : Int) : Prop := Int.emod a M = Int.emod b M

@[reducible] def RunUp (x : List Int) (l r : Nat) : Prop :=
  ∀ k ∈ Finset.Ico l r, x[k + 1]? = (x[k]?).map (fun v => v + 1)

@[reducible] def RunDown (x : List Int) (l r : Nat) : Prop :=
  ∀ k ∈ Finset.Ico l r, x[k + 1]? = (x[k]?).map (fun v => v - 1)

@[reducible] def Consecutive (x : List Int) (l r : Nat) : Prop :=
  l ≤ r ∧ r < x.length ∧ (RunUp x l r ∨ RunDown x l r)

def segSum (x : List Int) (l r : Nat) : Int :=
  ∑ k ∈ Finset.Ico l (r + 1), nth x k

def Tsum (x : List Int) : Int :=
  ∑ l ∈ Finset.range x.length, ∑ r ∈ Finset.range x.length,
    if Consecutive x l r then segSum x l r else 0

def Lsum (x : List Int) : Int :=
  ∑ l ∈ Finset.range x.length, ∑ r ∈ Finset.range x.length,
    if Consecutive x l r then (((r + 1) - l : Nat) : Int) else 0

/-- For any slice x, call a subarray x[l..r] (0 <= l <= r < len(x)) consecutive if either (a) for every k with l <= k < r, x[k+1] = x[k] + 1, or (b) for every k with l <= k < r, x[k+1] = x[k] - 1; when l = r both conditions are vacuous, so length-1 subarrays are consecutive. Let T(x) be the sum, over all consecutive subarrays x[l..r] of x, of sum_{k=l}^{r} x[k]. Whenever get_sum nums returns a result r, r = T(nums) mod M, where mod M denotes the unique integer in [0, M-1] congruent to T(nums) modulo M.
  Preconditions: Let M = 1000000007. 1 <= len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000. -/
theorem spec_1 (nums : Slice Std.I64)
    (hlen : 1 ≤ (vals nums).length) (hlen' : (vals nums).length ≤ 100000)
    (hval : ∀ v ∈ vals nums, 1 ≤ v ∧ v ≤ 100000) :
    ∀ r : Std.I64, Aegis.GetSum.get_sum nums = ok r →
      r.val = modM (Tsum (vals nums)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : 1 ≤ (vals nums).length) (hlen' : (vals nums).length ≤ 100000)
    (hval : ∀ v ∈ vals nums, 1 ≤ v ∧ v ≤ 100000), ∀ r : Std.I64, Aegis.GetSum.get_sum nums = ok r →
      r.val = modM (Tsum (vals nums))) := by
  sorry

/-- get_sum nums does not fail: it returns Result.ok r for some i64 r.
  Preconditions: 1 <= len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000. -/
theorem spec_2 (nums : Slice Std.I64)
    (hlen : 1 ≤ (vals nums).length) (hlen' : (vals nums).length ≤ 100000)
    (hval : ∀ v ∈ vals nums, 1 ≤ v ∧ v ≤ 100000) :
    ∃ r : Std.I64, Aegis.GetSum.get_sum nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : 1 ≤ (vals nums).length) (hlen' : (vals nums).length ≤ 100000)
    (hval : ∀ v ∈ vals nums, 1 ≤ v ∧ v ≤ 100000), ∃ r : Std.I64, Aegis.GetSum.get_sum nums = ok r) := by
  sorry

/-- Whenever get_sum nums returns a result r, 0 <= r < 1000000007.
  Preconditions: 1 <= len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000. -/
theorem spec_3 (nums : Slice Std.I64)
    (hlen : 1 ≤ (vals nums).length) (hlen' : (vals nums).length ≤ 100000)
    (hval : ∀ v ∈ vals nums, 1 ≤ v ∧ v ≤ 100000) :
    ∀ r : Std.I64, Aegis.GetSum.get_sum nums = ok r →
      0 ≤ r.val ∧ r.val < 1000000007 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : 1 ≤ (vals nums).length) (hlen' : (vals nums).length ≤ 100000)
    (hval : ∀ v ∈ vals nums, 1 ≤ v ∧ v ≤ 100000), ∀ r : Std.I64, Aegis.GetSum.get_sum nums = ok r →
      0 ≤ r.val ∧ r.val < 1000000007) := by
  sorry

/-- Whenever get_sum nums returns a result r, r = nums[0].
  Preconditions: len(nums) = 1 and 1 <= nums[0] <= 100000. -/
theorem spec_4 (nums : Slice Std.I64)
    (hlen : (vals nums).length = 1)
    (hval : ∀ v ∈ vals nums, 1 ≤ v ∧ v ≤ 100000) :
    ∀ r : Std.I64, Aegis.GetSum.get_sum nums = ok r →
      r.val = nth (vals nums) 0 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : (vals nums).length = 1)
    (hval : ∀ v ∈ vals nums, 1 ≤ v ∧ v ≤ 100000), ∀ r : Std.I64, Aegis.GetSum.get_sum nums = ok r →
      r.val = nth (vals nums) 0) := by
  sorry

/-- Whenever get_sum nums returns a result r, r = nums[0] + nums[1] if |nums[1] - nums[0]| != 1, and r = 2 * (nums[0] + nums[1]) if |nums[1] - nums[0]| = 1.
  Preconditions: len(nums) = 2 and 1 <= nums[0] <= 100000 and 1 <= nums[1] <= 100000. -/
theorem spec_5 (nums : Slice Std.I64)
    (hlen : (vals nums).length = 2)
    (hval : ∀ v ∈ vals nums, 1 ≤ v ∧ v ≤ 100000) :
    ∀ r : Std.I64, Aegis.GetSum.get_sum nums = ok r →
      r.val = if |nth (vals nums) 1 - nth (vals nums) 0| = 1
        then 2 * (nth (vals nums) 0 + nth (vals nums) 1)
        else nth (vals nums) 0 + nth (vals nums) 1 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : (vals nums).length = 2)
    (hval : ∀ v ∈ vals nums, 1 ≤ v ∧ v ≤ 100000), ∀ r : Std.I64, Aegis.GetSum.get_sum nums = ok r →
      r.val = if |nth (vals nums) 1 - nth (vals nums) 0| = 1
        then 2 * (nth (vals nums) 0 + nth (vals nums) 1)
        else nth (vals nums) 0 + nth (vals nums) 1) := by
  sorry

/-- Whenever get_sum nums returns a result r, r = (sum_{k=0}^{len(nums)-1} nums[k] * (k+1) * (len(nums)-k)) mod 1000000007.
  Preconditions: 1 <= len(nums) <= 100000, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000, and either (for every i with 0 <= i < len(nums)-1, nums[i+1] = nums[i] + 1) or (for every i with 0 <= i < len(nums)-1, nums[i+1] = nums[i] - 1). -/
theorem spec_6 (nums : Slice Std.I64)
    (hlen : 1 ≤ (vals nums).length) (hlen' : (vals nums).length ≤ 100000)
    (hval : ∀ v ∈ vals nums, 1 ≤ v ∧ v ≤ 100000)
    (hrun : (∀ k, k + 1 < (vals nums).length →
        nth (vals nums) (k + 1) = nth (vals nums) k + 1) ∨
      (∀ k, k + 1 < (vals nums).length →
        nth (vals nums) (k + 1) = nth (vals nums) k - 1)) :
    ∀ r : Std.I64, Aegis.GetSum.get_sum nums = ok r →
      r.val = modM (∑ k ∈ Finset.range (vals nums).length,
        nth (vals nums) k * ((k : Int) + 1) * (((vals nums).length : Int) - (k : Int))) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : 1 ≤ (vals nums).length) (hlen' : (vals nums).length ≤ 100000)
    (hval : ∀ v ∈ vals nums, 1 ≤ v ∧ v ≤ 100000)
    (hrun : (∀ k, k + 1 < (vals nums).length →
        nth (vals nums) (k + 1) = nth (vals nums) k + 1) ∨
      (∀ k, k + 1 < (vals nums).length →
        nth (vals nums) (k + 1) = nth (vals nums) k - 1)), ∀ r : Std.I64, Aegis.GetSum.get_sum nums = ok r →
      r.val = modM (∑ k ∈ Finset.range (vals nums).length,
        nth (vals nums) k * ((k : Int) + 1) * (((vals nums).length : Int) - (k : Int)))) := by
  sorry

/-- Whenever get_sum nums returns a result r, r = (sum_{k=0}^{len(nums)-1} nums[k]) mod 1000000007.
  Preconditions: 1 <= len(nums) <= 100000, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000, and for every i with 0 <= i < len(nums)-1, nums[i+1] - nums[i] is neither 1 nor -1. -/
theorem spec_7 (nums : Slice Std.I64)
    (hlen : 1 ≤ (vals nums).length) (hlen' : (vals nums).length ≤ 100000)
    (hval : ∀ v ∈ vals nums, 1 ≤ v ∧ v ≤ 100000)
    (hsep : ∀ k, k + 1 < (vals nums).length →
      nth (vals nums) (k + 1) - nth (vals nums) k ≠ 1 ∧
      nth (vals nums) (k + 1) - nth (vals nums) k ≠ -1) :
    ∀ r : Std.I64, Aegis.GetSum.get_sum nums = ok r →
      r.val = modM (∑ k ∈ Finset.range (vals nums).length, nth (vals nums) k) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : 1 ≤ (vals nums).length) (hlen' : (vals nums).length ≤ 100000)
    (hval : ∀ v ∈ vals nums, 1 ≤ v ∧ v ≤ 100000)
    (hsep : ∀ k, k + 1 < (vals nums).length →
      nth (vals nums) (k + 1) - nth (vals nums) k ≠ 1 ∧
      nth (vals nums) (k + 1) - nth (vals nums) k ≠ -1), ∀ r : Std.I64, Aegis.GetSum.get_sum nums = ok r →
      r.val = modM (∑ k ∈ Finset.range (vals nums).length, nth (vals nums) k)) := by
  sorry

/-- Whenever get_sum nums returns a result r, r is congruent modulo 1000000007 to T(nums[0..p]) + T(nums[p+1..len(nums)-1]), where for any slice x, T(x) is the sum over all consecutive subarrays x[l..r] of x of sum_{k=l}^{r} x[k].
  Preconditions: len(nums) >= 2, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000, and p is an integer with 0 <= p < len(nums)-1 and |nums[p+1] - nums[p]| != 1. -/
theorem spec_8 (nums : Slice Std.I64)
    (hlen : 2 ≤ (vals nums).length)
    (hval : ∀ v ∈ vals nums, 1 ≤ v ∧ v ≤ 100000)
    (p : Nat) (hp : p + 1 < (vals nums).length)
    (hpbreak : |nth (vals nums) (p + 1) - nth (vals nums) p| ≠ 1) :
    ∀ r : Std.I64, Aegis.GetSum.get_sum nums = ok r →
      modEq r.val (Tsum ((vals nums).take (p + 1)) + Tsum ((vals nums).drop (p + 1))) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : 2 ≤ (vals nums).length)
    (hval : ∀ v ∈ vals nums, 1 ≤ v ∧ v ≤ 100000)
    (p : Nat) (hp : p + 1 < (vals nums).length)
    (hpbreak : |nth (vals nums) (p + 1) - nth (vals nums) p| ≠ 1), ∀ r : Std.I64, Aegis.GetSum.get_sum nums = ok r →
      modEq r.val (Tsum ((vals nums).take (p + 1)) + Tsum ((vals nums).drop (p + 1)))) := by
  sorry

/-- Whenever get_sum nums returns a result r and get_sum rev returns a result r', r = r'.
  Preconditions: nums satisfies the constraints of spec_1, and rev is a slice with len(rev) = len(nums) and rev[i] = nums[len(nums)-1-i] for every i with 0 <= i < len(nums). -/
theorem spec_9 (nums rev : Slice Std.I64)
    (hlen : 1 ≤ (vals nums).length) (hlen' : (vals nums).length ≤ 100000)
    (hval : ∀ v ∈ vals nums, 1 ≤ v ∧ v ≤ 100000)
    (hlenrev : (vals rev).length = (vals nums).length)
    (hrev : ∀ k, k < (vals nums).length →
      nth (vals rev) k = nth (vals nums) ((vals nums).length - 1 - k)) :
    ∀ r r' : Std.I64, Aegis.GetSum.get_sum nums = ok r →
      Aegis.GetSum.get_sum rev = ok r' → r.val = r'.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums rev : Slice Std.I64)
    (hlen : 1 ≤ (vals nums).length) (hlen' : (vals nums).length ≤ 100000)
    (hval : ∀ v ∈ vals nums, 1 ≤ v ∧ v ≤ 100000)
    (hlenrev : (vals rev).length = (vals nums).length)
    (hrev : ∀ k, k < (vals nums).length →
      nth (vals rev) k = nth (vals nums) ((vals nums).length - 1 - k)), ∀ r r' : Std.I64, Aegis.GetSum.get_sum nums = ok r →
      Aegis.GetSum.get_sum rev = ok r' → r.val = r'.val) := by
  sorry

/-- Let L(a) be the sum of (r-l+1) over all pairs (l,r) with 0 <= l <= r < len(a) such that a[l..r] is consecutive, i.e. all adjacent differences in a[l..r] are +1 or all are -1. Whenever get_sum a returns r_a and get_sum b returns r_b, r_b ≡ r_a + c * L(a) (mod 1000000007).
  Preconditions: a and b both satisfy 1 <= len <= 100000 and element values in [1, 100000], len(a) = len(b), and there exists an integer c such that b[i] = a[i] + c for every i with 0 <= i < len(a). -/
theorem spec_10 (a b : Slice Std.I64)
    (hlena : 1 ≤ (vals a).length) (hlena' : (vals a).length ≤ 100000)
    (hvala : ∀ v ∈ vals a, 1 ≤ v ∧ v ≤ 100000)
    (hlenb : 1 ≤ (vals b).length) (hlenb' : (vals b).length ≤ 100000)
    (hvalb : ∀ v ∈ vals b, 1 ≤ v ∧ v ≤ 100000)
    (hlen : (vals a).length = (vals b).length)
    (c : Int) (hc : ∀ k, k < (vals a).length → nth (vals b) k = nth (vals a) k + c) :
    ∀ ra rb : Std.I64, Aegis.GetSum.get_sum a = ok ra →
      Aegis.GetSum.get_sum b = ok rb →
      modEq rb.val (ra.val + c * Lsum (vals a)) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (a b : Slice Std.I64)
    (hlena : 1 ≤ (vals a).length) (hlena' : (vals a).length ≤ 100000)
    (hvala : ∀ v ∈ vals a, 1 ≤ v ∧ v ≤ 100000)
    (hlenb : 1 ≤ (vals b).length) (hlenb' : (vals b).length ≤ 100000)
    (hvalb : ∀ v ∈ vals b, 1 ≤ v ∧ v ≤ 100000)
    (hlen : (vals a).length = (vals b).length)
    (c : Int) (hc : ∀ k, k < (vals a).length → nth (vals b) k = nth (vals a) k + c), ∀ ra rb : Std.I64, Aegis.GetSum.get_sum a = ok ra →
      Aegis.GetSum.get_sum b = ok rb →
      modEq rb.val (ra.val + c * Lsum (vals a))) := by
  sorry

end AegisSpec.GetSum
