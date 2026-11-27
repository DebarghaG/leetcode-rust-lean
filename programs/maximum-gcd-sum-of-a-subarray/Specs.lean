import Aegis.MaxGcdSum.Code.Funs

/-!
# Specifications of `Aegis.MaxGcdSum.max_gcd_sum`

LeetCode problem `maximum-gcd-sum-of-a-subarray`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MaxGcdSum (max_gcd_sum)

namespace AegisSpec.MaxGcdSum

def vals (nums : Slice I64) : List Int := nums.val.map (fun x => x.val)

def valAt (nums : Slice I64) (i : Nat) (h : i < nums.val.length) : Int :=
  (nums.val.get ⟨i, h⟩).val

def listGcd (l : List Int) : Nat := l.foldr (fun x acc => Nat.gcd x.natAbs acc) 0

def segVals (nums : Slice I64) (l u : Nat) : List Int :=
  ((nums.val.drop l).take (u - l + 1)).map (fun x => x.val)

def segSum (nums : Slice I64) (l u : Nat) : Int := (segVals nums l u).sum

def segGcd (nums : Slice I64) (l u : Nat) : Int := ((listGcd (segVals nums l u) : Nat) : Int)

def segCost (nums : Slice I64) (l u : Nat) : Int := segSum nums l u * segGcd nums l u

def IsWindow (nums : Slice I64) (k : Int) (l u : Nat) : Prop :=
  l ≤ u ∧ u < nums.val.length ∧ k ≤ (u : Int) - (l : Int) + 1

def totalSum (nums : Slice I64) : Int := (vals nums).sum

def maxVal (nums : Slice I64) : Int := (vals nums).foldr max 0

def revSlice (nums : Slice I64) : Slice I64 :=
  Slice.from nums.val.reverse (by simp)

@[simp]
theorem revSlice_val (nums : Slice I64) : (revSlice nums).val = nums.val.reverse :=
  Slice.from_val _ _

def scaleSlice (c : Int) (nums : Slice I64)
    (hc : ∀ (i : Nat) (h : i < nums.val.length),
      1 ≤ c * valAt nums i h ∧ c * valAt nums i h ≤ 1000000) : Slice I64 :=
  Slice.from
    (List.ofFn (fun (i : Fin nums.val.length) =>
      IScalar.ofInt (c * valAt nums i.val i.isLt) (by
        have hi := hc i.val i.isLt
        have hmin : IScalar.cMin IScalarTy.I64 ≤ (1 : Int) := by decide
        have hmax : (1000000 : Int) ≤ IScalar.cMax IScalarTy.I64 := by decide
        omega)))
    (by simp)

/-- The function returns a result r, and the integer value of r is the maximum of C(l,u) over all pairs (l,u) with 0 <= l <= u < n and u-l+1 >= k. Here, for such a pair, S(l,u) = sum_{i=l}^{u} nums[i], G(l,u) is the greatest positive integer dividing every nums[i] with l <= i <= u, and C(l,u) = S(l,u) * G(l,u). Equivalently, C(l,u) <= r for every allowed pair, and C(l,u) = r for at least one allowed pair.
  Preconditions: Let n = len(nums). We have n >= 1; for every i with 0 <= i < n, 1 <= nums[i] <= 1000000; and 1 <= k <= n (k is interpreted as a mathematical integer). -/
theorem spec_1 (nums : Slice I64) (k : I64)
    (hn : 1 ≤ nums.val.length)
    (hpos : ∀ (i : Nat) (h : i < nums.val.length),
      1 ≤ valAt nums i h ∧ valAt nums i h ≤ 1000000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : Int)) :
    ∃ r : I64, max_gcd_sum nums k = ok r ∧
      (∀ (l u : Nat), IsWindow nums k.val l u → segCost nums l u ≤ r.val) ∧
      (∃ (l u : Nat), IsWindow nums k.val l u ∧ segCost nums l u = r.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice I64) (k : I64)
    (hn : 1 ≤ nums.val.length)
    (hpos : ∀ (i : Nat) (h : i < nums.val.length),
      1 ≤ valAt nums i h ∧ valAt nums i h ≤ 1000000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : Int)), ∃ r : I64, max_gcd_sum nums k = ok r ∧
      (∀ (l u : Nat), IsWindow nums k.val l u → segCost nums l u ≤ r.val) ∧
      (∃ (l u : Nat), IsWindow nums k.val l u ∧ segCost nums l u = r.val)) := by
  sorry

/-- The function returns a result r (it does not fail).
  Preconditions: Let n = len(nums). We have n >= 1; for every i with 0 <= i < n, 1 <= nums[i] <= 1000000; and 1 <= k <= n (k is interpreted as a mathematical integer). -/
theorem spec_2 (nums : Slice I64) (k : I64)
    (hn : 1 ≤ nums.val.length)
    (hpos : ∀ (i : Nat) (h : i < nums.val.length),
      1 ≤ valAt nums i h ∧ valAt nums i h ≤ 1000000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : Int)) :
    ∃ r : I64, max_gcd_sum nums k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice I64) (k : I64)
    (hn : 1 ≤ nums.val.length)
    (hpos : ∀ (i : Nat) (h : i < nums.val.length),
      1 ≤ valAt nums i h ∧ valAt nums i h ≤ 1000000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : Int)), ∃ r : I64, max_gcd_sum nums k = ok r) := by
  sorry

/-- Whenever the function returns a result r, there exist indices l and u with 0 <= l <= u < n and u-l+1 >= k such that the integer value of r equals S(l,u) * G(l,u), where S(l,u) = sum_{i=l}^{u} nums[i] and G(l,u) is the greatest positive integer dividing every nums[i] with l <= i <= u.
  Preconditions: Let n = len(nums). We have n >= 1; for every i with 0 <= i < n, 1 <= nums[i] <= 1000000; and 1 <= k <= n (k is interpreted as a mathematical integer). -/
theorem spec_3 (nums : Slice I64) (k : I64) (r : I64)
    (hn : 1 ≤ nums.val.length)
    (hpos : ∀ (i : Nat) (h : i < nums.val.length),
      1 ≤ valAt nums i h ∧ valAt nums i h ≤ 1000000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : Int))
    (hr : max_gcd_sum nums k = ok r) :
    ∃ (l u : Nat), IsWindow nums k.val l u ∧ r.val = segCost nums l u := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (r : I64)
    (hn : 1 ≤ nums.val.length)
    (hpos : ∀ (i : Nat) (h : i < nums.val.length),
      1 ≤ valAt nums i h ∧ valAt nums i h ≤ 1000000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : Int))
    (hr : max_gcd_sum nums k = ok r), ∃ (l u : Nat), IsWindow nums k.val l u ∧ r.val = segCost nums l u) := by
  sorry

/-- Whenever the function returns a result r, for every pair (l,u) with 0 <= l <= u < n and u-l+1 >= k, we have S(l,u) * G(l,u) <= r, where S(l,u) = sum_{i=l}^{u} nums[i] and G(l,u) is the greatest positive integer dividing every nums[i] with l <= i <= u.
  Preconditions: Let n = len(nums). We have n >= 1; for every i with 0 <= i < n, 1 <= nums[i] <= 1000000; and 1 <= k <= n (k is interpreted as a mathematical integer). -/
theorem spec_4 (nums : Slice I64) (k : I64) (r : I64)
    (hn : 1 ≤ nums.val.length)
    (hpos : ∀ (i : Nat) (h : i < nums.val.length),
      1 ≤ valAt nums i h ∧ valAt nums i h ≤ 1000000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : Int))
    (hr : max_gcd_sum nums k = ok r) :
    ∀ (l u : Nat), IsWindow nums k.val l u → segCost nums l u ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (r : I64)
    (hn : 1 ≤ nums.val.length)
    (hpos : ∀ (i : Nat) (h : i < nums.val.length),
      1 ≤ valAt nums i h ∧ valAt nums i h ≤ 1000000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : Int))
    (hr : max_gcd_sum nums k = ok r), ∀ (l u : Nat), IsWindow nums k.val l u → segCost nums l u ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, the integer value of r is at most (sum_{i=0}^{n-1} nums[i]) * (max_{0 <= i < n} nums[i]).
  Preconditions: Let n = len(nums). We have n >= 1; for every i with 0 <= i < n, 1 <= nums[i] <= 1000000; and 1 <= k <= n (k is interpreted as a mathematical integer). -/
theorem spec_5 (nums : Slice I64) (k : I64) (r : I64)
    (hn : 1 ≤ nums.val.length)
    (hpos : ∀ (i : Nat) (h : i < nums.val.length),
      1 ≤ valAt nums i h ∧ valAt nums i h ≤ 1000000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : Int))
    (hr : max_gcd_sum nums k = ok r) :
    r.val ≤ totalSum nums * maxVal nums := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (r : I64)
    (hn : 1 ≤ nums.val.length)
    (hpos : ∀ (i : Nat) (h : i < nums.val.length),
      1 ≤ valAt nums i h ∧ valAt nums i h ≤ 1000000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : Int))
    (hr : max_gcd_sum nums k = ok r), r.val ≤ totalSum nums * maxVal nums) := by
  sorry

/-- Whenever the function returns a result r, the integer value of r equals (sum_{i=0}^{n-1} nums[i]) * G(0,n-1), where G(0,n-1) is the greatest positive integer dividing every nums[i] for 0 <= i < n.
  Preconditions: Let n = len(nums). We have n >= 1; for every i with 0 <= i < n, 1 <= nums[i] <= 1000000; 1 <= k <= n (k is interpreted as a mathematical integer); and k = n. -/
theorem spec_6 (nums : Slice I64) (k : I64) (r : I64)
    (hn : 1 ≤ nums.val.length)
    (hpos : ∀ (i : Nat) (h : i < nums.val.length),
      1 ≤ valAt nums i h ∧ valAt nums i h ≤ 1000000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : Int))
    (hkn : k.val = (nums.val.length : Int))
    (hr : max_gcd_sum nums k = ok r) :
    r.val = totalSum nums * segGcd nums 0 (nums.val.length - 1) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (r : I64)
    (hn : 1 ≤ nums.val.length)
    (hpos : ∀ (i : Nat) (h : i < nums.val.length),
      1 ≤ valAt nums i h ∧ valAt nums i h ≤ 1000000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : Int))
    (hkn : k.val = (nums.val.length : Int))
    (hr : max_gcd_sum nums k = ok r), r.val = totalSum nums * segGcd nums 0 (nums.val.length - 1)) := by
  sorry

/-- Whenever max_gcd_sum(nums, k) returns a result r and max_gcd_sum(rev(nums), k) returns a result r', the integer values of r and r' are equal.
  Preconditions: Let n = len(nums). We have n >= 1; for every i with 0 <= i < n, 1 <= nums[i] <= 1000000; and 1 <= k <= n (k is interpreted as a mathematical integer). Let rev(nums) be the slice of length n with rev(nums)[i] = nums[n-1-i] for 0 <= i < n. -/
theorem spec_7 (nums : Slice I64) (k : I64) (r r' : I64)
    (hn : 1 ≤ nums.val.length)
    (hpos : ∀ (i : Nat) (h : i < nums.val.length),
      1 ≤ valAt nums i h ∧ valAt nums i h ≤ 1000000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : Int))
    (hr : max_gcd_sum nums k = ok r)
    (hr' : max_gcd_sum (revSlice nums) k = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (r r' : I64)
    (hn : 1 ≤ nums.val.length)
    (hpos : ∀ (i : Nat) (h : i < nums.val.length),
      1 ≤ valAt nums i h ∧ valAt nums i h ≤ 1000000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : Int))
    (hr : max_gcd_sum nums k = ok r)
    (hr' : max_gcd_sum (revSlice nums) k = ok r'), r.val = r'.val) := by
  sorry

/-- Whenever max_gcd_sum(nums, k1) returns a result r1 and max_gcd_sum(nums, k2) returns a result r2, we have r2 <= r1 (as integer values).
  Preconditions: Let n = len(nums). We have n >= 1; for every i with 0 <= i < n, 1 <= nums[i] <= 1000000; and let k1 and k2 be integers with 1 <= k1 <= k2 <= n. -/
theorem spec_8 (nums : Slice I64) (k1 k2 : I64) (r1 r2 : I64)
    (hn : 1 ≤ nums.val.length)
    (hpos : ∀ (i : Nat) (h : i < nums.val.length),
      1 ≤ valAt nums i h ∧ valAt nums i h ≤ 1000000)
    (hk1 : 1 ≤ k1.val) (hk12 : k1.val ≤ k2.val)
    (hk2 : k2.val ≤ (nums.val.length : Int))
    (hr1 : max_gcd_sum nums k1 = ok r1)
    (hr2 : max_gcd_sum nums k2 = ok r2) :
    r2.val ≤ r1.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice I64) (k1 k2 : I64) (r1 r2 : I64)
    (hn : 1 ≤ nums.val.length)
    (hpos : ∀ (i : Nat) (h : i < nums.val.length),
      1 ≤ valAt nums i h ∧ valAt nums i h ≤ 1000000)
    (hk1 : 1 ≤ k1.val) (hk12 : k1.val ≤ k2.val)
    (hk2 : k2.val ≤ (nums.val.length : Int))
    (hr1 : max_gcd_sum nums k1 = ok r1)
    (hr2 : max_gcd_sum nums k2 = ok r2), r2.val ≤ r1.val) := by
  sorry

/-- Whenever max_gcd_sum(nums, k) returns a result r and max_gcd_sum(c*nums, k) returns a result r', the integer value of r' equals c*c times the integer value of r.
  Preconditions: Let n = len(nums). We have n >= 1; for every i with 0 <= i < n, 1 <= nums[i] <= 1000000; and 1 <= k <= n (k is interpreted as a mathematical integer). Let c be a positive integer such that 1 <= c*nums[i] <= 1000000 for every i with 0 <= i < n; let c*nums be the slice of length n with (c*nums)[i] = c*nums[i]. -/
theorem spec_9 (nums : Slice I64) (k : I64) (r r' : I64) (c : Int)
    (hn : 1 ≤ nums.val.length)
    (hpos : ∀ (i : Nat) (h : i < nums.val.length),
      1 ≤ valAt nums i h ∧ valAt nums i h ≤ 1000000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : Int))
    (hc1 : 1 ≤ c)
    (hc2 : ∀ (i : Nat) (h : i < nums.val.length),
      1 ≤ c * valAt nums i h ∧ c * valAt nums i h ≤ 1000000)
    (hr : max_gcd_sum nums k = ok r)
    (hr' : max_gcd_sum (scaleSlice c nums hc2) k = ok r') :
    r'.val = c * c * r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (r r' : I64) (c : Int)
    (hn : 1 ≤ nums.val.length)
    (hpos : ∀ (i : Nat) (h : i < nums.val.length),
      1 ≤ valAt nums i h ∧ valAt nums i h ≤ 1000000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : Int))
    (hc1 : 1 ≤ c)
    (hc2 : ∀ (i : Nat) (h : i < nums.val.length),
      1 ≤ c * valAt nums i h ∧ c * valAt nums i h ≤ 1000000)
    (hr : max_gcd_sum nums k = ok r)
    (hr' : max_gcd_sum (scaleSlice c nums hc2) k = ok r'), r'.val = c * c * r.val) := by
  sorry

/-- Whenever the function returns a result r, the integer value of r equals n * v * v.
  Preconditions: Let n = len(nums). We have n >= 1; for every i with 0 <= i < n, 1 <= nums[i] <= 1000000; and 1 <= k <= n (k is interpreted as a mathematical integer). There is an integer v with 1 <= v <= 1000000 such that nums[i] = v for every i with 0 <= i < n. -/
theorem spec_10 (nums : Slice I64) (k : I64) (r : I64) (v : Int)
    (hn : 1 ≤ nums.val.length)
    (hpos : ∀ (i : Nat) (h : i < nums.val.length),
      1 ≤ valAt nums i h ∧ valAt nums i h ≤ 1000000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : Int))
    (hv1 : 1 ≤ v) (hv2 : v ≤ 1000000)
    (hconst : ∀ (i : Nat) (h : i < nums.val.length), valAt nums i h = v)
    (hr : max_gcd_sum nums k = ok r) :
    r.val = (nums.val.length : Int) * v * v := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (r : I64) (v : Int)
    (hn : 1 ≤ nums.val.length)
    (hpos : ∀ (i : Nat) (h : i < nums.val.length),
      1 ≤ valAt nums i h ∧ valAt nums i h ≤ 1000000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : Int))
    (hv1 : 1 ≤ v) (hv2 : v ≤ 1000000)
    (hconst : ∀ (i : Nat) (h : i < nums.val.length), valAt nums i h = v)
    (hr : max_gcd_sum nums k = ok r), r.val = (nums.val.length : Int) * v * v) := by
  sorry

/-- Whenever the function returns a result r, the integer value of r is at least (sum_{i=0}^{n-1} nums[i]) * G(0,n-1), where G(0,n-1) is the greatest positive integer dividing every nums[i] for 0 <= i < n.
  Preconditions: Let n = len(nums). We have n >= 1; for every i with 0 <= i < n, 1 <= nums[i] <= 1000000; and 1 <= k <= n (k is interpreted as a mathematical integer). -/
theorem spec_11 (nums : Slice I64) (k : I64) (r : I64)
    (hn : 1 ≤ nums.val.length)
    (hpos : ∀ (i : Nat) (h : i < nums.val.length),
      1 ≤ valAt nums i h ∧ valAt nums i h ≤ 1000000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : Int))
    (hr : max_gcd_sum nums k = ok r) :
    totalSum nums * segGcd nums 0 (nums.val.length - 1) ≤ r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (r : I64)
    (hn : 1 ≤ nums.val.length)
    (hpos : ∀ (i : Nat) (h : i < nums.val.length),
      1 ≤ valAt nums i h ∧ valAt nums i h ≤ 1000000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : Int))
    (hr : max_gcd_sum nums k = ok r), totalSum nums * segGcd nums 0 (nums.val.length - 1) ≤ r.val) := by
  sorry

end AegisSpec.MaxGcdSum
