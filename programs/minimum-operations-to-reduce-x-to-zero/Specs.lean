import Aegis.MinOperations.Code.Funs

/-!
# Specifications of `Aegis.MinOperations.min_operations`

LeetCode problem `minimum-operations-to-reduce-x-to-zero`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinOperations

def elems (nums : Slice I64) : List Int := nums.val.map (fun v => v.val)

def L (a : List Int) (k : Nat) : Int := (a.take k).sum

def R (a : List Int) (k : Nat) : Int := (a.drop (a.length - k)).sum

def total (a : List Int) : Int := a.sum

def segSum (a : List Int) (lo hi : Nat) : Int := ((a.drop lo).take (hi - lo)).sum

def T (a : List Int) (x : Int) : Set Int :=
  {m | ∃ l r : Nat, l + r ≤ a.length ∧ L a l + R a r = x ∧ m = (l + r : Nat)}

def HasPair (a : List Int) (x : Int) : Prop :=
  ∃ l r : Nat, l + r ≤ a.length ∧ L a l + R a r = x

def IsMinOf (S : Set Int) (m : Int) : Prop := m ∈ S ∧ ∀ y, y ∈ S → m ≤ y

def IsLargestSegLen (a : List Int) (x : Int) (K : Nat) : Prop :=
  (∃ lo hi : Nat, lo ≤ hi ∧ hi ≤ a.length ∧ hi - lo = K ∧ segSum a lo hi = total a - x) ∧
    ∀ lo hi : Nat, lo ≤ hi → hi ≤ a.length → segSum a lo hi = total a - x → hi - lo ≤ K

def IsReversed (nums rev : Slice I64) : Prop := elems rev = (elems nums).reverse

def ValidInput (nums : Slice I64) (x : I64) : Prop :=
  1 ≤ (elems nums).length ∧ (elems nums).length ≤ 100000 ∧
    (∀ v ∈ elems nums, 1 ≤ v ∧ v ≤ 10000) ∧ 1 ≤ x.val ∧ x.val ≤ 1000000000

/-- Define L(k) = sum_{i=0}^{k-1} nums[i] for 0 <= k <= n (with L(0)=0), and R(k) = sum_{i=n-k}^{n-1} nums[i] for 0 <= k <= n (with R(0)=0). Let T = { l+r | 0 <= l, 0 <= r, l+r <= n, and L(l)+R(r)=x }. Whenever the function returns a result res, if T is nonempty then res = min(T), and if T is empty then res = -1.
  Preconditions: Let n = len(nums). 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 10000; 1 <= x <= 1000000000. -/
theorem spec_1 (nums : Slice I64) (x : I64) (h : ValidInput nums x) :
    ∀ res : I64, Aegis.MinOperations.min_operations nums x = ok res →
      (HasPair (elems nums) x.val → IsMinOf (T (elems nums) x.val) res.val) ∧
        (¬ HasPair (elems nums) x.val → res.val = -1) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice I64) (x : I64) (h : ValidInput nums x), ∀ res : I64, Aegis.MinOperations.min_operations nums x = ok res →
      (HasPair (elems nums) x.val → IsMinOf (T (elems nums) x.val) res.val) ∧
        (¬ HasPair (elems nums) x.val → res.val = -1)) := by
  sorry

/-- Whenever the function returns a result res, either res = -1 or 1 <= res <= n.
  Preconditions: Let n = len(nums). 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 10000; 1 <= x <= 1000000000. -/
theorem spec_2 (nums : Slice I64) (x : I64) (h : ValidInput nums x) :
    ∀ res : I64, Aegis.MinOperations.min_operations nums x = ok res →
      res.val = -1 ∨ (1 ≤ res.val ∧ res.val ≤ ((elems nums).length : Int)) := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice I64) (x : I64) (h : ValidInput nums x), ∀ res : I64, Aegis.MinOperations.min_operations nums x = ok res →
      res.val = -1 ∨ (1 ≤ res.val ∧ res.val ≤ ((elems nums).length : Int))) := by
  sorry

/-- Whenever the function returns a result res, res = 1 if and only if (x = nums[0] or x = nums[n-1]).
  Preconditions: Let n = len(nums). 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 10000; 1 <= x <= 1000000000. -/
theorem spec_3 (nums : Slice I64) (x : I64) (h : ValidInput nums x) :
    ∀ res : I64, Aegis.MinOperations.min_operations nums x = ok res →
      (res.val = 1 ↔ ((elems nums).head? = some x.val ∨ (elems nums).getLast? = some x.val)) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice I64) (x : I64) (h : ValidInput nums x), ∀ res : I64, Aegis.MinOperations.min_operations nums x = ok res →
      (res.val = 1 ↔ ((elems nums).head? = some x.val ∨ (elems nums).getLast? = some x.val))) := by
  sorry

/-- Define total = sum_{i=0}^{n-1} nums[i]. Whenever the function returns a result res, res = n if and only if x = total.
  Preconditions: Let n = len(nums). 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 10000; 1 <= x <= 1000000000. -/
theorem spec_4 (nums : Slice I64) (x : I64) (h : ValidInput nums x) :
    ∀ res : I64, Aegis.MinOperations.min_operations nums x = ok res →
      (res.val = ((elems nums).length : Int) ↔ x.val = total (elems nums)) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice I64) (x : I64) (h : ValidInput nums x), ∀ res : I64, Aegis.MinOperations.min_operations nums x = ok res →
      (res.val = ((elems nums).length : Int) ↔ x.val = total (elems nums))) := by
  sorry

/-- Define total = sum_{i=0}^{n-1} nums[i]. Whenever the function returns a result res, if x > total then res = -1.
  Preconditions: Let n = len(nums). 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 10000; 1 <= x <= 1000000000. -/
theorem spec_5 (nums : Slice I64) (x : I64) (h : ValidInput nums x) :
    ∀ res : I64, Aegis.MinOperations.min_operations nums x = ok res →
      total (elems nums) < x.val → res.val = -1 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice I64) (x : I64) (h : ValidInput nums x), ∀ res : I64, Aegis.MinOperations.min_operations nums x = ok res →
      total (elems nums) < x.val → res.val = -1) := by
  sorry

/-- Whenever the function returns a result res, if x < min_{0 <= i < n} nums[i], then res = -1.
  Preconditions: Let n = len(nums). 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 10000; 1 <= x <= 1000000000. -/
theorem spec_6 (nums : Slice I64) (x : I64) (h : ValidInput nums x) :
    ∀ res : I64, Aegis.MinOperations.min_operations nums x = ok res →
      (∀ v ∈ elems nums, x.val < v) → res.val = -1 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice I64) (x : I64) (h : ValidInput nums x), ∀ res : I64, Aegis.MinOperations.min_operations nums x = ok res →
      (∀ v ∈ elems nums, x.val < v) → res.val = -1) := by
  sorry

/-- Whenever the function returns a result res, if res != -1 then res <= x.
  Preconditions: Let n = len(nums). 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 10000; 1 <= x <= 1000000000. -/
theorem spec_7 (nums : Slice I64) (x : I64) (h : ValidInput nums x) :
    ∀ res : I64, Aegis.MinOperations.min_operations nums x = ok res →
      res.val ≠ -1 → res.val ≤ x.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice I64) (x : I64) (h : ValidInput nums x), ∀ res : I64, Aegis.MinOperations.min_operations nums x = ok res →
      res.val ≠ -1 → res.val ≤ x.val) := by
  sorry

/-- Let rev be the slice of length n with rev[i] = nums[n-1-i] for every i with 0 <= i < n. Whenever the function returns res on input (nums, x) and res' on input (rev, x), we have res = res'.
  Preconditions: Let n = len(nums). 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 10000; 1 <= x <= 1000000000. -/
theorem spec_8 (nums rev : Slice I64) (x : I64) (h : ValidInput nums x)
    (hrev : IsReversed nums rev) :
    ∀ res res' : I64, Aegis.MinOperations.min_operations nums x = ok res →
      Aegis.MinOperations.min_operations rev x = ok res' → res = res' := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums rev : Slice I64) (x : I64) (h : ValidInput nums x)
    (hrev : IsReversed nums rev), ∀ res res' : I64, Aegis.MinOperations.min_operations nums x = ok res →
      Aegis.MinOperations.min_operations rev x = ok res' → res = res') := by
  sorry

/-- Define total = sum_{i=0}^{n-1} nums[i]. Whenever the function returns a result res with res != -1, the integer n - res is the largest integer L for which there exist indices a and b with 0 <= a <= b <= n, b - a = L, and sum_{i=a}^{b-1} nums[i] = total - x. The empty subarray (a = b) is allowed and has sum 0.
  Preconditions: Let n = len(nums). 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 10000; 1 <= x <= 1000000000. -/
theorem spec_9 (nums : Slice I64) (x : I64) (h : ValidInput nums x) :
    ∀ res : I64, Aegis.MinOperations.min_operations nums x = ok res → res.val ≠ -1 →
      ∃ K : Nat, IsLargestSegLen (elems nums) x.val K ∧
        res.val = ((elems nums).length : Int) - (K : Int) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice I64) (x : I64) (h : ValidInput nums x), ∀ res : I64, Aegis.MinOperations.min_operations nums x = ok res → res.val ≠ -1 →
      ∃ K : Nat, IsLargestSegLen (elems nums) x.val K ∧
        res.val = ((elems nums).length : Int) - (K : Int)) := by
  sorry

/-- Define L(k) = sum_{i=0}^{k-1} nums[i] for 0 <= k <= n (with L(0)=0), and R(k) = sum_{i=n-k}^{n-1} nums[i] for 0 <= k <= n (with R(0)=0). Whenever the function returns a result res with res != -1, there exist integers l and r such that 0 <= l, 0 <= r, l+r <= n, l+r = res, and L(l)+R(r)=x.
  Preconditions: Let n = len(nums). 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 10000; 1 <= x <= 1000000000. -/
theorem spec_10 (nums : Slice I64) (x : I64) (h : ValidInput nums x) :
    ∀ res : I64, Aegis.MinOperations.min_operations nums x = ok res → res.val ≠ -1 →
      ∃ l r : Nat, l + r ≤ (elems nums).length ∧ (l + r : Int) = res.val ∧
        L (elems nums) l + R (elems nums) r = x.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice I64) (x : I64) (h : ValidInput nums x), ∀ res : I64, Aegis.MinOperations.min_operations nums x = ok res → res.val ≠ -1 →
      ∃ l r : Nat, l + r ≤ (elems nums).length ∧ (l + r : Int) = res.val ∧
        L (elems nums) l + R (elems nums) r = x.val) := by
  sorry

/-- Define L(k) = sum_{i=0}^{k-1} nums[i] for 0 <= k <= n (with L(0)=0), and R(k) = sum_{i=n-k}^{n-1} nums[i] for 0 <= k <= n (with R(0)=0). Whenever the function returns a result res with res != -1, for every pair of integers l and r such that 0 <= l, 0 <= r, l+r <= n, and L(l)+R(r)=x, we have res <= l+r.
  Preconditions: Let n = len(nums). 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 10000; 1 <= x <= 1000000000. -/
theorem spec_11 (nums : Slice I64) (x : I64) (h : ValidInput nums x) :
    ∀ res : I64, Aegis.MinOperations.min_operations nums x = ok res → res.val ≠ -1 →
      ∀ l r : Nat, l + r ≤ (elems nums).length →
        L (elems nums) l + R (elems nums) r = x.val → res.val ≤ (l + r : Int) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice I64) (x : I64) (h : ValidInput nums x), ∀ res : I64, Aegis.MinOperations.min_operations nums x = ok res → res.val ≠ -1 →
      ∀ l r : Nat, l + r ≤ (elems nums).length →
        L (elems nums) l + R (elems nums) r = x.val → res.val ≤ (l + r : Int)) := by
  sorry

/-- Define L(k) = sum_{i=0}^{k-1} nums[i] for 0 <= k <= n (with L(0)=0), and R(k) = sum_{i=n-k}^{n-1} nums[i] for 0 <= k <= n (with R(0)=0). Whenever the function returns a result res, res = -1 if and only if there do not exist integers l and r with 0 <= l, 0 <= r, l+r <= n, and L(l)+R(r)=x.
  Preconditions: Let n = len(nums). 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 10000; 1 <= x <= 1000000000. -/
theorem spec_12 (nums : Slice I64) (x : I64) (h : ValidInput nums x) :
    ∀ res : I64, Aegis.MinOperations.min_operations nums x = ok res →
      (res.val = -1 ↔ ¬ HasPair (elems nums) x.val) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice I64) (x : I64) (h : ValidInput nums x), ∀ res : I64, Aegis.MinOperations.min_operations nums x = ok res →
      (res.val = -1 ↔ ¬ HasPair (elems nums) x.val)) := by
  sorry

/-- Define L(k) = sum_{i=0}^{k-1} nums[i] for 0 <= k <= n (with L(0)=0), and R(k) = sum_{i=n-k}^{n-1} nums[i] for 0 <= k <= n (with R(0)=0). Whenever the function returns a result res, for every integer k with 0 <= k <= n, if L(k)=x or R(k)=x, then res != -1 and res <= k.
  Preconditions: Let n = len(nums). 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 10000; 1 <= x <= 1000000000. -/
theorem spec_13 (nums : Slice I64) (x : I64) (h : ValidInput nums x) :
    ∀ res : I64, Aegis.MinOperations.min_operations nums x = ok res →
      ∀ k : Nat, k ≤ (elems nums).length →
        (L (elems nums) k = x.val ∨ R (elems nums) k = x.val) →
          res.val ≠ -1 ∧ res.val ≤ (k : Int) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums : Slice I64) (x : I64) (h : ValidInput nums x), ∀ res : I64, Aegis.MinOperations.min_operations nums x = ok res →
      ∀ k : Nat, k ≤ (elems nums).length →
        (L (elems nums) k = x.val ∨ R (elems nums) k = x.val) →
          res.val ≠ -1 ∧ res.val ≤ (k : Int)) := by
  sorry

/-- Whenever the function returns a result res, if x = 1, then res = 1 if (nums[0] = 1 or nums[n-1] = 1), and res = -1 otherwise.
  Preconditions: Let n = len(nums). 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 10000; 1 <= x <= 1000000000. -/
theorem spec_14 (nums : Slice I64) (x : I64) (h : ValidInput nums x) :
    ∀ res : I64, Aegis.MinOperations.min_operations nums x = ok res →
      x.val = 1 →
        (((elems nums).head? = some 1 ∨ (elems nums).getLast? = some 1) → res.val = 1) ∧
          (¬ ((elems nums).head? = some 1 ∨ (elems nums).getLast? = some 1) → res.val = -1) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (nums : Slice I64) (x : I64) (h : ValidInput nums x), ∀ res : I64, Aegis.MinOperations.min_operations nums x = ok res →
      x.val = 1 →
        (((elems nums).head? = some 1 ∨ (elems nums).getLast? = some 1) → res.val = 1) ∧
          (¬ ((elems nums).head? = some 1 ∨ (elems nums).getLast? = some 1) → res.val = -1)) := by
  sorry

/-- The function returns a result res (it does not fail, panic, or overflow) for every input satisfying the constraints.
  Preconditions: Let n = len(nums). 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 10000; 1 <= x <= 1000000000. -/
theorem spec_15 (nums : Slice I64) (x : I64) (h : ValidInput nums x) :
    ∃ res : I64, Aegis.MinOperations.min_operations nums x = ok res := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (nums : Slice I64) (x : I64) (h : ValidInput nums x), ∃ res : I64, Aegis.MinOperations.min_operations nums x = ok res) := by
  sorry

end AegisSpec.MinOperations
