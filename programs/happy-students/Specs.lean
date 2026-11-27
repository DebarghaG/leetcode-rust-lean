import Aegis.CountWays.Code.Funs

/-!
# Specifications of `Aegis.CountWays.count_ways`

LeetCode problem `happy-students`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.CountWays

open Aegis.CountWays

def vals (nums : Slice I64) : List Int := nums.val.map (fun x => x.val)

def elt (l : List Int) (i : Nat) : Int := l.getD i 0

def Precondition (l : List Int) : Prop :=
  1 ≤ l.length ∧ l.length ≤ 100000 ∧
    ∀ i, i < l.length → 0 ≤ elt l i ∧ elt l i < (l.length : Int)

def IsValid (l : List Int) (S : Finset Nat) : Prop :=
  S ⊆ Finset.range l.length ∧
    ∀ i ∈ Finset.range l.length,
      (i ∈ S → (S.card : Int) > elt l i) ∧ (i ∉ S → (S.card : Int) < elt l i)

instance decidableIsValid (l : List Int) (S : Finset Nat) : Decidable (IsValid l S) := by
  unfold IsValid
  infer_instance

def selections (l : List Int) : Finset (Finset Nat) :=
  (Finset.range l.length).powerset.filter (fun S => IsValid l S)

@[simp] theorem mem_selections {l : List Int} {S : Finset Nat} :
    S ∈ selections l ↔ IsValid l S := by
  rw [selections, Finset.mem_filter, Finset.mem_powerset]
  constructor
  · rintro ⟨-, h⟩; exact h
  · rintro h; exact ⟨h.1, h⟩

def countValid (l : List Int) : Nat := (selections l).card

def lessSet (l : List Int) (k : Nat) : Finset Nat :=
  (Finset.range l.length).filter (fun i => elt l i < (k : Int))

def L (l : List Int) (k : Nat) : Nat := (lessSet l k).card

def E (l : List Int) (k : Nat) : Nat :=
  ((Finset.range l.length).filter (fun i => elt l i = (k : Int))).card

def goodK (l : List Int) : Finset Nat :=
  (Finset.range (l.length + 1)).filter (fun k => L l k = k ∧ E l k = 0)

def sortedCondition (b : List Int) (k : Nat) : Prop :=
  (k = 0 ∨ elt b (k - 1) < (k : Int)) ∧ (k = b.length ∨ elt b k > (k : Int))

instance decidableSortedCondition (b : List Int) (k : Nat) : Decidable (sortedCondition b k) := by
  unfold sortedCondition
  infer_instance

def sortedCount (b : List Int) : Nat :=
  ((Finset.range (b.length + 1)).filter (fun k => sortedCondition b k)).card

def iota (n : Nat) : List Int := (List.range n).map (fun k => (k : Int))

/-- Whenever count_ways returns a result r, r equals the number of subsets S of {0,1,...,n-1} such that for every i with 0 <= i < n: if i is in S then |S| > nums[i], and if i is not in S then |S| < nums[i]. Here |S| is the number of selected indices; the empty subset and the full subset are allowed.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000 and for every i with 0 <= i < n, 0 <= nums[i] < n. -/
theorem spec_1 (nums : Slice I64) (hpre : Precondition (vals nums)) (r : I64)
    (hr : count_ways nums = ok r) :
    r.val = (countValid (vals nums) : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice I64) (hpre : Precondition (vals nums)) (r : I64)
    (hr : count_ways nums = ok r), r.val = (countValid (vals nums) : Int)) := by
  sorry

/-- For every input satisfying the preconditions, count_ways returns a result (it does not fail or panic), and the returned value is a valid 64-bit integer.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000 and for every i with 0 <= i < n, 0 <= nums[i] < n. -/
theorem spec_2 (nums : Slice I64) (hpre : Precondition (vals nums)) :
    ∃ r : I64, count_ways nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice I64) (hpre : Precondition (vals nums)), ∃ r : I64, count_ways nums = ok r) := by
  sorry

/-- Whenever count_ways returns a result r, 1 <= r <= n.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000 and for every i with 0 <= i < n, 0 <= nums[i] < n. -/
theorem spec_3 (nums : Slice I64) (hpre : Precondition (vals nums)) (r : I64)
    (hr : count_ways nums = ok r) :
    1 ≤ r.val ∧ r.val ≤ ((vals nums).length : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice I64) (hpre : Precondition (vals nums)) (r : I64)
    (hr : count_ways nums = ok r), 1 ≤ r.val ∧ r.val ≤ ((vals nums).length : Int)) := by
  sorry

/-- Whenever count_ways returns a result r, define L(k) as the number of indices i with 0 <= i < n and nums[i] < k, and E(k) as the number of indices i with 0 <= i < n and nums[i] = k. Then r equals the number of integers k with 0 <= k <= n such that L(k) = k and E(k) = 0.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000 and for every i with 0 <= i < n, 0 <= nums[i] < n. -/
theorem spec_4 (nums : Slice I64) (hpre : Precondition (vals nums)) (r : I64)
    (hr : count_ways nums = ok r) :
    r.val = ((goodK (vals nums)).card : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice I64) (hpre : Precondition (vals nums)) (r : I64)
    (hr : count_ways nums = ok r), r.val = ((goodK (vals nums)).card : Int)) := by
  sorry

/-- Whenever count_ways returns a result r, the full set S = {0,1,...,n-1} is a valid selection and is counted among the r ways; it has |S| = n and n > nums[i] for every i with 0 <= i < n.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000 and for every i with 0 <= i < n, 0 <= nums[i] < n. -/
theorem spec_5 (nums : Slice I64) (hpre : Precondition (vals nums)) (r : I64)
    (hr : count_ways nums = ok r) :
    Finset.range (vals nums).length ∈ selections (vals nums) ∧
      1 ≤ r.val ∧
        (Finset.range (vals nums).length).card = (vals nums).length ∧
          ∀ i, i < (vals nums).length → elt (vals nums) i < ((vals nums).length : Int) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice I64) (hpre : Precondition (vals nums)) (r : I64)
    (hr : count_ways nums = ok r), Finset.range (vals nums).length ∈ selections (vals nums) ∧
      1 ≤ r.val ∧
        (Finset.range (vals nums).length).card = (vals nums).length ∧
          ∀ i, i < (vals nums).length → elt (vals nums) i < ((vals nums).length : Int)) := by
  sorry

/-- Whenever count_ways returns a result r, let b be any nondecreasing rearrangement of nums of length n, so b[0] <= b[1] <= ... <= b[n-1] and b is a permutation of nums. Then r equals the number of integers k with 0 <= k <= n such that (k = 0 or b[k-1] < k) and (k = n or b[k] > k). Here b is 0-indexed, and b[k] is used only when k < n.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000 and for every i with 0 <= i < n, 0 <= nums[i] < n. -/
theorem spec_6 (nums : Slice I64) (hpre : Precondition (vals nums)) (r : I64)
    (hr : count_ways nums = ok r) (b : List Int) (hperm : b.Perm (vals nums))
    (hsorted : b.Pairwise (· ≤ ·)) :
    r.val = (sortedCount b : Int) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice I64) (hpre : Precondition (vals nums)) (r : I64)
    (hr : count_ways nums = ok r) (b : List Int) (hperm : b.Perm (vals nums))
    (hsorted : b.Pairwise (· ≤ ·)), r.val = (sortedCount b : Int)) := by
  sorry

/-- Whenever count_ways returns a result r and there is an integer v such that nums[i] = v for every i with 0 <= i < n, then r = 1 if v = 0, and r = 2 if v > 0.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000 and for every i with 0 <= i < n, 0 <= nums[i] < n. -/
theorem spec_7 (nums : Slice I64) (hpre : Precondition (vals nums)) (r : I64)
    (hr : count_ways nums = ok r) (v : Int)
    (hv : ∀ i, i < (vals nums).length → elt (vals nums) i = v) :
    (v = 0 → r.val = 1) ∧ (0 < v → r.val = 2) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice I64) (hpre : Precondition (vals nums)) (r : I64)
    (hr : count_ways nums = ok r) (v : Int)
    (hv : ∀ i, i < (vals nums).length → elt (vals nums) i = v), (v = 0 → r.val = 1) ∧ (0 < v → r.val = 2)) := by
  sorry

/-- Whenever count_ways returns a result r and nums is a permutation of {0,1,...,n-1} (that is, each value 0,1,...,n-1 occurs exactly once), then r = 1.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000 and for every i with 0 <= i < n, 0 <= nums[i] < n. -/
theorem spec_8 (nums : Slice I64) (hpre : Precondition (vals nums)) (r : I64)
    (hr : count_ways nums = ok r)
    (hperm : (vals nums).Perm (iota (vals nums).length)) :
    r.val = 1 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice I64) (hpre : Precondition (vals nums)) (r : I64)
    (hr : count_ways nums = ok r)
    (hperm : (vals nums).Perm (iota (vals nums).length)), r.val = 1) := by
  sorry

end AegisSpec.CountWays
