import Aegis.GcdSort.Code.Funs

/-!
# Specifications of `Aegis.GcdSort.gcd_sort`

LeetCode problem `gcd-sort-of-an-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.GcdSort

def vals (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

def valAt (l : List Int) (k : ℕ) : Int := l.getD k 0

def IsRearrangement (l s : List Int) : Prop := s.Perm l ∧ s.Pairwise (· ≤ ·)

def sortedList (l : List Int) : List Int := l.insertionSort (· ≤ ·)

def sortedVals (nums : Slice Std.I64) : List Int := sortedList (vals nums)

def Adj (l : List Int) (i j : ℕ) : Prop :=
  ∃ (hi : i < l.length) (hj : j < l.length), 1 < Int.gcd (l[i]) (l[j])

def GcdConn (nums : Slice Std.I64) (i j : ℕ) : Prop :=
  i < (vals nums).length ∧ j < (vals nums).length ∧
    Relation.ReflTransGen (Adj (vals nums)) i j

def ValAdj (l : List Int) (u v : Int) : Prop := u ∈ l ∧ v ∈ l ∧ 1 < Int.gcd u v

def SameValComponent (l : List Int) (u v : Int) : Prop :=
  u ∈ l ∧ v ∈ l ∧ Relation.ReflTransGen (ValAdj l) u v

noncomputable def connVals (nums : Slice Std.I64) (l : List Int) (i : ℕ) : List Int := by
  classical
  exact ((List.range (vals nums).length).filter (fun j => GcdConn nums i j)).map
    (fun j => valAt l j)

noncomputable def connValues (nums : Slice Std.I64) (l : List Int) (i : ℕ) : Multiset Int :=
  Multiset.ofList (connVals nums l i)

/-- Let s be the non-decreasing rearrangement of nums, i.e. the unique sequence of length n such that s[0] <= s[1] <= ... <= s[n-1] and s has the same multiset of values as nums. Say indices i and j (0 <= i, j < n) are gcd-connected if there is m >= 0 and a sequence of indices a_0, ..., a_m with a_0 = i, a_m = j and gcd(nums[a_t], nums[a_{t+1}]) > 1 for every 0 <= t < m. The function returns a result r and r = true if and only if for every i with 0 <= i < n, the multiset of values nums[j] over all j with 0 <= j < n that are gcd-connected to i equals the multiset of values s[j] over those same j.
  Preconditions: Let n = len(nums). 1 <= n <= 30000, and for every k with 0 <= k < n, 1 <= nums[k] <= 100000. (The problem lists 2 <= nums[k]; we allow 1 because the provided examples contain 1, and gcd(1, x) = 1 for every x.) -/
theorem spec_1 (nums : Slice Std.I64)
    (hpos : 1 ≤ (vals nums).length) (hle : (vals nums).length ≤ 30000)
    (hb : ∀ k, k < (vals nums).length → 1 ≤ valAt (vals nums) k ∧ valAt (vals nums) k ≤ 100000) :
    ∃ r, Aegis.GcdSort.gcd_sort nums = ok r ∧
      (r = true ↔ ∀ i, i < (vals nums).length →
        connValues nums (vals nums) i = connValues nums (sortedVals nums) i) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hpos : 1 ≤ (vals nums).length) (hle : (vals nums).length ≤ 30000)
    (hb : ∀ k, k < (vals nums).length → 1 ≤ valAt (vals nums) k ∧ valAt (vals nums) k ≤ 100000), ∃ r, Aegis.GcdSort.gcd_sort nums = ok r ∧
      (r = true ↔ ∀ i, i < (vals nums).length →
        connValues nums (vals nums) i = connValues nums (sortedVals nums) i)) := by
  sorry

/-- The function returns a result r (it never returns an error, panics, goes out of bounds, or overflows).
  Preconditions: Let n = len(nums). 1 <= n <= 30000, and for every k with 0 <= k < n, 1 <= nums[k] <= 100000. -/
theorem spec_2 (nums : Slice Std.I64)
    (hpos : 1 ≤ (vals nums).length) (hle : (vals nums).length ≤ 30000)
    (hb : ∀ k, k < (vals nums).length → 1 ≤ valAt (vals nums) k ∧ valAt (vals nums) k ≤ 100000) :
    ∃ r, Aegis.GcdSort.gcd_sort nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hpos : 1 ≤ (vals nums).length) (hle : (vals nums).length ≤ 30000)
    (hb : ∀ k, k < (vals nums).length → 1 ≤ valAt (vals nums) k ∧ valAt (vals nums) k ≤ 100000), ∃ r, Aegis.GcdSort.gcd_sort nums = ok r) := by
  sorry

/-- The function returns a result r and r = true.
  Preconditions: Let n = len(nums). n = 1, and 1 <= nums[0] <= 100000. -/
theorem spec_3 (nums : Slice Std.I64)
    (hlen : (vals nums).length = 1)
    (hb : 1 ≤ valAt (vals nums) 0 ∧ valAt (vals nums) 0 ≤ 100000) :
    ∃ r, Aegis.GcdSort.gcd_sort nums = ok r ∧ r = true := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : (vals nums).length = 1)
    (hb : 1 ≤ valAt (vals nums) 0 ∧ valAt (vals nums) 0 ≤ 100000), ∃ r, Aegis.GcdSort.gcd_sort nums = ok r ∧ r = true) := by
  sorry

/-- The function returns a result r and r = true if and only if (nums[0] <= nums[1] or gcd(nums[0], nums[1]) > 1).
  Preconditions: Let n = len(nums). n = 2, and 1 <= nums[0], nums[1] <= 100000. -/
theorem spec_4 (nums : Slice Std.I64)
    (hlen : (vals nums).length = 2)
    (hb0 : 1 ≤ valAt (vals nums) 0 ∧ valAt (vals nums) 0 ≤ 100000)
    (hb1 : 1 ≤ valAt (vals nums) 1 ∧ valAt (vals nums) 1 ≤ 100000) :
    ∃ r, Aegis.GcdSort.gcd_sort nums = ok r ∧
      (r = true ↔ (valAt (vals nums) 0 ≤ valAt (vals nums) 1 ∨
        1 < Int.gcd (valAt (vals nums) 0) (valAt (vals nums) 1))) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : (vals nums).length = 2)
    (hb0 : 1 ≤ valAt (vals nums) 0 ∧ valAt (vals nums) 0 ≤ 100000)
    (hb1 : 1 ≤ valAt (vals nums) 1 ∧ valAt (vals nums) 1 ≤ 100000), ∃ r, Aegis.GcdSort.gcd_sort nums = ok r ∧
      (r = true ↔ (valAt (vals nums) 0 ≤ valAt (vals nums) 1 ∨
        1 < Int.gcd (valAt (vals nums) 0) (valAt (vals nums) 1)))) := by
  sorry

/-- Say i and j (0 <= i, j < n) are gcd-connected if there is m >= 0 and indices a_0, ..., a_m with a_0 = i, a_m = j and gcd(nums[a_t], nums[a_{t+1}]) > 1 for every 0 <= t < m. If for every pair i, j with 0 <= i, j < n, i and j are gcd-connected (there is a single component), then the function returns a result r and r = true.
  Preconditions: Let n = len(nums). 1 <= n <= 30000, and for every k with 0 <= k < n, 1 <= nums[k] <= 100000. -/
theorem spec_5 (nums : Slice Std.I64)
    (hpos : 1 ≤ (vals nums).length) (hle : (vals nums).length ≤ 30000)
    (hb : ∀ k, k < (vals nums).length → 1 ≤ valAt (vals nums) k ∧ valAt (vals nums) k ≤ 100000)
    (hsingle : ∀ i, i < (vals nums).length → ∀ j, j < (vals nums).length → GcdConn nums i j) :
    ∃ r, Aegis.GcdSort.gcd_sort nums = ok r ∧ r = true := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hpos : 1 ≤ (vals nums).length) (hle : (vals nums).length ≤ 30000)
    (hb : ∀ k, k < (vals nums).length → 1 ≤ valAt (vals nums) k ∧ valAt (vals nums) k ≤ 100000)
    (hsingle : ∀ i, i < (vals nums).length → ∀ j, j < (vals nums).length → GcdConn nums i j), ∃ r, Aegis.GcdSort.gcd_sort nums = ok r ∧ r = true) := by
  sorry

/-- Let s be the non-decreasing rearrangement of nums. Whenever the function returns a result r with r = true, then for every i with 0 <= i < n: if gcd(nums[i], nums[j]) = 1 for every j with 0 <= j < n and j != i, then nums[i] = s[i].
  Preconditions: Let n = len(nums). 1 <= n <= 30000, and for every k with 0 <= k < n, 1 <= nums[k] <= 100000. -/
theorem spec_6 (nums : Slice Std.I64)
    (hpos : 1 ≤ (vals nums).length) (hle : (vals nums).length ≤ 30000)
    (hb : ∀ k, k < (vals nums).length → 1 ≤ valAt (vals nums) k ∧ valAt (vals nums) k ≤ 100000) :
    ∀ r, Aegis.GcdSort.gcd_sort nums = ok r → r = true →
      ∀ i, i < (vals nums).length →
        (∀ j, j < (vals nums).length → j ≠ i →
          Int.gcd (valAt (vals nums) i) (valAt (vals nums) j) = 1) →
        valAt (vals nums) i = valAt (sortedVals nums) i := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hpos : 1 ≤ (vals nums).length) (hle : (vals nums).length ≤ 30000)
    (hb : ∀ k, k < (vals nums).length → 1 ≤ valAt (vals nums) k ∧ valAt (vals nums) k ≤ 100000), ∀ r, Aegis.GcdSort.gcd_sort nums = ok r → r = true →
      ∀ i, i < (vals nums).length →
        (∀ j, j < (vals nums).length → j ≠ i →
          Int.gcd (valAt (vals nums) i) (valAt (vals nums) j) = 1) →
        valAt (vals nums) i = valAt (sortedVals nums) i) := by
  sorry

/-- Let s be the non-decreasing rearrangement of nums. Say i and j (0 <= i, j < n) are gcd-connected if there is m >= 0 and indices a_0, ..., a_m with a_0 = i, a_m = j and gcd(nums[a_t], nums[a_{t+1}]) > 1 for every 0 <= t < m. Whenever the function returns a result r with r = true, then for every i with 0 <= i < n there exists j with 0 <= j < n such that j is gcd-connected to i and nums[j] = s[i].
  Preconditions: Let n = len(nums). 1 <= n <= 30000, and for every k with 0 <= k < n, 1 <= nums[k] <= 100000. -/
theorem spec_7 (nums : Slice Std.I64)
    (hpos : 1 ≤ (vals nums).length) (hle : (vals nums).length ≤ 30000)
    (hb : ∀ k, k < (vals nums).length → 1 ≤ valAt (vals nums) k ∧ valAt (vals nums) k ≤ 100000) :
    ∀ r, Aegis.GcdSort.gcd_sort nums = ok r → r = true →
      ∀ i, i < (vals nums).length →
        ∃ j, j < (vals nums).length ∧ GcdConn nums i j ∧
          valAt (vals nums) j = valAt (sortedVals nums) i := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hpos : 1 ≤ (vals nums).length) (hle : (vals nums).length ≤ 30000)
    (hb : ∀ k, k < (vals nums).length → 1 ≤ valAt (vals nums) k ∧ valAt (vals nums) k ≤ 100000), ∀ r, Aegis.GcdSort.gcd_sort nums = ok r → r = true →
      ∀ i, i < (vals nums).length →
        ∃ j, j < (vals nums).length ∧ GcdConn nums i j ∧
          valAt (vals nums) j = valAt (sortedVals nums) i) := by
  sorry

/-- Let s be the non-decreasing rearrangement of nums. Say values u and v (each appearing among nums[0], ..., nums[n-1]) are in the same value-component if u = v or there exist m >= 1 and values w_0, ..., w_m, each appearing among nums[0], ..., nums[n-1], with w_0 = u, w_m = v and gcd(w_t, w_{t+1}) > 1 for every 0 <= t < m. Whenever the function returns a result r with r = true, then for every i with 0 <= i < n, nums[i] and s[i] are in the same value-component.
  Preconditions: Let n = len(nums). 1 <= n <= 30000, and for every k with 0 <= k < n, 1 <= nums[k] <= 100000. -/
theorem spec_8 (nums : Slice Std.I64)
    (hpos : 1 ≤ (vals nums).length) (hle : (vals nums).length ≤ 30000)
    (hb : ∀ k, k < (vals nums).length → 1 ≤ valAt (vals nums) k ∧ valAt (vals nums) k ≤ 100000) :
    ∀ r, Aegis.GcdSort.gcd_sort nums = ok r → r = true →
      ∀ i, i < (vals nums).length →
        SameValComponent (vals nums) (valAt (vals nums) i) (valAt (sortedVals nums) i) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hpos : 1 ≤ (vals nums).length) (hle : (vals nums).length ≤ 30000)
    (hb : ∀ k, k < (vals nums).length → 1 ≤ valAt (vals nums) k ∧ valAt (vals nums) k ≤ 100000), ∀ r, Aegis.GcdSort.gcd_sort nums = ok r → r = true →
      ∀ i, i < (vals nums).length →
        SameValComponent (vals nums) (valAt (vals nums) i) (valAt (sortedVals nums) i)) := by
  sorry

/-- Let s be the non-decreasing rearrangement of nums. The function returns a result r and r = true if and only if nums is non-decreasing (nums[k] <= nums[k+1] for every 0 <= k < n - 1).
  Preconditions: Let n = len(nums). 1 <= n <= 30000, for every k with 0 <= k < n, 1 <= nums[k] <= 100000, and for every i, j with 0 <= i < j < n, gcd(nums[i], nums[j]) = 1. -/
theorem spec_9 (nums : Slice Std.I64)
    (hpos : 1 ≤ (vals nums).length) (hle : (vals nums).length ≤ 30000)
    (hb : ∀ k, k < (vals nums).length → 1 ≤ valAt (vals nums) k ∧ valAt (vals nums) k ≤ 100000)
    (hcop : ∀ i, i < (vals nums).length → ∀ j, i < j → j < (vals nums).length →
      Int.gcd (valAt (vals nums) i) (valAt (vals nums) j) = 1) :
    ∃ r, Aegis.GcdSort.gcd_sort nums = ok r ∧
      (r = true ↔ ∀ k, k + 1 < (vals nums).length →
        valAt (vals nums) k ≤ valAt (vals nums) (k + 1)) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hpos : 1 ≤ (vals nums).length) (hle : (vals nums).length ≤ 30000)
    (hb : ∀ k, k < (vals nums).length → 1 ≤ valAt (vals nums) k ∧ valAt (vals nums) k ≤ 100000)
    (hcop : ∀ i, i < (vals nums).length → ∀ j, i < j → j < (vals nums).length →
      Int.gcd (valAt (vals nums) i) (valAt (vals nums) j) = 1), ∃ r, Aegis.GcdSort.gcd_sort nums = ok r ∧
      (r = true ↔ ∀ k, k + 1 < (vals nums).length →
        valAt (vals nums) k ≤ valAt (vals nums) (k + 1))) := by
  sorry

/-- Let s be the non-decreasing rearrangement of nums. If the function returns a result r and there exists i with 0 <= i < n such that gcd(nums[i], nums[j]) = 1 for every j with 0 <= j < n and j != i and nums[i] != s[i], then r = false.
  Preconditions: Let n = len(nums). 1 <= n <= 30000, and for every k with 0 <= k < n, 1 <= nums[k] <= 100000. -/
theorem spec_10 (nums : Slice Std.I64)
    (hpos : 1 ≤ (vals nums).length) (hle : (vals nums).length ≤ 30000)
    (hb : ∀ k, k < (vals nums).length → 1 ≤ valAt (vals nums) k ∧ valAt (vals nums) k ≤ 100000) :
    ∀ r, Aegis.GcdSort.gcd_sort nums = ok r →
      (∃ i, i < (vals nums).length ∧
        (∀ j, j < (vals nums).length → j ≠ i →
          Int.gcd (valAt (vals nums) i) (valAt (vals nums) j) = 1) ∧
        valAt (vals nums) i ≠ valAt (sortedVals nums) i) →
      r = false := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hpos : 1 ≤ (vals nums).length) (hle : (vals nums).length ≤ 30000)
    (hb : ∀ k, k < (vals nums).length → 1 ≤ valAt (vals nums) k ∧ valAt (vals nums) k ≤ 100000), ∀ r, Aegis.GcdSort.gcd_sort nums = ok r →
      (∃ i, i < (vals nums).length ∧
        (∀ j, j < (vals nums).length → j ≠ i →
          Int.gcd (valAt (vals nums) i) (valAt (vals nums) j) = 1) ∧
        valAt (vals nums) i ≠ valAt (sortedVals nums) i) →
      r = false) := by
  sorry

/-- Let s be the non-decreasing rearrangement of nums. Say i and j (0 <= i, j < n) are gcd-connected if there is m >= 0 and indices a_0, ..., a_m with a_0 = i, a_m = j and gcd(nums[a_t], nums[a_{t+1}]) > 1 for every 0 <= t < m. Whenever the function returns a result r with r = false, there exist an index i with 0 <= i < n and an integer value v such that the number of j with 0 <= j < n that are gcd-connected to i and satisfy nums[j] = v differs from the number of j with 0 <= j < n that are gcd-connected to i and satisfy s[j] = v.
  Preconditions: Let n = len(nums). 1 <= n <= 30000, and for every k with 0 <= k < n, 1 <= nums[k] <= 100000. -/
theorem spec_11 (nums : Slice Std.I64)
    (hpos : 1 ≤ (vals nums).length) (hle : (vals nums).length ≤ 30000)
    (hb : ∀ k, k < (vals nums).length → 1 ≤ valAt (vals nums) k ∧ valAt (vals nums) k ≤ 100000) :
    ∀ r, Aegis.GcdSort.gcd_sort nums = ok r → r = false →
      ∃ (i : ℕ) (v : Int), i < (vals nums).length ∧
        (connValues nums (vals nums) i).count v ≠
          (connValues nums (sortedVals nums) i).count v := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hpos : 1 ≤ (vals nums).length) (hle : (vals nums).length ≤ 30000)
    (hb : ∀ k, k < (vals nums).length → 1 ≤ valAt (vals nums) k ∧ valAt (vals nums) k ≤ 100000), ∀ r, Aegis.GcdSort.gcd_sort nums = ok r → r = false →
      ∃ (i : ℕ) (v : Int), i < (vals nums).length ∧
        (connValues nums (vals nums) i).count v ≠
          (connValues nums (sortedVals nums) i).count v) := by
  sorry

/-- Let s be the non-decreasing rearrangement of nums. Say values u and v (each appearing among nums[0], ..., nums[n-1]) are in the same value-component if u = v or there exist m >= 1 and values w_0, ..., w_m, each appearing among nums[0], ..., nums[n-1], with w_0 = u, w_m = v and gcd(w_t, w_{t+1}) > 1 for every 0 <= t < m. If for every i with 0 <= i < n, nums[i] and s[i] are in the same value-component, then the function returns a result r and r = true.
  Preconditions: Let n = len(nums). 1 <= n <= 30000, and for every k with 0 <= k < n, 1 <= nums[k] <= 100000. -/
theorem spec_12 (nums : Slice Std.I64)
    (hpos : 1 ≤ (vals nums).length) (hle : (vals nums).length ≤ 30000)
    (hb : ∀ k, k < (vals nums).length → 1 ≤ valAt (vals nums) k ∧ valAt (vals nums) k ≤ 100000)
    (hcomp : ∀ i, i < (vals nums).length →
      SameValComponent (vals nums) (valAt (vals nums) i) (valAt (sortedVals nums) i)) :
    ∃ r, Aegis.GcdSort.gcd_sort nums = ok r ∧ r = true := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hpos : 1 ≤ (vals nums).length) (hle : (vals nums).length ≤ 30000)
    (hb : ∀ k, k < (vals nums).length → 1 ≤ valAt (vals nums) k ∧ valAt (vals nums) k ≤ 100000)
    (hcomp : ∀ i, i < (vals nums).length →
      SameValComponent (vals nums) (valAt (vals nums) i) (valAt (sortedVals nums) i)), ∃ r, Aegis.GcdSort.gcd_sort nums = ok r ∧ r = true) := by
  sorry

end AegisSpec.GcdSort
