import Aegis.MinIncrementForUnique.Code.Funs

/-!
# Specifications of `Aegis.MinIncrementForUnique.min_increment_for_unique`

LeetCode problem `minimum-increment-to-make-array-unique`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinIncrementForUnique

def values (nums : Slice Std.I64) : List ℤ := nums.val.map (fun x => x.val)

def InRange (a : List ℤ) : Prop := ∀ v ∈ a, 0 ≤ v ∧ v ≤ 100000

def Valid (a b : List ℤ) : Prop :=
  b.length = a.length ∧
    (∀ (i : ℕ) (hi : i < a.length) (hi' : i < b.length), a.get ⟨i, hi⟩ ≤ b.get ⟨i, hi'⟩) ∧
    b.Nodup

def cost (a b : List ℤ) : ℤ := (List.zipWith (fun x y => y - x) a b).sum

def IsMinCost (a : List ℤ) (r : ℤ) : Prop :=
  (∃ b, Valid a b ∧ cost a b = r) ∧ ∀ b, Valid a b → r ≤ cost a b

def AnswerBound (a : List ℤ) : Prop := ∃ b, Valid a b ∧ cost a b ≤ 2 ^ 31 - 1

def Pre (nums : Slice Std.I64) : Prop :=
  1 ≤ (values nums).length ∧ (values nums).length ≤ 100000 ∧ InRange (values nums) ∧
    AnswerBound (values nums)

def NoDuplicates (a : List ℤ) : Prop :=
  ∀ (i j : ℕ) (hij : i < j) (hj : j < a.length), a.get ⟨i, Nat.lt_trans hij hj⟩ ≠ a.get ⟨j, hj⟩

def count (a : List ℤ) (v : ℤ) : ℕ := (a.filter (fun x => x = v)).length

def dupCostSum (a : List ℤ) : ℤ :=
  ∑ v ∈ a.toFinset, (((count a v) * (count a v - 1)) / 2 : ℕ)

def tri (n : ℕ) : ℤ := ((n * (n - 1)) / 2 : ℕ)

def BoundedIncrements (a b : List ℤ) : Prop :=
  b.length = a.length ∧
    ∀ (i : ℕ) (hi : i < a.length) (hi' : i < b.length),
      0 ≤ b.get ⟨i, hi'⟩ - a.get ⟨i, hi⟩ ∧
        b.get ⟨i, hi'⟩ - a.get ⟨i, hi⟩ ≤ (a.length : ℤ) - 1

def AgreesSomewhere (a b : List ℤ) : Prop :=
  ∃ (k : ℕ) (hk : k < a.length) (hk' : k < b.length), b.get ⟨k, hk'⟩ = a.get ⟨k, hk⟩

def yscanFrom : ℤ → List ℤ → List ℤ
  | _, [] => []
  | prev, x :: xs =>
    let y := max x (prev + 1)
    y :: yscanFrom y xs

def yscan : List ℤ → List ℤ
  | [] => []
  | x :: xs => x :: yscanFrom x xs

def IsPermutationOf (b a : List ℤ) : Prop :=
  ∃ π : Equiv.Perm (Fin a.length),
    b = (List.finRange a.length).map (fun i => a.get ⟨(π i).val, (π i).isLt⟩)

def IsSubMultisetOf (b a : List ℤ) : Prop :=
  ∃ φ : Fin b.length → Fin a.length,
    Function.Injective φ ∧
      b = (List.finRange b.length).map (fun j => a.get ⟨(φ j).val, (φ j).isLt⟩)

def IsShiftOf (other nums : Slice Std.I64) (c : ℤ) : Prop :=
  values other = (values nums).map (fun v => v + c)

def IsInsertOf (other nums : Slice Std.I64) (z : ℤ) : Prop :=
  List.Perm (values other) (z :: values nums)

/-- Let n = len(nums). For a length-n integer list b, call b valid when b[i] >= nums[i] for every i with 0 <= i < n and the values b[0],...,b[n-1] are pairwise distinct. Define cost(b) = sum_{i=0}^{n-1} (b[i] - nums[i]). The function returns a result r, and r is the minimum of cost(b) over all valid b.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000, and for every i with 0 <= i < n, 0 <= nums[i] <= 100000. Also assume the promised 32-bit answer bound: the minimum number of one-step increments needed to make all values of nums pairwise distinct is at most 2^31 - 1. -/
theorem spec_1 (nums : Slice Std.I64)
    (hn1 : 1 ≤ (values nums).length) (hn2 : (values nums).length ≤ 100000)
    (hrange : InRange (values nums)) (hbound : AnswerBound (values nums)) :
    ∃ r : Std.I64,
      Aegis.MinIncrementForUnique.min_increment_for_unique nums = ok r ∧
        IsMinCost (values nums) r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn1 : 1 ≤ (values nums).length) (hn2 : (values nums).length ≤ 100000)
    (hrange : InRange (values nums)) (hbound : AnswerBound (values nums)), ∃ r : Std.I64,
      Aegis.MinIncrementForUnique.min_increment_for_unique nums = ok r ∧
        IsMinCost (values nums) r.val) := by
  sorry

/-- The function returns a result r for every input satisfying the preconditions; it does not fail, panic, or overflow.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000, and for every i with 0 <= i < n, 0 <= nums[i] <= 100000. Also assume the promised 32-bit answer bound: the minimum number of one-step increments needed to make all values of nums pairwise distinct is at most 2^31 - 1. -/
theorem spec_2 (nums : Slice Std.I64)
    (hn1 : 1 ≤ (values nums).length) (hn2 : (values nums).length ≤ 100000)
    (hrange : InRange (values nums)) (hbound : AnswerBound (values nums)) :
    ∃ r : Std.I64, Aegis.MinIncrementForUnique.min_increment_for_unique nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn1 : 1 ≤ (values nums).length) (hn2 : (values nums).length ≤ 100000)
    (hrange : InRange (values nums)) (hbound : AnswerBound (values nums)), ∃ r : Std.I64, Aegis.MinIncrementForUnique.min_increment_for_unique nums = ok r) := by
  sorry

/-- Let c(v) be the number of indices i with 0 <= i < n and nums[i] = v, for integer v; only finitely many c(v) are nonzero. The function returns a result r, and r >= sum over all integers v of c(v)*(c(v)-1)/2.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000, and for every i with 0 <= i < n, 0 <= nums[i] <= 100000. Also assume the promised 32-bit answer bound: the minimum number of one-step increments needed to make all values of nums pairwise distinct is at most 2^31 - 1. -/
theorem spec_3 (nums : Slice Std.I64)
    (hn1 : 1 ≤ (values nums).length) (hn2 : (values nums).length ≤ 100000)
    (hrange : InRange (values nums)) (hbound : AnswerBound (values nums)) :
    ∃ r : Std.I64,
      Aegis.MinIncrementForUnique.min_increment_for_unique nums = ok r ∧
        dupCostSum (values nums) ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn1 : 1 ≤ (values nums).length) (hn2 : (values nums).length ≤ 100000)
    (hrange : InRange (values nums)) (hbound : AnswerBound (values nums)), ∃ r : Std.I64,
      Aegis.MinIncrementForUnique.min_increment_for_unique nums = ok r ∧
        dupCostSum (values nums) ≤ r.val) := by
  sorry

/-- The function returns a result r, and r <= n*(n-1)/2, where n = len(nums).
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000, and for every i with 0 <= i < n, 0 <= nums[i] <= 100000. Also assume the promised 32-bit answer bound: the minimum number of one-step increments needed to make all values of nums pairwise distinct is at most 2^31 - 1. -/
theorem spec_4 (nums : Slice Std.I64)
    (hn1 : 1 ≤ (values nums).length) (hn2 : (values nums).length ≤ 100000)
    (hrange : InRange (values nums)) (hbound : AnswerBound (values nums)) :
    ∃ r : Std.I64,
      Aegis.MinIncrementForUnique.min_increment_for_unique nums = ok r ∧
        r.val ≤ tri (values nums).length := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn1 : 1 ≤ (values nums).length) (hn2 : (values nums).length ≤ 100000)
    (hrange : InRange (values nums)) (hbound : AnswerBound (values nums)), ∃ r : Std.I64,
      Aegis.MinIncrementForUnique.min_increment_for_unique nums = ok r ∧
        r.val ≤ tri (values nums).length) := by
  sorry

/-- The function returns a result r, and r = 0 if and only if nums has no repeated values, i.e. nums[i] != nums[j] for every 0 <= i < j < n.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000, and for every i with 0 <= i < n, 0 <= nums[i] <= 100000. Also assume the promised 32-bit answer bound: the minimum number of one-step increments needed to make all values of nums pairwise distinct is at most 2^31 - 1. -/
theorem spec_5 (nums : Slice Std.I64)
    (hn1 : 1 ≤ (values nums).length) (hn2 : (values nums).length ≤ 100000)
    (hrange : InRange (values nums)) (hbound : AnswerBound (values nums)) :
    ∃ r : Std.I64,
      Aegis.MinIncrementForUnique.min_increment_for_unique nums = ok r ∧
        (r.val = 0 ↔ NoDuplicates (values nums)) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn1 : 1 ≤ (values nums).length) (hn2 : (values nums).length ≤ 100000)
    (hrange : InRange (values nums)) (hbound : AnswerBound (values nums)), ∃ r : Std.I64,
      Aegis.MinIncrementForUnique.min_increment_for_unique nums = ok r ∧
        (r.val = 0 ↔ NoDuplicates (values nums))) := by
  sorry

/-- Under the precondition that all n values are equal to c, the function returns a result r and r = n*(n-1)/2.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000, and for every i with 0 <= i < n, 0 <= nums[i] <= 100000. Also assume the promised 32-bit answer bound: the minimum number of one-step increments needed to make all values of nums pairwise distinct is at most 2^31 - 1. In addition, assume nums[0] = nums[1] = ... = nums[n-1] = c for some integer c. -/
theorem spec_6 (nums : Slice Std.I64)
    (hn1 : 1 ≤ (values nums).length) (hn2 : (values nums).length ≤ 100000)
    (hrange : InRange (values nums)) (hbound : AnswerBound (values nums))
    (hconst : ∃ c : ℤ, ∀ (i : ℕ) (hi : i < (values nums).length),
      (values nums).get ⟨i, hi⟩ = c) :
    ∃ r : Std.I64,
      Aegis.MinIncrementForUnique.min_increment_for_unique nums = ok r ∧
        r.val = tri (values nums).length := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn1 : 1 ≤ (values nums).length) (hn2 : (values nums).length ≤ 100000)
    (hrange : InRange (values nums)) (hbound : AnswerBound (values nums))
    (hconst : ∃ c : ℤ, ∀ (i : ℕ) (hi : i < (values nums).length),
      (values nums).get ⟨i, hi⟩ = c), ∃ r : Std.I64,
      Aegis.MinIncrementForUnique.min_increment_for_unique nums = ok r ∧
        r.val = tri (values nums).length) := by
  sorry

/-- The function returns a result r, and there exists a length-n integer list b such that b[i] >= nums[i] for all 0 <= i < n, the values b[0],...,b[n-1] are pairwise distinct, sum_{i=0}^{n-1}(b[i]-nums[i]) = r, and 0 <= b[i]-nums[i] <= n-1 for every i with 0 <= i < n.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000, and for every i with 0 <= i < n, 0 <= nums[i] <= 100000. Also assume the promised 32-bit answer bound: the minimum number of one-step increments needed to make all values of nums pairwise distinct is at most 2^31 - 1. -/
theorem spec_7 (nums : Slice Std.I64)
    (hn1 : 1 ≤ (values nums).length) (hn2 : (values nums).length ≤ 100000)
    (hrange : InRange (values nums)) (hbound : AnswerBound (values nums)) :
    ∃ r : Std.I64,
      Aegis.MinIncrementForUnique.min_increment_for_unique nums = ok r ∧
        ∃ b : List ℤ,
          Valid (values nums) b ∧ cost (values nums) b = r.val ∧
            BoundedIncrements (values nums) b := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn1 : 1 ≤ (values nums).length) (hn2 : (values nums).length ≤ 100000)
    (hrange : InRange (values nums)) (hbound : AnswerBound (values nums)), ∃ r : Std.I64,
      Aegis.MinIncrementForUnique.min_increment_for_unique nums = ok r ∧
        ∃ b : List ℤ,
          Valid (values nums) b ∧ cost (values nums) b = r.val ∧
            BoundedIncrements (values nums) b) := by
  sorry

/-- The function returns a result r, and there exists a length-n integer list b such that b[i] >= nums[i] for all 0 <= i < n, the values b[0],...,b[n-1] are pairwise distinct, sum_{i=0}^{n-1}(b[i]-nums[i]) = r, and b[k] = nums[k] for at least one index k with 0 <= k < n.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000, and for every i with 0 <= i < n, 0 <= nums[i] <= 100000. Also assume the promised 32-bit answer bound: the minimum number of one-step increments needed to make all values of nums pairwise distinct is at most 2^31 - 1. -/
theorem spec_8 (nums : Slice Std.I64)
    (hn1 : 1 ≤ (values nums).length) (hn2 : (values nums).length ≤ 100000)
    (hrange : InRange (values nums)) (hbound : AnswerBound (values nums)) :
    ∃ r : Std.I64,
      Aegis.MinIncrementForUnique.min_increment_for_unique nums = ok r ∧
        ∃ b : List ℤ,
          Valid (values nums) b ∧ cost (values nums) b = r.val ∧
            AgreesSomewhere (values nums) b := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn1 : 1 ≤ (values nums).length) (hn2 : (values nums).length ≤ 100000)
    (hrange : InRange (values nums)) (hbound : AnswerBound (values nums)), ∃ r : Std.I64,
      Aegis.MinIncrementForUnique.min_increment_for_unique nums = ok r ∧
        ∃ b : List ℤ,
          Valid (values nums) b ∧ cost (values nums) b = r.val ∧
            AgreesSomewhere (values nums) b) := by
  sorry

/-- For every slice other with len(other) = n for which there is a bijection pi on {0,...,n-1} such that other[i] = nums[pi(i)] for all i with 0 <= i < n, if other satisfies the preconditions then the function returns results r for nums and r_other for other, and r_other = r.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000, and for every i with 0 <= i < n, 0 <= nums[i] <= 100000. Also assume the promised 32-bit answer bound: the minimum number of one-step increments needed to make all values of nums pairwise distinct is at most 2^31 - 1. For any other slice mentioned below, assume it also satisfies the same constraints and answer bound. -/
theorem spec_9 (nums other : Slice Std.I64)
    (hn1 : 1 ≤ (values nums).length) (hn2 : (values nums).length ≤ 100000)
    (hrange : InRange (values nums)) (hbound : AnswerBound (values nums))
    (hpre_other : Pre other)
    (hperm : IsPermutationOf (values other) (values nums)) :
    ∃ r r_other : Std.I64,
      Aegis.MinIncrementForUnique.min_increment_for_unique nums = ok r ∧
        Aegis.MinIncrementForUnique.min_increment_for_unique other = ok r_other ∧
          r_other.val = r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums other : Slice Std.I64)
    (hn1 : 1 ≤ (values nums).length) (hn2 : (values nums).length ≤ 100000)
    (hrange : InRange (values nums)) (hbound : AnswerBound (values nums))
    (hpre_other : Pre other)
    (hperm : IsPermutationOf (values other) (values nums)), ∃ r r_other : Std.I64,
      Aegis.MinIncrementForUnique.min_increment_for_unique nums = ok r ∧
        Aegis.MinIncrementForUnique.min_increment_for_unique other = ok r_other ∧
          r_other.val = r.val) := by
  sorry

/-- For every integer c such that the length-n slice shifted with shifted[i] = nums[i] + c for all 0 <= i < n satisfies the preconditions, the function returns results r for nums and r_shifted for shifted, and r_shifted = r.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000, and for every i with 0 <= i < n, 0 <= nums[i] <= 100000. Also assume the promised 32-bit answer bound: the minimum number of one-step increments needed to make all values of nums pairwise distinct is at most 2^31 - 1. For the shifted slice mentioned below, assume it also satisfies the same constraints and answer bound. -/
theorem spec_10 (nums shifted : Slice Std.I64) (c : ℤ)
    (hn1 : 1 ≤ (values nums).length) (hn2 : (values nums).length ≤ 100000)
    (hrange : InRange (values nums)) (hbound : AnswerBound (values nums))
    (hpre_shifted : Pre shifted)
    (hshift : IsShiftOf shifted nums c) :
    ∃ r r_shifted : Std.I64,
      Aegis.MinIncrementForUnique.min_increment_for_unique nums = ok r ∧
        Aegis.MinIncrementForUnique.min_increment_for_unique shifted = ok r_shifted ∧
          r_shifted.val = r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums shifted : Slice Std.I64) (c : ℤ)
    (hn1 : 1 ≤ (values nums).length) (hn2 : (values nums).length ≤ 100000)
    (hrange : InRange (values nums)) (hbound : AnswerBound (values nums))
    (hpre_shifted : Pre shifted)
    (hshift : IsShiftOf shifted nums c), ∃ r r_shifted : Std.I64,
      Aegis.MinIncrementForUnique.min_increment_for_unique nums = ok r ∧
        Aegis.MinIncrementForUnique.min_increment_for_unique shifted = ok r_shifted ∧
          r_shifted.val = r.val) := by
  sorry

/-- Let other be any slice of length n+1 whose multiset of values is the multiset of nums plus one extra value z. If z < min_{0 <= i < n} nums[i] and other satisfies the preconditions, then the function returns results r for nums and r_other for other, and r_other = r.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000, and for every i with 0 <= i < n, 0 <= nums[i] <= 100000. Also assume the promised 32-bit answer bound: the minimum number of one-step increments needed to make all values of nums pairwise distinct is at most 2^31 - 1. For any other slice mentioned below, assume it also satisfies the same constraints and answer bound. -/
theorem spec_11 (nums other : Slice Std.I64) (z : ℤ)
    (hn1 : 1 ≤ (values nums).length) (hn2 : (values nums).length ≤ 100000)
    (hrange : InRange (values nums)) (hbound : AnswerBound (values nums))
    (hpre_other : Pre other)
    (hins : IsInsertOf other nums z)
    (hmin : ∀ v ∈ values nums, z < v) :
    ∃ r r_other : Std.I64,
      Aegis.MinIncrementForUnique.min_increment_for_unique nums = ok r ∧
        Aegis.MinIncrementForUnique.min_increment_for_unique other = ok r_other ∧
          r_other.val = r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums other : Slice Std.I64) (z : ℤ)
    (hn1 : 1 ≤ (values nums).length) (hn2 : (values nums).length ≤ 100000)
    (hrange : InRange (values nums)) (hbound : AnswerBound (values nums))
    (hpre_other : Pre other)
    (hins : IsInsertOf other nums z)
    (hmin : ∀ v ∈ values nums, z < v), ∃ r r_other : Std.I64,
      Aegis.MinIncrementForUnique.min_increment_for_unique nums = ok r ∧
        Aegis.MinIncrementForUnique.min_increment_for_unique other = ok r_other ∧
          r_other.val = r.val) := by
  sorry

/-- Let other be any slice of length n+1 whose multiset of values is the multiset of nums plus one extra value z. If z >= max_{0 <= i < n} nums[i] + n and other satisfies the preconditions, then the function returns results r for nums and r_other for other, and r_other = r.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000, and for every i with 0 <= i < n, 0 <= nums[i] <= 100000. Also assume the promised 32-bit answer bound: the minimum number of one-step increments needed to make all values of nums pairwise distinct is at most 2^31 - 1. For any other slice mentioned below, assume it also satisfies the same constraints and answer bound. -/
theorem spec_12 (nums other : Slice Std.I64) (z : ℤ)
    (hn1 : 1 ≤ (values nums).length) (hn2 : (values nums).length ≤ 100000)
    (hrange : InRange (values nums)) (hbound : AnswerBound (values nums))
    (hpre_other : Pre other)
    (hins : IsInsertOf other nums z)
    (hmax : ∀ v ∈ values nums, v + (values nums).length ≤ z) :
    ∃ r r_other : Std.I64,
      Aegis.MinIncrementForUnique.min_increment_for_unique nums = ok r ∧
        Aegis.MinIncrementForUnique.min_increment_for_unique other = ok r_other ∧
          r_other.val = r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums other : Slice Std.I64) (z : ℤ)
    (hn1 : 1 ≤ (values nums).length) (hn2 : (values nums).length ≤ 100000)
    (hrange : InRange (values nums)) (hbound : AnswerBound (values nums))
    (hpre_other : Pre other)
    (hins : IsInsertOf other nums z)
    (hmax : ∀ v ∈ values nums, v + (values nums).length ≤ z), ∃ r r_other : Std.I64,
      Aegis.MinIncrementForUnique.min_increment_for_unique nums = ok r ∧
        Aegis.MinIncrementForUnique.min_increment_for_unique other = ok r_other ∧
          r_other.val = r.val) := by
  sorry

/-- Let a be a nondecreasing rearrangement of nums, so a[0] <= a[1] <= ... <= a[n-1]. Define y[0] = a[0], and for 1 <= i < n define y[i] = max(a[i], y[i-1] + 1). Then the function returns a result r, and r = sum_{i=0}^{n-1} (y[i] - a[i]).
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000, and for every i with 0 <= i < n, 0 <= nums[i] <= 100000. Also assume the promised 32-bit answer bound. -/
theorem spec_13 (nums : Slice Std.I64) (a : List ℤ)
    (hn1 : 1 ≤ (values nums).length) (hn2 : (values nums).length ≤ 100000)
    (hrange : InRange (values nums)) (hbound : AnswerBound (values nums))
    (hperm : List.Perm a (values nums)) (hsorted : a.Pairwise (· ≤ ·)) :
    ∃ r : Std.I64,
      Aegis.MinIncrementForUnique.min_increment_for_unique nums = ok r ∧
        r.val = cost a (yscan a) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums : Slice Std.I64) (a : List ℤ)
    (hn1 : 1 ≤ (values nums).length) (hn2 : (values nums).length ≤ 100000)
    (hrange : InRange (values nums)) (hbound : AnswerBound (values nums))
    (hperm : List.Perm a (values nums)) (hsorted : a.Pairwise (· ≤ ·)), ∃ r : Std.I64,
      Aegis.MinIncrementForUnique.min_increment_for_unique nums = ok r ∧
        r.val = cost a (yscan a)) := by
  sorry

/-- The function returns results r for nums and r_sub for sub, and r_sub <= r.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000, and for every i with 0 <= i < n, 0 <= nums[i] <= 100000. Also assume the promised 32-bit answer bound. Let sub be any slice of length m with 1 <= m <= n for which there is an injection phi from {0,...,m-1} to {0,...,n-1} such that sub[j] = nums[phi(j)] for every 0 <= j < m. Assume sub also satisfies the same constraints and answer bound. -/
theorem spec_14 (nums sub : Slice Std.I64)
    (hn1 : 1 ≤ (values nums).length) (hn2 : (values nums).length ≤ 100000)
    (hrange : InRange (values nums)) (hbound : AnswerBound (values nums))
    (hpre_sub : Pre sub) (hmn : (values sub).length ≤ (values nums).length)
    (hsub : IsSubMultisetOf (values sub) (values nums)) :
    ∃ r r_sub : Std.I64,
      Aegis.MinIncrementForUnique.min_increment_for_unique nums = ok r ∧
        Aegis.MinIncrementForUnique.min_increment_for_unique sub = ok r_sub ∧
          r_sub.val ≤ r.val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (nums sub : Slice Std.I64)
    (hn1 : 1 ≤ (values nums).length) (hn2 : (values nums).length ≤ 100000)
    (hrange : InRange (values nums)) (hbound : AnswerBound (values nums))
    (hpre_sub : Pre sub) (hmn : (values sub).length ≤ (values nums).length)
    (hsub : IsSubMultisetOf (values sub) (values nums)), ∃ r r_sub : Std.I64,
      Aegis.MinIncrementForUnique.min_increment_for_unique nums = ok r ∧
        Aegis.MinIncrementForUnique.min_increment_for_unique sub = ok r_sub ∧
          r_sub.val ≤ r.val) := by
  sorry

end AegisSpec.MinIncrementForUnique
