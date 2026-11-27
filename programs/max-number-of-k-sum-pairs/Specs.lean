import Aegis.MaxOperations.Code.Funs

/-!
# Specifications of `Aegis.MaxOperations.max_operations`

LeetCode problem `max-number-of-k-sum-pairs`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxOperations

def len (nums : Slice Std.I64) : ℕ := nums.val.length

def vals (nums : Slice Std.I64) : List ℤ := nums.val.map (fun x => x.val)

def elemAt (nums : Slice Std.I64) (i : ℕ) : Option ℤ := (nums.val[i]?).map (fun x => x.val)

def LenRange (nums : Slice Std.I64) : Prop := 1 ≤ len nums ∧ len nums ≤ 100000

def ElemRange (nums : Slice Std.I64) : Prop :=
  ∀ i : ℕ, i < len nums → ∃ v : ℤ, elemAt nums i = some v ∧ 1 ≤ v ∧ v ≤ 1000000000

def KRange (k : Std.I64) : Prop := 1 ≤ k.val ∧ k.val ≤ 1000000000

def cnt (nums : Slice Std.I64) (v : ℤ) : ℕ :=
  ((Finset.range (len nums)).filter (fun i => elemAt nums i = some v)).card

def Occurs (nums : Slice Std.I64) (v : ℤ) : Prop := 0 < cnt nums v

instance decidableOccurs (nums : Slice Std.I64) (v : ℤ) : Decidable (Occurs nums v) :=
  decidable_of_iff (0 < cnt nums v) Iff.rfl

def PairwiseDisjointPairs (P : Finset (ℕ × ℕ)) : Prop :=
  ∀ p ∈ P, ∀ q ∈ P, p ≠ q → Disjoint ({p.1, p.2} : Finset ℕ) {q.1, q.2}

def used (P : Finset (ℕ × ℕ)) : Finset ℕ := P.biUnion (fun p => ({p.1, p.2} : Finset ℕ))

def IsKSumPair (nums : Slice Std.I64) (k : ℤ) (p : ℕ × ℕ) : Prop :=
  p.1 < p.2 ∧ ∃ a b : ℤ, elemAt nums p.1 = some a ∧ elemAt nums p.2 = some b ∧ a + b = k

def IsPairSet (nums : Slice Std.I64) (k : ℤ) (P : Finset (ℕ × ℕ)) : Prop :=
  PairwiseDisjointPairs P ∧ ∀ p ∈ P, IsKSumPair nums k p

def pairVals (nums : Slice Std.I64) (p : ℕ × ℕ) : Option (ℤ × ℤ) :=
  match elemAt nums p.1, elemAt nums p.2 with
  | some a, some b => some (a, b)
  | _, _ => none

def countValPairs (nums : Slice Std.I64) (P : Finset (ℕ × ℕ)) (v w : ℤ) : ℕ :=
  (P.filter (fun p => pairVals nums p = some (v, w) ∨ pairVals nums p = some (w, v))).card

/-- The function returns a result r, and r is the maximum cardinality of a set P of unordered pairs of indices such that: (a) every pair {i,j} in P satisfies 0 <= i < j < len(nums) and nums[i] + nums[j] = k; (b) the pairs in P are pairwise disjoint, i.e., no index occurs in two different pairs of P. Formally, r = max { |P| : P is such a set }.
  Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 1 <= k <= 1000000000. -/
theorem spec_1 (nums : Slice Std.I64) (k : Std.I64)
    (hlen : LenRange nums) (hval : ElemRange nums) (hk : KRange k) :
    ∃ r : Std.I64, Aegis.MaxOperations.max_operations nums k = ok r ∧
      ∃ P : Finset (ℕ × ℕ), IsPairSet nums k.val P ∧ (P.card : ℤ) = r.val ∧
        ∀ Q : Finset (ℕ × ℕ), IsPairSet nums k.val Q → Q.card ≤ P.card := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen : LenRange nums) (hval : ElemRange nums) (hk : KRange k), ∃ r : Std.I64, Aegis.MaxOperations.max_operations nums k = ok r ∧
      ∃ P : Finset (ℕ × ℕ), IsPairSet nums k.val P ∧ (P.card : ℤ) = r.val ∧
        ∀ Q : Finset (ℕ × ℕ), IsPairSet nums k.val Q → Q.card ≤ P.card) := by
  sorry

/-- The function returns a result r and 0 <= r <= len(nums) / 2, where / denotes integer division (floor).
  Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 1 <= k <= 1000000000. -/
theorem spec_2 (nums : Slice Std.I64) (k : Std.I64)
    (hlen : LenRange nums) (hval : ElemRange nums) (hk : KRange k) :
    ∃ r : Std.I64, Aegis.MaxOperations.max_operations nums k = ok r ∧
      0 ≤ r.val ∧ r.val ≤ ((len nums / 2 : ℕ) : ℤ) := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen : LenRange nums) (hval : ElemRange nums) (hk : KRange k), ∃ r : Std.I64, Aegis.MaxOperations.max_operations nums k = ok r ∧
      0 ≤ r.val ∧ r.val ≤ ((len nums / 2 : ℕ) : ℤ)) := by
  sorry

/-- The function returns a result r and there exists a set P of r pairwise disjoint unordered pairs of indices {i,j} such that 0 <= i < j < len(nums) and nums[i] + nums[j] = k.
  Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 1 <= k <= 1000000000. -/
theorem spec_3 (nums : Slice Std.I64) (k : Std.I64)
    (hlen : LenRange nums) (hval : ElemRange nums) (hk : KRange k) :
    ∃ r : Std.I64, Aegis.MaxOperations.max_operations nums k = ok r ∧
      ∃ P : Finset (ℕ × ℕ), IsPairSet nums k.val P ∧ (P.card : ℤ) = r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen : LenRange nums) (hval : ElemRange nums) (hk : KRange k), ∃ r : Std.I64, Aegis.MaxOperations.max_operations nums k = ok r ∧
      ∃ P : Finset (ℕ × ℕ), IsPairSet nums k.val P ∧ (P.card : ℤ) = r.val) := by
  sorry

/-- Whenever the function returns a result r, for every set P of pairwise disjoint unordered pairs of indices {i,j} with 0 <= i < j < len(nums) and nums[i] + nums[j] = k, we have |P| <= r.
  Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 1 <= k <= 1000000000. -/
theorem spec_4 (nums : Slice Std.I64) (k : Std.I64)
    (hlen : LenRange nums) (hval : ElemRange nums) (hk : KRange k) :
    ∀ r : Std.I64, Aegis.MaxOperations.max_operations nums k = ok r →
      ∀ P : Finset (ℕ × ℕ), IsPairSet nums k.val P → (P.card : ℤ) ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen : LenRange nums) (hval : ElemRange nums) (hk : KRange k), ∀ r : Std.I64, Aegis.MaxOperations.max_operations nums k = ok r →
      ∀ P : Finset (ℕ × ℕ), IsPairSet nums k.val P → (P.card : ℤ) ≤ r.val) := by
  sorry

/-- The function returns a result r and, letting cnt(v) denote the number of indices i with 0 <= i < len(nums) and nums[i] = v, r = (sum over all integers v with v < k - v of min(cnt(v), cnt(k - v))) + (if k is even then floor(cnt(k/2) / 2) else 0).
  Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 1 <= k <= 1000000000. -/
theorem spec_5 (nums : Slice Std.I64) (k : Std.I64)
    (hlen : LenRange nums) (hval : ElemRange nums) (hk : KRange k) :
    ∃ r : Std.I64, Aegis.MaxOperations.max_operations nums k = ok r ∧
      r.val = (∑ v ∈ (Finset.range (k.val.toNat + 1)).filter
              (fun v : ℕ => 1 ≤ v ∧ (v : ℤ) < k.val - (v : ℤ)),
            ((min (cnt nums (v : ℤ)) (cnt nums (k.val - (v : ℤ))) : ℕ) : ℤ))
          + (if k.val % 2 = 0 then ((cnt nums (k.val / 2) / 2 : ℕ) : ℤ) else 0) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen : LenRange nums) (hval : ElemRange nums) (hk : KRange k), ∃ r : Std.I64, Aegis.MaxOperations.max_operations nums k = ok r ∧
      r.val = (∑ v ∈ (Finset.range (k.val.toNat + 1)).filter
              (fun v : ℕ => 1 ≤ v ∧ (v : ℤ) < k.val - (v : ℤ)),
            ((min (cnt nums (v : ℤ)) (cnt nums (k.val - (v : ℤ))) : ℕ) : ℤ))
          + (if k.val % 2 = 0 then ((cnt nums (k.val / 2) / 2 : ℕ) : ℤ) else 0)) := by
  sorry

/-- The function returns a result r; it does not fail (no arithmetic overflow, out-of-bounds access, or panic).
  Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 1 <= k <= 1000000000. -/
theorem spec_6 (nums : Slice Std.I64) (k : Std.I64)
    (hlen : LenRange nums) (hval : ElemRange nums) (hk : KRange k) :
    ∃ r : Std.I64, Aegis.MaxOperations.max_operations nums k = ok r := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen : LenRange nums) (hval : ElemRange nums) (hk : KRange k), ∃ r : Std.I64, Aegis.MaxOperations.max_operations nums k = ok r) := by
  sorry

/-- The function returns a result r, and r = 0 if and only if there do not exist indices i,j with 0 <= i < j < len(nums) and nums[i] + nums[j] = k.
  Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 1 <= k <= 1000000000. -/
theorem spec_7 (nums : Slice Std.I64) (k : Std.I64)
    (hlen : LenRange nums) (hval : ElemRange nums) (hk : KRange k) :
    ∃ r : Std.I64, Aegis.MaxOperations.max_operations nums k = ok r ∧
      (r.val = 0 ↔ ¬ ∃ i j : ℕ, i < j ∧ j < len nums ∧
        ∃ a b : ℤ, elemAt nums i = some a ∧ elemAt nums j = some b ∧ a + b = k.val) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen : LenRange nums) (hval : ElemRange nums) (hk : KRange k), ∃ r : Std.I64, Aegis.MaxOperations.max_operations nums k = ok r ∧
      (r.val = 0 ↔ ¬ ∃ i j : ℕ, i < j ∧ j < len nums ∧
        ∃ a b : ℤ, elemAt nums i = some a ∧ elemAt nums j = some b ∧ a + b = k.val)) := by
  sorry

/-- The function returns a result r and r = 0.
  Preconditions: len(nums) = 1; 1 <= nums[0] <= 1000000000; 1 <= k <= 1000000000. -/
theorem spec_8 (nums : Slice Std.I64) (k : Std.I64)
    (hlen : len nums = 1)
    (hval : ∃ v : ℤ, elemAt nums 0 = some v ∧ 1 ≤ v ∧ v ≤ 1000000000)
    (hk : KRange k) :
    ∃ r : Std.I64, Aegis.MaxOperations.max_operations nums k = ok r ∧ r.val = 0 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen : len nums = 1)
    (hval : ∃ v : ℤ, elemAt nums 0 = some v ∧ 1 ≤ v ∧ v ≤ 1000000000)
    (hk : KRange k), ∃ r : Std.I64, Aegis.MaxOperations.max_operations nums k = ok r ∧ r.val = 0) := by
  sorry

/-- The function returns a result r and r = len(nums) / 2, where / denotes integer division (floor).
  Preconditions: k is even; let h = k/2; 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), nums[i] = h; 1 <= k <= 1000000000. -/
theorem spec_9 (nums : Slice Std.I64) (k : Std.I64)
    (hk_even : k.val % 2 = 0) (hlen : LenRange nums)
    (hval : ∀ i : ℕ, i < len nums → ∀ v : ℤ, elemAt nums i = some v → v = k.val / 2)
    (hk : KRange k) :
    ∃ r : Std.I64, Aegis.MaxOperations.max_operations nums k = ok r ∧
      r.val = ((len nums / 2 : ℕ) : ℤ) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hk_even : k.val % 2 = 0) (hlen : LenRange nums)
    (hval : ∀ i : ℕ, i < len nums → ∀ v : ℤ, elemAt nums i = some v → v = k.val / 2)
    (hk : KRange k), ∃ r : Std.I64, Aegis.MaxOperations.max_operations nums k = ok r ∧
      r.val = ((len nums / 2 : ℕ) : ℤ)) := by
  sorry

/-- The function returns a result r and r equals the number of integers v such that v < k - v and there exist indices i,j with nums[i] = v and nums[j] = k - v.
  Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; for every i,j with 0 <= i < j < len(nums), nums[i] != nums[j]; 1 <= k <= 1000000000. -/
theorem spec_10 (nums : Slice Std.I64) (k : Std.I64)
    (hlen : LenRange nums) (hval : ElemRange nums) (hk : KRange k)
    (hdistinct : ∀ i j : ℕ, i < j → j < len nums → ∀ a b : ℤ,
      elemAt nums i = some a → elemAt nums j = some b → a ≠ b) :
    ∃ r : Std.I64, Aegis.MaxOperations.max_operations nums k = ok r ∧
      r.val = (((vals nums).toFinset.filter
              (fun v => v < k.val - v ∧ Occurs nums (k.val - v))).card : ℤ) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen : LenRange nums) (hval : ElemRange nums) (hk : KRange k)
    (hdistinct : ∀ i j : ℕ, i < j → j < len nums → ∀ a b : ℤ,
      elemAt nums i = some a → elemAt nums j = some b → a ≠ b), ∃ r : Std.I64, Aegis.MaxOperations.max_operations nums k = ok r ∧
      r.val = (((vals nums).toFinset.filter
              (fun v => v < k.val - v ∧ Occurs nums (k.val - v))).card : ℤ)) := by
  sorry

/-- If max_operations(nums, k) returns r and max_operations(nums', k) returns r', then r = r'.
  Preconditions: nums and nums' are slices of i64; 1 <= len(nums) <= 100000; len(nums') = len(nums); for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; for every integer v, the number of indices i with nums'[i] = v equals the number with nums[i] = v; 1 <= k <= 1000000000. -/
theorem spec_11 (nums nums' : Slice Std.I64) (k : Std.I64)
    (hlen : LenRange nums) (hlen' : len nums' = len nums) (hval : ElemRange nums)
    (hc : ∀ v : ℤ, cnt nums' v = cnt nums v) (hk : KRange k) :
    ∀ r r' : Std.I64, Aegis.MaxOperations.max_operations nums k = ok r →
      Aegis.MaxOperations.max_operations nums' k = ok r' → r.val = r'.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (k : Std.I64)
    (hlen : LenRange nums) (hlen' : len nums' = len nums) (hval : ElemRange nums)
    (hc : ∀ v : ℤ, cnt nums' v = cnt nums v) (hk : KRange k), ∀ r r' : Std.I64, Aegis.MaxOperations.max_operations nums k = ok r →
      Aegis.MaxOperations.max_operations nums' k = ok r' → r.val = r'.val) := by
  sorry

/-- If max_operations(nums, k) returns r and max_operations(nums', k) returns r', then r <= r'.
  Preconditions: nums and nums' are slices of i64; 1 <= len(nums) < 100000; len(nums') = len(nums) + 1; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; there exists x with 1 <= x <= 1000000000 such that the multiset of nums' equals the multiset of nums plus one occurrence of x; 1 <= k <= 1000000000. -/
theorem spec_12 (nums nums' : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ len nums ∧ len nums < 100000) (hlen' : len nums' = len nums + 1)
    (hval : ElemRange nums)
    (hmult : ∃ x : ℤ, 1 ≤ x ∧ x ≤ 1000000000 ∧ (vals nums').Perm (x :: vals nums))
    (hk : KRange k) :
    ∀ r r' : Std.I64, Aegis.MaxOperations.max_operations nums k = ok r →
      Aegis.MaxOperations.max_operations nums' k = ok r' → r.val ≤ r'.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ len nums ∧ len nums < 100000) (hlen' : len nums' = len nums + 1)
    (hval : ElemRange nums)
    (hmult : ∃ x : ℤ, 1 ≤ x ∧ x ≤ 1000000000 ∧ (vals nums').Perm (x :: vals nums))
    (hk : KRange k), ∀ r r' : Std.I64, Aegis.MaxOperations.max_operations nums k = ok r →
      Aegis.MaxOperations.max_operations nums' k = ok r' → r.val ≤ r'.val) := by
  sorry

/-- The function returns a result r and there exists a set P of r pairwise disjoint k-sum pairs (each pair {i,j} has 0 <= i < j < len(nums) and nums[i] + nums[j] = k) such that, letting used(P) be the set of all indices occurring in pairs of P, for every i,j with 0 <= i < j < len(nums), if i is not in used(P) and j is not in used(P), then nums[i] + nums[j] != k.
  Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 1 <= k <= 1000000000. -/
theorem spec_13 (nums : Slice Std.I64) (k : Std.I64)
    (hlen : LenRange nums) (hval : ElemRange nums) (hk : KRange k) :
    ∃ r : Std.I64, Aegis.MaxOperations.max_operations nums k = ok r ∧
      ∃ P : Finset (ℕ × ℕ), IsPairSet nums k.val P ∧ (P.card : ℤ) = r.val ∧
        ∀ i j : ℕ, i < j → j < len nums → i ∉ used P → j ∉ used P →
          ∀ a b : ℤ, elemAt nums i = some a → elemAt nums j = some b → a + b ≠ k.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen : LenRange nums) (hval : ElemRange nums) (hk : KRange k), ∃ r : Std.I64, Aegis.MaxOperations.max_operations nums k = ok r ∧
      ∃ P : Finset (ℕ × ℕ), IsPairSet nums k.val P ∧ (P.card : ℤ) = r.val ∧
        ∀ i j : ℕ, i < j → j < len nums → i ∉ used P → j ∉ used P →
          ∀ a b : ℤ, elemAt nums i = some a → elemAt nums j = some b → a + b ≠ k.val) := by
  sorry

/-- The function returns a result r, and for every set P of r pairwise disjoint unordered pairs of indices {i,j} with 0 <= i < j < len(nums) and nums[i] + nums[j] = k, letting cnt(v) be the number of indices i with nums[i] = v, the following hold: (a) for every integer v with v < k - v, P contains exactly min(cnt(v), cnt(k - v)) pairs whose two values are v and k - v; (b) if k is even, P contains exactly floor(cnt(k/2) / 2) pairs both of whose values are k/2.
  Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 1 <= k <= 1000000000. -/
theorem spec_14 (nums : Slice Std.I64) (k : Std.I64)
    (hlen : LenRange nums) (hval : ElemRange nums) (hk : KRange k) :
    ∃ r : Std.I64, Aegis.MaxOperations.max_operations nums k = ok r ∧
      ∀ P : Finset (ℕ × ℕ), IsPairSet nums k.val P → (P.card : ℤ) = r.val →
        (∀ v : ℤ, v < k.val - v →
            countValPairs nums P v (k.val - v) = min (cnt nums v) (cnt nums (k.val - v)))
        ∧ (k.val % 2 = 0 →
            countValPairs nums P (k.val / 2) (k.val / 2) = cnt nums (k.val / 2) / 2) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen : LenRange nums) (hval : ElemRange nums) (hk : KRange k), ∃ r : Std.I64, Aegis.MaxOperations.max_operations nums k = ok r ∧
      ∀ P : Finset (ℕ × ℕ), IsPairSet nums k.val P → (P.card : ℤ) = r.val →
        (∀ v : ℤ, v < k.val - v →
            countValPairs nums P v (k.val - v) = min (cnt nums v) (cnt nums (k.val - v)))
        ∧ (k.val % 2 = 0 →
            countValPairs nums P (k.val / 2) (k.val / 2) = cnt nums (k.val / 2) / 2)) := by
  sorry

/-- If max_operations(nums, k) returns r and max_operations(nums', k) returns r', then r' <= r + 1.
  Preconditions: nums and nums' are slices of i64; 1 <= len(nums) < 100000; len(nums') = len(nums) + 1; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; there exists x with 1 <= x <= 1000000000 such that the multiset of nums' equals the multiset of nums plus one occurrence of x; 1 <= k <= 1000000000. -/
theorem spec_15 (nums nums' : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ len nums ∧ len nums < 100000) (hlen' : len nums' = len nums + 1)
    (hval : ElemRange nums)
    (hmult : ∃ x : ℤ, 1 ≤ x ∧ x ≤ 1000000000 ∧ (vals nums').Perm (x :: vals nums))
    (hk : KRange k) :
    ∀ r r' : Std.I64, Aegis.MaxOperations.max_operations nums k = ok r →
      Aegis.MaxOperations.max_operations nums' k = ok r' → r'.val ≤ r.val + 1 := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ len nums ∧ len nums < 100000) (hlen' : len nums' = len nums + 1)
    (hval : ElemRange nums)
    (hmult : ∃ x : ℤ, 1 ≤ x ∧ x ≤ 1000000000 ∧ (vals nums').Perm (x :: vals nums))
    (hk : KRange k), ∀ r r' : Std.I64, Aegis.MaxOperations.max_operations nums k = ok r →
      Aegis.MaxOperations.max_operations nums' k = ok r' → r'.val ≤ r.val + 1) := by
  sorry

end AegisSpec.MaxOperations
