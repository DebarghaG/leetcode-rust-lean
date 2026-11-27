import Aegis.SortJumbled.Code.Funs

/-!
# Specifications of `Aegis.SortJumbled.sort_jumbled`

LeetCode problem `sort-the-jumbled-numbers`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.SortJumbled

def decimalDigits (n : Nat) : List Nat :=
  if n < 10 then [n] else n % 10 :: decimalDigits (n / 10)
termination_by n
decreasing_by omega

def digitImage (mapping : List Int) (d : Nat) : Int := mapping.getD d 0

def mapval (mapping : List Int) (n : Nat) : Int :=
  ((decimalDigits n).mapIdx fun j d => digitImage mapping d * 10 ^ j).sum

def mapVals (mapping : List Std.I64) : List Int := mapping.map fun x => x.val

def valsOf (l : List Std.I64) : List Int := l.map fun x => x.val

def entryVal (l : List Std.I64) (i : Nat) : Int := (l.getD i 0#i64).val

def key (mapping : List Std.I64) (x : Std.I64) : Int := mapval (mapVals mapping) x.val.toNat

def keyAt (mapping l : List Std.I64) (i : Nat) : Int := key mapping (l.getD i 0#i64)

def indicesWithKey (mapping : List Std.I64) (nums : List Std.I64) (v : Int) : List Nat :=
  (List.range nums.length).filter fun i => keyAt mapping nums i = v

def entriesWithKey (mapping : List Std.I64) (nums : List Std.I64) (v : Int) : List Int :=
  (indicesWithKey mapping nums v).map fun i => entryVal nums i

def countValues (l : List Std.I64) (x : Int) : Nat := (l.filter fun y => y.val = x).length

def countKeys (mapping : List Std.I64) (l : List Std.I64) (v : Int) : Nat :=
  (l.filter fun y => key mapping y = v).length

def countKeysLe (mapping : List Std.I64) (l : List Std.I64) (t : Int) : Nat :=
  (l.filter fun y => key mapping y ≤ t).length

def EntriesFrom (r nums : List Std.I64) : Prop :=
  ∀ p, p < r.length → r.getD p 0#i64 ∈ nums

def EntriesBounded (r : List Std.I64) : Prop :=
  ∀ p, p < r.length → 0 ≤ entryVal r p ∧ entryVal r p < 10 ^ 9

def IsDigitPermutation (mapping : List Std.I64) : Prop :=
  mapping.length = 10 ∧
    (∀ i, i < 10 → 0 ≤ entryVal mapping i ∧ entryVal mapping i ≤ 9) ∧
      mapping.Nodup

def IsValidInput (nums : List Std.I64) : Prop :=
  1 ≤ nums.length ∧ nums.length ≤ 30000 ∧
    ∀ i, i < nums.length → 0 ≤ entryVal nums i ∧ entryVal nums i < 10 ^ 9

/-- Define mapval(n) for a nonnegative integer n as follows: write n in decimal without leading zeros, except write 0 as the single digit 0; if the digits from most significant to least significant are d_k,...,d_0, then mapval(n) = sum_{j=0}^{k} mapping[d_j] * 10^j. Whenever the function returns a result r, let L = len(nums); for each integer v, let I_v be the increasing list of indices i with 0 <= i < L and mapval(nums[i]) = v; let V be the increasing list of all v for which I_v is nonempty. Then len(r) = L and r is exactly the concatenation, over v in V, of the lists [nums[i] for i in I_v].
  Preconditions: len(mapping) = 10; for every i with 0 <= i < 10, 0 <= mapping[i] <= 9; mapping[0],...,mapping[9] are pairwise distinct; let L = len(nums); 1 <= L <= 30000; for every i with 0 <= i < L, 0 <= nums[i] < 10^9. -/
theorem spec_1 (mapping nums : Slice Std.I64)
    (hmap : IsDigitPermutation mapping.val) (hnums : IsValidInput nums.val) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.SortJumbled.sort_jumbled mapping nums = ok r →
        r.val.length = nums.val.length ∧
          ∃ V : List Int,
            V.Pairwise (· < ·) ∧
              (∀ v : Int, v ∈ V ↔ entriesWithKey mapping.val nums.val v ≠ []) ∧
                valsOf r.val = V.flatMap fun v => entriesWithKey mapping.val nums.val v := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (mapping nums : Slice Std.I64)
    (hmap : IsDigitPermutation mapping.val) (hnums : IsValidInput nums.val), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.SortJumbled.sort_jumbled mapping nums = ok r →
        r.val.length = nums.val.length ∧
          ∃ V : List Int,
            V.Pairwise (· < ·) ∧
              (∀ v : Int, v ∈ V ↔ entriesWithKey mapping.val nums.val v ≠ []) ∧
                valsOf r.val = V.flatMap fun v => entriesWithKey mapping.val nums.val v) := by
  sorry

/-- For every mapping and nums satisfying the preconditions, the function returns a result r (the Result is successful; it does not panic, overflow, go out of bounds, or otherwise fail).
  Preconditions: len(mapping) = 10; for every i with 0 <= i < 10, 0 <= mapping[i] <= 9; mapping[0],...,mapping[9] are pairwise distinct; let L = len(nums); 1 <= L <= 30000; for every i with 0 <= i < L, 0 <= nums[i] < 10^9. -/
theorem spec_2 (mapping nums : Slice Std.I64)
    (hmap : IsDigitPermutation mapping.val) (hnums : IsValidInput nums.val) :
    ∃ r : alloc.vec.Vec Std.I64, Aegis.SortJumbled.sort_jumbled mapping nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (mapping nums : Slice Std.I64)
    (hmap : IsDigitPermutation mapping.val) (hnums : IsValidInput nums.val), ∃ r : alloc.vec.Vec Std.I64, Aegis.SortJumbled.sort_jumbled mapping nums = ok r) := by
  sorry

/-- Whenever the function returns a result r, len(r) = len(nums).
  Preconditions: len(mapping) = 10; for every i with 0 <= i < 10, 0 <= mapping[i] <= 9; mapping[0],...,mapping[9] are pairwise distinct; let L = len(nums); 1 <= L <= 30000; for every i with 0 <= i < L, 0 <= nums[i] < 10^9. -/
theorem spec_3 (mapping nums : Slice Std.I64)
    (hmap : IsDigitPermutation mapping.val) (hnums : IsValidInput nums.val) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.SortJumbled.sort_jumbled mapping nums = ok r → r.val.length = nums.val.length := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (mapping nums : Slice Std.I64)
    (hmap : IsDigitPermutation mapping.val) (hnums : IsValidInput nums.val), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.SortJumbled.sort_jumbled mapping nums = ok r → r.val.length = nums.val.length) := by
  sorry

/-- Whenever the function returns a result r, for every p with 0 <= p < len(r), 0 <= r[p] < 10^9.
  Preconditions: len(mapping) = 10; for every i with 0 <= i < 10, 0 <= mapping[i] <= 9; mapping[0],...,mapping[9] are pairwise distinct; let L = len(nums); 1 <= L <= 30000; for every i with 0 <= i < L, 0 <= nums[i] < 10^9. -/
theorem spec_4 (mapping nums : Slice Std.I64)
    (hmap : IsDigitPermutation mapping.val) (hnums : IsValidInput nums.val) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.SortJumbled.sort_jumbled mapping nums = ok r → EntriesBounded r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (mapping nums : Slice Std.I64)
    (hmap : IsDigitPermutation mapping.val) (hnums : IsValidInput nums.val), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.SortJumbled.sort_jumbled mapping nums = ok r → EntriesBounded r.val) := by
  sorry

/-- Whenever the function returns a result r, for every integer x, the number of indices p with 0 <= p < len(r) and r[p] = x equals the number of indices i with 0 <= i < len(nums) and nums[i] = x.
  Preconditions: len(mapping) = 10; for every i with 0 <= i < 10, 0 <= mapping[i] <= 9; mapping[0],...,mapping[9] are pairwise distinct; let L = len(nums); 1 <= L <= 30000; for every i with 0 <= i < L, 0 <= nums[i] < 10^9. -/
theorem spec_5 (mapping nums : Slice Std.I64)
    (hmap : IsDigitPermutation mapping.val) (hnums : IsValidInput nums.val) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.SortJumbled.sort_jumbled mapping nums = ok r →
        ∀ x : Int, countValues r.val x = countValues nums.val x := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (mapping nums : Slice Std.I64)
    (hmap : IsDigitPermutation mapping.val) (hnums : IsValidInput nums.val), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.SortJumbled.sort_jumbled mapping nums = ok r →
        ∀ x : Int, countValues r.val x = countValues nums.val x) := by
  sorry

/-- Define mapval as in spec_1. Whenever the function returns a result r, every entry of r is an input number (so 0 <= r[p] < 10^9 for every p), and for all p and q with 0 <= p < q < len(r), mapval(r[p]) <= mapval(r[q]).
  Preconditions: len(mapping) = 10; for every i with 0 <= i < 10, 0 <= mapping[i] <= 9; mapping[0],...,mapping[9] are pairwise distinct; let L = len(nums); 1 <= L <= 30000; for every i with 0 <= i < L, 0 <= nums[i] < 10^9. -/
theorem spec_6 (mapping nums : Slice Std.I64)
    (hmap : IsDigitPermutation mapping.val) (hnums : IsValidInput nums.val) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.SortJumbled.sort_jumbled mapping nums = ok r →
        EntriesFrom r.val nums.val ∧ EntriesBounded r.val ∧
          ∀ p q : Nat,
            p < q →
              q < r.val.length →
                keyAt mapping.val r.val p ≤ keyAt mapping.val r.val q := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (mapping nums : Slice Std.I64)
    (hmap : IsDigitPermutation mapping.val) (hnums : IsValidInput nums.val), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.SortJumbled.sort_jumbled mapping nums = ok r →
        EntriesFrom r.val nums.val ∧ EntriesBounded r.val ∧
          ∀ p q : Nat,
            p < q →
              q < r.val.length →
                keyAt mapping.val r.val p ≤ keyAt mapping.val r.val q) := by
  sorry

/-- Define mapval as in spec_1. Whenever the function returns a result r, there exists a bijection f from {0,...,len(r)-1} to {0,...,len(nums)-1} such that r[p] = nums[f(p)] for every p, and for all p and q with 0 <= p < q < len(r), if mapval(r[p]) = mapval(r[q]), then f(p) < f(q).
  Preconditions: len(mapping) = 10; for every i with 0 <= i < 10, 0 <= mapping[i] <= 9; mapping[0],...,mapping[9] are pairwise distinct; let L = len(nums); 1 <= L <= 30000; for every i with 0 <= i < L, 0 <= nums[i] < 10^9. -/
theorem spec_7 (mapping nums : Slice Std.I64)
    (hmap : IsDigitPermutation mapping.val) (hnums : IsValidInput nums.val) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.SortJumbled.sort_jumbled mapping nums = ok r →
        ∃ e : Fin r.val.length ≃ Fin nums.val.length,
          (∀ p : Fin r.val.length, (r.val.get p).val = (nums.val.get (e p)).val) ∧
            ∀ p q : Fin r.val.length,
              p.val < q.val →
                key mapping.val (r.val.get p) = key mapping.val (r.val.get q) →
                  (e p).val < (e q).val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (mapping nums : Slice Std.I64)
    (hmap : IsDigitPermutation mapping.val) (hnums : IsValidInput nums.val), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.SortJumbled.sort_jumbled mapping nums = ok r →
        ∃ e : Fin r.val.length ≃ Fin nums.val.length,
          (∀ p : Fin r.val.length, (r.val.get p).val = (nums.val.get (e p)).val) ∧
            ∀ p q : Fin r.val.length,
              p.val < q.val →
                key mapping.val (r.val.get p) = key mapping.val (r.val.get q) →
                  (e p).val < (e q).val) := by
  sorry

/-- Define mapval as in spec_1. Whenever the function returns a result r, len(r) = len(nums) and every entry of r is an input number; let m = min { mapval(nums[i]) | 0 <= i < len(nums) }. Then mapval(r[0]) = m, and if i0 is the smallest index with 0 <= i0 < len(nums) and mapval(nums[i0]) = m, then r[0] = nums[i0].
  Preconditions: len(mapping) = 10; for every i with 0 <= i < 10, 0 <= mapping[i] <= 9; mapping[0],...,mapping[9] are pairwise distinct; let L = len(nums); 1 <= L <= 30000; for every i with 0 <= i < L, 0 <= nums[i] < 10^9. -/
theorem spec_8 (mapping nums : Slice Std.I64)
    (hmap : IsDigitPermutation mapping.val) (hnums : IsValidInput nums.val) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.SortJumbled.sort_jumbled mapping nums = ok r →
        r.val.length = nums.val.length ∧
          EntriesFrom r.val nums.val ∧
            ∃ m : Int,
              (∀ i, i < nums.val.length → m ≤ keyAt mapping.val nums.val i) ∧
                (∃ i, i < nums.val.length ∧ keyAt mapping.val nums.val i = m) ∧
                  keyAt mapping.val r.val 0 = m ∧
                    ∀ i0,
                      i0 < nums.val.length →
                        keyAt mapping.val nums.val i0 = m →
                          (∀ j, j < i0 → keyAt mapping.val nums.val j ≠ m) →
                            entryVal r.val 0 = entryVal nums.val i0 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (mapping nums : Slice Std.I64)
    (hmap : IsDigitPermutation mapping.val) (hnums : IsValidInput nums.val), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.SortJumbled.sort_jumbled mapping nums = ok r →
        r.val.length = nums.val.length ∧
          EntriesFrom r.val nums.val ∧
            ∃ m : Int,
              (∀ i, i < nums.val.length → m ≤ keyAt mapping.val nums.val i) ∧
                (∃ i, i < nums.val.length ∧ keyAt mapping.val nums.val i = m) ∧
                  keyAt mapping.val r.val 0 = m ∧
                    ∀ i0,
                      i0 < nums.val.length →
                        keyAt mapping.val nums.val i0 = m →
                          (∀ j, j < i0 → keyAt mapping.val nums.val j ≠ m) →
                            entryVal r.val 0 = entryVal nums.val i0) := by
  sorry

/-- Define mapval as in spec_1. Whenever the function returns a result r, len(r) = len(nums) and every entry of r is an input number; let M = max { mapval(nums[i]) | 0 <= i < len(nums) }. Then mapval(r[len(r)-1]) = M, and if iM is the largest index with 0 <= iM < len(nums) and mapval(nums[iM]) = M, then r[len(r)-1] = nums[iM].
  Preconditions: len(mapping) = 10; for every i with 0 <= i < 10, 0 <= mapping[i] <= 9; mapping[0],...,mapping[9] are pairwise distinct; let L = len(nums); 1 <= L <= 30000; for every i with 0 <= i < L, 0 <= nums[i] < 10^9. -/
theorem spec_9 (mapping nums : Slice Std.I64)
    (hmap : IsDigitPermutation mapping.val) (hnums : IsValidInput nums.val) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.SortJumbled.sort_jumbled mapping nums = ok r →
        r.val.length = nums.val.length ∧
          EntriesFrom r.val nums.val ∧
            ∃ M : Int,
              (∀ i, i < nums.val.length → keyAt mapping.val nums.val i ≤ M) ∧
                (∃ i, i < nums.val.length ∧ keyAt mapping.val nums.val i = M) ∧
                  keyAt mapping.val r.val (r.val.length - 1) = M ∧
                    ∀ iM,
                      iM < nums.val.length →
                        keyAt mapping.val nums.val iM = M →
                          (∀ j, iM < j → j < nums.val.length →
                            keyAt mapping.val nums.val j ≠ M) →
                            entryVal r.val (r.val.length - 1) = entryVal nums.val iM := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (mapping nums : Slice Std.I64)
    (hmap : IsDigitPermutation mapping.val) (hnums : IsValidInput nums.val), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.SortJumbled.sort_jumbled mapping nums = ok r →
        r.val.length = nums.val.length ∧
          EntriesFrom r.val nums.val ∧
            ∃ M : Int,
              (∀ i, i < nums.val.length → keyAt mapping.val nums.val i ≤ M) ∧
                (∃ i, i < nums.val.length ∧ keyAt mapping.val nums.val i = M) ∧
                  keyAt mapping.val r.val (r.val.length - 1) = M ∧
                    ∀ iM,
                      iM < nums.val.length →
                        keyAt mapping.val nums.val iM = M →
                          (∀ j, iM < j → j < nums.val.length →
                            keyAt mapping.val nums.val j ≠ M) →
                            entryVal r.val (r.val.length - 1) = entryVal nums.val iM) := by
  sorry

/-- Define mapval as in spec_1. Whenever the function returns a result r, every entry of r is an input number; for every integer v, the number of positions p with 0 <= p < len(r) and mapval(r[p]) = v equals the number of indices i with 0 <= i < len(nums) and mapval(nums[i]) = v.
  Preconditions: len(mapping) = 10; for every i with 0 <= i < 10, 0 <= mapping[i] <= 9; mapping[0],...,mapping[9] are pairwise distinct; let L = len(nums); 1 <= L <= 30000; for every i with 0 <= i < L, 0 <= nums[i] < 10^9. -/
theorem spec_10 (mapping nums : Slice Std.I64)
    (hmap : IsDigitPermutation mapping.val) (hnums : IsValidInput nums.val) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.SortJumbled.sort_jumbled mapping nums = ok r →
        EntriesFrom r.val nums.val ∧
          ∀ v : Int, countKeys mapping.val r.val v = countKeys mapping.val nums.val v := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (mapping nums : Slice Std.I64)
    (hmap : IsDigitPermutation mapping.val) (hnums : IsValidInput nums.val), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.SortJumbled.sort_jumbled mapping nums = ok r →
        EntriesFrom r.val nums.val ∧
          ∀ v : Int, countKeys mapping.val r.val v = countKeys mapping.val nums.val v) := by
  sorry

/-- Define mapval as in spec_1. Whenever the function returns a result r, every entry of r is an input number; for every integer v, the set { p | 0 <= p < len(r) and mapval(r[p]) = v } is a contiguous interval of integers (possibly empty).
  Preconditions: len(mapping) = 10; for every i with 0 <= i < 10, 0 <= mapping[i] <= 9; mapping[0],...,mapping[9] are pairwise distinct; let L = len(nums); 1 <= L <= 30000; for every i with 0 <= i < L, 0 <= nums[i] < 10^9. -/
theorem spec_11 (mapping nums : Slice Std.I64)
    (hmap : IsDigitPermutation mapping.val) (hnums : IsValidInput nums.val) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.SortJumbled.sort_jumbled mapping nums = ok r →
        EntriesFrom r.val nums.val ∧
          ∀ v : Int,
            ∃ lo hi : Nat,
              lo ≤ hi ∧
                ∀ p, p < r.val.length → (keyAt mapping.val r.val p = v ↔ lo ≤ p ∧ p < hi) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (mapping nums : Slice Std.I64)
    (hmap : IsDigitPermutation mapping.val) (hnums : IsValidInput nums.val), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.SortJumbled.sort_jumbled mapping nums = ok r →
        EntriesFrom r.val nums.val ∧
          ∀ v : Int,
            ∃ lo hi : Nat,
              lo ≤ hi ∧
                ∀ p, p < r.val.length → (keyAt mapping.val r.val p = v ↔ lo ≤ p ∧ p < hi)) := by
  sorry

/-- Define mapval as in spec_1. Whenever the function returns a result r, len(r) = len(nums) and every entry of r is an input number; for every integer t, let k be the number of indices i with 0 <= i < len(nums) and mapval(nums[i]) <= t. Then for every p with 0 <= p < k, mapval(r[p]) <= t, and for every p with k <= p < len(r), mapval(r[p]) > t.
  Preconditions: len(mapping) = 10; for every i with 0 <= i < 10, 0 <= mapping[i] <= 9; mapping[0],...,mapping[9] are pairwise distinct; let L = len(nums); 1 <= L <= 30000; for every i with 0 <= i < L, 0 <= nums[i] < 10^9. -/
theorem spec_12 (mapping nums : Slice Std.I64)
    (hmap : IsDigitPermutation mapping.val) (hnums : IsValidInput nums.val) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.SortJumbled.sort_jumbled mapping nums = ok r →
        r.val.length = nums.val.length ∧
          EntriesFrom r.val nums.val ∧
            ∀ t : Int,
              ∀ k : Nat,
                k = countKeysLe mapping.val nums.val t →
                  (∀ p, p < k → p < r.val.length → keyAt mapping.val r.val p ≤ t) ∧
                    ∀ p, k ≤ p → p < r.val.length → t < keyAt mapping.val r.val p := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (mapping nums : Slice Std.I64)
    (hmap : IsDigitPermutation mapping.val) (hnums : IsValidInput nums.val), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.SortJumbled.sort_jumbled mapping nums = ok r →
        r.val.length = nums.val.length ∧
          EntriesFrom r.val nums.val ∧
            ∀ t : Int,
              ∀ k : Nat,
                k = countKeysLe mapping.val nums.val t →
                  (∀ p, p < k → p < r.val.length → keyAt mapping.val r.val p ≤ t) ∧
                    ∀ p, k ≤ p → p < r.val.length → t < keyAt mapping.val r.val p) := by
  sorry

end AegisSpec.SortJumbled
