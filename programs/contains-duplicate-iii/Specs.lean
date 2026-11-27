import Aegis.ContainsNearbyAlmostDuplicate.Code.Funs

/-!
# Specifications of `Aegis.ContainsNearbyAlmostDuplicate.contains_nearby_almost_duplicate`

LeetCode problem `contains-duplicate-iii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.ContainsNearbyAlmostDuplicate

  def valAt (nums : Slice Std.I64) (i : Nat) (hi : i < nums.val.length) : Int :=
    (nums.val[i]'hi).val

  /-- Whenever the function returns a result r, r is true if and only if there exist indices i and j such that 0 <= i < n, 0 <= j < n, i != j, |i - j| <= indexDiff, and |nums[i] - nums[j]| <= valueDiff. Here nums[i] is the mathematical integer represented by the i-th I64 entry, |x| is mathematical absolute value, and comparisons with indexDiff and valueDiff are mathematical integer comparisons.
    Preconditions: Let n = len(nums). The mathematical values of indexDiff and valueDiff satisfy indexDiff >= 0 and valueDiff >= 0. No upper bound on n or on the elements of nums is assumed for this specification. -/
  theorem spec_1 (nums : Slice Std.I64) (indexDiff valueDiff : Std.I64)
      (h_indexDiff : 0 ≤ indexDiff.val) (h_valueDiff : 0 ≤ valueDiff.val) :
      ∀ r : Bool,
        Aegis.ContainsNearbyAlmostDuplicate.contains_nearby_almost_duplicate nums indexDiff
            valueDiff = ok r →
          (r = true ↔
            ∃ (i j : Nat) (hi : i < nums.val.length) (hj : j < nums.val.length),
              i ≠ j ∧ |(i : Int) - (j : Int)| ≤ indexDiff.val ∧
                |valAt nums i hi - valAt nums j hj| ≤ valueDiff.val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (indexDiff valueDiff : Std.I64)
        (h_indexDiff : 0 ≤ indexDiff.val) (h_valueDiff : 0 ≤ valueDiff.val), ∀ r : Bool,
          Aegis.ContainsNearbyAlmostDuplicate.contains_nearby_almost_duplicate nums indexDiff
              valueDiff = ok r →
            (r = true ↔
              ∃ (i j : Nat) (hi : i < nums.val.length) (hj : j < nums.val.length),
                i ≠ j ∧ |(i : Int) - (j : Int)| ≤ indexDiff.val ∧
                  |valAt nums i hi - valAt nums j hj| ≤ valueDiff.val)) := by
    sorry

  /-- The function returns a result r (it does not fail, panic, overflow, or go out of bounds).
    Preconditions: Let n = len(nums). We have 0 <= n <= 100000; for every i with 0 <= i < n, -2147483648 <= nums[i] <= 2147483647; 0 <= indexDiff <= 100000; and 0 <= valueDiff <= 4294967294. -/
  theorem spec_2 (nums : Slice Std.I64) (indexDiff valueDiff : Std.I64)
      (h_n : nums.val.length ≤ 100000)
      (h_elems : ∀ (i : Nat) (hi : i < nums.val.length),
        -2147483648 ≤ valAt nums i hi ∧ valAt nums i hi ≤ 2147483647)
      (h_indexDiff : 0 ≤ indexDiff.val ∧ indexDiff.val ≤ 100000)
      (h_valueDiff : 0 ≤ valueDiff.val ∧ valueDiff.val ≤ 4294967294) :
      ∃ r : Bool,
        Aegis.ContainsNearbyAlmostDuplicate.contains_nearby_almost_duplicate nums indexDiff
            valueDiff = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (indexDiff valueDiff : Std.I64)
        (h_n : nums.val.length ≤ 100000)
        (h_elems : ∀ (i : Nat) (hi : i < nums.val.length),
          -2147483648 ≤ valAt nums i hi ∧ valAt nums i hi ≤ 2147483647)
        (h_indexDiff : 0 ≤ indexDiff.val ∧ indexDiff.val ≤ 100000)
        (h_valueDiff : 0 ≤ valueDiff.val ∧ valueDiff.val ≤ 4294967294), ∃ r : Bool,
          Aegis.ContainsNearbyAlmostDuplicate.contains_nearby_almost_duplicate nums indexDiff
              valueDiff = ok r) := by
    sorry

  /-- Whenever the function returns true, there exist indices i and j with 0 <= i < j < n, j - i <= indexDiff, and |nums[j] - nums[i]| <= valueDiff.
    Preconditions: Let n = len(nums). Assume indexDiff >= 0 and valueDiff >= 0. -/
  theorem spec_3 (nums : Slice Std.I64) (indexDiff valueDiff : Std.I64)
      (h_indexDiff : 0 ≤ indexDiff.val) (h_valueDiff : 0 ≤ valueDiff.val) :
      ∀ r : Bool,
        Aegis.ContainsNearbyAlmostDuplicate.contains_nearby_almost_duplicate nums indexDiff
            valueDiff = ok r →
          r = true →
          ∃ (i j : Nat) (hi : i < nums.val.length) (hj : j < nums.val.length),
            i < j ∧ (j : Int) - (i : Int) ≤ indexDiff.val ∧
              |valAt nums j hj - valAt nums i hi| ≤ valueDiff.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (indexDiff valueDiff : Std.I64)
        (h_indexDiff : 0 ≤ indexDiff.val) (h_valueDiff : 0 ≤ valueDiff.val), ∀ r : Bool,
          Aegis.ContainsNearbyAlmostDuplicate.contains_nearby_almost_duplicate nums indexDiff
              valueDiff = ok r →
            r = true →
            ∃ (i j : Nat) (hi : i < nums.val.length) (hj : j < nums.val.length),
              i < j ∧ (j : Int) - (i : Int) ≤ indexDiff.val ∧
                |valAt nums j hj - valAt nums i hi| ≤ valueDiff.val) := by
    sorry

  /-- Whenever the function returns false, for every pair of indices i and j with 0 <= i < n, 0 <= j < n, and i != j, if |i - j| <= indexDiff then |nums[i] - nums[j]| > valueDiff.
    Preconditions: Let n = len(nums). Assume indexDiff >= 0 and valueDiff >= 0. -/
  theorem spec_4 (nums : Slice Std.I64) (indexDiff valueDiff : Std.I64)
      (h_indexDiff : 0 ≤ indexDiff.val) (h_valueDiff : 0 ≤ valueDiff.val) :
      ∀ r : Bool,
        Aegis.ContainsNearbyAlmostDuplicate.contains_nearby_almost_duplicate nums indexDiff
            valueDiff = ok r →
          r = false →
          ∀ (i j : Nat) (hi : i < nums.val.length) (hj : j < nums.val.length),
            i ≠ j → |(i : Int) - (j : Int)| ≤ indexDiff.val →
              valueDiff.val < |valAt nums i hi - valAt nums j hj| := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (indexDiff valueDiff : Std.I64)
        (h_indexDiff : 0 ≤ indexDiff.val) (h_valueDiff : 0 ≤ valueDiff.val), ∀ r : Bool,
          Aegis.ContainsNearbyAlmostDuplicate.contains_nearby_almost_duplicate nums indexDiff
              valueDiff = ok r →
            r = false →
            ∀ (i j : Nat) (hi : i < nums.val.length) (hj : j < nums.val.length),
              i ≠ j → |(i : Int) - (j : Int)| ≤ indexDiff.val →
                valueDiff.val < |valAt nums i hi - valAt nums j hj|) := by
    sorry

  /-- Whenever the function returns a result r, r = false.
    Preconditions: Let n = len(nums). Assume n < 2, indexDiff >= 0, and valueDiff >= 0. -/
  theorem spec_5 (nums : Slice Std.I64) (indexDiff valueDiff : Std.I64)
      (h_n : nums.val.length < 2) (h_indexDiff : 0 ≤ indexDiff.val)
      (h_valueDiff : 0 ≤ valueDiff.val) :
      ∀ r : Bool,
        Aegis.ContainsNearbyAlmostDuplicate.contains_nearby_almost_duplicate nums indexDiff
            valueDiff = ok r →
          r = false := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (indexDiff valueDiff : Std.I64)
        (h_n : nums.val.length < 2) (h_indexDiff : 0 ≤ indexDiff.val)
        (h_valueDiff : 0 ≤ valueDiff.val), ∀ r : Bool,
          Aegis.ContainsNearbyAlmostDuplicate.contains_nearby_almost_duplicate nums indexDiff
              valueDiff = ok r →
            r = false) := by
    sorry

  /-- Whenever the function returns a result r, r is true if and only if there exist indices i and j with 0 <= i < j < n, j - i <= indexDiff, and nums[i] = nums[j].
    Preconditions: Let n = len(nums). Assume indexDiff >= 0 and valueDiff = 0. -/
  theorem spec_6 (nums : Slice Std.I64) (indexDiff valueDiff : Std.I64)
      (h_indexDiff : 0 ≤ indexDiff.val) (h_valueDiff : valueDiff.val = 0) :
      ∀ r : Bool,
        Aegis.ContainsNearbyAlmostDuplicate.contains_nearby_almost_duplicate nums indexDiff
            valueDiff = ok r →
          (r = true ↔
            ∃ (i j : Nat) (hi : i < nums.val.length) (hj : j < nums.val.length),
              i < j ∧ (j : Int) - (i : Int) ≤ indexDiff.val ∧
                valAt nums i hi = valAt nums j hj) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (indexDiff valueDiff : Std.I64)
        (h_indexDiff : 0 ≤ indexDiff.val) (h_valueDiff : valueDiff.val = 0), ∀ r : Bool,
          Aegis.ContainsNearbyAlmostDuplicate.contains_nearby_almost_duplicate nums indexDiff
              valueDiff = ok r →
            (r = true ↔
              ∃ (i j : Nat) (hi : i < nums.val.length) (hj : j < nums.val.length),
                i < j ∧ (j : Int) - (i : Int) ≤ indexDiff.val ∧
                  valAt nums i hi = valAt nums j hj)) := by
    sorry

  /-- Whenever both calls return results, r1 = true implies r2 = true (equivalently, r2 = false implies r1 = false).
    Preconditions: Let n = len(nums). Fix a slice nums of length n and integers k1, k2, t with 0 <= k1 <= k2 and t >= 0. Let r1 be the result of the call on (nums, k1, t) and r2 the result of the call on (nums, k2, t). -/
  theorem spec_7 (nums : Slice Std.I64) (k1 k2 t : Std.I64)
      (h_k1 : 0 ≤ k1.val) (h_k1k2 : k1.val ≤ k2.val) (h_t : 0 ≤ t.val) :
      ∀ r1 r2 : Bool,
        Aegis.ContainsNearbyAlmostDuplicate.contains_nearby_almost_duplicate nums k1 t = ok r1 →
          Aegis.ContainsNearbyAlmostDuplicate.contains_nearby_almost_duplicate nums k2 t =
              ok r2 →
            r1 = true → r2 = true := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (k1 k2 t : Std.I64)
        (h_k1 : 0 ≤ k1.val) (h_k1k2 : k1.val ≤ k2.val) (h_t : 0 ≤ t.val), ∀ r1 r2 : Bool,
          Aegis.ContainsNearbyAlmostDuplicate.contains_nearby_almost_duplicate nums k1 t = ok r1 →
            Aegis.ContainsNearbyAlmostDuplicate.contains_nearby_almost_duplicate nums k2 t =
                ok r2 →
              r1 = true → r2 = true) := by
    sorry

  /-- Whenever both calls return results, r = r'.
    Preconditions: Let n = len(nums). Assume indexDiff >= 0 and valueDiff >= 0. Let c be an integer and let nums' be any slice of length n such that, for every i with 0 <= i < n, nums'[i] = nums[i] + c holds in mathematical integers (so each nums'[i] is an I64 value). Let r be the result of the call on (nums, indexDiff, valueDiff) and r' the result of the call on (nums', indexDiff, valueDiff). -/
  theorem spec_8 (nums nums' : Slice Std.I64) (indexDiff valueDiff : Std.I64) (c : Int)
      (h_len : nums'.val.length = nums.val.length)
      (h_shift : ∀ (i : Nat) (hi : i < nums.val.length) (hi' : i < nums'.val.length),
        valAt nums' i hi' = valAt nums i hi + c)
      (h_indexDiff : 0 ≤ indexDiff.val) (h_valueDiff : 0 ≤ valueDiff.val) :
      ∀ r r' : Bool,
        Aegis.ContainsNearbyAlmostDuplicate.contains_nearby_almost_duplicate nums indexDiff
            valueDiff = ok r →
          Aegis.ContainsNearbyAlmostDuplicate.contains_nearby_almost_duplicate nums' indexDiff
              valueDiff = ok r' →
            r = r' := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums nums' : Slice Std.I64) (indexDiff valueDiff : Std.I64) (c : Int)
        (h_len : nums'.val.length = nums.val.length)
        (h_shift : ∀ (i : Nat) (hi : i < nums.val.length) (hi' : i < nums'.val.length),
          valAt nums' i hi' = valAt nums i hi + c)
        (h_indexDiff : 0 ≤ indexDiff.val) (h_valueDiff : 0 ≤ valueDiff.val), ∀ r r' : Bool,
          Aegis.ContainsNearbyAlmostDuplicate.contains_nearby_almost_duplicate nums indexDiff
              valueDiff = ok r →
            Aegis.ContainsNearbyAlmostDuplicate.contains_nearby_almost_duplicate nums' indexDiff
                valueDiff = ok r' →
              r = r') := by
    sorry

  /-- Whenever the function returns a result r, r is true if and only if there exist indices i and j with 0 <= i < j < n and |nums[i] - nums[j]| <= valueDiff.
    Preconditions: Let n = len(nums). Assume n >= 1, indexDiff >= n - 1, and valueDiff >= 0. -/
  theorem spec_9 (nums : Slice Std.I64) (indexDiff valueDiff : Std.I64)
      (h_n : 1 ≤ nums.val.length) (h_indexDiff : (nums.val.length : Int) - 1 ≤ indexDiff.val)
      (h_valueDiff : 0 ≤ valueDiff.val) :
      ∀ r : Bool,
        Aegis.ContainsNearbyAlmostDuplicate.contains_nearby_almost_duplicate nums indexDiff
            valueDiff = ok r →
          (r = true ↔
            ∃ (i j : Nat) (hi : i < nums.val.length) (hj : j < nums.val.length),
              i < j ∧ |valAt nums i hi - valAt nums j hj| ≤ valueDiff.val) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64) (indexDiff valueDiff : Std.I64)
        (h_n : 1 ≤ nums.val.length) (h_indexDiff : (nums.val.length : Int) - 1 ≤ indexDiff.val)
        (h_valueDiff : 0 ≤ valueDiff.val), ∀ r : Bool,
          Aegis.ContainsNearbyAlmostDuplicate.contains_nearby_almost_duplicate nums indexDiff
              valueDiff = ok r →
            (r = true ↔
              ∃ (i j : Nat) (hi : i < nums.val.length) (hj : j < nums.val.length),
                i < j ∧ |valAt nums i hi - valAt nums j hj| ≤ valueDiff.val)) := by
    sorry

  /-- Whenever the function returns a result r, r is true if and only if there exists an index i with 0 <= i < n - 1 and |nums[i] - nums[i+1]| <= valueDiff.
    Preconditions: Let n = len(nums). Assume indexDiff = 1 and valueDiff >= 0. -/
  theorem spec_10 (nums : Slice Std.I64) (indexDiff valueDiff : Std.I64)
      (h_indexDiff : indexDiff.val = 1) (h_valueDiff : 0 ≤ valueDiff.val) :
      ∀ r : Bool,
        Aegis.ContainsNearbyAlmostDuplicate.contains_nearby_almost_duplicate nums indexDiff
            valueDiff = ok r →
          (r = true ↔
            ∃ (i : Nat) (hi : i < nums.val.length - 1),
              |(nums.val[i]'(by omega)).val - (nums.val[i + 1]'(by omega)).val| ≤
                valueDiff.val) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64) (indexDiff valueDiff : Std.I64)
        (h_indexDiff : indexDiff.val = 1) (h_valueDiff : 0 ≤ valueDiff.val), ∀ r : Bool,
          Aegis.ContainsNearbyAlmostDuplicate.contains_nearby_almost_duplicate nums indexDiff
              valueDiff = ok r →
            (r = true ↔
              ∃ (i : Nat) (hi : i < nums.val.length - 1),
                |(nums.val[i]'(by omega)).val - (nums.val[i + 1]'(by omega)).val| ≤
                  valueDiff.val)) := by
    sorry

  /-- Whenever the function returns a result r, r = true.
    Preconditions: Let n = len(nums). Assume n >= 2, indexDiff >= 1, valueDiff >= 0, and valueDiff >= max{ |nums[i]-nums[j]| : 0 <= i < n and 0 <= j < n }. -/
  theorem spec_11 (nums : Slice Std.I64) (indexDiff valueDiff : Std.I64)
      (h_n : 2 ≤ nums.val.length) (h_indexDiff : 1 ≤ indexDiff.val)
      (h_valueDiff : 0 ≤ valueDiff.val)
      (h_max : ∀ (i j : Nat) (hi : i < nums.val.length) (hj : j < nums.val.length),
        |valAt nums i hi - valAt nums j hj| ≤ valueDiff.val) :
      ∀ r : Bool,
        Aegis.ContainsNearbyAlmostDuplicate.contains_nearby_almost_duplicate nums indexDiff
            valueDiff = ok r →
          r = true := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64) (indexDiff valueDiff : Std.I64)
        (h_n : 2 ≤ nums.val.length) (h_indexDiff : 1 ≤ indexDiff.val)
        (h_valueDiff : 0 ≤ valueDiff.val)
        (h_max : ∀ (i j : Nat) (hi : i < nums.val.length) (hj : j < nums.val.length),
          |valAt nums i hi - valAt nums j hj| ≤ valueDiff.val), ∀ r : Bool,
          Aegis.ContainsNearbyAlmostDuplicate.contains_nearby_almost_duplicate nums indexDiff
              valueDiff = ok r →
            r = true) := by
    sorry

  end AegisSpec.ContainsNearbyAlmostDuplicate
