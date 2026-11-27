import Aegis.FindKthPositive.Code.Funs

/-!
# Specifications of `Aegis.FindKthPositive.find_kth_positive`

LeetCode problem `kth-missing-positive-number`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.FindKthPositive

  def occurs (arr : Slice Std.I64) (x : Int) : Prop :=
    x ∈ arr.val.map (fun s => s.val)

  def strictlyIncreasing (arr : Slice Std.I64) : Prop :=
    (arr.val.map (fun s => s.val)).Pairwise (fun a b => a < b)

  def entriesInRange (arr : Slice Std.I64) : Prop :=
    ∀ x ∈ arr.val, 1 ≤ x.val ∧ x.val ≤ 1000

  def arrGet? (arr : Slice Std.I64) (i : Nat) : Option Int :=
    (arr.val[i]?).map (fun s => s.val)

  noncomputable def countMissingBelow (arr : Slice Std.I64) (r : Int) : Int := by
    classical
    exact (((Finset.range (r - 1).toNat).filter
      (fun (n : Nat) => ¬ occurs arr ((n : Int) + 1))).card : Int)

  noncomputable def countMissingUpTo (arr : Slice Std.I64) (r : Int) : Int := by
    classical
    exact (((Finset.range r.toNat).filter
      (fun (n : Nat) => ¬ occurs arr ((n : Int) + 1))).card : Int)

  noncomputable def numIndicesBelow (arr : Slice Std.I64) (r : Int) : Nat :=
    (arr.val.filter (fun s => decide (s.val < r))).length

  /-- The function returns a result r and does not fail. The value r is positive, r is not equal to arr[i] for any i with 0 <= i < len(arr), and the number of positive integers x with 1 <= x < r and x not in the array arr is exactly k - 1.
    Preconditions: len(arr) >= 1 and len(arr) <= 1000; for every i with 0 <= i < len(arr), 1 <= arr[i] <= 1000; for every i, j with 0 <= i < j < len(arr), arr[i] < arr[j]; 1 <= k <= 1000. -/
  theorem spec_1
      (arr : Slice Std.I64) (k : Std.I64)
      (hlen_lower : 1 ≤ arr.val.length) (hlen_upper : arr.val.length ≤ 1000)
      (hentries : entriesInRange arr)
      (hsorted : strictlyIncreasing arr)
      (hk_lower : 1 ≤ k.val) (hk_upper : k.val ≤ 1000) :
      ∃ r : Std.I64,
        Aegis.FindKthPositive.find_kth_positive arr k = ok r ∧
        0 < r.val ∧
        ¬ occurs arr r.val ∧
        countMissingBelow arr r.val = k.val - 1 := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (arr : Slice Std.I64) (k : Std.I64)
        (hlen_lower : 1 ≤ arr.val.length) (hlen_upper : arr.val.length ≤ 1000)
        (hentries : entriesInRange arr)
        (hsorted : strictlyIncreasing arr)
        (hk_lower : 1 ≤ k.val) (hk_upper : k.val ≤ 1000), ∃ r : Std.I64,
          Aegis.FindKthPositive.find_kth_positive arr k = ok r ∧
          0 < r.val ∧
          ¬ occurs arr r.val ∧
          countMissingBelow arr r.val = k.val - 1) := by
    sorry

  /-- The function returns a result r; it does not fail, overflow, or access arr out of bounds.
    Preconditions: len(arr) >= 1 and len(arr) <= 1000; for every i with 0 <= i < len(arr), 1 <= arr[i] <= 1000; for every i, j with 0 <= i < j < len(arr), arr[i] < arr[j]; 1 <= k <= 1000. -/
  theorem spec_2
      (arr : Slice Std.I64) (k : Std.I64)
      (hlen_lower : 1 ≤ arr.val.length) (hlen_upper : arr.val.length ≤ 1000)
      (hentries : entriesInRange arr)
      (hsorted : strictlyIncreasing arr)
      (hk_lower : 1 ≤ k.val) (hk_upper : k.val ≤ 1000) :
      ∃ r : Std.I64, Aegis.FindKthPositive.find_kth_positive arr k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (arr : Slice Std.I64) (k : Std.I64)
        (hlen_lower : 1 ≤ arr.val.length) (hlen_upper : arr.val.length ≤ 1000)
        (hentries : entriesInRange arr)
        (hsorted : strictlyIncreasing arr)
        (hk_lower : 1 ≤ k.val) (hk_upper : k.val ≤ 1000), ∃ r : Std.I64, Aegis.FindKthPositive.find_kth_positive arr k = ok r) := by
    sorry

  /-- Whenever the function returns a result r, k <= r.
    Preconditions: len(arr) >= 1 and len(arr) <= 1000; for every i with 0 <= i < len(arr), 1 <= arr[i] <= 1000; for every i, j with 0 <= i < j < len(arr), arr[i] < arr[j]; 1 <= k <= 1000. -/
  theorem spec_3
      (arr : Slice Std.I64) (k : Std.I64)
      (hlen_lower : 1 ≤ arr.val.length) (hlen_upper : arr.val.length ≤ 1000)
      (hentries : entriesInRange arr)
      (hsorted : strictlyIncreasing arr)
      (hk_lower : 1 ≤ k.val) (hk_upper : k.val ≤ 1000)
      (r : Std.I64)
      (hres : Aegis.FindKthPositive.find_kth_positive arr k = ok r) :
      k.val ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (arr : Slice Std.I64) (k : Std.I64)
        (hlen_lower : 1 ≤ arr.val.length) (hlen_upper : arr.val.length ≤ 1000)
        (hentries : entriesInRange arr)
        (hsorted : strictlyIncreasing arr)
        (hk_lower : 1 ≤ k.val) (hk_upper : k.val ≤ 1000)
        (r : Std.I64)
        (hres : Aegis.FindKthPositive.find_kth_positive arr k = ok r), k.val ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r <= k + len(arr).
    Preconditions: len(arr) >= 1 and len(arr) <= 1000; for every i with 0 <= i < len(arr), 1 <= arr[i] <= 1000; for every i, j with 0 <= i < j < len(arr), arr[i] < arr[j]; 1 <= k <= 1000. -/
  theorem spec_4
      (arr : Slice Std.I64) (k : Std.I64)
      (hlen_lower : 1 ≤ arr.val.length) (hlen_upper : arr.val.length ≤ 1000)
      (hentries : entriesInRange arr)
      (hsorted : strictlyIncreasing arr)
      (hk_lower : 1 ≤ k.val) (hk_upper : k.val ≤ 1000)
      (r : Std.I64)
      (hres : Aegis.FindKthPositive.find_kth_positive arr k = ok r) :
      r.val ≤ k.val + (arr.val.length : Int) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (arr : Slice Std.I64) (k : Std.I64)
        (hlen_lower : 1 ≤ arr.val.length) (hlen_upper : arr.val.length ≤ 1000)
        (hentries : entriesInRange arr)
        (hsorted : strictlyIncreasing arr)
        (hk_lower : 1 ≤ k.val) (hk_upper : k.val ≤ 1000)
        (r : Std.I64)
        (hres : Aegis.FindKthPositive.find_kth_positive arr k = ok r), r.val ≤ k.val + (arr.val.length : Int)) := by
    sorry

  /-- Whenever the function returns a result r, the number of positive integers x such that 1 <= x <= r and x is not equal to arr[i] for every i with 0 <= i < len(arr) is exactly k.
    Preconditions: len(arr) >= 1 and len(arr) <= 1000; for every i with 0 <= i < len(arr), 1 <= arr[i] <= 1000; for every i, j with 0 <= i < j < len(arr), arr[i] < arr[j]; 1 <= k <= 1000. -/
  theorem spec_5
      (arr : Slice Std.I64) (k : Std.I64)
      (hlen_lower : 1 ≤ arr.val.length) (hlen_upper : arr.val.length ≤ 1000)
      (hentries : entriesInRange arr)
      (hsorted : strictlyIncreasing arr)
      (hk_lower : 1 ≤ k.val) (hk_upper : k.val ≤ 1000)
      (r : Std.I64)
      (hres : Aegis.FindKthPositive.find_kth_positive arr k = ok r) :
      countMissingUpTo arr r.val = k.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (arr : Slice Std.I64) (k : Std.I64)
        (hlen_lower : 1 ≤ arr.val.length) (hlen_upper : arr.val.length ≤ 1000)
        (hentries : entriesInRange arr)
        (hsorted : strictlyIncreasing arr)
        (hk_lower : 1 ≤ k.val) (hk_upper : k.val ≤ 1000)
        (r : Std.I64)
        (hres : Aegis.FindKthPositive.find_kth_positive arr k = ok r), countMissingUpTo arr r.val = k.val) := by
    sorry

  /-- Whenever the function returns a result r, r = k + m, where m is the number of indices i with 0 <= i < len(arr) and arr[i] < r.
    Preconditions: len(arr) >= 1 and len(arr) <= 1000; for every i with 0 <= i < len(arr), 1 <= arr[i] <= 1000; for every i, j with 0 <= i < j < len(arr), arr[i] < arr[j]; 1 <= k <= 1000. -/
  theorem spec_6
      (arr : Slice Std.I64) (k : Std.I64)
      (hlen_lower : 1 ≤ arr.val.length) (hlen_upper : arr.val.length ≤ 1000)
      (hentries : entriesInRange arr)
      (hsorted : strictlyIncreasing arr)
      (hk_lower : 1 ≤ k.val) (hk_upper : k.val ≤ 1000)
      (r : Std.I64)
      (hres : Aegis.FindKthPositive.find_kth_positive arr k = ok r) :
      r.val = k.val + (numIndicesBelow arr r.val : Int) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (arr : Slice Std.I64) (k : Std.I64)
        (hlen_lower : 1 ≤ arr.val.length) (hlen_upper : arr.val.length ≤ 1000)
        (hentries : entriesInRange arr)
        (hsorted : strictlyIncreasing arr)
        (hk_lower : 1 ≤ k.val) (hk_upper : k.val ≤ 1000)
        (r : Std.I64)
        (hres : Aegis.FindKthPositive.find_kth_positive arr k = ok r), r.val = k.val + (numIndicesBelow arr r.val : Int)) := by
    sorry

  /-- Whenever the function returns a result r, let m be the number of indices i with 0 <= i < len(arr) and arr[i] < r. Then 0 <= m <= len(arr); if m > 0 then arr[m-1] < r; and if m < len(arr) then r < arr[m].
    Preconditions: len(arr) >= 1 and len(arr) <= 1000; for every i with 0 <= i < len(arr), 1 <= arr[i] <= 1000; for every i, j with 0 <= i < j < len(arr), arr[i] < arr[j]; 1 <= k <= 1000. -/
  theorem spec_7
      (arr : Slice Std.I64) (k : Std.I64)
      (hlen_lower : 1 ≤ arr.val.length) (hlen_upper : arr.val.length ≤ 1000)
      (hentries : entriesInRange arr)
      (hsorted : strictlyIncreasing arr)
      (hk_lower : 1 ≤ k.val) (hk_upper : k.val ≤ 1000)
      (r : Std.I64)
      (hres : Aegis.FindKthPositive.find_kth_positive arr k = ok r) :
      0 ≤ numIndicesBelow arr r.val ∧
      numIndicesBelow arr r.val ≤ arr.val.length ∧
      (0 < numIndicesBelow arr r.val →
        ∃ v : Int, arrGet? arr (numIndicesBelow arr r.val - 1) = some v ∧ v < r.val) ∧
      (numIndicesBelow arr r.val < arr.val.length →
        ∃ v : Int, arrGet? arr (numIndicesBelow arr r.val) = some v ∧ r.val < v) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (arr : Slice Std.I64) (k : Std.I64)
        (hlen_lower : 1 ≤ arr.val.length) (hlen_upper : arr.val.length ≤ 1000)
        (hentries : entriesInRange arr)
        (hsorted : strictlyIncreasing arr)
        (hk_lower : 1 ≤ k.val) (hk_upper : k.val ≤ 1000)
        (r : Std.I64)
        (hres : Aegis.FindKthPositive.find_kth_positive arr k = ok r), 0 ≤ numIndicesBelow arr r.val ∧
        numIndicesBelow arr r.val ≤ arr.val.length ∧
        (0 < numIndicesBelow arr r.val →
          ∃ v : Int, arrGet? arr (numIndicesBelow arr r.val - 1) = some v ∧ v < r.val) ∧
        (numIndicesBelow arr r.val < arr.val.length →
          ∃ v : Int, arrGet? arr (numIndicesBelow arr r.val) = some v ∧ r.val < v)) := by
    sorry

  /-- Whenever the function returns a result r, for every positive integer y with y < r, the number of positive integers x with 1 <= x <= y and x not in arr is at most k - 1.
    Preconditions: len(arr) >= 1 and len(arr) <= 1000; for every i with 0 <= i < len(arr), 1 <= arr[i] <= 1000; for every i, j with 0 <= i < j < len(arr), arr[i] < arr[j]; 1 <= k <= 1000. -/
  theorem spec_8
      (arr : Slice Std.I64) (k : Std.I64)
      (hlen_lower : 1 ≤ arr.val.length) (hlen_upper : arr.val.length ≤ 1000)
      (hentries : entriesInRange arr)
      (hsorted : strictlyIncreasing arr)
      (hk_lower : 1 ≤ k.val) (hk_upper : k.val ≤ 1000)
      (r : Std.I64)
      (hres : Aegis.FindKthPositive.find_kth_positive arr k = ok r) :
      ∀ y : Int, 0 < y → y < r.val → countMissingUpTo arr y ≤ k.val - 1 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (arr : Slice Std.I64) (k : Std.I64)
        (hlen_lower : 1 ≤ arr.val.length) (hlen_upper : arr.val.length ≤ 1000)
        (hentries : entriesInRange arr)
        (hsorted : strictlyIncreasing arr)
        (hk_lower : 1 ≤ k.val) (hk_upper : k.val ≤ 1000)
        (r : Std.I64)
        (hres : Aegis.FindKthPositive.find_kth_positive arr k = ok r), ∀ y : Int, 0 < y → y < r.val → countMissingUpTo arr y ≤ k.val - 1) := by
    sorry

  /-- Whenever the function returns a result r, for every positive integer y with r < y, the number of positive integers x with 1 <= x < y and x not in arr is at least k.
    Preconditions: len(arr) >= 1 and len(arr) <= 1000; for every i with 0 <= i < len(arr), 1 <= arr[i] <= 1000; for every i, j with 0 <= i < j < len(arr), arr[i] < arr[j]; 1 <= k <= 1000. -/
  theorem spec_9
      (arr : Slice Std.I64) (k : Std.I64)
      (hlen_lower : 1 ≤ arr.val.length) (hlen_upper : arr.val.length ≤ 1000)
      (hentries : entriesInRange arr)
      (hsorted : strictlyIncreasing arr)
      (hk_lower : 1 ≤ k.val) (hk_upper : k.val ≤ 1000)
      (r : Std.I64)
      (hres : Aegis.FindKthPositive.find_kth_positive arr k = ok r) :
      ∀ y : Int, 0 < y → r.val < y → k.val ≤ countMissingBelow arr y := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (arr : Slice Std.I64) (k : Std.I64)
        (hlen_lower : 1 ≤ arr.val.length) (hlen_upper : arr.val.length ≤ 1000)
        (hentries : entriesInRange arr)
        (hsorted : strictlyIncreasing arr)
        (hk_lower : 1 ≤ k.val) (hk_upper : k.val ≤ 1000)
        (r : Std.I64)
        (hres : Aegis.FindKthPositive.find_kth_positive arr k = ok r), ∀ y : Int, 0 < y → r.val < y → k.val ≤ countMissingBelow arr y) := by
    sorry

  /-- Whenever the function returns a result r, for every positive integer y, if y is not equal to arr[i] for every i with 0 <= i < len(arr), and the number of positive integers x with 1 <= x < y and x not in arr is exactly k - 1, then y = r.
    Preconditions: len(arr) >= 1 and len(arr) <= 1000; for every i with 0 <= i < len(arr), 1 <= arr[i] <= 1000; for every i, j with 0 <= i < j < len(arr), arr[i] < arr[j]; 1 <= k <= 1000. -/
  theorem spec_10
      (arr : Slice Std.I64) (k : Std.I64)
      (hlen_lower : 1 ≤ arr.val.length) (hlen_upper : arr.val.length ≤ 1000)
      (hentries : entriesInRange arr)
      (hsorted : strictlyIncreasing arr)
      (hk_lower : 1 ≤ k.val) (hk_upper : k.val ≤ 1000)
      (r : Std.I64)
      (hres : Aegis.FindKthPositive.find_kth_positive arr k = ok r) :
      ∀ y : Int, 0 < y → ¬ occurs arr y →
        countMissingBelow arr y = k.val - 1 → y = r.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (arr : Slice Std.I64) (k : Std.I64)
        (hlen_lower : 1 ≤ arr.val.length) (hlen_upper : arr.val.length ≤ 1000)
        (hentries : entriesInRange arr)
        (hsorted : strictlyIncreasing arr)
        (hk_lower : 1 ≤ k.val) (hk_upper : k.val ≤ 1000)
        (r : Std.I64)
        (hres : Aegis.FindKthPositive.find_kth_positive arr k = ok r), ∀ y : Int, 0 < y → ¬ occurs arr y →
          countMissingBelow arr y = k.val - 1 → y = r.val) := by
    sorry

  end AegisSpec.FindKthPositive
