import Aegis.CanThreePartsEqualSum.Code.Funs

/-!
# Specifications of `Aegis.CanThreePartsEqualSum.can_three_parts_equal_sum`

LeetCode problem `partition-array-into-three-parts-with-equal-sum`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.CanThreePartsEqualSum

open Aeneas Aeneas.Std Result

def vals (arr : Slice Std.I64) : List Int := arr.val.map (fun x => x.val)

def prefixSum (arr : Slice Std.I64) (k : Nat) : Int := (vals arr).take k |>.sum

def segSum (arr : Slice Std.I64) (a b : Nat) : Int := prefixSum arr b - prefixSum arr a

def totalSum (arr : Slice Std.I64) : Int := (vals arr).sum

def elem (arr : Slice Std.I64) (i : Nat) : Int :=
  match arr.val[i]? with
  | some x => x.val
  | none => 0

theorem prefixSum_zero (arr : Slice Std.I64) : prefixSum arr 0 = 0 := rfl

theorem prefixSum_length (arr : Slice Std.I64) :
    prefixSum arr arr.val.length = totalSum arr := by
  have h : (List.map (fun x : Std.I64 => x.val) arr.val).length = arr.val.length :=
    List.length_map ..
  simp only [prefixSum, totalSum, vals, ← h, List.take_length]

theorem segSum_self (arr : Slice Std.I64) (a : Nat) : segSum arr a a = 0 := by
  simp [segSum]

theorem elem_eq_get (arr : Slice Std.I64) (i : Nat) (h : i < arr.val.length) :
    elem arr i = (arr.val[i]'h).val := by
  simp [elem, List.getElem?_eq_getElem h]

/-- Let n = len(arr) and let S(a,b) denote arr[a] + arr[a+1] + ... + arr[b-1] for 0 <= a <= b <= n (so S(a,a) = 0). The function returns a result r (it does not fail) and r = true if and only if there exist integers p and q with 1 <= p < q <= n-1 such that S(0,p) = S(p,q) = S(q,n).
  Preconditions: 3 <= len(arr) <= 5 * 10^4 and for every i with 0 <= i < len(arr), -10^4 <= arr[i] <= 10^4. -/
theorem spec_1 (arr : Slice Std.I64)
    (hlen : 3 ≤ arr.val.length) (hlen' : arr.val.length ≤ 50000)
    (hbounds : ∀ (i : Nat), i < arr.val.length → -10000 ≤ elem arr i ∧ elem arr i ≤ 10000) :
    ∃ r : Bool,
      Aegis.CanThreePartsEqualSum.can_three_parts_equal_sum arr = ok r ∧
        (r = true ↔ ∃ p q : Nat,
          1 ≤ p ∧ p < q ∧ q ≤ arr.val.length - 1 ∧
            segSum arr 0 p = segSum arr p q ∧
            segSum arr p q = segSum arr q arr.val.length) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen : 3 ≤ arr.val.length) (hlen' : arr.val.length ≤ 50000)
    (hbounds : ∀ (i : Nat), i < arr.val.length → -10000 ≤ elem arr i ∧ elem arr i ≤ 10000), ∃ r : Bool,
      Aegis.CanThreePartsEqualSum.can_three_parts_equal_sum arr = ok r ∧
        (r = true ↔ ∃ p q : Nat,
          1 ≤ p ∧ p < q ∧ q ≤ arr.val.length - 1 ∧
            segSum arr 0 p = segSum arr p q ∧
            segSum arr p q = segSum arr q arr.val.length)) := by
  sorry

/-- The function returns a result r and does not fail (no overflow, out-of-bounds access, or panic).
  Preconditions: 3 <= len(arr) <= 5 * 10^4 and for every i with 0 <= i < len(arr), -10^4 <= arr[i] <= 10^4. -/
theorem spec_2 (arr : Slice Std.I64)
    (hlen : 3 ≤ arr.val.length) (hlen' : arr.val.length ≤ 50000)
    (hbounds : ∀ (i : Nat), i < arr.val.length → -10000 ≤ elem arr i ∧ elem arr i ≤ 10000) :
    ∃ r : Bool, Aegis.CanThreePartsEqualSum.can_three_parts_equal_sum arr = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen : 3 ≤ arr.val.length) (hlen' : arr.val.length ≤ 50000)
    (hbounds : ∀ (i : Nat), i < arr.val.length → -10000 ≤ elem arr i ∧ elem arr i ≤ 10000), ∃ r : Bool, Aegis.CanThreePartsEqualSum.can_three_parts_equal_sum arr = ok r) := by
  sorry

/-- Whenever the function returns a result r, if r = true then the total sum T = arr[0] + arr[1] + ... + arr[len(arr)-1] satisfies T = 3*s for some integer s.
  Preconditions: 3 <= len(arr) <= 5 * 10^4 and for every i with 0 <= i < len(arr), -10^4 <= arr[i] <= 10^4. -/
theorem spec_3 (arr : Slice Std.I64)
    (hlen : 3 ≤ arr.val.length) (hlen' : arr.val.length ≤ 50000)
    (hbounds : ∀ (i : Nat), i < arr.val.length → -10000 ≤ elem arr i ∧ elem arr i ≤ 10000) :
    ∀ r : Bool,
      Aegis.CanThreePartsEqualSum.can_three_parts_equal_sum arr = ok r →
        r = true → ∃ s : Int, totalSum arr = 3 * s := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen : 3 ≤ arr.val.length) (hlen' : arr.val.length ≤ 50000)
    (hbounds : ∀ (i : Nat), i < arr.val.length → -10000 ≤ elem arr i ∧ elem arr i ≤ 10000), ∀ r : Bool,
      Aegis.CanThreePartsEqualSum.can_three_parts_equal_sum arr = ok r →
        r = true → ∃ s : Int, totalSum arr = 3 * s) := by
  sorry

/-- Whenever the function returns a result r, if the total sum T = arr[0] + arr[1] + ... + arr[len(arr)-1] is not divisible by 3 (there is no integer s with T = 3*s), then r = false.
  Preconditions: 3 <= len(arr) <= 5 * 10^4 and for every i with 0 <= i < len(arr), -10^4 <= arr[i] <= 10^4. -/
theorem spec_4 (arr : Slice Std.I64)
    (hlen : 3 ≤ arr.val.length) (hlen' : arr.val.length ≤ 50000)
    (hbounds : ∀ (i : Nat), i < arr.val.length → -10000 ≤ elem arr i ∧ elem arr i ≤ 10000) :
    ∀ r : Bool,
      Aegis.CanThreePartsEqualSum.can_three_parts_equal_sum arr = ok r →
        (¬ ∃ s : Int, totalSum arr = 3 * s) → r = false := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen : 3 ≤ arr.val.length) (hlen' : arr.val.length ≤ 50000)
    (hbounds : ∀ (i : Nat), i < arr.val.length → -10000 ≤ elem arr i ∧ elem arr i ≤ 10000), ∀ r : Bool,
      Aegis.CanThreePartsEqualSum.can_three_parts_equal_sum arr = ok r →
        (¬ ∃ s : Int, totalSum arr = 3 * s) → r = false) := by
  sorry

/-- Whenever the function returns a result r, if r = true then there exist integers p, q, and s with 1 <= p < q <= len(arr)-1, P(p) = s, P(q) = 2*s, and T = 3*s, where T = arr[0] + ... + arr[len(arr)-1] and P(k) = arr[0] + ... + arr[k-1] for 0 <= k <= len(arr).
  Preconditions: 3 <= len(arr) <= 5 * 10^4 and for every i with 0 <= i < len(arr), -10^4 <= arr[i] <= 10^4. -/
theorem spec_5 (arr : Slice Std.I64)
    (hlen : 3 ≤ arr.val.length) (hlen' : arr.val.length ≤ 50000)
    (hbounds : ∀ (i : Nat), i < arr.val.length → -10000 ≤ elem arr i ∧ elem arr i ≤ 10000) :
    ∀ r : Bool,
      Aegis.CanThreePartsEqualSum.can_three_parts_equal_sum arr = ok r →
        r = true →
          ∃ (p q : Nat) (s : Int),
            1 ≤ p ∧ p < q ∧ q ≤ arr.val.length - 1 ∧
              prefixSum arr p = s ∧ prefixSum arr q = 2 * s ∧ totalSum arr = 3 * s := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen : 3 ≤ arr.val.length) (hlen' : arr.val.length ≤ 50000)
    (hbounds : ∀ (i : Nat), i < arr.val.length → -10000 ≤ elem arr i ∧ elem arr i ≤ 10000), ∀ r : Bool,
      Aegis.CanThreePartsEqualSum.can_three_parts_equal_sum arr = ok r →
        r = true →
          ∃ (p q : Nat) (s : Int),
            1 ≤ p ∧ p < q ∧ q ≤ arr.val.length - 1 ∧
              prefixSum arr p = s ∧ prefixSum arr q = 2 * s ∧ totalSum arr = 3 * s) := by
  sorry

/-- Whenever the function returns a result r, if there exist integers p, q, and s with 1 <= p < q <= len(arr)-1, P(p) = s, P(q) = 2*s, and T = 3*s, where T = arr[0] + ... + arr[len(arr)-1] and P(k) = arr[0] + ... + arr[k-1] for 0 <= k <= len(arr), then r = true.
  Preconditions: 3 <= len(arr) <= 5 * 10^4 and for every i with 0 <= i < len(arr), -10^4 <= arr[i] <= 10^4. -/
theorem spec_6 (arr : Slice Std.I64)
    (hlen : 3 ≤ arr.val.length) (hlen' : arr.val.length ≤ 50000)
    (hbounds : ∀ (i : Nat), i < arr.val.length → -10000 ≤ elem arr i ∧ elem arr i ≤ 10000) :
    ∀ r : Bool,
      Aegis.CanThreePartsEqualSum.can_three_parts_equal_sum arr = ok r →
        (∃ (p q : Nat) (s : Int),
            1 ≤ p ∧ p < q ∧ q ≤ arr.val.length - 1 ∧
              prefixSum arr p = s ∧ prefixSum arr q = 2 * s ∧ totalSum arr = 3 * s) →
          r = true := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen : 3 ≤ arr.val.length) (hlen' : arr.val.length ≤ 50000)
    (hbounds : ∀ (i : Nat), i < arr.val.length → -10000 ≤ elem arr i ∧ elem arr i ≤ 10000), ∀ r : Bool,
      Aegis.CanThreePartsEqualSum.can_three_parts_equal_sum arr = ok r →
        (∃ (p q : Nat) (s : Int),
            1 ≤ p ∧ p < q ∧ q ≤ arr.val.length - 1 ∧
              prefixSum arr p = s ∧ prefixSum arr q = 2 * s ∧ totalSum arr = 3 * s) →
          r = true) := by
  sorry

/-- Whenever the function returns a result r, r = false if and only if for every pair of integers p and q with 1 <= p < q <= len(arr)-1, it is not the case that S(0,p) = S(p,q) and S(p,q) = S(q,n), where n = len(arr) and S(a,b) = arr[a] + ... + arr[b-1] for 0 <= a <= b <= n.
  Preconditions: 3 <= len(arr) <= 5 * 10^4 and for every i with 0 <= i < len(arr), -10^4 <= arr[i] <= 10^4. -/
theorem spec_7 (arr : Slice Std.I64)
    (hlen : 3 ≤ arr.val.length) (hlen' : arr.val.length ≤ 50000)
    (hbounds : ∀ (i : Nat), i < arr.val.length → -10000 ≤ elem arr i ∧ elem arr i ≤ 10000) :
    ∀ r : Bool,
      Aegis.CanThreePartsEqualSum.can_three_parts_equal_sum arr = ok r →
        (r = false ↔
          ∀ (p q : Nat), 1 ≤ p → p < q → q ≤ arr.val.length - 1 →
            ¬ (segSum arr 0 p = segSum arr p q ∧ segSum arr p q = segSum arr q arr.val.length)) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen : 3 ≤ arr.val.length) (hlen' : arr.val.length ≤ 50000)
    (hbounds : ∀ (i : Nat), i < arr.val.length → -10000 ≤ elem arr i ∧ elem arr i ≤ 10000), ∀ r : Bool,
      Aegis.CanThreePartsEqualSum.can_three_parts_equal_sum arr = ok r →
        (r = false ↔
          ∀ (p q : Nat), 1 ≤ p → p < q → q ≤ arr.val.length - 1 →
            ¬ (segSum arr 0 p = segSum arr p q ∧ segSum arr p q = segSum arr q arr.val.length))) := by
  sorry

/-- Whenever the function returns a result r, r = true if and only if arr[0] = arr[1] and arr[1] = arr[2].
  Preconditions: len(arr) = 3 and for every i with 0 <= i < 3, -10^4 <= arr[i] <= 10^4. -/
theorem spec_8 (arr : Slice Std.I64)
    (hlen : arr.val.length = 3)
    (hbounds : ∀ (i : Nat), i < 3 → -10000 ≤ elem arr i ∧ elem arr i ≤ 10000) :
    ∀ r : Bool,
      Aegis.CanThreePartsEqualSum.can_three_parts_equal_sum arr = ok r →
        (r = true ↔ elem arr 0 = elem arr 1 ∧ elem arr 1 = elem arr 2) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen : arr.val.length = 3)
    (hbounds : ∀ (i : Nat), i < 3 → -10000 ≤ elem arr i ∧ elem arr i ≤ 10000), ∀ r : Bool,
      Aegis.CanThreePartsEqualSum.can_three_parts_equal_sum arr = ok r →
        (r = true ↔ elem arr 0 = elem arr 1 ∧ elem arr 1 = elem arr 2)) := by
  sorry

/-- Whenever the function returns a result r, if T = arr[0] + ... + arr[len(arr)-1] = 0, then r = true if and only if there exist integers p and q with 1 <= p < q <= len(arr)-1 such that P(p) = 0 and P(q) = 0, where P(k) = arr[0] + ... + arr[k-1] for 0 <= k <= len(arr).
  Preconditions: 3 <= len(arr) <= 5 * 10^4 and for every i with 0 <= i < len(arr), -10^4 <= arr[i] <= 10^4. -/
theorem spec_9 (arr : Slice Std.I64)
    (hlen : 3 ≤ arr.val.length) (hlen' : arr.val.length ≤ 50000)
    (hbounds : ∀ (i : Nat), i < arr.val.length → -10000 ≤ elem arr i ∧ elem arr i ≤ 10000) :
    ∀ r : Bool,
      Aegis.CanThreePartsEqualSum.can_three_parts_equal_sum arr = ok r →
        totalSum arr = 0 →
          (r = true ↔ ∃ p q : Nat,
            1 ≤ p ∧ p < q ∧ q ≤ arr.val.length - 1 ∧
              prefixSum arr p = 0 ∧ prefixSum arr q = 0) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen : 3 ≤ arr.val.length) (hlen' : arr.val.length ≤ 50000)
    (hbounds : ∀ (i : Nat), i < arr.val.length → -10000 ≤ elem arr i ∧ elem arr i ≤ 10000), ∀ r : Bool,
      Aegis.CanThreePartsEqualSum.can_three_parts_equal_sum arr = ok r →
        totalSum arr = 0 →
          (r = true ↔ ∃ p q : Nat,
            1 ≤ p ∧ p < q ∧ q ≤ arr.val.length - 1 ∧
              prefixSum arr p = 0 ∧ prefixSum arr q = 0)) := by
  sorry

/-- Whenever the function returns a result r, if r = true then there exists an integer p with 1 <= p <= len(arr)-2 such that P(p) = s for some integer s with T = 3*s, where T = arr[0] + ... + arr[len(arr)-1] and P(k) = arr[0] + ... + arr[k-1] for 0 <= k <= len(arr).
  Preconditions: 3 <= len(arr) <= 5 * 10^4 and for every i with 0 <= i < len(arr), -10^4 <= arr[i] <= 10^4. -/
theorem spec_10 (arr : Slice Std.I64)
    (hlen : 3 ≤ arr.val.length) (hlen' : arr.val.length ≤ 50000)
    (hbounds : ∀ (i : Nat), i < arr.val.length → -10000 ≤ elem arr i ∧ elem arr i ≤ 10000) :
    ∀ r : Bool,
      Aegis.CanThreePartsEqualSum.can_three_parts_equal_sum arr = ok r →
        r = true →
          ∃ (p : Nat) (s : Int),
            1 ≤ p ∧ p ≤ arr.val.length - 2 ∧ prefixSum arr p = s ∧ totalSum arr = 3 * s := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen : 3 ≤ arr.val.length) (hlen' : arr.val.length ≤ 50000)
    (hbounds : ∀ (i : Nat), i < arr.val.length → -10000 ≤ elem arr i ∧ elem arr i ≤ 10000), ∀ r : Bool,
      Aegis.CanThreePartsEqualSum.can_three_parts_equal_sum arr = ok r →
        r = true →
          ∃ (p : Nat) (s : Int),
            1 ≤ p ∧ p ≤ arr.val.length - 2 ∧ prefixSum arr p = s ∧ totalSum arr = 3 * s) := by
  sorry

/-- Whenever the function returns a result r, if r = true then there exists an integer q with 2 <= q <= len(arr)-1 such that P(q) = 2*s for some integer s with T = 3*s, where T = arr[0] + ... + arr[len(arr)-1] and P(k) = arr[0] + ... + arr[k-1] for 0 <= k <= len(arr).
  Preconditions: 3 <= len(arr) <= 5 * 10^4 and for every i with 0 <= i < len(arr), -10^4 <= arr[i] <= 10^4. -/
theorem spec_11 (arr : Slice Std.I64)
    (hlen : 3 ≤ arr.val.length) (hlen' : arr.val.length ≤ 50000)
    (hbounds : ∀ (i : Nat), i < arr.val.length → -10000 ≤ elem arr i ∧ elem arr i ≤ 10000) :
    ∀ r : Bool,
      Aegis.CanThreePartsEqualSum.can_three_parts_equal_sum arr = ok r →
        r = true →
          ∃ (q : Nat) (s : Int),
            2 ≤ q ∧ q ≤ arr.val.length - 1 ∧ prefixSum arr q = 2 * s ∧ totalSum arr = 3 * s := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen : 3 ≤ arr.val.length) (hlen' : arr.val.length ≤ 50000)
    (hbounds : ∀ (i : Nat), i < arr.val.length → -10000 ≤ elem arr i ∧ elem arr i ≤ 10000), ∀ r : Bool,
      Aegis.CanThreePartsEqualSum.can_three_parts_equal_sum arr = ok r →
        r = true →
          ∃ (q : Nat) (s : Int),
            2 ≤ q ∧ q ≤ arr.val.length - 1 ∧ prefixSum arr q = 2 * s ∧ totalSum arr = 3 * s) := by
  sorry

/-- Whenever the function returns a result r, if T = 3*s for some integer s and there is no integer p with 1 <= p <= len(arr)-2 and P(p) = s, then r = false, where T = arr[0] + ... + arr[len(arr)-1] and P(k) = arr[0] + ... + arr[k-1] for 0 <= k <= len(arr).
  Preconditions: 3 <= len(arr) <= 5 * 10^4 and for every i with 0 <= i < len(arr), -10^4 <= arr[i] <= 10^4. -/
theorem spec_12 (arr : Slice Std.I64)
    (hlen : 3 ≤ arr.val.length) (hlen' : arr.val.length ≤ 50000)
    (hbounds : ∀ (i : Nat), i < arr.val.length → -10000 ≤ elem arr i ∧ elem arr i ≤ 10000) :
    ∀ r : Bool,
      Aegis.CanThreePartsEqualSum.can_three_parts_equal_sum arr = ok r →
        ∀ s : Int,
          totalSum arr = 3 * s →
            (¬ ∃ p : Nat, 1 ≤ p ∧ p ≤ arr.val.length - 2 ∧ prefixSum arr p = s) → r = false := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen : 3 ≤ arr.val.length) (hlen' : arr.val.length ≤ 50000)
    (hbounds : ∀ (i : Nat), i < arr.val.length → -10000 ≤ elem arr i ∧ elem arr i ≤ 10000), ∀ r : Bool,
      Aegis.CanThreePartsEqualSum.can_three_parts_equal_sum arr = ok r →
        ∀ s : Int,
          totalSum arr = 3 * s →
            (¬ ∃ p : Nat, 1 ≤ p ∧ p ≤ arr.val.length - 2 ∧ prefixSum arr p = s) → r = false) := by
  sorry

/-- Whenever the function returns a result r, if T = 3*s for some integer s and there is no integer q with 2 <= q <= len(arr)-1 and P(q) = 2*s, then r = false, where T = arr[0] + ... + arr[len(arr)-1] and P(k) = arr[0] + ... + arr[k-1] for 0 <= k <= len(arr).
  Preconditions: 3 <= len(arr) <= 5 * 10^4 and for every i with 0 <= i < len(arr), -10^4 <= arr[i] <= 10^4. -/
theorem spec_13 (arr : Slice Std.I64)
    (hlen : 3 ≤ arr.val.length) (hlen' : arr.val.length ≤ 50000)
    (hbounds : ∀ (i : Nat), i < arr.val.length → -10000 ≤ elem arr i ∧ elem arr i ≤ 10000) :
    ∀ r : Bool,
      Aegis.CanThreePartsEqualSum.can_three_parts_equal_sum arr = ok r →
        ∀ s : Int,
          totalSum arr = 3 * s →
            (¬ ∃ q : Nat, 2 ≤ q ∧ q ≤ arr.val.length - 1 ∧ prefixSum arr q = 2 * s) →
              r = false := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen : 3 ≤ arr.val.length) (hlen' : arr.val.length ≤ 50000)
    (hbounds : ∀ (i : Nat), i < arr.val.length → -10000 ≤ elem arr i ∧ elem arr i ≤ 10000), ∀ r : Bool,
      Aegis.CanThreePartsEqualSum.can_three_parts_equal_sum arr = ok r →
        ∀ s : Int,
          totalSum arr = 3 * s →
            (¬ ∃ q : Nat, 2 ≤ q ∧ q ≤ arr.val.length - 1 ∧ prefixSum arr q = 2 * s) →
              r = false) := by
  sorry

end AegisSpec.CanThreePartsEqualSum
