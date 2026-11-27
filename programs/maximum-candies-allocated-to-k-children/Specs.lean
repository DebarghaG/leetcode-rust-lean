import Aegis.MaximumCandies.Code.Funs

/-!
# Specifications of `Aegis.MaximumCandies.maximum_candies`

LeetCode problem `maximum-candies-allocated-to-k-children`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaximumCandies

  def intsOf (candies : Slice Std.I64) : List ℤ :=
    candies.val.map (fun c => c.val)

  def elem (candies : Slice Std.I64) (i : ℕ) : ℤ :=
    (intsOf candies).getD i 0

  def totalCandies (candies : Slice Std.I64) : ℤ :=
    (intsOf candies).sum

  def countAt (candies : Slice Std.I64) (x : ℤ) : ℤ :=
    ((intsOf candies).map (fun c => c / x)).sum

  def maxCandy (candies : Slice Std.I64) : ℤ :=
    (intsOf candies).foldr max 0

  def Feasible (candies : Slice Std.I64) (k : ℤ) (x : ℤ) : Prop :=
    x = 0 ∨ (0 < x ∧ k ≤ countAt candies x)

  def GreatestFeasible (candies : Slice Std.I64) (k : ℤ) (r : ℤ) : Prop :=
    Feasible candies k r ∧ ∀ x : ℤ, Feasible candies k x → x ≤ r

  /-- Let n = len(candies). Whenever the function returns a result r, r is the greatest nonnegative integer x such that either x = 0, or x > 0 and the sum over i = 0,...,n-1 of floor(candies[i] / x) is at least k.
    Preconditions: len(candies) >= 1, len(candies) <= 100000, for every i with 0 <= i < len(candies), 1 <= candies[i] <= 10000000, and 1 <= k <= 1000000000000. All values are machine i64 values within these bounds. -/
  theorem spec_1 (candies : Slice Std.I64) (k : Std.I64)
      (h_len_pos : 1 ≤ candies.length) (h_len_le : candies.length ≤ 100000)
      (h_elem : ∀ c ∈ intsOf candies, 1 ≤ c ∧ c ≤ 10000000)
      (h_k : 1 ≤ k.val ∧ k.val ≤ 1000000000000) :
      ∀ r : Std.I64,
        Aegis.MaximumCandies.maximum_candies candies k = ok r →
          GreatestFeasible candies k.val r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (candies : Slice Std.I64) (k : Std.I64)
        (h_len_pos : 1 ≤ candies.length) (h_len_le : candies.length ≤ 100000)
        (h_elem : ∀ c ∈ intsOf candies, 1 ≤ c ∧ c ≤ 10000000)
        (h_k : 1 ≤ k.val ∧ k.val ≤ 1000000000000), ∀ r : Std.I64,
          Aegis.MaximumCandies.maximum_candies candies k = ok r →
            GreatestFeasible candies k.val r.val) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r; in particular it does not panic, go out of bounds, or overflow during its computation.
    Preconditions: len(candies) >= 1, len(candies) <= 100000, for every i with 0 <= i < len(candies), 1 <= candies[i] <= 10000000, and 1 <= k <= 1000000000000. -/
  theorem spec_2 (candies : Slice Std.I64) (k : Std.I64)
      (h_len_pos : 1 ≤ candies.length) (h_len_le : candies.length ≤ 100000)
      (h_elem : ∀ c ∈ intsOf candies, 1 ≤ c ∧ c ≤ 10000000)
      (h_k : 1 ≤ k.val ∧ k.val ≤ 1000000000000) :
      ∃ r : Std.I64, Aegis.MaximumCandies.maximum_candies candies k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (candies : Slice Std.I64) (k : Std.I64)
        (h_len_pos : 1 ≤ candies.length) (h_len_le : candies.length ≤ 100000)
        (h_elem : ∀ c ∈ intsOf candies, 1 ≤ c ∧ c ≤ 10000000)
        (h_k : 1 ≤ k.val ∧ k.val ≤ 1000000000000), ∃ r : Std.I64, Aegis.MaximumCandies.maximum_candies candies k = ok r) := by
    sorry

  /-- Let M be the maximum value among candies[0],...,candies[n-1], where n = len(candies). Whenever the function returns a result r, r <= M.
    Preconditions: len(candies) >= 1, len(candies) <= 100000, for every i with 0 <= i < len(candies), 1 <= candies[i] <= 10000000, and 1 <= k <= 1000000000000. -/
  theorem spec_3 (candies : Slice Std.I64) (k : Std.I64)
      (h_len_pos : 1 ≤ candies.length) (h_len_le : candies.length ≤ 100000)
      (h_elem : ∀ c ∈ intsOf candies, 1 ≤ c ∧ c ≤ 10000000)
      (h_k : 1 ≤ k.val ∧ k.val ≤ 1000000000000) :
      ∀ r : Std.I64,
        Aegis.MaximumCandies.maximum_candies candies k = ok r → r.val ≤ maxCandy candies := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (candies : Slice Std.I64) (k : Std.I64)
        (h_len_pos : 1 ≤ candies.length) (h_len_le : candies.length ≤ 100000)
        (h_elem : ∀ c ∈ intsOf candies, 1 ≤ c ∧ c ≤ 10000000)
        (h_k : 1 ≤ k.val ∧ k.val ≤ 1000000000000), ∀ r : Std.I64,
          Aegis.MaximumCandies.maximum_candies candies k = ok r → r.val ≤ maxCandy candies) := by
    sorry

  /-- Let n = len(candies). Whenever the function returns a result r, as mathematical integers, k * r <= the sum over i = 0,...,n-1 of candies[i].
    Preconditions: len(candies) >= 1, len(candies) <= 100000, for every i with 0 <= i < len(candies), 1 <= candies[i] <= 10000000, and 1 <= k <= 1000000000000. -/
  theorem spec_4 (candies : Slice Std.I64) (k : Std.I64)
      (h_len_pos : 1 ≤ candies.length) (h_len_le : candies.length ≤ 100000)
      (h_elem : ∀ c ∈ intsOf candies, 1 ≤ c ∧ c ≤ 10000000)
      (h_k : 1 ≤ k.val ∧ k.val ≤ 1000000000000) :
      ∀ r : Std.I64,
        Aegis.MaximumCandies.maximum_candies candies k = ok r →
          k.val * r.val ≤ totalCandies candies := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (candies : Slice Std.I64) (k : Std.I64)
        (h_len_pos : 1 ≤ candies.length) (h_len_le : candies.length ≤ 100000)
        (h_elem : ∀ c ∈ intsOf candies, 1 ≤ c ∧ c ≤ 10000000)
        (h_k : 1 ≤ k.val ∧ k.val ≤ 1000000000000), ∀ r : Std.I64,
          Aegis.MaximumCandies.maximum_candies candies k = ok r →
            k.val * r.val ≤ totalCandies candies) := by
    sorry

  /-- Let n = len(candies). Whenever the function returns a result r, r = 0 if and only if the sum over i = 0,...,n-1 of candies[i] is less than k.
    Preconditions: len(candies) >= 1, len(candies) <= 100000, for every i with 0 <= i < len(candies), 1 <= candies[i] <= 10000000, and 1 <= k <= 1000000000000. -/
  theorem spec_5 (candies : Slice Std.I64) (k : Std.I64)
      (h_len_pos : 1 ≤ candies.length) (h_len_le : candies.length ≤ 100000)
      (h_elem : ∀ c ∈ intsOf candies, 1 ≤ c ∧ c ≤ 10000000)
      (h_k : 1 ≤ k.val ∧ k.val ≤ 1000000000000) :
      ∀ r : Std.I64,
        Aegis.MaximumCandies.maximum_candies candies k = ok r →
          (r.val = 0 ↔ totalCandies candies < k.val) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (candies : Slice Std.I64) (k : Std.I64)
        (h_len_pos : 1 ≤ candies.length) (h_len_le : candies.length ≤ 100000)
        (h_elem : ∀ c ∈ intsOf candies, 1 ≤ c ∧ c ≤ 10000000)
        (h_k : 1 ≤ k.val ∧ k.val ≤ 1000000000000), ∀ r : Std.I64,
          Aegis.MaximumCandies.maximum_candies candies k = ok r →
            (r.val = 0 ↔ totalCandies candies < k.val)) := by
    sorry

  /-- Whenever the function returns a result r, r = 1.
    Preconditions: len(candies) >= 1, len(candies) <= 100000, for every i with 0 <= i < len(candies), 1 <= candies[i] <= 10000000, 1 <= k <= 1000000000000, and the sum over i = 0,...,len(candies)-1 of candies[i] equals k. -/
  theorem spec_6 (candies : Slice Std.I64) (k : Std.I64)
      (h_len_pos : 1 ≤ candies.length) (h_len_le : candies.length ≤ 100000)
      (h_elem : ∀ c ∈ intsOf candies, 1 ≤ c ∧ c ≤ 10000000)
      (h_k : 1 ≤ k.val ∧ k.val ≤ 1000000000000)
      (h_sum : totalCandies candies = k.val) :
      ∀ r : Std.I64, Aegis.MaximumCandies.maximum_candies candies k = ok r → r.val = 1 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (candies : Slice Std.I64) (k : Std.I64)
        (h_len_pos : 1 ≤ candies.length) (h_len_le : candies.length ≤ 100000)
        (h_elem : ∀ c ∈ intsOf candies, 1 ≤ c ∧ c ≤ 10000000)
        (h_k : 1 ≤ k.val ∧ k.val ≤ 1000000000000)
        (h_sum : totalCandies candies = k.val), ∀ r : Std.I64, Aegis.MaximumCandies.maximum_candies candies k = ok r → r.val = 1) := by
    sorry

  /-- Let M be the maximum value among candies[0],...,candies[n-1], where n = len(candies). Whenever the function returns a result r, r = M.
    Preconditions: len(candies) >= 1, len(candies) <= 100000, for every i with 0 <= i < len(candies), 1 <= candies[i] <= 10000000, and k = 1. -/
  theorem spec_7 (candies : Slice Std.I64) (k : Std.I64)
      (h_len_pos : 1 ≤ candies.length) (h_len_le : candies.length ≤ 100000)
      (h_elem : ∀ c ∈ intsOf candies, 1 ≤ c ∧ c ≤ 10000000)
      (h_k : k.val = 1) :
      ∀ r : Std.I64,
        Aegis.MaximumCandies.maximum_candies candies k = ok r → r.val = maxCandy candies := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (candies : Slice Std.I64) (k : Std.I64)
        (h_len_pos : 1 ≤ candies.length) (h_len_le : candies.length ≤ 100000)
        (h_elem : ∀ c ∈ intsOf candies, 1 ≤ c ∧ c ≤ 10000000)
        (h_k : k.val = 1), ∀ r : Std.I64,
          Aegis.MaximumCandies.maximum_candies candies k = ok r → r.val = maxCandy candies) := by
    sorry

  /-- Whenever the function returns a result r, r = floor(candies[0] / k).
    Preconditions: len(candies) = 1, 1 <= candies[0] <= 10000000, and 1 <= k <= 1000000000000. -/
  theorem spec_8 (candies : Slice Std.I64) (k : Std.I64)
      (h_len : candies.length = 1)
      (h_elem0 : 1 ≤ elem candies 0 ∧ elem candies 0 ≤ 10000000)
      (h_k : 1 ≤ k.val ∧ k.val ≤ 1000000000000) :
      ∀ r : Std.I64,
        Aegis.MaximumCandies.maximum_candies candies k = ok r → r.val = elem candies 0 / k.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (candies : Slice Std.I64) (k : Std.I64)
        (h_len : candies.length = 1)
        (h_elem0 : 1 ≤ elem candies 0 ∧ elem candies 0 ≤ 10000000)
        (h_k : 1 ≤ k.val ∧ k.val ≤ 1000000000000), ∀ r : Std.I64,
          Aegis.MaximumCandies.maximum_candies candies k = ok r → r.val = elem candies 0 / k.val) := by
    sorry

  /-- Let n = len(candies). Whenever the function returns a result r with r > 0, there exist nonnegative integers a_0,...,a_{n-1} such that the sum over i = 0,...,n-1 of a_i equals k, and for every i with 0 <= i < n, a_i * r <= candies[i].
    Preconditions: len(candies) >= 1, len(candies) <= 100000, for every i with 0 <= i < len(candies), 1 <= candies[i] <= 10000000, and 1 <= k <= 1000000000000. -/
  theorem spec_9 (candies : Slice Std.I64) (k : Std.I64)
      (h_len_pos : 1 ≤ candies.length) (h_len_le : candies.length ≤ 100000)
      (h_elem : ∀ c ∈ intsOf candies, 1 ≤ c ∧ c ≤ 10000000)
      (h_k : 1 ≤ k.val ∧ k.val ≤ 1000000000000) :
      ∀ r : Std.I64, Aegis.MaximumCandies.maximum_candies candies k = ok r → 0 < r.val →
        ∃ a : List ℤ, a.length = candies.length ∧ a.sum = k.val ∧
          ∀ i : ℕ, i < a.length → 0 ≤ a.getD i 0 ∧ a.getD i 0 * r.val ≤ elem candies i := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (candies : Slice Std.I64) (k : Std.I64)
        (h_len_pos : 1 ≤ candies.length) (h_len_le : candies.length ≤ 100000)
        (h_elem : ∀ c ∈ intsOf candies, 1 ≤ c ∧ c ≤ 10000000)
        (h_k : 1 ≤ k.val ∧ k.val ≤ 1000000000000), ∀ r : Std.I64, Aegis.MaximumCandies.maximum_candies candies k = ok r → 0 < r.val →
          ∃ a : List ℤ, a.length = candies.length ∧ a.sum = k.val ∧
            ∀ i : ℕ, i < a.length → 0 ≤ a.getD i 0 ∧ a.getD i 0 * r.val ≤ elem candies i) := by
    sorry

  /-- Let n = len(candies). Whenever the function returns a result r, if r > 0 then the sum over i = 0,...,n-1 of floor(candies[i] / r) is at least k.
    Preconditions: len(candies) >= 1, len(candies) <= 100000, for every i with 0 <= i < len(candies), 1 <= candies[i] <= 10000000, and 1 <= k <= 1000000000000. -/
  theorem spec_10 (candies : Slice Std.I64) (k : Std.I64)
      (h_len_pos : 1 ≤ candies.length) (h_len_le : candies.length ≤ 100000)
      (h_elem : ∀ c ∈ intsOf candies, 1 ≤ c ∧ c ≤ 10000000)
      (h_k : 1 ≤ k.val ∧ k.val ≤ 1000000000000) :
      ∀ r : Std.I64, Aegis.MaximumCandies.maximum_candies candies k = ok r → 0 < r.val →
        k.val ≤ countAt candies r.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (candies : Slice Std.I64) (k : Std.I64)
        (h_len_pos : 1 ≤ candies.length) (h_len_le : candies.length ≤ 100000)
        (h_elem : ∀ c ∈ intsOf candies, 1 ≤ c ∧ c ≤ 10000000)
        (h_k : 1 ≤ k.val ∧ k.val ≤ 1000000000000), ∀ r : Std.I64, Aegis.MaximumCandies.maximum_candies candies k = ok r → 0 < r.val →
          k.val ≤ countAt candies r.val) := by
    sorry

  /-- Let n = len(candies). Whenever the function returns a result r, for every integer y with r < y, the sum over i = 0,...,n-1 of floor(candies[i] / y) is less than k.
    Preconditions: len(candies) >= 1, len(candies) <= 100000, for every i with 0 <= i < len(candies), 1 <= candies[i] <= 10000000, and 1 <= k <= 1000000000000. -/
  theorem spec_11 (candies : Slice Std.I64) (k : Std.I64)
      (h_len_pos : 1 ≤ candies.length) (h_len_le : candies.length ≤ 100000)
      (h_elem : ∀ c ∈ intsOf candies, 1 ≤ c ∧ c ≤ 10000000)
      (h_k : 1 ≤ k.val ∧ k.val ≤ 1000000000000) :
      ∀ r : Std.I64, Aegis.MaximumCandies.maximum_candies candies k = ok r →
        ∀ y : ℤ, r.val < y → countAt candies y < k.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (candies : Slice Std.I64) (k : Std.I64)
        (h_len_pos : 1 ≤ candies.length) (h_len_le : candies.length ≤ 100000)
        (h_elem : ∀ c ∈ intsOf candies, 1 ≤ c ∧ c ≤ 10000000)
        (h_k : 1 ≤ k.val ∧ k.val ≤ 1000000000000), ∀ r : Std.I64, Aegis.MaximumCandies.maximum_candies candies k = ok r →
          ∀ y : ℤ, r.val < y → countAt candies y < k.val) := by
    sorry

  /-- Let n = len(candies). Whenever the function returns a result r, for every integer y with 0 < y <= r, the sum over i = 0,...,n-1 of floor(candies[i] / y) is at least k.
    Preconditions: len(candies) >= 1, len(candies) <= 100000, for every i with 0 <= i < len(candies), 1 <= candies[i] <= 10000000, and 1 <= k <= 1000000000000. -/
  theorem spec_12 (candies : Slice Std.I64) (k : Std.I64)
      (h_len_pos : 1 ≤ candies.length) (h_len_le : candies.length ≤ 100000)
      (h_elem : ∀ c ∈ intsOf candies, 1 ≤ c ∧ c ≤ 10000000)
      (h_k : 1 ≤ k.val ∧ k.val ≤ 1000000000000) :
      ∀ r : Std.I64, Aegis.MaximumCandies.maximum_candies candies k = ok r →
        ∀ y : ℤ, 0 < y → y ≤ r.val → k.val ≤ countAt candies y := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (candies : Slice Std.I64) (k : Std.I64)
        (h_len_pos : 1 ≤ candies.length) (h_len_le : candies.length ≤ 100000)
        (h_elem : ∀ c ∈ intsOf candies, 1 ≤ c ∧ c ≤ 10000000)
        (h_k : 1 ≤ k.val ∧ k.val ≤ 1000000000000), ∀ r : Std.I64, Aegis.MaximumCandies.maximum_candies candies k = ok r →
          ∀ y : ℤ, 0 < y → y ≤ r.val → k.val ≤ countAt candies y) := by
    sorry

  end AegisSpec.MaximumCandies
