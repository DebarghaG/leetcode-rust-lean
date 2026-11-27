import Aegis.GetFinalState.Code.Funs

/-!
# Specifications of `Aegis.GetFinalState.get_final_state`

LeetCode problem `final-array-state-after-k-multiplication-operations-i`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  open Aegis.GetFinalState

  namespace AegisSpec.GetFinalState

  def sliceVals (nums : Slice Std.I64) : List ℤ := nums.val.map (fun x => x.val)

  def vecVals (res : alloc.vec.Vec Std.I64) : List ℤ := res.val.map (fun x => x.val)

  def listMin (l : List ℤ) : ℤ := l.foldr min (l.headD 0)

  def IsFirstMinIdx (l : List ℤ) (m : ℕ) : Prop :=
    m < l.length ∧
      (∀ j, j < l.length → l[m]! ≤ l[j]!) ∧
      (∀ j, j < m → l[m]! < l[j]!)

  def IterStep (l : List ℤ) (mult : ℤ) (l' : List ℤ) : Prop :=
    ∀ m, IsFirstMinIdx l m → l' = l.set m (l[m]! * mult)

  def IterSeq (si : List ℤ) (mult : ℤ) (k : ℕ) (a : ℕ → List ℤ) : Prop :=
    (∀ t, t ≤ k → (a t).length = si.length) ∧
      a 0 = si ∧
      (∀ t, t < k → IterStep (a t) mult (a (t + 1)))

  /-- The function returns a result r and there exists a sequence of arrays a_0, a_1, ..., a_k, each of length n, such that: (1) for every i with 0 <= i < n, a_0[i] = nums[i]; (2) for every i with 0 <= i < n, r[i] = a_k[i]; (3) for every t with 0 <= t < k, if i_t is the smallest index such that a_t[i_t] = min_{0 <= j < n} a_t[j], then for every j with 0 <= j < n, a_{t+1}[j] = a_t[j] * multiplier if j = i_t, and a_{t+1}[j] = a_t[j] otherwise.
    Preconditions: n = len(nums); 1 <= n <= 100; for every i with 0 <= i < n, 1 <= nums[i] <= 100; 1 <= k <= 10; 1 <= multiplier <= 5. -/
  theorem spec_1
      (nums : Slice Std.I64) (k multiplier : Std.I64) (n : ℕ)
      (hn : n = nums.val.length)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
      (hnums : ∀ i, i < n → 1 ≤ (sliceVals nums)[i]! ∧ (sliceVals nums)[i]! ≤ 100)
      (hk : 1 ≤ k.val) (hk_le : k.val ≤ 10)
      (hmult : 1 ≤ multiplier.val) (hmult_le : multiplier.val ≤ 5) :
      ∃ r : alloc.vec.Vec Std.I64,
        get_final_state nums k multiplier = ok r ∧
          ∃ a : ℕ → List ℤ,
            IterSeq (sliceVals nums) multiplier.val k.val.toNat a ∧
              (∀ t, t ≤ k.val.toNat → (a t).length = n) ∧
              (∀ i, i < n → (vecVals r)[i]! = (a k.val.toNat)[i]!) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (k multiplier : Std.I64) (n : ℕ)
        (hn : n = nums.val.length)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
        (hnums : ∀ i, i < n → 1 ≤ (sliceVals nums)[i]! ∧ (sliceVals nums)[i]! ≤ 100)
        (hk : 1 ≤ k.val) (hk_le : k.val ≤ 10)
        (hmult : 1 ≤ multiplier.val) (hmult_le : multiplier.val ≤ 5), ∃ r : alloc.vec.Vec Std.I64,
          get_final_state nums k multiplier = ok r ∧
            ∃ a : ℕ → List ℤ,
              IterSeq (sliceVals nums) multiplier.val k.val.toNat a ∧
                (∀ t, t ≤ k.val.toNat → (a t).length = n) ∧
                (∀ i, i < n → (vecVals r)[i]! = (a k.val.toNat)[i]!)) := by
    sorry

  /-- Whenever the function returns a result r, len(r) = len(nums).
    Preconditions: n = len(nums); 1 <= n <= 100; for every i with 0 <= i < n, 1 <= nums[i] <= 100; 1 <= k <= 10; 1 <= multiplier <= 5. -/
  theorem spec_2
      (nums : Slice Std.I64) (k multiplier : Std.I64) (n : ℕ)
      (hn : n = nums.val.length)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
      (hnums : ∀ i, i < n → 1 ≤ (sliceVals nums)[i]! ∧ (sliceVals nums)[i]! ≤ 100)
      (hk : 1 ≤ k.val) (hk_le : k.val ≤ 10)
      (hmult : 1 ≤ multiplier.val) (hmult_le : multiplier.val ≤ 5) :
      ∀ r : alloc.vec.Vec Std.I64,
        get_final_state nums k multiplier = ok r → r.val.length = nums.val.length := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (k multiplier : Std.I64) (n : ℕ)
        (hn : n = nums.val.length)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
        (hnums : ∀ i, i < n → 1 ≤ (sliceVals nums)[i]! ∧ (sliceVals nums)[i]! ≤ 100)
        (hk : 1 ≤ k.val) (hk_le : k.val ≤ 10)
        (hmult : 1 ≤ multiplier.val) (hmult_le : multiplier.val ≤ 5), ∀ r : alloc.vec.Vec Std.I64,
          get_final_state nums k multiplier = ok r → r.val.length = nums.val.length) := by
    sorry

  /-- The function returns a result r for every input satisfying the preconditions (it does not overflow, panic, or go out of bounds).
    Preconditions: n = len(nums); 1 <= n <= 100; for every i with 0 <= i < n, 1 <= nums[i] <= 100; 1 <= k <= 10; 1 <= multiplier <= 5. -/
  theorem spec_3
      (nums : Slice Std.I64) (k multiplier : Std.I64) (n : ℕ)
      (hn : n = nums.val.length)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
      (hnums : ∀ i, i < n → 1 ≤ (sliceVals nums)[i]! ∧ (sliceVals nums)[i]! ≤ 100)
      (hk : 1 ≤ k.val) (hk_le : k.val ≤ 10)
      (hmult : 1 ≤ multiplier.val) (hmult_le : multiplier.val ≤ 5) :
      ∃ r : alloc.vec.Vec Std.I64, get_final_state nums k multiplier = ok r := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (k multiplier : Std.I64) (n : ℕ)
        (hn : n = nums.val.length)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
        (hnums : ∀ i, i < n → 1 ≤ (sliceVals nums)[i]! ∧ (sliceVals nums)[i]! ≤ 100)
        (hk : 1 ≤ k.val) (hk_le : k.val ≤ 10)
        (hmult : 1 ≤ multiplier.val) (hmult_le : multiplier.val ≤ 5), ∃ r : alloc.vec.Vec Std.I64, get_final_state nums k multiplier = ok r) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(nums), nums[i] <= r[i] <= nums[i] * multiplier^k.
    Preconditions: n = len(nums); 1 <= n <= 100; for every i with 0 <= i < n, 1 <= nums[i] <= 100; 1 <= k <= 10; 1 <= multiplier <= 5. -/
  theorem spec_4
      (nums : Slice Std.I64) (k multiplier : Std.I64) (n : ℕ)
      (hn : n = nums.val.length)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
      (hnums : ∀ i, i < n → 1 ≤ (sliceVals nums)[i]! ∧ (sliceVals nums)[i]! ≤ 100)
      (hk : 1 ≤ k.val) (hk_le : k.val ≤ 10)
      (hmult : 1 ≤ multiplier.val) (hmult_le : multiplier.val ≤ 5) :
      ∀ r : alloc.vec.Vec Std.I64,
        get_final_state nums k multiplier = ok r →
          ∀ i, i < n →
            (sliceVals nums)[i]! ≤ (vecVals r)[i]! ∧
              (vecVals r)[i]! ≤ (sliceVals nums)[i]! * multiplier.val ^ k.val.toNat := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (k multiplier : Std.I64) (n : ℕ)
        (hn : n = nums.val.length)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
        (hnums : ∀ i, i < n → 1 ≤ (sliceVals nums)[i]! ∧ (sliceVals nums)[i]! ≤ 100)
        (hk : 1 ≤ k.val) (hk_le : k.val ≤ 10)
        (hmult : 1 ≤ multiplier.val) (hmult_le : multiplier.val ≤ 5), ∀ r : alloc.vec.Vec Std.I64,
          get_final_state nums k multiplier = ok r →
            ∀ i, i < n →
              (sliceVals nums)[i]! ≤ (vecVals r)[i]! ∧
                (vecVals r)[i]! ≤ (sliceVals nums)[i]! * multiplier.val ^ k.val.toNat) := by
    sorry

  /-- Whenever the function returns a result r, there exist nonnegative integers c_0, c_1, ..., c_{n-1} (where n = len(nums)) such that for every i with 0 <= i < n, r[i] = nums[i] * multiplier^{c_i}, and sum_{i=0}^{n-1} c_i = k.
    Preconditions: n = len(nums); 1 <= n <= 100; for every i with 0 <= i < n, 1 <= nums[i] <= 100; 1 <= k <= 10; 1 <= multiplier <= 5. -/
  theorem spec_5
      (nums : Slice Std.I64) (k multiplier : Std.I64) (n : ℕ)
      (hn : n = nums.val.length)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
      (hnums : ∀ i, i < n → 1 ≤ (sliceVals nums)[i]! ∧ (sliceVals nums)[i]! ≤ 100)
      (hk : 1 ≤ k.val) (hk_le : k.val ≤ 10)
      (hmult : 1 ≤ multiplier.val) (hmult_le : multiplier.val ≤ 5) :
      ∀ r : alloc.vec.Vec Std.I64,
        get_final_state nums k multiplier = ok r →
          ∃ c : ℕ → ℕ,
            (∀ i, i < n → (vecVals r)[i]! = (sliceVals nums)[i]! * multiplier.val ^ (c i)) ∧
              (Finset.sum (Finset.range n) fun i => c i) = k.val.toNat := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (k multiplier : Std.I64) (n : ℕ)
        (hn : n = nums.val.length)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
        (hnums : ∀ i, i < n → 1 ≤ (sliceVals nums)[i]! ∧ (sliceVals nums)[i]! ≤ 100)
        (hk : 1 ≤ k.val) (hk_le : k.val ≤ 10)
        (hmult : 1 ≤ multiplier.val) (hmult_le : multiplier.val ≤ 5), ∀ r : alloc.vec.Vec Std.I64,
          get_final_state nums k multiplier = ok r →
            ∃ c : ℕ → ℕ,
              (∀ i, i < n → (vecVals r)[i]! = (sliceVals nums)[i]! * multiplier.val ^ (c i)) ∧
                (Finset.sum (Finset.range n) fun i => c i) = k.val.toNat) := by
    sorry

  /-- Whenever the function returns a result r, there exist nonnegative integers c_0, c_1, ..., c_{n-1} (where n = len(nums)) such that for every i with 0 <= i < n, r[i] = nums[i] * multiplier^{c_i}, sum_{i=0}^{n-1} c_i = k, and for every i with c_i > 0 and every j with 0 <= j < n, nums[i] * multiplier^{c_i - 1} <= r[j].
    Preconditions: n = len(nums); 1 <= n <= 100; for every i with 0 <= i < n, 1 <= nums[i] <= 100; 1 <= k <= 10; 1 <= multiplier <= 5. -/
  theorem spec_6
      (nums : Slice Std.I64) (k multiplier : Std.I64) (n : ℕ)
      (hn : n = nums.val.length)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
      (hnums : ∀ i, i < n → 1 ≤ (sliceVals nums)[i]! ∧ (sliceVals nums)[i]! ≤ 100)
      (hk : 1 ≤ k.val) (hk_le : k.val ≤ 10)
      (hmult : 1 ≤ multiplier.val) (hmult_le : multiplier.val ≤ 5) :
      ∀ r : alloc.vec.Vec Std.I64,
        get_final_state nums k multiplier = ok r →
          ∃ c : ℕ → ℕ,
            (∀ i, i < n → (vecVals r)[i]! = (sliceVals nums)[i]! * multiplier.val ^ (c i)) ∧
              (Finset.sum (Finset.range n) fun i => c i) = k.val.toNat ∧
                (∀ i, i < n → 0 < c i → ∀ j, j < n →
                  (sliceVals nums)[i]! * multiplier.val ^ (c i - 1) ≤ (vecVals r)[j]!) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (k multiplier : Std.I64) (n : ℕ)
        (hn : n = nums.val.length)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
        (hnums : ∀ i, i < n → 1 ≤ (sliceVals nums)[i]! ∧ (sliceVals nums)[i]! ≤ 100)
        (hk : 1 ≤ k.val) (hk_le : k.val ≤ 10)
        (hmult : 1 ≤ multiplier.val) (hmult_le : multiplier.val ≤ 5), ∀ r : alloc.vec.Vec Std.I64,
          get_final_state nums k multiplier = ok r →
            ∃ c : ℕ → ℕ,
              (∀ i, i < n → (vecVals r)[i]! = (sliceVals nums)[i]! * multiplier.val ^ (c i)) ∧
                (Finset.sum (Finset.range n) fun i => c i) = k.val.toNat ∧
                  (∀ i, i < n → 0 < c i → ∀ j, j < n →
                    (sliceVals nums)[i]! * multiplier.val ^ (c i - 1) ≤ (vecVals r)[j]!)) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < n, r[i] = nums[i].
    Preconditions: n = len(nums); 1 <= n <= 100; for every i with 0 <= i < n, 1 <= nums[i] <= 100; 1 <= k <= 10; multiplier = 1. -/
  theorem spec_7
      (nums : Slice Std.I64) (k multiplier : Std.I64) (n : ℕ)
      (hn : n = nums.val.length)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
      (hnums : ∀ i, i < n → 1 ≤ (sliceVals nums)[i]! ∧ (sliceVals nums)[i]! ≤ 100)
      (hk : 1 ≤ k.val) (hk_le : k.val ≤ 10)
      (hmult : multiplier.val = 1) :
      ∀ r : alloc.vec.Vec Std.I64,
        get_final_state nums k multiplier = ok r →
          ∀ i, i < n → (vecVals r)[i]! = (sliceVals nums)[i]! := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (k multiplier : Std.I64) (n : ℕ)
        (hn : n = nums.val.length)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
        (hnums : ∀ i, i < n → 1 ≤ (sliceVals nums)[i]! ∧ (sliceVals nums)[i]! ≤ 100)
        (hk : 1 ≤ k.val) (hk_le : k.val ≤ 10)
        (hmult : multiplier.val = 1), ∀ r : alloc.vec.Vec Std.I64,
          get_final_state nums k multiplier = ok r →
            ∀ i, i < n → (vecVals r)[i]! = (sliceVals nums)[i]!) := by
    sorry

  /-- Whenever the function returns a result r, r[0] = nums[0] * multiplier^k.
    Preconditions: n = len(nums); n = 1; 1 <= nums[0] <= 100; 1 <= k <= 10; 1 <= multiplier <= 5. -/
  theorem spec_8
      (nums : Slice Std.I64) (k multiplier : Std.I64) (n : ℕ)
      (hn : n = nums.val.length)
      (hn_one : n = 1)
      (hnums_pos : 1 ≤ (sliceVals nums)[0]!)
      (hnums_le : (sliceVals nums)[0]! ≤ 100)
      (hk : 1 ≤ k.val) (hk_le : k.val ≤ 10)
      (hmult : 1 ≤ multiplier.val) (hmult_le : multiplier.val ≤ 5) :
      ∀ r : alloc.vec.Vec Std.I64,
        get_final_state nums k multiplier = ok r →
          (vecVals r)[0]! = (sliceVals nums)[0]! * multiplier.val ^ k.val.toNat := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (k multiplier : Std.I64) (n : ℕ)
        (hn : n = nums.val.length)
        (hn_one : n = 1)
        (hnums_pos : 1 ≤ (sliceVals nums)[0]!)
        (hnums_le : (sliceVals nums)[0]! ≤ 100)
        (hk : 1 ≤ k.val) (hk_le : k.val ≤ 10)
        (hmult : 1 ≤ multiplier.val) (hmult_le : multiplier.val ≤ 5), ∀ r : alloc.vec.Vec Std.I64,
          get_final_state nums k multiplier = ok r →
            (vecVals r)[0]! = (sliceVals nums)[0]! * multiplier.val ^ k.val.toNat) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < n, if i < k then r[i] = nums[i] * multiplier, and if i >= k then r[i] = nums[i].
    Preconditions: n = len(nums); 1 <= n <= 100; for every i with 0 <= i < n, 1 <= nums[i] <= 100; there exists v such that for every i with 0 <= i < n, nums[i] = v; 1 <= k <= n; 1 <= multiplier <= 5. -/
  theorem spec_9
      (nums : Slice Std.I64) (k multiplier : Std.I64) (n : ℕ)
      (hn : n = nums.val.length)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
      (hnums : ∀ i, i < n → 1 ≤ (sliceVals nums)[i]! ∧ (sliceVals nums)[i]! ≤ 100)
      (hnums_const : ∃ v, ∀ i, i < n → (sliceVals nums)[i]! = v)
      (hk : 1 ≤ k.val) (hk_le : k.val ≤ n)
      (hmult : 1 ≤ multiplier.val) (hmult_le : multiplier.val ≤ 5) :
      ∀ r : alloc.vec.Vec Std.I64,
        get_final_state nums k multiplier = ok r →
          ∀ i, i < n →
            (i < k.val.toNat → (vecVals r)[i]! = (sliceVals nums)[i]! * multiplier.val) ∧
              (k.val.toNat ≤ i → (vecVals r)[i]! = (sliceVals nums)[i]!) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64) (k multiplier : Std.I64) (n : ℕ)
        (hn : n = nums.val.length)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
        (hnums : ∀ i, i < n → 1 ≤ (sliceVals nums)[i]! ∧ (sliceVals nums)[i]! ≤ 100)
        (hnums_const : ∃ v, ∀ i, i < n → (sliceVals nums)[i]! = v)
        (hk : 1 ≤ k.val) (hk_le : k.val ≤ n)
        (hmult : 1 ≤ multiplier.val) (hmult_le : multiplier.val ≤ 5), ∀ r : alloc.vec.Vec Std.I64,
          get_final_state nums k multiplier = ok r →
            ∀ i, i < n →
              (i < k.val.toNat → (vecVals r)[i]! = (sliceVals nums)[i]! * multiplier.val) ∧
                (k.val.toNat ≤ i → (vecVals r)[i]! = (sliceVals nums)[i]!)) := by
    sorry

  /-- Whenever the function returns a result r and multiplier > 1 and k >= 1, there exists an index i with 0 <= i < n such that r[i] != nums[i] (in fact r[i] > nums[i]).
    Preconditions: n = len(nums); 1 <= n <= 100; for every i with 0 <= i < n, 1 <= nums[i] <= 100; 1 <= k <= 10; 1 <= multiplier <= 5. -/
  theorem spec_10
      (nums : Slice Std.I64) (k multiplier : Std.I64) (n : ℕ)
      (hn : n = nums.val.length)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
      (hnums : ∀ i, i < n → 1 ≤ (sliceVals nums)[i]! ∧ (sliceVals nums)[i]! ≤ 100)
      (hk : 1 ≤ k.val) (hk_le : k.val ≤ 10)
      (hmult : 1 ≤ multiplier.val) (hmult_le : multiplier.val ≤ 5) :
      ∀ r : alloc.vec.Vec Std.I64,
        get_final_state nums k multiplier = ok r → 1 < multiplier.val → 1 ≤ k.val →
          ∃ i, i < n ∧ (sliceVals nums)[i]! < (vecVals r)[i]! := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64) (k multiplier : Std.I64) (n : ℕ)
        (hn : n = nums.val.length)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
        (hnums : ∀ i, i < n → 1 ≤ (sliceVals nums)[i]! ∧ (sliceVals nums)[i]! ≤ 100)
        (hk : 1 ≤ k.val) (hk_le : k.val ≤ 10)
        (hmult : 1 ≤ multiplier.val) (hmult_le : multiplier.val ≤ 5), ∀ r : alloc.vec.Vec Std.I64,
          get_final_state nums k multiplier = ok r → 1 < multiplier.val → 1 ≤ k.val →
            ∃ i, i < n ∧ (sliceVals nums)[i]! < (vecVals r)[i]!) := by
    sorry

  /-- Whenever the function returns a result r, the number of indices i with 0 <= i < n such that r[i] != nums[i] is at most k.
    Preconditions: n = len(nums); 1 <= n <= 100; for every i with 0 <= i < n, 1 <= nums[i] <= 100; 1 <= k <= 10; 1 <= multiplier <= 5. -/
  theorem spec_11
      (nums : Slice Std.I64) (k multiplier : Std.I64) (n : ℕ)
      (hn : n = nums.val.length)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
      (hnums : ∀ i, i < n → 1 ≤ (sliceVals nums)[i]! ∧ (sliceVals nums)[i]! ≤ 100)
      (hk : 1 ≤ k.val) (hk_le : k.val ≤ 10)
      (hmult : 1 ≤ multiplier.val) (hmult_le : multiplier.val ≤ 5) :
      ∀ r : alloc.vec.Vec Std.I64,
        get_final_state nums k multiplier = ok r →
          ((List.range n).filter
              (fun i => (vecVals r)[i]! ≠ (sliceVals nums)[i]!)).length ≤ k.val.toNat := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64) (k multiplier : Std.I64) (n : ℕ)
        (hn : n = nums.val.length)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
        (hnums : ∀ i, i < n → 1 ≤ (sliceVals nums)[i]! ∧ (sliceVals nums)[i]! ≤ 100)
        (hk : 1 ≤ k.val) (hk_le : k.val ≤ 10)
        (hmult : 1 ≤ multiplier.val) (hmult_le : multiplier.val ≤ 5), ∀ r : alloc.vec.Vec Std.I64,
          get_final_state nums k multiplier = ok r →
            ((List.range n).filter
                (fun i => (vecVals r)[i]! ≠ (sliceVals nums)[i]!)).length ≤ k.val.toNat) := by
    sorry

  /-- Whenever the function returns a result r, let i* be the smallest index with 0 <= i* < n such that nums[i*] = min_{0 <= j < n} nums[j]. Then r[i*] = nums[i*] * multiplier, and for every j with 0 <= j < n and j != i*, r[j] = nums[j].
    Preconditions: n = len(nums); 1 <= n <= 100; for every i with 0 <= i < n, 1 <= nums[i] <= 100; k = 1; 1 <= multiplier <= 5. -/
  theorem spec_12
      (nums : Slice Std.I64) (k multiplier : Std.I64) (n : ℕ)
      (hn : n = nums.val.length)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
      (hnums : ∀ i, i < n → 1 ≤ (sliceVals nums)[i]! ∧ (sliceVals nums)[i]! ≤ 100)
      (hk : k.val = 1)
      (hmult : 1 ≤ multiplier.val) (hmult_le : multiplier.val ≤ 5) :
      ∀ r : alloc.vec.Vec Std.I64,
        get_final_state nums k multiplier = ok r →
          ∀ i0, IsFirstMinIdx (sliceVals nums) i0 →
            (vecVals r)[i0]! = (sliceVals nums)[i0]! * multiplier.val ∧
              (∀ j, j < n → j ≠ i0 → (vecVals r)[j]! = (sliceVals nums)[j]!) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice Std.I64) (k multiplier : Std.I64) (n : ℕ)
        (hn : n = nums.val.length)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
        (hnums : ∀ i, i < n → 1 ≤ (sliceVals nums)[i]! ∧ (sliceVals nums)[i]! ≤ 100)
        (hk : k.val = 1)
        (hmult : 1 ≤ multiplier.val) (hmult_le : multiplier.val ≤ 5), ∀ r : alloc.vec.Vec Std.I64,
          get_final_state nums k multiplier = ok r →
            ∀ i0, IsFirstMinIdx (sliceVals nums) i0 →
              (vecVals r)[i0]! = (sliceVals nums)[i0]! * multiplier.val ∧
                (∀ j, j < n → j ≠ i0 → (vecVals r)[j]! = (sliceVals nums)[j]!)) := by
    sorry

  /-- Whenever the function returns a result r, there exist nonnegative integers c_0, c_1, ..., c_{n-1} (where n = len(nums)) such that for every i with 0 <= i < n, r[i] = nums[i] * multiplier^{c_i}, sum_{i=0}^{n-1} c_i = k, and for every i, r[i] = nums[i] if and only if c_i = 0, and r[i] > nums[i] if and only if c_i > 0.
    Preconditions: n = len(nums); 1 <= n <= 100; for every i with 0 <= i < n, 1 <= nums[i] <= 100; 1 <= k <= 10; 1 <= multiplier <= 5; multiplier > 1. -/
  theorem spec_13
      (nums : Slice Std.I64) (k multiplier : Std.I64) (n : ℕ)
      (hn : n = nums.val.length)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
      (hnums : ∀ i, i < n → 1 ≤ (sliceVals nums)[i]! ∧ (sliceVals nums)[i]! ≤ 100)
      (hk : 1 ≤ k.val) (hk_le : k.val ≤ 10)
      (hmult : 1 ≤ multiplier.val) (hmult_le : multiplier.val ≤ 5)
      (hmult_gt : 1 < multiplier.val) :
      ∀ r : alloc.vec.Vec Std.I64,
        get_final_state nums k multiplier = ok r →
          ∃ c : ℕ → ℕ,
            (∀ i, i < n → (vecVals r)[i]! = (sliceVals nums)[i]! * multiplier.val ^ (c i)) ∧
              (Finset.sum (Finset.range n) fun i => c i) = k.val.toNat ∧
                (∀ i, i < n →
                  ((vecVals r)[i]! = (sliceVals nums)[i]! ↔ c i = 0) ∧
                    ((sliceVals nums)[i]! < (vecVals r)[i]! ↔ 0 < c i)) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums : Slice Std.I64) (k multiplier : Std.I64) (n : ℕ)
        (hn : n = nums.val.length)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
        (hnums : ∀ i, i < n → 1 ≤ (sliceVals nums)[i]! ∧ (sliceVals nums)[i]! ≤ 100)
        (hk : 1 ≤ k.val) (hk_le : k.val ≤ 10)
        (hmult : 1 ≤ multiplier.val) (hmult_le : multiplier.val ≤ 5)
        (hmult_gt : 1 < multiplier.val), ∀ r : alloc.vec.Vec Std.I64,
          get_final_state nums k multiplier = ok r →
            ∃ c : ℕ → ℕ,
              (∀ i, i < n → (vecVals r)[i]! = (sliceVals nums)[i]! * multiplier.val ^ (c i)) ∧
                (Finset.sum (Finset.range n) fun i => c i) = k.val.toNat ∧
                  (∀ i, i < n →
                    ((vecVals r)[i]! = (sliceVals nums)[i]! ↔ c i = 0) ∧
                      ((sliceVals nums)[i]! < (vecVals r)[i]! ↔ 0 < c i))) := by
    sorry

  /-- Let a_0, a_1, ..., a_k be the sequence of arrays described in S1 (which exists and is unique). For each t with 0 <= t <= k, let m_t = min_{0 <= j < n} a_t[j]. Then m_0 <= m_1 <= ... <= m_k.
    Preconditions: n = len(nums); 1 <= n <= 100; for every i with 0 <= i < n, 1 <= nums[i] <= 100; 1 <= k <= 10; 1 <= multiplier <= 5. -/
  theorem spec_14
      (nums : Slice Std.I64) (k multiplier : Std.I64) (n : ℕ)
      (hn : n = nums.val.length)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
      (hnums : ∀ i, i < n → 1 ≤ (sliceVals nums)[i]! ∧ (sliceVals nums)[i]! ≤ 100)
      (hk : 1 ≤ k.val) (hk_le : k.val ≤ 10)
      (hmult : 1 ≤ multiplier.val) (hmult_le : multiplier.val ≤ 5) :
      ∀ r : alloc.vec.Vec Std.I64,
        get_final_state nums k multiplier = ok r →
          ∀ a : ℕ → List ℤ,
            IterSeq (sliceVals nums) multiplier.val k.val.toNat a →
              (∀ i, i < n → (vecVals r)[i]! = (a k.val.toNat)[i]!) →
                ∀ t, t < k.val.toNat → listMin (a t) ≤ listMin (a (t + 1)) := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (nums : Slice Std.I64) (k multiplier : Std.I64) (n : ℕ)
        (hn : n = nums.val.length)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
        (hnums : ∀ i, i < n → 1 ≤ (sliceVals nums)[i]! ∧ (sliceVals nums)[i]! ≤ 100)
        (hk : 1 ≤ k.val) (hk_le : k.val ≤ 10)
        (hmult : 1 ≤ multiplier.val) (hmult_le : multiplier.val ≤ 5), ∀ r : alloc.vec.Vec Std.I64,
          get_final_state nums k multiplier = ok r →
            ∀ a : ℕ → List ℤ,
              IterSeq (sliceVals nums) multiplier.val k.val.toNat a →
                (∀ i, i < n → (vecVals r)[i]! = (a k.val.toNat)[i]!) →
                  ∀ t, t < k.val.toNat → listMin (a t) ≤ listMin (a (t + 1))) := by
    sorry

  end AegisSpec.GetFinalState
