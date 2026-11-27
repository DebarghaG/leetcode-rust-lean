import Aegis.MinCost.Code.Funs

/-!
# Specifications of `Aegis.MinCost.min_cost`

LeetCode problem `collecting-chocolates`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result ControlFlow Error
  open Aegis.MinCost

  namespace AegisSpec.MinCost

  def costs (nums : Slice I64) : List ℤ := nums.val.map (fun v => v.val)

  def cost (nums : Slice I64) (i : ℕ) : ℤ := (costs nums).getD i 0

  def length (nums : Slice I64) : ℕ := (costs nums).length

  def listMin : List ℤ → ℤ
    | [] => 0
    | a :: l => l.foldl (fun acc b => min acc b) a

  def InBounds (z : ℤ) : Prop := 1 ≤ z ∧ z ≤ 10 ^ 9

  def EntriesInBounds (nums : Slice I64) : Prop :=
    ∀ i, i < length nums → InBounds (cost nums i)

  def GeneralConstraints (nums : Slice I64) (x : I64) : Prop :=
    1 ≤ length nums ∧ length nums ≤ 1000 ∧ EntriesInBounds nums ∧ InBounds x.val

  def finSelfMap : (n : ℕ) → Fin n → Fin n
    | 0 => fun i => i.elim0
    | n + 1 => fun _ => ⟨0, Nat.succ_pos n⟩

  noncomputable def assignmentCost (c : List ℤ) (x : ℤ) (p : Fin c.length → Fin c.length) : ℤ :=
    (∑ j : Fin c.length, c.get (p j)) +
      x * ((Finset.univ.sup
        (fun j : Fin c.length => (j.val + c.length - (p j).val) % c.length) : ℕ) : ℤ)

  noncomputable def minAssignmentCost (c : List ℤ) (x : ℤ) : ℤ :=
    (Finset.univ : Finset (Fin c.length → Fin c.length)).inf'
      ⟨finSelfMap c.length, Finset.mem_univ _⟩ (fun p => assignmentCost c x p)

  def cyclicGet (c : List ℤ) (i : ℕ) : ℤ := c.getD (i % c.length) 0

  noncomputable def windowMin (c : List ℤ) (T j : ℕ) : ℤ :=
    (Finset.range (T + 1)).inf' ⟨0, Finset.mem_range.mpr (Nat.succ_pos T)⟩
      (fun d => cyclicGet c (j + c.length - d))

  noncomputable def windowCost (c : List ℤ) (x : ℤ) (T : ℕ) : ℤ :=
    x * (T : ℤ) + ∑ j ∈ Finset.range c.length, windowMin c T j

  noncomputable def minWindowCost (c : List ℤ) (x : ℤ) : ℤ :=
    listMin ((List.range c.length).map (fun T => windowCost c x T))

  /-- The function returns a result r and r = min_{p : {0,...,n-1} -> {0,...,n-1}} ( Σ_{j=0}^{n-1} nums[p(j)] + x * max_{j=0}^{n-1} ((j - p(j)) mod n) ), where n = len(nums) and (a mod n) denotes the remainder in {0,...,n-1}.
    Preconditions: The general constraints: 1 <= len(nums) <= 1000, for all i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9, and 1 <= x <= 10^9. -/
  theorem spec_1 (nums : Slice I64) (x : I64) (hgen : GeneralConstraints nums x) :
      ∃ r : I64,
        min_cost nums x = ok r ∧ r.val = minAssignmentCost (costs nums) x.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice I64) (x : I64) (hgen : GeneralConstraints nums x), ∃ r : I64,
          min_cost nums x = ok r ∧ r.val = minAssignmentCost (costs nums) x.val) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r (it does not fail).
    Preconditions: The general constraints: 1 <= len(nums) <= 1000, for all i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9, and 1 <= x <= 10^9. -/
  theorem spec_2 (nums : Slice I64) (x : I64) (hgen : GeneralConstraints nums x) :
      ∃ r : I64, min_cost nums x = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice I64) (x : I64) (hgen : GeneralConstraints nums x), ∃ r : I64, min_cost nums x = ok r) := by
    sorry

  /-- If the function returns a result r, then r >= n * min_{0 <= i < n} nums[i], where n = len(nums).
    Preconditions: The general constraints: 1 <= len(nums) <= 1000, for all i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9, and 1 <= x <= 10^9. -/
  theorem spec_3 (nums : Slice I64) (x : I64) (hgen : GeneralConstraints nums x) :
      ∀ r : I64, min_cost nums x = ok r →
        (length nums : ℤ) * listMin (costs nums) ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice I64) (x : I64) (hgen : GeneralConstraints nums x), ∀ r : I64, min_cost nums x = ok r →
          (length nums : ℤ) * listMin (costs nums) ≤ r.val) := by
    sorry

  /-- If the function returns a result r, then r <= Σ_{i=0}^{n-1} nums[i], where n = len(nums).
    Preconditions: The general constraints: 1 <= len(nums) <= 1000, for all i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9, and 1 <= x <= 10^9. -/
  theorem spec_4 (nums : Slice I64) (x : I64) (hgen : GeneralConstraints nums x) :
      ∀ r : I64, min_cost nums x = ok r → r.val ≤ (costs nums).sum := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice I64) (x : I64) (hgen : GeneralConstraints nums x), ∀ r : I64, min_cost nums x = ok r → r.val ≤ (costs nums).sum) := by
    sorry

  /-- If the function returns a result r, then r <= n * min_{0 <= i < n} nums[i] + x * (n - 1), where n = len(nums).
    Preconditions: The general constraints: 1 <= len(nums) <= 1000, for all i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9, and 1 <= x <= 10^9. -/
  theorem spec_5 (nums : Slice I64) (x : I64) (hgen : GeneralConstraints nums x) :
      ∀ r : I64, min_cost nums x = ok r →
        r.val ≤ (length nums : ℤ) * listMin (costs nums) + x.val * ((length nums : ℤ) - 1) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice I64) (x : I64) (hgen : GeneralConstraints nums x), ∀ r : I64, min_cost nums x = ok r →
          r.val ≤ (length nums : ℤ) * listMin (costs nums) + x.val * ((length nums : ℤ) - 1)) := by
    sorry

  /-- The function returns a result r and r = nums[0].
    Preconditions: len(nums) = 1, and the general constraints: 1 <= nums[0] <= 10^9, and 1 <= x <= 10^9. -/
  theorem spec_6 (nums : Slice I64) (x : I64) (hlen : length nums = 1)
      (h0 : InBounds (cost nums 0)) (hx : InBounds x.val) :
      ∃ r : I64, min_cost nums x = ok r ∧ r.val = cost nums 0 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice I64) (x : I64) (hlen : length nums = 1)
        (h0 : InBounds (cost nums 0)) (hx : InBounds x.val), ∃ r : I64, min_cost nums x = ok r ∧ r.val = cost nums 0) := by
    sorry

  /-- The function returns a result r and r = min( nums[0] + nums[1], 2 * min(nums[0], nums[1]) + x ).
    Preconditions: len(nums) = 2, and the general constraints: 1 <= nums[0], nums[1] <= 10^9, and 1 <= x <= 10^9. -/
  theorem spec_7 (nums : Slice I64) (x : I64) (hlen : length nums = 2)
      (h0 : InBounds (cost nums 0)) (h1 : InBounds (cost nums 1)) (hx : InBounds x.val) :
      ∃ r : I64,
        min_cost nums x = ok r ∧
          r.val = min (cost nums 0 + cost nums 1)
            (2 * min (cost nums 0) (cost nums 1) + x.val) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice I64) (x : I64) (hlen : length nums = 2)
        (h0 : InBounds (cost nums 0)) (h1 : InBounds (cost nums 1)) (hx : InBounds x.val), ∃ r : I64,
          min_cost nums x = ok r ∧
            r.val = min (cost nums 0 + cost nums 1)
              (2 * min (cost nums 0) (cost nums 1) + x.val)) := by
    sorry

  /-- The function returns a result r and r = n * c, where n = len(nums).
    Preconditions: The general constraints: 1 <= len(nums) <= 1000, 1 <= x <= 10^9, and there exists an integer c such that for all 0 <= i < len(nums), nums[i] = c (with 1 <= c <= 10^9). -/
  theorem spec_8 (nums : Slice I64) (x : I64)
      (hnpos : 1 ≤ length nums) (hnle : length nums ≤ 1000) (hx : InBounds x.val)
      (c : ℤ) (hc : ∀ i, i < length nums → cost nums i = c) (hc1 : 1 ≤ c) (hc2 : c ≤ 10 ^ 9) :
      ∃ r : I64, min_cost nums x = ok r ∧ r.val = (length nums : ℤ) * c := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice I64) (x : I64)
        (hnpos : 1 ≤ length nums) (hnle : length nums ≤ 1000) (hx : InBounds x.val)
        (c : ℤ) (hc : ∀ i, i < length nums → cost nums i = c) (hc1 : 1 ≤ c) (hc2 : c ≤ 10 ^ 9), ∃ r : I64, min_cost nums x = ok r ∧ r.val = (length nums : ℤ) * c) := by
    sorry

  /-- The function returns a result r and r = Σ_{i=0}^{n-1} nums[i].
    Preconditions: The general constraints: 1 <= len(nums) <= 1000, for all i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9, 1 <= x <= 10^9, and x >= (Σ_{i=0}^{n-1} nums[i]) - n * min_{0 <= i < n} nums[i], where n = len(nums). -/
  theorem spec_9 (nums : Slice I64) (x : I64) (hgen : GeneralConstraints nums x)
      (hx : (costs nums).sum - (length nums : ℤ) * listMin (costs nums) ≤ x.val) :
      ∃ r : I64, min_cost nums x = ok r ∧ r.val = (costs nums).sum := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice I64) (x : I64) (hgen : GeneralConstraints nums x)
        (hx : (costs nums).sum - (length nums : ℤ) * listMin (costs nums) ≤ x.val), ∃ r : I64, min_cost nums x = ok r ∧ r.val = (costs nums).sum) := by
    sorry

  /-- Let r be the result on nums and r' be the result on nums'. Then the function returns r and r' on the respective inputs, and r = r'.
    Preconditions: The general constraints: 1 <= len(nums) <= 1000, 1 <= x <= 10^9, and nums satisfies 1 <= nums[i] <= 10^9. Let k be an integer with 0 <= k < n where n = len(nums), and let nums' be the slice of length n defined by nums'[i] = nums[(i + k) mod n] for all 0 <= i < n. Then nums' also satisfies 1 <= nums'[i] <= 10^9. -/
  theorem spec_10 (nums nums' : Slice I64) (x : I64) (hgen : GeneralConstraints nums x)
      (hlen : length nums' = length nums) (k : ℕ) (hk : k < length nums)
      (hrot : ∀ i, i < length nums → cost nums' i = cost nums ((i + k) % length nums)) :
      ∃ r r' : I64,
        min_cost nums x = ok r ∧ min_cost nums' x = ok r' ∧ r.val = r'.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums nums' : Slice I64) (x : I64) (hgen : GeneralConstraints nums x)
        (hlen : length nums' = length nums) (k : ℕ) (hk : k < length nums)
        (hrot : ∀ i, i < length nums → cost nums' i = cost nums ((i + k) % length nums)), ∃ r r' : I64,
          min_cost nums x = ok r ∧ min_cost nums' x = ok r' ∧ r.val = r'.val) := by
    sorry

  /-- Let r be the result on nums and r' be the result on nums'. Then the function returns r and r' on the respective inputs, and r' = r + n * c, where n = len(nums).
    Preconditions: The general constraints: 1 <= len(nums) <= 1000, 1 <= x <= 10^9, and nums satisfies 1 <= nums[i] <= 10^9. Let c be an integer such that for all 0 <= i < n, 1 <= nums[i] + c <= 10^9. Let nums' be the slice with nums'[i] = nums[i] + c for all i. -/
  theorem spec_11 (nums nums' : Slice I64) (x : I64) (hgen : GeneralConstraints nums x) (c : ℤ)
      (hc : ∀ i, i < length nums → InBounds (cost nums i + c))
      (hlen : length nums' = length nums)
      (hshift : ∀ i, i < length nums → cost nums' i = cost nums i + c) :
      ∃ r r' : I64,
        min_cost nums x = ok r ∧ min_cost nums' x = ok r' ∧
          r'.val = r.val + (length nums : ℤ) * c := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums nums' : Slice I64) (x : I64) (hgen : GeneralConstraints nums x) (c : ℤ)
        (hc : ∀ i, i < length nums → InBounds (cost nums i + c))
        (hlen : length nums' = length nums)
        (hshift : ∀ i, i < length nums → cost nums' i = cost nums i + c), ∃ r r' : I64,
          min_cost nums x = ok r ∧ min_cost nums' x = ok r' ∧
            r'.val = r.val + (length nums : ℤ) * c) := by
    sorry

  /-- Let r be the result on nums and r' be the result on nums'. Then the function returns r and r', and r <= r'.
    Preconditions: Let n = len(nums) = len(nums') with 1 <= n <= 1000. For all 0 <= i < n, 1 <= nums[i] <= nums'[i] <= 10^9. Also 1 <= x <= 10^9. -/
  theorem spec_12 (nums nums' : Slice I64) (x : I64)
      (hlen : length nums = length nums') (hnpos : 1 ≤ length nums)
      (hnle : length nums ≤ 1000) (hmono : ∀ i, i < length nums → cost nums i ≤ cost nums' i)
      (hb : EntriesInBounds nums) (hb' : EntriesInBounds nums') (hx : InBounds x.val) :
      ∃ r r' : I64,
        min_cost nums x = ok r ∧ min_cost nums' x = ok r' ∧ r.val ≤ r'.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums nums' : Slice I64) (x : I64)
        (hlen : length nums = length nums') (hnpos : 1 ≤ length nums)
        (hnle : length nums ≤ 1000) (hmono : ∀ i, i < length nums → cost nums i ≤ cost nums' i)
        (hb : EntriesInBounds nums) (hb' : EntriesInBounds nums') (hx : InBounds x.val), ∃ r r' : I64,
          min_cost nums x = ok r ∧ min_cost nums' x = ok r' ∧ r.val ≤ r'.val) := by
    sorry

  /-- Let r1 be the result on (nums, x1) and r2 be the result on (nums, x2). Then the function returns r1 and r2 on the respective inputs, and r1 <= r2.
    Preconditions: The general constraints hold for nums (1 <= len(nums) <= 1000, 1 <= nums[i] <= 10^9), and 1 <= x1 <= x2 <= 10^9. -/
  theorem spec_13 (nums : Slice I64) (x1 x2 : I64) (hgen : GeneralConstraints nums x1)
      (h12 : x1.val ≤ x2.val) (hx2 : x2.val ≤ 10 ^ 9) :
      ∃ r1 r2 : I64,
        min_cost nums x1 = ok r1 ∧ min_cost nums x2 = ok r2 ∧ r1.val ≤ r2.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums : Slice I64) (x1 x2 : I64) (hgen : GeneralConstraints nums x1)
        (h12 : x1.val ≤ x2.val) (hx2 : x2.val ≤ 10 ^ 9), ∃ r1 r2 : I64,
          min_cost nums x1 = ok r1 ∧ min_cost nums x2 = ok r2 ∧ r1.val ≤ r2.val) := by
    sorry

  /-- The function returns a result r and r = min_{T=0}^{n-1} ( x * T + Σ_{j=0}^{n-1} min_{d=0}^{T} nums[(j - d) mod n] ), where n = len(nums).
    Preconditions: The general constraints: 1 <= len(nums) <= 1000, for all i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9, and 1 <= x <= 10^9. -/
  theorem spec_14 (nums : Slice I64) (x : I64) (hgen : GeneralConstraints nums x) :
      ∃ r : I64, min_cost nums x = ok r ∧ r.val = minWindowCost (costs nums) x.val := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (nums : Slice I64) (x : I64) (hgen : GeneralConstraints nums x), ∃ r : I64, min_cost nums x = ok r ∧ r.val = minWindowCost (costs nums) x.val) := by
    sorry

  end AegisSpec.MinCost
