import Aegis.MinimumSwaps.Code.Funs

/-!
# Specifications of `Aegis.MinimumSwaps.minimum_swaps`

LeetCode problem `minimum-adjacent-swaps-to-make-a-valid-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinimumSwaps

  open Aegis.MinimumSwaps

  def vals (nums : Slice I64) : List Int := nums.val.map (fun x => x.val)

  def len (nums : Slice I64) : Nat := (vals nums).length

  def get (nums : Slice I64) (i : Nat) : Int := (vals nums).getD i 0

  def lmin : List Int → Int
    | [] => 0
    | x :: xs => xs.foldl min x

  def lmax : List Int → Int
    | [] => 0
    | x :: xs => xs.foldl max x

  def minVal (nums : Slice I64) : Int := lmin (vals nums)

  def maxVal (nums : Slice I64) : Int := lmax (vals nums)

  def firstMinIdxAux : List Int → Nat → Int → Nat → Nat
    | [], _, _, j => j
    | x :: xs, i, v, j =>
      if x < v then firstMinIdxAux xs (i + 1) x i else firstMinIdxAux xs (i + 1) v j

  def firstMinIdx (nums : Slice I64) : Nat :=
    match vals nums with
    | [] => 0
    | x :: xs => firstMinIdxAux xs 1 x 0

  def lastMaxIdxAux : List Int → Nat → Int → Nat → Nat
    | [], _, _, j => j
    | x :: xs, i, v, j =>
      if v ≤ x then lastMaxIdxAux xs (i + 1) x i else lastMaxIdxAux xs (i + 1) v j

  def lastMaxIdx (nums : Slice I64) : Nat :=
    match vals nums with
    | [] => 0
    | x :: xs => lastMaxIdxAux xs 1 x 0

  def AdjSwap (l l' : List Int) : Prop :=
    ∃ (pre : List Int) (x y : Int) (suf : List Int), l = pre ++ x :: y :: suf ∧ l' = pre ++ y :: x :: suf

  def AdjSwapsExactly : Nat → List Int → List Int → Prop
    | 0, l, l' => l = l'
    | k + 1, l, l' => ∃ m, AdjSwapsExactly k l m ∧ AdjSwap m l'

  /-- Whenever minimum_swaps(nums) returns a result r, the following holds. Let n = len(nums), mn = min{ nums[i] | 0 <= i < n }, and mx = max{ nums[i] | 0 <= i < n }. Then r is the least integer of the form p + (n - 1 - q) - c, where p and q are indices with 0 <= p < n, 0 <= q < n, nums[p] = mn, nums[q] = mx, and c = 1 if p > q and c = 0 otherwise.
    Preconditions: len(nums) >= 1 and len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000. -/
  theorem spec_1 (nums : Slice I64)
      (h_len_ge : 1 ≤ len nums) (h_len_le : len nums ≤ 100000)
      (h_range : ∀ i, i < len nums → 1 ≤ get nums i ∧ get nums i ≤ 100000) :
      ∀ r : I64, minimum_swaps nums = ok r →
        (∀ p q : Nat, p < len nums → q < len nums →
            get nums p = minVal nums → get nums q = maxVal nums →
            r.val ≤ (p : Int) + ((len nums : Int) - 1 - (q : Int)) -
              (if p > q then (1 : Int) else 0)) ∧
        (∃ p q : Nat, p < len nums ∧ q < len nums ∧ get nums p = minVal nums ∧
            get nums q = maxVal nums ∧
            r.val = (p : Int) + ((len nums : Int) - 1 - (q : Int)) -
              (if p > q then (1 : Int) else 0)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice I64)
        (h_len_ge : 1 ≤ len nums) (h_len_le : len nums ≤ 100000)
        (h_range : ∀ i, i < len nums → 1 ≤ get nums i ∧ get nums i ≤ 100000), ∀ r : I64, minimum_swaps nums = ok r →
          (∀ p q : Nat, p < len nums → q < len nums →
              get nums p = minVal nums → get nums q = maxVal nums →
              r.val ≤ (p : Int) + ((len nums : Int) - 1 - (q : Int)) -
                (if p > q then (1 : Int) else 0)) ∧
          (∃ p q : Nat, p < len nums ∧ q < len nums ∧ get nums p = minVal nums ∧
              get nums q = maxVal nums ∧
              r.val = (p : Int) + ((len nums : Int) - 1 - (q : Int)) -
                (if p > q then (1 : Int) else 0))) := by
    sorry

  /-- For every nums satisfying the preconditions, the evaluation of minimum_swaps(nums) returns a result r; it does not fail (no overflow, out-of-bounds access, or panic).
    Preconditions: len(nums) >= 1 and len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000. -/
  theorem spec_2 (nums : Slice I64)
      (h_len_ge : 1 ≤ len nums) (h_len_le : len nums ≤ 100000)
      (h_range : ∀ i, i < len nums → 1 ≤ get nums i ∧ get nums i ≤ 100000) :
      ∃ r : I64, minimum_swaps nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice I64)
        (h_len_ge : 1 ≤ len nums) (h_len_le : len nums ≤ 100000)
        (h_range : ∀ i, i < len nums → 1 ≤ get nums i ∧ get nums i ≤ 100000), ∃ r : I64, minimum_swaps nums = ok r) := by
    sorry

  /-- Whenever minimum_swaps(nums) returns a result r, r >= 0.
    Preconditions: len(nums) >= 1 and len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000. -/
  theorem spec_3 (nums : Slice I64)
      (h_len_ge : 1 ≤ len nums) (h_len_le : len nums ≤ 100000)
      (h_range : ∀ i, i < len nums → 1 ≤ get nums i ∧ get nums i ≤ 100000) :
      ∀ r : I64, minimum_swaps nums = ok r → 0 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice I64)
        (h_len_ge : 1 ≤ len nums) (h_len_le : len nums ≤ 100000)
        (h_range : ∀ i, i < len nums → 1 ≤ get nums i ∧ get nums i ≤ 100000), ∀ r : I64, minimum_swaps nums = ok r → 0 ≤ r.val) := by
    sorry

  /-- Whenever minimum_swaps(nums) returns a result r, r <= 2 * len(nums) - 3.
    Preconditions: len(nums) >= 2, len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000. -/
  theorem spec_4 (nums : Slice I64)
      (h_len_ge : 2 ≤ len nums) (h_len_le : len nums ≤ 100000)
      (h_range : ∀ i, i < len nums → 1 ≤ get nums i ∧ get nums i ≤ 100000) :
      ∀ r : I64, minimum_swaps nums = ok r → r.val ≤ 2 * (len nums : Int) - 3 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice I64)
        (h_len_ge : 2 ≤ len nums) (h_len_le : len nums ≤ 100000)
        (h_range : ∀ i, i < len nums → 1 ≤ get nums i ∧ get nums i ≤ 100000), ∀ r : I64, minimum_swaps nums = ok r → r.val ≤ 2 * (len nums : Int) - 3) := by
    sorry

  /-- Whenever minimum_swaps(nums) returns a result r, let n = len(nums), mn = min{ nums[i] | 0 <= i < n }, and mx = max{ nums[i] | 0 <= i < n }. Then r = 0 if and only if nums[0] = mn and nums[n-1] = mx.
    Preconditions: len(nums) >= 1 and len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000. -/
  theorem spec_5 (nums : Slice I64)
      (h_len_ge : 1 ≤ len nums) (h_len_le : len nums ≤ 100000)
      (h_range : ∀ i, i < len nums → 1 ≤ get nums i ∧ get nums i ≤ 100000) :
      ∀ r : I64, minimum_swaps nums = ok r →
        (r.val = 0 ↔ (get nums 0 = minVal nums ∧ get nums (len nums - 1) = maxVal nums)) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice I64)
        (h_len_ge : 1 ≤ len nums) (h_len_le : len nums ≤ 100000)
        (h_range : ∀ i, i < len nums → 1 ≤ get nums i ∧ get nums i ≤ 100000), ∀ r : I64, minimum_swaps nums = ok r →
          (r.val = 0 ↔ (get nums 0 = minVal nums ∧ get nums (len nums - 1) = maxVal nums))) := by
    sorry

  /-- Whenever minimum_swaps(nums) returns a result r, r = 2 * n - 3.
    Preconditions: Let n = len(nums), mn = min{ nums[i] | 0 <= i < n }, and mx = max{ nums[i] | 0 <= i < n }. The input satisfies len(nums) >= 2, len(nums) <= 100000, 1 <= nums[i] <= 100000 for all i, mn < mx, nums[0] = mx, nums[n-1] = mn, and for every i with 1 <= i <= n-2, mn < nums[i] < mx. -/
  theorem spec_6 (nums : Slice I64)
      (h_len_ge : 2 ≤ len nums) (h_len_le : len nums ≤ 100000)
      (h_range : ∀ i, i < len nums → 1 ≤ get nums i ∧ get nums i ≤ 100000)
      (h_min_lt_max : minVal nums < maxVal nums)
      (h_first_max : get nums 0 = maxVal nums)
      (h_last_min : get nums (len nums - 1) = minVal nums)
      (h_middle : ∀ i, 1 ≤ i → i ≤ len nums - 2 →
        minVal nums < get nums i ∧ get nums i < maxVal nums) :
      ∀ r : I64, minimum_swaps nums = ok r → r.val = 2 * (len nums : Int) - 3 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice I64)
        (h_len_ge : 2 ≤ len nums) (h_len_le : len nums ≤ 100000)
        (h_range : ∀ i, i < len nums → 1 ≤ get nums i ∧ get nums i ≤ 100000)
        (h_min_lt_max : minVal nums < maxVal nums)
        (h_first_max : get nums 0 = maxVal nums)
        (h_last_min : get nums (len nums - 1) = minVal nums)
        (h_middle : ∀ i, 1 ≤ i → i ≤ len nums - 2 →
          minVal nums < get nums i ∧ get nums i < maxVal nums), ∀ r : I64, minimum_swaps nums = ok r → r.val = 2 * (len nums : Int) - 3) := by
    sorry

  /-- Whenever minimum_swaps(nums) returns a result r and minimum_swaps(nums2) returns a result r2, r = r2.
    Preconditions: For two arrays nums and nums2, both satisfy len(x) >= 1, len(x) <= 100000, and 1 <= x[i] <= 100000 for all valid indices, and they have the same length n. Let p0(x) be the least index p with 0 <= p < n and x[p] = min{ x[i] | 0 <= i < n }, and let q0(x) be the greatest index q with 0 <= q < n and x[q] = max{ x[i] | 0 <= i < n }. Assume p0(nums) = p0(nums2) and q0(nums) = q0(nums2). -/
  theorem spec_7 (nums nums2 : Slice I64)
      (h_len_ge : 1 ≤ len nums) (h_len_le : len nums ≤ 100000)
      (h_range : ∀ i, i < len nums → 1 ≤ get nums i ∧ get nums i ≤ 100000)
      (h_len_ge2 : 1 ≤ len nums2) (h_len_le2 : len nums2 ≤ 100000)
      (h_range2 : ∀ i, i < len nums2 → 1 ≤ get nums2 i ∧ get nums2 i ≤ 100000)
      (h_len_eq : len nums = len nums2)
      (h_p0 : firstMinIdx nums = firstMinIdx nums2)
      (h_q0 : lastMaxIdx nums = lastMaxIdx nums2) :
      ∀ r r2 : I64, minimum_swaps nums = ok r → minimum_swaps nums2 = ok r2 → r = r2 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums nums2 : Slice I64)
        (h_len_ge : 1 ≤ len nums) (h_len_le : len nums ≤ 100000)
        (h_range : ∀ i, i < len nums → 1 ≤ get nums i ∧ get nums i ≤ 100000)
        (h_len_ge2 : 1 ≤ len nums2) (h_len_le2 : len nums2 ≤ 100000)
        (h_range2 : ∀ i, i < len nums2 → 1 ≤ get nums2 i ∧ get nums2 i ≤ 100000)
        (h_len_eq : len nums = len nums2)
        (h_p0 : firstMinIdx nums = firstMinIdx nums2)
        (h_q0 : lastMaxIdx nums = lastMaxIdx nums2), ∀ r r2 : I64, minimum_swaps nums = ok r → minimum_swaps nums2 = ok r2 → r = r2) := by
    sorry

  /-- Whenever minimum_swaps(nums) returns a result r, let n = len(nums), mn = min{ nums[i] | 0 <= i < n }, and mx = max{ nums[i] | 0 <= i < n }. There exists an array b and a finite sequence of exactly r adjacent swaps (each swap exchanges two neighboring entries of the current array) that transforms nums into b, such that b[0] = mn and b[n-1] = mx.
    Preconditions: len(nums) >= 1 and len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000. -/
  theorem spec_8 (nums : Slice I64)
      (h_len_ge : 1 ≤ len nums) (h_len_le : len nums ≤ 100000)
      (h_range : ∀ i, i < len nums → 1 ≤ get nums i ∧ get nums i ≤ 100000) :
      ∀ r : I64, minimum_swaps nums = ok r →
        ∃ (b : Slice I64) (k : Nat), r.val = (k : Int) ∧
          AdjSwapsExactly k (vals nums) (vals b) ∧
          get b 0 = minVal nums ∧ get b (len nums - 1) = maxVal nums := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice I64)
        (h_len_ge : 1 ≤ len nums) (h_len_le : len nums ≤ 100000)
        (h_range : ∀ i, i < len nums → 1 ≤ get nums i ∧ get nums i ≤ 100000), ∀ r : I64, minimum_swaps nums = ok r →
          ∃ (b : Slice I64) (k : Nat), r.val = (k : Int) ∧
            AdjSwapsExactly k (vals nums) (vals b) ∧
            get b 0 = minVal nums ∧ get b (len nums - 1) = maxVal nums) := by
    sorry

  /-- Whenever minimum_swaps(nums) returns a result r, let n = len(nums), mn = min{ nums[i] | 0 <= i < n }, and mx = max{ nums[i] | 0 <= i < n }. For every integer k with 0 <= k < r and every array b obtainable from nums by exactly k adjacent swaps, either b[0] != mn or b[n-1] != mx.
    Preconditions: len(nums) >= 1 and len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000. -/
  theorem spec_9 (nums : Slice I64)
      (h_len_ge : 1 ≤ len nums) (h_len_le : len nums ≤ 100000)
      (h_range : ∀ i, i < len nums → 1 ≤ get nums i ∧ get nums i ≤ 100000) :
      ∀ r : I64, minimum_swaps nums = ok r →
        ∀ (k : Nat) (b : Slice I64), (k : Int) < r.val →
          AdjSwapsExactly k (vals nums) (vals b) →
          (get b 0 ≠ minVal nums ∨ get b (len nums - 1) ≠ maxVal nums) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice I64)
        (h_len_ge : 1 ≤ len nums) (h_len_le : len nums ≤ 100000)
        (h_range : ∀ i, i < len nums → 1 ≤ get nums i ∧ get nums i ≤ 100000), ∀ r : I64, minimum_swaps nums = ok r →
          ∀ (k : Nat) (b : Slice I64), (k : Int) < r.val →
            AdjSwapsExactly k (vals nums) (vals b) →
            (get b 0 ≠ minVal nums ∨ get b (len nums - 1) ≠ maxVal nums)) := by
    sorry

  /-- Whenever minimum_swaps(nums) returns a result r, r = p0 + (n - 1 - q0).
    Preconditions: Let n = len(nums), mn = min{ nums[i] | 0 <= i < n }, mx = max{ nums[i] | 0 <= i < n }, p0 = the least index p with nums[p] = mn, and q0 = the greatest index q with nums[q] = mx. The input satisfies len(nums) >= 1, len(nums) <= 100000, 1 <= nums[i] <= 100000 for all i, and p0 <= q0. -/
  theorem spec_10 (nums : Slice I64)
      (h_len_ge : 1 ≤ len nums) (h_len_le : len nums ≤ 100000)
      (h_range : ∀ i, i < len nums → 1 ≤ get nums i ∧ get nums i ≤ 100000)
      (h_p0_le_q0 : firstMinIdx nums ≤ lastMaxIdx nums) :
      ∀ r : I64, minimum_swaps nums = ok r →
        r.val = (firstMinIdx nums : Int) + ((len nums : Int) - 1 - (lastMaxIdx nums : Int)) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice I64)
        (h_len_ge : 1 ≤ len nums) (h_len_le : len nums ≤ 100000)
        (h_range : ∀ i, i < len nums → 1 ≤ get nums i ∧ get nums i ≤ 100000)
        (h_p0_le_q0 : firstMinIdx nums ≤ lastMaxIdx nums), ∀ r : I64, minimum_swaps nums = ok r →
          r.val = (firstMinIdx nums : Int) + ((len nums : Int) - 1 - (lastMaxIdx nums : Int))) := by
    sorry

  /-- Whenever minimum_swaps(nums) returns a result r, r = p0 + (n - 1 - q0) - 1.
    Preconditions: Let n = len(nums), mn = min{ nums[i] | 0 <= i < n }, mx = max{ nums[i] | 0 <= i < n }, p0 = the least index p with nums[p] = mn, and q0 = the greatest index q with nums[q] = mx. The input satisfies len(nums) >= 1, len(nums) <= 100000, 1 <= nums[i] <= 100000 for all i, and p0 > q0. -/
  theorem spec_11 (nums : Slice I64)
      (h_len_ge : 1 ≤ len nums) (h_len_le : len nums ≤ 100000)
      (h_range : ∀ i, i < len nums → 1 ≤ get nums i ∧ get nums i ≤ 100000)
      (h_q0_lt_p0 : lastMaxIdx nums < firstMinIdx nums) :
      ∀ r : I64, minimum_swaps nums = ok r →
        r.val = (firstMinIdx nums : Int) + ((len nums : Int) - 1 - (lastMaxIdx nums : Int)) - 1 := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice I64)
        (h_len_ge : 1 ≤ len nums) (h_len_le : len nums ≤ 100000)
        (h_range : ∀ i, i < len nums → 1 ≤ get nums i ∧ get nums i ≤ 100000)
        (h_q0_lt_p0 : lastMaxIdx nums < firstMinIdx nums), ∀ r : I64, minimum_swaps nums = ok r →
          r.val = (firstMinIdx nums : Int) + ((len nums : Int) - 1 - (lastMaxIdx nums : Int)) - 1) := by
    sorry

  /-- Whenever minimum_swaps(nums) returns a result r, r <= n - 1.
    Preconditions: Let n = len(nums), mn = min{ nums[i] | 0 <= i < n }, and mx = max{ nums[i] | 0 <= i < n }. The input satisfies len(nums) >= 1, len(nums) <= 100000, 1 <= nums[i] <= 100000 for all i, and (nums[0] = mn or nums[n-1] = mx). -/
  theorem spec_12 (nums : Slice I64)
      (h_len_ge : 1 ≤ len nums) (h_len_le : len nums ≤ 100000)
      (h_range : ∀ i, i < len nums → 1 ≤ get nums i ∧ get nums i ≤ 100000)
      (h_end : get nums 0 = minVal nums ∨ get nums (len nums - 1) = maxVal nums) :
      ∀ r : I64, minimum_swaps nums = ok r → r.val ≤ (len nums : Int) - 1 := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice I64)
        (h_len_ge : 1 ≤ len nums) (h_len_le : len nums ≤ 100000)
        (h_range : ∀ i, i < len nums → 1 ≤ get nums i ∧ get nums i ≤ 100000)
        (h_end : get nums 0 = minVal nums ∨ get nums (len nums - 1) = maxVal nums), ∀ r : I64, minimum_swaps nums = ok r → r.val ≤ (len nums : Int) - 1) := by
    sorry

  /-- Whenever minimum_swaps(nums) returns a result r, r = 0 if nums[0] <= nums[1], and r = 1 if nums[0] > nums[1].
    Preconditions: len(nums) = 2, and 1 <= nums[0] <= 100000 and 1 <= nums[1] <= 100000. -/
  theorem spec_13 (nums : Slice I64)
      (h_len : len nums = 2)
      (h_0 : 1 ≤ get nums 0 ∧ get nums 0 ≤ 100000)
      (h_1 : 1 ≤ get nums 1 ∧ get nums 1 ≤ 100000) :
      ∀ r : I64, minimum_swaps nums = ok r →
        (get nums 0 ≤ get nums 1 → r.val = 0) ∧ (get nums 1 < get nums 0 → r.val = 1) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums : Slice I64)
        (h_len : len nums = 2)
        (h_0 : 1 ≤ get nums 0 ∧ get nums 0 ≤ 100000)
        (h_1 : 1 ≤ get nums 1 ∧ get nums 1 ≤ 100000), ∀ r : I64, minimum_swaps nums = ok r →
          (get nums 0 ≤ get nums 1 → r.val = 0) ∧ (get nums 1 < get nums 0 → r.val = 1)) := by
    sorry

  end AegisSpec.MinimumSwaps
