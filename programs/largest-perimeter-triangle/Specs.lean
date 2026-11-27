import Aegis.LargestPerimeter.Code.Funs

/-!
# Specifications of `Aegis.LargestPerimeter.largest_perimeter`

LeetCode problem `largest-perimeter-triangle`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.LargestPerimeter

  open Aegis.LargestPerimeter

  def vals (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

  def lget (l : List Int) (i : Nat) : Int := l.getD i 0

  def valAt (nums : Slice Std.I64) (i : Nat) : Int := lget (vals nums) i

  def TriangleIneq (nums : Slice Std.I64) (i j k : Nat) : Prop :=
    valAt nums i + valAt nums j > valAt nums k ∧
    valAt nums i + valAt nums k > valAt nums j ∧
    valAt nums j + valAt nums k > valAt nums i

  def IsTriangleIdx (nums : Slice Std.I64) (i j k : Nat) : Prop :=
    i < j ∧ j < k ∧ k < nums.val.length ∧ TriangleIneq nums i j k

  def IsValidSum (nums : Slice Std.I64) (p : Int) : Prop :=
    ∃ i j k, IsTriangleIdx nums i j k ∧ p = valAt nums i + valAt nums j + valAt nums k

  def IsMaxOf (P : Int → Prop) (r : Int) : Prop := P r ∧ ∀ q, P q → q ≤ r

  def Nondecreasing (l : List Int) : Prop := l.Pairwise (fun a b => a ≤ b)

  def IsSortedTripleSum (b : List Int) (q : Int) : Prop :=
    ∃ i, i < b.length - 2 ∧ q = lget b i + lget b (i + 1) + lget b (i + 2) ∧
      lget b i + lget b (i + 1) > lget b (i + 2)

  /-- Whenever the function returns a result r, let P be the set of all integers p for which there exist indices i, j, k with 0 <= i < j < k < len(nums), p = nums[i] + nums[j] + nums[k], and the three strict triangle inequalities nums[i] + nums[j] > nums[k], nums[i] + nums[k] > nums[j], and nums[j] + nums[k] > nums[i] hold. If P is nonempty, r is the maximum element of P. If P is empty, r = 0.
    Preconditions: len(nums) >= 3, len(nums) <= 10000, and for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
  theorem spec_1 (nums : Slice Std.I64)
      (hlen_lo : 3 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 10000)
      (hval : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000) :
      ∀ r : Std.I64, largest_perimeter nums = ok r →
        (((∃ p, IsValidSum nums p) → IsMaxOf (IsValidSum nums) r.val) ∧
          ((¬ ∃ p, IsValidSum nums p) → r.val = 0)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lo : 3 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 10000)
        (hval : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000), ∀ r : Std.I64, largest_perimeter nums = ok r →
          (((∃ p, IsValidSum nums p) → IsMaxOf (IsValidSum nums) r.val) ∧
            ((¬ ∃ p, IsValidSum nums p) → r.val = 0))) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r; it does not fail by overflow, panic, or out-of-bounds access.
    Preconditions: len(nums) >= 3, len(nums) <= 10000, and for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
  theorem spec_2 (nums : Slice Std.I64)
      (hlen_lo : 3 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 10000)
      (hval : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000) :
      ∃ r : Std.I64, largest_perimeter nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lo : 3 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 10000)
        (hval : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000), ∃ r : Std.I64, largest_perimeter nums = ok r) := by
    sorry

  /-- Whenever the function returns a result r with r > 0, there exist indices i, j, k with 0 <= i < j < k < len(nums) such that r = nums[i] + nums[j] + nums[k] and nums[i] + nums[j] > nums[k], nums[i] + nums[k] > nums[j], and nums[j] + nums[k] > nums[i].
    Preconditions: len(nums) >= 3, len(nums) <= 10000, and for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
  theorem spec_3 (nums : Slice Std.I64)
      (hlen_lo : 3 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 10000)
      (hval : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000) :
      ∀ r : Std.I64, largest_perimeter nums = ok r → 0 < r.val →
        ∃ i j k, IsTriangleIdx nums i j k ∧
          r.val = valAt nums i + valAt nums j + valAt nums k := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lo : 3 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 10000)
        (hval : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000), ∀ r : Std.I64, largest_perimeter nums = ok r → 0 < r.val →
          ∃ i j k, IsTriangleIdx nums i j k ∧
            r.val = valAt nums i + valAt nums j + valAt nums k) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 if and only if there do not exist indices i, j, k with 0 <= i < j < k < len(nums) satisfying nums[i] + nums[j] > nums[k], nums[i] + nums[k] > nums[j], and nums[j] + nums[k] > nums[i].
    Preconditions: len(nums) >= 3, len(nums) <= 10000, and for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
  theorem spec_4 (nums : Slice Std.I64)
      (hlen_lo : 3 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 10000)
      (hval : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000) :
      ∀ r : Std.I64, largest_perimeter nums = ok r →
        (r.val = 0 ↔ ¬ ∃ i j k, IsTriangleIdx nums i j k) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lo : 3 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 10000)
        (hval : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000), ∀ r : Std.I64, largest_perimeter nums = ok r →
          (r.val = 0 ↔ ¬ ∃ i j k, IsTriangleIdx nums i j k)) := by
    sorry

  /-- Whenever the function returns a result r, for every choice of indices i, j, k with 0 <= i < j < k < len(nums) that satisfies nums[i] + nums[j] > nums[k], nums[i] + nums[k] > nums[j], and nums[j] + nums[k] > nums[i], we have nums[i] + nums[j] + nums[k] <= r.
    Preconditions: len(nums) >= 3, len(nums) <= 10000, and for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
  theorem spec_5 (nums : Slice Std.I64)
      (hlen_lo : 3 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 10000)
      (hval : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000) :
      ∀ r : Std.I64, largest_perimeter nums = ok r →
        ∀ i j k, IsTriangleIdx nums i j k →
          valAt nums i + valAt nums j + valAt nums k ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lo : 3 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 10000)
        (hval : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000), ∀ r : Std.I64, largest_perimeter nums = ok r →
          ∀ i j k, IsTriangleIdx nums i j k →
            valAt nums i + valAt nums j + valAt nums k ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r <= 3000000.
    Preconditions: len(nums) >= 3, len(nums) <= 10000, and for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
  theorem spec_6 (nums : Slice Std.I64)
      (hlen_lo : 3 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 10000)
      (hval : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000) :
      ∀ r : Std.I64, largest_perimeter nums = ok r → 0 ≤ r.val ∧ r.val ≤ 3000000 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lo : 3 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 10000)
        (hval : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000), ∀ r : Std.I64, largest_perimeter nums = ok r → 0 ≤ r.val ∧ r.val ≤ 3000000) := by
    sorry

  /-- For any slice nums' such that len(nums') = len(nums) and nums' is a permutation of nums (the same multiset of entries, possibly in a different order), if largest_perimeter(nums) returns r and largest_perimeter(nums') returns r', then r = r'.
    Preconditions: len(nums) >= 3, len(nums) <= 10000, and for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
  theorem spec_7 (nums nums' : Slice Std.I64)
      (hlen_lo : 3 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 10000)
      (hval : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000)
      (hlen' : nums'.val.length = nums.val.length)
      (hperm : List.Perm nums'.val nums.val) :
      ∀ r r' : Std.I64, largest_perimeter nums = ok r → largest_perimeter nums' = ok r' →
        r.val = r'.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums nums' : Slice Std.I64)
        (hlen_lo : 3 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 10000)
        (hval : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000)
        (hlen' : nums'.val.length = nums.val.length)
        (hperm : List.Perm nums'.val nums.val), ∀ r r' : Std.I64, largest_perimeter nums = ok r → largest_perimeter nums' = ok r' →
          r.val = r'.val) := by
    sorry

  /-- Let c be a positive integer, and let nums' be a slice with len(nums') = len(nums), nums'[i] = c * nums[i] for every i with 0 <= i < len(nums), and 1 <= nums'[i] <= 1000000 for every i with 0 <= i < len(nums'). If largest_perimeter(nums) returns r and largest_perimeter(nums') returns r', then r' = c * r.
    Preconditions: len(nums) >= 3, len(nums) <= 10000, and for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
  theorem spec_8 (nums nums' : Slice Std.I64) (c : Nat)
      (hc : 0 < c)
      (hlen_lo : 3 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 10000)
      (hval : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000)
      (hlen' : nums'.val.length = nums.val.length)
      (hscale : ∀ i, i < nums.val.length → valAt nums' i = (c : Int) * valAt nums i)
      (hval' : ∀ x ∈ nums'.val, 1 ≤ x.val ∧ x.val ≤ 1000000) :
      ∀ r r' : Std.I64, largest_perimeter nums = ok r → largest_perimeter nums' = ok r' →
        r'.val = (c : Int) * r.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums nums' : Slice Std.I64) (c : Nat)
        (hc : 0 < c)
        (hlen_lo : 3 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 10000)
        (hval : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000)
        (hlen' : nums'.val.length = nums.val.length)
        (hscale : ∀ i, i < nums.val.length → valAt nums' i = (c : Int) * valAt nums i)
        (hval' : ∀ x ∈ nums'.val, 1 ≤ x.val ∧ x.val ≤ 1000000), ∀ r r' : Std.I64, largest_perimeter nums = ok r → largest_perimeter nums' = ok r' →
          r'.val = (c : Int) * r.val) := by
    sorry

  /-- If there exist indices i, j, k with 0 <= i < j < k < len(nums) such that for every index h with 0 <= h < len(nums) and h not in {i, j, k}, nums[h] <= min(nums[i], nums[j], nums[k]), and nums[i] + nums[j] > nums[k], nums[i] + nums[k] > nums[j], and nums[j] + nums[k] > nums[i], then whenever the function returns a result r, r = nums[i] + nums[j] + nums[k].
    Preconditions: len(nums) >= 3, len(nums) <= 10000, and for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
  theorem spec_9 (nums : Slice Std.I64)
      (hlen_lo : 3 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 10000)
      (hval : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000) :
      ∀ i j k, IsTriangleIdx nums i j k →
        (∀ h, h < nums.val.length → h ≠ i → h ≠ j → h ≠ k →
          valAt nums h ≤ min (valAt nums i) (min (valAt nums j) (valAt nums k))) →
        ∀ r : Std.I64, largest_perimeter nums = ok r →
          r.val = valAt nums i + valAt nums j + valAt nums k := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lo : 3 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 10000)
        (hval : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000), ∀ i j k, IsTriangleIdx nums i j k →
          (∀ h, h < nums.val.length → h ≠ i → h ≠ j → h ≠ k →
            valAt nums h ≤ min (valAt nums i) (min (valAt nums j) (valAt nums k))) →
          ∀ r : Std.I64, largest_perimeter nums = ok r →
            r.val = valAt nums i + valAt nums j + valAt nums k) := by
    sorry

  /-- Let b be the entries of nums sorted in nondecreasing order. Let Q be the set of all integers q for which there exists an index i with 0 <= i < len(nums)-2, q = b[i] + b[i+1] + b[i+2], and b[i] + b[i+1] > b[i+2]. Whenever the function returns a result r, if Q is nonempty then r is the maximum element of Q; if Q is empty then r = 0.
    Preconditions: len(nums) >= 3, len(nums) <= 10000, and for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
  theorem spec_10 (nums : Slice Std.I64)
      (hlen_lo : 3 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 10000)
      (hval : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000) :
      ∀ b : List Int, Nondecreasing b → List.Perm b (vals nums) →
        ∀ r : Std.I64, largest_perimeter nums = ok r →
          (((∃ q, IsSortedTripleSum b q) → IsMaxOf (IsSortedTripleSum b) r.val) ∧
            ((¬ ∃ q, IsSortedTripleSum b q) → r.val = 0)) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lo : 3 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 10000)
        (hval : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000), ∀ b : List Int, Nondecreasing b → List.Perm b (vals nums) →
          ∀ r : Std.I64, largest_perimeter nums = ok r →
            (((∃ q, IsSortedTripleSum b q) → IsMaxOf (IsSortedTripleSum b) r.val) ∧
              ((¬ ∃ q, IsSortedTripleSum b q) → r.val = 0))) := by
    sorry

  end AegisSpec.LargestPerimeter
