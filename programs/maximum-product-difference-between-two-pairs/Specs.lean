import Aegis.MaxProductDifference.Code.Funs

/-!
# Specifications of `Aegis.MaxProductDifference.max_product_difference`

LeetCode problem `maximum-product-difference-between-two-pairs`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxProductDifference

def vals (nums : Slice Std.I64) : List ℤ := nums.val.map (fun x => x.val)

def nth (l : List ℤ) (i : ℕ) : ℤ := l.getD i 0

@[reducible] def Pairwise4 (w x y z : ℕ) : Prop :=
  w ≠ x ∧ w ≠ y ∧ w ≠ z ∧ x ≠ y ∧ x ≠ z ∧ y ≠ z

@[reducible] def IsMaxOf (s : Finset ℤ) (m : ℤ) : Prop := m ∈ s ∧ ∀ q ∈ s, q ≤ m

@[reducible] def IsMinOf (s : Finset ℤ) (m : ℤ) : Prop := m ∈ s ∧ ∀ q ∈ s, m ≤ q

def quadDiffs (l : List ℤ) : Finset ℤ :=
  Finset.image
    (fun q : Fin l.length × Fin l.length × Fin l.length × Fin l.length =>
      l.get q.1 * l.get q.2.1 - l.get q.2.2.1 * l.get q.2.2.2)
    (Finset.filter
      (fun q : Fin l.length × Fin l.length × Fin l.length × Fin l.length =>
        Pairwise4 q.1 q.2.1 q.2.2.1 q.2.2.2)
      Finset.univ)

def pairProducts (l : List ℤ) : Finset ℤ :=
  Finset.image (fun p : Fin l.length × Fin l.length => l.get p.1 * l.get p.2)
    (Finset.filter (fun p : Fin l.length × Fin l.length => p.1 < p.2) Finset.univ)

/-- Let Q = { nums[w] * nums[x] - nums[y] * nums[z] | 0 <= w, x, y, z < n and the four indices w, x, y, z are pairwise distinct }. The function returns a result r and r = max(Q).
  Preconditions: Let n = len(nums). 4 <= n <= 10000 and 1 <= nums[i] <= 10000 for every 0 <= i < n. -/
theorem spec_1 (nums : Slice Std.I64)
    (h_len_lo : 4 ≤ (vals nums).length) (h_len_hi : (vals nums).length ≤ 10000)
    (h_bnd : ∀ v ∈ vals nums, 1 ≤ v ∧ v ≤ 10000) :
    ∃ r : Std.I64,
      Aegis.MaxProductDifference.max_product_difference nums = ok r ∧
        IsMaxOf (quadDiffs (vals nums)) r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_lo : 4 ≤ (vals nums).length) (h_len_hi : (vals nums).length ≤ 10000)
    (h_bnd : ∀ v ∈ vals nums, 1 ≤ v ∧ v ≤ 10000), ∃ r : Std.I64,
      Aegis.MaxProductDifference.max_product_difference nums = ok r ∧
        IsMaxOf (quadDiffs (vals nums)) r.val) := by
  sorry

/-- The function returns a result r; it does not fail, panic, access an out-of-bounds index, or overflow 64-bit integer arithmetic.
  Preconditions: Let n = len(nums). 4 <= n <= 10000 and 1 <= nums[i] <= 10000 for every 0 <= i < n. -/
theorem spec_2 (nums : Slice Std.I64)
    (h_len_lo : 4 ≤ (vals nums).length) (h_len_hi : (vals nums).length ≤ 10000)
    (h_bnd : ∀ v ∈ vals nums, 1 ≤ v ∧ v ≤ 10000) :
    ∃ r : Std.I64, Aegis.MaxProductDifference.max_product_difference nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_lo : 4 ≤ (vals nums).length) (h_len_hi : (vals nums).length ≤ 10000)
    (h_bnd : ∀ v ∈ vals nums, 1 ≤ v ∧ v ≤ 10000), ∃ r : Std.I64, Aegis.MaxProductDifference.max_product_difference nums = ok r) := by
  sorry

/-- Whenever the function returns a result r, if s is a nondecreasing rearrangement of nums (so s[0] <= s[1] <= ... <= s[n-1]), then r = s[n-1] * s[n-2] - s[0] * s[1].
  Preconditions: Let n = len(nums). 4 <= n <= 10000 and 1 <= nums[i] <= 10000 for every 0 <= i < n. -/
theorem spec_3 (nums : Slice Std.I64)
    (h_len_lo : 4 ≤ (vals nums).length) (h_len_hi : (vals nums).length ≤ 10000)
    (h_bnd : ∀ v ∈ vals nums, 1 ≤ v ∧ v ≤ 10000)
    (r : Std.I64) (h_r : Aegis.MaxProductDifference.max_product_difference nums = ok r)
    (s : List ℤ) (h_perm : s.Perm (vals nums)) (h_sorted : s.Pairwise (· ≤ ·)) :
    r.val = nth s (s.length - 1) * nth s (s.length - 2) - nth s 0 * nth s 1 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_lo : 4 ≤ (vals nums).length) (h_len_hi : (vals nums).length ≤ 10000)
    (h_bnd : ∀ v ∈ vals nums, 1 ≤ v ∧ v ≤ 10000)
    (r : Std.I64) (h_r : Aegis.MaxProductDifference.max_product_difference nums = ok r)
    (s : List ℤ) (h_perm : s.Perm (vals nums)) (h_sorted : s.Pairwise (· ≤ ·)), r.val = nth s (s.length - 1) * nth s (s.length - 2) - nth s 0 * nth s 1) := by
  sorry

/-- Whenever the function returns a result r, with Pmax = max{ nums[i] * nums[j] | 0 <= i < j < n } and Pmin = min{ nums[i] * nums[j] | 0 <= i < j < n }, we have r = Pmax - Pmin.
  Preconditions: Let n = len(nums). 4 <= n <= 10000 and 1 <= nums[i] <= 10000 for every 0 <= i < n. -/
theorem spec_4 (nums : Slice Std.I64)
    (h_len_lo : 4 ≤ (vals nums).length) (h_len_hi : (vals nums).length ≤ 10000)
    (h_bnd : ∀ v ∈ vals nums, 1 ≤ v ∧ v ≤ 10000)
    (r : Std.I64) (h_r : Aegis.MaxProductDifference.max_product_difference nums = ok r) :
    ∃ Pmax Pmin : ℤ,
      IsMaxOf (pairProducts (vals nums)) Pmax ∧ IsMinOf (pairProducts (vals nums)) Pmin ∧
        r.val = Pmax - Pmin := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_lo : 4 ≤ (vals nums).length) (h_len_hi : (vals nums).length ≤ 10000)
    (h_bnd : ∀ v ∈ vals nums, 1 ≤ v ∧ v ≤ 10000)
    (r : Std.I64) (h_r : Aegis.MaxProductDifference.max_product_difference nums = ok r), ∃ Pmax Pmin : ℤ,
      IsMaxOf (pairProducts (vals nums)) Pmax ∧ IsMinOf (pairProducts (vals nums)) Pmin ∧
        r.val = Pmax - Pmin) := by
  sorry

/-- Whenever the function returns a result r, there exist pairwise distinct indices w, x, y, z such that: (i) every index t not equal to w or x satisfies nums[t] <= nums[w] and nums[t] <= nums[x]; (ii) every index t not equal to y or z satisfies nums[t] >= nums[y] and nums[t] >= nums[z]; and (iii) r = nums[w] * nums[x] - nums[y] * nums[z].
  Preconditions: Let n = len(nums). 4 <= n <= 10000 and 1 <= nums[i] <= 10000 for every 0 <= i < n. -/
theorem spec_5 (nums : Slice Std.I64)
    (h_len_lo : 4 ≤ (vals nums).length) (h_len_hi : (vals nums).length ≤ 10000)
    (h_bnd : ∀ v ∈ vals nums, 1 ≤ v ∧ v ≤ 10000)
    (r : Std.I64) (h_r : Aegis.MaxProductDifference.max_product_difference nums = ok r) :
    ∃ w x y z : ℕ,
      w < (vals nums).length ∧ x < (vals nums).length ∧ y < (vals nums).length ∧
        z < (vals nums).length ∧ Pairwise4 w x y z ∧
        (∀ t : ℕ, t < (vals nums).length → t ≠ w → t ≠ x →
          nth (vals nums) t ≤ nth (vals nums) w ∧ nth (vals nums) t ≤ nth (vals nums) x) ∧
        (∀ t : ℕ, t < (vals nums).length → t ≠ y → t ≠ z →
          nth (vals nums) y ≤ nth (vals nums) t ∧ nth (vals nums) z ≤ nth (vals nums) t) ∧
        r.val = nth (vals nums) w * nth (vals nums) x - nth (vals nums) y * nth (vals nums) z := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_lo : 4 ≤ (vals nums).length) (h_len_hi : (vals nums).length ≤ 10000)
    (h_bnd : ∀ v ∈ vals nums, 1 ≤ v ∧ v ≤ 10000)
    (r : Std.I64) (h_r : Aegis.MaxProductDifference.max_product_difference nums = ok r), ∃ w x y z : ℕ,
      w < (vals nums).length ∧ x < (vals nums).length ∧ y < (vals nums).length ∧
        z < (vals nums).length ∧ Pairwise4 w x y z ∧
        (∀ t : ℕ, t < (vals nums).length → t ≠ w → t ≠ x →
          nth (vals nums) t ≤ nth (vals nums) w ∧ nth (vals nums) t ≤ nth (vals nums) x) ∧
        (∀ t : ℕ, t < (vals nums).length → t ≠ y → t ≠ z →
          nth (vals nums) y ≤ nth (vals nums) t ∧ nth (vals nums) z ≤ nth (vals nums) t) ∧
        r.val = nth (vals nums) w * nth (vals nums) x - nth (vals nums) y * nth (vals nums) z) := by
  sorry

/-- Whenever the function returns a result r, for every four pairwise distinct indices w, x, y, z with 0 <= w, x, y, z < n, we have |nums[w] * nums[x] - nums[y] * nums[z]| <= r.
  Preconditions: Let n = len(nums). 4 <= n <= 10000 and 1 <= nums[i] <= 10000 for every 0 <= i < n. -/
theorem spec_6 (nums : Slice Std.I64)
    (h_len_lo : 4 ≤ (vals nums).length) (h_len_hi : (vals nums).length ≤ 10000)
    (h_bnd : ∀ v ∈ vals nums, 1 ≤ v ∧ v ≤ 10000)
    (r : Std.I64) (h_r : Aegis.MaxProductDifference.max_product_difference nums = ok r) :
    ∀ w x y z : ℕ,
      w < (vals nums).length → x < (vals nums).length → y < (vals nums).length →
        z < (vals nums).length → Pairwise4 w x y z →
          |nth (vals nums) w * nth (vals nums) x - nth (vals nums) y * nth (vals nums) z| ≤
            r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_lo : 4 ≤ (vals nums).length) (h_len_hi : (vals nums).length ≤ 10000)
    (h_bnd : ∀ v ∈ vals nums, 1 ≤ v ∧ v ≤ 10000)
    (r : Std.I64) (h_r : Aegis.MaxProductDifference.max_product_difference nums = ok r), ∀ w x y z : ℕ,
      w < (vals nums).length → x < (vals nums).length → y < (vals nums).length →
        z < (vals nums).length → Pairwise4 w x y z →
          |nth (vals nums) w * nth (vals nums) x - nth (vals nums) y * nth (vals nums) z| ≤
            r.val) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if nums[0] = nums[1] = ... = nums[n-1].
  Preconditions: Let n = len(nums). 4 <= n <= 10000 and 1 <= nums[i] <= 10000 for every 0 <= i < n. -/
theorem spec_7 (nums : Slice Std.I64)
    (h_len_lo : 4 ≤ (vals nums).length) (h_len_hi : (vals nums).length ≤ 10000)
    (h_bnd : ∀ v ∈ vals nums, 1 ≤ v ∧ v ≤ 10000)
    (r : Std.I64) (h_r : Aegis.MaxProductDifference.max_product_difference nums = ok r) :
    r.val = 0 ↔ ∀ i : ℕ, i < (vals nums).length → nth (vals nums) i = nth (vals nums) 0 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_lo : 4 ≤ (vals nums).length) (h_len_hi : (vals nums).length ≤ 10000)
    (h_bnd : ∀ v ∈ vals nums, 1 ≤ v ∧ v ≤ 10000)
    (r : Std.I64) (h_r : Aegis.MaxProductDifference.max_product_difference nums = ok r), r.val = 0 ↔ ∀ i : ℕ, i < (vals nums).length → nth (vals nums) i = nth (vals nums) 0) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r <= 99999999.
  Preconditions: Let n = len(nums). 4 <= n <= 10000 and 1 <= nums[i] <= 10000 for every 0 <= i < n. -/
theorem spec_8 (nums : Slice Std.I64)
    (h_len_lo : 4 ≤ (vals nums).length) (h_len_hi : (vals nums).length ≤ 10000)
    (h_bnd : ∀ v ∈ vals nums, 1 ≤ v ∧ v ≤ 10000)
    (r : Std.I64) (h_r : Aegis.MaxProductDifference.max_product_difference nums = ok r) :
    0 ≤ r.val ∧ r.val ≤ 99999999 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_lo : 4 ≤ (vals nums).length) (h_len_hi : (vals nums).length ≤ 10000)
    (h_bnd : ∀ v ∈ vals nums, 1 ≤ v ∧ v ≤ 10000)
    (r : Std.I64) (h_r : Aegis.MaxProductDifference.max_product_difference nums = ok r), 0 ≤ r.val ∧ r.val ≤ 99999999) := by
  sorry

/-- Whenever the function returns a result r, writing a = nums[0], b = nums[1], c = nums[2], d = nums[3], we have r = max(|a*b - c*d|, |a*c - b*d|, |a*d - b*c|).
  Preconditions: Let n = len(nums) = 4 and 1 <= nums[i] <= 10000 for every 0 <= i < 4. -/
theorem spec_9 (nums : Slice Std.I64)
    (h_len : (vals nums).length = 4)
    (h_bnd : ∀ v ∈ vals nums, 1 ≤ v ∧ v ≤ 10000)
    (r : Std.I64) (h_r : Aegis.MaxProductDifference.max_product_difference nums = ok r) :
    r.val =
      max (max |nth (vals nums) 0 * nth (vals nums) 1 - nth (vals nums) 2 * nth (vals nums) 3|
            |nth (vals nums) 0 * nth (vals nums) 2 - nth (vals nums) 1 * nth (vals nums) 3|)
        |nth (vals nums) 0 * nth (vals nums) 3 - nth (vals nums) 1 * nth (vals nums) 2| := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len : (vals nums).length = 4)
    (h_bnd : ∀ v ∈ vals nums, 1 ≤ v ∧ v ≤ 10000)
    (r : Std.I64) (h_r : Aegis.MaxProductDifference.max_product_difference nums = ok r), r.val =
      max (max |nth (vals nums) 0 * nth (vals nums) 1 - nth (vals nums) 2 * nth (vals nums) 3|
            |nth (vals nums) 0 * nth (vals nums) 2 - nth (vals nums) 1 * nth (vals nums) 3|)
        |nth (vals nums) 0 * nth (vals nums) 3 - nth (vals nums) 1 * nth (vals nums) 2|) := by
  sorry

/-- Whenever max_product_difference(nums) returns a result r and max_product_difference(nums') returns a result r' for a slice nums' that is a permutation of nums (same length and same multiset of entries) and also satisfies the same length and value bounds, we have r = r'.
  Preconditions: Let n = len(nums). 4 <= n <= 10000 and 1 <= nums[i] <= 10000 for every 0 <= i < n. -/
theorem spec_10 (nums nums' : Slice Std.I64)
    (h_len_lo : 4 ≤ (vals nums).length) (h_len_hi : (vals nums).length ≤ 10000)
    (h_bnd : ∀ v ∈ vals nums, 1 ≤ v ∧ v ≤ 10000)
    (h_len_lo' : 4 ≤ (vals nums').length) (h_len_hi' : (vals nums').length ≤ 10000)
    (h_bnd' : ∀ v ∈ vals nums', 1 ≤ v ∧ v ≤ 10000)
    (h_perm : (vals nums').Perm (vals nums))
    (r r' : Std.I64)
    (h_r : Aegis.MaxProductDifference.max_product_difference nums = ok r)
    (h_r' : Aegis.MaxProductDifference.max_product_difference nums' = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums nums' : Slice Std.I64)
    (h_len_lo : 4 ≤ (vals nums).length) (h_len_hi : (vals nums).length ≤ 10000)
    (h_bnd : ∀ v ∈ vals nums, 1 ≤ v ∧ v ≤ 10000)
    (h_len_lo' : 4 ≤ (vals nums').length) (h_len_hi' : (vals nums').length ≤ 10000)
    (h_bnd' : ∀ v ∈ vals nums', 1 ≤ v ∧ v ≤ 10000)
    (h_perm : (vals nums').Perm (vals nums))
    (r r' : Std.I64)
    (h_r : Aegis.MaxProductDifference.max_product_difference nums = ok r)
    (h_r' : Aegis.MaxProductDifference.max_product_difference nums' = ok r'), r.val = r'.val) := by
  sorry

/-- Whenever max_product_difference(nums) returns a result r and max_product_difference(nums') returns a result r' for a slice nums' of the same length such that nums'[i] = k * nums[i] for every 0 <= i < n, for some positive integer k, and nums' also satisfies 1 <= nums'[i] <= 10000 for every i, we have r' = k*k*r.
  Preconditions: Let n = len(nums). 4 <= n <= 10000 and 1 <= nums[i] <= 10000 for every 0 <= i < n. -/
theorem spec_11 (nums nums' : Slice Std.I64)
    (h_len_lo : 4 ≤ (vals nums).length) (h_len_hi : (vals nums).length ≤ 10000)
    (h_bnd : ∀ v ∈ vals nums, 1 ≤ v ∧ v ≤ 10000)
    (h_len_lo' : 4 ≤ (vals nums').length) (h_len_hi' : (vals nums').length ≤ 10000)
    (h_bnd' : ∀ v ∈ vals nums', 1 ≤ v ∧ v ≤ 10000)
    (h_len_eq : (vals nums').length = (vals nums).length)
    (k : ℤ) (h_k : 0 < k)
    (h_scale : ∀ i : ℕ, i < (vals nums).length → nth (vals nums') i = k * nth (vals nums) i)
    (r r' : Std.I64)
    (h_r : Aegis.MaxProductDifference.max_product_difference nums = ok r)
    (h_r' : Aegis.MaxProductDifference.max_product_difference nums' = ok r') :
    r'.val = k * k * r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums nums' : Slice Std.I64)
    (h_len_lo : 4 ≤ (vals nums).length) (h_len_hi : (vals nums).length ≤ 10000)
    (h_bnd : ∀ v ∈ vals nums, 1 ≤ v ∧ v ≤ 10000)
    (h_len_lo' : 4 ≤ (vals nums').length) (h_len_hi' : (vals nums').length ≤ 10000)
    (h_bnd' : ∀ v ∈ vals nums', 1 ≤ v ∧ v ≤ 10000)
    (h_len_eq : (vals nums').length = (vals nums).length)
    (k : ℤ) (h_k : 0 < k)
    (h_scale : ∀ i : ℕ, i < (vals nums).length → nth (vals nums') i = k * nth (vals nums) i)
    (r r' : Std.I64)
    (h_r : Aegis.MaxProductDifference.max_product_difference nums = ok r)
    (h_r' : Aegis.MaxProductDifference.max_product_difference nums' = ok r'), r'.val = k * k * r.val) := by
  sorry

end AegisSpec.MaxProductDifference
