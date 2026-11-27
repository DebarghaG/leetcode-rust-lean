import Aegis.StableMountains.Code.Funs

/-!
# Specifications of `Aegis.StableMountains.stable_mountains`

LeetCode problem `find-indices-of-stable-mountains`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.StableMountains

def hvals (height : Slice Std.I64) : List Int := height.val.map (fun x => x.val)

def hlen (height : Slice Std.I64) : Nat := height.val.length

def heightAt (height : Slice Std.I64) (i : Int) : Int := (hvals height).getD i.toNat 0

def rvals (r : alloc.vec.Vec Std.I64) : List Int := r.val.map (fun x => x.val)

def resultAt (r : alloc.vec.Vec Std.I64) (j : Nat) : Int := (rvals r).getD j 0

def stableCount (height : Slice Std.I64) (threshold : Int) : Nat :=
  (List.range (hlen height)).countP
    (fun i => decide (1 ≤ i ∧ heightAt height ((i : Int) - 1) > threshold))

/-- The function returns a result r, and r contains exactly the stable mountain indices, each exactly once, in some order: for every integer v, the number of positions j with 0 <= j < len(r) and r[j] = v equals 1 if (1 <= v <= len(height) - 1 and height[v - 1] > threshold), and equals 0 otherwise. (Equivalently, as a multiset r is exactly the set { i : 1 <= i < len(height) and height[i - 1] > threshold }.)
  Preconditions: height is a slice of 64-bit integers with 2 <= len(height) <= 100 and 1 <= height[i] <= 100 for every i with 0 <= i < len(height); threshold is a 64-bit integer with 1 <= threshold <= 100. -/
theorem spec_1 (height : Slice Std.I64) (threshold : Std.I64)
    (hlen_lo : 2 ≤ hlen height) (hlen_hi : hlen height ≤ 100)
    (hheight : ∀ i : Nat, i < hlen height →
      1 ≤ heightAt height (i : Int) ∧ heightAt height (i : Int) ≤ 100)
    (hthreshold_lo : 1 ≤ threshold.val) (hthreshold_hi : threshold.val ≤ 100) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.StableMountains.stable_mountains height threshold = ok r ∧
        ∀ v : Int,
          (rvals r).count v =
            if 1 ≤ v ∧ v ≤ (hlen height : Int) - 1 ∧ heightAt height (v - 1) > threshold.val
              then 1
              else 0 := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (height : Slice Std.I64) (threshold : Std.I64)
    (hlen_lo : 2 ≤ hlen height) (hlen_hi : hlen height ≤ 100)
    (hheight : ∀ i : Nat, i < hlen height →
      1 ≤ heightAt height (i : Int) ∧ heightAt height (i : Int) ≤ 100)
    (hthreshold_lo : 1 ≤ threshold.val) (hthreshold_hi : threshold.val ≤ 100), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.StableMountains.stable_mountains height threshold = ok r ∧
        ∀ v : Int,
          (rvals r).count v =
            if 1 ≤ v ∧ v ≤ (hlen height : Int) - 1 ∧ heightAt height (v - 1) > threshold.val
              then 1
              else 0) := by
  sorry

/-- For every such height and threshold, the function returns a result r; it never fails (no arithmetic overflow, no out-of-bounds access, no panic).
  Preconditions: height is a slice of 64-bit integers with 2 <= len(height) <= 100 and 1 <= height[i] <= 100 for every i with 0 <= i < len(height); threshold is a 64-bit integer with 1 <= threshold <= 100. -/
theorem spec_2 (height : Slice Std.I64) (threshold : Std.I64)
    (hlen_lo : 2 ≤ hlen height) (hlen_hi : hlen height ≤ 100)
    (hheight : ∀ i : Nat, i < hlen height →
      1 ≤ heightAt height (i : Int) ∧ heightAt height (i : Int) ≤ 100)
    (hthreshold_lo : 1 ≤ threshold.val) (hthreshold_hi : threshold.val ≤ 100) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.StableMountains.stable_mountains height threshold = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (height : Slice Std.I64) (threshold : Std.I64)
    (hlen_lo : 2 ≤ hlen height) (hlen_hi : hlen height ≤ 100)
    (hheight : ∀ i : Nat, i < hlen height →
      1 ≤ heightAt height (i : Int) ∧ heightAt height (i : Int) ≤ 100)
    (hthreshold_lo : 1 ≤ threshold.val) (hthreshold_hi : threshold.val ≤ 100), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.StableMountains.stable_mountains height threshold = ok r) := by
  sorry

/-- Whenever the function returns a result r, every element of r is a valid non-zero index of height: for every j with 0 <= j < len(r), 1 <= r[j] <= len(height) - 1. In particular, 0 never occurs in r and no index >= len(height) occurs in r.
  Preconditions: height is a slice of 64-bit integers with 2 <= len(height) <= 100 and 1 <= height[i] <= 100 for every i with 0 <= i < len(height); threshold is a 64-bit integer with 1 <= threshold <= 100. -/
theorem spec_3 (height : Slice Std.I64) (threshold : Std.I64)
    (hlen_lo : 2 ≤ hlen height) (hlen_hi : hlen height ≤ 100)
    (hheight : ∀ i : Nat, i < hlen height →
      1 ≤ heightAt height (i : Int) ∧ heightAt height (i : Int) ≤ 100)
    (hthreshold_lo : 1 ≤ threshold.val) (hthreshold_hi : threshold.val ≤ 100) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.StableMountains.stable_mountains height threshold = ok r →
        ∀ j : Nat, j < (rvals r).length →
          1 ≤ resultAt r j ∧ resultAt r j ≤ (hlen height : Int) - 1 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (height : Slice Std.I64) (threshold : Std.I64)
    (hlen_lo : 2 ≤ hlen height) (hlen_hi : hlen height ≤ 100)
    (hheight : ∀ i : Nat, i < hlen height →
      1 ≤ heightAt height (i : Int) ∧ heightAt height (i : Int) ≤ 100)
    (hthreshold_lo : 1 ≤ threshold.val) (hthreshold_hi : threshold.val ≤ 100), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.StableMountains.stable_mountains height threshold = ok r →
        ∀ j : Nat, j < (rvals r).length →
          1 ≤ resultAt r j ∧ resultAt r j ≤ (hlen height : Int) - 1) := by
  sorry

/-- Whenever the function returns a result r, every returned index is a valid stable mountain: for every j with 0 <= j < len(r), 1 <= r[j] < len(height) and height[r[j] - 1] > threshold.
  Preconditions: height is a slice of 64-bit integers with 2 <= len(height) <= 100 and 1 <= height[i] <= 100 for every i with 0 <= i < len(height); threshold is a 64-bit integer with 1 <= threshold <= 100. -/
theorem spec_4 (height : Slice Std.I64) (threshold : Std.I64)
    (hlen_lo : 2 ≤ hlen height) (hlen_hi : hlen height ≤ 100)
    (hheight : ∀ i : Nat, i < hlen height →
      1 ≤ heightAt height (i : Int) ∧ heightAt height (i : Int) ≤ 100)
    (hthreshold_lo : 1 ≤ threshold.val) (hthreshold_hi : threshold.val ≤ 100) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.StableMountains.stable_mountains height threshold = ok r →
        ∀ j : Nat, j < (rvals r).length →
          1 ≤ resultAt r j ∧ resultAt r j < (hlen height : Int) ∧
            heightAt height (resultAt r j - 1) > threshold.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (height : Slice Std.I64) (threshold : Std.I64)
    (hlen_lo : 2 ≤ hlen height) (hlen_hi : hlen height ≤ 100)
    (hheight : ∀ i : Nat, i < hlen height →
      1 ≤ heightAt height (i : Int) ∧ heightAt height (i : Int) ≤ 100)
    (hthreshold_lo : 1 ≤ threshold.val) (hthreshold_hi : threshold.val ≤ 100), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.StableMountains.stable_mountains height threshold = ok r →
        ∀ j : Nat, j < (rvals r).length →
          1 ≤ resultAt r j ∧ resultAt r j < (hlen height : Int) ∧
            heightAt height (resultAt r j - 1) > threshold.val) := by
  sorry

/-- Whenever the function returns a result r, every stable mountain index is present in r: for every i with 1 <= i < len(height), if height[i - 1] > threshold then there exists j with 0 <= j < len(r) and r[j] = i.
  Preconditions: height is a slice of 64-bit integers with 2 <= len(height) <= 100 and 1 <= height[i] <= 100 for every i with 0 <= i < len(height); threshold is a 64-bit integer with 1 <= threshold <= 100. -/
theorem spec_5 (height : Slice Std.I64) (threshold : Std.I64)
    (hlen_lo : 2 ≤ hlen height) (hlen_hi : hlen height ≤ 100)
    (hheight : ∀ i : Nat, i < hlen height →
      1 ≤ heightAt height (i : Int) ∧ heightAt height (i : Int) ≤ 100)
    (hthreshold_lo : 1 ≤ threshold.val) (hthreshold_hi : threshold.val ≤ 100) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.StableMountains.stable_mountains height threshold = ok r →
        ∀ i : Nat, 1 ≤ i → i < hlen height →
          heightAt height ((i : Int) - 1) > threshold.val →
            ∃ j : Nat, j < (rvals r).length ∧ resultAt r j = (i : Int) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (height : Slice Std.I64) (threshold : Std.I64)
    (hlen_lo : 2 ≤ hlen height) (hlen_hi : hlen height ≤ 100)
    (hheight : ∀ i : Nat, i < hlen height →
      1 ≤ heightAt height (i : Int) ∧ heightAt height (i : Int) ≤ 100)
    (hthreshold_lo : 1 ≤ threshold.val) (hthreshold_hi : threshold.val ≤ 100), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.StableMountains.stable_mountains height threshold = ok r →
        ∀ i : Nat, 1 ≤ i → i < hlen height →
          heightAt height ((i : Int) - 1) > threshold.val →
            ∃ j : Nat, j < (rvals r).length ∧ resultAt r j = (i : Int)) := by
  sorry

/-- Whenever the function returns a result r, r has no repeated elements: for all j and k with 0 <= j < k < len(r), r[j] != r[k].
  Preconditions: height is a slice of 64-bit integers with 2 <= len(height) <= 100 and 1 <= height[i] <= 100 for every i with 0 <= i < len(height); threshold is a 64-bit integer with 1 <= threshold <= 100. -/
theorem spec_6 (height : Slice Std.I64) (threshold : Std.I64)
    (hlen_lo : 2 ≤ hlen height) (hlen_hi : hlen height ≤ 100)
    (hheight : ∀ i : Nat, i < hlen height →
      1 ≤ heightAt height (i : Int) ∧ heightAt height (i : Int) ≤ 100)
    (hthreshold_lo : 1 ≤ threshold.val) (hthreshold_hi : threshold.val ≤ 100) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.StableMountains.stable_mountains height threshold = ok r →
        ∀ j k : Nat, j < k → k < (rvals r).length → resultAt r j ≠ resultAt r k := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (height : Slice Std.I64) (threshold : Std.I64)
    (hlen_lo : 2 ≤ hlen height) (hlen_hi : hlen height ≤ 100)
    (hheight : ∀ i : Nat, i < hlen height →
      1 ≤ heightAt height (i : Int) ∧ heightAt height (i : Int) ≤ 100)
    (hthreshold_lo : 1 ≤ threshold.val) (hthreshold_hi : threshold.val ≤ 100), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.StableMountains.stable_mountains height threshold = ok r →
        ∀ j k : Nat, j < k → k < (rvals r).length → resultAt r j ≠ resultAt r k) := by
  sorry

/-- Whenever the function returns a result r, the length of r equals the number of stable mountains: len(r) = the number of indices i with 1 <= i < len(height) and height[i - 1] > threshold.
  Preconditions: height is a slice of 64-bit integers with 2 <= len(height) <= 100 and 1 <= height[i] <= 100 for every i with 0 <= i < len(height); threshold is a 64-bit integer with 1 <= threshold <= 100. -/
theorem spec_7 (height : Slice Std.I64) (threshold : Std.I64)
    (hlen_lo : 2 ≤ hlen height) (hlen_hi : hlen height ≤ 100)
    (hheight : ∀ i : Nat, i < hlen height →
      1 ≤ heightAt height (i : Int) ∧ heightAt height (i : Int) ≤ 100)
    (hthreshold_lo : 1 ≤ threshold.val) (hthreshold_hi : threshold.val ≤ 100) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.StableMountains.stable_mountains height threshold = ok r →
        (rvals r).length = stableCount height threshold.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (height : Slice Std.I64) (threshold : Std.I64)
    (hlen_lo : 2 ≤ hlen height) (hlen_hi : hlen height ≤ 100)
    (hheight : ∀ i : Nat, i < hlen height →
      1 ≤ heightAt height (i : Int) ∧ heightAt height (i : Int) ≤ 100)
    (hthreshold_lo : 1 ≤ threshold.val) (hthreshold_hi : threshold.val ≤ 100), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.StableMountains.stable_mountains height threshold = ok r →
        (rvals r).length = stableCount height threshold.val) := by
  sorry

/-- Whenever the function returns a result r and len(height) = 2, the answer is determined by the single candidate mountain 1: if height[0] > threshold then len(r) = 1 and r[0] = 1; if height[0] <= threshold then len(r) = 0.
  Preconditions: height is a slice of 64-bit integers with len(height) = 2 and 1 <= height[i] <= 100 for i with 0 <= i < 2; threshold is a 64-bit integer with 1 <= threshold <= 100. -/
theorem spec_8 (height : Slice Std.I64) (threshold : Std.I64)
    (hlen : hlen height = 2)
    (hheight : ∀ i : Nat, i < 2 →
      1 ≤ heightAt height (i : Int) ∧ heightAt height (i : Int) ≤ 100)
    (hthreshold_lo : 1 ≤ threshold.val) (hthreshold_hi : threshold.val ≤ 100) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.StableMountains.stable_mountains height threshold = ok r →
        ((heightAt height 0 > threshold.val →
            (rvals r).length = 1 ∧ resultAt r 0 = 1) ∧
          (heightAt height 0 ≤ threshold.val → (rvals r).length = 0)) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (height : Slice Std.I64) (threshold : Std.I64)
    (hlen : hlen height = 2)
    (hheight : ∀ i : Nat, i < 2 →
      1 ≤ heightAt height (i : Int) ∧ heightAt height (i : Int) ≤ 100)
    (hthreshold_lo : 1 ≤ threshold.val) (hthreshold_hi : threshold.val ≤ 100), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.StableMountains.stable_mountains height threshold = ok r →
        ((heightAt height 0 > threshold.val →
            (rvals r).length = 1 ∧ resultAt r 0 = 1) ∧
          (heightAt height 0 ≤ threshold.val → (rvals r).length = 0))) := by
  sorry

/-- Whenever the function returns a result r, len(r) >= 1 if and only if there exists an index i with 1 <= i < len(height) and height[i - 1] > threshold.
  Preconditions: height is a slice of 64-bit integers with 2 <= len(height) <= 100 and 1 <= height[i] <= 100 for every i with 0 <= i < len(height); threshold is a 64-bit integer with 1 <= threshold <= 100. -/
theorem spec_9 (height : Slice Std.I64) (threshold : Std.I64)
    (hlen_lo : 2 ≤ hlen height) (hlen_hi : hlen height ≤ 100)
    (hheight : ∀ i : Nat, i < hlen height →
      1 ≤ heightAt height (i : Int) ∧ heightAt height (i : Int) ≤ 100)
    (hthreshold_lo : 1 ≤ threshold.val) (hthreshold_hi : threshold.val ≤ 100) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.StableMountains.stable_mountains height threshold = ok r →
        (1 ≤ (rvals r).length ↔
          ∃ i : Nat, 1 ≤ i ∧ i < hlen height ∧
            heightAt height ((i : Int) - 1) > threshold.val) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (height : Slice Std.I64) (threshold : Std.I64)
    (hlen_lo : 2 ≤ hlen height) (hlen_hi : hlen height ≤ 100)
    (hheight : ∀ i : Nat, i < hlen height →
      1 ≤ heightAt height (i : Int) ∧ heightAt height (i : Int) ≤ 100)
    (hthreshold_lo : 1 ≤ threshold.val) (hthreshold_hi : threshold.val ≤ 100), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.StableMountains.stable_mountains height threshold = ok r →
        (1 ≤ (rvals r).length ↔
          ∃ i : Nat, 1 ≤ i ∧ i < hlen height ∧
            heightAt height ((i : Int) - 1) > threshold.val)) := by
  sorry

/-- Let r1 be the result of calling the function on (height, t1) and r2 the result on (height, t2) (both exist by no-failure). Then every index returned for the larger threshold is also returned for the smaller threshold: for every j with 0 <= j < len(r2) there exists k with 0 <= k < len(r1) and r1[k] = r2[j].
  Preconditions: height is a slice of 64-bit integers with 2 <= len(height) <= 100 and 1 <= height[i] <= 100 for every i with 0 <= i < len(height); t1 and t2 are 64-bit integers with 1 <= t1 <= t2 <= 100. -/
theorem spec_10 (height : Slice Std.I64) (t1 t2 : Std.I64)
    (hlen_lo : 2 ≤ hlen height) (hlen_hi : hlen height ≤ 100)
    (hheight : ∀ i : Nat, i < hlen height →
      1 ≤ heightAt height (i : Int) ∧ heightAt height (i : Int) ≤ 100)
    (ht1_lo : 1 ≤ t1.val) (ht_le : t1.val ≤ t2.val) (ht2_hi : t2.val ≤ 100) :
    ∀ r1 r2 : alloc.vec.Vec Std.I64,
      Aegis.StableMountains.stable_mountains height t1 = ok r1 →
        Aegis.StableMountains.stable_mountains height t2 = ok r2 →
          ∀ j : Nat, j < (rvals r2).length →
            ∃ k : Nat, k < (rvals r1).length ∧ resultAt r1 k = resultAt r2 j := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (height : Slice Std.I64) (t1 t2 : Std.I64)
    (hlen_lo : 2 ≤ hlen height) (hlen_hi : hlen height ≤ 100)
    (hheight : ∀ i : Nat, i < hlen height →
      1 ≤ heightAt height (i : Int) ∧ heightAt height (i : Int) ≤ 100)
    (ht1_lo : 1 ≤ t1.val) (ht_le : t1.val ≤ t2.val) (ht2_hi : t2.val ≤ 100), ∀ r1 r2 : alloc.vec.Vec Std.I64,
      Aegis.StableMountains.stable_mountains height t1 = ok r1 →
        Aegis.StableMountains.stable_mountains height t2 = ok r2 →
          ∀ j : Nat, j < (rvals r2).length →
            ∃ k : Nat, k < (rvals r1).length ∧ resultAt r1 k = resultAt r2 j) := by
  sorry

/-- Suppose that for every i with 0 <= i < n - 1, (height1[i] > t1) holds if and only if (height2[i] > t2) holds. Let r1, r2 be the results on (height1, t1) and (height2, t2) respectively (both exist by no-failure). Then r1 and r2 contain the same multiset of indices: for every integer v, the number of positions j with r1[j] = v equals the number of positions j with r2[j] = v.
  Preconditions: height1 and height2 are slices of 64-bit integers with len(height1) = len(height2) = n, 2 <= n <= 100, and all entries of both in the range [1, 100]; t1 and t2 are 64-bit integers with 1 <= t1 <= 100 and 1 <= t2 <= 100. -/
theorem spec_11 (height1 height2 : Slice Std.I64) (t1 t2 : Std.I64) (n : Nat)
    (hlen1 : hlen height1 = n) (hlen2 : hlen height2 = n)
    (hn_lo : 2 ≤ n) (hn_hi : n ≤ 100)
    (hheight1 : ∀ i : Nat, i < n →
      1 ≤ heightAt height1 (i : Int) ∧ heightAt height1 (i : Int) ≤ 100)
    (hheight2 : ∀ i : Nat, i < n →
      1 ≤ heightAt height2 (i : Int) ∧ heightAt height2 (i : Int) ≤ 100)
    (ht1_lo : 1 ≤ t1.val) (ht1_hi : t1.val ≤ 100)
    (ht2_lo : 1 ≤ t2.val) (ht2_hi : t2.val ≤ 100)
    (hagree : ∀ i : Nat, i < n - 1 →
      (heightAt height1 (i : Int) > t1.val ↔ heightAt height2 (i : Int) > t2.val)) :
    ∀ r1 r2 : alloc.vec.Vec Std.I64,
      Aegis.StableMountains.stable_mountains height1 t1 = ok r1 →
        Aegis.StableMountains.stable_mountains height2 t2 = ok r2 →
          ∀ v : Int, (rvals r1).count v = (rvals r2).count v := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (height1 height2 : Slice Std.I64) (t1 t2 : Std.I64) (n : Nat)
    (hlen1 : hlen height1 = n) (hlen2 : hlen height2 = n)
    (hn_lo : 2 ≤ n) (hn_hi : n ≤ 100)
    (hheight1 : ∀ i : Nat, i < n →
      1 ≤ heightAt height1 (i : Int) ∧ heightAt height1 (i : Int) ≤ 100)
    (hheight2 : ∀ i : Nat, i < n →
      1 ≤ heightAt height2 (i : Int) ∧ heightAt height2 (i : Int) ≤ 100)
    (ht1_lo : 1 ≤ t1.val) (ht1_hi : t1.val ≤ 100)
    (ht2_lo : 1 ≤ t2.val) (ht2_hi : t2.val ≤ 100)
    (hagree : ∀ i : Nat, i < n - 1 →
      (heightAt height1 (i : Int) > t1.val ↔ heightAt height2 (i : Int) > t2.val)), ∀ r1 r2 : alloc.vec.Vec Std.I64,
      Aegis.StableMountains.stable_mountains height1 t1 = ok r1 →
        Aegis.StableMountains.stable_mountains height2 t2 = ok r2 →
          ∀ v : Int, (rvals r1).count v = (rvals r2).count v) := by
  sorry

/-- Let r1 be the result on (height1, threshold) and r2 the result on (height2, threshold) (both exist by no-failure). Then every index returned for height1 is also returned for height2: for every j with 0 <= j < len(r1) there exists k with 0 <= k < len(r2) and r2[k] = r1[j].
  Preconditions: height1 and height2 are slices of 64-bit integers with len(height1) = len(height2) = n, 2 <= n <= 100, all entries in [1, 100], and height1[i] <= height2[i] for every i with 0 <= i < n; threshold is a 64-bit integer with 1 <= threshold <= 100. -/
theorem spec_12 (height1 height2 : Slice Std.I64) (threshold : Std.I64) (n : Nat)
    (hlen1 : hlen height1 = n) (hlen2 : hlen height2 = n)
    (hn_lo : 2 ≤ n) (hn_hi : n ≤ 100)
    (hheight1 : ∀ i : Nat, i < n →
      1 ≤ heightAt height1 (i : Int) ∧ heightAt height1 (i : Int) ≤ 100)
    (hheight2 : ∀ i : Nat, i < n →
      1 ≤ heightAt height2 (i : Int) ∧ heightAt height2 (i : Int) ≤ 100)
    (hthreshold_lo : 1 ≤ threshold.val) (hthreshold_hi : threshold.val ≤ 100)
    (hmono : ∀ i : Nat, i < n → heightAt height1 (i : Int) ≤ heightAt height2 (i : Int)) :
    ∀ r1 r2 : alloc.vec.Vec Std.I64,
      Aegis.StableMountains.stable_mountains height1 threshold = ok r1 →
        Aegis.StableMountains.stable_mountains height2 threshold = ok r2 →
          ∀ j : Nat, j < (rvals r1).length →
            ∃ k : Nat, k < (rvals r2).length ∧ resultAt r2 k = resultAt r1 j := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (height1 height2 : Slice Std.I64) (threshold : Std.I64) (n : Nat)
    (hlen1 : hlen height1 = n) (hlen2 : hlen height2 = n)
    (hn_lo : 2 ≤ n) (hn_hi : n ≤ 100)
    (hheight1 : ∀ i : Nat, i < n →
      1 ≤ heightAt height1 (i : Int) ∧ heightAt height1 (i : Int) ≤ 100)
    (hheight2 : ∀ i : Nat, i < n →
      1 ≤ heightAt height2 (i : Int) ∧ heightAt height2 (i : Int) ≤ 100)
    (hthreshold_lo : 1 ≤ threshold.val) (hthreshold_hi : threshold.val ≤ 100)
    (hmono : ∀ i : Nat, i < n → heightAt height1 (i : Int) ≤ heightAt height2 (i : Int)), ∀ r1 r2 : alloc.vec.Vec Std.I64,
      Aegis.StableMountains.stable_mountains height1 threshold = ok r1 →
        Aegis.StableMountains.stable_mountains height2 threshold = ok r2 →
          ∀ j : Nat, j < (rvals r1).length →
            ∃ k : Nat, k < (rvals r2).length ∧ resultAt r2 k = resultAt r1 j) := by
  sorry

end AegisSpec.StableMountains
