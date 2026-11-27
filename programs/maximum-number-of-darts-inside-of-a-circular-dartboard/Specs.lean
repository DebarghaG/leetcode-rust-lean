import Aegis.NumPoints.Code.Funs
import Mathlib.Data.Real.Basic

/-!
# Specifications of `Aegis.NumPoints.num_points`

LeetCode problem `maximum-number-of-darts-inside-of-a-circular-dartboard`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.NumPoints (num_points)

namespace AegisSpec.NumPoints

def coords (darts : Slice (alloc.vec.Vec Std.I64)) : List (ℤ × ℤ) :=
  darts.val.map fun v =>
    match v.val with
    | [x, y] => (x.val, y.val)
    | _ => (0, 0)

noncomputable def inDisk (pts : List (ℤ × ℤ)) (rr : ℤ) (cx cy : ℝ) : List (ℤ × ℤ) :=
  pts.filter fun p => ((p.1 : ℝ) - cx) ^ 2 + ((p.2 : ℝ) - cy) ^ 2 ≤ (rr : ℝ) ^ 2

noncomputable def countInDisk (pts : List (ℤ × ℤ)) (rr : ℤ) (cx cy : ℝ) : ℕ :=
  (inDisk pts rr cx cy).length

noncomputable def IsMaxCount (pts : List (ℤ × ℤ)) (rr : ℤ) (k : ℤ) : Prop :=
  (∀ cx cy : ℝ, ((countInDisk pts rr cx cy : ℕ) : ℤ) ≤ k) ∧
    ∃ cx cy : ℝ, ((countInDisk pts rr cx cy : ℕ) : ℤ) = k

/-- Whenever num_points(darts, r) returns Ok k, k equals the maximum, over all real centers (cx, cy), of the number of indices i with 0 <= i < n and (xi - cx)^2 + (yi - cy)^2 <= r^2, where xi, yi, and r are interpreted as real numbers. The disk is closed, so darts on the boundary count.
  Preconditions: Let n = len(darts). Assume 1 <= n <= 100; each darts[i] is a vector of length 2, written darts[i] = [xi, yi]; -10000 <= xi, yi <= 10000; the pairs (xi, yi) are pairwise distinct; and 1 <= r <= 5000. -/
theorem spec_1
    (darts : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64) (k : Std.I64) (n : ℕ)
    (hlen : darts.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
    (hlen2 : ∀ v ∈ darts.val, v.val.length = 2)
    (hbound : ∀ p ∈ coords darts,
      -10000 ≤ p.1 ∧ p.1 ≤ 10000 ∧ -10000 ≤ p.2 ∧ p.2 ≤ 10000)
    (hnodup : (coords darts).Nodup)
    (hr : 1 ≤ r.val ∧ r.val ≤ 5000)
    (hres : num_points darts r = ok k) :
    IsMaxCount (coords darts) r.val k.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (darts : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64) (k : Std.I64) (n : ℕ)
    (hlen : darts.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
    (hlen2 : ∀ v ∈ darts.val, v.val.length = 2)
    (hbound : ∀ p ∈ coords darts,
      -10000 ≤ p.1 ∧ p.1 ≤ 10000 ∧ -10000 ≤ p.2 ∧ p.2 ≤ 10000)
    (hnodup : (coords darts).Nodup)
    (hr : 1 ≤ r.val ∧ r.val ≤ 5000)
    (hres : num_points darts r = ok k), IsMaxCount (coords darts) r.val k.val) := by
  sorry

/-- For every such input, num_points(darts, r) returns Ok k for some 64-bit integer k; it does not fail, panic, or overflow.
  Preconditions: Let n = len(darts). Assume 1 <= n <= 100; each darts[i] is a vector of length 2, written darts[i] = [xi, yi]; -10000 <= xi, yi <= 10000; the pairs (xi, yi) are pairwise distinct; and 1 <= r <= 5000. -/
theorem spec_2
    (darts : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64) (n : ℕ)
    (hlen : darts.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
    (hlen2 : ∀ v ∈ darts.val, v.val.length = 2)
    (hbound : ∀ p ∈ coords darts,
      -10000 ≤ p.1 ∧ p.1 ≤ 10000 ∧ -10000 ≤ p.2 ∧ p.2 ≤ 10000)
    (hnodup : (coords darts).Nodup)
    (hr : 1 ≤ r.val ∧ r.val ≤ 5000) :
    ∃ k : Std.I64, num_points darts r = ok k := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (darts : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64) (n : ℕ)
    (hlen : darts.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
    (hlen2 : ∀ v ∈ darts.val, v.val.length = 2)
    (hbound : ∀ p ∈ coords darts,
      -10000 ≤ p.1 ∧ p.1 ≤ 10000 ∧ -10000 ≤ p.2 ∧ p.2 ≤ 10000)
    (hnodup : (coords darts).Nodup)
    (hr : 1 ≤ r.val ∧ r.val ≤ 5000), ∃ k : Std.I64, num_points darts r = ok k) := by
  sorry

/-- Whenever num_points(darts, r) returns Ok k, 0 <= k <= n.
  Preconditions: Let n = len(darts). Assume 1 <= n <= 100; each darts[i] has length 2; coordinates are in [-10000, 10000]; darts are pairwise distinct; and 1 <= r <= 5000. -/
theorem spec_3
    (darts : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64) (k : Std.I64) (n : ℕ)
    (hlen : darts.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
    (hlen2 : ∀ v ∈ darts.val, v.val.length = 2)
    (hbound : ∀ p ∈ coords darts,
      -10000 ≤ p.1 ∧ p.1 ≤ 10000 ∧ -10000 ≤ p.2 ∧ p.2 ≤ 10000)
    (hnodup : (coords darts).Nodup)
    (hr : 1 ≤ r.val ∧ r.val ≤ 5000)
    (hres : num_points darts r = ok k) :
    0 ≤ k.val ∧ k.val ≤ (n : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (darts : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64) (k : Std.I64) (n : ℕ)
    (hlen : darts.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
    (hlen2 : ∀ v ∈ darts.val, v.val.length = 2)
    (hbound : ∀ p ∈ coords darts,
      -10000 ≤ p.1 ∧ p.1 ≤ 10000 ∧ -10000 ≤ p.2 ∧ p.2 ≤ 10000)
    (hnodup : (coords darts).Nodup)
    (hr : 1 ≤ r.val ∧ r.val ≤ 5000)
    (hres : num_points darts r = ok k), 0 ≤ k.val ∧ k.val ≤ (n : ℤ)) := by
  sorry

/-- Whenever num_points(darts, r) returns Ok k, k >= 1.
  Preconditions: Let n = len(darts). Assume 1 <= n <= 100; each darts[i] has length 2; coordinates are in [-10000, 10000]; darts are pairwise distinct; and 1 <= r <= 5000. -/
theorem spec_4
    (darts : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64) (k : Std.I64) (n : ℕ)
    (hlen : darts.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
    (hlen2 : ∀ v ∈ darts.val, v.val.length = 2)
    (hbound : ∀ p ∈ coords darts,
      -10000 ≤ p.1 ∧ p.1 ≤ 10000 ∧ -10000 ≤ p.2 ∧ p.2 ≤ 10000)
    (hnodup : (coords darts).Nodup)
    (hr : 1 ≤ r.val ∧ r.val ≤ 5000)
    (hres : num_points darts r = ok k) :
    1 ≤ k.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (darts : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64) (k : Std.I64) (n : ℕ)
    (hlen : darts.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
    (hlen2 : ∀ v ∈ darts.val, v.val.length = 2)
    (hbound : ∀ p ∈ coords darts,
      -10000 ≤ p.1 ∧ p.1 ≤ 10000 ∧ -10000 ≤ p.2 ∧ p.2 ≤ 10000)
    (hnodup : (coords darts).Nodup)
    (hr : 1 ≤ r.val ∧ r.val ≤ 5000)
    (hres : num_points darts r = ok k), 1 ≤ k.val) := by
  sorry

/-- Whenever num_points(darts, r) returns Ok k, there exists a real center (cx, cy) such that the number of indices i with 0 <= i < n and (xi - cx)^2 + (yi - cy)^2 <= r^2 is exactly k.
  Preconditions: Let n = len(darts). Assume 1 <= n <= 100; each darts[i] has length 2, written darts[i] = [xi, yi]; coordinates are in [-10000, 10000]; darts are pairwise distinct; and 1 <= r <= 5000. -/
theorem spec_5
    (darts : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64) (k : Std.I64) (n : ℕ)
    (hlen : darts.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
    (hlen2 : ∀ v ∈ darts.val, v.val.length = 2)
    (hbound : ∀ p ∈ coords darts,
      -10000 ≤ p.1 ∧ p.1 ≤ 10000 ∧ -10000 ≤ p.2 ∧ p.2 ≤ 10000)
    (hnodup : (coords darts).Nodup)
    (hr : 1 ≤ r.val ∧ r.val ≤ 5000)
    (hres : num_points darts r = ok k) :
    ∃ cx cy : ℝ, ((countInDisk (coords darts) r.val cx cy : ℕ) : ℤ) = k.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (darts : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64) (k : Std.I64) (n : ℕ)
    (hlen : darts.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
    (hlen2 : ∀ v ∈ darts.val, v.val.length = 2)
    (hbound : ∀ p ∈ coords darts,
      -10000 ≤ p.1 ∧ p.1 ≤ 10000 ∧ -10000 ≤ p.2 ∧ p.2 ≤ 10000)
    (hnodup : (coords darts).Nodup)
    (hr : 1 ≤ r.val ∧ r.val ≤ 5000)
    (hres : num_points darts r = ok k), ∃ cx cy : ℝ, ((countInDisk (coords darts) r.val cx cy : ℕ) : ℤ) = k.val) := by
  sorry

/-- Whenever num_points(darts, r) returns Ok k, for every real center (cx, cy), the number of indices i with 0 <= i < n and (xi - cx)^2 + (yi - cy)^2 <= r^2 is at most k.
  Preconditions: Let n = len(darts). Assume 1 <= n <= 100; each darts[i] has length 2, written darts[i] = [xi, yi]; coordinates are in [-10000, 10000]; darts are pairwise distinct; and 1 <= r <= 5000. -/
theorem spec_6
    (darts : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64) (k : Std.I64) (n : ℕ)
    (hlen : darts.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
    (hlen2 : ∀ v ∈ darts.val, v.val.length = 2)
    (hbound : ∀ p ∈ coords darts,
      -10000 ≤ p.1 ∧ p.1 ≤ 10000 ∧ -10000 ≤ p.2 ∧ p.2 ≤ 10000)
    (hnodup : (coords darts).Nodup)
    (hr : 1 ≤ r.val ∧ r.val ≤ 5000)
    (hres : num_points darts r = ok k) :
    ∀ cx cy : ℝ, ((countInDisk (coords darts) r.val cx cy : ℕ) : ℤ) ≤ k.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (darts : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64) (k : Std.I64) (n : ℕ)
    (hlen : darts.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
    (hlen2 : ∀ v ∈ darts.val, v.val.length = 2)
    (hbound : ∀ p ∈ coords darts,
      -10000 ≤ p.1 ∧ p.1 ≤ 10000 ∧ -10000 ≤ p.2 ∧ p.2 ≤ 10000)
    (hnodup : (coords darts).Nodup)
    (hr : 1 ≤ r.val ∧ r.val ≤ 5000)
    (hres : num_points darts r = ok k), ∀ cx cy : ℝ, ((countInDisk (coords darts) r.val cx cy : ℕ) : ℤ) ≤ k.val) := by
  sorry

/-- Whenever num_points(darts, r) returns Ok k, k = n if and only if there exists a real center (cx, cy) such that for every i with 0 <= i < n, (xi - cx)^2 + (yi - cy)^2 <= r^2.
  Preconditions: Let n = len(darts). Assume 1 <= n <= 100; each darts[i] has length 2, written darts[i] = [xi, yi]; coordinates are in [-10000, 10000]; darts are pairwise distinct; and 1 <= r <= 5000. -/
theorem spec_7
    (darts : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64) (k : Std.I64) (n : ℕ)
    (hlen : darts.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
    (hlen2 : ∀ v ∈ darts.val, v.val.length = 2)
    (hbound : ∀ p ∈ coords darts,
      -10000 ≤ p.1 ∧ p.1 ≤ 10000 ∧ -10000 ≤ p.2 ∧ p.2 ≤ 10000)
    (hnodup : (coords darts).Nodup)
    (hr : 1 ≤ r.val ∧ r.val ≤ 5000)
    (hres : num_points darts r = ok k) :
    (k.val = (n : ℤ) ↔
      ∃ cx cy : ℝ, ((countInDisk (coords darts) r.val cx cy : ℕ) : ℤ) = (n : ℤ)) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (darts : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64) (k : Std.I64) (n : ℕ)
    (hlen : darts.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
    (hlen2 : ∀ v ∈ darts.val, v.val.length = 2)
    (hbound : ∀ p ∈ coords darts,
      -10000 ≤ p.1 ∧ p.1 ≤ 10000 ∧ -10000 ≤ p.2 ∧ p.2 ≤ 10000)
    (hnodup : (coords darts).Nodup)
    (hr : 1 ≤ r.val ∧ r.val ≤ 5000)
    (hres : num_points darts r = ok k), (k.val = (n : ℤ) ↔
      ∃ cx cy : ℝ, ((countInDisk (coords darts) r.val cx cy : ℕ) : ℤ) = (n : ℤ))) := by
  sorry

/-- Whenever num_points(darts, r) returns Ok k, k = 1.
  Preconditions: Let n = len(darts). Assume 1 <= n <= 100; each darts[i] has length 2, written darts[i] = [xi, yi]; coordinates are in [-10000, 10000]; darts are pairwise distinct; and 1 <= r <= 5000. Also assume that for every i, j with 0 <= i < j < n, (xi - xj)^2 + (yi - yj)^2 > (2*r)^2. -/
theorem spec_8
    (darts : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64) (k : Std.I64) (n : ℕ)
    (hlen : darts.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
    (hlen2 : ∀ v ∈ darts.val, v.val.length = 2)
    (hbound : ∀ p ∈ coords darts,
      -10000 ≤ p.1 ∧ p.1 ≤ 10000 ∧ -10000 ≤ p.2 ∧ p.2 ≤ 10000)
    (hnodup : (coords darts).Nodup)
    (hr : 1 ≤ r.val ∧ r.val ≤ 5000)
    (hsep : ∀ (i j : Fin (coords darts).length), i < j →
      (((coords darts).get i).1 - ((coords darts).get j).1) ^ 2 +
        (((coords darts).get i).2 - ((coords darts).get j).2) ^ 2 > (2 * r.val) ^ 2)
    (hres : num_points darts r = ok k) :
    k.val = 1 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (darts : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64) (k : Std.I64) (n : ℕ)
    (hlen : darts.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
    (hlen2 : ∀ v ∈ darts.val, v.val.length = 2)
    (hbound : ∀ p ∈ coords darts,
      -10000 ≤ p.1 ∧ p.1 ≤ 10000 ∧ -10000 ≤ p.2 ∧ p.2 ≤ 10000)
    (hnodup : (coords darts).Nodup)
    (hr : 1 ≤ r.val ∧ r.val ≤ 5000)
    (hsep : ∀ (i j : Fin (coords darts).length), i < j →
      (((coords darts).get i).1 - ((coords darts).get j).1) ^ 2 +
        (((coords darts).get i).2 - ((coords darts).get j).2) ^ 2 > (2 * r.val) ^ 2)
    (hres : num_points darts r = ok k), k.val = 1) := by
  sorry

/-- Whenever num_points(darts, r) returns Ok k and num_points(darts', r) returns Ok k', we have k = k'.
  Preconditions: Let n = len(darts). Assume 1 <= n <= 100; each darts[i] has length 2; coordinates are in [-10000, 10000]; darts are pairwise distinct; and 1 <= r <= 5000. Let p be any bijection from {0,...,n-1} to itself, and let darts' be the slice defined by darts'[i] = darts[p(i)] for 0 <= i < n. -/
theorem spec_9
    (darts darts' : Slice (alloc.vec.Vec Std.I64)) (r k k' : Std.I64) (n : ℕ)
    (hlen : darts.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
    (hlen2 : ∀ v ∈ darts.val, v.val.length = 2)
    (hbound : ∀ p ∈ coords darts,
      -10000 ≤ p.1 ∧ p.1 ≤ 10000 ∧ -10000 ≤ p.2 ∧ p.2 ≤ 10000)
    (hnodup : (coords darts).Nodup)
    (hr : 1 ≤ r.val ∧ r.val ≤ 5000)
    (p : Equiv.Perm (Fin n))
    (hdarts' : darts'.val =
      List.ofFn (fun i : Fin n => darts.val.get (Fin.cast hlen.symm (p i))))
    (hres : num_points darts r = ok k)
    (hres' : num_points darts' r = ok k') :
    k.val = k'.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (darts darts' : Slice (alloc.vec.Vec Std.I64)) (r k k' : Std.I64) (n : ℕ)
    (hlen : darts.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
    (hlen2 : ∀ v ∈ darts.val, v.val.length = 2)
    (hbound : ∀ p ∈ coords darts,
      -10000 ≤ p.1 ∧ p.1 ≤ 10000 ∧ -10000 ≤ p.2 ∧ p.2 ≤ 10000)
    (hnodup : (coords darts).Nodup)
    (hr : 1 ≤ r.val ∧ r.val ≤ 5000)
    (p : Equiv.Perm (Fin n))
    (hdarts' : darts'.val =
      List.ofFn (fun i : Fin n => darts.val.get (Fin.cast hlen.symm (p i))))
    (hres : num_points darts r = ok k)
    (hres' : num_points darts' r = ok k'), k.val = k'.val) := by
  sorry

/-- Whenever num_points(darts, r) returns Ok k and num_points(darts, r') returns Ok k', we have k <= k'.
  Preconditions: Let n = len(darts). Assume 1 <= n <= 100; each darts[i] has length 2; coordinates are in [-10000, 10000]; darts are pairwise distinct. Let r and r' be integers with 1 <= r <= r' <= 5000. -/
theorem spec_10
    (darts : Slice (alloc.vec.Vec Std.I64)) (r r' : Std.I64) (k k' : Std.I64) (n : ℕ)
    (hlen : darts.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
    (hlen2 : ∀ v ∈ darts.val, v.val.length = 2)
    (hbound : ∀ p ∈ coords darts,
      -10000 ≤ p.1 ∧ p.1 ≤ 10000 ∧ -10000 ≤ p.2 ∧ p.2 ≤ 10000)
    (hnodup : (coords darts).Nodup)
    (hr : 1 ≤ r.val ∧ r.val ≤ r'.val ∧ r'.val ≤ 5000)
    (hres : num_points darts r = ok k)
    (hres' : num_points darts r' = ok k') :
    k.val ≤ k'.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (darts : Slice (alloc.vec.Vec Std.I64)) (r r' : Std.I64) (k k' : Std.I64) (n : ℕ)
    (hlen : darts.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
    (hlen2 : ∀ v ∈ darts.val, v.val.length = 2)
    (hbound : ∀ p ∈ coords darts,
      -10000 ≤ p.1 ∧ p.1 ≤ 10000 ∧ -10000 ≤ p.2 ∧ p.2 ≤ 10000)
    (hnodup : (coords darts).Nodup)
    (hr : 1 ≤ r.val ∧ r.val ≤ r'.val ∧ r'.val ≤ 5000)
    (hres : num_points darts r = ok k)
    (hres' : num_points darts r' = ok k'), k.val ≤ k'.val) := by
  sorry

/-- Whenever num_points(darts, r) returns Ok k and num_points(darts', r) returns Ok k', we have k <= k'.
  Preconditions: Let n = len(darts). Assume 1 <= n < 100; each darts[i] has length 2; coordinates are in [-10000, 10000]; darts are pairwise distinct; and 1 <= r <= 5000. Let [x, y] be an integer pair with -10000 <= x, y <= 10000 that is distinct from every darts[i], and let darts' be darts with [x, y] appended, so len(darts') = n+1. -/
theorem spec_11
    (darts darts' : Slice (alloc.vec.Vec Std.I64)) (r k k' : Std.I64)
    (x y : Std.I64) (n : ℕ)
    (hlen : darts.val.length = n)
    (hn_pos : 1 ≤ n) (hn_lt : n < 100)
    (hlen2 : ∀ v ∈ darts.val, v.val.length = 2)
    (hbound : ∀ p ∈ coords darts,
      -10000 ≤ p.1 ∧ p.1 ≤ 10000 ∧ -10000 ≤ p.2 ∧ p.2 ≤ 10000)
    (hnodup : (coords darts).Nodup)
    (hr : 1 ≤ r.val ∧ r.val ≤ 5000)
    (hxy : -10000 ≤ x.val ∧ x.val ≤ 10000 ∧ -10000 ≤ y.val ∧ y.val ≤ 10000)
    (hfresh : (x.val, y.val) ∉ coords darts)
    (hdarts' : coords darts' = coords darts ++ [(x.val, y.val)])
    (hdarts'_len : darts'.val.length = n + 1)
    (hres : num_points darts r = ok k)
    (hres' : num_points darts' r = ok k') :
    k.val ≤ k'.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (darts darts' : Slice (alloc.vec.Vec Std.I64)) (r k k' : Std.I64)
    (x y : Std.I64) (n : ℕ)
    (hlen : darts.val.length = n)
    (hn_pos : 1 ≤ n) (hn_lt : n < 100)
    (hlen2 : ∀ v ∈ darts.val, v.val.length = 2)
    (hbound : ∀ p ∈ coords darts,
      -10000 ≤ p.1 ∧ p.1 ≤ 10000 ∧ -10000 ≤ p.2 ∧ p.2 ≤ 10000)
    (hnodup : (coords darts).Nodup)
    (hr : 1 ≤ r.val ∧ r.val ≤ 5000)
    (hxy : -10000 ≤ x.val ∧ x.val ≤ 10000 ∧ -10000 ≤ y.val ∧ y.val ≤ 10000)
    (hfresh : (x.val, y.val) ∉ coords darts)
    (hdarts' : coords darts' = coords darts ++ [(x.val, y.val)])
    (hdarts'_len : darts'.val.length = n + 1)
    (hres : num_points darts r = ok k)
    (hres' : num_points darts' r = ok k'), k.val ≤ k'.val) := by
  sorry

end AegisSpec.NumPoints
