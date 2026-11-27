import Aegis.VideoStitching.Code.Funs
import Mathlib.Data.Real.Basic

/-!
# Specifications of `Aegis.VideoStitching.video_stitching`

LeetCode problem `video-stitching`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.VideoStitching

open Aegis.VideoStitching

def clipVals (clips : Slice (alloc.vec.Vec I64)) (i : ℕ) : Option (List ℤ) :=
  (clips.val[i]?).map (fun v => v.slice.val.map IScalar.val)

def cstart (clips : Slice (alloc.vec.Vec I64)) (i : ℕ) : ℤ :=
  ((clipVals clips i).bind (fun l => l[0]?)).getD 0

def cend (clips : Slice (alloc.vec.Vec I64)) (i : ℕ) : ℤ :=
  ((clipVals clips i).bind (fun l => l[1]?)).getD 0

def Covered (clips : Slice (alloc.vec.Vec I64)) (x : ℝ) : Prop :=
  ∃ i, i < clips.length ∧ (cstart clips i : ℝ) ≤ x ∧ x ≤ (cend clips i : ℝ)

def Cover (clips : Slice (alloc.vec.Vec I64)) (T : ℤ) (S : Finset ℕ) : Prop :=
  (∀ i ∈ S, i < clips.length) ∧
    ∀ x : ℝ, 0 ≤ x → x ≤ (T : ℝ) →
      ∃ i ∈ S, (cstart clips i : ℝ) ≤ x ∧ x ≤ (cend clips i : ℝ)

def IsChain (clips : Slice (alloc.vec.Vec I64)) (T : ℤ) {k : ℕ} (hk : 1 ≤ k)
    (f : Fin k → ℕ) : Prop :=
  Function.Injective f ∧
    (∀ h : Fin k, f h < clips.length) ∧
    cstart clips (f ⟨0, hk⟩) ≤ 0 ∧
    (∃ h : Fin k, T ≤ cend clips (f h)) ∧
    ∀ (j : ℕ) (hj : j < k), 1 ≤ j →
      ∃ (h : ℕ) (hh : h < j),
        cstart clips (f ⟨j, hj⟩) ≤ cend clips (f ⟨h, Nat.lt_trans hh hj⟩)

/-- Define Cover(S), for S a subset of {0,...,n-1}, to mean: for every real x with 0 <= x <= time there exists i in S with clips[i][0] <= x <= clips[i][1]. Whenever video_stitching clips time returns a result r: if no subset S of {0,...,n-1} satisfies Cover(S), then r = -1; otherwise r is the least nonnegative integer k such that some subset S with |S| = k satisfies Cover(S).
  Preconditions: Let n = len(clips). Assume 1 <= n <= 100; for each i with 0 <= i < n, clips[i] has length 2, write clips[i] = [s_i, e_i], and 0 <= s_i <= e_i <= 100; and 1 <= time <= 100. -/
theorem spec_1
    (clips : Slice (alloc.vec.Vec I64)) (time : I64)
    (hne : 1 ≤ clips.length) (hle : clips.length ≤ 100)
    (hclips : ∀ i, i < clips.length → ∃ s e : ℤ,
      clipVals clips i = some [s, e] ∧ 0 ≤ s ∧ s ≤ e ∧ e ≤ 100)
    (htime : 1 ≤ time.val ∧ time.val ≤ 100)
    (r : I64) (hr : video_stitching clips time = ok r) :
    ((∀ S : Finset ℕ, ¬ Cover clips time.val S) → r.val = -1) ∧
      ((∃ S : Finset ℕ, Cover clips time.val S) →
        (∃ S : Finset ℕ, Cover clips time.val S ∧ (S.card : ℤ) = r.val) ∧
          (∀ S : Finset ℕ, Cover clips time.val S → r.val ≤ (S.card : ℤ))) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (clips : Slice (alloc.vec.Vec I64)) (time : I64)
    (hne : 1 ≤ clips.length) (hle : clips.length ≤ 100)
    (hclips : ∀ i, i < clips.length → ∃ s e : ℤ,
      clipVals clips i = some [s, e] ∧ 0 ≤ s ∧ s ≤ e ∧ e ≤ 100)
    (htime : 1 ≤ time.val ∧ time.val ≤ 100)
    (r : I64) (hr : video_stitching clips time = ok r), ((∀ S : Finset ℕ, ¬ Cover clips time.val S) → r.val = -1) ∧
      ((∃ S : Finset ℕ, Cover clips time.val S) →
        (∃ S : Finset ℕ, Cover clips time.val S ∧ (S.card : ℤ) = r.val) ∧
          (∀ S : Finset ℕ, Cover clips time.val S → r.val ≤ (S.card : ℤ)))) := by
  sorry

/-- video_stitching clips time returns a result r; it does not fail (no panic, out-of-bounds access, or i64 overflow) on any input satisfying the preconditions.
  Preconditions: Let n = len(clips). Assume 1 <= n <= 100; for each i with 0 <= i < n, clips[i] has length 2, write clips[i] = [s_i, e_i], and 0 <= s_i <= e_i <= 100; and 1 <= time <= 100. -/
theorem spec_2
    (clips : Slice (alloc.vec.Vec I64)) (time : I64)
    (hne : 1 ≤ clips.length) (hle : clips.length ≤ 100)
    (hclips : ∀ i, i < clips.length → ∃ s e : ℤ,
      clipVals clips i = some [s, e] ∧ 0 ≤ s ∧ s ≤ e ∧ e ≤ 100)
    (htime : 1 ≤ time.val ∧ time.val ≤ 100) :
    ∃ r : I64, video_stitching clips time = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (clips : Slice (alloc.vec.Vec I64)) (time : I64)
    (hne : 1 ≤ clips.length) (hle : clips.length ≤ 100)
    (hclips : ∀ i, i < clips.length → ∃ s e : ℤ,
      clipVals clips i = some [s, e] ∧ 0 ≤ s ∧ s ≤ e ∧ e ≤ 100)
    (htime : 1 ≤ time.val ∧ time.val ≤ 100), ∃ r : I64, video_stitching clips time = ok r) := by
  sorry

/-- Define U = {x : 0 <= x <= time and there exists i with clips[i][0] <= x <= clips[i][1]}. Whenever video_stitching clips time returns r, r = -1 iff U is not equal to the whole interval [0,time] (equivalently, the union of all clip intervals does not cover [0,time]).
  Preconditions: Let n = len(clips). Assume 1 <= n <= 100; for each i with 0 <= i < n, clips[i] has length 2, write clips[i] = [s_i, e_i], and 0 <= s_i <= e_i <= 100; and 1 <= time <= 100. -/
theorem spec_3
    (clips : Slice (alloc.vec.Vec I64)) (time : I64)
    (hne : 1 ≤ clips.length) (hle : clips.length ≤ 100)
    (hclips : ∀ i, i < clips.length → ∃ s e : ℤ,
      clipVals clips i = some [s, e] ∧ 0 ≤ s ∧ s ≤ e ∧ e ≤ 100)
    (htime : 1 ≤ time.val ∧ time.val ≤ 100)
    (r : I64) (hr : video_stitching clips time = ok r) :
    (r.val = -1) ↔
      ∃ x : ℝ, 0 ≤ x ∧ x ≤ (time.val : ℝ) ∧ ¬ Covered clips x := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (clips : Slice (alloc.vec.Vec I64)) (time : I64)
    (hne : 1 ≤ clips.length) (hle : clips.length ≤ 100)
    (hclips : ∀ i, i < clips.length → ∃ s e : ℤ,
      clipVals clips i = some [s, e] ∧ 0 ≤ s ∧ s ≤ e ∧ e ≤ 100)
    (htime : 1 ≤ time.val ∧ time.val ≤ 100)
    (r : I64) (hr : video_stitching clips time = ok r), (r.val = -1) ↔
      ∃ x : ℝ, 0 ≤ x ∧ x ≤ (time.val : ℝ) ∧ ¬ Covered clips x) := by
  sorry

/-- Whenever video_stitching clips time returns r and r != -1, there exists a subset S of {0,...,n-1} such that |S| = r and for every real x with 0 <= x <= time there is i in S with clips[i][0] <= x <= clips[i][1].
  Preconditions: Let n = len(clips). Assume 1 <= n <= 100; for each i with 0 <= i < n, clips[i] has length 2, write clips[i] = [s_i, e_i], and 0 <= s_i <= e_i <= 100; and 1 <= time <= 100. -/
theorem spec_4
    (clips : Slice (alloc.vec.Vec I64)) (time : I64)
    (hne : 1 ≤ clips.length) (hle : clips.length ≤ 100)
    (hclips : ∀ i, i < clips.length → ∃ s e : ℤ,
      clipVals clips i = some [s, e] ∧ 0 ≤ s ∧ s ≤ e ∧ e ≤ 100)
    (htime : 1 ≤ time.val ∧ time.val ≤ 100)
    (r : I64) (hr : video_stitching clips time = ok r) (hrne : r.val ≠ -1) :
    ∃ S : Finset ℕ, Cover clips time.val S ∧ (S.card : ℤ) = r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (clips : Slice (alloc.vec.Vec I64)) (time : I64)
    (hne : 1 ≤ clips.length) (hle : clips.length ≤ 100)
    (hclips : ∀ i, i < clips.length → ∃ s e : ℤ,
      clipVals clips i = some [s, e] ∧ 0 ≤ s ∧ s ≤ e ∧ e ≤ 100)
    (htime : 1 ≤ time.val ∧ time.val ≤ 100)
    (r : I64) (hr : video_stitching clips time = ok r) (hrne : r.val ≠ -1), ∃ S : Finset ℕ, Cover clips time.val S ∧ (S.card : ℤ) = r.val) := by
  sorry

/-- Whenever video_stitching clips time returns r and r != -1, for every subset S of {0,...,n-1} with |S| < r, it is not true that for every real x with 0 <= x <= time there is i in S with clips[i][0] <= x <= clips[i][1].
  Preconditions: Let n = len(clips). Assume 1 <= n <= 100; for each i with 0 <= i < n, clips[i] has length 2, write clips[i] = [s_i, e_i], and 0 <= s_i <= e_i <= 100; and 1 <= time <= 100. -/
theorem spec_5
    (clips : Slice (alloc.vec.Vec I64)) (time : I64)
    (hne : 1 ≤ clips.length) (hle : clips.length ≤ 100)
    (hclips : ∀ i, i < clips.length → ∃ s e : ℤ,
      clipVals clips i = some [s, e] ∧ 0 ≤ s ∧ s ≤ e ∧ e ≤ 100)
    (htime : 1 ≤ time.val ∧ time.val ≤ 100)
    (r : I64) (hr : video_stitching clips time = ok r) (hrne : r.val ≠ -1) :
    ∀ S : Finset ℕ, (S.card : ℤ) < r.val → ¬ Cover clips time.val S := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (clips : Slice (alloc.vec.Vec I64)) (time : I64)
    (hne : 1 ≤ clips.length) (hle : clips.length ≤ 100)
    (hclips : ∀ i, i < clips.length → ∃ s e : ℤ,
      clipVals clips i = some [s, e] ∧ 0 ≤ s ∧ s ≤ e ∧ e ≤ 100)
    (htime : 1 ≤ time.val ∧ time.val ≤ 100)
    (r : I64) (hr : video_stitching clips time = ok r) (hrne : r.val ≠ -1), ∀ S : Finset ℕ, (S.card : ℤ) < r.val → ¬ Cover clips time.val S) := by
  sorry

/-- Whenever video_stitching clips time returns r, either r = -1 or 1 <= r <= n.
  Preconditions: Let n = len(clips). Assume 1 <= n <= 100; for each i with 0 <= i < n, clips[i] has length 2, write clips[i] = [s_i, e_i], and 0 <= s_i <= e_i <= 100; and 1 <= time <= 100. -/
theorem spec_6
    (clips : Slice (alloc.vec.Vec I64)) (time : I64)
    (hne : 1 ≤ clips.length) (hle : clips.length ≤ 100)
    (hclips : ∀ i, i < clips.length → ∃ s e : ℤ,
      clipVals clips i = some [s, e] ∧ 0 ≤ s ∧ s ≤ e ∧ e ≤ 100)
    (htime : 1 ≤ time.val ∧ time.val ≤ 100)
    (r : I64) (hr : video_stitching clips time = ok r) :
    r.val = -1 ∨ (1 ≤ r.val ∧ r.val ≤ (clips.length : ℤ)) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (clips : Slice (alloc.vec.Vec I64)) (time : I64)
    (hne : 1 ≤ clips.length) (hle : clips.length ≤ 100)
    (hclips : ∀ i, i < clips.length → ∃ s e : ℤ,
      clipVals clips i = some [s, e] ∧ 0 ≤ s ∧ s ≤ e ∧ e ≤ 100)
    (htime : 1 ≤ time.val ∧ time.val ≤ 100)
    (r : I64) (hr : video_stitching clips time = ok r), r.val = -1 ∨ (1 ≤ r.val ∧ r.val ≤ (clips.length : ℤ))) := by
  sorry

/-- If there exists an index i with 0 <= i < n, clips[i][0] <= 0, and clips[i][1] >= time, then whenever video_stitching clips time returns r, r = 1.
  Preconditions: Let n = len(clips). Assume 1 <= n <= 100; for each i with 0 <= i < n, clips[i] has length 2, write clips[i] = [s_i, e_i], and 0 <= s_i <= e_i <= 100; and 1 <= time <= 100. -/
theorem spec_7
    (clips : Slice (alloc.vec.Vec I64)) (time : I64)
    (hne : 1 ≤ clips.length) (hle : clips.length ≤ 100)
    (hclips : ∀ i, i < clips.length → ∃ s e : ℤ,
      clipVals clips i = some [s, e] ∧ 0 ≤ s ∧ s ≤ e ∧ e ≤ 100)
    (htime : 1 ≤ time.val ∧ time.val ≤ 100)
    (hsingle : ∃ i, i < clips.length ∧ cstart clips i ≤ 0 ∧ time.val ≤ cend clips i)
    (r : I64) (hr : video_stitching clips time = ok r) :
    r.val = 1 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (clips : Slice (alloc.vec.Vec I64)) (time : I64)
    (hne : 1 ≤ clips.length) (hle : clips.length ≤ 100)
    (hclips : ∀ i, i < clips.length → ∃ s e : ℤ,
      clipVals clips i = some [s, e] ∧ 0 ≤ s ∧ s ≤ e ∧ e ≤ 100)
    (htime : 1 ≤ time.val ∧ time.val ≤ 100)
    (hsingle : ∃ i, i < clips.length ∧ cstart clips i ≤ 0 ∧ time.val ≤ cend clips i)
    (r : I64) (hr : video_stitching clips time = ok r), r.val = 1) := by
  sorry

/-- Whenever video_stitching clips time returns r and r = 1, there exists an index i with 0 <= i < n, clips[i][0] <= 0, and clips[i][1] >= time.
  Preconditions: Let n = len(clips). Assume 1 <= n <= 100; for each i with 0 <= i < n, clips[i] has length 2, write clips[i] = [s_i, e_i], and 0 <= s_i <= e_i <= 100; and 1 <= time <= 100. -/
theorem spec_8
    (clips : Slice (alloc.vec.Vec I64)) (time : I64)
    (hne : 1 ≤ clips.length) (hle : clips.length ≤ 100)
    (hclips : ∀ i, i < clips.length → ∃ s e : ℤ,
      clipVals clips i = some [s, e] ∧ 0 ≤ s ∧ s ≤ e ∧ e ≤ 100)
    (htime : 1 ≤ time.val ∧ time.val ≤ 100)
    (r : I64) (hr : video_stitching clips time = ok r) (hrone : r.val = 1) :
    ∃ i, i < clips.length ∧ cstart clips i ≤ 0 ∧ time.val ≤ cend clips i := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (clips : Slice (alloc.vec.Vec I64)) (time : I64)
    (hne : 1 ≤ clips.length) (hle : clips.length ≤ 100)
    (hclips : ∀ i, i < clips.length → ∃ s e : ℤ,
      clipVals clips i = some [s, e] ∧ 0 ≤ s ∧ s ≤ e ∧ e ≤ 100)
    (htime : 1 ≤ time.val ∧ time.val ≤ 100)
    (r : I64) (hr : video_stitching clips time = ok r) (hrone : r.val = 1), ∃ i, i < clips.length ∧ cstart clips i ≤ 0 ∧ time.val ≤ cend clips i) := by
  sorry

/-- If there is no index i with 0 <= i < n and clips[i][0] <= 0, then whenever video_stitching clips time returns r, r = -1.
  Preconditions: Let n = len(clips). Assume 1 <= n <= 100; for each i with 0 <= i < n, clips[i] has length 2, write clips[i] = [s_i, e_i], and 0 <= s_i <= e_i <= 100; and 1 <= time <= 100. -/
theorem spec_9
    (clips : Slice (alloc.vec.Vec I64)) (time : I64)
    (hne : 1 ≤ clips.length) (hle : clips.length ≤ 100)
    (hclips : ∀ i, i < clips.length → ∃ s e : ℤ,
      clipVals clips i = some [s, e] ∧ 0 ≤ s ∧ s ≤ e ∧ e ≤ 100)
    (htime : 1 ≤ time.val ∧ time.val ≤ 100)
    (hno : ∀ i, i < clips.length → ¬ cstart clips i ≤ 0)
    (r : I64) (hr : video_stitching clips time = ok r) :
    r.val = -1 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (clips : Slice (alloc.vec.Vec I64)) (time : I64)
    (hne : 1 ≤ clips.length) (hle : clips.length ≤ 100)
    (hclips : ∀ i, i < clips.length → ∃ s e : ℤ,
      clipVals clips i = some [s, e] ∧ 0 ≤ s ∧ s ≤ e ∧ e ≤ 100)
    (htime : 1 ≤ time.val ∧ time.val ≤ 100)
    (hno : ∀ i, i < clips.length → ¬ cstart clips i ≤ 0)
    (r : I64) (hr : video_stitching clips time = ok r), r.val = -1) := by
  sorry

/-- If there is no index i with 0 <= i < n and clips[i][1] >= time, then whenever video_stitching clips time returns r, r = -1.
  Preconditions: Let n = len(clips). Assume 1 <= n <= 100; for each i with 0 <= i < n, clips[i] has length 2, write clips[i] = [s_i, e_i], and 0 <= s_i <= e_i <= 100; and 1 <= time <= 100. -/
theorem spec_10
    (clips : Slice (alloc.vec.Vec I64)) (time : I64)
    (hne : 1 ≤ clips.length) (hle : clips.length ≤ 100)
    (hclips : ∀ i, i < clips.length → ∃ s e : ℤ,
      clipVals clips i = some [s, e] ∧ 0 ≤ s ∧ s ≤ e ∧ e ≤ 100)
    (htime : 1 ≤ time.val ∧ time.val ≤ 100)
    (hno : ∀ i, i < clips.length → ¬ time.val ≤ cend clips i)
    (r : I64) (hr : video_stitching clips time = ok r) :
    r.val = -1 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (clips : Slice (alloc.vec.Vec I64)) (time : I64)
    (hne : 1 ≤ clips.length) (hle : clips.length ≤ 100)
    (hclips : ∀ i, i < clips.length → ∃ s e : ℤ,
      clipVals clips i = some [s, e] ∧ 0 ≤ s ∧ s ≤ e ∧ e ≤ 100)
    (htime : 1 ≤ time.val ∧ time.val ≤ 100)
    (hno : ∀ i, i < clips.length → ¬ time.val ≤ cend clips i)
    (r : I64) (hr : video_stitching clips time = ok r), r.val = -1) := by
  sorry

/-- Whenever video_stitching clips time returns r and video_stitching clips' time returns r', we have r' = r.
  Preconditions: Let n = len(clips). Assume 1 <= n <= 100; for each i with 0 <= i < n, clips[i] has length 2, write clips[i] = [s_i, e_i], and 0 <= s_i <= e_i <= 100; and 1 <= time <= 100. Let clips' be any slice of Vec I64 obtained by permuting clips; assume len(clips') = n and clips' also satisfies the endpoint constraints 0 <= start <= end <= 100 for every entry. -/
theorem spec_11
    (clips clips' : Slice (alloc.vec.Vec I64)) (time : I64)
    (hne : 1 ≤ clips.length) (hle : clips.length ≤ 100)
    (hclips : ∀ i, i < clips.length → ∃ s e : ℤ,
      clipVals clips i = some [s, e] ∧ 0 ≤ s ∧ s ≤ e ∧ e ≤ 100)
    (htime : 1 ≤ time.val ∧ time.val ≤ 100)
    (hlen' : clips'.length = clips.length)
    (hclips' : ∀ i, i < clips'.length → ∃ s e : ℤ,
      clipVals clips' i = some [s, e] ∧ 0 ≤ s ∧ s ≤ e ∧ e ≤ 100)
    (hperm : clips.val.Perm clips'.val)
    (r r' : I64)
    (hr : video_stitching clips time = ok r) (hr' : video_stitching clips' time = ok r') :
    r'.val = r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (clips clips' : Slice (alloc.vec.Vec I64)) (time : I64)
    (hne : 1 ≤ clips.length) (hle : clips.length ≤ 100)
    (hclips : ∀ i, i < clips.length → ∃ s e : ℤ,
      clipVals clips i = some [s, e] ∧ 0 ≤ s ∧ s ≤ e ∧ e ≤ 100)
    (htime : 1 ≤ time.val ∧ time.val ≤ 100)
    (hlen' : clips'.length = clips.length)
    (hclips' : ∀ i, i < clips'.length → ∃ s e : ℤ,
      clipVals clips' i = some [s, e] ∧ 0 ≤ s ∧ s ≤ e ∧ e ≤ 100)
    (hperm : clips.val.Perm clips'.val)
    (r r' : I64)
    (hr : video_stitching clips time = ok r) (hr' : video_stitching clips' time = ok r'), r'.val = r.val) := by
  sorry

/-- Whenever video_stitching clips time returns r with r != -1 and video_stitching clips' time returns r', we have r' != -1 and r' <= r.
  Preconditions: Let n = len(clips). Assume 1 <= n <= 100; for each i with 0 <= i < n, clips[i] has length 2, write clips[i] = [s_i, e_i], and 0 <= s_i <= e_i <= 100; and 1 <= time <= 100. Let clips' be obtained from clips by inserting one or more additional two-element intervals, each satisfying 0 <= start <= end <= 100, so 1 <= len(clips') <= 100. -/
theorem spec_12
    (clips clips' : Slice (alloc.vec.Vec I64)) (time : I64)
    (hne : 1 ≤ clips.length) (hle : clips.length ≤ 100)
    (hclips : ∀ i, i < clips.length → ∃ s e : ℤ,
      clipVals clips i = some [s, e] ∧ 0 ≤ s ∧ s ≤ e ∧ e ≤ 100)
    (htime : 1 ≤ time.val ∧ time.val ≤ 100)
    (hsubl : clips.val.Sublist clips'.val)
    (hmore : clips.length < clips'.length)
    (hlen' : 1 ≤ clips'.length ∧ clips'.length ≤ 100)
    (hclips' : ∀ i, i < clips'.length → ∃ s e : ℤ,
      clipVals clips' i = some [s, e] ∧ 0 ≤ s ∧ s ≤ e ∧ e ≤ 100)
    (r r' : I64)
    (hr : video_stitching clips time = ok r) (hr' : video_stitching clips' time = ok r')
    (hrne : r.val ≠ -1) :
    r'.val ≠ -1 ∧ r'.val ≤ r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (clips clips' : Slice (alloc.vec.Vec I64)) (time : I64)
    (hne : 1 ≤ clips.length) (hle : clips.length ≤ 100)
    (hclips : ∀ i, i < clips.length → ∃ s e : ℤ,
      clipVals clips i = some [s, e] ∧ 0 ≤ s ∧ s ≤ e ∧ e ≤ 100)
    (htime : 1 ≤ time.val ∧ time.val ≤ 100)
    (hsubl : clips.val.Sublist clips'.val)
    (hmore : clips.length < clips'.length)
    (hlen' : 1 ≤ clips'.length ∧ clips'.length ≤ 100)
    (hclips' : ∀ i, i < clips'.length → ∃ s e : ℤ,
      clipVals clips' i = some [s, e] ∧ 0 ≤ s ∧ s ≤ e ∧ e ≤ 100)
    (r r' : I64)
    (hr : video_stitching clips time = ok r) (hr' : video_stitching clips' time = ok r')
    (hrne : r.val ≠ -1), r'.val ≠ -1 ∧ r'.val ≤ r.val) := by
  sorry

/-- If there exist indices i and j with 0 <= i,j < n such that clips[i][0] <= 0, clips[j][1] >= time, and clips[j][0] <= clips[i][1], then whenever video_stitching clips time returns r, r = 2.
  Preconditions: Let n = len(clips). Assume 1 <= n <= 100; for each i with 0 <= i < n, clips[i] has length 2, write clips[i] = [s_i, e_i], and 0 <= s_i <= e_i <= 100; and 1 <= time <= 100. Also assume no index i satisfies clips[i][0] <= 0 and clips[i][1] >= time (so no single clip covers [0,time]). -/
theorem spec_13
    (clips : Slice (alloc.vec.Vec I64)) (time : I64)
    (hne : 1 ≤ clips.length) (hle : clips.length ≤ 100)
    (hclips : ∀ i, i < clips.length → ∃ s e : ℤ,
      clipVals clips i = some [s, e] ∧ 0 ≤ s ∧ s ≤ e ∧ e ≤ 100)
    (htime : 1 ≤ time.val ∧ time.val ≤ 100)
    (hsingle : ∀ i, i < clips.length → ¬ (cstart clips i ≤ 0 ∧ time.val ≤ cend clips i))
    (hij : ∃ i j, i < clips.length ∧ j < clips.length ∧
      cstart clips i ≤ 0 ∧ time.val ≤ cend clips j ∧ cstart clips j ≤ cend clips i)
    (r : I64) (hr : video_stitching clips time = ok r) :
    r.val = 2 := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (clips : Slice (alloc.vec.Vec I64)) (time : I64)
    (hne : 1 ≤ clips.length) (hle : clips.length ≤ 100)
    (hclips : ∀ i, i < clips.length → ∃ s e : ℤ,
      clipVals clips i = some [s, e] ∧ 0 ≤ s ∧ s ≤ e ∧ e ≤ 100)
    (htime : 1 ≤ time.val ∧ time.val ≤ 100)
    (hsingle : ∀ i, i < clips.length → ¬ (cstart clips i ≤ 0 ∧ time.val ≤ cend clips i))
    (hij : ∃ i j, i < clips.length ∧ j < clips.length ∧
      cstart clips i ≤ 0 ∧ time.val ≤ cend clips j ∧ cstart clips j ≤ cend clips i)
    (r : I64) (hr : video_stitching clips time = ok r), r.val = 2) := by
  sorry

/-- Whenever video_stitching clips time returns r and r = k >= 1, there exist distinct indices i_0, ..., i_{k-1} in {0,...,n-1} such that: (a) clips[i_0][0] <= 0; (b) max over 0 <= h < k of clips[i_h][1] is at least time; (c) for every j with 1 <= j < k, clips[i_j][0] <= max over 0 <= h < j of clips[i_h][1].
  Preconditions: Let n = len(clips). Assume 1 <= n <= 100; for each i with 0 <= i < n, clips[i] has length 2, write clips[i] = [s_i, e_i], and 0 <= s_i <= e_i <= 100; and 1 <= time <= 100. -/
theorem spec_14
    (clips : Slice (alloc.vec.Vec I64)) (time : I64)
    (hne : 1 ≤ clips.length) (hle : clips.length ≤ 100)
    (hclips : ∀ i, i < clips.length → ∃ s e : ℤ,
      clipVals clips i = some [s, e] ∧ 0 ≤ s ∧ s ≤ e ∧ e ≤ 100)
    (htime : 1 ≤ time.val ∧ time.val ≤ 100)
    (r : I64) (hr : video_stitching clips time = ok r) :
    ∀ (k : ℕ) (hk : 1 ≤ k), r.val = (k : ℤ) →
      ∃ f : Fin k → ℕ, IsChain clips time.val hk f := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (clips : Slice (alloc.vec.Vec I64)) (time : I64)
    (hne : 1 ≤ clips.length) (hle : clips.length ≤ 100)
    (hclips : ∀ i, i < clips.length → ∃ s e : ℤ,
      clipVals clips i = some [s, e] ∧ 0 ≤ s ∧ s ≤ e ∧ e ≤ 100)
    (htime : 1 ≤ time.val ∧ time.val ≤ 100)
    (r : I64) (hr : video_stitching clips time = ok r), ∀ (k : ℕ) (hk : 1 ≤ k), r.val = (k : ℤ) →
      ∃ f : Fin k → ℕ, IsChain clips time.val hk f) := by
  sorry

end AegisSpec.VideoStitching
