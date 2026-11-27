import Aegis.LongestCommonSubpath.Code.Funs

/-!
# Specifications of `Aegis.LongestCommonSubpath.longest_common_subpath`

LeetCode problem `longest-common-subpath`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.LongestCommonSubpath

namespace AegisSpec.LongestCommonSubpath

def vecList (v : alloc.vec.Vec Std.I64) : List Int := v.val.map (fun x => x.val)

def pathList (paths : Slice (alloc.vec.Vec Std.I64)) : List (List Int) :=
  paths.val.map vecList

def pathAt (ps : List (List Int)) (i : Nat) : List Int := (ps[i]?).getD []

def elemAt (p : List Int) (j : Nat) : Int := (p[j]?).getD 0

def Occurs (v : Int) (p : List Int) : Prop :=
  ∃ j, j < p.length ∧ elemAt p j = v

def ValidInput (n : Std.I64) (paths : Slice (alloc.vec.Vec Std.I64)) : Prop :=
  let ps := pathList paths
  1 ≤ n.val ∧ n.val ≤ 100000 ∧
  2 ≤ ps.length ∧ ps.length ≤ 100000 ∧
  (ps.map (fun p => p.length)).sum ≤ 100000 ∧
  (∀ i, i < ps.length → ∀ j, j < (pathAt ps i).length →
      0 ≤ elemAt (pathAt ps i) j ∧ elemAt (pathAt ps i) j < n.val) ∧
  (∀ i, i < ps.length → ∀ j, j + 1 < (pathAt ps i).length →
      elemAt (pathAt ps i) j ≠ elemAt (pathAt ps i) (j + 1))

def Achievable (ps : List (List Int)) (L : Int) : Prop :=
  0 ≤ L ∧
  ∃ s : Nat → Int,
    ∀ i, i < ps.length →
      0 ≤ s i ∧ s i + L ≤ ((pathAt ps i).length : Int) ∧
      ∀ k, 0 ≤ k → k < L →
        (pathAt ps i)[(s i + k).toNat]? = (pathAt ps 0)[(s 0 + k).toNat]?

def IsLargestAchievable (ps : List (List Int)) (r : Int) : Prop :=
  Achievable ps r ∧ ∀ L, Achievable ps L → L ≤ r

def PairCommon (A B : List Int) (L : Int) : Prop :=
  0 ≤ L ∧
  ∃ s t : Int,
    0 ≤ s ∧ s + L ≤ (A.length : Int) ∧
    0 ≤ t ∧ t + L ≤ (B.length : Int) ∧
    ∀ k, 0 ≤ k → k < L → A[(s + k).toNat]? = B[(t + k).toNat]?

def IsPairLongest (A B : List Int) (L : Int) : Prop :=
  PairCommon A B L ∧ ∀ L', PairCommon A B L' → L' ≤ L

def reversePaths (ps : List (List Int)) : List (List Int) := ps.map List.reverse

def reorderPaths (ps : List (List Int)) (pi : Equiv.Perm (Fin ps.length)) :
    List (List Int) :=
  (List.finRange ps.length).map (fun i => ps.get (pi i))

def permFun {k : Nat} (f : Equiv.Perm (Fin k)) (j : Nat) : Nat :=
  if h : j < k then (f ⟨j, h⟩).val else j

def permutePaths {k : Nat} (f : Equiv.Perm (Fin k)) (ps : List (List Int)) :
    List (List Int) :=
  ps.map (fun p => p.map (fun v => ((permFun f v.toNat : Nat) : Int)))

def InsertOne (ps ps' : List (List Int)) : Prop :=
  ∃ i : Nat, ∃ x : List Int, i ≤ ps.length ∧ ps' = ps.take i ++ [x] ++ ps.drop i

/-- The function returns a result r (it does not fail). Let m = len(paths). For L >= 0, say L is achievable when there exist integers s_0, ..., s_{m-1} such that for every i with 0 <= i < m, 0 <= s_i and s_i + L <= len(paths[i]), and for every i with 0 <= i < m and every k with 0 <= k < L, paths[i][s_i+k] = paths[0][s_0+k]. Then r is the largest achievable L.
  Preconditions: n is an integer with 1 <= n <= 100000; paths is a list of m vectors with m = len(paths), 2 <= m <= 100000; the sum of len(paths[i]) over i = 0..m-1 is at most 100000; for every i with 0 <= i < m and every j with 0 <= j < len(paths[i]), 0 <= paths[i][j] < n; and for every i with 0 <= i < m and every j with 0 <= j+1 < len(paths[i]), paths[i][j] != paths[i][j+1]. -/
theorem spec_1 (n : Std.I64) (paths : Slice (alloc.vec.Vec Std.I64))
    (h : ValidInput n paths) :
    ∃ r : Std.I64,
      longest_common_subpath n paths = ok r ∧
        IsLargestAchievable (pathList paths) r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Std.I64) (paths : Slice (alloc.vec.Vec Std.I64))
    (h : ValidInput n paths), ∃ r : Std.I64,
      longest_common_subpath n paths = ok r ∧
        IsLargestAchievable (pathList paths) r.val) := by
  sorry

/-- For every n and paths satisfying the preconditions, the function returns a result (some Std.I64 value); it does not overflow, panic, or access an index out of bounds.
  Preconditions: n is an integer with 1 <= n <= 100000; paths is a list of m vectors with m = len(paths), 2 <= m <= 100000; the sum of len(paths[i]) over i = 0..m-1 is at most 100000; for every i with 0 <= i < m and every j with 0 <= j < len(paths[i]), 0 <= paths[i][j] < n; and for every i with 0 <= i < m and every j with 0 <= j+1 < len(paths[i]), paths[i][j] != paths[i][j+1]. -/
theorem spec_2 (n : Std.I64) (paths : Slice (alloc.vec.Vec Std.I64))
    (h : ValidInput n paths) :
    ∃ r : Std.I64, longest_common_subpath n paths = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Std.I64) (paths : Slice (alloc.vec.Vec Std.I64))
    (h : ValidInput n paths), ∃ r : Std.I64, longest_common_subpath n paths = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r <= len(paths[i]) for every i with 0 <= i < len(paths). Equivalently, r <= min_{0 <= i < len(paths)} len(paths[i]).
  Preconditions: n is an integer with 1 <= n <= 100000; paths is a list of m vectors with m = len(paths), 2 <= m <= 100000; the sum of len(paths[i]) over i = 0..m-1 is at most 100000; for every i with 0 <= i < m and every j with 0 <= j < len(paths[i]), 0 <= paths[i][j] < n; and for every i with 0 <= i < m and every j with 0 <= j+1 < len(paths[i]), paths[i][j] != paths[i][j+1]. -/
theorem spec_3 (n : Std.I64) (paths : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64)
    (h : ValidInput n paths) (hr : longest_common_subpath n paths = ok r) :
    0 ≤ r.val ∧
      ∀ i, i < (pathList paths).length → r.val ≤ ((pathAt (pathList paths) i).length : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : Std.I64) (paths : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64)
    (h : ValidInput n paths) (hr : longest_common_subpath n paths = ok r), 0 ≤ r.val ∧
      ∀ i, i < (pathList paths).length → r.val ≤ ((pathAt (pathList paths) i).length : Int)) := by
  sorry

/-- Whenever the function returns a result r, for every integer L >= 0, if L is achievable for paths (i.e., with m = len(paths), there exist integers s_0, ..., s_{m-1} such that 0 <= s_i, s_i + L <= len(paths[i]) for all i with 0 <= i < m, and paths[i][s_i+k] = paths[0][s_0+k] for all i with 0 <= i < m and all k with 0 <= k < L), then r >= L.
  Preconditions: n is an integer with 1 <= n <= 100000; paths is a list of m vectors with m = len(paths), 2 <= m <= 100000; the sum of len(paths[i]) over i = 0..m-1 is at most 100000; for every i with 0 <= i < m and every j with 0 <= j < len(paths[i]), 0 <= paths[i][j] < n; and for every i with 0 <= i < m and every j with 0 <= j+1 < len(paths[i]), paths[i][j] != paths[i][j+1]. -/
theorem spec_4 (n : Std.I64) (paths : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64)
    (h : ValidInput n paths) (hr : longest_common_subpath n paths = ok r) :
    ∀ L : Int, Achievable (pathList paths) L → L ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : Std.I64) (paths : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64)
    (h : ValidInput n paths) (hr : longest_common_subpath n paths = ok r), ∀ L : Int, Achievable (pathList paths) L → L ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r itself is achievable: with m = len(paths), there exist integers s_0, ..., s_{m-1} such that 0 <= s_i, s_i + r <= len(paths[i]) for every i with 0 <= i < m, and paths[i][s_i+k] = paths[0][s_0+k] for every i with 0 <= i < m and every k with 0 <= k < r. For r = 0 this is vacuous (take all s_i = 0).
  Preconditions: n is an integer with 1 <= n <= 100000; paths is a list of m vectors with m = len(paths), 2 <= m <= 100000; the sum of len(paths[i]) over i = 0..m-1 is at most 100000; for every i with 0 <= i < m and every j with 0 <= j < len(paths[i]), 0 <= paths[i][j] < n; and for every i with 0 <= i < m and every j with 0 <= j+1 < len(paths[i]), paths[i][j] != paths[i][j+1]. -/
theorem spec_5 (n : Std.I64) (paths : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64)
    (h : ValidInput n paths) (hr : longest_common_subpath n paths = ok r) :
    Achievable (pathList paths) r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : Std.I64) (paths : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64)
    (h : ValidInput n paths) (hr : longest_common_subpath n paths = ok r), Achievable (pathList paths) r.val) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if there is no integer v such that for every i with 0 <= i < len(paths), v occurs in paths[i] (i.e., there exists j with 0 <= j < len(paths[i]) and paths[i][j] = v).
  Preconditions: n is an integer with 1 <= n <= 100000; paths is a list of m vectors with m = len(paths), 2 <= m <= 100000; the sum of len(paths[i]) over i = 0..m-1 is at most 100000; for every i with 0 <= i < m and every j with 0 <= j < len(paths[i]), 0 <= paths[i][j] < n; and for every i with 0 <= i < m and every j with 0 <= j+1 < len(paths[i]), paths[i][j] != paths[i][j+1]. -/
theorem spec_6 (n : Std.I64) (paths : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64)
    (h : ValidInput n paths) (hr : longest_common_subpath n paths = ok r) :
    (r.val = 0 ↔
      ¬ ∃ v : Int,
        ∀ i, i < (pathList paths).length → Occurs v (pathAt (pathList paths) i)) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : Std.I64) (paths : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64)
    (h : ValidInput n paths) (hr : longest_common_subpath n paths = ok r), (r.val = 0 ↔
      ¬ ∃ v : Int,
        ∀ i, i < (pathList paths).length → Occurs v (pathAt (pathList paths) i))) := by
  sorry

/-- Whenever the function returns a result r, if all paths are identical (i.e., for every i with 0 <= i < len(paths), len(paths[i]) = len(paths[0]), and for every j with 0 <= j < len(paths[0]), paths[i][j] = paths[0][j]), then r = len(paths[0]).
  Preconditions: n is an integer with 1 <= n <= 100000; paths is a list of m vectors with m = len(paths), 2 <= m <= 100000; the sum of len(paths[i]) over i = 0..m-1 is at most 100000; for every i with 0 <= i < m and every j with 0 <= j < len(paths[i]), 0 <= paths[i][j] < n; and for every i with 0 <= i < m and every j with 0 <= j+1 < len(paths[i]), paths[i][j] != paths[i][j+1]. -/
theorem spec_7 (n : Std.I64) (paths : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64)
    (h : ValidInput n paths) (hr : longest_common_subpath n paths = ok r)
    (hall : ∀ i, i < (pathList paths).length →
      pathAt (pathList paths) i = pathAt (pathList paths) 0) :
    r.val = ((pathAt (pathList paths) 0).length : Int) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : Std.I64) (paths : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64)
    (h : ValidInput n paths) (hr : longest_common_subpath n paths = ok r)
    (hall : ∀ i, i < (pathList paths).length →
      pathAt (pathList paths) i = pathAt (pathList paths) 0), r.val = ((pathAt (pathList paths) 0).length : Int)) := by
  sorry

/-- Whenever the function returns a result r, for every pair of indices i, j with 0 <= i < j < len(paths), r is at most the longest common subpath length of the two paths paths[i] and paths[j]. Here a length L is common to two paths A and B when there exist s, t with 0 <= s, s + L <= len(A), 0 <= t, t + L <= len(B), and A[s+k] = B[t+k] for all k with 0 <= k < L.
  Preconditions: n is an integer with 1 <= n <= 100000; paths is a list of m vectors with m = len(paths), 2 <= m <= 100000; the sum of len(paths[i]) over i = 0..m-1 is at most 100000; for every i with 0 <= i < m and every j with 0 <= j < len(paths[i]), 0 <= paths[i][j] < n; and for every i with 0 <= i < m and every j with 0 <= j+1 < len(paths[i]), paths[i][j] != paths[i][j+1]. -/
theorem spec_8 (n : Std.I64) (paths : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64)
    (h : ValidInput n paths) (hr : longest_common_subpath n paths = ok r) :
    ∀ i j, i < j → j < (pathList paths).length →
      ∃ Lmax : Int,
        IsPairLongest (pathAt (pathList paths) i) (pathAt (pathList paths) j) Lmax ∧
          r.val ≤ Lmax := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n : Std.I64) (paths : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64)
    (h : ValidInput n paths) (hr : longest_common_subpath n paths = ok r), ∀ i j, i < j → j < (pathList paths).length →
      ∃ Lmax : Int,
        IsPairLongest (pathAt (pathList paths) i) (pathAt (pathList paths) j) Lmax ∧
          r.val ≤ Lmax) := by
  sorry

/-- Whenever the function returns a result r, let rev(paths) be the list whose i-th path is paths[i] reversed, so rev(paths)[i][j] = paths[i][len(paths[i])-1-j] for 0 <= j < len(paths[i]). Then r is also the largest L >= 0 for which there exist integers t_0, ..., t_{m-1} (with m = len(paths)) such that 0 <= t_i and t_i + L <= len(rev(paths)[i]) for all i, and rev(paths)[i][t_i+k] = rev(paths)[0][t_0+k] for all i and all k with 0 <= k < L.
  Preconditions: n is an integer with 1 <= n <= 100000; paths is a list of m vectors with m = len(paths), 2 <= m <= 100000; the sum of len(paths[i]) over i = 0..m-1 is at most 100000; for every i with 0 <= i < m and every j with 0 <= j < len(paths[i]), 0 <= paths[i][j] < n; and for every i with 0 <= i < m and every j with 0 <= j+1 < len(paths[i]), paths[i][j] != paths[i][j+1]. -/
theorem spec_9 (n : Std.I64) (paths : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64)
    (h : ValidInput n paths) (hr : longest_common_subpath n paths = ok r) :
    IsLargestAchievable (reversePaths (pathList paths)) r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n : Std.I64) (paths : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64)
    (h : ValidInput n paths) (hr : longest_common_subpath n paths = ok r), IsLargestAchievable (reversePaths (pathList paths)) r.val) := by
  sorry

/-- Whenever the function returns a result r, for every permutation pi of the index set {0, 1, ..., m-1} with m = len(paths), the largest achievable common-subpath length for the reordered list paths[pi(0)], paths[pi(1)], ..., paths[pi(m-1)] is also r. Here achievable for a list of paths is defined by the same start-index condition as in the main specification, taking the first path in that list as the reference.
  Preconditions: n is an integer with 1 <= n <= 100000; paths is a list of m vectors with m = len(paths), 2 <= m <= 100000; the sum of len(paths[i]) over i = 0..m-1 is at most 100000; for every i with 0 <= i < m and every j with 0 <= j < len(paths[i]), 0 <= paths[i][j] < n; and for every i with 0 <= i < m and every j with 0 <= j+1 < len(paths[i]), paths[i][j] != paths[i][j+1]. -/
theorem spec_10 (n : Std.I64) (paths : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64)
    (h : ValidInput n paths) (hr : longest_common_subpath n paths = ok r) :
    ∀ pi : Equiv.Perm (Fin (pathList paths).length),
      IsLargestAchievable (reorderPaths (pathList paths) pi) r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n : Std.I64) (paths : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64)
    (h : ValidInput n paths) (hr : longest_common_subpath n paths = ok r), ∀ pi : Equiv.Perm (Fin (pathList paths).length),
      IsLargestAchievable (reorderPaths (pathList paths) pi) r.val) := by
  sorry

/-- Whenever the function returns a result r for the given n, for every integer n' with 1 <= n' <= 100000 and such that 0 <= paths[i][j] < n' for every i with 0 <= i < len(paths) and every j with 0 <= j < len(paths[i]), the function called with the same paths but with n' in place of n also returns r.
  Preconditions: n is an integer with 1 <= n <= 100000; paths is a list of m vectors with m = len(paths), 2 <= m <= 100000; the sum of len(paths[i]) over i = 0..m-1 is at most 100000; for every i with 0 <= i < m and every j with 0 <= j < len(paths[i]), 0 <= paths[i][j] < n; and for every i with 0 <= i < m and every j with 0 <= j+1 < len(paths[i]), paths[i][j] != paths[i][j+1]. -/
theorem spec_11 (n : Std.I64) (paths : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64)
    (h : ValidInput n paths) (hr : longest_common_subpath n paths = ok r)
    (n' : Std.I64) (hn'₁ : 1 ≤ n'.val) (hn'₂ : n'.val ≤ 100000)
    (hn'range : ∀ i, i < (pathList paths).length →
      ∀ j, j < (pathAt (pathList paths) i).length →
        0 ≤ elemAt (pathAt (pathList paths) i) j ∧
          elemAt (pathAt (pathList paths) i) j < n'.val) :
    longest_common_subpath n' paths = ok r := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (n : Std.I64) (paths : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64)
    (h : ValidInput n paths) (hr : longest_common_subpath n paths = ok r)
    (n' : Std.I64) (hn'₁ : 1 ≤ n'.val) (hn'₂ : n'.val ≤ 100000)
    (hn'range : ∀ i, i < (pathList paths).length →
      ∀ j, j < (pathAt (pathList paths) i).length →
        0 ≤ elemAt (pathAt (pathList paths) i) j ∧
          elemAt (pathAt (pathList paths) i) j < n'.val), longest_common_subpath n' paths = ok r) := by
  sorry

/-- Whenever the function returns a result r, for every bijection f from {0, 1, ..., n-1} to itself, let paths' be defined by paths'[i][j] = f(paths[i][j]) for all i with 0 <= i < len(paths) and all j with 0 <= j < len(paths[i]). Then the largest achievable common-subpath length for paths' is also r.
  Preconditions: n is an integer with 1 <= n <= 100000; paths is a list of m vectors with m = len(paths), 2 <= m <= 100000; the sum of len(paths[i]) over i = 0..m-1 is at most 100000; for every i with 0 <= i < m and every j with 0 <= j < len(paths[i]), 0 <= paths[i][j] < n; and for every i with 0 <= i < m and every j with 0 <= j+1 < len(paths[i]), paths[i][j] != paths[i][j+1]. -/
theorem spec_12 (n : Std.I64) (paths : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64)
    (h : ValidInput n paths) (hr : longest_common_subpath n paths = ok r) :
    ∀ f : Equiv.Perm (Fin n.val.toNat),
      IsLargestAchievable (permutePaths f (pathList paths)) r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (n : Std.I64) (paths : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64)
    (h : ValidInput n paths) (hr : longest_common_subpath n paths = ok r), ∀ f : Equiv.Perm (Fin n.val.toNat),
      IsLargestAchievable (permutePaths f (pathList paths)) r.val) := by
  sorry

/-- Whenever the function returns a result r, for every integer L with 0 <= L <= r, L is achievable for paths: with m = len(paths), there exist integers s_0, ..., s_{m-1} such that 0 <= s_i and s_i + L <= len(paths[i]) for every i with 0 <= i < m, and paths[i][s_i+k] = paths[0][s_0+k] for every i with 0 <= i < m and every k with 0 <= k < L. Thus shorter common subpaths exist whenever a common subpath of length r exists.
  Preconditions: n is an integer with 1 <= n <= 100000; paths is a list of m vectors with m = len(paths), 2 <= m <= 100000; the sum of len(paths[i]) over i = 0..m-1 is at most 100000; for every i with 0 <= i < m and every j with 0 <= j < len(paths[i]), 0 <= paths[i][j] < n; and for every i with 0 <= i < m and every j with 0 <= j+1 < len(paths[i]), paths[i][j] != paths[i][j+1]. -/
theorem spec_13 (n : Std.I64) (paths : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64)
    (h : ValidInput n paths) (hr : longest_common_subpath n paths = ok r) :
    ∀ L : Int, 0 ≤ L → L ≤ r.val → Achievable (pathList paths) L := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (n : Std.I64) (paths : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64)
    (h : ValidInput n paths) (hr : longest_common_subpath n paths = ok r), ∀ L : Int, 0 ≤ L → L ≤ r.val → Achievable (pathList paths) L) := by
  sorry

/-- Whenever the function returns r for paths and returns r' for paths', then r' <= r.
  Preconditions: n is an integer with 1 <= n <= 100000; paths is a list of m vectors with m = len(paths), 2 <= m <= 100000; the sum of len(paths[i]) over i = 0..m-1 is at most 100000; for every i with 0 <= i < m and every j with 0 <= j < len(paths[i]), 0 <= paths[i][j] < n; and for every i with 0 <= i < m and every j with 0 <= j+1 < len(paths[i]), paths[i][j] != paths[i][j+1]; paths' is another list of vectors satisfying the same constraints with the same n and is obtained by inserting exactly one additional path into paths. -/
theorem spec_14 (n : Std.I64)
    (paths paths' : Slice (alloc.vec.Vec Std.I64)) (r r' : Std.I64)
    (h : ValidInput n paths) (h' : ValidInput n paths')
    (hins : InsertOne (pathList paths) (pathList paths'))
    (hr : longest_common_subpath n paths = ok r)
    (hr' : longest_common_subpath n paths' = ok r') :
    r'.val ≤ r.val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (n : Std.I64)
    (paths paths' : Slice (alloc.vec.Vec Std.I64)) (r r' : Std.I64)
    (h : ValidInput n paths) (h' : ValidInput n paths')
    (hins : InsertOne (pathList paths) (pathList paths'))
    (hr : longest_common_subpath n paths = ok r)
    (hr' : longest_common_subpath n paths' = ok r'), r'.val ≤ r.val) := by
  sorry

end AegisSpec.LongestCommonSubpath
