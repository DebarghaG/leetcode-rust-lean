import Aegis.MaximizeSquareArea.Code.Funs

/-!
# Specifications of `Aegis.MaximizeSquareArea.maximize_square_area`

LeetCode problem `maximum-square-area-by-removing-fences-from-a-field`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaximizeSquareArea

  def positions (bound : I64) (fences : Slice I64) : Finset ℤ :=
    ({1, bound.val} : Finset ℤ) ∪ (fences.val.map (fun x => x.val)).toFinset

  def positiveDiffs (S : Finset ℤ) : Finset ℤ :=
    ((S.product S).image (fun p : ℤ × ℤ => p.2 - p.1)).filter (fun d => 0 < d)

  def commonDiffs (m n : I64) (hFences vFences : Slice I64) : Finset ℤ :=
    positiveDiffs (positions m hFences) ∩ positiveDiffs (positions n vFences)

  def InputOK (m n : I64) (hFences vFences : Slice I64) : Prop :=
    3 ≤ m.val ∧ m.val ≤ 1000000000 ∧
    3 ≤ n.val ∧ n.val ≤ 1000000000 ∧
    1 ≤ hFences.val.length ∧ hFences.val.length ≤ 600 ∧
    1 ≤ vFences.val.length ∧ vFences.val.length ≤ 600 ∧
    (∀ i : Fin hFences.val.length,
      1 < (hFences.val.get i).val ∧ (hFences.val.get i).val < m.val) ∧
    (∀ j : Fin vFences.val.length,
      1 < (vFences.val.get j).val ∧ (vFences.val.get j).val < n.val) ∧
    hFences.val.Nodup ∧ vFences.val.Nodup

  /-- Let X = {1, m} union { hFences[i] | 0 <= i < len(hFences) } and Y = {1, n} union { vFences[j] | 0 <= j < len(vFences) }. Let C = { d | d > 0 and there exist a in X and b in X with b - a = d and there exist c in Y and e in Y with e - c = d }. The function returns a result r (it does not fail). If C is nonempty, let d* be the maximum element of C; then r = (d* * d*) mod 1000000007, where mod is the nonnegative remainder in {0, 1, ..., 1000000006}. If C is empty, then r = -1.
    Preconditions: 3 <= m <= 1000000000 and 3 <= n <= 1000000000; 1 <= len(hFences) <= 600 and 1 <= len(vFences) <= 600; for every i with 0 <= i < len(hFences), 1 < hFences[i] < m; for every j with 0 <= j < len(vFences), 1 < vFences[j] < n; the values hFences[i] are pairwise distinct and the values vFences[j] are pairwise distinct. -/
  theorem spec_1 (m n : I64) (hFences vFences : Slice I64)
      (hpre : InputOK m n hFences vFences) :
      ∃ r : I64,
        Aegis.MaximizeSquareArea.maximize_square_area m n hFences vFences = ok r ∧
        (∀ (hC : (commonDiffs m n hFences vFences).Nonempty),
          r.val = (((commonDiffs m n hFences vFences).max' hC) *
                   ((commonDiffs m n hFences vFences).max' hC)) % 1000000007) ∧
        (commonDiffs m n hFences vFences = ∅ → r.val = -1) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (m n : I64) (hFences vFences : Slice I64)
        (hpre : InputOK m n hFences vFences), ∃ r : I64,
          Aegis.MaximizeSquareArea.maximize_square_area m n hFences vFences = ok r ∧
          (∀ (hC : (commonDiffs m n hFences vFences).Nonempty),
            r.val = (((commonDiffs m n hFences vFences).max' hC) *
                     ((commonDiffs m n hFences vFences).max' hC)) % 1000000007) ∧
          (commonDiffs m n hFences vFences = ∅ → r.val = -1)) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r; it does not fail, overflow, access out of bounds, or panic.
    Preconditions: 3 <= m <= 1000000000 and 3 <= n <= 1000000000; 1 <= len(hFences) <= 600 and 1 <= len(vFences) <= 600; for every i with 0 <= i < len(hFences), 1 < hFences[i] < m; for every j with 0 <= j < len(vFences), 1 < vFences[j] < n; the values hFences[i] are pairwise distinct and the values vFences[j] are pairwise distinct. -/
  theorem spec_2 (m n : I64) (hFences vFences : Slice I64)
      (hpre : InputOK m n hFences vFences) :
      ∃ r : I64,
        Aegis.MaximizeSquareArea.maximize_square_area m n hFences vFences = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (m n : I64) (hFences vFences : Slice I64)
        (hpre : InputOK m n hFences vFences), ∃ r : I64,
          Aegis.MaximizeSquareArea.maximize_square_area m n hFences vFences = ok r) := by
    sorry

  /-- Whenever the function returns a result r, either r = -1 or 1 <= r <= 1000000006.
    Preconditions: 3 <= m <= 1000000000 and 3 <= n <= 1000000000; 1 <= len(hFences) <= 600 and 1 <= len(vFences) <= 600; for every i with 0 <= i < len(hFences), 1 < hFences[i] < m; for every j with 0 <= j < len(vFences), 1 < vFences[j] < n; the values hFences[i] are pairwise distinct and the values vFences[j] are pairwise distinct. -/
  theorem spec_3 (m n : I64) (hFences vFences : Slice I64)
      (hpre : InputOK m n hFences vFences) :
      ∀ r : I64,
        Aegis.MaximizeSquareArea.maximize_square_area m n hFences vFences = ok r →
          r.val = -1 ∨ (1 ≤ r.val ∧ r.val ≤ 1000000006) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (m n : I64) (hFences vFences : Slice I64)
        (hpre : InputOK m n hFences vFences), ∀ r : I64,
          Aegis.MaximizeSquareArea.maximize_square_area m n hFences vFences = ok r →
            r.val = -1 ∨ (1 ≤ r.val ∧ r.val ≤ 1000000006)) := by
    sorry

  /-- The function returns r = ((m - 1) * (m - 1)) mod 1000000007.
    Preconditions: The main preconditions hold and additionally m = n. -/
  theorem spec_4 (m n : I64) (hFences vFences : Slice I64)
      (hpre : InputOK m n hFences vFences) (hmn : m = n) :
      ∃ r : I64,
        Aegis.MaximizeSquareArea.maximize_square_area m n hFences vFences = ok r ∧
        r.val = ((m.val - 1) * (m.val - 1)) % 1000000007 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (m n : I64) (hFences vFences : Slice I64)
        (hpre : InputOK m n hFences vFences) (hmn : m = n), ∃ r : I64,
          Aegis.MaximizeSquareArea.maximize_square_area m n hFences vFences = ok r ∧
          r.val = ((m.val - 1) * (m.val - 1)) % 1000000007) := by
    sorry

  /-- Let X = {1, m} union { hFences[i] | 0 <= i < len(hFences) } and Y = {1, n} union { vFences[j] | 0 <= j < len(vFences) }. Let C be the set of positive integers d such that d = b - a for some a,b in X and also d = e - c for some c,e in Y. The function returns r = -1 if and only if C is empty.
    Preconditions: 3 <= m <= 1000000000 and 3 <= n <= 1000000000; 1 <= len(hFences) <= 600 and 1 <= len(vFences) <= 600; for every i with 0 <= i < len(hFences), 1 < hFences[i] < m; for every j with 0 <= j < len(vFences), 1 < vFences[j] < n; the values hFences[i] are pairwise distinct and the values vFences[j] are pairwise distinct. -/
  theorem spec_5 (m n : I64) (hFences vFences : Slice I64)
      (hpre : InputOK m n hFences vFences) :
      ∃ r : I64,
        Aegis.MaximizeSquareArea.maximize_square_area m n hFences vFences = ok r ∧
        (r.val = -1 ↔ commonDiffs m n hFences vFences = ∅) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (m n : I64) (hFences vFences : Slice I64)
        (hpre : InputOK m n hFences vFences), ∃ r : I64,
          Aegis.MaximizeSquareArea.maximize_square_area m n hFences vFences = ok r ∧
          (r.val = -1 ↔ commonDiffs m n hFences vFences = ∅)) := by
    sorry

  /-- Let X = {1, m} union { hFences[i] | 0 <= i < len(hFences) } and Y = {1, n} union { vFences[j] | 0 <= j < len(vFences) }. Whenever the function returns a result r with r != -1, there exist a,b in X and c,e in Y such that |a - b| = |c - e| = d for some integer d > 0 and r = (d * d) mod 1000000007.
    Preconditions: 3 <= m <= 1000000000 and 3 <= n <= 1000000000; 1 <= len(hFences) <= 600 and 1 <= len(vFences) <= 600; for every i with 0 <= i < len(hFences), 1 < hFences[i] < m; for every j with 0 <= j < len(vFences), 1 < vFences[j] < n; the values hFences[i] are pairwise distinct and the values vFences[j] are pairwise distinct. -/
  theorem spec_6 (m n : I64) (hFences vFences : Slice I64)
      (hpre : InputOK m n hFences vFences) :
      ∀ r : I64,
        Aegis.MaximizeSquareArea.maximize_square_area m n hFences vFences = ok r →
          r.val ≠ -1 →
            ∃ a ∈ positions m hFences, ∃ b ∈ positions m hFences,
              ∃ c ∈ positions n vFences, ∃ e ∈ positions n vFences,
                ∃ d : ℤ, 0 < d ∧ |a - b| = d ∧ |c - e| = d ∧
                  r.val = (d * d) % 1000000007 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (m n : I64) (hFences vFences : Slice I64)
        (hpre : InputOK m n hFences vFences), ∀ r : I64,
          Aegis.MaximizeSquareArea.maximize_square_area m n hFences vFences = ok r →
            r.val ≠ -1 →
              ∃ a ∈ positions m hFences, ∃ b ∈ positions m hFences,
                ∃ c ∈ positions n vFences, ∃ e ∈ positions n vFences,
                  ∃ d : ℤ, 0 < d ∧ |a - b| = d ∧ |c - e| = d ∧
                    r.val = (d * d) % 1000000007) := by
    sorry

  /-- The two calls maximize_square_area(m, n, hFences, vFences) and maximize_square_area(n, m, vFences, hFences) return the same result r.
    Preconditions: 3 <= m <= 1000000000 and 3 <= n <= 1000000000; 1 <= len(hFences) <= 600 and 1 <= len(vFences) <= 600; for every i with 0 <= i < len(hFences), 1 < hFences[i] < m; for every j with 0 <= j < len(vFences), 1 < vFences[j] < n; the values hFences[i] are pairwise distinct and the values vFences[j] are pairwise distinct. -/
  theorem spec_7 (m n : I64) (hFences vFences : Slice I64)
      (hpre : InputOK m n hFences vFences) :
      ∃ r : I64,
        Aegis.MaximizeSquareArea.maximize_square_area m n hFences vFences = ok r ∧
        Aegis.MaximizeSquareArea.maximize_square_area n m vFences hFences = ok r := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (m n : I64) (hFences vFences : Slice I64)
        (hpre : InputOK m n hFences vFences), ∃ r : I64,
          Aegis.MaximizeSquareArea.maximize_square_area m n hFences vFences = ok r ∧
          Aegis.MaximizeSquareArea.maximize_square_area n m vFences hFences = ok r) := by
    sorry

  /-- maximize_square_area(m, n, hFences, vFences) = maximize_square_area(m, n, hFences', vFences').
    Preconditions: The main preconditions hold. Also hFences' is any permutation of hFences and vFences' is any permutation of vFences. -/
  theorem spec_8 (m n : I64) (hFences hFences' vFences vFences' : Slice I64)
      (hpre : InputOK m n hFences vFences)
      (hh : List.Perm hFences.val hFences'.val)
      (hv : List.Perm vFences.val vFences'.val) :
      Aegis.MaximizeSquareArea.maximize_square_area m n hFences vFences =
        Aegis.MaximizeSquareArea.maximize_square_area m n hFences' vFences' := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (m n : I64) (hFences hFences' vFences vFences' : Slice I64)
        (hpre : InputOK m n hFences vFences)
        (hh : List.Perm hFences.val hFences'.val)
        (hv : List.Perm vFences.val vFences'.val), Aegis.MaximizeSquareArea.maximize_square_area m n hFences vFences =
          Aegis.MaximizeSquareArea.maximize_square_area m n hFences' vFences') := by
    sorry

  /-- Let X = {1, m} union { hFences[i] | 0 <= i < len(hFences) }, Y = {1, n} union { vFences[j] | 0 <= j < len(vFences) }, and d0 = min(m - 1, n - 1). If there exist a,b in X with b - a = d0 and c,e in Y with e - c = d0, then the function returns r = (d0 * d0) mod 1000000007.
    Preconditions: 3 <= m <= 1000000000 and 3 <= n <= 1000000000; 1 <= len(hFences) <= 600 and 1 <= len(vFences) <= 600; for every i with 0 <= i < len(hFences), 1 < hFences[i] < m; for every j with 0 <= j < len(vFences), 1 < vFences[j] < n; the values hFences[i] are pairwise distinct and the values vFences[j] are pairwise distinct. -/
  theorem spec_9 (m n : I64) (hFences vFences : Slice I64)
      (hpre : InputOK m n hFences vFences) (d0 : ℤ)
      (hd0 : d0 = min (m.val - 1) (n.val - 1))
      (hX : ∃ a ∈ positions m hFences, ∃ b ∈ positions m hFences, b - a = d0)
      (hY : ∃ c ∈ positions n vFences, ∃ e ∈ positions n vFences, e - c = d0) :
      ∃ r : I64,
        Aegis.MaximizeSquareArea.maximize_square_area m n hFences vFences = ok r ∧
        r.val = (d0 * d0) % 1000000007 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (m n : I64) (hFences vFences : Slice I64)
        (hpre : InputOK m n hFences vFences) (d0 : ℤ)
        (hd0 : d0 = min (m.val - 1) (n.val - 1))
        (hX : ∃ a ∈ positions m hFences, ∃ b ∈ positions m hFences, b - a = d0)
        (hY : ∃ c ∈ positions n vFences, ∃ e ∈ positions n vFences, e - c = d0), ∃ r : I64,
          Aegis.MaximizeSquareArea.maximize_square_area m n hFences vFences = ok r ∧
          r.val = (d0 * d0) % 1000000007) := by
    sorry

  end AegisSpec.MaximizeSquareArea
