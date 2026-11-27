import Aegis.MaxArea.Code.Funs

/-!
# Specifications of `Aegis.MaxArea.max_area`

LeetCode problem `maximum-area-of-a-piece-of-cake-after-horizontal-and-vertical-cuts`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaxArea

  def modulus : ℤ := 1000000007

  def cutVals (cuts : List Std.I64) : List ℤ := cuts.map (fun c => c.val)

  def sortedPoints (limit : ℤ) (cuts : List Std.I64) : List ℤ :=
    List.insertionSort (· ≤ ·) (0 :: limit :: cutVals cuts)

  def consecutiveGaps (limit : ℤ) (cuts : List Std.I64) : List ℤ :=
    let ps := sortedPoints limit cuts
    (ps.zip ps.tail).map (fun p => p.2 - p.1)

  def maxGap (limit : ℤ) (cuts : List Std.I64) : ℤ :=
    (consecutiveGaps limit cuts).foldr max 0

  def Consecutive (limit : ℤ) (cuts : List Std.I64) (a b : ℤ) : Prop :=
    a < b ∧ (a = 0 ∨ a ∈ cutVals cuts) ∧ (b = limit ∨ b ∈ cutVals cuts) ∧
      ∀ c ∈ cutVals cuts, ¬ (a < c ∧ c < b)

  def IsResidue (x q : ℤ) : Prop :=
    0 ≤ q ∧ q < modulus ∧ Int.ModEq modulus q x

  def ValidInput (h w : Std.I64) (horizontalCuts verticalCuts : Slice Std.I64) : Prop :=
    2 ≤ h.val ∧ h.val ≤ 1000000000 ∧
    2 ≤ w.val ∧ w.val ≤ 1000000000 ∧
    1 ≤ (horizontalCuts.val.length : ℤ) ∧
    (horizontalCuts.val.length : ℤ) ≤ min (h.val - 1) 100000 ∧
    1 ≤ (verticalCuts.val.length : ℤ) ∧
    (verticalCuts.val.length : ℤ) ≤ min (w.val - 1) 100000 ∧
    (∀ i : Fin horizontalCuts.val.length,
      1 ≤ (horizontalCuts.val.get i).val ∧ (horizontalCuts.val.get i).val < h.val) ∧
    (∀ j : Fin verticalCuts.val.length,
      1 ≤ (verticalCuts.val.get j).val ∧ (verticalCuts.val.get j).val < w.val) ∧
    horizontalCuts.val.Nodup ∧ verticalCuts.val.Nodup

  /-- For every input satisfying the preconditions, max_area h w horizontalCuts verticalCuts returns Result.ok r, and the integer value of r is the unique integer q such that 0 <= q < 1000000007 and q is congruent to MH * MV modulo 1000000007. Here MH is the maximum difference between consecutive elements of the sorted set {0, h} union {horizontalCuts[i] | 0 <= i < len(horizontalCuts)}, and MV is defined analogously as the maximum difference between consecutive elements of the sorted set {0, w} union {verticalCuts[j] | 0 <= j < len(verticalCuts)}.
    Preconditions: h and w are integers with 2 <= h <= 1000000000 and 2 <= w <= 1000000000. horizontalCuts and verticalCuts are slices of 64-bit integers. Let n = len(horizontalCuts) and m = len(verticalCuts). Then 1 <= n <= min(h - 1, 100000) and 1 <= m <= min(w - 1, 100000). For every i with 0 <= i < n, 1 <= horizontalCuts[i] < h; for every j with 0 <= j < m, 1 <= verticalCuts[j] < w. All elements of horizontalCuts are pairwise distinct, and all elements of verticalCuts are pairwise distinct. -/
  theorem spec_1 (h w : Std.I64) (horizontalCuts verticalCuts : Slice Std.I64)
      (hpre : ValidInput h w horizontalCuts verticalCuts) :
      ∃ r : Std.I64,
        Aegis.MaxArea.max_area h w horizontalCuts verticalCuts = ok r ∧
        IsResidue
          (maxGap h.val horizontalCuts.val * maxGap w.val verticalCuts.val) r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (h w : Std.I64) (horizontalCuts verticalCuts : Slice Std.I64)
        (hpre : ValidInput h w horizontalCuts verticalCuts), ∃ r : Std.I64,
          Aegis.MaxArea.max_area h w horizontalCuts verticalCuts = ok r ∧
          IsResidue
            (maxGap h.val horizontalCuts.val * maxGap w.val verticalCuts.val) r.val) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns successfully: there exists a 64-bit integer r such that max_area h w horizontalCuts verticalCuts = Result.ok r. In particular, the function does not fail due to overflow, out-of-bounds access, or panic.
    Preconditions: h and w are integers with 2 <= h <= 1000000000 and 2 <= w <= 1000000000. horizontalCuts and verticalCuts are slices of 64-bit integers. Let n = len(horizontalCuts) and m = len(verticalCuts). Then 1 <= n <= min(h - 1, 100000) and 1 <= m <= min(w - 1, 100000). For every i with 0 <= i < n, 1 <= horizontalCuts[i] < h; for every j with 0 <= j < m, 1 <= verticalCuts[j] < w. All elements of horizontalCuts are pairwise distinct, and all elements of verticalCuts are pairwise distinct. -/
  theorem spec_2 (h w : Std.I64) (horizontalCuts verticalCuts : Slice Std.I64)
      (hpre : ValidInput h w horizontalCuts verticalCuts) :
      ∃ r : Std.I64,
        Aegis.MaxArea.max_area h w horizontalCuts verticalCuts = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (h w : Std.I64) (horizontalCuts verticalCuts : Slice Std.I64)
        (hpre : ValidInput h w horizontalCuts verticalCuts), ∃ r : Std.I64,
          Aegis.MaxArea.max_area h w horizontalCuts verticalCuts = ok r) := by
    sorry

  /-- Whenever max_area h w horizontalCuts verticalCuts returns Result.ok r, the integer value of r satisfies 1 <= r <= 1000000006.
    Preconditions: h and w are integers with 2 <= h <= 1000000000 and 2 <= w <= 1000000000. horizontalCuts and verticalCuts are slices of 64-bit integers. Let n = len(horizontalCuts) and m = len(verticalCuts). Then 1 <= n <= min(h - 1, 100000) and 1 <= m <= min(w - 1, 100000). For every i with 0 <= i < n, 1 <= horizontalCuts[i] < h; for every j with 0 <= j < m, 1 <= verticalCuts[j] < w. All elements of horizontalCuts are pairwise distinct, and all elements of verticalCuts are pairwise distinct. -/
  theorem spec_3 (h w : Std.I64) (horizontalCuts verticalCuts : Slice Std.I64)
      (hpre : ValidInput h w horizontalCuts verticalCuts) :
      ∀ r : Std.I64,
        Aegis.MaxArea.max_area h w horizontalCuts verticalCuts = ok r →
        1 ≤ r.val ∧ r.val ≤ modulus - 1 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (h w : Std.I64) (horizontalCuts verticalCuts : Slice Std.I64)
        (hpre : ValidInput h w horizontalCuts verticalCuts), ∀ r : Std.I64,
          Aegis.MaxArea.max_area h w horizontalCuts verticalCuts = ok r →
          1 ≤ r.val ∧ r.val ≤ modulus - 1) := by
    sorry

  /-- Whenever max_area h w horizontalCuts verticalCuts returns Result.ok r, the integer value of r is congruent modulo 1000000007 to MH * MV, where MH is the maximum difference between consecutive elements of the sorted set {0, h} union {horizontalCuts[i] | 0 <= i < len(horizontalCuts)} and MV is defined analogously from {0, w} union {verticalCuts[j] | 0 <= j < len(verticalCuts)}.
    Preconditions: h and w are integers with 2 <= h <= 1000000000 and 2 <= w <= 1000000000. horizontalCuts and verticalCuts are slices of 64-bit integers. Let n = len(horizontalCuts) and m = len(verticalCuts). Then 1 <= n <= min(h - 1, 100000) and 1 <= m <= min(w - 1, 100000). For every i with 0 <= i < n, 1 <= horizontalCuts[i] < h; for every j with 0 <= j < m, 1 <= verticalCuts[j] < w. All elements of horizontalCuts are pairwise distinct, and all elements of verticalCuts are pairwise distinct. -/
  theorem spec_4 (h w : Std.I64) (horizontalCuts verticalCuts : Slice Std.I64)
      (hpre : ValidInput h w horizontalCuts verticalCuts) :
      ∀ r : Std.I64,
        Aegis.MaxArea.max_area h w horizontalCuts verticalCuts = ok r →
        IsResidue
          (maxGap h.val horizontalCuts.val * maxGap w.val verticalCuts.val) r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (h w : Std.I64) (horizontalCuts verticalCuts : Slice Std.I64)
        (hpre : ValidInput h w horizontalCuts verticalCuts), ∀ r : Std.I64,
          Aegis.MaxArea.max_area h w horizontalCuts verticalCuts = ok r →
          IsResidue
            (maxGap h.val horizontalCuts.val * maxGap w.val verticalCuts.val) r.val) := by
    sorry

  /-- Whenever max_area h w horizontalCuts verticalCuts returns Result.ok r, there exist consecutive elements aH < bH of the sorted set {0, h} union {horizontalCuts[i] | 0 <= i < len(horizontalCuts)} and consecutive elements aV < bV of the sorted set {0, w} union {verticalCuts[j] | 0 <= j < len(verticalCuts)} such that bH - aH = MH, bV - aV = MV, and the integer value of r is the unique integer q with 0 <= q < 1000000007 and q congruent to (bH - aH) * (bV - aV) modulo 1000000007. Here MH and MV are the maximum horizontal and vertical gaps.
    Preconditions: h and w are integers with 2 <= h <= 1000000000 and 2 <= w <= 1000000000. horizontalCuts and verticalCuts are slices of 64-bit integers. Let n = len(horizontalCuts) and m = len(verticalCuts). Then 1 <= n <= min(h - 1, 100000) and 1 <= m <= min(w - 1, 100000). For every i with 0 <= i < n, 1 <= horizontalCuts[i] < h; for every j with 0 <= j < m, 1 <= verticalCuts[j] < w. All elements of horizontalCuts are pairwise distinct, and all elements of verticalCuts are pairwise distinct. -/
  theorem spec_5 (h w : Std.I64) (horizontalCuts verticalCuts : Slice Std.I64)
      (hpre : ValidInput h w horizontalCuts verticalCuts) :
      ∀ r : Std.I64,
        Aegis.MaxArea.max_area h w horizontalCuts verticalCuts = ok r →
        ∃ aH bH aV bV : ℤ,
          Consecutive h.val horizontalCuts.val aH bH ∧
          bH - aH = maxGap h.val horizontalCuts.val ∧
          Consecutive w.val verticalCuts.val aV bV ∧
          bV - aV = maxGap w.val verticalCuts.val ∧
          IsResidue ((bH - aH) * (bV - aV)) r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (h w : Std.I64) (horizontalCuts verticalCuts : Slice Std.I64)
        (hpre : ValidInput h w horizontalCuts verticalCuts), ∀ r : Std.I64,
          Aegis.MaxArea.max_area h w horizontalCuts verticalCuts = ok r →
          ∃ aH bH aV bV : ℤ,
            Consecutive h.val horizontalCuts.val aH bH ∧
            bH - aH = maxGap h.val horizontalCuts.val ∧
            Consecutive w.val verticalCuts.val aV bV ∧
            bV - aV = maxGap w.val verticalCuts.val ∧
            IsResidue ((bH - aH) * (bV - aV)) r.val) := by
    sorry

  /-- For every input satisfying the preconditions, both max_area h w horizontalCuts verticalCuts and max_area w h verticalCuts horizontalCuts return Result.ok r, and the two returned 64-bit values are equal.
    Preconditions: h and w are integers with 2 <= h <= 1000000000 and 2 <= w <= 1000000000. horizontalCuts and verticalCuts are slices of 64-bit integers. Let n = len(horizontalCuts) and m = len(verticalCuts). Then 1 <= n <= min(h - 1, 100000) and 1 <= m <= min(w - 1, 100000). For every i with 0 <= i < n, 1 <= horizontalCuts[i] < h; for every j with 0 <= j < m, 1 <= verticalCuts[j] < w. All elements of horizontalCuts are pairwise distinct, and all elements of verticalCuts are pairwise distinct. -/
  theorem spec_6 (h w : Std.I64) (horizontalCuts verticalCuts : Slice Std.I64)
      (hpre : ValidInput h w horizontalCuts verticalCuts) :
      ∃ r r' : Std.I64,
        Aegis.MaxArea.max_area h w horizontalCuts verticalCuts = ok r ∧
        Aegis.MaxArea.max_area w h verticalCuts horizontalCuts = ok r' ∧
        r.val = r'.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (h w : Std.I64) (horizontalCuts verticalCuts : Slice Std.I64)
        (hpre : ValidInput h w horizontalCuts verticalCuts), ∃ r r' : Std.I64,
          Aegis.MaxArea.max_area h w horizontalCuts verticalCuts = ok r ∧
          Aegis.MaxArea.max_area w h verticalCuts horizontalCuts = ok r' ∧
          r.val = r'.val) := by
    sorry

  /-- For every such input and every such permutations, both max_area h w horizontalCuts verticalCuts and max_area h w H V return Result.ok r, and the two returned 64-bit values are equal.
    Preconditions: h and w are integers with 2 <= h <= 1000000000 and 2 <= w <= 1000000000. horizontalCuts and verticalCuts are slices of 64-bit integers. Let n = len(horizontalCuts) and m = len(verticalCuts). Then 1 <= n <= min(h - 1, 100000) and 1 <= m <= min(w - 1, 100000). For every i with 0 <= i < n, 1 <= horizontalCuts[i] < h; for every j with 0 <= j < m, 1 <= verticalCuts[j] < w. All elements of horizontalCuts are pairwise distinct, and all elements of verticalCuts are pairwise distinct. Let pi be any permutation of {0, ..., n-1}, sigma any permutation of {0, ..., m-1}, and define H[i] = horizontalCuts[pi(i)] for 0 <= i < n and V[j] = verticalCuts[sigma(j)] for 0 <= j < m. -/
  theorem spec_7 (h w : Std.I64) (horizontalCuts verticalCuts H' V' : Slice Std.I64)
      (hpre : ValidInput h w horizontalCuts verticalCuts)
      (hH' : H'.val.Perm horizontalCuts.val)
      (hV' : V'.val.Perm verticalCuts.val) :
      ∃ r r' : Std.I64,
        Aegis.MaxArea.max_area h w horizontalCuts verticalCuts = ok r ∧
        Aegis.MaxArea.max_area h w H' V' = ok r' ∧
        r.val = r'.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (h w : Std.I64) (horizontalCuts verticalCuts H' V' : Slice Std.I64)
        (hpre : ValidInput h w horizontalCuts verticalCuts)
        (hH' : H'.val.Perm horizontalCuts.val)
        (hV' : V'.val.Perm verticalCuts.val), ∃ r r' : Std.I64,
          Aegis.MaxArea.max_area h w horizontalCuts verticalCuts = ok r ∧
          Aegis.MaxArea.max_area h w H' V' = ok r' ∧
          r.val = r'.val) := by
    sorry

  /-- Let A = MH * MV, where MH and MV are the maximum horizontal and vertical gaps. Whenever max_area h w horizontalCuts verticalCuts returns Result.ok r and A < 1000000007, the integer value of r equals A.
    Preconditions: h and w are integers with 2 <= h <= 1000000000 and 2 <= w <= 1000000000. horizontalCuts and verticalCuts are slices of 64-bit integers. Let n = len(horizontalCuts) and m = len(verticalCuts). Then 1 <= n <= min(h - 1, 100000) and 1 <= m <= min(w - 1, 100000). For every i with 0 <= i < n, 1 <= horizontalCuts[i] < h; for every j with 0 <= j < m, 1 <= verticalCuts[j] < w. All elements of horizontalCuts are pairwise distinct, and all elements of verticalCuts are pairwise distinct. -/
  theorem spec_8 (h w : Std.I64) (horizontalCuts verticalCuts : Slice Std.I64)
      (hpre : ValidInput h w horizontalCuts verticalCuts) :
      ∀ r : Std.I64,
        Aegis.MaxArea.max_area h w horizontalCuts verticalCuts = ok r →
        maxGap h.val horizontalCuts.val * maxGap w.val verticalCuts.val < modulus →
        r.val = maxGap h.val horizontalCuts.val * maxGap w.val verticalCuts.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (h w : Std.I64) (horizontalCuts verticalCuts : Slice Std.I64)
        (hpre : ValidInput h w horizontalCuts verticalCuts), ∀ r : Std.I64,
          Aegis.MaxArea.max_area h w horizontalCuts verticalCuts = ok r →
          maxGap h.val horizontalCuts.val * maxGap w.val verticalCuts.val < modulus →
          r.val = maxGap h.val horizontalCuts.val * maxGap w.val verticalCuts.val) := by
    sorry

  /-- Let A = MH * MV, where MH and MV are the maximum horizontal and vertical gaps. Whenever max_area h w horizontalCuts verticalCuts returns Result.ok r and A >= 1000000007, the integer value of r is strictly less than A.
    Preconditions: h and w are integers with 2 <= h <= 1000000000 and 2 <= w <= 1000000000. horizontalCuts and verticalCuts are slices of 64-bit integers. Let n = len(horizontalCuts) and m = len(verticalCuts). Then 1 <= n <= min(h - 1, 100000) and 1 <= m <= min(w - 1, 100000). For every i with 0 <= i < n, 1 <= horizontalCuts[i] < h; for every j with 0 <= j < m, 1 <= verticalCuts[j] < w. All elements of horizontalCuts are pairwise distinct, and all elements of verticalCuts are pairwise distinct. -/
  theorem spec_9 (h w : Std.I64) (horizontalCuts verticalCuts : Slice Std.I64)
      (hpre : ValidInput h w horizontalCuts verticalCuts) :
      ∀ r : Std.I64,
        Aegis.MaxArea.max_area h w horizontalCuts verticalCuts = ok r →
        modulus ≤ maxGap h.val horizontalCuts.val * maxGap w.val verticalCuts.val →
        r.val < maxGap h.val horizontalCuts.val * maxGap w.val verticalCuts.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (h w : Std.I64) (horizontalCuts verticalCuts : Slice Std.I64)
        (hpre : ValidInput h w horizontalCuts verticalCuts), ∀ r : Std.I64,
          Aegis.MaxArea.max_area h w horizontalCuts verticalCuts = ok r →
          modulus ≤ maxGap h.val horizontalCuts.val * maxGap w.val verticalCuts.val →
          r.val < maxGap h.val horizontalCuts.val * maxGap w.val verticalCuts.val) := by
    sorry

  /-- For every two such inputs, max_area h w H1 V1 returns Result.ok r1 and max_area h w H2 V2 returns Result.ok r2, and the integer values of r1 and r2 are equal.
    Preconditions: Two inputs (h, w, H1, V1) and (h, w, H2, V2) both satisfy the problem constraints: 2 <= h <= 1000000000, 2 <= w <= 1000000000; 1 <= len(H1) <= min(h - 1, 100000) and 1 <= len(V1) <= min(w - 1, 100000); 1 <= len(H2) <= min(h - 1, 100000) and 1 <= len(V2) <= min(w - 1, 100000); all elements of H1 and H2 lie in [1, h) and are pairwise distinct within each slice; all elements of V1 and V2 lie in [1, w) and are pairwise distinct within each slice. Let MH1, MV1 be the maximum horizontal and vertical gaps for the first input, and MH2, MV2 for the second input. Assume MH1 = MH2 and MV1 = MV2. -/
  theorem spec_10 (h w : Std.I64) (H1 V1 H2 V2 : Slice Std.I64)
      (hpre1 : ValidInput h w H1 V1) (hpre2 : ValidInput h w H2 V2)
      (hMH : maxGap h.val H1.val = maxGap h.val H2.val)
      (hMV : maxGap w.val V1.val = maxGap w.val V2.val) :
      ∃ r1 r2 : Std.I64,
        Aegis.MaxArea.max_area h w H1 V1 = ok r1 ∧
        Aegis.MaxArea.max_area h w H2 V2 = ok r2 ∧
        r1.val = r2.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (h w : Std.I64) (H1 V1 H2 V2 : Slice Std.I64)
        (hpre1 : ValidInput h w H1 V1) (hpre2 : ValidInput h w H2 V2)
        (hMH : maxGap h.val H1.val = maxGap h.val H2.val)
        (hMV : maxGap w.val V1.val = maxGap w.val V2.val), ∃ r1 r2 : Std.I64,
          Aegis.MaxArea.max_area h w H1 V1 = ok r1 ∧
          Aegis.MaxArea.max_area h w H2 V2 = ok r2 ∧
          r1.val = r2.val) := by
    sorry

  /-- For every such original input and lambda, max_area h w horizontalCuts verticalCuts returns Result.ok r, max_area (lambda * h) (lambda * w) H' V' returns Result.ok r', and the integer value of r' is congruent modulo 1000000007 to lambda^2 times the integer value of r.
    Preconditions: The original input (h, w, horizontalCuts, verticalCuts) satisfies the problem constraints: 2 <= h <= 1000000000, 2 <= w <= 1000000000; 1 <= len(horizontalCuts) <= min(h - 1, 100000); 1 <= len(verticalCuts) <= min(w - 1, 100000); all horizontalCuts elements are in [1, h) and distinct; all verticalCuts elements are in [1, w) and distinct. Let lambda be a positive integer such that lambda * h <= 1000000000 and lambda * w <= 1000000000. Define H'[i] = lambda * horizontalCuts[i] for 0 <= i < len(horizontalCuts), and V'[j] = lambda * verticalCuts[j] for 0 <= j < len(verticalCuts). These scaled inputs also satisfy the problem constraints. -/
  theorem spec_11 (h w : Std.I64) (horizontalCuts verticalCuts : Slice Std.I64)
      (hpre : ValidInput h w horizontalCuts verticalCuts)
      (lam : ℤ) (hlam : 0 < lam)
      (hhlam : lam * h.val ≤ 1000000000) (hwlam : lam * w.val ≤ 1000000000)
      (h' w' : Std.I64) (hh' : h'.val = lam * h.val) (hw' : w'.val = lam * w.val)
      (H' V' : Slice Std.I64)
      (hH' : H'.val.map (fun c => c.val) =
        (horizontalCuts.val.map (fun c => c.val)).map (fun c => lam * c))
      (hV' : V'.val.map (fun c => c.val) =
        (verticalCuts.val.map (fun c => c.val)).map (fun c => lam * c)) :
      ∃ r r' : Std.I64,
        Aegis.MaxArea.max_area h w horizontalCuts verticalCuts = ok r ∧
        Aegis.MaxArea.max_area h' w' H' V' = ok r' ∧
        Int.ModEq modulus r'.val (lam ^ 2 * r.val) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (h w : Std.I64) (horizontalCuts verticalCuts : Slice Std.I64)
        (hpre : ValidInput h w horizontalCuts verticalCuts)
        (lam : ℤ) (hlam : 0 < lam)
        (hhlam : lam * h.val ≤ 1000000000) (hwlam : lam * w.val ≤ 1000000000)
        (h' w' : Std.I64) (hh' : h'.val = lam * h.val) (hw' : w'.val = lam * w.val)
        (H' V' : Slice Std.I64)
        (hH' : H'.val.map (fun c => c.val) =
          (horizontalCuts.val.map (fun c => c.val)).map (fun c => lam * c))
        (hV' : V'.val.map (fun c => c.val) =
          (verticalCuts.val.map (fun c => c.val)).map (fun c => lam * c)), ∃ r r' : Std.I64,
          Aegis.MaxArea.max_area h w horizontalCuts verticalCuts = ok r ∧
          Aegis.MaxArea.max_area h' w' H' V' = ok r' ∧
          Int.ModEq modulus r'.val (lam ^ 2 * r.val)) := by
    sorry

  end AegisSpec.MaxArea
