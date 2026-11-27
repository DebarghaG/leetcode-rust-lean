import Aegis.MinAbsoluteSumDiff.Code.Funs

/-!
# Specifications of `Aegis.MinAbsoluteSumDiff.min_absolute_sum_diff`

LeetCode problem `minimum-absolute-sum-difference`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.MinAbsoluteSumDiff (min_absolute_sum_diff)

  namespace AegisSpec.MinAbsoluteSumDiff

  def M : ℤ := 1000000007

  def absDiff (a b : I64) : ℤ := |a.val - b.val|

  def valAt (l : List I64) (i : ℕ) : ℤ :=
    match l[i]? with
    | some x => x.val
    | none => 0

  theorem valAt_of_lt {l : List I64} {i : ℕ} (h : i < l.length) :
      valAt l i = (l.get ⟨i, h⟩).val := by
    simp only [valAt, List.getElem?_eq_getElem h]
    rfl

  def diffAt (a b : List I64) (i j : ℕ) : ℤ := |valAt a i - valAt b j|

  def totalDiff (nums1 nums2 : Slice I64) (n : ℕ) : ℤ :=
    ((List.range n).map (fun k => diffAt nums1.val nums2.val k k)).sum

  def totalDiffConst (l : List I64) (n : ℕ) (c : ℤ) : ℤ :=
    ((List.range n).map (fun k => |valAt l k - c|)).sum

  def C (nums1 nums2 : Slice I64) (n i j : ℕ) : ℤ :=
    totalDiff nums1 nums2 n - diffAt nums1.val nums2.val i i +
      diffAt nums1.val nums2.val j i

  def IsTrueMin (nums1 nums2 : Slice I64) (n : ℕ) (B : ℤ) : Prop :=
    B ≤ totalDiff nums1 nums2 n ∧
      (∀ i, i < n → ∀ j, j < n → B ≤ C nums1 nums2 n i j) ∧
      (B = totalDiff nums1 nums2 n ∨ ∃ i, i < n ∧ ∃ j, j < n ∧ B = C nums1 nums2 n i j)

  def AllInRange (l : List I64) (n : ℕ) (lo hi : ℤ) : Prop :=
    ∀ i, i < n → lo ≤ valAt l i ∧ valAt l i ≤ hi

  def ConstUpTo (l : List I64) (n : ℕ) (c : ℤ) : Prop :=
    ∀ i, i < n → valAt l i = c

  def IsMaxOn (f : ℕ → ℤ) (n : ℕ) (m : ℤ) : Prop :=
    (∃ i, i < n ∧ m = f i) ∧ ∀ i, i < n → f i ≤ m

  def IsMinOn (f : ℕ → ℤ) (n : ℕ) (m : ℤ) : Prop :=
    (∃ i, i < n ∧ m = f i) ∧ ∀ i, i < n → m ≤ f i

  def permVals (l : List I64) (n : ℕ) (pi : Equiv.Perm (Fin n)) : List ℤ :=
    List.ofFn (fun i : Fin n => valAt l (pi i))

  def shiftVals (l : List I64) (c : ℤ) : List ℤ := l.map (fun x => x.val + c)

  /-- Let M = 1000000007 and S = sum_{k=0}^{n-1} |nums1[k] - nums2[k]|. For 0 <= i < n and 0 <= j < n, let C(i,j) = S - |nums1[i] - nums2[i]| + |nums1[j] - nums2[i]|. Let B be the minimum of S and all values C(i,j); this is the true absolute sum difference after either no replacement or one replacement of nums1[i] by the value nums1[j]. The function returns a result r such that 0 <= r < M and there is an integer q >= 0 with B = q * M + r.
    Preconditions: Let n = len(nums1). Assume len(nums2) = n, 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= nums1[i] <= 100000 and 1 <= nums2[i] <= 100000. -/
  theorem spec_1 (nums1 nums2 : Slice I64) (n : ℕ) (B : ℤ)
      (hn : nums1.val.length = n) (hn2 : nums2.val.length = n)
      (hpos : 1 ≤ n) (hmax : n ≤ 100000)
      (hb1 : AllInRange nums1.val n 1 100000) (hb2 : AllInRange nums2.val n 1 100000)
      (hB : IsTrueMin nums1 nums2 n B) :
      ∃ r : I64, min_absolute_sum_diff nums1 nums2 = ok r ∧ 0 ≤ r.val ∧ r.val < M ∧
        ∃ q : ℤ, 0 ≤ q ∧ B = q * M + r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums1 nums2 : Slice I64) (n : ℕ) (B : ℤ)
        (hn : nums1.val.length = n) (hn2 : nums2.val.length = n)
        (hpos : 1 ≤ n) (hmax : n ≤ 100000)
        (hb1 : AllInRange nums1.val n 1 100000) (hb2 : AllInRange nums2.val n 1 100000)
        (hB : IsTrueMin nums1 nums2 n B), ∃ r : I64, min_absolute_sum_diff nums1 nums2 = ok r ∧ 0 ≤ r.val ∧ r.val < M ∧
          ∃ q : ℤ, 0 ≤ q ∧ B = q * M + r.val) := by
    sorry

  /-- The function returns a result r; it does not fail (overflow, out-of-bounds, or panic) on any input satisfying the preconditions.
    Preconditions: Let n = len(nums1). Assume len(nums2) = n, 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= nums1[i] <= 100000 and 1 <= nums2[i] <= 100000. -/
  theorem spec_2 (nums1 nums2 : Slice I64) (n : ℕ)
      (hn : nums1.val.length = n) (hn2 : nums2.val.length = n)
      (hpos : 1 ≤ n) (hmax : n ≤ 100000)
      (hb1 : AllInRange nums1.val n 1 100000) (hb2 : AllInRange nums2.val n 1 100000) :
      ∃ r : I64, min_absolute_sum_diff nums1 nums2 = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums1 nums2 : Slice I64) (n : ℕ)
        (hn : nums1.val.length = n) (hn2 : nums2.val.length = n)
        (hpos : 1 ≤ n) (hmax : n ≤ 100000)
        (hb1 : AllInRange nums1.val n 1 100000) (hb2 : AllInRange nums2.val n 1 100000), ∃ r : I64, min_absolute_sum_diff nums1 nums2 = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r < 1000000007.
    Preconditions: Let n = len(nums1). Assume len(nums2) = n, 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= nums1[i] <= 100000 and 1 <= nums2[i] <= 100000. -/
  theorem spec_3 (nums1 nums2 : Slice I64) (n : ℕ)
      (hn : nums1.val.length = n) (hn2 : nums2.val.length = n)
      (hpos : 1 ≤ n) (hmax : n ≤ 100000)
      (hb1 : AllInRange nums1.val n 1 100000) (hb2 : AllInRange nums2.val n 1 100000) :
      ∀ r : I64, min_absolute_sum_diff nums1 nums2 = ok r → 0 ≤ r.val ∧ r.val < M := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums1 nums2 : Slice I64) (n : ℕ)
        (hn : nums1.val.length = n) (hn2 : nums2.val.length = n)
        (hpos : 1 ≤ n) (hmax : n ≤ 100000)
        (hb1 : AllInRange nums1.val n 1 100000) (hb2 : AllInRange nums2.val n 1 100000), ∀ r : I64, min_absolute_sum_diff nums1 nums2 = ok r → 0 ≤ r.val ∧ r.val < M) := by
    sorry

  /-- Let S = sum_{k=0}^{n-1} |nums1[k] - nums2[k]|, let B be the true minimum absolute sum difference after at most one replacement, and let D = max_{0 <= i < n} |nums1[i] - nums2[i]|. Whenever the function returns r, r is B modulo 1000000007 and S - D <= B <= S.
    Preconditions: Let n = len(nums1). Assume len(nums2) = n, 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= nums1[i] <= 100000 and 1 <= nums2[i] <= 100000. -/
  theorem spec_4 (nums1 nums2 : Slice I64) (n : ℕ) (B D : ℤ)
      (hn : nums1.val.length = n) (hn2 : nums2.val.length = n)
      (hpos : 1 ≤ n) (hmax : n ≤ 100000)
      (hb1 : AllInRange nums1.val n 1 100000) (hb2 : AllInRange nums2.val n 1 100000)
      (hB : IsTrueMin nums1 nums2 n B)
      (hD : IsMaxOn (fun i => diffAt nums1.val nums2.val i i) n D) :
      ∀ r : I64, min_absolute_sum_diff nums1 nums2 = ok r →
        (∃ q : ℤ, 0 ≤ q ∧ B = q * M + r.val) ∧
          totalDiff nums1 nums2 n - D ≤ B ∧ B ≤ totalDiff nums1 nums2 n := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums1 nums2 : Slice I64) (n : ℕ) (B D : ℤ)
        (hn : nums1.val.length = n) (hn2 : nums2.val.length = n)
        (hpos : 1 ≤ n) (hmax : n ≤ 100000)
        (hb1 : AllInRange nums1.val n 1 100000) (hb2 : AllInRange nums2.val n 1 100000)
        (hB : IsTrueMin nums1 nums2 n B)
        (hD : IsMaxOn (fun i => diffAt nums1.val nums2.val i i) n D), ∀ r : I64, min_absolute_sum_diff nums1 nums2 = ok r →
          (∃ q : ℤ, 0 ≤ q ∧ B = q * M + r.val) ∧
            totalDiff nums1 nums2 n - D ≤ B ∧ B ≤ totalDiff nums1 nums2 n) := by
    sorry

  /-- The function returns r = |nums1[0] - nums2[0]|.
    Preconditions: Let n = len(nums1). Assume n = 1, len(nums2) = 1, and 1 <= nums1[0] <= 100000 and 1 <= nums2[0] <= 100000. -/
  theorem spec_5 (nums1 nums2 : Slice I64) (n : ℕ)
      (hn : nums1.val.length = n) (hn2 : nums2.val.length = n) (hone : n = 1)
      (hb1 : AllInRange nums1.val n 1 100000) (hb2 : AllInRange nums2.val n 1 100000) :
      ∃ r : I64, min_absolute_sum_diff nums1 nums2 = ok r ∧
        r.val = |valAt nums1.val 0 - valAt nums2.val 0| := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums1 nums2 : Slice I64) (n : ℕ)
        (hn : nums1.val.length = n) (hn2 : nums2.val.length = n) (hone : n = 1)
        (hb1 : AllInRange nums1.val n 1 100000) (hb2 : AllInRange nums2.val n 1 100000), ∃ r : I64, min_absolute_sum_diff nums1 nums2 = ok r ∧
          r.val = |valAt nums1.val 0 - valAt nums2.val 0|) := by
    sorry

  /-- The function returns r = 0.
    Preconditions: Let n = len(nums1). Assume len(nums2) = n, 1 <= n <= 100000, 1 <= nums1[i] <= 100000 and 1 <= nums2[i] <= 100000 for every i, and nums1[i] = nums2[i] for every i with 0 <= i < n. -/
  theorem spec_6 (nums1 nums2 : Slice I64) (n : ℕ)
      (hn : nums1.val.length = n) (hn2 : nums2.val.length = n)
      (hpos : 1 ≤ n) (hmax : n ≤ 100000)
      (hb1 : AllInRange nums1.val n 1 100000) (hb2 : AllInRange nums2.val n 1 100000)
      (heq : ∀ i, i < n → valAt nums1.val i = valAt nums2.val i) :
      ∃ r : I64, min_absolute_sum_diff nums1 nums2 = ok r ∧ r.val = 0 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums1 nums2 : Slice I64) (n : ℕ)
        (hn : nums1.val.length = n) (hn2 : nums2.val.length = n)
        (hpos : 1 ≤ n) (hmax : n ≤ 100000)
        (hb1 : AllInRange nums1.val n 1 100000) (hb2 : AllInRange nums2.val n 1 100000)
        (heq : ∀ i, i < n → valAt nums1.val i = valAt nums2.val i), ∃ r : I64, min_absolute_sum_diff nums1 nums2 = ok r ∧ r.val = 0) := by
    sorry

  /-- Let S = sum_{k=0}^{n-1} |c - nums2[k]|. The function returns r such that 0 <= r < 1000000007 and S = q * 1000000007 + r for some integer q >= 0.
    Preconditions: Let n = len(nums1). Assume len(nums2) = n, 1 <= n <= 100000, and 1 <= nums1[i] <= 100000 and 1 <= nums2[i] <= 100000 for every i. Assume also that there is an integer c with nums1[i] = c for every 0 <= i < n. -/
  theorem spec_7 (nums1 nums2 : Slice I64) (n : ℕ) (c : ℤ)
      (hn : nums1.val.length = n) (hn2 : nums2.val.length = n)
      (hpos : 1 ≤ n) (hmax : n ≤ 100000)
      (hb1 : AllInRange nums1.val n 1 100000) (hb2 : AllInRange nums2.val n 1 100000)
      (hc : ConstUpTo nums1.val n c) :
      ∃ r : I64, min_absolute_sum_diff nums1 nums2 = ok r ∧ 0 ≤ r.val ∧ r.val < M ∧
        ∃ q : ℤ, 0 ≤ q ∧ totalDiffConst nums2.val n c = q * M + r.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums1 nums2 : Slice I64) (n : ℕ) (c : ℤ)
        (hn : nums1.val.length = n) (hn2 : nums2.val.length = n)
        (hpos : 1 ≤ n) (hmax : n ≤ 100000)
        (hb1 : AllInRange nums1.val n 1 100000) (hb2 : AllInRange nums2.val n 1 100000)
        (hc : ConstUpTo nums1.val n c), ∃ r : I64, min_absolute_sum_diff nums1 nums2 = ok r ∧ 0 ≤ r.val ∧ r.val < M ∧
          ∃ q : ℤ, 0 ≤ q ∧ totalDiffConst nums2.val n c = q * M + r.val) := by
    sorry

  /-- Let S = sum_{k=0}^{n-1} |nums1[k] - c|, Dmax = max_{0 <= i < n} |nums1[i] - c|, and Dmin = min_{0 <= j < n} |nums1[j] - c|. The function returns r such that 0 <= r < 1000000007 and S - Dmax + Dmin = q * 1000000007 + r for some integer q >= 0.
    Preconditions: Let n = len(nums1). Assume len(nums2) = n, 1 <= n <= 100000, and 1 <= nums1[i] <= 100000 and 1 <= nums2[i] <= 100000 for every i. Assume also that there is an integer c with nums2[i] = c for every 0 <= i < n. -/
  theorem spec_8 (nums1 nums2 : Slice I64) (n : ℕ) (c Dmax Dmin : ℤ)
      (hn : nums1.val.length = n) (hn2 : nums2.val.length = n)
      (hpos : 1 ≤ n) (hmax : n ≤ 100000)
      (hb1 : AllInRange nums1.val n 1 100000) (hb2 : AllInRange nums2.val n 1 100000)
      (hc : ConstUpTo nums2.val n c)
      (hDmax : IsMaxOn (fun i => |valAt nums1.val i - c|) n Dmax)
      (hDmin : IsMinOn (fun i => |valAt nums1.val i - c|) n Dmin) :
      ∃ r : I64, min_absolute_sum_diff nums1 nums2 = ok r ∧ 0 ≤ r.val ∧ r.val < M ∧
        ∃ q : ℤ, 0 ≤ q ∧
          totalDiffConst nums1.val n c - Dmax + Dmin = q * M + r.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums1 nums2 : Slice I64) (n : ℕ) (c Dmax Dmin : ℤ)
        (hn : nums1.val.length = n) (hn2 : nums2.val.length = n)
        (hpos : 1 ≤ n) (hmax : n ≤ 100000)
        (hb1 : AllInRange nums1.val n 1 100000) (hb2 : AllInRange nums2.val n 1 100000)
        (hc : ConstUpTo nums2.val n c)
        (hDmax : IsMaxOn (fun i => |valAt nums1.val i - c|) n Dmax)
        (hDmin : IsMinOn (fun i => |valAt nums1.val i - c|) n Dmin), ∃ r : I64, min_absolute_sum_diff nums1 nums2 = ok r ∧ 0 ≤ r.val ∧ r.val < M ∧
          ∃ q : ℤ, 0 ≤ q ∧
            totalDiffConst nums1.val n c - Dmax + Dmin = q * M + r.val) := by
    sorry

  /-- Let S = sum_{k=0}^{n-1} |nums1[k] - nums2[k]|, and for 0 <= i,j < n let C(i,j) = S - |nums1[i] - nums2[i]| + |nums1[j] - nums2[i]|. Let B be the minimum of S and all C(i,j). Whenever the function returns r, there exist indices i,j with 0 <= i,j < n such that C(i,j) = B, and r is B modulo 1000000007.
    Preconditions: Let n = len(nums1). Assume len(nums2) = n, 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= nums1[i] <= 100000 and 1 <= nums2[i] <= 100000. -/
  theorem spec_9 (nums1 nums2 : Slice I64) (n : ℕ) (B : ℤ)
      (hn : nums1.val.length = n) (hn2 : nums2.val.length = n)
      (hpos : 1 ≤ n) (hmax : n ≤ 100000)
      (hb1 : AllInRange nums1.val n 1 100000) (hb2 : AllInRange nums2.val n 1 100000)
      (hB : IsTrueMin nums1 nums2 n B) :
      ∀ r : I64, min_absolute_sum_diff nums1 nums2 = ok r →
        (∃ i, i < n ∧ ∃ j, j < n ∧ C nums1 nums2 n i j = B) ∧
          ∃ q : ℤ, 0 ≤ q ∧ B = q * M + r.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums1 nums2 : Slice I64) (n : ℕ) (B : ℤ)
        (hn : nums1.val.length = n) (hn2 : nums2.val.length = n)
        (hpos : 1 ≤ n) (hmax : n ≤ 100000)
        (hb1 : AllInRange nums1.val n 1 100000) (hb2 : AllInRange nums2.val n 1 100000)
        (hB : IsTrueMin nums1 nums2 n B), ∀ r : I64, min_absolute_sum_diff nums1 nums2 = ok r →
          (∃ i, i < n ∧ ∃ j, j < n ∧ C nums1 nums2 n i j = B) ∧
            ∃ q : ℤ, 0 ≤ q ∧ B = q * M + r.val) := by
    sorry

  /-- Let S = sum_{k=0}^{n-1} |nums1[k] - nums2[k]|, for 0 <= i,j < n let C(i,j) = S - |nums1[i] - nums2[i]| + |nums1[j] - nums2[i]|, and let B be the true minimum after at most one replacement. Whenever the function returns r, r is B modulo 1000000007, B <= S, and B <= C(i,j) for every 0 <= i,j < n.
    Preconditions: Let n = len(nums1). Assume len(nums2) = n, 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= nums1[i] <= 100000 and 1 <= nums2[i] <= 100000. -/
  theorem spec_10 (nums1 nums2 : Slice I64) (n : ℕ) (B : ℤ)
      (hn : nums1.val.length = n) (hn2 : nums2.val.length = n)
      (hpos : 1 ≤ n) (hmax : n ≤ 100000)
      (hb1 : AllInRange nums1.val n 1 100000) (hb2 : AllInRange nums2.val n 1 100000)
      (hB : IsTrueMin nums1 nums2 n B) :
      ∀ r : I64, min_absolute_sum_diff nums1 nums2 = ok r →
        (∃ q : ℤ, 0 ≤ q ∧ B = q * M + r.val) ∧
          B ≤ totalDiff nums1 nums2 n ∧
          ∀ i, i < n → ∀ j, j < n → B ≤ C nums1 nums2 n i j := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums1 nums2 : Slice I64) (n : ℕ) (B : ℤ)
        (hn : nums1.val.length = n) (hn2 : nums2.val.length = n)
        (hpos : 1 ≤ n) (hmax : n ≤ 100000)
        (hb1 : AllInRange nums1.val n 1 100000) (hb2 : AllInRange nums2.val n 1 100000)
        (hB : IsTrueMin nums1 nums2 n B), ∀ r : I64, min_absolute_sum_diff nums1 nums2 = ok r →
          (∃ q : ℤ, 0 ≤ q ∧ B = q * M + r.val) ∧
            B ≤ totalDiff nums1 nums2 n ∧
            ∀ i, i < n → ∀ j, j < n → B ≤ C nums1 nums2 n i j) := by
    sorry

  /-- For every permutation pi of {0,1,...,n-1}, define slices a' and b' of length n by a'[i] = nums1[pi(i)] and b'[i] = nums2[pi(i)] for 0 <= i < n. Whenever min_absolute_sum_diff(nums1, nums2) returns r and min_absolute_sum_diff(a', b') returns r', we have r = r'.
    Preconditions: Let n = len(nums1). Assume len(nums2) = n, 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= nums1[i] <= 100000 and 1 <= nums2[i] <= 100000. -/
  theorem spec_11 (nums1 nums2 a' b' : Slice I64) (n : ℕ) (pi : Equiv.Perm (Fin n))
      (hn : nums1.val.length = n) (hn2 : nums2.val.length = n)
      (hpos : 1 ≤ n) (hmax : n ≤ 100000)
      (hb1 : AllInRange nums1.val n 1 100000) (hb2 : AllInRange nums2.val n 1 100000)
      (ha' : a'.val.map (fun x => x.val) = permVals nums1.val n pi)
      (hb' : b'.val.map (fun x => x.val) = permVals nums2.val n pi) :
      ∀ r r' : I64, min_absolute_sum_diff nums1 nums2 = ok r →
        min_absolute_sum_diff a' b' = ok r' → r.val = r'.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums1 nums2 a' b' : Slice I64) (n : ℕ) (pi : Equiv.Perm (Fin n))
        (hn : nums1.val.length = n) (hn2 : nums2.val.length = n)
        (hpos : 1 ≤ n) (hmax : n ≤ 100000)
        (hb1 : AllInRange nums1.val n 1 100000) (hb2 : AllInRange nums2.val n 1 100000)
        (ha' : a'.val.map (fun x => x.val) = permVals nums1.val n pi)
        (hb' : b'.val.map (fun x => x.val) = permVals nums2.val n pi), ∀ r r' : I64, min_absolute_sum_diff nums1 nums2 = ok r →
          min_absolute_sum_diff a' b' = ok r' → r.val = r'.val) := by
    sorry

  /-- For any integer c such that 1 <= nums1[i] + c <= 100000 and 1 <= nums2[i] + c <= 100000 for all 0 <= i < n, define a'[i] = nums1[i] + c and b'[i] = nums2[i] + c. Whenever min_absolute_sum_diff(nums1, nums2) returns r and min_absolute_sum_diff(a', b') returns r', we have r = r'.
    Preconditions: Let n = len(nums1). Assume len(nums2) = n, 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= nums1[i] <= 100000 and 1 <= nums2[i] <= 100000. -/
  theorem spec_12 (nums1 nums2 a' b' : Slice I64) (n : ℕ) (c : ℤ)
      (hn : nums1.val.length = n) (hn2 : nums2.val.length = n)
      (hpos : 1 ≤ n) (hmax : n ≤ 100000)
      (hb1 : AllInRange nums1.val n 1 100000) (hb2 : AllInRange nums2.val n 1 100000)
      (hshift1 : ∀ i, i < n → 1 ≤ valAt nums1.val i + c ∧ valAt nums1.val i + c ≤ 100000)
      (hshift2 : ∀ i, i < n → 1 ≤ valAt nums2.val i + c ∧ valAt nums2.val i + c ≤ 100000)
      (ha' : a'.val.map (fun x => x.val) = shiftVals nums1.val c)
      (hb' : b'.val.map (fun x => x.val) = shiftVals nums2.val c) :
      ∀ r r' : I64, min_absolute_sum_diff nums1 nums2 = ok r →
        min_absolute_sum_diff a' b' = ok r' → r.val = r'.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums1 nums2 a' b' : Slice I64) (n : ℕ) (c : ℤ)
        (hn : nums1.val.length = n) (hn2 : nums2.val.length = n)
        (hpos : 1 ≤ n) (hmax : n ≤ 100000)
        (hb1 : AllInRange nums1.val n 1 100000) (hb2 : AllInRange nums2.val n 1 100000)
        (hshift1 : ∀ i, i < n → 1 ≤ valAt nums1.val i + c ∧ valAt nums1.val i + c ≤ 100000)
        (hshift2 : ∀ i, i < n → 1 ≤ valAt nums2.val i + c ∧ valAt nums2.val i + c ≤ 100000)
        (ha' : a'.val.map (fun x => x.val) = shiftVals nums1.val c)
        (hb' : b'.val.map (fun x => x.val) = shiftVals nums2.val c), ∀ r r' : I64, min_absolute_sum_diff nums1 nums2 = ok r →
          min_absolute_sum_diff a' b' = ok r' → r.val = r'.val) := by
    sorry

  end AegisSpec.MinAbsoluteSumDiff
