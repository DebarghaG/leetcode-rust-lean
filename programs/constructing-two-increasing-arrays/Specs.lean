import Aegis.MinLargest.Code.Funs

/-!
# Specifications of `Aegis.MinLargest.min_largest`

LeetCode problem `constructing-two-increasing-arrays`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.MinLargest

  namespace AegisSpec.MinLargest

  def IsBitSeq (l : List Aeneas.Std.I64) : Prop := ∀ x ∈ l, x.val = 0 ∨ x.val = 1

  def BitParity (b : Aeneas.Std.I64) (a : Int) : Prop :=
    (b.val = 0 → a % 2 = 0) ∧ (b.val = 1 → a % 2 = 1)

  def ValidAssign (nums1 nums2 : List Aeneas.Std.I64) (A B : List Int) : Prop :=
    A.length = nums1.length ∧
    B.length = nums2.length ∧
    A.Pairwise (· < ·) ∧
    B.Pairwise (· < ·) ∧
    (∀ p ∈ A.zip nums1, 0 < p.1 ∧ BitParity p.2 p.1) ∧
    (∀ p ∈ B.zip nums2, 0 < p.1 ∧ BitParity p.2 p.1) ∧
    (∀ a ∈ A, ∀ b ∈ B, a ≠ b)

  def assignmentMax (A B : List Int) : Int := (A ++ B).foldr max 0

  def achievable (nums1 nums2 : List Aeneas.Std.I64) : Set Int :=
    {m | ∃ A B : List Int, ValidAssign nums1 nums2 A B ∧ assignmentMax A B = m}

  def IsMinLargest (nums1 nums2 : List Aeneas.Std.I64) (r : Int) : Prop :=
    r ∈ achievable nums1 nums2 ∧ ∀ m ∈ achievable nums1 nums2, r ≤ m

  def firstOf (b : Aeneas.Std.I64) : Int := if b.val = 0 then 2 else 1

  def nextOf (b : Aeneas.Std.I64) (a : Int) : Int := if a % 2 = b.val then a + 2 else a + 1

  def greedyFrom (a : Int) : List Aeneas.Std.I64 → List Int
    | [] => [a]
    | b :: bs => a :: greedyFrom (nextOf b a) bs

  def greedySeq (l : List Aeneas.Std.I64) : List Int :=
    match l with
    | [] => []
    | b :: bs => greedyFrom (firstOf b) bs

  def gval (l : List Aeneas.Std.I64) : Int := (greedySeq l).getLastD 0

  def countOf (v : Int) (l : List Aeneas.Std.I64) : Nat :=
    (l.filter (fun x => x.val = v)).length

  theorem greedyFrom_length (a : Int) (l : List Std.I64) :
      (greedyFrom a l).length = l.length + 1 := by
    induction l generalizing a with
    | nil => simp [greedyFrom]
    | cons b bs ih => simp [greedyFrom, ih]

  theorem greedySeq_length (l : List Std.I64) : (greedySeq l).length = l.length := by
    match l with
    | [] => rfl
    | b :: bs => simp [greedySeq, greedyFrom_length]

  /-- Let n1 = len(nums1) and n2 = len(nums2). A valid assignment consists of two strictly increasing sequences A = (a_0, ..., a_{n1-1}) and B = (b_0, ..., b_{n2-1}) of positive integers satisfying: (1) for each i with 0 <= i < n1, a_i is even if nums1[i] = 0 and odd if nums1[i] = 1; (2) for each j with 0 <= j < n2, b_j is even if nums2[j] = 0 and odd if nums2[j] = 1; (3) all a_i and b_j are pairwise distinct. The maximum assigned integer for such an assignment is max({a_i} ∪ {b_j}) if the union is non-empty, and 0 otherwise. The function returns an integer r that is the minimum possible value of this maximum over all valid assignments.
    Preconditions: nums1 and nums2 are sequences of integers, each element is 0 or 1. len(nums1) <= 1000, len(nums2) <= 1000. -/
  theorem spec_1 (nums1 nums2 : Slice Std.I64)
      (hbits1 : IsBitSeq nums1.val) (hbits2 : IsBitSeq nums2.val)
      (hlen1 : nums1.val.length ≤ 1000) (hlen2 : nums2.val.length ≤ 1000) :
      ∃ r : Std.I64,
        min_largest nums1 nums2 = ok r ∧ IsMinLargest nums1.val nums2.val r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64)
        (hbits1 : IsBitSeq nums1.val) (hbits2 : IsBitSeq nums2.val)
        (hlen1 : nums1.val.length ≤ 1000) (hlen2 : nums2.val.length ≤ 1000), ∃ r : Std.I64,
          min_largest nums1 nums2 = ok r ∧ IsMinLargest nums1.val nums2.val r.val) := by
    sorry

  /-- The function returns a result (i.e., it does not panic or fail) for every input satisfying the preconditions.
    Preconditions: nums1 and nums2 are sequences of integers, each element is 0 or 1. len(nums1) <= 1000, len(nums2) <= 1000. -/
  theorem spec_2 (nums1 nums2 : Slice Std.I64)
      (hbits1 : IsBitSeq nums1.val) (hbits2 : IsBitSeq nums2.val)
      (hlen1 : nums1.val.length ≤ 1000) (hlen2 : nums2.val.length ≤ 1000) :
      ∃ r : Std.I64, min_largest nums1 nums2 = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64)
        (hbits1 : IsBitSeq nums1.val) (hbits2 : IsBitSeq nums2.val)
        (hlen1 : nums1.val.length ≤ 1000) (hlen2 : nums2.val.length ≤ 1000), ∃ r : Std.I64, min_largest nums1 nums2 = ok r) := by
    sorry

  /-- If N > 0, then 1 <= r <= 2*N. If N = 0, then r = 0.
    Preconditions: nums1 and nums2 are sequences of integers, each element is 0 or 1. len(nums1) <= 1000, len(nums2) <= 1000. Let N = len(nums1) + len(nums2). -/
  theorem spec_3 (nums1 nums2 : Slice Std.I64)
      (hbits1 : IsBitSeq nums1.val) (hbits2 : IsBitSeq nums2.val)
      (hlen1 : nums1.val.length ≤ 1000) (hlen2 : nums2.val.length ≤ 1000) :
      ∀ r : Std.I64, min_largest nums1 nums2 = ok r →
        (0 < nums1.val.length + nums2.val.length →
          1 ≤ r.val ∧ r.val ≤ 2 * (↑(nums1.val.length + nums2.val.length) : Int)) ∧
        (nums1.val.length + nums2.val.length = 0 → r.val = 0) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64)
        (hbits1 : IsBitSeq nums1.val) (hbits2 : IsBitSeq nums2.val)
        (hlen1 : nums1.val.length ≤ 1000) (hlen2 : nums2.val.length ≤ 1000), ∀ r : Std.I64, min_largest nums1 nums2 = ok r →
          (0 < nums1.val.length + nums2.val.length →
            1 ≤ r.val ∧ r.val ≤ 2 * (↑(nums1.val.length + nums2.val.length) : Int)) ∧
          (nums1.val.length + nums2.val.length = 0 → r.val = 0)) := by
    sorry

  /-- r >= N.
    Preconditions: nums1 and nums2 are sequences of integers, each element is 0 or 1. len(nums1) <= 1000, len(nums2) <= 1000. Let N = len(nums1) + len(nums2). -/
  theorem spec_4 (nums1 nums2 : Slice Std.I64)
      (hbits1 : IsBitSeq nums1.val) (hbits2 : IsBitSeq nums2.val)
      (hlen1 : nums1.val.length ≤ 1000) (hlen2 : nums2.val.length ≤ 1000) :
      ∀ r : Std.I64, min_largest nums1 nums2 = ok r →
        (↑(nums1.val.length + nums2.val.length) : Int) ≤ r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64)
        (hbits1 : IsBitSeq nums1.val) (hbits2 : IsBitSeq nums2.val)
        (hlen1 : nums1.val.length ≤ 1000) (hlen2 : nums2.val.length ≤ 1000), ∀ r : Std.I64, min_largest nums1 nums2 = ok r →
          (↑(nums1.val.length + nums2.val.length) : Int) ≤ r.val) := by
    sorry

  /-- min_largest(nums1, nums2) = min_largest(nums2, nums1).
    Preconditions: nums1 and nums2 are sequences of integers, each element is 0 or 1. len(nums1) <= 1000, len(nums2) <= 1000. -/
  theorem spec_5 (nums1 nums2 : Slice Std.I64)
      (hbits1 : IsBitSeq nums1.val) (hbits2 : IsBitSeq nums2.val)
      (hlen1 : nums1.val.length ≤ 1000) (hlen2 : nums2.val.length ≤ 1000) :
      min_largest nums1 nums2 = min_largest nums2 nums1 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64)
        (hbits1 : IsBitSeq nums1.val) (hbits2 : IsBitSeq nums2.val)
        (hlen1 : nums1.val.length ≤ 1000) (hlen2 : nums2.val.length ≤ 1000), min_largest nums1 nums2 = min_largest nums2 nums1) := by
    sorry

  /-- There exists a valid assignment (as defined in spec_1) whose maximum assigned integer is exactly r.
    Preconditions: nums1 and nums2 are sequences of integers, each element is 0 or 1. len(nums1) <= 1000, len(nums2) <= 1000. -/
  theorem spec_6 (nums1 nums2 : Slice Std.I64)
      (hbits1 : IsBitSeq nums1.val) (hbits2 : IsBitSeq nums2.val)
      (hlen1 : nums1.val.length ≤ 1000) (hlen2 : nums2.val.length ≤ 1000) :
      ∀ r : Std.I64, min_largest nums1 nums2 = ok r →
        r.val ∈ achievable nums1.val nums2.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64)
        (hbits1 : IsBitSeq nums1.val) (hbits2 : IsBitSeq nums2.val)
        (hlen1 : nums1.val.length ≤ 1000) (hlen2 : nums2.val.length ≤ 1000), ∀ r : Std.I64, min_largest nums1 nums2 = ok r →
          r.val ∈ achievable nums1.val nums2.val) := by
    sorry

  /-- For every valid assignment (as defined in spec_1), its maximum assigned integer is at least r.
    Preconditions: nums1 and nums2 are sequences of integers, each element is 0 or 1. len(nums1) <= 1000, len(nums2) <= 1000. -/
  theorem spec_7 (nums1 nums2 : Slice Std.I64)
      (hbits1 : IsBitSeq nums1.val) (hbits2 : IsBitSeq nums2.val)
      (hlen1 : nums1.val.length ≤ 1000) (hlen2 : nums2.val.length ≤ 1000) :
      ∀ r : Std.I64, min_largest nums1 nums2 = ok r →
        ∀ m ∈ achievable nums1.val nums2.val, r.val ≤ m := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64)
        (hbits1 : IsBitSeq nums1.val) (hbits2 : IsBitSeq nums2.val)
        (hlen1 : nums1.val.length ≤ 1000) (hlen2 : nums2.val.length ≤ 1000), ∀ r : Std.I64, min_largest nums1 nums2 = ok r →
          ∀ m ∈ achievable nums1.val nums2.val, r.val ≤ m) := by
    sorry

  /-- Let N = len(nums1) + len(nums2). If N > 0, then r = 2*N. If N = 0, then r = 0.
    Preconditions: nums1 and nums2 are sequences of integers, each element is 0. len(nums1) <= 1000 and len(nums2) <= 1000. -/
  theorem spec_8 (nums1 nums2 : Slice Std.I64)
      (hbits1 : ∀ x ∈ nums1.val, x.val = 0) (hbits2 : ∀ x ∈ nums2.val, x.val = 0)
      (hlen1 : nums1.val.length ≤ 1000) (hlen2 : nums2.val.length ≤ 1000) :
      ∀ r : Std.I64, min_largest nums1 nums2 = ok r →
        (0 < nums1.val.length + nums2.val.length →
          r.val = 2 * (↑(nums1.val.length + nums2.val.length) : Int)) ∧
        (nums1.val.length + nums2.val.length = 0 → r.val = 0) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64)
        (hbits1 : ∀ x ∈ nums1.val, x.val = 0) (hbits2 : ∀ x ∈ nums2.val, x.val = 0)
        (hlen1 : nums1.val.length ≤ 1000) (hlen2 : nums2.val.length ≤ 1000), ∀ r : Std.I64, min_largest nums1 nums2 = ok r →
          (0 < nums1.val.length + nums2.val.length →
            r.val = 2 * (↑(nums1.val.length + nums2.val.length) : Int)) ∧
          (nums1.val.length + nums2.val.length = 0 → r.val = 0)) := by
    sorry

  /-- Let N = len(nums1) + len(nums2). If N > 0, then r = 2*N - 1. If N = 0, then r = 0.
    Preconditions: nums1 and nums2 are sequences of integers, each element is 1. len(nums1) <= 1000 and len(nums2) <= 1000. -/
  theorem spec_9 (nums1 nums2 : Slice Std.I64)
      (hbits1 : ∀ x ∈ nums1.val, x.val = 1) (hbits2 : ∀ x ∈ nums2.val, x.val = 1)
      (hlen1 : nums1.val.length ≤ 1000) (hlen2 : nums2.val.length ≤ 1000) :
      ∀ r : Std.I64, min_largest nums1 nums2 = ok r →
        (0 < nums1.val.length + nums2.val.length →
          r.val = 2 * (↑(nums1.val.length + nums2.val.length) : Int) - 1) ∧
        (nums1.val.length + nums2.val.length = 0 → r.val = 0) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64)
        (hbits1 : ∀ x ∈ nums1.val, x.val = 1) (hbits2 : ∀ x ∈ nums2.val, x.val = 1)
        (hlen1 : nums1.val.length ≤ 1000) (hlen2 : nums2.val.length ≤ 1000), ∀ r : Std.I64, min_largest nums1 nums2 = ok r →
          (0 < nums1.val.length + nums2.val.length →
            r.val = 2 * (↑(nums1.val.length + nums2.val.length) : Int) - 1) ∧
          (nums1.val.length + nums2.val.length = 0 → r.val = 0)) := by
    sorry

  /-- If x = 0 and y = 0, then r = 4. If x = 1 and y = 1, then r = 3. If x != y, then r = 2.
    Preconditions: nums1 and nums2 are sequences of integers, each element is 0 or 1. len(nums1) = 1, len(nums2) = 1, and x = nums1[0], y = nums2[0]. -/
  theorem spec_10 (nums1 nums2 : Slice Std.I64) (x y : Std.I64)
      (hbits1 : IsBitSeq nums1.val) (hbits2 : IsBitSeq nums2.val)
      (hlen1 : nums1.val.length = 1) (hlen2 : nums2.val.length = 1)
      (hx : nums1.val = [x]) (hy : nums2.val = [y]) :
      ∀ r : Std.I64, min_largest nums1 nums2 = ok r →
        ((x.val = 0 ∧ y.val = 0) → r.val = 4) ∧
        ((x.val = 1 ∧ y.val = 1) → r.val = 3) ∧
        (x.val ≠ y.val → r.val = 2) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64) (x y : Std.I64)
        (hbits1 : IsBitSeq nums1.val) (hbits2 : IsBitSeq nums2.val)
        (hlen1 : nums1.val.length = 1) (hlen2 : nums2.val.length = 1)
        (hx : nums1.val = [x]) (hy : nums2.val = [y]), ∀ r : Std.I64, min_largest nums1 nums2 = ok r →
          ((x.val = 0 ∧ y.val = 0) → r.val = 4) ∧
          ((x.val = 1 ∧ y.val = 1) → r.val = 3) ∧
          (x.val ≠ y.val → r.val = 2)) := by
    sorry

  /-- Let A = (a_0, ..., a_{k-1}) be the unique sequence of positive integers such that for each i, a_i is even if nums2[i] = 0 and odd if nums2[i] = 1, a_0 is the smallest positive integer with that parity, and for i > 0, a_i is the smallest integer greater than a_{i-1} with the parity of nums2[i]. Then r = a_{k-1}.
    Preconditions: nums1 is empty; nums2 is a sequence of 0s and 1s with len(nums2) = k and 1 <= k <= 1000. -/
  theorem spec_11 (nums1 nums2 : Slice Std.I64) (k : Nat)
      (hbits2 : IsBitSeq nums2.val)
      (hempty : nums1.val = [])
      (hlen : nums2.val.length = k)
      (hk1 : 1 ≤ k) (hk2 : k ≤ 1000) :
      ∀ r : Std.I64, min_largest nums1 nums2 = ok r →
        r.val = gval nums2.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64) (k : Nat)
        (hbits2 : IsBitSeq nums2.val)
        (hempty : nums1.val = [])
        (hlen : nums2.val.length = k)
        (hk1 : 1 ≤ k) (hk2 : k ≤ 1000), ∀ r : Std.I64, min_largest nums1 nums2 = ok r →
          r.val = gval nums2.val) := by
    sorry

  /-- min_largest(nums1, nums2) <= min_largest(nums1', nums2').
    Preconditions: nums1, nums2, nums1', nums2' are sequences of 0s and 1s with len(nums1) <= len(nums1') <= 1000 and len(nums2) <= len(nums2') <= 1000, and for all i < len(nums1), nums1[i] = nums1'[i], and for all j < len(nums2), nums2[j] = nums2'[j]. -/
  theorem spec_12 (nums1 nums1' nums2 nums2' : Slice Std.I64)
      (hbits1 : IsBitSeq nums1.val) (hbits2 : IsBitSeq nums2.val)
      (hbits1' : IsBitSeq nums1'.val) (hbits2' : IsBitSeq nums2'.val)
      (hlen1 : nums1.val.length ≤ nums1'.val.length) (hlen1' : nums1'.val.length ≤ 1000)
      (hlen2 : nums2.val.length ≤ nums2'.val.length) (hlen2' : nums2'.val.length ≤ 1000)
      (hpre1 : ∀ (i : Nat) (hi : i < nums1.val.length) (hi' : i < nums1'.val.length),
        nums1.val[i] = nums1'.val[i])
      (hpre2 : ∀ (j : Nat) (hj : j < nums2.val.length) (hj' : j < nums2'.val.length),
        nums2.val[j] = nums2'.val[j]) :
      ∀ r r' : Std.I64,
        min_largest nums1 nums2 = ok r → min_largest nums1' nums2' = ok r' → r.val ≤ r'.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums1 nums1' nums2 nums2' : Slice Std.I64)
        (hbits1 : IsBitSeq nums1.val) (hbits2 : IsBitSeq nums2.val)
        (hbits1' : IsBitSeq nums1'.val) (hbits2' : IsBitSeq nums2'.val)
        (hlen1 : nums1.val.length ≤ nums1'.val.length) (hlen1' : nums1'.val.length ≤ 1000)
        (hlen2 : nums2.val.length ≤ nums2'.val.length) (hlen2' : nums2'.val.length ≤ 1000)
        (hpre1 : ∀ (i : Nat) (hi : i < nums1.val.length) (hi' : i < nums1'.val.length),
          nums1.val[i] = nums1'.val[i])
        (hpre2 : ∀ (j : Nat) (hj : j < nums2.val.length) (hj' : j < nums2'.val.length),
          nums2.val[j] = nums2'.val[j]), ∀ r r' : Std.I64,
          min_largest nums1 nums2 = ok r → min_largest nums1' nums2' = ok r' → r.val ≤ r'.val) := by
    sorry

  /-- Let g(seq) be defined for any sequence seq of 0s and 1s as follows: g(empty) = 0; otherwise, let (a_0, ..., a_{m-1}) be the unique sequence of positive integers such that a_i is even if seq[i] = 0 and odd if seq[i] = 1, a_0 is the smallest positive integer with that parity, and for i > 0, a_i is the smallest integer greater than a_{i-1} with the parity of seq[i]; then g(seq) = a_{m-1}. Then r >= max(g(nums1), g(nums2)).
    Preconditions: nums1 and nums2 are sequences of integers, each element is 0 or 1. len(nums1) <= 1000, len(nums2) <= 1000. -/
  theorem spec_13 (nums1 nums2 : Slice Std.I64)
      (hbits1 : IsBitSeq nums1.val) (hbits2 : IsBitSeq nums2.val)
      (hlen1 : nums1.val.length ≤ 1000) (hlen2 : nums2.val.length ≤ 1000) :
      ∀ r : Std.I64, min_largest nums1 nums2 = ok r →
        max (gval nums1.val) (gval nums2.val) ≤ r.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64)
        (hbits1 : IsBitSeq nums1.val) (hbits2 : IsBitSeq nums2.val)
        (hlen1 : nums1.val.length ≤ 1000) (hlen2 : nums2.val.length ≤ 1000), ∀ r : Std.I64, min_largest nums1 nums2 = ok r →
          max (gval nums1.val) (gval nums2.val) ≤ r.val) := by
    sorry

  /-- r >= max(2*z, 2*o - 1, 0).
    Preconditions: nums1 and nums2 are sequences of integers, each element is 0 or 1. len(nums1) <= 1000 and len(nums2) <= 1000. Let z be the total number of zeros in nums1 and nums2, and let o be the total number of ones in nums1 and nums2. -/
  theorem spec_14 (nums1 nums2 : Slice Std.I64)
      (hbits1 : IsBitSeq nums1.val) (hbits2 : IsBitSeq nums2.val)
      (hlen1 : nums1.val.length ≤ 1000) (hlen2 : nums2.val.length ≤ 1000) :
      ∀ r : Std.I64, min_largest nums1 nums2 = ok r →
        max (2 * (↑(countOf 0 nums1.val + countOf 0 nums2.val) : Int))
            (max (2 * (↑(countOf 1 nums1.val + countOf 1 nums2.val) : Int) - 1) 0) ≤ r.val := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64)
        (hbits1 : IsBitSeq nums1.val) (hbits2 : IsBitSeq nums2.val)
        (hlen1 : nums1.val.length ≤ 1000) (hlen2 : nums2.val.length ≤ 1000), ∀ r : Std.I64, min_largest nums1 nums2 = ok r →
          max (2 * (↑(countOf 0 nums1.val + countOf 0 nums2.val) : Int))
              (max (2 * (↑(countOf 1 nums1.val + countOf 1 nums2.val) : Int) - 1) 0) ≤ r.val) := by
    sorry

  /-- If r = min_largest(nums1, nums2) and r' = min_largest(nums1', nums2'), then r <= r' <= r + 2.
    Preconditions: nums1, nums2, nums1', nums2' are sequences of 0s and 1s, each of length at most 1000. Either (nums1' is nums1 with one element b appended and nums2' = nums2) or (nums1' = nums1 and nums2' is nums2 with one element b appended), for some b in {0,1}. -/
  theorem spec_15 (nums1 nums2 nums1' nums2' : Slice Std.I64) (b : Std.I64)
      (hbits1 : IsBitSeq nums1.val) (hbits2 : IsBitSeq nums2.val)
      (hbits1' : IsBitSeq nums1'.val) (hbits2' : IsBitSeq nums2'.val)
      (hb : b.val = 0 ∨ b.val = 1)
      (hlen1 : nums1.val.length ≤ 1000) (hlen2 : nums2.val.length ≤ 1000)
      (hlen1' : nums1'.val.length ≤ 1000) (hlen2' : nums2'.val.length ≤ 1000)
      (happend : (nums1'.val = nums1.val ++ [b] ∧ nums2'.val = nums2.val) ∨
        (nums1'.val = nums1.val ∧ nums2'.val = nums2.val ++ [b])) :
      ∀ r r' : Std.I64,
        min_largest nums1 nums2 = ok r → min_largest nums1' nums2' = ok r' →
        r.val ≤ r'.val ∧ r'.val ≤ r.val + 2 := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (nums1 nums2 nums1' nums2' : Slice Std.I64) (b : Std.I64)
        (hbits1 : IsBitSeq nums1.val) (hbits2 : IsBitSeq nums2.val)
        (hbits1' : IsBitSeq nums1'.val) (hbits2' : IsBitSeq nums2'.val)
        (hb : b.val = 0 ∨ b.val = 1)
        (hlen1 : nums1.val.length ≤ 1000) (hlen2 : nums2.val.length ≤ 1000)
        (hlen1' : nums1'.val.length ≤ 1000) (hlen2' : nums2'.val.length ≤ 1000)
        (happend : (nums1'.val = nums1.val ++ [b] ∧ nums2'.val = nums2.val) ∨
          (nums1'.val = nums1.val ∧ nums2'.val = nums2.val ++ [b])), ∀ r r' : Std.I64,
          min_largest nums1 nums2 = ok r → min_largest nums1' nums2' = ok r' →
          r.val ≤ r'.val ∧ r'.val ≤ r.val + 2) := by
    sorry

  /-- r <= g(nums1 ++ nums2) and r <= g(nums2 ++ nums1).
    Preconditions: nums1 and nums2 are sequences of integers, each element is 0 or 1. len(nums1) <= 1000 and len(nums2) <= 1000. Let g be the function defined in spec_13. -/
  theorem spec_16 (nums1 nums2 : Slice Std.I64)
      (hbits1 : IsBitSeq nums1.val) (hbits2 : IsBitSeq nums2.val)
      (hlen1 : nums1.val.length ≤ 1000) (hlen2 : nums2.val.length ≤ 1000) :
      ∀ r : Std.I64, min_largest nums1 nums2 = ok r →
        r.val ≤ gval (nums1.val ++ nums2.val) ∧ r.val ≤ gval (nums2.val ++ nums1.val) := by
    sorry

  theorem spec_16_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64)
        (hbits1 : IsBitSeq nums1.val) (hbits2 : IsBitSeq nums2.val)
        (hlen1 : nums1.val.length ≤ 1000) (hlen2 : nums2.val.length ≤ 1000), ∀ r : Std.I64, min_largest nums1 nums2 = ok r →
          r.val ≤ gval (nums1.val ++ nums2.val) ∧ r.val ≤ gval (nums2.val ++ nums1.val)) := by
    sorry

  end AegisSpec.MinLargest
