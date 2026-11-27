import Aegis.GoodTriplets.Code.Funs

/-!
# Specifications of `Aegis.GoodTriplets.good_triplets`

LeetCode problem `count-good-triplets-in-an-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.GoodTriplets

  def ivals (s : Slice Std.I64) : List Int := s.val.map (fun x => x.val)

  def nth (s : Slice Std.I64) (i : Nat) : Int := (ivals s).getD i 0

  def InRange (n : Nat) (s : Slice Std.I64) : Prop :=
    ∀ i : Nat, i < n → 0 ≤ nth s i ∧ nth s i < (n : Int)

  def OccursOnce (n : Nat) (s : Slice Std.I64) : Prop :=
    ∀ v : Int, 0 ≤ v → v < (n : Int) → (ivals s).count v = 1

  def pos (s : Slice Std.I64) (v : Int) : Nat := (ivals s).idxOf v

  def choose3 (n : Nat) : Nat := n * (n - 1) * (n - 2) / 6

  noncomputable def goodTripleCount (nums1 nums2 : Slice Std.I64) (n : Nat) : Nat :=
    (((Finset.range n).product ((Finset.range n).product (Finset.range n))).filter
      (fun t : Nat × Nat × Nat =>
        pos nums1 (t.1 : Int) < pos nums1 (t.2.1 : Int) ∧
        pos nums1 (t.2.1 : Int) < pos nums1 (t.2.2 : Int) ∧
        pos nums2 (t.1 : Int) < pos nums2 (t.2.1 : Int) ∧
        pos nums2 (t.2.1 : Int) < pos nums2 (t.2.2 : Int))).card

  noncomputable def increasingTriples (s : Slice Std.I64) (n : Nat) : Nat :=
    (((Finset.range n).product ((Finset.range n).product (Finset.range n))).filter
      (fun t : Nat × Nat × Nat =>
        t.1 < t.2.1 ∧ t.2.1 < t.2.2 ∧
        nth s t.1 < nth s t.2.1 ∧ nth s t.2.1 < nth s t.2.2)).card

  /-- The function returns a result r and r is the number of triples (x,y,z) of integers with 0 <= x,y,z < n such that pos1(x) < pos1(y) < pos1(z) and pos2(x) < pos2(y) < pos2(z), where pos1(v) denotes the unique index i with 0 <= i < n and nums1[i] = v, and pos2(v) denotes the unique index i with 0 <= i < n and nums2[i] = v. Equivalently, r is the number of 3-element subsets {x,y,z} of {0,...,n-1} whose elements occur in the same relative order in nums1 and nums2.
    Preconditions: Let n = len(nums1). Preconditions: len(nums2) = n; 3 <= n <= 100000; for every i with 0 <= i < n, 0 <= nums1[i] < n and 0 <= nums2[i] < n; every value v with 0 <= v < n occurs exactly once in nums1 and exactly once in nums2 (equivalently, nums1 and nums2 are permutations of [0,1,...,n-1]). -/
  theorem spec_1 (nums1 nums2 : Slice Std.I64) (n : Nat)
      (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
      (hn3 : 3 ≤ n) (hnmax : n ≤ 100000)
      (hr1 : InRange n nums1) (hr2 : InRange n nums2)
      (ho1 : OccursOnce n nums1) (ho2 : OccursOnce n nums2) :
      ∃ r : Std.I64,
        Aegis.GoodTriplets.good_triplets nums1 nums2 = ok r ∧
          r.val = (goodTripleCount nums1 nums2 n : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64) (n : Nat)
        (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
        (hn3 : 3 ≤ n) (hnmax : n ≤ 100000)
        (hr1 : InRange n nums1) (hr2 : InRange n nums2)
        (ho1 : OccursOnce n nums1) (ho2 : OccursOnce n nums2), ∃ r : Std.I64,
          Aegis.GoodTriplets.good_triplets nums1 nums2 = ok r ∧
            r.val = (goodTripleCount nums1 nums2 n : Int)) := by
    sorry

  /-- For every nums1 and nums2 satisfying the preconditions, the function returns a result r (it does not fail, overflow, or panic).
    Preconditions: Let n = len(nums1). Preconditions: len(nums2) = n; 3 <= n <= 100000; for every i with 0 <= i < n, 0 <= nums1[i] < n and 0 <= nums2[i] < n; every value v with 0 <= v < n occurs exactly once in nums1 and exactly once in nums2 (equivalently, nums1 and nums2 are permutations of [0,1,...,n-1]). -/
  theorem spec_2 (nums1 nums2 : Slice Std.I64) (n : Nat)
      (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
      (hn3 : 3 ≤ n) (hnmax : n ≤ 100000)
      (hr1 : InRange n nums1) (hr2 : InRange n nums2)
      (ho1 : OccursOnce n nums1) (ho2 : OccursOnce n nums2) :
      ∃ r : Std.I64, Aegis.GoodTriplets.good_triplets nums1 nums2 = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64) (n : Nat)
        (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
        (hn3 : 3 ≤ n) (hnmax : n ≤ 100000)
        (hr1 : InRange n nums1) (hr2 : InRange n nums2)
        (ho1 : OccursOnce n nums1) (ho2 : OccursOnce n nums2), ∃ r : Std.I64, Aegis.GoodTriplets.good_triplets nums1 nums2 = ok r) := by
    sorry

  /-- Whenever the function returns a result r for inputs satisfying the preconditions, r <= n*(n-1)*(n-2)/6, where n = len(nums1) and the right-hand side is computed over the integers (it equals C(n,3)).
    Preconditions: Let n = len(nums1). Preconditions: len(nums2) = n; 3 <= n <= 100000; for every i with 0 <= i < n, 0 <= nums1[i] < n and 0 <= nums2[i] < n; every value v with 0 <= v < n occurs exactly once in nums1 and exactly once in nums2 (equivalently, nums1 and nums2 are permutations of [0,1,...,n-1]). -/
  theorem spec_3 (nums1 nums2 : Slice Std.I64) (n : Nat)
      (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
      (hn3 : 3 ≤ n) (hnmax : n ≤ 100000)
      (hr1 : InRange n nums1) (hr2 : InRange n nums2)
      (ho1 : OccursOnce n nums1) (ho2 : OccursOnce n nums2) :
      ∀ r : Std.I64,
        Aegis.GoodTriplets.good_triplets nums1 nums2 = ok r → r.val ≤ (choose3 n : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64) (n : Nat)
        (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
        (hn3 : 3 ≤ n) (hnmax : n ≤ 100000)
        (hr1 : InRange n nums1) (hr2 : InRange n nums2)
        (ho1 : OccursOnce n nums1) (ho2 : OccursOnce n nums2), ∀ r : Std.I64,
          Aegis.GoodTriplets.good_triplets nums1 nums2 = ok r → r.val ≤ (choose3 n : Int)) := by
    sorry

  /-- Whenever the function returns a result r, r = 0.
    Preconditions: Let n = len(nums1). Preconditions: len(nums2) = n; 3 <= n <= 100000; for every i with 0 <= i < n, 0 <= nums1[i] < n and 0 <= nums2[i] < n; every value v with 0 <= v < n occurs exactly once in nums1 and exactly once in nums2 (equivalently, nums1 and nums2 are permutations of [0,1,...,n-1]); additionally nums2[i] = nums1[n-1-i] for every i with 0 <= i < n (nums2 is the reversal of nums1). -/
  theorem spec_4 (nums1 nums2 : Slice Std.I64) (n : Nat)
      (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
      (hn3 : 3 ≤ n) (hnmax : n ≤ 100000)
      (hr1 : InRange n nums1) (hr2 : InRange n nums2)
      (ho1 : OccursOnce n nums1) (ho2 : OccursOnce n nums2)
      (hrev : ∀ i : Nat, i < n → nth nums2 i = nth nums1 (n - 1 - i)) :
      ∀ r : Std.I64,
        Aegis.GoodTriplets.good_triplets nums1 nums2 = ok r → r.val = 0 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64) (n : Nat)
        (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
        (hn3 : 3 ≤ n) (hnmax : n ≤ 100000)
        (hr1 : InRange n nums1) (hr2 : InRange n nums2)
        (ho1 : OccursOnce n nums1) (ho2 : OccursOnce n nums2)
        (hrev : ∀ i : Nat, i < n → nth nums2 i = nth nums1 (n - 1 - i)), ∀ r : Std.I64,
          Aegis.GoodTriplets.good_triplets nums1 nums2 = ok r → r.val = 0) := by
    sorry

  /-- For every pair of inputs (nums1,nums2) satisfying the preconditions, if the function returns r on (nums1,nums2) and returns r' on (nums2,nums1), then r = r'.
    Preconditions: Let n = len(nums1). Preconditions: len(nums2) = n; 3 <= n <= 100000; for every i with 0 <= i < n, 0 <= nums1[i] < n and 0 <= nums2[i] < n; every value v with 0 <= v < n occurs exactly once in nums1 and exactly once in nums2 (equivalently, nums1 and nums2 are permutations of [0,1,...,n-1]). -/
  theorem spec_5 (nums1 nums2 : Slice Std.I64) (n : Nat)
      (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
      (hn3 : 3 ≤ n) (hnmax : n ≤ 100000)
      (hr1 : InRange n nums1) (hr2 : InRange n nums2)
      (ho1 : OccursOnce n nums1) (ho2 : OccursOnce n nums2) :
      ∀ r r' : Std.I64,
        Aegis.GoodTriplets.good_triplets nums1 nums2 = ok r →
          Aegis.GoodTriplets.good_triplets nums2 nums1 = ok r' → r = r' := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64) (n : Nat)
        (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
        (hn3 : 3 ≤ n) (hnmax : n ≤ 100000)
        (hr1 : InRange n nums1) (hr2 : InRange n nums2)
        (ho1 : OccursOnce n nums1) (ho2 : OccursOnce n nums2), ∀ r r' : Std.I64,
          Aegis.GoodTriplets.good_triplets nums1 nums2 = ok r →
            Aegis.GoodTriplets.good_triplets nums2 nums1 = ok r' → r = r') := by
    sorry

  /-- Let nums1' and nums2' be defined by nums1'[i] = nums1[n-1-i] and nums2'[i] = nums2[n-1-i] for every i with 0 <= i < n. If the function returns r on (nums1,nums2) and returns r' on (nums1',nums2'), then r = r'.
    Preconditions: Let n = len(nums1). Preconditions: len(nums2) = n; 3 <= n <= 100000; for every i with 0 <= i < n, 0 <= nums1[i] < n and 0 <= nums2[i] < n; every value v with 0 <= v < n occurs exactly once in nums1 and exactly once in nums2 (equivalently, nums1 and nums2 are permutations of [0,1,...,n-1]). -/
  theorem spec_6 (nums1 nums2 nums1' nums2' : Slice Std.I64) (n : Nat)
      (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
      (hn1' : nums1'.val.length = n) (hn2' : nums2'.val.length = n)
      (hn3 : 3 ≤ n) (hnmax : n ≤ 100000)
      (hr1 : InRange n nums1) (hr2 : InRange n nums2)
      (ho1 : OccursOnce n nums1) (ho2 : OccursOnce n nums2)
      (hrev1 : ∀ i : Nat, i < n → nth nums1' i = nth nums1 (n - 1 - i))
      (hrev2 : ∀ i : Nat, i < n → nth nums2' i = nth nums2 (n - 1 - i)) :
      ∀ r r' : Std.I64,
        Aegis.GoodTriplets.good_triplets nums1 nums2 = ok r →
          Aegis.GoodTriplets.good_triplets nums1' nums2' = ok r' → r = r' := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums1 nums2 nums1' nums2' : Slice Std.I64) (n : Nat)
        (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
        (hn1' : nums1'.val.length = n) (hn2' : nums2'.val.length = n)
        (hn3 : 3 ≤ n) (hnmax : n ≤ 100000)
        (hr1 : InRange n nums1) (hr2 : InRange n nums2)
        (ho1 : OccursOnce n nums1) (ho2 : OccursOnce n nums2)
        (hrev1 : ∀ i : Nat, i < n → nth nums1' i = nth nums1 (n - 1 - i))
        (hrev2 : ∀ i : Nat, i < n → nth nums2' i = nth nums2 (n - 1 - i)), ∀ r r' : Std.I64,
          Aegis.GoodTriplets.good_triplets nums1 nums2 = ok r →
            Aegis.GoodTriplets.good_triplets nums1' nums2' = ok r' → r = r') := by
    sorry

  /-- For every bijection sigma from {0,...,n-1} to itself, define nums1'[i] = sigma(nums1[i]) and nums2'[i] = sigma(nums2[i]) for every i with 0 <= i < n. If the function returns r on (nums1,nums2) and returns r' on (nums1',nums2'), then r = r'.
    Preconditions: Let n = len(nums1). Preconditions: len(nums2) = n; 3 <= n <= 100000; for every i with 0 <= i < n, 0 <= nums1[i] < n and 0 <= nums2[i] < n; every value v with 0 <= v < n occurs exactly once in nums1 and exactly once in nums2 (equivalently, nums1 and nums2 are permutations of [0,1,...,n-1]). -/
  theorem spec_7 (nums1 nums2 nums1' nums2' : Slice Std.I64) (n : Nat)
      (sigma : Int → Int)
      (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
      (hn1' : nums1'.val.length = n) (hn2' : nums2'.val.length = n)
      (hn3 : 3 ≤ n) (hnmax : n ≤ 100000)
      (hr1 : InRange n nums1) (hr2 : InRange n nums2)
      (ho1 : OccursOnce n nums1) (ho2 : OccursOnce n nums2)
      (hsigma_maps : ∀ v : Int, 0 ≤ v → v < (n : Int) → 0 ≤ sigma v ∧ sigma v < (n : Int))
      (hsigma_inj : ∀ v w : Int, 0 ≤ v → v < (n : Int) → 0 ≤ w → w < (n : Int) →
        sigma v = sigma w → v = w)
      (hmapped1 : ∀ i : Nat, i < n → nth nums1' i = sigma (nth nums1 i))
      (hmapped2 : ∀ i : Nat, i < n → nth nums2' i = sigma (nth nums2 i)) :
      ∀ r r' : Std.I64,
        Aegis.GoodTriplets.good_triplets nums1 nums2 = ok r →
          Aegis.GoodTriplets.good_triplets nums1' nums2' = ok r' → r = r' := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums1 nums2 nums1' nums2' : Slice Std.I64) (n : Nat)
        (sigma : Int → Int)
        (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
        (hn1' : nums1'.val.length = n) (hn2' : nums2'.val.length = n)
        (hn3 : 3 ≤ n) (hnmax : n ≤ 100000)
        (hr1 : InRange n nums1) (hr2 : InRange n nums2)
        (ho1 : OccursOnce n nums1) (ho2 : OccursOnce n nums2)
        (hsigma_maps : ∀ v : Int, 0 ≤ v → v < (n : Int) → 0 ≤ sigma v ∧ sigma v < (n : Int))
        (hsigma_inj : ∀ v w : Int, 0 ≤ v → v < (n : Int) → 0 ≤ w → w < (n : Int) →
          sigma v = sigma w → v = w)
        (hmapped1 : ∀ i : Nat, i < n → nth nums1' i = sigma (nth nums1 i))
        (hmapped2 : ∀ i : Nat, i < n → nth nums2' i = sigma (nth nums2 i)), ∀ r r' : Std.I64,
          Aegis.GoodTriplets.good_triplets nums1 nums2 = ok r →
            Aegis.GoodTriplets.good_triplets nums1' nums2' = ok r' → r = r') := by
    sorry

  /-- Whenever the function returns a result r, r equals the number of triples of indices (a,b,c) with 0 <= a < b < c < n such that nums2[a] < nums2[b] < nums2[c].
    Preconditions: Let n = len(nums1). Preconditions: len(nums2) = n; 3 <= n <= 100000; for every i with 0 <= i < n, 0 <= nums1[i] < n and 0 <= nums2[i] < n; every value v with 0 <= v < n occurs exactly once in nums1 and exactly once in nums2 (equivalently, nums1 and nums2 are permutations of [0,1,...,n-1]); additionally nums1[i] = i for every i with 0 <= i < n (nums1 is the increasing permutation). -/
  theorem spec_8 (nums1 nums2 : Slice Std.I64) (n : Nat)
      (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
      (hn3 : 3 ≤ n) (hnmax : n ≤ 100000)
      (hr1 : InRange n nums1) (hr2 : InRange n nums2)
      (ho1 : OccursOnce n nums1) (ho2 : OccursOnce n nums2)
      (hid : ∀ i : Nat, i < n → nth nums1 i = (i : Int)) :
      ∀ r : Std.I64, Aegis.GoodTriplets.good_triplets nums1 nums2 = ok r →
        r.val = (increasingTriples nums2 n : Int) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64) (n : Nat)
        (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
        (hn3 : 3 ≤ n) (hnmax : n ≤ 100000)
        (hr1 : InRange n nums1) (hr2 : InRange n nums2)
        (ho1 : OccursOnce n nums1) (ho2 : OccursOnce n nums2)
        (hid : ∀ i : Nat, i < n → nth nums1 i = (i : Int)), ∀ r : Std.I64, Aegis.GoodTriplets.good_triplets nums1 nums2 = ok r →
          r.val = (increasingTriples nums2 n : Int)) := by
    sorry

  /-- Whenever the function returns a result r, r = n*(n-1)*(n-2)/6 if and only if nums1[i] = nums2[i] for every i with 0 <= i < n.
    Preconditions: Let n = len(nums1). Preconditions: len(nums2) = n; 3 <= n <= 100000; for every i with 0 <= i < n, 0 <= nums1[i] < n and 0 <= nums2[i] < n; every value v with 0 <= v < n occurs exactly once in nums1 and exactly once in nums2 (equivalently, nums1 and nums2 are permutations of [0,1,...,n-1]). -/
  theorem spec_9 (nums1 nums2 : Slice Std.I64) (n : Nat)
      (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
      (hn3 : 3 ≤ n) (hnmax : n ≤ 100000)
      (hr1 : InRange n nums1) (hr2 : InRange n nums2)
      (ho1 : OccursOnce n nums1) (ho2 : OccursOnce n nums2) :
      ∀ r : Std.I64, Aegis.GoodTriplets.good_triplets nums1 nums2 = ok r →
        (r.val = (choose3 n : Int) ↔ ∀ i : Nat, i < n → nth nums1 i = nth nums2 i) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64) (n : Nat)
        (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
        (hn3 : 3 ≤ n) (hnmax : n ≤ 100000)
        (hr1 : InRange n nums1) (hr2 : InRange n nums2)
        (ho1 : OccursOnce n nums1) (ho2 : OccursOnce n nums2), ∀ r : Std.I64, Aegis.GoodTriplets.good_triplets nums1 nums2 = ok r →
          (r.val = (choose3 n : Int) ↔ ∀ i : Nat, i < n → nth nums1 i = nth nums2 i)) := by
    sorry

  /-- Whenever the function returns a result r, r equals the number of triples of indices (a,b,c) with 0 <= a < b < c < n such that nums1[a] < nums1[b] < nums1[c].
    Preconditions: Let n = len(nums1). Preconditions: len(nums2) = n; 3 <= n <= 100000; for every i with 0 <= i < n, 0 <= nums1[i] < n and 0 <= nums2[i] < n; every value v with 0 <= v < n occurs exactly once in nums1 and exactly once in nums2 (equivalently, nums1 and nums2 are permutations of [0,1,...,n-1]); additionally nums2[i] = i for every i with 0 <= i < n (nums2 is the increasing permutation). -/
  theorem spec_10 (nums1 nums2 : Slice Std.I64) (n : Nat)
      (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
      (hn3 : 3 ≤ n) (hnmax : n ≤ 100000)
      (hr1 : InRange n nums1) (hr2 : InRange n nums2)
      (ho1 : OccursOnce n nums1) (ho2 : OccursOnce n nums2)
      (hid : ∀ i : Nat, i < n → nth nums2 i = (i : Int)) :
      ∀ r : Std.I64, Aegis.GoodTriplets.good_triplets nums1 nums2 = ok r →
        r.val = (increasingTriples nums1 n : Int) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64) (n : Nat)
        (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
        (hn3 : 3 ≤ n) (hnmax : n ≤ 100000)
        (hr1 : InRange n nums1) (hr2 : InRange n nums2)
        (ho1 : OccursOnce n nums1) (ho2 : OccursOnce n nums2)
        (hid : ∀ i : Nat, i < n → nth nums2 i = (i : Int)), ∀ r : Std.I64, Aegis.GoodTriplets.good_triplets nums1 nums2 = ok r →
          r.val = (increasingTriples nums1 n : Int)) := by
    sorry

  end AegisSpec.GoodTriplets
