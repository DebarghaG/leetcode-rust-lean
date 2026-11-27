import Aegis.LexicographicallySmallestArray.Code.Funs

/-!
# Specifications of `Aegis.LexicographicallySmallestArray.lexicographically_smallest_array`

LeetCode problem `make-lexicographically-smallest-array-by-swapping-elements`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.LexicographicallySmallestArray

  open scoped Classical

  noncomputable section

  def sval (s : Slice Std.I64) : List ℤ := s.val.map (fun x => x.val)

  def vval (v : alloc.vec.Vec Std.I64) : List ℤ := v.val.map (fun x => x.val)

  def entry (l : List ℤ) (i : ℕ) : ℤ := l.getD i 0

  def Pre (nums : Slice Std.I64) (limit : Std.I64) : Prop :=
    1 ≤ (sval nums).length ∧ (sval nums).length ≤ 100000 ∧
      (∀ i : Fin (sval nums).length,
        1 ≤ (sval nums).get i ∧ (sval nums).get i ≤ 1000000000) ∧
      0 ≤ limit.val ∧ limit.val ≤ 1000000000

  def swapAt (a : List ℤ) (p q : ℕ) : List ℤ := (a.set p (a.getD q 0)).set q (a.getD p 0)

  def SwapStep (limit : ℤ) (a b : List ℤ) : Prop :=
    ∃ p q, p < a.length ∧ q < a.length ∧ |a.getD p 0 - a.getD q 0| ≤ limit ∧ b = swapAt a p q

  def Obtainable (limit : ℤ) (a b : List ℤ) : Prop := Relation.ReflTransGen (SwapStep limit) a b

  def LexLe (a b : List ℤ) : Prop :=
    a = b ∨
      ∃ h, h < a.length ∧ h < b.length ∧ a.take h = b.take h ∧ a.getD h 0 < b.getD h 0

  def SameComp (us : List ℤ) (limit : ℤ) (i j : Fin us.length) : Prop :=
    Relation.ReflTransGen (fun p q : Fin us.length => p ≠ q ∧ |us.get p - us.get q| ≤ limit) i j

  def compCount (us : List ℤ) (limit : ℤ) (i : Fin us.length) (l : List ℤ) (v : ℤ) : ℕ :=
    (Finset.univ.filter (fun j : Fin us.length => SameComp us limit i j ∧ entry l j.val = v)).card

  def countVal (l : List ℤ) (v : ℤ) : ℕ :=
    (Finset.univ.filter (fun j : Fin l.length => l.get j = v)).card

  def IsMinOf (us : List ℤ) (m : ℤ) : Prop := (∀ x ∈ us, m ≤ x) ∧ m ∈ us

  def IsMaxOf (us : List ℤ) (M : ℤ) : Prop := (∀ x ∈ us, x ≤ M) ∧ M ∈ us

  def IsSmallestInComp (us : List ℤ) (limit : ℤ) (i p : Fin us.length) : Prop :=
    SameComp us limit i p ∧ ∀ j, SameComp us limit i j → p.val ≤ j.val

  def IsLargestInComp (us : List ℤ) (limit : ℤ) (i q : Fin us.length) : Prop :=
    SameComp us limit i q ∧ ∀ j, SameComp us limit i j → j.val ≤ q.val

  def IsCompMin (us : List ℤ) (limit : ℤ) (i : Fin us.length) (m : ℤ) : Prop :=
    (∀ j, SameComp us limit i j → m ≤ entry us j.val) ∧
      ∃ j, SameComp us limit i j ∧ entry us j.val = m

  def IsCompMax (us : List ℤ) (limit : ℤ) (i : Fin us.length) (M : ℤ) : Prop :=
    (∀ j, SameComp us limit i j → entry us j.val ≤ M) ∧
      ∃ j, SameComp us limit i j ∧ entry us j.val = M

  /-- Define an array b (with len(b) = len(nums)) to be obtainable from nums if there is a finite sequence of arrays a_0, ..., a_k of length len(nums) such that a_0 = nums, a_k = b, and for each t with 0 <= t < k, a_{t+1} is obtained from a_t by swapping the entries at some indices p and q with 0 <= p < len(nums), 0 <= q < len(nums), and |a_t[p] - a_t[q]| <= limit. Whenever the function returns a result r, r is obtainable from nums, and for every array b obtainable from nums, r is lexicographically no larger than b: either r = b, or at the least index h with 0 <= h < len(nums) and r[h] != b[h], we have r[h] < b[h].
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 0 <= limit <= 1000000000. -/
  theorem spec_1 (nums : Slice Std.I64) (limit : Std.I64) (hpre : Pre nums limit) :
      ∀ r, Aegis.LexicographicallySmallestArray.lexicographically_smallest_array nums limit
            = ok r →
        Obtainable limit.val (sval nums) (vval r) ∧
          ∀ b : List ℤ, b.length = (sval nums).length →
            Obtainable limit.val (sval nums) b → LexLe (vval r) b := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (limit : Std.I64) (hpre : Pre nums limit), ∀ r, Aegis.LexicographicallySmallestArray.lexicographically_smallest_array nums limit
              = ok r →
          Obtainable limit.val (sval nums) (vval r) ∧
            ∀ b : List ℤ, b.length = (sval nums).length →
              Obtainable limit.val (sval nums) b → LexLe (vval r) b) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r; it does not fail through arithmetic overflow, out-of-bounds access, or panic.
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 0 <= limit <= 1000000000. -/
  theorem spec_2 (nums : Slice Std.I64) (limit : Std.I64) (hpre : Pre nums limit) :
      ∃ r, Aegis.LexicographicallySmallestArray.lexicographically_smallest_array nums limit
            = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (limit : Std.I64) (hpre : Pre nums limit), ∃ r, Aegis.LexicographicallySmallestArray.lexicographically_smallest_array nums limit
              = ok r) := by
    sorry

  /-- Whenever the function returns a result r, len(r) = len(nums).
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 0 <= limit <= 1000000000. -/
  theorem spec_3 (nums : Slice Std.I64) (limit : Std.I64) (hpre : Pre nums limit) :
      ∀ r, Aegis.LexicographicallySmallestArray.lexicographically_smallest_array nums limit
            = ok r →
        (vval r).length = (sval nums).length := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (limit : Std.I64) (hpre : Pre nums limit), ∀ r, Aegis.LexicographicallySmallestArray.lexicographically_smallest_array nums limit
              = ok r →
          (vval r).length = (sval nums).length) := by
    sorry

  /-- Let G be the graph whose vertices are the indices 0, ..., len(nums)-1, with an edge between two distinct indices p and q exactly when |nums[p] - nums[q]| <= limit. Whenever the function returns a result r, for every connected component C of G and every integer v, the number of indices i in C with r[i] = v equals the number of indices i in C with nums[i] = v.
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 0 <= limit <= 1000000000. -/
  theorem spec_4 (nums : Slice Std.I64) (limit : Std.I64) (hpre : Pre nums limit) :
      ∀ r, Aegis.LexicographicallySmallestArray.lexicographically_smallest_array nums limit
            = ok r →
        ∀ (v : ℤ) (i : Fin (sval nums).length),
          compCount (sval nums) limit.val i (vval r) v
            = compCount (sval nums) limit.val i (sval nums) v := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (limit : Std.I64) (hpre : Pre nums limit), ∀ r, Aegis.LexicographicallySmallestArray.lexicographically_smallest_array nums limit
              = ok r →
          ∀ (v : ℤ) (i : Fin (sval nums).length),
            compCount (sval nums) limit.val i (vval r) v
              = compCount (sval nums) limit.val i (sval nums) v) := by
    sorry

  /-- Let G be the graph whose vertices are the indices 0, ..., len(nums)-1, with an edge between two distinct indices p and q exactly when |nums[p] - nums[q]| <= limit. Whenever the function returns a result r, for every i and j with 0 <= i < j < len(nums), if i and j are in the same connected component of G, then r[i] <= r[j].
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 0 <= limit <= 1000000000. -/
  theorem spec_5 (nums : Slice Std.I64) (limit : Std.I64) (hpre : Pre nums limit) :
      ∀ r, Aegis.LexicographicallySmallestArray.lexicographically_smallest_array nums limit
            = ok r →
        ∀ (i j : ℕ) (hi : i < (sval nums).length) (hj : j < (sval nums).length), i < j →
          SameComp (sval nums) limit.val ⟨i, hi⟩ ⟨j, hj⟩ →
            entry (vval r) i ≤ entry (vval r) j := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (limit : Std.I64) (hpre : Pre nums limit), ∀ r, Aegis.LexicographicallySmallestArray.lexicographically_smallest_array nums limit
              = ok r →
          ∀ (i j : ℕ) (hi : i < (sval nums).length) (hj : j < (sval nums).length), i < j →
            SameComp (sval nums) limit.val ⟨i, hi⟩ ⟨j, hj⟩ →
              entry (vval r) i ≤ entry (vval r) j) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(nums), min_{0 <= t < len(nums)} nums[t] <= r[i] <= max_{0 <= t < len(nums)} nums[t]. In particular, 1 <= r[i] <= 1000000000.
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 0 <= limit <= 1000000000. -/
  theorem spec_6 (nums : Slice Std.I64) (limit : Std.I64) (hpre : Pre nums limit) :
      ∀ r, Aegis.LexicographicallySmallestArray.lexicographically_smallest_array nums limit
            = ok r →
        ∀ (i : ℕ) (hi : i < (sval nums).length),
          (∀ m : ℤ, IsMinOf (sval nums) m → m ≤ entry (vval r) i) ∧
            (∀ M : ℤ, IsMaxOf (sval nums) M → entry (vval r) i ≤ M) ∧
            1 ≤ entry (vval r) i ∧ entry (vval r) i ≤ 1000000000 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (limit : Std.I64) (hpre : Pre nums limit), ∀ r, Aegis.LexicographicallySmallestArray.lexicographically_smallest_array nums limit
              = ok r →
          ∀ (i : ℕ) (hi : i < (sval nums).length),
            (∀ m : ℤ, IsMinOf (sval nums) m → m ≤ entry (vval r) i) ∧
              (∀ M : ℤ, IsMaxOf (sval nums) M → entry (vval r) i ≤ M) ∧
              1 ≤ entry (vval r) i ∧ entry (vval r) i ≤ 1000000000) := by
    sorry

  /-- Whenever the function returns a result r, r[i] = nums[i] for every i with 0 <= i < len(nums).
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; limit = 0. -/
  theorem spec_7 (nums : Slice Std.I64) (limit : Std.I64) (hpre : Pre nums limit)
      (hlim : limit.val = 0) :
      ∀ r, Aegis.LexicographicallySmallestArray.lexicographically_smallest_array nums limit
            = ok r →
        ∀ (i : ℕ) (hi : i < (sval nums).length), entry (vval r) i = entry (sval nums) i := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (limit : Std.I64) (hpre : Pre nums limit)
        (hlim : limit.val = 0), ∀ r, Aegis.LexicographicallySmallestArray.lexicographically_smallest_array nums limit
              = ok r →
          ∀ (i : ℕ) (hi : i < (sval nums).length), entry (vval r) i = entry (sval nums) i) := by
    sorry

  /-- Whenever the function returns a result r, r is a nondecreasing permutation of nums: for every i and j with 0 <= i < j < len(nums), r[i] <= r[j], and for every integer v, the number of indices i with r[i] = v equals the number of indices i with nums[i] = v.
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 0 <= limit <= 1000000000; max_{0 <= t < len(nums)} nums[t] - min_{0 <= t < len(nums)} nums[t] <= limit. -/
  theorem spec_8 (nums : Slice Std.I64) (limit : Std.I64) (hpre : Pre nums limit)
      (hrange : ∀ M m : ℤ, IsMaxOf (sval nums) M → IsMinOf (sval nums) m →
        M - m ≤ limit.val) :
      ∀ r, Aegis.LexicographicallySmallestArray.lexicographically_smallest_array nums limit
            = ok r →
        (∀ (i j : ℕ) (hi : i < (sval nums).length) (hj : j < (sval nums).length), i < j →
            entry (vval r) i ≤ entry (vval r) j) ∧
          ∀ v : ℤ, countVal (vval r) v = countVal (sval nums) v := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (limit : Std.I64) (hpre : Pre nums limit)
        (hrange : ∀ M m : ℤ, IsMaxOf (sval nums) M → IsMinOf (sval nums) m →
          M - m ≤ limit.val), ∀ r, Aegis.LexicographicallySmallestArray.lexicographically_smallest_array nums limit
              = ok r →
          (∀ (i j : ℕ) (hi : i < (sval nums).length) (hj : j < (sval nums).length), i < j →
              entry (vval r) i ≤ entry (vval r) j) ∧
            ∀ v : ℤ, countVal (vval r) v = countVal (sval nums) v) := by
    sorry

  /-- Let G be the graph whose vertices are the indices 0, ..., len(nums)-1, with an edge between two distinct indices p and q exactly when |nums[p] - nums[q]| <= limit. Whenever the function returns a result r, for every connected component C of G, if p is the smallest index in C, then r[p] = min_{i in C} nums[i].
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 0 <= limit <= 1000000000. -/
  theorem spec_9 (nums : Slice Std.I64) (limit : Std.I64) (hpre : Pre nums limit) :
      ∀ r, Aegis.LexicographicallySmallestArray.lexicographically_smallest_array nums limit
            = ok r →
        ∀ (i p : Fin (sval nums).length) (m : ℤ),
          IsSmallestInComp (sval nums) limit.val i p →
            IsCompMin (sval nums) limit.val i m → entry (vval r) p.val = m := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64) (limit : Std.I64) (hpre : Pre nums limit), ∀ r, Aegis.LexicographicallySmallestArray.lexicographically_smallest_array nums limit
              = ok r →
          ∀ (i p : Fin (sval nums).length) (m : ℤ),
            IsSmallestInComp (sval nums) limit.val i p →
              IsCompMin (sval nums) limit.val i m → entry (vval r) p.val = m) := by
    sorry

  /-- Let G be the graph whose vertices are the indices 0, ..., len(nums)-1, with an edge between two distinct indices p and q exactly when |nums[p] - nums[q]| <= limit. Whenever the function returns a result r, for every connected component C of G, if q is the largest index in C, then r[q] = max_{i in C} nums[i].
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 0 <= limit <= 1000000000. -/
  theorem spec_10 (nums : Slice Std.I64) (limit : Std.I64) (hpre : Pre nums limit) :
      ∀ r, Aegis.LexicographicallySmallestArray.lexicographically_smallest_array nums limit
            = ok r →
        ∀ (i q : Fin (sval nums).length) (M : ℤ),
          IsLargestInComp (sval nums) limit.val i q →
            IsCompMax (sval nums) limit.val i M → entry (vval r) q.val = M := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64) (limit : Std.I64) (hpre : Pre nums limit), ∀ r, Aegis.LexicographicallySmallestArray.lexicographically_smallest_array nums limit
              = ok r →
          ∀ (i q : Fin (sval nums).length) (M : ℤ),
            IsLargestInComp (sval nums) limit.val i q →
              IsCompMax (sval nums) limit.val i M → entry (vval r) q.val = M) := by
    sorry

  /-- Whenever the function returns a result r, for every integer v, the number of indices i with 0 <= i < len(nums) and r[i] = v equals the number of indices i with 0 <= i < len(nums) and nums[i] = v.
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 0 <= limit <= 1000000000. -/
  theorem spec_11 (nums : Slice Std.I64) (limit : Std.I64) (hpre : Pre nums limit) :
      ∀ r, Aegis.LexicographicallySmallestArray.lexicographically_smallest_array nums limit
            = ok r →
        ∀ v : ℤ, countVal (vval r) v = countVal (sval nums) v := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64) (limit : Std.I64) (hpre : Pre nums limit), ∀ r, Aegis.LexicographicallySmallestArray.lexicographically_smallest_array nums limit
              = ok r →
          ∀ v : ℤ, countVal (vval r) v = countVal (sval nums) v) := by
    sorry

  /-- Whenever the function returns a result r, for every index k with 0 <= k < len(nums) such that for all j with 0 <= j < len(nums) and j != k we have |nums[k] - nums[j]| > limit, it holds that r[k] = nums[k].
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 0 <= limit <= 1000000000. -/
  theorem spec_12 (nums : Slice Std.I64) (limit : Std.I64) (hpre : Pre nums limit) :
      ∀ r, Aegis.LexicographicallySmallestArray.lexicographically_smallest_array nums limit
            = ok r →
        ∀ (k : ℕ) (hk : k < (sval nums).length),
          (∀ (j : ℕ) (hj : j < (sval nums).length), j ≠ k →
              limit.val < |entry (sval nums) k - entry (sval nums) j|) →
            entry (vval r) k = entry (sval nums) k := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice Std.I64) (limit : Std.I64) (hpre : Pre nums limit), ∀ r, Aegis.LexicographicallySmallestArray.lexicographically_smallest_array nums limit
              = ok r →
          ∀ (k : ℕ) (hk : k < (sval nums).length),
            (∀ (j : ℕ) (hj : j < (sval nums).length), j ≠ k →
                limit.val < |entry (sval nums) k - entry (sval nums) j|) →
              entry (vval r) k = entry (sval nums) k) := by
    sorry

  end

  end AegisSpec.LexicographicallySmallestArray
