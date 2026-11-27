import Aegis.MaximumTastiness.Code.Funs

/-!
# Specifications of `Aegis.MaximumTastiness.maximum_tastiness`

LeetCode problem `maximum-tastiness-of-candy-basket`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.MaximumTastiness (maximum_tastiness)

  namespace AegisSpec.MaximumTastiness

  def vals (price : Slice Std.I64) : List ℤ := price.val.map (fun x => x.val)

  def absDiff (a b : ℤ) : ℤ := (a - b).natAbs

  def pairDistsOn (l : List ℤ) (S : Finset ℕ) : Finset ℤ :=
    ((S.product S).filter (fun p => p.1 < p.2)).image
      (fun p => absDiff (l.getD p.1 0) (l.getD p.2 0))

  noncomputable def tastinessOn (l : List ℤ) (S : Finset ℕ) : ℤ :=
    if h : (pairDistsOn l S).Nonempty then (pairDistsOn l S).min' h else 0

  def kSelections (l : List ℤ) (k : ℕ) : Finset (Finset ℕ) :=
    (Finset.range l.length).powerset.filter (fun S => S.card = k)

  noncomputable def maxTastiness (l : List ℤ) (k : ℕ) : ℤ :=
    if h : (kSelections l k).Nonempty then
      ((kSelections l k).image (tastinessOn l)).max' (Finset.Nonempty.image h _)
    else 0

  def consecutiveGaps (s : List ℤ) (S : Finset ℕ) : Finset ℤ :=
    ((S.product S).filter
        (fun p => p.1 < p.2 ∧ ∀ m ∈ S, ¬ (p.1 < m ∧ m < p.2))).image
      (fun p => s.getD p.2 0 - s.getD p.1 0)

  noncomputable def minConsecutiveGap (s : List ℤ) (S : Finset ℕ) : ℤ :=
    if h : (consecutiveGaps s S).Nonempty then (consecutiveGaps s S).min' h else 0

  noncomputable def maxMinConsecutiveGap (s : List ℤ) (k : ℕ) : ℤ :=
    if h : (kSelections s k).Nonempty then
      ((kSelections s k).image (minConsecutiveGap s)).max' (Finset.Nonempty.image h _)
    else 0

  noncomputable def maxPrice (l : List ℤ) : ℤ :=
    if h : l.toFinset.Nonempty then l.toFinset.max' h else 0

  noncomputable def minPrice (l : List ℤ) : ℤ :=
    if h : l.toFinset.Nonempty then l.toFinset.min' h else 0

  /-- Let n = len(price). For any subset S of {0,1,...,n-1} with |S| = k, define tastiness(S) = min { |price[i] - price[j]| : i, j in S and i != j }. The function returns a result r such that r = max { tastiness(S) : S is a subset of {0,...,n-1} with |S| = k }.
    Preconditions: len(price) >= 2; 2 <= k <= len(price); len(price) <= 100000; for every i with 0 <= i < len(price), 1 <= price[i] <= 1000000000. -/
  theorem spec_1 (price : Slice Std.I64) (k : Std.I64)
      (h_n : 2 ≤ price.length)
      (h_k_lo : 2 ≤ k.val) (h_k_hi : k.val ≤ (price.length : ℤ))
      (h_len : price.length ≤ 100000)
      (h_price : ∀ x ∈ price.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
      ∃ r, maximum_tastiness price k = ok r ∧
        r.val = maxTastiness (vals price) k.val.toNat := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (price : Slice Std.I64) (k : Std.I64)
        (h_n : 2 ≤ price.length)
        (h_k_lo : 2 ≤ k.val) (h_k_hi : k.val ≤ (price.length : ℤ))
        (h_len : price.length ≤ 100000)
        (h_price : ∀ x ∈ price.val, 1 ≤ x.val ∧ x.val ≤ 1000000000), ∃ r, maximum_tastiness price k = ok r ∧
          r.val = maxTastiness (vals price) k.val.toNat) := by
    sorry

  /-- The function returns a result r; it does not fail due to overflow, out-of-bounds access, or panic.
    Preconditions: len(price) >= 2; 2 <= k <= len(price); len(price) <= 100000; for every i with 0 <= i < len(price), 1 <= price[i] <= 1000000000. -/
  theorem spec_2 (price : Slice Std.I64) (k : Std.I64)
      (h_n : 2 ≤ price.length)
      (h_k_lo : 2 ≤ k.val) (h_k_hi : k.val ≤ (price.length : ℤ))
      (h_len : price.length ≤ 100000)
      (h_price : ∀ x ∈ price.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
      ∃ r, maximum_tastiness price k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (price : Slice Std.I64) (k : Std.I64)
        (h_n : 2 ≤ price.length)
        (h_k_lo : 2 ≤ k.val) (h_k_hi : k.val ≤ (price.length : ℤ))
        (h_len : price.length ≤ 100000)
        (h_price : ∀ x ∈ price.val, 1 ≤ x.val ∧ x.val ≤ 1000000000), ∃ r, maximum_tastiness price k = ok r) := by
    sorry

  /-- The function returns a result r and r >= 0.
    Preconditions: len(price) >= 2; 2 <= k <= len(price); len(price) <= 100000; for every i with 0 <= i < len(price), 1 <= price[i] <= 1000000000. -/
  theorem spec_3 (price : Slice Std.I64) (k : Std.I64)
      (h_n : 2 ≤ price.length)
      (h_k_lo : 2 ≤ k.val) (h_k_hi : k.val ≤ (price.length : ℤ))
      (h_len : price.length ≤ 100000)
      (h_price : ∀ x ∈ price.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
      ∃ r, maximum_tastiness price k = ok r ∧ 0 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (price : Slice Std.I64) (k : Std.I64)
        (h_n : 2 ≤ price.length)
        (h_k_lo : 2 ≤ k.val) (h_k_hi : k.val ≤ (price.length : ℤ))
        (h_len : price.length ≤ 100000)
        (h_price : ∀ x ∈ price.val, 1 ≤ x.val ∧ x.val ≤ 1000000000), ∃ r, maximum_tastiness price k = ok r ∧ 0 ≤ r.val) := by
    sorry

  /-- The function returns a result r and r <= max_{0 <= i < len(price)} price[i] - min_{0 <= i < len(price)} price[i].
    Preconditions: len(price) >= 2; 2 <= k <= len(price); len(price) <= 100000; for every i with 0 <= i < len(price), 1 <= price[i] <= 1000000000. -/
  theorem spec_4 (price : Slice Std.I64) (k : Std.I64)
      (h_n : 2 ≤ price.length)
      (h_k_lo : 2 ≤ k.val) (h_k_hi : k.val ≤ (price.length : ℤ))
      (h_len : price.length ≤ 100000)
      (h_price : ∀ x ∈ price.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
      ∃ r, maximum_tastiness price k = ok r ∧
        r.val ≤ maxPrice (vals price) - minPrice (vals price) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (price : Slice Std.I64) (k : Std.I64)
        (h_n : 2 ≤ price.length)
        (h_k_lo : 2 ≤ k.val) (h_k_hi : k.val ≤ (price.length : ℤ))
        (h_len : price.length ≤ 100000)
        (h_price : ∀ x ∈ price.val, 1 ≤ x.val ∧ x.val ≤ 1000000000), ∃ r, maximum_tastiness price k = ok r ∧
          r.val ≤ maxPrice (vals price) - minPrice (vals price)) := by
    sorry

  /-- The function returns a result r and there exists a subset S of {0,1,...,len(price)-1} with |S| = k such that tastiness(S) = r, where tastiness(S) = min { |price[i] - price[j]| : i, j in S and i != j }.
    Preconditions: len(price) >= 2; 2 <= k <= len(price); len(price) <= 100000; for every i with 0 <= i < len(price), 1 <= price[i] <= 1000000000. -/
  theorem spec_5 (price : Slice Std.I64) (k : Std.I64)
      (h_n : 2 ≤ price.length)
      (h_k_lo : 2 ≤ k.val) (h_k_hi : k.val ≤ (price.length : ℤ))
      (h_len : price.length ≤ 100000)
      (h_price : ∀ x ∈ price.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
      ∃ r, maximum_tastiness price k = ok r ∧
        ∃ S : Finset ℕ, S ⊆ Finset.range (vals price).length ∧
          S.card = k.val.toNat ∧ tastinessOn (vals price) S = r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (price : Slice Std.I64) (k : Std.I64)
        (h_n : 2 ≤ price.length)
        (h_k_lo : 2 ≤ k.val) (h_k_hi : k.val ≤ (price.length : ℤ))
        (h_len : price.length ≤ 100000)
        (h_price : ∀ x ∈ price.val, 1 ≤ x.val ∧ x.val ≤ 1000000000), ∃ r, maximum_tastiness price k = ok r ∧
          ∃ S : Finset ℕ, S ⊆ Finset.range (vals price).length ∧
            S.card = k.val.toNat ∧ tastinessOn (vals price) S = r.val) := by
    sorry

  /-- The function returns a result r and for every subset S of {0,1,...,len(price)-1} with |S| = k, tastiness(S) <= r, where tastiness(S) = min { |price[i] - price[j]| : i, j in S and i != j }.
    Preconditions: len(price) >= 2; 2 <= k <= len(price); len(price) <= 100000; for every i with 0 <= i < len(price), 1 <= price[i] <= 1000000000. -/
  theorem spec_6 (price : Slice Std.I64) (k : Std.I64)
      (h_n : 2 ≤ price.length)
      (h_k_lo : 2 ≤ k.val) (h_k_hi : k.val ≤ (price.length : ℤ))
      (h_len : price.length ≤ 100000)
      (h_price : ∀ x ∈ price.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
      ∃ r, maximum_tastiness price k = ok r ∧
        ∀ S : Finset ℕ, S ⊆ Finset.range (vals price).length → S.card = k.val.toNat →
          tastinessOn (vals price) S ≤ r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (price : Slice Std.I64) (k : Std.I64)
        (h_n : 2 ≤ price.length)
        (h_k_lo : 2 ≤ k.val) (h_k_hi : k.val ≤ (price.length : ℤ))
        (h_len : price.length ≤ 100000)
        (h_price : ∀ x ∈ price.val, 1 ≤ x.val ∧ x.val ≤ 1000000000), ∃ r, maximum_tastiness price k = ok r ∧
          ∀ S : Finset ℕ, S ⊆ Finset.range (vals price).length → S.card = k.val.toNat →
            tastinessOn (vals price) S ≤ r.val) := by
    sorry

  /-- The function returns a result r and for every integer d >= 0, r >= d if and only if there exists a subset S of {0,1,...,len(price)-1} with |S| = k such that for all i, j in S with i != j, |price[i] - price[j]| >= d.
    Preconditions: len(price) >= 2; 2 <= k <= len(price); len(price) <= 100000; for every i with 0 <= i < len(price), 1 <= price[i] <= 1000000000. -/
  theorem spec_7 (price : Slice Std.I64) (k : Std.I64)
      (h_n : 2 ≤ price.length)
      (h_k_lo : 2 ≤ k.val) (h_k_hi : k.val ≤ (price.length : ℤ))
      (h_len : price.length ≤ 100000)
      (h_price : ∀ x ∈ price.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
      ∃ r, maximum_tastiness price k = ok r ∧
        ∀ d : ℤ, 0 ≤ d → (d ≤ r.val ↔
          ∃ S : Finset ℕ, S ⊆ Finset.range (vals price).length ∧ S.card = k.val.toNat ∧
            ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
              d ≤ absDiff ((vals price).getD i 0) ((vals price).getD j 0)) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (price : Slice Std.I64) (k : Std.I64)
        (h_n : 2 ≤ price.length)
        (h_k_lo : 2 ≤ k.val) (h_k_hi : k.val ≤ (price.length : ℤ))
        (h_len : price.length ≤ 100000)
        (h_price : ∀ x ∈ price.val, 1 ≤ x.val ∧ x.val ≤ 1000000000), ∃ r, maximum_tastiness price k = ok r ∧
          ∀ d : ℤ, 0 ≤ d → (d ≤ r.val ↔
            ∃ S : Finset ℕ, S ⊆ Finset.range (vals price).length ∧ S.card = k.val.toNat ∧
              ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
                d ≤ absDiff ((vals price).getD i 0) ((vals price).getD j 0))) := by
    sorry

  /-- The function returns a result r and there exist indices i, j with 0 <= i < j < len(price) such that r = |price[i] - price[j]|.
    Preconditions: len(price) >= 2; 2 <= k <= len(price); len(price) <= 100000; for every i with 0 <= i < len(price), 1 <= price[i] <= 1000000000. -/
  theorem spec_8 (price : Slice Std.I64) (k : Std.I64)
      (h_n : 2 ≤ price.length)
      (h_k_lo : 2 ≤ k.val) (h_k_hi : k.val ≤ (price.length : ℤ))
      (h_len : price.length ≤ 100000)
      (h_price : ∀ x ∈ price.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
      ∃ r, maximum_tastiness price k = ok r ∧
        ∃ i j : ℕ, i < j ∧ j < (vals price).length ∧
          r.val = absDiff ((vals price).getD i 0) ((vals price).getD j 0) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (price : Slice Std.I64) (k : Std.I64)
        (h_n : 2 ≤ price.length)
        (h_k_lo : 2 ≤ k.val) (h_k_hi : k.val ≤ (price.length : ℤ))
        (h_len : price.length ≤ 100000)
        (h_price : ∀ x ∈ price.val, 1 ≤ x.val ∧ x.val ≤ 1000000000), ∃ r, maximum_tastiness price k = ok r ∧
          ∃ i j : ℕ, i < j ∧ j < (vals price).length ∧
            r.val = absDiff ((vals price).getD i 0) ((vals price).getD j 0)) := by
    sorry

  /-- The function returns a result r and if k = 2, then r = max_{0 <= i < len(price)} price[i] - min_{0 <= i < len(price)} price[i].
    Preconditions: len(price) >= 2; 2 <= k <= len(price); len(price) <= 100000; for every i with 0 <= i < len(price), 1 <= price[i] <= 1000000000. -/
  theorem spec_9 (price : Slice Std.I64) (k : Std.I64)
      (h_n : 2 ≤ price.length)
      (h_k_lo : 2 ≤ k.val) (h_k_hi : k.val ≤ (price.length : ℤ))
      (h_len : price.length ≤ 100000)
      (h_price : ∀ x ∈ price.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
      ∃ r, maximum_tastiness price k = ok r ∧
        (k.val = 2 → r.val = maxPrice (vals price) - minPrice (vals price)) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (price : Slice Std.I64) (k : Std.I64)
        (h_n : 2 ≤ price.length)
        (h_k_lo : 2 ≤ k.val) (h_k_hi : k.val ≤ (price.length : ℤ))
        (h_len : price.length ≤ 100000)
        (h_price : ∀ x ∈ price.val, 1 ≤ x.val ∧ x.val ≤ 1000000000), ∃ r, maximum_tastiness price k = ok r ∧
          (k.val = 2 → r.val = maxPrice (vals price) - minPrice (vals price))) := by
    sorry

  /-- The function returns a result r and if k = len(price), then r = min { |price[i] - price[j]| : 0 <= i < j < len(price) }.
    Preconditions: len(price) >= 2; 2 <= k <= len(price); len(price) <= 100000; for every i with 0 <= i < len(price), 1 <= price[i] <= 1000000000. -/
  theorem spec_10 (price : Slice Std.I64) (k : Std.I64)
      (h_n : 2 ≤ price.length)
      (h_k_lo : 2 ≤ k.val) (h_k_hi : k.val ≤ (price.length : ℤ))
      (h_len : price.length ≤ 100000)
      (h_price : ∀ x ∈ price.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
      ∃ r, maximum_tastiness price k = ok r ∧
        (k.val = (price.length : ℤ) →
          r.val = tastinessOn (vals price) (Finset.range (vals price).length)) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (price : Slice Std.I64) (k : Std.I64)
        (h_n : 2 ≤ price.length)
        (h_k_lo : 2 ≤ k.val) (h_k_hi : k.val ≤ (price.length : ℤ))
        (h_len : price.length ≤ 100000)
        (h_price : ∀ x ∈ price.val, 1 ≤ x.val ∧ x.val ≤ 1000000000), ∃ r, maximum_tastiness price k = ok r ∧
          (k.val = (price.length : ℤ) →
            r.val = tastinessOn (vals price) (Finset.range (vals price).length))) := by
    sorry

  /-- The function returns a result r and r = 0 if and only if the number of distinct values among price[0], ..., price[len(price)-1] is less than k.
    Preconditions: len(price) >= 2; 2 <= k <= len(price); len(price) <= 100000; for every i with 0 <= i < len(price), 1 <= price[i] <= 1000000000. -/
  theorem spec_11 (price : Slice Std.I64) (k : Std.I64)
      (h_n : 2 ≤ price.length)
      (h_k_lo : 2 ≤ k.val) (h_k_hi : k.val ≤ (price.length : ℤ))
      (h_len : price.length ≤ 100000)
      (h_price : ∀ x ∈ price.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
      ∃ r, maximum_tastiness price k = ok r ∧
        (r.val = 0 ↔ (vals price).dedup.length < k.val.toNat) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (price : Slice Std.I64) (k : Std.I64)
        (h_n : 2 ≤ price.length)
        (h_k_lo : 2 ≤ k.val) (h_k_hi : k.val ≤ (price.length : ℤ))
        (h_len : price.length ≤ 100000)
        (h_price : ∀ x ∈ price.val, 1 ≤ x.val ∧ x.val ≤ 1000000000), ∃ r, maximum_tastiness price k = ok r ∧
          (r.val = 0 ↔ (vals price).dedup.length < k.val.toNat)) := by
    sorry

  /-- Let s be the nondecreasing rearrangement of price, i.e., s[0] <= s[1] <= ... <= s[len(price)-1] and the multiset {s[0], ..., s[len(price)-1]} equals the multiset {price[0], ..., price[len(price)-1]}. The function returns a result r and r = max { min_{t=1}^{k-1} (s[i_{t+1}] - s[i_t]) : 0 <= i_1 < i_2 < ... < i_k < len(price) }.
    Preconditions: len(price) >= 2; 2 <= k <= len(price); len(price) <= 100000; for every i with 0 <= i < len(price), 1 <= price[i] <= 1000000000. -/
  theorem spec_12 (price : Slice Std.I64) (k : Std.I64) (s : List ℤ)
      (h_n : 2 ≤ price.length)
      (h_k_lo : 2 ≤ k.val) (h_k_hi : k.val ≤ (price.length : ℤ))
      (h_len : price.length ≤ 100000)
      (h_price : ∀ x ∈ price.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
      (h_sorted : s.Pairwise (· ≤ ·)) (h_perm : s.Perm (vals price)) :
      ∃ r, maximum_tastiness price k = ok r ∧
        r.val = maxMinConsecutiveGap s k.val.toNat := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (price : Slice Std.I64) (k : Std.I64) (s : List ℤ)
        (h_n : 2 ≤ price.length)
        (h_k_lo : 2 ≤ k.val) (h_k_hi : k.val ≤ (price.length : ℤ))
        (h_len : price.length ≤ 100000)
        (h_price : ∀ x ∈ price.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
        (h_sorted : s.Pairwise (· ≤ ·)) (h_perm : s.Perm (vals price)), ∃ r, maximum_tastiness price k = ok r ∧
          r.val = maxMinConsecutiveGap s k.val.toNat) := by
    sorry

  /-- The function returns a result r. For every permutation pi of the index set {0,1,...,len(price)-1}, let q be the array with q[i] = price[pi(i)] for 0 <= i < len(price). Then the maximum tastiness for q (with the same k) is also r.
    Preconditions: len(price) >= 2; 2 <= k <= len(price); len(price) <= 100000; for every i with 0 <= i < len(price), 1 <= price[i] <= 1000000000. -/
  theorem spec_13 (price : Slice Std.I64) (k : Std.I64)
      (h_n : 2 ≤ price.length)
      (h_k_lo : 2 ≤ k.val) (h_k_hi : k.val ≤ (price.length : ℤ))
      (h_len : price.length ≤ 100000)
      (h_price : ∀ x ∈ price.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
      ∃ r, maximum_tastiness price k = ok r ∧
        ∀ q : Slice Std.I64, (vals q).Perm (vals price) →
          ∃ r', maximum_tastiness q k = ok r' ∧ r'.val = r.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (price : Slice Std.I64) (k : Std.I64)
        (h_n : 2 ≤ price.length)
        (h_k_lo : 2 ≤ k.val) (h_k_hi : k.val ≤ (price.length : ℤ))
        (h_len : price.length ≤ 100000)
        (h_price : ∀ x ∈ price.val, 1 ≤ x.val ∧ x.val ≤ 1000000000), ∃ r, maximum_tastiness price k = ok r ∧
          ∀ q : Slice Std.I64, (vals q).Perm (vals price) →
            ∃ r', maximum_tastiness q k = ok r' ∧ r'.val = r.val) := by
    sorry

  /-- The function returns a result r. For every integer c such that 1 <= price[i] + c <= 1000000000 for all i with 0 <= i < len(price), let q be the array with q[i] = price[i] + c. Then the maximum tastiness for q (with the same k) is also r.
    Preconditions: len(price) >= 2; 2 <= k <= len(price); len(price) <= 100000; for every i with 0 <= i < len(price), 1 <= price[i] <= 1000000000. -/
  theorem spec_14 (price : Slice Std.I64) (k : Std.I64) (c : ℤ)
      (h_n : 2 ≤ price.length)
      (h_k_lo : 2 ≤ k.val) (h_k_hi : k.val ≤ (price.length : ℤ))
      (h_len : price.length ≤ 100000)
      (h_price : ∀ x ∈ price.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
      (h_c : ∀ x ∈ vals price, 1 ≤ x + c ∧ x + c ≤ 1000000000) :
      ∃ r, maximum_tastiness price k = ok r ∧
        ∀ q : Slice Std.I64, vals q = (vals price).map (fun x => x + c) →
          ∃ r', maximum_tastiness q k = ok r' ∧ r'.val = r.val := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (price : Slice Std.I64) (k : Std.I64) (c : ℤ)
        (h_n : 2 ≤ price.length)
        (h_k_lo : 2 ≤ k.val) (h_k_hi : k.val ≤ (price.length : ℤ))
        (h_len : price.length ≤ 100000)
        (h_price : ∀ x ∈ price.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
        (h_c : ∀ x ∈ vals price, 1 ≤ x + c ∧ x + c ≤ 1000000000), ∃ r, maximum_tastiness price k = ok r ∧
          ∀ q : Slice Std.I64, vals q = (vals price).map (fun x => x + c) →
            ∃ r', maximum_tastiness q k = ok r' ∧ r'.val = r.val) := by
    sorry

  /-- Let r1 be the result of the function on input (price, k1) and r2 the result on input (price, k2). Then r1 >= r2.
    Preconditions: len(price) >= 2; 2 <= k1 <= k2 <= len(price); len(price) <= 100000; for every i with 0 <= i < len(price), 1 <= price[i] <= 1000000000. -/
  theorem spec_15 (price : Slice Std.I64) (k1 k2 : Std.I64)
      (h_n : 2 ≤ price.length)
      (h_k1_lo : 2 ≤ k1.val) (h_k12 : k1.val ≤ k2.val) (h_k2_hi : k2.val ≤ (price.length : ℤ))
      (h_len : price.length ≤ 100000)
      (h_price : ∀ x ∈ price.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
      ∃ r1 r2, maximum_tastiness price k1 = ok r1 ∧ maximum_tastiness price k2 = ok r2 ∧
        r2.val ≤ r1.val := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (price : Slice Std.I64) (k1 k2 : Std.I64)
        (h_n : 2 ≤ price.length)
        (h_k1_lo : 2 ≤ k1.val) (h_k12 : k1.val ≤ k2.val) (h_k2_hi : k2.val ≤ (price.length : ℤ))
        (h_len : price.length ≤ 100000)
        (h_price : ∀ x ∈ price.val, 1 ≤ x.val ∧ x.val ≤ 1000000000), ∃ r1 r2, maximum_tastiness price k1 = ok r1 ∧ maximum_tastiness price k2 = ok r2 ∧
          r2.val ≤ r1.val) := by
    sorry

  /-- The function returns a result r and (k - 1) * r <= max_{0 <= i < len(price)} price[i] - min_{0 <= i < len(price)} price[i].
    Preconditions: len(price) >= 2; 2 <= k <= len(price); len(price) <= 100000; for every i with 0 <= i < len(price), 1 <= price[i] <= 1000000000. -/
  theorem spec_16 (price : Slice Std.I64) (k : Std.I64)
      (h_n : 2 ≤ price.length)
      (h_k_lo : 2 ≤ k.val) (h_k_hi : k.val ≤ (price.length : ℤ))
      (h_len : price.length ≤ 100000)
      (h_price : ∀ x ∈ price.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
      ∃ r, maximum_tastiness price k = ok r ∧
        (k.val - 1) * r.val ≤ maxPrice (vals price) - minPrice (vals price) := by
    sorry

  theorem spec_16_neg :
      ¬ (∀ (price : Slice Std.I64) (k : Std.I64)
        (h_n : 2 ≤ price.length)
        (h_k_lo : 2 ≤ k.val) (h_k_hi : k.val ≤ (price.length : ℤ))
        (h_len : price.length ≤ 100000)
        (h_price : ∀ x ∈ price.val, 1 ≤ x.val ∧ x.val ≤ 1000000000), ∃ r, maximum_tastiness price k = ok r ∧
          (k.val - 1) * r.val ≤ maxPrice (vals price) - minPrice (vals price)) := by
    sorry

  end AegisSpec.MaximumTastiness
