import Aegis.MaxScore.Code.Funs

/-!
# Specifications of `Aegis.MaxScore.max_score`

LeetCode problem `maximum-points-you-can-obtain-from-cards`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxScore

def cards (s : Slice Std.I64) : List ℤ := s.list.toList.map (fun x => x.val)

theorem listN_toList_length {n : ℕ} (l : Aeneas.Data.ListN.ListN I64 n) : l.toList.length = n := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [Aeneas.Data.ListN.ListN.toList, ih]

theorem cards_length (s : Slice Std.I64) : (cards s).length = Slice.length s := by
  have h : (↑s : List Std.I64) = s.list.toList := rfl
  simp [cards, Slice.length, h, listN_toList_length s.list]

def ValidCards (s : Slice Std.I64) : Prop :=
  1 ≤ (cards s).length ∧ (cards s).length ≤ 100000 ∧ ∀ x ∈ cards s, 1 ≤ x ∧ x ≤ 10000

def sumRange (l : List ℤ) (a b : ℕ) : ℤ := ((l.drop a).take (b - a)).sum

def score (l : List ℤ) (n k t : ℕ) : ℤ := sumRange l 0 t + sumRange l (n - k + t) n

def middle (l : List ℤ) (m s : ℕ) : ℤ := sumRange l s (s + m)

def minRange (f : ℕ → ℤ) (k : ℕ) : ℤ :=
  (List.range (k + 1)).foldl (fun acc s => min acc (f s)) (f 0)

def listMin (l : List ℤ) : ℤ := l.foldl min (l.getD 0 0)

/-- The function returns a result r, and r is the maximum obtainable score with exactly k cards taken from the two ends. For each integer t with 0 <= t <= k define score(t) = (sum of cardPoints[i] for 0 <= i < t) + (sum of cardPoints[j] for n-k+t <= j < n), where an empty sum is 0. Then: (a) score(t) <= r for every t with 0 <= t <= k; and (b) there exists t0 with 0 <= t0 <= k such that r = score(t0).
  Preconditions: Let n = len(cardPoints). n is an integer with 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= cardPoints[i] <= 10000; and 1 <= k <= n. -/
theorem spec_1 (cardPoints : Slice Std.I64) (k : Std.I64)
    (hcards : ValidCards cardPoints) (hk_lo : 1 ≤ k.val)
    (hk_hi : k.val ≤ ((cards cardPoints).length : ℤ)) :
    ∃ r : Std.I64, Aegis.MaxScore.max_score cardPoints k = ok r ∧
      (∀ t : ℕ, t ≤ k.val.toNat →
        score (cards cardPoints) (cards cardPoints).length k.val.toNat t ≤ r.val) ∧
      (∃ t₀ : ℕ, t₀ ≤ k.val.toNat ∧
        r.val = score (cards cardPoints) (cards cardPoints).length k.val.toNat t₀) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (cardPoints : Slice Std.I64) (k : Std.I64)
    (hcards : ValidCards cardPoints) (hk_lo : 1 ≤ k.val)
    (hk_hi : k.val ≤ ((cards cardPoints).length : ℤ)), ∃ r : Std.I64, Aegis.MaxScore.max_score cardPoints k = ok r ∧
      (∀ t : ℕ, t ≤ k.val.toNat →
        score (cards cardPoints) (cards cardPoints).length k.val.toNat t ≤ r.val) ∧
      (∃ t₀ : ℕ, t₀ ≤ k.val.toNat ∧
        r.val = score (cards cardPoints) (cards cardPoints).length k.val.toNat t₀)) := by
  sorry

/-- The function returns a result r for every input satisfying the preconditions; it does not fail, overflow, or go out of bounds.
  Preconditions: Let n = len(cardPoints). n is an integer with 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= cardPoints[i] <= 10000; and 1 <= k <= n. -/
theorem spec_2 (cardPoints : Slice Std.I64) (k : Std.I64)
    (hcards : ValidCards cardPoints) (hk_lo : 1 ≤ k.val)
    (hk_hi : k.val ≤ ((cards cardPoints).length : ℤ)) :
    ∃ r : Std.I64, Aegis.MaxScore.max_score cardPoints k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (cardPoints : Slice Std.I64) (k : Std.I64)
    (hcards : ValidCards cardPoints) (hk_lo : 1 ≤ k.val)
    (hk_hi : k.val ≤ ((cards cardPoints).length : ℤ)), ∃ r : Std.I64, Aegis.MaxScore.max_score cardPoints k = ok r) := by
  sorry

/-- Whenever the function returns a result r, r <= (sum of cardPoints[i] for 0 <= i < n).
  Preconditions: Let n = len(cardPoints). n is an integer with 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= cardPoints[i] <= 10000; and 1 <= k <= n. -/
theorem spec_3 (cardPoints : Slice Std.I64) (k : Std.I64)
    (hcards : ValidCards cardPoints) (hk_lo : 1 ≤ k.val)
    (hk_hi : k.val ≤ ((cards cardPoints).length : ℤ)) :
    ∀ r : Std.I64, Aegis.MaxScore.max_score cardPoints k = ok r →
      r.val ≤ (cards cardPoints).sum := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (cardPoints : Slice Std.I64) (k : Std.I64)
    (hcards : ValidCards cardPoints) (hk_lo : 1 ≤ k.val)
    (hk_hi : k.val ≤ ((cards cardPoints).length : ℤ)), ∀ r : Std.I64, Aegis.MaxScore.max_score cardPoints k = ok r →
      r.val ≤ (cards cardPoints).sum) := by
  sorry

/-- Whenever the function returns a result r, r >= (sum of cardPoints[i] for n-k <= i < n).
  Preconditions: Let n = len(cardPoints). n is an integer with 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= cardPoints[i] <= 10000; and 1 <= k <= n. -/
theorem spec_4 (cardPoints : Slice Std.I64) (k : Std.I64)
    (hcards : ValidCards cardPoints) (hk_lo : 1 ≤ k.val)
    (hk_hi : k.val ≤ ((cards cardPoints).length : ℤ)) :
    ∀ r : Std.I64, Aegis.MaxScore.max_score cardPoints k = ok r →
      sumRange (cards cardPoints) ((cards cardPoints).length - k.val.toNat)
        (cards cardPoints).length ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (cardPoints : Slice Std.I64) (k : Std.I64)
    (hcards : ValidCards cardPoints) (hk_lo : 1 ≤ k.val)
    (hk_hi : k.val ≤ ((cards cardPoints).length : ℤ)), ∀ r : Std.I64, Aegis.MaxScore.max_score cardPoints k = ok r →
      sumRange (cards cardPoints) ((cards cardPoints).length - k.val.toNat)
        (cards cardPoints).length ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r >= (sum of cardPoints[i] for 0 <= i < k).
  Preconditions: Let n = len(cardPoints). n is an integer with 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= cardPoints[i] <= 10000; and 1 <= k <= n. -/
theorem spec_5 (cardPoints : Slice Std.I64) (k : Std.I64)
    (hcards : ValidCards cardPoints) (hk_lo : 1 ≤ k.val)
    (hk_hi : k.val ≤ ((cards cardPoints).length : ℤ)) :
    ∀ r : Std.I64, Aegis.MaxScore.max_score cardPoints k = ok r →
      sumRange (cards cardPoints) 0 k.val.toNat ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (cardPoints : Slice Std.I64) (k : Std.I64)
    (hcards : ValidCards cardPoints) (hk_lo : 1 ≤ k.val)
    (hk_hi : k.val ≤ ((cards cardPoints).length : ℤ)), ∀ r : Std.I64, Aegis.MaxScore.max_score cardPoints k = ok r →
      sumRange (cards cardPoints) 0 k.val.toNat ≤ r.val) := by
  sorry

/-- If k = n, then whenever the function returns a result r, r = (sum of cardPoints[i] for 0 <= i < n).
  Preconditions: Let n = len(cardPoints). n is an integer with 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= cardPoints[i] <= 10000; and k = n. -/
theorem spec_6 (cardPoints : Slice Std.I64) (k : Std.I64)
    (hcards : ValidCards cardPoints) (hk : k.val = ((cards cardPoints).length : ℤ)) :
    ∀ r : Std.I64, Aegis.MaxScore.max_score cardPoints k = ok r →
      r.val = (cards cardPoints).sum := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (cardPoints : Slice Std.I64) (k : Std.I64)
    (hcards : ValidCards cardPoints) (hk : k.val = ((cards cardPoints).length : ℤ)), ∀ r : Std.I64, Aegis.MaxScore.max_score cardPoints k = ok r →
      r.val = (cards cardPoints).sum) := by
  sorry

/-- If k = 1, then whenever the function returns a result r, r = max(cardPoints[0], cardPoints[n-1]), where max denotes the larger of the two values.
  Preconditions: Let n = len(cardPoints). n is an integer with 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= cardPoints[i] <= 10000; and k = 1. -/
theorem spec_7 (cardPoints : Slice Std.I64) (k : Std.I64)
    (hcards : ValidCards cardPoints) (hk : k.val = 1) :
    ∀ r : Std.I64, Aegis.MaxScore.max_score cardPoints k = ok r →
      r.val = max ((cards cardPoints).getD 0 0)
        ((cards cardPoints).getD ((cards cardPoints).length - 1) 0) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (cardPoints : Slice Std.I64) (k : Std.I64)
    (hcards : ValidCards cardPoints) (hk : k.val = 1), ∀ r : Std.I64, Aegis.MaxScore.max_score cardPoints k = ok r →
      r.val = max ((cards cardPoints).getD 0 0)
        ((cards cardPoints).getD ((cards cardPoints).length - 1) 0)) := by
  sorry

/-- If n >= 2 and k = n-1, then whenever the function returns a result r, r = (sum of cardPoints[i] for 0 <= i < n) - min(cardPoints[i] for 0 <= i < n), where min denotes the smallest card value.
  Preconditions: Let n = len(cardPoints). n is an integer with 2 <= n <= 100000; for every i with 0 <= i < n, 1 <= cardPoints[i] <= 10000; and k = n-1. -/
theorem spec_8 (cardPoints : Slice Std.I64) (k : Std.I64)
    (hcards : ValidCards cardPoints) (hn : 2 ≤ (cards cardPoints).length)
    (hk : k.val = ((cards cardPoints).length : ℤ) - 1) :
    ∀ r : Std.I64, Aegis.MaxScore.max_score cardPoints k = ok r →
      r.val = (cards cardPoints).sum - listMin (cards cardPoints) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (cardPoints : Slice Std.I64) (k : Std.I64)
    (hcards : ValidCards cardPoints) (hn : 2 ≤ (cards cardPoints).length)
    (hk : k.val = ((cards cardPoints).length : ℤ) - 1), ∀ r : Std.I64, Aegis.MaxScore.max_score cardPoints k = ok r →
      r.val = (cards cardPoints).sum - listMin (cards cardPoints)) := by
  sorry

/-- Let rev be the slice of length n with rev[i] = cardPoints[n-1-i] for every i with 0 <= i < n. Whenever max_score(cardPoints, k) returns r and max_score(rev, k) returns r', we have r = r'.
  Preconditions: Let n = len(cardPoints). n is an integer with 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= cardPoints[i] <= 10000; and 1 <= k <= n. -/
theorem spec_9 (cardPoints rev : Slice Std.I64) (k : Std.I64)
    (hcards : ValidCards cardPoints) (hk_lo : 1 ≤ k.val)
    (hk_hi : k.val ≤ ((cards cardPoints).length : ℤ))
    (hrev : cards rev = (cards cardPoints).reverse) :
    ∀ r r' : Std.I64, Aegis.MaxScore.max_score cardPoints k = ok r →
      Aegis.MaxScore.max_score rev k = ok r' → r.val = r'.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (cardPoints rev : Slice Std.I64) (k : Std.I64)
    (hcards : ValidCards cardPoints) (hk_lo : 1 ≤ k.val)
    (hk_hi : k.val ≤ ((cards cardPoints).length : ℤ))
    (hrev : cards rev = (cards cardPoints).reverse), ∀ r r' : Std.I64, Aegis.MaxScore.max_score cardPoints k = ok r →
      Aegis.MaxScore.max_score rev k = ok r' → r.val = r'.val) := by
  sorry

/-- Let total = (sum of cardPoints[i] for 0 <= i < n) and m = n-k. For each integer s with 0 <= s <= k define middle(s) = (sum of cardPoints[i] for s <= i < s+m), with an empty sum equal to 0. Whenever the function returns a result r, r = total - min(middle(s) for 0 <= s <= k), where min denotes the smallest value among these middle sums.
  Preconditions: Let n = len(cardPoints). n is an integer with 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= cardPoints[i] <= 10000; and 1 <= k <= n. -/
theorem spec_10 (cardPoints : Slice Std.I64) (k : Std.I64)
    (hcards : ValidCards cardPoints) (hk_lo : 1 ≤ k.val)
    (hk_hi : k.val ≤ ((cards cardPoints).length : ℤ)) :
    ∀ r : Std.I64, Aegis.MaxScore.max_score cardPoints k = ok r →
      r.val = (cards cardPoints).sum -
        minRange (fun s => middle (cards cardPoints)
          ((cards cardPoints).length - k.val.toNat) s) k.val.toNat := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (cardPoints : Slice Std.I64) (k : Std.I64)
    (hcards : ValidCards cardPoints) (hk_lo : 1 ≤ k.val)
    (hk_hi : k.val ≤ ((cards cardPoints).length : ℤ)), ∀ r : Std.I64, Aegis.MaxScore.max_score cardPoints k = ok r →
      r.val = (cards cardPoints).sum -
        minRange (fun s => middle (cards cardPoints)
          ((cards cardPoints).length - k.val.toNat) s) k.val.toNat) := by
  sorry

/-- For any k1 with 1 <= k1 < n, whenever max_score(cardPoints, k1) returns r and max_score(cardPoints, k1+1) returns r', we have r <= r'.
  Preconditions: Let n = len(cardPoints). n is an integer with 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= cardPoints[i] <= 10000; and let k1 be an integer with 1 <= k1 < n. -/
theorem spec_11 (cardPoints : Slice Std.I64) (k1 k2 : Std.I64)
    (hcards : ValidCards cardPoints) (hk1_lo : 1 ≤ k1.val)
    (hk1_hi : k1.val < ((cards cardPoints).length : ℤ))
    (hk2 : k2.val = k1.val + 1) :
    ∀ r r' : Std.I64, Aegis.MaxScore.max_score cardPoints k1 = ok r →
      Aegis.MaxScore.max_score cardPoints k2 = ok r' → r.val ≤ r'.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (cardPoints : Slice Std.I64) (k1 k2 : Std.I64)
    (hcards : ValidCards cardPoints) (hk1_lo : 1 ≤ k1.val)
    (hk1_hi : k1.val < ((cards cardPoints).length : ℤ))
    (hk2 : k2.val = k1.val + 1), ∀ r r' : Std.I64, Aegis.MaxScore.max_score cardPoints k1 = ok r →
      Aegis.MaxScore.max_score cardPoints k2 = ok r' → r.val ≤ r'.val) := by
  sorry

/-- Let shifted be the slice of length n with shifted[i] = cardPoints[i] + c for every i with 0 <= i < n. Whenever max_score(cardPoints, k) returns r and max_score(shifted, k) returns r', we have r' = r + k*c.
  Preconditions: Let n = len(cardPoints). n is an integer with 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= cardPoints[i] <= 10000; 1 <= k <= n; and c is an integer with 0 <= c such that 1 <= cardPoints[i]+c <= 10000 for every i with 0 <= i < n. -/
theorem spec_12 (cardPoints shifted : Slice Std.I64) (k : Std.I64) (c : ℤ)
    (hcards : ValidCards cardPoints) (hk_lo : 1 ≤ k.val)
    (hk_hi : k.val ≤ ((cards cardPoints).length : ℤ))
    (hc : 0 ≤ c) (hshift : cards shifted = (cards cardPoints).map (fun x => x + c))
    (hshift_bounds : ∀ x ∈ cards cardPoints, 1 ≤ x + c ∧ x + c ≤ 10000) :
    ∀ r r' : Std.I64, Aegis.MaxScore.max_score cardPoints k = ok r →
      Aegis.MaxScore.max_score shifted k = ok r' → r'.val = r.val + k.val * c := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (cardPoints shifted : Slice Std.I64) (k : Std.I64) (c : ℤ)
    (hcards : ValidCards cardPoints) (hk_lo : 1 ≤ k.val)
    (hk_hi : k.val ≤ ((cards cardPoints).length : ℤ))
    (hc : 0 ≤ c) (hshift : cards shifted = (cards cardPoints).map (fun x => x + c))
    (hshift_bounds : ∀ x ∈ cards cardPoints, 1 ≤ x + c ∧ x + c ≤ 10000), ∀ r r' : Std.I64, Aegis.MaxScore.max_score cardPoints k = ok r →
      Aegis.MaxScore.max_score shifted k = ok r' → r'.val = r.val + k.val * c) := by
  sorry

/-- Let scaled be the slice of length n with scaled[i] = a*cardPoints[i] for every i with 0 <= i < n. Whenever max_score(cardPoints, k) returns r and max_score(scaled, k) returns r', we have r' = a*r.
  Preconditions: Let n = len(cardPoints). n is an integer with 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= cardPoints[i] <= 10000; 1 <= k <= n; and a is an integer with 1 <= a such that 1 <= a*cardPoints[i] <= 10000 for every i with 0 <= i < n. -/
theorem spec_13 (cardPoints scaled : Slice Std.I64) (k : Std.I64) (a : ℤ)
    (hcards : ValidCards cardPoints) (hk_lo : 1 ≤ k.val)
    (hk_hi : k.val ≤ ((cards cardPoints).length : ℤ))
    (ha : 1 ≤ a) (hscaled : cards scaled = (cards cardPoints).map (fun x => a * x))
    (hscaled_bounds : ∀ x ∈ cards cardPoints, 1 ≤ a * x ∧ a * x ≤ 10000) :
    ∀ r r' : Std.I64, Aegis.MaxScore.max_score cardPoints k = ok r →
      Aegis.MaxScore.max_score scaled k = ok r' → r'.val = a * r.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (cardPoints scaled : Slice Std.I64) (k : Std.I64) (a : ℤ)
    (hcards : ValidCards cardPoints) (hk_lo : 1 ≤ k.val)
    (hk_hi : k.val ≤ ((cards cardPoints).length : ℤ))
    (ha : 1 ≤ a) (hscaled : cards scaled = (cards cardPoints).map (fun x => a * x))
    (hscaled_bounds : ∀ x ∈ cards cardPoints, 1 ≤ a * x ∧ a * x ≤ 10000), ∀ r r' : Std.I64, Aegis.MaxScore.max_score cardPoints k = ok r →
      Aegis.MaxScore.max_score scaled k = ok r' → r'.val = a * r.val) := by
  sorry

/-- Whenever max_score(cardPoints, k) returns r and max_score(other, k) returns r', we have r <= r'.
  Preconditions: Let n = len(cardPoints). n is an integer with 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= cardPoints[i] <= 10000; 1 <= k <= n; and let other be a slice of length n with 1 <= other[i] <= 10000 and cardPoints[i] <= other[i] for every i with 0 <= i < n. -/
theorem spec_14 (cardPoints other : Slice Std.I64) (k : Std.I64)
    (hcards : ValidCards cardPoints) (hk_lo : 1 ≤ k.val)
    (hk_hi : k.val ≤ ((cards cardPoints).length : ℤ))
    (hother_len : (cards other).length = (cards cardPoints).length)
    (hother_bounds : ∀ x ∈ cards other, 1 ≤ x ∧ x ≤ 10000)
    (hmono : ∀ i : ℕ, i < (cards cardPoints).length →
      (cards cardPoints).getD i 0 ≤ (cards other).getD i 0) :
    ∀ r r' : Std.I64, Aegis.MaxScore.max_score cardPoints k = ok r →
      Aegis.MaxScore.max_score other k = ok r' → r.val ≤ r'.val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (cardPoints other : Slice Std.I64) (k : Std.I64)
    (hcards : ValidCards cardPoints) (hk_lo : 1 ≤ k.val)
    (hk_hi : k.val ≤ ((cards cardPoints).length : ℤ))
    (hother_len : (cards other).length = (cards cardPoints).length)
    (hother_bounds : ∀ x ∈ cards other, 1 ≤ x ∧ x ≤ 10000)
    (hmono : ∀ i : ℕ, i < (cards cardPoints).length →
      (cards cardPoints).getD i 0 ≤ (cards other).getD i 0), ∀ r r' : Std.I64, Aegis.MaxScore.max_score cardPoints k = ok r →
      Aegis.MaxScore.max_score other k = ok r' → r.val ≤ r'.val) := by
  sorry

end AegisSpec.MaxScore
