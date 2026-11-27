import Aegis.ShareCandies.Code.Funs

/-!
# Specifications of `Aegis.ShareCandies.share_candies`

LeetCode problem `number-of-unique-flavors-after-sharing-k-candies`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.ShareCandies

  namespace AegisSpec.ShareCandies

  def vals (candies : Slice Std.I64) : List ℤ :=
    candies.val.map (fun x => x.val)

  def distinctCount (candies : Slice Std.I64) : ℕ :=
    (vals candies).toFinset.card

  def keptCount (candies : Slice Std.I64) (s k : ℤ) : ℕ :=
    (((Finset.univ : Finset (Fin candies.val.length)).filter
        (fun i => (i.val : ℤ) < s ∨ s + k ≤ (i.val : ℤ))).image
      (fun i => (candies.val.get i).val)).card

  def bestKept (candies : Slice Std.I64) (k : ℤ) : ℕ :=
    ((((List.range (candies.val.length + 1)).map (fun i => (i : ℤ))).toFinset).filter
        (fun s => s ≤ (candies.val.length : ℤ) - k)).sup (fun s => keptCount candies s k)

  def revSlice (candies : Slice Std.I64) : Slice Std.I64 :=
    Slice.from candies.val.reverse (by
      rw [List.length_reverse]
      exact Slice.length_ineq candies)

  def i64Succ (k : Std.I64) : Std.I64 :=
    ⟨k.bv + (1 : BitVec 64)⟩

  /-- The function returns a result r and r = max { C(s) | s is an integer with 0 <= s <= len(candies) - k }, where for each such s, C(s) is the number of distinct integers v for which there exists an i with 0 <= i < len(candies), candies[i] = v, and (i < s or i >= s + k).
    Preconditions: len(candies) <= 100000, 0 <= k <= len(candies), and for every i with 0 <= i < len(candies), 1 <= candies[i] <= 100000. -/
  theorem spec_1 (candies : Slice Std.I64) (k : Std.I64)
      (hlen : candies.val.length ≤ 100000)
      (hk0 : 0 ≤ k.val)
      (hkn : k.val ≤ (candies.val.length : ℤ))
      (hrange : ∀ (i : ℕ) (hi : i < candies.val.length),
        1 ≤ (candies.val.get ⟨i, hi⟩).val ∧ (candies.val.get ⟨i, hi⟩).val ≤ 100000) :
      ∃ r, share_candies candies k = ok r ∧ r.val = (bestKept candies k.val : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (candies : Slice Std.I64) (k : Std.I64)
        (hlen : candies.val.length ≤ 100000)
        (hk0 : 0 ≤ k.val)
        (hkn : k.val ≤ (candies.val.length : ℤ))
        (hrange : ∀ (i : ℕ) (hi : i < candies.val.length),
          1 ≤ (candies.val.get ⟨i, hi⟩).val ∧ (candies.val.get ⟨i, hi⟩).val ≤ 100000), ∃ r, share_candies candies k = ok r ∧ r.val = (bestKept candies k.val : ℤ)) := by
    sorry

  /-- The function returns a result r for every such candies and k; it does not overflow, access out of bounds, or panic.
    Preconditions: len(candies) <= 100000, 0 <= k <= len(candies), and for every i with 0 <= i < len(candies), 1 <= candies[i] <= 100000. -/
  theorem spec_2 (candies : Slice Std.I64) (k : Std.I64)
      (hlen : candies.val.length ≤ 100000)
      (hk0 : 0 ≤ k.val)
      (hkn : k.val ≤ (candies.val.length : ℤ))
      (hrange : ∀ (i : ℕ) (hi : i < candies.val.length),
        1 ≤ (candies.val.get ⟨i, hi⟩).val ∧ (candies.val.get ⟨i, hi⟩).val ≤ 100000) :
      ∃ r, share_candies candies k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (candies : Slice Std.I64) (k : Std.I64)
        (hlen : candies.val.length ≤ 100000)
        (hk0 : 0 ≤ k.val)
        (hkn : k.val ≤ (candies.val.length : ℤ))
        (hrange : ∀ (i : ℕ) (hi : i < candies.val.length),
          1 ≤ (candies.val.get ⟨i, hi⟩).val ∧ (candies.val.get ⟨i, hi⟩).val ≤ 100000), ∃ r, share_candies candies k = ok r) := by
    sorry

  /-- Whenever the function returns a result r, r <= len(candies) - k.
    Preconditions: len(candies) <= 100000, 0 <= k <= len(candies), and for every i with 0 <= i < len(candies), 1 <= candies[i] <= 100000. -/
  theorem spec_3 (candies : Slice Std.I64) (k : Std.I64)
      (hlen : candies.val.length ≤ 100000)
      (hk0 : 0 ≤ k.val)
      (hkn : k.val ≤ (candies.val.length : ℤ))
      (hrange : ∀ (i : ℕ) (hi : i < candies.val.length),
        1 ≤ (candies.val.get ⟨i, hi⟩).val ∧ (candies.val.get ⟨i, hi⟩).val ≤ 100000) :
      ∀ r, share_candies candies k = ok r →
        r.val ≤ (candies.val.length : ℤ) - k.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (candies : Slice Std.I64) (k : Std.I64)
        (hlen : candies.val.length ≤ 100000)
        (hk0 : 0 ≤ k.val)
        (hkn : k.val ≤ (candies.val.length : ℤ))
        (hrange : ∀ (i : ℕ) (hi : i < candies.val.length),
          1 ≤ (candies.val.get ⟨i, hi⟩).val ∧ (candies.val.get ⟨i, hi⟩).val ≤ 100000), ∀ r, share_candies candies k = ok r →
          r.val ≤ (candies.val.length : ℤ) - k.val) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r.
    Preconditions: len(candies) <= 100000, 0 <= k <= len(candies), and for every i with 0 <= i < len(candies), 1 <= candies[i] <= 100000. -/
  theorem spec_4 (candies : Slice Std.I64) (k : Std.I64)
      (hlen : candies.val.length ≤ 100000)
      (hk0 : 0 ≤ k.val)
      (hkn : k.val ≤ (candies.val.length : ℤ))
      (hrange : ∀ (i : ℕ) (hi : i < candies.val.length),
        1 ≤ (candies.val.get ⟨i, hi⟩).val ∧ (candies.val.get ⟨i, hi⟩).val ≤ 100000) :
      ∀ r, share_candies candies k = ok r → 0 ≤ r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (candies : Slice Std.I64) (k : Std.I64)
        (hlen : candies.val.length ≤ 100000)
        (hk0 : 0 ≤ k.val)
        (hkn : k.val ≤ (candies.val.length : ℤ))
        (hrange : ∀ (i : ℕ) (hi : i < candies.val.length),
          1 ≤ (candies.val.get ⟨i, hi⟩).val ∧ (candies.val.get ⟨i, hi⟩).val ≤ 100000), ∀ r, share_candies candies k = ok r → 0 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, 1 <= r.
    Preconditions: len(candies) <= 100000, 0 <= k < len(candies), and for every i with 0 <= i < len(candies), 1 <= candies[i] <= 100000. -/
  theorem spec_5 (candies : Slice Std.I64) (k : Std.I64)
      (hlen : candies.val.length ≤ 100000)
      (hk0 : 0 ≤ k.val)
      (hkn : k.val < (candies.val.length : ℤ))
      (hrange : ∀ (i : ℕ) (hi : i < candies.val.length),
        1 ≤ (candies.val.get ⟨i, hi⟩).val ∧ (candies.val.get ⟨i, hi⟩).val ≤ 100000) :
      ∀ r, share_candies candies k = ok r → 1 ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (candies : Slice Std.I64) (k : Std.I64)
        (hlen : candies.val.length ≤ 100000)
        (hk0 : 0 ≤ k.val)
        (hkn : k.val < (candies.val.length : ℤ))
        (hrange : ∀ (i : ℕ) (hi : i < candies.val.length),
          1 ≤ (candies.val.get ⟨i, hi⟩).val ∧ (candies.val.get ⟨i, hi⟩).val ≤ 100000), ∀ r, share_candies candies k = ok r → 1 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r <= U, where U is the number of distinct integers occurring among candies[0], ..., candies[len(candies)-1], with U = 0 when len(candies) = 0.
    Preconditions: len(candies) <= 100000, 0 <= k <= len(candies), and for every i with 0 <= i < len(candies), 1 <= candies[i] <= 100000. -/
  theorem spec_6 (candies : Slice Std.I64) (k : Std.I64)
      (hlen : candies.val.length ≤ 100000)
      (hk0 : 0 ≤ k.val)
      (hkn : k.val ≤ (candies.val.length : ℤ))
      (hrange : ∀ (i : ℕ) (hi : i < candies.val.length),
        1 ≤ (candies.val.get ⟨i, hi⟩).val ∧ (candies.val.get ⟨i, hi⟩).val ≤ 100000) :
      ∀ r, share_candies candies k = ok r → r.val ≤ (distinctCount candies : ℤ) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (candies : Slice Std.I64) (k : Std.I64)
        (hlen : candies.val.length ≤ 100000)
        (hk0 : 0 ≤ k.val)
        (hkn : k.val ≤ (candies.val.length : ℤ))
        (hrange : ∀ (i : ℕ) (hi : i < candies.val.length),
          1 ≤ (candies.val.get ⟨i, hi⟩).val ∧ (candies.val.get ⟨i, hi⟩).val ≤ 100000), ∀ r, share_candies candies k = ok r → r.val ≤ (distinctCount candies : ℤ)) := by
    sorry

  /-- The function returns a result r and r = U, where U is the number of distinct integers occurring among candies[0], ..., candies[len(candies)-1], with U = 0 when len(candies) = 0.
    Preconditions: len(candies) <= 100000, k = 0, and for every i with 0 <= i < len(candies), 1 <= candies[i] <= 100000. -/
  theorem spec_7 (candies : Slice Std.I64) (k : Std.I64)
      (hlen : candies.val.length ≤ 100000)
      (hk : k.val = 0)
      (hrange : ∀ (i : ℕ) (hi : i < candies.val.length),
        1 ≤ (candies.val.get ⟨i, hi⟩).val ∧ (candies.val.get ⟨i, hi⟩).val ≤ 100000) :
      ∃ r, share_candies candies k = ok r ∧ r.val = (distinctCount candies : ℤ) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (candies : Slice Std.I64) (k : Std.I64)
        (hlen : candies.val.length ≤ 100000)
        (hk : k.val = 0)
        (hrange : ∀ (i : ℕ) (hi : i < candies.val.length),
          1 ≤ (candies.val.get ⟨i, hi⟩).val ∧ (candies.val.get ⟨i, hi⟩).val ≤ 100000), ∃ r, share_candies candies k = ok r ∧ r.val = (distinctCount candies : ℤ)) := by
    sorry

  /-- The function returns a result r and r = 0.
    Preconditions: len(candies) <= 100000, len(candies) > 0, k = len(candies), and for every i with 0 <= i < len(candies), 1 <= candies[i] <= 100000. -/
  theorem spec_8 (candies : Slice Std.I64) (k : Std.I64)
      (hlen : candies.val.length ≤ 100000)
      (hn0 : 0 < candies.val.length)
      (hk : k.val = (candies.val.length : ℤ))
      (hrange : ∀ (i : ℕ) (hi : i < candies.val.length),
        1 ≤ (candies.val.get ⟨i, hi⟩).val ∧ (candies.val.get ⟨i, hi⟩).val ≤ 100000) :
      ∃ r, share_candies candies k = ok r ∧ r.val = 0 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (candies : Slice Std.I64) (k : Std.I64)
        (hlen : candies.val.length ≤ 100000)
        (hn0 : 0 < candies.val.length)
        (hk : k.val = (candies.val.length : ℤ))
        (hrange : ∀ (i : ℕ) (hi : i < candies.val.length),
          1 ≤ (candies.val.get ⟨i, hi⟩).val ∧ (candies.val.get ⟨i, hi⟩).val ≤ 100000), ∃ r, share_candies candies k = ok r ∧ r.val = 0) := by
    sorry

  /-- The function returns a result r and r = 1.
    Preconditions: len(candies) <= 100000, len(candies) > 0, k = len(candies) - 1, and for every i with 0 <= i < len(candies), 1 <= candies[i] <= 100000. -/
  theorem spec_9 (candies : Slice Std.I64) (k : Std.I64)
      (hlen : candies.val.length ≤ 100000)
      (hn0 : 0 < candies.val.length)
      (hk : k.val = (candies.val.length : ℤ) - 1)
      (hrange : ∀ (i : ℕ) (hi : i < candies.val.length),
        1 ≤ (candies.val.get ⟨i, hi⟩).val ∧ (candies.val.get ⟨i, hi⟩).val ≤ 100000) :
      ∃ r, share_candies candies k = ok r ∧ r.val = 1 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (candies : Slice Std.I64) (k : Std.I64)
        (hlen : candies.val.length ≤ 100000)
        (hn0 : 0 < candies.val.length)
        (hk : k.val = (candies.val.length : ℤ) - 1)
        (hrange : ∀ (i : ℕ) (hi : i < candies.val.length),
          1 ≤ (candies.val.get ⟨i, hi⟩).val ∧ (candies.val.get ⟨i, hi⟩).val ≤ 100000), ∃ r, share_candies candies k = ok r ∧ r.val = 1) := by
    sorry

  /-- The function returns a result r and: r = 0 if k = len(candies), and r = 1 if k < len(candies).
    Preconditions: len(candies) <= 100000, len(candies) > 0, 0 <= k <= len(candies), for every i with 0 <= i < len(candies), 1 <= candies[i] <= 100000, and there exists an integer c such that for every i with 0 <= i < len(candies), candies[i] = c. -/
  theorem spec_10 (candies : Slice Std.I64) (k : Std.I64)
      (hlen : candies.val.length ≤ 100000)
      (hn0 : 0 < candies.val.length)
      (hk0 : 0 ≤ k.val)
      (hkn : k.val ≤ (candies.val.length : ℤ))
      (hrange : ∀ (i : ℕ) (hi : i < candies.val.length),
        1 ≤ (candies.val.get ⟨i, hi⟩).val ∧ (candies.val.get ⟨i, hi⟩).val ≤ 100000)
      (hconst : ∃ c : ℤ, ∀ (i : ℕ) (hi : i < candies.val.length),
        (candies.val.get ⟨i, hi⟩).val = c) :
      ∃ r, share_candies candies k = ok r ∧
        (k.val = (candies.val.length : ℤ) → r.val = 0) ∧
        (k.val < (candies.val.length : ℤ) → r.val = 1) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (candies : Slice Std.I64) (k : Std.I64)
        (hlen : candies.val.length ≤ 100000)
        (hn0 : 0 < candies.val.length)
        (hk0 : 0 ≤ k.val)
        (hkn : k.val ≤ (candies.val.length : ℤ))
        (hrange : ∀ (i : ℕ) (hi : i < candies.val.length),
          1 ≤ (candies.val.get ⟨i, hi⟩).val ∧ (candies.val.get ⟨i, hi⟩).val ≤ 100000)
        (hconst : ∃ c : ℤ, ∀ (i : ℕ) (hi : i < candies.val.length),
          (candies.val.get ⟨i, hi⟩).val = c), ∃ r, share_candies candies k = ok r ∧
          (k.val = (candies.val.length : ℤ) → r.val = 0) ∧
          (k.val < (candies.val.length : ℤ) → r.val = 1)) := by
    sorry

  /-- Whenever the function returns a result r, there exists an integer s with 0 <= s <= len(candies) - k such that C(s) = r, where C(s) is the number of distinct integers v for which there is an i with 0 <= i < len(candies), candies[i] = v, and (i < s or i >= s + k).
    Preconditions: len(candies) <= 100000, 0 <= k <= len(candies), and for every i with 0 <= i < len(candies), 1 <= candies[i] <= 100000. -/
  theorem spec_11 (candies : Slice Std.I64) (k : Std.I64)
      (hlen : candies.val.length ≤ 100000)
      (hk0 : 0 ≤ k.val)
      (hkn : k.val ≤ (candies.val.length : ℤ))
      (hrange : ∀ (i : ℕ) (hi : i < candies.val.length),
        1 ≤ (candies.val.get ⟨i, hi⟩).val ∧ (candies.val.get ⟨i, hi⟩).val ≤ 100000) :
      ∀ r, share_candies candies k = ok r →
        ∃ s : ℤ, 0 ≤ s ∧ s ≤ (candies.val.length : ℤ) - k.val ∧
          (keptCount candies s k.val : ℤ) = r.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (candies : Slice Std.I64) (k : Std.I64)
        (hlen : candies.val.length ≤ 100000)
        (hk0 : 0 ≤ k.val)
        (hkn : k.val ≤ (candies.val.length : ℤ))
        (hrange : ∀ (i : ℕ) (hi : i < candies.val.length),
          1 ≤ (candies.val.get ⟨i, hi⟩).val ∧ (candies.val.get ⟨i, hi⟩).val ≤ 100000), ∀ r, share_candies candies k = ok r →
          ∃ s : ℤ, 0 ≤ s ∧ s ≤ (candies.val.length : ℤ) - k.val ∧
            (keptCount candies s k.val : ℤ) = r.val) := by
    sorry

  /-- Whenever the function returns a result r, for every integer s with 0 <= s <= len(candies) - k, C(s) <= r, where C(s) is the number of distinct integers v for which there is an i with 0 <= i < len(candies), candies[i] = v, and (i < s or i >= s + k).
    Preconditions: len(candies) <= 100000, 0 <= k <= len(candies), and for every i with 0 <= i < len(candies), 1 <= candies[i] <= 100000. -/
  theorem spec_12 (candies : Slice Std.I64) (k : Std.I64)
      (hlen : candies.val.length ≤ 100000)
      (hk0 : 0 ≤ k.val)
      (hkn : k.val ≤ (candies.val.length : ℤ))
      (hrange : ∀ (i : ℕ) (hi : i < candies.val.length),
        1 ≤ (candies.val.get ⟨i, hi⟩).val ∧ (candies.val.get ⟨i, hi⟩).val ≤ 100000) :
      ∀ r, share_candies candies k = ok r →
        ∀ s : ℤ, 0 ≤ s → s ≤ (candies.val.length : ℤ) - k.val →
          (keptCount candies s k.val : ℤ) ≤ r.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (candies : Slice Std.I64) (k : Std.I64)
        (hlen : candies.val.length ≤ 100000)
        (hk0 : 0 ≤ k.val)
        (hkn : k.val ≤ (candies.val.length : ℤ))
        (hrange : ∀ (i : ℕ) (hi : i < candies.val.length),
          1 ≤ (candies.val.get ⟨i, hi⟩).val ∧ (candies.val.get ⟨i, hi⟩).val ≤ 100000), ∀ r, share_candies candies k = ok r →
          ∀ s : ℤ, 0 ≤ s → s ≤ (candies.val.length : ℤ) - k.val →
            (keptCount candies s k.val : ℤ) ≤ r.val) := by
    sorry

  /-- Let rev be the array of length len(candies) with rev[i] = candies[len(candies) - 1 - i] for 0 <= i < len(candies). Whenever share_candies(candies, k) returns r and share_candies(rev, k) returns r_rev, we have r = r_rev.
    Preconditions: len(candies) <= 100000, 0 <= k <= len(candies), and for every i with 0 <= i < len(candies), 1 <= candies[i] <= 100000. -/
  theorem spec_13 (candies : Slice Std.I64) (k : Std.I64)
      (hlen : candies.val.length ≤ 100000)
      (hk0 : 0 ≤ k.val)
      (hkn : k.val ≤ (candies.val.length : ℤ))
      (hrange : ∀ (i : ℕ) (hi : i < candies.val.length),
        1 ≤ (candies.val.get ⟨i, hi⟩).val ∧ (candies.val.get ⟨i, hi⟩).val ≤ 100000) :
      ∀ r r_rev, share_candies candies k = ok r →
        share_candies (revSlice candies) k = ok r_rev → r.val = r_rev.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (candies : Slice Std.I64) (k : Std.I64)
        (hlen : candies.val.length ≤ 100000)
        (hk0 : 0 ≤ k.val)
        (hkn : k.val ≤ (candies.val.length : ℤ))
        (hrange : ∀ (i : ℕ) (hi : i < candies.val.length),
          1 ≤ (candies.val.get ⟨i, hi⟩).val ∧ (candies.val.get ⟨i, hi⟩).val ≤ 100000), ∀ r r_rev, share_candies candies k = ok r →
          share_candies (revSlice candies) k = ok r_rev → r.val = r_rev.val) := by
    sorry

  /-- Whenever share_candies(candies, k) returns r and share_candies(candies, k + 1) returns r_next, we have r >= r_next.
    Preconditions: len(candies) <= 100000, 0 <= k, k + 1 <= len(candies), and for every i with 0 <= i < len(candies), 1 <= candies[i] <= 100000. -/
  theorem spec_14 (candies : Slice Std.I64) (k : Std.I64)
      (hlen : candies.val.length ≤ 100000)
      (hk0 : 0 ≤ k.val)
      (hk1 : k.val + 1 ≤ (candies.val.length : ℤ))
      (hrange : ∀ (i : ℕ) (hi : i < candies.val.length),
        1 ≤ (candies.val.get ⟨i, hi⟩).val ∧ (candies.val.get ⟨i, hi⟩).val ≤ 100000) :
      ∀ r r_next, share_candies candies k = ok r →
        share_candies candies (i64Succ k) = ok r_next → r_next.val ≤ r.val := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (candies : Slice Std.I64) (k : Std.I64)
        (hlen : candies.val.length ≤ 100000)
        (hk0 : 0 ≤ k.val)
        (hk1 : k.val + 1 ≤ (candies.val.length : ℤ))
        (hrange : ∀ (i : ℕ) (hi : i < candies.val.length),
          1 ≤ (candies.val.get ⟨i, hi⟩).val ∧ (candies.val.get ⟨i, hi⟩).val ≤ 100000), ∀ r r_next, share_candies candies k = ok r →
          share_candies candies (i64Succ k) = ok r_next → r_next.val ≤ r.val) := by
    sorry

  /-- For every array d with len(d) = len(candies), 1 <= d[i] <= 100000 for all i with 0 <= i < len(d), and such that for all i and j with 0 <= i < len(candies) and 0 <= j < len(candies), candies[i] = candies[j] if and only if d[i] = d[j], whenever share_candies(candies, k) returns r and share_candies(d, k) returns r_d, we have r = r_d.
    Preconditions: len(candies) <= 100000, 0 <= k <= len(candies), and for every i with 0 <= i < len(candies), 1 <= candies[i] <= 100000. -/
  theorem spec_15 (candies : Slice Std.I64) (k : Std.I64)
      (hlen : candies.val.length ≤ 100000)
      (hk0 : 0 ≤ k.val)
      (hkn : k.val ≤ (candies.val.length : ℤ))
      (hrange : ∀ (i : ℕ) (hi : i < candies.val.length),
        1 ≤ (candies.val.get ⟨i, hi⟩).val ∧ (candies.val.get ⟨i, hi⟩).val ≤ 100000)
      (d : Slice Std.I64)
      (hdlen : d.val.length = candies.val.length)
      (hdrange : ∀ (i : ℕ) (hi : i < d.val.length),
        1 ≤ (d.val.get ⟨i, hi⟩).val ∧ (d.val.get ⟨i, hi⟩).val ≤ 100000)
      (hpat : ∀ (i j : ℕ) (hi : i < candies.val.length) (hj : j < candies.val.length),
        ((candies.val.get ⟨i, hi⟩).val = (candies.val.get ⟨j, hj⟩).val ↔
          (d.val.get ⟨i, hdlen.symm ▸ hi⟩).val = (d.val.get ⟨j, hdlen.symm ▸ hj⟩).val)) :
      ∀ r r_d, share_candies candies k = ok r →
        share_candies d k = ok r_d → r.val = r_d.val := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (candies : Slice Std.I64) (k : Std.I64)
        (hlen : candies.val.length ≤ 100000)
        (hk0 : 0 ≤ k.val)
        (hkn : k.val ≤ (candies.val.length : ℤ))
        (hrange : ∀ (i : ℕ) (hi : i < candies.val.length),
          1 ≤ (candies.val.get ⟨i, hi⟩).val ∧ (candies.val.get ⟨i, hi⟩).val ≤ 100000)
        (d : Slice Std.I64)
        (hdlen : d.val.length = candies.val.length)
        (hdrange : ∀ (i : ℕ) (hi : i < d.val.length),
          1 ≤ (d.val.get ⟨i, hi⟩).val ∧ (d.val.get ⟨i, hi⟩).val ≤ 100000)
        (hpat : ∀ (i j : ℕ) (hi : i < candies.val.length) (hj : j < candies.val.length),
          ((candies.val.get ⟨i, hi⟩).val = (candies.val.get ⟨j, hj⟩).val ↔
            (d.val.get ⟨i, hdlen.symm ▸ hi⟩).val = (d.val.get ⟨j, hdlen.symm ▸ hj⟩).val)), ∀ r r_d, share_candies candies k = ok r →
          share_candies d k = ok r_d → r.val = r_d.val) := by
    sorry

  /-- Whenever the function returns a result r, r >= max(0, U - k), where U is the number of distinct integers occurring among candies[0], ..., candies[len(candies)-1], with U = 0 when len(candies) = 0.
    Preconditions: len(candies) <= 100000, 0 <= k <= len(candies), and for every i with 0 <= i < len(candies), 1 <= candies[i] <= 100000. -/
  theorem spec_16 (candies : Slice Std.I64) (k : Std.I64)
      (hlen : candies.val.length ≤ 100000)
      (hk0 : 0 ≤ k.val)
      (hkn : k.val ≤ (candies.val.length : ℤ))
      (hrange : ∀ (i : ℕ) (hi : i < candies.val.length),
        1 ≤ (candies.val.get ⟨i, hi⟩).val ∧ (candies.val.get ⟨i, hi⟩).val ≤ 100000) :
      ∀ r, share_candies candies k = ok r →
        max 0 ((distinctCount candies : ℤ) - k.val) ≤ r.val := by
    sorry

  theorem spec_16_neg :
      ¬ (∀ (candies : Slice Std.I64) (k : Std.I64)
        (hlen : candies.val.length ≤ 100000)
        (hk0 : 0 ≤ k.val)
        (hkn : k.val ≤ (candies.val.length : ℤ))
        (hrange : ∀ (i : ℕ) (hi : i < candies.val.length),
          1 ≤ (candies.val.get ⟨i, hi⟩).val ∧ (candies.val.get ⟨i, hi⟩).val ≤ 100000), ∀ r, share_candies candies k = ok r →
          max 0 ((distinctCount candies : ℤ) - k.val) ≤ r.val) := by
    sorry

  /-- The function returns a result r and r = len(candies) - k.
    Preconditions: len(candies) <= 100000, 0 <= k <= len(candies), for every i with 0 <= i < len(candies), 1 <= candies[i] <= 100000, and for all i and j with 0 <= i < len(candies) and 0 <= j < len(candies), if i != j then candies[i] != candies[j]. -/
  theorem spec_17 (candies : Slice Std.I64) (k : Std.I64)
      (hlen : candies.val.length ≤ 100000)
      (hk0 : 0 ≤ k.val)
      (hkn : k.val ≤ (candies.val.length : ℤ))
      (hrange : ∀ (i : ℕ) (hi : i < candies.val.length),
        1 ≤ (candies.val.get ⟨i, hi⟩).val ∧ (candies.val.get ⟨i, hi⟩).val ≤ 100000)
      (hdistinct : ∀ (i j : ℕ) (hi : i < candies.val.length) (hj : j < candies.val.length),
        i ≠ j → (candies.val.get ⟨i, hi⟩).val ≠ (candies.val.get ⟨j, hj⟩).val) :
      ∃ r, share_candies candies k = ok r ∧
        r.val = (candies.val.length : ℤ) - k.val := by
    sorry

  theorem spec_17_neg :
      ¬ (∀ (candies : Slice Std.I64) (k : Std.I64)
        (hlen : candies.val.length ≤ 100000)
        (hk0 : 0 ≤ k.val)
        (hkn : k.val ≤ (candies.val.length : ℤ))
        (hrange : ∀ (i : ℕ) (hi : i < candies.val.length),
          1 ≤ (candies.val.get ⟨i, hi⟩).val ∧ (candies.val.get ⟨i, hi⟩).val ≤ 100000)
        (hdistinct : ∀ (i j : ℕ) (hi : i < candies.val.length) (hj : j < candies.val.length),
          i ≠ j → (candies.val.get ⟨i, hi⟩).val ≠ (candies.val.get ⟨j, hj⟩).val), ∃ r, share_candies candies k = ok r ∧
          r.val = (candies.val.length : ℤ) - k.val) := by
    sorry

  end AegisSpec.ShareCandies
