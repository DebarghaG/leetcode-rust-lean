import Aegis.PickGifts.Code.Funs

/-!
# Specifications of `Aegis.PickGifts.pick_gifts`

LeetCode problem `take-gifts-from-the-richest-pile`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.PickGifts

def giftsInts (gifts : Slice Std.I64) : List ℤ := gifts.val.map (fun x => x.val)

def giftsMultiset (gifts : Slice Std.I64) : Multiset ℤ := giftsInts gifts

def floorSqrt (x : ℤ) : ℤ := ((x.toNat).sqrt : ℕ)

def iterFloorSqrt : ℕ → ℤ → ℤ
  | 0, x => x
  | t + 1, x => floorSqrt (iterFloorSqrt t x)

def IsMaxOf (M : ℤ) (l : List ℤ) : Prop := M ∈ l ∧ ∀ x ∈ l, x ≤ M

def ProcessStep (S S' : Multiset ℤ) : Prop :=
  ∃ x ∈ S, (∀ y ∈ S, y ≤ x) ∧ S' = (S.erase x) + {floorSqrt x}

def ProcessRun (S : Multiset ℤ) (k : ℕ) (S' : Multiset ℤ) : Prop :=
  ∃ Ss : ℕ → Multiset ℤ,
    Ss 0 = S ∧ (∀ t, t < k → ProcessStep (Ss t) (Ss (t + 1))) ∧ Ss k = S'

/-- The function returns a result r, and r equals the total number of gifts after k seconds of the following process. Start with the multiset S_0 consisting of the entries gifts[0],...,gifts[len(gifts)-1]. For each t from 0 to k-1, form S_{t+1} by choosing an occurrence x of the maximum element of S_t, deleting that occurrence, and inserting floor_sqrt(x). If several occurrences tie for the maximum, any choice gives the same multiset. Then r is the sum of the elements of S_k.
  Preconditions: len(gifts) is between 1 and 10^3 inclusive; for every i with 0 <= i < len(gifts), 1 <= gifts[i] <= 10^9; 1 <= k <= 10^3. Here floor_sqrt(x) denotes the greatest integer s with s >= 0 and s*s <= x. -/
theorem spec_1 (gifts : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ (giftsInts gifts).length ∧ (giftsInts gifts).length ≤ 1000)
    (hentries : ∀ i, i < (giftsInts gifts).length →
      1 ≤ (giftsInts gifts)[i]! ∧ (giftsInts gifts)[i]! ≤ 10 ^ 9)
    (hk : 1 ≤ k.val ∧ k.val ≤ 1000) :
    ∃ r : Std.I64,
      Aegis.PickGifts.pick_gifts gifts k = Result.ok r ∧
        ∀ S : ℕ → Multiset ℤ,
          S 0 = giftsMultiset gifts →
            (∀ t, t < k.val.toNat → ProcessStep (S t) (S (t + 1))) →
              r.val = (S k.val.toNat).sum := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (gifts : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ (giftsInts gifts).length ∧ (giftsInts gifts).length ≤ 1000)
    (hentries : ∀ i, i < (giftsInts gifts).length →
      1 ≤ (giftsInts gifts)[i]! ∧ (giftsInts gifts)[i]! ≤ 10 ^ 9)
    (hk : 1 ≤ k.val ∧ k.val ≤ 1000), ∃ r : Std.I64,
      Aegis.PickGifts.pick_gifts gifts k = Result.ok r ∧
        ∀ S : ℕ → Multiset ℤ,
          S 0 = giftsMultiset gifts →
            (∀ t, t < k.val.toNat → ProcessStep (S t) (S (t + 1))) →
              r.val = (S k.val.toNat).sum) := by
  sorry

/-- For every input satisfying the preconditions, the function returns some result: it does not overflow, go out of bounds, or panic.
  Preconditions: len(gifts) is between 1 and 10^3 inclusive; for every i with 0 <= i < len(gifts), 1 <= gifts[i] <= 10^9; 1 <= k <= 10^3. -/
theorem spec_2 (gifts : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ (giftsInts gifts).length ∧ (giftsInts gifts).length ≤ 1000)
    (hentries : ∀ i, i < (giftsInts gifts).length →
      1 ≤ (giftsInts gifts)[i]! ∧ (giftsInts gifts)[i]! ≤ 10 ^ 9)
    (hk : 1 ≤ k.val ∧ k.val ≤ 1000) :
    ∃ r : Std.I64, Aegis.PickGifts.pick_gifts gifts k = Result.ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (gifts : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ (giftsInts gifts).length ∧ (giftsInts gifts).length ≤ 1000)
    (hentries : ∀ i, i < (giftsInts gifts).length →
      1 ≤ (giftsInts gifts)[i]! ∧ (giftsInts gifts)[i]! ≤ 10 ^ 9)
    (hk : 1 ≤ k.val ∧ k.val ≤ 1000), ∃ r : Std.I64, Aegis.PickGifts.pick_gifts gifts k = Result.ok r) := by
  sorry

/-- The function returns a result r and r <= gifts[0] + ... + gifts[len(gifts)-1].
  Preconditions: len(gifts) is between 1 and 10^3 inclusive; for every i with 0 <= i < len(gifts), 1 <= gifts[i] <= 10^9; 1 <= k <= 10^3. -/
theorem spec_3 (gifts : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ (giftsInts gifts).length ∧ (giftsInts gifts).length ≤ 1000)
    (hentries : ∀ i, i < (giftsInts gifts).length →
      1 ≤ (giftsInts gifts)[i]! ∧ (giftsInts gifts)[i]! ≤ 10 ^ 9)
    (hk : 1 ≤ k.val ∧ k.val ≤ 1000) :
    ∃ r : Std.I64,
      Aegis.PickGifts.pick_gifts gifts k = Result.ok r ∧
        r.val ≤ (giftsInts gifts).sum := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (gifts : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ (giftsInts gifts).length ∧ (giftsInts gifts).length ≤ 1000)
    (hentries : ∀ i, i < (giftsInts gifts).length →
      1 ≤ (giftsInts gifts)[i]! ∧ (giftsInts gifts)[i]! ≤ 10 ^ 9)
    (hk : 1 ≤ k.val ∧ k.val ≤ 1000), ∃ r : Std.I64,
      Aegis.PickGifts.pick_gifts gifts k = Result.ok r ∧
        r.val ≤ (giftsInts gifts).sum) := by
  sorry

/-- The function returns a result r and r >= len(gifts).
  Preconditions: len(gifts) is between 1 and 10^3 inclusive; for every i with 0 <= i < len(gifts), 1 <= gifts[i] <= 10^9; 1 <= k <= 10^3. Here floor_sqrt(x) denotes the greatest integer s with s >= 0 and s*s <= x. -/
theorem spec_4 (gifts : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ (giftsInts gifts).length ∧ (giftsInts gifts).length ≤ 1000)
    (hentries : ∀ i, i < (giftsInts gifts).length →
      1 ≤ (giftsInts gifts)[i]! ∧ (giftsInts gifts)[i]! ≤ 10 ^ 9)
    (hk : 1 ≤ k.val ∧ k.val ≤ 1000) :
    ∃ r : Std.I64,
      Aegis.PickGifts.pick_gifts gifts k = Result.ok r ∧
        ((giftsInts gifts).length : ℤ) ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (gifts : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ (giftsInts gifts).length ∧ (giftsInts gifts).length ≤ 1000)
    (hentries : ∀ i, i < (giftsInts gifts).length →
      1 ≤ (giftsInts gifts)[i]! ∧ (giftsInts gifts)[i]! ≤ 10 ^ 9)
    (hk : 1 ≤ k.val ∧ k.val ≤ 1000), ∃ r : Std.I64,
      Aegis.PickGifts.pick_gifts gifts k = Result.ok r ∧
        ((giftsInts gifts).length : ℤ) ≤ r.val) := by
  sorry

/-- If k = 1, the function returns a result r and r = (sum of all entries of gifts) - M + floor_sqrt(M), where M is the maximum entry of gifts.
  Preconditions: len(gifts) is between 1 and 10^3 inclusive; for every i with 0 <= i < len(gifts), 1 <= gifts[i] <= 10^9; 1 <= k <= 10^3. Here floor_sqrt(x) denotes the greatest integer s with s >= 0 and s*s <= x. -/
theorem spec_5 (gifts : Slice Std.I64) (k : Std.I64) (M : ℤ)
    (hlen : 1 ≤ (giftsInts gifts).length ∧ (giftsInts gifts).length ≤ 1000)
    (hentries : ∀ i, i < (giftsInts gifts).length →
      1 ≤ (giftsInts gifts)[i]! ∧ (giftsInts gifts)[i]! ≤ 10 ^ 9)
    (hk : 1 ≤ k.val ∧ k.val ≤ 1000)
    (hk1 : k.val = 1)
    (hM : IsMaxOf M (giftsInts gifts)) :
    ∃ r : Std.I64,
      Aegis.PickGifts.pick_gifts gifts k = Result.ok r ∧
        r.val = (giftsInts gifts).sum - M + floorSqrt M := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (gifts : Slice Std.I64) (k : Std.I64) (M : ℤ)
    (hlen : 1 ≤ (giftsInts gifts).length ∧ (giftsInts gifts).length ≤ 1000)
    (hentries : ∀ i, i < (giftsInts gifts).length →
      1 ≤ (giftsInts gifts)[i]! ∧ (giftsInts gifts)[i]! ≤ 10 ^ 9)
    (hk : 1 ≤ k.val ∧ k.val ≤ 1000)
    (hk1 : k.val = 1)
    (hM : IsMaxOf M (giftsInts gifts)), ∃ r : Std.I64,
      Aegis.PickGifts.pick_gifts gifts k = Result.ok r ∧
        r.val = (giftsInts gifts).sum - M + floorSqrt M) := by
  sorry

/-- If every entry of gifts is 1, then the function returns a result r and r = len(gifts).
  Preconditions: len(gifts) is between 1 and 10^3 inclusive; for every i with 0 <= i < len(gifts), 1 <= gifts[i] <= 10^9; 1 <= k <= 10^3. -/
theorem spec_6 (gifts : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ (giftsInts gifts).length ∧ (giftsInts gifts).length ≤ 1000)
    (hentries : ∀ i, i < (giftsInts gifts).length →
      1 ≤ (giftsInts gifts)[i]! ∧ (giftsInts gifts)[i]! ≤ 10 ^ 9)
    (hk : 1 ≤ k.val ∧ k.val ≤ 1000)
    (hone : ∀ x ∈ giftsInts gifts, x = 1) :
    ∃ r : Std.I64,
      Aegis.PickGifts.pick_gifts gifts k = Result.ok r ∧
        r.val = ((giftsInts gifts).length : ℤ) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (gifts : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ (giftsInts gifts).length ∧ (giftsInts gifts).length ≤ 1000)
    (hentries : ∀ i, i < (giftsInts gifts).length →
      1 ≤ (giftsInts gifts)[i]! ∧ (giftsInts gifts)[i]! ≤ 10 ^ 9)
    (hk : 1 ≤ k.val ∧ k.val ≤ 1000)
    (hone : ∀ x ∈ giftsInts gifts, x = 1), ∃ r : Std.I64,
      Aegis.PickGifts.pick_gifts gifts k = Result.ok r ∧
        r.val = ((giftsInts gifts).length : ℤ)) := by
  sorry

/-- If k >= 5*len(gifts), then the function returns a result r and r = len(gifts).
  Preconditions: len(gifts) is between 1 and 10^3 inclusive; for every i with 0 <= i < len(gifts), 1 <= gifts[i] <= 10^9; 1 <= k <= 10^3. Here floor_sqrt(x) denotes the greatest integer s with s >= 0 and s*s <= x. -/
theorem spec_7 (gifts : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ (giftsInts gifts).length ∧ (giftsInts gifts).length ≤ 1000)
    (hentries : ∀ i, i < (giftsInts gifts).length →
      1 ≤ (giftsInts gifts)[i]! ∧ (giftsInts gifts)[i]! ≤ 10 ^ 9)
    (hk : 1 ≤ k.val ∧ k.val ≤ 1000)
    (hbig : 5 * ((giftsInts gifts).length : ℤ) ≤ k.val) :
    ∃ r : Std.I64,
      Aegis.PickGifts.pick_gifts gifts k = Result.ok r ∧
        r.val = ((giftsInts gifts).length : ℤ) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (gifts : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ (giftsInts gifts).length ∧ (giftsInts gifts).length ≤ 1000)
    (hentries : ∀ i, i < (giftsInts gifts).length →
      1 ≤ (giftsInts gifts)[i]! ∧ (giftsInts gifts)[i]! ≤ 10 ^ 9)
    (hk : 1 ≤ k.val ∧ k.val ≤ 1000)
    (hbig : 5 * ((giftsInts gifts).length : ℤ) ≤ k.val), ∃ r : Std.I64,
      Aegis.PickGifts.pick_gifts gifts k = Result.ok r ∧
        r.val = ((giftsInts gifts).length : ℤ)) := by
  sorry

/-- For every slice gifts' of the same length that is a permutation of gifts, meaning the two slices have the same multiset of entries, the calls pick_gifts(gifts,k) and pick_gifts(gifts',k) both return results r and r', and r = r'.
  Preconditions: len(gifts) is between 1 and 10^3 inclusive; for every i with 0 <= i < len(gifts), 1 <= gifts[i] <= 10^9; 1 <= k <= 10^3. -/
theorem spec_8 (gifts gifts' : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ (giftsInts gifts).length ∧ (giftsInts gifts).length ≤ 1000)
    (hentries : ∀ i, i < (giftsInts gifts).length →
      1 ≤ (giftsInts gifts)[i]! ∧ (giftsInts gifts)[i]! ≤ 10 ^ 9)
    (hk : 1 ≤ k.val ∧ k.val ≤ 1000)
    (hlen' : (giftsInts gifts').length = (giftsInts gifts).length)
    (hperm : giftsMultiset gifts' = giftsMultiset gifts) :
    ∃ r r' : Std.I64,
      Aegis.PickGifts.pick_gifts gifts k = Result.ok r ∧
        Aegis.PickGifts.pick_gifts gifts' k = Result.ok r' ∧ r.val = r'.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (gifts gifts' : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ (giftsInts gifts).length ∧ (giftsInts gifts).length ≤ 1000)
    (hentries : ∀ i, i < (giftsInts gifts).length →
      1 ≤ (giftsInts gifts)[i]! ∧ (giftsInts gifts)[i]! ≤ 10 ^ 9)
    (hk : 1 ≤ k.val ∧ k.val ≤ 1000)
    (hlen' : (giftsInts gifts').length = (giftsInts gifts).length)
    (hperm : giftsMultiset gifts' = giftsMultiset gifts), ∃ r r' : Std.I64,
      Aegis.PickGifts.pick_gifts gifts k = Result.ok r ∧
        Aegis.PickGifts.pick_gifts gifts' k = Result.ok r' ∧ r.val = r'.val) := by
  sorry

/-- For every k1 and k2 with 1 <= k1 <= k2 <= 10^3, the calls pick_gifts(gifts,k1) and pick_gifts(gifts,k2) both return results r1 and r2, and r1 >= r2.
  Preconditions: len(gifts) is between 1 and 10^3 inclusive; for every i with 0 <= i < len(gifts), 1 <= gifts[i] <= 10^9. -/
theorem spec_9 (gifts : Slice Std.I64) (k1 k2 : Std.I64)
    (hlen : 1 ≤ (giftsInts gifts).length ∧ (giftsInts gifts).length ≤ 1000)
    (hentries : ∀ i, i < (giftsInts gifts).length →
      1 ≤ (giftsInts gifts)[i]! ∧ (giftsInts gifts)[i]! ≤ 10 ^ 9)
    (hk1 : 1 ≤ k1.val)
    (hk12 : k1.val ≤ k2.val)
    (hk2 : k2.val ≤ 1000) :
    ∃ r1 r2 : Std.I64,
      Aegis.PickGifts.pick_gifts gifts k1 = Result.ok r1 ∧
        Aegis.PickGifts.pick_gifts gifts k2 = Result.ok r2 ∧ r2.val ≤ r1.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (gifts : Slice Std.I64) (k1 k2 : Std.I64)
    (hlen : 1 ≤ (giftsInts gifts).length ∧ (giftsInts gifts).length ≤ 1000)
    (hentries : ∀ i, i < (giftsInts gifts).length →
      1 ≤ (giftsInts gifts)[i]! ∧ (giftsInts gifts)[i]! ≤ 10 ^ 9)
    (hk1 : 1 ≤ k1.val)
    (hk12 : k1.val ≤ k2.val)
    (hk2 : k2.val ≤ 1000), ∃ r1 r2 : Std.I64,
      Aegis.PickGifts.pick_gifts gifts k1 = Result.ok r1 ∧
        Aegis.PickGifts.pick_gifts gifts k2 = Result.ok r2 ∧ r2.val ≤ r1.val) := by
  sorry

/-- If M = max(gifts) > 1, then the function returns a result r and r < gifts[0] + ... + gifts[len(gifts)-1].
  Preconditions: len(gifts) is between 1 and 10^3 inclusive; for every i with 0 <= i < len(gifts), 1 <= gifts[i] <= 10^9; 1 <= k <= 10^3. Here floor_sqrt(x) denotes the greatest integer s with s >= 0 and s*s <= x. -/
theorem spec_10 (gifts : Slice Std.I64) (k : Std.I64) (M : ℤ)
    (hlen : 1 ≤ (giftsInts gifts).length ∧ (giftsInts gifts).length ≤ 1000)
    (hentries : ∀ i, i < (giftsInts gifts).length →
      1 ≤ (giftsInts gifts)[i]! ∧ (giftsInts gifts)[i]! ≤ 10 ^ 9)
    (hk : 1 ≤ k.val ∧ k.val ≤ 1000)
    (hM : IsMaxOf M (giftsInts gifts))
    (hM1 : 1 < M) :
    ∃ r : Std.I64,
      Aegis.PickGifts.pick_gifts gifts k = Result.ok r ∧
        r.val < (giftsInts gifts).sum := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (gifts : Slice Std.I64) (k : Std.I64) (M : ℤ)
    (hlen : 1 ≤ (giftsInts gifts).length ∧ (giftsInts gifts).length ≤ 1000)
    (hentries : ∀ i, i < (giftsInts gifts).length →
      1 ≤ (giftsInts gifts)[i]! ∧ (giftsInts gifts)[i]! ≤ 10 ^ 9)
    (hk : 1 ≤ k.val ∧ k.val ≤ 1000)
    (hM : IsMaxOf M (giftsInts gifts))
    (hM1 : 1 < M), ∃ r : Std.I64,
      Aegis.PickGifts.pick_gifts gifts k = Result.ok r ∧
        r.val < (giftsInts gifts).sum) := by
  sorry

/-- If len(gifts) = 1, let x_0 = gifts[0] and x_{t+1} = floor_sqrt(x_t) for t >= 0. The function returns r = x_k.
  Preconditions: len(gifts) = 1; 1 <= gifts[0] <= 10^9; 1 <= k <= 10^3. Here floor_sqrt(x) denotes the greatest integer s with s >= 0 and s*s <= x. -/
theorem spec_11 (gifts : Slice Std.I64) (k : Std.I64)
    (hlen : (giftsInts gifts).length = 1)
    (hentry : 1 ≤ (giftsInts gifts)[0]! ∧ (giftsInts gifts)[0]! ≤ 10 ^ 9)
    (hk : 1 ≤ k.val ∧ k.val ≤ 1000) :
    ∃ r : Std.I64,
      Aegis.PickGifts.pick_gifts gifts k = Result.ok r ∧
        r.val = iterFloorSqrt k.val.toNat (giftsInts gifts)[0]! := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (gifts : Slice Std.I64) (k : Std.I64)
    (hlen : (giftsInts gifts).length = 1)
    (hentry : 1 ≤ (giftsInts gifts)[0]! ∧ (giftsInts gifts)[0]! ≤ 10 ^ 9)
    (hk : 1 ≤ k.val ∧ k.val ≤ 1000), ∃ r : Std.I64,
      Aegis.PickGifts.pick_gifts gifts k = Result.ok r ∧
        r.val = iterFloorSqrt k.val.toNat (giftsInts gifts)[0]!) := by
  sorry

/-- The function returns a result r, and there exist non-negative integers c_0,...,c_{len(gifts)-1} such that c_0 + ... + c_{len(gifts)-1} = k and r = sum_{i=0}^{len(gifts)-1} F(c_i, gifts[i]).
  Preconditions: len(gifts) is between 1 and 10^3 inclusive; for every i with 0 <= i < len(gifts), 1 <= gifts[i] <= 10^9; 1 <= k <= 10^3. Here floor_sqrt(x) denotes the greatest integer s with s >= 0 and s*s <= x, and F(0,x)=x, F(t+1,x)=floor_sqrt(F(t,x)). -/
theorem spec_12 (gifts : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ (giftsInts gifts).length ∧ (giftsInts gifts).length ≤ 1000)
    (hentries : ∀ i, i < (giftsInts gifts).length →
      1 ≤ (giftsInts gifts)[i]! ∧ (giftsInts gifts)[i]! ≤ 10 ^ 9)
    (hk : 1 ≤ k.val ∧ k.val ≤ 1000) :
    ∃ r : Std.I64,
      Aegis.PickGifts.pick_gifts gifts k = Result.ok r ∧
        ∃ c : List ℕ,
          c.length = (giftsInts gifts).length ∧
            c.sum = k.val.toNat ∧
              r.val = (c.zipWith (fun ci xi => iterFloorSqrt ci xi) (giftsInts gifts)).sum := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (gifts : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ (giftsInts gifts).length ∧ (giftsInts gifts).length ≤ 1000)
    (hentries : ∀ i, i < (giftsInts gifts).length →
      1 ≤ (giftsInts gifts)[i]! ∧ (giftsInts gifts)[i]! ≤ 10 ^ 9)
    (hk : 1 ≤ k.val ∧ k.val ≤ 1000), ∃ r : Std.I64,
      Aegis.PickGifts.pick_gifts gifts k = Result.ok r ∧
        ∃ c : List ℕ,
          c.length = (giftsInts gifts).length ∧
            c.sum = k.val.toNat ∧
              r.val = (c.zipWith (fun ci xi => iterFloorSqrt ci xi) (giftsInts gifts)).sum) := by
  sorry

/-- Let M be the maximum entry of gifts. For every k satisfying the preconditions, the function returns a result r and r <= (sum of all entries of gifts) - M + floor_sqrt(M).
  Preconditions: len(gifts) is between 1 and 10^3 inclusive; for every i with 0 <= i < len(gifts), 1 <= gifts[i] <= 10^9; 1 <= k <= 10^3. Here floor_sqrt(x) denotes the greatest integer s with s >= 0 and s*s <= x. -/
theorem spec_13 (gifts : Slice Std.I64) (k : Std.I64) (M : ℤ)
    (hlen : 1 ≤ (giftsInts gifts).length ∧ (giftsInts gifts).length ≤ 1000)
    (hentries : ∀ i, i < (giftsInts gifts).length →
      1 ≤ (giftsInts gifts)[i]! ∧ (giftsInts gifts)[i]! ≤ 10 ^ 9)
    (hk : 1 ≤ k.val ∧ k.val ≤ 1000)
    (hM : IsMaxOf M (giftsInts gifts)) :
    ∃ r : Std.I64,
      Aegis.PickGifts.pick_gifts gifts k = Result.ok r ∧
        r.val ≤ (giftsInts gifts).sum - M + floorSqrt M := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (gifts : Slice Std.I64) (k : Std.I64) (M : ℤ)
    (hlen : 1 ≤ (giftsInts gifts).length ∧ (giftsInts gifts).length ≤ 1000)
    (hentries : ∀ i, i < (giftsInts gifts).length →
      1 ≤ (giftsInts gifts)[i]! ∧ (giftsInts gifts)[i]! ≤ 10 ^ 9)
    (hk : 1 ≤ k.val ∧ k.val ≤ 1000)
    (hM : IsMaxOf M (giftsInts gifts)), ∃ r : Std.I64,
      Aegis.PickGifts.pick_gifts gifts k = Result.ok r ∧
        r.val ≤ (giftsInts gifts).sum - M + floorSqrt M) := by
  sorry

/-- For every k with 1 <= k < 10^3, if pick_gifts(gifts,k) returns r_k and pick_gifts(gifts,k+1) returns r_{k+1}, then r_k > len(gifts) implies r_{k+1} < r_k.
  Preconditions: len(gifts) is between 1 and 10^3 inclusive; for every i with 0 <= i < len(gifts), 1 <= gifts[i] <= 10^9; 1 <= k < 10^3. -/
theorem spec_14 (gifts : Slice Std.I64) (k1 k2 : Std.I64)
    (hlen : 1 ≤ (giftsInts gifts).length ∧ (giftsInts gifts).length ≤ 1000)
    (hentries : ∀ i, i < (giftsInts gifts).length →
      1 ≤ (giftsInts gifts)[i]! ∧ (giftsInts gifts)[i]! ≤ 10 ^ 9)
    (hk1 : 1 ≤ k1.val ∧ k1.val < 1000)
    (hkstep : k2.val = k1.val + 1) :
    ∀ r1 r2 : Std.I64,
      Aegis.PickGifts.pick_gifts gifts k1 = Result.ok r1 →
        Aegis.PickGifts.pick_gifts gifts k2 = Result.ok r2 →
          ((giftsInts gifts).length : ℤ) < r1.val → r2.val < r1.val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (gifts : Slice Std.I64) (k1 k2 : Std.I64)
    (hlen : 1 ≤ (giftsInts gifts).length ∧ (giftsInts gifts).length ≤ 1000)
    (hentries : ∀ i, i < (giftsInts gifts).length →
      1 ≤ (giftsInts gifts)[i]! ∧ (giftsInts gifts)[i]! ≤ 10 ^ 9)
    (hk1 : 1 ≤ k1.val ∧ k1.val < 1000)
    (hkstep : k2.val = k1.val + 1), ∀ r1 r2 : Std.I64,
      Aegis.PickGifts.pick_gifts gifts k1 = Result.ok r1 →
        Aegis.PickGifts.pick_gifts gifts k2 = Result.ok r2 →
          ((giftsInts gifts).length : ℤ) < r1.val → r2.val < r1.val) := by
  sorry

end AegisSpec.PickGifts
