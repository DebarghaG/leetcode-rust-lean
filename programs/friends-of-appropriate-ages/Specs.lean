import Aegis.NumFriendRequests.Code.Funs

/-!
# Specifications of `Aegis.NumFriendRequests.num_friend_requests`

LeetCode problem `friends-of-appropriate-ages`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.NumFriendRequests

  open Aegis.NumFriendRequests

  def ageAt (ages : Slice Std.I64) (i : Nat) : Int :=
    match ages.val[i]? with
    | some a => a.val
    | none => 0

  def countVal (ages : Slice Std.I64) (n : Nat) (v : Int) : Nat :=
    ((Finset.range n).filter (fun i => ageAt ages i = v)).card

  abbrev friendRequest (x y : Int) : Prop :=
    y ≤ x ∧ x + 14 < 2 * y

  def orderedRequestCount (ages : Slice Std.I64) (n : Nat) : Nat :=
    ((Finset.range n ×ˢ Finset.range n).filter
      (fun p : Nat × Nat => p.1 ≠ p.2 ∧ friendRequest (ageAt ages p.1) (ageAt ages p.2))).card

  def unorderedRequestCount (ages : Slice Std.I64) (n : Nat) : Nat :=
    ((Finset.range n ×ˢ Finset.range n).filter
      (fun p : Nat × Nat =>
        p.1 < p.2 ∧
          max (ageAt ages p.1) (ageAt ages p.2) + 14 <
            2 * min (ageAt ages p.1) (ageAt ages p.2))).card

  /-- Whenever the function returns a result r on input ages satisfying the preconditions, r is the number of ordered pairs (i,j) of indices such that 0 <= i < n, 0 <= j < n, i != j, ages[j] <= ages[i], and 2*ages[j] > ages[i] + 14. Equivalently, r is the total number of friend requests made, counting a request from person i to person j separately from a request from person j to person i. The problem's third exclusion, ages[j] > 100 and ages[i] < 100, is automatically implied by ages[j] > ages[i], so it does not remove any additional pair.
    Preconditions: n = len(ages), 1 <= n <= 20000, and for every i with 0 <= i < n, 1 <= ages[i] <= 120. All indices are 0-based. -/
  theorem spec_1 (ages : Slice Std.I64) (n : Nat)
      (hlen : ages.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 20000)
      (hbound : ∀ i, i < n → 1 ≤ ageAt ages i ∧ ageAt ages i ≤ 120) :
      ∀ r, num_friend_requests ages = ok r → r.val = (orderedRequestCount ages n : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (ages : Slice Std.I64) (n : Nat)
        (hlen : ages.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 20000)
        (hbound : ∀ i, i < n → 1 ≤ ageAt ages i ∧ ageAt ages i ≤ 120), ∀ r, num_friend_requests ages = ok r → r.val = (orderedRequestCount ages n : Int)) := by
    sorry

  /-- For every input ages satisfying the preconditions, the function returns a result r; it does not fail (no overflow, out-of-bounds access, or panic).
    Preconditions: n = len(ages), 1 <= n <= 20000, and for every i with 0 <= i < n, 1 <= ages[i] <= 120. -/
  theorem spec_2 (ages : Slice Std.I64) (n : Nat)
      (hlen : ages.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 20000)
      (hbound : ∀ i, i < n → 1 ≤ ageAt ages i ∧ ageAt ages i ≤ 120) :
      ∃ r, num_friend_requests ages = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (ages : Slice Std.I64) (n : Nat)
        (hlen : ages.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 20000)
        (hbound : ∀ i, i < n → 1 ≤ ageAt ages i ∧ ageAt ages i ≤ 120), ∃ r, num_friend_requests ages = ok r) := by
    sorry

  /-- Whenever the function returns a result r on input ages satisfying the preconditions, 0 <= r.
    Preconditions: n = len(ages), 1 <= n <= 20000, and for every i with 0 <= i < n, 1 <= ages[i] <= 120. -/
  theorem spec_3 (ages : Slice Std.I64) (n : Nat)
      (hlen : ages.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 20000)
      (hbound : ∀ i, i < n → 1 ≤ ageAt ages i ∧ ageAt ages i ≤ 120) :
      ∀ r, num_friend_requests ages = ok r → 0 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (ages : Slice Std.I64) (n : Nat)
        (hlen : ages.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 20000)
        (hbound : ∀ i, i < n → 1 ≤ ageAt ages i ∧ ageAt ages i ≤ 120), ∀ r, num_friend_requests ages = ok r → 0 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r on input ages satisfying the preconditions, r <= n*(n-1), where n = len(ages).
    Preconditions: n = len(ages), 1 <= n <= 20000, and for every i with 0 <= i < n, 1 <= ages[i] <= 120. -/
  theorem spec_4 (ages : Slice Std.I64) (n : Nat)
      (hlen : ages.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 20000)
      (hbound : ∀ i, i < n → 1 ≤ ageAt ages i ∧ ageAt ages i ≤ 120) :
      ∀ r, num_friend_requests ages = ok r → r.val ≤ (n : Int) * ((n : Int) - 1) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (ages : Slice Std.I64) (n : Nat)
        (hlen : ages.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 20000)
        (hbound : ∀ i, i < n → 1 ≤ ageAt ages i ∧ ageAt ages i ≤ 120), ∀ r, num_friend_requests ages = ok r → r.val ≤ (n : Int) * ((n : Int) - 1)) := by
    sorry

  /-- Whenever the function returns a result r, r = 0.
    Preconditions: len(ages) = 1 and 1 <= ages[0] <= 120. -/
  theorem spec_5 (ages : Slice Std.I64)
      (hlen : ages.val.length = 1) (hlo : 1 ≤ ageAt ages 0) (hhi : ageAt ages 0 ≤ 120) :
      ∀ r, num_friend_requests ages = ok r → r.val = 0 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (ages : Slice Std.I64)
        (hlen : ages.val.length = 1) (hlo : 1 ≤ ageAt ages 0) (hhi : ageAt ages 0 ≤ 120), ∀ r, num_friend_requests ages = ok r → r.val = 0) := by
    sorry

  /-- Whenever the function returns a result r on input ages satisfying the preconditions, r = 0.
    Preconditions: n = len(ages), 1 <= n <= 20000, and for every i with 0 <= i < n, 1 <= ages[i] <= 14. -/
  theorem spec_6 (ages : Slice Std.I64) (n : Nat)
      (hlen : ages.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 20000)
      (hbound : ∀ i, i < n → 1 ≤ ageAt ages i ∧ ageAt ages i ≤ 14) :
      ∀ r, num_friend_requests ages = ok r → r.val = 0 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (ages : Slice Std.I64) (n : Nat)
        (hlen : ages.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 20000)
        (hbound : ∀ i, i < n → 1 ≤ ageAt ages i ∧ ageAt ages i ≤ 14), ∀ r, num_friend_requests ages = ok r → r.val = 0) := by
    sorry

  /-- Whenever the function returns a result r on input ages satisfying the preconditions, r = n*(n-1).
    Preconditions: n = len(ages), 1 <= n <= 20000, and there exists an integer a with 15 <= a <= 120 such that ages[i] = a for every i with 0 <= i < n. -/
  theorem spec_7 (ages : Slice Std.I64) (n : Nat) (a : Int)
      (hlen : ages.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 20000)
      (ha1 : 15 ≤ a) (ha2 : a ≤ 120)
      (hconst : ∀ i, i < n → ageAt ages i = a) :
      ∀ r, num_friend_requests ages = ok r → r.val = (n : Int) * ((n : Int) - 1) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (ages : Slice Std.I64) (n : Nat) (a : Int)
        (hlen : ages.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 20000)
        (ha1 : 15 ≤ a) (ha2 : a ≤ 120)
        (hconst : ∀ i, i < n → ageAt ages i = a), ∀ r, num_friend_requests ages = ok r → r.val = (n : Int) * ((n : Int) - 1)) := by
    sorry

  /-- If the function returns r on ages and r2 on ages2, then r = r2.
    Preconditions: ages and ages2 both satisfy the problem constraints; they have the same length n with 1 <= n <= 20000; there is a bijection pi from {0,...,n-1} to itself such that ages2[i] = ages[pi(i)] for every i with 0 <= i < n. -/
  theorem spec_8 (ages ages2 : Slice Std.I64) (n : Nat) (π : Nat → Nat)
      (hlen : ages.val.length = n) (hlen2 : ages2.val.length = n)
      (hn1 : 1 ≤ n) (hn2 : n ≤ 20000)
      (hbound : ∀ i, i < n → 1 ≤ ageAt ages i ∧ ageAt ages i ≤ 120)
      (hbound2 : ∀ i, i < n → 1 ≤ ageAt ages2 i ∧ ageAt ages2 i ≤ 120)
      (hπmem : ∀ i, i < n → π i < n)
      (hπinj : ∀ i j, i < n → j < n → π i = π j → i = j)
      (hπsurj : ∀ j, j < n → ∃ i, i < n ∧ π i = j)
      (hperm : ∀ i, i < n → ageAt ages2 i = ageAt ages (π i)) :
      ∀ r r2, num_friend_requests ages = ok r → num_friend_requests ages2 = ok r2 →
        r = r2 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (ages ages2 : Slice Std.I64) (n : Nat) (π : Nat → Nat)
        (hlen : ages.val.length = n) (hlen2 : ages2.val.length = n)
        (hn1 : 1 ≤ n) (hn2 : n ≤ 20000)
        (hbound : ∀ i, i < n → 1 ≤ ageAt ages i ∧ ageAt ages i ≤ 120)
        (hbound2 : ∀ i, i < n → 1 ≤ ageAt ages2 i ∧ ageAt ages2 i ≤ 120)
        (hπmem : ∀ i, i < n → π i < n)
        (hπinj : ∀ i j, i < n → j < n → π i = π j → i = j)
        (hπsurj : ∀ j, j < n → ∃ i, i < n ∧ π i = j)
        (hperm : ∀ i, i < n → ageAt ages2 i = ageAt ages (π i)), ∀ r r2, num_friend_requests ages = ok r → num_friend_requests ages2 = ok r2 →
          r = r2) := by
    sorry

  /-- If the function returns r on ages and r2 on ages2, then r2 = r + C, where C is the sum of: (1) the number of indices i with 0 <= i < n such that 2*a > ages[i] + 14 and a <= ages[i], plus (2) the number of indices i with 0 <= i < n such that 2*ages[i] > a + 14 and ages[i] <= a. These two counts are added separately, so if both hold for the same i, both directed requests are counted.
    Preconditions: ages satisfies n = len(ages) with 1 <= n <= 19999 and 1 <= ages[i] <= 120 for all i; a is an integer with 1 <= a <= 120; ages2 has length n+1, agrees with ages on indices 0 <= i < n, and has ages2[n] = a. -/
  theorem spec_9 (ages ages2 : Slice Std.I64) (n : Nat) (a : Int)
      (hlen : ages.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 19999)
      (hbound : ∀ i, i < n → 1 ≤ ageAt ages i ∧ ageAt ages i ≤ 120)
      (ha1 : 1 ≤ a) (ha2 : a ≤ 120)
      (hlen2 : ages2.val.length = n + 1)
      (hagree : ∀ i, i < n → ageAt ages2 i = ageAt ages i)
      (hlast : ageAt ages2 n = a) :
      ∀ r r2, num_friend_requests ages = ok r → num_friend_requests ages2 = ok r2 →
        r2.val = r.val
          + (((Finset.range n).filter
              (fun i => a ≤ ageAt ages i ∧ ageAt ages i + 14 < 2 * a)).card : Int)
          + (((Finset.range n).filter
              (fun i => ageAt ages i ≤ a ∧ a + 14 < 2 * ageAt ages i)).card : Int) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (ages ages2 : Slice Std.I64) (n : Nat) (a : Int)
        (hlen : ages.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 19999)
        (hbound : ∀ i, i < n → 1 ≤ ageAt ages i ∧ ageAt ages i ≤ 120)
        (ha1 : 1 ≤ a) (ha2 : a ≤ 120)
        (hlen2 : ages2.val.length = n + 1)
        (hagree : ∀ i, i < n → ageAt ages2 i = ageAt ages i)
        (hlast : ageAt ages2 n = a), ∀ r r2, num_friend_requests ages = ok r → num_friend_requests ages2 = ok r2 →
          r2.val = r.val
            + (((Finset.range n).filter
                (fun i => a ≤ ageAt ages i ∧ ageAt ages i + 14 < 2 * a)).card : Int)
            + (((Finset.range n).filter
                (fun i => ageAt ages i ≤ a ∧ a + 14 < 2 * ageAt ages i)).card : Int)) := by
    sorry

  /-- Whenever the function returns a result r on input ages satisfying the preconditions, r equals the number of unordered pairs {i,j} with 0 <= i < j < n such that, letting y be the index among i,j with the smaller age and o be the index with the larger age, 2*ages[y] > ages[o] + 14.
    Preconditions: n = len(ages), 1 <= n <= 20000, for every i with 0 <= i < n, 1 <= ages[i] <= 120, and the ages are pairwise distinct: for every i != j, ages[i] != ages[j]. -/
  theorem spec_10 (ages : Slice Std.I64) (n : Nat)
      (hlen : ages.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 20000)
      (hbound : ∀ i, i < n → 1 ≤ ageAt ages i ∧ ageAt ages i ≤ 120)
      (hdistinct : ∀ i j, i < n → j < n → i ≠ j → ageAt ages i ≠ ageAt ages j) :
      ∀ r, num_friend_requests ages = ok r → r.val = (unorderedRequestCount ages n : Int) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (ages : Slice Std.I64) (n : Nat)
        (hlen : ages.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 20000)
        (hbound : ∀ i, i < n → 1 ≤ ageAt ages i ∧ ageAt ages i ≤ 120)
        (hdistinct : ∀ i j, i < n → j < n → i ≠ j → ageAt ages i ≠ ageAt ages j), ∀ r, num_friend_requests ages = ok r → r.val = (unorderedRequestCount ages n : Int)) := by
    sorry

  /-- Whenever the function returns a result r on input ages satisfying the preconditions, r = T_a + T_b + T_ab, where T_a = c_a*(c_a-1) if a >= 15 and T_a = 0 otherwise; T_b = c_b*(c_b-1) if b >= 15 and T_b = 0 otherwise; and T_ab = c_a*c_b if 2*a > b + 14 and T_ab = 0 otherwise.
    Preconditions: n = len(ages), 1 <= n <= 20000, for every i with 0 <= i < n, 1 <= ages[i] <= 120, and there exist integers a and b with 1 <= a < b <= 120 such that every ages[i] is either a or b. Let c_a be the number of indices i with ages[i] = a, and let c_b be the number of indices i with ages[i] = b, so c_a + c_b = n. -/
  theorem spec_11 (ages : Slice Std.I64) (n : Nat) (a b : Int)
      (hlen : ages.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 20000)
      (ha1 : 1 ≤ a) (hab : a < b) (hb2 : b ≤ 120)
      (hconst : ∀ i, i < n → ageAt ages i = a ∨ ageAt ages i = b) :
      ∀ r, num_friend_requests ages = ok r →
        r.val
          = (if 15 ≤ a then (countVal ages n a : Int) * ((countVal ages n a : Int) - 1) else 0)
            + (if 15 ≤ b then (countVal ages n b : Int) * ((countVal ages n b : Int) - 1) else 0)
            + (if b + 14 < 2 * a then (countVal ages n a : Int) * (countVal ages n b : Int)
               else 0) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (ages : Slice Std.I64) (n : Nat) (a b : Int)
        (hlen : ages.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 20000)
        (ha1 : 1 ≤ a) (hab : a < b) (hb2 : b ≤ 120)
        (hconst : ∀ i, i < n → ageAt ages i = a ∨ ageAt ages i = b), ∀ r, num_friend_requests ages = ok r →
          r.val
            = (if 15 ≤ a then (countVal ages n a : Int) * ((countVal ages n a : Int) - 1) else 0)
              + (if 15 ≤ b then (countVal ages n b : Int) * ((countVal ages n b : Int) - 1) else 0)
              + (if b + 14 < 2 * a then (countVal ages n a : Int) * (countVal ages n b : Int)
                 else 0)) := by
    sorry

  /-- Whenever the function returns a result r on input ages satisfying the preconditions, r >= sum over v from 15 to 120 of c_v*(c_v-1).
    Preconditions: n = len(ages), 1 <= n <= 20000, and for every i with 0 <= i < n, 1 <= ages[i] <= 120. For each integer v with 15 <= v <= 120, let c_v be the number of indices i with ages[i] = v. -/
  theorem spec_12 (ages : Slice Std.I64) (n : Nat)
      (hlen : ages.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 20000)
      (hbound : ∀ i, i < n → 1 ≤ ageAt ages i ∧ ageAt ages i ≤ 120) :
      ∀ r, num_friend_requests ages = ok r →
        r.val ≥ (((Finset.Icc 15 120).sum
                    (fun v : Nat => countVal ages n (v : Int) * (countVal ages n (v : Int) - 1))) :
                  Int) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (ages : Slice Std.I64) (n : Nat)
        (hlen : ages.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 20000)
        (hbound : ∀ i, i < n → 1 ≤ ageAt ages i ∧ ageAt ages i ≤ 120), ∀ r, num_friend_requests ages = ok r →
          r.val ≥ (((Finset.Icc 15 120).sum
                      (fun v : Nat => countVal ages n (v : Int) * (countVal ages n (v : Int) - 1))) :
                    Int)) := by
    sorry

  end AegisSpec.NumFriendRequests
