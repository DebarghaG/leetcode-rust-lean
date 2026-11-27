import Aegis.MinimumCardPickup.Code.Funs

/-!
# Specifications of `Aegis.MinimumCardPickup.minimum_card_pickup`

LeetCode problem `minimum-consecutive-cards-to-pick-up`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MinimumCardPickup

namespace AegisSpec.MinimumCardPickup

def lval (l : List Std.I64) (i : ℕ) (hi : i < l.length) : ℤ := (l.get ⟨i, hi⟩).val

def HasDup (l : List Std.I64) : Prop :=
  ∃ (i j : ℕ) (hi : i < l.length) (hj : j < l.length), i < j ∧ lval l i hi = lval l j hj

def SegHasDup (l : List Std.I64) (L R : ℕ) : Prop :=
  ∃ (p q : ℕ) (hp : p < l.length) (hq : q < l.length),
    L ≤ p ∧ p < q ∧ q ≤ R ∧ lval l p hp = lval l q hq

def SegNoDup (l : List Std.I64) (L s : ℕ) : Prop :=
  ∀ (p q : ℕ) (hp : p < l.length) (hq : q < l.length),
    L ≤ p → p < q → q < L + s → lval l p hp ≠ lval l q hq

def IsMinDupWindow (l : List Std.I64) (x : ℤ) : Prop :=
  (∃ (L R : ℕ), L ≤ R ∧ R < l.length ∧ SegHasDup l L R ∧ x = (R : ℤ) + 1 - (L : ℤ)) ∧
    (∀ (L R : ℕ), L ≤ R → R < l.length → SegHasDup l L R → x ≤ (R : ℤ) + 1 - (L : ℤ))

def IsMinGap (l : List Std.I64) (x : ℤ) : Prop :=
  (∃ (i j : ℕ) (hi : i < l.length) (hj : j < l.length),
      i < j ∧ lval l i hi = lval l j hj ∧ x = (j : ℤ) - (i : ℤ)) ∧
    (∀ (i j : ℕ) (hi : i < l.length) (hj : j < l.length),
      i < j → lval l i hi = lval l j hj → x ≤ (j : ℤ) - (i : ℤ))

def ValidInput (cards : Slice Std.I64) : Prop :=
  1 ≤ cards.val.length ∧ cards.val.length ≤ 100000 ∧
    ∀ (i : ℕ) (hi : i < cards.val.length), 0 ≤ lval cards.val i hi ∧ lval cards.val i hi ≤ 1000000

/-- Whenever the function returns a result r, the following holds. If there exist indices i and j with 0 <= i < j < len(cards) and cards[i] = cards[j], then r != -1 and r = min{ R - L + 1 | 0 <= L <= R < len(cards) and there exist p and q with L <= p < q <= R and cards[p] = cards[q] }. If no such indices i and j exist, then r = -1.
  Preconditions: cards is a slice of 64-bit signed integers with 1 <= len(cards) <= 100000 and, for every i with 0 <= i < len(cards), 0 <= cards[i] <= 1000000. -/
theorem spec_1 (cards : Slice Std.I64) (h : ValidInput cards) :
    ∀ (r : Std.I64), minimum_card_pickup cards = ok r →
      (HasDup cards.val → r.val ≠ -1 ∧ IsMinDupWindow cards.val r.val) ∧
        (¬ HasDup cards.val → r.val = -1) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (cards : Slice Std.I64) (h : ValidInput cards), ∀ (r : Std.I64), minimum_card_pickup cards = ok r →
      (HasDup cards.val → r.val ≠ -1 ∧ IsMinDupWindow cards.val r.val) ∧
        (¬ HasDup cards.val → r.val = -1)) := by
  sorry

/-- Whenever the precondition holds, the function returns a result r; it does not fail.
  Preconditions: cards is a slice of 64-bit signed integers with 1 <= len(cards) <= 100000 and, for every i with 0 <= i < len(cards), 0 <= cards[i] <= 1000000. -/
theorem spec_2 (cards : Slice Std.I64) (h : ValidInput cards) :
    ∃ (r : Std.I64), minimum_card_pickup cards = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (cards : Slice Std.I64) (h : ValidInput cards), ∃ (r : Std.I64), minimum_card_pickup cards = ok r) := by
  sorry

/-- Whenever the function returns a result r, either r = -1 or 2 <= r <= len(cards).
  Preconditions: cards is a slice of 64-bit signed integers with 1 <= len(cards) <= 100000 and, for every i with 0 <= i < len(cards), 0 <= cards[i] <= 1000000. -/
theorem spec_3 (cards : Slice Std.I64) (h : ValidInput cards) :
    ∀ (r : Std.I64), minimum_card_pickup cards = ok r →
      r.val = -1 ∨ (2 ≤ r.val ∧ r.val ≤ (cards.val.length : ℤ)) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (cards : Slice Std.I64) (h : ValidInput cards), ∀ (r : Std.I64), minimum_card_pickup cards = ok r →
      r.val = -1 ∨ (2 ≤ r.val ∧ r.val ≤ (cards.val.length : ℤ))) := by
  sorry

/-- Whenever the function returns a result r, r = -1 if and only if for every i and j with 0 <= i < j < len(cards), cards[i] != cards[j].
  Preconditions: cards is a slice of 64-bit signed integers with 1 <= len(cards) <= 100000 and, for every i with 0 <= i < len(cards), 0 <= cards[i] <= 1000000. -/
theorem spec_4 (cards : Slice Std.I64) (h : ValidInput cards) :
    ∀ (r : Std.I64), minimum_card_pickup cards = ok r →
      (r.val = -1 ↔ ¬ HasDup cards.val) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (cards : Slice Std.I64) (h : ValidInput cards), ∀ (r : Std.I64), minimum_card_pickup cards = ok r →
      (r.val = -1 ↔ ¬ HasDup cards.val)) := by
  sorry

/-- Whenever the function returns a result r and r != -1, r = 1 + min{ j - i | 0 <= i < j < len(cards) and cards[i] = cards[j] }.
  Preconditions: cards is a slice of 64-bit signed integers with 1 <= len(cards) <= 100000 and, for every i with 0 <= i < len(cards), 0 <= cards[i] <= 1000000. -/
theorem spec_5 (cards : Slice Std.I64) (h : ValidInput cards) :
    ∀ (r : Std.I64), minimum_card_pickup cards = ok r → r.val ≠ -1 →
      ∃ m : ℤ, IsMinGap cards.val m ∧ r.val = 1 + m := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (cards : Slice Std.I64) (h : ValidInput cards), ∀ (r : Std.I64), minimum_card_pickup cards = ok r → r.val ≠ -1 →
      ∃ m : ℤ, IsMinGap cards.val m ∧ r.val = 1 + m) := by
  sorry

/-- Whenever the function returns a result r and r != -1, there exist indices i and j such that 0 <= i < j < len(cards), cards[i] = cards[j], and j - i = r - 1.
  Preconditions: cards is a slice of 64-bit signed integers with 1 <= len(cards) <= 100000 and, for every i with 0 <= i < len(cards), 0 <= cards[i] <= 1000000. -/
theorem spec_6 (cards : Slice Std.I64) (h : ValidInput cards) :
    ∀ (r : Std.I64), minimum_card_pickup cards = ok r → r.val ≠ -1 →
      ∃ (i j : ℕ) (hi : i < cards.val.length) (hj : j < cards.val.length),
        i < j ∧ lval cards.val i hi = lval cards.val j hj ∧
          (j : ℤ) - (i : ℤ) = r.val - 1 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (cards : Slice Std.I64) (h : ValidInput cards), ∀ (r : Std.I64), minimum_card_pickup cards = ok r → r.val ≠ -1 →
      ∃ (i j : ℕ) (hi : i < cards.val.length) (hj : j < cards.val.length),
        i < j ∧ lval cards.val i hi = lval cards.val j hj ∧
          (j : ℤ) - (i : ℤ) = r.val - 1) := by
  sorry

/-- Whenever the function returns a result r and r != -1, for every i and j with 0 <= i < j < len(cards) and cards[i] = cards[j], we have r - 1 <= j - i.
  Preconditions: cards is a slice of 64-bit signed integers with 1 <= len(cards) <= 100000 and, for every i with 0 <= i < len(cards), 0 <= cards[i] <= 1000000. -/
theorem spec_7 (cards : Slice Std.I64) (h : ValidInput cards) :
    ∀ (r : Std.I64), minimum_card_pickup cards = ok r → r.val ≠ -1 →
      ∀ (i j : ℕ) (hi : i < cards.val.length) (hj : j < cards.val.length),
        i < j → lval cards.val i hi = lval cards.val j hj → r.val - 1 ≤ (j : ℤ) - (i : ℤ) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (cards : Slice Std.I64) (h : ValidInput cards), ∀ (r : Std.I64), minimum_card_pickup cards = ok r → r.val ≠ -1 →
      ∀ (i j : ℕ) (hi : i < cards.val.length) (hj : j < cards.val.length),
        i < j → lval cards.val i hi = lval cards.val j hj → r.val - 1 ≤ (j : ℤ) - (i : ℤ)) := by
  sorry

/-- Whenever the function returns a result r and r != -1, there exists an index L with 0 <= L <= len(cards) - r such that the consecutive segment cards[L], cards[L+1], ..., cards[L+r-1] contains two equal cards: there exist p and q with L <= p < q <= L+r-1 and cards[p] = cards[q].
  Preconditions: cards is a slice of 64-bit signed integers with 1 <= len(cards) <= 100000 and, for every i with 0 <= i < len(cards), 0 <= cards[i] <= 1000000. -/
theorem spec_8 (cards : Slice Std.I64) (h : ValidInput cards) :
    ∀ (r : Std.I64), minimum_card_pickup cards = ok r → r.val ≠ -1 →
      ∃ (L : ℕ) (p q : ℕ) (hp : p < cards.val.length) (hq : q < cards.val.length),
        (L : ℤ) ≤ (cards.val.length : ℤ) - r.val ∧ L ≤ p ∧ p < q ∧
          (q : ℤ) ≤ (L : ℤ) + r.val - 1 ∧ lval cards.val p hp = lval cards.val q hq := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (cards : Slice Std.I64) (h : ValidInput cards), ∀ (r : Std.I64), minimum_card_pickup cards = ok r → r.val ≠ -1 →
      ∃ (L : ℕ) (p q : ℕ) (hp : p < cards.val.length) (hq : q < cards.val.length),
        (L : ℤ) ≤ (cards.val.length : ℤ) - r.val ∧ L ≤ p ∧ p < q ∧
          (q : ℤ) ≤ (L : ℤ) + r.val - 1 ∧ lval cards.val p hp = lval cards.val q hq) := by
  sorry

/-- Whenever the function returns a result r and r != -1, for every index L and every length s with 1 <= s < r and 0 <= L and L + s <= len(cards), the consecutive segment cards[L], cards[L+1], ..., cards[L+s-1] contains no two equal cards: for all p and q with L <= p < q < L+s, cards[p] != cards[q].
  Preconditions: cards is a slice of 64-bit signed integers with 1 <= len(cards) <= 100000 and, for every i with 0 <= i < len(cards), 0 <= cards[i] <= 1000000. -/
theorem spec_9 (cards : Slice Std.I64) (h : ValidInput cards) :
    ∀ (r : Std.I64), minimum_card_pickup cards = ok r → r.val ≠ -1 →
      ∀ (L s : ℕ), 1 ≤ s → (s : ℤ) < r.val →
        (L : ℤ) + (s : ℤ) ≤ (cards.val.length : ℤ) → SegNoDup cards.val L s := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (cards : Slice Std.I64) (h : ValidInput cards), ∀ (r : Std.I64), minimum_card_pickup cards = ok r → r.val ≠ -1 →
      ∀ (L s : ℕ), 1 ≤ s → (s : ℤ) < r.val →
        (L : ℤ) + (s : ℤ) ≤ (cards.val.length : ℤ) → SegNoDup cards.val L s) := by
  sorry

/-- Whenever the function returns a result r, r = 2 if and only if there exists an index i with 0 <= i < len(cards) - 1 and cards[i] = cards[i+1].
  Preconditions: cards is a slice of 64-bit signed integers with 1 <= len(cards) <= 100000 and, for every i with 0 <= i < len(cards), 0 <= cards[i] <= 1000000. -/
theorem spec_10 (cards : Slice Std.I64) (h : ValidInput cards) :
    ∀ (r : Std.I64), minimum_card_pickup cards = ok r →
      (r.val = 2 ↔
        ∃ (i : ℕ) (hi : i < cards.val.length) (hi1 : i + 1 < cards.val.length),
          lval cards.val i hi = lval cards.val (i + 1) hi1) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (cards : Slice Std.I64) (h : ValidInput cards), ∀ (r : Std.I64), minimum_card_pickup cards = ok r →
      (r.val = 2 ↔
        ∃ (i : ℕ) (hi : i < cards.val.length) (hi1 : i + 1 < cards.val.length),
          lval cards.val i hi = lval cards.val (i + 1) hi1)) := by
  sorry

/-- Let rev be the slice of length len(cards) defined by rev[i] = cards[len(cards) - 1 - i] for every i with 0 <= i < len(cards). Whenever minimum_card_pickup(cards) returns r and minimum_card_pickup(rev) returns r_rev, r = r_rev.
  Preconditions: cards is a slice of 64-bit signed integers with 1 <= len(cards) <= 100000 and, for every i with 0 <= i < len(cards), 0 <= cards[i] <= 1000000. -/
theorem spec_11 (cards : Slice Std.I64) (h : ValidInput cards) :
    ∀ (rev : Slice Std.I64), rev.val = cards.val.reverse →
      ∀ (r r_rev : Std.I64), minimum_card_pickup cards = ok r →
        minimum_card_pickup rev = ok r_rev → r.val = r_rev.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (cards : Slice Std.I64) (h : ValidInput cards), ∀ (rev : Slice Std.I64), rev.val = cards.val.reverse →
      ∀ (r r_rev : Std.I64), minimum_card_pickup cards = ok r →
        minimum_card_pickup rev = ok r_rev → r.val = r_rev.val) := by
  sorry

/-- Let f be any injective function from the set { cards[i] | 0 <= i < len(cards) } to the 64-bit integers in [0, 1000000], and let cards2 be the slice with len(cards2) = len(cards) and cards2[i] = f(cards[i]) for every i with 0 <= i < len(cards). Whenever minimum_card_pickup(cards) returns r and minimum_card_pickup(cards2) returns r2, r = r2.
  Preconditions: cards is a slice of 64-bit signed integers with 1 <= len(cards) <= 100000 and, for every i with 0 <= i < len(cards), 0 <= cards[i] <= 1000000. -/
theorem spec_12 (cards : Slice Std.I64) (h : ValidInput cards) :
    ∀ (f : ℤ → ℤ) (cards2 : Slice Std.I64),
      (∀ (i : ℕ) (hi : i < cards.val.length),
          0 ≤ f (lval cards.val i hi) ∧ f (lval cards.val i hi) ≤ 1000000) →
      (∀ (i j : ℕ) (hi : i < cards.val.length) (hj : j < cards.val.length),
          f (lval cards.val i hi) = f (lval cards.val j hj) →
            lval cards.val i hi = lval cards.val j hj) →
      cards2.val.length = cards.val.length →
      (∀ (i : ℕ) (hi : i < cards.val.length) (hi2 : i < cards2.val.length),
          lval cards2.val i hi2 = f (lval cards.val i hi)) →
      ∀ (r r2 : Std.I64), minimum_card_pickup cards = ok r →
        minimum_card_pickup cards2 = ok r2 → r.val = r2.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (cards : Slice Std.I64) (h : ValidInput cards), ∀ (f : ℤ → ℤ) (cards2 : Slice Std.I64),
      (∀ (i : ℕ) (hi : i < cards.val.length),
          0 ≤ f (lval cards.val i hi) ∧ f (lval cards.val i hi) ≤ 1000000) →
      (∀ (i j : ℕ) (hi : i < cards.val.length) (hj : j < cards.val.length),
          f (lval cards.val i hi) = f (lval cards.val j hj) →
            lval cards.val i hi = lval cards.val j hj) →
      cards2.val.length = cards.val.length →
      (∀ (i : ℕ) (hi : i < cards.val.length) (hi2 : i < cards2.val.length),
          lval cards2.val i hi2 = f (lval cards.val i hi)) →
      ∀ (r r2 : Std.I64), minimum_card_pickup cards = ok r →
        minimum_card_pickup cards2 = ok r2 → r.val = r2.val) := by
  sorry

/-- For every k with 1 <= k <= len(cards), let pref be the slice of length k with pref[i] = cards[i] for every i with 0 <= i < k. Whenever minimum_card_pickup(cards) returns r and minimum_card_pickup(pref) returns r_pref, if r_pref != -1 then r != -1 and r <= r_pref.
  Preconditions: cards is a slice of 64-bit signed integers with 1 <= len(cards) <= 100000 and, for every i with 0 <= i < len(cards), 0 <= cards[i] <= 1000000. -/
theorem spec_13 (cards : Slice Std.I64) (h : ValidInput cards) :
    ∀ (k : ℕ), 1 ≤ k → k ≤ cards.val.length →
      ∀ (pref : Slice Std.I64), pref.val = cards.val.take k →
        ∀ (r r_pref : Std.I64), minimum_card_pickup cards = ok r →
          minimum_card_pickup pref = ok r_pref → r_pref.val ≠ -1 →
            r.val ≠ -1 ∧ r.val ≤ r_pref.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (cards : Slice Std.I64) (h : ValidInput cards), ∀ (k : ℕ), 1 ≤ k → k ≤ cards.val.length →
      ∀ (pref : Slice Std.I64), pref.val = cards.val.take k →
        ∀ (r r_pref : Std.I64), minimum_card_pickup cards = ok r →
          minimum_card_pickup pref = ok r_pref → r_pref.val ≠ -1 →
            r.val ≠ -1 ∧ r.val ≤ r_pref.val) := by
  sorry

end AegisSpec.MinimumCardPickup
