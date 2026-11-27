import Aegis.IsNStraightHand.Code.Funs

/-!
# Specifications of `Aegis.IsNStraightHand.is_n_straight_hand`

LeetCode problem `hand-of-straights`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.IsNStraightHand

def countVal (l : List Std.I64) (v : ℤ) : ℕ :=
  l.countP (fun x => x.val = v)

def distinctValCount (l : List Std.I64) : ℕ :=
  (l.map (fun x => x.val)).dedup.length

def IsMinEntry (l : List Std.I64) (m : ℤ) : Prop :=
  (∀ x ∈ l, m ≤ x.val) ∧ ∃ x ∈ l, x.val = m

def IsMaxEntry (l : List Std.I64) (M : ℤ) : Prop :=
  (∀ x ∈ l, x.val ≤ M) ∧ ∃ x ∈ l, x.val = M

/-- Let c(v) = #{i | 0 <= i < len(hand) and hand[i] = v} for every integer v. Whenever is_n_straight_hand(hand, group_size) returns a result r, we have r = true if and only if there exists a function m : Z -> N such that m(s) = 0 for all but finitely many integers s, and for every integer v, c(v) = Σ_{t=0}^{group_size-1} m(v - t). Equivalently, the multiset of entries of hand can be partitioned into len(hand)/group_size groups, each of size group_size, whose entries are group_size consecutive integers with each value appearing exactly once in its group.
  Preconditions: 1 <= len(hand) <= 10^4; for every i with 0 <= i < len(hand), 0 <= hand[i] <= 10^9; 1 <= group_size <= len(hand). All quantities are within the signed 64-bit range. -/
theorem spec_1
    (hand : Slice Std.I64) (group_size : Std.I64)
    (hlen_lb : 1 ≤ hand.val.length) (hlen_ub : hand.val.length ≤ 10000)
    (hval : ∀ x ∈ hand.val, 0 ≤ x.val ∧ x.val ≤ 1000000000)
    (hg_lb : 1 ≤ group_size.val) (hg_ub : group_size.val ≤ (hand.val.length : ℤ)) :
    ∀ r : Bool, Aegis.IsNStraightHand.is_n_straight_hand hand group_size = ok r →
      (r = true ↔
        ∃ m : ℤ → ℕ,
          Set.Finite {s : ℤ | m s ≠ 0} ∧
            ∀ v : ℤ,
              countVal hand.val v =
                Finset.sum (Finset.range group_size.val.toNat) (fun t => m (v - (t : ℤ)))) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (hand : Slice Std.I64) (group_size : Std.I64)
    (hlen_lb : 1 ≤ hand.val.length) (hlen_ub : hand.val.length ≤ 10000)
    (hval : ∀ x ∈ hand.val, 0 ≤ x.val ∧ x.val ≤ 1000000000)
    (hg_lb : 1 ≤ group_size.val) (hg_ub : group_size.val ≤ (hand.val.length : ℤ)), ∀ r : Bool, Aegis.IsNStraightHand.is_n_straight_hand hand group_size = ok r →
      (r = true ↔
        ∃ m : ℤ → ℕ,
          Set.Finite {s : ℤ | m s ≠ 0} ∧
            ∀ v : ℤ,
              countVal hand.val v =
                Finset.sum (Finset.range group_size.val.toNat) (fun t => m (v - (t : ℤ))))) := by
  sorry

/-- For every valid input, is_n_straight_hand(hand, group_size) returns a result r; it does not fail, panic, or overflow.
  Preconditions: 1 <= len(hand) <= 10^4; for every i with 0 <= i < len(hand), 0 <= hand[i] <= 10^9; 1 <= group_size <= len(hand). All quantities are within the signed 64-bit range. -/
theorem spec_2
    (hand : Slice Std.I64) (group_size : Std.I64)
    (hlen_lb : 1 ≤ hand.val.length) (hlen_ub : hand.val.length ≤ 10000)
    (hval : ∀ x ∈ hand.val, 0 ≤ x.val ∧ x.val ≤ 1000000000)
    (hg_lb : 1 ≤ group_size.val) (hg_ub : group_size.val ≤ (hand.val.length : ℤ)) :
    ∃ r : Bool, Aegis.IsNStraightHand.is_n_straight_hand hand group_size = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (hand : Slice Std.I64) (group_size : Std.I64)
    (hlen_lb : 1 ≤ hand.val.length) (hlen_ub : hand.val.length ≤ 10000)
    (hval : ∀ x ∈ hand.val, 0 ≤ x.val ∧ x.val ≤ 1000000000)
    (hg_lb : 1 ≤ group_size.val) (hg_ub : group_size.val ≤ (hand.val.length : ℤ)), ∃ r : Bool, Aegis.IsNStraightHand.is_n_straight_hand hand group_size = ok r) := by
  sorry

/-- For every valid input, if len(hand) mod group_size ≠ 0, then is_n_straight_hand(hand, group_size) returns a result r with r = false.
  Preconditions: 1 <= len(hand) <= 10^4; for every i with 0 <= i < len(hand), 0 <= hand[i] <= 10^9; 1 <= group_size <= len(hand). All quantities are within the signed 64-bit range. -/
theorem spec_3
    (hand : Slice Std.I64) (group_size : Std.I64)
    (hlen_lb : 1 ≤ hand.val.length) (hlen_ub : hand.val.length ≤ 10000)
    (hval : ∀ x ∈ hand.val, 0 ≤ x.val ∧ x.val ≤ 1000000000)
    (hg_lb : 1 ≤ group_size.val) (hg_ub : group_size.val ≤ (hand.val.length : ℤ))
    (hmod : hand.val.length % group_size.val.toNat ≠ 0) :
    ∀ r : Bool, Aegis.IsNStraightHand.is_n_straight_hand hand group_size = ok r → r = false := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (hand : Slice Std.I64) (group_size : Std.I64)
    (hlen_lb : 1 ≤ hand.val.length) (hlen_ub : hand.val.length ≤ 10000)
    (hval : ∀ x ∈ hand.val, 0 ≤ x.val ∧ x.val ≤ 1000000000)
    (hg_lb : 1 ≤ group_size.val) (hg_ub : group_size.val ≤ (hand.val.length : ℤ))
    (hmod : hand.val.length % group_size.val.toNat ≠ 0), ∀ r : Bool, Aegis.IsNStraightHand.is_n_straight_hand hand group_size = ok r → r = false) := by
  sorry

/-- For every valid input with group_size = 1, is_n_straight_hand(hand, group_size) returns a result r with r = true.
  Preconditions: 1 <= len(hand) <= 10^4; for every i with 0 <= i < len(hand), 0 <= hand[i] <= 10^9; 1 <= group_size <= len(hand). All quantities are within the signed 64-bit range. -/
theorem spec_4
    (hand : Slice Std.I64) (group_size : Std.I64)
    (hlen_lb : 1 ≤ hand.val.length) (hlen_ub : hand.val.length ≤ 10000)
    (hval : ∀ x ∈ hand.val, 0 ≤ x.val ∧ x.val ≤ 1000000000)
    (hg_lb : 1 ≤ group_size.val) (hg_ub : group_size.val ≤ (hand.val.length : ℤ))
    (hg_one : group_size.val = 1) :
    ∀ r : Bool, Aegis.IsNStraightHand.is_n_straight_hand hand group_size = ok r → r = true := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (hand : Slice Std.I64) (group_size : Std.I64)
    (hlen_lb : 1 ≤ hand.val.length) (hlen_ub : hand.val.length ≤ 10000)
    (hval : ∀ x ∈ hand.val, 0 ≤ x.val ∧ x.val ≤ 1000000000)
    (hg_lb : 1 ≤ group_size.val) (hg_ub : group_size.val ≤ (hand.val.length : ℤ))
    (hg_one : group_size.val = 1), ∀ r : Bool, Aegis.IsNStraightHand.is_n_straight_hand hand group_size = ok r → r = true) := by
  sorry

/-- Let c(v) = #{i | 0 <= i < len(hand) and hand[i] = v} for every integer v. For every valid input with group_size = len(hand), whenever is_n_straight_hand(hand, group_size) returns a result r, r = true if and only if there exists an integer a such that for every integer v, c(v) = 1 when a <= v < a + group_size, and c(v) = 0 otherwise.
  Preconditions: 1 <= len(hand) <= 10^4; for every i with 0 <= i < len(hand), 0 <= hand[i] <= 10^9; 1 <= group_size <= len(hand). All quantities are within the signed 64-bit range. -/
theorem spec_5
    (hand : Slice Std.I64) (group_size : Std.I64)
    (hlen_lb : 1 ≤ hand.val.length) (hlen_ub : hand.val.length ≤ 10000)
    (hval : ∀ x ∈ hand.val, 0 ≤ x.val ∧ x.val ≤ 1000000000)
    (hg_lb : 1 ≤ group_size.val) (hg_ub : group_size.val ≤ (hand.val.length : ℤ))
    (hlen_eq : group_size.val = (hand.val.length : ℤ)) :
    ∀ r : Bool, Aegis.IsNStraightHand.is_n_straight_hand hand group_size = ok r →
      (r = true ↔
        ∃ a : ℤ, ∀ v : ℤ,
          countVal hand.val v = if a ≤ v ∧ v < a + group_size.val then 1 else 0) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (hand : Slice Std.I64) (group_size : Std.I64)
    (hlen_lb : 1 ≤ hand.val.length) (hlen_ub : hand.val.length ≤ 10000)
    (hval : ∀ x ∈ hand.val, 0 ≤ x.val ∧ x.val ≤ 1000000000)
    (hg_lb : 1 ≤ group_size.val) (hg_ub : group_size.val ≤ (hand.val.length : ℤ))
    (hlen_eq : group_size.val = (hand.val.length : ℤ)), ∀ r : Bool, Aegis.IsNStraightHand.is_n_straight_hand hand group_size = ok r →
      (r = true ↔
        ∃ a : ℤ, ∀ v : ℤ,
          countVal hand.val v = if a ≤ v ∧ v < a + group_size.val then 1 else 0)) := by
  sorry

/-- For every valid input, if is_n_straight_hand(hand, group_size) returns a result r with r = true, then max(hand) - min(hand) >= group_size - 1, where max(hand) and min(hand) are the maximum and minimum entries of hand.
  Preconditions: 1 <= len(hand) <= 10^4; for every i with 0 <= i < len(hand), 0 <= hand[i] <= 10^9; 1 <= group_size <= len(hand). All quantities are within the signed 64-bit range. -/
theorem spec_6
    (hand : Slice Std.I64) (group_size : Std.I64)
    (hlen_lb : 1 ≤ hand.val.length) (hlen_ub : hand.val.length ≤ 10000)
    (hval : ∀ x ∈ hand.val, 0 ≤ x.val ∧ x.val ≤ 1000000000)
    (hg_lb : 1 ≤ group_size.val) (hg_ub : group_size.val ≤ (hand.val.length : ℤ)) :
    ∀ r : Bool, Aegis.IsNStraightHand.is_n_straight_hand hand group_size = ok r → r = true →
      ∀ mx mn : ℤ, IsMaxEntry hand.val mx → IsMinEntry hand.val mn →
        group_size.val - 1 ≤ mx - mn := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (hand : Slice Std.I64) (group_size : Std.I64)
    (hlen_lb : 1 ≤ hand.val.length) (hlen_ub : hand.val.length ≤ 10000)
    (hval : ∀ x ∈ hand.val, 0 ≤ x.val ∧ x.val ≤ 1000000000)
    (hg_lb : 1 ≤ group_size.val) (hg_ub : group_size.val ≤ (hand.val.length : ℤ)), ∀ r : Bool, Aegis.IsNStraightHand.is_n_straight_hand hand group_size = ok r → r = true →
      ∀ mx mn : ℤ, IsMaxEntry hand.val mx → IsMinEntry hand.val mn →
        group_size.val - 1 ≤ mx - mn) := by
  sorry

/-- Let c(v) = #{i | 0 <= i < len(hand) and hand[i] = v} for every integer v. For every valid input, if is_n_straight_hand(hand, group_size) returns a result r with r = true, then for every integer v, c(v) <= len(hand) / group_size, where / denotes exact integer division (which is justified because r = true implies len(hand) is divisible by group_size).
  Preconditions: 1 <= len(hand) <= 10^4; for every i with 0 <= i < len(hand), 0 <= hand[i] <= 10^9; 1 <= group_size <= len(hand). All quantities are within the signed 64-bit range. -/
theorem spec_7
    (hand : Slice Std.I64) (group_size : Std.I64)
    (hlen_lb : 1 ≤ hand.val.length) (hlen_ub : hand.val.length ≤ 10000)
    (hval : ∀ x ∈ hand.val, 0 ≤ x.val ∧ x.val ≤ 1000000000)
    (hg_lb : 1 ≤ group_size.val) (hg_ub : group_size.val ≤ (hand.val.length : ℤ)) :
    ∀ r : Bool, Aegis.IsNStraightHand.is_n_straight_hand hand group_size = ok r → r = true →
      ∀ v : ℤ, countVal hand.val v ≤ hand.val.length / group_size.val.toNat := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (hand : Slice Std.I64) (group_size : Std.I64)
    (hlen_lb : 1 ≤ hand.val.length) (hlen_ub : hand.val.length ≤ 10000)
    (hval : ∀ x ∈ hand.val, 0 ≤ x.val ∧ x.val ≤ 1000000000)
    (hg_lb : 1 ≤ group_size.val) (hg_ub : group_size.val ≤ (hand.val.length : ℤ)), ∀ r : Bool, Aegis.IsNStraightHand.is_n_straight_hand hand group_size = ok r → r = true →
      ∀ v : ℤ, countVal hand.val v ≤ hand.val.length / group_size.val.toNat) := by
  sorry

/-- Let c(v) = #{i | 0 <= i < len(hand) and hand[i] = v} for every integer v. For every valid input, if is_n_straight_hand(hand, group_size) returns a result r with r = true, then the number of integers v with c(v) > 0 is at least group_size.
  Preconditions: 1 <= len(hand) <= 10^4; for every i with 0 <= i < len(hand), 0 <= hand[i] <= 10^9; 1 <= group_size <= len(hand). All quantities are within the signed 64-bit range. -/
theorem spec_8
    (hand : Slice Std.I64) (group_size : Std.I64)
    (hlen_lb : 1 ≤ hand.val.length) (hlen_ub : hand.val.length ≤ 10000)
    (hval : ∀ x ∈ hand.val, 0 ≤ x.val ∧ x.val ≤ 1000000000)
    (hg_lb : 1 ≤ group_size.val) (hg_ub : group_size.val ≤ (hand.val.length : ℤ)) :
    ∀ r : Bool, Aegis.IsNStraightHand.is_n_straight_hand hand group_size = ok r → r = true →
      group_size.val.toNat ≤ distinctValCount hand.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (hand : Slice Std.I64) (group_size : Std.I64)
    (hlen_lb : 1 ≤ hand.val.length) (hlen_ub : hand.val.length ≤ 10000)
    (hval : ∀ x ∈ hand.val, 0 ≤ x.val ∧ x.val ≤ 1000000000)
    (hg_lb : 1 ≤ group_size.val) (hg_ub : group_size.val ≤ (hand.val.length : ℤ)), ∀ r : Bool, Aegis.IsNStraightHand.is_n_straight_hand hand group_size = ok r → r = true →
      group_size.val.toNat ≤ distinctValCount hand.val) := by
  sorry

/-- For every valid input, if is_n_straight_hand(hand, group_size) returns a result r with r = true, then writing mn = min(hand), for every t with 0 <= t < group_size there exists an index i with 0 <= i < len(hand) and hand[i] = mn + t.
  Preconditions: 1 <= len(hand) <= 10^4; for every i with 0 <= i < len(hand), 0 <= hand[i] <= 10^9; 1 <= group_size <= len(hand). All quantities are within the signed 64-bit range. -/
theorem spec_9
    (hand : Slice Std.I64) (group_size : Std.I64)
    (hlen_lb : 1 ≤ hand.val.length) (hlen_ub : hand.val.length ≤ 10000)
    (hval : ∀ x ∈ hand.val, 0 ≤ x.val ∧ x.val ≤ 1000000000)
    (hg_lb : 1 ≤ group_size.val) (hg_ub : group_size.val ≤ (hand.val.length : ℤ)) :
    ∀ r : Bool, Aegis.IsNStraightHand.is_n_straight_hand hand group_size = ok r → r = true →
      ∀ mn : ℤ, IsMinEntry hand.val mn →
        ∀ t : ℤ, 0 ≤ t → t < group_size.val → ∃ x ∈ hand.val, x.val = mn + t := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (hand : Slice Std.I64) (group_size : Std.I64)
    (hlen_lb : 1 ≤ hand.val.length) (hlen_ub : hand.val.length ≤ 10000)
    (hval : ∀ x ∈ hand.val, 0 ≤ x.val ∧ x.val ≤ 1000000000)
    (hg_lb : 1 ≤ group_size.val) (hg_ub : group_size.val ≤ (hand.val.length : ℤ)), ∀ r : Bool, Aegis.IsNStraightHand.is_n_straight_hand hand group_size = ok r → r = true →
      ∀ mn : ℤ, IsMinEntry hand.val mn →
        ∀ t : ℤ, 0 ≤ t → t < group_size.val → ∃ x ∈ hand.val, x.val = mn + t) := by
  sorry

/-- If for every integer v the number of indices i with 0 <= i < len(hand) and hand[i] = v equals the number of indices j with 0 <= j < len(hand') and hand'[j] = v, then whenever is_n_straight_hand(hand, group_size) returns a result r and is_n_straight_hand(hand', group_size') returns a result r', we have r = r'.
  Preconditions: Both (hand, group_size) and (hand', group_size') satisfy the problem constraints: 1 <= len(hand), len(hand') <= 10^4; all entries are in [0, 10^9]; 1 <= group_size <= len(hand); 1 <= group_size' <= len(hand'); and group_size = group_size'. -/
theorem spec_10
    (hand hand' : Slice Std.I64) (group_size group_size' : Std.I64)
    (hlen_lb : 1 ≤ hand.val.length) (hlen_ub : hand.val.length ≤ 10000)
    (hval : ∀ x ∈ hand.val, 0 ≤ x.val ∧ x.val ≤ 1000000000)
    (hg_lb : 1 ≤ group_size.val) (hg_ub : group_size.val ≤ (hand.val.length : ℤ))
    (hlen_lb' : 1 ≤ hand'.val.length) (hlen_ub' : hand'.val.length ≤ 10000)
    (hval' : ∀ x ∈ hand'.val, 0 ≤ x.val ∧ x.val ≤ 1000000000)
    (hg_lb' : 1 ≤ group_size'.val) (hg_ub' : group_size'.val ≤ (hand'.val.length : ℤ))
    (hg_eq : group_size = group_size')
    (hcount : ∀ v : ℤ, countVal hand.val v = countVal hand'.val v) :
    ∀ r r' : Bool,
      Aegis.IsNStraightHand.is_n_straight_hand hand group_size = ok r →
        Aegis.IsNStraightHand.is_n_straight_hand hand' group_size' = ok r' → r = r' := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (hand hand' : Slice Std.I64) (group_size group_size' : Std.I64)
    (hlen_lb : 1 ≤ hand.val.length) (hlen_ub : hand.val.length ≤ 10000)
    (hval : ∀ x ∈ hand.val, 0 ≤ x.val ∧ x.val ≤ 1000000000)
    (hg_lb : 1 ≤ group_size.val) (hg_ub : group_size.val ≤ (hand.val.length : ℤ))
    (hlen_lb' : 1 ≤ hand'.val.length) (hlen_ub' : hand'.val.length ≤ 10000)
    (hval' : ∀ x ∈ hand'.val, 0 ≤ x.val ∧ x.val ≤ 1000000000)
    (hg_lb' : 1 ≤ group_size'.val) (hg_ub' : group_size'.val ≤ (hand'.val.length : ℤ))
    (hg_eq : group_size = group_size')
    (hcount : ∀ v : ℤ, countVal hand.val v = countVal hand'.val v), ∀ r r' : Bool,
      Aegis.IsNStraightHand.is_n_straight_hand hand group_size = ok r →
        Aegis.IsNStraightHand.is_n_straight_hand hand' group_size' = ok r' → r = r') := by
  sorry

/-- For every valid input with group_size > 1 and hand[i] = hand[0] for every i with 0 <= i < len(hand), whenever is_n_straight_hand(hand, group_size) returns a result r, r = false.
  Preconditions: 1 <= len(hand) <= 10^4; for every i with 0 <= i < len(hand), 0 <= hand[i] <= 10^9; 1 <= group_size <= len(hand). All quantities are within the signed 64-bit range. -/
theorem spec_11
    (hand : Slice Std.I64) (group_size : Std.I64)
    (hlen_lb : 1 ≤ hand.val.length) (hlen_ub : hand.val.length ≤ 10000)
    (hval : ∀ x ∈ hand.val, 0 ≤ x.val ∧ x.val ≤ 1000000000)
    (hg_lb : 1 ≤ group_size.val) (hg_ub : group_size.val ≤ (hand.val.length : ℤ))
    (hg_gt : 1 < group_size.val)
    (hconst : ∃ c : ℤ, ∀ x ∈ hand.val, x.val = c) :
    ∀ r : Bool, Aegis.IsNStraightHand.is_n_straight_hand hand group_size = ok r → r = false := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (hand : Slice Std.I64) (group_size : Std.I64)
    (hlen_lb : 1 ≤ hand.val.length) (hlen_ub : hand.val.length ≤ 10000)
    (hval : ∀ x ∈ hand.val, 0 ≤ x.val ∧ x.val ≤ 1000000000)
    (hg_lb : 1 ≤ group_size.val) (hg_ub : group_size.val ≤ (hand.val.length : ℤ))
    (hg_gt : 1 < group_size.val)
    (hconst : ∃ c : ℤ, ∀ x ∈ hand.val, x.val = c), ∀ r : Bool, Aegis.IsNStraightHand.is_n_straight_hand hand group_size = ok r → r = false) := by
  sorry

/-- For every valid input, if is_n_straight_hand(hand, group_size) returns a result r with r = true, then writing mx = max(hand), for every t with 0 <= t < group_size there exists an index i with 0 <= i < len(hand) and hand[i] = mx - t.
  Preconditions: 1 <= len(hand) <= 10^4; for every i with 0 <= i < len(hand), 0 <= hand[i] <= 10^9; 1 <= group_size <= len(hand). All quantities are within the signed 64-bit range. -/
theorem spec_12
    (hand : Slice Std.I64) (group_size : Std.I64)
    (hlen_lb : 1 ≤ hand.val.length) (hlen_ub : hand.val.length ≤ 10000)
    (hval : ∀ x ∈ hand.val, 0 ≤ x.val ∧ x.val ≤ 1000000000)
    (hg_lb : 1 ≤ group_size.val) (hg_ub : group_size.val ≤ (hand.val.length : ℤ)) :
    ∀ r : Bool, Aegis.IsNStraightHand.is_n_straight_hand hand group_size = ok r → r = true →
      ∀ mx : ℤ, IsMaxEntry hand.val mx →
        ∀ t : ℤ, 0 ≤ t → t < group_size.val → ∃ x ∈ hand.val, x.val = mx - t := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (hand : Slice Std.I64) (group_size : Std.I64)
    (hlen_lb : 1 ≤ hand.val.length) (hlen_ub : hand.val.length ≤ 10000)
    (hval : ∀ x ∈ hand.val, 0 ≤ x.val ∧ x.val ≤ 1000000000)
    (hg_lb : 1 ≤ group_size.val) (hg_ub : group_size.val ≤ (hand.val.length : ℤ)), ∀ r : Bool, Aegis.IsNStraightHand.is_n_straight_hand hand group_size = ok r → r = true →
      ∀ mx : ℤ, IsMaxEntry hand.val mx →
        ∀ t : ℤ, 0 ≤ t → t < group_size.val → ∃ x ∈ hand.val, x.val = mx - t) := by
  sorry

/-- Whenever is_n_straight_hand(hand, group_size) returns a result r and is_n_straight_hand(hand', group_size) returns a result r', we have r = r'.
  Preconditions: Both (hand, group_size) and (hand', group_size) satisfy the problem constraints: 1 <= len(hand) <= 10^4; 1 <= len(hand') <= 10^4; for every i with 0 <= i < len(hand), 0 <= hand[i] <= 10^9; for every j with 0 <= j < len(hand'), 0 <= hand'[j] <= 10^9; 1 <= group_size <= len(hand); 1 <= group_size <= len(hand'); len(hand) = len(hand'); and there exists an integer k such that hand'[i] = hand[i] + k for every i with 0 <= i < len(hand). All quantities are within the signed 64-bit range. -/
theorem spec_13
    (hand hand' : Slice Std.I64) (group_size : Std.I64)
    (hlen_lb : 1 ≤ hand.val.length) (hlen_ub : hand.val.length ≤ 10000)
    (hval : ∀ x ∈ hand.val, 0 ≤ x.val ∧ x.val ≤ 1000000000)
    (hg_lb : 1 ≤ group_size.val) (hg_ub : group_size.val ≤ (hand.val.length : ℤ))
    (hlen_lb' : 1 ≤ hand'.val.length) (hlen_ub' : hand'.val.length ≤ 10000)
    (hval' : ∀ x ∈ hand'.val, 0 ≤ x.val ∧ x.val ≤ 1000000000)
    (hg_lb' : 1 ≤ group_size.val) (hg_ub' : group_size.val ≤ (hand'.val.length : ℤ))
    (hlen_eq : hand.val.length = hand'.val.length)
    (hshift : ∃ k : ℤ,
      ∀ p : Std.I64 × Std.I64, p ∈ hand.val.zip hand'.val → p.2.val = p.1.val + k) :
    ∀ r r' : Bool,
      Aegis.IsNStraightHand.is_n_straight_hand hand group_size = ok r →
        Aegis.IsNStraightHand.is_n_straight_hand hand' group_size = ok r' → r = r' := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (hand hand' : Slice Std.I64) (group_size : Std.I64)
    (hlen_lb : 1 ≤ hand.val.length) (hlen_ub : hand.val.length ≤ 10000)
    (hval : ∀ x ∈ hand.val, 0 ≤ x.val ∧ x.val ≤ 1000000000)
    (hg_lb : 1 ≤ group_size.val) (hg_ub : group_size.val ≤ (hand.val.length : ℤ))
    (hlen_lb' : 1 ≤ hand'.val.length) (hlen_ub' : hand'.val.length ≤ 10000)
    (hval' : ∀ x ∈ hand'.val, 0 ≤ x.val ∧ x.val ≤ 1000000000)
    (hg_lb' : 1 ≤ group_size.val) (hg_ub' : group_size.val ≤ (hand'.val.length : ℤ))
    (hlen_eq : hand.val.length = hand'.val.length)
    (hshift : ∃ k : ℤ,
      ∀ p : Std.I64 × Std.I64, p ∈ hand.val.zip hand'.val → p.2.val = p.1.val + k), ∀ r r' : Bool,
      Aegis.IsNStraightHand.is_n_straight_hand hand group_size = ok r →
        Aegis.IsNStraightHand.is_n_straight_hand hand' group_size = ok r' → r = r') := by
  sorry

end AegisSpec.IsNStraightHand
