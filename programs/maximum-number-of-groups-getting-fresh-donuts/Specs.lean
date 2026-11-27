import Aegis.MaxHappyGroups.Code.Funs

/-!
# Specifications of `Aegis.MaxHappyGroups.max_happy_groups`

LeetCode problem `maximum-number-of-groups-getting-fresh-donuts`. Each `spec_<n>` theorem states one property of the function.
-/

set_option autoImplicit false

open Aeneas.Std
open Aeneas.Std.Result
open Aegis.MaxHappyGroups

namespace AegisSpec.MaxHappyGroups

def IsIndexPermutation (p : List Nat) (n : Nat) : Prop :=
  p.length = n ∧ (∀ i ∈ p, i < n) ∧ p.Nodup ∧ (∀ i : Nat, i < n → i ∈ p)

def prefixSum (groups : List I64) (p : List Nat) (j : Nat) : Int :=
  ((p.take j).map (fun k => (groups.getD k default).val)).sum

def happyAt (batchSize : Int) (groups : List I64) (p : List Nat) (j : Nat) : Prop :=
  prefixSum groups p j % batchSize = 0

def happyCount (batchSize : Int) (groups : List I64) (p : List Nat) : Nat :=
  ((List.range p.length).filter (fun j => prefixSum groups p j % batchSize = 0)).length

def bestHappyCount (batchSize : Int) (groups : List I64) : Nat :=
  ((List.range groups.length).permutations.map
    (fun p => happyCount batchSize groups p)).foldr max 0

def regroup (groups : List I64) (q : List Nat) : List I64 :=
  q.map (fun i => groups.getD i default)

def numZeroMod (batchSize : Int) (groups : List I64) : Nat :=
  (groups.filter (fun g => g.val % batchSize = 0)).length

def numNonzeroMod (batchSize : Int) (groups : List I64) : Nat :=
  (groups.filter (fun g => g.val % batchSize ≠ 0)).length

def numEven (groups : List I64) : Nat :=
  (groups.filter (fun g => g.val % 2 = 0)).length

def numOdd (groups : List I64) : Nat :=
  (groups.filter (fun g => g.val % 2 ≠ 0)).length

def totalSize (groups : List I64) : Int :=
  ((groups.map (fun g => g.val)).sum)

def ceilDiv (a b : Nat) : Nat := (a + b - 1) / b

/-- Let n = len(groups). Call a sequence p a permutation of the groups if p is a sequence of the n indices 0,...,n-1 in which every index occurs exactly once. For such p and an index j with 0 <= j < n, the group at position j is happy when (sum_{k=0}^{j-1} groups[p[k]]) mod batchSize = 0, where the empty sum at j=0 is 0. Let H(p) be the number of positions j with 0 <= j < n at which the group is happy. The function returns a result r and r = max { H(p) | p is a permutation of the groups }.
  Preconditions: batchSize is an integer with 1 <= batchSize <= 9. groups is a nonempty slice of 64-bit integers with n = len(groups), 1 <= n <= 30, and 1 <= groups[i] <= 10^9 for every 0 <= i < n. -/
theorem spec_1
    (batchSize : I64) (groups : Slice I64) (n : Nat)
    (hbatch_lo : 1 ≤ batchSize.val) (hbatch_hi : batchSize.val ≤ 9)
    (hn_len : groups.val.length = n) (hn_lo : 1 ≤ n) (hn_hi : n ≤ 30)
    (hgroups : ∀ (i : Nat) (hi : i < groups.val.length),
      1 ≤ (groups.val[i]).val ∧ (groups.val[i]).val ≤ 10 ^ 9) :
    ∃ r : I64, max_happy_groups batchSize groups = ok r ∧
      r.val = (bestHappyCount batchSize.val groups.val : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (batchSize : I64) (groups : Slice I64) (n : Nat)
    (hbatch_lo : 1 ≤ batchSize.val) (hbatch_hi : batchSize.val ≤ 9)
    (hn_len : groups.val.length = n) (hn_lo : 1 ≤ n) (hn_hi : n ≤ 30)
    (hgroups : ∀ (i : Nat) (hi : i < groups.val.length),
      1 ≤ (groups.val[i]).val ∧ (groups.val[i]).val ≤ 10 ^ 9), ∃ r : I64, max_happy_groups batchSize groups = ok r ∧
      r.val = (bestHappyCount batchSize.val groups.val : Int)) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r; it does not fail, panic, overflow, or go out of bounds.
  Preconditions: batchSize is an integer with 1 <= batchSize <= 9. groups is a nonempty slice of 64-bit integers with n = len(groups), 1 <= n <= 30, and 1 <= groups[i] <= 10^9 for every 0 <= i < n. -/
theorem spec_2
    (batchSize : I64) (groups : Slice I64) (n : Nat)
    (hbatch_lo : 1 ≤ batchSize.val) (hbatch_hi : batchSize.val ≤ 9)
    (hn_len : groups.val.length = n) (hn_lo : 1 ≤ n) (hn_hi : n ≤ 30)
    (hgroups : ∀ (i : Nat) (hi : i < groups.val.length),
      1 ≤ (groups.val[i]).val ∧ (groups.val[i]).val ≤ 10 ^ 9) :
    ∃ r : I64, max_happy_groups batchSize groups = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (batchSize : I64) (groups : Slice I64) (n : Nat)
    (hbatch_lo : 1 ≤ batchSize.val) (hbatch_hi : batchSize.val ≤ 9)
    (hn_len : groups.val.length = n) (hn_lo : 1 ≤ n) (hn_hi : n ≤ 30)
    (hgroups : ∀ (i : Nat) (hi : i < groups.val.length),
      1 ≤ (groups.val[i]).val ∧ (groups.val[i]).val ≤ 10 ^ 9), ∃ r : I64, max_happy_groups batchSize groups = ok r) := by
  sorry

/-- Whenever the function returns r for an input satisfying the preconditions, 1 <= r <= len(groups).
  Preconditions: batchSize is an integer with 1 <= batchSize <= 9. groups is a nonempty slice of 64-bit integers with n = len(groups), 1 <= n <= 30, and 1 <= groups[i] <= 10^9 for every 0 <= i < n. -/
theorem spec_3
    (batchSize : I64) (groups : Slice I64) (n : Nat)
    (hbatch_lo : 1 ≤ batchSize.val) (hbatch_hi : batchSize.val ≤ 9)
    (hn_len : groups.val.length = n) (hn_lo : 1 ≤ n) (hn_hi : n ≤ 30)
    (hgroups : ∀ (i : Nat) (hi : i < groups.val.length),
      1 ≤ (groups.val[i]).val ∧ (groups.val[i]).val ≤ 10 ^ 9) :
    ∀ r : I64, max_happy_groups batchSize groups = ok r →
      1 ≤ r.val ∧ r.val ≤ (groups.val.length : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (batchSize : I64) (groups : Slice I64) (n : Nat)
    (hbatch_lo : 1 ≤ batchSize.val) (hbatch_hi : batchSize.val ≤ 9)
    (hn_len : groups.val.length = n) (hn_lo : 1 ≤ n) (hn_hi : n ≤ 30)
    (hgroups : ∀ (i : Nat) (hi : i < groups.val.length),
      1 ≤ (groups.val[i]).val ∧ (groups.val[i]).val ≤ 10 ^ 9), ∀ r : I64, max_happy_groups batchSize groups = ok r →
      1 ≤ r.val ∧ r.val ≤ (groups.val.length : Int)) := by
  sorry

/-- Let z = number of indices i with 0 <= i < len(groups) and groups[i] mod batchSize = 0. Whenever the function returns r, r >= min(len(groups), z + 1).
  Preconditions: batchSize is an integer with 1 <= batchSize <= 9. groups is a nonempty slice of 64-bit integers with n = len(groups), 1 <= n <= 30, and 1 <= groups[i] <= 10^9 for every 0 <= i < n. -/
theorem spec_4
    (batchSize : I64) (groups : Slice I64) (n : Nat)
    (hbatch_lo : 1 ≤ batchSize.val) (hbatch_hi : batchSize.val ≤ 9)
    (hn_len : groups.val.length = n) (hn_lo : 1 ≤ n) (hn_hi : n ≤ 30)
    (hgroups : ∀ (i : Nat) (hi : i < groups.val.length),
      1 ≤ (groups.val[i]).val ∧ (groups.val[i]).val ≤ 10 ^ 9) :
    ∀ r : I64, max_happy_groups batchSize groups = ok r →
      ((min groups.val.length
        (numZeroMod batchSize.val groups.val + 1) : Nat) : Int) ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (batchSize : I64) (groups : Slice I64) (n : Nat)
    (hbatch_lo : 1 ≤ batchSize.val) (hbatch_hi : batchSize.val ≤ 9)
    (hn_len : groups.val.length = n) (hn_lo : 1 ≤ n) (hn_hi : n ≤ 30)
    (hgroups : ∀ (i : Nat) (hi : i < groups.val.length),
      1 ≤ (groups.val[i]).val ∧ (groups.val[i]).val ≤ 10 ^ 9), ∀ r : I64, max_happy_groups batchSize groups = ok r →
      ((min groups.val.length
        (numZeroMod batchSize.val groups.val + 1) : Nat) : Int) ≤ r.val) := by
  sorry

/-- Let z = number of indices i with 0 <= i < len(groups) and groups[i] mod batchSize = 0, and let m = len(groups) - z. Whenever the function returns r, r <= z + ceil(m / 2), where ceil(m / 2) = (m + 1) div 2.
  Preconditions: batchSize is an integer with 1 <= batchSize <= 9. groups is a nonempty slice of 64-bit integers with n = len(groups), 1 <= n <= 30, and 1 <= groups[i] <= 10^9 for every 0 <= i < n. -/
theorem spec_5
    (batchSize : I64) (groups : Slice I64) (n : Nat)
    (hbatch_lo : 1 ≤ batchSize.val) (hbatch_hi : batchSize.val ≤ 9)
    (hn_len : groups.val.length = n) (hn_lo : 1 ≤ n) (hn_hi : n ≤ 30)
    (hgroups : ∀ (i : Nat) (hi : i < groups.val.length),
      1 ≤ (groups.val[i]).val ∧ (groups.val[i]).val ≤ 10 ^ 9) :
    ∀ r : I64, max_happy_groups batchSize groups = ok r →
      r.val ≤ (numZeroMod batchSize.val groups.val : Int) +
        (ceilDiv (groups.val.length - numZeroMod batchSize.val groups.val) 2 : Int) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (batchSize : I64) (groups : Slice I64) (n : Nat)
    (hbatch_lo : 1 ≤ batchSize.val) (hbatch_hi : batchSize.val ≤ 9)
    (hn_len : groups.val.length = n) (hn_lo : 1 ≤ n) (hn_hi : n ≤ 30)
    (hgroups : ∀ (i : Nat) (hi : i < groups.val.length),
      1 ≤ (groups.val[i]).val ∧ (groups.val[i]).val ≤ 10 ^ 9), ∀ r : I64, max_happy_groups batchSize groups = ok r →
      r.val ≤ (numZeroMod batchSize.val groups.val : Int) +
        (ceilDiv (groups.val.length - numZeroMod batchSize.val groups.val) 2 : Int)) := by
  sorry

/-- Let m = number of indices i with 0 <= i < len(groups) and groups[i] mod batchSize != 0. Whenever the function returns r, r = len(groups) if and only if m <= 1.
  Preconditions: batchSize is an integer with 1 <= batchSize <= 9. groups is a nonempty slice of 64-bit integers with n = len(groups), 1 <= n <= 30, and 1 <= groups[i] <= 10^9 for every 0 <= i < n. -/
theorem spec_6
    (batchSize : I64) (groups : Slice I64) (n : Nat)
    (hbatch_lo : 1 ≤ batchSize.val) (hbatch_hi : batchSize.val ≤ 9)
    (hn_len : groups.val.length = n) (hn_lo : 1 ≤ n) (hn_hi : n ≤ 30)
    (hgroups : ∀ (i : Nat) (hi : i < groups.val.length),
      1 ≤ (groups.val[i]).val ∧ (groups.val[i]).val ≤ 10 ^ 9) :
    ∀ r : I64, max_happy_groups batchSize groups = ok r →
      (r.val = (groups.val.length : Int) ↔
        numNonzeroMod batchSize.val groups.val ≤ 1) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (batchSize : I64) (groups : Slice I64) (n : Nat)
    (hbatch_lo : 1 ≤ batchSize.val) (hbatch_hi : batchSize.val ≤ 9)
    (hn_len : groups.val.length = n) (hn_lo : 1 ≤ n) (hn_hi : n ≤ 30)
    (hgroups : ∀ (i : Nat) (hi : i < groups.val.length),
      1 ≤ (groups.val[i]).val ∧ (groups.val[i]).val ≤ 10 ^ 9), ∀ r : I64, max_happy_groups batchSize groups = ok r →
      (r.val = (groups.val.length : Int) ↔
        numNonzeroMod batchSize.val groups.val ≤ 1)) := by
  sorry

/-- Let m = number of indices i with 0 <= i < len(groups) and groups[i] mod batchSize != 0. If m = 2, then whenever the function returns r, r = len(groups) - 1.
  Preconditions: batchSize is an integer with 1 <= batchSize <= 9. groups is a nonempty slice of 64-bit integers with n = len(groups), 1 <= n <= 30, and 1 <= groups[i] <= 10^9 for every 0 <= i < n. -/
theorem spec_7
    (batchSize : I64) (groups : Slice I64) (n : Nat)
    (hbatch_lo : 1 ≤ batchSize.val) (hbatch_hi : batchSize.val ≤ 9)
    (hn_len : groups.val.length = n) (hn_lo : 1 ≤ n) (hn_hi : n ≤ 30)
    (hgroups : ∀ (i : Nat) (hi : i < groups.val.length),
      1 ≤ (groups.val[i]).val ∧ (groups.val[i]).val ≤ 10 ^ 9)
    (hm : numNonzeroMod batchSize.val groups.val = 2) :
    ∀ r : I64, max_happy_groups batchSize groups = ok r →
      r.val = (groups.val.length : Int) - 1 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (batchSize : I64) (groups : Slice I64) (n : Nat)
    (hbatch_lo : 1 ≤ batchSize.val) (hbatch_hi : batchSize.val ≤ 9)
    (hn_len : groups.val.length = n) (hn_lo : 1 ≤ n) (hn_hi : n ≤ 30)
    (hgroups : ∀ (i : Nat) (hi : i < groups.val.length),
      1 ≤ (groups.val[i]).val ∧ (groups.val[i]).val ≤ 10 ^ 9)
    (hm : numNonzeroMod batchSize.val groups.val = 2), ∀ r : I64, max_happy_groups batchSize groups = ok r →
      r.val = (groups.val.length : Int) - 1) := by
  sorry

/-- Assume batchSize = 2. Let z = number of even values among groups[i] and m = number of odd values among groups[i], so z + m = len(groups). Whenever the function returns r, r = z + ceil(m / 2), where ceil(m / 2) = (m + 1) div 2.
  Preconditions: batchSize is an integer with 1 <= batchSize <= 9. groups is a nonempty slice of 64-bit integers with n = len(groups), 1 <= n <= 30, and 1 <= groups[i] <= 10^9 for every 0 <= i < n. -/
theorem spec_8
    (batchSize : I64) (groups : Slice I64) (n : Nat)
    (hbatch_lo : 1 ≤ batchSize.val) (hbatch_hi : batchSize.val ≤ 9)
    (hn_len : groups.val.length = n) (hn_lo : 1 ≤ n) (hn_hi : n ≤ 30)
    (hgroups : ∀ (i : Nat) (hi : i < groups.val.length),
      1 ≤ (groups.val[i]).val ∧ (groups.val[i]).val ≤ 10 ^ 9)
    (hbatch_two : batchSize.val = 2) :
    ∀ r : I64, max_happy_groups batchSize groups = ok r →
      r.val = (numEven groups.val : Int) +
        (ceilDiv (numOdd groups.val) 2 : Int) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (batchSize : I64) (groups : Slice I64) (n : Nat)
    (hbatch_lo : 1 ≤ batchSize.val) (hbatch_hi : batchSize.val ≤ 9)
    (hn_len : groups.val.length = n) (hn_lo : 1 ≤ n) (hn_hi : n ≤ 30)
    (hgroups : ∀ (i : Nat) (hi : i < groups.val.length),
      1 ≤ (groups.val[i]).val ∧ (groups.val[i]).val ≤ 10 ^ 9)
    (hbatch_two : batchSize.val = 2), ∀ r : I64, max_happy_groups batchSize groups = ok r →
      r.val = (numEven groups.val : Int) +
        (ceilDiv (numOdd groups.val) 2 : Int)) := by
  sorry

/-- If groups[i] = 1 for every index i with 0 <= i < len(groups), then whenever the function returns r, r = ceil(len(groups) / batchSize), where ceil(n / batchSize) = (n + batchSize - 1) div batchSize.
  Preconditions: batchSize is an integer with 1 <= batchSize <= 9. groups is a nonempty slice of 64-bit integers with n = len(groups), 1 <= n <= 30, and 1 <= groups[i] <= 10^9 for every 0 <= i < n. -/
theorem spec_9
    (batchSize : I64) (groups : Slice I64) (n : Nat)
    (hbatch_lo : 1 ≤ batchSize.val) (hbatch_hi : batchSize.val ≤ 9)
    (hn_len : groups.val.length = n) (hn_lo : 1 ≤ n) (hn_hi : n ≤ 30)
    (hgroups : ∀ (i : Nat) (hi : i < groups.val.length),
      1 ≤ (groups.val[i]).val ∧ (groups.val[i]).val ≤ 10 ^ 9)
    (hall_one : ∀ (i : Nat) (hi : i < groups.val.length),
      (groups.val[i]).val = 1) :
    ∀ r : I64, max_happy_groups batchSize groups = ok r →
      r.val = (ceilDiv groups.val.length batchSize.val.toNat : Int) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (batchSize : I64) (groups : Slice I64) (n : Nat)
    (hbatch_lo : 1 ≤ batchSize.val) (hbatch_hi : batchSize.val ≤ 9)
    (hn_len : groups.val.length = n) (hn_lo : 1 ≤ n) (hn_hi : n ≤ 30)
    (hgroups : ∀ (i : Nat) (hi : i < groups.val.length),
      1 ≤ (groups.val[i]).val ∧ (groups.val[i]).val ≤ 10 ^ 9)
    (hall_one : ∀ (i : Nat) (hi : i < groups.val.length),
      (groups.val[i]).val = 1), ∀ r : I64, max_happy_groups batchSize groups = ok r →
      r.val = (ceilDiv groups.val.length batchSize.val.toNat : Int)) := by
  sorry

/-- Let S = sum_{i=0}^{len(groups)-1} groups[i]. If S < batchSize, then whenever the function returns r, r = 1.
  Preconditions: batchSize is an integer with 1 <= batchSize <= 9. groups is a nonempty slice of 64-bit integers with n = len(groups), 1 <= n <= 30, and 1 <= groups[i] <= 10^9 for every 0 <= i < n. -/
theorem spec_10
    (batchSize : I64) (groups : Slice I64) (n : Nat)
    (hbatch_lo : 1 ≤ batchSize.val) (hbatch_hi : batchSize.val ≤ 9)
    (hn_len : groups.val.length = n) (hn_lo : 1 ≤ n) (hn_hi : n ≤ 30)
    (hgroups : ∀ (i : Nat) (hi : i < groups.val.length),
      1 ≤ (groups.val[i]).val ∧ (groups.val[i]).val ≤ 10 ^ 9)
    (hS : totalSize groups.val < batchSize.val) :
    ∀ r : I64, max_happy_groups batchSize groups = ok r → r.val = 1 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (batchSize : I64) (groups : Slice I64) (n : Nat)
    (hbatch_lo : 1 ≤ batchSize.val) (hbatch_hi : batchSize.val ≤ 9)
    (hn_len : groups.val.length = n) (hn_lo : 1 ≤ n) (hn_hi : n ≤ 30)
    (hgroups : ∀ (i : Nat) (hi : i < groups.val.length),
      1 ≤ (groups.val[i]).val ∧ (groups.val[i]).val ≤ 10 ^ 9)
    (hS : totalSize groups.val < batchSize.val), ∀ r : I64, max_happy_groups batchSize groups = ok r → r.val = 1) := by
  sorry

/-- If r is the result on (batchSize, groups) and r' is the result on (batchSize, groups'), then r' = r + 1.
  Preconditions: batchSize is an integer with 1 <= batchSize <= 9. groups is a nonempty slice of 64-bit integers with n = len(groups), 1 <= n <= 30, and 1 <= groups[i] <= 10^9 for every 0 <= i < n. Let g be an integer with 1 <= g <= 10^9 and g mod batchSize = 0. Let n = len(groups) and assume n <= 29. Let groups' be the slice of length n+1 with groups'[i] = groups[i] for 0 <= i < n and groups'[n] = g. -/
theorem spec_11
    (batchSize : I64) (groups groups' : Slice I64) (g : I64) (n : Nat)
    (hbatch_lo : 1 ≤ batchSize.val) (hbatch_hi : batchSize.val ≤ 9)
    (hn_len : groups.val.length = n) (hn_lo : 1 ≤ n) (hn_hi : n ≤ 29)
    (hgroups : ∀ (i : Nat) (hi : i < groups.val.length),
      1 ≤ (groups.val[i]).val ∧ (groups.val[i]).val ≤ 10 ^ 9)
    (hg_lo : 1 ≤ g.val) (hg_hi : g.val ≤ 10 ^ 9)
    (hg_mod : g.val % batchSize.val = 0)
    (hgroups' : groups'.val = groups.val ++ [g]) :
    ∀ r r' : I64, max_happy_groups batchSize groups = ok r →
      max_happy_groups batchSize groups' = ok r' → r'.val = r.val + 1 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (batchSize : I64) (groups groups' : Slice I64) (g : I64) (n : Nat)
    (hbatch_lo : 1 ≤ batchSize.val) (hbatch_hi : batchSize.val ≤ 9)
    (hn_len : groups.val.length = n) (hn_lo : 1 ≤ n) (hn_hi : n ≤ 29)
    (hgroups : ∀ (i : Nat) (hi : i < groups.val.length),
      1 ≤ (groups.val[i]).val ∧ (groups.val[i]).val ≤ 10 ^ 9)
    (hg_lo : 1 ≤ g.val) (hg_hi : g.val ≤ 10 ^ 9)
    (hg_mod : g.val % batchSize.val = 0)
    (hgroups' : groups'.val = groups.val ++ [g]), ∀ r r' : I64, max_happy_groups batchSize groups = ok r →
      max_happy_groups batchSize groups' = ok r' → r'.val = r.val + 1) := by
  sorry

/-- If r is the result on (batchSize, groups) and r' is the result on (batchSize, groups'), then r' = r.
  Preconditions: batchSize is an integer with 1 <= batchSize <= 9. groups is a nonempty slice of 64-bit integers with n = len(groups), 1 <= n <= 30, and 1 <= groups[i] <= 10^9 for every 0 <= i < n. Let q be a permutation of the indices 0,...,n-1, and let groups' be the slice of length n with groups'[j] = groups[q[j]] for every 0 <= j < n. -/
theorem spec_12
    (batchSize : I64) (groups groups' : Slice I64) (q : List Nat) (n : Nat)
    (hbatch_lo : 1 ≤ batchSize.val) (hbatch_hi : batchSize.val ≤ 9)
    (hn_len : groups.val.length = n) (hn_lo : 1 ≤ n) (hn_hi : n ≤ 30)
    (hgroups : ∀ (i : Nat) (hi : i < groups.val.length),
      1 ≤ (groups.val[i]).val ∧ (groups.val[i]).val ≤ 10 ^ 9)
    (hq : IsIndexPermutation q n)
    (hgroups' : groups'.val = regroup groups.val q) :
    ∀ r r' : I64, max_happy_groups batchSize groups = ok r →
      max_happy_groups batchSize groups' = ok r' → r'.val = r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (batchSize : I64) (groups groups' : Slice I64) (q : List Nat) (n : Nat)
    (hbatch_lo : 1 ≤ batchSize.val) (hbatch_hi : batchSize.val ≤ 9)
    (hn_len : groups.val.length = n) (hn_lo : 1 ≤ n) (hn_hi : n ≤ 30)
    (hgroups : ∀ (i : Nat) (hi : i < groups.val.length),
      1 ≤ (groups.val[i]).val ∧ (groups.val[i]).val ≤ 10 ^ 9)
    (hq : IsIndexPermutation q n)
    (hgroups' : groups'.val = regroup groups.val q), ∀ r r' : I64, max_happy_groups batchSize groups = ok r →
      max_happy_groups batchSize groups' = ok r' → r'.val = r.val) := by
  sorry

/-- Let n = len(groups). A permutation p is a sequence of the n indices 0,...,n-1 in which every index occurs exactly once. Define H(p) = the number of indices j with 0 <= j < n such that (sum_{k=0}^{j-1} groups[p[k]]) mod batchSize = 0, with the empty sum at j=0 equal to 0. Whenever the function returns r, there exists a permutation p of 0,...,n-1 with H(p) = r.
  Preconditions: batchSize is an integer with 1 <= batchSize <= 9. groups is a nonempty slice of 64-bit integers with n = len(groups), 1 <= n <= 30, and 1 <= groups[i] <= 10^9 for every 0 <= i < n. -/
theorem spec_13
    (batchSize : I64) (groups : Slice I64) (n : Nat)
    (hbatch_lo : 1 ≤ batchSize.val) (hbatch_hi : batchSize.val ≤ 9)
    (hn_len : groups.val.length = n) (hn_lo : 1 ≤ n) (hn_hi : n ≤ 30)
    (hgroups : ∀ (i : Nat) (hi : i < groups.val.length),
      1 ≤ (groups.val[i]).val ∧ (groups.val[i]).val ≤ 10 ^ 9) :
    ∀ r : I64, max_happy_groups batchSize groups = ok r →
      ∃ p : List Nat, IsIndexPermutation p n ∧
        (happyCount batchSize.val groups.val p : Int) = r.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (batchSize : I64) (groups : Slice I64) (n : Nat)
    (hbatch_lo : 1 ≤ batchSize.val) (hbatch_hi : batchSize.val ≤ 9)
    (hn_len : groups.val.length = n) (hn_lo : 1 ≤ n) (hn_hi : n ≤ 30)
    (hgroups : ∀ (i : Nat) (hi : i < groups.val.length),
      1 ≤ (groups.val[i]).val ∧ (groups.val[i]).val ≤ 10 ^ 9), ∀ r : I64, max_happy_groups batchSize groups = ok r →
      ∃ p : List Nat, IsIndexPermutation p n ∧
        (happyCount batchSize.val groups.val p : Int) = r.val) := by
  sorry

end AegisSpec.MaxHappyGroups
