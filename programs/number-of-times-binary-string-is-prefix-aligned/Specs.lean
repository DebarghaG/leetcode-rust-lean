import Aegis.NumTimesAllBlue.Code.Funs

/-!
# Specifications of `Aegis.NumTimesAllBlue.num_times_all_blue`

LeetCode problem `number-of-times-binary-string-is-prefix-aligned`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.NumTimesAllBlue

def iotaInt (i : Nat) : Finset Int := (Finset.range i).image (fun (k : Nat) => (k : Int) + 1)

def iotaNat (i : Nat) : Finset Nat := (Finset.range i).image (fun (k : Nat) => k + 1)

def flipAt (flips : Slice Std.I64) (j : Nat) : Option Int := flips.val[j]?.map (fun x => x.val)

def prefixSet (flips : Slice Std.I64) (i : Nat) : Finset Int :=
  ((flips.val.take i).map (fun x => x.val)).toFinset

abbrev PrefixAligned (flips : Slice Std.I64) (i : Nat) : Prop := prefixSet flips i = iotaInt i

def alignedIdx (flips : Slice Std.I64) (n : Nat) : Finset Nat :=
  (Finset.range n).filter (fun k => PrefixAligned flips (k + 1))

def prefixMax (flips : Slice Std.I64) (i : Nat) : Option Int :=
  ((flips.val.take i).map (fun x => x.val)).foldr
    (fun x acc => some (match acc with | none => x | some y => max x y)) none

/-- Whenever the function returns a result r, r equals the number of integers i with 1 <= i <= n such that the set {flips[j] | 0 <= j < i} equals the set {1, 2, ..., i}.
  Preconditions: Let n = len(flips). 1 <= n <= 50000, and the multiset {flips[0], ..., flips[n-1]} equals {1, 2, ..., n} (so flips is a permutation of 1..n). -/
theorem spec_1 (flips : Slice Std.I64) (n : Nat)
    (h_len : flips.val.length = n) (h_n_ge : 1 ≤ n) (h_n_le : n ≤ 50000)
    (h_perm : (flips.val.map (fun x => x.val)).Perm ((List.range n).map (fun k => (k : Int) + 1)))
    (r : Std.I64) (h_ret : Aegis.NumTimesAllBlue.num_times_all_blue flips = ok r) :
    r.val = (((Finset.range n).filter (fun k => prefixSet flips (k + 1) = iotaInt (k + 1))).card : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (flips : Slice Std.I64) (n : Nat)
    (h_len : flips.val.length = n) (h_n_ge : 1 ≤ n) (h_n_le : n ≤ 50000)
    (h_perm : (flips.val.map (fun x => x.val)).Perm ((List.range n).map (fun k => (k : Int) + 1)))
    (r : Std.I64) (h_ret : Aegis.NumTimesAllBlue.num_times_all_blue flips = ok r), r.val = (((Finset.range n).filter (fun k => prefixSet flips (k + 1) = iotaInt (k + 1))).card : Int)) := by
  sorry

/-- The function returns a result r for every input satisfying the preconditions; it does not fail, panic, or overflow.
  Preconditions: Let n = len(flips). 1 <= n <= 50000, and the multiset {flips[0], ..., flips[n-1]} equals {1, 2, ..., n}. -/
theorem spec_2 (flips : Slice Std.I64) (n : Nat)
    (h_len : flips.val.length = n) (h_n_ge : 1 ≤ n) (h_n_le : n ≤ 50000)
    (h_perm : (flips.val.map (fun x => x.val)).Perm ((List.range n).map (fun k => (k : Int) + 1))) :
    ∃ r, Aegis.NumTimesAllBlue.num_times_all_blue flips = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (flips : Slice Std.I64) (n : Nat)
    (h_len : flips.val.length = n) (h_n_ge : 1 ≤ n) (h_n_le : n ≤ 50000)
    (h_perm : (flips.val.map (fun x => x.val)).Perm ((List.range n).map (fun k => (k : Int) + 1))), ∃ r, Aegis.NumTimesAllBlue.num_times_all_blue flips = ok r) := by
  sorry

/-- Whenever the function returns a result r, 1 <= r <= n.
  Preconditions: Let n = len(flips). 1 <= n <= 50000, and the multiset {flips[0], ..., flips[n-1]} equals {1, 2, ..., n}. -/
theorem spec_3 (flips : Slice Std.I64) (n : Nat)
    (h_len : flips.val.length = n) (h_n_ge : 1 ≤ n) (h_n_le : n ≤ 50000)
    (h_perm : (flips.val.map (fun x => x.val)).Perm ((List.range n).map (fun k => (k : Int) + 1)))
    (r : Std.I64) (h_ret : Aegis.NumTimesAllBlue.num_times_all_blue flips = ok r) :
    1 ≤ r.val ∧ r.val ≤ (n : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (flips : Slice Std.I64) (n : Nat)
    (h_len : flips.val.length = n) (h_n_ge : 1 ≤ n) (h_n_le : n ≤ 50000)
    (h_perm : (flips.val.map (fun x => x.val)).Perm ((List.range n).map (fun k => (k : Int) + 1)))
    (r : Std.I64) (h_ret : Aegis.NumTimesAllBlue.num_times_all_blue flips = ok r), 1 ≤ r.val ∧ r.val ≤ (n : Int)) := by
  sorry

/-- Whenever the function returns a result r, r equals the number of integers i with 1 <= i <= n such that max{flips[j] | 0 <= j < i} = i.
  Preconditions: Let n = len(flips). 1 <= n <= 50000, and the multiset {flips[0], ..., flips[n-1]} equals {1, 2, ..., n}. -/
theorem spec_4 (flips : Slice Std.I64) (n : Nat)
    (h_len : flips.val.length = n) (h_n_ge : 1 ≤ n) (h_n_le : n ≤ 50000)
    (h_perm : (flips.val.map (fun x => x.val)).Perm ((List.range n).map (fun k => (k : Int) + 1)))
    (r : Std.I64) (h_ret : Aegis.NumTimesAllBlue.num_times_all_blue flips = ok r) :
    r.val = (((Finset.range n).filter (fun k => prefixMax flips (k + 1) = some ((k : Int) + 1))).card : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (flips : Slice Std.I64) (n : Nat)
    (h_len : flips.val.length = n) (h_n_ge : 1 ≤ n) (h_n_le : n ≤ 50000)
    (h_perm : (flips.val.map (fun x => x.val)).Perm ((List.range n).map (fun k => (k : Int) + 1)))
    (r : Std.I64) (h_ret : Aegis.NumTimesAllBlue.num_times_all_blue flips = ok r), r.val = (((Finset.range n).filter (fun k => prefixMax flips (k + 1) = some ((k : Int) + 1))).card : Int)) := by
  sorry

/-- Define pos on {1, ..., n} by: pos(v) is the unique integer p with 1 <= p <= n and flips[p-1] = v. Whenever the function returns a result r, r equals the number of integers i with 1 <= i <= n such that the set {pos(v) | 1 <= v <= i} equals {1, 2, ..., i}.
  Preconditions: Let n = len(flips). 1 <= n <= 50000, and the multiset {flips[0], ..., flips[n-1]} equals {1, 2, ..., n}. -/
theorem spec_5 (flips : Slice Std.I64) (n : Nat)
    (h_len : flips.val.length = n) (h_n_ge : 1 ≤ n) (h_n_le : n ≤ 50000)
    (h_perm : (flips.val.map (fun x => x.val)).Perm ((List.range n).map (fun k => (k : Int) + 1)))
    (pos : Int → Nat)
    (h_pos : ∀ v, 1 ≤ v → v ≤ (n : Int) →
      1 ≤ pos v ∧ pos v ≤ n ∧ flipAt flips (pos v - 1) = some v)
    (r : Std.I64) (h_ret : Aegis.NumTimesAllBlue.num_times_all_blue flips = ok r) :
    r.val = (((Finset.range n).filter
      (fun k => (Finset.range (k + 1)).image (fun (j : Nat) => pos ((j : Int) + 1)) = iotaNat (k + 1))).card : Int) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (flips : Slice Std.I64) (n : Nat)
    (h_len : flips.val.length = n) (h_n_ge : 1 ≤ n) (h_n_le : n ≤ 50000)
    (h_perm : (flips.val.map (fun x => x.val)).Perm ((List.range n).map (fun k => (k : Int) + 1)))
    (pos : Int → Nat)
    (h_pos : ∀ v, 1 ≤ v → v ≤ (n : Int) →
      1 ≤ pos v ∧ pos v ≤ n ∧ flipAt flips (pos v - 1) = some v)
    (r : Std.I64) (h_ret : Aegis.NumTimesAllBlue.num_times_all_blue flips = ok r), r.val = (((Finset.range n).filter
      (fun k => (Finset.range (k + 1)).image (fun (j : Nat) => pos ((j : Int) + 1)) = iotaNat (k + 1))).card : Int)) := by
  sorry

/-- Whenever the function returns a result r, r = n if and only if flips[i] = i+1 for every i with 0 <= i < n (flips is the identity permutation).
  Preconditions: Let n = len(flips). 1 <= n <= 50000, and the multiset {flips[0], ..., flips[n-1]} equals {1, 2, ..., n}. -/
theorem spec_6 (flips : Slice Std.I64) (n : Nat)
    (h_len : flips.val.length = n) (h_n_ge : 1 ≤ n) (h_n_le : n ≤ 50000)
    (h_perm : (flips.val.map (fun x => x.val)).Perm ((List.range n).map (fun k => (k : Int) + 1)))
    (r : Std.I64) (h_ret : Aegis.NumTimesAllBlue.num_times_all_blue flips = ok r) :
    r.val = (n : Int) ↔ ∀ i, i < n → flipAt flips i = some ((i : Int) + 1) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (flips : Slice Std.I64) (n : Nat)
    (h_len : flips.val.length = n) (h_n_ge : 1 ≤ n) (h_n_le : n ≤ 50000)
    (h_perm : (flips.val.map (fun x => x.val)).Perm ((List.range n).map (fun k => (k : Int) + 1)))
    (r : Std.I64) (h_ret : Aegis.NumTimesAllBlue.num_times_all_blue flips = ok r), r.val = (n : Int) ↔ ∀ i, i < n → flipAt flips i = some ((i : Int) + 1)) := by
  sorry

/-- Whenever the function returns a result r, if flips[0] = n then r = 1.
  Preconditions: Let n = len(flips). 1 <= n <= 50000, and the multiset {flips[0], ..., flips[n-1]} equals {1, 2, ..., n}. -/
theorem spec_7 (flips : Slice Std.I64) (n : Nat)
    (h_len : flips.val.length = n) (h_n_ge : 1 ≤ n) (h_n_le : n ≤ 50000)
    (h_perm : (flips.val.map (fun x => x.val)).Perm ((List.range n).map (fun k => (k : Int) + 1)))
    (r : Std.I64) (h_ret : Aegis.NumTimesAllBlue.num_times_all_blue flips = ok r) :
    flipAt flips 0 = some (n : Int) → r.val = 1 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (flips : Slice Std.I64) (n : Nat)
    (h_len : flips.val.length = n) (h_n_ge : 1 ≤ n) (h_n_le : n ≤ 50000)
    (h_perm : (flips.val.map (fun x => x.val)).Perm ((List.range n).map (fun k => (k : Int) + 1)))
    (r : Std.I64) (h_ret : Aegis.NumTimesAllBlue.num_times_all_blue flips = ok r), flipAt flips 0 = some (n : Int) → r.val = 1) := by
  sorry

/-- Whenever the function returns a result r, if n >= 2 and flips[0] = 1 then r >= 2.
  Preconditions: Let n = len(flips). 1 <= n <= 50000, and the multiset {flips[0], ..., flips[n-1]} equals {1, 2, ..., n}. -/
theorem spec_8 (flips : Slice Std.I64) (n : Nat)
    (h_len : flips.val.length = n) (h_n_ge : 1 ≤ n) (h_n_le : n ≤ 50000)
    (h_perm : (flips.val.map (fun x => x.val)).Perm ((List.range n).map (fun k => (k : Int) + 1)))
    (r : Std.I64) (h_ret : Aegis.NumTimesAllBlue.num_times_all_blue flips = ok r) :
    2 ≤ n → flipAt flips 0 = some 1 → 2 ≤ r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (flips : Slice Std.I64) (n : Nat)
    (h_len : flips.val.length = n) (h_n_ge : 1 ≤ n) (h_n_le : n ≤ 50000)
    (h_perm : (flips.val.map (fun x => x.val)).Perm ((List.range n).map (fun k => (k : Int) + 1)))
    (r : Std.I64) (h_ret : Aegis.NumTimesAllBlue.num_times_all_blue flips = ok r), 2 ≤ n → flipAt flips 0 = some 1 → 2 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, if flips[0] != 1 then r <= n-1.
  Preconditions: Let n = len(flips). 1 <= n <= 50000, and the multiset {flips[0], ..., flips[n-1]} equals {1, 2, ..., n}. -/
theorem spec_9 (flips : Slice Std.I64) (n : Nat)
    (h_len : flips.val.length = n) (h_n_ge : 1 ≤ n) (h_n_le : n ≤ 50000)
    (h_perm : (flips.val.map (fun x => x.val)).Perm ((List.range n).map (fun k => (k : Int) + 1)))
    (r : Std.I64) (h_ret : Aegis.NumTimesAllBlue.num_times_all_blue flips = ok r) :
    flipAt flips 0 ≠ some 1 → r.val ≤ (n : Int) - 1 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (flips : Slice Std.I64) (n : Nat)
    (h_len : flips.val.length = n) (h_n_ge : 1 ≤ n) (h_n_le : n ≤ 50000)
    (h_perm : (flips.val.map (fun x => x.val)).Perm ((List.range n).map (fun k => (k : Int) + 1)))
    (r : Std.I64) (h_ret : Aegis.NumTimesAllBlue.num_times_all_blue flips = ok r), flipAt flips 0 ≠ some 1 → r.val ≤ (n : Int) - 1) := by
  sorry

/-- Whenever the function returns a result r, if flips[n-1] = 1 then r = 1.
  Preconditions: Let n = len(flips). 1 <= n <= 50000, and the multiset {flips[0], ..., flips[n-1]} equals {1, 2, ..., n}. -/
theorem spec_10 (flips : Slice Std.I64) (n : Nat)
    (h_len : flips.val.length = n) (h_n_ge : 1 ≤ n) (h_n_le : n ≤ 50000)
    (h_perm : (flips.val.map (fun x => x.val)).Perm ((List.range n).map (fun k => (k : Int) + 1)))
    (r : Std.I64) (h_ret : Aegis.NumTimesAllBlue.num_times_all_blue flips = ok r) :
    flipAt flips (n - 1) = some 1 → r.val = 1 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (flips : Slice Std.I64) (n : Nat)
    (h_len : flips.val.length = n) (h_n_ge : 1 ≤ n) (h_n_le : n ≤ 50000)
    (h_perm : (flips.val.map (fun x => x.val)).Perm ((List.range n).map (fun k => (k : Int) + 1)))
    (r : Std.I64) (h_ret : Aegis.NumTimesAllBlue.num_times_all_blue flips = ok r), flipAt flips (n - 1) = some 1 → r.val = 1) := by
  sorry

end AegisSpec.NumTimesAllBlue
