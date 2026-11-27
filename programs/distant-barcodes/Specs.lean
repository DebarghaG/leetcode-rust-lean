import Aegis.RearrangeBarcodes.Code.Funs

/-!
# Specifications of `Aegis.RearrangeBarcodes.rearrange_barcodes`

LeetCode problem `distant-barcodes`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.RearrangeBarcodes (rearrange_barcodes)

namespace AegisSpec.RearrangeBarcodes

def toInts (xs : List Std.I64) : List Int := xs.map (fun x => x.val)

def count (xs : List Int) (v : Int) : Nat :=
  (xs.filter (fun x => decide (x = v))).length

def occurs (xs : List Int) (v : Int) : Prop := 0 < count xs v

def NoAdjacentEq (xs : List Int) : Prop :=
  ∀ (i : Nat) (_ : i + 1 < xs.length), xs[i] ≠ xs[i + 1]

def Admissible (xs : List Int) : Prop :=
  ∀ v : Int, count xs v ≤ (xs.length + 1) / 2

/-- The function returns a result r and r is a valid rearrangement of barcodes with no equal adjacent entries: len(r) = n, for every integer v count(r,v) = count(barcodes,v), and for every i with 0 <= i and i+1 < len(r), r[i] != r[i+1].
  Preconditions: Let n = len(barcodes). The input satisfies 1 <= n <= 10000; for every i with 0 <= i < n, 1 <= barcodes[i] <= 10000; and barcodes admits at least one rearrangement with no equal adjacent entries (equivalently, for every integer v, count(barcodes,v) <= ceil(n/2), where count(xs,v) is the number of indices j with 0 <= j < len(xs) and xs[j]=v). -/
theorem spec_1 (barcodes : Slice Std.I64)
    (hne : 1 ≤ barcodes.val.length)
    (hmax : barcodes.val.length ≤ 10000)
    (hbounds : ∀ (i : Nat) (_ : i < barcodes.val.length),
      1 ≤ barcodes.val[i].val ∧ barcodes.val[i].val ≤ 10000)
    (hadm : Admissible (toInts barcodes.val)) :
    ∃ r : alloc.vec.Vec Std.I64,
      rearrange_barcodes barcodes = ok r ∧
        r.val.length = barcodes.val.length ∧
        (∀ v : Int, count (toInts r.val) v = count (toInts barcodes.val) v) ∧
        NoAdjacentEq (toInts r.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (barcodes : Slice Std.I64)
    (hne : 1 ≤ barcodes.val.length)
    (hmax : barcodes.val.length ≤ 10000)
    (hbounds : ∀ (i : Nat) (_ : i < barcodes.val.length),
      1 ≤ barcodes.val[i].val ∧ barcodes.val[i].val ≤ 10000)
    (hadm : Admissible (toInts barcodes.val)), ∃ r : alloc.vec.Vec Std.I64,
      rearrange_barcodes barcodes = ok r ∧
        r.val.length = barcodes.val.length ∧
        (∀ v : Int, count (toInts r.val) v = count (toInts barcodes.val) v) ∧
        NoAdjacentEq (toInts r.val)) := by
  sorry

/-- The function returns a result r; in particular, it does not panic, overflow, or return an error on any input satisfying the preconditions.
  Preconditions: Let n = len(barcodes). The input satisfies 1 <= n <= 10000; for every i with 0 <= i < n, 1 <= barcodes[i] <= 10000; and barcodes admits at least one rearrangement with no equal adjacent entries (equivalently, for every integer v, count(barcodes,v) <= ceil(n/2)). -/
theorem spec_2 (barcodes : Slice Std.I64)
    (hne : 1 ≤ barcodes.val.length)
    (hmax : barcodes.val.length ≤ 10000)
    (hbounds : ∀ (i : Nat) (_ : i < barcodes.val.length),
      1 ≤ barcodes.val[i].val ∧ barcodes.val[i].val ≤ 10000)
    (hadm : Admissible (toInts barcodes.val)) :
    ∃ r : alloc.vec.Vec Std.I64, rearrange_barcodes barcodes = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (barcodes : Slice Std.I64)
    (hne : 1 ≤ barcodes.val.length)
    (hmax : barcodes.val.length ≤ 10000)
    (hbounds : ∀ (i : Nat) (_ : i < barcodes.val.length),
      1 ≤ barcodes.val[i].val ∧ barcodes.val[i].val ≤ 10000)
    (hadm : Admissible (toInts barcodes.val)), ∃ r : alloc.vec.Vec Std.I64, rearrange_barcodes barcodes = ok r) := by
  sorry

/-- Whenever the function returns a result r, len(r) = len(barcodes).
  Preconditions: Let n = len(barcodes). The input satisfies 1 <= n <= 10000; for every i with 0 <= i < n, 1 <= barcodes[i] <= 10000; and barcodes admits at least one rearrangement with no equal adjacent entries (equivalently, for every integer v, count(barcodes,v) <= ceil(n/2)). -/
theorem spec_3 (barcodes : Slice Std.I64)
    (hne : 1 ≤ barcodes.val.length)
    (hmax : barcodes.val.length ≤ 10000)
    (hbounds : ∀ (i : Nat) (_ : i < barcodes.val.length),
      1 ≤ barcodes.val[i].val ∧ barcodes.val[i].val ≤ 10000)
    (hadm : Admissible (toInts barcodes.val)) :
    ∀ r : alloc.vec.Vec Std.I64, rearrange_barcodes barcodes = ok r →
      r.val.length = barcodes.val.length := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (barcodes : Slice Std.I64)
    (hne : 1 ≤ barcodes.val.length)
    (hmax : barcodes.val.length ≤ 10000)
    (hbounds : ∀ (i : Nat) (_ : i < barcodes.val.length),
      1 ≤ barcodes.val[i].val ∧ barcodes.val[i].val ≤ 10000)
    (hadm : Admissible (toInts barcodes.val)), ∀ r : alloc.vec.Vec Std.I64, rearrange_barcodes barcodes = ok r →
      r.val.length = barcodes.val.length) := by
  sorry

/-- Whenever the function returns a result r, for every integer v, count(r,v) = count(barcodes,v).
  Preconditions: Let n = len(barcodes). The input satisfies 1 <= n <= 10000; for every i with 0 <= i < n, 1 <= barcodes[i] <= 10000; and barcodes admits at least one rearrangement with no equal adjacent entries (equivalently, for every integer v, count(barcodes,v) <= ceil(n/2), where count(xs,v) is the number of indices j with 0 <= j < len(xs) and xs[j]=v). -/
theorem spec_4 (barcodes : Slice Std.I64)
    (hne : 1 ≤ barcodes.val.length)
    (hmax : barcodes.val.length ≤ 10000)
    (hbounds : ∀ (i : Nat) (_ : i < barcodes.val.length),
      1 ≤ barcodes.val[i].val ∧ barcodes.val[i].val ≤ 10000)
    (hadm : Admissible (toInts barcodes.val)) :
    ∀ r : alloc.vec.Vec Std.I64, rearrange_barcodes barcodes = ok r →
      ∀ v : Int, count (toInts r.val) v = count (toInts barcodes.val) v := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (barcodes : Slice Std.I64)
    (hne : 1 ≤ barcodes.val.length)
    (hmax : barcodes.val.length ≤ 10000)
    (hbounds : ∀ (i : Nat) (_ : i < barcodes.val.length),
      1 ≤ barcodes.val[i].val ∧ barcodes.val[i].val ≤ 10000)
    (hadm : Admissible (toInts barcodes.val)), ∀ r : alloc.vec.Vec Std.I64, rearrange_barcodes barcodes = ok r →
      ∀ v : Int, count (toInts r.val) v = count (toInts barcodes.val) v) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i and i+1 < len(r), r[i] != r[i+1].
  Preconditions: Let n = len(barcodes). The input satisfies 1 <= n <= 10000; for every i with 0 <= i < n, 1 <= barcodes[i] <= 10000; and barcodes admits at least one rearrangement with no equal adjacent entries (equivalently, for every integer v, count(barcodes,v) <= ceil(n/2)). -/
theorem spec_5 (barcodes : Slice Std.I64)
    (hne : 1 ≤ barcodes.val.length)
    (hmax : barcodes.val.length ≤ 10000)
    (hbounds : ∀ (i : Nat) (_ : i < barcodes.val.length),
      1 ≤ barcodes.val[i].val ∧ barcodes.val[i].val ≤ 10000)
    (hadm : Admissible (toInts barcodes.val)) :
    ∀ r : alloc.vec.Vec Std.I64, rearrange_barcodes barcodes = ok r →
      NoAdjacentEq (toInts r.val) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (barcodes : Slice Std.I64)
    (hne : 1 ≤ barcodes.val.length)
    (hmax : barcodes.val.length ≤ 10000)
    (hbounds : ∀ (i : Nat) (_ : i < barcodes.val.length),
      1 ≤ barcodes.val[i].val ∧ barcodes.val[i].val ≤ 10000)
    (hadm : Admissible (toInts barcodes.val)), ∀ r : alloc.vec.Vec Std.I64, rearrange_barcodes barcodes = ok r →
      NoAdjacentEq (toInts r.val)) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(r), 1 <= r[i] <= 10000.
  Preconditions: Let n = len(barcodes). The input satisfies 1 <= n <= 10000; for every i with 0 <= i < n, 1 <= barcodes[i] <= 10000; and barcodes admits at least one rearrangement with no equal adjacent entries (equivalently, for every integer v, count(barcodes,v) <= ceil(n/2)). -/
theorem spec_6 (barcodes : Slice Std.I64)
    (hne : 1 ≤ barcodes.val.length)
    (hmax : barcodes.val.length ≤ 10000)
    (hbounds : ∀ (i : Nat) (_ : i < barcodes.val.length),
      1 ≤ barcodes.val[i].val ∧ barcodes.val[i].val ≤ 10000)
    (hadm : Admissible (toInts barcodes.val)) :
    ∀ r : alloc.vec.Vec Std.I64, rearrange_barcodes barcodes = ok r →
      ∀ (i : Nat) (_ : i < r.val.length), 1 ≤ r.val[i].val ∧ r.val[i].val ≤ 10000 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (barcodes : Slice Std.I64)
    (hne : 1 ≤ barcodes.val.length)
    (hmax : barcodes.val.length ≤ 10000)
    (hbounds : ∀ (i : Nat) (_ : i < barcodes.val.length),
      1 ≤ barcodes.val[i].val ∧ barcodes.val[i].val ≤ 10000)
    (hadm : Admissible (toInts barcodes.val)), ∀ r : alloc.vec.Vec Std.I64, rearrange_barcodes barcodes = ok r →
      ∀ (i : Nat) (_ : i < r.val.length), 1 ≤ r.val[i].val ∧ r.val[i].val ≤ 10000) := by
  sorry

/-- Whenever the function returns a result r, for every integer v, v occurs in r if and only if v occurs in barcodes; that is, count(r,v) > 0 if and only if count(barcodes,v) > 0.
  Preconditions: Let n = len(barcodes). The input satisfies 1 <= n <= 10000; for every i with 0 <= i < n, 1 <= barcodes[i] <= 10000; and barcodes admits at least one rearrangement with no equal adjacent entries (equivalently, for every integer v, count(barcodes,v) <= ceil(n/2), where count(xs,v) is the number of indices j with 0 <= j < len(xs) and xs[j]=v). -/
theorem spec_7 (barcodes : Slice Std.I64)
    (hne : 1 ≤ barcodes.val.length)
    (hmax : barcodes.val.length ≤ 10000)
    (hbounds : ∀ (i : Nat) (_ : i < barcodes.val.length),
      1 ≤ barcodes.val[i].val ∧ barcodes.val[i].val ≤ 10000)
    (hadm : Admissible (toInts barcodes.val)) :
    ∀ r : alloc.vec.Vec Std.I64, rearrange_barcodes barcodes = ok r →
      ∀ v : Int, occurs (toInts r.val) v ↔ occurs (toInts barcodes.val) v := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (barcodes : Slice Std.I64)
    (hne : 1 ≤ barcodes.val.length)
    (hmax : barcodes.val.length ≤ 10000)
    (hbounds : ∀ (i : Nat) (_ : i < barcodes.val.length),
      1 ≤ barcodes.val[i].val ∧ barcodes.val[i].val ≤ 10000)
    (hadm : Admissible (toInts barcodes.val)), ∀ r : alloc.vec.Vec Std.I64, rearrange_barcodes barcodes = ok r →
      ∀ v : Int, occurs (toInts r.val) v ↔ occurs (toInts barcodes.val) v) := by
  sorry

/-- Let v be any integer with count(barcodes,v) = (len(barcodes)+1)/2. Whenever the function returns a result r, len(r) = len(barcodes) and for every i with 0 <= i < len(r), r[i] = v if and only if i is even.
  Preconditions: Let n = len(barcodes). The input satisfies 1 <= n <= 10000; for every i with 0 <= i < n, 1 <= barcodes[i] <= 10000; barcodes admits at least one rearrangement with no equal adjacent entries; n is odd; and there exists an integer v such that count(barcodes,v) = (n+1)/2, where count(xs,v) is the number of indices j with 0 <= j < len(xs) and xs[j]=v. -/
theorem spec_8 (barcodes : Slice Std.I64)
    (hne : 1 ≤ barcodes.val.length)
    (hmax : barcodes.val.length ≤ 10000)
    (hbounds : ∀ (i : Nat) (_ : i < barcodes.val.length),
      1 ≤ barcodes.val[i].val ∧ barcodes.val[i].val ≤ 10000)
    (hadm : Admissible (toInts barcodes.val))
    (hodd : barcodes.val.length % 2 = 1)
    (hexists : ∃ v : Int, count (toInts barcodes.val) v = (barcodes.val.length + 1) / 2) :
    ∀ v : Int, count (toInts barcodes.val) v = (barcodes.val.length + 1) / 2 →
      ∀ r : alloc.vec.Vec Std.I64, rearrange_barcodes barcodes = ok r →
        r.val.length = barcodes.val.length ∧
          ∀ (i : Nat) (_ : i < r.val.length), (r.val[i].val = v ↔ i % 2 = 0) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (barcodes : Slice Std.I64)
    (hne : 1 ≤ barcodes.val.length)
    (hmax : barcodes.val.length ≤ 10000)
    (hbounds : ∀ (i : Nat) (_ : i < barcodes.val.length),
      1 ≤ barcodes.val[i].val ∧ barcodes.val[i].val ≤ 10000)
    (hadm : Admissible (toInts barcodes.val))
    (hodd : barcodes.val.length % 2 = 1)
    (hexists : ∃ v : Int, count (toInts barcodes.val) v = (barcodes.val.length + 1) / 2), ∀ v : Int, count (toInts barcodes.val) v = (barcodes.val.length + 1) / 2 →
      ∀ r : alloc.vec.Vec Std.I64, rearrange_barcodes barcodes = ok r →
        r.val.length = barcodes.val.length ∧
          ∀ (i : Nat) (_ : i < r.val.length), (r.val[i].val = v ↔ i % 2 = 0)) := by
  sorry

end AegisSpec.RearrangeBarcodes
