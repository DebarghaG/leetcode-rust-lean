import Aegis.FindPeaks.Code.Funs

/-!
# Specifications of `Aegis.FindPeaks.find_peaks`

LeetCode problem `find-the-peaks`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.FindPeaks

  def vals (l : List Std.I64) : List Int := l.map (fun x => x.val)

  def vals_slice (mountain : Slice Std.I64) : List Int := vals mountain.val

  def vals_vec (v : alloc.vec.Vec Std.I64) : List Int := vals v.val

  def el (l : List Int) (i : Nat) : Int := l.getD i 0

  def elI (l : List Int) (i : Int) : Int := l.getD i.toNat 0

  def mget (mountain : Slice Std.I64) (i : Nat) : Int := el (vals_slice mountain) i

  def rget (r : alloc.vec.Vec Std.I64) (k : Nat) : Int := el (vals_vec r) k

  def occ (l : List Int) (x : Int) : Nat := (l.filter (fun y => decide (y = x))).length

  def Occurs (l : List Int) (x : Int) : Prop := x ∈ l

  def isPeak (l : List Int) (i : Int) : Bool :=
    decide (1 ≤ i) && decide (i + 1 < (l.length : Int)) &&
      decide (elI l (i - 1) < elI l i) && decide (elI l (i + 1) < elI l i)

  def IsPeak (l : List Int) (i : Int) : Prop := isPeak l i = true

  def peakIndices (l : List Int) : List Nat :=
    (List.range l.length).filter (fun i => isPeak l (i : Int))

  /-- The function returns a result r such that r is a permutation of the list [i | 0 <= i < len(mountain), 1 <= i, i < len(mountain)-1, mountain[i-1] < mountain[i], mountain[i+1] < mountain[i]]; equivalently, for every integer i, the number of occurrences of i as an element of r is 1 if 1 <= i < len(mountain)-1 and mountain[i-1] < mountain[i] and mountain[i+1] < mountain[i], and is 0 otherwise.
    Preconditions: len(mountain) >= 3 and len(mountain) <= 100, and for every i with 0 <= i < len(mountain), 1 <= mountain[i] and mountain[i] <= 100. -/
  theorem spec_1 (mountain : Slice Std.I64)
      (hlen_lo : 3 ≤ mountain.val.length)
      (hlen_hi : mountain.val.length ≤ 100)
      (hval : ∀ i, i < mountain.val.length → 1 ≤ mget mountain i ∧ mget mountain i ≤ 100) :
      ∃ r : alloc.vec.Vec Std.I64,
        Aegis.FindPeaks.find_peaks mountain = ok r ∧
        List.Perm (vals_vec r) ((peakIndices (vals_slice mountain)).map (fun i => (i : Int))) ∧
        (∀ i : Int, occ (vals_vec r) i =
          if isPeak (vals_slice mountain) i then 1 else 0) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (mountain : Slice Std.I64)
        (hlen_lo : 3 ≤ mountain.val.length)
        (hlen_hi : mountain.val.length ≤ 100)
        (hval : ∀ i, i < mountain.val.length → 1 ≤ mget mountain i ∧ mget mountain i ≤ 100), ∃ r : alloc.vec.Vec Std.I64,
          Aegis.FindPeaks.find_peaks mountain = ok r ∧
          List.Perm (vals_vec r) ((peakIndices (vals_slice mountain)).map (fun i => (i : Int))) ∧
          (∀ i : Int, occ (vals_vec r) i =
            if isPeak (vals_slice mountain) i then 1 else 0)) := by
    sorry

  /-- The function returns a result r and does not fail: there is no overflow, out-of-bounds access, or panic.
    Preconditions: len(mountain) >= 3 and len(mountain) <= 100, and for every i with 0 <= i < len(mountain), 1 <= mountain[i] and mountain[i] <= 100. -/
  theorem spec_2 (mountain : Slice Std.I64)
      (hlen_lo : 3 ≤ mountain.val.length)
      (hlen_hi : mountain.val.length ≤ 100)
      (hval : ∀ i, i < mountain.val.length → 1 ≤ mget mountain i ∧ mget mountain i ≤ 100) :
      ∃ r : alloc.vec.Vec Std.I64, Aegis.FindPeaks.find_peaks mountain = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (mountain : Slice Std.I64)
        (hlen_lo : 3 ≤ mountain.val.length)
        (hlen_hi : mountain.val.length ≤ 100)
        (hval : ∀ i, i < mountain.val.length → 1 ≤ mget mountain i ∧ mget mountain i ≤ 100), ∃ r : alloc.vec.Vec Std.I64, Aegis.FindPeaks.find_peaks mountain = ok r) := by
    sorry

  /-- Whenever the function returns a result r, for every k with 0 <= k < len(r), 1 <= r[k] and r[k] < len(mountain)-1. Thus every returned value is an interior index of mountain, not 0 and not len(mountain)-1.
    Preconditions: len(mountain) >= 3 and len(mountain) <= 100, and for every i with 0 <= i < len(mountain), 1 <= mountain[i] and mountain[i] <= 100. -/
  theorem spec_3 (mountain : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
      (hlen_lo : 3 ≤ mountain.val.length)
      (hlen_hi : mountain.val.length ≤ 100)
      (hval : ∀ i, i < mountain.val.length → 1 ≤ mget mountain i ∧ mget mountain i ≤ 100)
      (hres : Aegis.FindPeaks.find_peaks mountain = ok r) :
      ∀ k, k < (vals_vec r).length →
        1 ≤ rget r k ∧ rget r k < ((vals_slice mountain).length : Int) - 1 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (mountain : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
        (hlen_lo : 3 ≤ mountain.val.length)
        (hlen_hi : mountain.val.length ≤ 100)
        (hval : ∀ i, i < mountain.val.length → 1 ≤ mget mountain i ∧ mget mountain i ≤ 100)
        (hres : Aegis.FindPeaks.find_peaks mountain = ok r), ∀ k, k < (vals_vec r).length →
          1 ≤ rget r k ∧ rget r k < ((vals_slice mountain).length : Int) - 1) := by
    sorry

  /-- Whenever the function returns a result r, for every k with 0 <= k < len(r), the index i = r[k] is a peak: 1 <= i < len(mountain)-1, mountain[i-1] < mountain[i], and mountain[i+1] < mountain[i].
    Preconditions: len(mountain) >= 3 and len(mountain) <= 100, and for every i with 0 <= i < len(mountain), 1 <= mountain[i] and mountain[i] <= 100. -/
  theorem spec_4 (mountain : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
      (hlen_lo : 3 ≤ mountain.val.length)
      (hlen_hi : mountain.val.length ≤ 100)
      (hval : ∀ i, i < mountain.val.length → 1 ≤ mget mountain i ∧ mget mountain i ≤ 100)
      (hres : Aegis.FindPeaks.find_peaks mountain = ok r) :
      ∀ k, k < (vals_vec r).length → IsPeak (vals_slice mountain) (rget r k) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (mountain : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
        (hlen_lo : 3 ≤ mountain.val.length)
        (hlen_hi : mountain.val.length ≤ 100)
        (hval : ∀ i, i < mountain.val.length → 1 ≤ mget mountain i ∧ mget mountain i ≤ 100)
        (hres : Aegis.FindPeaks.find_peaks mountain = ok r), ∀ k, k < (vals_vec r).length → IsPeak (vals_slice mountain) (rget r k)) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 1 <= i < len(mountain)-1, if mountain[i-1] < mountain[i] and mountain[i+1] < mountain[i], then i occurs as an element of r.
    Preconditions: len(mountain) >= 3 and len(mountain) <= 100, and for every i with 0 <= i < len(mountain), 1 <= mountain[i] and mountain[i] <= 100. -/
  theorem spec_5 (mountain : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
      (hlen_lo : 3 ≤ mountain.val.length)
      (hlen_hi : mountain.val.length ≤ 100)
      (hval : ∀ i, i < mountain.val.length → 1 ≤ mget mountain i ∧ mget mountain i ≤ 100)
      (hres : Aegis.FindPeaks.find_peaks mountain = ok r) :
      ∀ i : Int, IsPeak (vals_slice mountain) i → Occurs (vals_vec r) i := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (mountain : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
        (hlen_lo : 3 ≤ mountain.val.length)
        (hlen_hi : mountain.val.length ≤ 100)
        (hval : ∀ i, i < mountain.val.length → 1 ≤ mget mountain i ∧ mget mountain i ≤ 100)
        (hres : Aegis.FindPeaks.find_peaks mountain = ok r), ∀ i : Int, IsPeak (vals_slice mountain) i → Occurs (vals_vec r) i) := by
    sorry

  /-- Whenever the function returns a result r, all elements of r are distinct: for every a and b with 0 <= a < b < len(r), r[a] != r[b].
    Preconditions: len(mountain) >= 3 and len(mountain) <= 100, and for every i with 0 <= i < len(mountain), 1 <= mountain[i] and mountain[i] <= 100. -/
  theorem spec_6 (mountain : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
      (hlen_lo : 3 ≤ mountain.val.length)
      (hlen_hi : mountain.val.length ≤ 100)
      (hval : ∀ i, i < mountain.val.length → 1 ≤ mget mountain i ∧ mget mountain i ≤ 100)
      (hres : Aegis.FindPeaks.find_peaks mountain = ok r) :
      ∀ a b, a < b → b < (vals_vec r).length → rget r a ≠ rget r b := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (mountain : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
        (hlen_lo : 3 ≤ mountain.val.length)
        (hlen_hi : mountain.val.length ≤ 100)
        (hval : ∀ i, i < mountain.val.length → 1 ≤ mget mountain i ∧ mget mountain i ≤ 100)
        (hres : Aegis.FindPeaks.find_peaks mountain = ok r), ∀ a b, a < b → b < (vals_vec r).length → rget r a ≠ rget r b) := by
    sorry

  /-- Whenever the function returns a result r, len(r) <= floor((len(mountain)-1)/2), where the division is rounded down.
    Preconditions: len(mountain) >= 3 and len(mountain) <= 100, and for every i with 0 <= i < len(mountain), 1 <= mountain[i] and mountain[i] <= 100. -/
  theorem spec_7 (mountain : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
      (hlen_lo : 3 ≤ mountain.val.length)
      (hlen_hi : mountain.val.length ≤ 100)
      (hval : ∀ i, i < mountain.val.length → 1 ≤ mget mountain i ∧ mget mountain i ≤ 100)
      (hres : Aegis.FindPeaks.find_peaks mountain = ok r) :
      (vals_vec r).length ≤ (mountain.val.length - 1) / 2 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (mountain : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
        (hlen_lo : 3 ≤ mountain.val.length)
        (hlen_hi : mountain.val.length ≤ 100)
        (hval : ∀ i, i < mountain.val.length → 1 ≤ mget mountain i ∧ mget mountain i ≤ 100)
        (hres : Aegis.FindPeaks.find_peaks mountain = ok r), (vals_vec r).length ≤ (mountain.val.length - 1) / 2) := by
    sorry

  /-- Whenever the function returns a result r, len(r) = 0 if and only if there is no index i such that 1 <= i < len(mountain)-1, mountain[i-1] < mountain[i], and mountain[i+1] < mountain[i].
    Preconditions: len(mountain) >= 3 and len(mountain) <= 100, and for every i with 0 <= i < len(mountain), 1 <= mountain[i] and mountain[i] <= 100. -/
  theorem spec_8 (mountain : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
      (hlen_lo : 3 ≤ mountain.val.length)
      (hlen_hi : mountain.val.length ≤ 100)
      (hval : ∀ i, i < mountain.val.length → 1 ≤ mget mountain i ∧ mget mountain i ≤ 100)
      (hres : Aegis.FindPeaks.find_peaks mountain = ok r) :
      ((vals_vec r).length = 0 ↔ ¬ ∃ i : Int, IsPeak (vals_slice mountain) i) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (mountain : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
        (hlen_lo : 3 ≤ mountain.val.length)
        (hlen_hi : mountain.val.length ≤ 100)
        (hval : ∀ i, i < mountain.val.length → 1 ≤ mget mountain i ∧ mget mountain i ≤ 100)
        (hres : Aegis.FindPeaks.find_peaks mountain = ok r), ((vals_vec r).length = 0 ↔ ¬ ∃ i : Int, IsPeak (vals_slice mountain) i)) := by
    sorry

  /-- Whenever the function returns a result r and len(mountain) = 3, then r = [1] if mountain[0] < mountain[1] and mountain[2] < mountain[1], and r = [] otherwise.
    Preconditions: len(mountain) >= 3 and len(mountain) <= 100, and for every i with 0 <= i < len(mountain), 1 <= mountain[i] and mountain[i] <= 100. -/
  theorem spec_9 (mountain : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
      (hlen_lo : 3 ≤ mountain.val.length)
      (hlen_hi : mountain.val.length ≤ 100)
      (hval : ∀ i, i < mountain.val.length → 1 ≤ mget mountain i ∧ mget mountain i ≤ 100)
      (hres : Aegis.FindPeaks.find_peaks mountain = ok r)
      (hlen3 : mountain.val.length = 3) :
      vals_vec r = (if (mget mountain 0 < mget mountain 1 ∧ mget mountain 2 < mget mountain 1)
                    then [1] else []) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (mountain : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
        (hlen_lo : 3 ≤ mountain.val.length)
        (hlen_hi : mountain.val.length ≤ 100)
        (hval : ∀ i, i < mountain.val.length → 1 ≤ mget mountain i ∧ mget mountain i ≤ 100)
        (hres : Aegis.FindPeaks.find_peaks mountain = ok r)
        (hlen3 : mountain.val.length = 3), vals_vec r = (if (mget mountain 0 < mget mountain 1 ∧ mget mountain 2 < mget mountain 1)
                      then [1] else [])) := by
    sorry

  /-- Whenever the function returns a result r, if mountain[i] = mountain[0] for every i with 0 <= i < len(mountain), then len(r) = 0.
    Preconditions: len(mountain) >= 3 and len(mountain) <= 100, and for every i with 0 <= i < len(mountain), 1 <= mountain[i] and mountain[i] <= 100. -/
  theorem spec_10 (mountain : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
      (hlen_lo : 3 ≤ mountain.val.length)
      (hlen_hi : mountain.val.length ≤ 100)
      (hval : ∀ i, i < mountain.val.length → 1 ≤ mget mountain i ∧ mget mountain i ≤ 100)
      (hres : Aegis.FindPeaks.find_peaks mountain = ok r)
      (hconst : ∀ i, i < (vals_slice mountain).length → mget mountain i = mget mountain 0) :
      (vals_vec r).length = 0 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (mountain : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
        (hlen_lo : 3 ≤ mountain.val.length)
        (hlen_hi : mountain.val.length ≤ 100)
        (hval : ∀ i, i < mountain.val.length → 1 ≤ mget mountain i ∧ mget mountain i ≤ 100)
        (hres : Aegis.FindPeaks.find_peaks mountain = ok r)
        (hconst : ∀ i, i < (vals_slice mountain).length → mget mountain i = mget mountain 0), (vals_vec r).length = 0) := by
    sorry

  /-- Whenever the function returns a result r, if mountain[i] < mountain[i+1] for every 0 <= i < len(mountain)-1, or if mountain[i] > mountain[i+1] for every 0 <= i < len(mountain)-1, then len(r) = 0.
    Preconditions: len(mountain) >= 3 and len(mountain) <= 100, and for every i with 0 <= i < len(mountain), 1 <= mountain[i] and mountain[i] <= 100. -/
  theorem spec_11 (mountain : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
      (hlen_lo : 3 ≤ mountain.val.length)
      (hlen_hi : mountain.val.length ≤ 100)
      (hval : ∀ i, i < mountain.val.length → 1 ≤ mget mountain i ∧ mget mountain i ≤ 100)
      (hres : Aegis.FindPeaks.find_peaks mountain = ok r)
      (hmono : (∀ i, i + 1 < (vals_slice mountain).length → mget mountain i < mget mountain (i + 1)) ∨
        (∀ i, i + 1 < (vals_slice mountain).length → mget mountain i > mget mountain (i + 1))) :
      (vals_vec r).length = 0 := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (mountain : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
        (hlen_lo : 3 ≤ mountain.val.length)
        (hlen_hi : mountain.val.length ≤ 100)
        (hval : ∀ i, i < mountain.val.length → 1 ≤ mget mountain i ∧ mget mountain i ≤ 100)
        (hres : Aegis.FindPeaks.find_peaks mountain = ok r)
        (hmono : (∀ i, i + 1 < (vals_slice mountain).length → mget mountain i < mget mountain (i + 1)) ∨
          (∀ i, i + 1 < (vals_slice mountain).length → mget mountain i > mget mountain (i + 1))), (vals_vec r).length = 0) := by
    sorry

  /-- Whenever the function returns a result r, no two distinct elements of r are consecutive integers: for every a and b with 0 <= a < len(r) and 0 <= b < len(r), if r[a] != r[b], then r[a] + 1 != r[b] and r[a] - 1 != r[b].
    Preconditions: len(mountain) >= 3 and len(mountain) <= 100, and for every i with 0 <= i < len(mountain), 1 <= mountain[i] and mountain[i] <= 100. -/
  theorem spec_12 (mountain : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
      (hlen_lo : 3 ≤ mountain.val.length)
      (hlen_hi : mountain.val.length ≤ 100)
      (hval : ∀ i, i < mountain.val.length → 1 ≤ mget mountain i ∧ mget mountain i ≤ 100)
      (hres : Aegis.FindPeaks.find_peaks mountain = ok r) :
      ∀ a b, a < (vals_vec r).length → b < (vals_vec r).length → rget r a ≠ rget r b →
        rget r a + 1 ≠ rget r b ∧ rget r a - 1 ≠ rget r b := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (mountain : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
        (hlen_lo : 3 ≤ mountain.val.length)
        (hlen_hi : mountain.val.length ≤ 100)
        (hval : ∀ i, i < mountain.val.length → 1 ≤ mget mountain i ∧ mget mountain i ≤ 100)
        (hres : Aegis.FindPeaks.find_peaks mountain = ok r), ∀ a b, a < (vals_vec r).length → b < (vals_vec r).length → rget r a ≠ rget r b →
          rget r a + 1 ≠ rget r b ∧ rget r a - 1 ≠ rget r b) := by
    sorry

  /-- For any two inputs mountain and mountain' of the same length, if for every i with 0 <= i < len(mountain)-1 the strict comparisons agree, namely mountain[i] < mountain[i+1] iff mountain'[i] < mountain'[i+1] and mountain[i] > mountain[i+1] iff mountain'[i] > mountain'[i+1], then whenever the function returns r on mountain and r' on mountain', the set of integers occurring as elements of r equals the set of integers occurring as elements of r'.
    Preconditions: For any two slices mountain and mountain' that each satisfy: len >= 3, len <= 100, and all elements are between 1 and 100. -/
  theorem spec_13 (mountain mountain' : Slice Std.I64)
      (r r' : alloc.vec.Vec Std.I64)
      (hlen_lo : 3 ≤ mountain.val.length)
      (hlen_hi : mountain.val.length ≤ 100)
      (hval : ∀ i, i < mountain.val.length → 1 ≤ mget mountain i ∧ mget mountain i ≤ 100)
      (hlen_lo' : 3 ≤ mountain'.val.length)
      (hlen_hi' : mountain'.val.length ≤ 100)
      (hval' : ∀ i, i < mountain'.val.length → 1 ≤ mget mountain' i ∧ mget mountain' i ≤ 100)
      (hsame : mountain'.val.length = mountain.val.length)
      (hcmp : ∀ i, i + 1 < (vals_slice mountain).length →
        (mget mountain i < mget mountain (i + 1) ↔ mget mountain' i < mget mountain' (i + 1)) ∧
        (mget mountain i > mget mountain (i + 1) ↔ mget mountain' i > mget mountain' (i + 1)))
      (hres : Aegis.FindPeaks.find_peaks mountain = ok r)
      (hres' : Aegis.FindPeaks.find_peaks mountain' = ok r') :
      ∀ x : Int, Occurs (vals_vec r) x ↔ Occurs (vals_vec r') x := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (mountain mountain' : Slice Std.I64)
        (r r' : alloc.vec.Vec Std.I64)
        (hlen_lo : 3 ≤ mountain.val.length)
        (hlen_hi : mountain.val.length ≤ 100)
        (hval : ∀ i, i < mountain.val.length → 1 ≤ mget mountain i ∧ mget mountain i ≤ 100)
        (hlen_lo' : 3 ≤ mountain'.val.length)
        (hlen_hi' : mountain'.val.length ≤ 100)
        (hval' : ∀ i, i < mountain'.val.length → 1 ≤ mget mountain' i ∧ mget mountain' i ≤ 100)
        (hsame : mountain'.val.length = mountain.val.length)
        (hcmp : ∀ i, i + 1 < (vals_slice mountain).length →
          (mget mountain i < mget mountain (i + 1) ↔ mget mountain' i < mget mountain' (i + 1)) ∧
          (mget mountain i > mget mountain (i + 1) ↔ mget mountain' i > mget mountain' (i + 1)))
        (hres : Aegis.FindPeaks.find_peaks mountain = ok r)
        (hres' : Aegis.FindPeaks.find_peaks mountain' = ok r'), ∀ x : Int, Occurs (vals_vec r) x ↔ Occurs (vals_vec r') x) := by
    sorry

  end AegisSpec.FindPeaks
