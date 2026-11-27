import Aegis.PourWater.Code.Funs

/-!
# Specifications of `Aegis.PourWater.pour_water`

LeetCode problem `pour-water`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.PourWater (pour_water)

namespace AegisSpec.PourWater

def i64At (xs : List Std.I64) (i : Nat) : Int := ((xs[i]?).map (fun x => x.val)).getD 0

def i64List (xs : List Std.I64) : List Int := xs.map (fun x => x.val)

def iAt (xs : List Int) (i : Nat) : Int := (xs[i]?).getD 0

def seg (L : List Int) (lo hi : Nat) : List Int :=
  (List.range (hi + 1 - lo)).map (fun t => iAt L (lo + t))

def segMin (L : List Int) (lo hi : Nat) : Int :=
  (seg L lo hi).foldr min (iAt L hi)

def firstIdxOf (L : List Int) (lo hi : Nat) (v : Int) : Nat :=
  lo + (seg L lo hi).idxOf v

def lastIdxOf (L : List Int) (lo hi : Nat) (v : Int) : Nat :=
  let s := seg L lo hi
  lo + (s.length - 1 - s.reverse.idxOf v)

def leftRunStart (L : List Int) : Nat → Nat
  | 0 => 0
  | (k + 1) => if iAt L k ≤ iAt L (k + 1) then leftRunStart L k else k + 1

def rightRunEnd (L : List Int) (n : Nat) : Nat → Nat → Nat
  | 0, b => b
  | (fuel + 1), b =>
    if b + 1 < n ∧ iAt L (b + 1) ≤ iAt L b then rightRunEnd L n fuel (b + 1) else b

def pourTarget (L : List Int) (n k : Nat) : Nat :=
  let a := leftRunStart L k
  let mL := segMin L a k
  if mL < iAt L k then lastIdxOf L a k mL
  else
    let b := rightRunEnd L n n k
    let mR := segMin L k b
    if mR < iAt L k then firstIdxOf L k b mR else k

def pourStep (L : List Int) (n k : Nat) : List Int :=
  let j := pourTarget L n k
  L.set j (iAt L j + 1)

def pourLevels (h : List Int) (volume : Int) (k : Nat) : List Int :=
  (List.range volume.toNat).foldl (fun L _ => pourStep L h.length k) h

/-- Let n = len(heights). Whenever the function returns a result r, len(r) = n and r is the final level array defined by the following sequential process. Initialize w^0_i = 0 for every i with 0 <= i < n. For each t = 0,1,...,volume-1, let L^t_i = heights[i] + w^t_i. Define the next index j_t as follows. Let a be the smallest index with 0 <= a <= k such that L^t_k >= L^t_{k-1} >= ... >= L^t_a (this chain is vacuous if a = k) and either a = 0 or L^t_{a-1} > L^t_a. Let m_L = min { L^t_i : a <= i <= k }. If m_L < L^t_k, let j_L be the largest index i with a <= i <= k and L^t_i = m_L. If m_L < L^t_k, set j_t = j_L. Otherwise, let b be the largest index with k <= b < n such that L^t_k >= L^t_{k+1} >= ... >= L^t_b (this chain is vacuous if b = k) and either b = n-1 or L^t_{b+1} > L^t_b. Let m_R = min { L^t_i : k <= i <= b }. If m_R < L^t_k, let j_R be the smallest index i with k <= i <= b and L^t_i = m_R. If m_R < L^t_k, set j_t = j_R. If neither left nor right case applies, set j_t = k. Then set w^{t+1}_i = w^t_i + 1 if i = j_t, and w^{t+1}_i = w^t_i otherwise. Finally, for every i with 0 <= i < n, r[i] = heights[i] + w^{volume}_i.
  Preconditions: len(heights) is an integer with 1 <= len(heights) <= 100; for every i with 0 <= i < len(heights), 0 <= heights[i] <= 99; 0 <= volume <= 2000; 0 <= k < len(heights). -/
theorem spec_1 (heights : Slice Std.I64) (volume k : Std.I64)
    (hlen1 : 1 ≤ heights.val.length)
    (hlen100 : heights.val.length ≤ 100)
    (hrange : ∀ i, i < heights.val.length → 0 ≤ i64At heights.val i ∧ i64At heights.val i ≤ 99)
    (hvol0 : 0 ≤ volume.val) (hvol2000 : volume.val ≤ 2000)
    (hk0 : 0 ≤ k.val) (hklen : k.val < (heights.val.length : Int)) :
    ∀ r, pour_water heights volume k = ok r →
      r.val.length = heights.val.length ∧
        i64List r.val = pourLevels (i64List heights.val) volume.val k.val.toNat := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (heights : Slice Std.I64) (volume k : Std.I64)
    (hlen1 : 1 ≤ heights.val.length)
    (hlen100 : heights.val.length ≤ 100)
    (hrange : ∀ i, i < heights.val.length → 0 ≤ i64At heights.val i ∧ i64At heights.val i ≤ 99)
    (hvol0 : 0 ≤ volume.val) (hvol2000 : volume.val ≤ 2000)
    (hk0 : 0 ≤ k.val) (hklen : k.val < (heights.val.length : Int)), ∀ r, pour_water heights volume k = ok r →
      r.val.length = heights.val.length ∧
        i64List r.val = pourLevels (i64List heights.val) volume.val k.val.toNat) := by
  sorry

/-- The function returns a result r for every input satisfying the preconditions; it does not fail, panic, or overflow.
  Preconditions: len(heights) is an integer with 1 <= len(heights) <= 100; for every i with 0 <= i < len(heights), 0 <= heights[i] <= 99; 0 <= volume <= 2000; 0 <= k < len(heights). -/
theorem spec_2 (heights : Slice Std.I64) (volume k : Std.I64)
    (hlen1 : 1 ≤ heights.val.length)
    (hlen100 : heights.val.length ≤ 100)
    (hrange : ∀ i, i < heights.val.length → 0 ≤ i64At heights.val i ∧ i64At heights.val i ≤ 99)
    (hvol0 : 0 ≤ volume.val) (hvol2000 : volume.val ≤ 2000)
    (hk0 : 0 ≤ k.val) (hklen : k.val < (heights.val.length : Int)) :
    ∃ r, pour_water heights volume k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (heights : Slice Std.I64) (volume k : Std.I64)
    (hlen1 : 1 ≤ heights.val.length)
    (hlen100 : heights.val.length ≤ 100)
    (hrange : ∀ i, i < heights.val.length → 0 ≤ i64At heights.val i ∧ i64At heights.val i ≤ 99)
    (hvol0 : 0 ≤ volume.val) (hvol2000 : volume.val ≤ 2000)
    (hk0 : 0 ≤ k.val) (hklen : k.val < (heights.val.length : Int)), ∃ r, pour_water heights volume k = ok r) := by
  sorry

/-- Whenever the function returns a result r, len(r) = len(heights).
  Preconditions: len(heights) is an integer with 1 <= len(heights) <= 100; for every i with 0 <= i < len(heights), 0 <= heights[i] <= 99; 0 <= volume <= 2000; 0 <= k < len(heights). -/
theorem spec_3 (heights : Slice Std.I64) (volume k : Std.I64)
    (hlen1 : 1 ≤ heights.val.length)
    (hlen100 : heights.val.length ≤ 100)
    (hrange : ∀ i, i < heights.val.length → 0 ≤ i64At heights.val i ∧ i64At heights.val i ≤ 99)
    (hvol0 : 0 ≤ volume.val) (hvol2000 : volume.val ≤ 2000)
    (hk0 : 0 ≤ k.val) (hklen : k.val < (heights.val.length : Int)) :
    ∀ r, pour_water heights volume k = ok r → r.val.length = heights.val.length := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (heights : Slice Std.I64) (volume k : Std.I64)
    (hlen1 : 1 ≤ heights.val.length)
    (hlen100 : heights.val.length ≤ 100)
    (hrange : ∀ i, i < heights.val.length → 0 ≤ i64At heights.val i ∧ i64At heights.val i ≤ 99)
    (hvol0 : 0 ≤ volume.val) (hvol2000 : volume.val ≤ 2000)
    (hk0 : 0 ≤ k.val) (hklen : k.val < (heights.val.length : Int)), ∀ r, pour_water heights volume k = ok r → r.val.length = heights.val.length) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(heights), heights[i] <= r[i] <= heights[i] + volume.
  Preconditions: len(heights) is an integer with 1 <= len(heights) <= 100; for every i with 0 <= i < len(heights), 0 <= heights[i] <= 99; 0 <= volume <= 2000; 0 <= k < len(heights). -/
theorem spec_4 (heights : Slice Std.I64) (volume k : Std.I64)
    (hlen1 : 1 ≤ heights.val.length)
    (hlen100 : heights.val.length ≤ 100)
    (hrange : ∀ i, i < heights.val.length → 0 ≤ i64At heights.val i ∧ i64At heights.val i ≤ 99)
    (hvol0 : 0 ≤ volume.val) (hvol2000 : volume.val ≤ 2000)
    (hk0 : 0 ≤ k.val) (hklen : k.val < (heights.val.length : Int)) :
    ∀ r, pour_water heights volume k = ok r →
      ∀ i, i < heights.val.length →
        i64At heights.val i ≤ i64At r.val i ∧
          i64At r.val i ≤ i64At heights.val i + volume.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (heights : Slice Std.I64) (volume k : Std.I64)
    (hlen1 : 1 ≤ heights.val.length)
    (hlen100 : heights.val.length ≤ 100)
    (hrange : ∀ i, i < heights.val.length → 0 ≤ i64At heights.val i ∧ i64At heights.val i ≤ 99)
    (hvol0 : 0 ≤ volume.val) (hvol2000 : volume.val ≤ 2000)
    (hk0 : 0 ≤ k.val) (hklen : k.val < (heights.val.length : Int)), ∀ r, pour_water heights volume k = ok r →
      ∀ i, i < heights.val.length →
        i64At heights.val i ≤ i64At r.val i ∧
          i64At r.val i ≤ i64At heights.val i + volume.val) := by
  sorry

def sumDiff (r h : List Std.I64) (n : Nat) : Int :=
  ((List.range n).map (fun i => i64At r i - i64At h i)).sum

/-- Whenever the function returns a result r, sum_{i=0}^{len(heights)-1} (r[i] - heights[i]) = volume.
  Preconditions: len(heights) is an integer with 1 <= len(heights) <= 100; for every i with 0 <= i < len(heights), 0 <= heights[i] <= 99; 0 <= volume <= 2000; 0 <= k < len(heights). -/
theorem spec_5 (heights : Slice Std.I64) (volume k : Std.I64)
    (hlen1 : 1 ≤ heights.val.length)
    (hlen100 : heights.val.length ≤ 100)
    (hrange : ∀ i, i < heights.val.length → 0 ≤ i64At heights.val i ∧ i64At heights.val i ≤ 99)
    (hvol0 : 0 ≤ volume.val) (hvol2000 : volume.val ≤ 2000)
    (hk0 : 0 ≤ k.val) (hklen : k.val < (heights.val.length : Int)) :
    ∀ r, pour_water heights volume k = ok r →
      sumDiff r.val heights.val heights.val.length = volume.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (heights : Slice Std.I64) (volume k : Std.I64)
    (hlen1 : 1 ≤ heights.val.length)
    (hlen100 : heights.val.length ≤ 100)
    (hrange : ∀ i, i < heights.val.length → 0 ≤ i64At heights.val i ∧ i64At heights.val i ≤ 99)
    (hvol0 : 0 ≤ volume.val) (hvol2000 : volume.val ≤ 2000)
    (hk0 : 0 ≤ k.val) (hklen : k.val < (heights.val.length : Int)), ∀ r, pour_water heights volume k = ok r →
      sumDiff r.val heights.val heights.val.length = volume.val) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(heights), r[i] = heights[i].
  Preconditions: len(heights) is an integer with 1 <= len(heights) <= 100; for every i with 0 <= i < len(heights), 0 <= heights[i] <= 99; 0 <= volume <= 2000; 0 <= k < len(heights); volume = 0. -/
theorem spec_6 (heights : Slice Std.I64) (volume k : Std.I64)
    (hlen1 : 1 ≤ heights.val.length)
    (hlen100 : heights.val.length ≤ 100)
    (hrange : ∀ i, i < heights.val.length → 0 ≤ i64At heights.val i ∧ i64At heights.val i ≤ 99)
    (hvol0 : 0 ≤ volume.val) (hvol2000 : volume.val ≤ 2000)
    (hk0 : 0 ≤ k.val) (hklen : k.val < (heights.val.length : Int))
    (hvol : volume.val = 0) :
    ∀ r, pour_water heights volume k = ok r →
      ∀ i, i < heights.val.length → i64At r.val i = i64At heights.val i := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (heights : Slice Std.I64) (volume k : Std.I64)
    (hlen1 : 1 ≤ heights.val.length)
    (hlen100 : heights.val.length ≤ 100)
    (hrange : ∀ i, i < heights.val.length → 0 ≤ i64At heights.val i ∧ i64At heights.val i ≤ 99)
    (hvol0 : 0 ≤ volume.val) (hvol2000 : volume.val ≤ 2000)
    (hk0 : 0 ≤ k.val) (hklen : k.val < (heights.val.length : Int))
    (hvol : volume.val = 0), ∀ r, pour_water heights volume k = ok r →
      ∀ i, i < heights.val.length → i64At r.val i = i64At heights.val i) := by
  sorry

/-- Whenever the function returns a result r, len(r) = 1 and r[0] = heights[0] + volume.
  Preconditions: len(heights) is an integer with 1 <= len(heights) <= 100; for every i with 0 <= i < len(heights), 0 <= heights[i] <= 99; 0 <= volume <= 2000; 0 <= k < len(heights); len(heights) = 1. -/
theorem spec_7 (heights : Slice Std.I64) (volume k : Std.I64)
    (hlen1 : 1 ≤ heights.val.length)
    (hlen100 : heights.val.length ≤ 100)
    (hrange : ∀ i, i < heights.val.length → 0 ≤ i64At heights.val i ∧ i64At heights.val i ≤ 99)
    (hvol0 : 0 ≤ volume.val) (hvol2000 : volume.val ≤ 2000)
    (hk0 : 0 ≤ k.val) (hklen : k.val < (heights.val.length : Int))
    (hlen : heights.val.length = 1) :
    ∀ r, pour_water heights volume k = ok r →
      r.val.length = 1 ∧ i64At r.val 0 = i64At heights.val 0 + volume.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (heights : Slice Std.I64) (volume k : Std.I64)
    (hlen1 : 1 ≤ heights.val.length)
    (hlen100 : heights.val.length ≤ 100)
    (hrange : ∀ i, i < heights.val.length → 0 ≤ i64At heights.val i ∧ i64At heights.val i ≤ 99)
    (hvol0 : 0 ≤ volume.val) (hvol2000 : volume.val ≤ 2000)
    (hk0 : 0 ≤ k.val) (hklen : k.val < (heights.val.length : Int))
    (hlen : heights.val.length = 1), ∀ r, pour_water heights volume k = ok r →
      r.val.length = 1 ∧ i64At r.val 0 = i64At heights.val 0 + volume.val) := by
  sorry

/-- Whenever the function returns a result r, there exists an index i with 0 <= i < len(heights) such that r[i] > heights[i].
  Preconditions: len(heights) is an integer with 1 <= len(heights) <= 100; for every i with 0 <= i < len(heights), 0 <= heights[i] <= 99; 0 <= volume <= 2000; 0 <= k < len(heights); volume > 0. -/
theorem spec_8 (heights : Slice Std.I64) (volume k : Std.I64)
    (hlen1 : 1 ≤ heights.val.length)
    (hlen100 : heights.val.length ≤ 100)
    (hrange : ∀ i, i < heights.val.length → 0 ≤ i64At heights.val i ∧ i64At heights.val i ≤ 99)
    (hvol0 : 0 ≤ volume.val) (hvol2000 : volume.val ≤ 2000)
    (hk0 : 0 ≤ k.val) (hklen : k.val < (heights.val.length : Int))
    (hvol : 0 < volume.val) :
    ∀ r, pour_water heights volume k = ok r →
      ∃ i, i < heights.val.length ∧ i64At heights.val i < i64At r.val i := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (heights : Slice Std.I64) (volume k : Std.I64)
    (hlen1 : 1 ≤ heights.val.length)
    (hlen100 : heights.val.length ≤ 100)
    (hrange : ∀ i, i < heights.val.length → 0 ≤ i64At heights.val i ∧ i64At heights.val i ≤ 99)
    (hvol0 : 0 ≤ volume.val) (hvol2000 : volume.val ≤ 2000)
    (hk0 : 0 ≤ k.val) (hklen : k.val < (heights.val.length : Int))
    (hvol : 0 < volume.val), ∀ r, pour_water heights volume k = ok r →
      ∃ i, i < heights.val.length ∧ i64At heights.val i < i64At r.val i) := by
  sorry

/-- Whenever the function returns a result r, there exists an index i with 0 <= i < len(heights) such that r[i] = heights[i].
  Preconditions: len(heights) is an integer with 1 <= len(heights) <= 100; for every i with 0 <= i < len(heights), 0 <= heights[i] <= 99; 0 <= volume <= 2000; 0 <= k < len(heights); volume < len(heights). -/
theorem spec_9 (heights : Slice Std.I64) (volume k : Std.I64)
    (hlen1 : 1 ≤ heights.val.length)
    (hlen100 : heights.val.length ≤ 100)
    (hrange : ∀ i, i < heights.val.length → 0 ≤ i64At heights.val i ∧ i64At heights.val i ≤ 99)
    (hvol0 : 0 ≤ volume.val) (hvol2000 : volume.val ≤ 2000)
    (hk0 : 0 ≤ k.val) (hklen : k.val < (heights.val.length : Int))
    (hvol : volume.val < (heights.val.length : Int)) :
    ∀ r, pour_water heights volume k = ok r →
      ∃ i, i < heights.val.length ∧ i64At r.val i = i64At heights.val i := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (heights : Slice Std.I64) (volume k : Std.I64)
    (hlen1 : 1 ≤ heights.val.length)
    (hlen100 : heights.val.length ≤ 100)
    (hrange : ∀ i, i < heights.val.length → 0 ≤ i64At heights.val i ∧ i64At heights.val i ≤ 99)
    (hvol0 : 0 ≤ volume.val) (hvol2000 : volume.val ≤ 2000)
    (hk0 : 0 ≤ k.val) (hklen : k.val < (heights.val.length : Int))
    (hvol : volume.val < (heights.val.length : Int)), ∀ r, pour_water heights volume k = ok r →
      ∃ i, i < heights.val.length ∧ i64At r.val i = i64At heights.val i) := by
  sorry

def cycleOrder (k : Nat) (t : Nat) : Nat := if t ≤ k then k - t else t

def cyclePrefixIndicator (k rmd i : Nat) : Int :=
  if (List.range rmd).any (fun t => decide (cycleOrder k t = i)) then 1 else 0

/-- Let n = len(heights), V = volume, q = V / n (integer division), and rmd = V mod n, so V = q*n + rmd with 0 <= rmd < n. Define the sequence O of length n by O_t = k - t for 0 <= t <= k, and O_t = t for k < t < n. Then whenever the function returns a result r, for every i with 0 <= i < n, r[i] = c + q + (1 if there exists t with 0 <= t < rmd and O_t = i, else 0).
  Preconditions: len(heights) is an integer with 1 <= len(heights) <= 100; for every i with 0 <= i < len(heights), 0 <= heights[i] <= 99; 0 <= volume <= 2000; 0 <= k < len(heights); there exists an integer c such that for every i with 0 <= i < len(heights), heights[i] = c. -/
theorem spec_10 (heights : Slice Std.I64) (volume k : Std.I64) (c : Int)
    (hlen1 : 1 ≤ heights.val.length)
    (hlen100 : heights.val.length ≤ 100)
    (hrange : ∀ i, i < heights.val.length → 0 ≤ i64At heights.val i ∧ i64At heights.val i ≤ 99)
    (hvol0 : 0 ≤ volume.val) (hvol2000 : volume.val ≤ 2000)
    (hk0 : 0 ≤ k.val) (hklen : k.val < (heights.val.length : Int))
    (hconst : ∀ i, i < heights.val.length → i64At heights.val i = c) :
    ∀ r, pour_water heights volume k = ok r →
      ∀ i, i < heights.val.length →
        i64At r.val i =
          c + volume.val / (heights.val.length : Int) +
            cyclePrefixIndicator k.val.toNat
              (volume.val % (heights.val.length : Int)).toNat i := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (heights : Slice Std.I64) (volume k : Std.I64) (c : Int)
    (hlen1 : 1 ≤ heights.val.length)
    (hlen100 : heights.val.length ≤ 100)
    (hrange : ∀ i, i < heights.val.length → 0 ≤ i64At heights.val i ∧ i64At heights.val i ≤ 99)
    (hvol0 : 0 ≤ volume.val) (hvol2000 : volume.val ≤ 2000)
    (hk0 : 0 ≤ k.val) (hklen : k.val < (heights.val.length : Int))
    (hconst : ∀ i, i < heights.val.length → i64At heights.val i = c), ∀ r, pour_water heights volume k = ok r →
      ∀ i, i < heights.val.length →
        i64At r.val i =
          c + volume.val / (heights.val.length : Int) +
            cyclePrefixIndicator k.val.toNat
              (volume.val % (heights.val.length : Int)).toNat i) := by
  sorry

/-- Whenever the function returns a result r, there exists an index i with 0 <= i < len(heights) such that len(heights) * (r[i] - heights[i]) >= volume.
  Preconditions: len(heights) is an integer with 1 <= len(heights) <= 100; for every i with 0 <= i < len(heights), 0 <= heights[i] <= 99; 0 <= volume <= 2000; 0 <= k < len(heights). -/
theorem spec_11 (heights : Slice Std.I64) (volume k : Std.I64)
    (hlen1 : 1 ≤ heights.val.length)
    (hlen100 : heights.val.length ≤ 100)
    (hrange : ∀ i, i < heights.val.length → 0 ≤ i64At heights.val i ∧ i64At heights.val i ≤ 99)
    (hvol0 : 0 ≤ volume.val) (hvol2000 : volume.val ≤ 2000)
    (hk0 : 0 ≤ k.val) (hklen : k.val < (heights.val.length : Int)) :
    ∀ r, pour_water heights volume k = ok r →
      ∃ i, i < heights.val.length ∧
        (heights.val.length : Int) * (i64At r.val i - i64At heights.val i) ≥ volume.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (heights : Slice Std.I64) (volume k : Std.I64)
    (hlen1 : 1 ≤ heights.val.length)
    (hlen100 : heights.val.length ≤ 100)
    (hrange : ∀ i, i < heights.val.length → 0 ≤ i64At heights.val i ∧ i64At heights.val i ≤ 99)
    (hvol0 : 0 ≤ volume.val) (hvol2000 : volume.val ≤ 2000)
    (hk0 : 0 ≤ k.val) (hklen : k.val < (heights.val.length : Int)), ∀ r, pour_water heights volume k = ok r →
      ∃ i, i < heights.val.length ∧
        (heights.val.length : Int) * (i64At r.val i - i64At heights.val i) ≥ volume.val) := by
  sorry

/-- Let r1 be the result of pouring v1 units at index k and r2 the result of pouring v2 units at index k on the same heights. Whenever both calls return, for every i with 0 <= i < len(heights), r1[i] <= r2[i].
  Preconditions: len(heights) is an integer with 1 <= len(heights) <= 100; for every i with 0 <= i < len(heights), 0 <= heights[i] <= 99; 0 <= k < len(heights); 0 <= v1 <= v2 <= 2000. -/
theorem spec_12 (heights : Slice Std.I64) (k v1 v2 : Std.I64)
    (hlen1 : 1 ≤ heights.val.length)
    (hlen100 : heights.val.length ≤ 100)
    (hrange : ∀ i, i < heights.val.length → 0 ≤ i64At heights.val i ∧ i64At heights.val i ≤ 99)
    (hk0 : 0 ≤ k.val) (hklen : k.val < (heights.val.length : Int))
    (hv10 : 0 ≤ v1.val) (hv12 : v1.val ≤ v2.val) (hv22 : v2.val ≤ 2000) :
    ∀ r1 r2, pour_water heights v1 k = ok r1 →
      pour_water heights v2 k = ok r2 →
        ∀ i, i < heights.val.length → i64At r1.val i ≤ i64At r2.val i := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (heights : Slice Std.I64) (k v1 v2 : Std.I64)
    (hlen1 : 1 ≤ heights.val.length)
    (hlen100 : heights.val.length ≤ 100)
    (hrange : ∀ i, i < heights.val.length → 0 ≤ i64At heights.val i ∧ i64At heights.val i ≤ 99)
    (hk0 : 0 ≤ k.val) (hklen : k.val < (heights.val.length : Int))
    (hv10 : 0 ≤ v1.val) (hv12 : v1.val ≤ v2.val) (hv22 : v2.val ≤ 2000), ∀ r1 r2, pour_water heights v1 k = ok r1 →
      pour_water heights v2 k = ok r2 →
        ∀ i, i < heights.val.length → i64At r1.val i ≤ i64At r2.val i) := by
  sorry

def raisedCount (r h : List Std.I64) (n : Nat) : Nat :=
  ((List.range n).filter (fun i => decide (i64At h i < i64At r i))).length

/-- Whenever the function returns a result r, the number of indices i with 0 <= i < len(heights) and r[i] > heights[i] is at most min(volume, len(heights)).
  Preconditions: len(heights) is an integer with 1 <= len(heights) <= 100; for every i with 0 <= i < len(heights), 0 <= heights[i] <= 99; 0 <= volume <= 2000; 0 <= k < len(heights). -/
theorem spec_13 (heights : Slice Std.I64) (volume k : Std.I64)
    (hlen1 : 1 ≤ heights.val.length)
    (hlen100 : heights.val.length ≤ 100)
    (hrange : ∀ i, i < heights.val.length → 0 ≤ i64At heights.val i ∧ i64At heights.val i ≤ 99)
    (hvol0 : 0 ≤ volume.val) (hvol2000 : volume.val ≤ 2000)
    (hk0 : 0 ≤ k.val) (hklen : k.val < (heights.val.length : Int)) :
    ∀ r, pour_water heights volume k = ok r →
      (raisedCount r.val heights.val heights.val.length : Int) ≤
        min volume.val (heights.val.length : Int) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (heights : Slice Std.I64) (volume k : Std.I64)
    (hlen1 : 1 ≤ heights.val.length)
    (hlen100 : heights.val.length ≤ 100)
    (hrange : ∀ i, i < heights.val.length → 0 ≤ i64At heights.val i ∧ i64At heights.val i ≤ 99)
    (hvol0 : 0 ≤ volume.val) (hvol2000 : volume.val ≤ 2000)
    (hk0 : 0 ≤ k.val) (hklen : k.val < (heights.val.length : Int)), ∀ r, pour_water heights volume k = ok r →
      (raisedCount r.val heights.val heights.val.length : Int) ≤
        min volume.val (heights.val.length : Int)) := by
  sorry

end AegisSpec.PourWater
