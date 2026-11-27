import Aegis.MaximumCost.Code.Funs

/-!
# Specifications of `Aegis.MaximumCost.maximum_cost`

LeetCode problem `maximum-cost-of-trip-with-k-highways`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.MaximumCost

  namespace AegisSpec.MaximumCost

  def entryInts (e : alloc.vec.Vec Std.I64) : List ℤ := e.val.map (fun x => x.val)

  def entryTriple (highways : Slice (alloc.vec.Vec Std.I64)) (i : ℕ) : Option (ℤ × ℤ × ℤ) :=
    match highways.val[i]? with
    | none => none
    | some e =>
      match entryInts e with
      | [u, v, c] => some (u, v, c)
      | _ => none

  def SamePair (u v u' v' : ℤ) : Prop := (u = u' ∧ v = v') ∨ (u = v' ∧ v = u')

  def WellFormed (n : ℤ) (highways : Slice (alloc.vec.Vec Std.I64)) : Prop :=
    ∀ i : ℕ, i < highways.val.length →
      ∃ u v c : ℤ,
        entryTriple highways i = some (u, v, c) ∧
          0 ≤ u ∧ u < n ∧ 0 ≤ v ∧ v < n ∧ u ≠ v ∧ 0 ≤ c ∧ c ≤ 100

  def Univocal (highways : Slice (alloc.vec.Vec Std.I64)) : Prop :=
    ∀ (i j : ℕ), i < highways.val.length → j < highways.val.length → i ≠ j →
      ∀ u v c u' v' c' : ℤ,
        entryTriple highways i = some (u, v, c) →
          entryTriple highways j = some (u', v', c') → ¬ SamePair u v u' v'

  def edgeToll (highways : Slice (alloc.vec.Vec Std.I64)) (a b : ℤ) : Option ℤ :=
    highways.val.findSome? (fun e =>
      match entryInts e with
      | [u, v, c] => if (u = a ∧ v = b) ∨ (u = b ∧ v = a) then some c else none
      | _ => none)

  def consecutive (p : List ℤ) : List (ℤ × ℤ) := p.zip p.tail

  def IsWalk (highways : Slice (alloc.vec.Vec Std.I64)) (p : List ℤ) : Prop :=
    ∀ q ∈ consecutive p, ∃ c : ℤ, edgeToll highways q.1 q.2 = some c

  def IsTrip (n k : ℤ) (highways : Slice (alloc.vec.Vec Std.I64)) (p : List ℤ) : Prop :=
    p.length = k.toNat + 1 ∧ (∀ x ∈ p, 0 ≤ x ∧ x < n) ∧ p.Nodup ∧ IsWalk highways p

  def HasTrip (n k : ℤ) (highways : Slice (alloc.vec.Vec Std.I64)) : Prop :=
    ∃ p : List ℤ, IsTrip n k highways p

  def tripCost (highways : Slice (alloc.vec.Vec Std.I64)) (p : List ℤ) : ℤ :=
    ((consecutive p).map (fun q => (edgeToll highways q.1 q.2).getD 0)).sum

  def allTolls (highways : Slice (alloc.vec.Vec Std.I64)) : List ℤ :=
    highways.val.filterMap (fun e =>
      match entryInts e with
      | [_, _, c] => some c
      | _ => none)

  def maxToll (highways : Slice (alloc.vec.Vec Std.I64)) : ℤ :=
    match allTolls highways with
    | [] => 0
    | c :: cs => cs.foldl max c

  def minToll (highways : Slice (alloc.vec.Vec Std.I64)) : ℤ :=
    match allTolls highways with
    | [] => 0
    | c :: cs => cs.foldl min c

  def SwapSubset (highways hs' : Slice (alloc.vec.Vec Std.I64)) : Prop :=
    hs'.val.length = highways.val.length ∧
      ∀ (i : ℕ) (u v c : ℤ),
        i < highways.val.length → entryTriple highways i = some (u, v, c) →
          entryTriple hs' i = some (u, v, c) ∨ entryTriple hs' i = some (v, u, c)

  def SharedPair (highways : Slice (alloc.vec.Vec Std.I64)) (i j : ℕ) (s : ℤ) : Prop :=
    ∃ u v c u' v' c' : ℤ,
      entryTriple highways i = some (u, v, c) ∧
        entryTriple highways j = some (u', v', c') ∧
          (u = u' ∨ u = v' ∨ v = u' ∨ v = v') ∧ ¬ SamePair u v u' v' ∧ s = c + c'

  def HasSharedPair (highways : Slice (alloc.vec.Vec Std.I64)) : Prop :=
    ∃ (i j : ℕ) (s : ℤ), SharedPair highways i j s

  /-- Let a valid trip be a sequence (p_0,...,p_k) of integers such that each p_i satisfies 0 <= p_i < n, the values p_0,...,p_k are pairwise distinct, and for every j with 0 <= j < k there is an entry [u,v,c] in highways with {u,v} = {p_j,p_{j+1}}; because no unordered endpoint pair repeats, this entry and its toll c are unique. Its cost is the sum of these k unique tolls. The function returns a result r, and: if at least one valid trip exists, r equals the maximum cost of a valid trip; if no valid trip exists, r = -1.
    Preconditions: n, k, and every entry of highways are 64-bit integers; 2 <= n <= 15; 1 <= len(highways) <= 50; each highways[i] has length 3; for each i, writing highways[i] = [u,v,c], we have 0 <= u < n, 0 <= v < n, u != v, and 0 <= c <= 100; no two entries have the same unordered pair of endpoints; 1 <= k <= 50. -/
  theorem spec_1 (n k : Std.I64) (highways : Slice (alloc.vec.Vec Std.I64))
      (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 15)
      (hlen_lo : 1 ≤ highways.val.length) (hlen_hi : highways.val.length ≤ 50)
      (hwf : WellFormed n.val highways) (huniq : Univocal highways)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 50) :
      ∃ r : Std.I64,
        maximum_cost n highways k = ok r ∧
          (HasTrip n.val k.val highways →
            ∃ p : List ℤ,
              IsTrip n.val k.val highways p ∧ tripCost highways p = r.val ∧
                ∀ q : List ℤ, IsTrip n.val k.val highways q → tripCost highways q ≤ r.val) ∧
          (¬ HasTrip n.val k.val highways → r.val = -1) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n k : Std.I64) (highways : Slice (alloc.vec.Vec Std.I64))
        (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 15)
        (hlen_lo : 1 ≤ highways.val.length) (hlen_hi : highways.val.length ≤ 50)
        (hwf : WellFormed n.val highways) (huniq : Univocal highways)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 50), ∃ r : Std.I64,
          maximum_cost n highways k = ok r ∧
            (HasTrip n.val k.val highways →
              ∃ p : List ℤ,
                IsTrip n.val k.val highways p ∧ tripCost highways p = r.val ∧
                  ∀ q : List ℤ, IsTrip n.val k.val highways q → tripCost highways q ≤ r.val) ∧
            (¬ HasTrip n.val k.val highways → r.val = -1)) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r (it does not fail, panic, or overflow).
    Preconditions: n, k, and every entry of highways are 64-bit integers; 2 <= n <= 15; 1 <= len(highways) <= 50; each highways[i] has length 3; for each i, writing highways[i] = [u,v,c], we have 0 <= u < n, 0 <= v < n, u != v, and 0 <= c <= 100; no two entries have the same unordered pair of endpoints; 1 <= k <= 50. -/
  theorem spec_2 (n k : Std.I64) (highways : Slice (alloc.vec.Vec Std.I64))
      (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 15)
      (hlen_lo : 1 ≤ highways.val.length) (hlen_hi : highways.val.length ≤ 50)
      (hwf : WellFormed n.val highways) (huniq : Univocal highways)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 50) :
      ∃ r : Std.I64, maximum_cost n highways k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n k : Std.I64) (highways : Slice (alloc.vec.Vec Std.I64))
        (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 15)
        (hlen_lo : 1 ≤ highways.val.length) (hlen_hi : highways.val.length ≤ 50)
        (hwf : WellFormed n.val highways) (huniq : Univocal highways)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 50), ∃ r : Std.I64, maximum_cost n highways k = ok r) := by
    sorry

  /-- Whenever the function returns a result r with r != -1, there exists a valid trip whose cost is r, where a valid trip is a sequence (p_0,...,p_k) of pairwise distinct integers in [0,n-1] such that each consecutive pair is connected by a highway, and its cost is the sum of the k unique corresponding highway tolls.
    Preconditions: n, k, and every entry of highways are 64-bit integers; 2 <= n <= 15; 1 <= len(highways) <= 50; each highways[i] has length 3; for each i, writing highways[i] = [u,v,c], we have 0 <= u < n, 0 <= v < n, u != v, and 0 <= c <= 100; no two entries have the same unordered pair of endpoints; 1 <= k <= 50. -/
  theorem spec_3 (n k : Std.I64) (highways : Slice (alloc.vec.Vec Std.I64))
      (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 15)
      (hlen_lo : 1 ≤ highways.val.length) (hlen_hi : highways.val.length ≤ 50)
      (hwf : WellFormed n.val highways) (huniq : Univocal highways)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 50) :
      ∀ r : Std.I64, maximum_cost n highways k = ok r → r.val ≠ -1 →
        ∃ p : List ℤ, IsTrip n.val k.val highways p ∧ tripCost highways p = r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n k : Std.I64) (highways : Slice (alloc.vec.Vec Std.I64))
        (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 15)
        (hlen_lo : 1 ≤ highways.val.length) (hlen_hi : highways.val.length ≤ 50)
        (hwf : WellFormed n.val highways) (huniq : Univocal highways)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 50), ∀ r : Std.I64, maximum_cost n highways k = ok r → r.val ≠ -1 →
          ∃ p : List ℤ, IsTrip n.val k.val highways p ∧ tripCost highways p = r.val) := by
    sorry

  /-- Whenever the function returns a result r with r != -1, every valid trip has cost at most r, where a valid trip is a sequence (p_0,...,p_k) of pairwise distinct integers in [0,n-1] such that each consecutive pair is connected by a highway, and its cost is the sum of the k unique corresponding highway tolls.
    Preconditions: n, k, and every entry of highways are 64-bit integers; 2 <= n <= 15; 1 <= len(highways) <= 50; each highways[i] has length 3; for each i, writing highways[i] = [u,v,c], we have 0 <= u < n, 0 <= v < n, u != v, and 0 <= c <= 100; no two entries have the same unordered pair of endpoints; 1 <= k <= 50. -/
  theorem spec_4 (n k : Std.I64) (highways : Slice (alloc.vec.Vec Std.I64))
      (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 15)
      (hlen_lo : 1 ≤ highways.val.length) (hlen_hi : highways.val.length ≤ 50)
      (hwf : WellFormed n.val highways) (huniq : Univocal highways)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 50) :
      ∀ r : Std.I64, maximum_cost n highways k = ok r → r.val ≠ -1 →
        ∀ p : List ℤ, IsTrip n.val k.val highways p → tripCost highways p ≤ r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n k : Std.I64) (highways : Slice (alloc.vec.Vec Std.I64))
        (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 15)
        (hlen_lo : 1 ≤ highways.val.length) (hlen_hi : highways.val.length ≤ 50)
        (hwf : WellFormed n.val highways) (huniq : Univocal highways)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 50), ∀ r : Std.I64, maximum_cost n highways k = ok r → r.val ≠ -1 →
          ∀ p : List ℤ, IsTrip n.val k.val highways p → tripCost highways p ≤ r.val) := by
    sorry

  /-- Whenever the function returns r = -1, there is no valid trip, where a valid trip is a sequence (p_0,...,p_k) of pairwise distinct integers in [0,n-1] such that each consecutive pair is connected by a highway.
    Preconditions: n, k, and every entry of highways are 64-bit integers; 2 <= n <= 15; 1 <= len(highways) <= 50; each highways[i] has length 3; for each i, writing highways[i] = [u,v,c], we have 0 <= u < n, 0 <= v < n, u != v, and 0 <= c <= 100; no two entries have the same unordered pair of endpoints; 1 <= k <= 50. -/
  theorem spec_5 (n k : Std.I64) (highways : Slice (alloc.vec.Vec Std.I64))
      (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 15)
      (hlen_lo : 1 ≤ highways.val.length) (hlen_hi : highways.val.length ≤ 50)
      (hwf : WellFormed n.val highways) (huniq : Univocal highways)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 50) :
      ∀ r : Std.I64, maximum_cost n highways k = ok r → r.val = -1 →
        ¬ HasTrip n.val k.val highways := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n k : Std.I64) (highways : Slice (alloc.vec.Vec Std.I64))
        (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 15)
        (hlen_lo : 1 ≤ highways.val.length) (hlen_hi : highways.val.length ≤ 50)
        (hwf : WellFormed n.val highways) (huniq : Univocal highways)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 50), ∀ r : Std.I64, maximum_cost n highways k = ok r → r.val = -1 →
          ¬ HasTrip n.val k.val highways) := by
    sorry

  /-- If there exists a valid trip, where a valid trip is a sequence (p_0,...,p_k) of pairwise distinct integers in [0,n-1] such that each consecutive pair is connected by a highway, then the function returns a result r with r != -1.
    Preconditions: n, k, and every entry of highways are 64-bit integers; 2 <= n <= 15; 1 <= len(highways) <= 50; each highways[i] has length 3; for each i, writing highways[i] = [u,v,c], we have 0 <= u < n, 0 <= v < n, u != v, and 0 <= c <= 100; no two entries have the same unordered pair of endpoints; 1 <= k <= 50. -/
  theorem spec_6 (n k : Std.I64) (highways : Slice (alloc.vec.Vec Std.I64))
      (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 15)
      (hlen_lo : 1 ≤ highways.val.length) (hlen_hi : highways.val.length ≤ 50)
      (hwf : WellFormed n.val highways) (huniq : Univocal highways)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 50) :
      HasTrip n.val k.val highways →
        ∃ r : Std.I64, maximum_cost n highways k = ok r ∧ r.val ≠ -1 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n k : Std.I64) (highways : Slice (alloc.vec.Vec Std.I64))
        (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 15)
        (hlen_lo : 1 ≤ highways.val.length) (hlen_hi : highways.val.length ≤ 50)
        (hwf : WellFormed n.val highways) (huniq : Univocal highways)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 50), HasTrip n.val k.val highways →
          ∃ r : Std.I64, maximum_cost n highways k = ok r ∧ r.val ≠ -1) := by
    sorry

  /-- Whenever the function returns a result r with r != -1, 0 <= r <= k * M, where M is the maximum toll among all entries of highways.
    Preconditions: n, k, and every entry of highways are 64-bit integers; 2 <= n <= 15; 1 <= len(highways) <= 50; each highways[i] has length 3; for each i, writing highways[i] = [u,v,c], we have 0 <= u < n, 0 <= v < n, u != v, and 0 <= c <= 100; no two entries have the same unordered pair of endpoints; 1 <= k <= 50. -/
  theorem spec_7 (n k : Std.I64) (highways : Slice (alloc.vec.Vec Std.I64))
      (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 15)
      (hlen_lo : 1 ≤ highways.val.length) (hlen_hi : highways.val.length ≤ 50)
      (hwf : WellFormed n.val highways) (huniq : Univocal highways)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 50) :
      ∀ r : Std.I64, maximum_cost n highways k = ok r → r.val ≠ -1 →
        0 ≤ r.val ∧ r.val ≤ k.val * maxToll highways := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n k : Std.I64) (highways : Slice (alloc.vec.Vec Std.I64))
        (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 15)
        (hlen_lo : 1 ≤ highways.val.length) (hlen_hi : highways.val.length ≤ 50)
        (hwf : WellFormed n.val highways) (huniq : Univocal highways)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 50), ∀ r : Std.I64, maximum_cost n highways k = ok r → r.val ≠ -1 →
          0 ≤ r.val ∧ r.val ≤ k.val * maxToll highways) := by
    sorry

  /-- If k >= n, the function returns -1.
    Preconditions: n, k, and every entry of highways are 64-bit integers; 2 <= n <= 15; 1 <= len(highways) <= 50; each highways[i] has length 3; for each i, writing highways[i] = [u,v,c], we have 0 <= u < n, 0 <= v < n, u != v, and 0 <= c <= 100; no two entries have the same unordered pair of endpoints; 1 <= k <= 50. -/
  theorem spec_8 (n k : Std.I64) (highways : Slice (alloc.vec.Vec Std.I64))
      (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 15)
      (hlen_lo : 1 ≤ highways.val.length) (hlen_hi : highways.val.length ≤ 50)
      (hwf : WellFormed n.val highways) (huniq : Univocal highways)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 50)
      (hkn : n.val ≤ k.val) :
      maximum_cost n highways k = ok (-1)#i64 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n k : Std.I64) (highways : Slice (alloc.vec.Vec Std.I64))
        (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 15)
        (hlen_lo : 1 ≤ highways.val.length) (hlen_hi : highways.val.length ≤ 50)
        (hwf : WellFormed n.val highways) (huniq : Univocal highways)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 50)
        (hkn : n.val ≤ k.val), maximum_cost n highways k = ok (-1)#i64) := by
    sorry

  /-- If k > len(highways), the function returns -1.
    Preconditions: n, k, and every entry of highways are 64-bit integers; 2 <= n <= 15; 1 <= len(highways) <= 50; each highways[i] has length 3; for each i, writing highways[i] = [u,v,c], we have 0 <= u < n, 0 <= v < n, u != v, and 0 <= c <= 100; no two entries have the same unordered pair of endpoints; 1 <= k <= 50. -/
  theorem spec_9 (n k : Std.I64) (highways : Slice (alloc.vec.Vec Std.I64))
      (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 15)
      (hlen_lo : 1 ≤ highways.val.length) (hlen_hi : highways.val.length ≤ 50)
      (hwf : WellFormed n.val highways) (huniq : Univocal highways)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 50)
      (hkl : highways.val.length < k.val) :
      maximum_cost n highways k = ok (-1)#i64 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n k : Std.I64) (highways : Slice (alloc.vec.Vec Std.I64))
        (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 15)
        (hlen_lo : 1 ≤ highways.val.length) (hlen_hi : highways.val.length ≤ 50)
        (hwf : WellFormed n.val highways) (huniq : Univocal highways)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 50)
        (hkl : highways.val.length < k.val), maximum_cost n highways k = ok (-1)#i64) := by
    sorry

  /-- If k = 1, the function returns r, where r is the maximum toll among all entries of highways.
    Preconditions: n, k, and every entry of highways are 64-bit integers; 2 <= n <= 15; 1 <= len(highways) <= 50; each highways[i] has length 3; for each i, writing highways[i] = [u,v,c], we have 0 <= u < n, 0 <= v < n, u != v, and 0 <= c <= 100; no two entries have the same unordered pair of endpoints; 1 <= k <= 50; k = 1. -/
  theorem spec_10 (n k : Std.I64) (highways : Slice (alloc.vec.Vec Std.I64))
      (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 15)
      (hlen_lo : 1 ≤ highways.val.length) (hlen_hi : highways.val.length ≤ 50)
      (hwf : WellFormed n.val highways) (huniq : Univocal highways)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 50)
      (hk : k.val = 1) :
      ∃ r : Std.I64, maximum_cost n highways k = ok r ∧ r.val = maxToll highways := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n k : Std.I64) (highways : Slice (alloc.vec.Vec Std.I64))
        (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 15)
        (hlen_lo : 1 ≤ highways.val.length) (hlen_hi : highways.val.length ≤ 50)
        (hwf : WellFormed n.val highways) (huniq : Univocal highways)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 50)
        (hk : k.val = 1), ∃ r : Std.I64, maximum_cost n highways k = ok r ∧ r.val = maxToll highways) := by
    sorry

  /-- If every entry [u,v,c] in highways has c = 0, then the function returns r, and r = 0 if there exists a valid trip (a sequence (p_0,...,p_k) of pairwise distinct integers in [0,n-1] such that each consecutive pair is connected by a highway), otherwise r = -1.
    Preconditions: n, k, and every entry of highways are 64-bit integers; 2 <= n <= 15; 1 <= len(highways) <= 50; each highways[i] has length 3; for each i, writing highways[i] = [u,v,c], we have 0 <= u < n, 0 <= v < n, u != v, and 0 <= c <= 100; no two entries have the same unordered pair of endpoints; 1 <= k <= 50; every entry [u,v,c] in highways has c = 0. -/
  theorem spec_11 (n k : Std.I64) (highways : Slice (alloc.vec.Vec Std.I64))
      (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 15)
      (hlen_lo : 1 ≤ highways.val.length) (hlen_hi : highways.val.length ≤ 50)
      (hwf : WellFormed n.val highways) (huniq : Univocal highways)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 50)
      (hzero : ∀ (i : ℕ) (u v c : ℤ), i < highways.val.length →
        entryTriple highways i = some (u, v, c) → c = 0) :
      ∃ r : Std.I64,
        maximum_cost n highways k = ok r ∧
          (HasTrip n.val k.val highways → r.val = 0) ∧
          (¬ HasTrip n.val k.val highways → r.val = -1) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (n k : Std.I64) (highways : Slice (alloc.vec.Vec Std.I64))
        (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 15)
        (hlen_lo : 1 ≤ highways.val.length) (hlen_hi : highways.val.length ≤ 50)
        (hwf : WellFormed n.val highways) (huniq : Univocal highways)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 50)
        (hzero : ∀ (i : ℕ) (u v c : ℤ), i < highways.val.length →
          entryTriple highways i = some (u, v, c) → c = 0), ∃ r : Std.I64,
          maximum_cost n highways k = ok r ∧
            (HasTrip n.val k.val highways → r.val = 0) ∧
            (¬ HasTrip n.val k.val highways → r.val = -1)) := by
    sorry

  /-- For every list hs' that is a permutation of highways, if maximum_cost(n, highways, k) returns r and maximum_cost(n, hs', k) returns r', then r = r'.
    Preconditions: n, k, and every entry of highways are 64-bit integers; 2 <= n <= 15; 1 <= len(highways) <= 50; each highways[i] has length 3; for each i, writing highways[i] = [u,v,c], we have 0 <= u < n, 0 <= v < n, u != v, and 0 <= c <= 100; no two entries have the same unordered pair of endpoints; 1 <= k <= 50; hs' is any permutation of the list highways. -/
  theorem spec_12 (n k : Std.I64) (highways : Slice (alloc.vec.Vec Std.I64))
      (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 15)
      (hlen_lo : 1 ≤ highways.val.length) (hlen_hi : highways.val.length ≤ 50)
      (hwf : WellFormed n.val highways) (huniq : Univocal highways)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 50)
      (hs' : Slice (alloc.vec.Vec Std.I64)) (hperm : highways.val.Perm hs'.val) :
      ∀ r r' : Std.I64,
        maximum_cost n highways k = ok r → maximum_cost n hs' k = ok r' → r = r' := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (n k : Std.I64) (highways : Slice (alloc.vec.Vec Std.I64))
        (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 15)
        (hlen_lo : 1 ≤ highways.val.length) (hlen_hi : highways.val.length ≤ 50)
        (hwf : WellFormed n.val highways) (huniq : Univocal highways)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 50)
        (hs' : Slice (alloc.vec.Vec Std.I64)) (hperm : highways.val.Perm hs'.val), ∀ r r' : Std.I64,
          maximum_cost n highways k = ok r → maximum_cost n hs' k = ok r' → r = r') := by
    sorry

  /-- For every list hs' obtained from highways by reversing any subset of the highway endpoint pairs, if maximum_cost(n, highways, k) returns r and maximum_cost(n, hs', k) returns r', then r = r'.
    Preconditions: n, k, and every entry of highways are 64-bit integers; 2 <= n <= 15; 1 <= len(highways) <= 50; each highways[i] has length 3; for each i, writing highways[i] = [u,v,c], we have 0 <= u < n, 0 <= v < n, u != v, and 0 <= c <= 100; no two entries have the same unordered pair of endpoints; 1 <= k <= 50; hs' is any list obtained from highways by replacing each entry [u,v,c] with either [u,v,c] or [v,u,c]. -/
  theorem spec_13 (n k : Std.I64) (highways : Slice (alloc.vec.Vec Std.I64))
      (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 15)
      (hlen_lo : 1 ≤ highways.val.length) (hlen_hi : highways.val.length ≤ 50)
      (hwf : WellFormed n.val highways) (huniq : Univocal highways)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 50)
      (hs' : Slice (alloc.vec.Vec Std.I64)) (hswap : SwapSubset highways hs') :
      ∀ r r' : Std.I64,
        maximum_cost n highways k = ok r → maximum_cost n hs' k = ok r' → r = r' := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (n k : Std.I64) (highways : Slice (alloc.vec.Vec Std.I64))
        (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 15)
        (hlen_lo : 1 ≤ highways.val.length) (hlen_hi : highways.val.length ≤ 50)
        (hwf : WellFormed n.val highways) (huniq : Univocal highways)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 50)
        (hs' : Slice (alloc.vec.Vec Std.I64)) (hswap : SwapSubset highways hs'), ∀ r r' : Std.I64,
          maximum_cost n highways k = ok r → maximum_cost n hs' k = ok r' → r = r') := by
    sorry

  /-- Whenever the function returns a result r with r != -1, r >= k * m, where m is the minimum toll among all entries of highways.
    Preconditions: n, k, and every entry of highways are 64-bit integers; 2 <= n <= 15; 1 <= len(highways) <= 50; each highways[i] has length 3; for each i, writing highways[i] = [u,v,c], we have 0 <= u < n, 0 <= v < n, u != v, and 0 <= c <= 100; no two entries have the same unordered pair of endpoints; 1 <= k <= 50. -/
  theorem spec_14 (n k : Std.I64) (highways : Slice (alloc.vec.Vec Std.I64))
      (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 15)
      (hlen_lo : 1 ≤ highways.val.length) (hlen_hi : highways.val.length ≤ 50)
      (hwf : WellFormed n.val highways) (huniq : Univocal highways)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 50) :
      ∀ r : Std.I64, maximum_cost n highways k = ok r → r.val ≠ -1 →
        k.val * minToll highways ≤ r.val := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (n k : Std.I64) (highways : Slice (alloc.vec.Vec Std.I64))
        (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 15)
        (hlen_lo : 1 ≤ highways.val.length) (hlen_hi : highways.val.length ≤ 50)
        (hwf : WellFormed n.val highways) (huniq : Univocal highways)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 50), ∀ r : Std.I64, maximum_cost n highways k = ok r → r.val ≠ -1 →
          k.val * minToll highways ≤ r.val) := by
    sorry

  /-- If k = 2, the function returns a result r, and r = -1 if there are no two distinct entries [u,v,c] and [u',v',c'] in highways with the sets {u,v} and {u',v'} intersecting in exactly one city; otherwise r is the maximum, over all such pairs of entries, of c + c'.
    Preconditions: n, k, and every entry of highways are 64-bit integers; 2 <= n <= 15; 1 <= len(highways) <= 50; each highways[i] has length 3; for each i, writing highways[i] = [u,v,c], we have 0 <= u < n, 0 <= v < n, u != v, and 0 <= c <= 100; no two entries have the same unordered pair of endpoints; 1 <= k <= 50; k = 2. -/
  theorem spec_15 (n k : Std.I64) (highways : Slice (alloc.vec.Vec Std.I64))
      (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 15)
      (hlen_lo : 1 ≤ highways.val.length) (hlen_hi : highways.val.length ≤ 50)
      (hwf : WellFormed n.val highways) (huniq : Univocal highways)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 50)
      (hk : k.val = 2) :
      ∃ r : Std.I64,
        maximum_cost n highways k = ok r ∧
          (HasSharedPair highways →
            ∃ (i j : ℕ) (s : ℤ),
              SharedPair highways i j s ∧ r.val = s ∧
                ∀ (i' j' : ℕ) (s' : ℤ), SharedPair highways i' j' s' → s' ≤ r.val) ∧
          (¬ HasSharedPair highways → r.val = -1) := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (n k : Std.I64) (highways : Slice (alloc.vec.Vec Std.I64))
        (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 15)
        (hlen_lo : 1 ≤ highways.val.length) (hlen_hi : highways.val.length ≤ 50)
        (hwf : WellFormed n.val highways) (huniq : Univocal highways)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 50)
        (hk : k.val = 2), ∃ r : Std.I64,
          maximum_cost n highways k = ok r ∧
            (HasSharedPair highways →
              ∃ (i j : ℕ) (s : ℤ),
                SharedPair highways i j s ∧ r.val = s ∧
                  ∀ (i' j' : ℕ) (s' : ℤ), SharedPair highways i' j' s' → s' ≤ r.val) ∧
            (¬ HasSharedPair highways → r.val = -1)) := by
    sorry

  end AegisSpec.MaximumCost
