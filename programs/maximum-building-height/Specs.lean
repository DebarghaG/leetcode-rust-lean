import Aegis.MaxBuilding.Code.Funs

/-!
# Specifications of `Aegis.MaxBuilding.max_building`

LeetCode problem `maximum-building-height`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxBuilding

def iabs (x : Int) : Int := if x ≥ 0 then x else -x

def idAt (restrictions : Slice (alloc.vec.Vec Std.I64)) (j : Nat) : Int :=
  ((restrictions.val[j]!).val[0]!).val

def mAt (restrictions : Slice (alloc.vec.Vec Std.I64)) (j : Nat) : Int :=
  ((restrictions.val[j]!).val[1]!).val

def pairList (restrictions : Slice (alloc.vec.Vec Std.I64)) : List (Int × Int) :=
  (List.range restrictions.val.length).map (fun j => (idAt restrictions j, mAt restrictions j))

def Feasible (n : Int) (restrictions : Slice (alloc.vec.Vec Std.I64)) (h : Int → Int) : Prop :=
  h 1 = 0 ∧
    (∀ i : Int, 1 ≤ i → i ≤ n → 0 ≤ h i) ∧
    (∀ i : Int, 1 ≤ i → i < n → iabs (h (i + 1) - h i) ≤ 1) ∧
    (∀ j : Nat, j < restrictions.val.length → h (idAt restrictions j) ≤ mAt restrictions j)

def IsMaxOverFeasible (n : Int) (restrictions : Slice (alloc.vec.Vec Std.I64)) (r : Int) : Prop :=
  (∃ (h : Int → Int) (i : Int), Feasible n restrictions h ∧ 1 ≤ i ∧ i ≤ n ∧ h i = r) ∧
    (∀ (h : Int → Int) (i : Int), Feasible n restrictions h → 1 ≤ i → i ≤ n → h i ≤ r)

def maxOverLabels (n : Int) (f : Int → Int) : Int :=
  (List.range n.toNat).foldr (fun k acc => max (f (((k : Nat) : Int) + 1)) acc) (f 1)

def bfun (restrictions : Slice (alloc.vec.Vec Std.I64)) (i : Int) : Int :=
  (List.range restrictions.val.length).foldr
    (fun j acc => min acc (mAt restrictions j + iabs (i - idAt restrictions j))) (i - 1)

def SameIds (restrictions restrictions' : Slice (alloc.vec.Vec Std.I64)) : Prop :=
  (∀ j : Nat, j < restrictions.val.length →
      ∃ j' : Nat, j' < restrictions'.val.length ∧ idAt restrictions' j' = idAt restrictions j) ∧
    (∀ j' : Nat, j' < restrictions'.val.length →
      ∃ j : Nat, j < restrictions.val.length ∧ idAt restrictions j = idAt restrictions' j)

def HeightsLe (restrictions restrictions' : Slice (alloc.vec.Vec Std.I64)) : Prop :=
  ∀ j : Nat, j < restrictions.val.length →
    ∃ j' : Nat,
      j' < restrictions'.val.length ∧ idAt restrictions' j' = idAt restrictions j ∧
        mAt restrictions j ≤ mAt restrictions' j'

/-- Whenever max_building(n, restrictions) returns a result r, r equals the maximum value of max_{1 <= i <= n} h(i) over all height sequences h satisfying: (a) h maps each label 1,...,n to an integer; (b) h(1) = 0; (c) h(i) >= 0 for every i with 1 <= i <= n; (d) |h(i+1) - h(i)| <= 1 for every i with 1 <= i < n; and (e) h(id_j) <= m_j for every j with 0 <= j < len(restrictions). This maximum exists because the all-zero height sequence is feasible.
  Preconditions: n is an integer with 2 <= n <= 10^9. restrictions is a list of pairs of 64-bit integers: for every j with 0 <= j < len(restrictions), restrictions[j] has length 2, and writing id_j = restrictions[j][0] and m_j = restrictions[j][1], we have 2 <= id_j <= n, 0 <= m_j <= 10^9, the id_j are pairwise distinct, no id_j equals 1, and len(restrictions) <= min(n-1, 10^5). -/
theorem spec_1 (n : Std.I64) (restrictions : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 10 ^ 9)
    (hlen : ∀ j : Nat, j < restrictions.val.length → (restrictions.val[j]!).val.length = 2)
    (hid_lo : ∀ j : Nat, j < restrictions.val.length → 2 ≤ idAt restrictions j)
    (hid_hi : ∀ j : Nat, j < restrictions.val.length → idAt restrictions j ≤ n.val)
    (hm_lo : ∀ j : Nat, j < restrictions.val.length → 0 ≤ mAt restrictions j)
    (hm_hi : ∀ j : Nat, j < restrictions.val.length → mAt restrictions j ≤ 10 ^ 9)
    (hid_ne_one : ∀ j : Nat, j < restrictions.val.length → idAt restrictions j ≠ 1)
    (hid_distinct : ((List.range restrictions.val.length).map (fun j => idAt restrictions j)).Nodup)
    (hcount : (restrictions.val.length : Int) ≤ min (n.val - 1) 100000) :
    ∀ r : Std.I64,
      Aegis.MaxBuilding.max_building n restrictions = ok r →
        IsMaxOverFeasible n.val restrictions r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Std.I64) (restrictions : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 10 ^ 9)
    (hlen : ∀ j : Nat, j < restrictions.val.length → (restrictions.val[j]!).val.length = 2)
    (hid_lo : ∀ j : Nat, j < restrictions.val.length → 2 ≤ idAt restrictions j)
    (hid_hi : ∀ j : Nat, j < restrictions.val.length → idAt restrictions j ≤ n.val)
    (hm_lo : ∀ j : Nat, j < restrictions.val.length → 0 ≤ mAt restrictions j)
    (hm_hi : ∀ j : Nat, j < restrictions.val.length → mAt restrictions j ≤ 10 ^ 9)
    (hid_ne_one : ∀ j : Nat, j < restrictions.val.length → idAt restrictions j ≠ 1)
    (hid_distinct : ((List.range restrictions.val.length).map (fun j => idAt restrictions j)).Nodup)
    (hcount : (restrictions.val.length : Int) ≤ min (n.val - 1) 100000), ∀ r : Std.I64,
      Aegis.MaxBuilding.max_building n restrictions = ok r →
        IsMaxOverFeasible n.val restrictions r.val) := by
  sorry

/-- For every input satisfying the preconditions, max_building(n, restrictions) returns a result r; it does not panic, go out of bounds, overflow, or otherwise fail.
  Preconditions: n is an integer with 2 <= n <= 10^9. restrictions is a list of pairs of 64-bit integers: for every j with 0 <= j < len(restrictions), restrictions[j] has length 2, and writing id_j = restrictions[j][0] and m_j = restrictions[j][1], we have 2 <= id_j <= n, 0 <= m_j <= 10^9, the id_j are pairwise distinct, no id_j equals 1, and len(restrictions) <= min(n-1, 10^5). -/
theorem spec_2 (n : Std.I64) (restrictions : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 10 ^ 9)
    (hlen : ∀ j : Nat, j < restrictions.val.length → (restrictions.val[j]!).val.length = 2)
    (hid_lo : ∀ j : Nat, j < restrictions.val.length → 2 ≤ idAt restrictions j)
    (hid_hi : ∀ j : Nat, j < restrictions.val.length → idAt restrictions j ≤ n.val)
    (hm_lo : ∀ j : Nat, j < restrictions.val.length → 0 ≤ mAt restrictions j)
    (hm_hi : ∀ j : Nat, j < restrictions.val.length → mAt restrictions j ≤ 10 ^ 9)
    (hid_ne_one : ∀ j : Nat, j < restrictions.val.length → idAt restrictions j ≠ 1)
    (hid_distinct : ((List.range restrictions.val.length).map (fun j => idAt restrictions j)).Nodup)
    (hcount : (restrictions.val.length : Int) ≤ min (n.val - 1) 100000) :
    ∃ r : Std.I64, Aegis.MaxBuilding.max_building n restrictions = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Std.I64) (restrictions : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 10 ^ 9)
    (hlen : ∀ j : Nat, j < restrictions.val.length → (restrictions.val[j]!).val.length = 2)
    (hid_lo : ∀ j : Nat, j < restrictions.val.length → 2 ≤ idAt restrictions j)
    (hid_hi : ∀ j : Nat, j < restrictions.val.length → idAt restrictions j ≤ n.val)
    (hm_lo : ∀ j : Nat, j < restrictions.val.length → 0 ≤ mAt restrictions j)
    (hm_hi : ∀ j : Nat, j < restrictions.val.length → mAt restrictions j ≤ 10 ^ 9)
    (hid_ne_one : ∀ j : Nat, j < restrictions.val.length → idAt restrictions j ≠ 1)
    (hid_distinct : ((List.range restrictions.val.length).map (fun j => idAt restrictions j)).Nodup)
    (hcount : (restrictions.val.length : Int) ≤ min (n.val - 1) 100000), ∃ r : Std.I64, Aegis.MaxBuilding.max_building n restrictions = ok r) := by
  sorry

/-- Whenever max_building(n, restrictions) returns a result r, r <= n - 1.
  Preconditions: n is an integer with 2 <= n <= 10^9. restrictions is a list of pairs of 64-bit integers: for every j with 0 <= j < len(restrictions), restrictions[j] has length 2, and writing id_j = restrictions[j][0] and m_j = restrictions[j][1], we have 2 <= id_j <= n, 0 <= m_j <= 10^9, the id_j are pairwise distinct, no id_j equals 1, and len(restrictions) <= min(n-1, 10^5). -/
theorem spec_3 (n : Std.I64) (restrictions : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 10 ^ 9)
    (hlen : ∀ j : Nat, j < restrictions.val.length → (restrictions.val[j]!).val.length = 2)
    (hid_lo : ∀ j : Nat, j < restrictions.val.length → 2 ≤ idAt restrictions j)
    (hid_hi : ∀ j : Nat, j < restrictions.val.length → idAt restrictions j ≤ n.val)
    (hm_lo : ∀ j : Nat, j < restrictions.val.length → 0 ≤ mAt restrictions j)
    (hm_hi : ∀ j : Nat, j < restrictions.val.length → mAt restrictions j ≤ 10 ^ 9)
    (hid_ne_one : ∀ j : Nat, j < restrictions.val.length → idAt restrictions j ≠ 1)
    (hid_distinct : ((List.range restrictions.val.length).map (fun j => idAt restrictions j)).Nodup)
    (hcount : (restrictions.val.length : Int) ≤ min (n.val - 1) 100000) :
    ∀ r : Std.I64,
      Aegis.MaxBuilding.max_building n restrictions = ok r → r.val ≤ n.val - 1 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : Std.I64) (restrictions : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 10 ^ 9)
    (hlen : ∀ j : Nat, j < restrictions.val.length → (restrictions.val[j]!).val.length = 2)
    (hid_lo : ∀ j : Nat, j < restrictions.val.length → 2 ≤ idAt restrictions j)
    (hid_hi : ∀ j : Nat, j < restrictions.val.length → idAt restrictions j ≤ n.val)
    (hm_lo : ∀ j : Nat, j < restrictions.val.length → 0 ≤ mAt restrictions j)
    (hm_hi : ∀ j : Nat, j < restrictions.val.length → mAt restrictions j ≤ 10 ^ 9)
    (hid_ne_one : ∀ j : Nat, j < restrictions.val.length → idAt restrictions j ≠ 1)
    (hid_distinct : ((List.range restrictions.val.length).map (fun j => idAt restrictions j)).Nodup)
    (hcount : (restrictions.val.length : Int) ≤ min (n.val - 1) 100000), ∀ r : Std.I64,
      Aegis.MaxBuilding.max_building n restrictions = ok r → r.val ≤ n.val - 1) := by
  sorry

/-- Whenever max_building(n, restrictions) returns a result r, there exist a height sequence h and a label i with 1 <= i <= n such that h is feasible, meaning h maps labels 1,...,n to integers, h(1)=0, h(k)>=0 for all k, |h(k+1)-h(k)|<=1 for all k with 1<=k<n, and h(id_j)<=m_j for all j, and such that h(i)=r.
  Preconditions: n is an integer with 2 <= n <= 10^9. restrictions is a list of pairs of 64-bit integers: for every j with 0 <= j < len(restrictions), restrictions[j] has length 2, and writing id_j = restrictions[j][0] and m_j = restrictions[j][1], we have 2 <= id_j <= n, 0 <= m_j <= 10^9, the id_j are pairwise distinct, no id_j equals 1, and len(restrictions) <= min(n-1, 10^5). -/
theorem spec_4 (n : Std.I64) (restrictions : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 10 ^ 9)
    (hlen : ∀ j : Nat, j < restrictions.val.length → (restrictions.val[j]!).val.length = 2)
    (hid_lo : ∀ j : Nat, j < restrictions.val.length → 2 ≤ idAt restrictions j)
    (hid_hi : ∀ j : Nat, j < restrictions.val.length → idAt restrictions j ≤ n.val)
    (hm_lo : ∀ j : Nat, j < restrictions.val.length → 0 ≤ mAt restrictions j)
    (hm_hi : ∀ j : Nat, j < restrictions.val.length → mAt restrictions j ≤ 10 ^ 9)
    (hid_ne_one : ∀ j : Nat, j < restrictions.val.length → idAt restrictions j ≠ 1)
    (hid_distinct : ((List.range restrictions.val.length).map (fun j => idAt restrictions j)).Nodup)
    (hcount : (restrictions.val.length : Int) ≤ min (n.val - 1) 100000) :
    ∀ r : Std.I64,
      Aegis.MaxBuilding.max_building n restrictions = ok r →
        ∃ (h : Int → Int) (i : Int),
          Feasible n.val restrictions h ∧ 1 ≤ i ∧ i ≤ n.val ∧ h i = r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : Std.I64) (restrictions : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 10 ^ 9)
    (hlen : ∀ j : Nat, j < restrictions.val.length → (restrictions.val[j]!).val.length = 2)
    (hid_lo : ∀ j : Nat, j < restrictions.val.length → 2 ≤ idAt restrictions j)
    (hid_hi : ∀ j : Nat, j < restrictions.val.length → idAt restrictions j ≤ n.val)
    (hm_lo : ∀ j : Nat, j < restrictions.val.length → 0 ≤ mAt restrictions j)
    (hm_hi : ∀ j : Nat, j < restrictions.val.length → mAt restrictions j ≤ 10 ^ 9)
    (hid_ne_one : ∀ j : Nat, j < restrictions.val.length → idAt restrictions j ≠ 1)
    (hid_distinct : ((List.range restrictions.val.length).map (fun j => idAt restrictions j)).Nodup)
    (hcount : (restrictions.val.length : Int) ≤ min (n.val - 1) 100000), ∀ r : Std.I64,
      Aegis.MaxBuilding.max_building n restrictions = ok r →
        ∃ (h : Int → Int) (i : Int),
          Feasible n.val restrictions h ∧ 1 ≤ i ∧ i ≤ n.val ∧ h i = r.val) := by
  sorry

/-- Whenever max_building(n, restrictions) returns a result r, for every feasible height sequence h and every label i with 1 <= i <= n, we have h(i) <= r, where feasible means h maps labels 1,...,n to integers, h(1)=0, h(k)>=0 for all k, |h(k+1)-h(k)|<=1 for all k with 1<=k<n, and h(id_j)<=m_j for all j.
  Preconditions: n is an integer with 2 <= n <= 10^9. restrictions is a list of pairs of 64-bit integers: for every j with 0 <= j < len(restrictions), restrictions[j] has length 2, and writing id_j = restrictions[j][0] and m_j = restrictions[j][1], we have 2 <= id_j <= n, 0 <= m_j <= 10^9, the id_j are pairwise distinct, no id_j equals 1, and len(restrictions) <= min(n-1, 10^5). -/
theorem spec_5 (n : Std.I64) (restrictions : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 10 ^ 9)
    (hlen : ∀ j : Nat, j < restrictions.val.length → (restrictions.val[j]!).val.length = 2)
    (hid_lo : ∀ j : Nat, j < restrictions.val.length → 2 ≤ idAt restrictions j)
    (hid_hi : ∀ j : Nat, j < restrictions.val.length → idAt restrictions j ≤ n.val)
    (hm_lo : ∀ j : Nat, j < restrictions.val.length → 0 ≤ mAt restrictions j)
    (hm_hi : ∀ j : Nat, j < restrictions.val.length → mAt restrictions j ≤ 10 ^ 9)
    (hid_ne_one : ∀ j : Nat, j < restrictions.val.length → idAt restrictions j ≠ 1)
    (hid_distinct : ((List.range restrictions.val.length).map (fun j => idAt restrictions j)).Nodup)
    (hcount : (restrictions.val.length : Int) ≤ min (n.val - 1) 100000) :
    ∀ r : Std.I64,
      Aegis.MaxBuilding.max_building n restrictions = ok r →
        ∀ (h : Int → Int) (i : Int),
          Feasible n.val restrictions h → 1 ≤ i → i ≤ n.val → h i ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : Std.I64) (restrictions : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 10 ^ 9)
    (hlen : ∀ j : Nat, j < restrictions.val.length → (restrictions.val[j]!).val.length = 2)
    (hid_lo : ∀ j : Nat, j < restrictions.val.length → 2 ≤ idAt restrictions j)
    (hid_hi : ∀ j : Nat, j < restrictions.val.length → idAt restrictions j ≤ n.val)
    (hm_lo : ∀ j : Nat, j < restrictions.val.length → 0 ≤ mAt restrictions j)
    (hm_hi : ∀ j : Nat, j < restrictions.val.length → mAt restrictions j ≤ 10 ^ 9)
    (hid_ne_one : ∀ j : Nat, j < restrictions.val.length → idAt restrictions j ≠ 1)
    (hid_distinct : ((List.range restrictions.val.length).map (fun j => idAt restrictions j)).Nodup)
    (hcount : (restrictions.val.length : Int) ≤ min (n.val - 1) 100000), ∀ r : Std.I64,
      Aegis.MaxBuilding.max_building n restrictions = ok r →
        ∀ (h : Int → Int) (i : Int),
          Feasible n.val restrictions h → 1 ≤ i → i ≤ n.val → h i ≤ r.val) := by
  sorry

/-- Whenever max_building(n, restrictions) returns a result r, for every label i with 1 <= i <= n, r >= B_i, where B_i = min( {i-1} union { m_j + |i - id_j| : 0 <= j < len(restrictions) } ).
  Preconditions: n is an integer with 2 <= n <= 10^9. restrictions is a list of pairs of 64-bit integers: for every j with 0 <= j < len(restrictions), restrictions[j] has length 2, and writing id_j = restrictions[j][0] and m_j = restrictions[j][1], we have 2 <= id_j <= n, 0 <= m_j <= 10^9, the id_j are pairwise distinct, no id_j equals 1, and len(restrictions) <= min(n-1, 10^5). -/
theorem spec_6 (n : Std.I64) (restrictions : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 10 ^ 9)
    (hlen : ∀ j : Nat, j < restrictions.val.length → (restrictions.val[j]!).val.length = 2)
    (hid_lo : ∀ j : Nat, j < restrictions.val.length → 2 ≤ idAt restrictions j)
    (hid_hi : ∀ j : Nat, j < restrictions.val.length → idAt restrictions j ≤ n.val)
    (hm_lo : ∀ j : Nat, j < restrictions.val.length → 0 ≤ mAt restrictions j)
    (hm_hi : ∀ j : Nat, j < restrictions.val.length → mAt restrictions j ≤ 10 ^ 9)
    (hid_ne_one : ∀ j : Nat, j < restrictions.val.length → idAt restrictions j ≠ 1)
    (hid_distinct : ((List.range restrictions.val.length).map (fun j => idAt restrictions j)).Nodup)
    (hcount : (restrictions.val.length : Int) ≤ min (n.val - 1) 100000) :
    ∀ r : Std.I64,
      Aegis.MaxBuilding.max_building n restrictions = ok r →
        ∀ i : Int, 1 ≤ i → i ≤ n.val → bfun restrictions i ≤ r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : Std.I64) (restrictions : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 10 ^ 9)
    (hlen : ∀ j : Nat, j < restrictions.val.length → (restrictions.val[j]!).val.length = 2)
    (hid_lo : ∀ j : Nat, j < restrictions.val.length → 2 ≤ idAt restrictions j)
    (hid_hi : ∀ j : Nat, j < restrictions.val.length → idAt restrictions j ≤ n.val)
    (hm_lo : ∀ j : Nat, j < restrictions.val.length → 0 ≤ mAt restrictions j)
    (hm_hi : ∀ j : Nat, j < restrictions.val.length → mAt restrictions j ≤ 10 ^ 9)
    (hid_ne_one : ∀ j : Nat, j < restrictions.val.length → idAt restrictions j ≠ 1)
    (hid_distinct : ((List.range restrictions.val.length).map (fun j => idAt restrictions j)).Nodup)
    (hcount : (restrictions.val.length : Int) ≤ min (n.val - 1) 100000), ∀ r : Std.I64,
      Aegis.MaxBuilding.max_building n restrictions = ok r →
        ∀ i : Int, 1 ≤ i → i ≤ n.val → bfun restrictions i ≤ r.val) := by
  sorry

/-- Whenever max_building(n, restrictions) returns a result r, r = n - 1.
  Preconditions: n is an integer with 2 <= n <= 10^9. restrictions is a list of pairs of 64-bit integers: for every j with 0 <= j < len(restrictions), restrictions[j] has length 2, and writing id_j = restrictions[j][0] and m_j = restrictions[j][1], we have 2 <= id_j <= n, 0 <= m_j <= 10^9, the id_j are pairwise distinct, no id_j equals 1, and len(restrictions) <= min(n-1, 10^5). Additionally len(restrictions) = 0. -/
theorem spec_7 (n : Std.I64) (restrictions : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 10 ^ 9)
    (hlen : ∀ j : Nat, j < restrictions.val.length → (restrictions.val[j]!).val.length = 2)
    (hid_lo : ∀ j : Nat, j < restrictions.val.length → 2 ≤ idAt restrictions j)
    (hid_hi : ∀ j : Nat, j < restrictions.val.length → idAt restrictions j ≤ n.val)
    (hm_lo : ∀ j : Nat, j < restrictions.val.length → 0 ≤ mAt restrictions j)
    (hm_hi : ∀ j : Nat, j < restrictions.val.length → mAt restrictions j ≤ 10 ^ 9)
    (hid_ne_one : ∀ j : Nat, j < restrictions.val.length → idAt restrictions j ≠ 1)
    (hid_distinct : ((List.range restrictions.val.length).map (fun j => idAt restrictions j)).Nodup)
    (hcount : (restrictions.val.length : Int) ≤ min (n.val - 1) 100000)
    (h_empty : restrictions.val.length = 0) :
    ∀ r : Std.I64,
      Aegis.MaxBuilding.max_building n restrictions = ok r → r.val = n.val - 1 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : Std.I64) (restrictions : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 10 ^ 9)
    (hlen : ∀ j : Nat, j < restrictions.val.length → (restrictions.val[j]!).val.length = 2)
    (hid_lo : ∀ j : Nat, j < restrictions.val.length → 2 ≤ idAt restrictions j)
    (hid_hi : ∀ j : Nat, j < restrictions.val.length → idAt restrictions j ≤ n.val)
    (hm_lo : ∀ j : Nat, j < restrictions.val.length → 0 ≤ mAt restrictions j)
    (hm_hi : ∀ j : Nat, j < restrictions.val.length → mAt restrictions j ≤ 10 ^ 9)
    (hid_ne_one : ∀ j : Nat, j < restrictions.val.length → idAt restrictions j ≠ 1)
    (hid_distinct : ((List.range restrictions.val.length).map (fun j => idAt restrictions j)).Nodup)
    (hcount : (restrictions.val.length : Int) ≤ min (n.val - 1) 100000)
    (h_empty : restrictions.val.length = 0), ∀ r : Std.I64,
      Aegis.MaxBuilding.max_building n restrictions = ok r → r.val = n.val - 1) := by
  sorry

/-- Whenever max_building(n, restrictions) returns a result r, r = min(1, m), where m = restrictions[0][1].
  Preconditions: n is an integer with 2 <= n <= 10^9. restrictions is a list of pairs of 64-bit integers: for every j with 0 <= j < len(restrictions), restrictions[j] has length 2, and writing id_j = restrictions[j][0] and m_j = restrictions[j][1], we have 2 <= id_j <= n, 0 <= m_j <= 10^9, the id_j are pairwise distinct, no id_j equals 1, and len(restrictions) <= min(n-1, 10^5). Additionally n = 2 and len(restrictions) = 1; the unique entry must be [2,m]. -/
theorem spec_8 (n : Std.I64) (restrictions : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 10 ^ 9)
    (hlen : ∀ j : Nat, j < restrictions.val.length → (restrictions.val[j]!).val.length = 2)
    (hid_lo : ∀ j : Nat, j < restrictions.val.length → 2 ≤ idAt restrictions j)
    (hid_hi : ∀ j : Nat, j < restrictions.val.length → idAt restrictions j ≤ n.val)
    (hm_lo : ∀ j : Nat, j < restrictions.val.length → 0 ≤ mAt restrictions j)
    (hm_hi : ∀ j : Nat, j < restrictions.val.length → mAt restrictions j ≤ 10 ^ 9)
    (hid_ne_one : ∀ j : Nat, j < restrictions.val.length → idAt restrictions j ≠ 1)
    (hid_distinct : ((List.range restrictions.val.length).map (fun j => idAt restrictions j)).Nodup)
    (hcount : (restrictions.val.length : Int) ≤ min (n.val - 1) 100000)
    (hn_two : n.val = 2) (h_len_one : restrictions.val.length = 1)
    (h_id_two : idAt restrictions 0 = 2) :
    ∀ r : Std.I64,
      Aegis.MaxBuilding.max_building n restrictions = ok r → r.val = min 1 (mAt restrictions 0) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n : Std.I64) (restrictions : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 10 ^ 9)
    (hlen : ∀ j : Nat, j < restrictions.val.length → (restrictions.val[j]!).val.length = 2)
    (hid_lo : ∀ j : Nat, j < restrictions.val.length → 2 ≤ idAt restrictions j)
    (hid_hi : ∀ j : Nat, j < restrictions.val.length → idAt restrictions j ≤ n.val)
    (hm_lo : ∀ j : Nat, j < restrictions.val.length → 0 ≤ mAt restrictions j)
    (hm_hi : ∀ j : Nat, j < restrictions.val.length → mAt restrictions j ≤ 10 ^ 9)
    (hid_ne_one : ∀ j : Nat, j < restrictions.val.length → idAt restrictions j ≠ 1)
    (hid_distinct : ((List.range restrictions.val.length).map (fun j => idAt restrictions j)).Nodup)
    (hcount : (restrictions.val.length : Int) ≤ min (n.val - 1) 100000)
    (hn_two : n.val = 2) (h_len_one : restrictions.val.length = 1)
    (h_id_two : idAt restrictions 0 = 2), ∀ r : Std.I64,
      Aegis.MaxBuilding.max_building n restrictions = ok r → r.val = min 1 (mAt restrictions 0)) := by
  sorry

/-- If max_building(n, restrictions) returns r and max_building(n, restrictions') returns r', then r <= r'.
  Preconditions: n is an integer with 2 <= n <= 10^9. restrictions is a list of pairs of 64-bit integers: for every j with 0 <= j < len(restrictions), restrictions[j] has length 2, and writing id_j = restrictions[j][0] and m_j = restrictions[j][1], we have 2 <= id_j <= n, 0 <= m_j <= 10^9, the id_j are pairwise distinct, no id_j equals 1, and len(restrictions) <= min(n-1, 10^5). Also restrictions' is another list satisfying the same conditions for the same n, has exactly the same set of ids as restrictions, and for each id its maxHeight in restrictions' is at least its maxHeight in restrictions. -/
theorem spec_9 (n : Std.I64) (restrictions restrictions' : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 10 ^ 9)
    (hlen : ∀ j : Nat, j < restrictions.val.length → (restrictions.val[j]!).val.length = 2)
    (hid_lo : ∀ j : Nat, j < restrictions.val.length → 2 ≤ idAt restrictions j)
    (hid_hi : ∀ j : Nat, j < restrictions.val.length → idAt restrictions j ≤ n.val)
    (hm_lo : ∀ j : Nat, j < restrictions.val.length → 0 ≤ mAt restrictions j)
    (hm_hi : ∀ j : Nat, j < restrictions.val.length → mAt restrictions j ≤ 10 ^ 9)
    (hid_ne_one : ∀ j : Nat, j < restrictions.val.length → idAt restrictions j ≠ 1)
    (hid_distinct : ((List.range restrictions.val.length).map (fun j => idAt restrictions j)).Nodup)
    (hcount : (restrictions.val.length : Int) ≤ min (n.val - 1) 100000)
    (hlen' : ∀ j : Nat, j < restrictions'.val.length → (restrictions'.val[j]!).val.length = 2)
    (hid_lo' : ∀ j : Nat, j < restrictions'.val.length → 2 ≤ idAt restrictions' j)
    (hid_hi' : ∀ j : Nat, j < restrictions'.val.length → idAt restrictions' j ≤ n.val)
    (hm_lo' : ∀ j : Nat, j < restrictions'.val.length → 0 ≤ mAt restrictions' j)
    (hm_hi' : ∀ j : Nat, j < restrictions'.val.length → mAt restrictions' j ≤ 10 ^ 9)
    (hid_ne_one' : ∀ j : Nat, j < restrictions'.val.length → idAt restrictions' j ≠ 1)
    (hid_distinct' :
      ((List.range restrictions'.val.length).map (fun j => idAt restrictions' j)).Nodup)
    (hcount' : (restrictions'.val.length : Int) ≤ min (n.val - 1) 100000)
    (hsame_ids : SameIds restrictions restrictions')
    (hheights : HeightsLe restrictions restrictions') :
    ∀ r r' : Std.I64,
      Aegis.MaxBuilding.max_building n restrictions = ok r →
        Aegis.MaxBuilding.max_building n restrictions' = ok r' → r.val ≤ r'.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n : Std.I64) (restrictions restrictions' : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 10 ^ 9)
    (hlen : ∀ j : Nat, j < restrictions.val.length → (restrictions.val[j]!).val.length = 2)
    (hid_lo : ∀ j : Nat, j < restrictions.val.length → 2 ≤ idAt restrictions j)
    (hid_hi : ∀ j : Nat, j < restrictions.val.length → idAt restrictions j ≤ n.val)
    (hm_lo : ∀ j : Nat, j < restrictions.val.length → 0 ≤ mAt restrictions j)
    (hm_hi : ∀ j : Nat, j < restrictions.val.length → mAt restrictions j ≤ 10 ^ 9)
    (hid_ne_one : ∀ j : Nat, j < restrictions.val.length → idAt restrictions j ≠ 1)
    (hid_distinct : ((List.range restrictions.val.length).map (fun j => idAt restrictions j)).Nodup)
    (hcount : (restrictions.val.length : Int) ≤ min (n.val - 1) 100000)
    (hlen' : ∀ j : Nat, j < restrictions'.val.length → (restrictions'.val[j]!).val.length = 2)
    (hid_lo' : ∀ j : Nat, j < restrictions'.val.length → 2 ≤ idAt restrictions' j)
    (hid_hi' : ∀ j : Nat, j < restrictions'.val.length → idAt restrictions' j ≤ n.val)
    (hm_lo' : ∀ j : Nat, j < restrictions'.val.length → 0 ≤ mAt restrictions' j)
    (hm_hi' : ∀ j : Nat, j < restrictions'.val.length → mAt restrictions' j ≤ 10 ^ 9)
    (hid_ne_one' : ∀ j : Nat, j < restrictions'.val.length → idAt restrictions' j ≠ 1)
    (hid_distinct' :
      ((List.range restrictions'.val.length).map (fun j => idAt restrictions' j)).Nodup)
    (hcount' : (restrictions'.val.length : Int) ≤ min (n.val - 1) 100000)
    (hsame_ids : SameIds restrictions restrictions')
    (hheights : HeightsLe restrictions restrictions'), ∀ r r' : Std.I64,
      Aegis.MaxBuilding.max_building n restrictions = ok r →
        Aegis.MaxBuilding.max_building n restrictions' = ok r' → r.val ≤ r'.val) := by
  sorry

/-- If max_building(n, restrictions) returns r and max_building(n, restrictions') returns r', then r = r'.
  Preconditions: n is an integer with 2 <= n <= 10^9. restrictions is a list of pairs of 64-bit integers: for every j with 0 <= j < len(restrictions), restrictions[j] has length 2, and writing id_j = restrictions[j][0] and m_j = restrictions[j][1], we have 2 <= id_j <= n, 0 <= m_j <= 10^9, the id_j are pairwise distinct, no id_j equals 1, and len(restrictions) <= min(n-1, 10^5). Also restrictions' is a permutation of restrictions (same length and same entries, possibly in a different order). -/
theorem spec_10 (n : Std.I64) (restrictions restrictions' : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 10 ^ 9)
    (hlen : ∀ j : Nat, j < restrictions.val.length → (restrictions.val[j]!).val.length = 2)
    (hid_lo : ∀ j : Nat, j < restrictions.val.length → 2 ≤ idAt restrictions j)
    (hid_hi : ∀ j : Nat, j < restrictions.val.length → idAt restrictions j ≤ n.val)
    (hm_lo : ∀ j : Nat, j < restrictions.val.length → 0 ≤ mAt restrictions j)
    (hm_hi : ∀ j : Nat, j < restrictions.val.length → mAt restrictions j ≤ 10 ^ 9)
    (hid_ne_one : ∀ j : Nat, j < restrictions.val.length → idAt restrictions j ≠ 1)
    (hid_distinct : ((List.range restrictions.val.length).map (fun j => idAt restrictions j)).Nodup)
    (hcount : (restrictions.val.length : Int) ≤ min (n.val - 1) 100000)
    (hlen' : ∀ j : Nat, j < restrictions'.val.length → (restrictions'.val[j]!).val.length = 2)
    (hid_lo' : ∀ j : Nat, j < restrictions'.val.length → 2 ≤ idAt restrictions' j)
    (hid_hi' : ∀ j : Nat, j < restrictions'.val.length → idAt restrictions' j ≤ n.val)
    (hm_lo' : ∀ j : Nat, j < restrictions'.val.length → 0 ≤ mAt restrictions' j)
    (hm_hi' : ∀ j : Nat, j < restrictions'.val.length → mAt restrictions' j ≤ 10 ^ 9)
    (hid_ne_one' : ∀ j : Nat, j < restrictions'.val.length → idAt restrictions' j ≠ 1)
    (hid_distinct' :
      ((List.range restrictions'.val.length).map (fun j => idAt restrictions' j)).Nodup)
    (hcount' : (restrictions'.val.length : Int) ≤ min (n.val - 1) 100000)
    (hperm : (pairList restrictions).Perm (pairList restrictions')) :
    ∀ r r' : Std.I64,
      Aegis.MaxBuilding.max_building n restrictions = ok r →
        Aegis.MaxBuilding.max_building n restrictions' = ok r' → r.val = r'.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n : Std.I64) (restrictions restrictions' : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 10 ^ 9)
    (hlen : ∀ j : Nat, j < restrictions.val.length → (restrictions.val[j]!).val.length = 2)
    (hid_lo : ∀ j : Nat, j < restrictions.val.length → 2 ≤ idAt restrictions j)
    (hid_hi : ∀ j : Nat, j < restrictions.val.length → idAt restrictions j ≤ n.val)
    (hm_lo : ∀ j : Nat, j < restrictions.val.length → 0 ≤ mAt restrictions j)
    (hm_hi : ∀ j : Nat, j < restrictions.val.length → mAt restrictions j ≤ 10 ^ 9)
    (hid_ne_one : ∀ j : Nat, j < restrictions.val.length → idAt restrictions j ≠ 1)
    (hid_distinct : ((List.range restrictions.val.length).map (fun j => idAt restrictions j)).Nodup)
    (hcount : (restrictions.val.length : Int) ≤ min (n.val - 1) 100000)
    (hlen' : ∀ j : Nat, j < restrictions'.val.length → (restrictions'.val[j]!).val.length = 2)
    (hid_lo' : ∀ j : Nat, j < restrictions'.val.length → 2 ≤ idAt restrictions' j)
    (hid_hi' : ∀ j : Nat, j < restrictions'.val.length → idAt restrictions' j ≤ n.val)
    (hm_lo' : ∀ j : Nat, j < restrictions'.val.length → 0 ≤ mAt restrictions' j)
    (hm_hi' : ∀ j : Nat, j < restrictions'.val.length → mAt restrictions' j ≤ 10 ^ 9)
    (hid_ne_one' : ∀ j : Nat, j < restrictions'.val.length → idAt restrictions' j ≠ 1)
    (hid_distinct' :
      ((List.range restrictions'.val.length).map (fun j => idAt restrictions' j)).Nodup)
    (hcount' : (restrictions'.val.length : Int) ≤ min (n.val - 1) 100000)
    (hperm : (pairList restrictions).Perm (pairList restrictions')), ∀ r r' : Std.I64,
      Aegis.MaxBuilding.max_building n restrictions = ok r →
        Aegis.MaxBuilding.max_building n restrictions' = ok r' → r.val = r'.val) := by
  sorry

/-- Whenever max_building(n, restrictions) returns a result r, for every j with 0 <= j < len(restrictions), writing id = restrictions[j][0] and m = restrictions[j][1], we have r <= max_{1 <= i <= n} min(i - 1, m + |i - id|).
  Preconditions: n is an integer with 2 <= n <= 10^9. restrictions is a list of pairs of 64-bit integers: for every j with 0 <= j < len(restrictions), restrictions[j] has length 2, and writing id_j = restrictions[j][0] and m_j = restrictions[j][1], we have 2 <= id_j <= n, 0 <= m_j <= 10^9, the id_j are pairwise distinct, no id_j equals 1, and len(restrictions) <= min(n-1, 10^5). -/
theorem spec_11 (n : Std.I64) (restrictions : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 10 ^ 9)
    (hlen : ∀ j : Nat, j < restrictions.val.length → (restrictions.val[j]!).val.length = 2)
    (hid_lo : ∀ j : Nat, j < restrictions.val.length → 2 ≤ idAt restrictions j)
    (hid_hi : ∀ j : Nat, j < restrictions.val.length → idAt restrictions j ≤ n.val)
    (hm_lo : ∀ j : Nat, j < restrictions.val.length → 0 ≤ mAt restrictions j)
    (hm_hi : ∀ j : Nat, j < restrictions.val.length → mAt restrictions j ≤ 10 ^ 9)
    (hid_ne_one : ∀ j : Nat, j < restrictions.val.length → idAt restrictions j ≠ 1)
    (hid_distinct : ((List.range restrictions.val.length).map (fun j => idAt restrictions j)).Nodup)
    (hcount : (restrictions.val.length : Int) ≤ min (n.val - 1) 100000) :
    ∀ r : Std.I64,
      Aegis.MaxBuilding.max_building n restrictions = ok r →
        ∀ j : Nat,
          j < restrictions.val.length →
            r.val ≤
              maxOverLabels n.val
                (fun i => min (i - 1) (mAt restrictions j + iabs (i - idAt restrictions j))) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (n : Std.I64) (restrictions : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 10 ^ 9)
    (hlen : ∀ j : Nat, j < restrictions.val.length → (restrictions.val[j]!).val.length = 2)
    (hid_lo : ∀ j : Nat, j < restrictions.val.length → 2 ≤ idAt restrictions j)
    (hid_hi : ∀ j : Nat, j < restrictions.val.length → idAt restrictions j ≤ n.val)
    (hm_lo : ∀ j : Nat, j < restrictions.val.length → 0 ≤ mAt restrictions j)
    (hm_hi : ∀ j : Nat, j < restrictions.val.length → mAt restrictions j ≤ 10 ^ 9)
    (hid_ne_one : ∀ j : Nat, j < restrictions.val.length → idAt restrictions j ≠ 1)
    (hid_distinct : ((List.range restrictions.val.length).map (fun j => idAt restrictions j)).Nodup)
    (hcount : (restrictions.val.length : Int) ≤ min (n.val - 1) 100000), ∀ r : Std.I64,
      Aegis.MaxBuilding.max_building n restrictions = ok r →
        ∀ j : Nat,
          j < restrictions.val.length →
            r.val ≤
              maxOverLabels n.val
                (fun i => min (i - 1) (mAt restrictions j + iabs (i - idAt restrictions j)))) := by
  sorry

/-- Whenever max_building(n, restrictions) returns a result r, the function B(i) = min( {i-1} union { m_j + |i - id_j| : 0 <= j < len(restrictions) } ) is a feasible height sequence and r = max_{1 <= i <= n} B(i).
  Preconditions: n is an integer with 2 <= n <= 10^9. restrictions is a list of pairs of 64-bit integers: for every j with 0 <= j < len(restrictions), restrictions[j] has length 2, and writing id_j = restrictions[j][0] and m_j = restrictions[j][1], we have 2 <= id_j <= n, 0 <= m_j <= 10^9, the id_j are pairwise distinct, no id_j equals 1, and len(restrictions) <= min(n-1, 10^5). -/
theorem spec_12 (n : Std.I64) (restrictions : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 10 ^ 9)
    (hlen : ∀ j : Nat, j < restrictions.val.length → (restrictions.val[j]!).val.length = 2)
    (hid_lo : ∀ j : Nat, j < restrictions.val.length → 2 ≤ idAt restrictions j)
    (hid_hi : ∀ j : Nat, j < restrictions.val.length → idAt restrictions j ≤ n.val)
    (hm_lo : ∀ j : Nat, j < restrictions.val.length → 0 ≤ mAt restrictions j)
    (hm_hi : ∀ j : Nat, j < restrictions.val.length → mAt restrictions j ≤ 10 ^ 9)
    (hid_ne_one : ∀ j : Nat, j < restrictions.val.length → idAt restrictions j ≠ 1)
    (hid_distinct : ((List.range restrictions.val.length).map (fun j => idAt restrictions j)).Nodup)
    (hcount : (restrictions.val.length : Int) ≤ min (n.val - 1) 100000) :
    ∀ r : Std.I64,
      Aegis.MaxBuilding.max_building n restrictions = ok r →
        Feasible n.val restrictions (bfun restrictions) ∧
          r.val = maxOverLabels n.val (bfun restrictions) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (n : Std.I64) (restrictions : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 10 ^ 9)
    (hlen : ∀ j : Nat, j < restrictions.val.length → (restrictions.val[j]!).val.length = 2)
    (hid_lo : ∀ j : Nat, j < restrictions.val.length → 2 ≤ idAt restrictions j)
    (hid_hi : ∀ j : Nat, j < restrictions.val.length → idAt restrictions j ≤ n.val)
    (hm_lo : ∀ j : Nat, j < restrictions.val.length → 0 ≤ mAt restrictions j)
    (hm_hi : ∀ j : Nat, j < restrictions.val.length → mAt restrictions j ≤ 10 ^ 9)
    (hid_ne_one : ∀ j : Nat, j < restrictions.val.length → idAt restrictions j ≠ 1)
    (hid_distinct : ((List.range restrictions.val.length).map (fun j => idAt restrictions j)).Nodup)
    (hcount : (restrictions.val.length : Int) ≤ min (n.val - 1) 100000), ∀ r : Std.I64,
      Aegis.MaxBuilding.max_building n restrictions = ok r →
        Feasible n.val restrictions (bfun restrictions) ∧
          r.val = maxOverLabels n.val (bfun restrictions)) := by
  sorry

end AegisSpec.MaxBuilding
