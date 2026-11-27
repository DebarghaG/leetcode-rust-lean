import Aegis.MaxEnvelopes.Code.Funs

/-!
# Specifications of `Aegis.MaxEnvelopes.max_envelopes`

LeetCode problem `russian-doll-envelopes`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

set_option autoImplicit false

namespace AegisSpec.MaxEnvelopes

def width (e : alloc.vec.Vec Std.I64) : Int := ((e.val[0]?).map (fun x => x.val)).getD 0

def height (e : alloc.vec.Vec Std.I64) : Int := ((e.val[1]?).map (fun x => x.val)).getD 0

def widthAt (es : List (alloc.vec.Vec Std.I64)) (i : Nat) : Int := ((es[i]?).map width).getD 0

def heightAt (es : List (alloc.vec.Vec Std.I64)) (i : Nat) : Int := ((es[i]?).map height).getD 0

def lenAt (es : List (alloc.vec.Vec Std.I64)) (i : Nat) : Nat :=
  ((es[i]?).map (fun v => v.val.length)).getD 0

def distinctWidths (es : List (alloc.vec.Vec Std.I64)) : Nat :=
  (es.map width).toFinset.card

def distinctHeights (es : List (alloc.vec.Vec Std.I64)) : Nat :=
  (es.map height).toFinset.card

def HasChain (es : List (alloc.vec.Vec Std.I64)) (k : Nat) : Prop :=
  ∃ f : Fin k → Fin es.length,
    Function.Injective f ∧
      ∀ p q : Fin k,
        p < q →
          widthAt es (f p).val < widthAt es (f q).val ∧
            heightAt es (f p).val < heightAt es (f q).val

def swapAt (es : List (alloc.vec.Vec Std.I64)) (i j : Nat) : List (alloc.vec.Vec Std.I64) :=
  (es.set i (es.getD j default)).set j (es.getD i default)

def eraseAt (es : List (alloc.vec.Vec Std.I64)) (j : Nat) : List (alloc.vec.Vec Std.I64) :=
  es.eraseIdx j

/-- Whenever max_envelopes(envelopes) returns a result r, r is the largest nonnegative integer k for which there exist pairwise distinct indices i_0, ..., i_{k-1} in {0, ..., len(envelopes)-1} such that, for every p and q with 0 <= p < q < k, both envelopes[i_p][0] < envelopes[i_q][0] and envelopes[i_p][1] < envelopes[i_q][1].
  Preconditions: envelopes is a nonempty slice with len(envelopes) <= 100000; for every i with 0 <= i < len(envelopes), len(envelopes[i]) = 2, and 1 <= envelopes[i][0] <= 100000 and 1 <= envelopes[i][1] <= 100000. -/
theorem spec_1 (envelopes : Slice (alloc.vec.Vec Std.I64))
    (hne : 0 < envelopes.val.length) (hlen : envelopes.val.length ≤ 100000)
    (h2 : ∀ i, i < envelopes.val.length → lenAt envelopes.val i = 2)
    (hb : ∀ i, i < envelopes.val.length →
      1 ≤ widthAt envelopes.val i ∧ widthAt envelopes.val i ≤ 100000 ∧
        1 ≤ heightAt envelopes.val i ∧ heightAt envelopes.val i ≤ 100000)
    (r : Std.I64) (hres : Aegis.MaxEnvelopes.max_envelopes envelopes = ok r) :
    0 ≤ r.val ∧ HasChain envelopes.val r.val.toNat ∧
      ∀ k : Nat, HasChain envelopes.val k → (k : Int) ≤ r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (envelopes : Slice (alloc.vec.Vec Std.I64))
    (hne : 0 < envelopes.val.length) (hlen : envelopes.val.length ≤ 100000)
    (h2 : ∀ i, i < envelopes.val.length → lenAt envelopes.val i = 2)
    (hb : ∀ i, i < envelopes.val.length →
      1 ≤ widthAt envelopes.val i ∧ widthAt envelopes.val i ≤ 100000 ∧
        1 ≤ heightAt envelopes.val i ∧ heightAt envelopes.val i ≤ 100000)
    (r : Std.I64) (hres : Aegis.MaxEnvelopes.max_envelopes envelopes = ok r), 0 ≤ r.val ∧ HasChain envelopes.val r.val.toNat ∧
      ∀ k : Nat, HasChain envelopes.val k → (k : Int) ≤ r.val) := by
  sorry

/-- For every envelopes satisfying the preconditions, max_envelopes(envelopes) does not fail: it returns a result r (no panic, out-of-bounds index, or arithmetic overflow).
  Preconditions: envelopes is a nonempty slice with len(envelopes) <= 100000; for every i with 0 <= i < len(envelopes), len(envelopes[i]) = 2, and 1 <= envelopes[i][0] <= 100000 and 1 <= envelopes[i][1] <= 100000. -/
theorem spec_2 (envelopes : Slice (alloc.vec.Vec Std.I64))
    (hne : 0 < envelopes.val.length) (hlen : envelopes.val.length ≤ 100000)
    (h2 : ∀ i, i < envelopes.val.length → lenAt envelopes.val i = 2)
    (hb : ∀ i, i < envelopes.val.length →
      1 ≤ widthAt envelopes.val i ∧ widthAt envelopes.val i ≤ 100000 ∧
        1 ≤ heightAt envelopes.val i ∧ heightAt envelopes.val i ≤ 100000) :
    ∃ r : Std.I64, Aegis.MaxEnvelopes.max_envelopes envelopes = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (envelopes : Slice (alloc.vec.Vec Std.I64))
    (hne : 0 < envelopes.val.length) (hlen : envelopes.val.length ≤ 100000)
    (h2 : ∀ i, i < envelopes.val.length → lenAt envelopes.val i = 2)
    (hb : ∀ i, i < envelopes.val.length →
      1 ≤ widthAt envelopes.val i ∧ widthAt envelopes.val i ≤ 100000 ∧
        1 ≤ heightAt envelopes.val i ∧ heightAt envelopes.val i ≤ 100000), ∃ r : Std.I64, Aegis.MaxEnvelopes.max_envelopes envelopes = ok r) := by
  sorry

/-- Whenever max_envelopes(envelopes) returns r, r >= 1.
  Preconditions: envelopes is a nonempty slice with len(envelopes) <= 100000; for every i with 0 <= i < len(envelopes), len(envelopes[i]) = 2, and 1 <= envelopes[i][0] <= 100000 and 1 <= envelopes[i][1] <= 100000. -/
theorem spec_3 (envelopes : Slice (alloc.vec.Vec Std.I64))
    (hne : 0 < envelopes.val.length) (hlen : envelopes.val.length ≤ 100000)
    (h2 : ∀ i, i < envelopes.val.length → lenAt envelopes.val i = 2)
    (hb : ∀ i, i < envelopes.val.length →
      1 ≤ widthAt envelopes.val i ∧ widthAt envelopes.val i ≤ 100000 ∧
        1 ≤ heightAt envelopes.val i ∧ heightAt envelopes.val i ≤ 100000)
    (r : Std.I64) (hres : Aegis.MaxEnvelopes.max_envelopes envelopes = ok r) :
    1 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (envelopes : Slice (alloc.vec.Vec Std.I64))
    (hne : 0 < envelopes.val.length) (hlen : envelopes.val.length ≤ 100000)
    (h2 : ∀ i, i < envelopes.val.length → lenAt envelopes.val i = 2)
    (hb : ∀ i, i < envelopes.val.length →
      1 ≤ widthAt envelopes.val i ∧ widthAt envelopes.val i ≤ 100000 ∧
        1 ≤ heightAt envelopes.val i ∧ heightAt envelopes.val i ≤ 100000)
    (r : Std.I64) (hres : Aegis.MaxEnvelopes.max_envelopes envelopes = ok r), 1 ≤ r.val) := by
  sorry

/-- Whenever max_envelopes(envelopes) returns r, r <= len(envelopes).
  Preconditions: envelopes is a nonempty slice with len(envelopes) <= 100000; for every i with 0 <= i < len(envelopes), len(envelopes[i]) = 2, and 1 <= envelopes[i][0] <= 100000 and 1 <= envelopes[i][1] <= 100000. -/
theorem spec_4 (envelopes : Slice (alloc.vec.Vec Std.I64))
    (hne : 0 < envelopes.val.length) (hlen : envelopes.val.length ≤ 100000)
    (h2 : ∀ i, i < envelopes.val.length → lenAt envelopes.val i = 2)
    (hb : ∀ i, i < envelopes.val.length →
      1 ≤ widthAt envelopes.val i ∧ widthAt envelopes.val i ≤ 100000 ∧
        1 ≤ heightAt envelopes.val i ∧ heightAt envelopes.val i ≤ 100000)
    (r : Std.I64) (hres : Aegis.MaxEnvelopes.max_envelopes envelopes = ok r) :
    r.val ≤ (envelopes.val.length : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (envelopes : Slice (alloc.vec.Vec Std.I64))
    (hne : 0 < envelopes.val.length) (hlen : envelopes.val.length ≤ 100000)
    (h2 : ∀ i, i < envelopes.val.length → lenAt envelopes.val i = 2)
    (hb : ∀ i, i < envelopes.val.length →
      1 ≤ widthAt envelopes.val i ∧ widthAt envelopes.val i ≤ 100000 ∧
        1 ≤ heightAt envelopes.val i ∧ heightAt envelopes.val i ≤ 100000)
    (r : Std.I64) (hres : Aegis.MaxEnvelopes.max_envelopes envelopes = ok r), r.val ≤ (envelopes.val.length : Int)) := by
  sorry

/-- Whenever max_envelopes(envelopes) returns r, let W be the number of distinct values in { envelopes[i][0] | 0 <= i < len(envelopes) } and H be the number of distinct values in { envelopes[i][1] | 0 <= i < len(envelopes) }; then r <= W and r <= H.
  Preconditions: envelopes is a nonempty slice with len(envelopes) <= 100000; for every i with 0 <= i < len(envelopes), len(envelopes[i]) = 2, and 1 <= envelopes[i][0] <= 100000 and 1 <= envelopes[i][1] <= 100000. -/
theorem spec_5 (envelopes : Slice (alloc.vec.Vec Std.I64))
    (hne : 0 < envelopes.val.length) (hlen : envelopes.val.length ≤ 100000)
    (h2 : ∀ i, i < envelopes.val.length → lenAt envelopes.val i = 2)
    (hb : ∀ i, i < envelopes.val.length →
      1 ≤ widthAt envelopes.val i ∧ widthAt envelopes.val i ≤ 100000 ∧
        1 ≤ heightAt envelopes.val i ∧ heightAt envelopes.val i ≤ 100000)
    (r : Std.I64) (hres : Aegis.MaxEnvelopes.max_envelopes envelopes = ok r) :
    r.val ≤ (distinctWidths envelopes.val : Int) ∧
      r.val ≤ (distinctHeights envelopes.val : Int) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (envelopes : Slice (alloc.vec.Vec Std.I64))
    (hne : 0 < envelopes.val.length) (hlen : envelopes.val.length ≤ 100000)
    (h2 : ∀ i, i < envelopes.val.length → lenAt envelopes.val i = 2)
    (hb : ∀ i, i < envelopes.val.length →
      1 ≤ widthAt envelopes.val i ∧ widthAt envelopes.val i ≤ 100000 ∧
        1 ≤ heightAt envelopes.val i ∧ heightAt envelopes.val i ≤ 100000)
    (r : Std.I64) (hres : Aegis.MaxEnvelopes.max_envelopes envelopes = ok r), r.val ≤ (distinctWidths envelopes.val : Int) ∧
      r.val ≤ (distinctHeights envelopes.val : Int)) := by
  sorry

/-- Whenever max_envelopes(envelopes) returns r, r = 1 if and only if there do not exist distinct indices i and j with 0 <= i < len(envelopes) and 0 <= j < len(envelopes) such that envelopes[i][0] < envelopes[j][0] and envelopes[i][1] < envelopes[j][1].
  Preconditions: envelopes is a nonempty slice with len(envelopes) <= 100000; for every i with 0 <= i < len(envelopes), len(envelopes[i]) = 2, and 1 <= envelopes[i][0] <= 100000 and 1 <= envelopes[i][1] <= 100000. -/
theorem spec_6 (envelopes : Slice (alloc.vec.Vec Std.I64))
    (hne : 0 < envelopes.val.length) (hlen : envelopes.val.length ≤ 100000)
    (h2 : ∀ i, i < envelopes.val.length → lenAt envelopes.val i = 2)
    (hb : ∀ i, i < envelopes.val.length →
      1 ≤ widthAt envelopes.val i ∧ widthAt envelopes.val i ≤ 100000 ∧
        1 ≤ heightAt envelopes.val i ∧ heightAt envelopes.val i ≤ 100000)
    (r : Std.I64) (hres : Aegis.MaxEnvelopes.max_envelopes envelopes = ok r) :
    (r.val = 1 ↔
      ¬ ∃ i j : Nat,
          i < envelopes.val.length ∧ j < envelopes.val.length ∧ i ≠ j ∧
            widthAt envelopes.val i < widthAt envelopes.val j ∧
              heightAt envelopes.val i < heightAt envelopes.val j) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (envelopes : Slice (alloc.vec.Vec Std.I64))
    (hne : 0 < envelopes.val.length) (hlen : envelopes.val.length ≤ 100000)
    (h2 : ∀ i, i < envelopes.val.length → lenAt envelopes.val i = 2)
    (hb : ∀ i, i < envelopes.val.length →
      1 ≤ widthAt envelopes.val i ∧ widthAt envelopes.val i ≤ 100000 ∧
        1 ≤ heightAt envelopes.val i ∧ heightAt envelopes.val i ≤ 100000)
    (r : Std.I64) (hres : Aegis.MaxEnvelopes.max_envelopes envelopes = ok r), (r.val = 1 ↔
      ¬ ∃ i j : Nat,
          i < envelopes.val.length ∧ j < envelopes.val.length ∧ i ≠ j ∧
            widthAt envelopes.val i < widthAt envelopes.val j ∧
              heightAt envelopes.val i < heightAt envelopes.val j)) := by
  sorry

/-- For every i and j with 0 <= i < len(envelopes) and 0 <= j < len(envelopes), let envelopes' be the slice obtained from envelopes by exchanging entries i and j. Whenever max_envelopes(envelopes) returns r and max_envelopes(envelopes') returns r', we have r = r'.
  Preconditions: envelopes is a nonempty slice with len(envelopes) <= 100000; for every i with 0 <= i < len(envelopes), len(envelopes[i]) = 2, and 1 <= envelopes[i][0] <= 100000 and 1 <= envelopes[i][1] <= 100000. -/
theorem spec_7 (envelopes : Slice (alloc.vec.Vec Std.I64))
    (hne : 0 < envelopes.val.length) (hlen : envelopes.val.length ≤ 100000)
    (h2 : ∀ i, i < envelopes.val.length → lenAt envelopes.val i = 2)
    (hb : ∀ i, i < envelopes.val.length →
      1 ≤ widthAt envelopes.val i ∧ widthAt envelopes.val i ≤ 100000 ∧
        1 ≤ heightAt envelopes.val i ∧ heightAt envelopes.val i ≤ 100000)
    (i j : Nat) (hi : i < envelopes.val.length) (hj : j < envelopes.val.length)
    (envelopes' : Slice (alloc.vec.Vec Std.I64))
    (h' : envelopes'.val = swapAt envelopes.val i j)
    (r r' : Std.I64)
    (hres : Aegis.MaxEnvelopes.max_envelopes envelopes = ok r)
    (hres' : Aegis.MaxEnvelopes.max_envelopes envelopes' = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (envelopes : Slice (alloc.vec.Vec Std.I64))
    (hne : 0 < envelopes.val.length) (hlen : envelopes.val.length ≤ 100000)
    (h2 : ∀ i, i < envelopes.val.length → lenAt envelopes.val i = 2)
    (hb : ∀ i, i < envelopes.val.length →
      1 ≤ widthAt envelopes.val i ∧ widthAt envelopes.val i ≤ 100000 ∧
        1 ≤ heightAt envelopes.val i ∧ heightAt envelopes.val i ≤ 100000)
    (i j : Nat) (hi : i < envelopes.val.length) (hj : j < envelopes.val.length)
    (envelopes' : Slice (alloc.vec.Vec Std.I64))
    (h' : envelopes'.val = swapAt envelopes.val i j)
    (r r' : Std.I64)
    (hres : Aegis.MaxEnvelopes.max_envelopes envelopes = ok r)
    (hres' : Aegis.MaxEnvelopes.max_envelopes envelopes' = ok r'), r.val = r'.val) := by
  sorry

/-- For any such i and j, let envelopes' be the slice obtained by deleting entry j. Whenever max_envelopes(envelopes) returns r and max_envelopes(envelopes') returns r', we have r' = r.
  Preconditions: envelopes is a nonempty slice with len(envelopes) <= 100000; for every i with 0 <= i < len(envelopes), len(envelopes[i]) = 2, and 1 <= envelopes[i][0] <= 100000 and 1 <= envelopes[i][1] <= 100000; there exist i and j with 0 <= i < j < len(envelopes) such that envelopes[i][0] = envelopes[j][0] and envelopes[i][1] = envelopes[j][1]. -/
theorem spec_8 (envelopes : Slice (alloc.vec.Vec Std.I64))
    (hne : 0 < envelopes.val.length) (hlen : envelopes.val.length ≤ 100000)
    (h2 : ∀ i, i < envelopes.val.length → lenAt envelopes.val i = 2)
    (hb : ∀ i, i < envelopes.val.length →
      1 ≤ widthAt envelopes.val i ∧ widthAt envelopes.val i ≤ 100000 ∧
        1 ≤ heightAt envelopes.val i ∧ heightAt envelopes.val i ≤ 100000)
    (i j : Nat) (hi : i < envelopes.val.length) (hj : j < envelopes.val.length)
    (hij : i < j)
    (hdup : widthAt envelopes.val i = widthAt envelopes.val j ∧
      heightAt envelopes.val i = heightAt envelopes.val j)
    (envelopes' : Slice (alloc.vec.Vec Std.I64))
    (h' : envelopes'.val = eraseAt envelopes.val j)
    (r r' : Std.I64)
    (hres : Aegis.MaxEnvelopes.max_envelopes envelopes = ok r)
    (hres' : Aegis.MaxEnvelopes.max_envelopes envelopes' = ok r') :
    r'.val = r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (envelopes : Slice (alloc.vec.Vec Std.I64))
    (hne : 0 < envelopes.val.length) (hlen : envelopes.val.length ≤ 100000)
    (h2 : ∀ i, i < envelopes.val.length → lenAt envelopes.val i = 2)
    (hb : ∀ i, i < envelopes.val.length →
      1 ≤ widthAt envelopes.val i ∧ widthAt envelopes.val i ≤ 100000 ∧
        1 ≤ heightAt envelopes.val i ∧ heightAt envelopes.val i ≤ 100000)
    (i j : Nat) (hi : i < envelopes.val.length) (hj : j < envelopes.val.length)
    (hij : i < j)
    (hdup : widthAt envelopes.val i = widthAt envelopes.val j ∧
      heightAt envelopes.val i = heightAt envelopes.val j)
    (envelopes' : Slice (alloc.vec.Vec Std.I64))
    (h' : envelopes'.val = eraseAt envelopes.val j)
    (r r' : Std.I64)
    (hres : Aegis.MaxEnvelopes.max_envelopes envelopes = ok r)
    (hres' : Aegis.MaxEnvelopes.max_envelopes envelopes' = ok r'), r'.val = r.val) := by
  sorry

/-- For every integers w and h with 1 <= w <= 100000 and 1 <= h <= 100000, let envelopes' be envelopes with the single entry [w, h] appended. Whenever max_envelopes(envelopes) returns r and max_envelopes(envelopes') returns r', we have r' >= r.
  Preconditions: envelopes is a nonempty slice with len(envelopes) < 100000; for every i with 0 <= i < len(envelopes), len(envelopes[i]) = 2, and 1 <= envelopes[i][0] <= 100000 and 1 <= envelopes[i][1] <= 100000. -/
theorem spec_9 (envelopes : Slice (alloc.vec.Vec Std.I64))
    (hne : 0 < envelopes.val.length) (hlen : envelopes.val.length < 100000)
    (h2 : ∀ i, i < envelopes.val.length → lenAt envelopes.val i = 2)
    (hb : ∀ i, i < envelopes.val.length →
      1 ≤ widthAt envelopes.val i ∧ widthAt envelopes.val i ≤ 100000 ∧
        1 ≤ heightAt envelopes.val i ∧ heightAt envelopes.val i ≤ 100000)
    (w h : Int) (hw1 : 1 ≤ w) (hw2 : w ≤ 100000) (hh1 : 1 ≤ h) (hh2 : h ≤ 100000)
    (e : alloc.vec.Vec Std.I64) (he : e.val.map (fun x => x.val) = [w, h])
    (envelopes' : Slice (alloc.vec.Vec Std.I64))
    (h' : envelopes'.val = envelopes.val ++ [e])
    (r r' : Std.I64)
    (hres : Aegis.MaxEnvelopes.max_envelopes envelopes = ok r)
    (hres' : Aegis.MaxEnvelopes.max_envelopes envelopes' = ok r') :
    r.val ≤ r'.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (envelopes : Slice (alloc.vec.Vec Std.I64))
    (hne : 0 < envelopes.val.length) (hlen : envelopes.val.length < 100000)
    (h2 : ∀ i, i < envelopes.val.length → lenAt envelopes.val i = 2)
    (hb : ∀ i, i < envelopes.val.length →
      1 ≤ widthAt envelopes.val i ∧ widthAt envelopes.val i ≤ 100000 ∧
        1 ≤ heightAt envelopes.val i ∧ heightAt envelopes.val i ≤ 100000)
    (w h : Int) (hw1 : 1 ≤ w) (hw2 : w ≤ 100000) (hh1 : 1 ≤ h) (hh2 : h ≤ 100000)
    (e : alloc.vec.Vec Std.I64) (he : e.val.map (fun x => x.val) = [w, h])
    (envelopes' : Slice (alloc.vec.Vec Std.I64))
    (h' : envelopes'.val = envelopes.val ++ [e])
    (r r' : Std.I64)
    (hres : Aegis.MaxEnvelopes.max_envelopes envelopes = ok r)
    (hres' : Aegis.MaxEnvelopes.max_envelopes envelopes' = ok r'), r.val ≤ r'.val) := by
  sorry

/-- Whenever max_envelopes(envelopes) returns r, r = len(envelopes) if and only if there exists a permutation pi of {0, ..., len(envelopes)-1} such that, for every p and q with 0 <= p < q < len(envelopes), envelopes[pi(p)][0] < envelopes[pi(q)][0] and envelopes[pi(p)][1] < envelopes[pi(q)][1].
  Preconditions: envelopes is a nonempty slice with len(envelopes) <= 100000; for every i with 0 <= i < len(envelopes), len(envelopes[i]) = 2, and 1 <= envelopes[i][0] <= 100000 and 1 <= envelopes[i][1] <= 100000. -/
theorem spec_10 (envelopes : Slice (alloc.vec.Vec Std.I64))
    (hne : 0 < envelopes.val.length) (hlen : envelopes.val.length ≤ 100000)
    (h2 : ∀ i, i < envelopes.val.length → lenAt envelopes.val i = 2)
    (hb : ∀ i, i < envelopes.val.length →
      1 ≤ widthAt envelopes.val i ∧ widthAt envelopes.val i ≤ 100000 ∧
        1 ≤ heightAt envelopes.val i ∧ heightAt envelopes.val i ≤ 100000)
    (r : Std.I64) (hres : Aegis.MaxEnvelopes.max_envelopes envelopes = ok r) :
    (r.val = (envelopes.val.length : Int) ↔
      ∃ pi : Fin envelopes.val.length → Fin envelopes.val.length,
        Function.Bijective pi ∧
          ∀ p q : Fin envelopes.val.length,
            p < q →
              widthAt envelopes.val (pi p).val < widthAt envelopes.val (pi q).val ∧
                heightAt envelopes.val (pi p).val < heightAt envelopes.val (pi q).val) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (envelopes : Slice (alloc.vec.Vec Std.I64))
    (hne : 0 < envelopes.val.length) (hlen : envelopes.val.length ≤ 100000)
    (h2 : ∀ i, i < envelopes.val.length → lenAt envelopes.val i = 2)
    (hb : ∀ i, i < envelopes.val.length →
      1 ≤ widthAt envelopes.val i ∧ widthAt envelopes.val i ≤ 100000 ∧
        1 ≤ heightAt envelopes.val i ∧ heightAt envelopes.val i ≤ 100000)
    (r : Std.I64) (hres : Aegis.MaxEnvelopes.max_envelopes envelopes = ok r), (r.val = (envelopes.val.length : Int) ↔
      ∃ pi : Fin envelopes.val.length → Fin envelopes.val.length,
        Function.Bijective pi ∧
          ∀ p q : Fin envelopes.val.length,
            p < q →
              widthAt envelopes.val (pi p).val < widthAt envelopes.val (pi q).val ∧
                heightAt envelopes.val (pi p).val < heightAt envelopes.val (pi q).val)) := by
  sorry

/-- Whenever max_envelopes(envelopes) returns r, there exist pairwise distinct indices i_0, ..., i_{r-1} in {0, ..., len(envelopes)-1} such that, for every p and q with 0 <= p < q < r, envelopes[i_p][0] < envelopes[i_q][0] and envelopes[i_p][1] < envelopes[i_q][1].
  Preconditions: envelopes is a nonempty slice with len(envelopes) <= 100000; for every i with 0 <= i < len(envelopes), len(envelopes[i]) = 2, and 1 <= envelopes[i][0] <= 100000 and 1 <= envelopes[i][1] <= 100000. -/
theorem spec_11 (envelopes : Slice (alloc.vec.Vec Std.I64))
    (hne : 0 < envelopes.val.length) (hlen : envelopes.val.length ≤ 100000)
    (h2 : ∀ i, i < envelopes.val.length → lenAt envelopes.val i = 2)
    (hb : ∀ i, i < envelopes.val.length →
      1 ≤ widthAt envelopes.val i ∧ widthAt envelopes.val i ≤ 100000 ∧
        1 ≤ heightAt envelopes.val i ∧ heightAt envelopes.val i ≤ 100000)
    (r : Std.I64) (hres : Aegis.MaxEnvelopes.max_envelopes envelopes = ok r) :
    HasChain envelopes.val r.val.toNat := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (envelopes : Slice (alloc.vec.Vec Std.I64))
    (hne : 0 < envelopes.val.length) (hlen : envelopes.val.length ≤ 100000)
    (h2 : ∀ i, i < envelopes.val.length → lenAt envelopes.val i = 2)
    (hb : ∀ i, i < envelopes.val.length →
      1 ≤ widthAt envelopes.val i ∧ widthAt envelopes.val i ≤ 100000 ∧
        1 ≤ heightAt envelopes.val i ∧ heightAt envelopes.val i ≤ 100000)
    (r : Std.I64) (hres : Aegis.MaxEnvelopes.max_envelopes envelopes = ok r), HasChain envelopes.val r.val.toNat) := by
  sorry

/-- Whenever max_envelopes(envelopes) returns r, for every nonnegative integer k and every sequence of pairwise distinct indices i_0, ..., i_{k-1} in {0, ..., len(envelopes)-1}, if for all p and q with 0 <= p < q < k we have envelopes[i_p][0] < envelopes[i_q][0] and envelopes[i_p][1] < envelopes[i_q][1], then k <= r.
  Preconditions: envelopes is a nonempty slice with len(envelopes) <= 100000; for every i with 0 <= i < len(envelopes), len(envelopes[i]) = 2, and 1 <= envelopes[i][0] <= 100000 and 1 <= envelopes[i][1] <= 100000. -/
theorem spec_12 (envelopes : Slice (alloc.vec.Vec Std.I64))
    (hne : 0 < envelopes.val.length) (hlen : envelopes.val.length ≤ 100000)
    (h2 : ∀ i, i < envelopes.val.length → lenAt envelopes.val i = 2)
    (hb : ∀ i, i < envelopes.val.length →
      1 ≤ widthAt envelopes.val i ∧ widthAt envelopes.val i ≤ 100000 ∧
        1 ≤ heightAt envelopes.val i ∧ heightAt envelopes.val i ≤ 100000)
    (r : Std.I64) (hres : Aegis.MaxEnvelopes.max_envelopes envelopes = ok r) :
    ∀ k : Nat, HasChain envelopes.val k → (k : Int) ≤ r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (envelopes : Slice (alloc.vec.Vec Std.I64))
    (hne : 0 < envelopes.val.length) (hlen : envelopes.val.length ≤ 100000)
    (h2 : ∀ i, i < envelopes.val.length → lenAt envelopes.val i = 2)
    (hb : ∀ i, i < envelopes.val.length →
      1 ≤ widthAt envelopes.val i ∧ widthAt envelopes.val i ≤ 100000 ∧
        1 ≤ heightAt envelopes.val i ∧ heightAt envelopes.val i ≤ 100000)
    (r : Std.I64) (hres : Aegis.MaxEnvelopes.max_envelopes envelopes = ok r), ∀ k : Nat, HasChain envelopes.val k → (k : Int) ≤ r.val) := by
  sorry

end AegisSpec.MaxEnvelopes
