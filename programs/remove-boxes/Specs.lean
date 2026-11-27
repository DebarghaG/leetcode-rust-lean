import Aegis.RemoveBoxes.Code.Funs

/-!
# Specifications of `Aegis.RemoveBoxes.remove_boxes`

LeetCode problem `remove-boxes`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.RemoveBoxes

def values (boxes : Slice I64) : List ℤ := boxes.val.map (fun x => x.val)

def valueAt (boxes : Slice I64) (i : ℕ) : ℤ :=
  match boxes.val[i]? with
  | some x => x.val
  | none => 0

def occurrences (c : ℤ) (l : List ℤ) : ℕ := (l.filter (fun x => decide (x = c))).length

def OccursOnce (c : ℤ) (l : List ℤ) : Prop := occurrences c l = 1

def runsAux (i start : ℕ) (prev : ℤ) : List ℤ → List (ℕ × ℕ)
  | [] => [(start, i - 1)]
  | y :: ys =>
    if y = prev then runsAux (i + 1) start prev ys
    else (start, i - 1) :: runsAux (i + 1) i y ys

def runs : List ℤ → List (ℕ × ℕ)
  | [] => []
  | x :: xs => runsAux 1 0 x xs

def runsScore (l : List ℤ) : ℕ :=
  ((runs l).map (fun p => (p.2 - p.1 + 1) * (p.2 - p.1 + 1))).sum

def colorScore (l : List ℤ) : ℕ := l.toFinset.sum (fun c => occurrences c l * occurrences c l)

structure IsValidRemoval (l : List ℤ) (m : ℕ) (G : ℕ → Finset ℕ) : Prop where

  nonempty : 1 ≤ m

  groups_nonempty : ∀ t, t < m → (G t).Nonempty

  in_range : ∀ t, t < m → ∀ i ∈ G t, i < l.length

  cover : ∀ i, i < l.length → ∃ t, t < m ∧ i ∈ G t

  disjoint : ∀ t₁ t₂, t₁ < m → t₂ < m → ∀ i, i ∈ G t₁ → i ∈ G t₂ → t₁ = t₂

  same_value : ∀ t, t < m → ∀ i ∈ G t, ∀ j ∈ G t, l.getD i 0 = l.getD j 0

  contiguous : ∀ t, t < m → ∀ i j k, i ∈ G t → j ∈ G t → i < k → k < j →
    (∀ t', t' < t → k ∉ G t') → k ∈ G t

def removalScore (m : ℕ) (G : ℕ → Finset ℕ) : ℕ :=
  (Finset.range m).sum (fun t => (G t).card * (G t).card)

/-- The function returns a result r. A complete valid removal of boxes is a finite ordered list G_0, ..., G_{m-1} (with m >= 1) of nonempty sets of indices such that: (1) the sets G_0, ..., G_{m-1} partition {0, ..., len(boxes)-1}; (2) for every t and for all i, j in G_t, boxes[i] = boxes[j]; (3) for every t, G_t is contiguous in the set of indices not in G_0 union ... union G_{t-1}, meaning that if i < j are in G_t and i < k < j with k not in G_0 union ... union G_{t-1}, then k is in G_t. Let score(G) = sum over t from 0 to m-1 of |G_t|^2. Then r = max { score(G) : G is a complete valid removal of boxes }.
  Preconditions: len(boxes) >= 1 and len(boxes) <= 100, and for every i with 0 <= i < len(boxes), 1 <= boxes[i] <= 100. -/
theorem spec_1 (boxes : Slice I64)
    (hlen_pos : 1 ≤ boxes.val.length) (hlen_le : boxes.val.length ≤ 100)
    (hrange : ∀ i, i < boxes.val.length → 1 ≤ valueAt boxes i ∧ valueAt boxes i ≤ 100) :
    ∃ r : I64, Aegis.RemoveBoxes.remove_boxes boxes = ok r ∧
      ∃ (m : ℕ) (G : ℕ → Finset ℕ), IsValidRemoval (values boxes) m G ∧
        r.val = (removalScore m G : ℤ) ∧
        ∀ (m' : ℕ) (G' : ℕ → Finset ℕ), IsValidRemoval (values boxes) m' G' →
          (removalScore m' G' : ℤ) ≤ r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (boxes : Slice I64)
    (hlen_pos : 1 ≤ boxes.val.length) (hlen_le : boxes.val.length ≤ 100)
    (hrange : ∀ i, i < boxes.val.length → 1 ≤ valueAt boxes i ∧ valueAt boxes i ≤ 100), ∃ r : I64, Aegis.RemoveBoxes.remove_boxes boxes = ok r ∧
      ∃ (m : ℕ) (G : ℕ → Finset ℕ), IsValidRemoval (values boxes) m G ∧
        r.val = (removalScore m G : ℤ) ∧
        ∀ (m' : ℕ) (G' : ℕ → Finset ℕ), IsValidRemoval (values boxes) m' G' →
          (removalScore m' G' : ℤ) ≤ r.val) := by
  sorry

/-- The function returns a result r; in particular it does not fail, overflow, panic, or access out of bounds.
  Preconditions: len(boxes) >= 1 and len(boxes) <= 100, and for every i with 0 <= i < len(boxes), 1 <= boxes[i] <= 100. -/
theorem spec_2 (boxes : Slice I64)
    (hlen_pos : 1 ≤ boxes.val.length) (hlen_le : boxes.val.length ≤ 100)
    (hrange : ∀ i, i < boxes.val.length → 1 ≤ valueAt boxes i ∧ valueAt boxes i ≤ 100) :
    ∃ r : I64, Aegis.RemoveBoxes.remove_boxes boxes = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (boxes : Slice I64)
    (hlen_pos : 1 ≤ boxes.val.length) (hlen_le : boxes.val.length ≤ 100)
    (hrange : ∀ i, i < boxes.val.length → 1 ≤ valueAt boxes i ∧ valueAt boxes i ≤ 100), ∃ r : I64, Aegis.RemoveBoxes.remove_boxes boxes = ok r) := by
  sorry

/-- Whenever the function returns a result r, len(boxes) <= r <= len(boxes)^2.
  Preconditions: len(boxes) >= 1 and len(boxes) <= 100, and for every i with 0 <= i < len(boxes), 1 <= boxes[i] <= 100. -/
theorem spec_3 (boxes : Slice I64)
    (hlen_pos : 1 ≤ boxes.val.length) (hlen_le : boxes.val.length ≤ 100)
    (hrange : ∀ i, i < boxes.val.length → 1 ≤ valueAt boxes i ∧ valueAt boxes i ≤ 100)
    (r : I64) (hr : Aegis.RemoveBoxes.remove_boxes boxes = ok r) :
    (boxes.val.length : ℤ) ≤ r.val ∧ r.val ≤ (boxes.val.length : ℤ) ^ 2 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (boxes : Slice I64)
    (hlen_pos : 1 ≤ boxes.val.length) (hlen_le : boxes.val.length ≤ 100)
    (hrange : ∀ i, i < boxes.val.length → 1 ≤ valueAt boxes i ∧ valueAt boxes i ≤ 100)
    (r : I64) (hr : Aegis.RemoveBoxes.remove_boxes boxes = ok r), (boxes.val.length : ℤ) ≤ r.val ∧ r.val ≤ (boxes.val.length : ℤ) ^ 2) := by
  sorry

/-- Whenever the function returns a result r, let [l_1,u_1], ..., [l_s,u_s] be the maximal contiguous constant runs of boxes, listed from left to right (so l_1 = 0, u_s = len(boxes)-1, l_{j+1} = u_j+1, boxes is constant on each interval, and adjacent intervals have different values). Then r >= sum from j=1 to s of (u_j - l_j + 1)^2.
  Preconditions: len(boxes) >= 1 and len(boxes) <= 100, and for every i with 0 <= i < len(boxes), 1 <= boxes[i] <= 100. -/
theorem spec_4 (boxes : Slice I64)
    (hlen_pos : 1 ≤ boxes.val.length) (hlen_le : boxes.val.length ≤ 100)
    (hrange : ∀ i, i < boxes.val.length → 1 ≤ valueAt boxes i ∧ valueAt boxes i ≤ 100)
    (r : I64) (hr : Aegis.RemoveBoxes.remove_boxes boxes = ok r) :
    (runsScore (values boxes) : ℤ) ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (boxes : Slice I64)
    (hlen_pos : 1 ≤ boxes.val.length) (hlen_le : boxes.val.length ≤ 100)
    (hrange : ∀ i, i < boxes.val.length → 1 ≤ valueAt boxes i ∧ valueAt boxes i ≤ 100)
    (r : I64) (hr : Aegis.RemoveBoxes.remove_boxes boxes = ok r), (runsScore (values boxes) : ℤ) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= sum over distinct values c occurring in boxes of m_c^2, where m_c is the number of indices i with 0 <= i < len(boxes) and boxes[i] = c.
  Preconditions: len(boxes) >= 1 and len(boxes) <= 100, and for every i with 0 <= i < len(boxes), 1 <= boxes[i] <= 100. -/
theorem spec_5 (boxes : Slice I64)
    (hlen_pos : 1 ≤ boxes.val.length) (hlen_le : boxes.val.length ≤ 100)
    (hrange : ∀ i, i < boxes.val.length → 1 ≤ valueAt boxes i ∧ valueAt boxes i ≤ 100)
    (r : I64) (hr : Aegis.RemoveBoxes.remove_boxes boxes = ok r) :
    r.val ≤ (colorScore (values boxes) : ℤ) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (boxes : Slice I64)
    (hlen_pos : 1 ≤ boxes.val.length) (hlen_le : boxes.val.length ≤ 100)
    (hrange : ∀ i, i < boxes.val.length → 1 ≤ valueAt boxes i ∧ valueAt boxes i ≤ 100)
    (r : I64) (hr : Aegis.RemoveBoxes.remove_boxes boxes = ok r), r.val ≤ (colorScore (values boxes) : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, r = len(boxes)^2.
  Preconditions: len(boxes) >= 1 and len(boxes) <= 100, for every i with 0 <= i < len(boxes) 1 <= boxes[i] <= 100, and for every i and j with 0 <= i < len(boxes) and 0 <= j < len(boxes), boxes[i] = boxes[j]. -/
theorem spec_6 (boxes : Slice I64)
    (hlen_pos : 1 ≤ boxes.val.length) (hlen_le : boxes.val.length ≤ 100)
    (hrange : ∀ i, i < boxes.val.length → 1 ≤ valueAt boxes i ∧ valueAt boxes i ≤ 100)
    (hconst : ∀ i j, i < boxes.val.length → j < boxes.val.length →
      valueAt boxes i = valueAt boxes j)
    (r : I64) (hr : Aegis.RemoveBoxes.remove_boxes boxes = ok r) :
    r.val = (boxes.val.length : ℤ) ^ 2 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (boxes : Slice I64)
    (hlen_pos : 1 ≤ boxes.val.length) (hlen_le : boxes.val.length ≤ 100)
    (hrange : ∀ i, i < boxes.val.length → 1 ≤ valueAt boxes i ∧ valueAt boxes i ≤ 100)
    (hconst : ∀ i j, i < boxes.val.length → j < boxes.val.length →
      valueAt boxes i = valueAt boxes j)
    (r : I64) (hr : Aegis.RemoveBoxes.remove_boxes boxes = ok r), r.val = (boxes.val.length : ℤ) ^ 2) := by
  sorry

/-- Whenever the function returns a result r, r = len(boxes) if and only if for every i and j with 0 <= i < j < len(boxes), boxes[i] != boxes[j].
  Preconditions: len(boxes) >= 1 and len(boxes) <= 100, and for every i with 0 <= i < len(boxes), 1 <= boxes[i] <= 100. -/
theorem spec_7 (boxes : Slice I64)
    (hlen_pos : 1 ≤ boxes.val.length) (hlen_le : boxes.val.length ≤ 100)
    (hrange : ∀ i, i < boxes.val.length → 1 ≤ valueAt boxes i ∧ valueAt boxes i ≤ 100)
    (r : I64) (hr : Aegis.RemoveBoxes.remove_boxes boxes = ok r) :
    r.val = (boxes.val.length : ℤ) ↔
      ∀ i j, i < j → j < boxes.val.length → valueAt boxes i ≠ valueAt boxes j := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (boxes : Slice I64)
    (hlen_pos : 1 ≤ boxes.val.length) (hlen_le : boxes.val.length ≤ 100)
    (hrange : ∀ i, i < boxes.val.length → 1 ≤ valueAt boxes i ∧ valueAt boxes i ≤ 100)
    (r : I64) (hr : Aegis.RemoveBoxes.remove_boxes boxes = ok r), r.val = (boxes.val.length : ℤ) ↔
      ∀ i j, i < j → j < boxes.val.length → valueAt boxes i ≠ valueAt boxes j) := by
  sorry

/-- Whenever the function returns a result r, r mod 2 = len(boxes) mod 2 (that is, r and len(boxes) have the same parity).
  Preconditions: len(boxes) >= 1 and len(boxes) <= 100, and for every i with 0 <= i < len(boxes), 1 <= boxes[i] <= 100. -/
theorem spec_8 (boxes : Slice I64)
    (hlen_pos : 1 ≤ boxes.val.length) (hlen_le : boxes.val.length ≤ 100)
    (hrange : ∀ i, i < boxes.val.length → 1 ≤ valueAt boxes i ∧ valueAt boxes i ≤ 100)
    (r : I64) (hr : Aegis.RemoveBoxes.remove_boxes boxes = ok r) :
    r.val % 2 = (boxes.val.length : ℤ) % 2 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (boxes : Slice I64)
    (hlen_pos : 1 ≤ boxes.val.length) (hlen_le : boxes.val.length ≤ 100)
    (hrange : ∀ i, i < boxes.val.length → 1 ≤ valueAt boxes i ∧ valueAt boxes i ≤ 100)
    (r : I64) (hr : Aegis.RemoveBoxes.remove_boxes boxes = ok r), r.val % 2 = (boxes.val.length : ℤ) % 2) := by
  sorry

/-- Whenever remove_boxes(boxes) returns r and remove_boxes(boxes') returns r', we have r = r'.
  Preconditions: len(boxes) >= 1 and len(boxes) <= 100, for every i with 0 <= i < len(boxes) 1 <= boxes[i] <= 100, len(boxes') = len(boxes), for every i with 0 <= i < len(boxes') 1 <= boxes'[i] <= 100, and for every i with 0 <= i < len(boxes), boxes'[i] = boxes[len(boxes)-1-i]. -/
theorem spec_9 (boxes boxes' : Slice I64)
    (hlen_pos : 1 ≤ boxes.val.length) (hlen_le : boxes.val.length ≤ 100)
    (hrange : ∀ i, i < boxes.val.length → 1 ≤ valueAt boxes i ∧ valueAt boxes i ≤ 100)
    (hlen' : boxes'.val.length = boxes.val.length)
    (hrange' : ∀ i, i < boxes'.val.length → 1 ≤ valueAt boxes' i ∧ valueAt boxes' i ≤ 100)
    (hrev : ∀ i, i < boxes.val.length →
      valueAt boxes' i = valueAt boxes (boxes.val.length - 1 - i))
    (r r' : I64) (hr : Aegis.RemoveBoxes.remove_boxes boxes = ok r)
    (hr' : Aegis.RemoveBoxes.remove_boxes boxes' = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (boxes boxes' : Slice I64)
    (hlen_pos : 1 ≤ boxes.val.length) (hlen_le : boxes.val.length ≤ 100)
    (hrange : ∀ i, i < boxes.val.length → 1 ≤ valueAt boxes i ∧ valueAt boxes i ≤ 100)
    (hlen' : boxes'.val.length = boxes.val.length)
    (hrange' : ∀ i, i < boxes'.val.length → 1 ≤ valueAt boxes' i ∧ valueAt boxes' i ≤ 100)
    (hrev : ∀ i, i < boxes.val.length →
      valueAt boxes' i = valueAt boxes (boxes.val.length - 1 - i))
    (r r' : I64) (hr : Aegis.RemoveBoxes.remove_boxes boxes = ok r)
    (hr' : Aegis.RemoveBoxes.remove_boxes boxes' = ok r'), r.val = r'.val) := by
  sorry

/-- Whenever remove_boxes(boxes) returns r and remove_boxes(boxes') returns r', we have r' = r + 1.
  Preconditions: len(boxes) >= 1 and len(boxes) <= 99, for every i with 0 <= i < len(boxes) 1 <= boxes[i] <= 100, c is an integer with 1 <= c <= 100 and c != boxes[i] for every i with 0 <= i < len(boxes), boxes' has length len(boxes)+1, for every i with 0 <= i < len(boxes) boxes'[i] = boxes[i], and boxes'[len(boxes)] = c. -/
theorem spec_10 (boxes boxes' : Slice I64) (c : ℤ)
    (hlen_pos : 1 ≤ boxes.val.length) (hlen_le : boxes.val.length ≤ 99)
    (hrange : ∀ i, i < boxes.val.length → 1 ≤ valueAt boxes i ∧ valueAt boxes i ≤ 100)
    (hc_low : 1 ≤ c) (hc_high : c ≤ 100)
    (hc_fresh : ∀ i, i < boxes.val.length → valueAt boxes i ≠ c)
    (hlen' : boxes'.val.length = boxes.val.length + 1)
    (hprefix : ∀ i, i < boxes.val.length → valueAt boxes' i = valueAt boxes i)
    (hlast : valueAt boxes' boxes.val.length = c)
    (r r' : I64) (hr : Aegis.RemoveBoxes.remove_boxes boxes = ok r)
    (hr' : Aegis.RemoveBoxes.remove_boxes boxes' = ok r') :
    r'.val = r.val + 1 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (boxes boxes' : Slice I64) (c : ℤ)
    (hlen_pos : 1 ≤ boxes.val.length) (hlen_le : boxes.val.length ≤ 99)
    (hrange : ∀ i, i < boxes.val.length → 1 ≤ valueAt boxes i ∧ valueAt boxes i ≤ 100)
    (hc_low : 1 ≤ c) (hc_high : c ≤ 100)
    (hc_fresh : ∀ i, i < boxes.val.length → valueAt boxes i ≠ c)
    (hlen' : boxes'.val.length = boxes.val.length + 1)
    (hprefix : ∀ i, i < boxes.val.length → valueAt boxes' i = valueAt boxes i)
    (hlast : valueAt boxes' boxes.val.length = c)
    (r r' : I64) (hr : Aegis.RemoveBoxes.remove_boxes boxes = ok r)
    (hr' : Aegis.RemoveBoxes.remove_boxes boxes' = ok r'), r'.val = r.val + 1) := by
  sorry

/-- Whenever the function returns a result r, r = 4 if boxes[0] = boxes[1], and r = 2 otherwise.
  Preconditions: len(boxes) = 2, and for every i with 0 <= i < 2, 1 <= boxes[i] <= 100. -/
theorem spec_11 (boxes : Slice I64)
    (hlen : boxes.val.length = 2)
    (hrange : ∀ i, i < 2 → 1 ≤ valueAt boxes i ∧ valueAt boxes i ≤ 100)
    (r : I64) (hr : Aegis.RemoveBoxes.remove_boxes boxes = ok r) :
    (valueAt boxes 0 = valueAt boxes 1 → r.val = 4) ∧
      (valueAt boxes 0 ≠ valueAt boxes 1 → r.val = 2) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (boxes : Slice I64)
    (hlen : boxes.val.length = 2)
    (hrange : ∀ i, i < 2 → 1 ≤ valueAt boxes i ∧ valueAt boxes i ≤ 100)
    (r : I64) (hr : Aegis.RemoveBoxes.remove_boxes boxes = ok r), (valueAt boxes 0 = valueAt boxes 1 → r.val = 4) ∧
      (valueAt boxes 0 ≠ valueAt boxes 1 → r.val = 2)) := by
  sorry

/-- Whenever the function returns a result r, r = (len(boxes)-1)^2 + 1.
  Preconditions: len(boxes) >= 2 and len(boxes) <= 100, for every i with 0 <= i < len(boxes) 1 <= boxes[i] <= 100, and there exists a value c such that c occurs exactly once in boxes and every index i with boxes[i] != c has the same value d (with d != c); equivalently, exactly two distinct colors occur and one of them occurs exactly once. -/
theorem spec_12 (boxes : Slice I64)
    (hlen_pos : 2 ≤ boxes.val.length) (hlen_le : boxes.val.length ≤ 100)
    (hrange : ∀ i, i < boxes.val.length → 1 ≤ valueAt boxes i ∧ valueAt boxes i ≤ 100)
    (hshape : ∃ c d : ℤ, c ≠ d ∧ OccursOnce c (values boxes) ∧
      ∀ i, i < boxes.val.length → valueAt boxes i ≠ c → valueAt boxes i = d)
    (r : I64) (hr : Aegis.RemoveBoxes.remove_boxes boxes = ok r) :
    r.val = ((boxes.val.length : ℤ) - 1) ^ 2 + 1 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (boxes : Slice I64)
    (hlen_pos : 2 ≤ boxes.val.length) (hlen_le : boxes.val.length ≤ 100)
    (hrange : ∀ i, i < boxes.val.length → 1 ≤ valueAt boxes i ∧ valueAt boxes i ≤ 100)
    (hshape : ∃ c d : ℤ, c ≠ d ∧ OccursOnce c (values boxes) ∧
      ∀ i, i < boxes.val.length → valueAt boxes i ≠ c → valueAt boxes i = d)
    (r : I64) (hr : Aegis.RemoveBoxes.remove_boxes boxes = ok r), r.val = ((boxes.val.length : ℤ) - 1) ^ 2 + 1) := by
  sorry

/-- Whenever the function returns a result r, for every integer c with 1 <= c <= 100, if m is the number of indices i with 0 <= i < len(boxes) and boxes[i] = c, and m >= 1, then r >= len(boxes) - m + m^2.
  Preconditions: len(boxes) >= 1 and len(boxes) <= 100, and for every i with 0 <= i < len(boxes), 1 <= boxes[i] <= 100. -/
theorem spec_13 (boxes : Slice I64)
    (hlen_pos : 1 ≤ boxes.val.length) (hlen_le : boxes.val.length ≤ 100)
    (hrange : ∀ i, i < boxes.val.length → 1 ≤ valueAt boxes i ∧ valueAt boxes i ≤ 100)
    (r : I64) (hr : Aegis.RemoveBoxes.remove_boxes boxes = ok r) :
    ∀ (c : ℤ) (m : ℕ), 1 ≤ c → c ≤ 100 → m = occurrences c (values boxes) → 1 ≤ m →
      (boxes.val.length : ℤ) - (m : ℤ) + (m : ℤ) ^ 2 ≤ r.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (boxes : Slice I64)
    (hlen_pos : 1 ≤ boxes.val.length) (hlen_le : boxes.val.length ≤ 100)
    (hrange : ∀ i, i < boxes.val.length → 1 ≤ valueAt boxes i ∧ valueAt boxes i ≤ 100)
    (r : I64) (hr : Aegis.RemoveBoxes.remove_boxes boxes = ok r), ∀ (c : ℤ) (m : ℕ), 1 ≤ c → c ≤ 100 → m = occurrences c (values boxes) → 1 ≤ m →
      (boxes.val.length : ℤ) - (m : ℤ) + (m : ℤ) ^ 2 ≤ r.val) := by
  sorry

end AegisSpec.RemoveBoxes
