import Aegis.IsSelfCrossing.Code.Funs

/-!
# Specifications of `Aegis.IsSelfCrossing.is_self_crossing`

LeetCode problem `self-crossing`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.IsSelfCrossing

  def vals (distance : Slice Std.I64) : List ℤ := distance.val.map (fun x => x.val)

  def dlen (distance : Slice Std.I64) : ℕ := (vals distance).length

  def dget (distance : Slice Std.I64) (i : ℕ) : ℤ := (vals distance).getD i 0

  def ValidInput (distance : Slice Std.I64) : Prop :=
    1 ≤ dlen distance ∧ dlen distance ≤ 10 ^ 5 ∧
      ∀ i, i < dlen distance → 1 ≤ dget distance i ∧ dget distance i ≤ 10 ^ 5

  def dir (k : ℕ) : ℤ × ℤ :=
    match k % 4 with
    | 0 => (0, 1)
    | 1 => (-1, 0)
    | 2 => (0, -1)
    | _ => (1, 0)

  def pt (distance : Slice Std.I64) (k : ℕ) : ℤ × ℤ :=
    ((Finset.range k).sum (fun i => dget distance i * (dir i).1),
     (Finset.range k).sum (fun i => dget distance i * (dir i).2))

  def seg (distance : Slice Std.I64) (k : ℕ) : Set (ℚ × ℚ) :=
    {p | ∃ t : ℚ, 0 ≤ t ∧ t ≤ 1 ∧
      p.1 = (1 - t) * ((pt distance k).1 : ℚ) + t * ((pt distance (k + 1)).1 : ℚ) ∧
      p.2 = (1 - t) * ((pt distance k).2 : ℚ) + t * ((pt distance (k + 1)).2 : ℚ)}

  def segInter (distance : Slice Std.I64) (i j : ℕ) : Prop :=
    ∃ p : ℚ × ℚ, p ∈ seg distance i ∧ p ∈ seg distance j

  def total (distance : Slice Std.I64) : ℤ := (vals distance).sum

  /-- Let P_0 = (0,0) and for k >= 0, P_{k+1} = P_k + distance[k] * v_k, where v_k = (0,1) if k mod 4 = 0, (-1,0) if k mod 4 = 1, (0,-1) if k mod 4 = 2, (1,0) if k mod 4 = 3. Let S_k be the closed line segment from P_k to P_{k+1} for 0 <= k < len(distance). The function returns a result r (i.e., it does not fail) and r = true if and only if there exist indices i and j with 0 <= i < j < len(distance) and j >= i+2 such that S_i and S_j intersect (i.e., share at least one point).
    Preconditions: distance is a slice of i64 with 1 <= len(distance) <= 10^5 and 1 <= distance[i] <= 10^5 for all i with 0 <= i < len(distance). -/
  theorem spec_1 (distance : Slice Std.I64) (hvalid : ValidInput distance) :
      ∃ r, Aegis.IsSelfCrossing.is_self_crossing distance = ok r ∧
        (r = true ↔ ∃ i j, i + 2 ≤ j ∧ j < dlen distance ∧ segInter distance i j) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (distance : Slice Std.I64) (hvalid : ValidInput distance), ∃ r, Aegis.IsSelfCrossing.is_self_crossing distance = ok r ∧
          (r = true ↔ ∃ i j, i + 2 ≤ j ∧ j < dlen distance ∧ segInter distance i j)) := by
    sorry

  /-- The function returns a result r (i.e., it does not fail).
    Preconditions: distance is a slice of i64 with 1 <= len(distance) <= 10^5 and 1 <= distance[i] <= 10^5 for all i with 0 <= i < len(distance). -/
  theorem spec_2 (distance : Slice Std.I64) (hvalid : ValidInput distance) :
      ∃ r, Aegis.IsSelfCrossing.is_self_crossing distance = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (distance : Slice Std.I64) (hvalid : ValidInput distance), ∃ r, Aegis.IsSelfCrossing.is_self_crossing distance = ok r) := by
    sorry

  /-- Let P_0 = (0,0) and for k >= 0, P_{k+1} = P_k + distance[k] * v_k, where v_k = (0,1) if k mod 4 = 0, (-1,0) if k mod 4 = 1, (0,-1) if k mod 4 = 2, (1,0) if k mod 4 = 3. If there exist indices k and m with 0 <= k < m <= len(distance) such that P_k = P_m, then the function returns a result r with r = true.
    Preconditions: distance is a slice of i64 with 1 <= len(distance) <= 10^5 and 1 <= distance[i] <= 10^5 for all i with 0 <= i < len(distance). -/
  theorem spec_3 (distance : Slice Std.I64) (hvalid : ValidInput distance)
      (hw : ∃ k m, k < m ∧ m ≤ dlen distance ∧ pt distance k = pt distance m) :
      ∃ r, Aegis.IsSelfCrossing.is_self_crossing distance = ok r ∧ r = true := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (distance : Slice Std.I64) (hvalid : ValidInput distance)
        (hw : ∃ k m, k < m ∧ m ≤ dlen distance ∧ pt distance k = pt distance m), ∃ r, Aegis.IsSelfCrossing.is_self_crossing distance = ok r ∧ r = true) := by
    sorry

  /-- Let distance' be the slice with distance'[i] = c * distance[i] for all i. Then is_self_crossing(distance) = is_self_crossing(distance').
    Preconditions: distance is a slice of i64 with 1 <= len(distance) <= 10^5 and 1 <= distance[i] <= 10^5 for all i with 0 <= i < len(distance). Let c be a positive integer such that c * distance[i] <= 10^5 for all i with 0 <= i < len(distance). -/
  theorem spec_4 (distance distance' : Slice Std.I64) (c : ℕ)
      (hc : 0 < c) (hvalid : ValidInput distance)
      (hbound : ∀ i, i < dlen distance → (c : ℤ) * dget distance i ≤ 10 ^ 5)
      (hscale : vals distance' = (vals distance).map (fun x => (c : ℤ) * x))
      (r : Bool) :
      (Aegis.IsSelfCrossing.is_self_crossing distance = ok r) ↔
        (Aegis.IsSelfCrossing.is_self_crossing distance' = ok r) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (distance distance' : Slice Std.I64) (c : ℕ)
        (hc : 0 < c) (hvalid : ValidInput distance)
        (hbound : ∀ i, i < dlen distance → (c : ℤ) * dget distance i ≤ 10 ^ 5)
        (hscale : vals distance' = (vals distance).map (fun x => (c : ℤ) * x))
        (r : Bool), (Aegis.IsSelfCrossing.is_self_crossing distance = ok r) ↔
          (Aegis.IsSelfCrossing.is_self_crossing distance' = ok r)) := by
    sorry

  /-- The function returns a result r and r = false.
    Preconditions: distance is a slice of i64 with 1 <= len(distance) <= 10^5 and 1 <= distance[i] <= 10^5 for all i with 0 <= i < len(distance). Additionally, for all i with 2 <= i < len(distance), distance[i] > distance[i-2]. -/
  theorem spec_5 (distance : Slice Std.I64) (hvalid : ValidInput distance)
      (hinc : ∀ i, 2 ≤ i → i < dlen distance → dget distance (i - 2) < dget distance i) :
      ∃ r, Aegis.IsSelfCrossing.is_self_crossing distance = ok r ∧ r = false := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (distance : Slice Std.I64) (hvalid : ValidInput distance)
        (hinc : ∀ i, 2 ≤ i → i < dlen distance → dget distance (i - 2) < dget distance i), ∃ r, Aegis.IsSelfCrossing.is_self_crossing distance = ok r ∧ r = false) := by
    sorry

  /-- Let P_0 = (0,0) and for k >= 0, P_{k+1} = P_k + distance[k] * v_k, where v_k = (0,1) if k mod 4 = 0, (-1,0) if k mod 4 = 1, (0,-1) if k mod 4 = 2, (1,0) if k mod 4 = 3. Let S_k be the closed line segment from P_k to P_{k+1} for 0 <= k < len(distance). If the function returns a result r with r = true, then there exist indices i and j with 0 <= i < j < len(distance) such that 3 <= j - i <= 5 and S_i and S_j intersect.
    Preconditions: distance is a slice of i64 with 1 <= len(distance) <= 10^5 and 1 <= distance[i] <= 10^5 for all i with 0 <= i < len(distance). -/
  theorem spec_6 (distance : Slice Std.I64) (hvalid : ValidInput distance)
      (h : Aegis.IsSelfCrossing.is_self_crossing distance = ok true) :
      ∃ i j, i + 3 ≤ j ∧ j - i ≤ 5 ∧ j < dlen distance ∧ segInter distance i j := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (distance : Slice Std.I64) (hvalid : ValidInput distance)
        (h : Aegis.IsSelfCrossing.is_self_crossing distance = ok true), ∃ i j, i + 3 ≤ j ∧ j - i ≤ 5 ∧ j < dlen distance ∧ segInter distance i j) := by
    sorry

  /-- The function returns a result r and r = true.
    Preconditions: distance is a slice of i64 with 1 <= len(distance) <= 10^5 and 1 <= distance[i] <= 10^5 for all i with 0 <= i < len(distance). There exists an index i with 0 <= i and i+3 < len(distance) such that distance[i+2] <= distance[i] and distance[i+3] >= distance[i+1]. -/
  theorem spec_7 (distance : Slice Std.I64) (hvalid : ValidInput distance)
      (hw : ∃ i, i + 3 < dlen distance ∧ dget distance (i + 2) ≤ dget distance i ∧
        dget distance (i + 1) ≤ dget distance (i + 3)) :
      ∃ r, Aegis.IsSelfCrossing.is_self_crossing distance = ok r ∧ r = true := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (distance : Slice Std.I64) (hvalid : ValidInput distance)
        (hw : ∃ i, i + 3 < dlen distance ∧ dget distance (i + 2) ≤ dget distance i ∧
          dget distance (i + 1) ≤ dget distance (i + 3)), ∃ r, Aegis.IsSelfCrossing.is_self_crossing distance = ok r ∧ r = true) := by
    sorry

  end AegisSpec.IsSelfCrossing
