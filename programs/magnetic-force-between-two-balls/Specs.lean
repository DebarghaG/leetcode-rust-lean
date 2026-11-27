import Aegis.MaxDistance.Code.Funs

/-!
# Specifications of `Aegis.MaxDistance.max_distance`

LeetCode problem `magnetic-force-between-two-balls`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaxDistance

  open Aegis.MaxDistance

  def vals (position : Slice Std.I64) : List Int := position.val.map (fun x => x.val)

  def SortedAsc (l : List Int) : Prop := l.Pairwise (· ≤ ·)

  def GapsAtLeast (d : Int) : List Int → Prop
    | [] => True
    | [_] => True
    | a :: b :: t => a + d ≤ b ∧ GapsAtLeast d (b :: t)

  def maxVal : List Std.I64 → Int
    | [] => 0
    | [a] => a.val
    | a :: b :: t => max a.val (maxVal (b :: t))

  def minVal : List Std.I64 → Int
    | [] => 0
    | [a] => a.val
    | a :: b :: t => min a.val (minVal (b :: t))

  def pairDistSet (position : Slice Std.I64)
      (S : Finset (Fin position.val.length)) : Finset Int :=
    S.offDiag.image (fun p : Fin position.val.length × Fin position.val.length =>
      |(position.val.get p.1).val - (position.val.get p.2).val|)

  def minDist (position : Slice Std.I64) (S : Finset (Fin position.val.length)) : Int :=
    if h : (pairDistSet position S).Nonempty then (pairDistSet position S).min' h else 0

  def minDistValues (position : Slice Std.I64) (m : Nat) : Finset Int :=
    ((Finset.univ : Finset (Fin position.val.length)).powersetCard m).image
      (fun S => minDist position S)

  def bestMinDist (position : Slice Std.I64) (m : Nat) : Int :=
    if h : (minDistValues position m).Nonempty then (minDistValues position m).max' h else 0

  def SubMultisetVals (position position' : Slice Std.I64) : Prop :=
    ∀ v : Int, (vals position).count v ≤ (vals position').count v

  /-- The function returns a result r and r = max{ minDist(S) : S ⊆ {0, 1, ..., n-1}, |S| = m }, where for any subset S with |S| >= 2, minDist(S) = min{ |position[i] - position[j]| : i, j ∈ S, i < j }.
    Preconditions: Let n = len(position). The preconditions are: 2 <= n <= 10^5; for all i with 0 <= i < n, 1 <= position[i] <= 10^9; all values position[i] are pairwise distinct; and m is an integer with 2 <= m <= n. -/
  theorem spec_1 (position : Slice Std.I64) (m : Std.I64)
      (hn : 2 ≤ position.val.length) (hnle : position.val.length ≤ 10 ^ 5)
      (hval : ∀ x ∈ position.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 9)
      (hnd : (vals position).Nodup)
      (hm : 2 ≤ m.val) (hmn : m.val ≤ (position.val.length : Int)) :
      ∃ r, max_distance position m = ok r ∧ r = bestMinDist position m.val.toNat := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (position : Slice Std.I64) (m : Std.I64)
        (hn : 2 ≤ position.val.length) (hnle : position.val.length ≤ 10 ^ 5)
        (hval : ∀ x ∈ position.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 9)
        (hnd : (vals position).Nodup)
        (hm : 2 ≤ m.val) (hmn : m.val ≤ (position.val.length : Int)), ∃ r, max_distance position m = ok r ∧ r = bestMinDist position m.val.toNat) := by
    sorry

  /-- The function returns a result r (i.e., it does not fail, panic, or overflow) for every input satisfying the preconditions.
    Preconditions: Let n = len(position). The preconditions are: 2 <= n <= 10^5; for all i with 0 <= i < n, 1 <= position[i] <= 10^9; all values position[i] are pairwise distinct; and m is an integer with 2 <= m <= n. -/
  theorem spec_2 (position : Slice Std.I64) (m : Std.I64)
      (hn : 2 ≤ position.val.length) (hnle : position.val.length ≤ 10 ^ 5)
      (hval : ∀ x ∈ position.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 9)
      (hnd : (vals position).Nodup)
      (hm : 2 ≤ m.val) (hmn : m.val ≤ (position.val.length : Int)) :
      ∃ r, max_distance position m = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (position : Slice Std.I64) (m : Std.I64)
        (hn : 2 ≤ position.val.length) (hnle : position.val.length ≤ 10 ^ 5)
        (hval : ∀ x ∈ position.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 9)
        (hnd : (vals position).Nodup)
        (hm : 2 ≤ m.val) (hmn : m.val ≤ (position.val.length : Int)), ∃ r, max_distance position m = ok r) := by
    sorry

  /-- The function returns a result r and r <= (M - m0) div (m - 1), where M = max_{0 <= i < n} position[i], m0 = min_{0 <= i < n} position[i], and div denotes integer division (floor).
    Preconditions: Let n = len(position). The preconditions are: 2 <= n <= 10^5; for all i with 0 <= i < n, 1 <= position[i] <= 10^9; all values position[i] are pairwise distinct; and m is an integer with 2 <= m <= n. -/
  theorem spec_3 (position : Slice Std.I64) (m : Std.I64)
      (hn : 2 ≤ position.val.length) (hnle : position.val.length ≤ 10 ^ 5)
      (hval : ∀ x ∈ position.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 9)
      (hnd : (vals position).Nodup)
      (hm : 2 ≤ m.val) (hmn : m.val ≤ (position.val.length : Int)) :
      ∃ r, max_distance position m = ok r ∧
        r ≤ (maxVal position.val - minVal position.val) / (m.val - 1) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (position : Slice Std.I64) (m : Std.I64)
        (hn : 2 ≤ position.val.length) (hnle : position.val.length ≤ 10 ^ 5)
        (hval : ∀ x ∈ position.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 9)
        (hnd : (vals position).Nodup)
        (hm : 2 ≤ m.val) (hmn : m.val ≤ (position.val.length : Int)), ∃ r, max_distance position m = ok r ∧
          r ≤ (maxVal position.val - minVal position.val) / (m.val - 1)) := by
    sorry

  /-- If m = 2, then the function returns a result r and r = M - m0, where M = max_{0 <= i < n} position[i] and m0 = min_{0 <= i < n} position[i].
    Preconditions: Let n = len(position). The preconditions are: 2 <= n <= 10^5; for all i with 0 <= i < n, 1 <= position[i] <= 10^9; all values position[i] are pairwise distinct; and m is an integer with 2 <= m <= n. -/
  theorem spec_4 (position : Slice Std.I64) (m : Std.I64)
      (hn : 2 ≤ position.val.length) (hnle : position.val.length ≤ 10 ^ 5)
      (hval : ∀ x ∈ position.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 9)
      (hnd : (vals position).Nodup)
      (hm : 2 ≤ m.val) (hmn : m.val ≤ (position.val.length : Int))
      (hm2 : m.val = 2) :
      ∃ r, max_distance position m = ok r ∧
        r = maxVal position.val - minVal position.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (position : Slice Std.I64) (m : Std.I64)
        (hn : 2 ≤ position.val.length) (hnle : position.val.length ≤ 10 ^ 5)
        (hval : ∀ x ∈ position.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 9)
        (hnd : (vals position).Nodup)
        (hm : 2 ≤ m.val) (hmn : m.val ≤ (position.val.length : Int))
        (hm2 : m.val = 2), ∃ r, max_distance position m = ok r ∧
          r = maxVal position.val - minVal position.val) := by
    sorry

  /-- If m = n, then the function returns a result r and r = min{ |position[i] - position[j]| : 0 <= i < j < n }.
    Preconditions: Let n = len(position). The preconditions are: 2 <= n <= 10^5; for all i with 0 <= i < n, 1 <= position[i] <= 10^9; all values position[i] are pairwise distinct; and m is an integer with 2 <= m <= n. -/
  theorem spec_5 (position : Slice Std.I64) (m : Std.I64)
      (hn : 2 ≤ position.val.length) (hnle : position.val.length ≤ 10 ^ 5)
      (hval : ∀ x ∈ position.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 9)
      (hnd : (vals position).Nodup)
      (hm : 2 ≤ m.val) (hmn : m.val ≤ (position.val.length : Int))
      (hmn' : m.val = (position.val.length : Int)) :
      ∃ r, max_distance position m = ok r ∧
        r = minDist position Finset.univ := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (position : Slice Std.I64) (m : Std.I64)
        (hn : 2 ≤ position.val.length) (hnle : position.val.length ≤ 10 ^ 5)
        (hval : ∀ x ∈ position.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 9)
        (hnd : (vals position).Nodup)
        (hm : 2 ≤ m.val) (hmn : m.val ≤ (position.val.length : Int))
        (hmn' : m.val = (position.val.length : Int)), ∃ r, max_distance position m = ok r ∧
          r = minDist position Finset.univ) := by
    sorry

  /-- The function returns a result r and there exists a subset S ⊆ {0, 1, ..., n-1} with |S| = m such that minDist(S) >= r, where minDist(S) = min{ |position[i] - position[j]| : i, j ∈ S, i < j }.
    Preconditions: Let n = len(position). The preconditions are: 2 <= n <= 10^5; for all i with 0 <= i < n, 1 <= position[i] <= 10^9; all values position[i] are pairwise distinct; and m is an integer with 2 <= m <= n. -/
  theorem spec_6 (position : Slice Std.I64) (m : Std.I64)
      (hn : 2 ≤ position.val.length) (hnle : position.val.length ≤ 10 ^ 5)
      (hval : ∀ x ∈ position.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 9)
      (hnd : (vals position).Nodup)
      (hm : 2 ≤ m.val) (hmn : m.val ≤ (position.val.length : Int)) :
      ∃ r, max_distance position m = ok r ∧
        ∃ S : Finset (Fin position.val.length),
          (S.card : Int) = m.val ∧ r ≤ minDist position S := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (position : Slice Std.I64) (m : Std.I64)
        (hn : 2 ≤ position.val.length) (hnle : position.val.length ≤ 10 ^ 5)
        (hval : ∀ x ∈ position.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 9)
        (hnd : (vals position).Nodup)
        (hm : 2 ≤ m.val) (hmn : m.val ≤ (position.val.length : Int)), ∃ r, max_distance position m = ok r ∧
          ∃ S : Finset (Fin position.val.length),
            (S.card : Int) = m.val ∧ r ≤ minDist position S) := by
    sorry

  /-- The function returns a result r and for every subset S ⊆ {0, 1, ..., n-1} with |S| = m, minDist(S) <= r, where minDist(S) = min{ |position[i] - position[j]| : i, j ∈ S, i < j }.
    Preconditions: Let n = len(position). The preconditions are: 2 <= n <= 10^5; for all i with 0 <= i < n, 1 <= position[i] <= 10^9; all values position[i] are pairwise distinct; and m is an integer with 2 <= m <= n. -/
  theorem spec_7 (position : Slice Std.I64) (m : Std.I64)
      (hn : 2 ≤ position.val.length) (hnle : position.val.length ≤ 10 ^ 5)
      (hval : ∀ x ∈ position.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 9)
      (hnd : (vals position).Nodup)
      (hm : 2 ≤ m.val) (hmn : m.val ≤ (position.val.length : Int)) :
      ∃ r, max_distance position m = ok r ∧
        ∀ S : Finset (Fin position.val.length),
          (S.card : Int) = m.val → minDist position S ≤ r := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (position : Slice Std.I64) (m : Std.I64)
        (hn : 2 ≤ position.val.length) (hnle : position.val.length ≤ 10 ^ 5)
        (hval : ∀ x ∈ position.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 9)
        (hnd : (vals position).Nodup)
        (hm : 2 ≤ m.val) (hmn : m.val ≤ (position.val.length : Int)), ∃ r, max_distance position m = ok r ∧
          ∀ S : Finset (Fin position.val.length),
            (S.card : Int) = m.val → minDist position S ≤ r) := by
    sorry

  /-- The function returns a result r and for every integer d, there exists a subset S ⊆ {0, 1, ..., n-1} with |S| = m such that minDist(S) >= d if and only if d <= r, where minDist(S) = min{ |position[i] - position[j]| : i, j ∈ S, i < j }.
    Preconditions: Let n = len(position). The preconditions are: 2 <= n <= 10^5; for all i with 0 <= i < n, 1 <= position[i] <= 10^9; all values position[i] are pairwise distinct; and m is an integer with 2 <= m <= n. -/
  theorem spec_8 (position : Slice Std.I64) (m : Std.I64)
      (hn : 2 ≤ position.val.length) (hnle : position.val.length ≤ 10 ^ 5)
      (hval : ∀ x ∈ position.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 9)
      (hnd : (vals position).Nodup)
      (hm : 2 ≤ m.val) (hmn : m.val ≤ (position.val.length : Int)) :
      ∃ r, max_distance position m = ok r ∧
        ∀ d : Int,
          (∃ S : Finset (Fin position.val.length),
            (S.card : Int) = m.val ∧ d ≤ minDist position S) ↔ d ≤ r := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (position : Slice Std.I64) (m : Std.I64)
        (hn : 2 ≤ position.val.length) (hnle : position.val.length ≤ 10 ^ 5)
        (hval : ∀ x ∈ position.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 9)
        (hnd : (vals position).Nodup)
        (hm : 2 ≤ m.val) (hmn : m.val ≤ (position.val.length : Int)), ∃ r, max_distance position m = ok r ∧
          ∀ d : Int,
            (∃ S : Finset (Fin position.val.length),
              (S.card : Int) = m.val ∧ d ≤ minDist position S) ↔ d ≤ r) := by
    sorry

  /-- For any integers m1 and m2 with 2 <= m1 <= m2 <= n, the value max_distance(position, m1) is greater than or equal to max_distance(position, m2), where max_distance(position, m) denotes the result of the function on the same position slice and the given m.
    Preconditions: Let n = len(position). The preconditions are: 2 <= n <= 10^5; for all i with 0 <= i < n, 1 <= position[i] <= 10^9; all values position[i] are pairwise distinct; and m is an integer with 2 <= m <= n. -/
  theorem spec_9 (position : Slice Std.I64) (m1 m2 : Std.I64)
      (hn : 2 ≤ position.val.length) (hnle : position.val.length ≤ 10 ^ 5)
      (hval : ∀ x ∈ position.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 9)
      (hnd : (vals position).Nodup)
      (hm1 : 2 ≤ m1.val) (hm12 : m1.val ≤ m2.val)
      (hm2n : m2.val ≤ (position.val.length : Int)) :
      ∃ r1 r2, max_distance position m1 = ok r1 ∧ max_distance position m2 = ok r2 ∧
        r2 ≤ r1 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (position : Slice Std.I64) (m1 m2 : Std.I64)
        (hn : 2 ≤ position.val.length) (hnle : position.val.length ≤ 10 ^ 5)
        (hval : ∀ x ∈ position.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 9)
        (hnd : (vals position).Nodup)
        (hm1 : 2 ≤ m1.val) (hm12 : m1.val ≤ m2.val)
        (hm2n : m2.val ≤ (position.val.length : Int)), ∃ r1 r2, max_distance position m1 = ok r1 ∧ max_distance position m2 = ok r2 ∧
          r2 ≤ r1) := by
    sorry

  /-- Let p_0 <= p_1 <= ... <= p_{n-1} be the elements of position sorted in non-decreasing order. The function returns a result r and r is the largest integer d such that there exist indices 0 <= i_1 < i_2 < ... < i_m <= n-1 with p_{i_{k+1}} - p_{i_k} >= d for every 1 <= k < m.
    Preconditions: Let n = len(position). The preconditions are: 2 <= n <= 10^5; for all i with 0 <= i < n, 1 <= position[i] <= 10^9; all values position[i] are pairwise distinct; and m is an integer with 2 <= m <= n. -/
  theorem spec_10 (position : Slice Std.I64) (m : Std.I64)
      (hn : 2 ≤ position.val.length) (hnle : position.val.length ≤ 10 ^ 5)
      (hval : ∀ x ∈ position.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 9)
      (hnd : (vals position).Nodup)
      (hm : 2 ≤ m.val) (hmn : m.val ≤ (position.val.length : Int)) :
      ∃ r, max_distance position m = ok r ∧
        ∀ p : List Int, SortedAsc p → p.Perm (vals position) →
          IsGreatest
            {d : Int | ∃ sel : List Int,
              sel.Sublist p ∧ sel.length = m.val.toNat ∧ GapsAtLeast d sel}
            r := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (position : Slice Std.I64) (m : Std.I64)
        (hn : 2 ≤ position.val.length) (hnle : position.val.length ≤ 10 ^ 5)
        (hval : ∀ x ∈ position.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 9)
        (hnd : (vals position).Nodup)
        (hm : 2 ≤ m.val) (hmn : m.val ≤ (position.val.length : Int)), ∃ r, max_distance position m = ok r ∧
          ∀ p : List Int, SortedAsc p → p.Perm (vals position) →
            IsGreatest
              {d : Int | ∃ sel : List Int,
                sel.Sublist p ∧ sel.length = m.val.toNat ∧ GapsAtLeast d sel}
              r) := by
    sorry

  /-- The function returns a result r and there exists a subset S ⊆ {0, 1, ..., n-1} with |S| = m such that minDist(S) = r, and S contains an index i with position[i] = min_{0 <= k < n} position[k] and an index j with position[j] = max_{0 <= k < n} position[k], where minDist(S) = min{ |position[i] - position[j]| : i, j ∈ S, i < j }.
    Preconditions: Let n = len(position). The preconditions are: 2 <= n <= 10^5; for all i with 0 <= i < n, 1 <= position[i] <= 10^9; all values position[i] are pairwise distinct; and m is an integer with 2 <= m <= n. -/
  theorem spec_11 (position : Slice Std.I64) (m : Std.I64)
      (hn : 2 ≤ position.val.length) (hnle : position.val.length ≤ 10 ^ 5)
      (hval : ∀ x ∈ position.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 9)
      (hnd : (vals position).Nodup)
      (hm : 2 ≤ m.val) (hmn : m.val ≤ (position.val.length : Int)) :
      ∃ r, max_distance position m = ok r ∧
        ∃ S : Finset (Fin position.val.length),
          (S.card : Int) = m.val ∧ minDist position S = r ∧
            (∃ i ∈ S, (position.val.get i).val = minVal position.val) ∧
            (∃ j ∈ S, (position.val.get j).val = maxVal position.val) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (position : Slice Std.I64) (m : Std.I64)
        (hn : 2 ≤ position.val.length) (hnle : position.val.length ≤ 10 ^ 5)
        (hval : ∀ x ∈ position.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 9)
        (hnd : (vals position).Nodup)
        (hm : 2 ≤ m.val) (hmn : m.val ≤ (position.val.length : Int)), ∃ r, max_distance position m = ok r ∧
          ∃ S : Finset (Fin position.val.length),
            (S.card : Int) = m.val ∧ minDist position S = r ∧
              (∃ i ∈ S, (position.val.get i).val = minVal position.val) ∧
              (∃ j ∈ S, (position.val.get j).val = maxVal position.val)) := by
    sorry

  /-- Let position' be any slice of integers such that the multiset of position' contains every element of position (i.e., position is a sub-multiset of position'), and let n' = len(position'). If the preconditions hold for position' with the same m (so 2 <= m <= n', all elements of position' are distinct, and 1 <= position'[i] <= 10^9 for all i), then max_distance(position', m) >= max_distance(position, m), where max_distance(position, m) denotes the result of the function on the given slice and m.
    Preconditions: Let n = len(position). The preconditions are: 2 <= n <= 10^5; for all i with 0 <= i < n, 1 <= position[i] <= 10^9; all values position[i] are pairwise distinct; and m is an integer with 2 <= m <= n. -/
  theorem spec_12 (position position' : Slice Std.I64) (m : Std.I64)
      (hn : 2 ≤ position.val.length) (hnle : position.val.length ≤ 10 ^ 5)
      (hval : ∀ x ∈ position.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 9)
      (hnd : (vals position).Nodup)
      (hm : 2 ≤ m.val) (hmn : m.val ≤ (position.val.length : Int))
      (hn' : 2 ≤ position'.val.length) (hnle' : position'.val.length ≤ 10 ^ 5)
      (hval' : ∀ x ∈ position'.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 9)
      (hnd' : (vals position').Nodup)
      (hmn' : m.val ≤ (position'.val.length : Int))
      (hsub : SubMultisetVals position position') :
      ∃ r r', max_distance position m = ok r ∧ max_distance position' m = ok r' ∧
        r ≤ r' := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (position position' : Slice Std.I64) (m : Std.I64)
        (hn : 2 ≤ position.val.length) (hnle : position.val.length ≤ 10 ^ 5)
        (hval : ∀ x ∈ position.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 9)
        (hnd : (vals position).Nodup)
        (hm : 2 ≤ m.val) (hmn : m.val ≤ (position.val.length : Int))
        (hn' : 2 ≤ position'.val.length) (hnle' : position'.val.length ≤ 10 ^ 5)
        (hval' : ∀ x ∈ position'.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 9)
        (hnd' : (vals position').Nodup)
        (hmn' : m.val ≤ (position'.val.length : Int))
        (hsub : SubMultisetVals position position'), ∃ r r', max_distance position m = ok r ∧ max_distance position' m = ok r' ∧
          r ≤ r') := by
    sorry

  end AegisSpec.MaxDistance
