import Aegis.MaxScore.Code.Funs

/-!
# Specifications of `Aegis.MaxScore.max_score`

LeetCode problem `maximize-the-minimum-game-score`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaxScore

  def contents (points : Slice Std.I64) : List Int := points.val.map (fun x => x.val)

  def entry (points : Slice Std.I64) (i : Nat) : Int := (contents points).getD i 0

  def listMin : List Int → Int
    | [] => 0
    | x :: xs => xs.foldl min x

  def listMax : List Int → Int
    | [] => 0
    | x :: xs => xs.foldl max x

  def minOver (n : Nat) (f : Nat → Int) : Int := listMin ((List.range n).map f)

  def maxOver (n : Nat) (f : Nat → Int) : Int := listMax ((List.range n).map f)

  def visits (m : Nat) (w : Nat → Int) (i : Nat) : Nat :=
    ((Finset.range m).filter (fun j => w (j + 1) = (i : Int))).card

  def IsWalk (n m : Nat) (w : Nat → Int) : Prop :=
    w 0 = -1 ∧ w 1 = 0 ∧
      (∀ j, 1 ≤ j → j ≤ m → 0 ≤ w j ∧ w j < (n : Int)) ∧
        (∀ j, j < m → w (j + 1) = w j + 1 ∨ w (j + 1) = w j - 1)

  def walkValue (n : Nat) (p : Nat → Int) (m : Nat) (w : Nat → Int) : Int :=
    minOver n (fun i => (visits m w i : Int) * p i)

  def Realizable (n m : Nat) (v : Nat → Nat) : Prop :=
    ∃ w, IsWalk n m w ∧ ∀ i, i < n → v i = visits m w i

  def IsMaxOverV (p : Nat → Int) (n m : Nat) (r : Int) : Prop :=
    (∀ v, Realizable n m v → minOver n (fun i => (v i : Int) * p i) ≤ r) ∧
      ∃ v, Realizable n m v ∧ minOver n (fun i => (v i : Int) * p i) = r

  def IsOptimal (n : Nat) (p : Nat → Int) (m : Nat) (r : Int) : Prop :=
    (∀ w, IsWalk n m w → walkValue n p m w ≤ r) ∧
      ∃ w, IsWalk n m w ∧ walkValue n p m w = r

  def IsOptimalUpTo (n : Nat) (p : Nat → Int) (m : Nat) (r : Int) : Prop :=
    (∀ t, t ≤ m → ∀ w, IsWalk n t w → walkValue n p t w ≤ r) ∧
      ∃ t, t ≤ m ∧ ∃ w, IsWalk n t w ∧ walkValue n p t w = r

  /-- Let V be the set of all vectors (v_0, ..., v_{n-1}) of nonnegative integers such that there exists a sequence w_1, ..., w_m with w_1 = 0, 0 <= w_j < n for all 1 <= j <= m, |w_{j+1} - w_j| = 1 for all 1 <= j < m, and v_i = |{ j | 1 <= j <= m, w_j = i }| for each i. The function returns r = max_{v in V} min_{i=0..n-1} (v_i * points[i]).
    Preconditions: Let n = len(points). Assume 2 <= n <= 50000, for all i with 0 <= i < n, 1 <= points[i] <= 10^6, and 1 <= m <= 10^9. -/
  theorem spec_1 (points : Slice Std.I64) (m : Std.I64)
      (hn_lo : 2 ≤ points.length) (hn_hi : points.length ≤ 50000)
      (hp : ∀ i, i < points.length → 1 ≤ entry points i ∧ entry points i ≤ (10 : Int) ^ 6)
      (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ (10 : Int) ^ 9) :
      ∃ r : Std.I64, Aegis.MaxScore.max_score points m = ok r ∧
        IsMaxOverV (entry points) points.length m.val.toNat r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (points : Slice Std.I64) (m : Std.I64)
        (hn_lo : 2 ≤ points.length) (hn_hi : points.length ≤ 50000)
        (hp : ∀ i, i < points.length → 1 ≤ entry points i ∧ entry points i ≤ (10 : Int) ^ 6)
        (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ (10 : Int) ^ 9), ∃ r : Std.I64, Aegis.MaxScore.max_score points m = ok r ∧
          IsMaxOverV (entry points) points.length m.val.toNat r.val) := by
    sorry

  /-- The function returns a result (i.e., it does not fail with overflow, out-of-bounds, or panic).
    Preconditions: Let n = len(points). Assume 2 <= n <= 50000, for all i with 0 <= i < n, 1 <= points[i] <= 10^6, and 1 <= m <= 10^9. -/
  theorem spec_2 (points : Slice Std.I64) (m : Std.I64)
      (hn_lo : 2 ≤ points.length) (hn_hi : points.length ≤ 50000)
      (hp : ∀ i, i < points.length → 1 ≤ entry points i ∧ entry points i ≤ (10 : Int) ^ 6)
      (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ (10 : Int) ^ 9) :
      ∃ r : Std.I64, Aegis.MaxScore.max_score points m = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (points : Slice Std.I64) (m : Std.I64)
        (hn_lo : 2 ≤ points.length) (hn_hi : points.length ≤ 50000)
        (hp : ∀ i, i < points.length → 1 ≤ entry points i ∧ entry points i ≤ (10 : Int) ^ 6)
        (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ (10 : Int) ^ 9), ∃ r : Std.I64, Aegis.MaxScore.max_score points m = ok r) := by
    sorry

  /-- The returned value r satisfies r >= 0.
    Preconditions: Let n = len(points). Assume 2 <= n <= 50000, for all i with 0 <= i < n, 1 <= points[i] <= 10^6, and 1 <= m <= 10^9. -/
  theorem spec_3 (points : Slice Std.I64) (m : Std.I64)
      (hn_lo : 2 ≤ points.length) (hn_hi : points.length ≤ 50000)
      (hp : ∀ i, i < points.length → 1 ≤ entry points i ∧ entry points i ≤ (10 : Int) ^ 6)
      (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ (10 : Int) ^ 9) :
      ∃ r : Std.I64, Aegis.MaxScore.max_score points m = ok r ∧ 0 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (points : Slice Std.I64) (m : Std.I64)
        (hn_lo : 2 ≤ points.length) (hn_hi : points.length ≤ 50000)
        (hp : ∀ i, i < points.length → 1 ≤ entry points i ∧ entry points i ≤ (10 : Int) ^ 6)
        (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ (10 : Int) ^ 9), ∃ r : Std.I64, Aegis.MaxScore.max_score points m = ok r ∧ 0 ≤ r.val) := by
    sorry

  /-- The returned value r satisfies r <= m * min_{i=0..n-1} points[i].
    Preconditions: Let n = len(points). Assume 2 <= n <= 50000, for all i with 0 <= i < n, 1 <= points[i] <= 10^6, and 1 <= m <= 10^9. -/
  theorem spec_4 (points : Slice Std.I64) (m : Std.I64)
      (hn_lo : 2 ≤ points.length) (hn_hi : points.length ≤ 50000)
      (hp : ∀ i, i < points.length → 1 ≤ entry points i ∧ entry points i ≤ (10 : Int) ^ 6)
      (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ (10 : Int) ^ 9) :
      ∃ r : Std.I64, Aegis.MaxScore.max_score points m = ok r ∧
        r.val ≤ m.val * minOver points.length (entry points) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (points : Slice Std.I64) (m : Std.I64)
        (hn_lo : 2 ≤ points.length) (hn_hi : points.length ≤ 50000)
        (hp : ∀ i, i < points.length → 1 ≤ entry points i ∧ entry points i ≤ (10 : Int) ^ 6)
        (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ (10 : Int) ^ 9), ∃ r : Std.I64, Aegis.MaxScore.max_score points m = ok r ∧
          r.val ≤ m.val * minOver points.length (entry points)) := by
    sorry

  /-- The returned value r satisfies r >= min_{i=0..n-1} points[i].
    Preconditions: Let n = len(points). Assume 2 <= n <= 50000, for all i with 0 <= i < n, 1 <= points[i] <= 10^6, 1 <= m <= 10^9, and m >= n. -/
  theorem spec_5 (points : Slice Std.I64) (m : Std.I64)
      (hn_lo : 2 ≤ points.length) (hn_hi : points.length ≤ 50000)
      (hp : ∀ i, i < points.length → 1 ≤ entry points i ∧ entry points i ≤ (10 : Int) ^ 6)
      (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ (10 : Int) ^ 9)
      (hmn : (points.length : Int) ≤ m.val) :
      ∃ r : Std.I64, Aegis.MaxScore.max_score points m = ok r ∧
        minOver points.length (entry points) ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (points : Slice Std.I64) (m : Std.I64)
        (hn_lo : 2 ≤ points.length) (hn_hi : points.length ≤ 50000)
        (hp : ∀ i, i < points.length → 1 ≤ entry points i ∧ entry points i ≤ (10 : Int) ^ 6)
        (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ (10 : Int) ^ 9)
        (hmn : (points.length : Int) ≤ m.val), ∃ r : Std.I64, Aegis.MaxScore.max_score points m = ok r ∧
          minOver points.length (entry points) ≤ r.val) := by
    sorry

  /-- The returned value r is 0.
    Preconditions: Let n = len(points). Assume 2 <= n <= 50000, for all i with 0 <= i < n, 1 <= points[i] <= 10^6, 1 <= m <= 10^9, and m < n. -/
  theorem spec_6 (points : Slice Std.I64) (m : Std.I64)
      (hn_lo : 2 ≤ points.length) (hn_hi : points.length ≤ 50000)
      (hp : ∀ i, i < points.length → 1 ≤ entry points i ∧ entry points i ≤ (10 : Int) ^ 6)
      (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ (10 : Int) ^ 9)
      (hmn : m.val < (points.length : Int)) :
      ∃ r : Std.I64, Aegis.MaxScore.max_score points m = ok r ∧ r.val = 0 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (points : Slice Std.I64) (m : Std.I64)
        (hn_lo : 2 ≤ points.length) (hn_hi : points.length ≤ 50000)
        (hp : ∀ i, i < points.length → 1 ≤ entry points i ∧ entry points i ≤ (10 : Int) ^ 6)
        (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ (10 : Int) ^ 9)
        (hmn : m.val < (points.length : Int)), ∃ r : Std.I64, Aegis.MaxScore.max_score points m = ok r ∧ r.val = 0) := by
    sorry

  /-- The returned value r = min( ((m+1) div 2) * points[0], (m div 2) * points[1] ).
    Preconditions: Let n = len(points) = 2. Assume 1 <= points[0], points[1] <= 10^6, and 1 <= m <= 10^9. -/
  theorem spec_7 (points : Slice Std.I64) (m : Std.I64)
      (hn : points.length = 2)
      (hp0 : 1 ≤ entry points 0 ∧ entry points 0 ≤ (10 : Int) ^ 6)
      (hp1 : 1 ≤ entry points 1 ∧ entry points 1 ≤ (10 : Int) ^ 6)
      (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ (10 : Int) ^ 9) :
      ∃ r : Std.I64, Aegis.MaxScore.max_score points m = ok r ∧
        r.val = min (((m.val + 1) / 2) * entry points 0) ((m.val / 2) * entry points 1) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (points : Slice Std.I64) (m : Std.I64)
        (hn : points.length = 2)
        (hp0 : 1 ≤ entry points 0 ∧ entry points 0 ≤ (10 : Int) ^ 6)
        (hp1 : 1 ≤ entry points 1 ∧ entry points 1 ≤ (10 : Int) ^ 6)
        (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ (10 : Int) ^ 9), ∃ r : Std.I64, Aegis.MaxScore.max_score points m = ok r ∧
          r.val = min (((m.val + 1) / 2) * entry points 0) ((m.val / 2) * entry points 1)) := by
    sorry

  /-- The returned value r = min_{i=0..n-1} points[i].
    Preconditions: Let n = len(points). Assume 2 <= n <= 50000, for all i with 0 <= i < n, 1 <= points[i] <= 10^6, 1 <= m <= 10^9, and m = n. -/
  theorem spec_8 (points : Slice Std.I64) (m : Std.I64)
      (hn_lo : 2 ≤ points.length) (hn_hi : points.length ≤ 50000)
      (hp : ∀ i, i < points.length → 1 ≤ entry points i ∧ entry points i ≤ (10 : Int) ^ 6)
      (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ (10 : Int) ^ 9)
      (hmn : m.val = (points.length : Int)) :
      ∃ r : Std.I64, Aegis.MaxScore.max_score points m = ok r ∧
        r.val = minOver points.length (entry points) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (points : Slice Std.I64) (m : Std.I64)
        (hn_lo : 2 ≤ points.length) (hn_hi : points.length ≤ 50000)
        (hp : ∀ i, i < points.length → 1 ≤ entry points i ∧ entry points i ≤ (10 : Int) ^ 6)
        (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ (10 : Int) ^ 9)
        (hmn : m.val = (points.length : Int)), ∃ r : Std.I64, Aegis.MaxScore.max_score points m = ok r ∧
          r.val = minOver points.length (entry points)) := by
    sorry

  /-- max_score(points, m1) <= max_score(points, m2).
    Preconditions: Let n = len(points). Assume 2 <= n <= 50000, for all i with 0 <= i < n, 1 <= points[i] <= 10^6. Let m1 and m2 be integers with 1 <= m1 <= m2 <= 10^9. -/
  theorem spec_9 (points : Slice Std.I64) (m1 m2 : Std.I64)
      (hn_lo : 2 ≤ points.length) (hn_hi : points.length ≤ 50000)
      (hp : ∀ i, i < points.length → 1 ≤ entry points i ∧ entry points i ≤ (10 : Int) ^ 6)
      (hm1_lo : 1 ≤ m1.val) (hm12 : m1.val ≤ m2.val) (hm2_hi : m2.val ≤ (10 : Int) ^ 9) :
      ∀ r1 r2 : Std.I64, Aegis.MaxScore.max_score points m1 = ok r1 →
        Aegis.MaxScore.max_score points m2 = ok r2 → r1.val ≤ r2.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (points : Slice Std.I64) (m1 m2 : Std.I64)
        (hn_lo : 2 ≤ points.length) (hn_hi : points.length ≤ 50000)
        (hp : ∀ i, i < points.length → 1 ≤ entry points i ∧ entry points i ≤ (10 : Int) ^ 6)
        (hm1_lo : 1 ≤ m1.val) (hm12 : m1.val ≤ m2.val) (hm2_hi : m2.val ≤ (10 : Int) ^ 9), ∀ r1 r2 : Std.I64, Aegis.MaxScore.max_score points m1 = ok r1 →
          Aegis.MaxScore.max_score points m2 = ok r2 → r1.val ≤ r2.val) := by
    sorry

  /-- max_score(points1, m) <= max_score(points2, m).
    Preconditions: Let n = len(points1) = len(points2). Assume 2 <= n <= 50000, for all i with 0 <= i < n, 1 <= points1[i] <= points2[i] <= 10^6, and 1 <= m <= 10^9. -/
  theorem spec_10 (points1 points2 : Slice Std.I64) (m : Std.I64)
      (hlen : points1.length = points2.length)
      (hn_lo : 2 ≤ points1.length) (hn_hi : points1.length ≤ 50000)
      (hp : ∀ i, i < points1.length →
        1 ≤ entry points1 i ∧ entry points1 i ≤ entry points2 i ∧
          entry points2 i ≤ (10 : Int) ^ 6)
      (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ (10 : Int) ^ 9) :
      ∀ r1 r2 : Std.I64, Aegis.MaxScore.max_score points1 m = ok r1 →
        Aegis.MaxScore.max_score points2 m = ok r2 → r1.val ≤ r2.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (points1 points2 : Slice Std.I64) (m : Std.I64)
        (hlen : points1.length = points2.length)
        (hn_lo : 2 ≤ points1.length) (hn_hi : points1.length ≤ 50000)
        (hp : ∀ i, i < points1.length →
          1 ≤ entry points1 i ∧ entry points1 i ≤ entry points2 i ∧
            entry points2 i ≤ (10 : Int) ^ 6)
        (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ (10 : Int) ^ 9), ∀ r1 r2 : Std.I64, Aegis.MaxScore.max_score points1 m = ok r1 →
          Aegis.MaxScore.max_score points2 m = ok r2 → r1.val ≤ r2.val) := by
    sorry

  /-- max_score(c * points, m) = c * max_score(points, m), where c * points denotes the array with elements c * points[i].
    Preconditions: Let n = len(points). Assume 2 <= n <= 50000, for all i with 0 <= i < n, 1 <= points[i] <= 10^6, and 1 <= m <= 10^9. Let c be a positive integer such that for all i, c * points[i] <= 10^6. -/
  theorem spec_11 (points points' : Slice Std.I64) (m c : Std.I64)
      (hn_lo : 2 ≤ points.length) (hn_hi : points.length ≤ 50000)
      (hp : ∀ i, i < points.length → 1 ≤ entry points i ∧ entry points i ≤ (10 : Int) ^ 6)
      (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ (10 : Int) ^ 9)
      (hc_pos : 0 < c.val)
      (hc_bound : ∀ i, i < points.length → c.val * entry points i ≤ (10 : Int) ^ 6)
      (hlen : points'.length = points.length)
      (hscaled : ∀ i, i < points.length → entry points' i = c.val * entry points i) :
      ∃ r r' : Std.I64, Aegis.MaxScore.max_score points' m = ok r ∧
        Aegis.MaxScore.max_score points m = ok r' ∧ r.val = c.val * r'.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (points points' : Slice Std.I64) (m c : Std.I64)
        (hn_lo : 2 ≤ points.length) (hn_hi : points.length ≤ 50000)
        (hp : ∀ i, i < points.length → 1 ≤ entry points i ∧ entry points i ≤ (10 : Int) ^ 6)
        (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ (10 : Int) ^ 9)
        (hc_pos : 0 < c.val)
        (hc_bound : ∀ i, i < points.length → c.val * entry points i ≤ (10 : Int) ^ 6)
        (hlen : points'.length = points.length)
        (hscaled : ∀ i, i < points.length → entry points' i = c.val * entry points i), ∃ r r' : Std.I64, Aegis.MaxScore.max_score points' m = ok r ∧
          Aegis.MaxScore.max_score points m = ok r' ∧ r.val = c.val * r'.val) := by
    sorry

  /-- There exists a walk of length exactly m (starting at -1, first move to 0, staying within 0..n-1, and moving to adjacent indices) with visit counts v such that min_{i=0..n-1} (v_i * points[i]) = r, where r is the returned value.
    Preconditions: Let n = len(points). Assume 2 <= n <= 50000, for all i with 0 <= i < n, 1 <= points[i] <= 10^6, and 1 <= m <= 10^9. -/
  theorem spec_12 (points : Slice Std.I64) (m : Std.I64)
      (hn_lo : 2 ≤ points.length) (hn_hi : points.length ≤ 50000)
      (hp : ∀ i, i < points.length → 1 ≤ entry points i ∧ entry points i ≤ (10 : Int) ^ 6)
      (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ (10 : Int) ^ 9) :
      ∃ r : Std.I64, Aegis.MaxScore.max_score points m = ok r ∧
        ∃ w : Nat → Int, IsWalk points.length m.val.toNat w ∧
          walkValue points.length (entry points) m.val.toNat w = r.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (points : Slice Std.I64) (m : Std.I64)
        (hn_lo : 2 ≤ points.length) (hn_hi : points.length ≤ 50000)
        (hp : ∀ i, i < points.length → 1 ≤ entry points i ∧ entry points i ≤ (10 : Int) ^ 6)
        (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ (10 : Int) ^ 9), ∃ r : Std.I64, Aegis.MaxScore.max_score points m = ok r ∧
          ∃ w : Nat → Int, IsWalk points.length m.val.toNat w ∧
            walkValue points.length (entry points) m.val.toNat w = r.val) := by
    sorry

  /-- For every walk of length exactly m (starting at -1, first move to 0, staying within 0..n-1, and moving to adjacent indices) with visit counts v, we have min_{i=0..n-1} (v_i * points[i]) <= r, where r is the returned value.
    Preconditions: Let n = len(points). Assume 2 <= n <= 50000, for all i with 0 <= i < n, 1 <= points[i] <= 10^6, and 1 <= m <= 10^9. -/
  theorem spec_13 (points : Slice Std.I64) (m : Std.I64)
      (hn_lo : 2 ≤ points.length) (hn_hi : points.length ≤ 50000)
      (hp : ∀ i, i < points.length → 1 ≤ entry points i ∧ entry points i ≤ (10 : Int) ^ 6)
      (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ (10 : Int) ^ 9) :
      ∀ r : Std.I64, Aegis.MaxScore.max_score points m = ok r →
        ∀ w : Nat → Int, IsWalk points.length m.val.toNat w →
          walkValue points.length (entry points) m.val.toNat w ≤ r.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (points : Slice Std.I64) (m : Std.I64)
        (hn_lo : 2 ≤ points.length) (hn_hi : points.length ≤ 50000)
        (hp : ∀ i, i < points.length → 1 ≤ entry points i ∧ entry points i ≤ (10 : Int) ^ 6)
        (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ (10 : Int) ^ 9), ∀ r : Std.I64, Aegis.MaxScore.max_score points m = ok r →
          ∀ w : Nat → Int, IsWalk points.length m.val.toNat w →
            walkValue points.length (entry points) m.val.toNat w ≤ r.val) := by
    sorry

  /-- For any integer x, x <= r if and only if there exists a walk of length exactly m (starting at -1, first move to 0, staying within 0..n-1, and moving to adjacent indices) with visit counts v such that for all i, v_i * points[i] >= x. Here r is the returned value.
    Preconditions: Let n = len(points). Assume 2 <= n <= 50000, for all i with 0 <= i < n, 1 <= points[i] <= 10^6, and 1 <= m <= 10^9. -/
  theorem spec_14 (points : Slice Std.I64) (m : Std.I64)
      (hn_lo : 2 ≤ points.length) (hn_hi : points.length ≤ 50000)
      (hp : ∀ i, i < points.length → 1 ≤ entry points i ∧ entry points i ≤ (10 : Int) ^ 6)
      (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ (10 : Int) ^ 9) :
      ∀ r : Std.I64, Aegis.MaxScore.max_score points m = ok r →
        ∀ x : Int, x ≤ r.val ↔
          ∃ w : Nat → Int, IsWalk points.length m.val.toNat w ∧
            ∀ i, i < points.length → x ≤ (visits m.val.toNat w i : Int) * entry points i := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (points : Slice Std.I64) (m : Std.I64)
        (hn_lo : 2 ≤ points.length) (hn_hi : points.length ≤ 50000)
        (hp : ∀ i, i < points.length → 1 ≤ entry points i ∧ entry points i ≤ (10 : Int) ^ 6)
        (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ (10 : Int) ^ 9), ∀ r : Std.I64, Aegis.MaxScore.max_score points m = ok r →
          ∀ x : Int, x ≤ r.val ↔
            ∃ w : Nat → Int, IsWalk points.length m.val.toNat w ∧
              ∀ i, i < points.length → x ≤ (visits m.val.toNat w i : Int) * entry points i) := by
    sorry

  /-- Let r_at_most be the maximum of min_{i=0..n-1} (v_i * points[i]) over all walks of length t for any integer t with 0 <= t <= m (starting at -1, first move to 0, staying within 0..n-1, and moving to adjacent indices). Then r_at_most = r, where r is the returned value.
    Preconditions: Let n = len(points). Assume 2 <= n <= 50000, for all i with 0 <= i < n, 1 <= points[i] <= 10^6, and 1 <= m <= 10^9. -/
  theorem spec_15 (points : Slice Std.I64) (m : Std.I64)
      (hn_lo : 2 ≤ points.length) (hn_hi : points.length ≤ 50000)
      (hp : ∀ i, i < points.length → 1 ≤ entry points i ∧ entry points i ≤ (10 : Int) ^ 6)
      (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ (10 : Int) ^ 9) :
      ∃ r : Std.I64, Aegis.MaxScore.max_score points m = ok r ∧
        IsOptimalUpTo points.length (entry points) m.val.toNat r.val := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (points : Slice Std.I64) (m : Std.I64)
        (hn_lo : 2 ≤ points.length) (hn_hi : points.length ≤ 50000)
        (hp : ∀ i, i < points.length → 1 ≤ entry points i ∧ entry points i ≤ (10 : Int) ^ 6)
        (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ (10 : Int) ^ 9), ∃ r : Std.I64, Aegis.MaxScore.max_score points m = ok r ∧
          IsOptimalUpTo points.length (entry points) m.val.toNat r.val) := by
    sorry

  /-- 0 <= r_m - r_{m-1} <= max_{i=0..n-1} points[i].
    Preconditions: Let n = len(points). Assume 2 <= n <= 50000, for all i with 0 <= i < n, 1 <= points[i] <= 10^6. Let m be an integer with 2 <= m <= 10^9. Let r_m = max_score(points, m) and r_{m-1} = max_score(points, m-1). -/
  theorem spec_16 (points : Slice Std.I64) (m m' : Std.I64)
      (hn_lo : 2 ≤ points.length) (hn_hi : points.length ≤ 50000)
      (hp : ∀ i, i < points.length → 1 ≤ entry points i ∧ entry points i ≤ (10 : Int) ^ 6)
      (hm_lo : 2 ≤ m.val) (hm_hi : m.val ≤ (10 : Int) ^ 9)
      (hm' : m'.val = m.val - 1) :
      ∀ rm rm1 : Std.I64, Aegis.MaxScore.max_score points m = ok rm →
        Aegis.MaxScore.max_score points m' = ok rm1 →
          0 ≤ rm.val - rm1.val ∧ rm.val - rm1.val ≤ maxOver points.length (entry points) := by
    sorry

  theorem spec_16_neg :
      ¬ (∀ (points : Slice Std.I64) (m m' : Std.I64)
        (hn_lo : 2 ≤ points.length) (hn_hi : points.length ≤ 50000)
        (hp : ∀ i, i < points.length → 1 ≤ entry points i ∧ entry points i ≤ (10 : Int) ^ 6)
        (hm_lo : 2 ≤ m.val) (hm_hi : m.val ≤ (10 : Int) ^ 9)
        (hm' : m'.val = m.val - 1), ∀ rm rm1 : Std.I64, Aegis.MaxScore.max_score points m = ok rm →
          Aegis.MaxScore.max_score points m' = ok rm1 →
            0 ≤ rm.val - rm1.val ∧ rm.val - rm1.val ≤ maxOver points.length (entry points)) := by
    sorry

  end AegisSpec.MaxScore
