import Aegis.MinTimeToReach.Code.Funs

/-!
# Specifications of `Aegis.MinTimeToReach.min_time_to_reach`

LeetCode problem `find-minimum-time-to-reach-last-room-i`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinTimeToReach

  abbrev Grid := Aeneas.Std.Slice (Aeneas.Std.alloc.vec.Vec Aeneas.Std.I64)

  def nrows (g : Grid) : Nat := g.val.length

  def ncols (g : Grid) : Nat :=
    match g.val with
    | [] => 0
    | r :: _ => r.val.length

  def entry (g : Grid) (i j : Nat) : Int :=
    match g.val[i]? with
    | none => 0
    | some r =>
      match r.val[j]? with
      | none => 0
      | some x => x.val

  def IsValidGrid (g : Grid) (n m : Nat) : Prop :=
    n = nrows g ∧ m = ncols g ∧
    2 ≤ n ∧ n ≤ 50 ∧ 2 ≤ m ∧ m ≤ 50 ∧
    (∀ r ∈ g.val, r.val.length = m) ∧
    (∀ i j, i < n → j < m → 0 ≤ entry g i j ∧ entry g i j ≤ 1000000000)

  def Adjacent (a b : Nat × Nat) : Prop :=
    (a.1 = b.1 ∧ (a.2 + 1 = b.2 ∨ b.2 + 1 = a.2)) ∨
    (a.2 = b.2 ∧ (a.1 + 1 = b.1 ∨ b.1 + 1 = a.1))

  def ConsecutiveAdjacent : List (Nat × Nat) → Prop
    | [] => True
    | [_] => True
    | a :: b :: rest => Adjacent a b ∧ ConsecutiveAdjacent (b :: rest)

  def InBounds (g : Grid) (q : Nat × Nat) : Prop := q.1 < nrows g ∧ q.2 < ncols g

  def AllInBounds (g : Grid) (p : List (Nat × Nat)) : Prop := ∀ q ∈ p, InBounds g q

  def IsPath (g : Grid) (p : List (Nat × Nat)) : Prop :=
    p.head? = some (0, 0) ∧
    p.getLast? = some (nrows g - 1, ncols g - 1) ∧
    ConsecutiveAdjacent p ∧
    AllInBounds g p

  def arrivalFrom (g : Grid) (t : Int) : List (Nat × Nat) → Int
    | [] => t
    | q :: qs => arrivalFrom g (max t (entry g q.1 q.2) + 1) qs

  def arrival (g : Grid) (p : List (Nat × Nat)) : Int :=
    match p with
    | [] => 0
    | _ :: qs => arrivalFrom g 0 qs

  def IndexBound (g : Grid) (p : List (Nat × Nat)) : Prop :=
    ∀ (q : Nat) (h : q < p.length), 1 ≤ q → entry g (p.get ⟨q, h⟩).1 (p.get ⟨q, h⟩).2 ≤ (q : Int) - 1

  def allEntries (g : Grid) (n m : Nat) : List Int :=
    (List.range n).flatMap fun i => (List.range m).map fun j => entry g i j

  def maxEntry (g : Grid) (n m : Nat) : Int :=
    match allEntries g n m with
    | [] => 0
    | x :: xs => xs.foldl max x

  /-- Define an admissible path as a finite sequence of rooms p_0,...,p_k with p_0=(0,0), p_k=(n-1,m-1), and each consecutive pair sharing a side (|di|+|dj|=1). For such a path define its arrival time T by T_0=0 and T_{s+1}=max(T_s, moveTime[p_{s+1}]) + 1 for 0 <= s < k. The function returns a result r, and r is the minimum of T_k over all admissible paths; equivalently, some admissible path has arrival time r and every admissible path has arrival time >= r.
    Preconditions: Let n = len(moveTime) and m = len(moveTime[0]). The input is valid: 2 <= n <= 50, every row of moveTime has length m, 2 <= m <= 50, and 0 <= moveTime[i][j] <= 10^9 for all 0 <= i < n and 0 <= j < m. -/
  theorem spec_1 (g : Grid) (n m : Nat) (h : IsValidGrid g n m) :
      ∃ r : Aeneas.Std.I64,
        Aegis.MinTimeToReach.min_time_to_reach g = Aeneas.Std.Result.ok r ∧
        (∃ p : List (Nat × Nat), IsPath g p ∧ arrival g p = r.val) ∧
        (∀ p : List (Nat × Nat), IsPath g p → r.val ≤ arrival g p) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (g : Grid) (n m : Nat) (h : IsValidGrid g n m), ∃ r : Aeneas.Std.I64,
          Aegis.MinTimeToReach.min_time_to_reach g = Aeneas.Std.Result.ok r ∧
          (∃ p : List (Nat × Nat), IsPath g p ∧ arrival g p = r.val) ∧
          (∀ p : List (Nat × Nat), IsPath g p → r.val ≤ arrival g p)) := by
    sorry

  /-- The function returns a result r; it does not fail (no panic, integer overflow, out-of-bounds access, or other failure) on any valid input.
    Preconditions: Let n = len(moveTime) and m = len(moveTime[0]). The input is valid: 2 <= n <= 50, every row of moveTime has length m, 2 <= m <= 50, and 0 <= moveTime[i][j] <= 10^9 for all 0 <= i < n and 0 <= j < m. -/
  theorem spec_2 (g : Grid) (n m : Nat) (h : IsValidGrid g n m) :
      ∃ r : Aeneas.Std.I64, Aegis.MinTimeToReach.min_time_to_reach g = Aeneas.Std.Result.ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (g : Grid) (n m : Nat) (h : IsValidGrid g n m), ∃ r : Aeneas.Std.I64, Aegis.MinTimeToReach.min_time_to_reach g = Aeneas.Std.Result.ok r) := by
    sorry

  /-- Whenever the function returns a result r, r >= n + m - 2.
    Preconditions: Let n = len(moveTime) and m = len(moveTime[0]). The input is valid: 2 <= n <= 50, every row of moveTime has length m, 2 <= m <= 50, and 0 <= moveTime[i][j] <= 10^9 for all 0 <= i < n and 0 <= j < m. -/
  theorem spec_3 (g : Grid) (n m : Nat) (h : IsValidGrid g n m) :
      ∀ r : Aeneas.Std.I64,
        Aegis.MinTimeToReach.min_time_to_reach g = Aeneas.Std.Result.ok r →
        (n : Int) + (m : Int) - 2 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (g : Grid) (n m : Nat) (h : IsValidGrid g n m), ∀ r : Aeneas.Std.I64,
          Aegis.MinTimeToReach.min_time_to_reach g = Aeneas.Std.Result.ok r →
          (n : Int) + (m : Int) - 2 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r >= moveTime[n-1][m-1] + 1.
    Preconditions: Let n = len(moveTime) and m = len(moveTime[0]). The input is valid: 2 <= n <= 50, every row of moveTime has length m, 2 <= m <= 50, and 0 <= moveTime[i][j] <= 10^9 for all 0 <= i < n and 0 <= j < m. -/
  theorem spec_4 (g : Grid) (n m : Nat) (h : IsValidGrid g n m) :
      ∀ r : Aeneas.Std.I64,
        Aegis.MinTimeToReach.min_time_to_reach g = Aeneas.Std.Result.ok r →
        entry g (n - 1) (m - 1) + 1 ≤ r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (g : Grid) (n m : Nat) (h : IsValidGrid g n m), ∀ r : Aeneas.Std.I64,
          Aegis.MinTimeToReach.min_time_to_reach g = Aeneas.Std.Result.ok r →
          entry g (n - 1) (m - 1) + 1 ≤ r.val) := by
    sorry

  /-- Let M = max{ moveTime[i][j] | 0 <= i < n and 0 <= j < m }. Whenever the function returns a result r, r <= M + n + m - 2.
    Preconditions: Let n = len(moveTime) and m = len(moveTime[0]). The input is valid: 2 <= n <= 50, every row of moveTime has length m, 2 <= m <= 50, and 0 <= moveTime[i][j] <= 10^9 for all 0 <= i < n and 0 <= j < m. -/
  theorem spec_5 (g : Grid) (n m : Nat) (h : IsValidGrid g n m) :
      ∀ r : Aeneas.Std.I64,
        Aegis.MinTimeToReach.min_time_to_reach g = Aeneas.Std.Result.ok r →
        r.val ≤ maxEntry g n m + (n : Int) + (m : Int) - 2 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (g : Grid) (n m : Nat) (h : IsValidGrid g n m), ∀ r : Aeneas.Std.I64,
          Aegis.MinTimeToReach.min_time_to_reach g = Aeneas.Std.Result.ok r →
          r.val ≤ maxEntry g n m + (n : Int) + (m : Int) - 2) := by
    sorry

  /-- The function returns a result r and r = n + m - 2.
    Preconditions: Let n = len(moveTime) and m = len(moveTime[0]). The input is valid: 2 <= n <= 50, every row of moveTime has length m, 2 <= m <= 50, and 0 <= moveTime[i][j] <= 10^9 for all 0 <= i < n and 0 <= j < m. Also moveTime[i][j] = 0 for every 0 <= i < n and 0 <= j < m. -/
  theorem spec_6 (g : Grid) (n m : Nat) (h : IsValidGrid g n m)
      (hzero : ∀ i j, i < n → j < m → entry g i j = 0) :
      ∃ r : Aeneas.Std.I64,
        Aegis.MinTimeToReach.min_time_to_reach g = Aeneas.Std.Result.ok r ∧
        r.val = (n : Int) + (m : Int) - 2 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (g : Grid) (n m : Nat) (h : IsValidGrid g n m)
        (hzero : ∀ i j, i < n → j < m → entry g i j = 0), ∃ r : Aeneas.Std.I64,
          Aegis.MinTimeToReach.min_time_to_reach g = Aeneas.Std.Result.ok r ∧
          r.val = (n : Int) + (m : Int) - 2) := by
    sorry

  /-- Whenever the function returns a result r, r = L if and only if there exists an adjacent-room path p_0,...,p_L with p_0=(0,0), p_L=(n-1,m-1), and moveTime[p_q] <= q-1 for every q with 1 <= q <= L.
    Preconditions: Let n = len(moveTime) and m = len(moveTime[0]). The input is valid: 2 <= n <= 50, every row of moveTime has length m, 2 <= m <= 50, and 0 <= moveTime[i][j] <= 10^9 for all 0 <= i < n and 0 <= j < m. Let L = n + m - 2. -/
  theorem spec_7 (g : Grid) (n m : Nat) (h : IsValidGrid g n m) :
      ∀ r : Aeneas.Std.I64,
        Aegis.MinTimeToReach.min_time_to_reach g = Aeneas.Std.Result.ok r →
        (r.val = (n : Int) + (m : Int) - 2 ↔
          ∃ p : List (Nat × Nat), IsPath g p ∧ p.length = n + m - 2 + 1 ∧ IndexBound g p) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (g : Grid) (n m : Nat) (h : IsValidGrid g n m), ∀ r : Aeneas.Std.I64,
          Aegis.MinTimeToReach.min_time_to_reach g = Aeneas.Std.Result.ok r →
          (r.val = (n : Int) + (m : Int) - 2 ↔
            ∃ p : List (Nat × Nat), IsPath g p ∧ p.length = n + m - 2 + 1 ∧ IndexBound g p)) := by
    sorry

  /-- If the function returns rA on A and rB on B, then rA <= rB.
    Preconditions: Let A and B be two valid n by m grids: 2 <= n <= 50, 2 <= m <= 50, every row has length m, and all entries are between 0 and 10^9. Assume A[i][j] <= B[i][j] for all 0 <= i < n and 0 <= j < m. -/
  theorem spec_8 (A B : Grid) (n m : Nat) (hA : IsValidGrid A n m) (hB : IsValidGrid B n m)
      (hle : ∀ i j, i < n → j < m → entry A i j ≤ entry B i j) :
      ∀ rA rB : Aeneas.Std.I64,
        Aegis.MinTimeToReach.min_time_to_reach A = Aeneas.Std.Result.ok rA →
        Aegis.MinTimeToReach.min_time_to_reach B = Aeneas.Std.Result.ok rB →
        rA.val ≤ rB.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (A B : Grid) (n m : Nat) (hA : IsValidGrid A n m) (hB : IsValidGrid B n m)
        (hle : ∀ i j, i < n → j < m → entry A i j ≤ entry B i j), ∀ rA rB : Aeneas.Std.I64,
          Aegis.MinTimeToReach.min_time_to_reach A = Aeneas.Std.Result.ok rA →
          Aegis.MinTimeToReach.min_time_to_reach B = Aeneas.Std.Result.ok rB →
          rA.val ≤ rB.val) := by
    sorry

  /-- If the function returns rA on A and rB on B, then rA = rB.
    Preconditions: Let A and B be two valid n by m grids: 2 <= n <= 50, 2 <= m <= 50, every row has length m, and all entries are between 0 and 10^9. Assume A[i][j] = B[i][j] for every 0 <= i < n and 0 <= j < m except possibly at (i,j)=(0,0). -/
  theorem spec_9 (A B : Grid) (n m : Nat) (hA : IsValidGrid A n m) (hB : IsValidGrid B n m)
      (heq : ∀ i j, i < n → j < m → (i, j) ≠ (0, 0) → entry A i j = entry B i j) :
      ∀ rA rB : Aeneas.Std.I64,
        Aegis.MinTimeToReach.min_time_to_reach A = Aeneas.Std.Result.ok rA →
        Aegis.MinTimeToReach.min_time_to_reach B = Aeneas.Std.Result.ok rB →
        rA.val = rB.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (A B : Grid) (n m : Nat) (hA : IsValidGrid A n m) (hB : IsValidGrid B n m)
        (heq : ∀ i j, i < n → j < m → (i, j) ≠ (0, 0) → entry A i j = entry B i j), ∀ rA rB : Aeneas.Std.I64,
          Aegis.MinTimeToReach.min_time_to_reach A = Aeneas.Std.Result.ok rA →
          Aegis.MinTimeToReach.min_time_to_reach B = Aeneas.Std.Result.ok rB →
          rA.val = rB.val) := by
    sorry

  /-- If the function returns rA on A and rB on B, then rB = rA + C.
    Preconditions: Let A be a valid n by m grid: 2 <= n <= 50, 2 <= m <= 50, every row has length m, and all entries are between 0 and 10^9. Let C be an integer with C >= 0, and let B be the n by m grid with B[i][j] = A[i][j] + C for all i,j; assume B is valid, i.e. A[i][j] + C <= 10^9 for all i,j. -/
  theorem spec_10 (A B : Grid) (n m : Nat) (C : Int) (hA : IsValidGrid A n m) (hC : 0 ≤ C)
      (hshift : ∀ i j, i < n → j < m → entry B i j = entry A i j + C)
      (hB : IsValidGrid B n m) :
      ∀ rA rB : Aeneas.Std.I64,
        Aegis.MinTimeToReach.min_time_to_reach A = Aeneas.Std.Result.ok rA →
        Aegis.MinTimeToReach.min_time_to_reach B = Aeneas.Std.Result.ok rB →
        rB.val = rA.val + C := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (A B : Grid) (n m : Nat) (C : Int) (hA : IsValidGrid A n m) (hC : 0 ≤ C)
        (hshift : ∀ i j, i < n → j < m → entry B i j = entry A i j + C)
        (hB : IsValidGrid B n m), ∀ rA rB : Aeneas.Std.I64,
          Aegis.MinTimeToReach.min_time_to_reach A = Aeneas.Std.Result.ok rA →
          Aegis.MinTimeToReach.min_time_to_reach B = Aeneas.Std.Result.ok rB →
          rB.val = rA.val + C) := by
    sorry

  /-- Whenever the function returns a result r, there exists an admissible path from (0,0) to (n-1,m-1) that visits no room more than once and whose arrival time, defined by T_0=0 and T_{s+1}=max(T_s, moveTime[next room]) + 1, is exactly r.
    Preconditions: Let n = len(moveTime) and m = len(moveTime[0]). The input is valid: 2 <= n <= 50, every row of moveTime has length m, 2 <= m <= 50, and 0 <= moveTime[i][j] <= 10^9 for all 0 <= i < n and 0 <= j < m. -/
  theorem spec_11 (g : Grid) (n m : Nat) (h : IsValidGrid g n m) :
      ∀ r : Aeneas.Std.I64,
        Aegis.MinTimeToReach.min_time_to_reach g = Aeneas.Std.Result.ok r →
        ∃ p : List (Nat × Nat), IsPath g p ∧ p.Nodup ∧ arrival g p = r.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (g : Grid) (n m : Nat) (h : IsValidGrid g n m), ∀ r : Aeneas.Std.I64,
          Aegis.MinTimeToReach.min_time_to_reach g = Aeneas.Std.Result.ok r →
          ∃ p : List (Nat × Nat), IsPath g p ∧ p.Nodup ∧ arrival g p = r.val) := by
    sorry

  /-- If the function returns r on A and r0 on A0, then r = max(d + 1, r0).
    Preconditions: Let A be a valid n by m grid: 2 <= n <= 50, 2 <= m <= 50, every row has length m, and all entries are between 0 and 10^9. Let d = A[n-1][m-1]. Let A0 be identical to A except that A0[n-1][m-1] = 0; A0 is valid. -/
  theorem spec_12 (A A0 : Grid) (n m : Nat) (d : Int) (hA : IsValidGrid A n m)
      (hd : d = entry A (n - 1) (m - 1)) (hA0 : IsValidGrid A0 n m)
      (htarget : entry A0 (n - 1) (m - 1) = 0)
      (heq : ∀ i j, i < n → j < m → (i, j) ≠ (n - 1, m - 1) → entry A0 i j = entry A i j) :
      ∀ r r0 : Aeneas.Std.I64,
        Aegis.MinTimeToReach.min_time_to_reach A = Aeneas.Std.Result.ok r →
        Aegis.MinTimeToReach.min_time_to_reach A0 = Aeneas.Std.Result.ok r0 →
        r.val = max (d + 1) r0.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (A A0 : Grid) (n m : Nat) (d : Int) (hA : IsValidGrid A n m)
        (hd : d = entry A (n - 1) (m - 1)) (hA0 : IsValidGrid A0 n m)
        (htarget : entry A0 (n - 1) (m - 1) = 0)
        (heq : ∀ i j, i < n → j < m → (i, j) ≠ (n - 1, m - 1) → entry A0 i j = entry A i j), ∀ r r0 : Aeneas.Std.I64,
          Aegis.MinTimeToReach.min_time_to_reach A = Aeneas.Std.Result.ok r →
          Aegis.MinTimeToReach.min_time_to_reach A0 = Aeneas.Std.Result.ok r0 →
          r.val = max (d + 1) r0.val) := by
    sorry

  /-- The function returns a result r and r = max(moveTime[1][1] + 1, min(moveTime[0][1], moveTime[1][0]) + 2).
    Preconditions: Let n = len(moveTime) and m = len(moveTime[0]). The input is valid: n = 2, m = 2, every row has length 2, and 0 <= moveTime[i][j] <= 10^9 for all i,j. -/
  theorem spec_13 (g : Grid) (h : IsValidGrid g 2 2) :
      ∃ r : Aeneas.Std.I64,
        Aegis.MinTimeToReach.min_time_to_reach g = Aeneas.Std.Result.ok r ∧
        r.val = max (entry g 1 1 + 1) (min (entry g 0 1) (entry g 1 0) + 2) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (g : Grid) (h : IsValidGrid g 2 2), ∃ r : Aeneas.Std.I64,
          Aegis.MinTimeToReach.min_time_to_reach g = Aeneas.Std.Result.ok r ∧
          r.val = max (entry g 1 1 + 1) (min (entry g 0 1) (entry g 1 0) + 2)) := by
    sorry

  /-- The function returns a result r and r = c + n + m - 2.
    Preconditions: Let n = len(moveTime) and m = len(moveTime[0]). The input is valid: 2 <= n <= 50, every row of moveTime has length m, 2 <= m <= 50, and 0 <= moveTime[i][j] <= 10^9 for all 0 <= i < n and 0 <= j < m. Let c be an integer with 0 <= c <= 10^9 such that moveTime[i][j] = c for every (i,j) with (i,j) != (0,0). -/
  theorem spec_14 (g : Grid) (n m : Nat) (c : Int) (h : IsValidGrid g n m)
      (hc0 : 0 ≤ c) (hc1 : c ≤ 1000000000)
      (hconst : ∀ i j, i < n → j < m → (i, j) ≠ (0, 0) → entry g i j = c) :
      ∃ r : Aeneas.Std.I64,
        Aegis.MinTimeToReach.min_time_to_reach g = Aeneas.Std.Result.ok r ∧
        r.val = c + (n : Int) + (m : Int) - 2 := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (g : Grid) (n m : Nat) (c : Int) (h : IsValidGrid g n m)
        (hc0 : 0 ≤ c) (hc1 : c ≤ 1000000000)
        (hconst : ∀ i j, i < n → j < m → (i, j) ≠ (0, 0) → entry g i j = c), ∃ r : Aeneas.Std.I64,
          Aegis.MinTimeToReach.min_time_to_reach g = Aeneas.Std.Result.ok r ∧
          r.val = c + (n : Int) + (m : Int) - 2) := by
    sorry

  end AegisSpec.MinTimeToReach
