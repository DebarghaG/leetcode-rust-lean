import Aegis.MaxPossibleScore.Code.Funs

/-!
# Specifications of `Aegis.MaxPossibleScore.max_possible_score`

LeetCode problem `maximize-score-of-numbers-in-ranges`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaxPossibleScore

  def contents (start : Slice Std.I64) : List ℤ := start.val.map (fun v => v.val)

  def pairSet (n : ℕ) : Finset (Fin n × Fin n) := Finset.univ.filter (fun p => p.1 < p.2)

  theorem pairSet_nonempty {n : ℕ} (h : 2 ≤ n) : (pairSet n).Nonempty := by
    refine ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), ?_⟩
    simp [pairSet]

  def Score {n : ℕ} (x : Fin n → ℤ) : ℤ :=
    if h : 2 ≤ n then (pairSet n).inf' (pairSet_nonempty h) (fun p => |x p.1 - x p.2|) else 0

  def minEntry (start : Slice Std.I64) : ℤ :=
    if h : 0 < start.val.length then
      letI : Nonempty (Fin start.val.length) := Fin.pos_iff_nonempty.mp h
      (Finset.univ : Finset (Fin start.val.length)).inf' Finset.univ_nonempty
        (fun i => (start.val.get i).val)
    else 0

  def maxEntry (start : Slice Std.I64) : ℤ :=
    if h : 0 < start.val.length then
      letI : Nonempty (Fin start.val.length) := Fin.pos_iff_nonempty.mp h
      (Finset.univ : Finset (Fin start.val.length)).sup' Finset.univ_nonempty
        (fun i => (start.val.get i).val)
    else 0

  def Valid (start : Slice Std.I64) (d : ℤ) (x : Fin start.val.length → ℤ) : Prop :=
    ∀ i : Fin start.val.length, (start.val.get i).val ≤ x i ∧ x i ≤ (start.val.get i).val + d

  def IsMaxScore (start : Slice Std.I64) (d : ℤ) (M : ℤ) : Prop :=
    (∃ x : Fin start.val.length → ℤ, Valid start d x ∧ Score x = M) ∧
      ∀ x : Fin start.val.length → ℤ, Valid start d x → Score x ≤ M

  def IsShift (start start' : Slice Std.I64) (c : ℤ) : Prop :=
    ∃ h : start'.val.length = start.val.length,
      ∀ i : Fin start.val.length, (start'.val.get (h ▸ i)).val = (start.val.get i).val + c

  /-- For a tuple of integers x_0,...,x_{n-1}, call it valid if start[i] <= x_i <= start[i] + d for every i with 0 <= i < n. For a valid tuple define score(x) = min over all pairs 0 <= i < j < n of |x_i - x_j|. Let M be the maximum of score(x) over all valid tuples. Whenever max_possible_score(start,d) returns a result r, r = M.
    Preconditions: Let n = len(start). The parameters satisfy 2 <= n <= 10^5, 0 <= d <= 10^9, and for every i with 0 <= i < n, 0 <= start[i] and start[i] + d <= 2^63 - 1, where start[i] + d is the mathematical sum (not wrapped). -/
  theorem spec_1 (start : Slice Std.I64) (d : Std.I64)
      (hn2 : 2 ≤ start.val.length) (hn : start.val.length ≤ 10 ^ 5)
      (hd0 : 0 ≤ d.val) (hd : d.val ≤ 10 ^ 9)
      (hlo : ∀ i : Fin start.val.length, 0 ≤ (start.val.get i).val)
      (hhi : ∀ i : Fin start.val.length, (start.val.get i).val + d.val ≤ (2 : ℤ) ^ 63 - 1)
      (r : Std.I64) (hr : Aegis.MaxPossibleScore.max_possible_score start d = ok r) :
      IsMaxScore start d.val r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (start : Slice Std.I64) (d : Std.I64)
        (hn2 : 2 ≤ start.val.length) (hn : start.val.length ≤ 10 ^ 5)
        (hd0 : 0 ≤ d.val) (hd : d.val ≤ 10 ^ 9)
        (hlo : ∀ i : Fin start.val.length, 0 ≤ (start.val.get i).val)
        (hhi : ∀ i : Fin start.val.length, (start.val.get i).val + d.val ≤ (2 : ℤ) ^ 63 - 1)
        (r : Std.I64) (hr : Aegis.MaxPossibleScore.max_possible_score start d = ok r), IsMaxScore start d.val r.val) := by
    sorry

  /-- The call max_possible_score(start,d) returns a result r; it does not fail, overflow, go out of bounds, or panic.
    Preconditions: Let n = len(start). The parameters satisfy 2 <= n <= 10^5, 0 <= d <= 10^9, and 0 <= start[i] <= 10^12 for every i with 0 <= i < n. -/
  theorem spec_2 (start : Slice Std.I64) (d : Std.I64)
      (hn2 : 2 ≤ start.val.length) (hn : start.val.length ≤ 10 ^ 5)
      (hd0 : 0 ≤ d.val) (hd : d.val ≤ 10 ^ 9)
      (hlo : ∀ i : Fin start.val.length, 0 ≤ (start.val.get i).val)
      (hhi : ∀ i : Fin start.val.length, (start.val.get i).val ≤ 10 ^ 12) :
      ∃ r : Std.I64, Aegis.MaxPossibleScore.max_possible_score start d = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (start : Slice Std.I64) (d : Std.I64)
        (hn2 : 2 ≤ start.val.length) (hn : start.val.length ≤ 10 ^ 5)
        (hd0 : 0 ≤ d.val) (hd : d.val ≤ 10 ^ 9)
        (hlo : ∀ i : Fin start.val.length, 0 ≤ (start.val.get i).val)
        (hhi : ∀ i : Fin start.val.length, (start.val.get i).val ≤ 10 ^ 12), ∃ r : Std.I64, Aegis.MaxPossibleScore.max_possible_score start d = ok r) := by
    sorry

  /-- Whenever max_possible_score(start,d) returns a result r, r >= min over all pairs 0 <= i < j < n of |start[i] - start[j]|.
    Preconditions: Let n = len(start). The parameters satisfy 2 <= n <= 10^5, 0 <= d <= 10^9, and for every i with 0 <= i < n, 0 <= start[i] and start[i] + d <= 2^63 - 1, where start[i] + d is the mathematical sum (not wrapped). -/
  theorem spec_3 (start : Slice Std.I64) (d : Std.I64)
      (hn2 : 2 ≤ start.val.length) (hn : start.val.length ≤ 10 ^ 5)
      (hd0 : 0 ≤ d.val) (hd : d.val ≤ 10 ^ 9)
      (hlo : ∀ i : Fin start.val.length, 0 ≤ (start.val.get i).val)
      (hhi : ∀ i : Fin start.val.length, (start.val.get i).val + d.val ≤ (2 : ℤ) ^ 63 - 1)
      (r : Std.I64) (hr : Aegis.MaxPossibleScore.max_possible_score start d = ok r) :
      Score (n := start.val.length) (fun i => (start.val.get i).val) ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (start : Slice Std.I64) (d : Std.I64)
        (hn2 : 2 ≤ start.val.length) (hn : start.val.length ≤ 10 ^ 5)
        (hd0 : 0 ≤ d.val) (hd : d.val ≤ 10 ^ 9)
        (hlo : ∀ i : Fin start.val.length, 0 ≤ (start.val.get i).val)
        (hhi : ∀ i : Fin start.val.length, (start.val.get i).val + d.val ≤ (2 : ℤ) ^ 63 - 1)
        (r : Std.I64) (hr : Aegis.MaxPossibleScore.max_possible_score start d = ok r), Score (n := start.val.length) (fun i => (start.val.get i).val) ≤ r.val) := by
    sorry

  /-- Let L = min_{0 <= i < n} start[i] and U = max_{0 <= i < n} (start[i] + d). Whenever max_possible_score(start,d) returns a result r, r <= floor((U - L) / (n - 1)).
    Preconditions: Let n = len(start). The parameters satisfy 2 <= n <= 10^5, 0 <= d <= 10^9, and for every i with 0 <= i < n, 0 <= start[i] and start[i] + d <= 2^63 - 1, where start[i] + d is the mathematical sum (not wrapped). -/
  theorem spec_4 (start : Slice Std.I64) (d : Std.I64)
      (hn2 : 2 ≤ start.val.length) (hn : start.val.length ≤ 10 ^ 5)
      (hd0 : 0 ≤ d.val) (hd : d.val ≤ 10 ^ 9)
      (hlo : ∀ i : Fin start.val.length, 0 ≤ (start.val.get i).val)
      (hhi : ∀ i : Fin start.val.length, (start.val.get i).val + d.val ≤ (2 : ℤ) ^ 63 - 1)
      (r : Std.I64) (hr : Aegis.MaxPossibleScore.max_possible_score start d = ok r) :
      r.val ≤ (maxEntry start + d.val - minEntry start) / ((start.val.length : ℤ) - 1) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (start : Slice Std.I64) (d : Std.I64)
        (hn2 : 2 ≤ start.val.length) (hn : start.val.length ≤ 10 ^ 5)
        (hd0 : 0 ≤ d.val) (hd : d.val ≤ 10 ^ 9)
        (hlo : ∀ i : Fin start.val.length, 0 ≤ (start.val.get i).val)
        (hhi : ∀ i : Fin start.val.length, (start.val.get i).val + d.val ≤ (2 : ℤ) ^ 63 - 1)
        (r : Std.I64) (hr : Aegis.MaxPossibleScore.max_possible_score start d = ok r), r.val ≤ (maxEntry start + d.val - minEntry start) / ((start.val.length : ℤ) - 1)) := by
    sorry

  /-- Whenever max_possible_score(start,d) returns a result r, r = floor(d / (n - 1)).
    Preconditions: Let n = len(start). The parameters satisfy 2 <= n <= 10^5, 0 <= d <= 10^9, and for every i with 0 <= i < n, 0 <= start[i] and start[i] + d <= 2^63 - 1. Additionally, there exists an integer c such that start[i] = c for every i with 0 <= i < n. -/
  theorem spec_5 (start : Slice Std.I64) (d : Std.I64) (c : ℤ)
      (hn2 : 2 ≤ start.val.length) (hn : start.val.length ≤ 10 ^ 5)
      (hd0 : 0 ≤ d.val) (hd : d.val ≤ 10 ^ 9)
      (hlo : ∀ i : Fin start.val.length, 0 ≤ (start.val.get i).val)
      (hhi : ∀ i : Fin start.val.length, (start.val.get i).val + d.val ≤ (2 : ℤ) ^ 63 - 1)
      (hc : ∀ i : Fin start.val.length, (start.val.get i).val = c)
      (r : Std.I64) (hr : Aegis.MaxPossibleScore.max_possible_score start d = ok r) :
      r.val = d.val / ((start.val.length : ℤ) - 1) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (start : Slice Std.I64) (d : Std.I64) (c : ℤ)
        (hn2 : 2 ≤ start.val.length) (hn : start.val.length ≤ 10 ^ 5)
        (hd0 : 0 ≤ d.val) (hd : d.val ≤ 10 ^ 9)
        (hlo : ∀ i : Fin start.val.length, 0 ≤ (start.val.get i).val)
        (hhi : ∀ i : Fin start.val.length, (start.val.get i).val + d.val ≤ (2 : ℤ) ^ 63 - 1)
        (hc : ∀ i : Fin start.val.length, (start.val.get i).val = c)
        (r : Std.I64) (hr : Aegis.MaxPossibleScore.max_possible_score start d = ok r), r.val = d.val / ((start.val.length : ℤ) - 1)) := by
    sorry

  /-- Whenever max_possible_score(start,d) returns a result r, r = max( |start[0] - (start[1] + d)|, |(start[0] + d) - start[1]| ).
    Preconditions: Let n = len(start). The parameters satisfy n = 2, 0 <= d <= 10^9, and for every i with 0 <= i < n, 0 <= start[i] and start[i] + d <= 2^63 - 1. -/
  theorem spec_6 (start : Slice Std.I64) (d : Std.I64)
      (hn : start.val.length = 2)
      (hd0 : 0 ≤ d.val) (hd : d.val ≤ 10 ^ 9)
      (hlo : ∀ i : Fin start.val.length, 0 ≤ (start.val.get i).val)
      (hhi : ∀ i : Fin start.val.length, (start.val.get i).val + d.val ≤ (2 : ℤ) ^ 63 - 1)
      (r : Std.I64) (hr : Aegis.MaxPossibleScore.max_possible_score start d = ok r) :
      r.val = max
        |(start.val.get ⟨0, by omega⟩).val - ((start.val.get ⟨1, by omega⟩).val + d.val)|
        |((start.val.get ⟨0, by omega⟩).val + d.val) - (start.val.get ⟨1, by omega⟩).val| := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (start : Slice Std.I64) (d : Std.I64)
        (hn : start.val.length = 2)
        (hd0 : 0 ≤ d.val) (hd : d.val ≤ 10 ^ 9)
        (hlo : ∀ i : Fin start.val.length, 0 ≤ (start.val.get i).val)
        (hhi : ∀ i : Fin start.val.length, (start.val.get i).val + d.val ≤ (2 : ℤ) ^ 63 - 1)
        (r : Std.I64) (hr : Aegis.MaxPossibleScore.max_possible_score start d = ok r), r.val = max
          |(start.val.get ⟨0, by omega⟩).val - ((start.val.get ⟨1, by omega⟩).val + d.val)|
          |((start.val.get ⟨0, by omega⟩).val + d.val) - (start.val.get ⟨1, by omega⟩).val|) := by
    sorry

  /-- Whenever max_possible_score(start,d) returns a result r, r = min over all pairs 0 <= i < j < n of |start[i] - start[j]|.
    Preconditions: Let n = len(start). The parameters satisfy 2 <= n <= 10^5, 0 <= start[i] and start[i] + 0 <= 2^63 - 1 for every i, and d = 0. -/
  theorem spec_7 (start : Slice Std.I64) (d : Std.I64)
      (hn2 : 2 ≤ start.val.length) (hn : start.val.length ≤ 10 ^ 5)
      (hd : d.val = 0)
      (hlo : ∀ i : Fin start.val.length, 0 ≤ (start.val.get i).val)
      (hhi : ∀ i : Fin start.val.length, (start.val.get i).val + 0 ≤ (2 : ℤ) ^ 63 - 1)
      (r : Std.I64) (hr : Aegis.MaxPossibleScore.max_possible_score start d = ok r) :
      r.val = Score (n := start.val.length) (fun i => (start.val.get i).val) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (start : Slice Std.I64) (d : Std.I64)
        (hn2 : 2 ≤ start.val.length) (hn : start.val.length ≤ 10 ^ 5)
        (hd : d.val = 0)
        (hlo : ∀ i : Fin start.val.length, 0 ≤ (start.val.get i).val)
        (hhi : ∀ i : Fin start.val.length, (start.val.get i).val + 0 ≤ (2 : ℤ) ^ 63 - 1)
        (r : Std.I64) (hr : Aegis.MaxPossibleScore.max_possible_score start d = ok r), r.val = Score (n := start.val.length) (fun i => (start.val.get i).val)) := by
    sorry

  /-- If max_possible_score(start,d1) returns r1 and max_possible_score(start,d2) returns r2, then r1 <= r2.
    Preconditions: Let n = len(start). The parameters satisfy 2 <= n <= 10^5, 0 <= start[i] for every i with 0 <= i < n, 0 <= d1 <= d2 <= 10^9, and start[i] + d2 <= 2^63 - 1 for every i. -/
  theorem spec_8 (start : Slice Std.I64) (d1 d2 : Std.I64)
      (hn2 : 2 ≤ start.val.length) (hn : start.val.length ≤ 10 ^ 5)
      (hlo : ∀ i : Fin start.val.length, 0 ≤ (start.val.get i).val)
      (hd10 : 0 ≤ d1.val) (hd12 : d1.val ≤ d2.val) (hd2 : d2.val ≤ 10 ^ 9)
      (hhi : ∀ i : Fin start.val.length, (start.val.get i).val + d2.val ≤ (2 : ℤ) ^ 63 - 1)
      (r1 r2 : Std.I64)
      (hr1 : Aegis.MaxPossibleScore.max_possible_score start d1 = ok r1)
      (hr2 : Aegis.MaxPossibleScore.max_possible_score start d2 = ok r2) :
      r1.val ≤ r2.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (start : Slice Std.I64) (d1 d2 : Std.I64)
        (hn2 : 2 ≤ start.val.length) (hn : start.val.length ≤ 10 ^ 5)
        (hlo : ∀ i : Fin start.val.length, 0 ≤ (start.val.get i).val)
        (hd10 : 0 ≤ d1.val) (hd12 : d1.val ≤ d2.val) (hd2 : d2.val ≤ 10 ^ 9)
        (hhi : ∀ i : Fin start.val.length, (start.val.get i).val + d2.val ≤ (2 : ℤ) ^ 63 - 1)
        (r1 r2 : Std.I64)
        (hr1 : Aegis.MaxPossibleScore.max_possible_score start d1 = ok r1)
        (hr2 : Aegis.MaxPossibleScore.max_possible_score start d2 = ok r2), r1.val ≤ r2.val) := by
    sorry

  /-- If max_possible_score(start,d) returns r and max_possible_score(start',d) returns r', then r = r'.
    Preconditions: Let n = len(start). The parameters satisfy 2 <= n <= 10^5, 0 <= d <= 10^9, and for every i with 0 <= i < n, 0 <= start[i] and start[i] + d <= 2^63 - 1. Let c be an integer such that for every i, 0 <= start[i] + c and start[i] + c + d <= 2^63 - 1. Define start'[i] = start[i] + c. -/
  theorem spec_9 (start start' : Slice Std.I64) (d : Std.I64) (c : ℤ)
      (hn2 : 2 ≤ start.val.length) (hn : start.val.length ≤ 10 ^ 5)
      (hd0 : 0 ≤ d.val) (hd : d.val ≤ 10 ^ 9)
      (hlo : ∀ i : Fin start.val.length, 0 ≤ (start.val.get i).val)
      (hhi : ∀ i : Fin start.val.length, (start.val.get i).val + d.val ≤ (2 : ℤ) ^ 63 - 1)
      (hlo' : ∀ i : Fin start.val.length, 0 ≤ (start.val.get i).val + c)
      (hhi' : ∀ i : Fin start.val.length, (start.val.get i).val + c + d.val ≤ (2 : ℤ) ^ 63 - 1)
      (hshift : IsShift start start' c)
      (r r' : Std.I64)
      (hr : Aegis.MaxPossibleScore.max_possible_score start d = ok r)
      (hr' : Aegis.MaxPossibleScore.max_possible_score start' d = ok r') :
      r.val = r'.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (start start' : Slice Std.I64) (d : Std.I64) (c : ℤ)
        (hn2 : 2 ≤ start.val.length) (hn : start.val.length ≤ 10 ^ 5)
        (hd0 : 0 ≤ d.val) (hd : d.val ≤ 10 ^ 9)
        (hlo : ∀ i : Fin start.val.length, 0 ≤ (start.val.get i).val)
        (hhi : ∀ i : Fin start.val.length, (start.val.get i).val + d.val ≤ (2 : ℤ) ^ 63 - 1)
        (hlo' : ∀ i : Fin start.val.length, 0 ≤ (start.val.get i).val + c)
        (hhi' : ∀ i : Fin start.val.length, (start.val.get i).val + c + d.val ≤ (2 : ℤ) ^ 63 - 1)
        (hshift : IsShift start start' c)
        (r r' : Std.I64)
        (hr : Aegis.MaxPossibleScore.max_possible_score start d = ok r)
        (hr' : Aegis.MaxPossibleScore.max_possible_score start' d = ok r'), r.val = r'.val) := by
    sorry

  /-- Whenever max_possible_score(start,d) returns a result r, there exist integers x_0,...,x_{n-1} such that start[i] <= x_i <= start[i] + d for every i with 0 <= i < n, and |x_i - x_j| >= r for every i,j with 0 <= i < j < n.
    Preconditions: Let n = len(start). The parameters satisfy 2 <= n <= 10^5, 0 <= d <= 10^9, and for every i with 0 <= i < n, 0 <= start[i] and start[i] + d <= 2^63 - 1, where start[i] + d is the mathematical sum (not wrapped). -/
  theorem spec_10 (start : Slice Std.I64) (d : Std.I64)
      (hn2 : 2 ≤ start.val.length) (hn : start.val.length ≤ 10 ^ 5)
      (hd0 : 0 ≤ d.val) (hd : d.val ≤ 10 ^ 9)
      (hlo : ∀ i : Fin start.val.length, 0 ≤ (start.val.get i).val)
      (hhi : ∀ i : Fin start.val.length, (start.val.get i).val + d.val ≤ (2 : ℤ) ^ 63 - 1)
      (r : Std.I64) (hr : Aegis.MaxPossibleScore.max_possible_score start d = ok r) :
      ∃ x : Fin start.val.length → ℤ,
        Valid start d.val x ∧
          ∀ i j : Fin start.val.length, i < j → r.val ≤ |x i - x j| := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (start : Slice Std.I64) (d : Std.I64)
        (hn2 : 2 ≤ start.val.length) (hn : start.val.length ≤ 10 ^ 5)
        (hd0 : 0 ≤ d.val) (hd : d.val ≤ 10 ^ 9)
        (hlo : ∀ i : Fin start.val.length, 0 ≤ (start.val.get i).val)
        (hhi : ∀ i : Fin start.val.length, (start.val.get i).val + d.val ≤ (2 : ℤ) ^ 63 - 1)
        (r : Std.I64) (hr : Aegis.MaxPossibleScore.max_possible_score start d = ok r), ∃ x : Fin start.val.length → ℤ,
          Valid start d.val x ∧
            ∀ i j : Fin start.val.length, i < j → r.val ≤ |x i - x j|) := by
    sorry

  /-- Whenever max_possible_score(start,d) returns a result r, for every choice of integers x_0,...,x_{n-1} with start[i] <= x_i <= start[i] + d for all i with 0 <= i < n, there exist i,j with 0 <= i < j < n and |x_i - x_j| <= r.
    Preconditions: Let n = len(start). The parameters satisfy 2 <= n <= 10^5, 0 <= d <= 10^9, and for every i with 0 <= i < n, 0 <= start[i] and start[i] + d <= 2^63 - 1, where start[i] + d is the mathematical sum (not wrapped). -/
  theorem spec_11 (start : Slice Std.I64) (d : Std.I64)
      (hn2 : 2 ≤ start.val.length) (hn : start.val.length ≤ 10 ^ 5)
      (hd0 : 0 ≤ d.val) (hd : d.val ≤ 10 ^ 9)
      (hlo : ∀ i : Fin start.val.length, 0 ≤ (start.val.get i).val)
      (hhi : ∀ i : Fin start.val.length, (start.val.get i).val + d.val ≤ (2 : ℤ) ^ 63 - 1)
      (r : Std.I64) (hr : Aegis.MaxPossibleScore.max_possible_score start d = ok r) :
      ∀ x : Fin start.val.length → ℤ, Valid start d.val x →
        ∃ i j : Fin start.val.length, i < j ∧ |x i - x j| ≤ r.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (start : Slice Std.I64) (d : Std.I64)
        (hn2 : 2 ≤ start.val.length) (hn : start.val.length ≤ 10 ^ 5)
        (hd0 : 0 ≤ d.val) (hd : d.val ≤ 10 ^ 9)
        (hlo : ∀ i : Fin start.val.length, 0 ≤ (start.val.get i).val)
        (hhi : ∀ i : Fin start.val.length, (start.val.get i).val + d.val ≤ (2 : ℤ) ^ 63 - 1)
        (r : Std.I64) (hr : Aegis.MaxPossibleScore.max_possible_score start d = ok r), ∀ x : Fin start.val.length → ℤ, Valid start d.val x →
          ∃ i j : Fin start.val.length, i < j ∧ |x i - x j| ≤ r.val) := by
    sorry

  end AegisSpec.MaxPossibleScore
