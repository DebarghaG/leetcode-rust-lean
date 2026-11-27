import Aegis.ButtonWithLongestTime.Code.Funs

/-!
# Specifications of `Aegis.ButtonWithLongestTime.button_with_longest_time`

LeetCode problem `button-with-longest-push-time`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.ButtonWithLongestTime

  def evRows (events : Slice (alloc.vec.Vec Std.I64)) : List (List ℤ) :=
    events.val.map (fun v => v.val.map (fun x => x.val))

  def rowAt (rows : List (List ℤ)) (i : ℕ) : List ℤ :=
    rows.getD i []

  def evIdx (rows : List (List ℤ)) (i : ℕ) : ℤ :=
    (rowAt rows i).getD 0 0

  def evTime (rows : List (List ℤ)) (i : ℕ) : ℤ :=
    (rowAt rows i).getD 1 0

  def gap (rows : List (List ℤ)) (i : ℕ) : ℤ :=
    if i = 0 then evTime rows 0 else evTime rows i - evTime rows (i - 1)

  def maxOver (rows : List (List ℤ)) (is : List ℕ) : ℤ :=
    match is with
    | [] => 0
    | i :: is' => is'.foldl (fun acc j => max acc (gap rows j)) (gap rows i)

  def score (rows : List (List ℤ)) (b : ℤ) : ℤ :=
    maxOver rows ((List.range rows.length).filter (fun i => decide (evIdx rows i = b)))

  def maxGap (rows : List (List ℤ)) : ℤ :=
    maxOver rows (List.range rows.length)

  def Occurs (rows : List (List ℤ)) (b : ℤ) : Prop :=
    ∃ j, j < rows.length ∧ evIdx rows j = b

  def IsSmallestMaxScore (rows : List (List ℤ)) (r : ℤ) : Prop :=
    Occurs rows r ∧
    (∀ b, Occurs rows b → score rows b ≤ score rows r) ∧
    (∀ b, Occurs rows b → b < r → score rows b < score rows r)

  /-- The function returns a result r and the following hold: (1) r = idx_k for at least one k with 0 <= k < n. (2) For every button b that occurs in events, score(r) >= score(b). (3) For every button b that occurs in events with b < r, score(b) < score(r). Equivalently, r is the smallest index among all occurring buttons whose score is maximum.
    Preconditions: Let n = len(events). Assume 1 <= n <= 1000. For every i with 0 <= i < n, len(events[i]) = 2; write idx_i = events[i][0] and t_i = events[i][1], and assume 1 <= idx_i <= 100000 and 1 <= t_i <= 100000. Assume the events are sorted by time: for every i with 0 <= i+1 < n, t_i <= t_{i+1}. Define d_0 = t_0 and, for 1 <= i < n, d_i = t_i - t_{i-1}. For any button value b that occurs in events (i.e., b = idx_j for some j with 0 <= j < n), define score(b) = max{ d_i | 0 <= i < n and idx_i = b }. -/
  theorem spec_1 (events : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
      (hn : n = (evRows events).length) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
      (hlen : ∀ i, i < n → (rowAt (evRows events) i).length = 2)
      (hidx1 : ∀ i, i < n → 1 ≤ evIdx (evRows events) i)
      (hidx2 : ∀ i, i < n → evIdx (evRows events) i ≤ 100000)
      (htime1 : ∀ i, i < n → 1 ≤ evTime (evRows events) i)
      (htime2 : ∀ i, i < n → evTime (evRows events) i ≤ 100000)
      (hsorted : ∀ i, i + 1 < n → evTime (evRows events) i ≤ evTime (evRows events) (i + 1)) :
      ∃ r, Aegis.ButtonWithLongestTime.button_with_longest_time events = ok r ∧
        IsSmallestMaxScore (evRows events) r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (events : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
        (hn : n = (evRows events).length) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
        (hlen : ∀ i, i < n → (rowAt (evRows events) i).length = 2)
        (hidx1 : ∀ i, i < n → 1 ≤ evIdx (evRows events) i)
        (hidx2 : ∀ i, i < n → evIdx (evRows events) i ≤ 100000)
        (htime1 : ∀ i, i < n → 1 ≤ evTime (evRows events) i)
        (htime2 : ∀ i, i < n → evTime (evRows events) i ≤ 100000)
        (hsorted : ∀ i, i + 1 < n → evTime (evRows events) i ≤ evTime (evRows events) (i + 1)), ∃ r, Aegis.ButtonWithLongestTime.button_with_longest_time events = ok r ∧
          IsSmallestMaxScore (evRows events) r.val) := by
    sorry

  /-- The function returns a result r; it does not fail, panic, or overflow.
    Preconditions: Let n = len(events). Assume 1 <= n <= 1000. For every i with 0 <= i < n, len(events[i]) = 2; write idx_i = events[i][0] and t_i = events[i][1], and assume 1 <= idx_i <= 100000 and 1 <= t_i <= 100000. Assume the events are sorted by time: for every i with 0 <= i+1 < n, t_i <= t_{i+1}. Define d_0 = t_0 and, for 1 <= i < n, d_i = t_i - t_{i-1}. For any button value b that occurs in events, define score(b) = max{ d_i | 0 <= i < n and idx_i = b }. -/
  theorem spec_2 (events : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
      (hn : n = (evRows events).length) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
      (hlen : ∀ i, i < n → (rowAt (evRows events) i).length = 2)
      (hidx1 : ∀ i, i < n → 1 ≤ evIdx (evRows events) i)
      (hidx2 : ∀ i, i < n → evIdx (evRows events) i ≤ 100000)
      (htime1 : ∀ i, i < n → 1 ≤ evTime (evRows events) i)
      (htime2 : ∀ i, i < n → evTime (evRows events) i ≤ 100000)
      (hsorted : ∀ i, i + 1 < n → evTime (evRows events) i ≤ evTime (evRows events) (i + 1)) :
      ∃ r, Aegis.ButtonWithLongestTime.button_with_longest_time events = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (events : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
        (hn : n = (evRows events).length) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
        (hlen : ∀ i, i < n → (rowAt (evRows events) i).length = 2)
        (hidx1 : ∀ i, i < n → 1 ≤ evIdx (evRows events) i)
        (hidx2 : ∀ i, i < n → evIdx (evRows events) i ≤ 100000)
        (htime1 : ∀ i, i < n → 1 ≤ evTime (evRows events) i)
        (htime2 : ∀ i, i < n → evTime (evRows events) i ≤ 100000)
        (hsorted : ∀ i, i + 1 < n → evTime (evRows events) i ≤ evTime (evRows events) (i + 1)), ∃ r, Aegis.ButtonWithLongestTime.button_with_longest_time events = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 1 <= r <= 100000.
    Preconditions: Let n = len(events). Assume 1 <= n <= 1000. For every i with 0 <= i < n, len(events[i]) = 2; write idx_i = events[i][0] and t_i = events[i][1], and assume 1 <= idx_i <= 100000 and 1 <= t_i <= 100000. Assume the events are sorted by time: for every i with 0 <= i+1 < n, t_i <= t_{i+1}. Define d_0 = t_0 and, for 1 <= i < n, d_i = t_i - t_{i-1}. For any button value b that occurs in events, define score(b) = max{ d_i | 0 <= i < n and idx_i = b }. -/
  theorem spec_3 (events : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
      (hn : n = (evRows events).length) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
      (hlen : ∀ i, i < n → (rowAt (evRows events) i).length = 2)
      (hidx1 : ∀ i, i < n → 1 ≤ evIdx (evRows events) i)
      (hidx2 : ∀ i, i < n → evIdx (evRows events) i ≤ 100000)
      (htime1 : ∀ i, i < n → 1 ≤ evTime (evRows events) i)
      (htime2 : ∀ i, i < n → evTime (evRows events) i ≤ 100000)
      (hsorted : ∀ i, i + 1 < n → evTime (evRows events) i ≤ evTime (evRows events) (i + 1)) :
      ∀ r, Aegis.ButtonWithLongestTime.button_with_longest_time events = ok r →
        1 ≤ r.val ∧ r.val ≤ 100000 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (events : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
        (hn : n = (evRows events).length) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
        (hlen : ∀ i, i < n → (rowAt (evRows events) i).length = 2)
        (hidx1 : ∀ i, i < n → 1 ≤ evIdx (evRows events) i)
        (hidx2 : ∀ i, i < n → evIdx (evRows events) i ≤ 100000)
        (htime1 : ∀ i, i < n → 1 ≤ evTime (evRows events) i)
        (htime2 : ∀ i, i < n → evTime (evRows events) i ≤ 100000)
        (hsorted : ∀ i, i + 1 < n → evTime (evRows events) i ≤ evTime (evRows events) (i + 1)), ∀ r, Aegis.ButtonWithLongestTime.button_with_longest_time events = ok r →
          1 ≤ r.val ∧ r.val ≤ 100000) := by
    sorry

  /-- Whenever the function returns a result r, there exists an event position k with 0 <= k < n such that r = idx_k.
    Preconditions: Let n = len(events). Assume 1 <= n <= 1000. For every i with 0 <= i < n, len(events[i]) = 2; write idx_i = events[i][0] and t_i = events[i][1], and assume 1 <= idx_i <= 100000 and 1 <= t_i <= 100000. Assume the events are sorted by time: for every i with 0 <= i+1 < n, t_i <= t_{i+1}. Define d_0 = t_0 and, for 1 <= i < n, d_i = t_i - t_{i-1}. For any button value b that occurs in events, define score(b) = max{ d_i | 0 <= i < n and idx_i = b }. -/
  theorem spec_4 (events : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
      (hn : n = (evRows events).length) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
      (hlen : ∀ i, i < n → (rowAt (evRows events) i).length = 2)
      (hidx1 : ∀ i, i < n → 1 ≤ evIdx (evRows events) i)
      (hidx2 : ∀ i, i < n → evIdx (evRows events) i ≤ 100000)
      (htime1 : ∀ i, i < n → 1 ≤ evTime (evRows events) i)
      (htime2 : ∀ i, i < n → evTime (evRows events) i ≤ 100000)
      (hsorted : ∀ i, i + 1 < n → evTime (evRows events) i ≤ evTime (evRows events) (i + 1)) :
      ∀ r, Aegis.ButtonWithLongestTime.button_with_longest_time events = ok r →
        ∃ k, k < n ∧ r.val = evIdx (evRows events) k := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (events : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
        (hn : n = (evRows events).length) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
        (hlen : ∀ i, i < n → (rowAt (evRows events) i).length = 2)
        (hidx1 : ∀ i, i < n → 1 ≤ evIdx (evRows events) i)
        (hidx2 : ∀ i, i < n → evIdx (evRows events) i ≤ 100000)
        (htime1 : ∀ i, i < n → 1 ≤ evTime (evRows events) i)
        (htime2 : ∀ i, i < n → evTime (evRows events) i ≤ 100000)
        (hsorted : ∀ i, i + 1 < n → evTime (evRows events) i ≤ evTime (evRows events) (i + 1)), ∀ r, Aegis.ButtonWithLongestTime.button_with_longest_time events = ok r →
          ∃ k, k < n ∧ r.val = evIdx (evRows events) k) := by
    sorry

  /-- Whenever the function returns a result r, r is an occurring button (there exists k with 0 <= k < n and r = idx_k), and for every button b that occurs in events, score(r) >= score(b).
    Preconditions: Let n = len(events). Assume 1 <= n <= 1000. For every i with 0 <= i < n, len(events[i]) = 2; write idx_i = events[i][0] and t_i = events[i][1], and assume 1 <= idx_i <= 100000 and 1 <= t_i <= 100000. Assume the events are sorted by time: for every i with 0 <= i+1 < n, t_i <= t_{i+1}. Define d_0 = t_0 and, for 1 <= i < n, d_i = t_i - t_{i-1}. For any button value b that occurs in events, define score(b) = max{ d_i | 0 <= i < n and idx_i = b }. -/
  theorem spec_5 (events : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
      (hn : n = (evRows events).length) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
      (hlen : ∀ i, i < n → (rowAt (evRows events) i).length = 2)
      (hidx1 : ∀ i, i < n → 1 ≤ evIdx (evRows events) i)
      (hidx2 : ∀ i, i < n → evIdx (evRows events) i ≤ 100000)
      (htime1 : ∀ i, i < n → 1 ≤ evTime (evRows events) i)
      (htime2 : ∀ i, i < n → evTime (evRows events) i ≤ 100000)
      (hsorted : ∀ i, i + 1 < n → evTime (evRows events) i ≤ evTime (evRows events) (i + 1)) :
      ∀ r, Aegis.ButtonWithLongestTime.button_with_longest_time events = ok r →
        Occurs (evRows events) r.val ∧
          ∀ b, Occurs (evRows events) b → score (evRows events) b ≤ score (evRows events) r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (events : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
        (hn : n = (evRows events).length) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
        (hlen : ∀ i, i < n → (rowAt (evRows events) i).length = 2)
        (hidx1 : ∀ i, i < n → 1 ≤ evIdx (evRows events) i)
        (hidx2 : ∀ i, i < n → evIdx (evRows events) i ≤ 100000)
        (htime1 : ∀ i, i < n → 1 ≤ evTime (evRows events) i)
        (htime2 : ∀ i, i < n → evTime (evRows events) i ≤ 100000)
        (hsorted : ∀ i, i + 1 < n → evTime (evRows events) i ≤ evTime (evRows events) (i + 1)), ∀ r, Aegis.ButtonWithLongestTime.button_with_longest_time events = ok r →
          Occurs (evRows events) r.val ∧
            ∀ b, Occurs (evRows events) b → score (evRows events) b ≤ score (evRows events) r.val) := by
    sorry

  /-- Whenever the function returns a result r, r is an occurring button (there exists k with 0 <= k < n and r = idx_k), and for every button b that occurs in events, if b < r then score(b) < score(r).
    Preconditions: Let n = len(events). Assume 1 <= n <= 1000. For every i with 0 <= i < n, len(events[i]) = 2; write idx_i = events[i][0] and t_i = events[i][1], and assume 1 <= idx_i <= 100000 and 1 <= t_i <= 100000. Assume the events are sorted by time: for every i with 0 <= i+1 < n, t_i <= t_{i+1}. Define d_0 = t_0 and, for 1 <= i < n, d_i = t_i - t_{i-1}. For any button value b that occurs in events, define score(b) = max{ d_i | 0 <= i < n and idx_i = b }. -/
  theorem spec_6 (events : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
      (hn : n = (evRows events).length) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
      (hlen : ∀ i, i < n → (rowAt (evRows events) i).length = 2)
      (hidx1 : ∀ i, i < n → 1 ≤ evIdx (evRows events) i)
      (hidx2 : ∀ i, i < n → evIdx (evRows events) i ≤ 100000)
      (htime1 : ∀ i, i < n → 1 ≤ evTime (evRows events) i)
      (htime2 : ∀ i, i < n → evTime (evRows events) i ≤ 100000)
      (hsorted : ∀ i, i + 1 < n → evTime (evRows events) i ≤ evTime (evRows events) (i + 1)) :
      ∀ r, Aegis.ButtonWithLongestTime.button_with_longest_time events = ok r →
        Occurs (evRows events) r.val ∧
          ∀ b, Occurs (evRows events) b → b < r.val → score (evRows events) b < score (evRows events) r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (events : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
        (hn : n = (evRows events).length) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
        (hlen : ∀ i, i < n → (rowAt (evRows events) i).length = 2)
        (hidx1 : ∀ i, i < n → 1 ≤ evIdx (evRows events) i)
        (hidx2 : ∀ i, i < n → evIdx (evRows events) i ≤ 100000)
        (htime1 : ∀ i, i < n → 1 ≤ evTime (evRows events) i)
        (htime2 : ∀ i, i < n → evTime (evRows events) i ≤ 100000)
        (hsorted : ∀ i, i + 1 < n → evTime (evRows events) i ≤ evTime (evRows events) (i + 1)), ∀ r, Aegis.ButtonWithLongestTime.button_with_longest_time events = ok r →
          Occurs (evRows events) r.val ∧
            ∀ b, Occurs (evRows events) b → b < r.val → score (evRows events) b < score (evRows events) r.val) := by
    sorry

  /-- Whenever the function returns a result r, there exists an event position k with 0 <= k < n such that idx_k = r and d_k = max{ d_i | 0 <= i < n }.
    Preconditions: Let n = len(events). Assume 1 <= n <= 1000. For every i with 0 <= i < n, len(events[i]) = 2; write idx_i = events[i][0] and t_i = events[i][1], and assume 1 <= idx_i <= 100000 and 1 <= t_i <= 100000. Assume the events are sorted by time: for every i with 0 <= i+1 < n, t_i <= t_{i+1}. Define d_0 = t_0 and, for 1 <= i < n, d_i = t_i - t_{i-1}. For any button value b that occurs in events, define score(b) = max{ d_i | 0 <= i < n and idx_i = b }. -/
  theorem spec_7 (events : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
      (hn : n = (evRows events).length) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
      (hlen : ∀ i, i < n → (rowAt (evRows events) i).length = 2)
      (hidx1 : ∀ i, i < n → 1 ≤ evIdx (evRows events) i)
      (hidx2 : ∀ i, i < n → evIdx (evRows events) i ≤ 100000)
      (htime1 : ∀ i, i < n → 1 ≤ evTime (evRows events) i)
      (htime2 : ∀ i, i < n → evTime (evRows events) i ≤ 100000)
      (hsorted : ∀ i, i + 1 < n → evTime (evRows events) i ≤ evTime (evRows events) (i + 1)) :
      ∀ r, Aegis.ButtonWithLongestTime.button_with_longest_time events = ok r →
        ∃ k, k < n ∧ evIdx (evRows events) k = r.val ∧ gap (evRows events) k = maxGap (evRows events) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (events : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
        (hn : n = (evRows events).length) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
        (hlen : ∀ i, i < n → (rowAt (evRows events) i).length = 2)
        (hidx1 : ∀ i, i < n → 1 ≤ evIdx (evRows events) i)
        (hidx2 : ∀ i, i < n → evIdx (evRows events) i ≤ 100000)
        (htime1 : ∀ i, i < n → 1 ≤ evTime (evRows events) i)
        (htime2 : ∀ i, i < n → evTime (evRows events) i ≤ 100000)
        (hsorted : ∀ i, i + 1 < n → evTime (evRows events) i ≤ evTime (evRows events) (i + 1)), ∀ r, Aegis.ButtonWithLongestTime.button_with_longest_time events = ok r →
          ∃ k, k < n ∧ evIdx (evRows events) k = r.val ∧ gap (evRows events) k = maxGap (evRows events)) := by
    sorry

  /-- Whenever the function returns a result r, r is an occurring button (there exists k with 0 <= k < n and r = idx_k), and 1 <= score(r) <= 100000.
    Preconditions: Let n = len(events). Assume 1 <= n <= 1000. For every i with 0 <= i < n, len(events[i]) = 2; write idx_i = events[i][0] and t_i = events[i][1], and assume 1 <= idx_i <= 100000 and 1 <= t_i <= 100000. Assume the events are sorted by time: for every i with 0 <= i+1 < n, t_i <= t_{i+1}. Define d_0 = t_0 and, for 1 <= i < n, d_i = t_i - t_{i-1}. For any button value b that occurs in events, define score(b) = max{ d_i | 0 <= i < n and idx_i = b }. -/
  theorem spec_8 (events : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
      (hn : n = (evRows events).length) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
      (hlen : ∀ i, i < n → (rowAt (evRows events) i).length = 2)
      (hidx1 : ∀ i, i < n → 1 ≤ evIdx (evRows events) i)
      (hidx2 : ∀ i, i < n → evIdx (evRows events) i ≤ 100000)
      (htime1 : ∀ i, i < n → 1 ≤ evTime (evRows events) i)
      (htime2 : ∀ i, i < n → evTime (evRows events) i ≤ 100000)
      (hsorted : ∀ i, i + 1 < n → evTime (evRows events) i ≤ evTime (evRows events) (i + 1)) :
      ∀ r, Aegis.ButtonWithLongestTime.button_with_longest_time events = ok r →
        Occurs (evRows events) r.val ∧ 1 ≤ score (evRows events) r.val ∧ score (evRows events) r.val ≤ 100000 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (events : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
        (hn : n = (evRows events).length) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
        (hlen : ∀ i, i < n → (rowAt (evRows events) i).length = 2)
        (hidx1 : ∀ i, i < n → 1 ≤ evIdx (evRows events) i)
        (hidx2 : ∀ i, i < n → evIdx (evRows events) i ≤ 100000)
        (htime1 : ∀ i, i < n → 1 ≤ evTime (evRows events) i)
        (htime2 : ∀ i, i < n → evTime (evRows events) i ≤ 100000)
        (hsorted : ∀ i, i + 1 < n → evTime (evRows events) i ≤ evTime (evRows events) (i + 1)), ∀ r, Aegis.ButtonWithLongestTime.button_with_longest_time events = ok r →
          Occurs (evRows events) r.val ∧ 1 ≤ score (evRows events) r.val ∧ score (evRows events) r.val ≤ 100000) := by
    sorry

  /-- Whenever the function returns a result r, for every positive integer c such that c*t_i <= 100000 for all i with 0 <= i < n, if events' is defined by len(events') = n, idx'_i = idx_i, and t'_i = c*t_i for all i, then r is the smallest index among all occurring buttons with maximum score computed from events'.
    Preconditions: Let n = len(events). Assume 1 <= n <= 1000. For every i with 0 <= i < n, len(events[i]) = 2; write idx_i = events[i][0] and t_i = events[i][1], and assume 1 <= idx_i <= 100000 and 1 <= t_i <= 100000. Assume the events are sorted by time: for every i with 0 <= i+1 < n, t_i <= t_{i+1}. Define d_0 = t_0 and, for 1 <= i < n, d_i = t_i - t_{i-1}. For any button value b that occurs in events, define score(b) = max{ d_i | 0 <= i < n and idx_i = b }. -/
  theorem spec_9 (events : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
      (hn : n = (evRows events).length) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
      (hlen : ∀ i, i < n → (rowAt (evRows events) i).length = 2)
      (hidx1 : ∀ i, i < n → 1 ≤ evIdx (evRows events) i)
      (hidx2 : ∀ i, i < n → evIdx (evRows events) i ≤ 100000)
      (htime1 : ∀ i, i < n → 1 ≤ evTime (evRows events) i)
      (htime2 : ∀ i, i < n → evTime (evRows events) i ≤ 100000)
      (hsorted : ∀ i, i + 1 < n → evTime (evRows events) i ≤ evTime (evRows events) (i + 1)) :
      ∀ r, Aegis.ButtonWithLongestTime.button_with_longest_time events = ok r →
        ∀ c : ℤ, 0 < c → (∀ i, i < n → c * evTime (evRows events) i ≤ 100000) →
          ∀ rows' : List (List ℤ), rows'.length = n →
            (∀ i, i < n → evIdx rows' i = evIdx (evRows events) i) →
            (∀ i, i < n → evTime rows' i = c * evTime (evRows events) i) →
            IsSmallestMaxScore rows' r.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (events : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
        (hn : n = (evRows events).length) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
        (hlen : ∀ i, i < n → (rowAt (evRows events) i).length = 2)
        (hidx1 : ∀ i, i < n → 1 ≤ evIdx (evRows events) i)
        (hidx2 : ∀ i, i < n → evIdx (evRows events) i ≤ 100000)
        (htime1 : ∀ i, i < n → 1 ≤ evTime (evRows events) i)
        (htime2 : ∀ i, i < n → evTime (evRows events) i ≤ 100000)
        (hsorted : ∀ i, i + 1 < n → evTime (evRows events) i ≤ evTime (evRows events) (i + 1)), ∀ r, Aegis.ButtonWithLongestTime.button_with_longest_time events = ok r →
          ∀ c : ℤ, 0 < c → (∀ i, i < n → c * evTime (evRows events) i ≤ 100000) →
            ∀ rows' : List (List ℤ), rows'.length = n →
              (∀ i, i < n → evIdx rows' i = evIdx (evRows events) i) →
              (∀ i, i < n → evTime rows' i = c * evTime (evRows events) i) →
              IsSmallestMaxScore rows' r.val) := by
    sorry

  /-- Whenever the function returns a result r, for every integer C >= 0 such that idx_i + C <= 100000 for all i with 0 <= i < n, if events' is defined by len(events') = n, idx'_i = idx_i + C, and t'_i = t_i for all i, then r + C is the smallest index among all occurring buttons with maximum score computed from events'.
    Preconditions: Let n = len(events). Assume 1 <= n <= 1000. For every i with 0 <= i < n, len(events[i]) = 2; write idx_i = events[i][0] and t_i = events[i][1], and assume 1 <= idx_i <= 100000 and 1 <= t_i <= 100000. Assume the events are sorted by time: for every i with 0 <= i+1 < n, t_i <= t_{i+1}. Define d_0 = t_0 and, for 1 <= i < n, d_i = t_i - t_{i-1}. For any button value b that occurs in events, define score(b) = max{ d_i | 0 <= i < n and idx_i = b }. -/
  theorem spec_10 (events : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
      (hn : n = (evRows events).length) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
      (hlen : ∀ i, i < n → (rowAt (evRows events) i).length = 2)
      (hidx1 : ∀ i, i < n → 1 ≤ evIdx (evRows events) i)
      (hidx2 : ∀ i, i < n → evIdx (evRows events) i ≤ 100000)
      (htime1 : ∀ i, i < n → 1 ≤ evTime (evRows events) i)
      (htime2 : ∀ i, i < n → evTime (evRows events) i ≤ 100000)
      (hsorted : ∀ i, i + 1 < n → evTime (evRows events) i ≤ evTime (evRows events) (i + 1)) :
      ∀ r, Aegis.ButtonWithLongestTime.button_with_longest_time events = ok r →
        ∀ C : ℤ, 0 ≤ C → (∀ i, i < n → evIdx (evRows events) i + C ≤ 100000) →
          ∀ rows' : List (List ℤ), rows'.length = n →
            (∀ i, i < n → evIdx rows' i = evIdx (evRows events) i + C) →
            (∀ i, i < n → evTime rows' i = evTime (evRows events) i) →
            IsSmallestMaxScore rows' (r.val + C) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (events : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
        (hn : n = (evRows events).length) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
        (hlen : ∀ i, i < n → (rowAt (evRows events) i).length = 2)
        (hidx1 : ∀ i, i < n → 1 ≤ evIdx (evRows events) i)
        (hidx2 : ∀ i, i < n → evIdx (evRows events) i ≤ 100000)
        (htime1 : ∀ i, i < n → 1 ≤ evTime (evRows events) i)
        (htime2 : ∀ i, i < n → evTime (evRows events) i ≤ 100000)
        (hsorted : ∀ i, i + 1 < n → evTime (evRows events) i ≤ evTime (evRows events) (i + 1)), ∀ r, Aegis.ButtonWithLongestTime.button_with_longest_time events = ok r →
          ∀ C : ℤ, 0 ≤ C → (∀ i, i < n → evIdx (evRows events) i + C ≤ 100000) →
            ∀ rows' : List (List ℤ), rows'.length = n →
              (∀ i, i < n → evIdx rows' i = evIdx (evRows events) i + C) →
              (∀ i, i < n → evTime rows' i = evTime (evRows events) i) →
              IsSmallestMaxScore rows' (r.val + C)) := by
    sorry

  end AegisSpec.ButtonWithLongestTime
