import Aegis.StrangePrinter.Code.Funs

/-!
# Specifications of `Aegis.StrangePrinter.strange_printer`

LeetCode problem `strange-printer`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.StrangePrinter

  open Aegis.StrangePrinter

  structure Turn where

    l : Nat

    r : Nat

    c : Std.U8

  def Turn.writeFrom (t : Turn) (i : Nat) : List (Option Std.U8) → List (Option Std.U8)
    | [] => []
    | x :: xs =>
      (if t.l ≤ i ∧ i ≤ t.r then some t.c else x) :: Turn.writeFrom t (i + 1) xs

  def Turn.write (t : Turn) (a : List (Option Std.U8)) : List (Option Std.U8) :=
    t.writeFrom 0 a

  def runPlan (plan : List Turn) (n : Nat) : List (Option Std.U8) :=
    plan.foldl (fun a t => t.write a) (List.replicate n none)

  def ValidPlan (s : List Std.U8) (plan : List Turn) : Prop :=
    (∀ t ∈ plan, t.l ≤ t.r ∧ t.r < s.length) ∧ runPlan plan s.length = s.map some

  noncomputable def minTurns (s : List Std.U8) : Nat :=
    sInf {m : Nat | ∃ plan : List Turn, ValidPlan s plan ∧ plan.length = m}

  def IsLowerByte (b : Std.U8) : Prop := 97 ≤ b.val ∧ b.val ≤ 122

  def distinctCount (s : List Std.U8) : Nat := s.dedup.length

  def IsMaximalRun (s : List Std.U8) (l r : Nat) : Prop :=
    l ≤ r ∧ r < s.length ∧
      (∀ i, l ≤ i → i ≤ r → s[i]? = s[l]?) ∧
      (l = 0 ∨ s[l - 1]? ≠ s[l]?) ∧
      (r + 1 = s.length ∨ s[r + 1]? ≠ s[r]?)

  def numRunsFrom (prev : Option Std.U8) : List Std.U8 → Nat
    | [] => 0
    | x :: xs => (if prev = some x then 0 else 1) + numRunsFrom (some x) xs

  def numRuns (s : List Std.U8) : Nat := numRunsFrom none s

  def compressFrom (prev : Option Std.U8) : List Std.U8 → List Std.U8
    | [] => []
    | x :: xs =>
      if prev = some x then compressFrom prev xs else x :: compressFrom (some x) xs

  def runCompress (s : List Std.U8) : List Std.U8 := compressFrom none s

  def subList (s : List Std.U8) (l r : Nat) : List Std.U8 := (s.drop l).take (r + 1 - l)

  def tail1 (s : List Std.U8) : List Std.U8 := s.drop 1

  def init1 (s : List Std.U8) : List Std.U8 := s.take (s.length - 1)

  /-- Define a turn to be a triple (l, r, c) where l and r are integers with 0 <= l <= r < n and c is a byte. Define a printing plan for s to be a finite sequence of turns T_1, ..., T_m (m >= 0). Starting from an array a of length n whose entries are all a special blank value different from every byte, apply the turns in order: for T_t = (l_t, r_t, c_t), set a[i] := c_t for every i with l_t <= i <= r_t. The plan is valid for s if after all turns a[i] = s[i] for every 0 <= i < n. Its cost is m. The function returns a result res such that res equals the least cost m over all printing plans that are valid for s.
    Preconditions: s is a byte slice representing a string of length n = len(s) with 1 <= n <= 100, and every byte of s is an ASCII lowercase letter ('a' through 'z'). -/
  theorem spec_1 (s : Slice Std.U8) (n : Nat) (hn : n = s.val.length) (hn1 : 1 ≤ n)
      (hn100 : n ≤ 100) (hlower : ∀ b ∈ s.val, IsLowerByte b) :
      ∃ res, strange_printer s = ok res ∧ res.val = (minTurns s.val : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s : Slice Std.U8) (n : Nat) (hn : n = s.val.length) (hn1 : 1 ≤ n)
        (hn100 : n ≤ 100) (hlower : ∀ b ∈ s.val, IsLowerByte b), ∃ res, strange_printer s = ok res ∧ res.val = (minTurns s.val : Int)) := by
    sorry

  /-- Let D be the number of distinct byte values that occur among the entries s[0], ..., s[n-1]. The function returns a result res and res >= D.
    Preconditions: s is a byte slice representing a string of length n = len(s) with 1 <= n <= 100, and every byte of s is an ASCII lowercase letter ('a' through 'z'). -/
  theorem spec_2 (s : Slice Std.U8) (n : Nat) (hn : n = s.val.length) (hn1 : 1 ≤ n)
      (hn100 : n ≤ 100) (hlower : ∀ b ∈ s.val, IsLowerByte b) :
      ∃ res, strange_printer s = ok res ∧ (distinctCount s.val : Int) ≤ res.val := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s : Slice Std.U8) (n : Nat) (hn : n = s.val.length) (hn1 : 1 ≤ n)
        (hn100 : n ≤ 100) (hlower : ∀ b ∈ s.val, IsLowerByte b), ∃ res, strange_printer s = ok res ∧ (distinctCount s.val : Int) ≤ res.val) := by
    sorry

  /-- Let R be the number of maximal runs of equal characters in s: an interval [l, r] with 0 <= l <= r < n is a maximal run when s[l] = s[l+1] = ... = s[r], and (l = 0 or s[l-1] != s[l]) and (r = n-1 or s[r+1] != s[r]); R is the number of such intervals, which partition [0, n-1]. The function returns a result res and res >= ceil((R + 1) / 2), equivalently 2 * res >= R + 1.
    Preconditions: s is a byte slice representing a string of length n = len(s) with 1 <= n <= 100, and every byte of s is an ASCII lowercase letter ('a' through 'z'). -/
  theorem spec_3 (s : Slice Std.U8) (n : Nat) (hn : n = s.val.length) (hn1 : 1 ≤ n)
      (hn100 : n ≤ 100) (hlower : ∀ b ∈ s.val, IsLowerByte b) :
      ∃ res, strange_printer s = ok res ∧ (numRuns s.val : Int) + 1 ≤ 2 * res.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s : Slice Std.U8) (n : Nat) (hn : n = s.val.length) (hn1 : 1 ≤ n)
        (hn100 : n ≤ 100) (hlower : ∀ b ∈ s.val, IsLowerByte b), ∃ res, strange_printer s = ok res ∧ (numRuns s.val : Int) + 1 ≤ 2 * res.val) := by
    sorry

  /-- Let R be the number of maximal runs of equal characters in s, as defined in spec_3. The function returns a result res and res <= R.
    Preconditions: s is a byte slice representing a string of length n = len(s) with 1 <= n <= 100, and every byte of s is an ASCII lowercase letter ('a' through 'z'). -/
  theorem spec_4 (s : Slice Std.U8) (n : Nat) (hn : n = s.val.length) (hn1 : 1 ≤ n)
      (hn100 : n ≤ 100) (hlower : ∀ b ∈ s.val, IsLowerByte b) :
      ∃ res, strange_printer s = ok res ∧ res.val ≤ (numRuns s.val : Int) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s : Slice Std.U8) (n : Nat) (hn : n = s.val.length) (hn1 : 1 ≤ n)
        (hn100 : n ≤ 100) (hlower : ∀ b ∈ s.val, IsLowerByte b), ∃ res, strange_printer s = ok res ∧ res.val ≤ (numRuns s.val : Int)) := by
    sorry

  /-- For every s satisfying the preconditions, the function returns a result res (it does not fail: no overflow, no out-of-bounds access, and no panic).
    Preconditions: s is a byte slice representing a string of length n = len(s) with 1 <= n <= 100, and every byte of s is an ASCII lowercase letter ('a' through 'z'). -/
  theorem spec_5 (s : Slice Std.U8) (n : Nat) (hn : n = s.val.length) (hn1 : 1 ≤ n)
      (hn100 : n ≤ 100) (hlower : ∀ b ∈ s.val, IsLowerByte b) :
      ∃ res, strange_printer s = ok res := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s : Slice Std.U8) (n : Nat) (hn : n = s.val.length) (hn1 : 1 ≤ n)
        (hn100 : n ≤ 100) (hlower : ∀ b ∈ s.val, IsLowerByte b), ∃ res, strange_printer s = ok res) := by
    sorry

  /-- Let rev(s) be the byte slice of length n with rev(s)[i] = s[n-1-i] for every 0 <= i < n. The function returns a result res, and res equals the minimum number of turns needed to print rev(s), using the definition of a valid printing plan from spec_1 with s replaced by rev(s).
    Preconditions: s is a byte slice representing a string of length n = len(s) with 1 <= n <= 100, and every byte of s is an ASCII lowercase letter ('a' through 'z'). -/
  theorem spec_6 (s : Slice Std.U8) (n : Nat) (hn : n = s.val.length) (hn1 : 1 ≤ n)
      (hn100 : n ≤ 100) (hlower : ∀ b ∈ s.val, IsLowerByte b) :
      ∃ res, strange_printer s = ok res ∧ res.val = (minTurns s.val.reverse : Int) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s : Slice Std.U8) (n : Nat) (hn : n = s.val.length) (hn1 : 1 ≤ n)
        (hn100 : n ≤ 100) (hlower : ∀ b ∈ s.val, IsLowerByte b), ∃ res, strange_printer s = ok res ∧ res.val = (minTurns s.val.reverse : Int)) := by
    sorry

  /-- Let R be the number of maximal runs of s as in spec_3, and let t be the run-length compression of s: t is the byte slice of length R such that t[k] is the common byte of the k-th maximal run of s for k = 0, ..., R-1. The function returns a result res, and res equals the minimum number of turns needed to print t, using the definition of a valid printing plan from spec_1 with s replaced by t.
    Preconditions: s is a byte slice representing a string of length n = len(s) with 1 <= n <= 100, and every byte of s is an ASCII lowercase letter ('a' through 'z'). -/
  theorem spec_7 (s : Slice Std.U8) (n : Nat) (hn : n = s.val.length) (hn1 : 1 ≤ n)
      (hn100 : n ≤ 100) (hlower : ∀ b ∈ s.val, IsLowerByte b) :
      ∃ res, strange_printer s = ok res ∧ res.val = (minTurns (runCompress s.val) : Int) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s : Slice Std.U8) (n : Nat) (hn : n = s.val.length) (hn1 : 1 ≤ n)
        (hn100 : n ≤ 100) (hlower : ∀ b ∈ s.val, IsLowerByte b), ∃ res, strange_printer s = ok res ∧ res.val = (minTurns (runCompress s.val) : Int)) := by
    sorry

  /-- The function returns a result res, and for every byte slice t with len(t) = n such that for all integers i, j with 0 <= i < n and 0 <= j < n we have s[i] = s[j] if and only if t[i] = t[j], the minimum number of turns needed to print t equals res.
    Preconditions: s is a byte slice representing a string of length n = len(s) with 1 <= n <= 100, and every byte of s is an ASCII lowercase letter ('a' through 'z'). -/
  theorem spec_8 (s : Slice Std.U8) (n : Nat) (hn : n = s.val.length) (hn1 : 1 ≤ n)
      (hn100 : n ≤ 100) (hlower : ∀ b ∈ s.val, IsLowerByte b) :
      ∃ res, strange_printer s = ok res ∧
        ∀ t : List Std.U8, t.length = n →
          (∀ i j, i < n → j < n → (s.val[i]? = s.val[j]? ↔ t[i]? = t[j]?)) →
          res.val = (minTurns t : Int) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s : Slice Std.U8) (n : Nat) (hn : n = s.val.length) (hn1 : 1 ≤ n)
        (hn100 : n ≤ 100) (hlower : ∀ b ∈ s.val, IsLowerByte b), ∃ res, strange_printer s = ok res ∧
          ∀ t : List Std.U8, t.length = n →
            (∀ i j, i < n → j < n → (s.val[i]? = s.val[j]? ↔ t[i]? = t[j]?)) →
            res.val = (minTurns t : Int)) := by
    sorry

  /-- Let res be the returned result. For every pair of integers l, r with 0 <= l <= r < n, let sub be the contiguous substring s[l..r], that is, the byte slice of length r-l+1 with sub[k] = s[l+k] for 0 <= k <= r-l. Then the minimum number of turns needed to print sub is at most res.
    Preconditions: s is a byte slice representing a string of length n = len(s) with 1 <= n <= 100, and every byte of s is an ASCII lowercase letter ('a' through 'z'). -/
  theorem spec_9 (s : Slice Std.U8) (n : Nat) (hn : n = s.val.length) (hn1 : 1 ≤ n)
      (hn100 : n ≤ 100) (hlower : ∀ b ∈ s.val, IsLowerByte b) :
      ∃ res, strange_printer s = ok res ∧
        ∀ l r, l ≤ r → r < n → (minTurns (subList s.val l r) : Int) ≤ res.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s : Slice Std.U8) (n : Nat) (hn : n = s.val.length) (hn1 : 1 ≤ n)
        (hn100 : n ≤ 100) (hlower : ∀ b ∈ s.val, IsLowerByte b), ∃ res, strange_printer s = ok res ∧
          ∀ l r, l ≤ r → r < n → (minTurns (subList s.val l r) : Int) ≤ res.val) := by
    sorry

  /-- Let res be the returned result and let t be the byte slice s[1..n-1] (if n = 1, t is the empty slice). Let M(t) denote the minimum number of turns needed to print t, with M(empty) = 0. Then res = M(t) or res = M(t) + 1.
    Preconditions: s is a byte slice representing a string of length n = len(s) with 1 <= n <= 100, and every byte of s is an ASCII lowercase letter ('a' through 'z'). -/
  theorem spec_10 (s : Slice Std.U8) (n : Nat) (hn : n = s.val.length) (hn1 : 1 ≤ n)
      (hn100 : n ≤ 100) (hlower : ∀ b ∈ s.val, IsLowerByte b) :
      ∃ res, strange_printer s = ok res ∧
        (res.val = (minTurns (tail1 s.val) : Int) ∨
          res.val = (minTurns (tail1 s.val) : Int) + 1) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (s : Slice Std.U8) (n : Nat) (hn : n = s.val.length) (hn1 : 1 ≤ n)
        (hn100 : n ≤ 100) (hlower : ∀ b ∈ s.val, IsLowerByte b), ∃ res, strange_printer s = ok res ∧
          (res.val = (minTurns (tail1 s.val) : Int) ∨
            res.val = (minTurns (tail1 s.val) : Int) + 1)) := by
    sorry

  /-- Let res be the returned result and let u be the byte slice s[0..n-2] (if n = 1, u is the empty slice). Let M(u) denote the minimum number of turns needed to print u, with M(empty) = 0. Then res = M(u) or res = M(u) + 1.
    Preconditions: s is a byte slice representing a string of length n = len(s) with 1 <= n <= 100, and every byte of s is an ASCII lowercase letter ('a' through 'z'). -/
  theorem spec_11 (s : Slice Std.U8) (n : Nat) (hn : n = s.val.length) (hn1 : 1 ≤ n)
      (hn100 : n ≤ 100) (hlower : ∀ b ∈ s.val, IsLowerByte b) :
      ∃ res, strange_printer s = ok res ∧
        (res.val = (minTurns (init1 s.val) : Int) ∨
          res.val = (minTurns (init1 s.val) : Int) + 1) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (s : Slice Std.U8) (n : Nat) (hn : n = s.val.length) (hn1 : 1 ≤ n)
        (hn100 : n ≤ 100) (hlower : ∀ b ∈ s.val, IsLowerByte b), ∃ res, strange_printer s = ok res ∧
          (res.val = (minTurns (init1 s.val) : Int) ∨
            res.val = (minTurns (init1 s.val) : Int) + 1)) := by
    sorry

  /-- For the returned result res, there exists a valid printing plan for s in the sense of spec_1 whose cost is exactly res.
    Preconditions: s is a byte slice representing a string of length n = len(s) with 1 <= n <= 100, and every byte of s is an ASCII lowercase letter ('a' through 'z'). -/
  theorem spec_12 (s : Slice Std.U8) (n : Nat) (hn : n = s.val.length) (hn1 : 1 ≤ n)
      (hn100 : n ≤ 100) (hlower : ∀ b ∈ s.val, IsLowerByte b) :
      ∃ res, strange_printer s = ok res ∧
        ∃ plan : List Turn, ValidPlan s.val plan ∧ (plan.length : Int) = res.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (s : Slice Std.U8) (n : Nat) (hn : n = s.val.length) (hn1 : 1 ≤ n)
        (hn100 : n ≤ 100) (hlower : ∀ b ∈ s.val, IsLowerByte b), ∃ res, strange_printer s = ok res ∧
          ∃ plan : List Turn, ValidPlan s.val plan ∧ (plan.length : Int) = res.val) := by
    sorry

  /-- Let M(u) denote the minimum number of turns needed to print a byte slice u using the definition of a valid printing plan from spec_1. For every integer k with 0 <= k < n-1, let u = s[0..k] and v = s[k+1..n-1]. Then res <= M(u) + M(v).
    Preconditions: s is a byte slice representing a string of length n = len(s) with 1 <= n <= 100, and every byte of s is an ASCII lowercase letter ('a' through 'z'). -/
  theorem spec_13 (s : Slice Std.U8) (n : Nat) (hn : n = s.val.length) (hn1 : 1 ≤ n)
      (hn100 : n ≤ 100) (hlower : ∀ b ∈ s.val, IsLowerByte b) :
      ∃ res, strange_printer s = ok res ∧
        ∀ k, k < n - 1 →
          res.val ≤ (minTurns (subList s.val 0 k) : Int) +
            (minTurns (subList s.val (k + 1) (n - 1)) : Int) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (s : Slice Std.U8) (n : Nat) (hn : n = s.val.length) (hn1 : 1 ≤ n)
        (hn100 : n ≤ 100) (hlower : ∀ b ∈ s.val, IsLowerByte b), ∃ res, strange_printer s = ok res ∧
          ∀ k, k < n - 1 →
            res.val ≤ (minTurns (subList s.val 0 k) : Int) +
              (minTurns (subList s.val (k + 1) (n - 1)) : Int)) := by
    sorry

  end AegisSpec.StrangePrinter
