import Aegis.CountSubstrings.Code.Funs

/-!
# Specifications of `Aegis.CountSubstrings.count_substrings`

LeetCode problem `count-substrings-that-differ-by-one-character`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.CountSubstrings

namespace AegisSpec.CountSubstrings

def byteLower (b : Std.U8) : Prop := 97 ≤ b.val ∧ b.val ≤ 122

def allLowerBelow (l : List Std.U8) (n : Nat) : Prop :=
  ∀ i, i < n → ∀ b, l[i]? = some b → byteLower b

def diffCount (s t : List Std.U8) (i j k : Nat) : Nat :=
  ((Finset.range k).filter (fun p => s[i + p]? ≠ t[j + p]?)).card

@[reducible] def oneDiff (s t : List Std.U8) (n m i j k : Nat) : Prop :=
  1 ≤ k ∧ i + k ≤ n ∧ j + k ≤ m ∧ diffCount s t i j k = 1

def oneDiffWindows (s t : List Std.U8) (n m : Nat) : Finset (Nat × Nat × Nat) :=
  (((Finset.range n) ×ˢ ((Finset.range m) ×ˢ (Finset.range (n + 1)))).filter
    (fun q => oneDiff s t n m q.1 q.2.1 q.2.2))

def oneDiffCount (s t : List Std.U8) (n m : Nat) : Nat := (oneDiffWindows s t n m).card

def nePairs (s t : List Std.U8) (n m : Nat) : Nat :=
  (((Finset.range n) ×ˢ (Finset.range m)).filter (fun p => s[p.1]? ≠ t[p.2]?)).card

def totalWindows (n m : Nat) : Nat :=
  (Finset.Icc 1 (min n m)).sum (fun k => (n - k + 1) * (m - k + 1))

def countNeFixed (o : Option Std.U8) (l : List Std.U8) : Nat :=
  match o with
  | none => 0
  | some b => (l.filter (fun x => x ≠ b)).length

def occursIn (pat l : List Std.U8) : Prop :=
  ∃ q, q + pat.length ≤ l.length ∧ ∀ j, j < pat.length → l[q + j]? = pat[j]?

def letterPerm (π : Std.U8 → Std.U8) : Prop :=
  (∀ b, byteLower b → byteLower (π b)) ∧
    (∀ a b, byteLower a → byteLower b → π a = π b → a = b) ∧
      (∀ b, byteLower b → ∃ a, byteLower a ∧ π a = b)

/-- Let val(r) be the mathematical integer represented by the returned I64 value r. The function returns a result r, and val(r) equals the number of triples (i,j,k) of natural numbers such that 0 <= i < n, 0 <= j < m, 1 <= k, i + k <= n, j + k <= m, and the number of positions p with 0 <= p < k and s[i+p] != t[j+p] is exactly 1. Equivalently, val(r) is the number of ordered pairs consisting of an occurrence of a non-empty contiguous substring of s, specified by start i and length k, and an occurrence of a contiguous substring of t of the same length, specified by start j and length k, such that the two substrings differ in exactly one position.
  Preconditions: Let n = len(s) and m = len(t). We assume 1 <= n <= 100, 1 <= m <= 100, for every i with 0 <= i < n the byte s[i] is an ASCII lowercase English letter (97 <= s[i] <= 122), and for every j with 0 <= j < m the byte t[j] is an ASCII lowercase English letter (97 <= t[j] <= 122). -/
theorem spec_1 (s t : Slice Std.U8) (n m : Nat)
    (hn : n = (Slice.len s).val) (hm : m = (Slice.len t).val)
    (hn_lb : 1 ≤ n) (hn_ub : n ≤ 100) (hm_lb : 1 ≤ m) (hm_ub : m ≤ 100)
    (hs : allLowerBelow s.val n) (ht : allLowerBelow t.val m) :
    ∃ r : Std.I64,
      count_substrings s t = ok r ∧ r.val = ((oneDiffCount s.val t.val n m : Nat) : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s t : Slice Std.U8) (n m : Nat)
    (hn : n = (Slice.len s).val) (hm : m = (Slice.len t).val)
    (hn_lb : 1 ≤ n) (hn_ub : n ≤ 100) (hm_lb : 1 ≤ m) (hm_ub : m ≤ 100)
    (hs : allLowerBelow s.val n) (ht : allLowerBelow t.val m), ∃ r : Std.I64,
      count_substrings s t = ok r ∧ r.val = ((oneDiffCount s.val t.val n m : Nat) : Int)) := by
  sorry

/-- The function returns a result r on every input satisfying the preconditions; it never fails, panics, or overflows.
  Preconditions: Let n = len(s) and m = len(t). We assume 1 <= n <= 100, 1 <= m <= 100, for every i with 0 <= i < n the byte s[i] is an ASCII lowercase English letter (97 <= s[i] <= 122), and for every j with 0 <= j < m the byte t[j] is an ASCII lowercase English letter (97 <= t[j] <= 122). -/
theorem spec_2 (s t : Slice Std.U8) (n m : Nat)
    (hn : n = (Slice.len s).val) (hm : m = (Slice.len t).val)
    (hn_lb : 1 ≤ n) (hn_ub : n ≤ 100) (hm_lb : 1 ≤ m) (hm_ub : m ≤ 100)
    (hs : allLowerBelow s.val n) (ht : allLowerBelow t.val m) :
    ∃ r : Std.I64, count_substrings s t = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s t : Slice Std.U8) (n m : Nat)
    (hn : n = (Slice.len s).val) (hm : m = (Slice.len t).val)
    (hn_lb : 1 ≤ n) (hn_ub : n ≤ 100) (hm_lb : 1 ≤ m) (hm_ub : m ≤ 100)
    (hs : allLowerBelow s.val n) (ht : allLowerBelow t.val m), ∃ r : Std.I64, count_substrings s t = ok r) := by
  sorry

/-- The function returns a result r, and val(r) >= 0, where val(r) is the mathematical integer represented by r.
  Preconditions: Let n = len(s) and m = len(t). We assume 1 <= n <= 100, 1 <= m <= 100, for every i with 0 <= i < n the byte s[i] is an ASCII lowercase English letter (97 <= s[i] <= 122), and for every j with 0 <= j < m the byte t[j] is an ASCII lowercase English letter (97 <= t[j] <= 122). -/
theorem spec_3 (s t : Slice Std.U8) (n m : Nat)
    (hn : n = (Slice.len s).val) (hm : m = (Slice.len t).val)
    (hn_lb : 1 ≤ n) (hn_ub : n ≤ 100) (hm_lb : 1 ≤ m) (hm_ub : m ≤ 100)
    (hs : allLowerBelow s.val n) (ht : allLowerBelow t.val m) :
    ∃ r : Std.I64, count_substrings s t = ok r ∧ (0 : Int) ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s t : Slice Std.U8) (n m : Nat)
    (hn : n = (Slice.len s).val) (hm : m = (Slice.len t).val)
    (hn_lb : 1 ≤ n) (hn_ub : n ≤ 100) (hm_lb : 1 ≤ m) (hm_ub : m ≤ 100)
    (hs : allLowerBelow s.val n) (ht : allLowerBelow t.val m), ∃ r : Std.I64, count_substrings s t = ok r ∧ (0 : Int) ≤ r.val) := by
  sorry

/-- The function returns a result r, and val(r) <= sum_{k=1}^{min(n,m)} (n-k+1)*(m-k+1), where val(r) is the mathematical integer represented by r. The right-hand side is the total number of ordered pairs of occurrences of non-empty contiguous substrings of s and t having equal length.
  Preconditions: Let n = len(s) and m = len(t). We assume 1 <= n <= 100, 1 <= m <= 100, for every i with 0 <= i < n the byte s[i] is an ASCII lowercase English letter (97 <= s[i] <= 122), and for every j with 0 <= j < m the byte t[j] is an ASCII lowercase English letter (97 <= t[j] <= 122). -/
theorem spec_4 (s t : Slice Std.U8) (n m : Nat)
    (hn : n = (Slice.len s).val) (hm : m = (Slice.len t).val)
    (hn_lb : 1 ≤ n) (hn_ub : n ≤ 100) (hm_lb : 1 ≤ m) (hm_ub : m ≤ 100)
    (hs : allLowerBelow s.val n) (ht : allLowerBelow t.val m) :
    ∃ r : Std.I64,
      count_substrings s t = ok r ∧ r.val ≤ ((totalWindows n m : Nat) : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s t : Slice Std.U8) (n m : Nat)
    (hn : n = (Slice.len s).val) (hm : m = (Slice.len t).val)
    (hn_lb : 1 ≤ n) (hn_ub : n ≤ 100) (hm_lb : 1 ≤ m) (hm_ub : m ≤ 100)
    (hs : allLowerBelow s.val n) (ht : allLowerBelow t.val m), ∃ r : Std.I64,
      count_substrings s t = ok r ∧ r.val ≤ ((totalWindows n m : Nat) : Int)) := by
  sorry

/-- The function returns a result r, and val(r) equals the number of indices j with 0 <= j < m and s[0] != t[j], where val(r) is the mathematical integer represented by r. Equivalently, val(r) = m minus the number of indices j with 0 <= j < m and t[j] = s[0].
  Preconditions: Let n = len(s) and m = len(t). We assume n = 1, 1 <= m <= 100, s[0] is an ASCII lowercase English letter (97 <= s[0] <= 122), and for every j with 0 <= j < m the byte t[j] is an ASCII lowercase English letter (97 <= t[j] <= 122). -/
theorem spec_5 (s t : Slice Std.U8) (n m : Nat)
    (hn : n = (Slice.len s).val) (hm : m = (Slice.len t).val) (hn_one : n = 1)
    (hm_lb : 1 ≤ m) (hm_ub : m ≤ 100)
    (hs : allLowerBelow s.val n) (ht : allLowerBelow t.val m) :
    ∃ r : Std.I64,
      count_substrings s t = ok r ∧ r.val = ((countNeFixed (s.val[0]?) t.val : Nat) : Int) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s t : Slice Std.U8) (n m : Nat)
    (hn : n = (Slice.len s).val) (hm : m = (Slice.len t).val) (hn_one : n = 1)
    (hm_lb : 1 ≤ m) (hm_ub : m ≤ 100)
    (hs : allLowerBelow s.val n) (ht : allLowerBelow t.val m), ∃ r : Std.I64,
      count_substrings s t = ok r ∧ r.val = ((countNeFixed (s.val[0]?) t.val : Nat) : Int)) := by
  sorry

/-- The function returns a result r, and val(r) equals the number of indices i with 0 <= i < n and s[i] != t[0], where val(r) is the mathematical integer represented by r. Equivalently, val(r) = n minus the number of indices i with 0 <= i < n and s[i] = t[0].
  Preconditions: Let n = len(s) and m = len(t). We assume 1 <= n <= 100, m = 1, for every i with 0 <= i < n the byte s[i] is an ASCII lowercase English letter (97 <= s[i] <= 122), and t[0] is an ASCII lowercase English letter (97 <= t[0] <= 122). -/
theorem spec_6 (s t : Slice Std.U8) (n m : Nat)
    (hn : n = (Slice.len s).val) (hm : m = (Slice.len t).val) (hm_one : m = 1)
    (hn_lb : 1 ≤ n) (hn_ub : n ≤ 100)
    (hs : allLowerBelow s.val n) (ht : allLowerBelow t.val m) :
    ∃ r : Std.I64,
      count_substrings s t = ok r ∧ r.val = ((countNeFixed (t.val[0]?) s.val : Nat) : Int) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s t : Slice Std.U8) (n m : Nat)
    (hn : n = (Slice.len s).val) (hm : m = (Slice.len t).val) (hm_one : m = 1)
    (hn_lb : 1 ≤ n) (hn_ub : n ≤ 100)
    (hs : allLowerBelow s.val n) (ht : allLowerBelow t.val m), ∃ r : Std.I64,
      count_substrings s t = ok r ∧ r.val = ((countNeFixed (t.val[0]?) s.val : Nat) : Int)) := by
  sorry

/-- The function returns a result r, and val(r) = n * m, where val(r) is the mathematical integer represented by r.
  Preconditions: Let n = len(s) and m = len(t). We assume 1 <= n <= 100, 1 <= m <= 100, for every i with 0 <= i < n the byte s[i] is an ASCII lowercase English letter (97 <= s[i] <= 122), for every j with 0 <= j < m the byte t[j] is an ASCII lowercase English letter (97 <= t[j] <= 122), and for every i with 0 <= i < n and every j with 0 <= j < m, s[i] != t[j]. -/
theorem spec_7 (s t : Slice Std.U8) (n m : Nat)
    (hn : n = (Slice.len s).val) (hm : m = (Slice.len t).val)
    (hn_lb : 1 ≤ n) (hn_ub : n ≤ 100) (hm_lb : 1 ≤ m) (hm_ub : m ≤ 100)
    (hs : allLowerBelow s.val n) (ht : allLowerBelow t.val m)
    (hdisj : ∀ (i j : Nat), i < n → j < m → s.val[i]? ≠ t.val[j]?) :
    ∃ r : Std.I64,
      count_substrings s t = ok r ∧ r.val = ((n * m : Nat) : Int) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s t : Slice Std.U8) (n m : Nat)
    (hn : n = (Slice.len s).val) (hm : m = (Slice.len t).val)
    (hn_lb : 1 ≤ n) (hn_ub : n ≤ 100) (hm_lb : 1 ≤ m) (hm_ub : m ≤ 100)
    (hs : allLowerBelow s.val n) (ht : allLowerBelow t.val m)
    (hdisj : ∀ (i j : Nat), i < n → j < m → s.val[i]? ≠ t.val[j]?), ∃ r : Std.I64,
      count_substrings s t = ok r ∧ r.val = ((n * m : Nat) : Int)) := by
  sorry

/-- The function returns a result r, and val(r) >= C, where val(r) is the mathematical integer represented by r and C is the number of ordered pairs (i,j) with 0 <= i < n, 0 <= j < m, and s[i] != t[j].
  Preconditions: Let n = len(s) and m = len(t). We assume 1 <= n <= 100, 1 <= m <= 100, for every i with 0 <= i < n the byte s[i] is an ASCII lowercase English letter (97 <= s[i] <= 122), and for every j with 0 <= j < m the byte t[j] is an ASCII lowercase English letter (97 <= t[j] <= 122). -/
theorem spec_8 (s t : Slice Std.U8) (n m : Nat)
    (hn : n = (Slice.len s).val) (hm : m = (Slice.len t).val)
    (hn_lb : 1 ≤ n) (hn_ub : n ≤ 100) (hm_lb : 1 ≤ m) (hm_ub : m ≤ 100)
    (hs : allLowerBelow s.val n) (ht : allLowerBelow t.val m) :
    ∃ r : Std.I64,
      count_substrings s t = ok r ∧ ((nePairs s.val t.val n m : Nat) : Int) ≤ r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s t : Slice Std.U8) (n m : Nat)
    (hn : n = (Slice.len s).val) (hm : m = (Slice.len t).val)
    (hn_lb : 1 ≤ n) (hn_ub : n ≤ 100) (hm_lb : 1 ≤ m) (hm_ub : m ≤ 100)
    (hs : allLowerBelow s.val n) (ht : allLowerBelow t.val m), ∃ r : Std.I64,
      count_substrings s t = ok r ∧ ((nePairs s.val t.val n m : Nat) : Int) ≤ r.val) := by
  sorry

/-- The function returns a result r, and val(r) = 0 if and only if there do not exist natural numbers i, j, k with 0 <= i < n, 0 <= j < m, 1 <= k, i+k <= n, j+k <= m, and exactly one position p with 0 <= p < k such that s[i+p] != t[j+p]; here val(r) is the mathematical integer represented by r.
  Preconditions: Let n = len(s) and m = len(t). We assume 1 <= n <= 100, 1 <= m <= 100, for every i with 0 <= i < n the byte s[i] is an ASCII lowercase English letter (97 <= s[i] <= 122), and for every j with 0 <= j < m the byte t[j] is an ASCII lowercase English letter (97 <= t[j] <= 122). -/
theorem spec_9 (s t : Slice Std.U8) (n m : Nat)
    (hn : n = (Slice.len s).val) (hm : m = (Slice.len t).val)
    (hn_lb : 1 ≤ n) (hn_ub : n ≤ 100) (hm_lb : 1 ≤ m) (hm_ub : m ≤ 100)
    (hs : allLowerBelow s.val n) (ht : allLowerBelow t.val m) :
    ∃ r : Std.I64,
      count_substrings s t = ok r ∧
        (r.val = 0 ↔
          ¬ (∃ i j k : Nat,
              i < n ∧ j < m ∧ 1 ≤ k ∧ i + k ≤ n ∧ j + k ≤ m ∧
                diffCount s.val t.val i j k = 1)) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s t : Slice Std.U8) (n m : Nat)
    (hn : n = (Slice.len s).val) (hm : m = (Slice.len t).val)
    (hn_lb : 1 ≤ n) (hn_ub : n ≤ 100) (hm_lb : 1 ≤ m) (hm_ub : m ≤ 100)
    (hs : allLowerBelow s.val n) (ht : allLowerBelow t.val m), ∃ r : Std.I64,
      count_substrings s t = ok r ∧
        (r.val = 0 ↔
          ¬ (∃ i j k : Nat,
              i < n ∧ j < m ∧ 1 ≤ k ∧ i + k ≤ n ∧ j + k ≤ m ∧
                diffCount s.val t.val i j k = 1))) := by
  sorry

/-- Let r be the result returned by count_substrings(s,t), and let r_swapped be the result returned by count_substrings(t,s). Under the preconditions both calls return results, and val(r) = val(r_swapped), where val denotes the mathematical integer represented by the corresponding I64 value.
  Preconditions: Let n = len(s) and m = len(t). We assume 1 <= n <= 100, 1 <= m <= 100, for every i with 0 <= i < n the byte s[i] is an ASCII lowercase English letter (97 <= s[i] <= 122), and for every j with 0 <= j < m the byte t[j] is an ASCII lowercase English letter (97 <= t[j] <= 122). -/
theorem spec_10 (s t : Slice Std.U8) (n m : Nat)
    (hn : n = (Slice.len s).val) (hm : m = (Slice.len t).val)
    (hn_lb : 1 ≤ n) (hn_ub : n ≤ 100) (hm_lb : 1 ≤ m) (hm_ub : m ≤ 100)
    (hs : allLowerBelow s.val n) (ht : allLowerBelow t.val m) :
    ∃ r r_swapped : Std.I64,
      count_substrings s t = ok r ∧ count_substrings t s = ok r_swapped ∧
        r.val = r_swapped.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s t : Slice Std.U8) (n m : Nat)
    (hn : n = (Slice.len s).val) (hm : m = (Slice.len t).val)
    (hn_lb : 1 ≤ n) (hn_ub : n ≤ 100) (hm_lb : 1 ≤ m) (hm_ub : m ≤ 100)
    (hs : allLowerBelow s.val n) (ht : allLowerBelow t.val m), ∃ r r_swapped : Std.I64,
      count_substrings s t = ok r ∧ count_substrings t s = ok r_swapped ∧
        r.val = r_swapped.val) := by
  sorry

/-- Define rev_s by len(rev_s) = n and rev_s[q] = s[n-1-q] for 0 <= q < n, and define rev_t by len(rev_t) = m and rev_t[q] = t[m-1-q] for 0 <= q < m. Let r be the result returned by count_substrings(s,t), and let r_rev be the result returned by count_substrings(rev_s,rev_t). Both calls return results, and val(r) = val(r_rev), where val denotes the mathematical integer represented by the corresponding I64 value.
  Preconditions: Let n = len(s) and m = len(t). We assume 1 <= n <= 100, 1 <= m <= 100, for every i with 0 <= i < n the byte s[i] is an ASCII lowercase English letter (97 <= s[i] <= 122), and for every j with 0 <= j < m the byte t[j] is an ASCII lowercase English letter (97 <= t[j] <= 122). -/
theorem spec_11 (s t rev_s rev_t : Slice Std.U8) (n m : Nat)
    (hn : n = (Slice.len s).val) (hm : m = (Slice.len t).val)
    (hn_lb : 1 ≤ n) (hn_ub : n ≤ 100) (hm_lb : 1 ≤ m) (hm_ub : m ≤ 100)
    (hs : allLowerBelow s.val n) (ht : allLowerBelow t.val m)
    (hrev_s : rev_s.val = s.val.reverse) (hrev_t : rev_t.val = t.val.reverse) :
    ∃ r r_rev : Std.I64,
      count_substrings s t = ok r ∧ count_substrings rev_s rev_t = ok r_rev ∧
        r.val = r_rev.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s t rev_s rev_t : Slice Std.U8) (n m : Nat)
    (hn : n = (Slice.len s).val) (hm : m = (Slice.len t).val)
    (hn_lb : 1 ≤ n) (hn_ub : n ≤ 100) (hm_lb : 1 ≤ m) (hm_ub : m ≤ 100)
    (hs : allLowerBelow s.val n) (ht : allLowerBelow t.val m)
    (hrev_s : rev_s.val = s.val.reverse) (hrev_t : rev_t.val = t.val.reverse), ∃ r r_rev : Std.I64,
      count_substrings s t = ok r ∧ count_substrings rev_s rev_t = ok r_rev ∧
        r.val = r_rev.val) := by
  sorry

/-- For every bijection pi from the set of lowercase English letters to itself, define s_pi by s_pi[i] = pi(s[i]) for 0 <= i < n and t_pi by t_pi[j] = pi(t[j]) for 0 <= j < m. Let r be the result returned by count_substrings(s,t), and let r_pi be the result returned by count_substrings(s_pi,t_pi). Both calls return results, and val(r) = val(r_pi), where val denotes the mathematical integer represented by the corresponding I64 value.
  Preconditions: Let n = len(s) and m = len(t). We assume 1 <= n <= 100, 1 <= m <= 100, for every i with 0 <= i < n the byte s[i] is an ASCII lowercase English letter (97 <= s[i] <= 122), and for every j with 0 <= j < m the byte t[j] is an ASCII lowercase English letter (97 <= t[j] <= 122). -/
theorem spec_12 (s t pi_s pi_t : Slice Std.U8) (π : Std.U8 → Std.U8) (n m : Nat)
    (hn : n = (Slice.len s).val) (hm : m = (Slice.len t).val)
    (hn_lb : 1 ≤ n) (hn_ub : n ≤ 100) (hm_lb : 1 ≤ m) (hm_ub : m ≤ 100)
    (hs : allLowerBelow s.val n) (ht : allLowerBelow t.val m)
    (hπ : letterPerm π)
    (hpi_s : pi_s.val = s.val.map π) (hpi_t : pi_t.val = t.val.map π) :
    ∃ r r_pi : Std.I64,
      count_substrings s t = ok r ∧ count_substrings pi_s pi_t = ok r_pi ∧
        r.val = r_pi.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (s t pi_s pi_t : Slice Std.U8) (π : Std.U8 → Std.U8) (n m : Nat)
    (hn : n = (Slice.len s).val) (hm : m = (Slice.len t).val)
    (hn_lb : 1 ≤ n) (hn_ub : n ≤ 100) (hm_lb : 1 ≤ m) (hm_ub : m ≤ 100)
    (hs : allLowerBelow s.val n) (ht : allLowerBelow t.val m)
    (hπ : letterPerm π)
    (hpi_s : pi_s.val = s.val.map π) (hpi_t : pi_t.val = t.val.map π), ∃ r r_pi : Std.I64,
      count_substrings s t = ok r ∧ count_substrings pi_s pi_t = ok r_pi ∧
        r.val = r_pi.val) := by
  sorry

/-- For every byte slice t2 with 1 <= len(t2) <= 100, all bytes of t2 lowercase English letters, and such that t occurs as a contiguous substring of t2 (there exists q with 0 <= q, q + m <= len(t2), and t2[q+j] = t[j] for all 0 <= j < m), let r be the result returned by count_substrings(s,t) and let r2 be the result returned by count_substrings(s,t2). Both calls return results, and val(r) <= val(r2), where val denotes the mathematical integer represented by the corresponding I64 value.
  Preconditions: Let n = len(s) and m = len(t). We assume 1 <= n <= 100, 1 <= m <= 100, for every i with 0 <= i < n the byte s[i] is an ASCII lowercase English letter (97 <= s[i] <= 122), and for every j with 0 <= j < m the byte t[j] is an ASCII lowercase English letter (97 <= t[j] <= 122). -/
theorem spec_13 (s t t2 : Slice Std.U8) (n m m2 : Nat)
    (hn : n = (Slice.len s).val) (hm : m = (Slice.len t).val)
    (hm2 : m2 = (Slice.len t2).val)
    (hn_lb : 1 ≤ n) (hn_ub : n ≤ 100) (hm_lb : 1 ≤ m) (hm_ub : m ≤ 100)
    (hm2_lb : 1 ≤ m2) (hm2_ub : m2 ≤ 100)
    (hs : allLowerBelow s.val n) (ht : allLowerBelow t.val m)
    (ht2 : allLowerBelow t2.val m2) (hocc : occursIn t.val t2.val) :
    ∃ r r2 : Std.I64,
      count_substrings s t = ok r ∧ count_substrings s t2 = ok r2 ∧ r.val ≤ r2.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (s t t2 : Slice Std.U8) (n m m2 : Nat)
    (hn : n = (Slice.len s).val) (hm : m = (Slice.len t).val)
    (hm2 : m2 = (Slice.len t2).val)
    (hn_lb : 1 ≤ n) (hn_ub : n ≤ 100) (hm_lb : 1 ≤ m) (hm_ub : m ≤ 100)
    (hm2_lb : 1 ≤ m2) (hm2_ub : m2 ≤ 100)
    (hs : allLowerBelow s.val n) (ht : allLowerBelow t.val m)
    (ht2 : allLowerBelow t2.val m2) (hocc : occursIn t.val t2.val), ∃ r r2 : Std.I64,
      count_substrings s t = ok r ∧ count_substrings s t2 = ok r2 ∧ r.val ≤ r2.val) := by
  sorry

/-- Let r be the result returned by count_substrings(s,t) and let r2 be the result returned by count_substrings(s2,t). Under the preconditions both calls return results, and val(r) <= val(r2), where val denotes the mathematical integer represented by the corresponding I64 value.
  Preconditions: Let n = len(s), m = len(t), and n2 = len(s2). Assume 1 <= n <= n2 <= 100, 1 <= m <= 100, all bytes of s, s2, and t are ASCII lowercase English letters (97 <= byte <= 122), and s occurs as a contiguous substring of s2: there exists q with 0 <= q, q + n <= n2, and s2[q+i] = s[i] for all 0 <= i < n. -/
theorem spec_14 (s s2 t : Slice Std.U8) (n n2 m : Nat)
    (hn : n = (Slice.len s).val) (hn2 : n2 = (Slice.len s2).val)
    (hm : m = (Slice.len t).val)
    (hn_lb : 1 ≤ n) (hn_le : n ≤ n2) (hn2_ub : n2 ≤ 100)
    (hm_lb : 1 ≤ m) (hm_ub : m ≤ 100)
    (hs : allLowerBelow s.val n) (hs2 : allLowerBelow s2.val n2)
    (ht : allLowerBelow t.val m) (hocc : occursIn s.val s2.val) :
    ∃ r r2 : Std.I64,
      count_substrings s t = ok r ∧ count_substrings s2 t = ok r2 ∧ r.val ≤ r2.val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (s s2 t : Slice Std.U8) (n n2 m : Nat)
    (hn : n = (Slice.len s).val) (hn2 : n2 = (Slice.len s2).val)
    (hm : m = (Slice.len t).val)
    (hn_lb : 1 ≤ n) (hn_le : n ≤ n2) (hn2_ub : n2 ≤ 100)
    (hm_lb : 1 ≤ m) (hm_ub : m ≤ 100)
    (hs : allLowerBelow s.val n) (hs2 : allLowerBelow s2.val n2)
    (ht : allLowerBelow t.val m) (hocc : occursIn s.val s2.val), ∃ r r2 : Std.I64,
      count_substrings s t = ok r ∧ count_substrings s2 t = ok r2 ∧ r.val ≤ r2.val) := by
  sorry

end AegisSpec.CountSubstrings
