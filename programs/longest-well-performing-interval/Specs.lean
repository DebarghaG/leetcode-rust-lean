import Aegis.LongestWpi.Code.Funs

/-!
# Specifications of `Aegis.LongestWpi.longest_wpi`

LeetCode problem `longest-well-performing-interval`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.LongestWpi

set_option autoImplicit false

namespace AegisSpec.LongestWpi

def entry (l : List Std.I64) (i : Nat) : Int := ((l[i]?).map (fun x => x.val)).getD 0

def wpi (x : Int) : Int := if x > 8 then 1 else -1

def score (l : List Std.I64) (a b : Nat) : Int :=
  (List.range (b - a)).foldl (fun acc k => acc + wpi (entry l (a + k))) 0

def total (l : List Std.I64) : Int := score l 0 l.length

def InRange (l : List Std.I64) : Prop :=
  ∀ (i : Nat), i < l.length → 0 ≤ entry l i ∧ entry l i ≤ 16

def AllHeavy (l : List Std.I64) : Prop :=
  ∀ (i : Nat), i < l.length → 8 < entry l i

def AllLight (l : List Std.I64) : Prop :=
  ∀ (i : Nat), i < l.length → entry l i ≤ 8

def UniqueHeavy (l : List Std.I64) : Prop :=
  ∃ (i : Nat), i < l.length ∧ 8 < entry l i ∧
    ∀ (j : Nat), j < l.length → 8 < entry l j → j = i

def IsLongestWpi (l : List Std.I64) (n : Nat) (ans : Int) : Prop :=
  (∀ (a b : Nat), a < b → b ≤ n → 0 < score l a b → (b - a : Int) ≤ ans) ∧
    (ans = 0 ∨ ∃ (a b : Nat), a < b ∧ b ≤ n ∧ 0 < score l a b ∧ (b - a : Int) = ans)

def rev (hours : Slice Std.I64) : Slice Std.I64 :=
  ⟨hours.val.reverse.length, Aeneas.Data.ListN.ListN.fromList hours.val.reverse, by
    rw [List.length_reverse]
    have h : hours.val.length = hours.leng := Aeneas.Data.ListN.ListN_length hours.list
    rw [h]
    exact hours.bound⟩

theorem entry_eq (l : List Std.I64) (i : Nat) (h : i < l.length) : entry l i = (l[i]).val := by
  simp [entry, List.getElem?_eq_getElem h]

theorem rev_val (hours : Slice Std.I64) : (rev hours).val = hours.val.reverse :=
  Aeneas.Data.ListN.ListN.from_to_inverse

theorem rev_length (hours : Slice Std.I64) :
    (rev hours).val.length = hours.val.length := by
  rw [rev_val, List.length_reverse]

/-- Let n = len(hours). For 0 <= a < b <= n, let score(a,b) = sum_{i=a}^{b-1} (1 if hours[i] > 8 else -1). Then longest_wpi hours returns a result ans such that: if the set S = { b-a | 0 <= a < b <= n and score(a,b) > 0 } is nonempty, ans = max S; if S is empty, ans = 0.
  Preconditions: hours is a valid input: n = len(hours), 1 <= n <= 10000, and for every i with 0 <= i < n, 0 <= hours[i] <= 16. -/
theorem spec_1 (hours : Slice Std.I64) (n : Nat) (hn : n = hours.val.length)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 10000) (hvalid : InRange hours.val) :
    ∃ (ans : Std.I64), longest_wpi hours = Result.ok ans ∧ IsLongestWpi hours.val n ans.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (hours : Slice Std.I64) (n : Nat) (hn : n = hours.val.length)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 10000) (hvalid : InRange hours.val), ∃ (ans : Std.I64), longest_wpi hours = Result.ok ans ∧ IsLongestWpi hours.val n ans.val) := by
  sorry

/-- For every valid input, longest_wpi hours returns a result ans; it does not fail.
  Preconditions: hours is a valid input: n = len(hours), 1 <= n <= 10000, and for every i with 0 <= i < n, 0 <= hours[i] <= 16. -/
theorem spec_2 (hours : Slice Std.I64) (n : Nat) (hn : n = hours.val.length)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 10000) (hvalid : InRange hours.val) :
    ∃ (ans : Std.I64), longest_wpi hours = Result.ok ans := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (hours : Slice Std.I64) (n : Nat) (hn : n = hours.val.length)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 10000) (hvalid : InRange hours.val), ∃ (ans : Std.I64), longest_wpi hours = Result.ok ans) := by
  sorry

/-- Whenever longest_wpi hours returns a result ans, 0 <= ans <= n, where n = len(hours).
  Preconditions: hours is a valid input: n = len(hours), 1 <= n <= 10000, and for every i with 0 <= i < n, 0 <= hours[i] <= 16. -/
theorem spec_3 (hours : Slice Std.I64) (n : Nat) (hn : n = hours.val.length)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 10000) (hvalid : InRange hours.val) :
    ∀ (ans : Std.I64), longest_wpi hours = Result.ok ans → 0 ≤ ans.val ∧ ans.val ≤ (n : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (hours : Slice Std.I64) (n : Nat) (hn : n = hours.val.length)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 10000) (hvalid : InRange hours.val), ∀ (ans : Std.I64), longest_wpi hours = Result.ok ans → 0 ≤ ans.val ∧ ans.val ≤ (n : Int)) := by
  sorry

/-- Whenever longest_wpi hours returns a result ans, ans = 0 if and only if for every i with 0 <= i < n, hours[i] <= 8.
  Preconditions: hours is a valid input: n = len(hours), 1 <= n <= 10000, and for every i with 0 <= i < n, 0 <= hours[i] <= 16. -/
theorem spec_4 (hours : Slice Std.I64) (n : Nat) (hn : n = hours.val.length)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 10000) (hvalid : InRange hours.val) :
    ∀ (ans : Std.I64), longest_wpi hours = Result.ok ans → (ans.val = 0 ↔ AllLight hours.val) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (hours : Slice Std.I64) (n : Nat) (hn : n = hours.val.length)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 10000) (hvalid : InRange hours.val), ∀ (ans : Std.I64), longest_wpi hours = Result.ok ans → (ans.val = 0 ↔ AllLight hours.val)) := by
  sorry

/-- Whenever longest_wpi hours returns a result ans, ans = n, where n = len(hours).
  Preconditions: hours is a valid input: n = len(hours), 1 <= n <= 10000, and for every i with 0 <= i < n, hours[i] > 8. -/
theorem spec_5 (hours : Slice Std.I64) (n : Nat) (hn : n = hours.val.length)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 10000) (hheavy : AllHeavy hours.val) :
    ∀ (ans : Std.I64), longest_wpi hours = Result.ok ans → ans.val = (n : Int) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (hours : Slice Std.I64) (n : Nat) (hn : n = hours.val.length)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 10000) (hheavy : AllHeavy hours.val), ∀ (ans : Std.I64), longest_wpi hours = Result.ok ans → ans.val = (n : Int)) := by
  sorry

/-- Let score(a,b) = sum_{i=a}^{b-1} (1 if hours[i] > 8 else -1) for 0 <= a < b <= n. Whenever longest_wpi hours returns a result ans with ans > 0, there exists an index l such that 0 <= l and l + ans <= n and score(l,l+ans) > 0.
  Preconditions: hours is a valid input: n = len(hours), 1 <= n <= 10000, and for every i with 0 <= i < n, 0 <= hours[i] <= 16. -/
theorem spec_6 (hours : Slice Std.I64) (n : Nat) (hn : n = hours.val.length)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 10000) (hvalid : InRange hours.val) :
    ∀ (ans : Std.I64), longest_wpi hours = Result.ok ans → 0 < ans.val →
      ∃ (l : Nat), l + ans.val.toNat ≤ n ∧ 0 < score hours.val l (l + ans.val.toNat) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (hours : Slice Std.I64) (n : Nat) (hn : n = hours.val.length)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 10000) (hvalid : InRange hours.val), ∀ (ans : Std.I64), longest_wpi hours = Result.ok ans → 0 < ans.val →
      ∃ (l : Nat), l + ans.val.toNat ≤ n ∧ 0 < score hours.val l (l + ans.val.toNat)) := by
  sorry

/-- Let score(a,b) = sum_{i=a}^{b-1} (1 if hours[i] > 8 else -1) for 0 <= a < b <= n. Whenever longest_wpi hours returns a result ans, for every l and L with 0 <= l, L >= 1, and l + L <= n, if score(l,l+L) > 0 then L <= ans.
  Preconditions: hours is a valid input: n = len(hours), 1 <= n <= 10000, and for every i with 0 <= i < n, 0 <= hours[i] <= 16. -/
theorem spec_7 (hours : Slice Std.I64) (n : Nat) (hn : n = hours.val.length)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 10000) (hvalid : InRange hours.val) :
    ∀ (ans : Std.I64), longest_wpi hours = Result.ok ans →
      ∀ (l L : Nat), 1 ≤ L → l + L ≤ n → 0 < score hours.val l (l + L) → (L : Int) ≤ ans.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (hours : Slice Std.I64) (n : Nat) (hn : n = hours.val.length)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 10000) (hvalid : InRange hours.val), ∀ (ans : Std.I64), longest_wpi hours = Result.ok ans →
      ∀ (l L : Nat), 1 ≤ L → l + L ≤ n → 0 < score hours.val l (l + L) → (L : Int) ≤ ans.val) := by
  sorry

/-- Let total = sum_{i=0}^{n-1} (1 if hours[i] > 8 else -1). Whenever longest_wpi hours returns a result ans, ans = n if and only if total > 0.
  Preconditions: hours is a valid input: n = len(hours), 1 <= n <= 10000, and for every i with 0 <= i < n, 0 <= hours[i] <= 16. -/
theorem spec_8 (hours : Slice Std.I64) (n : Nat) (hn : n = hours.val.length)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 10000) (hvalid : InRange hours.val) :
    ∀ (ans : Std.I64), longest_wpi hours = Result.ok ans → (ans.val = (n : Int) ↔ 0 < total hours.val) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (hours : Slice Std.I64) (n : Nat) (hn : n = hours.val.length)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 10000) (hvalid : InRange hours.val), ∀ (ans : Std.I64), longest_wpi hours = Result.ok ans → (ans.val = (n : Int) ↔ 0 < total hours.val)) := by
  sorry

/-- Whenever longest_wpi hours returns a result ans, ans = 1 if hours[0] > 8, and ans = 0 otherwise.
  Preconditions: hours is a valid input, n = len(hours) = 1, and 0 <= hours[0] <= 16. -/
theorem spec_9 (hours : Slice Std.I64) (n : Nat) (hn : n = hours.val.length) (hn1 : n = 1)
    (hvalid : InRange hours.val) :
    ∀ (ans : Std.I64), longest_wpi hours = Result.ok ans →
      ans.val = if 8 < entry hours.val 0 then 1 else 0 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (hours : Slice Std.I64) (n : Nat) (hn : n = hours.val.length) (hn1 : n = 1)
    (hvalid : InRange hours.val), ∀ (ans : Std.I64), longest_wpi hours = Result.ok ans →
      ans.val = if 8 < entry hours.val 0 then 1 else 0) := by
  sorry

/-- Whenever longest_wpi hours returns a result ans, ans = n - 1.
  Preconditions: Let n = len(hours) and define score(a,b) = sum_{i=a}^{b-1} (1 if hours[i] > 8 else -1). Assume hours is valid, n >= 2, (score(0,n-1) > 0 or score(1,n) > 0), and score(0,n) <= 0. -/
theorem spec_10 (hours : Slice Std.I64) (n : Nat) (hn : n = hours.val.length)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 10000) (hvalid : InRange hours.val) (hn3 : 2 ≤ n)
    (hpre : 0 < score hours.val 0 (n - 1) ∨ 0 < score hours.val 1 n)
    (htot : score hours.val 0 n ≤ 0) :
    ∀ (ans : Std.I64), longest_wpi hours = Result.ok ans → ans.val = (n : Int) - 1 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (hours : Slice Std.I64) (n : Nat) (hn : n = hours.val.length)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 10000) (hvalid : InRange hours.val) (hn3 : 2 ≤ n)
    (hpre : 0 < score hours.val 0 (n - 1) ∨ 0 < score hours.val 1 n)
    (htot : score hours.val 0 n ≤ 0), ∀ (ans : Std.I64), longest_wpi hours = Result.ok ans → ans.val = (n : Int) - 1) := by
  sorry

/-- Whenever longest_wpi hours returns a result ans1 and longest_wpi rev returns a result ans2, ans1 = ans2.
  Preconditions: hours is a valid input: n = len(hours), 1 <= n <= 10000, and for every i with 0 <= i < n, 0 <= hours[i] <= 16. Let rev be the list of length n with rev[i] = hours[n-1-i]. -/
theorem spec_11 (hours : Slice Std.I64) (n : Nat) (hn : n = hours.val.length)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 10000) (hvalid : InRange hours.val) :
    ∀ (ans1 ans2 : Std.I64), longest_wpi hours = Result.ok ans1 →
      longest_wpi (rev hours) = Result.ok ans2 → ans1.val = ans2.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (hours : Slice Std.I64) (n : Nat) (hn : n = hours.val.length)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 10000) (hvalid : InRange hours.val), ∀ (ans1 ans2 : Std.I64), longest_wpi hours = Result.ok ans1 →
      longest_wpi (rev hours) = Result.ok ans2 → ans1.val = ans2.val) := by
  sorry

/-- Whenever longest_wpi hours returns a result ans1 and longest_wpi other returns a result ans2, ans1 = ans2.
  Preconditions: hours and other are valid inputs of the same length n, with 1 <= n <= 10000, and for every i with 0 <= i < n, (hours[i] > 8) if and only if (other[i] > 8). -/
theorem spec_12 (hours other : Slice Std.I64) (n : Nat) (hn : n = hours.val.length)
    (hn' : n = other.val.length) (hn1 : 1 ≤ n) (hn2 : n ≤ 10000)
    (hvalid : InRange hours.val) (hvalid' : InRange other.val)
    (hsame : ∀ (i : Nat), i < n → (8 < entry hours.val i ↔ 8 < entry other.val i)) :
    ∀ (ans1 ans2 : Std.I64), longest_wpi hours = Result.ok ans1 →
      longest_wpi other = Result.ok ans2 → ans1.val = ans2.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (hours other : Slice Std.I64) (n : Nat) (hn : n = hours.val.length)
    (hn' : n = other.val.length) (hn1 : 1 ≤ n) (hn2 : n ≤ 10000)
    (hvalid : InRange hours.val) (hvalid' : InRange other.val)
    (hsame : ∀ (i : Nat), i < n → (8 < entry hours.val i ↔ 8 < entry other.val i)), ∀ (ans1 ans2 : Std.I64), longest_wpi hours = Result.ok ans1 →
      longest_wpi other = Result.ok ans2 → ans1.val = ans2.val) := by
  sorry

/-- Whenever longest_wpi hours returns a result ans1 and longest_wpi extended returns a result ans2, ans1 <= ans2.
  Preconditions: hours and extended are valid inputs with n = len(hours), m = len(extended), n <= m, and for every i with 0 <= i < n, extended[i] = hours[i]. -/
theorem spec_13 (hours extended : Slice Std.I64) (n m : Nat)
    (hn : n = hours.val.length) (hm : m = extended.val.length)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 10000) (hm1 : 1 ≤ m) (hm2 : m ≤ 10000)
    (hvalid : InRange hours.val) (hvalid' : InRange extended.val) (hnm : n ≤ m)
    (hprefix : ∀ (i : Nat), i < n → entry extended.val i = entry hours.val i) :
    ∀ (ans1 ans2 : Std.I64), longest_wpi hours = Result.ok ans1 →
      longest_wpi extended = Result.ok ans2 → ans1.val ≤ ans2.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (hours extended : Slice Std.I64) (n m : Nat)
    (hn : n = hours.val.length) (hm : m = extended.val.length)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 10000) (hm1 : 1 ≤ m) (hm2 : m ≤ 10000)
    (hvalid : InRange hours.val) (hvalid' : InRange extended.val) (hnm : n ≤ m)
    (hprefix : ∀ (i : Nat), i < n → entry extended.val i = entry hours.val i), ∀ (ans1 ans2 : Std.I64), longest_wpi hours = Result.ok ans1 →
      longest_wpi extended = Result.ok ans2 → ans1.val ≤ ans2.val) := by
  sorry

/-- Whenever longest_wpi hours returns a result ans, ans = 1.
  Preconditions: hours is a valid input: n = len(hours), 1 <= n <= 10000, for every i with 0 <= i < n, 0 <= hours[i] <= 16, and exactly one index i satisfies hours[i] > 8. -/
theorem spec_14 (hours : Slice Std.I64) (n : Nat) (hn : n = hours.val.length)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 10000) (hvalid : InRange hours.val)
    (huniq : UniqueHeavy hours.val) :
    ∀ (ans : Std.I64), longest_wpi hours = Result.ok ans → ans.val = 1 := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (hours : Slice Std.I64) (n : Nat) (hn : n = hours.val.length)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 10000) (hvalid : InRange hours.val)
    (huniq : UniqueHeavy hours.val), ∀ (ans : Std.I64), longest_wpi hours = Result.ok ans → ans.val = 1) := by
  sorry

end AegisSpec.LongestWpi
