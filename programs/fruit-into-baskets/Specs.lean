import Aegis.TotalFruit.Code.Funs

/-!
# Specifications of `Aegis.TotalFruit.total_fruit`

LeetCode problem `fruit-into-baskets`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.TotalFruit

def window (l : List Std.I64) (s m : Nat) : List Std.I64 := (l.drop s).take m

def numDistinct (l : List Std.I64) : Nat := (l.map (fun x => x.val)).dedup.length

def distinctIn (l : List Std.I64) (s m : Nat) : Nat := numDistinct (window l s m)

noncomputable def maxTwoDistinct (l : List Std.I64) : Nat :=
  letI := Classical.propDecidable
  ((Finset.range (l.length + 1)).filter
      (fun m => 1 ≤ m ∧ ∃ s : Nat, s + m ≤ l.length ∧ distinctIn l s m ≤ 2)).sup id

def InRange (fruits : Slice Std.I64) : Prop :=
  ∀ (i : Nat) (h : i < fruits.val.length),
    0 ≤ (fruits.val[i]).val ∧ (fruits.val[i]).val < (fruits.val.length : Int)

/-- Whenever total_fruit(fruits) returns a result r, r is the maximum length of a contiguous segment of fruits whose entries have at most two distinct fruit types. Precisely, for 0 <= l and 0 <= m with l+m <= n, let D(l,m) be the number of distinct values among fruits[l], fruits[l+1], ..., fruits[l+m-1]. Then r = max { m | 1 <= m <= n and there exists l such that 0 <= l <= n-m and D(l,m) <= 2 }.
  Preconditions: Let n = len(fruits). 1 <= n <= 100000, and for every i with 0 <= i < n, 0 <= fruits[i] < n. -/
theorem spec_1 (fruits : Slice Std.I64) (r : Std.I64)
    (h_len_lo : 1 ≤ fruits.val.length) (h_len_hi : fruits.val.length ≤ 100000)
    (h_entries : InRange fruits)
    (h : Aegis.TotalFruit.total_fruit fruits = ok r) :
    r.val = (maxTwoDistinct fruits.val : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (fruits : Slice Std.I64) (r : Std.I64)
    (h_len_lo : 1 ≤ fruits.val.length) (h_len_hi : fruits.val.length ≤ 100000)
    (h_entries : InRange fruits)
    (h : Aegis.TotalFruit.total_fruit fruits = ok r), r.val = (maxTwoDistinct fruits.val : Int)) := by
  sorry

/-- For every fruits satisfying these preconditions, total_fruit(fruits) returns a result r; it does not fail, panic, go out of bounds, or overflow.
  Preconditions: Let n = len(fruits). 1 <= n <= 100000, and for every i with 0 <= i < n, 0 <= fruits[i] < n. -/
theorem spec_2 (fruits : Slice Std.I64)
    (h_len_lo : 1 ≤ fruits.val.length) (h_len_hi : fruits.val.length ≤ 100000)
    (h_entries : InRange fruits) :
    ∃ r : Std.I64, Aegis.TotalFruit.total_fruit fruits = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (fruits : Slice Std.I64)
    (h_len_lo : 1 ≤ fruits.val.length) (h_len_hi : fruits.val.length ≤ 100000)
    (h_entries : InRange fruits), ∃ r : Std.I64, Aegis.TotalFruit.total_fruit fruits = ok r) := by
  sorry

/-- Whenever total_fruit(fruits) returns a result r, 1 <= r <= len(fruits).
  Preconditions: Let n = len(fruits). 1 <= n <= 100000, and for every i with 0 <= i < n, 0 <= fruits[i] < n. -/
theorem spec_3 (fruits : Slice Std.I64) (r : Std.I64)
    (h_len_lo : 1 ≤ fruits.val.length) (h_len_hi : fruits.val.length ≤ 100000)
    (h_entries : InRange fruits)
    (h : Aegis.TotalFruit.total_fruit fruits = ok r) :
    1 ≤ r.val ∧ r.val ≤ (fruits.val.length : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (fruits : Slice Std.I64) (r : Std.I64)
    (h_len_lo : 1 ≤ fruits.val.length) (h_len_hi : fruits.val.length ≤ 100000)
    (h_entries : InRange fruits)
    (h : Aegis.TotalFruit.total_fruit fruits = ok r), 1 ≤ r.val ∧ r.val ≤ (fruits.val.length : Int)) := by
  sorry

/-- Whenever total_fruit(fruits) returns a result r, there exists an integer l such that 0 <= l, l+r <= len(fruits), and the segment fruits[l], fruits[l+1], ..., fruits[l+r-1] contains at most two distinct fruit types, i.e. the set of values in that segment has cardinality at most 2.
  Preconditions: Let n = len(fruits). 1 <= n <= 100000, and for every i with 0 <= i < n, 0 <= fruits[i] < n. -/
theorem spec_4 (fruits : Slice Std.I64) (r : Std.I64)
    (h_len_lo : 1 ≤ fruits.val.length) (h_len_hi : fruits.val.length ≤ 100000)
    (h_entries : InRange fruits)
    (h : Aegis.TotalFruit.total_fruit fruits = ok r) :
    ∃ l : Nat,
      (l : Int) + r.val ≤ (fruits.val.length : Int) ∧ distinctIn fruits.val l r.val.toNat ≤ 2 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (fruits : Slice Std.I64) (r : Std.I64)
    (h_len_lo : 1 ≤ fruits.val.length) (h_len_hi : fruits.val.length ≤ 100000)
    (h_entries : InRange fruits)
    (h : Aegis.TotalFruit.total_fruit fruits = ok r), ∃ l : Nat,
      (l : Int) + r.val ≤ (fruits.val.length : Int) ∧ distinctIn fruits.val l r.val.toNat ≤ 2) := by
  sorry

/-- Whenever total_fruit(fruits) returns a result r, for every integer l and m with 0 <= l, r < m, and l+m <= len(fruits), the segment fruits[l], fruits[l+1], ..., fruits[l+m-1] contains at least three distinct fruit types.
  Preconditions: Let n = len(fruits). 1 <= n <= 100000, and for every i with 0 <= i < n, 0 <= fruits[i] < n. -/
theorem spec_5 (fruits : Slice Std.I64) (r : Std.I64)
    (h_len_lo : 1 ≤ fruits.val.length) (h_len_hi : fruits.val.length ≤ 100000)
    (h_entries : InRange fruits)
    (h : Aegis.TotalFruit.total_fruit fruits = ok r) :
    ∀ (l m : Nat), r.val < (m : Int) → l + m ≤ fruits.val.length →
      3 ≤ distinctIn fruits.val l m := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (fruits : Slice Std.I64) (r : Std.I64)
    (h_len_lo : 1 ≤ fruits.val.length) (h_len_hi : fruits.val.length ≤ 100000)
    (h_entries : InRange fruits)
    (h : Aegis.TotalFruit.total_fruit fruits = ok r), ∀ (l m : Nat), r.val < (m : Int) → l + m ≤ fruits.val.length →
      3 ≤ distinctIn fruits.val l m) := by
  sorry

/-- Whenever total_fruit(fruits) returns a result r, r = len(fruits).
  Preconditions: Let n = len(fruits). 2 <= n <= 100000, for every i with 0 <= i < n, 0 <= fruits[i] < n, and the set {fruits[0], fruits[1], ..., fruits[n-1]} has cardinality at most 2. -/
theorem spec_6 (fruits : Slice Std.I64) (r : Std.I64)
    (h_len_lo : 2 ≤ fruits.val.length) (h_len_hi : fruits.val.length ≤ 100000)
    (h_entries : InRange fruits) (h_two : numDistinct fruits.val ≤ 2)
    (h : Aegis.TotalFruit.total_fruit fruits = ok r) :
    r.val = (fruits.val.length : Int) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (fruits : Slice Std.I64) (r : Std.I64)
    (h_len_lo : 2 ≤ fruits.val.length) (h_len_hi : fruits.val.length ≤ 100000)
    (h_entries : InRange fruits) (h_two : numDistinct fruits.val ≤ 2)
    (h : Aegis.TotalFruit.total_fruit fruits = ok r), r.val = (fruits.val.length : Int)) := by
  sorry

/-- Whenever total_fruit(fruits) returns a result r, r < len(fruits).
  Preconditions: Let n = len(fruits). 1 <= n <= 100000, for every i with 0 <= i < n, 0 <= fruits[i] < n, and the set {fruits[0], fruits[1], ..., fruits[n-1]} has cardinality at least 3. -/
theorem spec_7 (fruits : Slice Std.I64) (r : Std.I64)
    (h_len_lo : 1 ≤ fruits.val.length) (h_len_hi : fruits.val.length ≤ 100000)
    (h_entries : InRange fruits) (h_three : 3 ≤ numDistinct fruits.val)
    (h : Aegis.TotalFruit.total_fruit fruits = ok r) :
    r.val < (fruits.val.length : Int) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (fruits : Slice Std.I64) (r : Std.I64)
    (h_len_lo : 1 ≤ fruits.val.length) (h_len_hi : fruits.val.length ≤ 100000)
    (h_entries : InRange fruits) (h_three : 3 ≤ numDistinct fruits.val)
    (h : Aegis.TotalFruit.total_fruit fruits = ok r), r.val < (fruits.val.length : Int)) := by
  sorry

/-- Whenever total_fruit(fruits) returns a result r, r >= 2.
  Preconditions: Let n = len(fruits). 2 <= n <= 100000, and for every i with 0 <= i < n, 0 <= fruits[i] < n. -/
theorem spec_8 (fruits : Slice Std.I64) (r : Std.I64)
    (h_len_lo : 2 ≤ fruits.val.length) (h_len_hi : fruits.val.length ≤ 100000)
    (h_entries : InRange fruits)
    (h : Aegis.TotalFruit.total_fruit fruits = ok r) :
    2 ≤ r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (fruits : Slice Std.I64) (r : Std.I64)
    (h_len_lo : 2 ≤ fruits.val.length) (h_len_hi : fruits.val.length ≤ 100000)
    (h_entries : InRange fruits)
    (h : Aegis.TotalFruit.total_fruit fruits = ok r), 2 ≤ r.val) := by
  sorry

/-- Whenever total_fruit(fruits) returns r and total_fruit(g) returns r', r = r'.
  Preconditions: Let n = len(fruits). 1 <= n <= 100000, and for every i with 0 <= i < n, 0 <= fruits[i] < n. Let g be the reversal of fruits, so len(g) = n and g[i] = fruits[n-1-i] for every 0 <= i < n. -/
theorem spec_9 (fruits g : Slice Std.I64) (r r' : Std.I64)
    (h_len_lo : 1 ≤ fruits.val.length) (h_len_hi : fruits.val.length ≤ 100000)
    (h_entries : InRange fruits)
    (hg : g.val = fruits.val.reverse)
    (hr : Aegis.TotalFruit.total_fruit fruits = ok r)
    (hr' : Aegis.TotalFruit.total_fruit g = ok r') :
    r = r' := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (fruits g : Slice Std.I64) (r r' : Std.I64)
    (h_len_lo : 1 ≤ fruits.val.length) (h_len_hi : fruits.val.length ≤ 100000)
    (h_entries : InRange fruits)
    (hg : g.val = fruits.val.reverse)
    (hr : Aegis.TotalFruit.total_fruit fruits = ok r)
    (hr' : Aegis.TotalFruit.total_fruit g = ok r'), r = r') := by
  sorry

/-- Whenever total_fruit(fruits) returns r and total_fruit(g) returns r', r' >= r.
  Preconditions: Let n = len(fruits). 1 <= n <= 99999, and for every i with 0 <= i < n, 0 <= fruits[i] < n. Let x be an integer with 0 <= x < n+1, and let g be the slice of length n+1 with g[i] = fruits[i] for 0 <= i < n and g[n] = x. -/
theorem spec_10 (fruits g : Slice Std.I64) (x r r' : Std.I64)
    (h_len_lo : 1 ≤ fruits.val.length) (h_len_hi : fruits.val.length ≤ 99999)
    (h_entries : InRange fruits)
    (hx_lo : 0 ≤ x.val) (hx_hi : x.val < (fruits.val.length : Int) + 1)
    (hg : g.val = fruits.val ++ [x])
    (hr : Aegis.TotalFruit.total_fruit fruits = ok r)
    (hr' : Aegis.TotalFruit.total_fruit g = ok r') :
    r.val ≤ r'.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (fruits g : Slice Std.I64) (x r r' : Std.I64)
    (h_len_lo : 1 ≤ fruits.val.length) (h_len_hi : fruits.val.length ≤ 99999)
    (h_entries : InRange fruits)
    (hx_lo : 0 ≤ x.val) (hx_hi : x.val < (fruits.val.length : Int) + 1)
    (hg : g.val = fruits.val ++ [x])
    (hr : Aegis.TotalFruit.total_fruit fruits = ok r)
    (hr' : Aegis.TotalFruit.total_fruit g = ok r'), r.val ≤ r'.val) := by
  sorry

/-- Whenever total_fruit(fruits) returns r and total_fruit(g) returns r', r' <= r + 1.
  Preconditions: Let n = len(fruits). 1 <= n <= 99999, and for every i with 0 <= i < n, 0 <= fruits[i] < n. Let x be an integer with 0 <= x < n+1, and let g be the slice of length n+1 with g[i] = fruits[i] for 0 <= i < n and g[n] = x. -/
theorem spec_11 (fruits g : Slice Std.I64) (x r r' : Std.I64)
    (h_len_lo : 1 ≤ fruits.val.length) (h_len_hi : fruits.val.length ≤ 99999)
    (h_entries : InRange fruits)
    (hx_lo : 0 ≤ x.val) (hx_hi : x.val < (fruits.val.length : Int) + 1)
    (hg : g.val = fruits.val ++ [x])
    (hr : Aegis.TotalFruit.total_fruit fruits = ok r)
    (hr' : Aegis.TotalFruit.total_fruit g = ok r') :
    r'.val ≤ r.val + 1 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (fruits g : Slice Std.I64) (x r r' : Std.I64)
    (h_len_lo : 1 ≤ fruits.val.length) (h_len_hi : fruits.val.length ≤ 99999)
    (h_entries : InRange fruits)
    (hx_lo : 0 ≤ x.val) (hx_hi : x.val < (fruits.val.length : Int) + 1)
    (hg : g.val = fruits.val ++ [x])
    (hr : Aegis.TotalFruit.total_fruit fruits = ok r)
    (hr' : Aegis.TotalFruit.total_fruit g = ok r'), r'.val ≤ r.val + 1) := by
  sorry

end AegisSpec.TotalFruit
