import Aegis.MinFlipsMonoIncr.Code.Funs

/-!
# Specifications of `Aegis.MinFlipsMonoIncr.min_flips_mono_incr`

LeetCode problem `flip-string-to-monotone-increasing`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinFlipsMonoIncr

  abbrev minFlips : Slice Std.U8 → Result Std.I64 :=
    _root_.Aegis.MinFlipsMonoIncr.min_flips_mono_incr

  def ones (l : List Std.U8) : Nat :=
    (l.filter (fun b => b.val = 49)).length

  def zeros (l : List Std.U8) : Nat :=
    (l.filter (fun b => b.val = 48)).length

  def splitCost (l : List Std.U8) (k : Nat) : Nat :=
    ones (l.take k) + zeros (l.drop k)

  def minSplitCostFrom (l : List Std.U8) : Nat → Nat
    | 0 => splitCost l 0
    | k + 1 => min (splitCost l (k + 1)) (minSplitCostFrom l k)

  def minSplitCost (l : List Std.U8) : Nat :=
    minSplitCostFrom l l.length

  def IsBinary (l : List Std.U8) : Prop :=
    ∀ i, i < l.length → l[i]? = some 48#u8 ∨ l[i]? = some 49#u8

  def IsMonoIncreasing (l : List Std.U8) : Prop :=
    ¬ ∃ i j, i < j ∧ j < l.length ∧ l[i]? = some 49#u8 ∧ l[j]? = some 48#u8

  def targetByte (a i : Nat) : Std.U8 :=
    if i < a then 48#u8 else 49#u8

  def flipsToTarget (l : List Std.U8) (a : Nat) : Nat :=
    (l.zipIdx.filter (fun p : Std.U8 × Nat => p.1.val ≠ (targetByte a p.2).val)).length

  /-- The function returns a result r and r = min_{k=0..n} ( ones(s[0..k]) + zeros(s[k..n]) ), where ones(x) is the number of indices i with x[i] = 49 and zeros(x) is the number of indices i with x[i] = 48. Here s[0..k] denotes the prefix of length k (indices 0 <= i < k) and s[k..n] denotes the suffix of length n-k (indices k <= i < n).
    Preconditions: s is a slice of U8 with length n = len(s). 1 <= n <= 100000. For every i with 0 <= i < n, s[i] is either 48 (ASCII '0') or 49 (ASCII '1'). -/
  theorem spec_1 (s : Slice Std.U8) (n : Nat)
      (hn : n = (Slice.len s).val) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hbin : IsBinary s.val) :
      ∃ r : Std.I64, minFlips s = ok r ∧ r.val = ((minSplitCost s.val : Nat) : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s : Slice Std.U8) (n : Nat)
        (hn : n = (Slice.len s).val) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hbin : IsBinary s.val), ∃ r : Std.I64, minFlips s = ok r ∧ r.val = ((minSplitCost s.val : Nat) : Int)) := by
    sorry

  /-- For every input s satisfying the preconditions, the function returns a result r (it does not fail).
    Preconditions: s is a slice of U8 with length n = len(s). 1 <= n <= 100000. For every i with 0 <= i < n, s[i] is either 48 (ASCII '0') or 49 (ASCII '1'). -/
  theorem spec_2 (s : Slice Std.U8) (n : Nat)
      (hn : n = (Slice.len s).val) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hbin : IsBinary s.val) :
      ∃ r : Std.I64, minFlips s = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s : Slice Std.U8) (n : Nat)
        (hn : n = (Slice.len s).val) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hbin : IsBinary s.val), ∃ r : Std.I64, minFlips s = ok r) := by
    sorry

  /-- If the function returns r on s, then 0 <= r <= n.
    Preconditions: s is a slice of U8 with length n = len(s). 1 <= n <= 100000. For every i with 0 <= i < n, s[i] is either 48 (ASCII '0') or 49 (ASCII '1'). -/
  theorem spec_3 (s : Slice Std.U8) (n : Nat)
      (hn : n = (Slice.len s).val) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hbin : IsBinary s.val) (r : Std.I64) (hr : minFlips s = ok r) :
      0 ≤ r.val ∧ r.val ≤ (n : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s : Slice Std.U8) (n : Nat)
        (hn : n = (Slice.len s).val) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hbin : IsBinary s.val) (r : Std.I64) (hr : minFlips s = ok r), 0 ≤ r.val ∧ r.val ≤ (n : Int)) := by
    sorry

  /-- If the function returns r on s, then r <= min(ones(s), zeros(s)), where ones(s) is the number of indices i with s[i] = 49 and zeros(s) is the number of indices i with s[i] = 48.
    Preconditions: s is a slice of U8 with length n = len(s). 1 <= n <= 100000. For every i with 0 <= i < n, s[i] is either 48 (ASCII '0') or 49 (ASCII '1'). -/
  theorem spec_4 (s : Slice Std.U8) (n : Nat)
      (hn : n = (Slice.len s).val) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hbin : IsBinary s.val) (r : Std.I64) (hr : minFlips s = ok r) :
      r.val ≤ ((min (ones s.val) (zeros s.val) : Nat) : Int) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s : Slice Std.U8) (n : Nat)
        (hn : n = (Slice.len s).val) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hbin : IsBinary s.val) (r : Std.I64) (hr : minFlips s = ok r), r.val ≤ ((min (ones s.val) (zeros s.val) : Nat) : Int)) := by
    sorry

  /-- If the function returns r on s, then r = 0 if and only if s is monotone increasing, i.e., there do not exist indices i and j with 0 <= i < j < n, s[i] = 49, and s[j] = 48.
    Preconditions: s is a slice of U8 with length n = len(s). 1 <= n <= 100000. For every i with 0 <= i < n, s[i] is either 48 (ASCII '0') or 49 (ASCII '1'). -/
  theorem spec_5 (s : Slice Std.U8) (n : Nat)
      (hn : n = (Slice.len s).val) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hbin : IsBinary s.val) (r : Std.I64) (hr : minFlips s = ok r) :
      r.val = 0 ↔ IsMonoIncreasing s.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s : Slice Std.U8) (n : Nat)
        (hn : n = (Slice.len s).val) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hbin : IsBinary s.val) (r : Std.I64) (hr : minFlips s = ok r), r.val = 0 ↔ IsMonoIncreasing s.val) := by
    sorry

  /-- If there exists an integer a with 0 <= a <= n such that for all i with 0 <= i < a we have s[i] = 49, and for all i with a <= i < n we have s[i] = 48 (so s = 1^a 0^{n-a}), then the result r of the function on s satisfies r = min(a, n-a).
    Preconditions: s is a slice of U8 with length n = len(s). 1 <= n <= 100000. For every i with 0 <= i < n, s[i] is either 48 (ASCII '0') or 49 (ASCII '1'). -/
  theorem spec_6 (s : Slice Std.U8) (n : Nat)
      (hn : n = (Slice.len s).val) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hbin : IsBinary s.val) (a : Nat) (ha : a ≤ n)
      (hpre : ∀ i, i < a → s.val[i]? = some 49#u8)
      (hsuf : ∀ i, a ≤ i → i < n → s.val[i]? = some 48#u8)
      (r : Std.I64) (hr : minFlips s = ok r) :
      r.val = ((min a (n - a) : Nat) : Int) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s : Slice Std.U8) (n : Nat)
        (hn : n = (Slice.len s).val) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hbin : IsBinary s.val) (a : Nat) (ha : a ≤ n)
        (hpre : ∀ i, i < a → s.val[i]? = some 49#u8)
        (hsuf : ∀ i, a ≤ i → i < n → s.val[i]? = some 48#u8)
        (r : Std.I64) (hr : minFlips s = ok r), r.val = ((min a (n - a) : Nat) : Int)) := by
    sorry

  /-- If the function returns r on s and returns r' on t, then r = r'.
    Preconditions: s is a slice of U8 with length n = len(s). 1 <= n < 100000. For every i with 0 <= i < n, s[i] is either 48 (ASCII '0') or 49 (ASCII '1'). Let t be the slice of U8 of length n+1 with t[i] = s[i] for 0 <= i < n and t[n] = 49. -/
  theorem spec_7 (s t : Slice Std.U8) (n : Nat)
      (hn : n = (Slice.len s).val) (hn1 : 1 ≤ n) (hn2 : n < 100000)
      (hbin : IsBinary s.val) (ht : t.val = s.val ++ [49#u8])
      (r r' : Std.I64) (hr : minFlips s = ok r) (hr' : minFlips t = ok r') :
      r = r' := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s t : Slice Std.U8) (n : Nat)
        (hn : n = (Slice.len s).val) (hn1 : 1 ≤ n) (hn2 : n < 100000)
        (hbin : IsBinary s.val) (ht : t.val = s.val ++ [49#u8])
        (r r' : Std.I64) (hr : minFlips s = ok r) (hr' : minFlips t = ok r'), r = r') := by
    sorry

  /-- If the function returns r on s and returns r' on t, then |r - r'| <= 1.
    Preconditions: s and t are slices of U8 of the same length n, 1 <= n <= 100000. Both are valid binary strings: for every i with 0 <= i < n, s[i] and t[i] are each either 48 (ASCII '0') or 49 (ASCII '1'). They differ in exactly one position: there exists exactly one index i with 0 <= i < n such that s[i] != t[i]. -/
  theorem spec_8 (s t : Slice Std.U8) (n : Nat)
      (hsn : n = (Slice.len s).val) (htn : n = (Slice.len t).val)
      (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hsbin : IsBinary s.val) (htbin : IsBinary t.val)
      (hdiff : ∃! i : Nat, i < n ∧ s.val[i]? ≠ t.val[i]?)
      (r r' : Std.I64) (hr : minFlips s = ok r) (hr' : minFlips t = ok r') :
      |r.val - r'.val| ≤ 1 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s t : Slice Std.U8) (n : Nat)
        (hsn : n = (Slice.len s).val) (htn : n = (Slice.len t).val)
        (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hsbin : IsBinary s.val) (htbin : IsBinary t.val)
        (hdiff : ∃! i : Nat, i < n ∧ s.val[i]? ≠ t.val[i]?)
        (r r' : Std.I64) (hr : minFlips s = ok r) (hr' : minFlips t = ok r'), |r.val - r'.val| ≤ 1) := by
    sorry

  /-- If the function returns r on s, then there exists an integer a with 0 <= a <= n such that the number of indices i with 0 <= i < n and s[i] != (48 if i < a else 49) is exactly r.
    Preconditions: s is a slice of U8 with length n = len(s). 1 <= n <= 100000. For every i with 0 <= i < n, s[i] is either 48 (ASCII '0') or 49 (ASCII '1'). -/
  theorem spec_9 (s : Slice Std.U8) (n : Nat)
      (hn : n = (Slice.len s).val) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hbin : IsBinary s.val) (r : Std.I64) (hr : minFlips s = ok r) :
      ∃ a : Nat, a ≤ n ∧ ((flipsToTarget s.val a : Nat) : Int) = r.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s : Slice Std.U8) (n : Nat)
        (hn : n = (Slice.len s).val) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hbin : IsBinary s.val) (r : Std.I64) (hr : minFlips s = ok r), ∃ a : Nat, a ≤ n ∧ ((flipsToTarget s.val a : Nat) : Int) = r.val) := by
    sorry

  /-- If the function returns r on s, then for every integer a with 0 <= a <= n, the number of indices i with 0 <= i < n and s[i] != (48 if i < a else 49) is at least r.
    Preconditions: s is a slice of U8 with length n = len(s). 1 <= n <= 100000. For every i with 0 <= i < n, s[i] is either 48 (ASCII '0') or 49 (ASCII '1'). -/
  theorem spec_10 (s : Slice Std.U8) (n : Nat)
      (hn : n = (Slice.len s).val) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hbin : IsBinary s.val) (r : Std.I64) (hr : minFlips s = ok r) :
      ∀ a : Nat, a ≤ n → r.val ≤ ((flipsToTarget s.val a : Nat) : Int) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (s : Slice Std.U8) (n : Nat)
        (hn : n = (Slice.len s).val) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hbin : IsBinary s.val) (r : Std.I64) (hr : minFlips s = ok r), ∀ a : Nat, a ≤ n → r.val ≤ ((flipsToTarget s.val a : Nat) : Int)) := by
    sorry

  /-- Let ans(x) denote the result of the function on a valid binary string x. Then ans(uv) = min( ans(u) + zeros(v), ones(u) + ans(v) ), where zeros(v) is the number of indices j with v[j] = 48 and ones(u) is the number of indices i with u[i] = 49.
    Preconditions: u and v are slices of U8 with lengths m = len(u) and l = len(v). 1 <= m, 1 <= l, and m+l <= 100000. For every i with 0 <= i < m, u[i] is either 48 (ASCII '0') or 49 (ASCII '1'); for every j with 0 <= j < l, v[j] is either 48 (ASCII '0') or 49 (ASCII '1'). Let uv be the concatenation of u and v, of length m+l. -/
  theorem spec_11 (u v : Slice Std.U8) (m l : Nat)
      (hm : m = (Slice.len u).val) (hl : l = (Slice.len v).val)
      (hm1 : 1 ≤ m) (hl1 : 1 ≤ l) (hml : m + l ≤ 100000)
      (hubin : IsBinary u.val) (hvbin : IsBinary v.val)
      (ru rv : Std.I64) (hru : minFlips u = ok ru) (hrv : minFlips v = ok rv)
      (uv : Slice Std.U8) (huv : uv.val = u.val ++ v.val)
      (ruv : Std.I64) (hruv : minFlips uv = ok ruv) :
      ruv.val =
        min (ru.val + ((zeros v.val : Nat) : Int)) (((ones u.val : Nat) : Int) + rv.val) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (u v : Slice Std.U8) (m l : Nat)
        (hm : m = (Slice.len u).val) (hl : l = (Slice.len v).val)
        (hm1 : 1 ≤ m) (hl1 : 1 ≤ l) (hml : m + l ≤ 100000)
        (hubin : IsBinary u.val) (hvbin : IsBinary v.val)
        (ru rv : Std.I64) (hru : minFlips u = ok ru) (hrv : minFlips v = ok rv)
        (uv : Slice Std.U8) (huv : uv.val = u.val ++ v.val)
        (ruv : Std.I64) (hruv : minFlips uv = ok ruv), ruv.val =
          min (ru.val + ((zeros v.val : Nat) : Int)) (((ones u.val : Nat) : Int) + rv.val)) := by
    sorry

  end AegisSpec.MinFlipsMonoIncr
