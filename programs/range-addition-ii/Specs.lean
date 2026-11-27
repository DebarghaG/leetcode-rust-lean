import Aegis.MaxCount.Code.Funs

/-!
# Specifications of `Aegis.MaxCount.max_count`

LeetCode problem `range-addition-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.MaxCount (max_count)

  namespace AegisSpec.MaxCount

  def opsList (ops : Slice (alloc.vec.Vec Std.I64)) : List (List ℤ) :=
    ops.val.map (fun v => v.val.map (fun x => x.val))

  def listMin : List ℤ → ℤ
    | [] => 0
    | x :: xs => xs.foldr min x

  def cntList (l : List (List ℤ)) (x y : ℤ) : ℕ :=
    l.countP (fun o => decide (x < o.getD 0 0 ∧ y < o.getD 1 0))

  def cnt (ops : Slice (alloc.vec.Vec Std.I64)) (x y : ℤ) : ℕ := cntList (opsList ops) x y

  def minAList (l : List (List ℤ)) : ℤ := listMin (l.map (fun o => o.getD 0 0))

  def minBList (l : List (List ℤ)) : ℤ := listMin (l.map (fun o => o.getD 1 0))

  def minA (ops : Slice (alloc.vec.Vec Std.I64)) : ℤ := minAList (opsList ops)

  def minB (ops : Slice (alloc.vec.Vec Std.I64)) : ℤ := minBList (opsList ops)

  def region (m n : ℤ) : List (ℤ × ℤ) :=
    (List.range m.toNat).flatMap fun x =>
      (List.range n.toNat).map fun y => ((x : ℤ), (y : ℤ))

  def maxCntList (m n : ℤ) (l : List (List ℤ)) : ℕ :=
    ((region m n).map (fun p => cntList l p.1 p.2)).foldr max 0

  def maxCnt (m n : ℤ) (ops : Slice (alloc.vec.Vec Std.I64)) : ℕ := maxCntList m n (opsList ops)

  def countCntList (m n : ℤ) (l : List (List ℤ)) (k : ℕ) : ℕ :=
    ((region m n).filter (fun p => cntList l p.1 p.2 = k)).length

  def countCnt (m n : ℤ) (ops : Slice (alloc.vec.Vec Std.I64)) (k : ℕ) : ℕ :=
    countCntList m n (opsList ops) k

  def countMax (m n : ℤ) (ops : Slice (alloc.vec.Vec Std.I64)) : ℕ :=
    countCnt m n ops (maxCnt m n ops)

  /-- For 0 <= x < m and 0 <= y < n, let cnt(x,y) be the number of indices i with 0 <= i < len(ops) such that x < ops[i][0] and y < ops[i][1]. Let maxcnt be the maximum of cnt(x,y) over all 0 <= x < m and 0 <= y < n. The function returns a result r, and r is the number of pairs (x,y) with 0 <= x < m and 0 <= y < n such that cnt(x,y) = maxcnt.
    Preconditions: m and n are integers with 1 <= m <= 40000 and 1 <= n <= 40000; ops is a slice of vectors; len(ops) <= 10000; for every i with 0 <= i < len(ops), ops[i] has length 2, and 1 <= ops[i][0] <= m and 1 <= ops[i][1] <= n. -/
  theorem spec_1 (m n : Std.I64) (ops : Slice (alloc.vec.Vec Std.I64))
      (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 40000)
      (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 40000)
      (hlen : ops.val.length ≤ 10000)
      (hops : ∀ (i : ℕ) (hi : i < ops.val.length),
        (ops.val[i]'hi).val.length = 2 ∧
        1 ≤ ((ops.val[i]'hi).val[0]!).val ∧ ((ops.val[i]'hi).val[0]!).val ≤ m.val ∧
        1 ≤ ((ops.val[i]'hi).val[1]!).val ∧ ((ops.val[i]'hi).val[1]!).val ≤ n.val) :
      ∃ r : Std.I64, max_count m n ops = ok r ∧ r.val = (countMax m.val n.val ops : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (m n : Std.I64) (ops : Slice (alloc.vec.Vec Std.I64))
        (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 40000)
        (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 40000)
        (hlen : ops.val.length ≤ 10000)
        (hops : ∀ (i : ℕ) (hi : i < ops.val.length),
          (ops.val[i]'hi).val.length = 2 ∧
          1 ≤ ((ops.val[i]'hi).val[0]!).val ∧ ((ops.val[i]'hi).val[0]!).val ≤ m.val ∧
          1 ≤ ((ops.val[i]'hi).val[1]!).val ∧ ((ops.val[i]'hi).val[1]!).val ≤ n.val), ∃ r : Std.I64, max_count m n ops = ok r ∧ r.val = (countMax m.val n.val ops : ℤ)) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r; it does not fail due to arithmetic overflow, out-of-bounds access, or panic.
    Preconditions: m and n are integers with 1 <= m <= 40000 and 1 <= n <= 40000; ops is a slice of vectors; len(ops) <= 10000; for every i with 0 <= i < len(ops), ops[i] has length 2, and 1 <= ops[i][0] <= m and 1 <= ops[i][1] <= n. -/
  theorem spec_2 (m n : Std.I64) (ops : Slice (alloc.vec.Vec Std.I64))
      (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 40000)
      (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 40000)
      (hlen : ops.val.length ≤ 10000)
      (hops : ∀ (i : ℕ) (hi : i < ops.val.length),
        (ops.val[i]'hi).val.length = 2 ∧
        1 ≤ ((ops.val[i]'hi).val[0]!).val ∧ ((ops.val[i]'hi).val[0]!).val ≤ m.val ∧
        1 ≤ ((ops.val[i]'hi).val[1]!).val ∧ ((ops.val[i]'hi).val[1]!).val ≤ n.val) :
      ∃ r : Std.I64, max_count m n ops = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (m n : Std.I64) (ops : Slice (alloc.vec.Vec Std.I64))
        (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 40000)
        (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 40000)
        (hlen : ops.val.length ≤ 10000)
        (hops : ∀ (i : ℕ) (hi : i < ops.val.length),
          (ops.val[i]'hi).val.length = 2 ∧
          1 ≤ ((ops.val[i]'hi).val[0]!).val ∧ ((ops.val[i]'hi).val[0]!).val ≤ m.val ∧
          1 ≤ ((ops.val[i]'hi).val[1]!).val ∧ ((ops.val[i]'hi).val[1]!).val ≤ n.val), ∃ r : Std.I64, max_count m n ops = ok r) := by
    sorry

  /-- If len(ops) > 0, then the function returns a result r and r = (min over 0 <= i < len(ops) of ops[i][0]) * (min over 0 <= i < len(ops) of ops[i][1]).
    Preconditions: m and n are integers with 1 <= m <= 40000 and 1 <= n <= 40000; ops is a slice of vectors; len(ops) <= 10000; for every i with 0 <= i < len(ops), ops[i] has length 2, and 1 <= ops[i][0] <= m and 1 <= ops[i][1] <= n. -/
  theorem spec_3 (m n : Std.I64) (ops : Slice (alloc.vec.Vec Std.I64))
      (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 40000)
      (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 40000)
      (hlen : ops.val.length ≤ 10000)
      (hops : ∀ (i : ℕ) (hi : i < ops.val.length),
        (ops.val[i]'hi).val.length = 2 ∧
        1 ≤ ((ops.val[i]'hi).val[0]!).val ∧ ((ops.val[i]'hi).val[0]!).val ≤ m.val ∧
        1 ≤ ((ops.val[i]'hi).val[1]!).val ∧ ((ops.val[i]'hi).val[1]!).val ≤ n.val)
      (hne : 0 < ops.val.length) :
      ∃ r : Std.I64, max_count m n ops = ok r ∧ r.val = minA ops * minB ops := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (m n : Std.I64) (ops : Slice (alloc.vec.Vec Std.I64))
        (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 40000)
        (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 40000)
        (hlen : ops.val.length ≤ 10000)
        (hops : ∀ (i : ℕ) (hi : i < ops.val.length),
          (ops.val[i]'hi).val.length = 2 ∧
          1 ≤ ((ops.val[i]'hi).val[0]!).val ∧ ((ops.val[i]'hi).val[0]!).val ≤ m.val ∧
          1 ≤ ((ops.val[i]'hi).val[1]!).val ∧ ((ops.val[i]'hi).val[1]!).val ≤ n.val)
        (hne : 0 < ops.val.length), ∃ r : Std.I64, max_count m n ops = ok r ∧ r.val = minA ops * minB ops) := by
    sorry

  /-- Whenever the function returns a result r, r <= m * n.
    Preconditions: m and n are integers with 1 <= m <= 40000 and 1 <= n <= 40000; ops is a slice of vectors; len(ops) <= 10000; for every i with 0 <= i < len(ops), ops[i] has length 2, and 1 <= ops[i][0] <= m and 1 <= ops[i][1] <= n. -/
  theorem spec_4 (m n : Std.I64) (ops : Slice (alloc.vec.Vec Std.I64))
      (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 40000)
      (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 40000)
      (hlen : ops.val.length ≤ 10000)
      (hops : ∀ (i : ℕ) (hi : i < ops.val.length),
        (ops.val[i]'hi).val.length = 2 ∧
        1 ≤ ((ops.val[i]'hi).val[0]!).val ∧ ((ops.val[i]'hi).val[0]!).val ≤ m.val ∧
        1 ≤ ((ops.val[i]'hi).val[1]!).val ∧ ((ops.val[i]'hi).val[1]!).val ≤ n.val) :
      ∀ r : Std.I64, max_count m n ops = ok r → r.val ≤ m.val * n.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (m n : Std.I64) (ops : Slice (alloc.vec.Vec Std.I64))
        (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 40000)
        (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 40000)
        (hlen : ops.val.length ≤ 10000)
        (hops : ∀ (i : ℕ) (hi : i < ops.val.length),
          (ops.val[i]'hi).val.length = 2 ∧
          1 ≤ ((ops.val[i]'hi).val[0]!).val ∧ ((ops.val[i]'hi).val[0]!).val ≤ m.val ∧
          1 ≤ ((ops.val[i]'hi).val[1]!).val ∧ ((ops.val[i]'hi).val[1]!).val ≤ n.val), ∀ r : Std.I64, max_count m n ops = ok r → r.val ≤ m.val * n.val) := by
    sorry

  /-- Whenever the function returns a result r, 1 <= r.
    Preconditions: m and n are integers with 1 <= m <= 40000 and 1 <= n <= 40000; ops is a slice of vectors; len(ops) <= 10000; for every i with 0 <= i < len(ops), ops[i] has length 2, and 1 <= ops[i][0] <= m and 1 <= ops[i][1] <= n. -/
  theorem spec_5 (m n : Std.I64) (ops : Slice (alloc.vec.Vec Std.I64))
      (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 40000)
      (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 40000)
      (hlen : ops.val.length ≤ 10000)
      (hops : ∀ (i : ℕ) (hi : i < ops.val.length),
        (ops.val[i]'hi).val.length = 2 ∧
        1 ≤ ((ops.val[i]'hi).val[0]!).val ∧ ((ops.val[i]'hi).val[0]!).val ≤ m.val ∧
        1 ≤ ((ops.val[i]'hi).val[1]!).val ∧ ((ops.val[i]'hi).val[1]!).val ≤ n.val) :
      ∀ r : Std.I64, max_count m n ops = ok r → 1 ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (m n : Std.I64) (ops : Slice (alloc.vec.Vec Std.I64))
        (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 40000)
        (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 40000)
        (hlen : ops.val.length ≤ 10000)
        (hops : ∀ (i : ℕ) (hi : i < ops.val.length),
          (ops.val[i]'hi).val.length = 2 ∧
          1 ≤ ((ops.val[i]'hi).val[0]!).val ∧ ((ops.val[i]'hi).val[0]!).val ≤ m.val ∧
          1 ≤ ((ops.val[i]'hi).val[1]!).val ∧ ((ops.val[i]'hi).val[1]!).val ≤ n.val), ∀ r : Std.I64, max_count m n ops = ok r → 1 ≤ r.val) := by
    sorry

  /-- For 0 <= x < m and 0 <= y < n, let cnt(x,y) be the number of indices i with 0 <= i < len(ops) such that x < ops[i][0] and y < ops[i][1]. Whenever the function returns a result r, for every such x,y we have cnt(x,y) <= cnt(0,0), and r is the number of pairs (x,y) with cnt(x,y) = cnt(0,0).
    Preconditions: m and n are integers with 1 <= m <= 40000 and 1 <= n <= 40000; ops is a slice of vectors; len(ops) <= 10000; for every i with 0 <= i < len(ops), ops[i] has length 2, and 1 <= ops[i][0] <= m and 1 <= ops[i][1] <= n. -/
  theorem spec_6 (m n : Std.I64) (ops : Slice (alloc.vec.Vec Std.I64))
      (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 40000)
      (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 40000)
      (hlen : ops.val.length ≤ 10000)
      (hops : ∀ (i : ℕ) (hi : i < ops.val.length),
        (ops.val[i]'hi).val.length = 2 ∧
        1 ≤ ((ops.val[i]'hi).val[0]!).val ∧ ((ops.val[i]'hi).val[0]!).val ≤ m.val ∧
        1 ≤ ((ops.val[i]'hi).val[1]!).val ∧ ((ops.val[i]'hi).val[1]!).val ≤ n.val) :
      ∀ r : Std.I64, max_count m n ops = ok r →
        (∀ x y : ℤ, 0 ≤ x → x < m.val → 0 ≤ y → y < n.val → cnt ops x y ≤ cnt ops 0 0) ∧
        r.val = (countCnt m.val n.val ops (cnt ops 0 0) : ℤ) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (m n : Std.I64) (ops : Slice (alloc.vec.Vec Std.I64))
        (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 40000)
        (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 40000)
        (hlen : ops.val.length ≤ 10000)
        (hops : ∀ (i : ℕ) (hi : i < ops.val.length),
          (ops.val[i]'hi).val.length = 2 ∧
          1 ≤ ((ops.val[i]'hi).val[0]!).val ∧ ((ops.val[i]'hi).val[0]!).val ≤ m.val ∧
          1 ≤ ((ops.val[i]'hi).val[1]!).val ∧ ((ops.val[i]'hi).val[1]!).val ≤ n.val), ∀ r : Std.I64, max_count m n ops = ok r →
          (∀ x y : ℤ, 0 ≤ x → x < m.val → 0 ≤ y → y < n.val → cnt ops x y ≤ cnt ops 0 0) ∧
          r.val = (countCnt m.val n.val ops (cnt ops 0 0) : ℤ)) := by
    sorry

  /-- If len(ops) > 0, let A = min over 0 <= i < len(ops) of ops[i][0] and B = min over 0 <= i < len(ops) of ops[i][1]. The function returns a result r, and for every x,y with 0 <= x < m and 0 <= y < n, the value cnt(x,y), defined as the number of i with x < ops[i][0] and y < ops[i][1], equals the maximum final matrix value if and only if x < A and y < B. Consequently r = A * B.
    Preconditions: m and n are integers with 1 <= m <= 40000 and 1 <= n <= 40000; ops is a slice of vectors; len(ops) <= 10000; for every i with 0 <= i < len(ops), ops[i] has length 2, and 1 <= ops[i][0] <= m and 1 <= ops[i][1] <= n. -/
  theorem spec_7 (m n : Std.I64) (ops : Slice (alloc.vec.Vec Std.I64))
      (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 40000)
      (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 40000)
      (hlen : ops.val.length ≤ 10000)
      (hops : ∀ (i : ℕ) (hi : i < ops.val.length),
        (ops.val[i]'hi).val.length = 2 ∧
        1 ≤ ((ops.val[i]'hi).val[0]!).val ∧ ((ops.val[i]'hi).val[0]!).val ≤ m.val ∧
        1 ≤ ((ops.val[i]'hi).val[1]!).val ∧ ((ops.val[i]'hi).val[1]!).val ≤ n.val)
      (hne : 0 < ops.val.length) :
      ∃ r : Std.I64, max_count m n ops = ok r ∧
        (∀ x y : ℤ, 0 ≤ x → x < m.val → 0 ≤ y → y < n.val →
          (cnt ops x y = maxCnt m.val n.val ops ↔ x < minA ops ∧ y < minB ops)) ∧
        r.val = minA ops * minB ops := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (m n : Std.I64) (ops : Slice (alloc.vec.Vec Std.I64))
        (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 40000)
        (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 40000)
        (hlen : ops.val.length ≤ 10000)
        (hops : ∀ (i : ℕ) (hi : i < ops.val.length),
          (ops.val[i]'hi).val.length = 2 ∧
          1 ≤ ((ops.val[i]'hi).val[0]!).val ∧ ((ops.val[i]'hi).val[0]!).val ≤ m.val ∧
          1 ≤ ((ops.val[i]'hi).val[1]!).val ∧ ((ops.val[i]'hi).val[1]!).val ≤ n.val)
        (hne : 0 < ops.val.length), ∃ r : Std.I64, max_count m n ops = ok r ∧
          (∀ x y : ℤ, 0 ≤ x → x < m.val → 0 ≤ y → y < n.val →
            (cnt ops x y = maxCnt m.val n.val ops ↔ x < minA ops ∧ y < minB ops)) ∧
          r.val = minA ops * minB ops) := by
    sorry

  /-- If ops2 is obtained from ops by appending the operation [m,n], then whenever the function returns r on (m,n,ops) and r2 on (m,n,ops2), r = r2.
    Preconditions: m and n are integers with 1 <= m <= 40000 and 1 <= n <= 40000; ops is a slice of vectors; len(ops) <= 10000; for every i with 0 <= i < len(ops), ops[i] has length 2, and 1 <= ops[i][0] <= m and 1 <= ops[i][1] <= n. -/
  theorem spec_8 (m n : Std.I64) (ops ops2 : Slice (alloc.vec.Vec Std.I64))
      (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 40000)
      (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 40000)
      (hlen : ops.val.length ≤ 10000)
      (hops : ∀ (i : ℕ) (hi : i < ops.val.length),
        (ops.val[i]'hi).val.length = 2 ∧
        1 ≤ ((ops.val[i]'hi).val[0]!).val ∧ ((ops.val[i]'hi).val[0]!).val ≤ m.val ∧
        1 ≤ ((ops.val[i]'hi).val[1]!).val ∧ ((ops.val[i]'hi).val[1]!).val ≤ n.val)
      (hops2 : opsList ops2 = opsList ops ++ [[m.val, n.val]]) :
      ∀ r r2 : Std.I64,
        max_count m n ops = ok r → max_count m n ops2 = ok r2 → r = r2 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (m n : Std.I64) (ops ops2 : Slice (alloc.vec.Vec Std.I64))
        (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 40000)
        (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 40000)
        (hlen : ops.val.length ≤ 10000)
        (hops : ∀ (i : ℕ) (hi : i < ops.val.length),
          (ops.val[i]'hi).val.length = 2 ∧
          1 ≤ ((ops.val[i]'hi).val[0]!).val ∧ ((ops.val[i]'hi).val[0]!).val ≤ m.val ∧
          1 ≤ ((ops.val[i]'hi).val[1]!).val ∧ ((ops.val[i]'hi).val[1]!).val ≤ n.val)
        (hops2 : opsList ops2 = opsList ops ++ [[m.val, n.val]]), ∀ r r2 : Std.I64,
          max_count m n ops = ok r → max_count m n ops2 = ok r2 → r = r2) := by
    sorry

  /-- Let a,b be integers with 1 <= a <= m and 1 <= b <= n, and let ops2 be obtained from ops by appending the operation [a,b]. If the function returns r on (m,n,ops) and r2 on (m,n,ops2), then r2 <= r.
    Preconditions: m and n are integers with 1 <= m <= 40000 and 1 <= n <= 40000; ops is a slice of vectors; len(ops) <= 10000; for every i with 0 <= i < len(ops), ops[i] has length 2, and 1 <= ops[i][0] <= m and 1 <= ops[i][1] <= n. -/
  theorem spec_9 (m n : Std.I64) (ops ops2 : Slice (alloc.vec.Vec Std.I64))
      (a b : Std.I64)
      (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 40000)
      (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 40000)
      (hlen : ops.val.length ≤ 10000)
      (hops : ∀ (i : ℕ) (hi : i < ops.val.length),
        (ops.val[i]'hi).val.length = 2 ∧
        1 ≤ ((ops.val[i]'hi).val[0]!).val ∧ ((ops.val[i]'hi).val[0]!).val ≤ m.val ∧
        1 ≤ ((ops.val[i]'hi).val[1]!).val ∧ ((ops.val[i]'hi).val[1]!).val ≤ n.val)
      (ha1 : 1 ≤ a.val) (ha2 : a.val ≤ m.val)
      (hb1 : 1 ≤ b.val) (hb2 : b.val ≤ n.val)
      (hops2 : opsList ops2 = opsList ops ++ [[a.val, b.val]]) :
      ∀ r r2 : Std.I64,
        max_count m n ops = ok r → max_count m n ops2 = ok r2 → r2.val ≤ r.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (m n : Std.I64) (ops ops2 : Slice (alloc.vec.Vec Std.I64))
        (a b : Std.I64)
        (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 40000)
        (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 40000)
        (hlen : ops.val.length ≤ 10000)
        (hops : ∀ (i : ℕ) (hi : i < ops.val.length),
          (ops.val[i]'hi).val.length = 2 ∧
          1 ≤ ((ops.val[i]'hi).val[0]!).val ∧ ((ops.val[i]'hi).val[0]!).val ≤ m.val ∧
          1 ≤ ((ops.val[i]'hi).val[1]!).val ∧ ((ops.val[i]'hi).val[1]!).val ≤ n.val)
        (ha1 : 1 ≤ a.val) (ha2 : a.val ≤ m.val)
        (hb1 : 1 ≤ b.val) (hb2 : b.val ≤ n.val)
        (hops2 : opsList ops2 = opsList ops ++ [[a.val, b.val]]), ∀ r r2 : Std.I64,
          max_count m n ops = ok r → max_count m n ops2 = ok r2 → r2.val ≤ r.val) := by
    sorry

  /-- If len(ops) > 0 and m2,n2 are integers with 1 <= m2 <= 40000 and 1 <= n2 <= 40000 such that 1 <= ops[i][0] <= m2 and 1 <= ops[i][1] <= n2 for every i with 0 <= i < len(ops), then whenever the function returns r on (m,n,ops) and r2 on (m2,n2,ops), r = r2.
    Preconditions: m and n are integers with 1 <= m <= 40000 and 1 <= n <= 40000; ops is a slice of vectors; len(ops) <= 10000; for every i with 0 <= i < len(ops), ops[i] has length 2, and 1 <= ops[i][0] <= m and 1 <= ops[i][1] <= n. -/
  theorem spec_10 (m n m2 n2 : Std.I64) (ops : Slice (alloc.vec.Vec Std.I64))
      (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 40000)
      (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 40000)
      (hlen : ops.val.length ≤ 10000)
      (hops : ∀ (i : ℕ) (hi : i < ops.val.length),
        (ops.val[i]'hi).val.length = 2 ∧
        1 ≤ ((ops.val[i]'hi).val[0]!).val ∧ ((ops.val[i]'hi).val[0]!).val ≤ m.val ∧
        1 ≤ ((ops.val[i]'hi).val[1]!).val ∧ ((ops.val[i]'hi).val[1]!).val ≤ n.val)
      (hm2a : 1 ≤ m2.val) (hm2b : m2.val ≤ 40000)
      (hn2a : 1 ≤ n2.val) (hn2b : n2.val ≤ 40000)
      (hne : 0 < ops.val.length)
      (hbound2 : ∀ (i : ℕ) (hi : i < ops.val.length),
        1 ≤ ((ops.val[i]'hi).val[0]!).val ∧ ((ops.val[i]'hi).val[0]!).val ≤ m2.val ∧
        1 ≤ ((ops.val[i]'hi).val[1]!).val ∧ ((ops.val[i]'hi).val[1]!).val ≤ n2.val) :
      ∀ r r2 : Std.I64,
        max_count m n ops = ok r → max_count m2 n2 ops = ok r2 → r = r2 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (m n m2 n2 : Std.I64) (ops : Slice (alloc.vec.Vec Std.I64))
        (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 40000)
        (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 40000)
        (hlen : ops.val.length ≤ 10000)
        (hops : ∀ (i : ℕ) (hi : i < ops.val.length),
          (ops.val[i]'hi).val.length = 2 ∧
          1 ≤ ((ops.val[i]'hi).val[0]!).val ∧ ((ops.val[i]'hi).val[0]!).val ≤ m.val ∧
          1 ≤ ((ops.val[i]'hi).val[1]!).val ∧ ((ops.val[i]'hi).val[1]!).val ≤ n.val)
        (hm2a : 1 ≤ m2.val) (hm2b : m2.val ≤ 40000)
        (hn2a : 1 ≤ n2.val) (hn2b : n2.val ≤ 40000)
        (hne : 0 < ops.val.length)
        (hbound2 : ∀ (i : ℕ) (hi : i < ops.val.length),
          1 ≤ ((ops.val[i]'hi).val[0]!).val ∧ ((ops.val[i]'hi).val[0]!).val ≤ m2.val ∧
          1 ≤ ((ops.val[i]'hi).val[1]!).val ∧ ((ops.val[i]'hi).val[1]!).val ≤ n2.val), ∀ r r2 : Std.I64,
          max_count m n ops = ok r → max_count m2 n2 ops = ok r2 → r = r2) := by
    sorry

  /-- Define ops_sw by ops_sw[i] = [ops[i][1], ops[i][0]] for every 0 <= i < len(ops). Whenever the function returns r on (m,n,ops) and r_sw on (n,m,ops_sw), r = r_sw.
    Preconditions: m and n are integers with 1 <= m <= 40000 and 1 <= n <= 40000; ops is a slice of vectors; len(ops) <= 10000; for every i with 0 <= i < len(ops), ops[i] has length 2, and 1 <= ops[i][0] <= m and 1 <= ops[i][1] <= n. -/
  theorem spec_11 (m n : Std.I64) (ops ops_sw : Slice (alloc.vec.Vec Std.I64))
      (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 40000)
      (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 40000)
      (hlen : ops.val.length ≤ 10000)
      (hops : ∀ (i : ℕ) (hi : i < ops.val.length),
        (ops.val[i]'hi).val.length = 2 ∧
        1 ≤ ((ops.val[i]'hi).val[0]!).val ∧ ((ops.val[i]'hi).val[0]!).val ≤ m.val ∧
        1 ≤ ((ops.val[i]'hi).val[1]!).val ∧ ((ops.val[i]'hi).val[1]!).val ≤ n.val)
      (hsw : opsList ops_sw = (opsList ops).map List.reverse) :
      ∀ r r_sw : Std.I64,
        max_count m n ops = ok r → max_count n m ops_sw = ok r_sw → r = r_sw := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (m n : Std.I64) (ops ops_sw : Slice (alloc.vec.Vec Std.I64))
        (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 40000)
        (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 40000)
        (hlen : ops.val.length ≤ 10000)
        (hops : ∀ (i : ℕ) (hi : i < ops.val.length),
          (ops.val[i]'hi).val.length = 2 ∧
          1 ≤ ((ops.val[i]'hi).val[0]!).val ∧ ((ops.val[i]'hi).val[0]!).val ≤ m.val ∧
          1 ≤ ((ops.val[i]'hi).val[1]!).val ∧ ((ops.val[i]'hi).val[1]!).val ≤ n.val)
        (hsw : opsList ops_sw = (opsList ops).map List.reverse), ∀ r r_sw : Std.I64,
          max_count m n ops = ok r → max_count n m ops_sw = ok r_sw → r = r_sw) := by
    sorry

  /-- Let ops_perm be any list of the same length whose entries are a permutation of the entries of ops. Whenever the function returns r on (m,n,ops) and r_perm on (m,n,ops_perm), r = r_perm.
    Preconditions: m and n are integers with 1 <= m <= 40000 and 1 <= n <= 40000; ops is a slice of vectors; len(ops) <= 10000; for every i with 0 <= i < len(ops), ops[i] has length 2, and 1 <= ops[i][0] <= m and 1 <= ops[i][1] <= n. -/
  theorem spec_12 (m n : Std.I64) (ops ops_perm : Slice (alloc.vec.Vec Std.I64))
      (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 40000)
      (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 40000)
      (hlen : ops.val.length ≤ 10000)
      (hops : ∀ (i : ℕ) (hi : i < ops.val.length),
        (ops.val[i]'hi).val.length = 2 ∧
        1 ≤ ((ops.val[i]'hi).val[0]!).val ∧ ((ops.val[i]'hi).val[0]!).val ≤ m.val ∧
        1 ≤ ((ops.val[i]'hi).val[1]!).val ∧ ((ops.val[i]'hi).val[1]!).val ≤ n.val)
      (hperm : (opsList ops_perm).Perm (opsList ops)) :
      ∀ r r_perm : Std.I64,
        max_count m n ops = ok r → max_count m n ops_perm = ok r_perm → r = r_perm := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (m n : Std.I64) (ops ops_perm : Slice (alloc.vec.Vec Std.I64))
        (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 40000)
        (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 40000)
        (hlen : ops.val.length ≤ 10000)
        (hops : ∀ (i : ℕ) (hi : i < ops.val.length),
          (ops.val[i]'hi).val.length = 2 ∧
          1 ≤ ((ops.val[i]'hi).val[0]!).val ∧ ((ops.val[i]'hi).val[0]!).val ≤ m.val ∧
          1 ≤ ((ops.val[i]'hi).val[1]!).val ∧ ((ops.val[i]'hi).val[1]!).val ≤ n.val)
        (hperm : (opsList ops_perm).Perm (opsList ops)), ∀ r r_perm : Std.I64,
          max_count m n ops = ok r → max_count m n ops_perm = ok r_perm → r = r_perm) := by
    sorry

  /-- The function returns a result r, and r = (if len(ops) = 0 then m * n else (min over 0 <= i < len(ops) of ops[i][0]) * (min over 0 <= i < len(ops) of ops[i][1])).
    Preconditions: m and n are integers with 1 <= m <= 40000 and 1 <= n <= 40000; ops is a slice of vectors; len(ops) <= 10000; for every i with 0 <= i < len(ops), ops[i] has length 2, and 1 <= ops[i][0] <= m and 1 <= ops[i][1] <= n. -/
  theorem spec_13 (m n : Std.I64) (ops : Slice (alloc.vec.Vec Std.I64))
      (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 40000)
      (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 40000)
      (hlen : ops.val.length ≤ 10000)
      (hops : ∀ (i : ℕ) (hi : i < ops.val.length),
        (ops.val[i]'hi).val.length = 2 ∧
        1 ≤ ((ops.val[i]'hi).val[0]!).val ∧ ((ops.val[i]'hi).val[0]!).val ≤ m.val ∧
        1 ≤ ((ops.val[i]'hi).val[1]!).val ∧ ((ops.val[i]'hi).val[1]!).val ≤ n.val) :
      ∃ r : Std.I64, max_count m n ops = ok r ∧
        r.val = (if ops.val.length = 0 then m.val * n.val else minA ops * minB ops) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (m n : Std.I64) (ops : Slice (alloc.vec.Vec Std.I64))
        (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 40000)
        (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 40000)
        (hlen : ops.val.length ≤ 10000)
        (hops : ∀ (i : ℕ) (hi : i < ops.val.length),
          (ops.val[i]'hi).val.length = 2 ∧
          1 ≤ ((ops.val[i]'hi).val[0]!).val ∧ ((ops.val[i]'hi).val[0]!).val ≤ m.val ∧
          1 ≤ ((ops.val[i]'hi).val[1]!).val ∧ ((ops.val[i]'hi).val[1]!).val ≤ n.val), ∃ r : Std.I64, max_count m n ops = ok r ∧
          r.val = (if ops.val.length = 0 then m.val * n.val else minA ops * minB ops)) := by
    sorry

  end AegisSpec.MaxCount
