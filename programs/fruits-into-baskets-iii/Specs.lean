import Aegis.NumOfUnplacedFruits.Code.Funs

/-!
# Specifications of `Aegis.NumOfUnplacedFruits.num_of_unplaced_fruits`

LeetCode problem `fruits-into-baskets-iii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.NumOfUnplacedFruits

  def entry (l : List Std.I64) (i : Nat) : Int :=
    ((l[i]?).map fun v => v.val).getD 0

  def Bounds (l : List Std.I64) : Prop :=
    ∀ i, i < l.length → 1 ≤ entry l i ∧ entry l i ≤ 1000000000

  def minEntry (l : List Std.I64) : Int :=
    ((l.map fun v => v.val).min?).getD 0

  def maxEntry (l : List Std.I64) : Int :=
    ((l.map fun v => v.val).max?).getD 0

  def firstAvailable (baskets : List Std.I64) (used : List Nat) (q : Int) : Option Nat :=
    (List.range baskets.length).find?
      (fun j => decide (q ≤ entry baskets j) && !used.contains j)

  def placeAux (baskets : List Std.I64) (used : List Nat) : List Std.I64 → List (Option Nat)
    | [] => []
    | q :: qs =>
      match firstAvailable baskets used q.val with
      | some j => some j :: placeAux baskets (used ++ [j]) qs
      | none => none :: placeAux baskets used qs

  def place (fruits baskets : List Std.I64) : List (Option Nat) :=
    placeAux baskets [] fruits

  def assigned (p : List (Option Nat)) : List Nat := p.filterMap id

  def numUnplaced (p : List (Option Nat)) : Nat := p.countP (fun x => x.isNone)

  def countGE (l : List Std.I64) (x : Int) : Nat :=
    (l.filter fun v => decide (x ≤ v.val)).length

  def countGT (l : List Std.I64) (y : Int) : Nat :=
    (l.filter fun v => decide (y < v.val)).length

  /-- Define indices b_0, b_1, ..., b_{n-1} recursively in increasing order of i: b_i is the least index j with 0 <= j < n such that baskets[j] >= fruits[i] and j is not equal to b_k for any k < i for which b_k is defined; if no such j exists, b_i is undefined. Let U = { i | 0 <= i < n and b_i is undefined }. Then the function returns a result r and r = |U|, the number of fruit types left unplaced.
    Preconditions: Let n = len(fruits). Assume len(baskets) = n, 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= fruits[i] <= 1000000000 and 1 <= baskets[i] <= 1000000000. -/
  theorem spec_1 (fruits baskets : Slice Std.I64)
      (hlen : baskets.val.length = fruits.val.length)
      (hn : 1 ≤ fruits.val.length) (hn_top : fruits.val.length ≤ 100000)
      (hf : Bounds fruits.val) (hb : Bounds baskets.val) :
      ∃ r, Aegis.NumOfUnplacedFruits.num_of_unplaced_fruits fruits baskets = ok r ∧
        r.val = (numUnplaced (place fruits.val baskets.val) : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (fruits baskets : Slice Std.I64)
        (hlen : baskets.val.length = fruits.val.length)
        (hn : 1 ≤ fruits.val.length) (hn_top : fruits.val.length ≤ 100000)
        (hf : Bounds fruits.val) (hb : Bounds baskets.val), ∃ r, Aegis.NumOfUnplacedFruits.num_of_unplaced_fruits fruits baskets = ok r ∧
          r.val = (numUnplaced (place fruits.val baskets.val) : Int)) := by
    sorry

  /-- The function returns a result r; it does not fail.
    Preconditions: Let n = len(fruits). Assume len(baskets) = n, 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= fruits[i] <= 1000000000 and 1 <= baskets[i] <= 1000000000. -/
  theorem spec_2 (fruits baskets : Slice Std.I64)
      (hlen : baskets.val.length = fruits.val.length)
      (hn : 1 ≤ fruits.val.length) (hn_top : fruits.val.length ≤ 100000)
      (hf : Bounds fruits.val) (hb : Bounds baskets.val) :
      ∃ r, Aegis.NumOfUnplacedFruits.num_of_unplaced_fruits fruits baskets = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (fruits baskets : Slice Std.I64)
        (hlen : baskets.val.length = fruits.val.length)
        (hn : 1 ≤ fruits.val.length) (hn_top : fruits.val.length ≤ 100000)
        (hf : Bounds fruits.val) (hb : Bounds baskets.val), ∃ r, Aegis.NumOfUnplacedFruits.num_of_unplaced_fruits fruits baskets = ok r) := by
    sorry

  /-- The function returns a result r and 0 <= r <= n.
    Preconditions: Let n = len(fruits). Assume len(baskets) = n, 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= fruits[i] <= 1000000000 and 1 <= baskets[i] <= 1000000000. -/
  theorem spec_3 (fruits baskets : Slice Std.I64)
      (hlen : baskets.val.length = fruits.val.length)
      (hn : 1 ≤ fruits.val.length) (hn_top : fruits.val.length ≤ 100000)
      (hf : Bounds fruits.val) (hb : Bounds baskets.val) :
      ∃ r, Aegis.NumOfUnplacedFruits.num_of_unplaced_fruits fruits baskets = ok r ∧
        0 ≤ r.val ∧ r.val ≤ (fruits.val.length : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (fruits baskets : Slice Std.I64)
        (hlen : baskets.val.length = fruits.val.length)
        (hn : 1 ≤ fruits.val.length) (hn_top : fruits.val.length ≤ 100000)
        (hf : Bounds fruits.val) (hb : Bounds baskets.val), ∃ r, Aegis.NumOfUnplacedFruits.num_of_unplaced_fruits fruits baskets = ok r ∧
          0 ≤ r.val ∧ r.val ≤ (fruits.val.length : Int)) := by
    sorry

  /-- The function returns a result r. Let minFruit = min_{0 <= i < n} fruits[i] and maxBasket = max_{0 <= j < n} baskets[j]. Then r = n if and only if minFruit > maxBasket.
    Preconditions: Let n = len(fruits). Assume len(baskets) = n, 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= fruits[i] <= 1000000000 and 1 <= baskets[i] <= 1000000000. -/
  theorem spec_4 (fruits baskets : Slice Std.I64)
      (hlen : baskets.val.length = fruits.val.length)
      (hn : 1 ≤ fruits.val.length) (hn_top : fruits.val.length ≤ 100000)
      (hf : Bounds fruits.val) (hb : Bounds baskets.val) :
      ∃ r, Aegis.NumOfUnplacedFruits.num_of_unplaced_fruits fruits baskets = ok r ∧
        (r.val = (fruits.val.length : Int) ↔
          minEntry fruits.val > maxEntry baskets.val) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (fruits baskets : Slice Std.I64)
        (hlen : baskets.val.length = fruits.val.length)
        (hn : 1 ≤ fruits.val.length) (hn_top : fruits.val.length ≤ 100000)
        (hf : Bounds fruits.val) (hb : Bounds baskets.val), ∃ r, Aegis.NumOfUnplacedFruits.num_of_unplaced_fruits fruits baskets = ok r ∧
          (r.val = (fruits.val.length : Int) ↔
            minEntry fruits.val > maxEntry baskets.val)) := by
    sorry

  /-- The function returns a result r and r = 0.
    Preconditions: Let n = len(fruits). Assume len(baskets) = n, 1 <= n <= 100000, for every i with 0 <= i < n, 1 <= fruits[i] <= 1000000000 and 1 <= baskets[i] <= 1000000000, and additionally min_{0 <= j < n} baskets[j] >= max_{0 <= i < n} fruits[i]. -/
  theorem spec_5 (fruits baskets : Slice Std.I64)
      (hlen : baskets.val.length = fruits.val.length)
      (hn : 1 ≤ fruits.val.length) (hn_top : fruits.val.length ≤ 100000)
      (hf : Bounds fruits.val) (hb : Bounds baskets.val)
      (hmin : maxEntry fruits.val ≤ minEntry baskets.val) :
      ∃ r, Aegis.NumOfUnplacedFruits.num_of_unplaced_fruits fruits baskets = ok r ∧
        r.val = 0 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (fruits baskets : Slice Std.I64)
        (hlen : baskets.val.length = fruits.val.length)
        (hn : 1 ≤ fruits.val.length) (hn_top : fruits.val.length ≤ 100000)
        (hf : Bounds fruits.val) (hb : Bounds baskets.val)
        (hmin : maxEntry fruits.val ≤ minEntry baskets.val), ∃ r, Aegis.NumOfUnplacedFruits.num_of_unplaced_fruits fruits baskets = ok r ∧
          r.val = 0) := by
    sorry

  /-- The function returns a result r and r = 0 if baskets[0] >= fruits[0], otherwise r = 1.
    Preconditions: Let n = len(fruits). Assume len(baskets) = n, n = 1, 1 <= fruits[0] <= 1000000000, and 1 <= baskets[0] <= 1000000000. -/
  theorem spec_6 (fruits baskets : Slice Std.I64)
      (hlen : baskets.val.length = fruits.val.length)
      (hn : fruits.val.length = 1)
      (hf0 : 1 ≤ entry fruits.val 0 ∧ entry fruits.val 0 ≤ 1000000000)
      (hb0 : 1 ≤ entry baskets.val 0 ∧ entry baskets.val 0 ≤ 1000000000) :
      ∃ r, Aegis.NumOfUnplacedFruits.num_of_unplaced_fruits fruits baskets = ok r ∧
        r.val = (if entry baskets.val 0 ≥ entry fruits.val 0 then 0 else 1) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (fruits baskets : Slice Std.I64)
        (hlen : baskets.val.length = fruits.val.length)
        (hn : fruits.val.length = 1)
        (hf0 : 1 ≤ entry fruits.val 0 ∧ entry fruits.val 0 ≤ 1000000000)
        (hb0 : 1 ≤ entry baskets.val 0 ∧ entry baskets.val 0 ≤ 1000000000), ∃ r, Aegis.NumOfUnplacedFruits.num_of_unplaced_fruits fruits baskets = ok r ∧
          r.val = (if entry baskets.val 0 ≥ entry fruits.val 0 then 0 else 1)) := by
    sorry

  /-- Consider the leftmost-available placement process: fruits are processed in increasing index, and each fruit is assigned the least-index basket not already assigned to an earlier fruit whose capacity is at least the fruit quantity, if such a basket exists; otherwise it is unplaced. The function returns a result r, and exactly n - r fruits are assigned a basket, with pairwise distinct assigned basket indices.
    Preconditions: Let n = len(fruits). Assume len(baskets) = n, 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= fruits[i] <= 1000000000 and 1 <= baskets[i] <= 1000000000. -/
  theorem spec_7 (fruits baskets : Slice Std.I64)
      (hlen : baskets.val.length = fruits.val.length)
      (hn : 1 ≤ fruits.val.length) (hn_top : fruits.val.length ≤ 100000)
      (hf : Bounds fruits.val) (hb : Bounds baskets.val) :
      ∃ r, Aegis.NumOfUnplacedFruits.num_of_unplaced_fruits fruits baskets = ok r ∧
        ((assigned (place fruits.val baskets.val)).length : Int) =
          (fruits.val.length : Int) - r.val ∧
        (assigned (place fruits.val baskets.val)).Nodup := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (fruits baskets : Slice Std.I64)
        (hlen : baskets.val.length = fruits.val.length)
        (hn : 1 ≤ fruits.val.length) (hn_top : fruits.val.length ≤ 100000)
        (hf : Bounds fruits.val) (hb : Bounds baskets.val), ∃ r, Aegis.NumOfUnplacedFruits.num_of_unplaced_fruits fruits baskets = ok r ∧
          ((assigned (place fruits.val baskets.val)).length : Int) =
            (fruits.val.length : Int) - r.val ∧
          (assigned (place fruits.val baskets.val)).Nodup) := by
    sorry

  /-- Both calls return results r and r2, and r2 <= r.
    Preconditions: Let n = len(fruits). Assume 1 <= n <= 100000 and for every i with 0 <= i < n, 1 <= fruits[i] <= 1000000000. Let baskets and baskets2 be two slices of length n such that 1 <= baskets[j] <= 1000000000 and 1 <= baskets2[j] <= 1000000000 for every j with 0 <= j < n, and baskets[j] <= baskets2[j] for every such j. Let r be the result of num_of_unplaced_fruits(fruits, baskets) and r2 the result of num_of_unplaced_fruits(fruits, baskets2). -/
  theorem spec_8 (fruits baskets baskets2 : Slice Std.I64)
      (hlen : baskets.val.length = fruits.val.length)
      (hlen2 : baskets2.val.length = fruits.val.length)
      (hn : 1 ≤ fruits.val.length) (hn_top : fruits.val.length ≤ 100000)
      (hf : Bounds fruits.val) (hb : Bounds baskets.val) (hb2 : Bounds baskets2.val)
      (hle : ∀ j, j < fruits.val.length → entry baskets.val j ≤ entry baskets2.val j) :
      ∃ r r2, Aegis.NumOfUnplacedFruits.num_of_unplaced_fruits fruits baskets = ok r ∧
        Aegis.NumOfUnplacedFruits.num_of_unplaced_fruits fruits baskets2 = ok r2 ∧
        r2.val ≤ r.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (fruits baskets baskets2 : Slice Std.I64)
        (hlen : baskets.val.length = fruits.val.length)
        (hlen2 : baskets2.val.length = fruits.val.length)
        (hn : 1 ≤ fruits.val.length) (hn_top : fruits.val.length ≤ 100000)
        (hf : Bounds fruits.val) (hb : Bounds baskets.val) (hb2 : Bounds baskets2.val)
        (hle : ∀ j, j < fruits.val.length → entry baskets.val j ≤ entry baskets2.val j), ∃ r r2, Aegis.NumOfUnplacedFruits.num_of_unplaced_fruits fruits baskets = ok r ∧
          Aegis.NumOfUnplacedFruits.num_of_unplaced_fruits fruits baskets2 = ok r2 ∧
          r2.val ≤ r.val) := by
    sorry

  /-- Both calls return results r and r2, and r <= r2.
    Preconditions: Let n = len(baskets). Assume 1 <= n <= 100000 and for every j with 0 <= j < n, 1 <= baskets[j] <= 1000000000. Let fruits and fruits2 be two slices of length n such that 1 <= fruits[i] <= 1000000000 and 1 <= fruits2[i] <= 1000000000 for every i with 0 <= i < n, and fruits[i] <= fruits2[i] for every such i. Let r be the result of num_of_unplaced_fruits(fruits, baskets) and r2 the result of num_of_unplaced_fruits(fruits2, baskets). -/
  theorem spec_9 (fruits fruits2 baskets : Slice Std.I64)
      (hlen : baskets.val.length = fruits.val.length)
      (hlen2 : baskets.val.length = fruits2.val.length)
      (hn : 1 ≤ baskets.val.length) (hn_top : baskets.val.length ≤ 100000)
      (hb : Bounds baskets.val) (hf : Bounds fruits.val) (hf2 : Bounds fruits2.val)
      (hle : ∀ i, i < baskets.val.length → entry fruits.val i ≤ entry fruits2.val i) :
      ∃ r r2, Aegis.NumOfUnplacedFruits.num_of_unplaced_fruits fruits baskets = ok r ∧
        Aegis.NumOfUnplacedFruits.num_of_unplaced_fruits fruits2 baskets = ok r2 ∧
        r.val ≤ r2.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (fruits fruits2 baskets : Slice Std.I64)
        (hlen : baskets.val.length = fruits.val.length)
        (hlen2 : baskets.val.length = fruits2.val.length)
        (hn : 1 ≤ baskets.val.length) (hn_top : baskets.val.length ≤ 100000)
        (hb : Bounds baskets.val) (hf : Bounds fruits.val) (hf2 : Bounds fruits2.val)
        (hle : ∀ i, i < baskets.val.length → entry fruits.val i ≤ entry fruits2.val i), ∃ r r2, Aegis.NumOfUnplacedFruits.num_of_unplaced_fruits fruits baskets = ok r ∧
          Aegis.NumOfUnplacedFruits.num_of_unplaced_fruits fruits2 baskets = ok r2 ∧
          r.val ≤ r2.val) := by
    sorry

  /-- The function returns a result r, and r = n - c where c = |{ j | 0 <= j < n and baskets[j] >= x }|.
    Preconditions: Let n = len(fruits). Assume len(baskets) = n, 1 <= n <= 100000, for every i with 0 <= i < n, 1 <= fruits[i] <= 1000000000 and 1 <= baskets[i] <= 1000000000, and there exists an integer x such that fruits[i] = x for every i with 0 <= i < n. -/
  theorem spec_10 (fruits baskets : Slice Std.I64)
      (hlen : baskets.val.length = fruits.val.length)
      (hn : 1 ≤ fruits.val.length) (hn_top : fruits.val.length ≤ 100000)
      (hf : Bounds fruits.val) (hb : Bounds baskets.val)
      (x : Int) (hx : ∀ i, i < fruits.val.length → entry fruits.val i = x) :
      ∃ r, Aegis.NumOfUnplacedFruits.num_of_unplaced_fruits fruits baskets = ok r ∧
        r.val = (fruits.val.length : Int) - (countGE baskets.val x : Int) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (fruits baskets : Slice Std.I64)
        (hlen : baskets.val.length = fruits.val.length)
        (hn : 1 ≤ fruits.val.length) (hn_top : fruits.val.length ≤ 100000)
        (hf : Bounds fruits.val) (hb : Bounds baskets.val)
        (x : Int) (hx : ∀ i, i < fruits.val.length → entry fruits.val i = x), ∃ r, Aegis.NumOfUnplacedFruits.num_of_unplaced_fruits fruits baskets = ok r ∧
          r.val = (fruits.val.length : Int) - (countGE baskets.val x : Int)) := by
    sorry

  /-- The function returns a result r, and r = |{ i | 0 <= i < n and fruits[i] > y }|.
    Preconditions: Let n = len(fruits). Assume len(baskets) = n, 1 <= n <= 100000, for every i with 0 <= i < n, 1 <= fruits[i] <= 1000000000 and 1 <= baskets[i] <= 1000000000, and there exists an integer y such that baskets[j] = y for every j with 0 <= j < n. -/
  theorem spec_11 (fruits baskets : Slice Std.I64)
      (hlen : baskets.val.length = fruits.val.length)
      (hn : 1 ≤ fruits.val.length) (hn_top : fruits.val.length ≤ 100000)
      (hf : Bounds fruits.val) (hb : Bounds baskets.val)
      (y : Int) (hy : ∀ j, j < baskets.val.length → entry baskets.val j = y) :
      ∃ r, Aegis.NumOfUnplacedFruits.num_of_unplaced_fruits fruits baskets = ok r ∧
        r.val = (countGT fruits.val y : Int) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (fruits baskets : Slice Std.I64)
        (hlen : baskets.val.length = fruits.val.length)
        (hn : 1 ≤ fruits.val.length) (hn_top : fruits.val.length ≤ 100000)
        (hf : Bounds fruits.val) (hb : Bounds baskets.val)
        (y : Int) (hy : ∀ j, j < baskets.val.length → entry baskets.val j = y), ∃ r, Aegis.NumOfUnplacedFruits.num_of_unplaced_fruits fruits baskets = ok r ∧
          r.val = (countGT fruits.val y : Int)) := by
    sorry

  /-- Both calls return results r and r2, and r = r2.
    Preconditions: Let n = len(fruits). Assume len(baskets) = n, 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= fruits[i] <= 1000000000 and 1 <= baskets[i] <= 1000000000. Let c be an integer. Let fruits2 and baskets2 be slices of length n such that fruits2[i] = fruits[i] + c and baskets2[j] = baskets[j] + c for every i,j with 0 <= i,j < n, and assume both input pairs satisfy the same 1 <= value <= 1000000000 constraints. Let r be the result for (fruits, baskets) and r2 the result for (fruits2, baskets2). -/
  theorem spec_12 (fruits baskets fruits2 baskets2 : Slice Std.I64) (c : Int)
      (hlen : baskets.val.length = fruits.val.length)
      (hlen2 : baskets2.val.length = fruits2.val.length)
      (hlen3 : fruits2.val.length = fruits.val.length)
      (hn : 1 ≤ fruits.val.length) (hn_top : fruits.val.length ≤ 100000)
      (hf : Bounds fruits.val) (hb : Bounds baskets.val)
      (hf2 : Bounds fruits2.val) (hb2 : Bounds baskets2.val)
      (hfc : ∀ i, i < fruits.val.length → entry fruits2.val i = entry fruits.val i + c)
      (hbc : ∀ j, j < baskets.val.length → entry baskets2.val j = entry baskets.val j + c) :
      ∃ r r2, Aegis.NumOfUnplacedFruits.num_of_unplaced_fruits fruits baskets = ok r ∧
        Aegis.NumOfUnplacedFruits.num_of_unplaced_fruits fruits2 baskets2 = ok r2 ∧
        r.val = r2.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (fruits baskets fruits2 baskets2 : Slice Std.I64) (c : Int)
        (hlen : baskets.val.length = fruits.val.length)
        (hlen2 : baskets2.val.length = fruits2.val.length)
        (hlen3 : fruits2.val.length = fruits.val.length)
        (hn : 1 ≤ fruits.val.length) (hn_top : fruits.val.length ≤ 100000)
        (hf : Bounds fruits.val) (hb : Bounds baskets.val)
        (hf2 : Bounds fruits2.val) (hb2 : Bounds baskets2.val)
        (hfc : ∀ i, i < fruits.val.length → entry fruits2.val i = entry fruits.val i + c)
        (hbc : ∀ j, j < baskets.val.length → entry baskets2.val j = entry baskets.val j + c), ∃ r r2, Aegis.NumOfUnplacedFruits.num_of_unplaced_fruits fruits baskets = ok r ∧
          Aegis.NumOfUnplacedFruits.num_of_unplaced_fruits fruits2 baskets2 = ok r2 ∧
          r.val = r2.val) := by
    sorry

  end AegisSpec.NumOfUnplacedFruits
