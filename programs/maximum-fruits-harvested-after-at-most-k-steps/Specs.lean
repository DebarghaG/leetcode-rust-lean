import Aegis.MaxTotalFruits.Code.Funs

/-!
# Specifications of `Aegis.MaxTotalFruits.max_total_fruits`

LeetCode problem `maximum-fruits-harvested-after-at-most-k-steps`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxTotalFruits

abbrev Fruits : Type := Slice (alloc.vec.Vec I64)

def fruitPos (v : alloc.vec.Vec I64) : ℤ := ((v.val[0]?).map IScalar.val).getD 0

def fruitAmt (v : alloc.vec.Vec I64) : ℤ := ((v.val[1]?).map IScalar.val).getD 0

def posAt (fs : Fruits) (i : ℕ) : ℤ := ((fs.val[i]?).map fruitPos).getD 0

def amtAt (fs : Fruits) (i : ℕ) : ℤ := ((fs.val[i]?).map fruitAmt).getD 0

def intDist (x y : ℤ) : ℤ := if x ≤ y then y - x else x - y

def rangeCost (startPos L R : ℤ) : ℤ := (R - L) + min (startPos - L) (R - startPos)

def rangeSum (fs : Fruits) (L R : ℤ) : ℤ :=
  ((List.range fs.val.length).map
    (fun i => if L ≤ posAt fs i ∧ posAt fs i ≤ R then amtAt fs i else 0)).sum

def nearSum (fs : Fruits) (startPos k : ℤ) : ℤ :=
  ((List.range fs.val.length).map
    (fun i => if intDist (posAt fs i) startPos ≤ k then amtAt fs i else 0)).sum

def eqSum (fs : Fruits) (x : ℤ) : ℤ :=
  ((List.range fs.val.length).map
    (fun i => if posAt fs i = x then amtAt fs i else 0)).sum

def totalSum (fs : Fruits) : ℤ :=
  ((List.range fs.val.length).map (fun i => amtAt fs i)).sum

def segSum (fs : Fruits) (i j : ℕ) : ℤ :=
  (((List.range (j + 1)).filter (fun t => i ≤ t)).map (fun t => amtAt fs t)).sum

def inCandidate (fs : Fruits) (startPos x : ℤ) : Prop :=
  x = startPos ∨ ∃ i, i < fs.val.length ∧ posAt fs i = x

def feasibleSum (fs : Fruits) (startPos k x : ℤ) : Prop :=
  ∃ L R : ℤ, L ≤ startPos ∧ startPos ≤ R ∧ rangeCost startPos L R ≤ k ∧
    x = rangeSum fs L R

/-- Whenever the function returns a result r, r = max { sum_{i: L <= p_i <= R} a_i | L and R are integers, L <= startPos <= R, and (R - L) + min(startPos - L, R - startPos) <= k }. The maximum is over a finite nonempty set because k >= 0 and L = R = startPos is always allowed.
  Preconditions: Let n = len(fruits). fruits is a nonempty slice with 1 <= n <= 100000. For every i with 0 <= i < n, fruits[i] has length 2; write p_i = fruits[i][0] and a_i = fruits[i][1]. For every i, 0 <= p_i <= 200000 and 1 <= a_i <= 10000. For every i with 1 <= i < n, p_{i-1} < p_i. Also 0 <= startPos <= 200000 and 0 <= k <= 200000. -/
theorem spec_1 (fruits : Fruits) (startPos k : I64) (r : I64)
    (hne : 1 ≤ fruits.val.length) (hn : fruits.val.length ≤ 100000)
    (hlen : ∀ v ∈ fruits.val, v.val.length = 2)
    (hpos : ∀ i, i < fruits.val.length → 0 ≤ posAt fruits i ∧ posAt fruits i ≤ 200000)
    (hamt : ∀ i, i < fruits.val.length → 1 ≤ amtAt fruits i ∧ amtAt fruits i ≤ 10000)
    (hsorted : ∀ i, i + 1 < fruits.val.length → posAt fruits i < posAt fruits (i + 1))
    (hstart : 0 ≤ startPos.val ∧ startPos.val ≤ 200000)
    (hk : 0 ≤ k.val ∧ k.val ≤ 200000)
    (hret : Aegis.MaxTotalFruits.max_total_fruits fruits startPos k = ok r) :
    IsGreatest {x : ℤ | feasibleSum fruits startPos.val k.val x} r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (fruits : Fruits) (startPos k : I64) (r : I64)
    (hne : 1 ≤ fruits.val.length) (hn : fruits.val.length ≤ 100000)
    (hlen : ∀ v ∈ fruits.val, v.val.length = 2)
    (hpos : ∀ i, i < fruits.val.length → 0 ≤ posAt fruits i ∧ posAt fruits i ≤ 200000)
    (hamt : ∀ i, i < fruits.val.length → 1 ≤ amtAt fruits i ∧ amtAt fruits i ≤ 10000)
    (hsorted : ∀ i, i + 1 < fruits.val.length → posAt fruits i < posAt fruits (i + 1))
    (hstart : 0 ≤ startPos.val ∧ startPos.val ≤ 200000)
    (hk : 0 ≤ k.val ∧ k.val ≤ 200000)
    (hret : Aegis.MaxTotalFruits.max_total_fruits fruits startPos k = ok r), IsGreatest {x : ℤ | feasibleSum fruits startPos.val k.val x} r.val) := by
  sorry

/-- The function returns a result r and does not fail: for every input satisfying the preconditions there is no out-of-bounds access, no arithmetic overflow in the 64-bit integers, and no other panic.
  Preconditions: Let n = len(fruits). fruits is a nonempty slice with 1 <= n <= 100000. For every i with 0 <= i < n, fruits[i] has length 2; write p_i = fruits[i][0] and a_i = fruits[i][1]. For every i, 0 <= p_i <= 200000 and 1 <= a_i <= 10000. For every i with 1 <= i < n, p_{i-1} < p_i. Also 0 <= startPos <= 200000 and 0 <= k <= 200000. -/
theorem spec_2 (fruits : Fruits) (startPos k : I64)
    (hne : 1 ≤ fruits.val.length) (hn : fruits.val.length ≤ 100000)
    (hlen : ∀ v ∈ fruits.val, v.val.length = 2)
    (hpos : ∀ i, i < fruits.val.length → 0 ≤ posAt fruits i ∧ posAt fruits i ≤ 200000)
    (hamt : ∀ i, i < fruits.val.length → 1 ≤ amtAt fruits i ∧ amtAt fruits i ≤ 10000)
    (hsorted : ∀ i, i + 1 < fruits.val.length → posAt fruits i < posAt fruits (i + 1))
    (hstart : 0 ≤ startPos.val ∧ startPos.val ≤ 200000)
    (hk : 0 ≤ k.val ∧ k.val ≤ 200000) :
    ∃ r : I64, Aegis.MaxTotalFruits.max_total_fruits fruits startPos k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (fruits : Fruits) (startPos k : I64)
    (hne : 1 ≤ fruits.val.length) (hn : fruits.val.length ≤ 100000)
    (hlen : ∀ v ∈ fruits.val, v.val.length = 2)
    (hpos : ∀ i, i < fruits.val.length → 0 ≤ posAt fruits i ∧ posAt fruits i ≤ 200000)
    (hamt : ∀ i, i < fruits.val.length → 1 ≤ amtAt fruits i ∧ amtAt fruits i ≤ 10000)
    (hsorted : ∀ i, i + 1 < fruits.val.length → posAt fruits i < posAt fruits (i + 1))
    (hstart : 0 ≤ startPos.val ∧ startPos.val ≤ 200000)
    (hk : 0 ≤ k.val ∧ k.val ≤ 200000), ∃ r : I64, Aegis.MaxTotalFruits.max_total_fruits fruits startPos k = ok r) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < n and |p_i - startPos| <= k, we have r >= a_i. Equivalently, r is at least the maximum amount among all fruits whose position is within distance k of startPos, or 0 if there is no such fruit.
  Preconditions: Let n = len(fruits). fruits is a nonempty slice with 1 <= n <= 100000. For every i with 0 <= i < n, fruits[i] has length 2; write p_i = fruits[i][0] and a_i = fruits[i][1]. For every i, 0 <= p_i <= 200000 and 1 <= a_i <= 10000. For every i with 1 <= i < n, p_{i-1} < p_i. Also 0 <= startPos <= 200000 and 0 <= k <= 200000. -/
theorem spec_3 (fruits : Fruits) (startPos k : I64) (r : I64)
    (hne : 1 ≤ fruits.val.length) (hn : fruits.val.length ≤ 100000)
    (hlen : ∀ v ∈ fruits.val, v.val.length = 2)
    (hpos : ∀ i, i < fruits.val.length → 0 ≤ posAt fruits i ∧ posAt fruits i ≤ 200000)
    (hamt : ∀ i, i < fruits.val.length → 1 ≤ amtAt fruits i ∧ amtAt fruits i ≤ 10000)
    (hsorted : ∀ i, i + 1 < fruits.val.length → posAt fruits i < posAt fruits (i + 1))
    (hstart : 0 ≤ startPos.val ∧ startPos.val ≤ 200000)
    (hk : 0 ≤ k.val ∧ k.val ≤ 200000)
    (hret : Aegis.MaxTotalFruits.max_total_fruits fruits startPos k = ok r) :
    ∀ i, i < fruits.val.length →
      intDist (posAt fruits i) startPos.val ≤ k.val → r.val ≥ amtAt fruits i := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (fruits : Fruits) (startPos k : I64) (r : I64)
    (hne : 1 ≤ fruits.val.length) (hn : fruits.val.length ≤ 100000)
    (hlen : ∀ v ∈ fruits.val, v.val.length = 2)
    (hpos : ∀ i, i < fruits.val.length → 0 ≤ posAt fruits i ∧ posAt fruits i ≤ 200000)
    (hamt : ∀ i, i < fruits.val.length → 1 ≤ amtAt fruits i ∧ amtAt fruits i ≤ 10000)
    (hsorted : ∀ i, i + 1 < fruits.val.length → posAt fruits i < posAt fruits (i + 1))
    (hstart : 0 ≤ startPos.val ∧ startPos.val ≤ 200000)
    (hk : 0 ≤ k.val ∧ k.val ≤ 200000)
    (hret : Aegis.MaxTotalFruits.max_total_fruits fruits startPos k = ok r), ∀ i, i < fruits.val.length →
      intDist (posAt fruits i) startPos.val ≤ k.val → r.val ≥ amtAt fruits i) := by
  sorry

/-- Whenever the function returns a result r, r <= sum_{i: |p_i - startPos| <= k} a_i.
  Preconditions: Let n = len(fruits). fruits is a nonempty slice with 1 <= n <= 100000. For every i with 0 <= i < n, fruits[i] has length 2; write p_i = fruits[i][0] and a_i = fruits[i][1]. For every i, 0 <= p_i <= 200000 and 1 <= a_i <= 10000. For every i with 1 <= i < n, p_{i-1} < p_i. Also 0 <= startPos <= 200000 and 0 <= k <= 200000. -/
theorem spec_4 (fruits : Fruits) (startPos k : I64) (r : I64)
    (hne : 1 ≤ fruits.val.length) (hn : fruits.val.length ≤ 100000)
    (hlen : ∀ v ∈ fruits.val, v.val.length = 2)
    (hpos : ∀ i, i < fruits.val.length → 0 ≤ posAt fruits i ∧ posAt fruits i ≤ 200000)
    (hamt : ∀ i, i < fruits.val.length → 1 ≤ amtAt fruits i ∧ amtAt fruits i ≤ 10000)
    (hsorted : ∀ i, i + 1 < fruits.val.length → posAt fruits i < posAt fruits (i + 1))
    (hstart : 0 ≤ startPos.val ∧ startPos.val ≤ 200000)
    (hk : 0 ≤ k.val ∧ k.val ≤ 200000)
    (hret : Aegis.MaxTotalFruits.max_total_fruits fruits startPos k = ok r) :
    r.val ≤ nearSum fruits startPos.val k.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (fruits : Fruits) (startPos k : I64) (r : I64)
    (hne : 1 ≤ fruits.val.length) (hn : fruits.val.length ≤ 100000)
    (hlen : ∀ v ∈ fruits.val, v.val.length = 2)
    (hpos : ∀ i, i < fruits.val.length → 0 ≤ posAt fruits i ∧ posAt fruits i ≤ 200000)
    (hamt : ∀ i, i < fruits.val.length → 1 ≤ amtAt fruits i ∧ amtAt fruits i ≤ 10000)
    (hsorted : ∀ i, i + 1 < fruits.val.length → posAt fruits i < posAt fruits (i + 1))
    (hstart : 0 ≤ startPos.val ∧ startPos.val ≤ 200000)
    (hk : 0 ≤ k.val ∧ k.val ≤ 200000)
    (hret : Aegis.MaxTotalFruits.max_total_fruits fruits startPos k = ok r), r.val ≤ nearSum fruits startPos.val k.val) := by
  sorry

/-- Whenever the function returns a result r, r = sum_{i: p_i = startPos} a_i.
  Preconditions: Let n = len(fruits). fruits is a nonempty slice with 1 <= n <= 100000. For every i with 0 <= i < n, fruits[i] has length 2; write p_i = fruits[i][0] and a_i = fruits[i][1]. For every i, 0 <= p_i <= 200000 and 1 <= a_i <= 10000. For every i with 1 <= i < n, p_{i-1} < p_i. Also 0 <= startPos <= 200000 and k = 0. -/
theorem spec_5 (fruits : Fruits) (startPos k : I64) (r : I64)
    (hne : 1 ≤ fruits.val.length) (hn : fruits.val.length ≤ 100000)
    (hlen : ∀ v ∈ fruits.val, v.val.length = 2)
    (hpos : ∀ i, i < fruits.val.length → 0 ≤ posAt fruits i ∧ posAt fruits i ≤ 200000)
    (hamt : ∀ i, i < fruits.val.length → 1 ≤ amtAt fruits i ∧ amtAt fruits i ≤ 10000)
    (hsorted : ∀ i, i + 1 < fruits.val.length → posAt fruits i < posAt fruits (i + 1))
    (hstart : 0 ≤ startPos.val ∧ startPos.val ≤ 200000)
    (hk : k.val = 0)
    (hret : Aegis.MaxTotalFruits.max_total_fruits fruits startPos k = ok r) :
    r.val = eqSum fruits startPos.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (fruits : Fruits) (startPos k : I64) (r : I64)
    (hne : 1 ≤ fruits.val.length) (hn : fruits.val.length ≤ 100000)
    (hlen : ∀ v ∈ fruits.val, v.val.length = 2)
    (hpos : ∀ i, i < fruits.val.length → 0 ≤ posAt fruits i ∧ posAt fruits i ≤ 200000)
    (hamt : ∀ i, i < fruits.val.length → 1 ≤ amtAt fruits i ∧ amtAt fruits i ≤ 10000)
    (hsorted : ∀ i, i + 1 < fruits.val.length → posAt fruits i < posAt fruits (i + 1))
    (hstart : 0 ≤ startPos.val ∧ startPos.val ≤ 200000)
    (hk : k.val = 0)
    (hret : Aegis.MaxTotalFruits.max_total_fruits fruits startPos k = ok r), r.val = eqSum fruits startPos.val) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if for every i with 0 <= i < n, |p_i - startPos| > k.
  Preconditions: Let n = len(fruits). fruits is a nonempty slice with 1 <= n <= 100000. For every i with 0 <= i < n, fruits[i] has length 2; write p_i = fruits[i][0] and a_i = fruits[i][1]. For every i, 0 <= p_i <= 200000 and 1 <= a_i <= 10000. For every i with 1 <= i < n, p_{i-1} < p_i. Also 0 <= startPos <= 200000 and 0 <= k <= 200000. -/
theorem spec_6 (fruits : Fruits) (startPos k : I64) (r : I64)
    (hne : 1 ≤ fruits.val.length) (hn : fruits.val.length ≤ 100000)
    (hlen : ∀ v ∈ fruits.val, v.val.length = 2)
    (hpos : ∀ i, i < fruits.val.length → 0 ≤ posAt fruits i ∧ posAt fruits i ≤ 200000)
    (hamt : ∀ i, i < fruits.val.length → 1 ≤ amtAt fruits i ∧ amtAt fruits i ≤ 10000)
    (hsorted : ∀ i, i + 1 < fruits.val.length → posAt fruits i < posAt fruits (i + 1))
    (hstart : 0 ≤ startPos.val ∧ startPos.val ≤ 200000)
    (hk : 0 ≤ k.val ∧ k.val ≤ 200000)
    (hret : Aegis.MaxTotalFruits.max_total_fruits fruits startPos k = ok r) :
    (r.val = 0 ↔
      ∀ i, i < fruits.val.length → intDist (posAt fruits i) startPos.val > k.val) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (fruits : Fruits) (startPos k : I64) (r : I64)
    (hne : 1 ≤ fruits.val.length) (hn : fruits.val.length ≤ 100000)
    (hlen : ∀ v ∈ fruits.val, v.val.length = 2)
    (hpos : ∀ i, i < fruits.val.length → 0 ≤ posAt fruits i ∧ posAt fruits i ≤ 200000)
    (hamt : ∀ i, i < fruits.val.length → 1 ≤ amtAt fruits i ∧ amtAt fruits i ≤ 10000)
    (hsorted : ∀ i, i + 1 < fruits.val.length → posAt fruits i < posAt fruits (i + 1))
    (hstart : 0 ≤ startPos.val ∧ startPos.val ≤ 200000)
    (hk : 0 ≤ k.val ∧ k.val ≤ 200000)
    (hret : Aegis.MaxTotalFruits.max_total_fruits fruits startPos k = ok r), (r.val = 0 ↔
      ∀ i, i < fruits.val.length → intDist (posAt fruits i) startPos.val > k.val)) := by
  sorry

/-- Whenever the function returns a result r, r = a_0 if |p_0 - startPos| <= k, and r = 0 otherwise.
  Preconditions: Let n = len(fruits). n = 1, so write p_0 = fruits[0][0] and a_0 = fruits[0][1]. For every i with 0 <= i < n, fruits[i] has length 2. Also 0 <= p_0 <= 200000, 1 <= a_0 <= 10000, 0 <= startPos <= 200000, and 0 <= k <= 200000. -/
theorem spec_7 (fruits : Fruits) (startPos k : I64) (r : I64)
    (hn : fruits.val.length = 1)
    (hlen : ∀ v ∈ fruits.val, v.val.length = 2)
    (hpos : 0 ≤ posAt fruits 0 ∧ posAt fruits 0 ≤ 200000)
    (hamt : 1 ≤ amtAt fruits 0 ∧ amtAt fruits 0 ≤ 10000)
    (hstart : 0 ≤ startPos.val ∧ startPos.val ≤ 200000)
    (hk : 0 ≤ k.val ∧ k.val ≤ 200000)
    (hret : Aegis.MaxTotalFruits.max_total_fruits fruits startPos k = ok r) :
    r.val =
      (if intDist (posAt fruits 0) startPos.val ≤ k.val then amtAt fruits 0 else 0) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (fruits : Fruits) (startPos k : I64) (r : I64)
    (hn : fruits.val.length = 1)
    (hlen : ∀ v ∈ fruits.val, v.val.length = 2)
    (hpos : 0 ≤ posAt fruits 0 ∧ posAt fruits 0 ≤ 200000)
    (hamt : 1 ≤ amtAt fruits 0 ∧ amtAt fruits 0 ≤ 10000)
    (hstart : 0 ≤ startPos.val ∧ startPos.val ≤ 200000)
    (hk : 0 ≤ k.val ∧ k.val ≤ 200000)
    (hret : Aegis.MaxTotalFruits.max_total_fruits fruits startPos k = ok r), r.val =
      (if intDist (posAt fruits 0) startPos.val ≤ k.val then amtAt fruits 0 else 0)) := by
  sorry

/-- Whenever the function returns a result r, r = sum_{i=0}^{n-1} a_i.
  Preconditions: Let n = len(fruits). fruits is a nonempty slice with 1 <= n <= 100000. For every i with 0 <= i < n, fruits[i] has length 2; write p_i = fruits[i][0] and a_i = fruits[i][1]. For every i, 0 <= p_i <= 200000 and 1 <= a_i <= 10000. For every i with 1 <= i < n, p_{i-1} < p_i. Also 0 <= startPos <= 200000 and 0 <= k <= 200000. Additionally, either (for every i, p_i >= startPos and p_{n-1} - startPos <= k) or (for every i, p_i <= startPos and startPos - p_0 <= k). -/
theorem spec_8 (fruits : Fruits) (startPos k : I64) (r : I64)
    (hne : 1 ≤ fruits.val.length) (hn : fruits.val.length ≤ 100000)
    (hlen : ∀ v ∈ fruits.val, v.val.length = 2)
    (hpos : ∀ i, i < fruits.val.length → 0 ≤ posAt fruits i ∧ posAt fruits i ≤ 200000)
    (hamt : ∀ i, i < fruits.val.length → 1 ≤ amtAt fruits i ∧ amtAt fruits i ≤ 10000)
    (hsorted : ∀ i, i + 1 < fruits.val.length → posAt fruits i < posAt fruits (i + 1))
    (hstart : 0 ≤ startPos.val ∧ startPos.val ≤ 200000)
    (hk : 0 ≤ k.val ∧ k.val ≤ 200000)
    (hside :
      ((∀ i, i < fruits.val.length → startPos.val ≤ posAt fruits i) ∧
        posAt fruits (fruits.val.length - 1) - startPos.val ≤ k.val) ∨
      ((∀ i, i < fruits.val.length → posAt fruits i ≤ startPos.val) ∧
        startPos.val - posAt fruits 0 ≤ k.val))
    (hret : Aegis.MaxTotalFruits.max_total_fruits fruits startPos k = ok r) :
    r.val = totalSum fruits := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (fruits : Fruits) (startPos k : I64) (r : I64)
    (hne : 1 ≤ fruits.val.length) (hn : fruits.val.length ≤ 100000)
    (hlen : ∀ v ∈ fruits.val, v.val.length = 2)
    (hpos : ∀ i, i < fruits.val.length → 0 ≤ posAt fruits i ∧ posAt fruits i ≤ 200000)
    (hamt : ∀ i, i < fruits.val.length → 1 ≤ amtAt fruits i ∧ amtAt fruits i ≤ 10000)
    (hsorted : ∀ i, i + 1 < fruits.val.length → posAt fruits i < posAt fruits (i + 1))
    (hstart : 0 ≤ startPos.val ∧ startPos.val ≤ 200000)
    (hk : 0 ≤ k.val ∧ k.val ≤ 200000)
    (hside :
      ((∀ i, i < fruits.val.length → startPos.val ≤ posAt fruits i) ∧
        posAt fruits (fruits.val.length - 1) - startPos.val ≤ k.val) ∨
      ((∀ i, i < fruits.val.length → posAt fruits i ≤ startPos.val) ∧
        startPos.val - posAt fruits 0 ≤ k.val))
    (hret : Aegis.MaxTotalFruits.max_total_fruits fruits startPos k = ok r), r.val = totalSum fruits) := by
  sorry

/-- If the call max_total_fruits(fruits, startPos, k1) returns r1 and the call max_total_fruits(fruits, startPos, k2) returns r2, then r1 <= r2.
  Preconditions: Let n = len(fruits). fruits is a nonempty slice with 1 <= n <= 100000. For every i with 0 <= i < n, fruits[i] has length 2; write p_i = fruits[i][0] and a_i = fruits[i][1]. For every i, 0 <= p_i <= 200000 and 1 <= a_i <= 10000. For every i with 1 <= i < n, p_{i-1} < p_i. Also 0 <= startPos <= 200000. Let k1 and k2 be integers with 0 <= k1 <= k2 <= 200000. -/
theorem spec_9 (fruits : Fruits) (startPos k1 k2 : I64) (r1 r2 : I64)
    (hne : 1 ≤ fruits.val.length) (hn : fruits.val.length ≤ 100000)
    (hlen : ∀ v ∈ fruits.val, v.val.length = 2)
    (hpos : ∀ i, i < fruits.val.length → 0 ≤ posAt fruits i ∧ posAt fruits i ≤ 200000)
    (hamt : ∀ i, i < fruits.val.length → 1 ≤ amtAt fruits i ∧ amtAt fruits i ≤ 10000)
    (hsorted : ∀ i, i + 1 < fruits.val.length → posAt fruits i < posAt fruits (i + 1))
    (hstart : 0 ≤ startPos.val ∧ startPos.val ≤ 200000)
    (hk1 : 0 ≤ k1.val) (hk12 : k1.val ≤ k2.val) (hk2 : k2.val ≤ 200000)
    (hret1 : Aegis.MaxTotalFruits.max_total_fruits fruits startPos k1 = ok r1)
    (hret2 : Aegis.MaxTotalFruits.max_total_fruits fruits startPos k2 = ok r2) :
    r1.val ≤ r2.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (fruits : Fruits) (startPos k1 k2 : I64) (r1 r2 : I64)
    (hne : 1 ≤ fruits.val.length) (hn : fruits.val.length ≤ 100000)
    (hlen : ∀ v ∈ fruits.val, v.val.length = 2)
    (hpos : ∀ i, i < fruits.val.length → 0 ≤ posAt fruits i ∧ posAt fruits i ≤ 200000)
    (hamt : ∀ i, i < fruits.val.length → 1 ≤ amtAt fruits i ∧ amtAt fruits i ≤ 10000)
    (hsorted : ∀ i, i + 1 < fruits.val.length → posAt fruits i < posAt fruits (i + 1))
    (hstart : 0 ≤ startPos.val ∧ startPos.val ≤ 200000)
    (hk1 : 0 ≤ k1.val) (hk12 : k1.val ≤ k2.val) (hk2 : k2.val ≤ 200000)
    (hret1 : Aegis.MaxTotalFruits.max_total_fruits fruits startPos k1 = ok r1)
    (hret2 : Aegis.MaxTotalFruits.max_total_fruits fruits startPos k2 = ok r2), r1.val ≤ r2.val) := by
  sorry

/-- If the call on fruits with startPos and k returns r and the call on fruits' with startPos and k returns r', then r = r'.
  Preconditions: Let n = len(fruits). fruits is a nonempty slice with 1 <= n <= 100000. For every i with 0 <= i < n, fruits[i] has length 2; write p_i = fruits[i][0] and a_i = fruits[i][1]. For every i, 0 <= p_i <= 200000 and 1 <= a_i <= 10000. For every i with 1 <= i < n, p_{i-1} < p_i. Also 0 <= startPos <= 200000 and 0 <= k <= 200000. Fix an index j with 0 <= j < n and |p_j - startPos| > k. Let a'_j be an integer with 1 <= a'_j <= 10000. Let fruits' be the slice obtained from fruits by replacing a_j by a'_j, with all positions and all other amounts unchanged. -/
theorem spec_10 (fruits fruits' : Fruits) (startPos k : I64) (r r' : I64) (j : ℕ) (a' : ℤ)
    (hne : 1 ≤ fruits.val.length) (hn : fruits.val.length ≤ 100000)
    (hlen : ∀ v ∈ fruits.val, v.val.length = 2)
    (hpos : ∀ i, i < fruits.val.length → 0 ≤ posAt fruits i ∧ posAt fruits i ≤ 200000)
    (hamt : ∀ i, i < fruits.val.length → 1 ≤ amtAt fruits i ∧ amtAt fruits i ≤ 10000)
    (hsorted : ∀ i, i + 1 < fruits.val.length → posAt fruits i < posAt fruits (i + 1))
    (hstart : 0 ≤ startPos.val ∧ startPos.val ≤ 200000)
    (hk : 0 ≤ k.val ∧ k.val ≤ 200000)
    (hj : j < fruits.val.length)
    (hjfar : intDist (posAt fruits j) startPos.val > k.val)
    (ha' : 1 ≤ a' ∧ a' ≤ 10000)
    (hlen' : ∀ v ∈ fruits'.val, v.val.length = 2)
    (hn' : fruits'.val.length = fruits.val.length)
    (hpos' : ∀ i, i < fruits.val.length → posAt fruits' i = posAt fruits i)
    (hamt' : ∀ i, i < fruits.val.length → i ≠ j → amtAt fruits' i = amtAt fruits i)
    (hamtj' : amtAt fruits' j = a')
    (hret : Aegis.MaxTotalFruits.max_total_fruits fruits startPos k = ok r)
    (hret' : Aegis.MaxTotalFruits.max_total_fruits fruits' startPos k = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (fruits fruits' : Fruits) (startPos k : I64) (r r' : I64) (j : ℕ) (a' : ℤ)
    (hne : 1 ≤ fruits.val.length) (hn : fruits.val.length ≤ 100000)
    (hlen : ∀ v ∈ fruits.val, v.val.length = 2)
    (hpos : ∀ i, i < fruits.val.length → 0 ≤ posAt fruits i ∧ posAt fruits i ≤ 200000)
    (hamt : ∀ i, i < fruits.val.length → 1 ≤ amtAt fruits i ∧ amtAt fruits i ≤ 10000)
    (hsorted : ∀ i, i + 1 < fruits.val.length → posAt fruits i < posAt fruits (i + 1))
    (hstart : 0 ≤ startPos.val ∧ startPos.val ≤ 200000)
    (hk : 0 ≤ k.val ∧ k.val ≤ 200000)
    (hj : j < fruits.val.length)
    (hjfar : intDist (posAt fruits j) startPos.val > k.val)
    (ha' : 1 ≤ a' ∧ a' ≤ 10000)
    (hlen' : ∀ v ∈ fruits'.val, v.val.length = 2)
    (hn' : fruits'.val.length = fruits.val.length)
    (hpos' : ∀ i, i < fruits.val.length → posAt fruits' i = posAt fruits i)
    (hamt' : ∀ i, i < fruits.val.length → i ≠ j → amtAt fruits' i = amtAt fruits i)
    (hamtj' : amtAt fruits' j = a')
    (hret : Aegis.MaxTotalFruits.max_total_fruits fruits startPos k = ok r)
    (hret' : Aegis.MaxTotalFruits.max_total_fruits fruits' startPos k = ok r'), r.val = r'.val) := by
  sorry

/-- Whenever the function returns a result r, there exist integers L and R such that L <= startPos <= R, (R - L) + min(startPos - L, R - startPos) <= k, and r = sum_{i: L <= p_i <= R} a_i.
  Preconditions: Let n = len(fruits). fruits is a nonempty slice with 1 <= n <= 100000. For every i with 0 <= i < n, fruits[i] has length 2; write p_i = fruits[i][0] and a_i = fruits[i][1]. For every i, 0 <= p_i <= 200000 and 1 <= a_i <= 10000. For every i with 1 <= i < n, p_{i-1} < p_i. Also 0 <= startPos <= 200000 and 0 <= k <= 200000. -/
theorem spec_11 (fruits : Fruits) (startPos k : I64) (r : I64)
    (hne : 1 ≤ fruits.val.length) (hn : fruits.val.length ≤ 100000)
    (hlen : ∀ v ∈ fruits.val, v.val.length = 2)
    (hpos : ∀ i, i < fruits.val.length → 0 ≤ posAt fruits i ∧ posAt fruits i ≤ 200000)
    (hamt : ∀ i, i < fruits.val.length → 1 ≤ amtAt fruits i ∧ amtAt fruits i ≤ 10000)
    (hsorted : ∀ i, i + 1 < fruits.val.length → posAt fruits i < posAt fruits (i + 1))
    (hstart : 0 ≤ startPos.val ∧ startPos.val ≤ 200000)
    (hk : 0 ≤ k.val ∧ k.val ≤ 200000)
    (hret : Aegis.MaxTotalFruits.max_total_fruits fruits startPos k = ok r) :
    ∃ L R : ℤ, L ≤ startPos.val ∧ startPos.val ≤ R ∧
      rangeCost startPos.val L R ≤ k.val ∧ r.val = rangeSum fruits L R := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (fruits : Fruits) (startPos k : I64) (r : I64)
    (hne : 1 ≤ fruits.val.length) (hn : fruits.val.length ≤ 100000)
    (hlen : ∀ v ∈ fruits.val, v.val.length = 2)
    (hpos : ∀ i, i < fruits.val.length → 0 ≤ posAt fruits i ∧ posAt fruits i ≤ 200000)
    (hamt : ∀ i, i < fruits.val.length → 1 ≤ amtAt fruits i ∧ amtAt fruits i ≤ 10000)
    (hsorted : ∀ i, i + 1 < fruits.val.length → posAt fruits i < posAt fruits (i + 1))
    (hstart : 0 ≤ startPos.val ∧ startPos.val ≤ 200000)
    (hk : 0 ≤ k.val ∧ k.val ≤ 200000)
    (hret : Aegis.MaxTotalFruits.max_total_fruits fruits startPos k = ok r), ∃ L R : ℤ, L ≤ startPos.val ∧ startPos.val ≤ R ∧
      rangeCost startPos.val L R ≤ k.val ∧ r.val = rangeSum fruits L R) := by
  sorry

/-- Whenever the function returns a result r, there exist L and R with L <= startPos <= R, each of L and R belonging to the set {startPos} union {p_i : 0 <= i < n}, (R - L) + min(startPos - L, R - startPos) <= k, and r = sum_{i: L <= p_i <= R} a_i.
  Preconditions: Let n = len(fruits). fruits is a nonempty slice with 1 <= n <= 100000. For every i with 0 <= i < n, fruits[i] has length 2; write p_i = fruits[i][0] and a_i = fruits[i][1]. For every i, 0 <= p_i <= 200000 and 1 <= a_i <= 10000. For every i with 1 <= i < n, p_{i-1} < p_i. Also 0 <= startPos <= 200000 and 0 <= k <= 200000. -/
theorem spec_12 (fruits : Fruits) (startPos k : I64) (r : I64)
    (hne : 1 ≤ fruits.val.length) (hn : fruits.val.length ≤ 100000)
    (hlen : ∀ v ∈ fruits.val, v.val.length = 2)
    (hpos : ∀ i, i < fruits.val.length → 0 ≤ posAt fruits i ∧ posAt fruits i ≤ 200000)
    (hamt : ∀ i, i < fruits.val.length → 1 ≤ amtAt fruits i ∧ amtAt fruits i ≤ 10000)
    (hsorted : ∀ i, i + 1 < fruits.val.length → posAt fruits i < posAt fruits (i + 1))
    (hstart : 0 ≤ startPos.val ∧ startPos.val ≤ 200000)
    (hk : 0 ≤ k.val ∧ k.val ≤ 200000)
    (hret : Aegis.MaxTotalFruits.max_total_fruits fruits startPos k = ok r) :
    ∃ L R : ℤ, L ≤ startPos.val ∧ startPos.val ≤ R ∧
      inCandidate fruits startPos.val L ∧ inCandidate fruits startPos.val R ∧
      rangeCost startPos.val L R ≤ k.val ∧ r.val = rangeSum fruits L R := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (fruits : Fruits) (startPos k : I64) (r : I64)
    (hne : 1 ≤ fruits.val.length) (hn : fruits.val.length ≤ 100000)
    (hlen : ∀ v ∈ fruits.val, v.val.length = 2)
    (hpos : ∀ i, i < fruits.val.length → 0 ≤ posAt fruits i ∧ posAt fruits i ≤ 200000)
    (hamt : ∀ i, i < fruits.val.length → 1 ≤ amtAt fruits i ∧ amtAt fruits i ≤ 10000)
    (hsorted : ∀ i, i + 1 < fruits.val.length → posAt fruits i < posAt fruits (i + 1))
    (hstart : 0 ≤ startPos.val ∧ startPos.val ≤ 200000)
    (hk : 0 ≤ k.val ∧ k.val ≤ 200000)
    (hret : Aegis.MaxTotalFruits.max_total_fruits fruits startPos k = ok r), ∃ L R : ℤ, L ≤ startPos.val ∧ startPos.val ≤ R ∧
      inCandidate fruits startPos.val L ∧ inCandidate fruits startPos.val R ∧
      rangeCost startPos.val L R ≤ k.val ∧ r.val = rangeSum fruits L R) := by
  sorry

/-- Whenever the function returns a result r, either r = 0, or there exist indices i and j with 0 <= i <= j < n such that r = sum_{t=i}^{j} a_t and, setting L = min(startPos, p_i) and R = max(startPos, p_j), one has (R - L) + min(startPos - L, R - startPos) <= k.
  Preconditions: Let n = len(fruits). fruits is a nonempty slice with 1 <= n <= 100000. For every i with 0 <= i < n, fruits[i] has length 2; write p_i = fruits[i][0] and a_i = fruits[i][1]. For every i, 0 <= p_i <= 200000 and 1 <= a_i <= 10000. For every i with 1 <= i < n, p_{i-1} < p_i. Also 0 <= startPos <= 200000 and 0 <= k <= 200000. -/
theorem spec_13 (fruits : Fruits) (startPos k : I64) (r : I64)
    (hne : 1 ≤ fruits.val.length) (hn : fruits.val.length ≤ 100000)
    (hlen : ∀ v ∈ fruits.val, v.val.length = 2)
    (hpos : ∀ i, i < fruits.val.length → 0 ≤ posAt fruits i ∧ posAt fruits i ≤ 200000)
    (hamt : ∀ i, i < fruits.val.length → 1 ≤ amtAt fruits i ∧ amtAt fruits i ≤ 10000)
    (hsorted : ∀ i, i + 1 < fruits.val.length → posAt fruits i < posAt fruits (i + 1))
    (hstart : 0 ≤ startPos.val ∧ startPos.val ≤ 200000)
    (hk : 0 ≤ k.val ∧ k.val ≤ 200000)
    (hret : Aegis.MaxTotalFruits.max_total_fruits fruits startPos k = ok r) :
    r.val = 0 ∨
      ∃ i j : ℕ, i ≤ j ∧ j < fruits.val.length ∧
        r.val = segSum fruits i j ∧
        rangeCost startPos.val (min startPos.val (posAt fruits i))
          (max startPos.val (posAt fruits j)) ≤ k.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (fruits : Fruits) (startPos k : I64) (r : I64)
    (hne : 1 ≤ fruits.val.length) (hn : fruits.val.length ≤ 100000)
    (hlen : ∀ v ∈ fruits.val, v.val.length = 2)
    (hpos : ∀ i, i < fruits.val.length → 0 ≤ posAt fruits i ∧ posAt fruits i ≤ 200000)
    (hamt : ∀ i, i < fruits.val.length → 1 ≤ amtAt fruits i ∧ amtAt fruits i ≤ 10000)
    (hsorted : ∀ i, i + 1 < fruits.val.length → posAt fruits i < posAt fruits (i + 1))
    (hstart : 0 ≤ startPos.val ∧ startPos.val ≤ 200000)
    (hk : 0 ≤ k.val ∧ k.val ≤ 200000)
    (hret : Aegis.MaxTotalFruits.max_total_fruits fruits startPos k = ok r), r.val = 0 ∨
      ∃ i j : ℕ, i ≤ j ∧ j < fruits.val.length ∧
        r.val = segSum fruits i j ∧
        rangeCost startPos.val (min startPos.val (posAt fruits i))
          (max startPos.val (posAt fruits j)) ≤ k.val) := by
  sorry

end AegisSpec.MaxTotalFruits
