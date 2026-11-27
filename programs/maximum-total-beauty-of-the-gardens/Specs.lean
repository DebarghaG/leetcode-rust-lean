import Aegis.MaximumBeauty.Code.Funs

/-!
# Specifications of `Aegis.MaximumBeauty.maximum_beauty`

LeetCode problem `maximum-total-beauty-of-the-gardens`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaximumBeauty

def contents (flowers : Slice Std.I64) : List ℤ :=
  flowers.val.map (fun v => v.val)

def countAtLeast (t : ℤ) (y : List ℤ) : ℕ :=
  y.countP (fun v => decide (t ≤ v))

def minBelow (t : ℤ) (y : List ℤ) : ℤ :=
  match y.filter (fun v => decide (v < t)) with
  | [] => 0
  | v :: vs => vs.foldr min v

def beauty (target full part : ℤ) (y : List ℤ) : ℤ :=
  (countAtLeast target y : ℤ) * full + minBelow target y * part

def deficit (t : ℤ) (y : List ℤ) : ℤ :=
  ((y.filter (fun v => decide (v < t))).map (fun v => t - v)).sum

def totalRaise (x y : List ℤ) : ℤ :=
  (x.zipWith (fun a b => b - a) y).sum

def Feasible (x y : List ℤ) (budget : ℤ) : Prop :=
  y.length = x.length ∧ List.Forall₂ (fun a b => a ≤ b) x y ∧ totalRaise x y ≤ budget

def Normalized (t : ℤ) (x y : List ℤ) : Prop :=
  List.Forall₂ (fun a b => (t ≤ a → b = a) ∧ (a < t → a ≤ b ∧ b ≤ t)) x y

def Preconditions (flowers : Slice Std.I64) (newFlowers target full «partial» : Std.I64) :
    Prop :=
  1 ≤ flowers.leng ∧ flowers.leng ≤ 100000 ∧
    (∀ v ∈ contents flowers, 1 ≤ v ∧ v ≤ 100000) ∧
    0 ≤ newFlowers.val ∧ newFlowers.val ≤ 10000000000 ∧
    1 ≤ target.val ∧ target.val ≤ 100000 ∧
    1 ≤ full.val ∧ full.val ≤ 100000 ∧
    1 ≤ «partial».val ∧ «partial».val ≤ 100000

/-- Whenever the function returns a result r, r is the maximum, over all length-n integer arrays y such that y[i] >= flowers[i] for every i with 0 <= i < n and sum_{i=0}^{n-1}(y[i]-flowers[i]) <= newFlowers, of C(y)*full + M(y)*partial, where C(y) = number of indices i with 0 <= i < n and y[i] >= target, and M(y) = 0 if C(y)=n, and otherwise M(y) = min{ y[i] | 0 <= i < n and y[i] < target }. The set of feasible y is nonempty because y=flowers is feasible.
  Preconditions: Let n = len(flowers). 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= flowers[i] <= 100000; 0 <= newFlowers <= 10000000000; 1 <= target <= 100000; 1 <= full <= 100000; 1 <= partial <= 100000. All input values are within the signed 64-bit range. -/
theorem spec_1 (flowers : Slice Std.I64) (newFlowers target full «partial» : Std.I64)
    (hpre : Preconditions flowers newFlowers target full «partial»)
    (r : Std.I64)
    (hr : Aegis.MaximumBeauty.maximum_beauty flowers newFlowers target full «partial» = ok r) :
    (∃ y : List ℤ,
        Feasible (contents flowers) y newFlowers.val ∧
          beauty target.val full.val «partial».val y = r.val) ∧
      (∀ y : List ℤ,
        Feasible (contents flowers) y newFlowers.val →
          beauty target.val full.val «partial».val y ≤ r.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (flowers : Slice Std.I64) (newFlowers target full «partial» : Std.I64)
    (hpre : Preconditions flowers newFlowers target full «partial»)
    (r : Std.I64)
    (hr : Aegis.MaximumBeauty.maximum_beauty flowers newFlowers target full «partial» = ok r), (∃ y : List ℤ,
        Feasible (contents flowers) y newFlowers.val ∧
          beauty target.val full.val «partial».val y = r.val) ∧
      (∀ y : List ℤ,
        Feasible (contents flowers) y newFlowers.val →
          beauty target.val full.val «partial».val y ≤ r.val)) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r; in particular it does not fail, panic, overflow, or access out of bounds.
  Preconditions: Let n = len(flowers). 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= flowers[i] <= 100000; 0 <= newFlowers <= 10000000000; 1 <= target <= 100000; 1 <= full <= 100000; 1 <= partial <= 100000. All input values are within the signed 64-bit range. -/
theorem spec_2 (flowers : Slice Std.I64) (newFlowers target full «partial» : Std.I64)
    (hpre : Preconditions flowers newFlowers target full «partial») :
    ∃ r : Std.I64,
      Aegis.MaximumBeauty.maximum_beauty flowers newFlowers target full «partial» = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (flowers : Slice Std.I64) (newFlowers target full «partial» : Std.I64)
    (hpre : Preconditions flowers newFlowers target full «partial»), ∃ r : Std.I64,
      Aegis.MaximumBeauty.maximum_beauty flowers newFlowers target full «partial» = ok r) := by
  sorry

/-- Let C0 = number of indices i with 0 <= i < n and flowers[i] >= target. Let M0 = 0 if C0 = n, and otherwise M0 = min{ flowers[i] | 0 <= i < n and flowers[i] < target }. Whenever the function returns a result r, r >= C0*full + M0*partial.
  Preconditions: Let n = len(flowers). 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= flowers[i] <= 100000; 0 <= newFlowers <= 10000000000; 1 <= target <= 100000; 1 <= full <= 100000; 1 <= partial <= 100000. All input values are within the signed 64-bit range. -/
theorem spec_3 (flowers : Slice Std.I64) (newFlowers target full «partial» : Std.I64)
    (hpre : Preconditions flowers newFlowers target full «partial»)
    (r : Std.I64)
    (hr : Aegis.MaximumBeauty.maximum_beauty flowers newFlowers target full «partial» = ok r) :
    beauty target.val full.val «partial».val (contents flowers) ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (flowers : Slice Std.I64) (newFlowers target full «partial» : Std.I64)
    (hpre : Preconditions flowers newFlowers target full «partial»)
    (r : Std.I64)
    (hr : Aegis.MaximumBeauty.maximum_beauty flowers newFlowers target full «partial» = ok r), beauty target.val full.val «partial».val (contents flowers) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= n*full + (target - 1)*partial.
  Preconditions: Let n = len(flowers). 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= flowers[i] <= 100000; 0 <= newFlowers <= 10000000000; 1 <= target <= 100000; 1 <= full <= 100000; 1 <= partial <= 100000. All input values are within the signed 64-bit range. -/
theorem spec_4 (flowers : Slice Std.I64) (newFlowers target full «partial» : Std.I64)
    (hpre : Preconditions flowers newFlowers target full «partial»)
    (r : Std.I64)
    (hr : Aegis.MaximumBeauty.maximum_beauty flowers newFlowers target full «partial» = ok r) :
    r.val ≤ (flowers.leng : ℤ) * full.val + (target.val - 1) * «partial».val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (flowers : Slice Std.I64) (newFlowers target full «partial» : Std.I64)
    (hpre : Preconditions flowers newFlowers target full «partial»)
    (r : Std.I64)
    (hr : Aegis.MaximumBeauty.maximum_beauty flowers newFlowers target full «partial» = ok r), r.val ≤ (flowers.leng : ℤ) * full.val + (target.val - 1) * «partial».val) := by
  sorry

/-- Whenever the function returns a result r, r = n*full.
  Preconditions: Let n = len(flowers). 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= flowers[i] <= 100000; 0 <= newFlowers <= 10000000000; 1 <= target <= 100000; 1 <= full <= 100000; 1 <= partial <= 100000. All input values are within the signed 64-bit range. Additionally, for every i with 0 <= i < n, flowers[i] >= target. -/
theorem spec_5 (flowers : Slice Std.I64) (newFlowers target full «partial» : Std.I64)
    (hpre : Preconditions flowers newFlowers target full «partial»)
    (hge : ∀ v ∈ contents flowers, target.val ≤ v)
    (r : Std.I64)
    (hr : Aegis.MaximumBeauty.maximum_beauty flowers newFlowers target full «partial» = ok r) :
    r.val = (flowers.leng : ℤ) * full.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (flowers : Slice Std.I64) (newFlowers target full «partial» : Std.I64)
    (hpre : Preconditions flowers newFlowers target full «partial»)
    (hge : ∀ v ∈ contents flowers, target.val ≤ v)
    (r : Std.I64)
    (hr : Aegis.MaximumBeauty.maximum_beauty flowers newFlowers target full «partial» = ok r), r.val = (flowers.leng : ℤ) * full.val) := by
  sorry

/-- Let C0 = number of indices i with 0 <= i < n and flowers[i] >= target. Let M0 = 0 if C0 = n, and otherwise M0 = min{ flowers[i] | 0 <= i < n and flowers[i] < target }. Whenever the function returns a result r, r = C0*full + M0*partial.
  Preconditions: Let n = len(flowers). 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= flowers[i] <= 100000; 0 <= newFlowers <= 10000000000; 1 <= target <= 100000; 1 <= full <= 100000; 1 <= partial <= 100000. All input values are within the signed 64-bit range. Additionally, newFlowers = 0. -/
theorem spec_6 (flowers : Slice Std.I64) (newFlowers target full «partial» : Std.I64)
    (hpre : Preconditions flowers newFlowers target full «partial»)
    (hnf : newFlowers.val = 0)
    (r : Std.I64)
    (hr : Aegis.MaximumBeauty.maximum_beauty flowers newFlowers target full «partial» = ok r) :
    r.val = beauty target.val full.val «partial».val (contents flowers) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (flowers : Slice Std.I64) (newFlowers target full «partial» : Std.I64)
    (hpre : Preconditions flowers newFlowers target full «partial»)
    (hnf : newFlowers.val = 0)
    (r : Std.I64)
    (hr : Aegis.MaximumBeauty.maximum_beauty flowers newFlowers target full «partial» = ok r), r.val = beauty target.val full.val «partial».val (contents flowers)) := by
  sorry

/-- Whenever the function returns a result r, r >= n*full.
  Preconditions: Let n = len(flowers). 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= flowers[i] <= 100000; 0 <= newFlowers <= 10000000000; 1 <= target <= 100000; 1 <= full <= 100000; 1 <= partial <= 100000. All input values are within the signed 64-bit range. Let D = sum over i with 0 <= i < n and flowers[i] < target of (target - flowers[i]). Additionally, D <= newFlowers. -/
theorem spec_7 (flowers : Slice Std.I64) (newFlowers target full «partial» : Std.I64)
    (hpre : Preconditions flowers newFlowers target full «partial»)
    (hd : deficit target.val (contents flowers) ≤ newFlowers.val)
    (r : Std.I64)
    (hr : Aegis.MaximumBeauty.maximum_beauty flowers newFlowers target full «partial» = ok r) :
    (flowers.leng : ℤ) * full.val ≤ r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (flowers : Slice Std.I64) (newFlowers target full «partial» : Std.I64)
    (hpre : Preconditions flowers newFlowers target full «partial»)
    (hd : deficit target.val (contents flowers) ≤ newFlowers.val)
    (r : Std.I64)
    (hr : Aegis.MaximumBeauty.maximum_beauty flowers newFlowers target full «partial» = ok r), (flowers.leng : ℤ) * full.val ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= (n - 1)*full + (target - 1)*partial.
  Preconditions: Let n = len(flowers). 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= flowers[i] <= 100000; 0 <= newFlowers <= 10000000000; 1 <= target <= 100000; 1 <= full <= 100000; 1 <= partial <= 100000. All input values are within the signed 64-bit range. Let D = sum over i with 0 <= i < n and flowers[i] < target of (target - flowers[i]). Additionally, D > newFlowers. -/
theorem spec_8 (flowers : Slice Std.I64) (newFlowers target full «partial» : Std.I64)
    (hpre : Preconditions flowers newFlowers target full «partial»)
    (hd : newFlowers.val < deficit target.val (contents flowers))
    (r : Std.I64)
    (hr : Aegis.MaximumBeauty.maximum_beauty flowers newFlowers target full «partial» = ok r) :
    r.val ≤ ((flowers.leng : ℤ) - 1) * full.val + (target.val - 1) * «partial».val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (flowers : Slice Std.I64) (newFlowers target full «partial» : Std.I64)
    (hpre : Preconditions flowers newFlowers target full «partial»)
    (hd : newFlowers.val < deficit target.val (contents flowers))
    (r : Std.I64)
    (hr : Aegis.MaximumBeauty.maximum_beauty flowers newFlowers target full «partial» = ok r), r.val ≤ ((flowers.leng : ℤ) - 1) * full.val + (target.val - 1) * «partial».val) := by
  sorry

/-- Whenever the function returns a result r, there exists a length-n integer array y such that: (a) y[i] >= flowers[i] for every i with 0 <= i < n; (b) sum_{i=0}^{n-1}(y[i]-flowers[i]) <= newFlowers; (c) r = C(y)*full + M(y)*partial, where C(y) is the number of indices i with y[i] >= target, and M(y) = 0 if C(y)=n and otherwise M(y) = min{ y[i] | 0 <= i < n and y[i] < target }; (d) if flowers[i] >= target then y[i] = flowers[i]; (e) if flowers[i] < target then flowers[i] <= y[i] <= target.
  Preconditions: Let n = len(flowers). 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= flowers[i] <= 100000; 0 <= newFlowers <= 10000000000; 1 <= target <= 100000; 1 <= full <= 100000; 1 <= partial <= 100000. All input values are within the signed 64-bit range. -/
theorem spec_9 (flowers : Slice Std.I64) (newFlowers target full «partial» : Std.I64)
    (hpre : Preconditions flowers newFlowers target full «partial»)
    (r : Std.I64)
    (hr : Aegis.MaximumBeauty.maximum_beauty flowers newFlowers target full «partial» = ok r) :
    ∃ y : List ℤ,
      Feasible (contents flowers) y newFlowers.val ∧
        beauty target.val full.val «partial».val y = r.val ∧
          Normalized target.val (contents flowers) y := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (flowers : Slice Std.I64) (newFlowers target full «partial» : Std.I64)
    (hpre : Preconditions flowers newFlowers target full «partial»)
    (r : Std.I64)
    (hr : Aegis.MaximumBeauty.maximum_beauty flowers newFlowers target full «partial» = ok r), ∃ y : List ℤ,
      Feasible (contents flowers) y newFlowers.val ∧
        beauty target.val full.val «partial».val y = r.val ∧
          Normalized target.val (contents flowers) y) := by
  sorry

/-- Whenever maximum_beauty(flowers, newFlowers, target, full, partial) returns r and maximum_beauty(flowers', newFlowers, target, full, partial) returns r', we have r = r'.
  Preconditions: Let n = len(flowers). 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= flowers[i] <= 100000; 0 <= newFlowers <= 10000000000; 1 <= target <= 100000; 1 <= full <= 100000; 1 <= partial <= 100000. All input values are within the signed 64-bit range. Let pi be any bijection from {0,...,n-1} to itself, and define flowers'[i] = flowers[pi(i)] for 0 <= i < n. -/
theorem spec_10 (flowers flowers' : Slice Std.I64)
    (newFlowers target full «partial» : Std.I64)
    (hpre : Preconditions flowers newFlowers target full «partial»)
    (hperm : (contents flowers').Perm (contents flowers))
    (r r' : Std.I64)
    (hr : Aegis.MaximumBeauty.maximum_beauty flowers newFlowers target full «partial» = ok r)
    (hr' : Aegis.MaximumBeauty.maximum_beauty flowers' newFlowers target full «partial» = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (flowers flowers' : Slice Std.I64)
    (newFlowers target full «partial» : Std.I64)
    (hpre : Preconditions flowers newFlowers target full «partial»)
    (hperm : (contents flowers').Perm (contents flowers))
    (r r' : Std.I64)
    (hr : Aegis.MaximumBeauty.maximum_beauty flowers newFlowers target full «partial» = ok r)
    (hr' : Aegis.MaximumBeauty.maximum_beauty flowers' newFlowers target full «partial» = ok r'), r.val = r'.val) := by
  sorry

/-- For every integer m with 0 <= m <= newFlowers, whenever maximum_beauty(flowers, m, target, full, partial) returns r_m and maximum_beauty(flowers, newFlowers, target, full, partial) returns r, we have r_m <= r.
  Preconditions: Let n = len(flowers). 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= flowers[i] <= 100000; 0 <= newFlowers <= 10000000000; 1 <= target <= 100000; 1 <= full <= 100000; 1 <= partial <= 100000. All input values are within the signed 64-bit range. -/
theorem spec_11 (flowers : Slice Std.I64) (newFlowers target full «partial» : Std.I64)
    (hpre : Preconditions flowers newFlowers target full «partial»)
    (m : Std.I64) (hm0 : 0 ≤ m.val) (hmn : m.val ≤ newFlowers.val)
    (r_m r : Std.I64)
    (hrm : Aegis.MaximumBeauty.maximum_beauty flowers m target full «partial» = ok r_m)
    (hr : Aegis.MaximumBeauty.maximum_beauty flowers newFlowers target full «partial» = ok r) :
    r_m.val ≤ r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (flowers : Slice Std.I64) (newFlowers target full «partial» : Std.I64)
    (hpre : Preconditions flowers newFlowers target full «partial»)
    (m : Std.I64) (hm0 : 0 ≤ m.val) (hmn : m.val ≤ newFlowers.val)
    (r_m r : Std.I64)
    (hrm : Aegis.MaximumBeauty.maximum_beauty flowers m target full «partial» = ok r_m)
    (hr : Aegis.MaximumBeauty.maximum_beauty flowers newFlowers target full «partial» = ok r), r_m.val ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r: if x >= target then r = full; else if newFlowers >= target - x then r = max(full, (target - 1)*partial); else r = (x + newFlowers)*partial.
  Preconditions: Let n = len(flowers). 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= flowers[i] <= 100000; 0 <= newFlowers <= 10000000000; 1 <= target <= 100000; 1 <= full <= 100000; 1 <= partial <= 100000. All input values are within the signed 64-bit range. Additionally, n = 1, and let x = flowers[0]. -/
theorem spec_12 (flowers : Slice Std.I64) (newFlowers target full «partial» : Std.I64)
    (hpre : Preconditions flowers newFlowers target full «partial»)
    (hn : flowers.leng = 1) (x : ℤ) (hx : (contents flowers)[0]? = some x)
    (r : Std.I64)
    (hr : Aegis.MaximumBeauty.maximum_beauty flowers newFlowers target full «partial» = ok r) :
    (target.val ≤ x → r.val = full.val) ∧
      (x < target.val → target.val - x ≤ newFlowers.val →
        r.val = max full.val ((target.val - 1) * «partial».val)) ∧
      (x < target.val → newFlowers.val < target.val - x →
        r.val = (x + newFlowers.val) * «partial».val) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (flowers : Slice Std.I64) (newFlowers target full «partial» : Std.I64)
    (hpre : Preconditions flowers newFlowers target full «partial»)
    (hn : flowers.leng = 1) (x : ℤ) (hx : (contents flowers)[0]? = some x)
    (r : Std.I64)
    (hr : Aegis.MaximumBeauty.maximum_beauty flowers newFlowers target full «partial» = ok r), (target.val ≤ x → r.val = full.val) ∧
      (x < target.val → target.val - x ≤ newFlowers.val →
        r.val = max full.val ((target.val - 1) * «partial».val)) ∧
      (x < target.val → newFlowers.val < target.val - x →
        r.val = (x + newFlowers.val) * «partial».val)) := by
  sorry

/-- Whenever the function returns a result r, r = max(n*full, (n-1)*full + (target - 1)*partial).
  Preconditions: Let n = len(flowers). 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= flowers[i] <= 100000; 0 <= newFlowers <= 10000000000; 1 <= target <= 100000; 1 <= full <= 100000; 1 <= partial <= 100000. All input values are within the signed 64-bit range. Let D = sum over i with 0 <= i < n and flowers[i] < target of (target - flowers[i]). Additionally, D <= newFlowers and D > 0. -/
theorem spec_13 (flowers : Slice Std.I64) (newFlowers target full «partial» : Std.I64)
    (hpre : Preconditions flowers newFlowers target full «partial»)
    (hd : deficit target.val (contents flowers) ≤ newFlowers.val)
    (hd0 : 0 < deficit target.val (contents flowers))
    (r : Std.I64)
    (hr : Aegis.MaximumBeauty.maximum_beauty flowers newFlowers target full «partial» = ok r) :
    r.val = max ((flowers.leng : ℤ) * full.val)
      (((flowers.leng : ℤ) - 1) * full.val + (target.val - 1) * «partial».val) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (flowers : Slice Std.I64) (newFlowers target full «partial» : Std.I64)
    (hpre : Preconditions flowers newFlowers target full «partial»)
    (hd : deficit target.val (contents flowers) ≤ newFlowers.val)
    (hd0 : 0 < deficit target.val (contents flowers))
    (r : Std.I64)
    (hr : Aegis.MaximumBeauty.maximum_beauty flowers newFlowers target full «partial» = ok r), r.val = max ((flowers.leng : ℤ) * full.val)
      (((flowers.leng : ℤ) - 1) * full.val + (target.val - 1) * «partial».val)) := by
  sorry

/-- Whenever the function returns a result r, r <= max(n*full, (n-1)*full + (target - 1)*partial).
  Preconditions: Let n = len(flowers). 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= flowers[i] <= 100000; 0 <= newFlowers <= 10000000000; 1 <= target <= 100000; 1 <= full <= 100000; 1 <= partial <= 100000. All input values are within the signed 64-bit range. -/
theorem spec_14 (flowers : Slice Std.I64) (newFlowers target full «partial» : Std.I64)
    (hpre : Preconditions flowers newFlowers target full «partial»)
    (r : Std.I64)
    (hr : Aegis.MaximumBeauty.maximum_beauty flowers newFlowers target full «partial» = ok r) :
    r.val ≤ max ((flowers.leng : ℤ) * full.val)
      (((flowers.leng : ℤ) - 1) * full.val + (target.val - 1) * «partial».val) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (flowers : Slice Std.I64) (newFlowers target full «partial» : Std.I64)
    (hpre : Preconditions flowers newFlowers target full «partial»)
    (r : Std.I64)
    (hr : Aegis.MaximumBeauty.maximum_beauty flowers newFlowers target full «partial» = ok r), r.val ≤ max ((flowers.leng : ℤ) * full.val)
      (((flowers.leng : ℤ) - 1) * full.val + (target.val - 1) * «partial».val)) := by
  sorry

end AegisSpec.MaximumBeauty
