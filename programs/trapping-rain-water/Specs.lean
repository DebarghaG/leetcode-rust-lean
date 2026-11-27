import Aegis.Trap.Code.Funs

/-!
# Specifications of `Aegis.Trap.trap`

LeetCode problem `trapping-rain-water`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.Trap

  open scoped BigOperators

  def hts (height : Slice Std.I64) : List ℤ := height.val.map (fun x => x.val)

  def elem (height : Slice Std.I64) (i : ℕ) : ℤ :=
    ((height.val[i]?).map (fun x => x.val)).getD 0

  @[simp] theorem hts_length (height : Slice Std.I64) :
      (hts height).length = height.val.length := by
    simp [hts]

  @[simp] theorem hts_getD (height : Slice Std.I64) (i : ℕ) :
      (hts height).getD i 0 = elem height i := by
    simp [hts, elem]

  def prefMax (l : List ℤ) (i : ℕ) : ℤ := ((l.take (i + 1)).max?).getD 0

  def suffMax (l : List ℤ) (i : ℕ) : ℤ := ((l.drop i).max?).getD 0

  def maxAll (l : List ℤ) : ℤ := (l.max?).getD 0

  def trappedAt (l : List ℤ) (i : ℕ) : ℤ := min (prefMax l i) (suffMax l i) - l.getD i 0

  def totalTrapped (l : List ℤ) : ℤ := ∑ i ∈ Finset.range l.length, trappedAt l i

  noncomputable def layerCount (l : List ℤ) (t : ℤ) : ℕ := by
    classical
    exact ((Finset.range l.length).filter
      (fun i => l.getD i 0 < t ∧
        ∃ lo q : ℕ, lo < i ∧ i < q ∧ q < l.length ∧ t ≤ l.getD lo 0 ∧ t ≤ l.getD q 0)).card

  noncomputable def layerSum (l : List ℤ) : ℤ :=
    ∑ t ∈ Finset.Icc 1 (maxAll l).toNat, (layerCount l (t : ℤ) : ℤ)

  /-- The function returns a result r and r = sum_{i=0}^{n-1} (min(P_i, S_i) - height[i]), where for each i, P_i = max{ height[j] | 0 <= j <= i } and S_i = max{ height[j] | i <= j < n }.
    Preconditions: Let n = len(height). 1 <= n <= 20000 and for every i with 0 <= i < n, 0 <= height[i] <= 100000. -/
  theorem spec_1 (height : Slice Std.I64)
      (hn1 : 1 ≤ height.val.length) (hn2 : height.val.length ≤ 20000)
      (hb : ∀ i, i < height.val.length → 0 ≤ elem height i ∧ elem height i ≤ 100000) :
      ∃ r, Aegis.Trap.trap height = ok r ∧ r.val = totalTrapped (hts height) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (height : Slice Std.I64)
        (hn1 : 1 ≤ height.val.length) (hn2 : height.val.length ≤ 20000)
        (hb : ∀ i, i < height.val.length → 0 ≤ elem height i ∧ elem height i ≤ 100000), ∃ r, Aegis.Trap.trap height = ok r ∧ r.val = totalTrapped (hts height)) := by
    sorry

  /-- For every input satisfying these preconditions, the function returns a result; it does not panic, index out of bounds, or overflow.
    Preconditions: Let n = len(height). 1 <= n <= 20000 and for every i with 0 <= i < n, 0 <= height[i] <= 100000. -/
  theorem spec_2 (height : Slice Std.I64)
      (hn1 : 1 ≤ height.val.length) (hn2 : height.val.length ≤ 20000)
      (hb : ∀ i, i < height.val.length → 0 ≤ elem height i ∧ elem height i ≤ 100000) :
      ∃ r, Aegis.Trap.trap height = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (height : Slice Std.I64)
        (hn1 : 1 ≤ height.val.length) (hn2 : height.val.length ≤ 20000)
        (hb : ∀ i, i < height.val.length → 0 ≤ elem height i ∧ elem height i ≤ 100000), ∃ r, Aegis.Trap.trap height = ok r) := by
    sorry

  /-- Whenever the function returns a result r on an input satisfying these preconditions, 0 <= r.
    Preconditions: Let n = len(height). 1 <= n <= 20000 and for every i with 0 <= i < n, 0 <= height[i] <= 100000. -/
  theorem spec_3 (height : Slice Std.I64)
      (hn1 : 1 ≤ height.val.length) (hn2 : height.val.length ≤ 20000)
      (hb : ∀ i, i < height.val.length → 0 ≤ elem height i ∧ elem height i ≤ 100000) :
      ∀ r, Aegis.Trap.trap height = ok r → 0 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (height : Slice Std.I64)
        (hn1 : 1 ≤ height.val.length) (hn2 : height.val.length ≤ 20000)
        (hb : ∀ i, i < height.val.length → 0 ≤ elem height i ∧ elem height i ≤ 100000), ∀ r, Aegis.Trap.trap height = ok r → 0 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r on an input satisfying these preconditions, r <= n * M - sum_{i=0}^{n-1} height[i], where M = max{ height[j] | 0 <= j < n }.
    Preconditions: Let n = len(height). 1 <= n <= 20000 and for every i with 0 <= i < n, 0 <= height[i] <= 100000. -/
  theorem spec_4 (height : Slice Std.I64)
      (hn1 : 1 ≤ height.val.length) (hn2 : height.val.length ≤ 20000)
      (hb : ∀ i, i < height.val.length → 0 ≤ elem height i ∧ elem height i ≤ 100000) :
      ∀ r, Aegis.Trap.trap height = ok r →
        r.val ≤ (height.val.length : ℤ) * maxAll (hts height) - (hts height).sum := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (height : Slice Std.I64)
        (hn1 : 1 ≤ height.val.length) (hn2 : height.val.length ≤ 20000)
        (hb : ∀ i, i < height.val.length → 0 ≤ elem height i ∧ elem height i ≤ 100000), ∀ r, Aegis.Trap.trap height = ok r →
          r.val ≤ (height.val.length : ℤ) * maxAll (hts height) - (hts height).sum) := by
    sorry

  /-- Whenever the function returns a result r, r + sum_{i=0}^{n-1} height[i] = sum_{i=0}^{n-1} min(P_i, S_i), where P_i = max{ height[j] | 0 <= j <= i } and S_i = max{ height[j] | i <= j < n }.
    Preconditions: Let n = len(height). 1 <= n <= 20000 and for every i with 0 <= i < n, 0 <= height[i] <= 100000. -/
  theorem spec_5 (height : Slice Std.I64)
      (hn1 : 1 ≤ height.val.length) (hn2 : height.val.length ≤ 20000)
      (hb : ∀ i, i < height.val.length → 0 ≤ elem height i ∧ elem height i ≤ 100000) :
      ∀ r, Aegis.Trap.trap height = ok r →
        r.val + (hts height).sum = totalTrapped (hts height) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (height : Slice Std.I64)
        (hn1 : 1 ≤ height.val.length) (hn2 : height.val.length ≤ 20000)
        (hb : ∀ i, i < height.val.length → 0 ≤ elem height i ∧ elem height i ≤ 100000), ∀ r, Aegis.Trap.trap height = ok r →
          r.val + (hts height).sum = totalTrapped (hts height)) := by
    sorry

  /-- Whenever the function returns a result r on height, if rev is the slice of length n defined by rev[i] = height[n-1-i] for 0 <= i < n, and if the function returns a result r' on rev, then r' = r.
    Preconditions: Let n = len(height). 1 <= n <= 20000 and for every i with 0 <= i < n, 0 <= height[i] <= 100000. -/
  theorem spec_6 (height rev : Slice Std.I64)
      (hn1 : 1 ≤ height.val.length) (hn2 : height.val.length ≤ 20000)
      (hb : ∀ i, i < height.val.length → 0 ≤ elem height i ∧ elem height i ≤ 100000)
      (hrev : hts rev = (hts height).reverse) :
      ∀ r r', Aegis.Trap.trap height = ok r → Aegis.Trap.trap rev = ok r' →
        r'.val = r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (height rev : Slice Std.I64)
        (hn1 : 1 ≤ height.val.length) (hn2 : height.val.length ≤ 20000)
        (hb : ∀ i, i < height.val.length → 0 ≤ elem height i ∧ elem height i ≤ 100000)
        (hrev : hts rev = (hts height).reverse), ∀ r r', Aegis.Trap.trap height = ok r → Aegis.Trap.trap rev = ok r' →
          r'.val = r.val) := by
    sorry

  /-- Whenever the function returns a result r on height, for every integer c with 0 <= c and height[i] + c <= 100000 for all i with 0 <= i < n, if height' is defined by height'[i] = height[i] + c and the function returns a result r' on height', then r' = r.
    Preconditions: Let n = len(height). 1 <= n <= 20000 and for every i with 0 <= i < n, 0 <= height[i] <= 100000. -/
  theorem spec_7 (height height' : Slice Std.I64) (c : ℤ)
      (hn1 : 1 ≤ height.val.length) (hn2 : height.val.length ≤ 20000)
      (hb : ∀ i, i < height.val.length → 0 ≤ elem height i ∧ elem height i ≤ 100000)
      (hc : 0 ≤ c)
      (hb' : ∀ i, i < height.val.length → elem height i + c ≤ 100000)
      (hshift : hts height' = (hts height).map (fun x => x + c)) :
      ∀ r r', Aegis.Trap.trap height = ok r → Aegis.Trap.trap height' = ok r' →
        r'.val = r.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (height height' : Slice Std.I64) (c : ℤ)
        (hn1 : 1 ≤ height.val.length) (hn2 : height.val.length ≤ 20000)
        (hb : ∀ i, i < height.val.length → 0 ≤ elem height i ∧ elem height i ≤ 100000)
        (hc : 0 ≤ c)
        (hb' : ∀ i, i < height.val.length → elem height i + c ≤ 100000)
        (hshift : hts height' = (hts height).map (fun x => x + c)), ∀ r r', Aegis.Trap.trap height = ok r → Aegis.Trap.trap height' = ok r' →
          r'.val = r.val) := by
    sorry

  /-- Whenever the function returns a result r on such an input, r = 0.
    Preconditions: Let n = len(height). 1 <= n <= 20000, for every i with 0 <= i < n, 0 <= height[i] <= 100000, and height is either nondecreasing (height[i] <= height[j] for all 0 <= i < j < n) or nonincreasing (height[i] >= height[j] for all 0 <= i < j < n). -/
  theorem spec_8 (height : Slice Std.I64)
      (hn1 : 1 ≤ height.val.length) (hn2 : height.val.length ≤ 20000)
      (hb : ∀ i, i < height.val.length → 0 ≤ elem height i ∧ elem height i ≤ 100000)
      (hmono :
        (∀ i j, i < j → j < height.val.length → elem height i ≤ elem height j) ∨
        (∀ i j, i < j → j < height.val.length → elem height j ≤ elem height i)) :
      ∀ r, Aegis.Trap.trap height = ok r → r.val = 0 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (height : Slice Std.I64)
        (hn1 : 1 ≤ height.val.length) (hn2 : height.val.length ≤ 20000)
        (hb : ∀ i, i < height.val.length → 0 ≤ elem height i ∧ elem height i ≤ 100000)
        (hmono :
          (∀ i j, i < j → j < height.val.length → elem height i ≤ elem height j) ∨
          (∀ i j, i < j → j < height.val.length → elem height j ≤ elem height i)), ∀ r, Aegis.Trap.trap height = ok r → r.val = 0) := by
    sorry

  /-- Whenever the function returns a result r, r = 0.
    Preconditions: Let n = len(height). 1 <= n <= 2 and for every i with 0 <= i < n, 0 <= height[i] <= 100000. -/
  theorem spec_9 (height : Slice Std.I64)
      (hn1 : 1 ≤ height.val.length) (hn2 : height.val.length ≤ 2)
      (hb : ∀ i, i < height.val.length → 0 ≤ elem height i ∧ elem height i ≤ 100000) :
      ∀ r, Aegis.Trap.trap height = ok r → r.val = 0 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (height : Slice Std.I64)
        (hn1 : 1 ≤ height.val.length) (hn2 : height.val.length ≤ 2)
        (hb : ∀ i, i < height.val.length → 0 ≤ elem height i ∧ elem height i ≤ 100000), ∀ r, Aegis.Trap.trap height = ok r → r.val = 0) := by
    sorry

  /-- Whenever the function returns a result r, r = max(0, min(height[0], height[2]) - height[1]).
    Preconditions: Let n = len(height). n = 3 and for every i with 0 <= i < n, 0 <= height[i] <= 100000. -/
  theorem spec_10 (height : Slice Std.I64)
      (hn : height.val.length = 3)
      (hb : ∀ i, i < height.val.length → 0 ≤ elem height i ∧ elem height i ≤ 100000) :
      ∀ r, Aegis.Trap.trap height = ok r →
        r.val = max 0 (min (elem height 0) (elem height 2) - elem height 1) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (height : Slice Std.I64)
        (hn : height.val.length = 3)
        (hb : ∀ i, i < height.val.length → 0 ≤ elem height i ∧ elem height i ≤ 100000), ∀ r, Aegis.Trap.trap height = ok r →
          r.val = max 0 (min (elem height 0) (elem height 2) - elem height 1)) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 if and only if for every i with 0 <= i < n, height[i] = min(P_i, S_i), where P_i = max{ height[j] | 0 <= j <= i } and S_i = max{ height[j] | i <= j < n }.
    Preconditions: Let n = len(height). 1 <= n <= 20000 and for every i with 0 <= i < n, 0 <= height[i] <= 100000. -/
  theorem spec_11 (height : Slice Std.I64)
      (hn1 : 1 ≤ height.val.length) (hn2 : height.val.length ≤ 20000)
      (hb : ∀ i, i < height.val.length → 0 ≤ elem height i ∧ elem height i ≤ 100000) :
      ∀ r, Aegis.Trap.trap height = ok r →
        (r.val = 0 ↔
          ∀ i, i < height.val.length →
            elem height i = min (prefMax (hts height) i) (suffMax (hts height) i)) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (height : Slice Std.I64)
        (hn1 : 1 ≤ height.val.length) (hn2 : height.val.length ≤ 20000)
        (hb : ∀ i, i < height.val.length → 0 ≤ elem height i ∧ elem height i ≤ 100000), ∀ r, Aegis.Trap.trap height = ok r →
          (r.val = 0 ↔
            ∀ i, i < height.val.length →
              elem height i = min (prefMax (hts height) i) (suffMax (hts height) i))) := by
    sorry

  /-- Whenever the function returns a result r, let M = max{ height[j] | 0 <= j < n }. Then r = sum_{t=1}^{M} C_t, where for each integer t, C_t is the number of indices i with 0 <= i < n such that height[i] < t and there exist indices l and q with 0 <= l < i < q < n, height[l] >= t, and height[q] >= t.
    Preconditions: Let n = len(height). 1 <= n <= 20000 and for every i with 0 <= i < n, 0 <= height[i] <= 100000. -/
  theorem spec_12 (height : Slice Std.I64)
      (hn1 : 1 ≤ height.val.length) (hn2 : height.val.length ≤ 20000)
      (hb : ∀ i, i < height.val.length → 0 ≤ elem height i ∧ elem height i ≤ 100000) :
      ∀ r, Aegis.Trap.trap height = ok r →
        r.val = layerSum (hts height) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (height : Slice Std.I64)
        (hn1 : 1 ≤ height.val.length) (hn2 : height.val.length ≤ 20000)
        (hb : ∀ i, i < height.val.length → 0 ≤ elem height i ∧ elem height i ≤ 100000), ∀ r, Aegis.Trap.trap height = ok r →
          r.val = layerSum (hts height)) := by
    sorry

  /-- Whenever the function returns a result r, if n >= 2 then r = sum_{i=1}^{n-2} (min(P_i, S_i) - height[i]) (the sum is empty when n = 2), and if n = 1 then r = 0; here P_i = max{ height[j] | 0 <= j <= i } and S_i = max{ height[j] | i <= j < n }.
    Preconditions: Let n = len(height). 1 <= n <= 20000 and for every i with 0 <= i < n, 0 <= height[i] <= 100000. -/
  theorem spec_13 (height : Slice Std.I64)
      (hn1 : 1 ≤ height.val.length) (hn2 : height.val.length ≤ 20000)
      (hb : ∀ i, i < height.val.length → 0 ≤ elem height i ∧ elem height i ≤ 100000) :
      ∀ r, Aegis.Trap.trap height = ok r →
        (2 ≤ height.val.length →
            r.val = ∑ i ∈ Finset.Icc 1 (height.val.length - 2),
              trappedAt (hts height) i) ∧
        (height.val.length = 1 → r.val = 0) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (height : Slice Std.I64)
        (hn1 : 1 ≤ height.val.length) (hn2 : height.val.length ≤ 20000)
        (hb : ∀ i, i < height.val.length → 0 ≤ elem height i ∧ elem height i ≤ 100000), ∀ r, Aegis.Trap.trap height = ok r →
          (2 ≤ height.val.length →
              r.val = ∑ i ∈ Finset.Icc 1 (height.val.length - 2),
                trappedAt (hts height) i) ∧
          (height.val.length = 1 → r.val = 0)) := by
    sorry

  /-- Whenever the function returns a result r, r <= sum_{i=1}^{n-2} (M - height[i]), where M = max{ height[j] | 0 <= j < n }.
    Preconditions: Let n = len(height). 3 <= n <= 20000 and for every i with 0 <= i < n, 0 <= height[i] <= 100000. -/
  theorem spec_14 (height : Slice Std.I64)
      (hn1 : 3 ≤ height.val.length) (hn2 : height.val.length ≤ 20000)
      (hb : ∀ i, i < height.val.length → 0 ≤ elem height i ∧ elem height i ≤ 100000) :
      ∀ r, Aegis.Trap.trap height = ok r →
        r.val ≤ ∑ i ∈ Finset.Icc 1 (height.val.length - 2),
          (maxAll (hts height) - elem height i) := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (height : Slice Std.I64)
        (hn1 : 3 ≤ height.val.length) (hn2 : height.val.length ≤ 20000)
        (hb : ∀ i, i < height.val.length → 0 ≤ elem height i ∧ elem height i ≤ 100000), ∀ r, Aegis.Trap.trap height = ok r →
          r.val ≤ ∑ i ∈ Finset.Icc 1 (height.val.length - 2),
            (maxAll (hts height) - elem height i)) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < n, r >= min(P_i, S_i) - height[i], where P_i = max{ height[j] | 0 <= j <= i } and S_i = max{ height[j] | i <= j < n }.
    Preconditions: Let n = len(height). 1 <= n <= 20000 and for every i with 0 <= i < n, 0 <= height[i] <= 100000. -/
  theorem spec_15 (height : Slice Std.I64)
      (hn1 : 1 ≤ height.val.length) (hn2 : height.val.length ≤ 20000)
      (hb : ∀ i, i < height.val.length → 0 ≤ elem height i ∧ elem height i ≤ 100000) :
      ∀ r, Aegis.Trap.trap height = ok r →
        ∀ i, i < height.val.length →
          r.val ≥ min (prefMax (hts height) i) (suffMax (hts height) i) - elem height i := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (height : Slice Std.I64)
        (hn1 : 1 ≤ height.val.length) (hn2 : height.val.length ≤ 20000)
        (hb : ∀ i, i < height.val.length → 0 ≤ elem height i ∧ elem height i ≤ 100000), ∀ r, Aegis.Trap.trap height = ok r →
          ∀ i, i < height.val.length →
            r.val ≥ min (prefMax (hts height) i) (suffMax (hts height) i) - elem height i) := by
    sorry

  /-- If height' is defined by height'[i] = k * height[i] for 0 <= i < n, and the function returns r on height and r' on height', then r' = k * r.
    Preconditions: Let n = len(height). 1 <= n <= 20000, for every i with 0 <= i < n, 0 <= height[i] <= 100000, and let k be an integer with 0 <= k and k * height[i] <= 100000 for every i. -/
  theorem spec_16 (height height' : Slice Std.I64) (k : ℤ)
      (hn1 : 1 ≤ height.val.length) (hn2 : height.val.length ≤ 20000)
      (hb : ∀ i, i < height.val.length → 0 ≤ elem height i ∧ elem height i ≤ 100000)
      (hk : 0 ≤ k)
      (hk' : ∀ i, i < height.val.length → k * elem height i ≤ 100000)
      (hscale : hts height' = (hts height).map (fun x => k * x)) :
      ∀ r r', Aegis.Trap.trap height = ok r → Aegis.Trap.trap height' = ok r' →
        r'.val = k * r.val := by
    sorry

  theorem spec_16_neg :
      ¬ (∀ (height height' : Slice Std.I64) (k : ℤ)
        (hn1 : 1 ≤ height.val.length) (hn2 : height.val.length ≤ 20000)
        (hb : ∀ i, i < height.val.length → 0 ≤ elem height i ∧ elem height i ≤ 100000)
        (hk : 0 ≤ k)
        (hk' : ∀ i, i < height.val.length → k * elem height i ≤ 100000)
        (hscale : hts height' = (hts height).map (fun x => k * x)), ∀ r r', Aegis.Trap.trap height = ok r → Aegis.Trap.trap height' = ok r' →
          r'.val = k * r.val) := by
    sorry

  /-- If the function returns r on height and r' on height', then r' = r.
    Preconditions: Let n = len(height). 1 <= n < 20000 and for every i with 0 <= i < n, 0 <= height[i] <= 100000. Define height' of length n+1 by height'[0] = 0 and height'[i+1] = height[i] for 0 <= i < n. -/
  theorem spec_17 (height height' : Slice Std.I64)
      (hn1 : 1 ≤ height.val.length) (hn2 : height.val.length < 20000)
      (hb : ∀ i, i < height.val.length → 0 ≤ elem height i ∧ elem height i ≤ 100000)
      (hpad : hts height' = 0 :: hts height) :
      ∀ r r', Aegis.Trap.trap height = ok r → Aegis.Trap.trap height' = ok r' →
        r'.val = r.val := by
    sorry

  theorem spec_17_neg :
      ¬ (∀ (height height' : Slice Std.I64)
        (hn1 : 1 ≤ height.val.length) (hn2 : height.val.length < 20000)
        (hb : ∀ i, i < height.val.length → 0 ≤ elem height i ∧ elem height i ≤ 100000)
        (hpad : hts height' = 0 :: hts height), ∀ r r', Aegis.Trap.trap height = ok r → Aegis.Trap.trap height' = ok r' →
          r'.val = r.val) := by
    sorry

  end AegisSpec.Trap
