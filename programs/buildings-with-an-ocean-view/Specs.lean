import Aegis.FindBuildings.Code.Funs

/-!
# Specifications of `Aegis.FindBuildings.find_buildings`

LeetCode problem `buildings-with-an-ocean-view`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.FindBuildings

  def elem (l : List Std.I64) (i : Nat) : Int :=
    match l[i]? with
    | some x => x.val
    | none => 0

  def elemNat (l : List Std.I64) (k : Nat) : Nat :=
    (elem l k).toNat

  @[reducible]
  def OceanView (l : List Std.I64) (i : Nat) : Prop :=
    i < l.length ∧ ∀ j ∈ List.range l.length, i < j → elem l j < elem l i

  def oceanViewCount (l : List Std.I64) : Nat :=
    ((List.range l.length).filter (fun i => decide (OceanView l i))).length

  /-- Define an index i to have an ocean view when 0 <= i < len(heights) and for every j with i < j < len(heights), heights[j] < heights[i]. Under the preconditions, the function returns a result r (it does not fail), and r is exactly the list of all indices that have an ocean view, in increasing order. Equivalently: for every k with 0 <= k < len(r), r[k] has an ocean view; for every i that has an ocean view there is exactly one k with 0 <= k < len(r) and r[k] = i; and for every k with 0 <= k < len(r) - 1, r[k] < r[k + 1].
    Preconditions: len(heights) >= 1, len(heights) <= 100000, and for every i with 0 <= i < len(heights), 1 <= heights[i] <= 1000000000. -/
  theorem spec_1
      (heights : Slice Std.I64)
      (hlen1 : 1 ≤ heights.val.length)
      (hlen2 : heights.val.length ≤ 100000)
      (hval : ∀ i, i < heights.val.length →
        1 ≤ elem heights.val i ∧ elem heights.val i ≤ 1000000000) :
      ∃ r, Aegis.FindBuildings.find_buildings heights = ok r ∧
        (∀ k, k < r.val.length → OceanView heights.val (elemNat r.val k)) ∧
        (∀ i, OceanView heights.val i →
          ∃! k, k < r.val.length ∧ elem r.val k = (i : Int)) ∧
        (∀ k, k + 1 < r.val.length → elem r.val k < elem r.val (k + 1)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (heights : Slice Std.I64)
        (hlen1 : 1 ≤ heights.val.length)
        (hlen2 : heights.val.length ≤ 100000)
        (hval : ∀ i, i < heights.val.length →
          1 ≤ elem heights.val i ∧ elem heights.val i ≤ 1000000000), ∃ r, Aegis.FindBuildings.find_buildings heights = ok r ∧
          (∀ k, k < r.val.length → OceanView heights.val (elemNat r.val k)) ∧
          (∀ i, OceanView heights.val i →
            ∃! k, k < r.val.length ∧ elem r.val k = (i : Int)) ∧
          (∀ k, k + 1 < r.val.length → elem r.val k < elem r.val (k + 1))) := by
    sorry

  /-- Under the preconditions, find_buildings returns successfully: there exists a vector r such that the result is r. It does not fail with overflow, out-of-bounds, or panic.
    Preconditions: len(heights) >= 1, len(heights) <= 100000, and for every i with 0 <= i < len(heights), 1 <= heights[i] <= 1000000000. -/
  theorem spec_2
      (heights : Slice Std.I64)
      (hlen1 : 1 ≤ heights.val.length)
      (hlen2 : heights.val.length ≤ 100000)
      (hval : ∀ i, i < heights.val.length →
        1 ≤ elem heights.val i ∧ elem heights.val i ≤ 1000000000) :
      ∃ r, Aegis.FindBuildings.find_buildings heights = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (heights : Slice Std.I64)
        (hlen1 : 1 ≤ heights.val.length)
        (hlen2 : heights.val.length ≤ 100000)
        (hval : ∀ i, i < heights.val.length →
          1 ≤ elem heights.val i ∧ elem heights.val i ≤ 1000000000), ∃ r, Aegis.FindBuildings.find_buildings heights = ok r) := by
    sorry

  /-- Whenever find_buildings returns a result r, for every k with 0 <= k < len(r), 0 <= r[k] < len(heights).
    Preconditions: len(heights) >= 1, len(heights) <= 100000, and for every i with 0 <= i < len(heights), 1 <= heights[i] <= 1000000000. -/
  theorem spec_3
      (heights : Slice Std.I64)
      (hlen1 : 1 ≤ heights.val.length)
      (hlen2 : heights.val.length ≤ 100000)
      (hval : ∀ i, i < heights.val.length →
        1 ≤ elem heights.val i ∧ elem heights.val i ≤ 1000000000) :
      ∀ r, Aegis.FindBuildings.find_buildings heights = ok r →
        ∀ k, k < r.val.length →
          0 ≤ elem r.val k ∧ elem r.val k < (heights.val.length : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (heights : Slice Std.I64)
        (hlen1 : 1 ≤ heights.val.length)
        (hlen2 : heights.val.length ≤ 100000)
        (hval : ∀ i, i < heights.val.length →
          1 ≤ elem heights.val i ∧ elem heights.val i ≤ 1000000000), ∀ r, Aegis.FindBuildings.find_buildings heights = ok r →
          ∀ k, k < r.val.length →
            0 ≤ elem r.val k ∧ elem r.val k < (heights.val.length : Int)) := by
    sorry

  /-- Whenever find_buildings returns a result r, for every k with 0 <= k < len(r) - 1, r[k] < r[k + 1].
    Preconditions: len(heights) >= 1, len(heights) <= 100000, and for every i with 0 <= i < len(heights), 1 <= heights[i] <= 1000000000. -/
  theorem spec_4
      (heights : Slice Std.I64)
      (hlen1 : 1 ≤ heights.val.length)
      (hlen2 : heights.val.length ≤ 100000)
      (hval : ∀ i, i < heights.val.length →
        1 ≤ elem heights.val i ∧ elem heights.val i ≤ 1000000000) :
      ∀ r, Aegis.FindBuildings.find_buildings heights = ok r →
        ∀ k, k + 1 < r.val.length → elem r.val k < elem r.val (k + 1) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (heights : Slice Std.I64)
        (hlen1 : 1 ≤ heights.val.length)
        (hlen2 : heights.val.length ≤ 100000)
        (hval : ∀ i, i < heights.val.length →
          1 ≤ elem heights.val i ∧ elem heights.val i ≤ 1000000000), ∀ r, Aegis.FindBuildings.find_buildings heights = ok r →
          ∀ k, k + 1 < r.val.length → elem r.val k < elem r.val (k + 1)) := by
    sorry

  /-- Whenever find_buildings returns a result r, len(r) >= 1.
    Preconditions: len(heights) >= 1, len(heights) <= 100000, and for every i with 0 <= i < len(heights), 1 <= heights[i] <= 1000000000. -/
  theorem spec_5
      (heights : Slice Std.I64)
      (hlen1 : 1 ≤ heights.val.length)
      (hlen2 : heights.val.length ≤ 100000)
      (hval : ∀ i, i < heights.val.length →
        1 ≤ elem heights.val i ∧ elem heights.val i ≤ 1000000000) :
      ∀ r, Aegis.FindBuildings.find_buildings heights = ok r → 1 ≤ r.val.length := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (heights : Slice Std.I64)
        (hlen1 : 1 ≤ heights.val.length)
        (hlen2 : heights.val.length ≤ 100000)
        (hval : ∀ i, i < heights.val.length →
          1 ≤ elem heights.val i ∧ elem heights.val i ≤ 1000000000), ∀ r, Aegis.FindBuildings.find_buildings heights = ok r → 1 ≤ r.val.length) := by
    sorry

  /-- Whenever find_buildings returns a result r, there exists k with 0 <= k < len(r) and r[k] = len(heights) - 1.
    Preconditions: len(heights) >= 1, len(heights) <= 100000, and for every i with 0 <= i < len(heights), 1 <= heights[i] <= 1000000000. -/
  theorem spec_6
      (heights : Slice Std.I64)
      (hlen1 : 1 ≤ heights.val.length)
      (hlen2 : heights.val.length ≤ 100000)
      (hval : ∀ i, i < heights.val.length →
        1 ≤ elem heights.val i ∧ elem heights.val i ≤ 1000000000) :
      ∀ r, Aegis.FindBuildings.find_buildings heights = ok r →
        ∃ k, k < r.val.length ∧ elem r.val k = (heights.val.length : Int) - 1 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (heights : Slice Std.I64)
        (hlen1 : 1 ≤ heights.val.length)
        (hlen2 : heights.val.length ≤ 100000)
        (hval : ∀ i, i < heights.val.length →
          1 ≤ elem heights.val i ∧ elem heights.val i ≤ 1000000000), ∀ r, Aegis.FindBuildings.find_buildings heights = ok r →
          ∃ k, k < r.val.length ∧ elem r.val k = (heights.val.length : Int) - 1) := by
    sorry

  /-- Whenever find_buildings returns a result r, len(r) >= 1 and r[len(r) - 1] = len(heights) - 1.
    Preconditions: len(heights) >= 1, len(heights) <= 100000, and for every i with 0 <= i < len(heights), 1 <= heights[i] <= 1000000000. -/
  theorem spec_7
      (heights : Slice Std.I64)
      (hlen1 : 1 ≤ heights.val.length)
      (hlen2 : heights.val.length ≤ 100000)
      (hval : ∀ i, i < heights.val.length →
        1 ≤ elem heights.val i ∧ elem heights.val i ≤ 1000000000) :
      ∀ r, Aegis.FindBuildings.find_buildings heights = ok r →
        1 ≤ r.val.length ∧
          elem r.val (r.val.length - 1) = (heights.val.length : Int) - 1 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (heights : Slice Std.I64)
        (hlen1 : 1 ≤ heights.val.length)
        (hlen2 : heights.val.length ≤ 100000)
        (hval : ∀ i, i < heights.val.length →
          1 ≤ elem heights.val i ∧ elem heights.val i ≤ 1000000000), ∀ r, Aegis.FindBuildings.find_buildings heights = ok r →
          1 ≤ r.val.length ∧
            elem r.val (r.val.length - 1) = (heights.val.length : Int) - 1) := by
    sorry

  /-- If all heights are equal, that is for every i with 0 <= i < len(heights), heights[i] = heights[0], then whenever find_buildings returns a result r, len(r) = 1 and r[0] = len(heights) - 1.
    Preconditions: len(heights) >= 1, len(heights) <= 100000, and for every i with 0 <= i < len(heights), 1 <= heights[i] <= 1000000000. -/
  theorem spec_8
      (heights : Slice Std.I64)
      (hlen1 : 1 ≤ heights.val.length)
      (hlen2 : heights.val.length ≤ 100000)
      (hval : ∀ i, i < heights.val.length →
        1 ≤ elem heights.val i ∧ elem heights.val i ≤ 1000000000)
      (heq : ∀ i, i < heights.val.length → elem heights.val i = elem heights.val 0) :
      ∀ r, Aegis.FindBuildings.find_buildings heights = ok r →
        r.val.length = 1 ∧ elem r.val 0 = (heights.val.length : Int) - 1 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (heights : Slice Std.I64)
        (hlen1 : 1 ≤ heights.val.length)
        (hlen2 : heights.val.length ≤ 100000)
        (hval : ∀ i, i < heights.val.length →
          1 ≤ elem heights.val i ∧ elem heights.val i ≤ 1000000000)
        (heq : ∀ i, i < heights.val.length → elem heights.val i = elem heights.val 0), ∀ r, Aegis.FindBuildings.find_buildings heights = ok r →
          r.val.length = 1 ∧ elem r.val 0 = (heights.val.length : Int) - 1) := by
    sorry

  /-- If for every i with 0 <= i < len(heights) - 1, heights[i] > heights[i + 1], then whenever find_buildings returns a result r, len(r) = len(heights) and for every k with 0 <= k < len(r), r[k] = k.
    Preconditions: len(heights) >= 1, len(heights) <= 100000, and for every i with 0 <= i < len(heights), 1 <= heights[i] <= 1000000000. -/
  theorem spec_9
      (heights : Slice Std.I64)
      (hlen1 : 1 ≤ heights.val.length)
      (hlen2 : heights.val.length ≤ 100000)
      (hval : ∀ i, i < heights.val.length →
        1 ≤ elem heights.val i ∧ elem heights.val i ≤ 1000000000)
      (hdec : ∀ i, i + 1 < heights.val.length →
        elem heights.val (i + 1) < elem heights.val i) :
      ∀ r, Aegis.FindBuildings.find_buildings heights = ok r →
        r.val.length = heights.val.length ∧
          ∀ k, k < r.val.length → elem r.val k = (k : Int) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (heights : Slice Std.I64)
        (hlen1 : 1 ≤ heights.val.length)
        (hlen2 : heights.val.length ≤ 100000)
        (hval : ∀ i, i < heights.val.length →
          1 ≤ elem heights.val i ∧ elem heights.val i ≤ 1000000000)
        (hdec : ∀ i, i + 1 < heights.val.length →
          elem heights.val (i + 1) < elem heights.val i), ∀ r, Aegis.FindBuildings.find_buildings heights = ok r →
          r.val.length = heights.val.length ∧
            ∀ k, k < r.val.length → elem r.val k = (k : Int)) := by
    sorry

  /-- If for every i with 0 <= i < len(heights) - 1, heights[i] < heights[i + 1], then whenever find_buildings returns a result r, len(r) = 1 and r[0] = len(heights) - 1.
    Preconditions: len(heights) >= 1, len(heights) <= 100000, and for every i with 0 <= i < len(heights), 1 <= heights[i] <= 1000000000. -/
  theorem spec_10
      (heights : Slice Std.I64)
      (hlen1 : 1 ≤ heights.val.length)
      (hlen2 : heights.val.length ≤ 100000)
      (hval : ∀ i, i < heights.val.length →
        1 ≤ elem heights.val i ∧ elem heights.val i ≤ 1000000000)
      (hinc : ∀ i, i + 1 < heights.val.length →
        elem heights.val i < elem heights.val (i + 1)) :
      ∀ r, Aegis.FindBuildings.find_buildings heights = ok r →
        r.val.length = 1 ∧ elem r.val 0 = (heights.val.length : Int) - 1 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (heights : Slice Std.I64)
        (hlen1 : 1 ≤ heights.val.length)
        (hlen2 : heights.val.length ≤ 100000)
        (hval : ∀ i, i < heights.val.length →
          1 ≤ elem heights.val i ∧ elem heights.val i ≤ 1000000000)
        (hinc : ∀ i, i + 1 < heights.val.length →
          elem heights.val i < elem heights.val (i + 1)), ∀ r, Aegis.FindBuildings.find_buildings heights = ok r →
          r.val.length = 1 ∧ elem r.val 0 = (heights.val.length : Int) - 1) := by
    sorry

  /-- Whenever find_buildings returns a result r, for every index i with 0 <= i < len(heights) that does not occur in r (that is, r[k] != i for all k with 0 <= k < len(r)), there exists j with i < j < len(heights) and heights[j] >= heights[i].
    Preconditions: len(heights) >= 1, len(heights) <= 100000, and for every i with 0 <= i < len(heights), 1 <= heights[i] <= 1000000000. -/
  theorem spec_11
      (heights : Slice Std.I64)
      (hlen1 : 1 ≤ heights.val.length)
      (hlen2 : heights.val.length ≤ 100000)
      (hval : ∀ i, i < heights.val.length →
        1 ≤ elem heights.val i ∧ elem heights.val i ≤ 1000000000) :
      ∀ r, Aegis.FindBuildings.find_buildings heights = ok r →
        ∀ i, i < heights.val.length →
          (∀ k, k < r.val.length → elem r.val k ≠ (i : Int)) →
            ∃ j, i < j ∧ j < heights.val.length ∧
              elem heights.val i ≤ elem heights.val j := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (heights : Slice Std.I64)
        (hlen1 : 1 ≤ heights.val.length)
        (hlen2 : heights.val.length ≤ 100000)
        (hval : ∀ i, i < heights.val.length →
          1 ≤ elem heights.val i ∧ elem heights.val i ≤ 1000000000), ∀ r, Aegis.FindBuildings.find_buildings heights = ok r →
          ∀ i, i < heights.val.length →
            (∀ k, k < r.val.length → elem r.val k ≠ (i : Int)) →
              ∃ j, i < j ∧ j < heights.val.length ∧
                elem heights.val i ≤ elem heights.val j) := by
    sorry

  /-- Whenever find_buildings returns a result r, for every k with 0 <= k < len(r) and every j with r[k] < j < len(heights), heights[j] < heights[r[k]].
    Preconditions: len(heights) >= 1, len(heights) <= 100000, and for every i with 0 <= i < len(heights), 1 <= heights[i] <= 1000000000. -/
  theorem spec_12
      (heights : Slice Std.I64)
      (hlen1 : 1 ≤ heights.val.length)
      (hlen2 : heights.val.length ≤ 100000)
      (hval : ∀ i, i < heights.val.length →
        1 ≤ elem heights.val i ∧ elem heights.val i ≤ 1000000000) :
      ∀ r, Aegis.FindBuildings.find_buildings heights = ok r →
        ∀ k, k < r.val.length →
          ∀ j, elemNat r.val k < j → j < heights.val.length →
            elem heights.val j < elem heights.val (elemNat r.val k) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (heights : Slice Std.I64)
        (hlen1 : 1 ≤ heights.val.length)
        (hlen2 : heights.val.length ≤ 100000)
        (hval : ∀ i, i < heights.val.length →
          1 ≤ elem heights.val i ∧ elem heights.val i ≤ 1000000000), ∀ r, Aegis.FindBuildings.find_buildings heights = ok r →
          ∀ k, k < r.val.length →
            ∀ j, elemNat r.val k < j → j < heights.val.length →
              elem heights.val j < elem heights.val (elemNat r.val k)) := by
    sorry

  /-- Whenever find_buildings returns a result r, for every k with 0 <= k < len(r) - 1, heights[r[k]] > heights[r[k + 1]].
    Preconditions: len(heights) >= 1, len(heights) <= 100000, and for every i with 0 <= i < len(heights), 1 <= heights[i] <= 1000000000. -/
  theorem spec_13
      (heights : Slice Std.I64)
      (hlen1 : 1 ≤ heights.val.length)
      (hlen2 : heights.val.length ≤ 100000)
      (hval : ∀ i, i < heights.val.length →
        1 ≤ elem heights.val i ∧ elem heights.val i ≤ 1000000000) :
      ∀ r, Aegis.FindBuildings.find_buildings heights = ok r →
        ∀ k, k + 1 < r.val.length →
          elem heights.val (elemNat r.val (k + 1)) <
            elem heights.val (elemNat r.val k) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (heights : Slice Std.I64)
        (hlen1 : 1 ≤ heights.val.length)
        (hlen2 : heights.val.length ≤ 100000)
        (hval : ∀ i, i < heights.val.length →
          1 ≤ elem heights.val i ∧ elem heights.val i ≤ 1000000000), ∀ r, Aegis.FindBuildings.find_buildings heights = ok r →
          ∀ k, k + 1 < r.val.length →
            elem heights.val (elemNat r.val (k + 1)) <
              elem heights.val (elemNat r.val k)) := by
    sorry

  /-- Whenever find_buildings returns a result r, len(r) equals the number of indices i with 0 <= i < len(heights) and for every j with i < j < len(heights), heights[j] < heights[i].
    Preconditions: len(heights) >= 1, len(heights) <= 100000, and for every i with 0 <= i < len(heights), 1 <= heights[i] <= 1000000000. -/
  theorem spec_14
      (heights : Slice Std.I64)
      (hlen1 : 1 ≤ heights.val.length)
      (hlen2 : heights.val.length ≤ 100000)
      (hval : ∀ i, i < heights.val.length →
        1 ≤ elem heights.val i ∧ elem heights.val i ≤ 1000000000) :
      ∀ r, Aegis.FindBuildings.find_buildings heights = ok r →
        r.val.length = oceanViewCount heights.val := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (heights : Slice Std.I64)
        (hlen1 : 1 ≤ heights.val.length)
        (hlen2 : heights.val.length ≤ 100000)
        (hval : ∀ i, i < heights.val.length →
          1 ≤ elem heights.val i ∧ elem heights.val i ≤ 1000000000), ∀ r, Aegis.FindBuildings.find_buildings heights = ok r →
          r.val.length = oceanViewCount heights.val) := by
    sorry

  /-- Whenever find_buildings returns a result r, len(r) >= 1, the index r[0] has an ocean view (for every j with r[0] < j < len(heights), heights[j] < heights[r[0]]), and no index i with 0 <= i < r[0] has an ocean view (that is, for every such i there exists j with i < j < len(heights) and heights[j] >= heights[i]).
    Preconditions: len(heights) >= 1, len(heights) <= 100000, and for every i with 0 <= i < len(heights), 1 <= heights[i] <= 1000000000. -/
  theorem spec_15
      (heights : Slice Std.I64)
      (hlen1 : 1 ≤ heights.val.length)
      (hlen2 : heights.val.length ≤ 100000)
      (hval : ∀ i, i < heights.val.length →
        1 ≤ elem heights.val i ∧ elem heights.val i ≤ 1000000000) :
      ∀ r, Aegis.FindBuildings.find_buildings heights = ok r →
        1 ≤ r.val.length ∧
          OceanView heights.val (elemNat r.val 0) ∧
          ∀ i, i < elemNat r.val 0 →
            ∃ j, i < j ∧ j < heights.val.length ∧
              elem heights.val i ≤ elem heights.val j := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (heights : Slice Std.I64)
        (hlen1 : 1 ≤ heights.val.length)
        (hlen2 : heights.val.length ≤ 100000)
        (hval : ∀ i, i < heights.val.length →
          1 ≤ elem heights.val i ∧ elem heights.val i ≤ 1000000000), ∀ r, Aegis.FindBuildings.find_buildings heights = ok r →
          1 ≤ r.val.length ∧
            OceanView heights.val (elemNat r.val 0) ∧
            ∀ i, i < elemNat r.val 0 →
              ∃ j, i < j ∧ j < heights.val.length ∧
                elem heights.val i ≤ elem heights.val j) := by
    sorry

  /-- For any slice h' of the same length as heights that also satisfies the problem constraints, and any integer C such that h'[i] = heights[i] + C for every i, whenever find_buildings(heights) returns r and find_buildings(h') returns r', the sequences r and r' are equal.
    Preconditions: len(heights) >= 1, len(heights) <= 100000, and for every i with 0 <= i < len(heights), 1 <= heights[i] <= 1000000000. -/
  theorem spec_16
      (heights : Slice Std.I64)
      (hlen1 : 1 ≤ heights.val.length)
      (hlen2 : heights.val.length ≤ 100000)
      (hval : ∀ i, i < heights.val.length →
        1 ≤ elem heights.val i ∧ elem heights.val i ≤ 1000000000)
      (h' : Slice Std.I64) (C : Int)
      (hlen' : h'.val.length = heights.val.length)
      (hlen1' : 1 ≤ h'.val.length)
      (hlen2' : h'.val.length ≤ 100000)
      (hval' : ∀ i, i < h'.val.length →
        1 ≤ elem h'.val i ∧ elem h'.val i ≤ 1000000000)
      (hshift : ∀ i, i < heights.val.length →
        elem h'.val i = elem heights.val i + C) :
      ∀ r r', Aegis.FindBuildings.find_buildings heights = ok r →
        Aegis.FindBuildings.find_buildings h' = ok r' → r.val = r'.val := by
    sorry

  theorem spec_16_neg :
      ¬ (∀ (heights : Slice Std.I64)
        (hlen1 : 1 ≤ heights.val.length)
        (hlen2 : heights.val.length ≤ 100000)
        (hval : ∀ i, i < heights.val.length →
          1 ≤ elem heights.val i ∧ elem heights.val i ≤ 1000000000)
        (h' : Slice Std.I64) (C : Int)
        (hlen' : h'.val.length = heights.val.length)
        (hlen1' : 1 ≤ h'.val.length)
        (hlen2' : h'.val.length ≤ 100000)
        (hval' : ∀ i, i < h'.val.length →
          1 ≤ elem h'.val i ∧ elem h'.val i ≤ 1000000000)
        (hshift : ∀ i, i < heights.val.length →
          elem h'.val i = elem heights.val i + C), ∀ r r', Aegis.FindBuildings.find_buildings heights = ok r →
          Aegis.FindBuildings.find_buildings h' = ok r' → r.val = r'.val) := by
    sorry

  end AegisSpec.FindBuildings
