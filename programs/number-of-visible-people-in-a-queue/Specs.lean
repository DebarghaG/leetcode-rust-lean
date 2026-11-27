import Aegis.CanSeePersonsCount.Code.Funs

/-!
# Specifications of `Aegis.CanSeePersonsCount.can_see_persons_count`

LeetCode problem `number-of-visible-people-in-a-queue`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.CanSeePersonsCount

  open Classical

  def hgt (heights : Slice Std.I64) (i : Nat) : Int := (heights.val[i]!).val

  def Visible (heights : Slice Std.I64) (i j : Nat) : Prop :=
    i < j ∧ ∀ k, i < k → k < j →
      hgt heights k < hgt heights i ∧ hgt heights k < hgt heights j

  def RecordHigh (heights : Slice Std.I64) (i j : Nat) : Prop :=
    i < j ∧ ∀ k, i < k → k < j → hgt heights k < hgt heights j

  noncomputable def visibleCount (heights : Slice Std.I64) (i : Nat) : Nat :=
    ((Finset.range heights.val.length).filter (fun j => Visible heights i j)).card

  noncomputable def visiblePairCount (heights : Slice Std.I64) : Nat :=
    ((Finset.range heights.val.length).product
        (Finset.range heights.val.length)).filter
      (fun p => Visible heights p.1 p.2) |>.card

  noncomputable def recordHighCount (heights : Slice Std.I64) (i : Nat) : Nat :=
    ((Finset.range heights.val.length).filter (fun j => RecordHigh heights i j)).card

  def IsLeastTaller (heights : Slice Std.I64) (i m : Nat) : Prop :=
    i < m ∧ m ≤ heights.val.length ∧
      (∀ k, i < k → k < m → hgt heights k < hgt heights i) ∧
      (m < heights.val.length → hgt heights i < hgt heights m)

  /-- The function returns a result r (it does not fail). The vector r has length n, and for every i with 0 <= i < n, r[i] = # { j | i < j < n and for every k with i < k < j, heights[k] < heights[i] and heights[k] < heights[j] }. In words, r[i] is the number of people strictly to the right of i whom i can see, where j is visible from i exactly when every person strictly between i and j is shorter than both i and j.
    Preconditions: Let n = len(heights). The slice heights satisfies 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= heights[i] <= 100000; and heights[i] != heights[j] for every 0 <= i < j < n. -/
  theorem spec_1 (heights : Slice Std.I64)
      (hpos : 1 ≤ heights.val.length) (hle : heights.val.length ≤ 100000)
      (hlo : ∀ i, i < heights.val.length → 1 ≤ hgt heights i)
      (hhi : ∀ i, i < heights.val.length → hgt heights i ≤ 100000)
      (hne : ∀ i j, i < j → j < heights.val.length → hgt heights i ≠ hgt heights j) :
      ∃ r, Aegis.CanSeePersonsCount.can_see_persons_count heights = ok r ∧
        r.val.length = heights.val.length ∧
        (∀ i, i < heights.val.length → (r.val[i]!).val = (visibleCount heights i : Int)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (heights : Slice Std.I64)
        (hpos : 1 ≤ heights.val.length) (hle : heights.val.length ≤ 100000)
        (hlo : ∀ i, i < heights.val.length → 1 ≤ hgt heights i)
        (hhi : ∀ i, i < heights.val.length → hgt heights i ≤ 100000)
        (hne : ∀ i j, i < j → j < heights.val.length → hgt heights i ≠ hgt heights j), ∃ r, Aegis.CanSeePersonsCount.can_see_persons_count heights = ok r ∧
          r.val.length = heights.val.length ∧
          (∀ i, i < heights.val.length → (r.val[i]!).val = (visibleCount heights i : Int))) := by
    sorry

  /-- Whenever the function returns a result r, len(r) = len(heights).
    Preconditions: Let n = len(heights). The slice heights satisfies 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= heights[i] <= 100000; and heights[i] != heights[j] for every 0 <= i < j < n. -/
  theorem spec_2 (heights : Slice Std.I64)
      (hpos : 1 ≤ heights.val.length) (hle : heights.val.length ≤ 100000)
      (hlo : ∀ i, i < heights.val.length → 1 ≤ hgt heights i)
      (hhi : ∀ i, i < heights.val.length → hgt heights i ≤ 100000)
      (hne : ∀ i j, i < j → j < heights.val.length → hgt heights i ≠ hgt heights j) :
      ∀ r, Aegis.CanSeePersonsCount.can_see_persons_count heights = ok r →
        r.val.length = heights.val.length := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (heights : Slice Std.I64)
        (hpos : 1 ≤ heights.val.length) (hle : heights.val.length ≤ 100000)
        (hlo : ∀ i, i < heights.val.length → 1 ≤ hgt heights i)
        (hhi : ∀ i, i < heights.val.length → hgt heights i ≤ 100000)
        (hne : ∀ i j, i < j → j < heights.val.length → hgt heights i ≠ hgt heights j), ∀ r, Aegis.CanSeePersonsCount.can_see_persons_count heights = ok r →
          r.val.length = heights.val.length) := by
    sorry

  /-- The function returns a result r (it does not fail, overflow, or panic) for every heights satisfying the preconditions.
    Preconditions: Let n = len(heights). The slice heights satisfies 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= heights[i] <= 100000; and heights[i] != heights[j] for every 0 <= i < j < n. -/
  theorem spec_3 (heights : Slice Std.I64)
      (hpos : 1 ≤ heights.val.length) (hle : heights.val.length ≤ 100000)
      (hlo : ∀ i, i < heights.val.length → 1 ≤ hgt heights i)
      (hhi : ∀ i, i < heights.val.length → hgt heights i ≤ 100000)
      (hne : ∀ i j, i < j → j < heights.val.length → hgt heights i ≠ hgt heights j) :
      ∃ r, Aegis.CanSeePersonsCount.can_see_persons_count heights = ok r := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (heights : Slice Std.I64)
        (hpos : 1 ≤ heights.val.length) (hle : heights.val.length ≤ 100000)
        (hlo : ∀ i, i < heights.val.length → 1 ≤ hgt heights i)
        (hhi : ∀ i, i < heights.val.length → hgt heights i ≤ 100000)
        (hne : ∀ i j, i < j → j < heights.val.length → hgt heights i ≠ hgt heights j), ∃ r, Aegis.CanSeePersonsCount.can_see_persons_count heights = ok r) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < n, r[i] = 0 if and only if i = n-1.
    Preconditions: Let n = len(heights). The slice heights satisfies 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= heights[i] <= 100000; and heights[i] != heights[j] for every 0 <= i < j < n. -/
  theorem spec_4 (heights : Slice Std.I64)
      (hpos : 1 ≤ heights.val.length) (hle : heights.val.length ≤ 100000)
      (hlo : ∀ i, i < heights.val.length → 1 ≤ hgt heights i)
      (hhi : ∀ i, i < heights.val.length → hgt heights i ≤ 100000)
      (hne : ∀ i j, i < j → j < heights.val.length → hgt heights i ≠ hgt heights j) :
      ∀ r, Aegis.CanSeePersonsCount.can_see_persons_count heights = ok r →
        ∀ i, i < heights.val.length →
          ((r.val[i]!).val = 0 ↔ i = heights.val.length - 1) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (heights : Slice Std.I64)
        (hpos : 1 ≤ heights.val.length) (hle : heights.val.length ≤ 100000)
        (hlo : ∀ i, i < heights.val.length → 1 ≤ hgt heights i)
        (hhi : ∀ i, i < heights.val.length → hgt heights i ≤ 100000)
        (hne : ∀ i j, i < j → j < heights.val.length → hgt heights i ≠ hgt heights j), ∀ r, Aegis.CanSeePersonsCount.can_see_persons_count heights = ok r →
          ∀ i, i < heights.val.length →
            ((r.val[i]!).val = 0 ↔ i = heights.val.length - 1)) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < n, r[i] <= n - 1 - i.
    Preconditions: Let n = len(heights). The slice heights satisfies 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= heights[i] <= 100000; and heights[i] != heights[j] for every 0 <= i < j < n. -/
  theorem spec_5 (heights : Slice Std.I64)
      (hpos : 1 ≤ heights.val.length) (hle : heights.val.length ≤ 100000)
      (hlo : ∀ i, i < heights.val.length → 1 ≤ hgt heights i)
      (hhi : ∀ i, i < heights.val.length → hgt heights i ≤ 100000)
      (hne : ∀ i j, i < j → j < heights.val.length → hgt heights i ≠ hgt heights j) :
      ∀ r, Aegis.CanSeePersonsCount.can_see_persons_count heights = ok r →
        ∀ i, i < heights.val.length →
          (r.val[i]!).val ≤ (heights.val.length : Int) - 1 - (i : Int) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (heights : Slice Std.I64)
        (hpos : 1 ≤ heights.val.length) (hle : heights.val.length ≤ 100000)
        (hlo : ∀ i, i < heights.val.length → 1 ≤ hgt heights i)
        (hhi : ∀ i, i < heights.val.length → hgt heights i ≤ 100000)
        (hne : ∀ i j, i < j → j < heights.val.length → hgt heights i ≠ hgt heights j), ∀ r, Aegis.CanSeePersonsCount.can_see_persons_count heights = ok r →
          ∀ i, i < heights.val.length →
            (r.val[i]!).val ≤ (heights.val.length : Int) - 1 - (i : Int)) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < n-1, if heights[i] < heights[i+1], then r[i] = 1.
    Preconditions: Let n = len(heights). The slice heights satisfies 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= heights[i] <= 100000; and heights[i] != heights[j] for every 0 <= i < j < n. -/
  theorem spec_6 (heights : Slice Std.I64)
      (hpos : 1 ≤ heights.val.length) (hle : heights.val.length ≤ 100000)
      (hlo : ∀ i, i < heights.val.length → 1 ≤ hgt heights i)
      (hhi : ∀ i, i < heights.val.length → hgt heights i ≤ 100000)
      (hne : ∀ i j, i < j → j < heights.val.length → hgt heights i ≠ hgt heights j) :
      ∀ r, Aegis.CanSeePersonsCount.can_see_persons_count heights = ok r →
        ∀ i, i < heights.val.length - 1 →
          hgt heights i < hgt heights (i + 1) → (r.val[i]!).val = 1 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (heights : Slice Std.I64)
        (hpos : 1 ≤ heights.val.length) (hle : heights.val.length ≤ 100000)
        (hlo : ∀ i, i < heights.val.length → 1 ≤ hgt heights i)
        (hhi : ∀ i, i < heights.val.length → hgt heights i ≤ 100000)
        (hne : ∀ i j, i < j → j < heights.val.length → hgt heights i ≠ hgt heights j), ∀ r, Aegis.CanSeePersonsCount.can_see_persons_count heights = ok r →
          ∀ i, i < heights.val.length - 1 →
            hgt heights i < hgt heights (i + 1) → (r.val[i]!).val = 1) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < n and every j with i < j < n, if heights[i] < heights[j], then r[i] <= j - i.
    Preconditions: Let n = len(heights). The slice heights satisfies 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= heights[i] <= 100000; and heights[i] != heights[j] for every 0 <= i < j < n. -/
  theorem spec_7 (heights : Slice Std.I64)
      (hpos : 1 ≤ heights.val.length) (hle : heights.val.length ≤ 100000)
      (hlo : ∀ i, i < heights.val.length → 1 ≤ hgt heights i)
      (hhi : ∀ i, i < heights.val.length → hgt heights i ≤ 100000)
      (hne : ∀ i j, i < j → j < heights.val.length → hgt heights i ≠ hgt heights j) :
      ∀ r, Aegis.CanSeePersonsCount.can_see_persons_count heights = ok r →
        ∀ i j, i < heights.val.length → i < j → j < heights.val.length →
          hgt heights i < hgt heights j → (r.val[i]!).val ≤ (j : Int) - (i : Int) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (heights : Slice Std.I64)
        (hpos : 1 ≤ heights.val.length) (hle : heights.val.length ≤ 100000)
        (hlo : ∀ i, i < heights.val.length → 1 ≤ hgt heights i)
        (hhi : ∀ i, i < heights.val.length → hgt heights i ≤ 100000)
        (hne : ∀ i j, i < j → j < heights.val.length → hgt heights i ≠ hgt heights j), ∀ r, Aegis.CanSeePersonsCount.can_see_persons_count heights = ok r →
          ∀ i j, i < heights.val.length → i < j → j < heights.val.length →
            hgt heights i < hgt heights j → (r.val[i]!).val ≤ (j : Int) - (i : Int)) := by
    sorry

  /-- Whenever the function returns a result r, the sum of its entries, sum_{i=0}^{n-1} r[i], equals # { (i,j) | 0 <= i < j < n and for every k with i < k < j, heights[k] < heights[i] and heights[k] < heights[j] }.
    Preconditions: Let n = len(heights). The slice heights satisfies 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= heights[i] <= 100000; and heights[i] != heights[j] for every 0 <= i < j < n. -/
  theorem spec_8 (heights : Slice Std.I64)
      (hpos : 1 ≤ heights.val.length) (hle : heights.val.length ≤ 100000)
      (hlo : ∀ i, i < heights.val.length → 1 ≤ hgt heights i)
      (hhi : ∀ i, i < heights.val.length → hgt heights i ≤ 100000)
      (hne : ∀ i j, i < j → j < heights.val.length → hgt heights i ≠ hgt heights j) :
      ∀ r, Aegis.CanSeePersonsCount.can_see_persons_count heights = ok r →
        (r.val.map (fun x => x.val)).sum = (visiblePairCount heights : Int) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (heights : Slice Std.I64)
        (hpos : 1 ≤ heights.val.length) (hle : heights.val.length ≤ 100000)
        (hlo : ∀ i, i < heights.val.length → 1 ≤ hgt heights i)
        (hhi : ∀ i, i < heights.val.length → hgt heights i ≤ 100000)
        (hne : ∀ i j, i < j → j < heights.val.length → hgt heights i ≠ hgt heights j), ∀ r, Aegis.CanSeePersonsCount.can_see_persons_count heights = ok r →
          (r.val.map (fun x => x.val)).sum = (visiblePairCount heights : Int)) := by
    sorry

  /-- Whenever the function returns r on heights and r' on heights', r'[i] = r[i].
    Preconditions: Let n = len(heights). The slice heights satisfies 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= heights[i] <= 100000; and heights[i] != heights[j] for every 0 <= i < j < n. Let heights' be another slice with len(heights') = n satisfying the same conditions, fix i with 0 <= i < n, and assume heights'[k] = heights[k] for every k with i <= k < n. -/
  theorem spec_9 (heights heights' : Slice Std.I64)
      (hpos : 1 ≤ heights.val.length) (hle : heights.val.length ≤ 100000)
      (hlo : ∀ i, i < heights.val.length → 1 ≤ hgt heights i)
      (hhi : ∀ i, i < heights.val.length → hgt heights i ≤ 100000)
      (hne : ∀ i j, i < j → j < heights.val.length → hgt heights i ≠ hgt heights j)
      (hpos' : 1 ≤ heights'.val.length) (hle' : heights'.val.length ≤ 100000)
      (hlo' : ∀ i, i < heights'.val.length → 1 ≤ hgt heights' i)
      (hhi' : ∀ i, i < heights'.val.length → hgt heights' i ≤ 100000)
      (hne' : ∀ i j, i < j → j < heights'.val.length → hgt heights' i ≠ hgt heights' j)
      (hlen' : heights'.val.length = heights.val.length)
      (i : Nat) (hi : i < heights.val.length)
      (hagree : ∀ k, i ≤ k → k < heights.val.length → hgt heights' k = hgt heights k) :
      ∀ r r', Aegis.CanSeePersonsCount.can_see_persons_count heights = ok r →
        Aegis.CanSeePersonsCount.can_see_persons_count heights' = ok r' →
        (r'.val[i]!).val = (r.val[i]!).val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (heights heights' : Slice Std.I64)
        (hpos : 1 ≤ heights.val.length) (hle : heights.val.length ≤ 100000)
        (hlo : ∀ i, i < heights.val.length → 1 ≤ hgt heights i)
        (hhi : ∀ i, i < heights.val.length → hgt heights i ≤ 100000)
        (hne : ∀ i j, i < j → j < heights.val.length → hgt heights i ≠ hgt heights j)
        (hpos' : 1 ≤ heights'.val.length) (hle' : heights'.val.length ≤ 100000)
        (hlo' : ∀ i, i < heights'.val.length → 1 ≤ hgt heights' i)
        (hhi' : ∀ i, i < heights'.val.length → hgt heights' i ≤ 100000)
        (hne' : ∀ i j, i < j → j < heights'.val.length → hgt heights' i ≠ hgt heights' j)
        (hlen' : heights'.val.length = heights.val.length)
        (i : Nat) (hi : i < heights.val.length)
        (hagree : ∀ k, i ≤ k → k < heights.val.length → hgt heights' k = hgt heights k), ∀ r r', Aegis.CanSeePersonsCount.can_see_persons_count heights = ok r →
          Aegis.CanSeePersonsCount.can_see_persons_count heights' = ok r' →
          (r'.val[i]!).val = (r.val[i]!).val) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < n, if heights[i] > heights[k] for every k with i < k < n, then r[i] = # { j | i < j < n and heights[j] > heights[k] for every k with i < k < j }.
    Preconditions: Let n = len(heights). The slice heights satisfies 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= heights[i] <= 100000; and heights[i] != heights[j] for every 0 <= i < j < n. -/
  theorem spec_10 (heights : Slice Std.I64)
      (hpos : 1 ≤ heights.val.length) (hle : heights.val.length ≤ 100000)
      (hlo : ∀ i, i < heights.val.length → 1 ≤ hgt heights i)
      (hhi : ∀ i, i < heights.val.length → hgt heights i ≤ 100000)
      (hne : ∀ i j, i < j → j < heights.val.length → hgt heights i ≠ hgt heights j) :
      ∀ r, Aegis.CanSeePersonsCount.can_see_persons_count heights = ok r →
        ∀ i, i < heights.val.length →
          (∀ k, i < k → k < heights.val.length → hgt heights k < hgt heights i) →
          (r.val[i]!).val = (recordHighCount heights i : Int) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (heights : Slice Std.I64)
        (hpos : 1 ≤ heights.val.length) (hle : heights.val.length ≤ 100000)
        (hlo : ∀ i, i < heights.val.length → 1 ≤ hgt heights i)
        (hhi : ∀ i, i < heights.val.length → hgt heights i ≤ 100000)
        (hne : ∀ i j, i < j → j < heights.val.length → hgt heights i ≠ hgt heights j), ∀ r, Aegis.CanSeePersonsCount.can_see_persons_count heights = ok r →
          ∀ i, i < heights.val.length →
            (∀ k, i < k → k < heights.val.length → hgt heights k < hgt heights i) →
            (r.val[i]!).val = (recordHighCount heights i : Int)) := by
    sorry

  end AegisSpec.CanSeePersonsCount
