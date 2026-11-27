import Aegis.MinimumCost.Code.Funs

/-!
# Specifications of `Aegis.MinimumCost.minimum_cost`

LeetCode problem `construct-string-with-minimum-cost-easy`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aeneas.Std.alloc.vec
  open Aegis.MinimumCost

  namespace AegisSpec.MinimumCost

  def vecAt (words : Slice (Vec Std.U8)) (i : Nat) : Vec Std.U8 :=
    match words.val[i]? with
    | some w => w
    | none => Vec.new Std.U8

  def i64At (costs : Slice Std.I64) (i : Nat) : Std.I64 :=
    match costs.val[i]? with
    | some c => c
    | none => 0#i64

  def wordAt (words : Slice (Vec Std.U8)) (i : Nat) : List Std.U8 := (vecAt words i).val

  def costAt (costs : Slice Std.I64) (i : Nat) : Int := (i64At costs i).val

  def IsDecomp (target : Slice Std.U8) (words : Slice (Vec Std.U8)) (idxs : List Nat) : Prop :=
    (∀ i ∈ idxs, i < words.val.length) ∧ (idxs.map (wordAt words)).flatten = target.val

  def decompCost (costs : Slice Std.I64) (idxs : List Nat) : Int :=
    (idxs.map (costAt costs)).sum

  def listMin : List Int → Int
    | [] => 0
    | c :: rest => rest.foldl (fun acc x => min acc x) c

  def byteCosts (words : Slice (Vec Std.U8)) (costs : Slice Std.I64) (b : Std.U8) : List Int :=
    ((List.range words.val.length).filter (fun i => decide (wordAt words i = [b]))).map
      (costAt costs)

  def minCostOfByte (words : Slice (Vec Std.U8)) (costs : Slice Std.I64) (b : Std.U8) : Int :=
    listMin (byteCosts words costs b)

  def sumOfMinCosts (target : Slice Std.U8) (words : Slice (Vec Std.U8))
      (costs : Slice Std.I64) : Int :=
    (target.val.map (fun b => minCostOfByte words costs b)).sum

  def IsPrefixOf (w t : List Std.U8) : Prop :=
    w.length ≤ t.length ∧ ∀ k, k < w.length → w[k]? = t[k]?

  def IsSuffixOf (w t : List Std.U8) : Prop :=
    w.length ≤ t.length ∧ ∀ k, k < w.length → w[k]? = t[t.length - w.length + k]?

  def IsExactRepeat (w : List Std.U8) (t : List Std.U8) : Prop :=
    t = (List.replicate (t.length / w.length) w).flatten

  def IsTargetSingleton (target : Slice Std.U8) (words : Slice (Vec Std.U8)) (i : Nat) : Prop :=
    i < words.val.length ∧ (wordAt words i).length = 1 ∧
      (wordAt words i).head? = target.val.head?

  /-- Whenever the function returns a result r, the following holds. If there is no valid decomposition of target (a finite sequence of indices i_0,...,i_{k-1} with k >= 0, 0 <= i_j < len(words) for every j, and words[i_0] ++ ... ++ words[i_{k-1}] = target, where ++ is byte-array concatenation), then r = -1. Otherwise r is the minimum, over all such valid decompositions, of the sum costs[i_0] + ... + costs[i_{k-1}].
    Preconditions: Common input assumptions: len(target) is between 1 and 2000 inclusive; 1 <= len(words) = len(costs) <= 50; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= len(target) and every byte of words[i] is a lowercase English letter code (97 through 122); every byte of target is a lowercase English letter code; for every i with 0 <= i < len(words), 1 <= costs[i] <= 100000. All indices are 0-based. -/
  theorem spec_1 (target : Slice Std.U8) (words : Slice (Vec Std.U8))
      (costs : Slice Std.I64)
      (hT_pos : 1 ≤ target.val.length) (hT_le : target.val.length ≤ 2000)
      (hW_pos : 1 ≤ words.val.length) (hWC : words.val.length = costs.val.length)
      (hW_le : words.val.length ≤ 50)
      (hW_word_pos : ∀ i, i < words.val.length → 1 ≤ (wordAt words i).length)
      (hW_word_le : ∀ i, i < words.val.length → (wordAt words i).length ≤ target.val.length)
      (hW_lower : ∀ i, i < words.val.length → ∀ b, b ∈ wordAt words i →
        97 ≤ b.val ∧ b.val ≤ 122)
      (hT_lower : ∀ b, b ∈ target.val → 97 ≤ b.val ∧ b.val ≤ 122)
      (hC_bounds : ∀ i, i < costs.val.length →
        1 ≤ costAt costs i ∧ costAt costs i ≤ 100000)
      (r : Std.I64) (hr : minimum_cost target words costs = ok r) :
      ((∀ idxs, ¬ IsDecomp target words idxs) → r.val = -1) ∧
        ((∃ idxs, IsDecomp target words idxs) →
          ∃ best, IsDecomp target words best ∧ decompCost costs best = r.val ∧
            ∀ idxs, IsDecomp target words idxs →
              decompCost costs best ≤ decompCost costs idxs) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (target : Slice Std.U8) (words : Slice (Vec Std.U8))
        (costs : Slice Std.I64)
        (hT_pos : 1 ≤ target.val.length) (hT_le : target.val.length ≤ 2000)
        (hW_pos : 1 ≤ words.val.length) (hWC : words.val.length = costs.val.length)
        (hW_le : words.val.length ≤ 50)
        (hW_word_pos : ∀ i, i < words.val.length → 1 ≤ (wordAt words i).length)
        (hW_word_le : ∀ i, i < words.val.length → (wordAt words i).length ≤ target.val.length)
        (hW_lower : ∀ i, i < words.val.length → ∀ b, b ∈ wordAt words i →
          97 ≤ b.val ∧ b.val ≤ 122)
        (hT_lower : ∀ b, b ∈ target.val → 97 ≤ b.val ∧ b.val ≤ 122)
        (hC_bounds : ∀ i, i < costs.val.length →
          1 ≤ costAt costs i ∧ costAt costs i ≤ 100000)
        (r : Std.I64) (hr : minimum_cost target words costs = ok r), ((∀ idxs, ¬ IsDecomp target words idxs) → r.val = -1) ∧
          ((∃ idxs, IsDecomp target words idxs) →
            ∃ best, IsDecomp target words best ∧ decompCost costs best = r.val ∧
              ∀ idxs, IsDecomp target words idxs →
                decompCost costs best ≤ decompCost costs idxs)) := by
    sorry

  /-- Whenever the function returns a result r, either r = -1, or 1 <= r <= len(target) * 100000. Since len(target) <= 2000, in the second case r <= 200000000.
    Preconditions: Common input assumptions: len(target) is between 1 and 2000 inclusive; 1 <= len(words) = len(costs) <= 50; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= len(target) and every byte of words[i] is a lowercase English letter code (97 through 122); every byte of target is a lowercase English letter code; for every i with 0 <= i < len(words), 1 <= costs[i] <= 100000. All indices are 0-based. -/
  theorem spec_2 (target : Slice Std.U8) (words : Slice (Vec Std.U8))
      (costs : Slice Std.I64)
      (hT_pos : 1 ≤ target.val.length) (hT_le : target.val.length ≤ 2000)
      (hW_pos : 1 ≤ words.val.length) (hWC : words.val.length = costs.val.length)
      (hW_le : words.val.length ≤ 50)
      (hW_word_pos : ∀ i, i < words.val.length → 1 ≤ (wordAt words i).length)
      (hW_word_le : ∀ i, i < words.val.length → (wordAt words i).length ≤ target.val.length)
      (hW_lower : ∀ i, i < words.val.length → ∀ b, b ∈ wordAt words i →
        97 ≤ b.val ∧ b.val ≤ 122)
      (hT_lower : ∀ b, b ∈ target.val → 97 ≤ b.val ∧ b.val ≤ 122)
      (hC_bounds : ∀ i, i < costs.val.length →
        1 ≤ costAt costs i ∧ costAt costs i ≤ 100000)
      (r : Std.I64) (hr : minimum_cost target words costs = ok r) :
      r.val = -1 ∨ (1 ≤ r.val ∧ r.val ≤ (target.val.length : Int) * 100000) := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (target : Slice Std.U8) (words : Slice (Vec Std.U8))
        (costs : Slice Std.I64)
        (hT_pos : 1 ≤ target.val.length) (hT_le : target.val.length ≤ 2000)
        (hW_pos : 1 ≤ words.val.length) (hWC : words.val.length = costs.val.length)
        (hW_le : words.val.length ≤ 50)
        (hW_word_pos : ∀ i, i < words.val.length → 1 ≤ (wordAt words i).length)
        (hW_word_le : ∀ i, i < words.val.length → (wordAt words i).length ≤ target.val.length)
        (hW_lower : ∀ i, i < words.val.length → ∀ b, b ∈ wordAt words i →
          97 ≤ b.val ∧ b.val ≤ 122)
        (hT_lower : ∀ b, b ∈ target.val → 97 ≤ b.val ∧ b.val ≤ 122)
        (hC_bounds : ∀ i, i < costs.val.length →
          1 ≤ costAt costs i ∧ costAt costs i ≤ 100000)
        (r : Std.I64) (hr : minimum_cost target words costs = ok r), r.val = -1 ∨ (1 ≤ r.val ∧ r.val ≤ (target.val.length : Int) * 100000)) := by
    sorry

  /-- Whenever the function returns a result r with r >= 0, there exists a valid decomposition of target (a finite sequence of indices i_0,...,i_{k-1} with 0 <= i_j < len(words) for every j and words[i_0] ++ ... ++ words[i_{k-1}] = target) such that sum costs[i_j] = r and 1 <= k <= len(target).
    Preconditions: Common input assumptions: len(target) is between 1 and 2000 inclusive; 1 <= len(words) = len(costs) <= 50; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= len(target) and every byte of words[i] is a lowercase English letter code (97 through 122); every byte of target is a lowercase English letter code; for every i with 0 <= i < len(words), 1 <= costs[i] <= 100000. All indices are 0-based. -/
  theorem spec_3 (target : Slice Std.U8) (words : Slice (Vec Std.U8))
      (costs : Slice Std.I64)
      (hT_pos : 1 ≤ target.val.length) (hT_le : target.val.length ≤ 2000)
      (hW_pos : 1 ≤ words.val.length) (hWC : words.val.length = costs.val.length)
      (hW_le : words.val.length ≤ 50)
      (hW_word_pos : ∀ i, i < words.val.length → 1 ≤ (wordAt words i).length)
      (hW_word_le : ∀ i, i < words.val.length → (wordAt words i).length ≤ target.val.length)
      (hW_lower : ∀ i, i < words.val.length → ∀ b, b ∈ wordAt words i →
        97 ≤ b.val ∧ b.val ≤ 122)
      (hT_lower : ∀ b, b ∈ target.val → 97 ≤ b.val ∧ b.val ≤ 122)
      (hC_bounds : ∀ i, i < costs.val.length →
        1 ≤ costAt costs i ∧ costAt costs i ≤ 100000)
      (r : Std.I64) (hr : minimum_cost target words costs = ok r) (hr_nonneg : 0 ≤ r.val) :
      ∃ idxs, IsDecomp target words idxs ∧ decompCost costs idxs = r.val ∧
        1 ≤ idxs.length ∧ idxs.length ≤ target.val.length := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (target : Slice Std.U8) (words : Slice (Vec Std.U8))
        (costs : Slice Std.I64)
        (hT_pos : 1 ≤ target.val.length) (hT_le : target.val.length ≤ 2000)
        (hW_pos : 1 ≤ words.val.length) (hWC : words.val.length = costs.val.length)
        (hW_le : words.val.length ≤ 50)
        (hW_word_pos : ∀ i, i < words.val.length → 1 ≤ (wordAt words i).length)
        (hW_word_le : ∀ i, i < words.val.length → (wordAt words i).length ≤ target.val.length)
        (hW_lower : ∀ i, i < words.val.length → ∀ b, b ∈ wordAt words i →
          97 ≤ b.val ∧ b.val ≤ 122)
        (hT_lower : ∀ b, b ∈ target.val → 97 ≤ b.val ∧ b.val ≤ 122)
        (hC_bounds : ∀ i, i < costs.val.length →
          1 ≤ costAt costs i ∧ costAt costs i ≤ 100000)
        (r : Std.I64) (hr : minimum_cost target words costs = ok r) (hr_nonneg : 0 ≤ r.val), ∃ idxs, IsDecomp target words idxs ∧ decompCost costs idxs = r.val ∧
          1 ≤ idxs.length ∧ idxs.length ≤ target.val.length) := by
    sorry

  /-- Whenever the function returns a result r with r >= 0, for every valid decomposition of target (a finite sequence of indices i_0,...,i_{k-1} with 0 <= i_j < len(words) for every j and words[i_0] ++ ... ++ words[i_{k-1}] = target), the inequality r <= costs[i_0] + ... + costs[i_{k-1}] holds.
    Preconditions: Common input assumptions: len(target) is between 1 and 2000 inclusive; 1 <= len(words) = len(costs) <= 50; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= len(target) and every byte of words[i] is a lowercase English letter code (97 through 122); every byte of target is a lowercase English letter code; for every i with 0 <= i < len(words), 1 <= costs[i] <= 100000. All indices are 0-based. -/
  theorem spec_4 (target : Slice Std.U8) (words : Slice (Vec Std.U8))
      (costs : Slice Std.I64)
      (hT_pos : 1 ≤ target.val.length) (hT_le : target.val.length ≤ 2000)
      (hW_pos : 1 ≤ words.val.length) (hWC : words.val.length = costs.val.length)
      (hW_le : words.val.length ≤ 50)
      (hW_word_pos : ∀ i, i < words.val.length → 1 ≤ (wordAt words i).length)
      (hW_word_le : ∀ i, i < words.val.length → (wordAt words i).length ≤ target.val.length)
      (hW_lower : ∀ i, i < words.val.length → ∀ b, b ∈ wordAt words i →
        97 ≤ b.val ∧ b.val ≤ 122)
      (hT_lower : ∀ b, b ∈ target.val → 97 ≤ b.val ∧ b.val ≤ 122)
      (hC_bounds : ∀ i, i < costs.val.length →
        1 ≤ costAt costs i ∧ costAt costs i ≤ 100000)
      (r : Std.I64) (hr : minimum_cost target words costs = ok r) (hr_nonneg : 0 ≤ r.val) :
      ∀ idxs, IsDecomp target words idxs → r.val ≤ decompCost costs idxs := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (target : Slice Std.U8) (words : Slice (Vec Std.U8))
        (costs : Slice Std.I64)
        (hT_pos : 1 ≤ target.val.length) (hT_le : target.val.length ≤ 2000)
        (hW_pos : 1 ≤ words.val.length) (hWC : words.val.length = costs.val.length)
        (hW_le : words.val.length ≤ 50)
        (hW_word_pos : ∀ i, i < words.val.length → 1 ≤ (wordAt words i).length)
        (hW_word_le : ∀ i, i < words.val.length → (wordAt words i).length ≤ target.val.length)
        (hW_lower : ∀ i, i < words.val.length → ∀ b, b ∈ wordAt words i →
          97 ≤ b.val ∧ b.val ≤ 122)
        (hT_lower : ∀ b, b ∈ target.val → 97 ≤ b.val ∧ b.val ≤ 122)
        (hC_bounds : ∀ i, i < costs.val.length →
          1 ≤ costAt costs i ∧ costAt costs i ≤ 100000)
        (r : Std.I64) (hr : minimum_cost target words costs = ok r) (hr_nonneg : 0 ≤ r.val), ∀ idxs, IsDecomp target words idxs → r.val ≤ decompCost costs idxs) := by
    sorry

  /-- Let w = words[0] and c = costs[0]. Whenever the function returns a result r, if len(w) divides len(target) and target is exactly the concatenation of len(target)/len(w) copies of w, then r = (len(target)/len(w)) * c; otherwise r = -1.
    Preconditions: Common input assumptions: len(target) is between 1 and 2000 inclusive; 1 <= len(words) = len(costs) <= 50; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= len(target) and every byte of words[i] is a lowercase English letter code (97 through 122); every byte of target is a lowercase English letter code; for every i with 0 <= i < len(words), 1 <= costs[i] <= 100000. All indices are 0-based. In addition, len(words) = 1. -/
  theorem spec_5 (target : Slice Std.U8) (words : Slice (Vec Std.U8))
      (costs : Slice Std.I64)
      (hT_pos : 1 ≤ target.val.length) (hT_le : target.val.length ≤ 2000)
      (hW_pos : 1 ≤ words.val.length) (hWC : words.val.length = costs.val.length)
      (hW_le : words.val.length ≤ 50)
      (hW_word_pos : ∀ i, i < words.val.length → 1 ≤ (wordAt words i).length)
      (hW_word_le : ∀ i, i < words.val.length → (wordAt words i).length ≤ target.val.length)
      (hW_lower : ∀ i, i < words.val.length → ∀ b, b ∈ wordAt words i →
        97 ≤ b.val ∧ b.val ≤ 122)
      (hT_lower : ∀ b, b ∈ target.val → 97 ≤ b.val ∧ b.val ≤ 122)
      (hC_bounds : ∀ i, i < costs.val.length →
        1 ≤ costAt costs i ∧ costAt costs i ≤ 100000)
      (hW_one : words.val.length = 1)
      (r : Std.I64) (hr : minimum_cost target words costs = ok r) :
      (((wordAt words 0).length ∣ target.val.length ∧
            IsExactRepeat (wordAt words 0) target.val) →
          r.val =
            ((target.val.length / (wordAt words 0).length : Nat) : Int) *
              costAt costs 0) ∧
        (¬ ((wordAt words 0).length ∣ target.val.length ∧
              IsExactRepeat (wordAt words 0) target.val) → r.val = -1) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (target : Slice Std.U8) (words : Slice (Vec Std.U8))
        (costs : Slice Std.I64)
        (hT_pos : 1 ≤ target.val.length) (hT_le : target.val.length ≤ 2000)
        (hW_pos : 1 ≤ words.val.length) (hWC : words.val.length = costs.val.length)
        (hW_le : words.val.length ≤ 50)
        (hW_word_pos : ∀ i, i < words.val.length → 1 ≤ (wordAt words i).length)
        (hW_word_le : ∀ i, i < words.val.length → (wordAt words i).length ≤ target.val.length)
        (hW_lower : ∀ i, i < words.val.length → ∀ b, b ∈ wordAt words i →
          97 ≤ b.val ∧ b.val ≤ 122)
        (hT_lower : ∀ b, b ∈ target.val → 97 ≤ b.val ∧ b.val ≤ 122)
        (hC_bounds : ∀ i, i < costs.val.length →
          1 ≤ costAt costs i ∧ costAt costs i ≤ 100000)
        (hW_one : words.val.length = 1)
        (r : Std.I64) (hr : minimum_cost target words costs = ok r), (((wordAt words 0).length ∣ target.val.length ∧
              IsExactRepeat (wordAt words 0) target.val) →
            r.val =
              ((target.val.length / (wordAt words 0).length : Nat) : Int) *
                costAt costs 0) ∧
          (¬ ((wordAt words 0).length ∣ target.val.length ∧
                IsExactRepeat (wordAt words 0) target.val) → r.val = -1)) := by
    sorry

  /-- Whenever the function returns a result r, if no index i with 0 <= i < len(words) satisfies len(words[i]) = 1 and words[i][0] = target[0], then r = -1; otherwise r = min { costs[i] | 0 <= i < len(words), len(words[i]) = 1, and words[i][0] = target[0] }.
    Preconditions: Common input assumptions: len(target) is between 1 and 2000 inclusive; 1 <= len(words) = len(costs) <= 50; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= len(target) and every byte of words[i] is a lowercase English letter code (97 through 122); every byte of target is a lowercase English letter code; for every i with 0 <= i < len(words), 1 <= costs[i] <= 100000. All indices are 0-based. In addition, len(target) = 1. -/
  theorem spec_6 (target : Slice Std.U8) (words : Slice (Vec Std.U8))
      (costs : Slice Std.I64)
      (hT_pos : 1 ≤ target.val.length) (hT_le : target.val.length ≤ 2000)
      (hW_pos : 1 ≤ words.val.length) (hWC : words.val.length = costs.val.length)
      (hW_le : words.val.length ≤ 50)
      (hW_word_pos : ∀ i, i < words.val.length → 1 ≤ (wordAt words i).length)
      (hW_word_le : ∀ i, i < words.val.length → (wordAt words i).length ≤ target.val.length)
      (hW_lower : ∀ i, i < words.val.length → ∀ b, b ∈ wordAt words i →
        97 ≤ b.val ∧ b.val ≤ 122)
      (hT_lower : ∀ b, b ∈ target.val → 97 ≤ b.val ∧ b.val ≤ 122)
      (hC_bounds : ∀ i, i < costs.val.length →
        1 ≤ costAt costs i ∧ costAt costs i ≤ 100000)
      (hT_one : target.val.length = 1)
      (r : Std.I64) (hr : minimum_cost target words costs = ok r) :
      ((∀ i, ¬ IsTargetSingleton target words i) → r.val = -1) ∧
        ((∃ i, IsTargetSingleton target words i) →
          (∃ i, IsTargetSingleton target words i ∧ r.val = costAt costs i) ∧
            (∀ i, IsTargetSingleton target words i → r.val ≤ costAt costs i)) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (target : Slice Std.U8) (words : Slice (Vec Std.U8))
        (costs : Slice Std.I64)
        (hT_pos : 1 ≤ target.val.length) (hT_le : target.val.length ≤ 2000)
        (hW_pos : 1 ≤ words.val.length) (hWC : words.val.length = costs.val.length)
        (hW_le : words.val.length ≤ 50)
        (hW_word_pos : ∀ i, i < words.val.length → 1 ≤ (wordAt words i).length)
        (hW_word_le : ∀ i, i < words.val.length → (wordAt words i).length ≤ target.val.length)
        (hW_lower : ∀ i, i < words.val.length → ∀ b, b ∈ wordAt words i →
          97 ≤ b.val ∧ b.val ≤ 122)
        (hT_lower : ∀ b, b ∈ target.val → 97 ≤ b.val ∧ b.val ≤ 122)
        (hC_bounds : ∀ i, i < costs.val.length →
          1 ≤ costAt costs i ∧ costAt costs i ≤ 100000)
        (hT_one : target.val.length = 1)
        (r : Std.I64) (hr : minimum_cost target words costs = ok r), ((∀ i, ¬ IsTargetSingleton target words i) → r.val = -1) ∧
          ((∃ i, IsTargetSingleton target words i) →
            (∃ i, IsTargetSingleton target words i ∧ r.val = costAt costs i) ∧
              (∀ i, IsTargetSingleton target words i → r.val ≤ costAt costs i))) := by
    sorry

  /-- Whenever the function returns a result r, if for every position j with 0 <= j < len(target) there exists an index i with words[i] = [target[j]], then r = sum_{j=0}^{len(target)-1} min { costs[i] | 0 <= i < len(words) and words[i] = [target[j]] }; otherwise r = -1. Here [target[j]] is the one-byte array containing target[j].
    Preconditions: Common input assumptions: len(target) is between 1 and 2000 inclusive; 1 <= len(words) = len(costs) <= 50; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= len(target) and every byte of words[i] is a lowercase English letter code (97 through 122); every byte of target is a lowercase English letter code; for every i with 0 <= i < len(words), 1 <= costs[i] <= 100000. All indices are 0-based. In addition, for every i with 0 <= i < len(words), len(words[i]) = 1. -/
  theorem spec_7 (target : Slice Std.U8) (words : Slice (Vec Std.U8))
      (costs : Slice Std.I64)
      (hT_pos : 1 ≤ target.val.length) (hT_le : target.val.length ≤ 2000)
      (hW_pos : 1 ≤ words.val.length) (hWC : words.val.length = costs.val.length)
      (hW_le : words.val.length ≤ 50)
      (hW_word_pos : ∀ i, i < words.val.length → 1 ≤ (wordAt words i).length)
      (hW_word_le : ∀ i, i < words.val.length → (wordAt words i).length ≤ target.val.length)
      (hW_lower : ∀ i, i < words.val.length → ∀ b, b ∈ wordAt words i →
        97 ≤ b.val ∧ b.val ≤ 122)
      (hT_lower : ∀ b, b ∈ target.val → 97 ≤ b.val ∧ b.val ≤ 122)
      (hC_bounds : ∀ i, i < costs.val.length →
        1 ≤ costAt costs i ∧ costAt costs i ≤ 100000)
      (hW_len_one : ∀ i, i < words.val.length → (wordAt words i).length = 1)
      (r : Std.I64) (hr : minimum_cost target words costs = ok r) :
      ((∀ j, j < target.val.length →
            ∃ i, i < words.val.length ∧ wordAt words i = [target.val.getD j 0#u8]) →
          r.val = sumOfMinCosts target words costs) ∧
        (¬ (∀ j, j < target.val.length →
              ∃ i, i < words.val.length ∧ wordAt words i = [target.val.getD j 0#u8]) →
          r.val = -1) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (target : Slice Std.U8) (words : Slice (Vec Std.U8))
        (costs : Slice Std.I64)
        (hT_pos : 1 ≤ target.val.length) (hT_le : target.val.length ≤ 2000)
        (hW_pos : 1 ≤ words.val.length) (hWC : words.val.length = costs.val.length)
        (hW_le : words.val.length ≤ 50)
        (hW_word_pos : ∀ i, i < words.val.length → 1 ≤ (wordAt words i).length)
        (hW_word_le : ∀ i, i < words.val.length → (wordAt words i).length ≤ target.val.length)
        (hW_lower : ∀ i, i < words.val.length → ∀ b, b ∈ wordAt words i →
          97 ≤ b.val ∧ b.val ≤ 122)
        (hT_lower : ∀ b, b ∈ target.val → 97 ≤ b.val ∧ b.val ≤ 122)
        (hC_bounds : ∀ i, i < costs.val.length →
          1 ≤ costAt costs i ∧ costAt costs i ≤ 100000)
        (hW_len_one : ∀ i, i < words.val.length → (wordAt words i).length = 1)
        (r : Std.I64) (hr : minimum_cost target words costs = ok r), ((∀ j, j < target.val.length →
              ∃ i, i < words.val.length ∧ wordAt words i = [target.val.getD j 0#u8]) →
            r.val = sumOfMinCosts target words costs) ∧
          (¬ (∀ j, j < target.val.length →
                ∃ i, i < words.val.length ∧ wordAt words i = [target.val.getD j 0#u8]) →
            r.val = -1)) := by
    sorry

  /-- Let r be the result of the function on (target, words, costs) and r' the result on (target, words', costs'). Whenever both results are returned, r' = r.
    Preconditions: Common input assumptions: len(target) is between 1 and 2000 inclusive; 1 <= len(words) = len(costs) <= 50; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= len(target) and every byte of words[i] is a lowercase English letter code (97 through 122); every byte of target is a lowercase English letter code; for every i with 0 <= i < len(words), 1 <= costs[i] <= 100000. All indices are 0-based. In addition, fix indices i and j with 0 <= i < len(words), 0 <= j < len(words), i != j, words[i] = words[j], and costs[j] <= costs[i]. Let words' and costs' be the arrays obtained by deleting position i from words and costs respectively. -/
  theorem spec_8 (target : Slice Std.U8) (words : Slice (Vec Std.U8))
      (costs : Slice Std.I64)
      (hT_pos : 1 ≤ target.val.length) (hT_le : target.val.length ≤ 2000)
      (hW_pos : 1 ≤ words.val.length) (hWC : words.val.length = costs.val.length)
      (hW_le : words.val.length ≤ 50)
      (hW_word_pos : ∀ i, i < words.val.length → 1 ≤ (wordAt words i).length)
      (hW_word_le : ∀ i, i < words.val.length → (wordAt words i).length ≤ target.val.length)
      (hW_lower : ∀ i, i < words.val.length → ∀ b, b ∈ wordAt words i →
        97 ≤ b.val ∧ b.val ≤ 122)
      (hT_lower : ∀ b, b ∈ target.val → 97 ≤ b.val ∧ b.val ≤ 122)
      (hC_bounds : ∀ i, i < costs.val.length →
        1 ≤ costAt costs i ∧ costAt costs i ≤ 100000)
      (i j : Nat) (hi : i < words.val.length) (hj : j < words.val.length) (hij : i ≠ j)
      (hsame : wordAt words i = wordAt words j) (hjle : costAt costs j ≤ costAt costs i)
      (words' : Slice (Vec Std.U8)) (costs' : Slice Std.I64)
      (hwords' : words'.val = words.val.eraseIdx i)
      (hcosts' : costs'.val = costs.val.eraseIdx i)
      (r r' : Std.I64) (hr : minimum_cost target words costs = ok r)
      (hr' : minimum_cost target words' costs' = ok r') :
      r' = r := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (target : Slice Std.U8) (words : Slice (Vec Std.U8))
        (costs : Slice Std.I64)
        (hT_pos : 1 ≤ target.val.length) (hT_le : target.val.length ≤ 2000)
        (hW_pos : 1 ≤ words.val.length) (hWC : words.val.length = costs.val.length)
        (hW_le : words.val.length ≤ 50)
        (hW_word_pos : ∀ i, i < words.val.length → 1 ≤ (wordAt words i).length)
        (hW_word_le : ∀ i, i < words.val.length → (wordAt words i).length ≤ target.val.length)
        (hW_lower : ∀ i, i < words.val.length → ∀ b, b ∈ wordAt words i →
          97 ≤ b.val ∧ b.val ≤ 122)
        (hT_lower : ∀ b, b ∈ target.val → 97 ≤ b.val ∧ b.val ≤ 122)
        (hC_bounds : ∀ i, i < costs.val.length →
          1 ≤ costAt costs i ∧ costAt costs i ≤ 100000)
        (i j : Nat) (hi : i < words.val.length) (hj : j < words.val.length) (hij : i ≠ j)
        (hsame : wordAt words i = wordAt words j) (hjle : costAt costs j ≤ costAt costs i)
        (words' : Slice (Vec Std.U8)) (costs' : Slice Std.I64)
        (hwords' : words'.val = words.val.eraseIdx i)
        (hcosts' : costs'.val = costs.val.eraseIdx i)
        (r r' : Std.I64) (hr : minimum_cost target words costs = ok r)
        (hr' : minimum_cost target words' costs' = ok r'), r' = r) := by
    sorry

  /-- Whenever both results are returned, the result of the function on (target, words_p, costs_p) equals the result of the function on (target, words, costs).
    Preconditions: Common input assumptions: len(target) is between 1 and 2000 inclusive; 1 <= len(words) = len(costs) <= 50; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= len(target) and every byte of words[i] is a lowercase English letter code (97 through 122); every byte of target is a lowercase English letter code; for every i with 0 <= i < len(words), 1 <= costs[i] <= 100000. All indices are 0-based. In addition, let p be any permutation of {0,...,len(words)-1}; define words_p[k] = words[p(k)] and costs_p[k] = costs[p(k)] for 0 <= k < len(words). -/
  theorem spec_9 (target : Slice Std.U8) (words : Slice (Vec Std.U8))
      (costs : Slice Std.I64)
      (hT_pos : 1 ≤ target.val.length) (hT_le : target.val.length ≤ 2000)
      (hW_pos : 1 ≤ words.val.length) (hWC : words.val.length = costs.val.length)
      (hW_le : words.val.length ≤ 50)
      (hW_word_pos : ∀ i, i < words.val.length → 1 ≤ (wordAt words i).length)
      (hW_word_le : ∀ i, i < words.val.length → (wordAt words i).length ≤ target.val.length)
      (hW_lower : ∀ i, i < words.val.length → ∀ b, b ∈ wordAt words i →
        97 ≤ b.val ∧ b.val ≤ 122)
      (hT_lower : ∀ b, b ∈ target.val → 97 ≤ b.val ∧ b.val ≤ 122)
      (hC_bounds : ∀ i, i < costs.val.length →
        1 ≤ costAt costs i ∧ costAt costs i ≤ 100000)
      (p : Nat → Nat)
      (hp_bound : ∀ k, k < words.val.length → p k < words.val.length)
      (hp_surj : ∀ k, k < words.val.length → ∃ k', k' < words.val.length ∧ p k' = k)
      (words_p : Slice (Vec Std.U8)) (costs_p : Slice Std.I64)
      (hwords_p : words_p.val = (List.range words.val.length).map (fun k => vecAt words (p k)))
      (hcosts_p : costs_p.val = (List.range costs.val.length).map (fun k => i64At costs (p k)))
      (r rp : Std.I64) (hr : minimum_cost target words costs = ok r)
      (hrp : minimum_cost target words_p costs_p = ok rp) :
      rp = r := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (target : Slice Std.U8) (words : Slice (Vec Std.U8))
        (costs : Slice Std.I64)
        (hT_pos : 1 ≤ target.val.length) (hT_le : target.val.length ≤ 2000)
        (hW_pos : 1 ≤ words.val.length) (hWC : words.val.length = costs.val.length)
        (hW_le : words.val.length ≤ 50)
        (hW_word_pos : ∀ i, i < words.val.length → 1 ≤ (wordAt words i).length)
        (hW_word_le : ∀ i, i < words.val.length → (wordAt words i).length ≤ target.val.length)
        (hW_lower : ∀ i, i < words.val.length → ∀ b, b ∈ wordAt words i →
          97 ≤ b.val ∧ b.val ≤ 122)
        (hT_lower : ∀ b, b ∈ target.val → 97 ≤ b.val ∧ b.val ≤ 122)
        (hC_bounds : ∀ i, i < costs.val.length →
          1 ≤ costAt costs i ∧ costAt costs i ≤ 100000)
        (p : Nat → Nat)
        (hp_bound : ∀ k, k < words.val.length → p k < words.val.length)
        (hp_surj : ∀ k, k < words.val.length → ∃ k', k' < words.val.length ∧ p k' = k)
        (words_p : Slice (Vec Std.U8)) (costs_p : Slice Std.I64)
        (hwords_p : words_p.val = (List.range words.val.length).map (fun k => vecAt words (p k)))
        (hcosts_p : costs_p.val = (List.range costs.val.length).map (fun k => i64At costs (p k)))
        (r rp : Std.I64) (hr : minimum_cost target words costs = ok r)
        (hrp : minimum_cost target words_p costs_p = ok rp), rp = r) := by
    sorry

  /-- Let r be the result on (target, words, costs) and r' the result on (target, words, costs'). Whenever both results are returned: r' = -1 if and only if r = -1, and if r >= 0 then r' >= r.
    Preconditions: Common input assumptions: len(target) is between 1 and 2000 inclusive; 1 <= len(words) = len(costs) <= 50; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= len(target) and every byte of words[i] is a lowercase English letter code (97 through 122); every byte of target is a lowercase English letter code; for every i with 0 <= i < len(words), 1 <= costs[i] <= 100000. All indices are 0-based. In addition, let costs' be an array with len(costs') = len(words) and costs[i] <= costs'[i] <= 100000 for every i with 0 <= i < len(words). -/
  theorem spec_10 (target : Slice Std.U8) (words : Slice (Vec Std.U8))
      (costs : Slice Std.I64)
      (hT_pos : 1 ≤ target.val.length) (hT_le : target.val.length ≤ 2000)
      (hW_pos : 1 ≤ words.val.length) (hWC : words.val.length = costs.val.length)
      (hW_le : words.val.length ≤ 50)
      (hW_word_pos : ∀ i, i < words.val.length → 1 ≤ (wordAt words i).length)
      (hW_word_le : ∀ i, i < words.val.length → (wordAt words i).length ≤ target.val.length)
      (hW_lower : ∀ i, i < words.val.length → ∀ b, b ∈ wordAt words i →
        97 ≤ b.val ∧ b.val ≤ 122)
      (hT_lower : ∀ b, b ∈ target.val → 97 ≤ b.val ∧ b.val ≤ 122)
      (hC_bounds : ∀ i, i < costs.val.length →
        1 ≤ costAt costs i ∧ costAt costs i ≤ 100000)
      (costs' : Slice Std.I64) (hcosts'_len : costs'.val.length = words.val.length)
      (hcosts'_ge : ∀ i, i < words.val.length → costAt costs i ≤ costAt costs' i)
      (hcosts'_le : ∀ i, i < costs'.val.length → costAt costs' i ≤ 100000)
      (r r' : Std.I64) (hr : minimum_cost target words costs = ok r)
      (hr' : minimum_cost target words costs' = ok r') :
      (r'.val = -1 ↔ r.val = -1) ∧ (0 ≤ r.val → r.val ≤ r'.val) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (target : Slice Std.U8) (words : Slice (Vec Std.U8))
        (costs : Slice Std.I64)
        (hT_pos : 1 ≤ target.val.length) (hT_le : target.val.length ≤ 2000)
        (hW_pos : 1 ≤ words.val.length) (hWC : words.val.length = costs.val.length)
        (hW_le : words.val.length ≤ 50)
        (hW_word_pos : ∀ i, i < words.val.length → 1 ≤ (wordAt words i).length)
        (hW_word_le : ∀ i, i < words.val.length → (wordAt words i).length ≤ target.val.length)
        (hW_lower : ∀ i, i < words.val.length → ∀ b, b ∈ wordAt words i →
          97 ≤ b.val ∧ b.val ≤ 122)
        (hT_lower : ∀ b, b ∈ target.val → 97 ≤ b.val ∧ b.val ≤ 122)
        (hC_bounds : ∀ i, i < costs.val.length →
          1 ≤ costAt costs i ∧ costAt costs i ≤ 100000)
        (costs' : Slice Std.I64) (hcosts'_len : costs'.val.length = words.val.length)
        (hcosts'_ge : ∀ i, i < words.val.length → costAt costs i ≤ costAt costs' i)
        (hcosts'_le : ∀ i, i < costs'.val.length → costAt costs' i ≤ 100000)
        (r r' : Std.I64) (hr : minimum_cost target words costs = ok r)
        (hr' : minimum_cost target words costs' = ok r'), (r'.val = -1 ↔ r.val = -1) ∧ (0 ≤ r.val → r.val ≤ r'.val)) := by
    sorry

  /-- Whenever the function returns a result r, if no valid decomposition of target exists (a finite sequence of indices i_0,...,i_{k-1} with 0 <= i_j < len(words) and words[i_0] ++ ... ++ words[i_{k-1}] = target), then r = -1; otherwise r = c * k, where k is the minimum length among all such valid decompositions.
    Preconditions: Common input assumptions: len(target) is between 1 and 2000 inclusive; 1 <= len(words) = len(costs) <= 50; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= len(target) and every byte of words[i] is a lowercase English letter code (97 through 122); every byte of target is a lowercase English letter code; for every i with 0 <= i < len(words), 1 <= costs[i] <= 100000. All indices are 0-based. In addition, there is an integer c with 1 <= c <= 100000 such that costs[i] = c for every i with 0 <= i < len(words). -/
  theorem spec_11 (target : Slice Std.U8) (words : Slice (Vec Std.U8))
      (costs : Slice Std.I64)
      (hT_pos : 1 ≤ target.val.length) (hT_le : target.val.length ≤ 2000)
      (hW_pos : 1 ≤ words.val.length) (hWC : words.val.length = costs.val.length)
      (hW_le : words.val.length ≤ 50)
      (hW_word_pos : ∀ i, i < words.val.length → 1 ≤ (wordAt words i).length)
      (hW_word_le : ∀ i, i < words.val.length → (wordAt words i).length ≤ target.val.length)
      (hW_lower : ∀ i, i < words.val.length → ∀ b, b ∈ wordAt words i →
        97 ≤ b.val ∧ b.val ≤ 122)
      (hT_lower : ∀ b, b ∈ target.val → 97 ≤ b.val ∧ b.val ≤ 122)
      (hC_bounds : ∀ i, i < costs.val.length →
        1 ≤ costAt costs i ∧ costAt costs i ≤ 100000)
      (c : Int) (hc_pos : 1 ≤ c) (hc_le : c ≤ 100000)
      (hc_uniform : ∀ i, i < costs.val.length → costAt costs i = c)
      (r : Std.I64) (hr : minimum_cost target words costs = ok r) :
      ((∀ idxs, ¬ IsDecomp target words idxs) → r.val = -1) ∧
        ((∃ idxs, IsDecomp target words idxs) →
          ∃ best, IsDecomp target words best ∧
            (∀ idxs, IsDecomp target words idxs → best.length ≤ idxs.length) ∧
              r.val = c * (best.length : Int)) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (target : Slice Std.U8) (words : Slice (Vec Std.U8))
        (costs : Slice Std.I64)
        (hT_pos : 1 ≤ target.val.length) (hT_le : target.val.length ≤ 2000)
        (hW_pos : 1 ≤ words.val.length) (hWC : words.val.length = costs.val.length)
        (hW_le : words.val.length ≤ 50)
        (hW_word_pos : ∀ i, i < words.val.length → 1 ≤ (wordAt words i).length)
        (hW_word_le : ∀ i, i < words.val.length → (wordAt words i).length ≤ target.val.length)
        (hW_lower : ∀ i, i < words.val.length → ∀ b, b ∈ wordAt words i →
          97 ≤ b.val ∧ b.val ≤ 122)
        (hT_lower : ∀ b, b ∈ target.val → 97 ≤ b.val ∧ b.val ≤ 122)
        (hC_bounds : ∀ i, i < costs.val.length →
          1 ≤ costAt costs i ∧ costAt costs i ≤ 100000)
        (c : Int) (hc_pos : 1 ≤ c) (hc_le : c ≤ 100000)
        (hc_uniform : ∀ i, i < costs.val.length → costAt costs i = c)
        (r : Std.I64) (hr : minimum_cost target words costs = ok r), ((∀ idxs, ¬ IsDecomp target words idxs) → r.val = -1) ∧
          ((∃ idxs, IsDecomp target words idxs) →
            ∃ best, IsDecomp target words best ∧
              (∀ idxs, IsDecomp target words idxs → best.length ≤ idxs.length) ∧
                r.val = c * (best.length : Int))) := by
    sorry

  /-- Whenever the function returns a result r, if there exists an index i with 0 <= i < len(words) such that words[i] = target, then r >= 0 and r <= min { costs[i] | 0 <= i < len(words) and words[i] = target }.
    Preconditions: Common input assumptions: len(target) is between 1 and 2000 inclusive; 1 <= len(words) = len(costs) <= 50; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= len(target) and every byte of words[i] is a lowercase English letter code (97 through 122); every byte of target is a lowercase English letter code; for every i with 0 <= i < len(words), 1 <= costs[i] <= 100000. All indices are 0-based. -/
  theorem spec_12 (target : Slice Std.U8) (words : Slice (Vec Std.U8))
      (costs : Slice Std.I64)
      (hT_pos : 1 ≤ target.val.length) (hT_le : target.val.length ≤ 2000)
      (hW_pos : 1 ≤ words.val.length) (hWC : words.val.length = costs.val.length)
      (hW_le : words.val.length ≤ 50)
      (hW_word_pos : ∀ i, i < words.val.length → 1 ≤ (wordAt words i).length)
      (hW_word_le : ∀ i, i < words.val.length → (wordAt words i).length ≤ target.val.length)
      (hW_lower : ∀ i, i < words.val.length → ∀ b, b ∈ wordAt words i →
        97 ≤ b.val ∧ b.val ≤ 122)
      (hT_lower : ∀ b, b ∈ target.val → 97 ≤ b.val ∧ b.val ≤ 122)
      (hC_bounds : ∀ i, i < costs.val.length →
        1 ≤ costAt costs i ∧ costAt costs i ≤ 100000)
      (h_exists : ∃ i, i < words.val.length ∧ wordAt words i = target.val)
      (r : Std.I64) (hr : minimum_cost target words costs = ok r) :
      0 ≤ r.val ∧
        (∀ i, i < words.val.length → wordAt words i = target.val → r.val ≤ costAt costs i) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (target : Slice Std.U8) (words : Slice (Vec Std.U8))
        (costs : Slice Std.I64)
        (hT_pos : 1 ≤ target.val.length) (hT_le : target.val.length ≤ 2000)
        (hW_pos : 1 ≤ words.val.length) (hWC : words.val.length = costs.val.length)
        (hW_le : words.val.length ≤ 50)
        (hW_word_pos : ∀ i, i < words.val.length → 1 ≤ (wordAt words i).length)
        (hW_word_le : ∀ i, i < words.val.length → (wordAt words i).length ≤ target.val.length)
        (hW_lower : ∀ i, i < words.val.length → ∀ b, b ∈ wordAt words i →
          97 ≤ b.val ∧ b.val ≤ 122)
        (hT_lower : ∀ b, b ∈ target.val → 97 ≤ b.val ∧ b.val ≤ 122)
        (hC_bounds : ∀ i, i < costs.val.length →
          1 ≤ costAt costs i ∧ costAt costs i ≤ 100000)
        (h_exists : ∃ i, i < words.val.length ∧ wordAt words i = target.val)
        (r : Std.I64) (hr : minimum_cost target words costs = ok r), 0 ≤ r.val ∧
          (∀ i, i < words.val.length → wordAt words i = target.val → r.val ≤ costAt costs i)) := by
    sorry

  /-- Whenever the function returns a result r with r >= 0, there exists an index i with 0 <= i < len(words) such that words[i] is a prefix of target, and there exists an index j with 0 <= j < len(words) such that words[j] is a suffix of target. Here words[i] is a prefix of target if len(words[i]) <= len(target) and words[i][k] = target[k] for every 0 <= k < len(words[i]); it is a suffix if len(words[j]) <= len(target) and words[j][k] = target[len(target)-len(words[j])+k] for every 0 <= k < len(words[j]).
    Preconditions: Common input assumptions: len(target) is between 1 and 2000 inclusive; 1 <= len(words) = len(costs) <= 50; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= len(target) and every byte of words[i] is a lowercase English letter code (97 through 122); every byte of target is a lowercase English letter code; for every i with 0 <= i < len(words), 1 <= costs[i] <= 100000. All indices are 0-based. -/
  theorem spec_13 (target : Slice Std.U8) (words : Slice (Vec Std.U8))
      (costs : Slice Std.I64)
      (hT_pos : 1 ≤ target.val.length) (hT_le : target.val.length ≤ 2000)
      (hW_pos : 1 ≤ words.val.length) (hWC : words.val.length = costs.val.length)
      (hW_le : words.val.length ≤ 50)
      (hW_word_pos : ∀ i, i < words.val.length → 1 ≤ (wordAt words i).length)
      (hW_word_le : ∀ i, i < words.val.length → (wordAt words i).length ≤ target.val.length)
      (hW_lower : ∀ i, i < words.val.length → ∀ b, b ∈ wordAt words i →
        97 ≤ b.val ∧ b.val ≤ 122)
      (hT_lower : ∀ b, b ∈ target.val → 97 ≤ b.val ∧ b.val ≤ 122)
      (hC_bounds : ∀ i, i < costs.val.length →
        1 ≤ costAt costs i ∧ costAt costs i ≤ 100000)
      (r : Std.I64) (hr : minimum_cost target words costs = ok r) (hr_nonneg : 0 ≤ r.val) :
      (∃ i, i < words.val.length ∧ IsPrefixOf (wordAt words i) target.val) ∧
        (∃ j, j < words.val.length ∧ IsSuffixOf (wordAt words j) target.val) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (target : Slice Std.U8) (words : Slice (Vec Std.U8))
        (costs : Slice Std.I64)
        (hT_pos : 1 ≤ target.val.length) (hT_le : target.val.length ≤ 2000)
        (hW_pos : 1 ≤ words.val.length) (hWC : words.val.length = costs.val.length)
        (hW_le : words.val.length ≤ 50)
        (hW_word_pos : ∀ i, i < words.val.length → 1 ≤ (wordAt words i).length)
        (hW_word_le : ∀ i, i < words.val.length → (wordAt words i).length ≤ target.val.length)
        (hW_lower : ∀ i, i < words.val.length → ∀ b, b ∈ wordAt words i →
          97 ≤ b.val ∧ b.val ≤ 122)
        (hT_lower : ∀ b, b ∈ target.val → 97 ≤ b.val ∧ b.val ≤ 122)
        (hC_bounds : ∀ i, i < costs.val.length →
          1 ≤ costAt costs i ∧ costAt costs i ≤ 100000)
        (r : Std.I64) (hr : minimum_cost target words costs = ok r) (hr_nonneg : 0 ≤ r.val), (∃ i, i < words.val.length ∧ IsPrefixOf (wordAt words i) target.val) ∧
          (∃ j, j < words.val.length ∧ IsSuffixOf (wordAt words j) target.val)) := by
    sorry

  /-- Let r be the result on (target, words, costs) and r_c the result on (target, words, costs_c). Whenever both results are returned: if r >= 0 then r_c = c * r, and if r = -1 then r_c = -1.
    Preconditions: Common input assumptions: len(target) is between 1 and 2000 inclusive; 1 <= len(words) = len(costs) <= 50; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= len(target) and every byte of words[i] is a lowercase English letter code (97 through 122); every byte of target is a lowercase English letter code; for every i with 0 <= i < len(words), 1 <= costs[i] <= 100000. All indices are 0-based. In addition, let c be an integer with 1 <= c and c * costs[i] <= 100000 for every i with 0 <= i < len(words); define costs_c[i] = c * costs[i] for 0 <= i < len(words). -/
  theorem spec_14 (target : Slice Std.U8) (words : Slice (Vec Std.U8))
      (costs : Slice Std.I64)
      (hT_pos : 1 ≤ target.val.length) (hT_le : target.val.length ≤ 2000)
      (hW_pos : 1 ≤ words.val.length) (hWC : words.val.length = costs.val.length)
      (hW_le : words.val.length ≤ 50)
      (hW_word_pos : ∀ i, i < words.val.length → 1 ≤ (wordAt words i).length)
      (hW_word_le : ∀ i, i < words.val.length → (wordAt words i).length ≤ target.val.length)
      (hW_lower : ∀ i, i < words.val.length → ∀ b, b ∈ wordAt words i →
        97 ≤ b.val ∧ b.val ≤ 122)
      (hT_lower : ∀ b, b ∈ target.val → 97 ≤ b.val ∧ b.val ≤ 122)
      (hC_bounds : ∀ i, i < costs.val.length →
        1 ≤ costAt costs i ∧ costAt costs i ≤ 100000)
      (c : Int) (hc_pos : 1 ≤ c)
      (hc_fits : ∀ i, i < costs.val.length → c * costAt costs i ≤ 100000)
      (costs_c : Slice Std.I64) (hcosts_c_len : costs_c.val.length = words.val.length)
      (hcosts_c : ∀ i, i < words.val.length → costAt costs_c i = c * costAt costs i)
      (r rc : Std.I64) (hr : minimum_cost target words costs = ok r)
      (hrc : minimum_cost target words costs_c = ok rc) :
      (0 ≤ r.val → rc.val = c * r.val) ∧ (r.val = -1 → rc.val = -1) := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (target : Slice Std.U8) (words : Slice (Vec Std.U8))
        (costs : Slice Std.I64)
        (hT_pos : 1 ≤ target.val.length) (hT_le : target.val.length ≤ 2000)
        (hW_pos : 1 ≤ words.val.length) (hWC : words.val.length = costs.val.length)
        (hW_le : words.val.length ≤ 50)
        (hW_word_pos : ∀ i, i < words.val.length → 1 ≤ (wordAt words i).length)
        (hW_word_le : ∀ i, i < words.val.length → (wordAt words i).length ≤ target.val.length)
        (hW_lower : ∀ i, i < words.val.length → ∀ b, b ∈ wordAt words i →
          97 ≤ b.val ∧ b.val ≤ 122)
        (hT_lower : ∀ b, b ∈ target.val → 97 ≤ b.val ∧ b.val ≤ 122)
        (hC_bounds : ∀ i, i < costs.val.length →
          1 ≤ costAt costs i ∧ costAt costs i ≤ 100000)
        (c : Int) (hc_pos : 1 ≤ c)
        (hc_fits : ∀ i, i < costs.val.length → c * costAt costs i ≤ 100000)
        (costs_c : Slice Std.I64) (hcosts_c_len : costs_c.val.length = words.val.length)
        (hcosts_c : ∀ i, i < words.val.length → costAt costs_c i = c * costAt costs i)
        (r rc : Std.I64) (hr : minimum_cost target words costs = ok r)
        (hrc : minimum_cost target words costs_c = ok rc), (0 ≤ r.val → rc.val = c * r.val) ∧ (r.val = -1 → rc.val = -1)) := by
    sorry

  /-- The function returns a result r; in particular, it does not fail (no out-of-bounds access, arithmetic overflow, or panic occurs) on any input satisfying the preconditions.
    Preconditions: Common input assumptions: len(target) is between 1 and 2000 inclusive; 1 <= len(words) = len(costs) <= 50; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= len(target) and every byte of words[i] is a lowercase English letter code (97 through 122); every byte of target is a lowercase English letter code; for every i with 0 <= i < len(words), 1 <= costs[i] <= 100000. All indices are 0-based. -/
  theorem spec_15 (target : Slice Std.U8) (words : Slice (Vec Std.U8))
      (costs : Slice Std.I64)
      (hT_pos : 1 ≤ target.val.length) (hT_le : target.val.length ≤ 2000)
      (hW_pos : 1 ≤ words.val.length) (hWC : words.val.length = costs.val.length)
      (hW_le : words.val.length ≤ 50)
      (hW_word_pos : ∀ i, i < words.val.length → 1 ≤ (wordAt words i).length)
      (hW_word_le : ∀ i, i < words.val.length → (wordAt words i).length ≤ target.val.length)
      (hW_lower : ∀ i, i < words.val.length → ∀ b, b ∈ wordAt words i →
        97 ≤ b.val ∧ b.val ≤ 122)
      (hT_lower : ∀ b, b ∈ target.val → 97 ≤ b.val ∧ b.val ≤ 122)
      (hC_bounds : ∀ i, i < costs.val.length →
        1 ≤ costAt costs i ∧ costAt costs i ≤ 100000) :
      ∃ r : Std.I64, minimum_cost target words costs = ok r := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (target : Slice Std.U8) (words : Slice (Vec Std.U8))
        (costs : Slice Std.I64)
        (hT_pos : 1 ≤ target.val.length) (hT_le : target.val.length ≤ 2000)
        (hW_pos : 1 ≤ words.val.length) (hWC : words.val.length = costs.val.length)
        (hW_le : words.val.length ≤ 50)
        (hW_word_pos : ∀ i, i < words.val.length → 1 ≤ (wordAt words i).length)
        (hW_word_le : ∀ i, i < words.val.length → (wordAt words i).length ≤ target.val.length)
        (hW_lower : ∀ i, i < words.val.length → ∀ b, b ∈ wordAt words i →
          97 ≤ b.val ∧ b.val ≤ 122)
        (hT_lower : ∀ b, b ∈ target.val → 97 ≤ b.val ∧ b.val ≤ 122)
        (hC_bounds : ∀ i, i < costs.val.length →
          1 ≤ costAt costs i ∧ costAt costs i ≤ 100000), ∃ r : Std.I64, minimum_cost target words costs = ok r) := by
    sorry

  end AegisSpec.MinimumCost
