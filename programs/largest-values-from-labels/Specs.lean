import Aegis.LargestValsFromLabels.Code.Funs

/-!
# Specifications of `Aegis.LargestValsFromLabels.largest_vals_from_labels`

LeetCode problem `largest-values-from-labels`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.LargestValsFromLabels

  namespace AegisSpec.LargestValsFromLabels

  def i64At (s : Slice I64) (i : Nat) : Int := ((s.val[i]?).map (fun x => x.val)).getD 0

  def toInts (s : Slice I64) : List Int := s.val.map (fun x => x.val)

  def listMax : List Int → Int
    | [] => 0
    | x :: xs => xs.foldr max x

  def maxVal (values : Slice I64) : Int := listMax (toInts values)

  def SortedDesc (w : List Int) : Prop := w.Pairwise (fun a b => b ≤ a)

  def IsSortedVals (values : Slice I64) (w : List Int) : Prop :=
    w.Perm (toInts values) ∧ SortedDesc w

  def sumFirst (w : List Int) (k : Nat) : Int := (w.take k).sum

  def sortDesc (w : List Int) : List Int := List.insertionSort (fun a b => a ≥ b) w

  def subsetSum (values : Slice I64) (S : Finset Nat) : Int := ∑ i ∈ S, i64At values i

  def Feasible (values labels : Slice I64) (S : Finset Nat) (numWanted useLimit : Int) : Prop :=
    (∀ i ∈ S, i < values.length) ∧
    ((S.card : Int) ≤ numWanted) ∧
    (∀ l : Int, ((S.filter (fun i => i64At labels i = l)).card : Int) ≤ useLimit)

  def IsMaxSum (values labels : Slice I64) (numWanted useLimit r : Int) : Prop :=
    (∃ S : Finset Nat, Feasible values labels S numWanted useLimit ∧ subsetSum values S = r) ∧
    (∀ S : Finset Nat, Feasible values labels S numWanted useLimit → subsetSum values S ≤ r)

  def labelSet (labels : Slice I64) : Finset Int := (Finset.range labels.length).image (i64At labels)

  def labelIdxs (labels : Slice I64) (l : Int) : Finset Nat :=
    (Finset.range labels.length).filter (fun i => i64At labels i = l)

  def labelVals (values labels : Slice I64) (l : Int) : List Int :=
    ((List.range labels.length).filter (fun i => (i64At labels i == l))).map (i64At values)

  def labelMultiplicity (labels : Slice I64) (l : Int) : Nat := (labelIdxs labels l).card

  def labelMax (values labels : Slice I64) (l : Int) : Int := listMax (labelVals values labels l)

  noncomputable def labelMaxList (values labels : Slice I64) : List Int :=
    (labelSet labels).toList.map (labelMax values labels)

  def topLabelSum (values labels : Slice I64) (l : Int) (t : Nat) : Int :=
    sumFirst (sortDesc (labelVals values labels l)) t

  def totalCap (labels : Slice I64) (useLimit : Int) : Nat :=
    ∑ l ∈ labelSet labels, min (labelMultiplicity labels l) useLimit.toNat

  def LengthOK (values labels : Slice I64) : Prop :=
    labels.length = values.length ∧ 1 ≤ values.length ∧ values.length ≤ 20000

  def ValueBounds (values : Slice I64) : Prop :=
    ∀ i : Nat, i < values.length → 0 ≤ i64At values i ∧ i64At values i ≤ 20000

  def LabelBounds (labels : Slice I64) : Prop :=
    ∀ i : Nat, i < labels.length → 0 ≤ i64At labels i ∧ i64At labels i ≤ 20000

  def NumWantedOK (values : Slice I64) (numWanted : I64) : Prop :=
    1 ≤ numWanted.val ∧ numWanted.val ≤ (values.length : Int)

  def UseLimitOK (values : Slice I64) (useLimit : I64) : Prop :=
    1 ≤ useLimit.val ∧ useLimit.val ≤ (values.length : Int)

  def PreBase (values labels : Slice I64) : Prop :=
    LengthOK values labels ∧ ValueBounds values ∧ LabelBounds labels

  def Pre (values labels : Slice I64) (numWanted useLimit : I64) : Prop :=
    PreBase values labels ∧ NumWantedOK values numWanted ∧ UseLimitOK values useLimit

  def Returns (values labels : Slice I64) (numWanted useLimit r : I64) : Prop :=
    largest_vals_from_labels values labels numWanted useLimit = ok r

  theorem feasible_empty (values labels : Slice I64) (numWanted useLimit : Int)
      (hn : 0 ≤ numWanted) (hu : 0 ≤ useLimit) :
      Feasible values labels ∅ numWanted useLimit := by
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      simp at hi
    · simpa using hn
    · intro l
      simpa using hu

  /-- The function returns a result r and r = max { ∑_{i∈S} values[i] | S ⊆ {0,...,n-1}, |S| ≤ numWanted, and for every integer l, |{i∈S | labels[i]=l}| ≤ useLimit }, where S ranges over finite subsets of indices and the empty subset is allowed.
    Preconditions: Let n = len(values) = len(labels). Assume 1 ≤ n ≤ 2·10^4, 0 ≤ values[i] ≤ 2·10^4 and 0 ≤ labels[i] ≤ 2·10^4 for every 0 ≤ i < n, and 1 ≤ numWanted ≤ n and 1 ≤ useLimit ≤ n. -/
  theorem spec_1 (values labels : Slice I64) (numWanted useLimit : I64)
      (hpre : Pre values labels numWanted useLimit) :
      ∃ r : I64, Returns values labels numWanted useLimit r ∧
        IsMaxSum values labels numWanted.val useLimit.val r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (values labels : Slice I64) (numWanted useLimit : I64)
        (hpre : Pre values labels numWanted useLimit), ∃ r : I64, Returns values labels numWanted useLimit r ∧
          IsMaxSum values labels numWanted.val useLimit.val r.val) := by
    sorry

  /-- The function returns a result r; it does not fail (no panic, out-of-bounds access, or arithmetic overflow).
    Preconditions: Let n = len(values) = len(labels). Assume 1 ≤ n ≤ 2·10^4, 0 ≤ values[i] ≤ 2·10^4 and 0 ≤ labels[i] ≤ 2·10^4 for every 0 ≤ i < n, and 1 ≤ numWanted ≤ n and 1 ≤ useLimit ≤ n. -/
  theorem spec_2 (values labels : Slice I64) (numWanted useLimit : I64)
      (hpre : Pre values labels numWanted useLimit) :
      ∃ r : I64, Returns values labels numWanted useLimit r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (values labels : Slice I64) (numWanted useLimit : I64)
        (hpre : Pre values labels numWanted useLimit), ∃ r : I64, Returns values labels numWanted useLimit r) := by
    sorry

  /-- Whenever the function returns a result r, let v_(1) ≥ v_(2) ≥ ... ≥ v_(n) be the values values[0],...,values[n-1] sorted in nonincreasing order (ties broken arbitrarily). Then r ≤ v_(1)+...+v_(numWanted).
    Preconditions: Let n = len(values) = len(labels). Assume 1 ≤ n ≤ 2·10^4, 0 ≤ values[i] ≤ 2·10^4 and 0 ≤ labels[i] ≤ 2·10^4 for every 0 ≤ i < n, and 1 ≤ numWanted ≤ n and 1 ≤ useLimit ≤ n. -/
  theorem spec_3 (values labels : Slice I64) (numWanted useLimit r : I64)
      (hpre : Pre values labels numWanted useLimit)
      (hres : Returns values labels numWanted useLimit r) :
      ∃ w : List Int, IsSortedVals values w ∧ r.val ≤ sumFirst w numWanted.val.toNat := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (values labels : Slice I64) (numWanted useLimit r : I64)
        (hpre : Pre values labels numWanted useLimit)
        (hres : Returns values labels numWanted useLimit r), ∃ w : List Int, IsSortedVals values w ∧ r.val ≤ sumFirst w numWanted.val.toNat) := by
    sorry

  /-- Whenever the function returns a result r, r ≥ max { values[i] | 0 ≤ i < n }.
    Preconditions: Let n = len(values) = len(labels). Assume 1 ≤ n ≤ 2·10^4, 0 ≤ values[i] ≤ 2·10^4 and 0 ≤ labels[i] ≤ 2·10^4 for every 0 ≤ i < n, and 1 ≤ numWanted ≤ n and 1 ≤ useLimit ≤ n. -/
  theorem spec_4 (values labels : Slice I64) (numWanted useLimit r : I64)
      (hpre : Pre values labels numWanted useLimit)
      (hres : Returns values labels numWanted useLimit r) :
      maxVal values ≤ r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (values labels : Slice I64) (numWanted useLimit r : I64)
        (hpre : Pre values labels numWanted useLimit)
        (hres : Returns values labels numWanted useLimit r), maxVal values ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, let w_(1) ≥ ... ≥ w_(n) be the values sorted in nonincreasing order and let k = min(numWanted, useLimit). Then r = w_(1)+...+w_(k).
    Preconditions: Let n = len(values) = len(labels). Assume 1 ≤ n ≤ 2·10^4, 0 ≤ values[i] ≤ 2·10^4 and 0 ≤ labels[i] ≤ 2·10^4 for every 0 ≤ i < n, and 1 ≤ numWanted ≤ n and 1 ≤ useLimit ≤ n. Additionally assume labels[i] = c for one fixed integer c and every 0 ≤ i < n. -/
  theorem spec_5 (values labels : Slice I64) (numWanted useLimit r : I64) (c : Int)
      (hpre : Pre values labels numWanted useLimit)
      (hlabels : ∀ i : Nat, i < values.length → i64At labels i = c)
      (hres : Returns values labels numWanted useLimit r) :
      ∃ w : List Int, IsSortedVals values w ∧
        r.val = sumFirst w (min numWanted.val.toNat useLimit.val.toNat) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (values labels : Slice I64) (numWanted useLimit r : I64) (c : Int)
        (hpre : Pre values labels numWanted useLimit)
        (hlabels : ∀ i : Nat, i < values.length → i64At labels i = c)
        (hres : Returns values labels numWanted useLimit r), ∃ w : List Int, IsSortedVals values w ∧
          r.val = sumFirst w (min numWanted.val.toNat useLimit.val.toNat)) := by
    sorry

  /-- Whenever the function returns a result r, let w_(1) ≥ ... ≥ w_(n) be the values sorted in nonincreasing order. Then r = w_(1)+...+w_(numWanted).
    Preconditions: Let n = len(values) = len(labels). Assume 1 ≤ n ≤ 2·10^4, 0 ≤ values[i] ≤ 2·10^4 and 0 ≤ labels[i] ≤ 2·10^4 for every 0 ≤ i < n, and 1 ≤ numWanted ≤ n and 1 ≤ useLimit ≤ n. Additionally assume labels[i] ≠ labels[j] for all 0 ≤ i < j < n. -/
  theorem spec_6 (values labels : Slice I64) (numWanted useLimit r : I64)
      (hpre : Pre values labels numWanted useLimit)
      (hdistinct : ∀ i j : Nat, i < j → j < values.length → i64At labels i ≠ i64At labels j)
      (hres : Returns values labels numWanted useLimit r) :
      ∃ w : List Int, IsSortedVals values w ∧ r.val = sumFirst w numWanted.val.toNat := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (values labels : Slice I64) (numWanted useLimit r : I64)
        (hpre : Pre values labels numWanted useLimit)
        (hdistinct : ∀ i j : Nat, i < j → j < values.length → i64At labels i ≠ i64At labels j)
        (hres : Returns values labels numWanted useLimit r), ∃ w : List Int, IsSortedVals values w ∧ r.val = sumFirst w numWanted.val.toNat) := by
    sorry

  /-- Whenever the function returns a result r, r = max { values[i] | 0 ≤ i < n }.
    Preconditions: Let n = len(values) = len(labels). Assume 1 ≤ n ≤ 2·10^4, 0 ≤ values[i] ≤ 2·10^4 and 0 ≤ labels[i] ≤ 2·10^4 for every 0 ≤ i < n, and 1 ≤ numWanted ≤ n and 1 ≤ useLimit ≤ n. Additionally assume numWanted = 1. -/
  theorem spec_7 (values labels : Slice I64) (numWanted useLimit r : I64)
      (hpre : Pre values labels numWanted useLimit)
      (hnumWanted : numWanted.val = 1)
      (hres : Returns values labels numWanted useLimit r) :
      r.val = maxVal values := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (values labels : Slice I64) (numWanted useLimit r : I64)
        (hpre : Pre values labels numWanted useLimit)
        (hnumWanted : numWanted.val = 1)
        (hres : Returns values labels numWanted useLimit r), r.val = maxVal values) := by
    sorry

  /-- Whenever the function returns a result r, let L be the set of integers l for which there exists i with 0 ≤ i < n and labels[i]=l. For each l∈L let M_l = max { values[i] | 0 ≤ i < n and labels[i]=l }. Let d=|L| and let M_(1) ≥ ... ≥ M_(d) be the numbers M_l sorted in nonincreasing order. Then r = M_(1)+...+M_(k), where k = min(numWanted, d).
    Preconditions: Let n = len(values) = len(labels). Assume 1 ≤ n ≤ 2·10^4, 0 ≤ values[i] ≤ 2·10^4 and 0 ≤ labels[i] ≤ 2·10^4 for every 0 ≤ i < n, and 1 ≤ numWanted ≤ n and 1 ≤ useLimit ≤ n. Additionally assume useLimit = 1. -/
  theorem spec_8 (values labels : Slice I64) (numWanted useLimit r : I64)
      (hpre : Pre values labels numWanted useLimit)
      (huseLimit : useLimit.val = 1)
      (hres : Returns values labels numWanted useLimit r) :
      ∃ ms : List Int, ms.Perm (labelMaxList values labels) ∧ SortedDesc ms ∧
        r.val = sumFirst ms (min numWanted.val.toNat (labelSet labels).card) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (values labels : Slice I64) (numWanted useLimit r : I64)
        (hpre : Pre values labels numWanted useLimit)
        (huseLimit : useLimit.val = 1)
        (hres : Returns values labels numWanted useLimit r), ∃ ms : List Int, ms.Perm (labelMaxList values labels) ∧ SortedDesc ms ∧
          r.val = sumFirst ms (min numWanted.val.toNat (labelSet labels).card)) := by
    sorry

  /-- Whenever the function returns a result r, let L be the set of integers l for which there exists i with labels[i]=l. For each l∈L let c_l = |{i | 0 ≤ i < n and labels[i]=l}| and t_l = min(useLimit, c_l). Let W_l be the sum of the t_l largest values in the multiset { values[i] | 0 ≤ i < n and labels[i]=l } (empty sum if t_l=0). Then r = ∑_{l∈L} W_l.
    Preconditions: Let n = len(values) = len(labels). Assume 1 ≤ n ≤ 2·10^4, 0 ≤ values[i] ≤ 2·10^4 and 0 ≤ labels[i] ≤ 2·10^4 for every 0 ≤ i < n, and 1 ≤ numWanted ≤ n and 1 ≤ useLimit ≤ n. Additionally assume numWanted = n. -/
  theorem spec_9 (values labels : Slice I64) (numWanted useLimit r : I64)
      (hpre : Pre values labels numWanted useLimit)
      (hnumWanted : numWanted.val = (values.length : Int))
      (hres : Returns values labels numWanted useLimit r) :
      r.val = ∑ l ∈ labelSet labels,
        topLabelSum values labels l (min useLimit.val.toNat (labelMultiplicity labels l)) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (values labels : Slice I64) (numWanted useLimit r : I64)
        (hpre : Pre values labels numWanted useLimit)
        (hnumWanted : numWanted.val = (values.length : Int))
        (hres : Returns values labels numWanted useLimit r), r.val = ∑ l ∈ labelSet labels,
          topLabelSum values labels l (min useLimit.val.toNat (labelMultiplicity labels l))) := by
    sorry

  /-- For every pair of integers k1,k2 with 1 ≤ k1 ≤ k2 ≤ n, let r1 be the result of largest_vals_from_labels(values, labels, k1, useLimit) and r2 the result of largest_vals_from_labels(values, labels, k2, useLimit). Whenever both calls return results, r1 ≤ r2.
    Preconditions: Let n = len(values) = len(labels). Assume 1 ≤ n ≤ 2·10^4, 0 ≤ values[i] ≤ 2·10^4 and 0 ≤ labels[i] ≤ 2·10^4 for every 0 ≤ i < n, and 1 ≤ useLimit ≤ n. -/
  theorem spec_10 (values labels : Slice I64) (useLimit k1 k2 r1 r2 : I64)
      (hpre : PreBase values labels ∧ UseLimitOK values useLimit)
      (hk : 1 ≤ k1.val ∧ k1.val ≤ k2.val ∧ k2.val ≤ (values.length : Int))
      (h1 : Returns values labels k1 useLimit r1)
      (h2 : Returns values labels k2 useLimit r2) :
      r1.val ≤ r2.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (values labels : Slice I64) (useLimit k1 k2 r1 r2 : I64)
        (hpre : PreBase values labels ∧ UseLimitOK values useLimit)
        (hk : 1 ≤ k1.val ∧ k1.val ≤ k2.val ∧ k2.val ≤ (values.length : Int))
        (h1 : Returns values labels k1 useLimit r1)
        (h2 : Returns values labels k2 useLimit r2), r1.val ≤ r2.val) := by
    sorry

  /-- For every pair of integers u1,u2 with 1 ≤ u1 ≤ u2 ≤ n, let r1 be the result of largest_vals_from_labels(values, labels, numWanted, u1) and r2 the result of largest_vals_from_labels(values, labels, numWanted, u2). Whenever both calls return results, r1 ≤ r2.
    Preconditions: Let n = len(values) = len(labels). Assume 1 ≤ n ≤ 2·10^4, 0 ≤ values[i] ≤ 2·10^4 and 0 ≤ labels[i] ≤ 2·10^4 for every 0 ≤ i < n, and 1 ≤ numWanted ≤ n. -/
  theorem spec_11 (values labels : Slice I64) (numWanted u1 u2 r1 r2 : I64)
      (hpre : PreBase values labels ∧ NumWantedOK values numWanted)
      (hu : 1 ≤ u1.val ∧ u1.val ≤ u2.val ∧ u2.val ≤ (values.length : Int))
      (h1 : Returns values labels numWanted u1 r1)
      (h2 : Returns values labels numWanted u2 r2) :
      r1.val ≤ r2.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (values labels : Slice I64) (numWanted u1 u2 r1 r2 : I64)
        (hpre : PreBase values labels ∧ NumWantedOK values numWanted)
        (hu : 1 ≤ u1.val ∧ u1.val ≤ u2.val ∧ u2.val ≤ (values.length : Int))
        (h1 : Returns values labels numWanted u1 r1)
        (h2 : Returns values labels numWanted u2 r2), r1.val ≤ r2.val) := by
    sorry

  /-- For every bijection π of {0,...,n-1}, define slices values' and labels' of length n by values'[i]=values[π(i)] and labels'[i]=labels[π(i)] for 0 ≤ i < n. Whenever the call on (values, labels, numWanted, useLimit) returns r and the call on (values', labels', numWanted, useLimit) returns r', we have r' = r.
    Preconditions: Let n = len(values) = len(labels). Assume 1 ≤ n ≤ 2·10^4, 0 ≤ values[i] ≤ 2·10^4 and 0 ≤ labels[i] ≤ 2·10^4 for every 0 ≤ i < n, and 1 ≤ numWanted ≤ n and 1 ≤ useLimit ≤ n. -/
  theorem spec_12 (values labels values' labels' : Slice I64) (numWanted useLimit r r' : I64)
      (hpre : Pre values labels numWanted useLimit)
      (hlenValues' : values'.length = values.length)
      (hlenLabels' : labels'.length = labels.length)
      (π : Equiv.Perm (Fin values.length))
      (hvalues' : ∀ i : Fin values.length, i64At values' i.val = i64At values (π i).val)
      (hlabels' : ∀ i : Fin values.length, i64At labels' i.val = i64At labels (π i).val)
      (hres : Returns values labels numWanted useLimit r)
      (hres' : Returns values' labels' numWanted useLimit r') :
      r' = r := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (values labels values' labels' : Slice I64) (numWanted useLimit r r' : I64)
        (hpre : Pre values labels numWanted useLimit)
        (hlenValues' : values'.length = values.length)
        (hlenLabels' : labels'.length = labels.length)
        (π : Equiv.Perm (Fin values.length))
        (hvalues' : ∀ i : Fin values.length, i64At values' i.val = i64At values (π i).val)
        (hlabels' : ∀ i : Fin values.length, i64At labels' i.val = i64At labels (π i).val)
        (hres : Returns values labels numWanted useLimit r)
        (hres' : Returns values' labels' numWanted useLimit r'), r' = r) := by
    sorry

  /-- Whenever the function returns a result r, let L be the set of labels appearing in labels, and for each l∈L let c_l = |{i | 0 ≤ i < n and labels[i]=l}|. Set C = ∑_{l∈L} min(c_l, useLimit) and k = min(numWanted, C). Then there exists a subset S ⊆ {0,...,n-1} such that |S| = k, |S| ≤ numWanted, for every label l we have |{i∈S | labels[i]=l}| ≤ useLimit, and ∑_{i∈S} values[i] = r.
    Preconditions: Let n = len(values) = len(labels). Assume 1 ≤ n ≤ 2·10^4, 0 ≤ values[i] ≤ 2·10^4 and 0 ≤ labels[i] ≤ 2·10^4 for every 0 ≤ i < n, and 1 ≤ numWanted ≤ n and 1 ≤ useLimit ≤ n. -/
  theorem spec_13 (values labels : Slice I64) (numWanted useLimit r : I64)
      (hpre : Pre values labels numWanted useLimit)
      (hres : Returns values labels numWanted useLimit r) :
      ∃ S : Finset Nat, Feasible values labels S numWanted.val useLimit.val ∧
        S.card = min numWanted.val.toNat (totalCap labels useLimit.val) ∧
        subsetSum values S = r.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (values labels : Slice I64) (numWanted useLimit r : I64)
        (hpre : Pre values labels numWanted useLimit)
        (hres : Returns values labels numWanted useLimit r), ∃ S : Finset Nat, Feasible values labels S numWanted.val useLimit.val ∧
          S.card = min numWanted.val.toNat (totalCap labels useLimit.val) ∧
          subsetSum values S = r.val) := by
    sorry

  /-- Whenever the function returns a result r, there exists a subset S ⊆ {0,...,n-1} such that |S| ≤ numWanted, for every integer l we have |{i∈S | labels[i]=l}| ≤ useLimit, ∑_{i∈S} values[i] = r, and values[i] > 0 for every i∈S.
    Preconditions: Let n = len(values) = len(labels). Assume 1 ≤ n ≤ 2·10^4, 0 ≤ values[i] ≤ 2·10^4 and 0 ≤ labels[i] ≤ 2·10^4 for every 0 ≤ i < n, and 1 ≤ numWanted ≤ n and 1 ≤ useLimit ≤ n. -/
  theorem spec_14 (values labels : Slice I64) (numWanted useLimit r : I64)
      (hpre : Pre values labels numWanted useLimit)
      (hres : Returns values labels numWanted useLimit r) :
      ∃ S : Finset Nat, Feasible values labels S numWanted.val useLimit.val ∧
        subsetSum values S = r.val ∧ ∀ i ∈ S, 0 < i64At values i := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (values labels : Slice I64) (numWanted useLimit r : I64)
        (hpre : Pre values labels numWanted useLimit)
        (hres : Returns values labels numWanted useLimit r), ∃ S : Finset Nat, Feasible values labels S numWanted.val useLimit.val ∧
          subsetSum values S = r.val ∧ ∀ i ∈ S, 0 < i64At values i) := by
    sorry

  /-- Whenever the function returns a result r, let w_(1) >= ... >= w_(n) be the values sorted in nonincreasing order. Then r = w_(1)+...+w_(numWanted).
    Preconditions: Let n = len(values) = len(labels). Assume 1 <= n <= 2*10^4, 0 <= values[i] <= 2*10^4 and 0 <= labels[i] <= 2*10^4 for every 0 <= i < n, and 1 <= numWanted <= n and useLimit = n. -/
  theorem spec_15 (values labels : Slice I64) (numWanted useLimit r : I64)
      (hpre : PreBase values labels ∧ NumWantedOK values numWanted)
      (huseLimit : useLimit.val = (values.length : Int))
      (hres : Returns values labels numWanted useLimit r) :
      ∃ w : List Int, IsSortedVals values w ∧ r.val = sumFirst w numWanted.val.toNat := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (values labels : Slice I64) (numWanted useLimit r : I64)
        (hpre : PreBase values labels ∧ NumWantedOK values numWanted)
        (huseLimit : useLimit.val = (values.length : Int))
        (hres : Returns values labels numWanted useLimit r), ∃ w : List Int, IsSortedVals values w ∧ r.val = sumFirst w numWanted.val.toNat) := by
    sorry

  end AegisSpec.LargestValsFromLabels
