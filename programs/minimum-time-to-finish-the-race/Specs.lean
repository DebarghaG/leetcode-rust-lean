import Aegis.MinimumFinishTime.Code.Funs

/-!
# Specifications of `Aegis.MinimumFinishTime.minimum_finish_time`

LeetCode problem `minimum-time-to-finish-the-race`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.MinimumFinishTime

  namespace AegisSpec.MinimumFinishTime

  abbrev Tires := Slice (alloc.vec.Vec Std.I64)

  def entryFirst (v : alloc.vec.Vec Std.I64) : Int :=
    ((v.val[0]?).map (fun x => x.val)).getD 0

  def entrySecond (v : alloc.vec.Vec Std.I64) : Int :=
    ((v.val[1]?).map (fun x => x.val)).getD 0

  def tireList (tires : Tires) : List (Int × Int) :=
    tires.val.map (fun v => (entryFirst v, entrySecond v))

  def ValidTires (tires : Tires) : Prop :=
    1 ≤ tires.val.length ∧ tires.val.length ≤ 100000 ∧
      ∀ v ∈ tires.val,
        v.val.length = 2 ∧ 1 ≤ entryFirst v ∧ entryFirst v ≤ 100000 ∧
          2 ≤ entrySecond v ∧ entrySecond v ≤ 100000

  def minOfList : List Int → Int
    | [] => 0
    | x :: xs => xs.foldl min x

  def minFirst (ts : List (Int × Int)) : Int :=
    minOfList (ts.map (fun t => t.1))

  def seg (f r : Int) (k : Nat) : Int :=
    f * (r ^ k - 1) / (r - 1)

  def entryAt (ts : List (Int × Int)) (i : Nat) : Int × Int :=
    ts.getD i (0, 0)

  def segAt (ts : List (Int × Int)) (i k : Nat) : Int :=
    seg (entryAt ts i).1 (entryAt ts i).2 k

  def minSegAt (ts : List (Int × Int)) (k : Nat) : Int :=
    minOfList (ts.map (fun t => seg t.1 t.2 k))

  def twoLapCost (t : Int × Int) : Int :=
    t.1 * (1 + t.2)

  def minTwoLapCost (ts : List (Int × Int)) : Int :=
    minOfList (ts.map twoLapCost)

  abbrev RacePlan := List (Nat × Nat)

  def IsRacePlan (ts : List (Int × Int)) (numLaps : Int) (p : RacePlan) : Prop :=
    p ≠ [] ∧ (∀ q ∈ p, 1 ≤ q.2 ∧ q.1 < ts.length) ∧
      ((p.map (fun q => q.2)).sum : Int) = numLaps

  def planTime (ts : List (Int × Int)) (changeTime : Int) (p : RacePlan) : Int :=
    match p with
    | [] => 0
    | [q] => segAt ts q.1 q.2
    | q :: rest => segAt ts q.1 q.2 + changeTime + planTime ts changeTime rest

  def IsOptTime (ts : List (Int × Int)) (changeTime numLaps v : Int) : Prop :=
    (∃ p, IsRacePlan ts numLaps p ∧ planTime ts changeTime p = v) ∧
      ∀ p, IsRacePlan ts numLaps p → v ≤ planTime ts changeTime p

  def IsPermutation (ts ts' : List (Int × Int)) : Prop :=
    ts'.length = ts.length ∧
      ∃ π : Nat → Nat,
        (∀ i, i < ts.length → π i < ts.length) ∧
          (∀ i j, i < ts.length → j < ts.length → π i = π j → i = j) ∧
            ∀ j, j < ts.length → ts'[j]? = ts[π j]?

  def Embeds (ts ts' : List (Int × Int)) : Prop :=
    ∃ φ : Nat → Nat,
      (∀ i j, i < ts.length → j < ts.length → i < j → φ i < φ j) ∧
        ∀ i, i < ts.length → φ i < ts'.length ∧ ts'[φ i]? = ts[i]?

  /-- Define f_i = tires[i][0] and r_i = tires[i][1] for 0 <= i < len(tires). For any index i and integer k >= 1, let seg(i,k) = f_i * (r_i^k - 1) / (r_i - 1). A race plan is a pair of finite sequences (k_1,...,k_m) and (i_1,...,i_m) such that m >= 1, each k_t >= 1, 0 <= i_t < len(tires), and sum_{t=1}^m k_t = numLaps. Its time is seg(i_1,k_1) + sum_{t=2}^m (changeTime + seg(i_t,k_t)). Let OPT be the minimum time over all race plans. Whenever the function returns a result r, r = OPT.
    Preconditions: len(tires) >= 1, len(tires) <= 100000, and for every i with 0 <= i < len(tires), tires[i] has length 2, 1 <= tires[i][0] <= 100000, and 2 <= tires[i][1] <= 100000; also 1 <= changeTime <= 100000 and 1 <= numLaps <= 1000. -/
  theorem spec_1 (tires : Tires) (changeTime numLaps : Std.I64) (r : Std.I64)
      (htires : ValidTires tires)
      (hchange : 1 ≤ changeTime.val ∧ changeTime.val ≤ 100000)
      (hlaps : 1 ≤ numLaps.val ∧ numLaps.val ≤ 1000)
      (hres : minimum_finish_time tires changeTime numLaps = ok r) :
      IsOptTime (tireList tires) changeTime.val numLaps.val r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (tires : Tires) (changeTime numLaps : Std.I64) (r : Std.I64)
        (htires : ValidTires tires)
        (hchange : 1 ≤ changeTime.val ∧ changeTime.val ≤ 100000)
        (hlaps : 1 ≤ numLaps.val ∧ numLaps.val ≤ 1000)
        (hres : minimum_finish_time tires changeTime numLaps = ok r), IsOptTime (tireList tires) changeTime.val numLaps.val r.val) := by
    sorry

  /-- The function returns a result r (it does not fail) on every input satisfying the preconditions.
    Preconditions: len(tires) >= 1, len(tires) <= 100000, and for every i with 0 <= i < len(tires), tires[i] has length 2, 1 <= tires[i][0] <= 100000, and 2 <= tires[i][1] <= 100000; also 1 <= changeTime <= 100000 and 1 <= numLaps <= 1000. -/
  theorem spec_2 (tires : Tires) (changeTime numLaps : Std.I64)
      (htires : ValidTires tires)
      (hchange : 1 ≤ changeTime.val ∧ changeTime.val ≤ 100000)
      (hlaps : 1 ≤ numLaps.val ∧ numLaps.val ≤ 1000) :
      ∃ r : Std.I64, minimum_finish_time tires changeTime numLaps = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (tires : Tires) (changeTime numLaps : Std.I64)
        (htires : ValidTires tires)
        (hchange : 1 ≤ changeTime.val ∧ changeTime.val ≤ 100000)
        (hlaps : 1 ≤ numLaps.val ∧ numLaps.val ≤ 1000), ∃ r : Std.I64, minimum_finish_time tires changeTime numLaps = ok r) := by
    sorry

  /-- Let minF = min { tires[i][0] | 0 <= i < len(tires) }. Whenever the function returns a result r, numLaps * minF <= r.
    Preconditions: len(tires) >= 1, len(tires) <= 100000, and for every i with 0 <= i < len(tires), tires[i] has length 2, 1 <= tires[i][0] <= 100000, and 2 <= tires[i][1] <= 100000; also 1 <= changeTime <= 100000 and 1 <= numLaps <= 1000. -/
  theorem spec_3 (tires : Tires) (changeTime numLaps : Std.I64) (r : Std.I64)
      (htires : ValidTires tires)
      (hchange : 1 ≤ changeTime.val ∧ changeTime.val ≤ 100000)
      (hlaps : 1 ≤ numLaps.val ∧ numLaps.val ≤ 1000)
      (hres : minimum_finish_time tires changeTime numLaps = ok r) :
      numLaps.val * minFirst (tireList tires) ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (tires : Tires) (changeTime numLaps : Std.I64) (r : Std.I64)
        (htires : ValidTires tires)
        (hchange : 1 ≤ changeTime.val ∧ changeTime.val ≤ 100000)
        (hlaps : 1 ≤ numLaps.val ∧ numLaps.val ≤ 1000)
        (hres : minimum_finish_time tires changeTime numLaps = ok r), numLaps.val * minFirst (tireList tires) ≤ r.val) := by
    sorry

  /-- Let minF = min { tires[i][0] | 0 <= i < len(tires) }. Whenever the function returns a result r, r <= numLaps * minF + (numLaps - 1) * changeTime. This bound is achieved by using a tire with first-lap time minF and changing after every lap except the last (equivalently, before every lap except the first).
    Preconditions: len(tires) >= 1, len(tires) <= 100000, and for every i with 0 <= i < len(tires), tires[i] has length 2, 1 <= tires[i][0] <= 100000, and 2 <= tires[i][1] <= 100000; also 1 <= changeTime <= 100000 and 1 <= numLaps <= 1000. -/
  theorem spec_4 (tires : Tires) (changeTime numLaps : Std.I64) (r : Std.I64)
      (htires : ValidTires tires)
      (hchange : 1 ≤ changeTime.val ∧ changeTime.val ≤ 100000)
      (hlaps : 1 ≤ numLaps.val ∧ numLaps.val ≤ 1000)
      (hres : minimum_finish_time tires changeTime numLaps = ok r) :
      r.val ≤ numLaps.val * minFirst (tireList tires) + (numLaps.val - 1) * changeTime.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (tires : Tires) (changeTime numLaps : Std.I64) (r : Std.I64)
        (htires : ValidTires tires)
        (hchange : 1 ≤ changeTime.val ∧ changeTime.val ≤ 100000)
        (hlaps : 1 ≤ numLaps.val ∧ numLaps.val ≤ 1000)
        (hres : minimum_finish_time tires changeTime numLaps = ok r), r.val ≤ numLaps.val * minFirst (tireList tires) + (numLaps.val - 1) * changeTime.val) := by
    sorry

  /-- Define seg(i,k) = tires[i][0] * (tires[i][1]^k - 1) / (tires[i][1] - 1) for 0 <= i < len(tires) and k >= 1. Whenever the function returns a result r, there exist m >= 1, integers k_1,...,k_m >= 1, and indices i_1,...,i_m with 0 <= i_t < len(tires), sum_{t=1}^m k_t = numLaps, and r = seg(i_1,k_1) + sum_{t=2}^m (changeTime + seg(i_t,k_t)).
    Preconditions: len(tires) >= 1, len(tires) <= 100000, and for every i with 0 <= i < len(tires), tires[i] has length 2, 1 <= tires[i][0] <= 100000, and 2 <= tires[i][1] <= 100000; also 1 <= changeTime <= 100000 and 1 <= numLaps <= 1000. -/
  theorem spec_5 (tires : Tires) (changeTime numLaps : Std.I64) (r : Std.I64)
      (htires : ValidTires tires)
      (hchange : 1 ≤ changeTime.val ∧ changeTime.val ≤ 100000)
      (hlaps : 1 ≤ numLaps.val ∧ numLaps.val ≤ 1000)
      (hres : minimum_finish_time tires changeTime numLaps = ok r) :
      ∃ p : RacePlan,
        IsRacePlan (tireList tires) numLaps.val p ∧
          planTime (tireList tires) changeTime.val p = r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (tires : Tires) (changeTime numLaps : Std.I64) (r : Std.I64)
        (htires : ValidTires tires)
        (hchange : 1 ≤ changeTime.val ∧ changeTime.val ≤ 100000)
        (hlaps : 1 ≤ numLaps.val ∧ numLaps.val ≤ 1000)
        (hres : minimum_finish_time tires changeTime numLaps = ok r), ∃ p : RacePlan,
          IsRacePlan (tireList tires) numLaps.val p ∧
            planTime (tireList tires) changeTime.val p = r.val) := by
    sorry

  /-- Let minF = min { tires[i][0] | 0 <= i < len(tires) }. Whenever the function returns a result r, r = minF.
    Preconditions: len(tires) >= 1, len(tires) <= 100000, and for every i with 0 <= i < len(tires), tires[i] has length 2, 1 <= tires[i][0] <= 100000, and 2 <= tires[i][1] <= 100000; also 1 <= changeTime <= 100000 and numLaps = 1. -/
  theorem spec_6 (tires : Tires) (changeTime numLaps : Std.I64) (r : Std.I64)
      (htires : ValidTires tires)
      (hchange : 1 ≤ changeTime.val ∧ changeTime.val ≤ 100000)
      (hlaps : numLaps.val = 1)
      (hres : minimum_finish_time tires changeTime numLaps = ok r) :
      r.val = minFirst (tireList tires) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (tires : Tires) (changeTime numLaps : Std.I64) (r : Std.I64)
        (htires : ValidTires tires)
        (hchange : 1 ≤ changeTime.val ∧ changeTime.val ≤ 100000)
        (hlaps : numLaps.val = 1)
        (hres : minimum_finish_time tires changeTime numLaps = ok r), r.val = minFirst (tireList tires)) := by
    sorry

  /-- Let minF = min { tires[i][0] | 0 <= i < len(tires) }. Whenever the function returns a result r, r = min( min { tires[i][0] * (1 + tires[i][1]) | 0 <= i < len(tires) }, 2 * minF + changeTime ).
    Preconditions: len(tires) >= 1, len(tires) <= 100000, and for every i with 0 <= i < len(tires), tires[i] has length 2, 1 <= tires[i][0] <= 100000, and 2 <= tires[i][1] <= 100000; also 1 <= changeTime <= 100000 and numLaps = 2. -/
  theorem spec_7 (tires : Tires) (changeTime numLaps : Std.I64) (r : Std.I64)
      (htires : ValidTires tires)
      (hchange : 1 ≤ changeTime.val ∧ changeTime.val ≤ 100000)
      (hlaps : numLaps.val = 2)
      (hres : minimum_finish_time tires changeTime numLaps = ok r) :
      r.val =
        min (minTwoLapCost (tireList tires)) (2 * minFirst (tireList tires) + changeTime.val) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (tires : Tires) (changeTime numLaps : Std.I64) (r : Std.I64)
        (htires : ValidTires tires)
        (hchange : 1 ≤ changeTime.val ∧ changeTime.val ≤ 100000)
        (hlaps : numLaps.val = 2)
        (hres : minimum_finish_time tires changeTime numLaps = ok r), r.val =
          min (minTwoLapCost (tireList tires)) (2 * minFirst (tireList tires) + changeTime.val)) := by
    sorry

  /-- For every integer n with 1 <= n <= numLaps, whenever the function on (tires, changeTime, numLaps) returns r and the function on (tires, changeTime, n) returns r_n, we have r >= r_n.
    Preconditions: len(tires) >= 1, len(tires) <= 100000, and for every i with 0 <= i < len(tires), tires[i] has length 2, 1 <= tires[i][0] <= 100000, and 2 <= tires[i][1] <= 100000; also 1 <= changeTime <= 100000 and 1 <= numLaps <= 1000. -/
  theorem spec_8 (tires : Tires) (changeTime numLaps n : Std.I64) (r r_n : Std.I64)
      (htires : ValidTires tires)
      (hchange : 1 ≤ changeTime.val ∧ changeTime.val ≤ 100000)
      (hlaps : 1 ≤ numLaps.val ∧ numLaps.val ≤ 1000)
      (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ numLaps.val)
      (hres : minimum_finish_time tires changeTime numLaps = ok r)
      (hres_n : minimum_finish_time tires changeTime n = ok r_n) :
      r_n.val ≤ r.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (tires : Tires) (changeTime numLaps n : Std.I64) (r r_n : Std.I64)
        (htires : ValidTires tires)
        (hchange : 1 ≤ changeTime.val ∧ changeTime.val ≤ 100000)
        (hlaps : 1 ≤ numLaps.val ∧ numLaps.val ≤ 1000)
        (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ numLaps.val)
        (hres : minimum_finish_time tires changeTime numLaps = ok r)
        (hres_n : minimum_finish_time tires changeTime n = ok r_n), r_n.val ≤ r.val) := by
    sorry

  /-- For every integer c with changeTime <= c <= 100000, whenever the function on (tires, changeTime, numLaps) returns r and the function on (tires, c, numLaps) returns r_c, we have r <= r_c.
    Preconditions: len(tires) >= 1, len(tires) <= 100000, and for every i with 0 <= i < len(tires), tires[i] has length 2, 1 <= tires[i][0] <= 100000, and 2 <= tires[i][1] <= 100000; also 1 <= changeTime <= 100000 and 1 <= numLaps <= 1000. -/
  theorem spec_9 (tires : Tires) (changeTime c numLaps : Std.I64) (r r_c : Std.I64)
      (htires : ValidTires tires)
      (hchange : 1 ≤ changeTime.val ∧ changeTime.val ≤ 100000)
      (hc1 : changeTime.val ≤ c.val) (hc2 : c.val ≤ 100000)
      (hlaps : 1 ≤ numLaps.val ∧ numLaps.val ≤ 1000)
      (hres : minimum_finish_time tires changeTime numLaps = ok r)
      (hres_c : minimum_finish_time tires c numLaps = ok r_c) :
      r.val ≤ r_c.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (tires : Tires) (changeTime c numLaps : Std.I64) (r r_c : Std.I64)
        (htires : ValidTires tires)
        (hchange : 1 ≤ changeTime.val ∧ changeTime.val ≤ 100000)
        (hc1 : changeTime.val ≤ c.val) (hc2 : c.val ≤ 100000)
        (hlaps : 1 ≤ numLaps.val ∧ numLaps.val ≤ 1000)
        (hres : minimum_finish_time tires changeTime numLaps = ok r)
        (hres_c : minimum_finish_time tires c numLaps = ok r_c), r.val ≤ r_c.val) := by
    sorry

  /-- For every permutation pi of {0,...,len(tires)-1}, let tires' be the list of length len(tires) with tires'[j] = tires[pi(j)] for 0 <= j < len(tires). Whenever the function on (tires, changeTime, numLaps) returns r and the function on (tires', changeTime, numLaps) returns r', we have r = r'.
    Preconditions: len(tires) >= 1, len(tires) <= 100000, and for every i with 0 <= i < len(tires), tires[i] has length 2, 1 <= tires[i][0] <= 100000, and 2 <= tires[i][1] <= 100000; also 1 <= changeTime <= 100000 and 1 <= numLaps <= 1000. -/
  theorem spec_10 (tires tires' : Tires) (changeTime numLaps : Std.I64) (r r' : Std.I64)
      (htires : ValidTires tires)
      (htires' : ValidTires tires')
      (hperm : IsPermutation (tireList tires) (tireList tires'))
      (hchange : 1 ≤ changeTime.val ∧ changeTime.val ≤ 100000)
      (hlaps : 1 ≤ numLaps.val ∧ numLaps.val ≤ 1000)
      (hres : minimum_finish_time tires changeTime numLaps = ok r)
      (hres' : minimum_finish_time tires' changeTime numLaps = ok r') :
      r.val = r'.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (tires tires' : Tires) (changeTime numLaps : Std.I64) (r r' : Std.I64)
        (htires : ValidTires tires)
        (htires' : ValidTires tires')
        (hperm : IsPermutation (tireList tires) (tireList tires'))
        (hchange : 1 ≤ changeTime.val ∧ changeTime.val ≤ 100000)
        (hlaps : 1 ≤ numLaps.val ∧ numLaps.val ≤ 1000)
        (hres : minimum_finish_time tires changeTime numLaps = ok r)
        (hres' : minimum_finish_time tires' changeTime numLaps = ok r'), r.val = r'.val) := by
    sorry

  /-- Let a and b be distinct indices with 0 <= a,b < len(tires), tires[a][0] >= tires[b][0], and tires[a][1] >= tires[b][1]. Let tires' be the list obtained from tires by deleting the entry at position a. Whenever the function on (tires, changeTime, numLaps) returns r and the function on (tires', changeTime, numLaps) returns r', we have r = r'.
    Preconditions: len(tires) >= 2, len(tires) <= 100000, and for every i with 0 <= i < len(tires), tires[i] has length 2, 1 <= tires[i][0] <= 100000, and 2 <= tires[i][1] <= 100000; also 1 <= changeTime <= 100000 and 1 <= numLaps <= 1000. -/
  theorem spec_11 (tires tires' : Tires) (changeTime numLaps : Std.I64) (a b : Nat)
      (r r' : Std.I64)
      (htires : ValidTires tires)
      (hlen : 2 ≤ tires.val.length)
      (ha : a < tires.val.length) (hb : b < tires.val.length) (hab : a ≠ b)
      (hfa : (entryAt (tireList tires) b).1 ≤ (entryAt (tireList tires) a).1)
      (hra : (entryAt (tireList tires) b).2 ≤ (entryAt (tireList tires) a).2)
      (hdel : tireList tires' = (tireList tires).eraseIdx a)
      (hchange : 1 ≤ changeTime.val ∧ changeTime.val ≤ 100000)
      (hlaps : 1 ≤ numLaps.val ∧ numLaps.val ≤ 1000)
      (hres : minimum_finish_time tires changeTime numLaps = ok r)
      (hres' : minimum_finish_time tires' changeTime numLaps = ok r') :
      r.val = r'.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (tires tires' : Tires) (changeTime numLaps : Std.I64) (a b : Nat)
        (r r' : Std.I64)
        (htires : ValidTires tires)
        (hlen : 2 ≤ tires.val.length)
        (ha : a < tires.val.length) (hb : b < tires.val.length) (hab : a ≠ b)
        (hfa : (entryAt (tireList tires) b).1 ≤ (entryAt (tireList tires) a).1)
        (hra : (entryAt (tireList tires) b).2 ≤ (entryAt (tireList tires) a).2)
        (hdel : tireList tires' = (tireList tires).eraseIdx a)
        (hchange : 1 ≤ changeTime.val ∧ changeTime.val ≤ 100000)
        (hlaps : 1 ≤ numLaps.val ∧ numLaps.val ≤ 1000)
        (hres : minimum_finish_time tires changeTime numLaps = ok r)
        (hres' : minimum_finish_time tires' changeTime numLaps = ok r'), r.val = r'.val) := by
    sorry

  /-- Let tires' be any list satisfying the same constraints, with len(tires') <= 100000 and each entry [f,r] having 1 <= f <= 100000 and 2 <= r <= 100000, for which there exists a strictly increasing function phi from {0,...,len(tires)-1} to {0,...,len(tires')-1} such that tires'[phi(i)] = tires[i] for every i. Whenever the function on (tires, changeTime, numLaps) returns r and the function on (tires', changeTime, numLaps) returns r', we have r' <= r.
    Preconditions: len(tires) >= 1, len(tires) <= 100000, and for every i with 0 <= i < len(tires), tires[i] has length 2, 1 <= tires[i][0] <= 100000, and 2 <= tires[i][1] <= 100000; also 1 <= changeTime <= 100000 and 1 <= numLaps <= 1000. -/
  theorem spec_12 (tires tires' : Tires) (changeTime numLaps : Std.I64) (r r' : Std.I64)
      (htires : ValidTires tires)
      (htires' : ValidTires tires')
      (hemb : Embeds (tireList tires) (tireList tires'))
      (hchange : 1 ≤ changeTime.val ∧ changeTime.val ≤ 100000)
      (hlaps : 1 ≤ numLaps.val ∧ numLaps.val ≤ 1000)
      (hres : minimum_finish_time tires changeTime numLaps = ok r)
      (hres' : minimum_finish_time tires' changeTime numLaps = ok r') :
      r'.val ≤ r.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (tires tires' : Tires) (changeTime numLaps : Std.I64) (r r' : Std.I64)
        (htires : ValidTires tires)
        (htires' : ValidTires tires')
        (hemb : Embeds (tireList tires) (tireList tires'))
        (hchange : 1 ≤ changeTime.val ∧ changeTime.val ≤ 100000)
        (hlaps : 1 ≤ numLaps.val ∧ numLaps.val ≤ 1000)
        (hres : minimum_finish_time tires changeTime numLaps = ok r)
        (hres' : minimum_finish_time tires' changeTime numLaps = ok r'), r'.val ≤ r.val) := by
    sorry

  /-- Let j be any index with 0 <= j < len(tires), and let tires' be tires with one additional final entry equal to tires[j], so len(tires') = len(tires)+1. Whenever the function on (tires, changeTime, numLaps) returns r and the function on (tires', changeTime, numLaps) returns r', we have r = r'.
    Preconditions: len(tires) >= 1, len(tires) < 100000, and for every i with 0 <= i < len(tires), tires[i] has length 2, 1 <= tires[i][0] <= 100000, and 2 <= tires[i][1] <= 100000; also 1 <= changeTime <= 100000 and 1 <= numLaps <= 1000. -/
  theorem spec_13 (tires tires' : Tires) (changeTime numLaps : Std.I64) (j : Nat)
      (r r' : Std.I64)
      (htires : ValidTires tires)
      (hstrict : tires.val.length < 100000)
      (hj : j < tires.val.length)
      (happ : tireList tires' = tireList tires ++ [entryAt (tireList tires) j])
      (hchange : 1 ≤ changeTime.val ∧ changeTime.val ≤ 100000)
      (hlaps : 1 ≤ numLaps.val ∧ numLaps.val ≤ 1000)
      (hres : minimum_finish_time tires changeTime numLaps = ok r)
      (hres' : minimum_finish_time tires' changeTime numLaps = ok r') :
      r.val = r'.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (tires tires' : Tires) (changeTime numLaps : Std.I64) (j : Nat)
        (r r' : Std.I64)
        (htires : ValidTires tires)
        (hstrict : tires.val.length < 100000)
        (hj : j < tires.val.length)
        (happ : tireList tires' = tireList tires ++ [entryAt (tireList tires) j])
        (hchange : 1 ≤ changeTime.val ∧ changeTime.val ≤ 100000)
        (hlaps : 1 ≤ numLaps.val ∧ numLaps.val ≤ 1000)
        (hres : minimum_finish_time tires changeTime numLaps = ok r)
        (hres' : minimum_finish_time tires' changeTime numLaps = ok r'), r.val = r'.val) := by
    sorry

  /-- Define seg(i,k) = tires[i][0] * (tires[i][1]^k - 1) / (tires[i][1] - 1) for 0 <= i < len(tires) and k >= 1. Whenever the function returns a result r, r <= min { seg(i, numLaps) | 0 <= i < len(tires) }.
    Preconditions: len(tires) >= 1, len(tires) <= 100000, and for every i with 0 <= i < len(tires), tires[i] has length 2, 1 <= tires[i][0] <= 100000, and 2 <= tires[i][1] <= 100000; also 1 <= changeTime <= 100000 and 1 <= numLaps <= 1000. -/
  theorem spec_14 (tires : Tires) (changeTime numLaps : Std.I64) (r : Std.I64)
      (htires : ValidTires tires)
      (hchange : 1 ≤ changeTime.val ∧ changeTime.val ≤ 100000)
      (hlaps : 1 ≤ numLaps.val ∧ numLaps.val ≤ 1000)
      (hres : minimum_finish_time tires changeTime numLaps = ok r) :
      r.val ≤ minSegAt (tireList tires) numLaps.val.toNat := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (tires : Tires) (changeTime numLaps : Std.I64) (r : Std.I64)
        (htires : ValidTires tires)
        (hchange : 1 ≤ changeTime.val ∧ changeTime.val ≤ 100000)
        (hlaps : 1 ≤ numLaps.val ∧ numLaps.val ≤ 1000)
        (hres : minimum_finish_time tires changeTime numLaps = ok r), r.val ≤ minSegAt (tireList tires) numLaps.val.toNat) := by
    sorry

  /-- Whenever the function on (tires, changeTime, numLaps) returns r and the function on (tires', changeTime, numLaps) returns r', we have r' <= r.
    Preconditions: len(tires) >= 1, len(tires) <= 100000, and for every i with 0 <= i < len(tires), tires[i] has length 2, 1 <= tires[i][0] <= 100000, and 2 <= tires[i][1] <= 100000; also 1 <= changeTime <= 100000 and 1 <= numLaps <= 1000. Let tires' be any list with len(tires') = len(tires), each entry [f'_i, r'_i] satisfying 1 <= f'_i <= 100000 and 2 <= r'_i <= 100000, and f'_i <= tires[i][0] and r'_i <= tires[i][1] for every i. -/
  theorem spec_15 (tires tires' : Tires) (changeTime numLaps : Std.I64) (r r' : Std.I64)
      (htires : ValidTires tires)
      (htires' : ValidTires tires')
      (hlen : (tireList tires').length = (tireList tires).length)
      (hle : ∀ i, i < (tireList tires).length →
        (entryAt (tireList tires') i).1 ≤ (entryAt (tireList tires) i).1 ∧
          (entryAt (tireList tires') i).2 ≤ (entryAt (tireList tires) i).2)
      (hchange : 1 ≤ changeTime.val ∧ changeTime.val ≤ 100000)
      (hlaps : 1 ≤ numLaps.val ∧ numLaps.val ≤ 1000)
      (hres : minimum_finish_time tires changeTime numLaps = ok r)
      (hres' : minimum_finish_time tires' changeTime numLaps = ok r') :
      r'.val ≤ r.val := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (tires tires' : Tires) (changeTime numLaps : Std.I64) (r r' : Std.I64)
        (htires : ValidTires tires)
        (htires' : ValidTires tires')
        (hlen : (tireList tires').length = (tireList tires).length)
        (hle : ∀ i, i < (tireList tires).length →
          (entryAt (tireList tires') i).1 ≤ (entryAt (tireList tires) i).1 ∧
            (entryAt (tireList tires') i).2 ≤ (entryAt (tireList tires) i).2)
        (hchange : 1 ≤ changeTime.val ∧ changeTime.val ≤ 100000)
        (hlaps : 1 ≤ numLaps.val ∧ numLaps.val ≤ 1000)
        (hres : minimum_finish_time tires changeTime numLaps = ok r)
        (hres' : minimum_finish_time tires' changeTime numLaps = ok r'), r'.val ≤ r.val) := by
    sorry

  end AegisSpec.MinimumFinishTime
