import Aegis.MinimumTime.Code.Funs

/-!
# Specifications of `Aegis.MinimumTime.minimum_time`

LeetCode problem `minimum-time-to-complete-trips`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinimumTime

def tripCount (time : Slice Std.I64) (T : Int) : Int :=
  (time.val.map (fun t => Int.fdiv T t.val)).sum

def minElem (time : Slice Std.I64) : Int :=
  match time.val with
  | [] => 0
  | t :: ts => ts.foldl (fun acc u => min acc u.val) t.val

def ceilDiv (a b : Int) : Int :=
  Int.fdiv (a + b - 1) b

/-- The function returns a result r (it does not fail) and r is the least integer T ≥ 0 such that Σ_{i=0}^{len(time)-1} ⌊T / time[i]⌋ ≥ totalTrips, where ⌊·/·⌋ denotes integer division (floor) for non-negative operands.
  Preconditions: The array `time` is non-empty (1 ≤ len(time) ≤ 100000) and every element satisfies 1 ≤ time[i] ≤ 10000000. The integer `totalTrips` satisfies 1 ≤ totalTrips ≤ 10000000. -/
theorem spec_1 (time : Slice Std.I64) (totalTrips : Std.I64)
    (hne : 1 ≤ time.length) (hlen : time.length ≤ 100000)
    (hlo : ∀ i (hi : i < time.length), 1 ≤ (time.val[i]).val)
    (hhi : ∀ i (hi : i < time.length), (time.val[i]).val ≤ 10000000)
    (htlo : 1 ≤ totalTrips.val) (hthi : totalTrips.val ≤ 10000000) :
    ∃ r : Std.I64,
      Aegis.MinimumTime.minimum_time time totalTrips = ok r ∧
      0 ≤ r.val ∧
      totalTrips.val ≤ tripCount time r.val ∧
      ∀ T : Int, 0 ≤ T → T < r.val → tripCount time T < totalTrips.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (time : Slice Std.I64) (totalTrips : Std.I64)
    (hne : 1 ≤ time.length) (hlen : time.length ≤ 100000)
    (hlo : ∀ i (hi : i < time.length), 1 ≤ (time.val[i]).val)
    (hhi : ∀ i (hi : i < time.length), (time.val[i]).val ≤ 10000000)
    (htlo : 1 ≤ totalTrips.val) (hthi : totalTrips.val ≤ 10000000), ∃ r : Std.I64,
      Aegis.MinimumTime.minimum_time time totalTrips = ok r ∧
      0 ≤ r.val ∧
      totalTrips.val ≤ tripCount time r.val ∧
      ∀ T : Int, 0 ≤ T → T < r.val → tripCount time T < totalTrips.val) := by
  sorry

/-- The function returns a result r and r ≤ totalTrips * min_{0 ≤ i < len(time)} time[i].
  Preconditions: Same as spec_1. -/
theorem spec_2 (time : Slice Std.I64) (totalTrips : Std.I64)
    (hne : 1 ≤ time.length) (hlen : time.length ≤ 100000)
    (hlo : ∀ i (hi : i < time.length), 1 ≤ (time.val[i]).val)
    (hhi : ∀ i (hi : i < time.length), (time.val[i]).val ≤ 10000000)
    (htlo : 1 ≤ totalTrips.val) (hthi : totalTrips.val ≤ 10000000) :
    ∃ r : Std.I64,
      Aegis.MinimumTime.minimum_time time totalTrips = ok r ∧
      r.val ≤ totalTrips.val * minElem time := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (time : Slice Std.I64) (totalTrips : Std.I64)
    (hne : 1 ≤ time.length) (hlen : time.length ≤ 100000)
    (hlo : ∀ i (hi : i < time.length), 1 ≤ (time.val[i]).val)
    (hhi : ∀ i (hi : i < time.length), (time.val[i]).val ≤ 10000000)
    (htlo : 1 ≤ totalTrips.val) (hthi : totalTrips.val ≤ 10000000), ∃ r : Std.I64,
      Aegis.MinimumTime.minimum_time time totalTrips = ok r ∧
      r.val ≤ totalTrips.val * minElem time) := by
  sorry

/-- The function returns a result r and Σ_{i=0}^{len(time)-1} ⌊r / time[i]⌋ ≥ totalTrips.
  Preconditions: Same as spec_1. -/
theorem spec_3 (time : Slice Std.I64) (totalTrips : Std.I64)
    (hne : 1 ≤ time.length) (hlen : time.length ≤ 100000)
    (hlo : ∀ i (hi : i < time.length), 1 ≤ (time.val[i]).val)
    (hhi : ∀ i (hi : i < time.length), (time.val[i]).val ≤ 10000000)
    (htlo : 1 ≤ totalTrips.val) (hthi : totalTrips.val ≤ 10000000) :
    ∃ r : Std.I64,
      Aegis.MinimumTime.minimum_time time totalTrips = ok r ∧
      totalTrips.val ≤ tripCount time r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (time : Slice Std.I64) (totalTrips : Std.I64)
    (hne : 1 ≤ time.length) (hlen : time.length ≤ 100000)
    (hlo : ∀ i (hi : i < time.length), 1 ≤ (time.val[i]).val)
    (hhi : ∀ i (hi : i < time.length), (time.val[i]).val ≤ 10000000)
    (htlo : 1 ≤ totalTrips.val) (hthi : totalTrips.val ≤ 10000000), ∃ r : Std.I64,
      Aegis.MinimumTime.minimum_time time totalTrips = ok r ∧
      totalTrips.val ≤ tripCount time r.val) := by
  sorry

/-- The function returns a result r and for every integer T with 0 ≤ T < r, Σ_{i=0}^{len(time)-1} ⌊T / time[i]⌋ < totalTrips.
  Preconditions: Same as spec_1. -/
theorem spec_4 (time : Slice Std.I64) (totalTrips : Std.I64)
    (hne : 1 ≤ time.length) (hlen : time.length ≤ 100000)
    (hlo : ∀ i (hi : i < time.length), 1 ≤ (time.val[i]).val)
    (hhi : ∀ i (hi : i < time.length), (time.val[i]).val ≤ 10000000)
    (htlo : 1 ≤ totalTrips.val) (hthi : totalTrips.val ≤ 10000000) :
    ∃ r : Std.I64,
      Aegis.MinimumTime.minimum_time time totalTrips = ok r ∧
      ∀ T : Int, 0 ≤ T → T < r.val → tripCount time T < totalTrips.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (time : Slice Std.I64) (totalTrips : Std.I64)
    (hne : 1 ≤ time.length) (hlen : time.length ≤ 100000)
    (hlo : ∀ i (hi : i < time.length), 1 ≤ (time.val[i]).val)
    (hhi : ∀ i (hi : i < time.length), (time.val[i]).val ≤ 10000000)
    (htlo : 1 ≤ totalTrips.val) (hthi : totalTrips.val ≤ 10000000), ∃ r : Std.I64,
      Aegis.MinimumTime.minimum_time time totalTrips = ok r ∧
      ∀ T : Int, 0 ≤ T → T < r.val → tripCount time T < totalTrips.val) := by
  sorry

/-- The function returns a result r and r ≥ min_{0 ≤ i < len(time)} time[i] * ceil(totalTrips / len(time)), where ceil(a/b) = (a + b - 1) / b for positive integers a, b.
  Preconditions: Same as spec_1. -/
theorem spec_5 (time : Slice Std.I64) (totalTrips : Std.I64)
    (hne : 1 ≤ time.length) (hlen : time.length ≤ 100000)
    (hlo : ∀ i (hi : i < time.length), 1 ≤ (time.val[i]).val)
    (hhi : ∀ i (hi : i < time.length), (time.val[i]).val ≤ 10000000)
    (htlo : 1 ≤ totalTrips.val) (hthi : totalTrips.val ≤ 10000000) :
    ∃ r : Std.I64,
      Aegis.MinimumTime.minimum_time time totalTrips = ok r ∧
      minElem time * ceilDiv totalTrips.val (time.length : Int) ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (time : Slice Std.I64) (totalTrips : Std.I64)
    (hne : 1 ≤ time.length) (hlen : time.length ≤ 100000)
    (hlo : ∀ i (hi : i < time.length), 1 ≤ (time.val[i]).val)
    (hhi : ∀ i (hi : i < time.length), (time.val[i]).val ≤ 10000000)
    (htlo : 1 ≤ totalTrips.val) (hthi : totalTrips.val ≤ 10000000), ∃ r : Std.I64,
      Aegis.MinimumTime.minimum_time time totalTrips = ok r ∧
      minElem time * ceilDiv totalTrips.val (time.length : Int) ≤ r.val) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result (it does not fail, overflow, or panic).
  Preconditions: Same as spec_1. -/
theorem spec_6 (time : Slice Std.I64) (totalTrips : Std.I64)
    (hne : 1 ≤ time.length) (hlen : time.length ≤ 100000)
    (hlo : ∀ i (hi : i < time.length), 1 ≤ (time.val[i]).val)
    (hhi : ∀ i (hi : i < time.length), (time.val[i]).val ≤ 10000000)
    (htlo : 1 ≤ totalTrips.val) (hthi : totalTrips.val ≤ 10000000) :
    ∃ r : Std.I64, Aegis.MinimumTime.minimum_time time totalTrips = ok r := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (time : Slice Std.I64) (totalTrips : Std.I64)
    (hne : 1 ≤ time.length) (hlen : time.length ≤ 100000)
    (hlo : ∀ i (hi : i < time.length), 1 ≤ (time.val[i]).val)
    (hhi : ∀ i (hi : i < time.length), (time.val[i]).val ≤ 10000000)
    (htlo : 1 ≤ totalTrips.val) (hthi : totalTrips.val ≤ 10000000), ∃ r : Std.I64, Aegis.MinimumTime.minimum_time time totalTrips = ok r) := by
  sorry

/-- The function returns a result r and r = min_{0 ≤ i < len(time)} time[i].
  Preconditions: Same as spec_1, and additionally totalTrips = 1. -/
theorem spec_7 (time : Slice Std.I64) (totalTrips : Std.I64)
    (hne : 1 ≤ time.length) (hlen : time.length ≤ 100000)
    (hlo : ∀ i (hi : i < time.length), 1 ≤ (time.val[i]).val)
    (hhi : ∀ i (hi : i < time.length), (time.val[i]).val ≤ 10000000)
    (htlo : 1 ≤ totalTrips.val) (hthi : totalTrips.val ≤ 10000000)
    (htrips : totalTrips.val = 1) :
    ∃ r : Std.I64,
      Aegis.MinimumTime.minimum_time time totalTrips = ok r ∧
      r.val = minElem time := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (time : Slice Std.I64) (totalTrips : Std.I64)
    (hne : 1 ≤ time.length) (hlen : time.length ≤ 100000)
    (hlo : ∀ i (hi : i < time.length), 1 ≤ (time.val[i]).val)
    (hhi : ∀ i (hi : i < time.length), (time.val[i]).val ≤ 10000000)
    (htlo : 1 ≤ totalTrips.val) (hthi : totalTrips.val ≤ 10000000)
    (htrips : totalTrips.val = 1), ∃ r : Std.I64,
      Aegis.MinimumTime.minimum_time time totalTrips = ok r ∧
      r.val = minElem time) := by
  sorry

/-- Whenever the function returns results r1 and r2 for these inputs, r1 ≤ r2.
  Preconditions: Consider two inputs (time, totalTrips1) and (time, totalTrips2) both satisfying the constraints of spec_1, with the same array `time` and totalTrips1 ≤ totalTrips2. Let r1 and r2 be the results returned for these inputs. -/
theorem spec_8 (time : Slice Std.I64) (totalTrips1 totalTrips2 : Std.I64)
    (hne : 1 ≤ time.length) (hlen : time.length ≤ 100000)
    (hlo : ∀ i (hi : i < time.length), 1 ≤ (time.val[i]).val)
    (hhi : ∀ i (hi : i < time.length), (time.val[i]).val ≤ 10000000)
    (htlo1 : 1 ≤ totalTrips1.val) (hthi1 : totalTrips1.val ≤ 10000000)
    (htlo2 : 1 ≤ totalTrips2.val) (hthi2 : totalTrips2.val ≤ 10000000)
    (hmono : totalTrips1.val ≤ totalTrips2.val) :
    ∀ r1 r2 : Std.I64,
      Aegis.MinimumTime.minimum_time time totalTrips1 = ok r1 →
      Aegis.MinimumTime.minimum_time time totalTrips2 = ok r2 →
      r1.val ≤ r2.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (time : Slice Std.I64) (totalTrips1 totalTrips2 : Std.I64)
    (hne : 1 ≤ time.length) (hlen : time.length ≤ 100000)
    (hlo : ∀ i (hi : i < time.length), 1 ≤ (time.val[i]).val)
    (hhi : ∀ i (hi : i < time.length), (time.val[i]).val ≤ 10000000)
    (htlo1 : 1 ≤ totalTrips1.val) (hthi1 : totalTrips1.val ≤ 10000000)
    (htlo2 : 1 ≤ totalTrips2.val) (hthi2 : totalTrips2.val ≤ 10000000)
    (hmono : totalTrips1.val ≤ totalTrips2.val), ∀ r1 r2 : Std.I64,
      Aegis.MinimumTime.minimum_time time totalTrips1 = ok r1 →
      Aegis.MinimumTime.minimum_time time totalTrips2 = ok r2 →
      r1.val ≤ r2.val) := by
  sorry

/-- Whenever the function returns results r1 and r2 for these inputs, r1 = r2.
  Preconditions: Consider two inputs (time1, totalTrips) and (time2, totalTrips) both satisfying the constraints of spec_1, such that time2 is a permutation of time1 (i.e., len(time1) = len(time2) and there exists a bijection π on {0, ..., len(time1)-1} with time2[i] = time1[π(i)] for all i). Let r1 and r2 be the results returned for these inputs. -/
theorem spec_9 (time1 time2 : Slice Std.I64) (totalTrips : Std.I64)
    (hne1 : 1 ≤ time1.length) (hlen1 : time1.length ≤ 100000)
    (hlo1 : ∀ i (hi : i < time1.length), 1 ≤ (time1.val[i]).val)
    (hhi1 : ∀ i (hi : i < time1.length), (time1.val[i]).val ≤ 10000000)
    (hne2 : 1 ≤ time2.length) (hlen2 : time2.length ≤ 100000)
    (hlo2 : ∀ i (hi : i < time2.length), 1 ≤ (time2.val[i]).val)
    (hhi2 : ∀ i (hi : i < time2.length), (time2.val[i]).val ≤ 10000000)
    (htlo : 1 ≤ totalTrips.val) (hthi : totalTrips.val ≤ 10000000)
    (hperm : List.Perm time1.val time2.val) :
    ∀ r1 r2 : Std.I64,
      Aegis.MinimumTime.minimum_time time1 totalTrips = ok r1 →
      Aegis.MinimumTime.minimum_time time2 totalTrips = ok r2 →
      r1 = r2 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (time1 time2 : Slice Std.I64) (totalTrips : Std.I64)
    (hne1 : 1 ≤ time1.length) (hlen1 : time1.length ≤ 100000)
    (hlo1 : ∀ i (hi : i < time1.length), 1 ≤ (time1.val[i]).val)
    (hhi1 : ∀ i (hi : i < time1.length), (time1.val[i]).val ≤ 10000000)
    (hne2 : 1 ≤ time2.length) (hlen2 : time2.length ≤ 100000)
    (hlo2 : ∀ i (hi : i < time2.length), 1 ≤ (time2.val[i]).val)
    (hhi2 : ∀ i (hi : i < time2.length), (time2.val[i]).val ≤ 10000000)
    (htlo : 1 ≤ totalTrips.val) (hthi : totalTrips.val ≤ 10000000)
    (hperm : List.Perm time1.val time2.val), ∀ r1 r2 : Std.I64,
      Aegis.MinimumTime.minimum_time time1 totalTrips = ok r1 →
      Aegis.MinimumTime.minimum_time time2 totalTrips = ok r2 →
      r1 = r2) := by
  sorry

/-- Whenever the function returns results r1 and r2 for these inputs, r2 = c * r1.
  Preconditions: Consider two inputs (time1, totalTrips) and (time2, totalTrips) both satisfying the constraints of spec_1, and a positive integer c ≥ 1 such that len(time1) = len(time2) and time2[i] = c * time1[i] for every 0 ≤ i < len(time1). Let r1 and r2 be the results returned for these inputs. -/
theorem spec_10 (time1 time2 : Slice Std.I64) (totalTrips : Std.I64) (c : Int)
    (hne1 : 1 ≤ time1.length) (hlen1 : time1.length ≤ 100000)
    (hlo1 : ∀ i (hi : i < time1.length), 1 ≤ (time1.val[i]).val)
    (hhi1 : ∀ i (hi : i < time1.length), (time1.val[i]).val ≤ 10000000)
    (hne2 : 1 ≤ time2.length) (hlen2 : time2.length ≤ 100000)
    (hlo2 : ∀ i (hi : i < time2.length), 1 ≤ (time2.val[i]).val)
    (hhi2 : ∀ i (hi : i < time2.length), (time2.val[i]).val ≤ 10000000)
    (htlo : 1 ≤ totalTrips.val) (hthi : totalTrips.val ≤ 10000000)
    (hc : 1 ≤ c) (hlen : time1.length = time2.length)
    (hscale : ∀ i (hi : i < time1.length), (time2.val[i]).val = c * (time1.val[i]).val) :
    ∀ r1 r2 : Std.I64,
      Aegis.MinimumTime.minimum_time time1 totalTrips = ok r1 →
      Aegis.MinimumTime.minimum_time time2 totalTrips = ok r2 →
      r2.val = c * r1.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (time1 time2 : Slice Std.I64) (totalTrips : Std.I64) (c : Int)
    (hne1 : 1 ≤ time1.length) (hlen1 : time1.length ≤ 100000)
    (hlo1 : ∀ i (hi : i < time1.length), 1 ≤ (time1.val[i]).val)
    (hhi1 : ∀ i (hi : i < time1.length), (time1.val[i]).val ≤ 10000000)
    (hne2 : 1 ≤ time2.length) (hlen2 : time2.length ≤ 100000)
    (hlo2 : ∀ i (hi : i < time2.length), 1 ≤ (time2.val[i]).val)
    (hhi2 : ∀ i (hi : i < time2.length), (time2.val[i]).val ≤ 10000000)
    (htlo : 1 ≤ totalTrips.val) (hthi : totalTrips.val ≤ 10000000)
    (hc : 1 ≤ c) (hlen : time1.length = time2.length)
    (hscale : ∀ i (hi : i < time1.length), (time2.val[i]).val = c * (time1.val[i]).val), ∀ r1 r2 : Std.I64,
      Aegis.MinimumTime.minimum_time time1 totalTrips = ok r1 →
      Aegis.MinimumTime.minimum_time time2 totalTrips = ok r2 →
      r2.val = c * r1.val) := by
  sorry

/-- The function returns a result r and there exists an index i with 0 ≤ i < len(time) such that r mod time[i] = 0 (i.e., r is an integer multiple of time[i]).
  Preconditions: Same as spec_1. -/
theorem spec_11 (time : Slice Std.I64) (totalTrips : Std.I64)
    (hne : 1 ≤ time.length) (hlen : time.length ≤ 100000)
    (hlo : ∀ i (hi : i < time.length), 1 ≤ (time.val[i]).val)
    (hhi : ∀ i (hi : i < time.length), (time.val[i]).val ≤ 10000000)
    (htlo : 1 ≤ totalTrips.val) (hthi : totalTrips.val ≤ 10000000) :
    ∃ r : Std.I64,
      Aegis.MinimumTime.minimum_time time totalTrips = ok r ∧
      ∃ i, ∃ hi : i < time.length, r.val % (time.val[i]).val = 0 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (time : Slice Std.I64) (totalTrips : Std.I64)
    (hne : 1 ≤ time.length) (hlen : time.length ≤ 100000)
    (hlo : ∀ i (hi : i < time.length), 1 ≤ (time.val[i]).val)
    (hhi : ∀ i (hi : i < time.length), (time.val[i]).val ≤ 10000000)
    (htlo : 1 ≤ totalTrips.val) (hthi : totalTrips.val ≤ 10000000), ∃ r : Std.I64,
      Aegis.MinimumTime.minimum_time time totalTrips = ok r ∧
      ∃ i, ∃ hi : i < time.length, r.val % (time.val[i]).val = 0) := by
  sorry

/-- Whenever the function returns results r1 and r2 for these inputs, r2 ≤ r1.
  Preconditions: Consider two inputs (time1, totalTrips) and (time2, totalTrips) both satisfying the constraints of spec_1, where time2 is obtained by appending one extra positive integer t to time1: len(time2) = len(time1) + 1, time2[i] = time1[i] for 0 ≤ i < len(time1), and time2[len(time1)] = t with 1 ≤ t ≤ 10000000. Let r1 and r2 be the results returned for these inputs. -/
theorem spec_12 (time1 time2 : Slice Std.I64) (totalTrips : Std.I64)
    (t : Std.I64)
    (hne1 : 1 ≤ time1.length) (hlen1 : time1.length ≤ 100000)
    (hlo1 : ∀ i (hi : i < time1.length), 1 ≤ (time1.val[i]).val)
    (hhi1 : ∀ i (hi : i < time1.length), (time1.val[i]).val ≤ 10000000)
    (hne2 : 1 ≤ time2.length) (hlen2 : time2.length ≤ 100000)
    (hlo2 : ∀ i (hi : i < time2.length), 1 ≤ (time2.val[i]).val)
    (hhi2 : ∀ i (hi : i < time2.length), (time2.val[i]).val ≤ 10000000)
    (htlo : 1 ≤ totalTrips.val) (hthi : totalTrips.val ≤ 10000000)
    (htlo' : 1 ≤ t.val) (hthi' : t.val ≤ 10000000)
    (happend : time2.val = time1.val ++ [t]) :
    ∀ r1 r2 : Std.I64,
      Aegis.MinimumTime.minimum_time time1 totalTrips = ok r1 →
      Aegis.MinimumTime.minimum_time time2 totalTrips = ok r2 →
      r2.val ≤ r1.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (time1 time2 : Slice Std.I64) (totalTrips : Std.I64)
    (t : Std.I64)
    (hne1 : 1 ≤ time1.length) (hlen1 : time1.length ≤ 100000)
    (hlo1 : ∀ i (hi : i < time1.length), 1 ≤ (time1.val[i]).val)
    (hhi1 : ∀ i (hi : i < time1.length), (time1.val[i]).val ≤ 10000000)
    (hne2 : 1 ≤ time2.length) (hlen2 : time2.length ≤ 100000)
    (hlo2 : ∀ i (hi : i < time2.length), 1 ≤ (time2.val[i]).val)
    (hhi2 : ∀ i (hi : i < time2.length), (time2.val[i]).val ≤ 10000000)
    (htlo : 1 ≤ totalTrips.val) (hthi : totalTrips.val ≤ 10000000)
    (htlo' : 1 ≤ t.val) (hthi' : t.val ≤ 10000000)
    (happend : time2.val = time1.val ++ [t]), ∀ r1 r2 : Std.I64,
      Aegis.MinimumTime.minimum_time time1 totalTrips = ok r1 →
      Aegis.MinimumTime.minimum_time time2 totalTrips = ok r2 →
      r2.val ≤ r1.val) := by
  sorry

/-- The function returns a result r and r = t * ceil(totalTrips / len(time)), where ceil(a/b) = (a + b - 1) / b for positive integers a, b.
  Preconditions: Same as spec_1, and additionally there exists an integer t with 1 ≤ t ≤ 10000000 such that time[i] = t for every 0 ≤ i < len(time). -/
theorem spec_13 (time : Slice Std.I64) (totalTrips : Std.I64) (t : Std.I64)
    (hne : 1 ≤ time.length) (hlen : time.length ≤ 100000)
    (hlo : ∀ i (hi : i < time.length), 1 ≤ (time.val[i]).val)
    (hhi : ∀ i (hi : i < time.length), (time.val[i]).val ≤ 10000000)
    (htlo : 1 ≤ totalTrips.val) (hthi : totalTrips.val ≤ 10000000)
    (htlo' : 1 ≤ t.val) (hthi' : t.val ≤ 10000000)
    (hconst : ∀ i (hi : i < time.length), (time.val[i]).val = t.val) :
    ∃ r : Std.I64,
      Aegis.MinimumTime.minimum_time time totalTrips = ok r ∧
      r.val = t.val * ceilDiv totalTrips.val (time.length : Int) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (time : Slice Std.I64) (totalTrips : Std.I64) (t : Std.I64)
    (hne : 1 ≤ time.length) (hlen : time.length ≤ 100000)
    (hlo : ∀ i (hi : i < time.length), 1 ≤ (time.val[i]).val)
    (hhi : ∀ i (hi : i < time.length), (time.val[i]).val ≤ 10000000)
    (htlo : 1 ≤ totalTrips.val) (hthi : totalTrips.val ≤ 10000000)
    (htlo' : 1 ≤ t.val) (hthi' : t.val ≤ 10000000)
    (hconst : ∀ i (hi : i < time.length), (time.val[i]).val = t.val), ∃ r : Std.I64,
      Aegis.MinimumTime.minimum_time time totalTrips = ok r ∧
      r.val = t.val * ceilDiv totalTrips.val (time.length : Int)) := by
  sorry

end AegisSpec.MinimumTime
