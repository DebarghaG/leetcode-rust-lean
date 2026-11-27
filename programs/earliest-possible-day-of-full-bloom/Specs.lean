import Aegis.EarliestFullBloom.Code.Funs

/-!
# Specifications of `Aegis.EarliestFullBloom.earliest_full_bloom`

LeetCode problem `earliest-possible-day-of-full-bloom`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.EarliestFullBloom

namespace AegisSpec.EarliestFullBloom

def sumVals (l : List Std.I64) : ℤ := (l.map (fun x => x.val)).sum

def totalPlantTime (plantTime : Slice Std.I64) : ℤ := sumVals plantTime.val

def maxGrow (growTime : Slice Std.I64) : ℤ :=
  (growTime.val.map (fun x => x.val)).foldr max 0

def minGrow (growTime : Slice Std.I64) : ℤ :=
  (growTime.val.map (fun x => x.val)).foldr min 0

def countOcc (i : ℕ) : List ℕ → ℕ
  | [] => 0
  | b :: bs => (if b = i then 1 else 0) + countOcc i bs

def IsPlantingSchedule (plantTime : Slice Std.I64) (S : List ℕ) : Prop :=
  (S.length : ℤ) = totalPlantTime plantTime ∧
    (∀ d ∈ S, d < plantTime.val.length) ∧
      ∀ i : Fin plantTime.val.length, (countOcc i.val S : ℤ) = (plantTime.val.get i).val

def lastOccAux (i : ℕ) (d : ℕ) : List ℕ → Option ℕ
  | [] => none
  | b :: bs =>
    match lastOccAux i (d + 1) bs with
    | some e => some e
    | none => if b = i then some d else none

def lastOcc (i : ℕ) (S : List ℕ) : Option ℕ := lastOccAux i 0 S

def BloomsBy (growTime : Slice Std.I64) (S : List ℕ) (target : ℤ) : Prop :=
  ∀ (i : Fin growTime.val.length) (d : ℕ),
    lastOcc i.val S = some d → (d : ℤ) + 1 + (growTime.val.get i).val ≤ target

def plantedThrough (plantTime : Slice Std.I64)
    (σ : Equiv.Perm (Fin plantTime.val.length)) (k : ℕ)
    (hk : k ≤ plantTime.val.length) : ℤ :=
  ((List.finRange k).map (fun j => (plantTime.val.get (σ (Fin.castLE hk j))).val)).sum

def bloomOfOrder (plantTime growTime : Slice Std.I64)
    (hlen : plantTime.val.length = growTime.val.length)
    (σ : Equiv.Perm (Fin plantTime.val.length)) (k : Fin plantTime.val.length) : ℤ :=
  plantedThrough plantTime σ (k.val + 1) (by omega) +
    (growTime.val.get ⟨(σ k).val, by omega⟩).val

/-- Let T = sum_{i=0}^{n-1} plantTime[i]. A planting schedule is a sequence S of length T with entries in {0,...,n-1} such that for every i, the value i occurs exactly plantTime[i] times in S. For seed i, let last_i(S) be the largest index d with S[d] = i. Seed i is completely planted at the end of day last_i(S), so its bloom day is last_i(S)+1+growTime[i]. Define fullBloom(S) = max_{0<=i<n} (last_i(S)+1+growTime[i]). Under the preconditions, the function returns a result r and r = min { fullBloom(S) | S is a planting schedule }. (Idle days cannot improve the answer, so this minimum over no-idle schedules is exactly the earliest possible day all seeds are blooming.)
  Preconditions: Let n = len(plantTime) = len(growTime). Assume 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= plantTime[i] <= 10000 and 1 <= growTime[i] <= 10000. -/
theorem spec_1 (plantTime growTime : Slice Std.I64)
    (hlen : plantTime.val.length = growTime.val.length)
    (hn_pos : 1 ≤ plantTime.val.length)
    (hn_le : plantTime.val.length ≤ 100000)
    (hP : ∀ i : Fin plantTime.val.length,
      1 ≤ (plantTime.val.get i).val ∧ (plantTime.val.get i).val ≤ 10000)
    (hG : ∀ i : Fin growTime.val.length,
      1 ≤ (growTime.val.get i).val ∧ (growTime.val.get i).val ≤ 10000) :
    ∃ r : Std.I64,
      earliest_full_bloom plantTime growTime = ok r ∧
        (∃ S : List ℕ, IsPlantingSchedule plantTime S ∧ BloomsBy growTime S r.val) ∧
        (∀ (S : List ℕ) (target : ℤ),
          IsPlantingSchedule plantTime S → BloomsBy growTime S target → r.val ≤ target) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (plantTime growTime : Slice Std.I64)
    (hlen : plantTime.val.length = growTime.val.length)
    (hn_pos : 1 ≤ plantTime.val.length)
    (hn_le : plantTime.val.length ≤ 100000)
    (hP : ∀ i : Fin plantTime.val.length,
      1 ≤ (plantTime.val.get i).val ∧ (plantTime.val.get i).val ≤ 10000)
    (hG : ∀ i : Fin growTime.val.length,
      1 ≤ (growTime.val.get i).val ∧ (growTime.val.get i).val ≤ 10000), ∃ r : Std.I64,
      earliest_full_bloom plantTime growTime = ok r ∧
        (∃ S : List ℕ, IsPlantingSchedule plantTime S ∧ BloomsBy growTime S r.val) ∧
        (∀ (S : List ℕ) (target : ℤ),
          IsPlantingSchedule plantTime S → BloomsBy growTime S target → r.val ≤ target)) := by
  sorry

/-- Under the preconditions, the function returns some result r; it does not fail, panic, or overflow.
  Preconditions: Let n = len(plantTime) = len(growTime). Assume 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= plantTime[i] <= 10000 and 1 <= growTime[i] <= 10000. -/
theorem spec_2 (plantTime growTime : Slice Std.I64)
    (hlen : plantTime.val.length = growTime.val.length)
    (hn_pos : 1 ≤ plantTime.val.length)
    (hn_le : plantTime.val.length ≤ 100000)
    (hP : ∀ i : Fin plantTime.val.length,
      1 ≤ (plantTime.val.get i).val ∧ (plantTime.val.get i).val ≤ 10000)
    (hG : ∀ i : Fin growTime.val.length,
      1 ≤ (growTime.val.get i).val ∧ (growTime.val.get i).val ≤ 10000) :
    ∃ r : Std.I64, earliest_full_bloom plantTime growTime = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (plantTime growTime : Slice Std.I64)
    (hlen : plantTime.val.length = growTime.val.length)
    (hn_pos : 1 ≤ plantTime.val.length)
    (hn_le : plantTime.val.length ≤ 100000)
    (hP : ∀ i : Fin plantTime.val.length,
      1 ≤ (plantTime.val.get i).val ∧ (plantTime.val.get i).val ≤ 10000)
    (hG : ∀ i : Fin growTime.val.length,
      1 ≤ (growTime.val.get i).val ∧ (growTime.val.get i).val ≤ 10000), ∃ r : Std.I64, earliest_full_bloom plantTime growTime = ok r) := by
  sorry

/-- Whenever the function returns a result r under the preconditions, for every i with 0 <= i < n we have r >= plantTime[i] + growTime[i].
  Preconditions: Let n = len(plantTime) = len(growTime). Assume 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= plantTime[i] <= 10000 and 1 <= growTime[i] <= 10000. -/
theorem spec_3 (plantTime growTime : Slice Std.I64)
    (hlen : plantTime.val.length = growTime.val.length)
    (hn_pos : 1 ≤ plantTime.val.length)
    (hn_le : plantTime.val.length ≤ 100000)
    (hP : ∀ i : Fin plantTime.val.length,
      1 ≤ (plantTime.val.get i).val ∧ (plantTime.val.get i).val ≤ 10000)
    (hG : ∀ i : Fin growTime.val.length,
      1 ≤ (growTime.val.get i).val ∧ (growTime.val.get i).val ≤ 10000) :
    ∀ r : Std.I64, earliest_full_bloom plantTime growTime = ok r →
      ∀ i : Fin plantTime.val.length,
        r.val ≥ (plantTime.val.get i).val + (growTime.val.get ⟨i.val, by omega⟩).val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (plantTime growTime : Slice Std.I64)
    (hlen : plantTime.val.length = growTime.val.length)
    (hn_pos : 1 ≤ plantTime.val.length)
    (hn_le : plantTime.val.length ≤ 100000)
    (hP : ∀ i : Fin plantTime.val.length,
      1 ≤ (plantTime.val.get i).val ∧ (plantTime.val.get i).val ≤ 10000)
    (hG : ∀ i : Fin growTime.val.length,
      1 ≤ (growTime.val.get i).val ∧ (growTime.val.get i).val ≤ 10000), ∀ r : Std.I64, earliest_full_bloom plantTime growTime = ok r →
      ∀ i : Fin plantTime.val.length,
        r.val ≥ (plantTime.val.get i).val + (growTime.val.get ⟨i.val, by omega⟩).val) := by
  sorry

/-- Whenever the function returns a result r under the preconditions, with T = sum_{i=0}^{n-1} plantTime[i], we have r >= T + min_{0<=i<n} growTime[i].
  Preconditions: Let n = len(plantTime) = len(growTime). Assume 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= plantTime[i] <= 10000 and 1 <= growTime[i] <= 10000. -/
theorem spec_4 (plantTime growTime : Slice Std.I64)
    (hlen : plantTime.val.length = growTime.val.length)
    (hn_pos : 1 ≤ plantTime.val.length)
    (hn_le : plantTime.val.length ≤ 100000)
    (hP : ∀ i : Fin plantTime.val.length,
      1 ≤ (plantTime.val.get i).val ∧ (plantTime.val.get i).val ≤ 10000)
    (hG : ∀ i : Fin growTime.val.length,
      1 ≤ (growTime.val.get i).val ∧ (growTime.val.get i).val ≤ 10000) :
    ∀ r : Std.I64, earliest_full_bloom plantTime growTime = ok r →
      r.val ≥ totalPlantTime plantTime + minGrow growTime := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (plantTime growTime : Slice Std.I64)
    (hlen : plantTime.val.length = growTime.val.length)
    (hn_pos : 1 ≤ plantTime.val.length)
    (hn_le : plantTime.val.length ≤ 100000)
    (hP : ∀ i : Fin plantTime.val.length,
      1 ≤ (plantTime.val.get i).val ∧ (plantTime.val.get i).val ≤ 10000)
    (hG : ∀ i : Fin growTime.val.length,
      1 ≤ (growTime.val.get i).val ∧ (growTime.val.get i).val ≤ 10000), ∀ r : Std.I64, earliest_full_bloom plantTime growTime = ok r →
      r.val ≥ totalPlantTime plantTime + minGrow growTime) := by
  sorry

/-- Whenever the function returns a result r under the preconditions, with T = sum_{i=0}^{n-1} plantTime[i], we have r <= T + max_{0<=i<n} growTime[i].
  Preconditions: Let n = len(plantTime) = len(growTime). Assume 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= plantTime[i] <= 10000 and 1 <= growTime[i] <= 10000. -/
theorem spec_5 (plantTime growTime : Slice Std.I64)
    (hlen : plantTime.val.length = growTime.val.length)
    (hn_pos : 1 ≤ plantTime.val.length)
    (hn_le : plantTime.val.length ≤ 100000)
    (hP : ∀ i : Fin plantTime.val.length,
      1 ≤ (plantTime.val.get i).val ∧ (plantTime.val.get i).val ≤ 10000)
    (hG : ∀ i : Fin growTime.val.length,
      1 ≤ (growTime.val.get i).val ∧ (growTime.val.get i).val ≤ 10000) :
    ∀ r : Std.I64, earliest_full_bloom plantTime growTime = ok r →
      r.val ≤ totalPlantTime plantTime + maxGrow growTime := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (plantTime growTime : Slice Std.I64)
    (hlen : plantTime.val.length = growTime.val.length)
    (hn_pos : 1 ≤ plantTime.val.length)
    (hn_le : plantTime.val.length ≤ 100000)
    (hP : ∀ i : Fin plantTime.val.length,
      1 ≤ (plantTime.val.get i).val ∧ (plantTime.val.get i).val ≤ 10000)
    (hG : ∀ i : Fin growTime.val.length,
      1 ≤ (growTime.val.get i).val ∧ (growTime.val.get i).val ≤ 10000), ∀ r : Std.I64, earliest_full_bloom plantTime growTime = ok r →
      r.val ≤ totalPlantTime plantTime + maxGrow growTime) := by
  sorry

/-- Whenever the function returns r under the preconditions, there exists a planting schedule S of length T = sum_{i=0}^{n-1} plantTime[i], with each i occurring exactly plantTime[i] times, such that for every i, if last_i(S) is the last position of i in S, then last_i(S)+1+growTime[i] <= r. In other words, r is a day by which some valid planting plan has all seeds blooming.
  Preconditions: Let n = len(plantTime) = len(growTime). Assume 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= plantTime[i] <= 10000 and 1 <= growTime[i] <= 10000. -/
theorem spec_6 (plantTime growTime : Slice Std.I64)
    (hlen : plantTime.val.length = growTime.val.length)
    (hn_pos : 1 ≤ plantTime.val.length)
    (hn_le : plantTime.val.length ≤ 100000)
    (hP : ∀ i : Fin plantTime.val.length,
      1 ≤ (plantTime.val.get i).val ∧ (plantTime.val.get i).val ≤ 10000)
    (hG : ∀ i : Fin growTime.val.length,
      1 ≤ (growTime.val.get i).val ∧ (growTime.val.get i).val ≤ 10000) :
    ∀ r : Std.I64, earliest_full_bloom plantTime growTime = ok r →
      ∃ S : List ℕ, IsPlantingSchedule plantTime S ∧ BloomsBy growTime S r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (plantTime growTime : Slice Std.I64)
    (hlen : plantTime.val.length = growTime.val.length)
    (hn_pos : 1 ≤ plantTime.val.length)
    (hn_le : plantTime.val.length ≤ 100000)
    (hP : ∀ i : Fin plantTime.val.length,
      1 ≤ (plantTime.val.get i).val ∧ (plantTime.val.get i).val ≤ 10000)
    (hG : ∀ i : Fin growTime.val.length,
      1 ≤ (growTime.val.get i).val ∧ (growTime.val.get i).val ≤ 10000), ∀ r : Std.I64, earliest_full_bloom plantTime growTime = ok r →
      ∃ S : List ℕ, IsPlantingSchedule plantTime S ∧ BloomsBy growTime S r.val) := by
  sorry

/-- Whenever the preconditions hold and there is a constant c such that growTime[i] = c for every i with 0 <= i < n, if the function returns r then r = (sum_{i=0}^{n-1} plantTime[i]) + c.
  Preconditions: Let n = len(plantTime) = len(growTime). Assume 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= plantTime[i] <= 10000 and 1 <= growTime[i] <= 10000. -/
theorem spec_7 (plantTime growTime : Slice Std.I64) (c : ℤ)
    (hlen : plantTime.val.length = growTime.val.length)
    (hn_pos : 1 ≤ plantTime.val.length)
    (hn_le : plantTime.val.length ≤ 100000)
    (hP : ∀ i : Fin plantTime.val.length,
      1 ≤ (plantTime.val.get i).val ∧ (plantTime.val.get i).val ≤ 10000)
    (hG : ∀ i : Fin growTime.val.length,
      1 ≤ (growTime.val.get i).val ∧ (growTime.val.get i).val ≤ 10000)
    (hGc : ∀ i : Fin growTime.val.length, (growTime.val.get i).val = c) :
    ∀ r : Std.I64, earliest_full_bloom plantTime growTime = ok r →
      r.val = totalPlantTime plantTime + c := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (plantTime growTime : Slice Std.I64) (c : ℤ)
    (hlen : plantTime.val.length = growTime.val.length)
    (hn_pos : 1 ≤ plantTime.val.length)
    (hn_le : plantTime.val.length ≤ 100000)
    (hP : ∀ i : Fin plantTime.val.length,
      1 ≤ (plantTime.val.get i).val ∧ (plantTime.val.get i).val ≤ 10000)
    (hG : ∀ i : Fin growTime.val.length,
      1 ≤ (growTime.val.get i).val ∧ (growTime.val.get i).val ≤ 10000)
    (hGc : ∀ i : Fin growTime.val.length, (growTime.val.get i).val = c), ∀ r : Std.I64, earliest_full_bloom plantTime growTime = ok r →
      r.val = totalPlantTime plantTime + c) := by
  sorry

/-- If r is the result returned for (P,G) and r' is the result returned for (P',G'), then r' = r.
  Preconditions: Write P=plantTime and G=growTime. Let P,G satisfy the main preconditions with n=len(P). Let P',G' satisfy the same preconditions with the same n. Assume pi is a bijection on {0,...,n-1} such that P'[i]=P[pi(i)] and G'[i]=G[pi(i)] for all 0 <= i < n. -/
theorem spec_8 (plantTime growTime plantTime' growTime' : Slice Std.I64)
    (hlen : plantTime.val.length = growTime.val.length)
    (hn_pos : 1 ≤ plantTime.val.length)
    (hn_le : plantTime.val.length ≤ 100000)
    (hP : ∀ i : Fin plantTime.val.length,
      1 ≤ (plantTime.val.get i).val ∧ (plantTime.val.get i).val ≤ 10000)
    (hG : ∀ i : Fin growTime.val.length,
      1 ≤ (growTime.val.get i).val ∧ (growTime.val.get i).val ≤ 10000)
    (hlenP' : plantTime'.val.length = plantTime.val.length)
    (hlenG' : growTime'.val.length = growTime.val.length)
    (hP' : ∀ i : Fin plantTime'.val.length,
      1 ≤ (plantTime'.val.get i).val ∧ (plantTime'.val.get i).val ≤ 10000)
    (hG' : ∀ i : Fin growTime'.val.length,
      1 ≤ (growTime'.val.get i).val ∧ (growTime'.val.get i).val ≤ 10000)
    (π : Equiv.Perm (Fin plantTime.val.length))
    (hπP : ∀ i : Fin plantTime.val.length,
      (plantTime'.val.get ⟨i.val, by omega⟩).val = (plantTime.val.get (π i)).val)
    (hπG : ∀ i : Fin growTime.val.length,
      (growTime'.val.get ⟨i.val, by omega⟩).val =
        (growTime.val.get ⟨(π ⟨i.val, by omega⟩).val, by omega⟩).val) :
    ∀ (r r' : Std.I64),
      earliest_full_bloom plantTime growTime = ok r →
        earliest_full_bloom plantTime' growTime' = ok r' → r' = r := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (plantTime growTime plantTime' growTime' : Slice Std.I64)
    (hlen : plantTime.val.length = growTime.val.length)
    (hn_pos : 1 ≤ plantTime.val.length)
    (hn_le : plantTime.val.length ≤ 100000)
    (hP : ∀ i : Fin plantTime.val.length,
      1 ≤ (plantTime.val.get i).val ∧ (plantTime.val.get i).val ≤ 10000)
    (hG : ∀ i : Fin growTime.val.length,
      1 ≤ (growTime.val.get i).val ∧ (growTime.val.get i).val ≤ 10000)
    (hlenP' : plantTime'.val.length = plantTime.val.length)
    (hlenG' : growTime'.val.length = growTime.val.length)
    (hP' : ∀ i : Fin plantTime'.val.length,
      1 ≤ (plantTime'.val.get i).val ∧ (plantTime'.val.get i).val ≤ 10000)
    (hG' : ∀ i : Fin growTime'.val.length,
      1 ≤ (growTime'.val.get i).val ∧ (growTime'.val.get i).val ≤ 10000)
    (π : Equiv.Perm (Fin plantTime.val.length))
    (hπP : ∀ i : Fin plantTime.val.length,
      (plantTime'.val.get ⟨i.val, by omega⟩).val = (plantTime.val.get (π i)).val)
    (hπG : ∀ i : Fin growTime.val.length,
      (growTime'.val.get ⟨i.val, by omega⟩).val =
        (growTime.val.get ⟨(π ⟨i.val, by omega⟩).val, by omega⟩).val), ∀ (r r' : Std.I64),
      earliest_full_bloom plantTime growTime = ok r →
        earliest_full_bloom plantTime' growTime' = ok r' → r' = r) := by
  sorry

/-- If r is the result returned for (P,G) and r' is the result returned for (P,G'), then r' >= r.
  Preconditions: Write P=plantTime. Let P,G and P,G' both satisfy the main preconditions with the same n and the same P, and assume G'[i] >= G[i] for every 0 <= i < n. -/
theorem spec_9 (plantTime growTime growTime' : Slice Std.I64)
    (hlen : plantTime.val.length = growTime.val.length)
    (hn_pos : 1 ≤ plantTime.val.length)
    (hn_le : plantTime.val.length ≤ 100000)
    (hP : ∀ i : Fin plantTime.val.length,
      1 ≤ (plantTime.val.get i).val ∧ (plantTime.val.get i).val ≤ 10000)
    (hG : ∀ i : Fin growTime.val.length,
      1 ≤ (growTime.val.get i).val ∧ (growTime.val.get i).val ≤ 10000)
    (hlenG' : growTime'.val.length = growTime.val.length)
    (hG' : ∀ i : Fin growTime'.val.length,
      1 ≤ (growTime'.val.get i).val ∧ (growTime'.val.get i).val ≤ 10000)
    (hle : ∀ i : Fin growTime.val.length,
      (growTime.val.get i).val ≤ (growTime'.val.get ⟨i.val, by omega⟩).val) :
    ∀ (r r' : Std.I64),
      earliest_full_bloom plantTime growTime = ok r →
        earliest_full_bloom plantTime growTime' = ok r' → r.val ≤ r'.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (plantTime growTime growTime' : Slice Std.I64)
    (hlen : plantTime.val.length = growTime.val.length)
    (hn_pos : 1 ≤ plantTime.val.length)
    (hn_le : plantTime.val.length ≤ 100000)
    (hP : ∀ i : Fin plantTime.val.length,
      1 ≤ (plantTime.val.get i).val ∧ (plantTime.val.get i).val ≤ 10000)
    (hG : ∀ i : Fin growTime.val.length,
      1 ≤ (growTime.val.get i).val ∧ (growTime.val.get i).val ≤ 10000)
    (hlenG' : growTime'.val.length = growTime.val.length)
    (hG' : ∀ i : Fin growTime'.val.length,
      1 ≤ (growTime'.val.get i).val ∧ (growTime'.val.get i).val ≤ 10000)
    (hle : ∀ i : Fin growTime.val.length,
      (growTime.val.get i).val ≤ (growTime'.val.get ⟨i.val, by omega⟩).val), ∀ (r r' : Std.I64),
      earliest_full_bloom plantTime growTime = ok r →
        earliest_full_bloom plantTime growTime' = ok r' → r.val ≤ r'.val) := by
  sorry

/-- If r is the result returned for (P,G) and r' is the result returned for (P',G), then r' >= r.
  Preconditions: Write G=growTime. Let P,G and P',G both satisfy the main preconditions with the same n and the same G, and assume P'[i] >= P[i] for every 0 <= i < n. -/
theorem spec_10 (plantTime plantTime' growTime : Slice Std.I64)
    (hlen : plantTime.val.length = growTime.val.length)
    (hn_pos : 1 ≤ plantTime.val.length)
    (hn_le : plantTime.val.length ≤ 100000)
    (hP : ∀ i : Fin plantTime.val.length,
      1 ≤ (plantTime.val.get i).val ∧ (plantTime.val.get i).val ≤ 10000)
    (hG : ∀ i : Fin growTime.val.length,
      1 ≤ (growTime.val.get i).val ∧ (growTime.val.get i).val ≤ 10000)
    (hlenP' : plantTime'.val.length = plantTime.val.length)
    (hP' : ∀ i : Fin plantTime'.val.length,
      1 ≤ (plantTime'.val.get i).val ∧ (plantTime'.val.get i).val ≤ 10000)
    (hle : ∀ i : Fin plantTime.val.length,
      (plantTime.val.get i).val ≤ (plantTime'.val.get ⟨i.val, by omega⟩).val) :
    ∀ (r r' : Std.I64),
      earliest_full_bloom plantTime growTime = ok r →
        earliest_full_bloom plantTime' growTime = ok r' → r.val ≤ r'.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (plantTime plantTime' growTime : Slice Std.I64)
    (hlen : plantTime.val.length = growTime.val.length)
    (hn_pos : 1 ≤ plantTime.val.length)
    (hn_le : plantTime.val.length ≤ 100000)
    (hP : ∀ i : Fin plantTime.val.length,
      1 ≤ (plantTime.val.get i).val ∧ (plantTime.val.get i).val ≤ 10000)
    (hG : ∀ i : Fin growTime.val.length,
      1 ≤ (growTime.val.get i).val ∧ (growTime.val.get i).val ≤ 10000)
    (hlenP' : plantTime'.val.length = plantTime.val.length)
    (hP' : ∀ i : Fin plantTime'.val.length,
      1 ≤ (plantTime'.val.get i).val ∧ (plantTime'.val.get i).val ≤ 10000)
    (hle : ∀ i : Fin plantTime.val.length,
      (plantTime.val.get i).val ≤ (plantTime'.val.get ⟨i.val, by omega⟩).val), ∀ (r r' : Std.I64),
      earliest_full_bloom plantTime growTime = ok r →
        earliest_full_bloom plantTime' growTime = ok r' → r.val ≤ r'.val) := by
  sorry

/-- If r is the result returned for (P,G) and r' is the result returned for (P,G'), then r' = r + d.
  Preconditions: Write P=plantTime and G=growTime. Let P,G satisfy the main preconditions. Let d >= 0 be such that G'[i] = G[i] + d satisfies 1 <= G'[i] <= 10000 for every i, so P,G' also satisfies the main preconditions. -/
theorem spec_11 (plantTime growTime growTime' : Slice Std.I64) (d : ℤ)
    (hlen : plantTime.val.length = growTime.val.length)
    (hn_pos : 1 ≤ plantTime.val.length)
    (hn_le : plantTime.val.length ≤ 100000)
    (hP : ∀ i : Fin plantTime.val.length,
      1 ≤ (plantTime.val.get i).val ∧ (plantTime.val.get i).val ≤ 10000)
    (hG : ∀ i : Fin growTime.val.length,
      1 ≤ (growTime.val.get i).val ∧ (growTime.val.get i).val ≤ 10000)
    (hd : 0 ≤ d)
    (hlenG' : growTime'.val.length = growTime.val.length)
    (hshift : ∀ i : Fin growTime.val.length,
      (growTime'.val.get ⟨i.val, by omega⟩).val = (growTime.val.get i).val + d)
    (hG' : ∀ i : Fin growTime'.val.length,
      1 ≤ (growTime'.val.get i).val ∧ (growTime'.val.get i).val ≤ 10000) :
    ∀ (r r' : Std.I64),
      earliest_full_bloom plantTime growTime = ok r →
        earliest_full_bloom plantTime growTime' = ok r' → r'.val = r.val + d := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (plantTime growTime growTime' : Slice Std.I64) (d : ℤ)
    (hlen : plantTime.val.length = growTime.val.length)
    (hn_pos : 1 ≤ plantTime.val.length)
    (hn_le : plantTime.val.length ≤ 100000)
    (hP : ∀ i : Fin plantTime.val.length,
      1 ≤ (plantTime.val.get i).val ∧ (plantTime.val.get i).val ≤ 10000)
    (hG : ∀ i : Fin growTime.val.length,
      1 ≤ (growTime.val.get i).val ∧ (growTime.val.get i).val ≤ 10000)
    (hd : 0 ≤ d)
    (hlenG' : growTime'.val.length = growTime.val.length)
    (hshift : ∀ i : Fin growTime.val.length,
      (growTime'.val.get ⟨i.val, by omega⟩).val = (growTime.val.get i).val + d)
    (hG' : ∀ i : Fin growTime'.val.length,
      1 ≤ (growTime'.val.get i).val ∧ (growTime'.val.get i).val ≤ 10000), ∀ (r r' : Std.I64),
      earliest_full_bloom plantTime growTime = ok r →
        earliest_full_bloom plantTime growTime' = ok r' → r'.val = r.val + d) := by
  sorry

/-- Whenever the function returns r under the preconditions, r = min( max(plantTime[0]+growTime[0], plantTime[0]+plantTime[1]+growTime[1]), max(plantTime[1]+growTime[1], plantTime[0]+plantTime[1]+growTime[0]) ).
  Preconditions: Let n = len(plantTime) = len(growTime). Assume n = 2, and for i=0,1, 1 <= plantTime[i] <= 10000 and 1 <= growTime[i] <= 10000. -/
theorem spec_12 (plantTime growTime : Slice Std.I64)
    (hlen : plantTime.val.length = growTime.val.length)
    (hn : plantTime.val.length = 2)
    (hP : ∀ i : Fin plantTime.val.length,
      1 ≤ (plantTime.val.get i).val ∧ (plantTime.val.get i).val ≤ 10000)
    (hG : ∀ i : Fin growTime.val.length,
      1 ≤ (growTime.val.get i).val ∧ (growTime.val.get i).val ≤ 10000) :
    ∀ r : Std.I64, earliest_full_bloom plantTime growTime = ok r →
      r.val =
        min
          (max
            ((plantTime.val.get ⟨0, by omega⟩).val + (growTime.val.get ⟨0, by omega⟩).val)
            ((plantTime.val.get ⟨0, by omega⟩).val + (plantTime.val.get ⟨1, by omega⟩).val +
              (growTime.val.get ⟨1, by omega⟩).val))
          (max
            ((plantTime.val.get ⟨1, by omega⟩).val + (growTime.val.get ⟨1, by omega⟩).val)
            ((plantTime.val.get ⟨0, by omega⟩).val + (plantTime.val.get ⟨1, by omega⟩).val +
              (growTime.val.get ⟨0, by omega⟩).val)) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (plantTime growTime : Slice Std.I64)
    (hlen : plantTime.val.length = growTime.val.length)
    (hn : plantTime.val.length = 2)
    (hP : ∀ i : Fin plantTime.val.length,
      1 ≤ (plantTime.val.get i).val ∧ (plantTime.val.get i).val ≤ 10000)
    (hG : ∀ i : Fin growTime.val.length,
      1 ≤ (growTime.val.get i).val ∧ (growTime.val.get i).val ≤ 10000), ∀ r : Std.I64, earliest_full_bloom plantTime growTime = ok r →
      r.val =
        min
          (max
            ((plantTime.val.get ⟨0, by omega⟩).val + (growTime.val.get ⟨0, by omega⟩).val)
            ((plantTime.val.get ⟨0, by omega⟩).val + (plantTime.val.get ⟨1, by omega⟩).val +
              (growTime.val.get ⟨1, by omega⟩).val))
          (max
            ((plantTime.val.get ⟨1, by omega⟩).val + (growTime.val.get ⟨1, by omega⟩).val)
            ((plantTime.val.get ⟨0, by omega⟩).val + (plantTime.val.get ⟨1, by omega⟩).val +
              (growTime.val.get ⟨0, by omega⟩).val))) := by
  sorry

/-- Under these preconditions, the returned result r equals max_{0 <= k < n} ( (sum_{j=0}^{k} plantTime[sigma(j)]) + growTime[sigma(k)] ).
  Preconditions: Let n = len(plantTime) = len(growTime). Assume 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= plantTime[i] <= 10000 and 1 <= growTime[i] <= 10000. Let sigma be any permutation of {0,...,n-1} such that growTime[sigma(0)] >= growTime[sigma(1)] >= ... >= growTime[sigma(n-1)]. -/
theorem spec_13 (plantTime growTime : Slice Std.I64)
    (hlen : plantTime.val.length = growTime.val.length)
    (hn_pos : 1 ≤ plantTime.val.length)
    (hn_le : plantTime.val.length ≤ 100000)
    (hP : ∀ i : Fin plantTime.val.length,
      1 ≤ (plantTime.val.get i).val ∧ (plantTime.val.get i).val ≤ 10000)
    (hG : ∀ i : Fin growTime.val.length,
      1 ≤ (growTime.val.get i).val ∧ (growTime.val.get i).val ≤ 10000)
    (σ : Equiv.Perm (Fin plantTime.val.length))
    (hσ : ∀ (i j : Fin plantTime.val.length), i.val ≤ j.val →
      (growTime.val.get ⟨(σ j).val, by omega⟩).val ≤
        (growTime.val.get ⟨(σ i).val, by omega⟩).val) :
    ∀ r : Std.I64, earliest_full_bloom plantTime growTime = ok r →
      (∀ k : Fin plantTime.val.length, bloomOfOrder plantTime growTime hlen σ k ≤ r.val) ∧
        (∃ k : Fin plantTime.val.length,
          r.val = bloomOfOrder plantTime growTime hlen σ k) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (plantTime growTime : Slice Std.I64)
    (hlen : plantTime.val.length = growTime.val.length)
    (hn_pos : 1 ≤ plantTime.val.length)
    (hn_le : plantTime.val.length ≤ 100000)
    (hP : ∀ i : Fin plantTime.val.length,
      1 ≤ (plantTime.val.get i).val ∧ (plantTime.val.get i).val ≤ 10000)
    (hG : ∀ i : Fin growTime.val.length,
      1 ≤ (growTime.val.get i).val ∧ (growTime.val.get i).val ≤ 10000)
    (σ : Equiv.Perm (Fin plantTime.val.length))
    (hσ : ∀ (i j : Fin plantTime.val.length), i.val ≤ j.val →
      (growTime.val.get ⟨(σ j).val, by omega⟩).val ≤
        (growTime.val.get ⟨(σ i).val, by omega⟩).val), ∀ r : Std.I64, earliest_full_bloom plantTime growTime = ok r →
      (∀ k : Fin plantTime.val.length, bloomOfOrder plantTime growTime hlen σ k ≤ r.val) ∧
        (∃ k : Fin plantTime.val.length,
          r.val = bloomOfOrder plantTime growTime hlen σ k)) := by
  sorry

end AegisSpec.EarliestFullBloom
