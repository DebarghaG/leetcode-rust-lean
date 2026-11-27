import Aegis.MaximumTotalDamage.Code.Funs

/-!
# Specifications of `Aegis.MaximumTotalDamage.maximum_total_damage`

LeetCode problem `maximum-total-damage-with-spell-casting`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaximumTotalDamage

open Aegis.MaximumTotalDamage

def content (power : Slice Std.I64) : List Int := power.val.map (fun x => x.val)

def Compatible (a b : Int) : Prop := a = b ∨ 3 ≤ (a - b).natAbs

def IsLegal (power : List Int) (T : Finset Nat) : Prop :=
  (∀ i ∈ T, i < power.length) ∧
    ∀ i ∈ T, ∀ j ∈ T, i ≠ j → Compatible power[i]! power[j]!

def totalDamage (power : List Int) (T : Finset Nat) : Int :=
  T.sum (fun i => power[i]!)

def legalSums (power : List Int) : Set Int :=
  {s | ∃ T : Finset Nat, IsLegal power T ∧ totalDamage power T = s}

def countOcc (power : List Int) (v : Int) : Nat :=
  (power.filter (fun x => x = v)).length

def ClosedUnderEqual (power : List Int) (T : Finset Nat) : Prop :=
  ∀ i ∈ T, ∀ j, j < power.length → power[j]! = power[i]! → j ∈ T

def InclusionMaximal (power : List Int) (T : Finset Nat) : Prop :=
  ∀ k, k < power.length → k ∉ T → ¬ IsLegal power (insert k T)

def SpreadAtMost (power : List Int) (d : Int) : Prop :=
  ∀ x ∈ power, ∀ y ∈ power, x ≤ y + d

def histMax (power : List Int) : Int :=
  (power.eraseDups.map (fun v => (countOcc power v : Int) * v)).foldr max 0

def IsPerm (power q : List Int) : Prop :=
  ∀ v : Int, countOcc power v = countOcc q v

def AppendValue (l : List Int) (v : Int) : List Int := l ++ [v]

def RemoveValue (l : List Int) (v : Int) : List Int := l.filter (fun x => x ≠ v)

/-- The function returns a result r and r = max { sum_{i in T} power[i] | T is a subset of {0,...,len(power)-1} and for all distinct i,j in T, either power[i] = power[j] or |power[i] - power[j]| >= 3 }. Equivalently, a legal cast set is any set of spell indices T in which two chosen spells with different damage values must have damage values differing by at least 3, while any number of spells with the same damage value may be chosen together; r is the largest possible sum of power[i] over a legal cast set T. The maximum is taken over all legal T; no particular optimal T is required.
  Preconditions: len(power) is between 1 and 100000 inclusive, and for every i with 0 <= i < len(power), 1 <= power[i] <= 1000000000. -/
theorem spec_1 (power : Slice Std.I64)
    (hlen : 1 ≤ power.val.length)
    (hlen' : power.val.length ≤ 100000)
    (hbound : ∀ x ∈ power.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
    ∃ r, maximum_total_damage power = ok r ∧
      IsGreatest (legalSums (content power)) r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (power : Slice Std.I64)
    (hlen : 1 ≤ power.val.length)
    (hlen' : power.val.length ≤ 100000)
    (hbound : ∀ x ∈ power.val, 1 ≤ x.val ∧ x.val ≤ 1000000000), ∃ r, maximum_total_damage power = ok r ∧
      IsGreatest (legalSums (content power)) r.val) := by
  sorry

/-- The function returns a result r and there exists a subset T of {0,...,len(power)-1} such that sum_{i in T} power[i] = r and, for all distinct i,j in T, either power[i] = power[j] or |power[i] - power[j]| >= 3.
  Preconditions: len(power) is between 1 and 100000 inclusive, and for every i with 0 <= i < len(power), 1 <= power[i] <= 1000000000. -/
theorem spec_2 (power : Slice Std.I64)
    (hlen : 1 ≤ power.val.length)
    (hlen' : power.val.length ≤ 100000)
    (hbound : ∀ x ∈ power.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
    ∃ r, maximum_total_damage power = ok r ∧
      ∃ T : Finset Nat, IsLegal (content power) T ∧
        totalDamage (content power) T = r.val := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (power : Slice Std.I64)
    (hlen : 1 ≤ power.val.length)
    (hlen' : power.val.length ≤ 100000)
    (hbound : ∀ x ∈ power.val, 1 ≤ x.val ∧ x.val ≤ 1000000000), ∃ r, maximum_total_damage power = ok r ∧
      ∃ T : Finset Nat, IsLegal (content power) T ∧
        totalDamage (content power) T = r.val) := by
  sorry

/-- Whenever the function returns a result r, for every subset T of {0,...,len(power)-1} such that for all distinct i,j in T either power[i] = power[j] or |power[i] - power[j]| >= 3, we have sum_{i in T} power[i] <= r.
  Preconditions: len(power) is between 1 and 100000 inclusive, and for every i with 0 <= i < len(power), 1 <= power[i] <= 1000000000. -/
theorem spec_3 (power : Slice Std.I64)
    (hlen : 1 ≤ power.val.length)
    (hlen' : power.val.length ≤ 100000)
    (hbound : ∀ x ∈ power.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
    ∀ r, maximum_total_damage power = ok r →
      ∀ T : Finset Nat, IsLegal (content power) T →
        totalDamage (content power) T ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (power : Slice Std.I64)
    (hlen : 1 ≤ power.val.length)
    (hlen' : power.val.length ≤ 100000)
    (hbound : ∀ x ∈ power.val, 1 ≤ x.val ∧ x.val ≤ 1000000000), ∀ r, maximum_total_damage power = ok r →
      ∀ T : Finset Nat, IsLegal (content power) T →
        totalDamage (content power) T ≤ r.val) := by
  sorry

/-- The function returns a result r and there exists a subset T of {0,...,len(power)-1} such that sum_{i in T} power[i] = r, T is legal (for all distinct i,j in T, either power[i] = power[j] or |power[i] - power[j]| >= 3), and T is closed under equal damage values: for every i in T and every j with 0 <= j < len(power), if power[j] = power[i] then j is in T.
  Preconditions: len(power) is between 1 and 100000 inclusive, and for every i with 0 <= i < len(power), 1 <= power[i] <= 1000000000. -/
theorem spec_4 (power : Slice Std.I64)
    (hlen : 1 ≤ power.val.length)
    (hlen' : power.val.length ≤ 100000)
    (hbound : ∀ x ∈ power.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
    ∃ r, maximum_total_damage power = ok r ∧
      ∃ T : Finset Nat, IsLegal (content power) T ∧
        totalDamage (content power) T = r.val ∧
        ClosedUnderEqual (content power) T := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (power : Slice Std.I64)
    (hlen : 1 ≤ power.val.length)
    (hlen' : power.val.length ≤ 100000)
    (hbound : ∀ x ∈ power.val, 1 ≤ x.val ∧ x.val ≤ 1000000000), ∃ r, maximum_total_damage power = ok r ∧
      ∃ T : Finset Nat, IsLegal (content power) T ∧
        totalDamage (content power) T = r.val ∧
        ClosedUnderEqual (content power) T) := by
  sorry

/-- Whenever the function returns a result r, every legal subset T of {0,...,len(power)-1} with sum_{i in T} power[i] = r is inclusion-maximal among legal subsets: there is no index k with 0 <= k < len(power) and k not in T such that T union {k} is legal. Here legal means that for all distinct i,j in T, either power[i] = power[j] or |power[i] - power[j]| >= 3.
  Preconditions: len(power) is between 1 and 100000 inclusive, and for every i with 0 <= i < len(power), 1 <= power[i] <= 1000000000. -/
theorem spec_5 (power : Slice Std.I64)
    (hlen : 1 ≤ power.val.length)
    (hlen' : power.val.length ≤ 100000)
    (hbound : ∀ x ∈ power.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
    ∀ r, maximum_total_damage power = ok r →
      ∀ T : Finset Nat, IsLegal (content power) T →
        totalDamage (content power) T = r.val →
          InclusionMaximal (content power) T := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (power : Slice Std.I64)
    (hlen : 1 ≤ power.val.length)
    (hlen' : power.val.length ≤ 100000)
    (hbound : ∀ x ∈ power.val, 1 ≤ x.val ∧ x.val ≤ 1000000000), ∀ r, maximum_total_damage power = ok r →
      ∀ T : Finset Nat, IsLegal (content power) T →
        totalDamage (content power) T = r.val →
          InclusionMaximal (content power) T) := by
  sorry

/-- The function returns a result r and r = max { c_v * v | v is an integer that occurs in power }, where c_v is the number of indices i with 0 <= i < len(power) and power[i] = v.
  Preconditions: len(power) is between 1 and 100000 inclusive, every power[i] is between 1 and 1000000000 inclusive, and max_{0 <= i < len(power)} power[i] - min_{0 <= i < len(power)} power[i] <= 2. -/
theorem spec_6 (power : Slice Std.I64)
    (hlen : 1 ≤ power.val.length)
    (hlen' : power.val.length ≤ 100000)
    (hbound : ∀ x ∈ power.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
    (hspread : SpreadAtMost (content power) 2) :
    ∃ r, maximum_total_damage power = ok r ∧
      r.val = histMax (content power) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (power : Slice Std.I64)
    (hlen : 1 ≤ power.val.length)
    (hlen' : power.val.length ≤ 100000)
    (hbound : ∀ x ∈ power.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
    (hspread : SpreadAtMost (content power) 2), ∃ r, maximum_total_damage power = ok r ∧
      r.val = histMax (content power)) := by
  sorry

/-- The function returns a result r and r = sum_{i=0}^{len(power)-1} power[i].
  Preconditions: len(power) is between 1 and 100000 inclusive, every power[i] is between 1 and 1000000000 inclusive, and for every i,j with 0 <= i < len(power) and 0 <= j < len(power), if i != j and power[i] != power[j], then |power[i] - power[j]| >= 3. -/
theorem spec_7 (power : Slice Std.I64)
    (hlen : 1 ≤ power.val.length)
    (hlen' : power.val.length ≤ 100000)
    (hbound : ∀ x ∈ power.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
    (hsep : ∀ x ∈ content power, ∀ y ∈ content power,
      x ≠ y → 3 ≤ (x - y).natAbs) :
    ∃ r, maximum_total_damage power = ok r ∧
      r.val = (content power).sum := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (power : Slice Std.I64)
    (hlen : 1 ≤ power.val.length)
    (hlen' : power.val.length ≤ 100000)
    (hbound : ∀ x ∈ power.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
    (hsep : ∀ x ∈ content power, ∀ y ∈ content power,
      x ≠ y → 3 ≤ (x - y).natAbs), ∃ r, maximum_total_damage power = ok r ∧
      r.val = (content power).sum) := by
  sorry

/-- The function returns a result r for input power; for every slice q satisfying the preconditions, the function returns a result s for input q and r = s.
  Preconditions: power and q are slices of i64 with len(power) = len(q) between 1 and 100000 inclusive, every entry of power and of q is between 1 and 1000000000 inclusive, and q is a permutation of power: for every integer v, the number of indices i with q[i] = v equals the number of indices i with power[i] = v. -/
theorem spec_8 (power q : Slice Std.I64)
    (hlen : 1 ≤ power.val.length)
    (hlen' : power.val.length ≤ 100000)
    (hqlen : q.val.length = power.val.length)
    (hbound : ∀ x ∈ power.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
    (hqbound : ∀ x ∈ q.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
    (hperm : IsPerm (content power) (content q)) :
    ∃ r, maximum_total_damage power = ok r ∧
      ∃ s, maximum_total_damage q = ok s ∧ r.val = s.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (power q : Slice Std.I64)
    (hlen : 1 ≤ power.val.length)
    (hlen' : power.val.length ≤ 100000)
    (hqlen : q.val.length = power.val.length)
    (hbound : ∀ x ∈ power.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
    (hqbound : ∀ x ∈ q.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
    (hperm : IsPerm (content power) (content q)), ∃ r, maximum_total_damage power = ok r ∧
      ∃ s, maximum_total_damage q = ok s ∧ r.val = s.val) := by
  sorry

/-- The function returns a result r on input power and a result r' on input power'; then r' = r + v.
  Preconditions: power is a slice of i64 with 1 <= len(power) <= 99999, every power[i] is between 1 and 1000000000 inclusive, v is an integer with 1 <= v <= 1000000000, for every i with 0 <= i < len(power), |power[i] - v| >= 3, and power' is the slice of length len(power)+1 such that power'[i] = power[i] for 0 <= i < len(power) and power'[len(power)] = v. -/
theorem spec_9 (power power' : Slice Std.I64) (v : Int)
    (hlen : 1 ≤ power.val.length)
    (hlen' : power.val.length ≤ 99999)
    (hbound : ∀ x ∈ power.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
    (hvlow : 1 ≤ v)
    (hvhigh : v ≤ 1000000000)
    (hsep : ∀ x ∈ content power, 3 ≤ (x - v).natAbs)
    (happ : content power' = AppendValue (content power) v) :
    ∃ r, maximum_total_damage power = ok r ∧
      ∃ r', maximum_total_damage power' = ok r' ∧ r'.val = r.val + v := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (power power' : Slice Std.I64) (v : Int)
    (hlen : 1 ≤ power.val.length)
    (hlen' : power.val.length ≤ 99999)
    (hbound : ∀ x ∈ power.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
    (hvlow : 1 ≤ v)
    (hvhigh : v ≤ 1000000000)
    (hsep : ∀ x ∈ content power, 3 ≤ (x - v).natAbs)
    (happ : content power' = AppendValue (content power) v), ∃ r, maximum_total_damage power = ok r ∧
      ∃ r', maximum_total_damage power' = ok r' ∧ r'.val = r.val + v) := by
  sorry

/-- The function returns a result r on input power and a result r0 on input power0; if c_v is the number of indices i with 0 <= i < len(power) and power[i] = v, then r = r0 + c_v * v.
  Preconditions: power is a slice of i64 with 2 <= len(power) <= 100000, every power[i] is between 1 and 1000000000 inclusive, v is an integer that occurs in power, for every i with 0 <= i < len(power) and power[i] != v, |power[i] - v| >= 3, and power0 is the slice obtained from power by deleting all entries equal to v (so 1 <= len(power0) < len(power)). -/
theorem spec_10 (power power0 : Slice Std.I64) (v : Int)
    (hlen : 2 ≤ power.val.length)
    (hlen' : power.val.length ≤ 100000)
    (hbound : ∀ x ∈ power.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
    (hocc : v ∈ content power)
    (hsep : ∀ x ∈ content power, x ≠ v → 3 ≤ (x - v).natAbs)
    (hdel : content power0 = RemoveValue (content power) v)
    (h0low : 1 ≤ power0.val.length)
    (h0high : power0.val.length < power.val.length) :
    ∃ r, maximum_total_damage power = ok r ∧
      ∃ r0, maximum_total_damage power0 = ok r0 ∧
        r.val = r0.val + (countOcc (content power) v : Int) * v := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (power power0 : Slice Std.I64) (v : Int)
    (hlen : 2 ≤ power.val.length)
    (hlen' : power.val.length ≤ 100000)
    (hbound : ∀ x ∈ power.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
    (hocc : v ∈ content power)
    (hsep : ∀ x ∈ content power, x ≠ v → 3 ≤ (x - v).natAbs)
    (hdel : content power0 = RemoveValue (content power) v)
    (h0low : 1 ≤ power0.val.length)
    (h0high : power0.val.length < power.val.length), ∃ r, maximum_total_damage power = ok r ∧
      ∃ r0, maximum_total_damage power0 = ok r0 ∧
        r.val = r0.val + (countOcc (content power) v : Int) * v) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r (it does not fail); in particular, no arithmetic overflow and no out-of-bounds access occurs.
  Preconditions: len(power) is between 1 and 100000 inclusive, and for every i with 0 <= i < len(power), 1 <= power[i] <= 1000000000. -/
theorem spec_11 (power : Slice Std.I64)
    (hlen : 1 ≤ power.val.length)
    (hlen' : power.val.length ≤ 100000)
    (hbound : ∀ x ∈ power.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
    ∃ r, maximum_total_damage power = ok r := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (power : Slice Std.I64)
    (hlen : 1 ≤ power.val.length)
    (hlen' : power.val.length ≤ 100000)
    (hbound : ∀ x ∈ power.val, 1 ≤ x.val ∧ x.val ≤ 1000000000), ∃ r, maximum_total_damage power = ok r) := by
  sorry

end AegisSpec.MaximumTotalDamage
