import Aegis.DividePlayers.Code.Funs

/-!
# Specifications of `Aegis.DividePlayers.divide_players`

LeetCode problem `divide-players-into-teams-of-equal-skill`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.DividePlayers

namespace AegisSpec.DividePlayers

def skillVals (skill : Slice Std.I64) : List Int := skill.val.map (fun x => x.val)

def skillEntry (skill : Slice Std.I64) (i : Nat) : Int :=
  ((skill.val[i]?).map (fun x => x.val)).getD 0

def countOcc (l : List Int) (v : Int) : Nat := (l.filter (fun x => decide (x = v))).length

def totalSkill (l : List Int) : Int := l.sum

def totalSkillSq (l : List Int) : Int := (l.map (fun x => x * x)).sum

def IsSortedVersion (l a : List Int) : Prop := a.Perm l ∧ a.Pairwise (· ≤ ·)

def outerPairSumsEq (a : List Int) (n : Nat) (S : Int) : Prop :=
  ∀ i, i < n / 2 → a.getD i 0 + a.getD (n - 1 - i) 0 = S

def outerPairProductSum (a : List Int) (n : Nat) : Int :=
  (List.zipWith (fun x y => x * y) (a.take (n / 2)) (a.reverse.take (n / 2))).sum

def IsValidPairingWithSum (l : List Int) (P : List (Nat × Nat)) (S : Int) : Prop :=
  P.Nodup ∧
  (∀ p ∈ P, p.1 < p.2 ∧ p.2 < l.length) ∧
  (∀ i, i < l.length → ∃! p, p ∈ P ∧ (p.1 = i ∨ p.2 = i)) ∧
  (∀ p ∈ P, l.getD p.1 0 + l.getD p.2 0 = S)

def IsValidPairing (l : List Int) (P : List (Nat × Nat)) : Prop :=
  ∃ S, IsValidPairingWithSum l P S

def HasValidPairing (l : List Int) : Prop := ∃ P, IsValidPairing l P

def pairingProductSum (l : List Int) (P : List (Nat × Nat)) : Int :=
  (P.map (fun p => l.getD p.1 0 * l.getD p.2 0)).sum

/-- Let n = len(skill). A valid equal-sum pairing of skill is a set P of n/2 unordered pairs {i,j}, with 0 <= i < j < n, such that every index i with 0 <= i < n occurs in exactly one pair of P and there exists an integer S with skill[i] + skill[j] = S for every {i,j} in P. The function returns a result r and: if a valid equal-sum pairing exists, then r = sum over {i,j} in P of skill[i] * skill[j] for every valid equal-sum pairing P, and this value is independent of P; if no valid equal-sum pairing exists, then r = -1.
  Preconditions: Let n = len(skill). n is even, 2 <= n <= 100000, and for every i with 0 <= i < n, 1 <= skill[i] <= 1000. -/
theorem spec_1 (skill : Slice Std.I64)
    (h_even : skill.val.length % 2 = 0)
    (h_ge : 2 ≤ skill.val.length)
    (h_le : skill.val.length ≤ 100000)
    (h_bounds : ∀ i, i < skill.val.length → 1 ≤ skillEntry skill i ∧ skillEntry skill i ≤ 1000) :
    ∃ r, divide_players skill = ok r ∧
      (HasValidPairing (skillVals skill) →
        ∀ P, IsValidPairing (skillVals skill) P → r.val = pairingProductSum (skillVals skill) P) ∧
      (¬ HasValidPairing (skillVals skill) → r.val = -1) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (skill : Slice Std.I64)
    (h_even : skill.val.length % 2 = 0)
    (h_ge : 2 ≤ skill.val.length)
    (h_le : skill.val.length ≤ 100000)
    (h_bounds : ∀ i, i < skill.val.length → 1 ≤ skillEntry skill i ∧ skillEntry skill i ≤ 1000), ∃ r, divide_players skill = ok r ∧
      (HasValidPairing (skillVals skill) →
        ∀ P, IsValidPairing (skillVals skill) P → r.val = pairingProductSum (skillVals skill) P) ∧
      (¬ HasValidPairing (skillVals skill) → r.val = -1)) := by
  sorry

/-- The function returns a result r; it does not fail (no panic, out-of-bounds access, or arithmetic overflow) on any input satisfying the preconditions.
  Preconditions: Let n = len(skill). n is even, 2 <= n <= 100000, and for every i with 0 <= i < n, 1 <= skill[i] <= 1000. -/
theorem spec_2 (skill : Slice Std.I64)
    (h_even : skill.val.length % 2 = 0)
    (h_ge : 2 ≤ skill.val.length)
    (h_le : skill.val.length ≤ 100000)
    (h_bounds : ∀ i, i < skill.val.length → 1 ≤ skillEntry skill i ∧ skillEntry skill i ≤ 1000) :
    ∃ r, divide_players skill = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (skill : Slice Std.I64)
    (h_even : skill.val.length % 2 = 0)
    (h_ge : 2 ≤ skill.val.length)
    (h_le : skill.val.length ≤ 100000)
    (h_bounds : ∀ i, i < skill.val.length → 1 ≤ skillEntry skill i ∧ skillEntry skill i ≤ 1000), ∃ r, divide_players skill = ok r) := by
  sorry

/-- Whenever divide_players(skill) returns a result r with r != -1, r <= (len(skill) / 2) * 1_000_000.
  Preconditions: Let n = len(skill). n is even, 2 <= n <= 100000, and for every i with 0 <= i < n, 1 <= skill[i] <= 1000. -/
theorem spec_3 (skill : Slice Std.I64)
    (h_even : skill.val.length % 2 = 0)
    (h_ge : 2 ≤ skill.val.length)
    (h_le : skill.val.length ≤ 100000)
    (h_bounds : ∀ i, i < skill.val.length → 1 ≤ skillEntry skill i ∧ skillEntry skill i ≤ 1000) :
    ∀ r, divide_players skill = ok r → r.val ≠ -1 →
      r.val ≤ ((skill.val.length / 2 : Nat) : Int) * 1000000 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (skill : Slice Std.I64)
    (h_even : skill.val.length % 2 = 0)
    (h_ge : 2 ≤ skill.val.length)
    (h_le : skill.val.length ≤ 100000)
    (h_bounds : ∀ i, i < skill.val.length → 1 ≤ skillEntry skill i ∧ skillEntry skill i ≤ 1000), ∀ r, divide_players skill = ok r → r.val ≠ -1 →
      r.val ≤ ((skill.val.length / 2 : Nat) : Int) * 1000000) := by
  sorry

/-- Whenever divide_players(skill) returns a result r with r != -1, r >= len(skill) / 2.
  Preconditions: Let n = len(skill). n is even, 2 <= n <= 100000, and for every i with 0 <= i < n, 1 <= skill[i] <= 1000. -/
theorem spec_4 (skill : Slice Std.I64)
    (h_even : skill.val.length % 2 = 0)
    (h_ge : 2 ≤ skill.val.length)
    (h_le : skill.val.length ≤ 100000)
    (h_bounds : ∀ i, i < skill.val.length → 1 ≤ skillEntry skill i ∧ skillEntry skill i ≤ 1000) :
    ∀ r, divide_players skill = ok r → r.val ≠ -1 →
      ((skill.val.length / 2 : Nat) : Int) ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (skill : Slice Std.I64)
    (h_even : skill.val.length % 2 = 0)
    (h_ge : 2 ≤ skill.val.length)
    (h_le : skill.val.length ≤ 100000)
    (h_bounds : ∀ i, i < skill.val.length → 1 ≤ skillEntry skill i ∧ skillEntry skill i ≤ 1000), ∀ r, divide_players skill = ok r → r.val ≠ -1 →
      ((skill.val.length / 2 : Nat) : Int) ≤ r.val) := by
  sorry

/-- The function returns a result r and r = skill[0] * skill[1].
  Preconditions: len(skill) = 2, and 1 <= skill[0] <= 1000 and 1 <= skill[1] <= 1000. -/
theorem spec_5 (skill : Slice Std.I64)
    (h_len : skill.val.length = 2)
    (h_bounds : ∀ i, i < skill.val.length → 1 ≤ skillEntry skill i ∧ skillEntry skill i ≤ 1000) :
    ∃ r, divide_players skill = ok r ∧
      r.val = skillEntry skill 0 * skillEntry skill 1 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (skill : Slice Std.I64)
    (h_len : skill.val.length = 2)
    (h_bounds : ∀ i, i < skill.val.length → 1 ≤ skillEntry skill i ∧ skillEntry skill i ≤ 1000), ∃ r, divide_players skill = ok r ∧
      r.val = skillEntry skill 0 * skillEntry skill 1) := by
  sorry

/-- The function returns a result r and r = (n / 2) * (v * v).
  Preconditions: Let n = len(skill). n is even, 2 <= n <= 100000. There exists an integer v with 1 <= v <= 1000 such that for every i with 0 <= i < n, skill[i] = v. -/
theorem spec_6 (skill : Slice Std.I64)
    (h_even : skill.val.length % 2 = 0)
    (h_ge : 2 ≤ skill.val.length)
    (h_le : skill.val.length ≤ 100000)
    (h_const : ∃ v : Int, 1 ≤ v ∧ v ≤ 1000 ∧
      ∀ i, i < skill.val.length → skillEntry skill i = v) :
    ∃ r, divide_players skill = ok r ∧
      ∀ v : Int, 1 ≤ v → v ≤ 1000 →
        (∀ i, i < skill.val.length → skillEntry skill i = v) →
        r.val = ((skill.val.length / 2 : Nat) : Int) * (v * v) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (skill : Slice Std.I64)
    (h_even : skill.val.length % 2 = 0)
    (h_ge : 2 ≤ skill.val.length)
    (h_le : skill.val.length ≤ 100000)
    (h_const : ∃ v : Int, 1 ≤ v ∧ v ≤ 1000 ∧
      ∀ i, i < skill.val.length → skillEntry skill i = v), ∃ r, divide_players skill = ok r ∧
      ∀ v : Int, 1 ≤ v → v ≤ 1000 →
        (∀ i, i < skill.val.length → skillEntry skill i = v) →
        r.val = ((skill.val.length / 2 : Nat) : Int) * (v * v)) := by
  sorry

/-- Whenever divide_players(skill) returns a result r with r != -1, let n = len(skill), T = sum_{i=0}^{n-1} skill[i], and Q = sum_{i=0}^{n-1} skill[i] * skill[i]. Then there is an integer S with 2*T = n*S and 2*r = S*T - Q.
  Preconditions: Let n = len(skill). n is even, 2 <= n <= 100000, and for every i with 0 <= i < n, 1 <= skill[i] <= 1000. -/
theorem spec_7 (skill : Slice Std.I64)
    (h_even : skill.val.length % 2 = 0)
    (h_ge : 2 ≤ skill.val.length)
    (h_le : skill.val.length ≤ 100000)
    (h_bounds : ∀ i, i < skill.val.length → 1 ≤ skillEntry skill i ∧ skillEntry skill i ≤ 1000) :
    ∀ r, divide_players skill = ok r → r.val ≠ -1 →
      ∃ S : Int,
        2 * totalSkill (skillVals skill) = (skill.val.length : Int) * S ∧
        2 * r.val = S * totalSkill (skillVals skill) - totalSkillSq (skillVals skill) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (skill : Slice Std.I64)
    (h_even : skill.val.length % 2 = 0)
    (h_ge : 2 ≤ skill.val.length)
    (h_le : skill.val.length ≤ 100000)
    (h_bounds : ∀ i, i < skill.val.length → 1 ≤ skillEntry skill i ∧ skillEntry skill i ≤ 1000), ∀ r, divide_players skill = ok r → r.val ≠ -1 →
      ∃ S : Int,
        2 * totalSkill (skillVals skill) = (skill.val.length : Int) * S ∧
        2 * r.val = S * totalSkill (skillVals skill) - totalSkillSq (skillVals skill)) := by
  sorry

/-- Whenever divide_players(skill) returns a result r and divide_players(perm) returns a result r_prime, we have r = -1 if and only if r_prime = -1, and if r != -1 then r = r_prime.
  Preconditions: Let n = len(skill). n is even, 2 <= n <= 100000, and for every i with 0 <= i < n, 1 <= skill[i] <= 1000. Let perm be any slice of length n such that for every integer v, the number of indices i with 0 <= i < n and perm[i] = v equals the number of indices i with 0 <= i < n and skill[i] = v. -/
theorem spec_8 (skill perm : Slice Std.I64)
    (h_even : skill.val.length % 2 = 0)
    (h_ge : 2 ≤ skill.val.length)
    (h_le : skill.val.length ≤ 100000)
    (h_bounds : ∀ i, i < skill.val.length → 1 ≤ skillEntry skill i ∧ skillEntry skill i ≤ 1000)
    (h_perm_len : perm.val.length = skill.val.length)
    (h_perm_count : ∀ v : Int, countOcc (skillVals perm) v = countOcc (skillVals skill) v) :
    ∀ r r' : Std.I64, divide_players skill = ok r → divide_players perm = ok r' →
      (r.val = -1 ↔ r'.val = -1) ∧ (r.val ≠ -1 → r.val = r') := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (skill perm : Slice Std.I64)
    (h_even : skill.val.length % 2 = 0)
    (h_ge : 2 ≤ skill.val.length)
    (h_le : skill.val.length ≤ 100000)
    (h_bounds : ∀ i, i < skill.val.length → 1 ≤ skillEntry skill i ∧ skillEntry skill i ≤ 1000)
    (h_perm_len : perm.val.length = skill.val.length)
    (h_perm_count : ∀ v : Int, countOcc (skillVals perm) v = countOcc (skillVals skill) v), ∀ r r' : Std.I64, divide_players skill = ok r → divide_players perm = ok r' →
      (r.val = -1 ↔ r'.val = -1) ∧ (r.val ≠ -1 → r.val = r')) := by
  sorry

/-- Whenever divide_players(skill) returns a result r with r != -1, let n = len(skill), T = sum_{i=0}^{n-1} skill[i], and S = (2 * T) / n. Then S is an integer and every valid equal-sum pairing of skill (a set of n/2 unordered index pairs covering every index exactly once with a common skill sum) has common pair sum S.
  Preconditions: Let n = len(skill). n is even, 2 <= n <= 100000, and for every i with 0 <= i < n, 1 <= skill[i] <= 1000. -/
theorem spec_9 (skill : Slice Std.I64)
    (h_even : skill.val.length % 2 = 0)
    (h_ge : 2 ≤ skill.val.length)
    (h_le : skill.val.length ≤ 100000)
    (h_bounds : ∀ i, i < skill.val.length → 1 ≤ skillEntry skill i ∧ skillEntry skill i ≤ 1000) :
    ∀ r, divide_players skill = ok r → r.val ≠ -1 →
      (skill.val.length : Int) ∣ 2 * totalSkill (skillVals skill) ∧
      ∀ (P : List (Nat × Nat)) (S : Int), IsValidPairingWithSum (skillVals skill) P S →
        S = 2 * totalSkill (skillVals skill) / (skill.val.length : Int) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (skill : Slice Std.I64)
    (h_even : skill.val.length % 2 = 0)
    (h_ge : 2 ≤ skill.val.length)
    (h_le : skill.val.length ≤ 100000)
    (h_bounds : ∀ i, i < skill.val.length → 1 ≤ skillEntry skill i ∧ skillEntry skill i ≤ 1000), ∀ r, divide_players skill = ok r → r.val ≠ -1 →
      (skill.val.length : Int) ∣ 2 * totalSkill (skillVals skill) ∧
      ∀ (P : List (Nat × Nat)) (S : Int), IsValidPairingWithSum (skillVals skill) P S →
        S = 2 * totalSkill (skillVals skill) / (skill.val.length : Int)) := by
  sorry

/-- Let n = len(skill) and T = sum_{i=0}^{n-1} skill[i]. Whenever divide_players(skill) returns a result r, r != -1 if and only if there exists an integer S such that 2*T = n*S and, for every integer v, the number of indices i with 0 <= i < n and skill[i] = v equals the number of indices i with 0 <= i < n and skill[i] = S - v (both counts being 0 when the value is outside the range of skill).
  Preconditions: Let n = len(skill). n is even, 2 <= n <= 100000, and for every i with 0 <= i < n, 1 <= skill[i] <= 1000. -/
theorem spec_10 (skill : Slice Std.I64)
    (h_even : skill.val.length % 2 = 0)
    (h_ge : 2 ≤ skill.val.length)
    (h_le : skill.val.length ≤ 100000)
    (h_bounds : ∀ i, i < skill.val.length → 1 ≤ skillEntry skill i ∧ skillEntry skill i ≤ 1000) :
    ∀ r, divide_players skill = ok r →
      (r.val ≠ -1 ↔
        ∃ S : Int,
          2 * totalSkill (skillVals skill) = (skill.val.length : Int) * S ∧
          ∀ v : Int, countOcc (skillVals skill) v = countOcc (skillVals skill) (S - v)) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (skill : Slice Std.I64)
    (h_even : skill.val.length % 2 = 0)
    (h_ge : 2 ≤ skill.val.length)
    (h_le : skill.val.length ≤ 100000)
    (h_bounds : ∀ i, i < skill.val.length → 1 ≤ skillEntry skill i ∧ skillEntry skill i ≤ 1000), ∀ r, divide_players skill = ok r →
      (r.val ≠ -1 ↔
        ∃ S : Int,
          2 * totalSkill (skillVals skill) = (skill.val.length : Int) * S ∧
          ∀ v : Int, countOcc (skillVals skill) v = countOcc (skillVals skill) (S - v))) := by
  sorry

/-- Whenever divide_players(skill) returns a result r with r != -1, let n = len(skill), T = sum_{i=0}^{n-1} skill[i], S = (2*T)/n, and let a be the nondecreasing sorted version of skill. Then S is an integer, for every i with 0 <= i < n/2 we have a[i] + a[n-1-i] = S, and r = sum_{i=0}^{n/2-1} a[i] * a[n-1-i].
  Preconditions: Let n = len(skill). n is even, 2 <= n <= 100000, and for every i with 0 <= i < n, 1 <= skill[i] <= 1000. -/
theorem spec_11 (skill : Slice Std.I64)
    (h_even : skill.val.length % 2 = 0)
    (h_ge : 2 ≤ skill.val.length)
    (h_le : skill.val.length ≤ 100000)
    (h_bounds : ∀ i, i < skill.val.length → 1 ≤ skillEntry skill i ∧ skillEntry skill i ≤ 1000) :
    ∀ r, divide_players skill = ok r → r.val ≠ -1 →
      let n := skill.val.length
      let T := totalSkill (skillVals skill)
      let S := 2 * T / (n : Int)
      (n : Int) ∣ 2 * T ∧
      ∀ a : List Int, IsSortedVersion (skillVals skill) a →
        outerPairSumsEq a n S ∧ r.val = outerPairProductSum a n := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (skill : Slice Std.I64)
    (h_even : skill.val.length % 2 = 0)
    (h_ge : 2 ≤ skill.val.length)
    (h_le : skill.val.length ≤ 100000)
    (h_bounds : ∀ i, i < skill.val.length → 1 ≤ skillEntry skill i ∧ skillEntry skill i ≤ 1000), ∀ r, divide_players skill = ok r → r.val ≠ -1 →
      let n := skill.val.length
      let T := totalSkill (skillVals skill)
      let S := 2 * T / (n : Int)
      (n : Int) ∣ 2 * T ∧
      ∀ a : List Int, IsSortedVersion (skillVals skill) a →
        outerPairSumsEq a n S ∧ r.val = outerPairProductSum a n) := by
  sorry

end AegisSpec.DividePlayers
