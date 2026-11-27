import Aegis.NumRabbits.Code.Funs

/-!
# Specifications of `Aegis.NumRabbits.num_rabbits`

LeetCode problem `rabbits-in-forest`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.NumRabbits

open scoped BigOperators

def count (answers : Slice Std.I64) (v : ℤ) : ℕ :=
  (answers.val.filter (fun a => decide (a.val = v))).length

def groupTotal (answers : Slice Std.I64) (v : ℕ) : ℕ :=
  ((count answers (v : ℤ) + v) / (v + 1)) * (v + 1)

def total (answers : Slice Std.I64) : ℕ :=
  ∑ v ∈ Finset.range 1000, groupTotal answers v

def maxEntry (answers : Slice Std.I64) : ℤ :=
  answers.val.foldr (fun a m => max a.val m) 0

def sumSucc (answers : Slice Std.I64) : ℤ :=
  (answers.val.map (fun a => a.val + 1)).sum

def othersTotal (answers : Slice Std.I64) (v : ℕ) : ℕ :=
  ∑ u ∈ Finset.range 1000, if u = v then 0 else groupTotal answers u

def colorClass {r : ℕ} (c : Fin r → ℕ) (x : Fin r) : Finset (Fin r) :=
  Finset.univ.filter (fun y => c y = c x)

def IsForest (answers : Slice Std.I64) (r : ℕ) : Prop :=
  ∃ (f : Fin answers.val.length → Fin r), Function.Injective f ∧
    ∃ (c : Fin r → ℕ), ∀ i : Fin answers.val.length,
      (colorClass c (f i)).card = (answers.val.get i).val.toNat + 1

def askedV (answers : Slice Std.I64) {r : ℕ} (f : Fin answers.val.length → Fin r)
    (v : ℕ) : Finset (Fin r) :=
  (Finset.univ.filter (fun i : Fin answers.val.length =>
    (answers.val.get i).val = (v : ℤ))).image f

def classesV (answers : Slice Std.I64) {r : ℕ} (f : Fin answers.val.length → Fin r)
    (c : Fin r → ℕ) (v : ℕ) : Finset (Finset (Fin r)) :=
  (askedV answers f v).image (fun x => colorClass c x)

def unionV (answers : Slice Std.I64) {r : ℕ} (f : Fin answers.val.length → Fin r)
    (c : Fin r → ℕ) (v : ℕ) : Finset (Fin r) :=
  (classesV answers f c v).biUnion id

def HasShape (answers : Slice Std.I64) (r : ℕ) : Prop :=
  ∃ (f : Fin answers.val.length → Fin r), Function.Injective f ∧
    ∃ (c : Fin r → ℕ),
      (∀ i : Fin answers.val.length,
        (colorClass c (f i)).card = (answers.val.get i).val.toNat + 1) ∧
      (∀ v ∈ Finset.range 1000, 0 < count answers (v : ℤ) →
        (unionV answers f c v).card = groupTotal answers v ∧
        (classesV answers f c v).card = groupTotal answers v / (v + 1) ∧
        (∀ C ∈ classesV answers f c v, C.card = v + 1) ∧
        (∀ C ∈ classesV answers f c v, ∃ y ∈ C, y ∈ askedV answers f v)) ∧
      (∀ v ∈ Finset.range 1000, ∀ w ∈ Finset.range 1000, v ≠ w →
        ∀ C ∈ classesV answers f c v, ∀ D ∈ classesV answers f c w, Disjoint C D) ∧
      (∀ x : Fin r, ∃ i : Fin answers.val.length, c (f i) = c x)

/-- The function returns a result r, and r = sum over all integers v with 0 <= v < 1000 and count(v) > 0 of ceil(count(v)/(v+1)) * (v+1), where count(v) is the number of indices i with 0 <= i < len(answers) and answers[i] = v. This r is the minimum possible total number of rabbits in the forest.
  Preconditions: 1 <= len(answers) <= 1000; for every i with 0 <= i < len(answers), 0 <= answers[i] < 1000. -/
theorem spec_1 (answers : Slice Std.I64)
    (hlen1 : 1 ≤ answers.val.length) (hlen2 : answers.val.length ≤ 1000)
    (hrange : ∀ a ∈ answers.val, 0 ≤ a.val ∧ a.val < 1000) :
    ∃ r, Aegis.NumRabbits.num_rabbits answers = ok r ∧ r.val = (total answers : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (answers : Slice Std.I64)
    (hlen1 : 1 ≤ answers.val.length) (hlen2 : answers.val.length ≤ 1000)
    (hrange : ∀ a ∈ answers.val, 0 ≤ a.val ∧ a.val < 1000), ∃ r, Aegis.NumRabbits.num_rabbits answers = ok r ∧ r.val = (total answers : ℤ)) := by
  sorry

/-- For every answers satisfying the preconditions, num_rabbits(answers) returns some result r; in particular it does not fail due to overflow, out-of-bounds access, or panic.
  Preconditions: 1 <= len(answers) <= 1000; for every i with 0 <= i < len(answers), 0 <= answers[i] < 1000. -/
theorem spec_2 (answers : Slice Std.I64)
    (hlen1 : 1 ≤ answers.val.length) (hlen2 : answers.val.length ≤ 1000)
    (hrange : ∀ a ∈ answers.val, 0 ≤ a.val ∧ a.val < 1000) :
    ∃ r, Aegis.NumRabbits.num_rabbits answers = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (answers : Slice Std.I64)
    (hlen1 : 1 ≤ answers.val.length) (hlen2 : answers.val.length ≤ 1000)
    (hrange : ∀ a ∈ answers.val, 0 ≤ a.val ∧ a.val < 1000), ∃ r, Aegis.NumRabbits.num_rabbits answers = ok r) := by
  sorry

/-- Whenever num_rabbits(answers) returns a result r, r >= len(answers).
  Preconditions: 1 <= len(answers) <= 1000; for every i with 0 <= i < len(answers), 0 <= answers[i] < 1000. -/
theorem spec_3 (answers : Slice Std.I64)
    (hlen1 : 1 ≤ answers.val.length) (hlen2 : answers.val.length ≤ 1000)
    (hrange : ∀ a ∈ answers.val, 0 ≤ a.val ∧ a.val < 1000)
    (r : Std.I64) (hr : Aegis.NumRabbits.num_rabbits answers = ok r) :
    (answers.val.length : ℤ) ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (answers : Slice Std.I64)
    (hlen1 : 1 ≤ answers.val.length) (hlen2 : answers.val.length ≤ 1000)
    (hrange : ∀ a ∈ answers.val, 0 ≤ a.val ∧ a.val < 1000)
    (r : Std.I64) (hr : Aegis.NumRabbits.num_rabbits answers = ok r), (answers.val.length : ℤ) ≤ r.val) := by
  sorry

/-- Whenever num_rabbits(answers) returns a result r, r >= M + 1, where M = max{answers[i] | 0 <= i < len(answers)}.
  Preconditions: 1 <= len(answers) <= 1000; for every i with 0 <= i < len(answers), 0 <= answers[i] < 1000. -/
theorem spec_4 (answers : Slice Std.I64)
    (hlen1 : 1 ≤ answers.val.length) (hlen2 : answers.val.length ≤ 1000)
    (hrange : ∀ a ∈ answers.val, 0 ≤ a.val ∧ a.val < 1000)
    (r : Std.I64) (hr : Aegis.NumRabbits.num_rabbits answers = ok r) :
    maxEntry answers + 1 ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (answers : Slice Std.I64)
    (hlen1 : 1 ≤ answers.val.length) (hlen2 : answers.val.length ≤ 1000)
    (hrange : ∀ a ∈ answers.val, 0 ≤ a.val ∧ a.val < 1000)
    (r : Std.I64) (hr : Aegis.NumRabbits.num_rabbits answers = ok r), maxEntry answers + 1 ≤ r.val) := by
  sorry

/-- Whenever num_rabbits(answers) returns a result r, r <= sum from i=0 to len(answers)-1 of (answers[i] + 1).
  Preconditions: 1 <= len(answers) <= 1000; for every i with 0 <= i < len(answers), 0 <= answers[i] < 1000. -/
theorem spec_5 (answers : Slice Std.I64)
    (hlen1 : 1 ≤ answers.val.length) (hlen2 : answers.val.length ≤ 1000)
    (hrange : ∀ a ∈ answers.val, 0 ≤ a.val ∧ a.val < 1000)
    (r : Std.I64) (hr : Aegis.NumRabbits.num_rabbits answers = ok r) :
    r.val ≤ sumSucc answers := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (answers : Slice Std.I64)
    (hlen1 : 1 ≤ answers.val.length) (hlen2 : answers.val.length ≤ 1000)
    (hrange : ∀ a ∈ answers.val, 0 ≤ a.val ∧ a.val < 1000)
    (r : Std.I64) (hr : Aegis.NumRabbits.num_rabbits answers = ok r), r.val ≤ sumSucc answers) := by
  sorry

/-- The function returns a result r and r = len(answers).
  Preconditions: 1 <= len(answers) <= 1000; for every i with 0 <= i < len(answers), answers[i] = 0. -/
theorem spec_6 (answers : Slice Std.I64)
    (hlen1 : 1 ≤ answers.val.length) (hlen2 : answers.val.length ≤ 1000)
    (hzero : ∀ a ∈ answers.val, a.val = 0) :
    ∃ r, Aegis.NumRabbits.num_rabbits answers = ok r ∧ r.val = (answers.val.length : ℤ) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (answers : Slice Std.I64)
    (hlen1 : 1 ≤ answers.val.length) (hlen2 : answers.val.length ≤ 1000)
    (hzero : ∀ a ∈ answers.val, a.val = 0), ∃ r, Aegis.NumRabbits.num_rabbits answers = ok r ∧ r.val = (answers.val.length : ℤ)) := by
  sorry

/-- The function returns a result r and r = ceil(len(answers)/(v+1)) * (v+1).
  Preconditions: 1 <= len(answers) <= 1000; there exists an integer v with 1 <= v < 1000 such that answers[i] = v for every i with 0 <= i < len(answers). -/
theorem spec_7 (answers : Slice Std.I64) (v : ℕ)
    (hlen1 : 1 ≤ answers.val.length) (hlen2 : answers.val.length ≤ 1000)
    (hv1 : 1 ≤ v) (hv2 : v < 1000)
    (hunif : ∀ a ∈ answers.val, a.val = (v : ℤ)) :
    ∃ r, Aegis.NumRabbits.num_rabbits answers = ok r ∧ r.val = (groupTotal answers v : ℤ) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (answers : Slice Std.I64) (v : ℕ)
    (hlen1 : 1 ≤ answers.val.length) (hlen2 : answers.val.length ≤ 1000)
    (hv1 : 1 ≤ v) (hv2 : v < 1000)
    (hunif : ∀ a ∈ answers.val, a.val = (v : ℤ)), ∃ r, Aegis.NumRabbits.num_rabbits answers = ok r ∧ r.val = (groupTotal answers v : ℤ)) := by
  sorry

/-- If num_rabbits(answers) returns r and num_rabbits(other) returns s, then r = s.
  Preconditions: answers and other are both valid inputs: 1 <= len(answers) <= 1000, 1 <= len(other) <= 1000, all entries are in [0,999], and other is a permutation of answers, meaning len(other)=len(answers) and there is a bijection between indices preserving the entry values. -/
theorem spec_8 (answers other : Slice Std.I64)
    (ha1 : 1 ≤ answers.val.length) (ha2 : answers.val.length ≤ 1000)
    (hb1 : 1 ≤ other.val.length) (hb2 : other.val.length ≤ 1000)
    (hca : ∀ a ∈ answers.val, 0 ≤ a.val ∧ a.val < 1000)
    (hcb : ∀ a ∈ other.val, 0 ≤ a.val ∧ a.val < 1000)
    (hperm : (answers.val.map (fun a => a.val)).Perm (other.val.map (fun a => a.val)))
    (r s : Std.I64) (hr : Aegis.NumRabbits.num_rabbits answers = ok r)
    (hs : Aegis.NumRabbits.num_rabbits other = ok s) :
    r.val = s.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (answers other : Slice Std.I64)
    (ha1 : 1 ≤ answers.val.length) (ha2 : answers.val.length ≤ 1000)
    (hb1 : 1 ≤ other.val.length) (hb2 : other.val.length ≤ 1000)
    (hca : ∀ a ∈ answers.val, 0 ≤ a.val ∧ a.val < 1000)
    (hcb : ∀ a ∈ other.val, 0 ≤ a.val ∧ a.val < 1000)
    (hperm : (answers.val.map (fun a => a.val)).Perm (other.val.map (fun a => a.val)))
    (r s : Std.I64) (hr : Aegis.NumRabbits.num_rabbits answers = ok r)
    (hs : Aegis.NumRabbits.num_rabbits other = ok s), r.val = s.val) := by
  sorry

/-- Whenever num_rabbits(answers) returns a result r, there exists a finite set of r rabbits partitioned into nonempty color classes and an injective assignment of each index i with 0 <= i < len(answers) to a distinct rabbit such that the color class containing the rabbit assigned to i has exactly answers[i] + 1 rabbits.
  Preconditions: 1 <= len(answers) <= 1000; for every i with 0 <= i < len(answers), 0 <= answers[i] < 1000. -/
theorem spec_9 (answers : Slice Std.I64)
    (hlen1 : 1 ≤ answers.val.length) (hlen2 : answers.val.length ≤ 1000)
    (hrange : ∀ a ∈ answers.val, 0 ≤ a.val ∧ a.val < 1000)
    (r : Std.I64) (hr : Aegis.NumRabbits.num_rabbits answers = ok r) :
    IsForest answers r.val.toNat := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (answers : Slice Std.I64)
    (hlen1 : 1 ≤ answers.val.length) (hlen2 : answers.val.length ≤ 1000)
    (hrange : ∀ a ∈ answers.val, 0 ≤ a.val ∧ a.val < 1000)
    (r : Std.I64) (hr : Aegis.NumRabbits.num_rabbits answers = ok r), IsForest answers r.val.toNat) := by
  sorry

/-- Whenever num_rabbits(answers) returns a result r, there exists a valid forest of r rabbits as in spec_9 with the following additional property. For every v with count(v) > 0, let T_v = ceil(count(v)/(v+1)) * (v+1). Then exactly T_v rabbits lie in color classes that contain at least one asked rabbit answering v; these T_v rabbits are partitioned into T_v/(v+1) color classes, each of size v+1 and each containing at least one asked rabbit answering v. Color classes associated with different v are disjoint, and every color class contains at least one asked rabbit.
  Preconditions: 1 <= len(answers) <= 1000; for every i with 0 <= i < len(answers), 0 <= answers[i] < 1000. -/
theorem spec_10 (answers : Slice Std.I64)
    (hlen1 : 1 ≤ answers.val.length) (hlen2 : answers.val.length ≤ 1000)
    (hrange : ∀ a ∈ answers.val, 0 ≤ a.val ∧ a.val < 1000)
    (r : Std.I64) (hr : Aegis.NumRabbits.num_rabbits answers = ok r) :
    HasShape answers r.val.toNat := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (answers : Slice Std.I64)
    (hlen1 : 1 ≤ answers.val.length) (hlen2 : answers.val.length ≤ 1000)
    (hrange : ∀ a ∈ answers.val, 0 ≤ a.val ∧ a.val < 1000)
    (r : Std.I64) (hr : Aegis.NumRabbits.num_rabbits answers = ok r), HasShape answers r.val.toNat) := by
  sorry

/-- Let answers' be the list of length len(answers)+1 obtained by appending v to answers, and let k = count(v) in answers. If num_rabbits(answers) returns r and num_rabbits(answers') returns r', then: if k mod (v+1) = 0 then r' = r + (v+1); otherwise r' = r.
  Preconditions: answers satisfies 1 <= len(answers) <= 1000 and all entries are in [0,999]; additionally len(answers) < 1000 and v is an integer with 0 <= v < 1000. -/
theorem spec_11 (answers answers' : Slice Std.I64) (v : ℕ) (w : Std.I64)
    (hlen1 : 1 ≤ answers.val.length) (hlen2 : answers.val.length ≤ 1000)
    (hlen3 : answers.val.length < 1000)
    (hrange : ∀ a ∈ answers.val, 0 ≤ a.val ∧ a.val < 1000)
    (hv : v < 1000) (hw : w.val = (v : ℤ))
    (happend : answers'.val = answers.val ++ [w])
    (r r' : Std.I64) (hr : Aegis.NumRabbits.num_rabbits answers = ok r)
    (hr' : Aegis.NumRabbits.num_rabbits answers' = ok r') :
    (count answers (v : ℤ) % (v + 1) = 0 → r'.val = r.val + ((v : ℤ) + 1)) ∧
    (count answers (v : ℤ) % (v + 1) ≠ 0 → r'.val = r.val) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (answers answers' : Slice Std.I64) (v : ℕ) (w : Std.I64)
    (hlen1 : 1 ≤ answers.val.length) (hlen2 : answers.val.length ≤ 1000)
    (hlen3 : answers.val.length < 1000)
    (hrange : ∀ a ∈ answers.val, 0 ≤ a.val ∧ a.val < 1000)
    (hv : v < 1000) (hw : w.val = (v : ℤ))
    (happend : answers'.val = answers.val ++ [w])
    (r r' : Std.I64) (hr : Aegis.NumRabbits.num_rabbits answers = ok r)
    (hr' : Aegis.NumRabbits.num_rabbits answers' = ok r'), (count answers (v : ℤ) % (v + 1) = 0 → r'.val = r.val + ((v : ℤ) + 1)) ∧
    (count answers (v : ℤ) % (v + 1) ≠ 0 → r'.val = r.val)) := by
  sorry

/-- Whenever num_rabbits(answers) returns a result r, r = (v+1) + sum over all u with count(u) > 0 and u != v of ceil(count(u)/(u+1)) * (u+1).
  Preconditions: 1 <= len(answers) <= 1000; all entries are in [0,999]; v is an integer with 0 <= v < 1000 and 1 <= count(v) <= v+1, where count(v) is the number of indices i with answers[i] = v. -/
theorem spec_12 (answers : Slice Std.I64) (v : ℕ)
    (hlen1 : 1 ≤ answers.val.length) (hlen2 : answers.val.length ≤ 1000)
    (hrange : ∀ a ∈ answers.val, 0 ≤ a.val ∧ a.val < 1000)
    (hv : v < 1000) (hc1 : 1 ≤ count answers (v : ℤ)) (hc2 : count answers (v : ℤ) ≤ v + 1)
    (r : Std.I64) (hr : Aegis.NumRabbits.num_rabbits answers = ok r) :
    r.val = ((v : ℤ) + 1) + (othersTotal answers v : ℤ) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (answers : Slice Std.I64) (v : ℕ)
    (hlen1 : 1 ≤ answers.val.length) (hlen2 : answers.val.length ≤ 1000)
    (hrange : ∀ a ∈ answers.val, 0 ≤ a.val ∧ a.val < 1000)
    (hv : v < 1000) (hc1 : 1 ≤ count answers (v : ℤ)) (hc2 : count answers (v : ℤ) ≤ v + 1)
    (r : Std.I64) (hr : Aegis.NumRabbits.num_rabbits answers = ok r), r.val = ((v : ℤ) + 1) + (othersTotal answers v : ℤ)) := by
  sorry

end AegisSpec.NumRabbits
