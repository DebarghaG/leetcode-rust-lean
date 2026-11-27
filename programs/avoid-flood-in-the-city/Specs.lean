import Aegis.AvoidFlood.Code.Funs

/-!
# Specifications of `Aegis.AvoidFlood.avoid_flood`

LeetCode problem `avoid-flood-in-the-city`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.AvoidFlood

  open Aegis.AvoidFlood

  def vals (l : List Std.I64) : List ℤ := l.map (fun x => x.val)

  def step (F : Finset ℤ) (r a : ℤ) : Option (Finset ℤ) :=
    if 0 < r then (if r ∈ F then none else some (insert r F))
    else if r = 0 then some (F.erase a)
    else none

  def simSteps : Finset ℤ → List ℤ → List ℤ → ℕ → Option (Finset ℤ)
    | F, _, _, 0 => some F
    | F, r :: rs, a :: ds, k + 1 => (step F r a).bind (fun F' => simSteps F' rs ds k)
    | _, [], _, _ + 1 => none
    | _, _ :: _, [], _ + 1 => none

  def sim (rains v : List ℤ) : Option (Finset ℤ) := simSteps ∅ rains v rains.length

  def fullBefore (rains v : List ℤ) (i : ℕ) : Option (Finset ℤ) := simSteps ∅ rains v i

  def FloodFree (rains v : List ℤ) : Prop :=
    v.length = rains.length ∧ ∃ F : Finset ℤ, sim rains v = some F

  def ValidAnswer (rains v : List ℤ) : Prop :=
    v.length = rains.length ∧
      (∀ (i : ℕ), i < rains.length →
        (0 < rains.getD i 0 → v.getD i 0 = -1) ∧
          (rains.getD i 0 = 0 → 0 < v.getD i 0)) ∧
      FloodFree rains v

  /-- Whenever the function returns a result r, r is a valid answer for rains when one exists, and r is the empty vector otherwise. A vector v of i64 is a valid answer for rains exactly when: (1) len(v) = n; (2) for every i with 0 <= i < n, if rains[i] > 0 then v[i] = -1, and if rains[i] = 0 then v[i] > 0; (3) the following simulation, run for i = 0,1,...,n-1 with an initially empty set F of lake numbers, never produces a flood: if rains[i] > 0, then a flood occurs if rains[i] is in F, otherwise rains[i] is added to F; if rains[i] = 0, then v[i] is removed from F if it is in F, otherwise F is unchanged. Thus, if at least one valid answer exists, the returned r must satisfy (1)-(3); if no valid answer exists, the returned r must have len(r) = 0. Every valid answer is accepted, including valid answers whose dry-day entries are arbitrary positive i64 lake numbers not occurring in rains.
    Preconditions: Let n = len(rains). The slice is nonempty (n >= 1), and for every i with 0 <= i < n we have 0 <= rains[i] <= 1000000000. -/
  theorem spec_1 (rains : Slice Std.I64)
      (hn : 1 ≤ rains.val.length)
      (hb : ∀ (i : ℕ) (hi : i < rains.val.length),
        0 ≤ (rains.val[i]).val ∧ (rains.val[i]).val ≤ 1000000000) :
      ∀ r : alloc.vec.Vec Std.I64, avoid_flood rains = ok r →
        ((∃ v : alloc.vec.Vec Std.I64, ValidAnswer (vals rains.val) (vals v.val)) →
            ValidAnswer (vals rains.val) (vals r.val)) ∧
          ((¬ ∃ v : alloc.vec.Vec Std.I64, ValidAnswer (vals rains.val) (vals v.val)) →
            r.val = []) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (rains : Slice Std.I64)
        (hn : 1 ≤ rains.val.length)
        (hb : ∀ (i : ℕ) (hi : i < rains.val.length),
          0 ≤ (rains.val[i]).val ∧ (rains.val[i]).val ≤ 1000000000), ∀ r : alloc.vec.Vec Std.I64, avoid_flood rains = ok r →
          ((∃ v : alloc.vec.Vec Std.I64, ValidAnswer (vals rains.val) (vals v.val)) →
              ValidAnswer (vals rains.val) (vals r.val)) ∧
            ((¬ ∃ v : alloc.vec.Vec Std.I64, ValidAnswer (vals rains.val) (vals v.val)) →
              r.val = [])) := by
    sorry

  /-- The function returns a result r; it does not fail by overflow, out-of-bounds access, or panic.
    Preconditions: Let n = len(rains). The slice is nonempty (n >= 1), and for every i with 0 <= i < n we have 0 <= rains[i] <= 1000000000. -/
  theorem spec_2 (rains : Slice Std.I64)
      (hn : 1 ≤ rains.val.length)
      (hb : ∀ (i : ℕ) (hi : i < rains.val.length),
        0 ≤ (rains.val[i]).val ∧ (rains.val[i]).val ≤ 1000000000) :
      ∃ r : alloc.vec.Vec Std.I64, avoid_flood rains = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (rains : Slice Std.I64)
        (hn : 1 ≤ rains.val.length)
        (hb : ∀ (i : ℕ) (hi : i < rains.val.length),
          0 ≤ (rains.val[i]).val ∧ (rains.val[i]).val ≤ 1000000000), ∃ r : alloc.vec.Vec Std.I64, avoid_flood rains = ok r) := by
    sorry

  /-- Whenever the function returns a result r, len(r) is either 0 or n. Equivalently, if r is nonempty, then len(r) = n.
    Preconditions: Let n = len(rains). The slice is nonempty (n >= 1), and for every i with 0 <= i < n we have 0 <= rains[i] <= 1000000000. -/
  theorem spec_3 (rains : Slice Std.I64)
      (hn : 1 ≤ rains.val.length)
      (hb : ∀ (i : ℕ) (hi : i < rains.val.length),
        0 ≤ (rains.val[i]).val ∧ (rains.val[i]).val ≤ 1000000000) :
      ∀ r : alloc.vec.Vec Std.I64, avoid_flood rains = ok r →
        r.val.length = 0 ∨ r.val.length = rains.val.length := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (rains : Slice Std.I64)
        (hn : 1 ≤ rains.val.length)
        (hb : ∀ (i : ℕ) (hi : i < rains.val.length),
          0 ≤ (rains.val[i]).val ∧ (rains.val[i]).val ≤ 1000000000), ∀ r : alloc.vec.Vec Std.I64, avoid_flood rains = ok r →
          r.val.length = 0 ∨ r.val.length = rains.val.length) := by
    sorry

  /-- Whenever the function returns a result r with len(r) > 0, for every i with 0 <= i < n and rains[i] > 0, we have r[i] = -1.
    Preconditions: Let n = len(rains). The slice is nonempty (n >= 1), and for every i with 0 <= i < n we have 0 <= rains[i] <= 1000000000. -/
  theorem spec_4 (rains : Slice Std.I64)
      (hn : 1 ≤ rains.val.length)
      (hb : ∀ (i : ℕ) (hi : i < rains.val.length),
        0 ≤ (rains.val[i]).val ∧ (rains.val[i]).val ≤ 1000000000) :
      ∀ r : alloc.vec.Vec Std.I64, avoid_flood rains = ok r → 0 < r.val.length →
        ∀ (i : ℕ) (hi : i < rains.val.length),
          0 < (rains.val[i]).val → (vals r.val).getD i 0 = -1 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (rains : Slice Std.I64)
        (hn : 1 ≤ rains.val.length)
        (hb : ∀ (i : ℕ) (hi : i < rains.val.length),
          0 ≤ (rains.val[i]).val ∧ (rains.val[i]).val ≤ 1000000000), ∀ r : alloc.vec.Vec Std.I64, avoid_flood rains = ok r → 0 < r.val.length →
          ∀ (i : ℕ) (hi : i < rains.val.length),
            0 < (rains.val[i]).val → (vals r.val).getD i 0 = -1) := by
    sorry

  /-- Whenever the function returns a result r with len(r) > 0, for every i with 0 <= i < n and rains[i] = 0, we have r[i] > 0. The value r[i] may be any positive i64 lake number; it is not required to occur among the positive entries of rains.
    Preconditions: Let n = len(rains). The slice is nonempty (n >= 1), and for every i with 0 <= i < n we have 0 <= rains[i] <= 1000000000. -/
  theorem spec_5 (rains : Slice Std.I64)
      (hn : 1 ≤ rains.val.length)
      (hb : ∀ (i : ℕ) (hi : i < rains.val.length),
        0 ≤ (rains.val[i]).val ∧ (rains.val[i]).val ≤ 1000000000) :
      ∀ r : alloc.vec.Vec Std.I64, avoid_flood rains = ok r → 0 < r.val.length →
        ∀ (i : ℕ) (hi : i < rains.val.length),
          (rains.val[i]).val = 0 → 0 < (vals r.val).getD i 0 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (rains : Slice Std.I64)
        (hn : 1 ≤ rains.val.length)
        (hb : ∀ (i : ℕ) (hi : i < rains.val.length),
          0 ≤ (rains.val[i]).val ∧ (rains.val[i]).val ≤ 1000000000), ∀ r : alloc.vec.Vec Std.I64, avoid_flood rains = ok r → 0 < r.val.length →
          ∀ (i : ℕ) (hi : i < rains.val.length),
            (rains.val[i]).val = 0 → 0 < (vals r.val).getD i 0) := by
    sorry

  /-- Whenever the function returns a result r with len(r) > 0, the drying schedule r is flood-free: let F be initially empty; for i = 0,1,...,n-1, if rains[i] > 0 then require rains[i] not in F and then add rains[i] to F; if rains[i] = 0 then remove r[i] from F if it is present, otherwise leave F unchanged. No rainy day may find its lake already in F.
    Preconditions: Let n = len(rains). The slice is nonempty (n >= 1), and for every i with 0 <= i < n we have 0 <= rains[i] <= 1000000000. -/
  theorem spec_6 (rains : Slice Std.I64)
      (hn : 1 ≤ rains.val.length)
      (hb : ∀ (i : ℕ) (hi : i < rains.val.length),
        0 ≤ (rains.val[i]).val ∧ (rains.val[i]).val ≤ 1000000000) :
      ∀ r : alloc.vec.Vec Std.I64, avoid_flood rains = ok r → 0 < r.val.length →
        FloodFree (vals rains.val) (vals r.val) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (rains : Slice Std.I64)
        (hn : 1 ≤ rains.val.length)
        (hb : ∀ (i : ℕ) (hi : i < rains.val.length),
          0 ≤ (rains.val[i]).val ∧ (rains.val[i]).val ≤ 1000000000), ∀ r : alloc.vec.Vec Std.I64, avoid_flood rains = ok r → 0 < r.val.length →
          FloodFree (vals rains.val) (vals r.val)) := by
    sorry

  /-- Whenever the function returns a result r, len(r) = 0 if and only if there does not exist any vector v with len(v) = n such that (i) for every i, v[i] = -1 when rains[i] > 0 and v[i] > 0 when rains[i] = 0, and (ii) the simulation with v described in spec_6 has no flood. Moreover, if len(r) > 0, then r itself satisfies (i) and (ii), i.e. r is a valid schedule.
    Preconditions: Let n = len(rains). The slice is nonempty (n >= 1), and for every i with 0 <= i < n we have 0 <= rains[i] <= 1000000000. -/
  theorem spec_7 (rains : Slice Std.I64)
      (hn : 1 ≤ rains.val.length)
      (hb : ∀ (i : ℕ) (hi : i < rains.val.length),
        0 ≤ (rains.val[i]).val ∧ (rains.val[i]).val ≤ 1000000000) :
      ∀ r : alloc.vec.Vec Std.I64, avoid_flood rains = ok r →
        (r.val.length = 0 ↔
            ¬ ∃ v : alloc.vec.Vec Std.I64, ValidAnswer (vals rains.val) (vals v.val)) ∧
          (0 < r.val.length → ValidAnswer (vals rains.val) (vals r.val)) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (rains : Slice Std.I64)
        (hn : 1 ≤ rains.val.length)
        (hb : ∀ (i : ℕ) (hi : i < rains.val.length),
          0 ≤ (rains.val[i]).val ∧ (rains.val[i]).val ≤ 1000000000), ∀ r : alloc.vec.Vec Std.I64, avoid_flood rains = ok r →
          (r.val.length = 0 ↔
              ¬ ∃ v : alloc.vec.Vec Std.I64, ValidAnswer (vals rains.val) (vals v.val)) ∧
            (0 < r.val.length → ValidAnswer (vals rains.val) (vals r.val))) := by
    sorry

  /-- The function returns a result r with len(r) = n, and r[i] = -1 for every 0 <= i < n.
    Preconditions: Let n = len(rains). The slice is nonempty (n >= 1), and for every i with 0 <= i < n we have 0 <= rains[i] <= 1000000000. Assume additionally that rains[i] > 0 for every 0 <= i < n, and that the positive values are pairwise distinct: for every 0 <= i < j < n, rains[i] != rains[j]. -/
  theorem spec_8 (rains : Slice Std.I64)
      (hn : 1 ≤ rains.val.length)
      (hb : ∀ (i : ℕ) (hi : i < rains.val.length),
        0 ≤ (rains.val[i]).val ∧ (rains.val[i]).val ≤ 1000000000)
      (hall : ∀ (i : ℕ) (hi : i < rains.val.length), 0 < (rains.val[i]).val)
      (hdist : ∀ (i j : ℕ) (hi : i < rains.val.length) (hj : j < rains.val.length),
        i < j → (rains.val[i]).val ≠ (rains.val[j]).val) :
      ∀ r : alloc.vec.Vec Std.I64, avoid_flood rains = ok r →
        r.val.length = rains.val.length ∧
          ∀ (i : ℕ) (hi : i < rains.val.length), (vals r.val).getD i 0 = -1 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (rains : Slice Std.I64)
        (hn : 1 ≤ rains.val.length)
        (hb : ∀ (i : ℕ) (hi : i < rains.val.length),
          0 ≤ (rains.val[i]).val ∧ (rains.val[i]).val ≤ 1000000000)
        (hall : ∀ (i : ℕ) (hi : i < rains.val.length), 0 < (rains.val[i]).val)
        (hdist : ∀ (i j : ℕ) (hi : i < rains.val.length) (hj : j < rains.val.length),
          i < j → (rains.val[i]).val ≠ (rains.val[j]).val), ∀ r : alloc.vec.Vec Std.I64, avoid_flood rains = ok r →
          r.val.length = rains.val.length ∧
            ∀ (i : ℕ) (hi : i < rains.val.length), (vals r.val).getD i 0 = -1) := by
    sorry

  /-- The function returns the empty vector, i.e. len(r) = 0.
    Preconditions: Let n = len(rains). The slice is nonempty (n >= 1), and for every i with 0 <= i < n we have 0 <= rains[i] <= 1000000000. Assume additionally that rains[i] > 0 for every 0 <= i < n, and that some lake rains twice: there exist i and j with 0 <= i < j < n and rains[i] = rains[j]. -/
  theorem spec_9 (rains : Slice Std.I64)
      (hn : 1 ≤ rains.val.length)
      (hb : ∀ (i : ℕ) (hi : i < rains.val.length),
        0 ≤ (rains.val[i]).val ∧ (rains.val[i]).val ≤ 1000000000)
      (hall : ∀ (i : ℕ) (hi : i < rains.val.length), 0 < (rains.val[i]).val)
      (htwice : ∃ (i j : ℕ) (hi : i < rains.val.length) (hj : j < rains.val.length),
        i < j ∧ (rains.val[i]).val = (rains.val[j]).val) :
      ∀ r : alloc.vec.Vec Std.I64, avoid_flood rains = ok r → r.val = [] := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (rains : Slice Std.I64)
        (hn : 1 ≤ rains.val.length)
        (hb : ∀ (i : ℕ) (hi : i < rains.val.length),
          0 ≤ (rains.val[i]).val ∧ (rains.val[i]).val ≤ 1000000000)
        (hall : ∀ (i : ℕ) (hi : i < rains.val.length), 0 < (rains.val[i]).val)
        (htwice : ∃ (i j : ℕ) (hi : i < rains.val.length) (hj : j < rains.val.length),
          i < j ∧ (rains.val[i]).val = (rains.val[j]).val), ∀ r : alloc.vec.Vec Std.I64, avoid_flood rains = ok r → r.val = []) := by
    sorry

  /-- The function returns a result r with len(r) = n and r[i] > 0 for every 0 <= i < n.
    Preconditions: Let n = len(rains). The slice is nonempty (n >= 1), and for every i with 0 <= i < n we have 0 <= rains[i] <= 1000000000. Assume additionally that rains[i] = 0 for every 0 <= i < n. -/
  theorem spec_10 (rains : Slice Std.I64)
      (hn : 1 ≤ rains.val.length)
      (hb : ∀ (i : ℕ) (hi : i < rains.val.length),
        0 ≤ (rains.val[i]).val ∧ (rains.val[i]).val ≤ 1000000000)
      (hall : ∀ (i : ℕ) (hi : i < rains.val.length), (rains.val[i]).val = 0) :
      ∀ r : alloc.vec.Vec Std.I64, avoid_flood rains = ok r →
        r.val.length = rains.val.length ∧
          ∀ (i : ℕ) (hi : i < rains.val.length), 0 < (vals r.val).getD i 0 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (rains : Slice Std.I64)
        (hn : 1 ≤ rains.val.length)
        (hb : ∀ (i : ℕ) (hi : i < rains.val.length),
          0 ≤ (rains.val[i]).val ∧ (rains.val[i]).val ≤ 1000000000)
        (hall : ∀ (i : ℕ) (hi : i < rains.val.length), (rains.val[i]).val = 0), ∀ r : alloc.vec.Vec Std.I64, avoid_flood rains = ok r →
          r.val.length = rains.val.length ∧
            ∀ (i : ℕ) (hi : i < rains.val.length), 0 < (vals r.val).getD i 0) := by
    sorry

  /-- Whenever the function returns a result r with len(r) > 0, let i be any index with 0 <= i < n and rains[i] = 0, and let F_i be the set of full lakes immediately before day i in the simulation of r (F_0 is empty). If r[i] is not in F_i, then replacing the single entry r[i] by any positive i64 lake d yields another valid answer for rains: the modified vector has length n, has -1 exactly on rainy days, has a positive value on every dry day, and its simulation is flood-free.
    Preconditions: Let n = len(rains). The slice is nonempty (n >= 1), and for every i with 0 <= i < n we have 0 <= rains[i] <= 1000000000. -/
  theorem spec_11 (rains : Slice Std.I64)
      (hn : 1 ≤ rains.val.length)
      (hb : ∀ (i : ℕ) (hi : i < rains.val.length),
        0 ≤ (rains.val[i]).val ∧ (rains.val[i]).val ≤ 1000000000) :
      ∀ r : alloc.vec.Vec Std.I64, avoid_flood rains = ok r → 0 < r.val.length →
        ∀ (i : ℕ) (hi : i < rains.val.length), (rains.val[i]).val = 0 →
          ∀ F : Finset ℤ, fullBefore (vals rains.val) (vals r.val) i = some F →
            (vals r.val).getD i 0 ∉ F →
              ∀ d : Std.I64, 0 < d.val →
                ValidAnswer (vals rains.val) ((vals r.val).set i d.val) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (rains : Slice Std.I64)
        (hn : 1 ≤ rains.val.length)
        (hb : ∀ (i : ℕ) (hi : i < rains.val.length),
          0 ≤ (rains.val[i]).val ∧ (rains.val[i]).val ≤ 1000000000), ∀ r : alloc.vec.Vec Std.I64, avoid_flood rains = ok r → 0 < r.val.length →
          ∀ (i : ℕ) (hi : i < rains.val.length), (rains.val[i]).val = 0 →
            ∀ F : Finset ℤ, fullBefore (vals rains.val) (vals r.val) i = some F →
              (vals r.val).getD i 0 ∉ F →
                ∀ d : Std.I64, 0 < d.val →
                  ValidAnswer (vals rains.val) ((vals r.val).set i d.val)) := by
    sorry

  end AegisSpec.AvoidFlood
