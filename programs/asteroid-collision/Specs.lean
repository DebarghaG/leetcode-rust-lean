import Aegis.AsteroidCollision.Code.Funs

/-!
# Specifications of `Aegis.AsteroidCollision.asteroid_collision`

LeetCode problem `asteroid-collision`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas
open Aeneas.Std
open Result

namespace AegisSpec.AsteroidCollision

def CollisionStep (L L' : List Aeneas.Std.I64) : Prop :=
  ∃ (p : List Aeneas.Std.I64) (a b : Aeneas.Std.I64) (q : List Aeneas.Std.I64),
    L = p ++ a :: b :: q ∧ 0 < a.val ∧ b.val < 0 ∧
      ((a.val > -(b.val) ∧ L' = p ++ a :: q) ∨
        (a.val = -(b.val) ∧ L' = p ++ q) ∨
        (a.val < -(b.val) ∧ L' = p ++ b :: q))

def CollisionReach : List Aeneas.Std.I64 → List Aeneas.Std.I64 → Prop :=
  Relation.ReflTransGen CollisionStep

def NoCollision (L : List Aeneas.Std.I64) : Prop :=
  ∀ (i : Nat) (h : i + 1 < L.length), ¬ (0 < (L[i]'(by omega)).val ∧ (L[i + 1]'h).val < 0)

def NegThenPos (L : List Aeneas.Std.I64) : Prop :=
  ∃ k : Nat, k ≤ L.length ∧
    (∀ (j : Nat) (hj : j < L.length), j < k → (L[j]'hj).val < 0) ∧
    (∀ (j : Nat) (hj : j < L.length), k ≤ j → 0 < (L[j]'hj).val)

/-- The function returns a result r. Let a collision step mean choosing an index i with 0 <= i < len(L)-1, L[i] > 0, and L[i+1] < 0 in a list L, deleting the two adjacent entries L[i], L[i+1], and inserting in their place the single entry L[i] if L[i] > -L[i+1], no entry if L[i] = -L[i+1], or the single entry L[i+1] if L[i] < -L[i+1]. Then r is the unique list reachable from asteroids by finitely many such collision steps and having no index i with 0 <= i < len(r)-1, r[i] > 0, and r[i+1] < 0. Equivalently, r is the state of the asteroids after all collisions; r may be empty.
  Preconditions: 2 <= len(asteroids) <= 10000; for every i with 0 <= i < len(asteroids), -1000 <= asteroids[i] <= 1000 and asteroids[i] != 0. -/
theorem spec_1 (asteroids : Slice Aeneas.Std.I64)
    (hlen : 2 ≤ asteroids.val.length) (hlen_max : asteroids.val.length ≤ 10000)
    (hvals : ∀ (i : Nat) (hi : i < asteroids.val.length),
      -1000 ≤ (asteroids.val[i]'hi).val ∧ (asteroids.val[i]'hi).val ≤ 1000 ∧
        (asteroids.val[i]'hi).val ≠ 0) :
    ∃ r, Aegis.AsteroidCollision.asteroid_collision asteroids = ok r ∧
      CollisionReach asteroids.val r.val ∧
      NoCollision r.val ∧
      (∀ r' : List Aeneas.Std.I64, CollisionReach asteroids.val r' → NoCollision r' →
        r' = r.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (asteroids : Slice Aeneas.Std.I64)
    (hlen : 2 ≤ asteroids.val.length) (hlen_max : asteroids.val.length ≤ 10000)
    (hvals : ∀ (i : Nat) (hi : i < asteroids.val.length),
      -1000 ≤ (asteroids.val[i]'hi).val ∧ (asteroids.val[i]'hi).val ≤ 1000 ∧
        (asteroids.val[i]'hi).val ≠ 0), ∃ r, Aegis.AsteroidCollision.asteroid_collision asteroids = ok r ∧
      CollisionReach asteroids.val r.val ∧
      NoCollision r.val ∧
      (∀ r' : List Aeneas.Std.I64, CollisionReach asteroids.val r' → NoCollision r' →
        r' = r.val)) := by
  sorry

/-- The function returns a result r; it does not fail by arithmetic overflow, out-of-bounds slice access, or panic.
  Preconditions: 2 <= len(asteroids) <= 10000; for every i with 0 <= i < len(asteroids), -1000 <= asteroids[i] <= 1000 and asteroids[i] != 0. -/
theorem spec_2 (asteroids : Slice Aeneas.Std.I64)
    (hlen : 2 ≤ asteroids.val.length) (hlen_max : asteroids.val.length ≤ 10000)
    (hvals : ∀ (i : Nat) (hi : i < asteroids.val.length),
      -1000 ≤ (asteroids.val[i]'hi).val ∧ (asteroids.val[i]'hi).val ≤ 1000 ∧
        (asteroids.val[i]'hi).val ≠ 0) :
    ∃ r, Aegis.AsteroidCollision.asteroid_collision asteroids = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (asteroids : Slice Aeneas.Std.I64)
    (hlen : 2 ≤ asteroids.val.length) (hlen_max : asteroids.val.length ≤ 10000)
    (hvals : ∀ (i : Nat) (hi : i < asteroids.val.length),
      -1000 ≤ (asteroids.val[i]'hi).val ∧ (asteroids.val[i]'hi).val ≤ 1000 ∧
        (asteroids.val[i]'hi).val ≠ 0), ∃ r, Aegis.AsteroidCollision.asteroid_collision asteroids = ok r) := by
  sorry

/-- The function returns a result r and 0 <= len(r) <= len(asteroids).
  Preconditions: 2 <= len(asteroids) <= 10000; for every i with 0 <= i < len(asteroids), -1000 <= asteroids[i] <= 1000 and asteroids[i] != 0. -/
theorem spec_3 (asteroids : Slice Aeneas.Std.I64)
    (hlen : 2 ≤ asteroids.val.length) (hlen_max : asteroids.val.length ≤ 10000)
    (hvals : ∀ (i : Nat) (hi : i < asteroids.val.length),
      -1000 ≤ (asteroids.val[i]'hi).val ∧ (asteroids.val[i]'hi).val ≤ 1000 ∧
        (asteroids.val[i]'hi).val ≠ 0) :
    ∃ r, Aegis.AsteroidCollision.asteroid_collision asteroids = ok r ∧
      0 ≤ r.val.length ∧ r.val.length ≤ asteroids.val.length := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (asteroids : Slice Aeneas.Std.I64)
    (hlen : 2 ≤ asteroids.val.length) (hlen_max : asteroids.val.length ≤ 10000)
    (hvals : ∀ (i : Nat) (hi : i < asteroids.val.length),
      -1000 ≤ (asteroids.val[i]'hi).val ∧ (asteroids.val[i]'hi).val ≤ 1000 ∧
        (asteroids.val[i]'hi).val ≠ 0), ∃ r, Aegis.AsteroidCollision.asteroid_collision asteroids = ok r ∧
      0 ≤ r.val.length ∧ r.val.length ≤ asteroids.val.length) := by
  sorry

/-- The function returns a result r and for every j with 0 <= j < len(r), r[j] != 0.
  Preconditions: 2 <= len(asteroids) <= 10000; for every i with 0 <= i < len(asteroids), -1000 <= asteroids[i] <= 1000 and asteroids[i] != 0. -/
theorem spec_4 (asteroids : Slice Aeneas.Std.I64)
    (hlen : 2 ≤ asteroids.val.length) (hlen_max : asteroids.val.length ≤ 10000)
    (hvals : ∀ (i : Nat) (hi : i < asteroids.val.length),
      -1000 ≤ (asteroids.val[i]'hi).val ∧ (asteroids.val[i]'hi).val ≤ 1000 ∧
        (asteroids.val[i]'hi).val ≠ 0) :
    ∃ r, Aegis.AsteroidCollision.asteroid_collision asteroids = ok r ∧
      ∀ (j : Nat) (hj : j < r.val.length), (r.val[j]'hj).val ≠ 0 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (asteroids : Slice Aeneas.Std.I64)
    (hlen : 2 ≤ asteroids.val.length) (hlen_max : asteroids.val.length ≤ 10000)
    (hvals : ∀ (i : Nat) (hi : i < asteroids.val.length),
      -1000 ≤ (asteroids.val[i]'hi).val ∧ (asteroids.val[i]'hi).val ≤ 1000 ∧
        (asteroids.val[i]'hi).val ≠ 0), ∃ r, Aegis.AsteroidCollision.asteroid_collision asteroids = ok r ∧
      ∀ (j : Nat) (hj : j < r.val.length), (r.val[j]'hj).val ≠ 0) := by
  sorry

/-- The function returns a result r and there is a strictly increasing sequence i_0, i_1, ..., i_{len(r)-1} of indices into asteroids (empty when len(r)=0) such that 0 <= i_0 < i_1 < ... < i_{len(r)-1} < len(asteroids) and r[j] = asteroids[i_j] for every j with 0 <= j < len(r).
  Preconditions: 2 <= len(asteroids) <= 10000; for every i with 0 <= i < len(asteroids), -1000 <= asteroids[i] <= 1000 and asteroids[i] != 0. -/
theorem spec_5 (asteroids : Slice Aeneas.Std.I64)
    (hlen : 2 ≤ asteroids.val.length) (hlen_max : asteroids.val.length ≤ 10000)
    (hvals : ∀ (i : Nat) (hi : i < asteroids.val.length),
      -1000 ≤ (asteroids.val[i]'hi).val ∧ (asteroids.val[i]'hi).val ≤ 1000 ∧
        (asteroids.val[i]'hi).val ≠ 0) :
    ∃ r, Aegis.AsteroidCollision.asteroid_collision asteroids = ok r ∧
      ∃ idx : Fin r.val.length → Fin asteroids.val.length,
        (∀ (j k : Fin r.val.length), j < k → idx j < idx k) ∧
        (∀ j : Fin r.val.length, r.val.get j = asteroids.val.get (idx j)) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (asteroids : Slice Aeneas.Std.I64)
    (hlen : 2 ≤ asteroids.val.length) (hlen_max : asteroids.val.length ≤ 10000)
    (hvals : ∀ (i : Nat) (hi : i < asteroids.val.length),
      -1000 ≤ (asteroids.val[i]'hi).val ∧ (asteroids.val[i]'hi).val ≤ 1000 ∧
        (asteroids.val[i]'hi).val ≠ 0), ∃ r, Aegis.AsteroidCollision.asteroid_collision asteroids = ok r ∧
      ∃ idx : Fin r.val.length → Fin asteroids.val.length,
        (∀ (j k : Fin r.val.length), j < k → idx j < idx k) ∧
        (∀ j : Fin r.val.length, r.val.get j = asteroids.val.get (idx j))) := by
  sorry

/-- The function returns a result r and there exists an integer k with 0 <= k <= len(r) such that for every j with 0 <= j < k, r[j] < 0, and for every j with k <= j < len(r), r[j] > 0.
  Preconditions: 2 <= len(asteroids) <= 10000; for every i with 0 <= i < len(asteroids), -1000 <= asteroids[i] <= 1000 and asteroids[i] != 0. -/
theorem spec_6 (asteroids : Slice Aeneas.Std.I64)
    (hlen : 2 ≤ asteroids.val.length) (hlen_max : asteroids.val.length ≤ 10000)
    (hvals : ∀ (i : Nat) (hi : i < asteroids.val.length),
      -1000 ≤ (asteroids.val[i]'hi).val ∧ (asteroids.val[i]'hi).val ≤ 1000 ∧
        (asteroids.val[i]'hi).val ≠ 0) :
    ∃ r, Aegis.AsteroidCollision.asteroid_collision asteroids = ok r ∧ NegThenPos r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (asteroids : Slice Aeneas.Std.I64)
    (hlen : 2 ≤ asteroids.val.length) (hlen_max : asteroids.val.length ≤ 10000)
    (hvals : ∀ (i : Nat) (hi : i < asteroids.val.length),
      -1000 ≤ (asteroids.val[i]'hi).val ∧ (asteroids.val[i]'hi).val ≤ 1000 ∧
        (asteroids.val[i]'hi).val ≠ 0), ∃ r, Aegis.AsteroidCollision.asteroid_collision asteroids = ok r ∧ NegThenPos r.val) := by
  sorry

/-- The function returns a result r, len(r) >= 1, and r[0] = asteroids[0].
  Preconditions: 2 <= len(asteroids) <= 10000; for every i with 0 <= i < len(asteroids), -1000 <= asteroids[i] <= 1000 and asteroids[i] != 0; asteroids[0] < 0. -/
theorem spec_7 (asteroids : Slice Aeneas.Std.I64)
    (hlen : 2 ≤ asteroids.val.length) (hlen_max : asteroids.val.length ≤ 10000)
    (hvals : ∀ (i : Nat) (hi : i < asteroids.val.length),
      -1000 ≤ (asteroids.val[i]'hi).val ∧ (asteroids.val[i]'hi).val ≤ 1000 ∧
        (asteroids.val[i]'hi).val ≠ 0)
    (hfirst : (asteroids.val[0]'(by omega)).val < 0) :
    ∃ r, Aegis.AsteroidCollision.asteroid_collision asteroids = ok r ∧
      1 ≤ r.val.length ∧
      ∃ t : List Aeneas.Std.I64, r.val = (asteroids.val[0]'(by omega)) :: t := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (asteroids : Slice Aeneas.Std.I64)
    (hlen : 2 ≤ asteroids.val.length) (hlen_max : asteroids.val.length ≤ 10000)
    (hvals : ∀ (i : Nat) (hi : i < asteroids.val.length),
      -1000 ≤ (asteroids.val[i]'hi).val ∧ (asteroids.val[i]'hi).val ≤ 1000 ∧
        (asteroids.val[i]'hi).val ≠ 0)
    (hfirst : (asteroids.val[0]'(by omega)).val < 0), ∃ r, Aegis.AsteroidCollision.asteroid_collision asteroids = ok r ∧
      1 ≤ r.val.length ∧
      ∃ t : List Aeneas.Std.I64, r.val = (asteroids.val[0]'(by omega)) :: t) := by
  sorry

/-- The function returns a result r, len(r) >= 1, and r[len(r)-1] = asteroids[len(asteroids)-1].
  Preconditions: 2 <= len(asteroids) <= 10000; for every i with 0 <= i < len(asteroids), -1000 <= asteroids[i] <= 1000 and asteroids[i] != 0; asteroids[len(asteroids)-1] > 0. -/
theorem spec_8 (asteroids : Slice Aeneas.Std.I64)
    (hlen : 2 ≤ asteroids.val.length) (hlen_max : asteroids.val.length ≤ 10000)
    (hvals : ∀ (i : Nat) (hi : i < asteroids.val.length),
      -1000 ≤ (asteroids.val[i]'hi).val ∧ (asteroids.val[i]'hi).val ≤ 1000 ∧
        (asteroids.val[i]'hi).val ≠ 0)
    (hlast : 0 < (asteroids.val[asteroids.val.length - 1]'(by omega)).val) :
    ∃ r, Aegis.AsteroidCollision.asteroid_collision asteroids = ok r ∧
      1 ≤ r.val.length ∧
      ∃ t : List Aeneas.Std.I64,
        r.val = t ++ [asteroids.val[asteroids.val.length - 1]'(by omega)] := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (asteroids : Slice Aeneas.Std.I64)
    (hlen : 2 ≤ asteroids.val.length) (hlen_max : asteroids.val.length ≤ 10000)
    (hvals : ∀ (i : Nat) (hi : i < asteroids.val.length),
      -1000 ≤ (asteroids.val[i]'hi).val ∧ (asteroids.val[i]'hi).val ≤ 1000 ∧
        (asteroids.val[i]'hi).val ≠ 0)
    (hlast : 0 < (asteroids.val[asteroids.val.length - 1]'(by omega)).val), ∃ r, Aegis.AsteroidCollision.asteroid_collision asteroids = ok r ∧
      1 ≤ r.val.length ∧
      ∃ t : List Aeneas.Std.I64,
        r.val = t ++ [asteroids.val[asteroids.val.length - 1]'(by omega)]) := by
  sorry

/-- The function returns a result r and r = asteroids.
  Preconditions: 2 <= len(asteroids) <= 10000; for every i with 0 <= i < len(asteroids), -1000 <= asteroids[i] <= 1000 and asteroids[i] != 0; there exists k with 0 <= k <= len(asteroids) such that for every j with 0 <= j < k, asteroids[j] < 0, and for every j with k <= j < len(asteroids), asteroids[j] > 0. -/
theorem spec_9 (asteroids : Slice Aeneas.Std.I64)
    (hlen : 2 ≤ asteroids.val.length) (hlen_max : asteroids.val.length ≤ 10000)
    (hvals : ∀ (i : Nat) (hi : i < asteroids.val.length),
      -1000 ≤ (asteroids.val[i]'hi).val ∧ (asteroids.val[i]'hi).val ≤ 1000 ∧
        (asteroids.val[i]'hi).val ≠ 0)
    (hshape : NegThenPos asteroids.val) :
    ∃ r, Aegis.AsteroidCollision.asteroid_collision asteroids = ok r ∧ r.val = asteroids.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (asteroids : Slice Aeneas.Std.I64)
    (hlen : 2 ≤ asteroids.val.length) (hlen_max : asteroids.val.length ≤ 10000)
    (hvals : ∀ (i : Nat) (hi : i < asteroids.val.length),
      -1000 ≤ (asteroids.val[i]'hi).val ∧ (asteroids.val[i]'hi).val ≤ 1000 ∧
        (asteroids.val[i]'hi).val ≠ 0)
    (hshape : NegThenPos asteroids.val), ∃ r, Aegis.AsteroidCollision.asteroid_collision asteroids = ok r ∧ r.val = asteroids.val) := by
  sorry

/-- Let a = asteroids[0] and b = asteroids[1]. The function returns a result r, and: if a > 0 and b < 0 and a > -b, then len(r)=1 and r[0]=a; if a > 0 and b < 0 and a = -b, then len(r)=0; if a > 0 and b < 0 and a < -b, then len(r)=1 and r[0]=b; in all other cases len(r)=2, r[0]=a, and r[1]=b.
  Preconditions: 2 <= len(asteroids) <= 10000; for every i with 0 <= i < len(asteroids), -1000 <= asteroids[i] <= 1000 and asteroids[i] != 0; len(asteroids) = 2. -/
theorem spec_10 (asteroids : Slice Aeneas.Std.I64)
    (hlen : 2 ≤ asteroids.val.length) (hlen_max : asteroids.val.length ≤ 10000)
    (hvals : ∀ (i : Nat) (hi : i < asteroids.val.length),
      -1000 ≤ (asteroids.val[i]'hi).val ∧ (asteroids.val[i]'hi).val ≤ 1000 ∧
        (asteroids.val[i]'hi).val ≠ 0)
    (hlen_two : asteroids.val.length = 2) :
    ∃ r, Aegis.AsteroidCollision.asteroid_collision asteroids = ok r ∧
      (let a : Aeneas.Std.I64 := asteroids.val[0]'(by omega);
        let b : Aeneas.Std.I64 := asteroids.val[1]'(by omega);
        (a.val > 0 ∧ b.val < 0 ∧ -(b.val) < a.val → r.val = [a]) ∧
        (a.val > 0 ∧ b.val < 0 ∧ a.val = -(b.val) → r.val = []) ∧
        (a.val > 0 ∧ b.val < 0 ∧ a.val < -(b.val) → r.val = [b]) ∧
        (¬(a.val > 0 ∧ b.val < 0) → r.val = [a, b])) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (asteroids : Slice Aeneas.Std.I64)
    (hlen : 2 ≤ asteroids.val.length) (hlen_max : asteroids.val.length ≤ 10000)
    (hvals : ∀ (i : Nat) (hi : i < asteroids.val.length),
      -1000 ≤ (asteroids.val[i]'hi).val ∧ (asteroids.val[i]'hi).val ≤ 1000 ∧
        (asteroids.val[i]'hi).val ≠ 0)
    (hlen_two : asteroids.val.length = 2), ∃ r, Aegis.AsteroidCollision.asteroid_collision asteroids = ok r ∧
      (let a : Aeneas.Std.I64 := asteroids.val[0]'(by omega);
        let b : Aeneas.Std.I64 := asteroids.val[1]'(by omega);
        (a.val > 0 ∧ b.val < 0 ∧ -(b.val) < a.val → r.val = [a]) ∧
        (a.val > 0 ∧ b.val < 0 ∧ a.val = -(b.val) → r.val = []) ∧
        (a.val > 0 ∧ b.val < 0 ∧ a.val < -(b.val) → r.val = [b]) ∧
        (¬(a.val > 0 ∧ b.val < 0) → r.val = [a, b]))) := by
  sorry

/-- Let n = len(asteroids). The function returns a result r. If there is no index j with 1 <= j < n and asteroids[0] <= -asteroids[j], then len(r)=1 and r[0]=asteroids[0]. Otherwise let j be the least such index. If asteroids[0] = -asteroids[j], then len(r)=n-1-j and for every t with 0 <= t < len(r), r[t]=asteroids[j+1+t]. If asteroids[0] < -asteroids[j], then len(r)=n-j and for every t with 0 <= t < len(r), r[t]=asteroids[j+t].
  Preconditions: 2 <= len(asteroids) <= 10000; for every i with 0 <= i < len(asteroids), -1000 <= asteroids[i] <= 1000 and asteroids[i] != 0; asteroids[0] > 0; for every i with 1 <= i < len(asteroids), asteroids[i] < 0. -/
theorem spec_11 (asteroids : Slice Aeneas.Std.I64)
    (hlen : 2 ≤ asteroids.val.length) (hlen_max : asteroids.val.length ≤ 10000)
    (hvals : ∀ (i : Nat) (hi : i < asteroids.val.length),
      -1000 ≤ (asteroids.val[i]'hi).val ∧ (asteroids.val[i]'hi).val ≤ 1000 ∧
        (asteroids.val[i]'hi).val ≠ 0)
    (hfirst : 0 < (asteroids.val[0]'(by omega)).val)
    (hrest : ∀ (i : Nat) (hi : 1 ≤ i) (hi' : i < asteroids.val.length),
      (asteroids.val[i]'hi').val < 0) :
    ∃ r, Aegis.AsteroidCollision.asteroid_collision asteroids = ok r ∧
      (let a0 : Aeneas.Std.I64 := asteroids.val[0]'(by omega);
        (∀ (hno : ∀ (j : Nat) (hj1 : 1 ≤ j) (hj2 : j < asteroids.val.length),
            a0.val > -(asteroids.val[j]'hj2).val), r.val = [a0]) ∧
        (∀ (j : Nat) (hj1 : 1 ≤ j) (hj2 : j < asteroids.val.length)
            (hleast : ∀ (i : Nat) (hi1 : 1 ≤ i) (hi2 : i < j),
              a0.val > -(asteroids.val[i]'(by omega)).val)
            (hle : a0.val ≤ -(asteroids.val[j]'hj2).val),
          (a0.val = -(asteroids.val[j]'hj2).val → r.val = asteroids.val.drop (j + 1)) ∧
          (a0.val < -(asteroids.val[j]'hj2).val → r.val = asteroids.val.drop j))) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (asteroids : Slice Aeneas.Std.I64)
    (hlen : 2 ≤ asteroids.val.length) (hlen_max : asteroids.val.length ≤ 10000)
    (hvals : ∀ (i : Nat) (hi : i < asteroids.val.length),
      -1000 ≤ (asteroids.val[i]'hi).val ∧ (asteroids.val[i]'hi).val ≤ 1000 ∧
        (asteroids.val[i]'hi).val ≠ 0)
    (hfirst : 0 < (asteroids.val[0]'(by omega)).val)
    (hrest : ∀ (i : Nat) (hi : 1 ≤ i) (hi' : i < asteroids.val.length),
      (asteroids.val[i]'hi').val < 0), ∃ r, Aegis.AsteroidCollision.asteroid_collision asteroids = ok r ∧
      (let a0 : Aeneas.Std.I64 := asteroids.val[0]'(by omega);
        (∀ (hno : ∀ (j : Nat) (hj1 : 1 ≤ j) (hj2 : j < asteroids.val.length),
            a0.val > -(asteroids.val[j]'hj2).val), r.val = [a0]) ∧
        (∀ (j : Nat) (hj1 : 1 ≤ j) (hj2 : j < asteroids.val.length)
            (hleast : ∀ (i : Nat) (hi1 : 1 ≤ i) (hi2 : i < j),
              a0.val > -(asteroids.val[i]'(by omega)).val)
            (hle : a0.val ≤ -(asteroids.val[j]'hj2).val),
          (a0.val = -(asteroids.val[j]'hj2).val → r.val = asteroids.val.drop (j + 1)) ∧
          (a0.val < -(asteroids.val[j]'hj2).val → r.val = asteroids.val.drop j)))) := by
  sorry

/-- Let n = len(asteroids) and b = -asteroids[n-1]. The function returns a result r. If there is no index j with 0 <= j < n-1 and asteroids[j] >= b, then len(r)=1 and r[0]=asteroids[n-1]. Otherwise let j be the greatest such index. If asteroids[j] = b, then len(r)=j and for every t with 0 <= t < len(r), r[t]=asteroids[t]. If asteroids[j] > b, then len(r)=j+1 and for every t with 0 <= t < len(r), r[t]=asteroids[t].
  Preconditions: 2 <= len(asteroids) <= 10000; for every i with 0 <= i < len(asteroids), -1000 <= asteroids[i] <= 1000 and asteroids[i] != 0; asteroids[len(asteroids)-1] < 0; for every i with 0 <= i < len(asteroids)-1, asteroids[i] > 0. -/
theorem spec_12 (asteroids : Slice Aeneas.Std.I64)
    (hlen : 2 ≤ asteroids.val.length) (hlen_max : asteroids.val.length ≤ 10000)
    (hvals : ∀ (i : Nat) (hi : i < asteroids.val.length),
      -1000 ≤ (asteroids.val[i]'hi).val ∧ (asteroids.val[i]'hi).val ≤ 1000 ∧
        (asteroids.val[i]'hi).val ≠ 0)
    (hlast : (asteroids.val[asteroids.val.length - 1]'(by omega)).val < 0)
    (hpos : ∀ (i : Nat) (hi : i < asteroids.val.length - 1),
      0 < (asteroids.val[i]'(by omega)).val) :
    ∃ r, Aegis.AsteroidCollision.asteroid_collision asteroids = ok r ∧
      (let last : Aeneas.Std.I64 := asteroids.val[asteroids.val.length - 1]'(by omega);
        let b : Int := -(last.val);
        (∀ (hno : ∀ (j : Nat) (hj : j < asteroids.val.length - 1),
            (asteroids.val[j]'(by omega)).val < b), r.val = [last]) ∧
        (∀ (j : Nat) (hj : j < asteroids.val.length - 1)
            (hge : b ≤ (asteroids.val[j]'(by omega)).val)
            (hgreatest : ∀ (i : Nat) (hi : i < asteroids.val.length - 1),
              j < i → (asteroids.val[i]'(by omega)).val < b),
          ((asteroids.val[j]'(by omega)).val = b → r.val = asteroids.val.take j) ∧
          (b < (asteroids.val[j]'(by omega)).val → r.val = asteroids.val.take (j + 1)))) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (asteroids : Slice Aeneas.Std.I64)
    (hlen : 2 ≤ asteroids.val.length) (hlen_max : asteroids.val.length ≤ 10000)
    (hvals : ∀ (i : Nat) (hi : i < asteroids.val.length),
      -1000 ≤ (asteroids.val[i]'hi).val ∧ (asteroids.val[i]'hi).val ≤ 1000 ∧
        (asteroids.val[i]'hi).val ≠ 0)
    (hlast : (asteroids.val[asteroids.val.length - 1]'(by omega)).val < 0)
    (hpos : ∀ (i : Nat) (hi : i < asteroids.val.length - 1),
      0 < (asteroids.val[i]'(by omega)).val), ∃ r, Aegis.AsteroidCollision.asteroid_collision asteroids = ok r ∧
      (let last : Aeneas.Std.I64 := asteroids.val[asteroids.val.length - 1]'(by omega);
        let b : Int := -(last.val);
        (∀ (hno : ∀ (j : Nat) (hj : j < asteroids.val.length - 1),
            (asteroids.val[j]'(by omega)).val < b), r.val = [last]) ∧
        (∀ (j : Nat) (hj : j < asteroids.val.length - 1)
            (hge : b ≤ (asteroids.val[j]'(by omega)).val)
            (hgreatest : ∀ (i : Nat) (hi : i < asteroids.val.length - 1),
              j < i → (asteroids.val[i]'(by omega)).val < b),
          ((asteroids.val[j]'(by omega)).val = b → r.val = asteroids.val.take j) ∧
          (b < (asteroids.val[j]'(by omega)).val → r.val = asteroids.val.take (j + 1))))) := by
  sorry

end AegisSpec.AsteroidCollision
