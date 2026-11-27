import Aegis.CountCollisions.Code.Funs

/-!
# Specifications of `Aegis.CountCollisions.count_collisions`

LeetCode problem `count-collisions-on-a-road`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.CountCollisions

  def byteL : Aeneas.Std.U8 := ⟨BitVec.ofNat 8 76⟩

  def byteR : Aeneas.Std.U8 := ⟨BitVec.ofNat 8 82⟩

  def byteS : Aeneas.Std.U8 := ⟨BitVec.ofNat 8 83⟩

  def isL (b : Aeneas.Std.U8) : Bool := b.val == 76

  def isR (b : Aeneas.Std.U8) : Bool := b.val == 82

  def isS (b : Aeneas.Std.U8) : Bool := b.val == 83

  def Pre (l : List Aeneas.Std.U8) : Prop :=
  1 ≤ l.length ∧ l.length ≤ 100000 ∧ ∀ b ∈ l, isL b = true ∨ isR b = true ∨ isS b = true

  def NoS (l : List Aeneas.Std.U8) : Prop := ∀ b ∈ l, isS b = false

  def countIf (p : Aeneas.Std.U8 → Bool) (l : List Aeneas.Std.U8) : ℕ := (l.filter p).length

  def countRange (l : List Aeneas.Std.U8) (start stop : ℕ) (p : Aeneas.Std.U8 → Bool) : ℕ :=
  countIf p ((l.drop start).take (stop - start))

  def firstIdx (p : Aeneas.Std.U8 → Bool) : List Aeneas.Std.U8 → ℕ
    | [] => 0
    | b :: rest => if p b then 0 else firstIdx p rest + 1

  def endIdx (p : Aeneas.Std.U8 → Bool) : List Aeneas.Std.U8 → ℕ
    | [] => 0
    | b :: rest => if endIdx p rest = 0 then (if p b then 1 else 0) else endIdx p rest + 1

  def firstNonL (l : List Aeneas.Std.U8) : ℕ := firstIdx (fun b => !isL b) l

  def endNonR (l : List Aeneas.Std.U8) : ℕ := endIdx (fun b => !isR b) l

  def trimmedMoves (l : List Aeneas.Std.U8) : ℕ :=
  countRange l (firstNonL l) (endNonR l) (fun b => !isS b)

  def countNotS (l : List Aeneas.Std.U8) : ℕ := countIf (fun b => !isS b) l

  def firstR (l : List Aeneas.Std.U8) : ℕ := firstIdx isR l

  def lastL (l : List Aeneas.Std.U8) : ℤ := (endIdx isL l : ℤ) - 1

  def firstS (l : List Aeneas.Std.U8) : ℕ := firstIdx isS l

  def lastS (l : List Aeneas.Std.U8) : ℤ := (endIdx isS l : ℤ) - 1

  def endS (l : List Aeneas.Std.U8) : ℕ := endIdx isS l

  def IsLSR (l : List Aeneas.Std.U8) : Prop :=
  ∃ a b c : ℕ,
    l = List.replicate a byteL ++ List.replicate b byteS ++ List.replicate c byteR

  /-- Let first be the least index i such that 0 <= i < n and directions[i] != 'L', or n if no such index exists. Let last be the greatest index i such that 0 <= i < n and directions[i] != 'R', or -1 if no such index exists. Whenever the function returns a result r, r is exactly the number of indices i with first <= i <= last and directions[i] != 'S'. Equivalently, r is the number of moving cars (direction 'L' or 'R') that remain after deleting every leading 'L' and every trailing 'R' from directions.
    Preconditions: Let n = len(directions). The input satisfies 1 <= n <= 100000 and, for every i with 0 <= i < n, directions[i] is one of the ASCII bytes 'L' (76), 'R' (82), or 'S' (83). -/
  theorem spec_1 (directions : Aeneas.Std.Slice Aeneas.Std.U8)
      (hpre : Pre directions.val) :
      ∀ r : Aeneas.Std.I64,
        Aegis.CountCollisions.count_collisions directions = ok r →
          r.val = (trimmedMoves directions.val : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (directions : Aeneas.Std.Slice Aeneas.Std.U8)
        (hpre : Pre directions.val), ∀ r : Aeneas.Std.I64,
          Aegis.CountCollisions.count_collisions directions = ok r →
            r.val = (trimmedMoves directions.val : ℤ)) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r; that is, it does not panic, access memory out of bounds, or overflow.
    Preconditions: Let n = len(directions). The input satisfies 1 <= n <= 100000 and, for every i with 0 <= i < n, directions[i] is one of the ASCII bytes 'L' (76), 'R' (82), or 'S' (83). -/
  theorem spec_2 (directions : Aeneas.Std.Slice Aeneas.Std.U8)
      (hpre : Pre directions.val) :
      ∃ r : Aeneas.Std.I64, Aegis.CountCollisions.count_collisions directions = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (directions : Aeneas.Std.Slice Aeneas.Std.U8)
        (hpre : Pre directions.val), ∃ r : Aeneas.Std.I64, Aegis.CountCollisions.count_collisions directions = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r <= the number of indices i with 0 <= i < n and directions[i] != 'S'.
    Preconditions: Let n = len(directions). The input satisfies 1 <= n <= 100000 and, for every i with 0 <= i < n, directions[i] is one of the ASCII bytes 'L' (76), 'R' (82), or 'S' (83). -/
  theorem spec_3 (directions : Aeneas.Std.Slice Aeneas.Std.U8)
      (hpre : Pre directions.val) :
      ∀ r : Aeneas.Std.I64,
        Aegis.CountCollisions.count_collisions directions = ok r →
          0 ≤ r.val ∧ r.val ≤ (countNotS directions.val : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (directions : Aeneas.Std.Slice Aeneas.Std.U8)
        (hpre : Pre directions.val), ∀ r : Aeneas.Std.I64,
          Aegis.CountCollisions.count_collisions directions = ok r →
            0 ≤ r.val ∧ r.val ≤ (countNotS directions.val : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 if and only if directions has the form L^a S^b R^c for some non-negative integers a, b, c with a + b + c = n; that is, the first a bytes are 'L', the next b bytes are 'S', and the final c bytes are 'R'.
    Preconditions: Let n = len(directions). The input satisfies 1 <= n <= 100000 and, for every i with 0 <= i < n, directions[i] is one of the ASCII bytes 'L' (76), 'R' (82), or 'S' (83). -/
  theorem spec_4 (directions : Aeneas.Std.Slice Aeneas.Std.U8)
      (hpre : Pre directions.val) :
      ∀ r : Aeneas.Std.I64,
        Aegis.CountCollisions.count_collisions directions = ok r →
          (r.val = 0 ↔ IsLSR directions.val) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (directions : Aeneas.Std.Slice Aeneas.Std.U8)
        (hpre : Pre directions.val), ∀ r : Aeneas.Std.I64,
          Aegis.CountCollisions.count_collisions directions = ok r →
            (r.val = 0 ↔ IsLSR directions.val)) := by
    sorry

  /-- Let firstR be the least index i with directions[i] = 'R', or n if no such index exists, and let lastL be the greatest index i with directions[i] = 'L', or -1 if no such index exists. Whenever the function returns a result r, r = max(0, lastL - firstR + 1).
    Preconditions: Let n = len(directions). The input satisfies 1 <= n <= 100000 and, for every i with 0 <= i < n, directions[i] is one of the ASCII bytes 'L' (76), 'R' (82), or 'S' (83). Additionally, directions[i] != 'S' for every i with 0 <= i < n. -/
  theorem spec_5 (directions : Aeneas.Std.Slice Aeneas.Std.U8)
      (hpre : Pre directions.val)
      (hnoS : ∀ b ∈ directions.val, isS b = false) :
      ∀ r : Aeneas.Std.I64,
        Aegis.CountCollisions.count_collisions directions = ok r →
          r.val = max 0 (lastL directions.val - (firstR directions.val : ℤ) + 1) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (directions : Aeneas.Std.Slice Aeneas.Std.U8)
        (hpre : Pre directions.val)
        (hnoS : ∀ b ∈ directions.val, isS b = false), ∀ r : Aeneas.Std.I64,
          Aegis.CountCollisions.count_collisions directions = ok r →
            r.val = max 0 (lastL directions.val - (firstR directions.val : ℤ) + 1)) := by
    sorry

  /-- If there is no index i with directions[i] = 'S', then whenever the function returns a result r, r = 0. Otherwise, let p be the least index with directions[p] = 'S'; then whenever the function returns a result r, r is the number of indices i with p < i < n and directions[i] = 'L'.
    Preconditions: Let n = len(directions). The input satisfies 1 <= n <= 100000 and, for every i with 0 <= i < n, directions[i] is one of the ASCII bytes 'L' (76), 'R' (82), or 'S' (83). Additionally, directions[i] != 'R' for every i with 0 <= i < n. -/
  theorem spec_6 (directions : Aeneas.Std.Slice Aeneas.Std.U8)
      (hpre : Pre directions.val)
      (hnoR : ∀ b ∈ directions.val, isR b = false) :
      (NoS directions.val →
          ∀ r : Aeneas.Std.I64,
            Aegis.CountCollisions.count_collisions directions = ok r → r.val = 0) ∧
        (¬ NoS directions.val →
          ∀ r : Aeneas.Std.I64,
            Aegis.CountCollisions.count_collisions directions = ok r →
              r.val = (countRange directions.val (firstS directions.val + 1)
                directions.val.length isL : ℤ)) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (directions : Aeneas.Std.Slice Aeneas.Std.U8)
        (hpre : Pre directions.val)
        (hnoR : ∀ b ∈ directions.val, isR b = false), (NoS directions.val →
            ∀ r : Aeneas.Std.I64,
              Aegis.CountCollisions.count_collisions directions = ok r → r.val = 0) ∧
          (¬ NoS directions.val →
            ∀ r : Aeneas.Std.I64,
              Aegis.CountCollisions.count_collisions directions = ok r →
                r.val = (countRange directions.val (firstS directions.val + 1)
                  directions.val.length isL : ℤ))) := by
    sorry

  /-- If there is no index i with directions[i] = 'S', then whenever the function returns a result r, r = 0. Otherwise, let q be the greatest index with directions[q] = 'S'; then whenever the function returns a result r, r is the number of indices i with 0 <= i < q and directions[i] = 'R'.
    Preconditions: Let n = len(directions). The input satisfies 1 <= n <= 100000 and, for every i with 0 <= i < n, directions[i] is one of the ASCII bytes 'L' (76), 'R' (82), or 'S' (83). Additionally, directions[i] != 'L' for every i with 0 <= i < n. -/
  theorem spec_7 (directions : Aeneas.Std.Slice Aeneas.Std.U8)
      (hpre : Pre directions.val)
      (hnoL : ∀ b ∈ directions.val, isL b = false) :
      (NoS directions.val →
          ∀ r : Aeneas.Std.I64,
            Aegis.CountCollisions.count_collisions directions = ok r → r.val = 0) ∧
        (¬ NoS directions.val →
          ∀ r : Aeneas.Std.I64,
            Aegis.CountCollisions.count_collisions directions = ok r →
              r.val = (countRange directions.val 0 (endS directions.val - 1) isR : ℤ)) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (directions : Aeneas.Std.Slice Aeneas.Std.U8)
        (hpre : Pre directions.val)
        (hnoL : ∀ b ∈ directions.val, isL b = false), (NoS directions.val →
            ∀ r : Aeneas.Std.I64,
              Aegis.CountCollisions.count_collisions directions = ok r → r.val = 0) ∧
          (¬ NoS directions.val →
            ∀ r : Aeneas.Std.I64,
              Aegis.CountCollisions.count_collisions directions = ok r →
                r.val = (countRange directions.val 0 (endS directions.val - 1) isR : ℤ))) := by
    sorry

  /-- Whenever the function returns a result r, if there exist indices i and j with 0 <= i < j < n, directions[i] = 'R', and directions[j] = 'L', then r >= 2.
    Preconditions: Let n = len(directions). The input satisfies 1 <= n <= 100000 and, for every i with 0 <= i < n, directions[i] is one of the ASCII bytes 'L' (76), 'R' (82), or 'S' (83). -/
  theorem spec_8 (directions : Aeneas.Std.Slice Aeneas.Std.U8)
      (hpre : Pre directions.val) :
      ∀ r : Aeneas.Std.I64,
        Aegis.CountCollisions.count_collisions directions = ok r →
          ((∃ i j : ℕ, i < j ∧ j < directions.val.length ∧
              directions.val[i]? = some byteR ∧ directions.val[j]? = some byteL) →
            2 ≤ r.val) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (directions : Aeneas.Std.Slice Aeneas.Std.U8)
        (hpre : Pre directions.val), ∀ r : Aeneas.Std.I64,
          Aegis.CountCollisions.count_collisions directions = ok r →
            ((∃ i j : ℕ, i < j ∧ j < directions.val.length ∧
                directions.val[i]? = some byteR ∧ directions.val[j]? = some byteL) →
              2 ≤ r.val)) := by
    sorry

  /-- Whenever the function returns a result r, if there exist indices i and j with 0 <= i < j < n, directions[i] = 'S', and directions[j] = 'L', then r >= 1.
    Preconditions: Let n = len(directions). The input satisfies 1 <= n <= 100000 and, for every i with 0 <= i < n, directions[i] is one of the ASCII bytes 'L' (76), 'R' (82), or 'S' (83). -/
  theorem spec_9 (directions : Aeneas.Std.Slice Aeneas.Std.U8)
      (hpre : Pre directions.val) :
      ∀ r : Aeneas.Std.I64,
        Aegis.CountCollisions.count_collisions directions = ok r →
          ((∃ i j : ℕ, i < j ∧ j < directions.val.length ∧
              directions.val[i]? = some byteS ∧ directions.val[j]? = some byteL) →
            1 ≤ r.val) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (directions : Aeneas.Std.Slice Aeneas.Std.U8)
        (hpre : Pre directions.val), ∀ r : Aeneas.Std.I64,
          Aegis.CountCollisions.count_collisions directions = ok r →
            ((∃ i j : ℕ, i < j ∧ j < directions.val.length ∧
                directions.val[i]? = some byteS ∧ directions.val[j]? = some byteL) →
              1 ≤ r.val)) := by
    sorry

  /-- Whenever the function returns a result r, if there exist indices i and j with 0 <= i < j < n, directions[i] = 'R', and directions[j] = 'S', then r >= 1.
    Preconditions: Let n = len(directions). The input satisfies 1 <= n <= 100000 and, for every i with 0 <= i < n, directions[i] is one of the ASCII bytes 'L' (76), 'R' (82), or 'S' (83). -/
  theorem spec_10 (directions : Aeneas.Std.Slice Aeneas.Std.U8)
      (hpre : Pre directions.val) :
      ∀ r : Aeneas.Std.I64,
        Aegis.CountCollisions.count_collisions directions = ok r →
          ((∃ i j : ℕ, i < j ∧ j < directions.val.length ∧
              directions.val[i]? = some byteR ∧ directions.val[j]? = some byteS) →
            1 ≤ r.val) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (directions : Aeneas.Std.Slice Aeneas.Std.U8)
        (hpre : Pre directions.val), ∀ r : Aeneas.Std.I64,
          Aegis.CountCollisions.count_collisions directions = ok r →
            ((∃ i j : ℕ, i < j ∧ j < directions.val.length ∧
                directions.val[i]? = some byteR ∧ directions.val[j]? = some byteS) →
              1 ≤ r.val)) := by
    sorry

  /-- Whenever the function returns r on directions and r' on d', r' = r.
    Preconditions: Let n = len(directions). The input satisfies 1 <= n <= 100000 and, for every i with 0 <= i < n, directions[i] is one of the ASCII bytes 'L' (76), 'R' (82), or 'S' (83). Let k >= 0 be an integer with k + n <= 100000, and let d' be the byte string of length k + n obtained by writing k copies of 'L' followed by directions. -/
  theorem spec_11 (directions d' : Aeneas.Std.Slice Aeneas.Std.U8) (k : ℕ)
      (hpre : Pre directions.val)
      (hk : k + directions.val.length ≤ 100000)
      (hd' : d'.val = List.replicate k byteL ++ directions.val) :
      ∀ r r' : Aeneas.Std.I64,
        Aegis.CountCollisions.count_collisions directions = ok r →
          Aegis.CountCollisions.count_collisions d' = ok r' → r' = r := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (directions d' : Aeneas.Std.Slice Aeneas.Std.U8) (k : ℕ)
        (hpre : Pre directions.val)
        (hk : k + directions.val.length ≤ 100000)
        (hd' : d'.val = List.replicate k byteL ++ directions.val), ∀ r r' : Aeneas.Std.I64,
          Aegis.CountCollisions.count_collisions directions = ok r →
            Aegis.CountCollisions.count_collisions d' = ok r' → r' = r) := by
    sorry

  end AegisSpec.CountCollisions
