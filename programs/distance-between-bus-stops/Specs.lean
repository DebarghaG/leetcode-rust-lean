import Aegis.DistanceBetweenBusStops.Code.Funs

/-!
# Specifications of `Aegis.DistanceBetweenBusStops.distance_between_bus_stops`

LeetCode problem `distance-between-bus-stops`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.DistanceBetweenBusStops

open Aegis.DistanceBetweenBusStops (distance_between_bus_stops)

def vals (distance : Slice Std.I64) : List ℤ := distance.val.map (fun x => x.val)

def len (distance : Slice Std.I64) : ℕ := distance.val.length

def elem (distance : Slice Std.I64) (i : ℕ) : ℤ := (vals distance).getD i 0

def idx (x : Std.I64) : ℕ := x.val.toNat

def subMod (a b n : ℕ) : ℕ := (a + n - b) % n

def negMod (a n : ℕ) : ℕ := (n - a % n) % n

def i64OfNat (m : ℕ) : Std.I64 := IScalar.mk (BitVec.ofNat 64 m)

theorem i64OfNat_val (m : ℕ) (h : m < 2 ^ 63) : (i64OfNat m).val = (m : ℤ) := by
  have h1 : (BitVec.ofNat 64 m).toInt = ((m : ℤ)).bmod (2 ^ 64) := BitVec.toInt_ofNat m
  rw [show (i64OfNat m).val = (BitVec.ofNat 64 m).toInt from rfl, h1, Int.bmod_def]
  simp
  omega

def total (distance : Slice Std.I64) : ℤ := (vals distance).sum

def dIdx (distance : Slice Std.I64) (start destination : Std.I64) : ℕ :=
  subMod (idx destination) (idx start) (len distance)

def cw (distance : Slice Std.I64) (start destination : Std.I64) : ℤ :=
  ((List.range (dIdx distance start destination)).map
      (fun k => elem distance ((idx start + k) % len distance))).sum

def ccw (distance : Slice Std.I64) (start destination : Std.I64) : ℤ :=
  total distance - cw distance start destination

def rotateVal (distance : Slice Std.I64) (c : ℕ) : List Std.I64 :=
  (List.range (len distance)).map
    (fun i => distance.val.getD ((i + c) % len distance) default)

def rotate (distance : Slice Std.I64) (c : ℕ) : Slice Std.I64 :=
  ⟨(rotateVal distance c).length, Aeneas.Data.ListN.ListN.fromList (rotateVal distance c), by
    have hlen : (rotateVal distance c).length = distance.leng := by
      rw [rotateVal, List.length_map, List.length_range]
      exact Aeneas.Data.ListN.ListN_length distance.list
    rw [hlen]
    exact distance.bound⟩

theorem rotate_val (distance : Slice Std.I64) (c : ℕ) :
    (rotate distance c).val = rotateVal distance c := by
  simp [rotate, Aeneas.Std.Slice.val, Aeneas.Data.ListN.ListN.from_to_inverse]

def shiftIdx (distance : Slice Std.I64) (x : Std.I64) (c : ℕ) : Std.I64 :=
  i64OfNat (subMod (idx x) c (len distance))

def reverseVal (distance : Slice Std.I64) : List Std.I64 :=
  (List.range (len distance)).map
    (fun i => distance.val.getD ((len distance - 1 - i) % len distance) default)

def reverse (distance : Slice Std.I64) : Slice Std.I64 :=
  ⟨(reverseVal distance).length, Aeneas.Data.ListN.ListN.fromList (reverseVal distance), by
    have hlen : (reverseVal distance).length = distance.leng := by
      rw [reverseVal, List.length_map, List.length_range]
      exact Aeneas.Data.ListN.ListN_length distance.list
    rw [hlen]
    exact distance.bound⟩

theorem reverse_val (distance : Slice Std.I64) :
    (reverse distance).val = reverseVal distance := by
  simp [reverse, Aeneas.Std.Slice.val, Aeneas.Data.ListN.ListN.from_to_inverse]

def revIdx (distance : Slice Std.I64) (x : Std.I64) : Std.I64 :=
  i64OfNat (negMod (idx x) (len distance))

def Pre (distance : Slice Std.I64) (start destination : Std.I64) : Prop :=
  1 ≤ len distance ∧
  len distance ≤ 10000 ∧
  (∀ i : ℕ, i < len distance → 0 ≤ elem distance i ∧ elem distance i ≤ 10000) ∧
  0 ≤ start.val ∧ start.val < (len distance : ℤ) ∧
  0 ≤ destination.val ∧ destination.val < (len distance : ℤ)

/-- Let n = len(distance). Let total = sum_{i=0}^{n-1} distance[i]. Let d = (destination - start) mod n, taken in [0,n). Let cw = sum_{k=0}^{d-1} distance[(start + k) mod n], with cw = 0 when d = 0. The function returns a result r and r = min(cw, total - cw).
  Preconditions: Let n = len(distance). Assume 1 <= n <= 10000; for every i with 0 <= i < n, 0 <= distance[i] <= 10000; and 0 <= start < n and 0 <= destination < n. (distance is a slice of 64-bit integers; start and destination are 64-bit integer indices.) -/
theorem spec_1 (distance : Slice Std.I64) (start destination : Std.I64)
    (h : Pre distance start destination) :
    ∃ r, distance_between_bus_stops distance start destination = ok r ∧
      r.val = min (cw distance start destination) (ccw distance start destination) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (distance : Slice Std.I64) (start destination : Std.I64)
    (h : Pre distance start destination), ∃ r, distance_between_bus_stops distance start destination = ok r ∧
      r.val = min (cw distance start destination) (ccw distance start destination)) := by
  sorry

/-- The function returns some result r (it does not fail due to arithmetic overflow, out-of-bounds indexing, or panic).
  Preconditions: Let n = len(distance). Assume 1 <= n <= 10000; for every i with 0 <= i < n, 0 <= distance[i] <= 10000; and 0 <= start < n and 0 <= destination < n. (distance is a slice of 64-bit integers; start and destination are 64-bit integer indices.) -/
theorem spec_2 (distance : Slice Std.I64) (start destination : Std.I64)
    (h : Pre distance start destination) :
    ∃ r, distance_between_bus_stops distance start destination = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (distance : Slice Std.I64) (start destination : Std.I64)
    (h : Pre distance start destination), ∃ r, distance_between_bus_stops distance start destination = ok r) := by
  sorry

/-- Whenever the function returns a result r, r >= 0.
  Preconditions: Let n = len(distance). Assume 1 <= n <= 10000; for every i with 0 <= i < n, 0 <= distance[i] <= 10000; and 0 <= start < n and 0 <= destination < n. (distance is a slice of 64-bit integers; start and destination are 64-bit integer indices.) -/
theorem spec_3 (distance : Slice Std.I64) (start destination : Std.I64)
    (h : Pre distance start destination) :
    ∀ r, distance_between_bus_stops distance start destination = ok r → 0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (distance : Slice Std.I64) (start destination : Std.I64)
    (h : Pre distance start destination), ∀ r, distance_between_bus_stops distance start destination = ok r → 0 ≤ r.val) := by
  sorry

/-- Let n = len(distance) and total = sum_{i=0}^{n-1} distance[i]. Whenever the function returns a result r, 2*r <= total.
  Preconditions: Let n = len(distance). Assume 1 <= n <= 10000; for every i with 0 <= i < n, 0 <= distance[i] <= 10000; and 0 <= start < n and 0 <= destination < n. (distance is a slice of 64-bit integers; start and destination are 64-bit integer indices.) -/
theorem spec_4 (distance : Slice Std.I64) (start destination : Std.I64)
    (h : Pre distance start destination) :
    ∀ r, distance_between_bus_stops distance start destination = ok r →
      2 * r.val ≤ total distance := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (distance : Slice Std.I64) (start destination : Std.I64)
    (h : Pre distance start destination), ∀ r, distance_between_bus_stops distance start destination = ok r →
      2 * r.val ≤ total distance) := by
  sorry

/-- Let n = len(distance). Let d = (destination - start) mod n, taken in [0,n). Let cw = sum_{k=0}^{d-1} distance[(start + k) mod n], with cw = 0 when d = 0. Whenever the function returns a result r, r <= cw.
  Preconditions: Let n = len(distance). Assume 1 <= n <= 10000; for every i with 0 <= i < n, 0 <= distance[i] <= 10000; and 0 <= start < n and 0 <= destination < n. (distance is a slice of 64-bit integers; start and destination are 64-bit integer indices.) -/
theorem spec_5 (distance : Slice Std.I64) (start destination : Std.I64)
    (h : Pre distance start destination) :
    ∀ r, distance_between_bus_stops distance start destination = ok r →
      r.val ≤ cw distance start destination := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (distance : Slice Std.I64) (start destination : Std.I64)
    (h : Pre distance start destination), ∀ r, distance_between_bus_stops distance start destination = ok r →
      r.val ≤ cw distance start destination) := by
  sorry

/-- Let n = len(distance). Let total = sum_{i=0}^{n-1} distance[i]. Let d = (destination - start) mod n, taken in [0,n). Let cw = sum_{k=0}^{d-1} distance[(start + k) mod n], with cw = 0 when d = 0. Whenever the function returns a result r, r <= total - cw.
  Preconditions: Let n = len(distance). Assume 1 <= n <= 10000; for every i with 0 <= i < n, 0 <= distance[i] <= 10000; and 0 <= start < n and 0 <= destination < n. (distance is a slice of 64-bit integers; start and destination are 64-bit integer indices.) -/
theorem spec_6 (distance : Slice Std.I64) (start destination : Std.I64)
    (h : Pre distance start destination) :
    ∀ r, distance_between_bus_stops distance start destination = ok r →
      r.val ≤ total distance - cw distance start destination := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (distance : Slice Std.I64) (start destination : Std.I64)
    (h : Pre distance start destination), ∀ r, distance_between_bus_stops distance start destination = ok r →
      r.val ≤ total distance - cw distance start destination) := by
  sorry

/-- For every distance, start, destination satisfying the preconditions, if the function returns r for (distance, start, destination) and returns r' for (distance, destination, start), then r = r'.
  Preconditions: Let n = len(distance). Assume 1 <= n <= 10000; for every i with 0 <= i < n, 0 <= distance[i] <= 10000; and 0 <= start < n and 0 <= destination < n. (distance is a slice of 64-bit integers; start and destination are 64-bit integer indices.) -/
theorem spec_7 (distance : Slice Std.I64) (start destination : Std.I64)
    (h : Pre distance start destination) (r r' : Std.I64)
    (hr : distance_between_bus_stops distance start destination = ok r)
    (hr' : distance_between_bus_stops distance destination start = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (distance : Slice Std.I64) (start destination : Std.I64)
    (h : Pre distance start destination) (r r' : Std.I64)
    (hr : distance_between_bus_stops distance start destination = ok r)
    (hr' : distance_between_bus_stops distance destination start = ok r'), r.val = r'.val) := by
  sorry

/-- For every integer c with 0 <= c < n, define distance_c[i] = distance[(i + c) mod n] for 0 <= i < n, start_c = (start - c) mod n, and destination_c = (destination - c) mod n, where mod n yields the representative in [0,n). If the function returns r for (distance, start, destination) and returns r_c for (distance_c, start_c, destination_c), then r = r_c.
  Preconditions: Let n = len(distance). Assume 1 <= n <= 10000; for every i with 0 <= i < n, 0 <= distance[i] <= 10000; and 0 <= start < n and 0 <= destination < n. (distance is a slice of 64-bit integers; start and destination are 64-bit integer indices.) -/
theorem spec_8 (distance : Slice Std.I64) (start destination : Std.I64) (c : ℕ)
    (h : Pre distance start destination) (hc : c < len distance)
    (r r_c : Std.I64)
    (hr : distance_between_bus_stops distance start destination = ok r)
    (hrc : distance_between_bus_stops (rotate distance c) (shiftIdx distance start c)
        (shiftIdx distance destination c) = ok r_c) :
    r.val = r_c.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (distance : Slice Std.I64) (start destination : Std.I64) (c : ℕ)
    (h : Pre distance start destination) (hc : c < len distance)
    (r r_c : Std.I64)
    (hr : distance_between_bus_stops distance start destination = ok r)
    (hrc : distance_between_bus_stops (rotate distance c) (shiftIdx distance start c)
        (shiftIdx distance destination c) = ok r_c), r.val = r_c.val) := by
  sorry

/-- Define distance_rev[i] = distance[(n - 1 - i) mod n] for 0 <= i < n, start_rev = (-start) mod n, and destination_rev = (-destination) mod n, where mod n yields the representative in [0,n). If the function returns r for (distance, start, destination) and returns r_rev for (distance_rev, start_rev, destination_rev), then r = r_rev.
  Preconditions: Let n = len(distance). Assume 1 <= n <= 10000; for every i with 0 <= i < n, 0 <= distance[i] <= 10000; and 0 <= start < n and 0 <= destination < n. (distance is a slice of 64-bit integers; start and destination are 64-bit integer indices.) -/
theorem spec_9 (distance : Slice Std.I64) (start destination : Std.I64)
    (h : Pre distance start destination) (r r_rev : Std.I64)
    (hr : distance_between_bus_stops distance start destination = ok r)
    (hrr : distance_between_bus_stops (reverse distance) (revIdx distance start)
        (revIdx distance destination) = ok r_rev) :
    r.val = r_rev.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (distance : Slice Std.I64) (start destination : Std.I64)
    (h : Pre distance start destination) (r r_rev : Std.I64)
    (hr : distance_between_bus_stops distance start destination = ok r)
    (hrr : distance_between_bus_stops (reverse distance) (revIdx distance start)
        (revIdx distance destination) = ok r_rev), r.val = r_rev.val) := by
  sorry

/-- Let distance1 and distance2 be slices of the same length n, both satisfying the preconditions (with the same n, start, and destination). If for every i with 0 <= i < n, distance1[i] <= distance2[i], and the function returns r1 for (distance1, start, destination) and r2 for (distance2, start, destination), then r1 <= r2.
  Preconditions: Let n = len(distance). Assume 1 <= n <= 10000; for every i with 0 <= i < n, 0 <= distance[i] <= 10000; and 0 <= start < n and 0 <= destination < n. (distance is a slice of 64-bit integers; start and destination are 64-bit integer indices.) -/
theorem spec_10 (distance1 distance2 : Slice Std.I64) (start destination : Std.I64)
    (h1 : Pre distance1 start destination) (h2 : Pre distance2 start destination)
    (hlen : len distance1 = len distance2)
    (hle : ∀ i : ℕ, i < len distance1 → elem distance1 i ≤ elem distance2 i)
    (r1 r2 : Std.I64)
    (hr1 : distance_between_bus_stops distance1 start destination = ok r1)
    (hr2 : distance_between_bus_stops distance2 start destination = ok r2) :
    r1.val ≤ r2.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (distance1 distance2 : Slice Std.I64) (start destination : Std.I64)
    (h1 : Pre distance1 start destination) (h2 : Pre distance2 start destination)
    (hlen : len distance1 = len distance2)
    (hle : ∀ i : ℕ, i < len distance1 → elem distance1 i ≤ elem distance2 i)
    (r1 r2 : Std.I64)
    (hr1 : distance_between_bus_stops distance1 start destination = ok r1)
    (hr2 : distance_between_bus_stops distance2 start destination = ok r2), r1.val ≤ r2.val) := by
  sorry

/-- Let n = len(distance). Let total = sum_{i=0}^{n-1} distance[i]. Let d = (destination - start) mod n, taken in [0,n). Let cw = sum_{k=0}^{d-1} distance[(start + k) mod n], with cw = 0 when d = 0. Whenever the function returns a result r, either r = cw or r = total - cw.
  Preconditions: Let n = len(distance). Assume 1 <= n <= 10000; for every i with 0 <= i < n, 0 <= distance[i] <= 10000; and 0 <= start < n and 0 <= destination < n. (distance is a slice of 64-bit integers; start and destination are 64-bit integer indices.) -/
theorem spec_11 (distance : Slice Std.I64) (start destination : Std.I64)
    (h : Pre distance start destination) :
    ∀ r, distance_between_bus_stops distance start destination = ok r →
      r.val = cw distance start destination ∨
        r.val = total distance - cw distance start destination := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (distance : Slice Std.I64) (start destination : Std.I64)
    (h : Pre distance start destination), ∀ r, distance_between_bus_stops distance start destination = ok r →
      r.val = cw distance start destination ∨
        r.val = total distance - cw distance start destination) := by
  sorry

end AegisSpec.DistanceBetweenBusStops
