import Aegis.MaxNumberOfFamilies.Code.Funs

/-!
# Specifications of `Aegis.MaxNumberOfFamilies.max_number_of_families`

LeetCode problem `cinema-seat-allocation`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxNumberOfFamilies

def pairOf (v : alloc.vec.Vec Std.I64) : Option (ℤ × ℤ) :=
  match v.val with
  | [r, s] => some (r.val, s.val)
  | _ => none

def reservedPairs (reservedSeats : Slice (alloc.vec.Vec Std.I64)) : List (ℤ × ℤ) :=
  reservedSeats.val.filterMap pairOf

def IsReserved (reservedSeats : Slice (alloc.vec.Vec Std.I64)) (t c : ℤ) : Prop :=
  (t, c) ∈ reservedPairs reservedSeats

inductive Block
  | L
  | M
  | R
  deriving DecidableEq

namespace Block

def seats : Block → List ℤ
  | L => [2, 3, 4, 5]
  | M => [4, 5, 6, 7]
  | R => [6, 7, 8, 9]

end Block

def blockFree (rp : List (ℤ × ℤ)) (t : ℤ) (b : Block) : Prop :=
  ∀ c ∈ b.seats, (t, c) ∉ rp

def blocksDisjoint (b₁ b₂ : Block) : Prop :=
  ∀ c, c ∈ b₁.seats → c ∈ b₂.seats → False

noncomputable def cap (rp : List (ℤ × ℤ)) (t : ℤ) : ℕ :=
  sSup {k : ℕ | ∃ I : Finset Block,
    (∀ b ∈ I, blockFree rp t b) ∧
    (∀ b₁ ∈ I, ∀ b₂ ∈ I, b₁ ≠ b₂ → blocksDisjoint b₁ b₂) ∧
    I.card = k}

noncomputable def capSum (reservedSeats : Slice (alloc.vec.Vec Std.I64)) (n : ℤ) : ℤ :=
  ∑ m ∈ Finset.Icc 1 n.toNat, (cap (reservedPairs reservedSeats) (m : ℤ) : ℤ)

def Pre (n : Std.I64) (reservedSeats : Slice (alloc.vec.Vec Std.I64)) : Prop :=
  1 ≤ n.val ∧ n.val ≤ 10 ^ 9 ∧
  (∀ v ∈ reservedSeats.val, v.val.length = 2) ∧
  (∀ p ∈ reservedPairs reservedSeats, 1 ≤ p.1 ∧ p.1 ≤ n.val ∧ 1 ≤ p.2 ∧ p.2 ≤ 10) ∧
  (reservedPairs reservedSeats).Nodup ∧
  ((reservedPairs reservedSeats).length : ℤ) ≤ min (10 * n.val) 10000

def affectedRows (rp : List (ℤ × ℤ)) : Finset ℤ :=
  (rp.toFinset.filter (fun p => 2 ≤ p.2 ∧ p.2 ≤ 9)).image (fun p => p.1)

def countSeatsInRow (rp : List (ℤ × ℤ)) (t : ℤ) : ℕ :=
  (rp.toFinset.filter (fun p => p.1 = t ∧ 2 ≤ p.2 ∧ p.2 ≤ 9)).card

def singleEntryRows (rp : List (ℤ × ℤ)) : Finset ℤ :=
  (affectedRows rp).filter (fun t => countSeatsInRow rp t = 1)

def Compatible (g₁ g₂ : ℤ × Block) : Prop :=
  g₁.1 ≠ g₂.1 ∨ blocksDisjoint g₁.2 g₂.2

def ValidAssignment (rp : List (ℤ × ℤ)) (n : ℤ) {k : ℕ} (g : Fin k → ℤ × Block) : Prop :=
  (∀ i, 1 ≤ (g i).1 ∧ (g i).1 ≤ n) ∧
  (∀ i, blockFree rp (g i).1 (g i).2) ∧
  (∀ i j, i ≠ j → Compatible (g i) (g j))

/-- Whenever the function returns a result r, r = Σ_{t=1}^{n} cap(t). For a row t and seat label c, say (t,c) is reserved if there is an index i with 0 <= i < len(reservedSeats), reservedSeats[i][0]=t, and reservedSeats[i][1]=c. For each row t, let L_t={2,3,4,5}, M_t={4,5,6,7}, R_t={6,7,8,9} be the allowed four-seat blocks (seat labels in row t). A block is free if none of its seats is reserved. cap(t) is the maximum number of pairwise disjoint free blocks among L_t, M_t, R_t. Equivalently, cap(t)=2 if all seats (t,c) with c in {2,3,4,5,6,7,8,9} are unreserved; cap(t)=1 if at least one of those seats is reserved but at least one of L_t, M_t, R_t is free; cap(t)=0 otherwise.
  Preconditions: n is an integer with 1 <= n <= 10^9. reservedSeats is a slice of vectors; every reservedSeats[i] has length 2 and is read as a pair [row, seat]. For every i with 0 <= i < len(reservedSeats), 1 <= reservedSeats[i][0] <= n and 1 <= reservedSeats[i][1] <= 10. All pairs reservedSeats[i] are distinct. Also len(reservedSeats) <= min(10*n, 10^4). The empty slice is allowed, as in the provided examples. -/
theorem spec_1 (n : Std.I64) (reservedSeats : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64)
    (hpre : Pre n reservedSeats)
    (hres : Aegis.MaxNumberOfFamilies.max_number_of_families n reservedSeats = ok r) :
    r.val = capSum reservedSeats n.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Std.I64) (reservedSeats : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64)
    (hpre : Pre n reservedSeats)
    (hres : Aegis.MaxNumberOfFamilies.max_number_of_families n reservedSeats = ok r), r.val = capSum reservedSeats n.val) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r; it does not fail, panic, overflow, or access an out-of-range element.
  Preconditions: n is an integer with 1 <= n <= 10^9. reservedSeats is a slice of vectors; every reservedSeats[i] has length 2 and is read as a pair [row, seat]. For every i with 0 <= i < len(reservedSeats), 1 <= reservedSeats[i][0] <= n and 1 <= reservedSeats[i][1] <= 10. All pairs reservedSeats[i] are distinct. Also len(reservedSeats) <= min(10*n, 10^4). The empty slice is allowed. -/
theorem spec_2 (n : Std.I64) (reservedSeats : Slice (alloc.vec.Vec Std.I64))
    (hpre : Pre n reservedSeats) :
    ∃ r : Std.I64, Aegis.MaxNumberOfFamilies.max_number_of_families n reservedSeats = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Std.I64) (reservedSeats : Slice (alloc.vec.Vec Std.I64))
    (hpre : Pre n reservedSeats), ∃ r : Std.I64, Aegis.MaxNumberOfFamilies.max_number_of_families n reservedSeats = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r <= 2*n.
  Preconditions: n is an integer with 1 <= n <= 10^9. reservedSeats is a slice of vectors; every reservedSeats[i] has length 2 and is read as a pair [row, seat]. For every i with 0 <= i < len(reservedSeats), 1 <= reservedSeats[i][0] <= n and 1 <= reservedSeats[i][1] <= 10. All pairs reservedSeats[i] are distinct. Also len(reservedSeats) <= min(10*n, 10^4). The empty slice is allowed. -/
theorem spec_3 (n : Std.I64) (reservedSeats : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64)
    (hpre : Pre n reservedSeats)
    (hres : Aegis.MaxNumberOfFamilies.max_number_of_families n reservedSeats = ok r) :
    0 ≤ r.val ∧ r.val ≤ 2 * n.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : Std.I64) (reservedSeats : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64)
    (hpre : Pre n reservedSeats)
    (hres : Aegis.MaxNumberOfFamilies.max_number_of_families n reservedSeats = ok r), 0 ≤ r.val ∧ r.val ≤ 2 * n.val) := by
  sorry

/-- If every entry reservedSeats[i] has seat label reservedSeats[i][1] equal to 1 or 10, so no seat in columns 2 through 9 is reserved in any row, then whenever the function returns a result r, r = 2*n.
  Preconditions: n is an integer with 1 <= n <= 10^9. reservedSeats is a slice of vectors; every reservedSeats[i] has length 2 and is read as a pair [row, seat]. For every i with 0 <= i < len(reservedSeats), 1 <= reservedSeats[i][0] <= n and 1 <= reservedSeats[i][1] <= 10. All pairs reservedSeats[i] are distinct. Also len(reservedSeats) <= min(10*n, 10^4). The empty slice is allowed. -/
theorem spec_4 (n : Std.I64) (reservedSeats : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64)
    (hpre : Pre n reservedSeats)
    (hseats : ∀ p ∈ reservedPairs reservedSeats, p.2 = 1 ∨ p.2 = 10)
    (hres : Aegis.MaxNumberOfFamilies.max_number_of_families n reservedSeats = ok r) :
    r.val = 2 * n.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : Std.I64) (reservedSeats : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64)
    (hpre : Pre n reservedSeats)
    (hseats : ∀ p ∈ reservedPairs reservedSeats, p.2 = 1 ∨ p.2 = 10)
    (hres : Aegis.MaxNumberOfFamilies.max_number_of_families n reservedSeats = ok r), r.val = 2 * n.val) := by
  sorry

/-- If for every row t with 1 <= t <= n, each of the three blocks L_t={2,3,4,5}, M_t={4,5,6,7}, R_t={6,7,8,9} contains at least one reserved seat in row t, then whenever the function returns a result r, r = 0.
  Preconditions: n is an integer with 1 <= n <= 10^9. reservedSeats is a slice of vectors; every reservedSeats[i] has length 2 and is read as a pair [row, seat]. For every i with 0 <= i < len(reservedSeats), 1 <= reservedSeats[i][0] <= n and 1 <= reservedSeats[i][1] <= 10. All pairs reservedSeats[i] are distinct. Also len(reservedSeats) <= min(10*n, 10^4). The empty slice is allowed. -/
theorem spec_5 (n : Std.I64) (reservedSeats : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64)
    (hpre : Pre n reservedSeats)
    (hfull : ∀ t, 1 ≤ t → t ≤ n.val →
      (∃ c ∈ Block.L.seats, IsReserved reservedSeats t c) ∧
      (∃ c ∈ Block.M.seats, IsReserved reservedSeats t c) ∧
      (∃ c ∈ Block.R.seats, IsReserved reservedSeats t c))
    (hres : Aegis.MaxNumberOfFamilies.max_number_of_families n reservedSeats = ok r) :
    r.val = 0 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : Std.I64) (reservedSeats : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64)
    (hpre : Pre n reservedSeats)
    (hfull : ∀ t, 1 ≤ t → t ≤ n.val →
      (∃ c ∈ Block.L.seats, IsReserved reservedSeats t c) ∧
      (∃ c ∈ Block.M.seats, IsReserved reservedSeats t c) ∧
      (∃ c ∈ Block.R.seats, IsReserved reservedSeats t c))
    (hres : Aegis.MaxNumberOfFamilies.max_number_of_families n reservedSeats = ok r), r.val = 0) := by
  sorry

/-- If the set of reserved pairs in A is a subset of the set of reserved pairs in B, and if max_number_of_families(n,A) returns r_A and max_number_of_families(n,B) returns r_B, then r_B <= r_A.
  Preconditions: Both inputs (n, A) and (n, B) satisfy the standard precondition: n is an integer with 1 <= n <= 10^9; each input is a slice of vectors, every element has length 2 and is read as [row, seat]; for every element, 1 <= row <= n and 1 <= seat <= 10; all pairs in each input are distinct; len <= min(10*n, 10^4); empty slices are allowed. The two inputs use the same n. -/
theorem spec_6 (n : Std.I64) (A B : Slice (alloc.vec.Vec Std.I64)) (rA rB : Std.I64)
    (hpreA : Pre n A) (hpreB : Pre n B)
    (hsub : ∀ p, p ∈ reservedPairs A → p ∈ reservedPairs B)
    (hA : Aegis.MaxNumberOfFamilies.max_number_of_families n A = ok rA)
    (hB : Aegis.MaxNumberOfFamilies.max_number_of_families n B = ok rB) :
    rB.val ≤ rA.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : Std.I64) (A B : Slice (alloc.vec.Vec Std.I64)) (rA rB : Std.I64)
    (hpreA : Pre n A) (hpreB : Pre n B)
    (hsub : ∀ p, p ∈ reservedPairs A → p ∈ reservedPairs B)
    (hA : Aegis.MaxNumberOfFamilies.max_number_of_families n A = ok rA)
    (hB : Aegis.MaxNumberOfFamilies.max_number_of_families n B = ok rB), rB.val ≤ rA.val) := by
  sorry

/-- If reservedSeats' is a permutation of reservedSeats, meaning they contain the same multiset of pairs (equivalently the same set, since all pairs are distinct), and if the two calls return r and r' respectively, then r = r'.
  Preconditions: Both inputs (n, reservedSeats) and (n, reservedSeats') satisfy the standard precondition: n is an integer with 1 <= n <= 10^9; each input is a slice of vectors, every element has length 2 and is read as [row, seat]; for every element, 1 <= row <= n and 1 <= seat <= 10; all pairs in each input are distinct; len <= min(10*n, 10^4); empty slices are allowed. The two inputs use the same n. -/
theorem spec_7 (n : Std.I64) (reservedSeats reservedSeats' : Slice (alloc.vec.Vec Std.I64))
    (r r' : Std.I64)
    (hpre : Pre n reservedSeats) (hpre' : Pre n reservedSeats')
    (hperm : (reservedPairs reservedSeats').Perm (reservedPairs reservedSeats))
    (hres : Aegis.MaxNumberOfFamilies.max_number_of_families n reservedSeats = ok r)
    (hres' : Aegis.MaxNumberOfFamilies.max_number_of_families n reservedSeats' = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : Std.I64) (reservedSeats reservedSeats' : Slice (alloc.vec.Vec Std.I64))
    (r r' : Std.I64)
    (hpre : Pre n reservedSeats) (hpre' : Pre n reservedSeats')
    (hperm : (reservedPairs reservedSeats').Perm (reservedPairs reservedSeats))
    (hres : Aegis.MaxNumberOfFamilies.max_number_of_families n reservedSeats = ok r)
    (hres' : Aegis.MaxNumberOfFamilies.max_number_of_families n reservedSeats' = ok r'), r.val = r'.val) := by
  sorry

/-- If max_number_of_families(n,reservedSeats) returns r and max_number_of_families(n,reservedSeats') returns r', then r = r'.
  Preconditions: The input (n, reservedSeats) satisfies the standard precondition: 1 <= n <= 10^9; every reservedSeats[i] has length 2 and is read as [row, seat]; 1 <= row <= n and 1 <= seat <= 10; all pairs are distinct; len(reservedSeats) <= min(10*n, 10^4); empty slices are allowed. Additionally t is a row with 1 <= t <= n, c is in {1,10}, (t,c) is not already in reservedSeats, and len(reservedSeats) < min(10*n, 10^4). reservedSeats' is reservedSeats with (t,c) appended; then reservedSeats' also satisfies the preconditions. -/
theorem spec_8 (n : Std.I64) (reservedSeats reservedSeats' : Slice (alloc.vec.Vec Std.I64))
    (t c : ℤ) (r r' : Std.I64)
    (hpre : Pre n reservedSeats)
    (ht : 1 ≤ t ∧ t ≤ n.val)
    (hc : c = 1 ∨ c = 10)
    (hnot : (t, c) ∉ reservedPairs reservedSeats)
    (hlen : ((reservedPairs reservedSeats).length : ℤ) < min (10 * n.val) 10000)
    (happ : ∃ v : alloc.vec.Vec Std.I64,
      reservedSeats'.val = reservedSeats.val ++ [v] ∧ pairOf v = some (t, c))
    (hres : Aegis.MaxNumberOfFamilies.max_number_of_families n reservedSeats = ok r)
    (hres' : Aegis.MaxNumberOfFamilies.max_number_of_families n reservedSeats' = ok r') :
    Pre n reservedSeats' ∧ r.val = r'.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n : Std.I64) (reservedSeats reservedSeats' : Slice (alloc.vec.Vec Std.I64))
    (t c : ℤ) (r r' : Std.I64)
    (hpre : Pre n reservedSeats)
    (ht : 1 ≤ t ∧ t ≤ n.val)
    (hc : c = 1 ∨ c = 10)
    (hnot : (t, c) ∉ reservedPairs reservedSeats)
    (hlen : ((reservedPairs reservedSeats).length : ℤ) < min (10 * n.val) 10000)
    (happ : ∃ v : alloc.vec.Vec Std.I64,
      reservedSeats'.val = reservedSeats.val ++ [v] ∧ pairOf v = some (t, c))
    (hres : Aegis.MaxNumberOfFamilies.max_number_of_families n reservedSeats = ok r)
    (hres' : Aegis.MaxNumberOfFamilies.max_number_of_families n reservedSeats' = ok r'), Pre n reservedSeats' ∧ r.val = r'.val) := by
  sorry

/-- Whenever the function returns a result r, there exists an assignment of r groups to seats such that each group occupies one entire allowed block L_t={(t,2),(t,3),(t,4),(t,5)}, M_t={(t,4),(t,5),(t,6),(t,7)}, or R_t={(t,6),(t,7),(t,8),(t,9)} for some row t in {1,...,n}; no two groups occupy the same seat; and no occupied seat is in reservedSeats.
  Preconditions: n is an integer with 1 <= n <= 10^9. reservedSeats is a slice of vectors; every reservedSeats[i] has length 2 and is read as a pair [row, seat]. For every i with 0 <= i < len(reservedSeats), 1 <= reservedSeats[i][0] <= n and 1 <= reservedSeats[i][1] <= 10. All pairs reservedSeats[i] are distinct. Also len(reservedSeats) <= min(10*n, 10^4). The empty slice is allowed. -/
theorem spec_9 (n : Std.I64) (reservedSeats : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64)
    (hpre : Pre n reservedSeats)
    (hres : Aegis.MaxNumberOfFamilies.max_number_of_families n reservedSeats = ok r) :
    ∃ k : ℕ, r.val = (k : ℤ) ∧
      ∃ g : Fin k → ℤ × Block, ValidAssignment (reservedPairs reservedSeats) n.val g := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n : Std.I64) (reservedSeats : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64)
    (hpre : Pre n reservedSeats)
    (hres : Aegis.MaxNumberOfFamilies.max_number_of_families n reservedSeats = ok r), ∃ k : ℕ, r.val = (k : ℤ) ∧
      ∃ g : Fin k → ℤ × Block, ValidAssignment (reservedPairs reservedSeats) n.val g) := by
  sorry

/-- Whenever the function returns a result r, for every collection of k four-person groups such that each group occupies one allowed block L_t={(t,2),(t,3),(t,4),(t,5)}, M_t={(t,4),(t,5),(t,6),(t,7)}, or R_t={(t,6),(t,7),(t,8),(t,9)} for some row t in {1,...,n}, no two groups share a seat, and no occupied seat is reserved, we have k <= r.
  Preconditions: n is an integer with 1 <= n <= 10^9. reservedSeats is a slice of vectors; every reservedSeats[i] has length 2 and is read as a pair [row, seat]. For every i with 0 <= i < len(reservedSeats), 1 <= reservedSeats[i][0] <= n and 1 <= reservedSeats[i][1] <= 10. All pairs reservedSeats[i] are distinct. Also len(reservedSeats) <= min(10*n, 10^4). The empty slice is allowed. -/
theorem spec_10 (n : Std.I64) (reservedSeats : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64)
    (hpre : Pre n reservedSeats)
    (hres : Aegis.MaxNumberOfFamilies.max_number_of_families n reservedSeats = ok r) :
    ∀ (k : ℕ) (g : Fin k → ℤ × Block),
      ValidAssignment (reservedPairs reservedSeats) n.val g → (k : ℤ) ≤ r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n : Std.I64) (reservedSeats : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64)
    (hpre : Pre n reservedSeats)
    (hres : Aegis.MaxNumberOfFamilies.max_number_of_families n reservedSeats = ok r), ∀ (k : ℕ) (g : Fin k → ℤ × Block),
      ValidAssignment (reservedPairs reservedSeats) n.val g → (k : ℤ) ≤ r.val) := by
  sorry

/-- Let k be the number of distinct rows t in {1,...,n} for which reservedSeats contains at least one pair with first coordinate t and second coordinate in {2,3,4,5,6,7,8,9}. Whenever the function returns a result r, r <= 2*n - k.
  Preconditions: n is an integer with 1 <= n <= 10^9. reservedSeats is a slice of vectors; every reservedSeats[i] has length 2 and is read as a pair [row, seat]. For every i with 0 <= i < len(reservedSeats), 1 <= reservedSeats[i][0] <= n and 1 <= reservedSeats[i][1] <= 10. All pairs reservedSeats[i] are distinct. Also len(reservedSeats) <= min(10*n, 10^4). The empty slice is allowed. -/
theorem spec_11 (n : Std.I64) (reservedSeats : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64)
    (hpre : Pre n reservedSeats)
    (hres : Aegis.MaxNumberOfFamilies.max_number_of_families n reservedSeats = ok r) :
    r.val ≤ 2 * n.val - ((affectedRows (reservedPairs reservedSeats)).card : ℤ) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (n : Std.I64) (reservedSeats : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64)
    (hpre : Pre n reservedSeats)
    (hres : Aegis.MaxNumberOfFamilies.max_number_of_families n reservedSeats = ok r), r.val ≤ 2 * n.val - ((affectedRows (reservedPairs reservedSeats)).card : ℤ)) := by
  sorry

/-- Let k be the number of distinct rows t in {1,...,n} for which reservedSeats contains at least one pair with first coordinate t and second coordinate in {2,3,4,5,6,7,8,9}. Let k1 be the number of distinct rows t for which exactly one entry of reservedSeats has first coordinate t and second coordinate in {2,3,4,5,6,7,8,9}. Whenever the function returns a result r, r >= 2*(n - k) + k1.
  Preconditions: n is an integer with 1 <= n <= 10^9. reservedSeats is a slice of vectors; every reservedSeats[i] has length 2 and is read as a pair [row, seat]. For every i with 0 <= i < len(reservedSeats), 1 <= reservedSeats[i][0] <= n and 1 <= reservedSeats[i][1] <= 10. All pairs reservedSeats[i] are distinct. Also len(reservedSeats) <= min(10*n, 10^4). The empty slice is allowed. -/
theorem spec_12 (n : Std.I64) (reservedSeats : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64)
    (hpre : Pre n reservedSeats)
    (hres : Aegis.MaxNumberOfFamilies.max_number_of_families n reservedSeats = ok r) :
    2 * (n.val - ((affectedRows (reservedPairs reservedSeats)).card : ℤ))
      + ((singleEntryRows (reservedPairs reservedSeats)).card : ℤ) ≤ r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (n : Std.I64) (reservedSeats : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64)
    (hpre : Pre n reservedSeats)
    (hres : Aegis.MaxNumberOfFamilies.max_number_of_families n reservedSeats = ok r), 2 * (n.val - ((affectedRows (reservedPairs reservedSeats)).card : ℤ))
      + ((singleEntryRows (reservedPairs reservedSeats)).card : ℤ) ≤ r.val) := by
  sorry

/-- Let r be the result of max_number_of_families(n, reservedSeats) and r' be the result of max_number_of_families(n', reservedSeats). Whenever both calls return results, r' = r + 2*(n' - n).
  Preconditions: The input (n, reservedSeats) satisfies the standard precondition: 1 <= n <= 10^9; every reservedSeats[i] has length 2 and is read as [row, seat]; 1 <= row <= n and 1 <= seat <= 10; all pairs are distinct; len <= min(10*n, 10^4); empty slices are allowed. Also n' is an integer with n <= n' <= 10^9, so (n', reservedSeats) also satisfies the same constraints because all reserved rows are at most n <= n'. -/
theorem spec_13 (n n' : Std.I64) (reservedSeats : Slice (alloc.vec.Vec Std.I64))
    (r r' : Std.I64)
    (hpre : Pre n reservedSeats)
    (hn : n.val ≤ n'.val) (hn' : n'.val ≤ 10 ^ 9)
    (hres : Aegis.MaxNumberOfFamilies.max_number_of_families n reservedSeats = ok r)
    (hres' : Aegis.MaxNumberOfFamilies.max_number_of_families n' reservedSeats = ok r') :
    r'.val = r.val + 2 * (n'.val - n.val) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (n n' : Std.I64) (reservedSeats : Slice (alloc.vec.Vec Std.I64))
    (r r' : Std.I64)
    (hpre : Pre n reservedSeats)
    (hn : n.val ≤ n'.val) (hn' : n'.val ≤ 10 ^ 9)
    (hres : Aegis.MaxNumberOfFamilies.max_number_of_families n reservedSeats = ok r)
    (hres' : Aegis.MaxNumberOfFamilies.max_number_of_families n' reservedSeats = ok r'), r'.val = r.val + 2 * (n'.val - n.val)) := by
  sorry

/-- If max_number_of_families(n, reservedSeats) returns r and max_number_of_families(n, reservedSeats') returns r', then r = r'.
  Preconditions: The input (n, reservedSeats) satisfies the standard precondition: 1 <= n <= 10^9; every reservedSeats[i] has length 2 and is read as [row, seat]; 1 <= row <= n and 1 <= seat <= 10; all pairs are distinct; len <= min(10*n, 10^4); empty slices are allowed. Also π is a permutation of {1,...,n}, and reservedSeats' is obtained from reservedSeats by replacing each pair [row, seat] with [π(row), seat]; then (n, reservedSeats') also satisfies the preconditions. -/
theorem spec_14 (n : Std.I64) (reservedSeats reservedSeats' : Slice (alloc.vec.Vec Std.I64))
    (π : ℤ → ℤ) (r r' : Std.I64)
    (hpre : Pre n reservedSeats) (hpre' : Pre n reservedSeats')
    (hπ : ∀ t, 1 ≤ t → t ≤ n.val → 1 ≤ π t ∧ π t ≤ n.val)
    (hπinj : ∀ a b, 1 ≤ a → a ≤ n.val → 1 ≤ b → b ≤ n.val → π a = π b → a = b)
    (hmap : (reservedPairs reservedSeats').Perm
      ((reservedPairs reservedSeats).map (fun p => (π p.1, p.2))))
    (hres : Aegis.MaxNumberOfFamilies.max_number_of_families n reservedSeats = ok r)
    (hres' : Aegis.MaxNumberOfFamilies.max_number_of_families n reservedSeats' = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (n : Std.I64) (reservedSeats reservedSeats' : Slice (alloc.vec.Vec Std.I64))
    (π : ℤ → ℤ) (r r' : Std.I64)
    (hpre : Pre n reservedSeats) (hpre' : Pre n reservedSeats')
    (hπ : ∀ t, 1 ≤ t → t ≤ n.val → 1 ≤ π t ∧ π t ≤ n.val)
    (hπinj : ∀ a b, 1 ≤ a → a ≤ n.val → 1 ≤ b → b ≤ n.val → π a = π b → a = b)
    (hmap : (reservedPairs reservedSeats').Perm
      ((reservedPairs reservedSeats).map (fun p => (π p.1, p.2))))
    (hres : Aegis.MaxNumberOfFamilies.max_number_of_families n reservedSeats = ok r)
    (hres' : Aegis.MaxNumberOfFamilies.max_number_of_families n reservedSeats' = ok r'), r.val = r'.val) := by
  sorry

end AegisSpec.MaxNumberOfFamilies
