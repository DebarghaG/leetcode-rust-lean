import Aegis.NumberOfPatterns.Code.Funs

/-!
# Specifications of `Aegis.NumberOfPatterns.number_of_patterns`

LeetCode problem `android-unlock-patterns`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.NumberOfPatterns (number_of_patterns)

namespace AegisSpec.NumberOfPatterns

def IsDot (d : Int) : Prop := 1 ≤ d ∧ d ≤ 9

def row (d : Int) : Int := (d - 1) / 3

def col (d : Int) : Int := (d - 1) % 3

def Blocking (a b c : Int) : Prop :=
  IsDot c ∧ c ≠ a ∧ c ≠ b ∧ 2 * row c = row a + row b ∧ 2 * col c = col a + col b

def ValidPattern (P : List Int) : Prop :=
  1 ≤ P.length ∧ P.length ≤ 9 ∧ (∀ d ∈ P, IsDot d) ∧ P.Nodup ∧
    ∀ (i : Nat) (h : i + 1 < P.length) (c : Int),
      Blocking (P[i]'(Nat.lt_trans (Nat.lt_succ_self i) h)) (P[i+1]'h) c → c ∈ P.take i

def dotListsUpTo (K : Nat) : Finset (List Int) :=
  (Finset.range (K + 1)).biUnion fun k =>
    Finset.univ.image fun f : Fin k → Fin 9 => List.ofFn fun i => ((f i).val : Int) + 1

def allPatterns : Finset (List Int) := dotListsUpTo 9

noncomputable def validPatternCount (m n : Int) : Nat := by
  classical
  exact (allPatterns.filter fun P =>
    ValidPattern P ∧ m ≤ (P.length : Int) ∧ (P.length : Int) ≤ n).card

noncomputable def validPatternCountExact (k : Int) : Nat := by
  classical
  exact (allPatterns.filter fun P => ValidPattern P ∧ (P.length : Int) = k).card

def intIcc (m n : Int) : Finset Int :=
  (Finset.range (n - m + 1).toNat).image fun i : Nat => m + (i : Int)

/-- Define the dots as 1,...,9 in row-major order on the 3x3 grid (1,2,3 top row; 4,5,6 middle row; 7,8,9 bottom row). For a dot d let row(d)=floor((d-1)/3) and col(d)=(d-1) mod 3. For distinct dots a,b, say that c is a blocking dot between a and b iff c is a dot distinct from a,b with row(c)=(row(a)+row(b))/2 and col(c)=(col(a)+col(b))/2; equivalently, c is the unique grid dot at the midpoint of the segment from a to b, and there is no such c when either average is not an integer. Call a list P of dots a valid pattern iff (i) 1 <= len(P) <= 9, (ii) all entries of P are distinct, and (iii) for every i with 0 <= i < len(P)-1, if there is a blocking dot c between P[i] and P[i+1], then c occurs among P[0],...,P[i-1] (i.e. it appeared earlier in the sequence). Then the function returns a result r with r equal to the number of valid patterns P such that m <= len(P) <= n. If m > n, the interval is empty and r = 0.
  Preconditions: m and n are integers with 1 <= m <= 9 and 1 <= n <= 9. -/
theorem spec_1 (m n : Std.I64) (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 9)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 9) :
    ∃ r, number_of_patterns m n = ok r ∧
      r.val = (validPatternCount m.val n.val : Int) ∧
      (n.val < m.val → r.val = 0) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (m n : Std.I64) (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 9)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 9), ∃ r, number_of_patterns m n = ok r ∧
      r.val = (validPatternCount m.val n.val : Int) ∧
      (n.val < m.val → r.val = 0)) := by
  sorry

/-- For every such m and n, the function returns a result r and does not fail (no overflow, panic, or out-of-bounds).
  Preconditions: 1 <= m <= 9 and 1 <= n <= 9. -/
theorem spec_2 (m n : Std.I64) (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 9)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 9) :
    ∃ r, number_of_patterns m n = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (m n : Std.I64) (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 9)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 9), ∃ r, number_of_patterns m n = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r.
  Preconditions: 1 <= m <= 9 and 1 <= n <= 9. -/
theorem spec_3 (m n r : Std.I64) (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 9)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 9)
    (h : number_of_patterns m n = ok r) :
    0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (m n r : Std.I64) (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 9)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 9)
    (h : number_of_patterns m n = ok r), 0 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= 389497.
  Preconditions: 1 <= m <= 9 and 1 <= n <= 9. -/
theorem spec_4 (m n r : Std.I64) (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 9)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 9)
    (h : number_of_patterns m n = ok r) :
    r.val ≤ 389497 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (m n r : Std.I64) (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 9)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 9)
    (h : number_of_patterns m n = ok r), r.val ≤ 389497) := by
  sorry

/-- For every such k, if the function returns a result r, then r equals the number of valid patterns of length exactly k. In particular, the exact-length counts are: k=1 gives 9, k=2 gives 56, k=3 gives 320, k=4 gives 1624, k=5 gives 7152, k=6 gives 26016, k=7 gives 72912, k=8 gives 140704, and k=9 gives 140704.
  Preconditions: 1 <= k <= 9, m = k, and n = k. -/
theorem spec_5 (k r : Std.I64) (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 9)
    (h : number_of_patterns k k = ok r) :
    r.val = (validPatternCountExact k.val : Int) ∧
      (k.val = 1 → r.val = 9) ∧ (k.val = 2 → r.val = 56) ∧
      (k.val = 3 → r.val = 320) ∧ (k.val = 4 → r.val = 1624) ∧
      (k.val = 5 → r.val = 7152) ∧ (k.val = 6 → r.val = 26016) ∧
      (k.val = 7 → r.val = 72912) ∧ (k.val = 8 → r.val = 140704) ∧
      (k.val = 9 → r.val = 140704) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (k r : Std.I64) (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 9)
    (h : number_of_patterns k k = ok r), r.val = (validPatternCountExact k.val : Int) ∧
      (k.val = 1 → r.val = 9) ∧ (k.val = 2 → r.val = 56) ∧
      (k.val = 3 → r.val = 320) ∧ (k.val = 4 → r.val = 1624) ∧
      (k.val = 5 → r.val = 7152) ∧ (k.val = 6 → r.val = 26016) ∧
      (k.val = 7 → r.val = 72912) ∧ (k.val = 8 → r.val = 140704) ∧
      (k.val = 9 → r.val = 140704)) := by
  sorry

/-- If number_of_patterns(m,n) returns r1 and number_of_patterns(m,n+1) returns r2, then r1 <= r2.
  Preconditions: 1 <= m <= n < 9. -/
theorem spec_6 (m n n' r1 r2 : Std.I64) (hm_lo : 1 ≤ m.val)
    (hmn : m.val ≤ n.val) (hn_hi : n.val < 9) (hn' : n'.val = n.val + 1)
    (h1 : number_of_patterns m n = ok r1)
    (h2 : number_of_patterns m n' = ok r2) :
    r1.val ≤ r2.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (m n n' r1 r2 : Std.I64) (hm_lo : 1 ≤ m.val)
    (hmn : m.val ≤ n.val) (hn_hi : n.val < 9) (hn' : n'.val = n.val + 1)
    (h1 : number_of_patterns m n = ok r1)
    (h2 : number_of_patterns m n' = ok r2), r1.val ≤ r2.val) := by
  sorry

/-- If number_of_patterns(m,n) returns r1 and number_of_patterns(m-1,n) returns r2, then r1 <= r2.
  Preconditions: 2 <= m <= n <= 9. -/
theorem spec_7 (m m' n r1 r2 : Std.I64) (hm_lo : 2 ≤ m.val)
    (hmn : m.val ≤ n.val) (hn_hi : n.val ≤ 9) (hm' : m'.val = m.val - 1)
    (h1 : number_of_patterns m n = ok r1)
    (h2 : number_of_patterns m' n = ok r2) :
    r1.val ≤ r2.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (m m' n r1 r2 : Std.I64) (hm_lo : 2 ≤ m.val)
    (hmn : m.val ≤ n.val) (hn_hi : n.val ≤ 9) (hm' : m'.val = m.val - 1)
    (h1 : number_of_patterns m n = ok r1)
    (h2 : number_of_patterns m' n = ok r2), r1.val ≤ r2.val) := by
  sorry

/-- If number_of_patterns(1,n) returns r, number_of_patterns(1,m-1) returns a, and number_of_patterns(m,n) returns b, then r = a + b.
  Preconditions: 2 <= m <= n <= 9. -/
theorem spec_8 (m m' n r a b : Std.I64) (hm_lo : 2 ≤ m.val)
    (hmn : m.val ≤ n.val) (hn_hi : n.val ≤ 9) (hm' : m'.val = m.val - 1)
    (hr : number_of_patterns (1#i64) n = ok r)
    (ha : number_of_patterns (1#i64) m' = ok a)
    (hb : number_of_patterns m n = ok b) :
    r.val = a.val + b.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (m m' n r a b : Std.I64) (hm_lo : 2 ≤ m.val)
    (hmn : m.val ≤ n.val) (hn_hi : n.val ≤ 9) (hm' : m'.val = m.val - 1)
    (hr : number_of_patterns (1#i64) n = ok r)
    (ha : number_of_patterns (1#i64) m' = ok a)
    (hb : number_of_patterns m n = ok b), r.val = a.val + b.val) := by
  sorry

/-- If number_of_patterns(m,n) returns r and number_of_patterns(k,k) returns c_k for each k with m <= k <= n, then r = c_m + c_(m+1) + ... + c_n.
  Preconditions: 1 <= m <= n <= 9. -/
theorem spec_9 (m n r : Std.I64) (c : Int → Std.I64) (hm_lo : 1 ≤ m.val)
    (hmn : m.val ≤ n.val) (hn_hi : n.val ≤ 9)
    (hr : number_of_patterns m n = ok r)
    (hc : ∀ (k : Std.I64), m.val ≤ k.val → k.val ≤ n.val →
      number_of_patterns k k = ok (c k.val)) :
    r.val = ∑ k ∈ intIcc m.val n.val, (c k).val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (m n r : Std.I64) (c : Int → Std.I64) (hm_lo : 1 ≤ m.val)
    (hmn : m.val ≤ n.val) (hn_hi : n.val ≤ 9)
    (hr : number_of_patterns m n = ok r)
    (hc : ∀ (k : Std.I64), m.val ≤ k.val → k.val ≤ n.val →
      number_of_patterns k k = ok (c k.val)), r.val = ∑ k ∈ intIcc m.val n.val, (c k).val) := by
  sorry

/-- If number_of_patterns(1,n) returns r, then r >= 9.
  Preconditions: 1 <= n <= 9. -/
theorem spec_10 (n r : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 9)
    (h : number_of_patterns (1#i64) n = ok r) :
    9 ≤ r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n r : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 9)
    (h : number_of_patterns (1#i64) n = ok r), 9 ≤ r.val) := by
  sorry

/-- The function returns a result r with r = 389497.
  Preconditions: m = 1 and n = 9. -/
theorem spec_11 :
    ∃ r, number_of_patterns (1#i64) (9#i64) = ok r ∧ r.val = 389497 := by
  sorry

theorem spec_11_neg :
    ¬ (∃ r, number_of_patterns (1#i64) (9#i64) = ok r ∧ r.val = 389497) := by
  sorry

/-- The function returns a result r with r = 65.
  Preconditions: m = 1 and n = 2. -/
theorem spec_12 :
    ∃ r, number_of_patterns (1#i64) (2#i64) = ok r ∧ r.val = 65 := by
  sorry

theorem spec_12_neg :
    ¬ (∃ r, number_of_patterns (1#i64) (2#i64) = ok r ∧ r.val = 65) := by
  sorry

/-- The function returns a result r with r = 8776.
  Preconditions: m = 4 and n = 5. -/
theorem spec_13 :
    ∃ r, number_of_patterns (4#i64) (5#i64) = ok r ∧ r.val = 8776 := by
  sorry

theorem spec_13_neg :
    ¬ (∃ r, number_of_patterns (4#i64) (5#i64) = ok r ∧ r.val = 8776) := by
  sorry

/-- The function returns a result r with r = 213616.
  Preconditions: m = 7 and n = 8. -/
theorem spec_14 :
    ∃ r, number_of_patterns (7#i64) (8#i64) = ok r ∧ r.val = 213616 := by
  sorry

theorem spec_14_neg :
    ¬ (∃ r, number_of_patterns (7#i64) (8#i64) = ok r ∧ r.val = 213616) := by
  sorry

end AegisSpec.NumberOfPatterns
