import Aegis.CountPoints.Code.Funs

/-!
# Specifications of `Aegis.CountPoints.count_points`

LeetCode problem `rings-and-rods`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.CountPoints

namespace AegisSpec.CountPoints

def byteAt? (rings : Slice U8) (i : Nat) : Option Nat :=
  (rings.val[i]?).map UScalar.val

def isColorCode (c : Nat) : Prop := c = 82 ∨ c = 71 ∨ c = 66

def colorOccurs (rings : Slice U8) (n : Nat) (c : Nat) : Prop :=
  ∃ j : Nat, j < n ∧ byteAt? rings (2 * j) = some c

def labelOccurs (rings : Slice U8) (n : Nat) (d : Nat) : Prop :=
  ∃ j : Nat, j < n ∧ byteAt? rings (2 * j + 1) = some (48 + d)

def occursOn (rings : Slice U8) (n : Nat) (c : Nat) (d : Nat) : Prop :=
  ∃ j : Nat, j < n ∧ byteAt? rings (2 * j) = some c ∧ byteAt? rings (2 * j + 1) = some (48 + d)

def complete (rings : Slice U8) (n : Nat) (d : Nat) : Prop :=
  occursOn rings n 82 d ∧ occursOn rings n 71 d ∧ occursOn rings n 66 d

noncomputable def completeCount (rings : Slice U8) (n : Nat) : Nat :=
  letI := Classical.propDecidable
  ((List.range 10).filter (fun d => decide (complete rings n d))).length

noncomputable def distinctLabelCount (rings : Slice U8) (n : Nat) : Nat :=
  letI := Classical.propDecidable
  ((List.range 10).filter (fun d => decide (labelOccurs rings n d))).length

/-- For a rod label d in {0,1,...,9}, say d is complete in rings if for each color byte c in {82 ('R'), 71 ('G'), 66 ('B')} there exists an index j with 0 <= j < n such that rings[2*j] = c and rings[2*j+1] = 48+d. The function returns a result r and r equals the number of rod labels d in {0,1,...,9} that are complete in rings.
  Preconditions: Let n = len(rings)/2. The byte slice rings has length 2*n for some integer n with 1 <= n <= 100. For every j with 0 <= j < n, rings[2*j] is one of the ASCII bytes 82 ('R'), 71 ('G'), 66 ('B'), and rings[2*j+1] is one of the ASCII bytes 48 ('0') through 57 ('9'). -/
theorem spec_1 (rings : Slice U8) (n : Nat)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100) (hlen : rings.val.length = 2 * n)
    (hcolor : ∀ j : Nat, j < n → ∃ c : Nat, isColorCode c ∧ byteAt? rings (2 * j) = some c)
    (hdigit : ∀ j : Nat, j < n → ∃ d : Nat, d ≤ 9 ∧ byteAt? rings (2 * j + 1) = some (48 + d)) :
    ∃ r : I64, count_points rings = ok r ∧ r.val = (completeCount rings n : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (rings : Slice U8) (n : Nat)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100) (hlen : rings.val.length = 2 * n)
    (hcolor : ∀ j : Nat, j < n → ∃ c : Nat, isColorCode c ∧ byteAt? rings (2 * j) = some c)
    (hdigit : ∀ j : Nat, j < n → ∃ d : Nat, d ≤ 9 ∧ byteAt? rings (2 * j + 1) = some (48 + d)), ∃ r : I64, count_points rings = ok r ∧ r.val = (completeCount rings n : Int)) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r <= 10.
  Preconditions: Let n = len(rings)/2. The byte slice rings has length 2*n for some integer n with 1 <= n <= 100. For every j with 0 <= j < n, rings[2*j] is one of the ASCII bytes 82 ('R'), 71 ('G'), 66 ('B'), and rings[2*j+1] is one of the ASCII bytes 48 ('0') through 57 ('9'). -/
theorem spec_2 (rings : Slice U8) (n : Nat)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100) (hlen : rings.val.length = 2 * n)
    (hcolor : ∀ j : Nat, j < n → ∃ c : Nat, isColorCode c ∧ byteAt? rings (2 * j) = some c)
    (hdigit : ∀ j : Nat, j < n → ∃ d : Nat, d ≤ 9 ∧ byteAt? rings (2 * j + 1) = some (48 + d)) :
    ∀ r : I64, count_points rings = ok r → 0 ≤ r.val ∧ r.val ≤ 10 := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (rings : Slice U8) (n : Nat)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100) (hlen : rings.val.length = 2 * n)
    (hcolor : ∀ j : Nat, j < n → ∃ c : Nat, isColorCode c ∧ byteAt? rings (2 * j) = some c)
    (hdigit : ∀ j : Nat, j < n → ∃ d : Nat, d ≤ 9 ∧ byteAt? rings (2 * j + 1) = some (48 + d)), ∀ r : I64, count_points rings = ok r → 0 ≤ r.val ∧ r.val ≤ 10) := by
  sorry

/-- Whenever the function returns a result r, r <= U, where U is the number of rod labels d in {0,1,...,9} for which there exists j with 0 <= j < n and rings[2*j+1] = 48+d (that is, U is the number of distinct rod labels occurring in rings).
  Preconditions: Let n = len(rings)/2. The byte slice rings has length 2*n for some integer n with 1 <= n <= 100. For every j with 0 <= j < n, rings[2*j] is one of the ASCII bytes 82 ('R'), 71 ('G'), 66 ('B'), and rings[2*j+1] is one of the ASCII bytes 48 ('0') through 57 ('9'). -/
theorem spec_3 (rings : Slice U8) (n : Nat)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100) (hlen : rings.val.length = 2 * n)
    (hcolor : ∀ j : Nat, j < n → ∃ c : Nat, isColorCode c ∧ byteAt? rings (2 * j) = some c)
    (hdigit : ∀ j : Nat, j < n → ∃ d : Nat, d ≤ 9 ∧ byteAt? rings (2 * j + 1) = some (48 + d)) :
    ∀ r : I64, count_points rings = ok r → r.val ≤ (distinctLabelCount rings n : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (rings : Slice U8) (n : Nat)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100) (hlen : rings.val.length = 2 * n)
    (hcolor : ∀ j : Nat, j < n → ∃ c : Nat, isColorCode c ∧ byteAt? rings (2 * j) = some c)
    (hdigit : ∀ j : Nat, j < n → ∃ d : Nat, d ≤ 9 ∧ byteAt? rings (2 * j + 1) = some (48 + d)), ∀ r : I64, count_points rings = ok r → r.val ≤ (distinctLabelCount rings n : Int)) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if no rod label d in {0,1,...,9} is complete in rings; here d is complete exactly when each of the color bytes 82, 71, 66 occurs on rod d, i.e. for each such c there is j with 0 <= j < n, rings[2*j] = c, and rings[2*j+1] = 48+d.
  Preconditions: Let n = len(rings)/2. The byte slice rings has length 2*n for some integer n with 1 <= n <= 100. For every j with 0 <= j < n, rings[2*j] is one of the ASCII bytes 82 ('R'), 71 ('G'), 66 ('B'), and rings[2*j+1] is one of the ASCII bytes 48 ('0') through 57 ('9'). -/
theorem spec_4 (rings : Slice U8) (n : Nat)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100) (hlen : rings.val.length = 2 * n)
    (hcolor : ∀ j : Nat, j < n → ∃ c : Nat, isColorCode c ∧ byteAt? rings (2 * j) = some c)
    (hdigit : ∀ j : Nat, j < n → ∃ d : Nat, d ≤ 9 ∧ byteAt? rings (2 * j + 1) = some (48 + d)) :
    ∀ r : I64, count_points rings = ok r →
      (r.val = 0 ↔ ¬ ∃ d : Nat, d ≤ 9 ∧ complete rings n d) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (rings : Slice U8) (n : Nat)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100) (hlen : rings.val.length = 2 * n)
    (hcolor : ∀ j : Nat, j < n → ∃ c : Nat, isColorCode c ∧ byteAt? rings (2 * j) = some c)
    (hdigit : ∀ j : Nat, j < n → ∃ d : Nat, d ≤ 9 ∧ byteAt? rings (2 * j + 1) = some (48 + d)), ∀ r : I64, count_points rings = ok r →
      (r.val = 0 ↔ ¬ ∃ d : Nat, d ≤ 9 ∧ complete rings n d)) := by
  sorry

/-- If at least one of the color bytes 82 ('R'), 71 ('G'), 66 ('B') does not occur at any even index of rings, then the function returns a result r and r = 0.
  Preconditions: Let n = len(rings)/2. The byte slice rings has length 2*n for some integer n with 1 <= n <= 100. For every j with 0 <= j < n, rings[2*j] is one of the ASCII bytes 82 ('R'), 71 ('G'), 66 ('B'), and rings[2*j+1] is one of the ASCII bytes 48 ('0') through 57 ('9'). -/
theorem spec_5 (rings : Slice U8) (n : Nat)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100) (hlen : rings.val.length = 2 * n)
    (hcolor : ∀ j : Nat, j < n → ∃ c : Nat, isColorCode c ∧ byteAt? rings (2 * j) = some c)
    (hdigit : ∀ j : Nat, j < n → ∃ d : Nat, d ≤ 9 ∧ byteAt? rings (2 * j + 1) = some (48 + d))
    (hmissing : ∃ c : Nat, isColorCode c ∧ ¬ colorOccurs rings n c) :
    ∃ r : I64, count_points rings = ok r ∧ r.val = 0 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (rings : Slice U8) (n : Nat)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100) (hlen : rings.val.length = 2 * n)
    (hcolor : ∀ j : Nat, j < n → ∃ c : Nat, isColorCode c ∧ byteAt? rings (2 * j) = some c)
    (hdigit : ∀ j : Nat, j < n → ∃ d : Nat, d ≤ 9 ∧ byteAt? rings (2 * j + 1) = some (48 + d))
    (hmissing : ∃ c : Nat, isColorCode c ∧ ¬ colorOccurs rings n c), ∃ r : I64, count_points rings = ok r ∧ r.val = 0) := by
  sorry

/-- Let U be the number of distinct rod labels d in {0,1,...,9} that occur in rings, i.e. for which there exists j with 0 <= j < n and rings[2*j+1] = 48+d. If every such occurring rod label d is complete in rings (meaning 82, 71, and 66 each occur on rod d), then the function returns a result r and r = U.
  Preconditions: Let n = len(rings)/2. The byte slice rings has length 2*n for some integer n with 1 <= n <= 100. For every j with 0 <= j < n, rings[2*j] is one of the ASCII bytes 82 ('R'), 71 ('G'), 66 ('B'), and rings[2*j+1] is one of the ASCII bytes 48 ('0') through 57 ('9'). -/
theorem spec_6 (rings : Slice U8) (n : Nat)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100) (hlen : rings.val.length = 2 * n)
    (hcolor : ∀ j : Nat, j < n → ∃ c : Nat, isColorCode c ∧ byteAt? rings (2 * j) = some c)
    (hdigit : ∀ j : Nat, j < n → ∃ d : Nat, d ≤ 9 ∧ byteAt? rings (2 * j + 1) = some (48 + d))
    (hall : ∀ d : Nat, d ≤ 9 → labelOccurs rings n d → complete rings n d) :
    ∃ r : I64, count_points rings = ok r ∧ r.val = (distinctLabelCount rings n : Int) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (rings : Slice U8) (n : Nat)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100) (hlen : rings.val.length = 2 * n)
    (hcolor : ∀ j : Nat, j < n → ∃ c : Nat, isColorCode c ∧ byteAt? rings (2 * j) = some c)
    (hdigit : ∀ j : Nat, j < n → ∃ d : Nat, d ≤ 9 ∧ byteAt? rings (2 * j + 1) = some (48 + d))
    (hall : ∀ d : Nat, d ≤ 9 → labelOccurs rings n d → complete rings n d), ∃ r : I64, count_points rings = ok r ∧ r.val = (distinctLabelCount rings n : Int)) := by
  sorry

/-- Whenever the function returns a result r with r > 0, there exists a rod label d in {0,1,...,9} such that d is complete in rings (i.e. 82, 71, and 66 each occur on rod d).
  Preconditions: Let n = len(rings)/2. The byte slice rings has length 2*n for some integer n with 1 <= n <= 100. For every j with 0 <= j < n, rings[2*j] is one of the ASCII bytes 82 ('R'), 71 ('G'), 66 ('B'), and rings[2*j+1] is one of the ASCII bytes 48 ('0') through 57 ('9'). -/
theorem spec_7 (rings : Slice U8) (n : Nat)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100) (hlen : rings.val.length = 2 * n)
    (hcolor : ∀ j : Nat, j < n → ∃ c : Nat, isColorCode c ∧ byteAt? rings (2 * j) = some c)
    (hdigit : ∀ j : Nat, j < n → ∃ d : Nat, d ≤ 9 ∧ byteAt? rings (2 * j + 1) = some (48 + d)) :
    ∀ r : I64, count_points rings = ok r → 0 < r.val →
      ∃ d : Nat, d ≤ 9 ∧ complete rings n d := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (rings : Slice U8) (n : Nat)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100) (hlen : rings.val.length = 2 * n)
    (hcolor : ∀ j : Nat, j < n → ∃ c : Nat, isColorCode c ∧ byteAt? rings (2 * j) = some c)
    (hdigit : ∀ j : Nat, j < n → ∃ d : Nat, d ≤ 9 ∧ byteAt? rings (2 * j + 1) = some (48 + d)), ∀ r : I64, count_points rings = ok r → 0 < r.val →
      ∃ d : Nat, d ≤ 9 ∧ complete rings n d) := by
  sorry

/-- Whenever the function returns a result r, r = 10 if and only if every rod label d in {0,1,...,9} is complete in rings (i.e. for every d, each of 82, 71, and 66 occurs on rod d).
  Preconditions: Let n = len(rings)/2. The byte slice rings has length 2*n for some integer n with 1 <= n <= 100. For every j with 0 <= j < n, rings[2*j] is one of the ASCII bytes 82 ('R'), 71 ('G'), 66 ('B'), and rings[2*j+1] is one of the ASCII bytes 48 ('0') through 57 ('9'). -/
theorem spec_8 (rings : Slice U8) (n : Nat)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100) (hlen : rings.val.length = 2 * n)
    (hcolor : ∀ j : Nat, j < n → ∃ c : Nat, isColorCode c ∧ byteAt? rings (2 * j) = some c)
    (hdigit : ∀ j : Nat, j < n → ∃ d : Nat, d ≤ 9 ∧ byteAt? rings (2 * j + 1) = some (48 + d)) :
    ∀ r : I64, count_points rings = ok r →
      (r.val = 10 ↔ ∀ d : Nat, d ≤ 9 → complete rings n d) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (rings : Slice U8) (n : Nat)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100) (hlen : rings.val.length = 2 * n)
    (hcolor : ∀ j : Nat, j < n → ∃ c : Nat, isColorCode c ∧ byteAt? rings (2 * j) = some c)
    (hdigit : ∀ j : Nat, j < n → ∃ d : Nat, d ≤ 9 ∧ byteAt? rings (2 * j + 1) = some (48 + d)), ∀ r : I64, count_points rings = ok r →
      (r.val = 10 ↔ ∀ d : Nat, d ≤ 9 → complete rings n d)) := by
  sorry

/-- Assume that for every d in {0,1,...,9} and every color byte c in {82,71,66}, c occurs on rod d in rings1 (there exists j with 0 <= j < len(rings1)/2, rings1[2*j] = c, and rings1[2*j+1] = 48+d) if and only if c occurs on rod d in rings2 (with the analogous condition using rings2). Then whenever count_points(rings1) returns r1 and count_points(rings2) returns r2, r1 = r2.
  Preconditions: Both rings1 and rings2 satisfy the S1 preconditions: each has length twice an integer between 1 and 100, with color bytes at even indices and digit bytes at odd indices. -/
theorem spec_9 (rings1 rings2 : Slice U8) (n1 n2 : Nat)
    (hn1_pos : 1 ≤ n1) (hn1_le : n1 ≤ 100) (hlen1 : rings1.val.length = 2 * n1)
    (hcolor1 : ∀ j : Nat, j < n1 → ∃ c : Nat, isColorCode c ∧ byteAt? rings1 (2 * j) = some c)
    (hdigit1 : ∀ j : Nat, j < n1 → ∃ d : Nat, d ≤ 9 ∧ byteAt? rings1 (2 * j + 1) = some (48 + d))
    (hn2_pos : 1 ≤ n2) (hn2_le : n2 ≤ 100) (hlen2 : rings2.val.length = 2 * n2)
    (hcolor2 : ∀ j : Nat, j < n2 → ∃ c : Nat, isColorCode c ∧ byteAt? rings2 (2 * j) = some c)
    (hdigit2 : ∀ j : Nat, j < n2 → ∃ d : Nat, d ≤ 9 ∧ byteAt? rings2 (2 * j + 1) = some (48 + d))
    (hsame : ∀ (d : Nat) (c : Nat), d ≤ 9 → isColorCode c →
      (occursOn rings1 n1 c d ↔ occursOn rings2 n2 c d)) :
    ∀ r1 r2 : I64, count_points rings1 = ok r1 → count_points rings2 = ok r2 → r1.val = r2.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (rings1 rings2 : Slice U8) (n1 n2 : Nat)
    (hn1_pos : 1 ≤ n1) (hn1_le : n1 ≤ 100) (hlen1 : rings1.val.length = 2 * n1)
    (hcolor1 : ∀ j : Nat, j < n1 → ∃ c : Nat, isColorCode c ∧ byteAt? rings1 (2 * j) = some c)
    (hdigit1 : ∀ j : Nat, j < n1 → ∃ d : Nat, d ≤ 9 ∧ byteAt? rings1 (2 * j + 1) = some (48 + d))
    (hn2_pos : 1 ≤ n2) (hn2_le : n2 ≤ 100) (hlen2 : rings2.val.length = 2 * n2)
    (hcolor2 : ∀ j : Nat, j < n2 → ∃ c : Nat, isColorCode c ∧ byteAt? rings2 (2 * j) = some c)
    (hdigit2 : ∀ j : Nat, j < n2 → ∃ d : Nat, d ≤ 9 ∧ byteAt? rings2 (2 * j + 1) = some (48 + d))
    (hsame : ∀ (d : Nat) (c : Nat), d ≤ 9 → isColorCode c →
      (occursOn rings1 n1 c d ↔ occursOn rings2 n2 c d)), ∀ r1 r2 : I64, count_points rings1 = ok r1 → count_points rings2 = ok r2 → r1.val = r2.val) := by
  sorry

/-- The function does not fail on rings: it returns a result r (in Lean, the evaluation is Result.ok r for some 64-bit integer r).
  Preconditions: Let n = len(rings)/2. The byte slice rings has length 2*n for some integer n with 1 <= n <= 100. For every j with 0 <= j < n, rings[2*j] is one of the ASCII bytes 82 ('R'), 71 ('G'), 66 ('B'), and rings[2*j+1] is one of the ASCII bytes 48 ('0') through 57 ('9'). -/
theorem spec_10 (rings : Slice U8) (n : Nat)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100) (hlen : rings.val.length = 2 * n)
    (hcolor : ∀ j : Nat, j < n → ∃ c : Nat, isColorCode c ∧ byteAt? rings (2 * j) = some c)
    (hdigit : ∀ j : Nat, j < n → ∃ d : Nat, d ≤ 9 ∧ byteAt? rings (2 * j + 1) = some (48 + d)) :
    ∃ r : I64, count_points rings = ok r := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (rings : Slice U8) (n : Nat)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100) (hlen : rings.val.length = 2 * n)
    (hcolor : ∀ j : Nat, j < n → ∃ c : Nat, isColorCode c ∧ byteAt? rings (2 * j) = some c)
    (hdigit : ∀ j : Nat, j < n → ∃ d : Nat, d ≤ 9 ∧ byteAt? rings (2 * j + 1) = some (48 + d)), ∃ r : I64, count_points rings = ok r) := by
  sorry

/-- When count_points(rings1) returns r1 and count_points(rings2) returns r2, we have r1 <= r2 <= r1 + 1.
  Preconditions: rings1 and rings2 both satisfy the S1 preconditions, with n1 = len(rings1)/2 and n2 = len(rings2)/2. Moreover, rings2 is obtained from rings1 by appending one color-position pair: n2 = n1 + 1, for every j with 0 <= j < n1 we have rings2[2*j] = rings1[2*j] and rings2[2*j+1] = rings1[2*j+1], and for some color byte c in {82,71,66} and digit d in {0,...,9} we have rings2[2*n1] = c and rings2[2*n1+1] = 48+d. -/
theorem spec_11 (rings1 rings2 : Slice U8) (n1 n2 : Nat)
    (hn1_pos : 1 ≤ n1) (hn1_le : n1 ≤ 100) (hlen1 : rings1.val.length = 2 * n1)
    (hcolor1 : ∀ j : Nat, j < n1 → ∃ c : Nat, isColorCode c ∧ byteAt? rings1 (2 * j) = some c)
    (hdigit1 : ∀ j : Nat, j < n1 → ∃ d : Nat, d ≤ 9 ∧ byteAt? rings1 (2 * j + 1) = some (48 + d))
    (hn2_pos : 1 ≤ n2) (hn2_le : n2 ≤ 100) (hlen2 : rings2.val.length = 2 * n2)
    (hcolor2 : ∀ j : Nat, j < n2 → ∃ c : Nat, isColorCode c ∧ byteAt? rings2 (2 * j) = some c)
    (hdigit2 : ∀ j : Nat, j < n2 → ∃ d : Nat, d ≤ 9 ∧ byteAt? rings2 (2 * j + 1) = some (48 + d))
    (hn2 : n2 = n1 + 1)
    (hprefix : ∀ j : Nat, j < n1 →
      rings2.val[2 * j]? = rings1.val[2 * j]? ∧
      byteAt? rings2 (2 * j + 1) = byteAt? rings1 (2 * j + 1))
    (hlast : ∃ (c : Nat) (d : Nat), isColorCode c ∧ d ≤ 9 ∧
      byteAt? rings2 (2 * n1) = some c ∧ byteAt? rings2 (2 * n1 + 1) = some (48 + d)) :
    ∀ r1 r2 : I64, count_points rings1 = ok r1 → count_points rings2 = ok r2 →
      r1.val ≤ r2.val ∧ r2.val ≤ r1.val + 1 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (rings1 rings2 : Slice U8) (n1 n2 : Nat)
    (hn1_pos : 1 ≤ n1) (hn1_le : n1 ≤ 100) (hlen1 : rings1.val.length = 2 * n1)
    (hcolor1 : ∀ j : Nat, j < n1 → ∃ c : Nat, isColorCode c ∧ byteAt? rings1 (2 * j) = some c)
    (hdigit1 : ∀ j : Nat, j < n1 → ∃ d : Nat, d ≤ 9 ∧ byteAt? rings1 (2 * j + 1) = some (48 + d))
    (hn2_pos : 1 ≤ n2) (hn2_le : n2 ≤ 100) (hlen2 : rings2.val.length = 2 * n2)
    (hcolor2 : ∀ j : Nat, j < n2 → ∃ c : Nat, isColorCode c ∧ byteAt? rings2 (2 * j) = some c)
    (hdigit2 : ∀ j : Nat, j < n2 → ∃ d : Nat, d ≤ 9 ∧ byteAt? rings2 (2 * j + 1) = some (48 + d))
    (hn2 : n2 = n1 + 1)
    (hprefix : ∀ j : Nat, j < n1 →
      rings2.val[2 * j]? = rings1.val[2 * j]? ∧
      byteAt? rings2 (2 * j + 1) = byteAt? rings1 (2 * j + 1))
    (hlast : ∃ (c : Nat) (d : Nat), isColorCode c ∧ d ≤ 9 ∧
      byteAt? rings2 (2 * n1) = some c ∧ byteAt? rings2 (2 * n1 + 1) = some (48 + d)), ∀ r1 r2 : I64, count_points rings1 = ok r1 → count_points rings2 = ok r2 →
      r1.val ≤ r2.val ∧ r2.val ≤ r1.val + 1) := by
  sorry

end AegisSpec.CountPoints
