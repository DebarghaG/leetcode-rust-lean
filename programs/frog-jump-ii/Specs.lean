import Aegis.MaxJump.Code.Funs

/-!
# Specifications of `Aegis.MaxJump.max_jump`

LeetCode problem `frog-jump-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxJump

def vals (stones : Slice Std.I64) : List ℤ := stones.val.map (fun x => x.val)

def len (stones : Slice Std.I64) : ℕ := stones.val.length

def valAt (stones : Slice Std.I64) (i : ℕ) : ℤ := (vals stones).getD i 0

def Pre (stones : Slice Std.I64) : Prop :=
  2 ≤ len stones ∧
  len stones ≤ 100000 ∧
  valAt stones 0 = 0 ∧
  (∀ i : ℕ, i < len stones → 0 ≤ valAt stones i ∧ valAt stones i ≤ 10 ^ 9) ∧
  (∀ i : ℕ, i + 1 < len stones → valAt stones i < valAt stones (i + 1))

def jumpLens (stones : Slice Std.I64) (p : List ℕ) : List ℤ :=
  (p.zip p.tail).map (fun q => |valAt stones q.2 - valAt stones q.1|)

def cost (stones : Slice Std.I64) (p : List ℕ) : ℤ := (jumpLens stones p).foldr max 0

def RoundTrip (stones : Slice Std.I64) (p : List ℕ) : Prop :=
  3 ≤ p.length ∧
  p.head? = some 0 ∧
  p.getLast? = some 0 ∧
  (∀ i ∈ p, i < len stones) ∧
  (p.drop 1).Nodup ∧
  (∃ t : ℕ, 1 ≤ t ∧ t + 1 < p.length ∧ p.getD t 0 = len stones - 1)

def maxTwoStep (stones : Slice Std.I64) : ℤ :=
  ((List.range (len stones - 2)).map (fun i => valAt stones (i + 2) - valAt stones i)).foldr max 0

/-- The function returns a result r, and r equals the minimum cost over all finite index sequences p_0,...,p_m such that: m >= 2; p_0 = 0 and p_m = 0; the indices p_1,...,p_m are pairwise distinct (so each stone is the target of at most one jump); and there exists t with 1 <= t < m and p_t = n-1. The cost of such a sequence is max_{0 <= j < m} |stones[p_{j+1}] - stones[p_j]|. The set of such sequences is nonempty (for example 0, n-1, 0), so the minimum is well-defined.
  Preconditions: Let n = len(stones). 2 <= n <= 100000; stones[0] = 0; for every i with 0 <= i < n, 0 <= stones[i] <= 10^9; for every i with 0 <= i < n-1, stones[i] < stones[i+1]. -/
theorem spec_1 (stones : Slice Std.I64) (hpre : Pre stones) :
    ∃ r : Std.I64,
      Aegis.MaxJump.max_jump stones = ok r ∧
        IsLeast {c : ℤ | ∃ p : List ℕ, RoundTrip stones p ∧ cost stones p = c} r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (stones : Slice Std.I64) (hpre : Pre stones), ∃ r : Std.I64,
      Aegis.MaxJump.max_jump stones = ok r ∧
        IsLeast {c : ℤ | ∃ p : List ℕ, RoundTrip stones p ∧ cost stones p = c} r.val) := by
  sorry

/-- Whenever the function returns a result r, r = (if n = 2 then stones[1] - stones[0] else max_{0 <= i <= n-3} (stones[i+2] - stones[i])).
  Preconditions: Let n = len(stones). 2 <= n <= 100000; stones[0] = 0; for every i with 0 <= i < n, 0 <= stones[i] <= 10^9; for every i with 0 <= i < n-1, stones[i] < stones[i+1]. -/
theorem spec_2 (stones : Slice Std.I64) (hpre : Pre stones) (r : Std.I64)
    (h : Aegis.MaxJump.max_jump stones = ok r) :
    r.val =
      (if len stones = 2 then valAt stones 1 - valAt stones 0 else maxTwoStep stones) := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (stones : Slice Std.I64) (hpre : Pre stones) (r : Std.I64)
    (h : Aegis.MaxJump.max_jump stones = ok r), r.val =
      (if len stones = 2 then valAt stones 1 - valAt stones 0 else maxTwoStep stones)) := by
  sorry

/-- The function returns a result r (it does not fail, panic, overflow, or go out of bounds) for every input satisfying the preconditions.
  Preconditions: Let n = len(stones). 2 <= n <= 100000; stones[0] = 0; for every i with 0 <= i < n, 0 <= stones[i] <= 10^9; for every i with 0 <= i < n-1, stones[i] < stones[i+1]. -/
theorem spec_3 (stones : Slice Std.I64) (hpre : Pre stones) :
    ∃ r : Std.I64, Aegis.MaxJump.max_jump stones = ok r := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (stones : Slice Std.I64) (hpre : Pre stones), ∃ r : Std.I64, Aegis.MaxJump.max_jump stones = ok r) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i <= n-3 we have r >= stones[i+2] - stones[i].
  Preconditions: Let n = len(stones). 2 <= n <= 100000; stones[0] = 0; for every i with 0 <= i < n, 0 <= stones[i] <= 10^9; for every i with 0 <= i < n-1, stones[i] < stones[i+1]. -/
theorem spec_4 (stones : Slice Std.I64) (hpre : Pre stones) (r : Std.I64)
    (h : Aegis.MaxJump.max_jump stones = ok r) :
    ∀ i : ℕ, i + 2 < len stones → valAt stones (i + 2) - valAt stones i ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (stones : Slice Std.I64) (hpre : Pre stones) (r : Std.I64)
    (h : Aegis.MaxJump.max_jump stones = ok r), ∀ i : ℕ, i + 2 < len stones → valAt stones (i + 2) - valAt stones i ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= (if n = 2 then stones[1] - stones[0] else max_{0 <= i <= n-3} (stones[i+2] - stones[i])).
  Preconditions: Let n = len(stones). 2 <= n <= 100000; stones[0] = 0; for every i with 0 <= i < n, 0 <= stones[i] <= 10^9; for every i with 0 <= i < n-1, stones[i] < stones[i+1]. -/
theorem spec_5 (stones : Slice Std.I64) (hpre : Pre stones) (r : Std.I64)
    (h : Aegis.MaxJump.max_jump stones = ok r) :
    r.val ≤
      (if len stones = 2 then valAt stones 1 - valAt stones 0 else maxTwoStep stones) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (stones : Slice Std.I64) (hpre : Pre stones) (r : Std.I64)
    (h : Aegis.MaxJump.max_jump stones = ok r), r.val ≤
      (if len stones = 2 then valAt stones 1 - valAt stones 0 else maxTwoStep stones)) := by
  sorry

/-- Whenever the function returns a result r, there exists a finite index sequence p_0,...,p_m satisfying the round-trip conditions from spec_1 whose cost max_{0 <= j < m} |stones[p_{j+1}] - stones[p_j]| is exactly r.
  Preconditions: Let n = len(stones). 2 <= n <= 100000; stones[0] = 0; for every i with 0 <= i < n, 0 <= stones[i] <= 10^9; for every i with 0 <= i < n-1, stones[i] < stones[i+1]. -/
theorem spec_6 (stones : Slice Std.I64) (hpre : Pre stones) (r : Std.I64)
    (h : Aegis.MaxJump.max_jump stones = ok r) :
    ∃ p : List ℕ, RoundTrip stones p ∧ cost stones p = r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (stones : Slice Std.I64) (hpre : Pre stones) (r : Std.I64)
    (h : Aegis.MaxJump.max_jump stones = ok r), ∃ p : List ℕ, RoundTrip stones p ∧ cost stones p = r.val) := by
  sorry

/-- If max_jump(A) returns r_A and max_jump(B) returns r_B, then r_B <= r_A.
  Preconditions: A and B are two arrays each satisfying the common preconditions: len(A) >= 2, len(B) >= 2, A[0] = B[0] = 0, all entries are in [0,10^9], and both are strictly increasing. Additionally every entry of A occurs in B and A[len(A)-1] = B[len(B)-1]. -/
theorem spec_7 (A B : Slice Std.I64) (hA : Pre A) (hB : Pre B)
    (hmono : ∀ x ∈ vals A, x ∈ vals B)
    (hlast : valAt A (len A - 1) = valAt B (len B - 1)) (rA rB : Std.I64)
    (hAres : Aegis.MaxJump.max_jump A = ok rA)
    (hBres : Aegis.MaxJump.max_jump B = ok rB) :
    rB.val ≤ rA.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (A B : Slice Std.I64) (hA : Pre A) (hB : Pre B)
    (hmono : ∀ x ∈ vals A, x ∈ vals B)
    (hlast : valAt A (len A - 1) = valAt B (len B - 1)) (rA rB : Std.I64)
    (hAres : Aegis.MaxJump.max_jump A = ok rA)
    (hBres : Aegis.MaxJump.max_jump B = ok rB), rB.val ≤ rA.val) := by
  sorry

/-- If max_jump(B) returns r_B and max_jump(A) returns r_A, then r_A = c * r_B.
  Preconditions: B is valid: len(B) >= 2, B[0] = 0, 0 <= B[i] <= 10^9 for every i, and B is strictly increasing. Let c be an integer with c >= 1, and let A be the array defined by A[i] = c * B[i] for all i; assume A also satisfies 0 <= A[i] <= 10^9 (hence A is strictly increasing) and A[0] = 0. -/
theorem spec_8 (A B : Slice Std.I64) (hB : Pre B)
    (c : ℤ) (hc : 1 ≤ c)
    (hscale : vals A = (vals B).map (fun x => c * x))
    (hAbound : ∀ i : ℕ, i < len A → 0 ≤ valAt A i ∧ valAt A i ≤ 10 ^ 9)
    (hA0 : valAt A 0 = 0) (rA rB : Std.I64)
    (hAres : Aegis.MaxJump.max_jump A = ok rA)
    (hBres : Aegis.MaxJump.max_jump B = ok rB) :
    rA.val = c * rB.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (A B : Slice Std.I64) (hB : Pre B)
    (c : ℤ) (hc : 1 ≤ c)
    (hscale : vals A = (vals B).map (fun x => c * x))
    (hAbound : ∀ i : ℕ, i < len A → 0 ≤ valAt A i ∧ valAt A i ≤ 10 ^ 9)
    (hA0 : valAt A 0 = 0) (rA rB : Std.I64)
    (hAres : Aegis.MaxJump.max_jump A = ok rA)
    (hBres : Aegis.MaxJump.max_jump B = ok rB), rA.val = c * rB.val) := by
  sorry

end AegisSpec.MaxJump
