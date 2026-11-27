import Aegis.WaysToReachStair.Code.Funs

/-!
# Specifications of `Aegis.WaysToReachStair.ways_to_reach_stair`

LeetCode problem `find-number-of-ways-to-reach-the-k-th-stair`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.WaysToReachStair

def binom (a b : ℤ) : ℤ :=
  if 0 ≤ b ∧ b ≤ a then (a.toNat.choose b.toNat : ℤ) else 0

inductive Op where
  | up
  | down
  deriving DecidableEq, Repr

structure St where
  stair : ℤ
  jump : ℕ
  deriving DecidableEq, Repr

def initSt : St := ⟨1, 0⟩

def stepOp (s : St) (o : Op) : St :=
  match o with
  | Op.up => ⟨s.stair + 2 ^ s.jump, s.jump + 1⟩
  | Op.down => ⟨s.stair - 1, s.jump⟩

def runOps (ops : List Op) : St := ops.foldl stepOp initSt

def upsCount : List Op → ℕ
  | [] => 0
  | Op.up :: rest => upsCount rest + 1
  | Op.down :: rest => upsCount rest

def legalAux : Option Op → St → List Op → Bool
  | _, _, [] => true
  | prev, s, o :: rest =>
    (match o with
      | Op.up => true
      | Op.down =>
        match prev with
        | some Op.down => false
        | _ => decide (0 < s.stair)) &&
      legalAux (some o) (stepOp s o) rest

def Legal (ops : List Op) : Prop := legalAux none initSt ops = true

def P (k : ℤ) : Set (List Op) := {ops | Legal ops ∧ (runOps ops).stair = k}

noncomputable def waysWithUps (k : ℤ) (n : ℕ) : ℕ :=
  {ops : List Op | Legal ops ∧ (runOps ops).stair = k ∧ upsCount ops = n}.ncard

/-- Let binom(a,b) denote the usual binomial coefficient for integers a,b, with the convention binom(a,b)=0 when b<0 or b>a. The function returns a result r and r = sum_{n=0}^{29} binom(n+1, 2^n - k).
  Preconditions: 0 <= k <= 1000000000. -/
theorem spec_1 (k : Std.I64) (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ 1000000000) :
    ∃ r, Aegis.WaysToReachStair.ways_to_reach_stair k = ok r ∧
      r.val = ∑ n ∈ Finset.range 30, binom ((n : ℤ) + 1) ((2 : ℤ) ^ n - k.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (k : Std.I64) (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ 1000000000), ∃ r, Aegis.WaysToReachStair.ways_to_reach_stair k = ok r ∧
      r.val = ∑ n ∈ Finset.range 30, binom ((n : ℤ) + 1) ((2 : ℤ) ^ n - k.val)) := by
  sorry

/-- The function returns a result r; in particular, for every k satisfying the precondition it does not fail (no integer overflow, out-of-bounds access, or panic).
  Preconditions: 0 <= k <= 1000000000. -/
theorem spec_2 (k : Std.I64) (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ 1000000000) :
    ∃ r, Aegis.WaysToReachStair.ways_to_reach_stair k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (k : Std.I64) (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ 1000000000), ∃ r, Aegis.WaysToReachStair.ways_to_reach_stair k = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r.
  Preconditions: 0 <= k <= 1000000000. -/
theorem spec_3 (k : Std.I64) (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ 1000000000) :
    ∀ r, Aegis.WaysToReachStair.ways_to_reach_stair k = ok r → 0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (k : Std.I64) (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ 1000000000), ∀ r, Aegis.WaysToReachStair.ways_to_reach_stair k = ok r → 0 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= 155117520.
  Preconditions: 0 <= k <= 1000000000. -/
theorem spec_4 (k : Std.I64) (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ 1000000000) :
    ∀ r, Aegis.WaysToReachStair.ways_to_reach_stair k = ok r → r.val ≤ 155117520 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (k : Std.I64) (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ 1000000000), ∀ r, Aegis.WaysToReachStair.ways_to_reach_stair k = ok r → r.val ≤ 155117520) := by
  sorry

/-- Consider finite sequences of operations under these rules: the initial state is (stair 1, jump 0); an up operation changes (s,j) to (s+2^j, j+1); a down operation changes (s,j) to (s-1,j) and is legal only if s>0 and the immediately preceding operation was not a down operation. Let P_k be the set of all legal finite operation sequences whose final stair is k, where the sequence is counted in full even if it visited stair k earlier. Whenever the function returns a result r, r = |P_k|.
  Preconditions: 0 <= k <= 1000000000. -/
theorem spec_5 (k : Std.I64) (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ 1000000000) :
    ∀ r, Aegis.WaysToReachStair.ways_to_reach_stair k = ok r →
      r.val = ((P k.val).ncard : ℤ) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (k : Std.I64) (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ 1000000000), ∀ r, Aegis.WaysToReachStair.ways_to_reach_stair k = ok r →
      r.val = ((P k.val).ncard : ℤ)) := by
  sorry

/-- Let binom(a,b) be the binomial coefficient, taken as 0 when b<0 or b>a. Let n be the unique integer satisfying 2^(n-1) < k <= 2^n (equivalently, the smallest integer n with 2^n >= k), and let m = 2^n - k. Whenever the function returns a result r, r = binom(n+1, m) if 0 <= m <= n+1, and r = 0 otherwise.
  Preconditions: 0 <= k <= 1000000000 and k >= 5. -/
theorem spec_6 (k : Std.I64) (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ 1000000000) (hk5 : 5 ≤ k.val)
    (n : ℕ) (hn1 : 1 ≤ n) (hn : (2 : ℤ) ^ (n - 1) < k.val ∧ k.val ≤ (2 : ℤ) ^ n) :
    ∀ r, Aegis.WaysToReachStair.ways_to_reach_stair k = ok r →
      r.val = binom ((n : ℤ) + 1) ((2 : ℤ) ^ n - k.val) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (k : Std.I64) (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ 1000000000) (hk5 : 5 ≤ k.val)
    (n : ℕ) (hn1 : 1 ≤ n) (hn : (2 : ℤ) ^ (n - 1) < k.val ∧ k.val ≤ (2 : ℤ) ^ n), ∀ r, Aegis.WaysToReachStair.ways_to_reach_stair k = ok r →
      r.val = binom ((n : ℤ) + 1) ((2 : ℤ) ^ n - k.val)) := by
  sorry

/-- Whenever the function returns a result r, r > 0 if and only if there exists an integer n with 0 <= n <= 29 such that 2^n - (n+1) <= k <= 2^n.
  Preconditions: 0 <= k <= 1000000000. -/
theorem spec_7 (k : Std.I64) (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ 1000000000) :
    ∀ r, Aegis.WaysToReachStair.ways_to_reach_stair k = ok r →
      (0 < r.val ↔
        ∃ n : ℕ, n ≤ 29 ∧ (2 : ℤ) ^ n - ((n : ℤ) + 1) ≤ k.val ∧ k.val ≤ (2 : ℤ) ^ n) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (k : Std.I64) (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ 1000000000), ∀ r, Aegis.WaysToReachStair.ways_to_reach_stair k = ok r →
      (0 < r.val ↔
        ∃ n : ℕ, n ≤ 29 ∧ (2 : ℤ) ^ n - ((n : ℤ) + 1) ≤ k.val ∧ k.val ≤ (2 : ℤ) ^ n)) := by
  sorry

end AegisSpec.WaysToReachStair
