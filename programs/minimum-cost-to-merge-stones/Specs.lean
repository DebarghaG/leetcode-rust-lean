import Aegis.MergeStones.Code.Funs

/-!
# Specifications of `Aegis.MergeStones.merge_stones`

LeetCode problem `minimum-cost-to-merge-stones`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MergeStones

abbrev Config : Type := List Int

def LegalMove (k : Nat) (cur next : Config) (cost : Int) : Prop :=
  ∃ j : Nat,
    j + k ≤ cur.length ∧
      next = cur.take j ++ [((cur.drop j).take k).sum] ++ cur.drop (j + k) ∧
      cost = ((cur.drop j).take k).sum

inductive MovesN (k : Nat) : Config → Config → Nat → Int → Prop where
  | refl (cur : Config) : MovesN k cur cur (0 : Nat) (0 : Int)
  | step {cur mid last : Config} {steps : Nat} {c t : Int} :
      LegalMove k cur mid c → MovesN k mid last steps t → MovesN k cur last (steps + 1) (c + t)

def Moves (k : Nat) (cur next : Config) (cost : Int) : Prop :=
  ∃ steps : Nat, MovesN k cur next steps cost

def IsReduction (k : Nat) (l : Config) (cost : Int) : Prop :=
  ∃ last : Config, last.length = 1 ∧ Moves k l last cost

def IsReductionWith (k : Nat) (l : Config) (steps : Nat) (cost : Int) : Prop :=
  ∃ last : Config, last.length = 1 ∧ MovesN k l last steps cost

def Opt (k : Nat) (l : Config) (r : Int) : Prop :=
  IsReduction k l r ∧ ∀ c : Int, IsReduction k l c → r ≤ c

def config (stones : Slice Std.I64) : Config := stones.val.map (fun x => x.val)

def numPiles (stones : Slice Std.I64) : Nat := stones.val.length

def kNat (k : Std.I64) : Nat := k.val.toNat

def totalSum (stones : Slice Std.I64) : Int := (config stones).sum

def modCond (stones : Slice Std.I64) (k : Std.I64) : Nat := (numPiles stones - 1) % (kNat k - 1)

/-- The function returns a result r and: if n = 1, then r = 0; if n > 1 and (n - 1) mod (k - 1) is nonzero, then r = -1; if n > 1 and (n - 1) mod (k - 1) is zero, then r = Opt(stones,k). Equivalently, r is the minimum possible total cost of merging all piles into one pile, or -1 exactly when no legal reduction exists.
  Preconditions: Let n = len(stones). Assume 1 <= n <= 30; for every i with 0 <= i < n, 1 <= stones[i] <= 100; and 2 <= k <= 30. A legal move on a current list of pile sizes chooses an index j with 0 <= j and j + k <= len(current), replaces current[j],...,current[j+k-1] by their sum at that position, leaves the other entries in order, and has cost equal to that sum. A legal reduction is a finite sequence of legal moves ending with a one-element list; its total cost is the sum of the costs of its moves. Define Opt(stones,k) to be the minimum total cost among all legal reductions of stones using exactly k consecutive piles per move. -/
theorem spec_1 (stones : Slice Std.I64) (k : Std.I64)
    (hn_lb : 1 ≤ numPiles stones) (hn_ub : numPiles stones ≤ 30)
    (hstones : ∀ (i : Nat) (hi : i < numPiles stones),
      1 ≤ (stones.val[i]).val ∧ (stones.val[i]).val ≤ 100)
    (hk_lb : 2 ≤ k.val) (hk_ub : k.val ≤ 30) :
    ∃ r : Std.I64,
      Aegis.MergeStones.merge_stones stones k = ok r ∧
        (numPiles stones = 1 → r.val = 0) ∧
        (1 < numPiles stones → modCond stones k ≠ 0 → r.val = -1) ∧
        (1 < numPiles stones → modCond stones k = 0 → Opt (kNat k) (config stones) r.val) ∧

        (r.val = -1 ↔ ¬ ∃ c : Int, IsReduction (kNat k) (config stones) c) ∧
        (0 ≤ r.val → Opt (kNat k) (config stones) r.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (stones : Slice Std.I64) (k : Std.I64)
    (hn_lb : 1 ≤ numPiles stones) (hn_ub : numPiles stones ≤ 30)
    (hstones : ∀ (i : Nat) (hi : i < numPiles stones),
      1 ≤ (stones.val[i]).val ∧ (stones.val[i]).val ≤ 100)
    (hk_lb : 2 ≤ k.val) (hk_ub : k.val ≤ 30), ∃ r : Std.I64,
      Aegis.MergeStones.merge_stones stones k = ok r ∧
        (numPiles stones = 1 → r.val = 0) ∧
        (1 < numPiles stones → modCond stones k ≠ 0 → r.val = -1) ∧
        (1 < numPiles stones → modCond stones k = 0 → Opt (kNat k) (config stones) r.val) ∧

        (r.val = -1 ↔ ¬ ∃ c : Int, IsReduction (kNat k) (config stones) c) ∧
        (0 ≤ r.val → Opt (kNat k) (config stones) r.val)) := by
  sorry

/-- The function returns a result r; it does not fail by panic, out-of-bounds access, division by zero, or signed 64-bit overflow.
  Preconditions: Let n = len(stones). Assume 1 <= n <= 30; for every i with 0 <= i < n, 1 <= stones[i] <= 100; and 2 <= k <= 30. -/
theorem spec_2 (stones : Slice Std.I64) (k : Std.I64)
    (hn_lb : 1 ≤ numPiles stones) (hn_ub : numPiles stones ≤ 30)
    (hstones : ∀ (i : Nat) (hi : i < numPiles stones),
      1 ≤ (stones.val[i]).val ∧ (stones.val[i]).val ≤ 100)
    (hk_lb : 2 ≤ k.val) (hk_ub : k.val ≤ 30) :
    ∃ r : Std.I64, Aegis.MergeStones.merge_stones stones k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (stones : Slice Std.I64) (k : Std.I64)
    (hn_lb : 1 ≤ numPiles stones) (hn_ub : numPiles stones ≤ 30)
    (hstones : ∀ (i : Nat) (hi : i < numPiles stones),
      1 ≤ (stones.val[i]).val ∧ (stones.val[i]).val ≤ 100)
    (hk_lb : 2 ≤ k.val) (hk_ub : k.val ≤ 30), ∃ r : Std.I64, Aegis.MergeStones.merge_stones stones k = ok r) := by
  sorry

/-- The function returns a result r with r >= S.
  Preconditions: Let n = len(stones), S = stones[0] + ... + stones[n-1]. Assume n > 1; 1 <= n <= 30; for every i with 0 <= i < n, 1 <= stones[i] <= 100; 2 <= k <= 30; and (n - 1) mod (k - 1) is zero. -/
theorem spec_3 (stones : Slice Std.I64) (k : Std.I64)
    (hn_gt1 : 1 < numPiles stones) (hn_lb : 1 ≤ numPiles stones) (hn_ub : numPiles stones ≤ 30)
    (hstones : ∀ (i : Nat) (hi : i < numPiles stones),
      1 ≤ (stones.val[i]).val ∧ (stones.val[i]).val ≤ 100)
    (hk_lb : 2 ≤ k.val) (hk_ub : k.val ≤ 30) (hmod : modCond stones k = 0) :
    ∃ r : Std.I64,
      Aegis.MergeStones.merge_stones stones k = ok r ∧ totalSum stones ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (stones : Slice Std.I64) (k : Std.I64)
    (hn_gt1 : 1 < numPiles stones) (hn_lb : 1 ≤ numPiles stones) (hn_ub : numPiles stones ≤ 30)
    (hstones : ∀ (i : Nat) (hi : i < numPiles stones),
      1 ≤ (stones.val[i]).val ∧ (stones.val[i]).val ≤ 100)
    (hk_lb : 2 ≤ k.val) (hk_ub : k.val ≤ 30) (hmod : modCond stones k = 0), ∃ r : Std.I64,
      Aegis.MergeStones.merge_stones stones k = ok r ∧ totalSum stones ≤ r.val) := by
  sorry

/-- The function returns a result r with r <= M * S.
  Preconditions: Let n = len(stones), S = stones[0] + ... + stones[n-1], and M = (n - 1) / (k - 1). Assume n > 1; 1 <= n <= 30; for every i with 0 <= i < n, 1 <= stones[i] <= 100; 2 <= k <= 30; and (n - 1) mod (k - 1) is zero. -/
theorem spec_4 (stones : Slice Std.I64) (k : Std.I64)
    (hn_gt1 : 1 < numPiles stones) (hn_lb : 1 ≤ numPiles stones) (hn_ub : numPiles stones ≤ 30)
    (hstones : ∀ (i : Nat) (hi : i < numPiles stones),
      1 ≤ (stones.val[i]).val ∧ (stones.val[i]).val ≤ 100)
    (hk_lb : 2 ≤ k.val) (hk_ub : k.val ≤ 30) (hmod : modCond stones k = 0) :
    ∃ r : Std.I64,
      Aegis.MergeStones.merge_stones stones k = ok r ∧
        r.val ≤ (((numPiles stones - 1) / (kNat k - 1) : Nat) : Int) * totalSum stones := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (stones : Slice Std.I64) (k : Std.I64)
    (hn_gt1 : 1 < numPiles stones) (hn_lb : 1 ≤ numPiles stones) (hn_ub : numPiles stones ≤ 30)
    (hstones : ∀ (i : Nat) (hi : i < numPiles stones),
      1 ≤ (stones.val[i]).val ∧ (stones.val[i]).val ≤ 100)
    (hk_lb : 2 ≤ k.val) (hk_ub : k.val ≤ 30) (hmod : modCond stones k = 0), ∃ r : Std.I64,
      Aegis.MergeStones.merge_stones stones k = ok r ∧
        r.val ≤ (((numPiles stones - 1) / (kNat k - 1) : Nat) : Int) * totalSum stones) := by
  sorry

/-- The function returns a result r with r > S.
  Preconditions: Let n = len(stones), S = stones[0] + ... + stones[n-1]. Assume n > k; for every i with 0 <= i < n, 1 <= stones[i] <= 100; 2 <= k <= 30; and (n - 1) mod (k - 1) is zero. -/
theorem spec_5 (stones : Slice Std.I64) (k : Std.I64)
    (hnk : kNat k < numPiles stones)
    (hstones : ∀ (i : Nat) (hi : i < numPiles stones),
      1 ≤ (stones.val[i]).val ∧ (stones.val[i]).val ≤ 100)
    (hk_lb : 2 ≤ k.val) (hk_ub : k.val ≤ 30) (hmod : modCond stones k = 0) :
    ∃ r : Std.I64,
      Aegis.MergeStones.merge_stones stones k = ok r ∧ totalSum stones < r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (stones : Slice Std.I64) (k : Std.I64)
    (hnk : kNat k < numPiles stones)
    (hstones : ∀ (i : Nat) (hi : i < numPiles stones),
      1 ≤ (stones.val[i]).val ∧ (stones.val[i]).val ≤ 100)
    (hk_lb : 2 ≤ k.val) (hk_ub : k.val ≤ 30) (hmod : modCond stones k = 0), ∃ r : Std.I64,
      Aegis.MergeStones.merge_stones stones k = ok r ∧ totalSum stones < r.val) := by
  sorry

/-- Whenever the function returns a value r with r >= 0, there exists a legal reduction of stones whose total cost is exactly r.
  Preconditions: Let n = len(stones). Assume 1 <= n <= 30; for every i with 0 <= i < n, 1 <= stones[i] <= 100; and 2 <= k <= 30. A legal reduction is a finite sequence of legal moves, each merging exactly k consecutive current piles and costing their sum, ending with one pile. -/
theorem spec_6 (stones : Slice Std.I64) (k : Std.I64)
    (hn_lb : 1 ≤ numPiles stones) (hn_ub : numPiles stones ≤ 30)
    (hstones : ∀ (i : Nat) (hi : i < numPiles stones),
      1 ≤ (stones.val[i]).val ∧ (stones.val[i]).val ≤ 100)
    (hk_lb : 2 ≤ k.val) (hk_ub : k.val ≤ 30) :
    ∀ (r : Std.I64), Aegis.MergeStones.merge_stones stones k = ok r → 0 ≤ r.val →
      IsReduction (kNat k) (config stones) r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (stones : Slice Std.I64) (k : Std.I64)
    (hn_lb : 1 ≤ numPiles stones) (hn_ub : numPiles stones ≤ 30)
    (hstones : ∀ (i : Nat) (hi : i < numPiles stones),
      1 ≤ (stones.val[i]).val ∧ (stones.val[i]).val ≤ 100)
    (hk_lb : 2 ≤ k.val) (hk_ub : k.val ≤ 30), ∀ (r : Std.I64), Aegis.MergeStones.merge_stones stones k = ok r → 0 ≤ r.val →
      IsReduction (kNat k) (config stones) r.val) := by
  sorry

/-- Whenever the function returns a value r with r >= 0, every legal reduction of stones has total cost at least r.
  Preconditions: Let n = len(stones). Assume 1 <= n <= 30; for every i with 0 <= i < n, 1 <= stones[i] <= 100; and 2 <= k <= 30. A legal reduction is a finite sequence of legal moves, each merging exactly k consecutive current piles and costing their sum, ending with one pile. -/
theorem spec_7 (stones : Slice Std.I64) (k : Std.I64)
    (hn_lb : 1 ≤ numPiles stones) (hn_ub : numPiles stones ≤ 30)
    (hstones : ∀ (i : Nat) (hi : i < numPiles stones),
      1 ≤ (stones.val[i]).val ∧ (stones.val[i]).val ≤ 100)
    (hk_lb : 2 ≤ k.val) (hk_ub : k.val ≤ 30) :
    ∀ (r : Std.I64), Aegis.MergeStones.merge_stones stones k = ok r → 0 ≤ r.val →
      ∀ c : Int, IsReduction (kNat k) (config stones) c → r.val ≤ c := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (stones : Slice Std.I64) (k : Std.I64)
    (hn_lb : 1 ≤ numPiles stones) (hn_ub : numPiles stones ≤ 30)
    (hstones : ∀ (i : Nat) (hi : i < numPiles stones),
      1 ≤ (stones.val[i]).val ∧ (stones.val[i]).val ≤ 100)
    (hk_lb : 2 ≤ k.val) (hk_ub : k.val ≤ 30), ∀ (r : Std.I64), Aegis.MergeStones.merge_stones stones k = ok r → 0 ≤ r.val →
      ∀ c : Int, IsReduction (kNat k) (config stones) c → r.val ≤ c) := by
  sorry

/-- Suppose merge_stones(stones,k) returns r and merge_stones(stones_c,k) returns r_c. If r = -1, then r_c = -1; if r >= 0, then r_c = c * r, with multiplication interpreted over mathematical integers.
  Preconditions: Let n = len(stones). Assume 1 <= n <= 30; for every i with 0 <= i < n, 1 <= stones[i] <= 100; and 2 <= k <= 30. Let c be a positive integer such that for every i with 0 <= i < n, 1 <= c * stones[i] <= 100, and let stones_c be the slice defined by stones_c[i] = c * stones[i]. -/
theorem spec_8 (stones stones_c : Slice Std.I64) (k : Std.I64) (c : Nat)
    (hn_lb : 1 ≤ numPiles stones) (hn_ub : numPiles stones ≤ 30)
    (hstones : ∀ (i : Nat) (hi : i < numPiles stones),
      1 ≤ (stones.val[i]).val ∧ (stones.val[i]).val ≤ 100)
    (hk_lb : 2 ≤ k.val) (hk_ub : k.val ≤ 30)
    (hc_pos : 0 < c)
    (hc_bound_lb : ∀ (i : Nat) (hi : i < numPiles stones), 1 ≤ (c : Int) * (stones.val[i]).val)
    (hc_bound_ub : ∀ (i : Nat) (hi : i < numPiles stones), (c : Int) * (stones.val[i]).val ≤ 100)
    (hc_config : config stones_c = (config stones).map (fun x => (c : Int) * x)) :
    ∀ (r r_c : Std.I64),
      Aegis.MergeStones.merge_stones stones k = ok r →
        Aegis.MergeStones.merge_stones stones_c k = ok r_c →
          (r.val = -1 → r_c.val = -1) ∧ (0 ≤ r.val → r_c.val = (c : Int) * r.val) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (stones stones_c : Slice Std.I64) (k : Std.I64) (c : Nat)
    (hn_lb : 1 ≤ numPiles stones) (hn_ub : numPiles stones ≤ 30)
    (hstones : ∀ (i : Nat) (hi : i < numPiles stones),
      1 ≤ (stones.val[i]).val ∧ (stones.val[i]).val ≤ 100)
    (hk_lb : 2 ≤ k.val) (hk_ub : k.val ≤ 30)
    (hc_pos : 0 < c)
    (hc_bound_lb : ∀ (i : Nat) (hi : i < numPiles stones), 1 ≤ (c : Int) * (stones.val[i]).val)
    (hc_bound_ub : ∀ (i : Nat) (hi : i < numPiles stones), (c : Int) * (stones.val[i]).val ≤ 100)
    (hc_config : config stones_c = (config stones).map (fun x => (c : Int) * x)), ∀ (r r_c : Std.I64),
      Aegis.MergeStones.merge_stones stones k = ok r →
        Aegis.MergeStones.merge_stones stones_c k = ok r_c →
          (r.val = -1 → r_c.val = -1) ∧ (0 ≤ r.val → r_c.val = (c : Int) * r.val)) := by
  sorry

/-- If r_a = -1, then r_b = -1; if r_a >= 0, then r_b >= r_a.
  Preconditions: Let n = len(stones). Assume 1 <= n <= 30; 2 <= k <= 30. Let a and b be two slices of length n with 1 <= a[i] <= b[i] <= 100 for every i with 0 <= i < n. Suppose merge_stones(a,k) returns r_a and merge_stones(b,k) returns r_b. -/
theorem spec_9 (a b : Slice Std.I64) (k : Std.I64)
    (hn_lb : 1 ≤ numPiles a) (hn_ub : numPiles a ≤ 30)
    (hlen : numPiles b = numPiles a)
    (hk_lb : 2 ≤ k.val) (hk_ub : k.val ≤ 30)
    (ha_lb : ∀ (i : Nat) (hi : i < numPiles a), 1 ≤ (a.val[i]).val)
    (hab : ∀ (i : Nat) (hia : i < numPiles a) (hib : i < numPiles b),
      (a.val[i]).val ≤ (b.val[i]).val)
    (hb_ub : ∀ (i : Nat) (hi : i < numPiles b), (b.val[i]).val ≤ 100) :
    ∀ (r_a r_b : Std.I64),
      Aegis.MergeStones.merge_stones a k = ok r_a →
        Aegis.MergeStones.merge_stones b k = ok r_b →
          (r_a.val = -1 → r_b.val = -1) ∧ (0 ≤ r_a.val → r_a.val ≤ r_b.val) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (a b : Slice Std.I64) (k : Std.I64)
    (hn_lb : 1 ≤ numPiles a) (hn_ub : numPiles a ≤ 30)
    (hlen : numPiles b = numPiles a)
    (hk_lb : 2 ≤ k.val) (hk_ub : k.val ≤ 30)
    (ha_lb : ∀ (i : Nat) (hi : i < numPiles a), 1 ≤ (a.val[i]).val)
    (hab : ∀ (i : Nat) (hia : i < numPiles a) (hib : i < numPiles b),
      (a.val[i]).val ≤ (b.val[i]).val)
    (hb_ub : ∀ (i : Nat) (hi : i < numPiles b), (b.val[i]).val ≤ 100), ∀ (r_a r_b : Std.I64),
      Aegis.MergeStones.merge_stones a k = ok r_a →
        Aegis.MergeStones.merge_stones b k = ok r_b →
          (r_a.val = -1 → r_b.val = -1) ∧ (0 ≤ r_a.val → r_a.val ≤ r_b.val)) := by
  sorry

end AegisSpec.MergeStones
