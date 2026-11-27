import Aegis.NumRollsToTarget.Code.Funs

/-!
# Specifications of `Aegis.NumRollsToTarget.num_rolls_to_target`

LeetCode problem `number-of-dice-rolls-with-target-sum`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.NumRollsToTarget

  abbrev I64 : Type := Aeneas.Std.I64

  def M : ℕ := 1000000007

  def ways (n k t : ℤ) : ℕ :=
    ((Finset.univ : Finset (Fin n.toNat → Fin k.toNat)).filter
        (fun a => ∑ i, (((a i : ℕ) : ℤ) + 1) = t)).card

  def pairs (k t : ℤ) : ℕ :=
    ((Finset.Icc (1 : ℕ) k.toNat).filter
        (fun (a : ℕ) => 1 ≤ t - (a : ℤ) ∧ t - (a : ℤ) ≤ k)).card

  /-- Let M = 1000000007. Let W be the number of ordered sequences (a_1, ..., a_n) of integers such that 1 <= a_i <= k for every i with 1 <= i <= n, and a_1 + ... + a_n = target. The function returns a result r (it does not fail), and r is the unique integer satisfying 0 <= r < M and r ≡ W (mod M). Equivalently, r is the remainder of W on division by M.
    Preconditions: n, k, and target are integers with 1 <= n <= 30, 1 <= k <= 30, and 1 <= target <= 1000. -/
  theorem spec_1 (n k target : I64)
      (hn_pos : 1 ≤ n.val) (hn_bound : n.val ≤ 30)
      (hk_pos : 1 ≤ k.val) (hk_bound : k.val ≤ 30)
      (ht_pos : 1 ≤ target.val) (ht_bound : target.val ≤ 1000) :
      ∃ r : I64,
        Aegis.NumRollsToTarget.num_rolls_to_target n k target = Aeneas.Std.Result.ok r ∧
          0 ≤ r.val ∧ r.val < (M : ℤ) ∧
          Int.ModEq (M : ℤ) r.val (ways n.val k.val target.val : ℤ) ∧
          ∀ r' : ℤ, 0 ≤ r' → r' < (M : ℤ) →
            Int.ModEq (M : ℤ) r' (ways n.val k.val target.val : ℤ) → r' = r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n k target : I64)
        (hn_pos : 1 ≤ n.val) (hn_bound : n.val ≤ 30)
        (hk_pos : 1 ≤ k.val) (hk_bound : k.val ≤ 30)
        (ht_pos : 1 ≤ target.val) (ht_bound : target.val ≤ 1000), ∃ r : I64,
          Aegis.NumRollsToTarget.num_rolls_to_target n k target = Aeneas.Std.Result.ok r ∧
            0 ≤ r.val ∧ r.val < (M : ℤ) ∧
            Int.ModEq (M : ℤ) r.val (ways n.val k.val target.val : ℤ) ∧
            ∀ r' : ℤ, 0 ≤ r' → r' < (M : ℤ) →
              Int.ModEq (M : ℤ) r' (ways n.val k.val target.val : ℤ) → r' = r.val) := by
    sorry

  /-- Whenever the function returns a result r on an input satisfying the preconditions, 0 <= r < M, where M = 1000000007.
    Preconditions: n, k, and target are integers with 1 <= n <= 30, 1 <= k <= 30, and 1 <= target <= 1000. -/
  theorem spec_2 (n k target r : I64)
      (hn_pos : 1 ≤ n.val) (hn_bound : n.val ≤ 30)
      (hk_pos : 1 ≤ k.val) (hk_bound : k.val ≤ 30)
      (ht_pos : 1 ≤ target.val) (ht_bound : target.val ≤ 1000)
      (hr : Aegis.NumRollsToTarget.num_rolls_to_target n k target = Aeneas.Std.Result.ok r) :
      0 ≤ r.val ∧ r.val < (M : ℤ) := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n k target r : I64)
        (hn_pos : 1 ≤ n.val) (hn_bound : n.val ≤ 30)
        (hk_pos : 1 ≤ k.val) (hk_bound : k.val ≤ 30)
        (ht_pos : 1 ≤ target.val) (ht_bound : target.val ≤ 1000)
        (hr : Aegis.NumRollsToTarget.num_rolls_to_target n k target = Aeneas.Std.Result.ok r), 0 ≤ r.val ∧ r.val < (M : ℤ)) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r (a successful Result containing an i64); it does not overflow, panic, go out of bounds, or otherwise fail.
    Preconditions: n, k, and target are integers with 1 <= n <= 30, 1 <= k <= 30, and 1 <= target <= 1000. -/
  theorem spec_3 (n k target : I64)
      (hn_pos : 1 ≤ n.val) (hn_bound : n.val ≤ 30)
      (hk_pos : 1 ≤ k.val) (hk_bound : k.val ≤ 30)
      (ht_pos : 1 ≤ target.val) (ht_bound : target.val ≤ 1000) :
      ∃ r : I64,
        Aegis.NumRollsToTarget.num_rolls_to_target n k target = Aeneas.Std.Result.ok r := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n k target : I64)
        (hn_pos : 1 ≤ n.val) (hn_bound : n.val ≤ 30)
        (hk_pos : 1 ≤ k.val) (hk_bound : k.val ≤ 30)
        (ht_pos : 1 ≤ target.val) (ht_bound : target.val ≤ 1000), ∃ r : I64,
          Aegis.NumRollsToTarget.num_rolls_to_target n k target = Aeneas.Std.Result.ok r) := by
    sorry

  /-- The function returns r = 0.
    Preconditions: n, k, and target are integers with 1 <= n <= 30, 1 <= k <= 30, 1 <= target <= 1000, and target < n. -/
  theorem spec_4 (n k target : I64)
      (hn_pos : 1 ≤ n.val) (hn_bound : n.val ≤ 30)
      (hk_pos : 1 ≤ k.val) (hk_bound : k.val ≤ 30)
      (ht_pos : 1 ≤ target.val) (ht_bound : target.val ≤ 1000)
      (htarget : target.val < n.val) :
      Aegis.NumRollsToTarget.num_rolls_to_target n k target = Aeneas.Std.Result.ok 0#i64 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n k target : I64)
        (hn_pos : 1 ≤ n.val) (hn_bound : n.val ≤ 30)
        (hk_pos : 1 ≤ k.val) (hk_bound : k.val ≤ 30)
        (ht_pos : 1 ≤ target.val) (ht_bound : target.val ≤ 1000)
        (htarget : target.val < n.val), Aegis.NumRollsToTarget.num_rolls_to_target n k target = Aeneas.Std.Result.ok 0#i64) := by
    sorry

  /-- The function returns r = 1 if 1 <= target <= k, and returns r = 0 if target > k.
    Preconditions: n = 1, 1 <= k <= 30, and 1 <= target <= 1000. -/
  theorem spec_5 (k target : I64)
      (hk_pos : 1 ≤ k.val) (hk_bound : k.val ≤ 30)
      (ht_pos : 1 ≤ target.val) (ht_bound : target.val ≤ 1000) :
      (target.val ≤ k.val →
          Aegis.NumRollsToTarget.num_rolls_to_target 1#i64 k target =
            Aeneas.Std.Result.ok 1#i64) ∧
        (k.val < target.val →
          Aegis.NumRollsToTarget.num_rolls_to_target 1#i64 k target =
            Aeneas.Std.Result.ok 0#i64) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (k target : I64)
        (hk_pos : 1 ≤ k.val) (hk_bound : k.val ≤ 30)
        (ht_pos : 1 ≤ target.val) (ht_bound : target.val ≤ 1000), (target.val ≤ k.val →
            Aegis.NumRollsToTarget.num_rolls_to_target 1#i64 k target =
              Aeneas.Std.Result.ok 1#i64) ∧
          (k.val < target.val →
            Aegis.NumRollsToTarget.num_rolls_to_target 1#i64 k target =
              Aeneas.Std.Result.ok 0#i64)) := by
    sorry

  /-- The function returns r = 1 if target = n, and returns r = 0 otherwise.
    Preconditions: 1 <= n <= 30, k = 1, and 1 <= target <= 1000. -/
  theorem spec_6 (n target : I64)
      (hn_pos : 1 ≤ n.val) (hn_bound : n.val ≤ 30)
      (ht_pos : 1 ≤ target.val) (ht_bound : target.val ≤ 1000) :
      (target.val = n.val →
          Aegis.NumRollsToTarget.num_rolls_to_target n 1#i64 target =
            Aeneas.Std.Result.ok 1#i64) ∧
        (target.val ≠ n.val →
          Aegis.NumRollsToTarget.num_rolls_to_target n 1#i64 target =
            Aeneas.Std.Result.ok 0#i64) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n target : I64)
        (hn_pos : 1 ≤ n.val) (hn_bound : n.val ≤ 30)
        (ht_pos : 1 ≤ target.val) (ht_bound : target.val ≤ 1000), (target.val = n.val →
            Aegis.NumRollsToTarget.num_rolls_to_target n 1#i64 target =
              Aeneas.Std.Result.ok 1#i64) ∧
          (target.val ≠ n.val →
            Aegis.NumRollsToTarget.num_rolls_to_target n 1#i64 target =
              Aeneas.Std.Result.ok 0#i64)) := by
    sorry

  /-- The function returns r = 1.
    Preconditions: 1 <= n <= 30, 1 <= k <= 30, 1 <= target <= 1000, and target = n. -/
  theorem spec_7 (n k target : I64)
      (hn_pos : 1 ≤ n.val) (hn_bound : n.val ≤ 30)
      (hk_pos : 1 ≤ k.val) (hk_bound : k.val ≤ 30)
      (ht_pos : 1 ≤ target.val) (ht_bound : target.val ≤ 1000)
      (htarget : target.val = n.val) :
      Aegis.NumRollsToTarget.num_rolls_to_target n k target = Aeneas.Std.Result.ok 1#i64 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n k target : I64)
        (hn_pos : 1 ≤ n.val) (hn_bound : n.val ≤ 30)
        (hk_pos : 1 ≤ k.val) (hk_bound : k.val ≤ 30)
        (ht_pos : 1 ≤ target.val) (ht_bound : target.val ≤ 1000)
        (htarget : target.val = n.val), Aegis.NumRollsToTarget.num_rolls_to_target n k target = Aeneas.Std.Result.ok 1#i64) := by
    sorry

  /-- Let t = target and t' = n*(k+1) - target. Let r be the function's result on (n, k, t), and let r' be the function's result on (n, k, t'). Then r = r'.
    Preconditions: 1 <= n <= 30, 1 <= k <= 30, 1 <= target <= 1000, and 1 <= n*(k+1) - target <= 1000. -/
  theorem spec_8 (n k target target' : I64)
      (hn_pos : 1 ≤ n.val) (hn_bound : n.val ≤ 30)
      (hk_pos : 1 ≤ k.val) (hk_bound : k.val ≤ 30)
      (ht_pos : 1 ≤ target.val) (ht_bound : target.val ≤ 1000)
      (hreflect_pos : 1 ≤ n.val * (k.val + 1) - target.val)
      (hreflect_bound : n.val * (k.val + 1) - target.val ≤ 1000)
      (htarget' : target'.val = n.val * (k.val + 1) - target.val) :
      Aegis.NumRollsToTarget.num_rolls_to_target n k target =
        Aegis.NumRollsToTarget.num_rolls_to_target n k target' := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n k target target' : I64)
        (hn_pos : 1 ≤ n.val) (hn_bound : n.val ≤ 30)
        (hk_pos : 1 ≤ k.val) (hk_bound : k.val ≤ 30)
        (ht_pos : 1 ≤ target.val) (ht_bound : target.val ≤ 1000)
        (hreflect_pos : 1 ≤ n.val * (k.val + 1) - target.val)
        (hreflect_bound : n.val * (k.val + 1) - target.val ≤ 1000)
        (htarget' : target'.val = n.val * (k.val + 1) - target.val), Aegis.NumRollsToTarget.num_rolls_to_target n k target =
          Aegis.NumRollsToTarget.num_rolls_to_target n k target') := by
    sorry

  /-- Let A be the set of integers a such that 1 <= a <= k and 1 <= target - a <= k. The function returns r = |A| mod M, where M = 1000000007 and |A| is the number of such integers. Since |A| <= 30, this is simply r = |A|.
    Preconditions: n = 2, 1 <= k <= 30, and 1 <= target <= 1000. -/
  theorem spec_9 (k target : I64)
      (hk_pos : 1 ≤ k.val) (hk_bound : k.val ≤ 30)
      (ht_pos : 1 ≤ target.val) (ht_bound : target.val ≤ 1000) :
      ∃ r : I64,
        Aegis.NumRollsToTarget.num_rolls_to_target 2#i64 k target =
            Aeneas.Std.Result.ok r ∧
          r.val = (((pairs k.val target.val) % M : ℕ) : ℤ) ∧
          r.val = (pairs k.val target.val : ℤ) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (k target : I64)
        (hk_pos : 1 ≤ k.val) (hk_bound : k.val ≤ 30)
        (ht_pos : 1 ≤ target.val) (ht_bound : target.val ≤ 1000), ∃ r : I64,
          Aegis.NumRollsToTarget.num_rolls_to_target 2#i64 k target =
              Aeneas.Std.Result.ok r ∧
            r.val = (((pairs k.val target.val) % M : ℕ) : ℤ) ∧
            r.val = (pairs k.val target.val : ℤ)) := by
    sorry

  /-- Let m = target - n. If 0 <= m <= n, the function returns r = binomial(n, m) mod M, where M = 1000000007; if m < 0 or m > n, the function returns r = 0.
    Preconditions: 1 <= n <= 30, k = 2, and 1 <= target <= 1000. -/
  theorem spec_10 (n target : I64)
      (hn_pos : 1 ≤ n.val) (hn_bound : n.val ≤ 30)
      (ht_pos : 1 ≤ target.val) (ht_bound : target.val ≤ 1000) :
      (0 ≤ target.val - n.val ∧ target.val - n.val ≤ n.val →
          ∃ r : I64,
            Aegis.NumRollsToTarget.num_rolls_to_target n 2#i64 target =
                Aeneas.Std.Result.ok r ∧
              0 ≤ r.val ∧ r.val < (M : ℤ) ∧
              Int.ModEq (M : ℤ) r.val
                (Nat.choose n.val.toNat (target.val - n.val).toNat : ℤ)) ∧
        (target.val - n.val < 0 ∨ n.val < target.val - n.val →
          Aegis.NumRollsToTarget.num_rolls_to_target n 2#i64 target =
            Aeneas.Std.Result.ok 0#i64) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n target : I64)
        (hn_pos : 1 ≤ n.val) (hn_bound : n.val ≤ 30)
        (ht_pos : 1 ≤ target.val) (ht_bound : target.val ≤ 1000), (0 ≤ target.val - n.val ∧ target.val - n.val ≤ n.val →
            ∃ r : I64,
              Aegis.NumRollsToTarget.num_rolls_to_target n 2#i64 target =
                  Aeneas.Std.Result.ok r ∧
                0 ≤ r.val ∧ r.val < (M : ℤ) ∧
                Int.ModEq (M : ℤ) r.val
                  (Nat.choose n.val.toNat (target.val - n.val).toNat : ℤ)) ∧
          (target.val - n.val < 0 ∨ n.val < target.val - n.val →
            Aegis.NumRollsToTarget.num_rolls_to_target n 2#i64 target =
              Aeneas.Std.Result.ok 0#i64)) := by
    sorry

  /-- For every integer k' with k <= k' <= 30, the function's result on (n, k, target) equals its result on (n, k', target).
    Preconditions: 1 <= n <= 30, 1 <= k <= 30, 1 <= target <= 1000, and target <= k. -/
  theorem spec_11 (n k target k' : I64)
      (hn_pos : 1 ≤ n.val) (hn_bound : n.val ≤ 30)
      (hk_pos : 1 ≤ k.val) (hk_bound : k.val ≤ 30)
      (ht_pos : 1 ≤ target.val) (ht_bound : target.val ≤ 1000)
      (htarget : target.val ≤ k.val)
      (hkk' : k.val ≤ k'.val) (hk'_bound : k'.val ≤ 30) :
      Aegis.NumRollsToTarget.num_rolls_to_target n k target =
        Aegis.NumRollsToTarget.num_rolls_to_target n k' target := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (n k target k' : I64)
        (hn_pos : 1 ≤ n.val) (hn_bound : n.val ≤ 30)
        (hk_pos : 1 ≤ k.val) (hk_bound : k.val ≤ 30)
        (ht_pos : 1 ≤ target.val) (ht_bound : target.val ≤ 1000)
        (htarget : target.val ≤ k.val)
        (hkk' : k.val ≤ k'.val) (hk'_bound : k'.val ≤ 30), Aegis.NumRollsToTarget.num_rolls_to_target n k target =
          Aegis.NumRollsToTarget.num_rolls_to_target n k' target) := by
    sorry

  /-- Let W be the number of ordered sequences (a_1, ..., a_n) of integers such that 1 <= a_i <= k for every i and a_1 + ... + a_n = target. Whenever the function returns a result r with r != 0, there exists at least one such sequence; equivalently, W > 0.
    Preconditions: n, k, and target are integers with 1 <= n <= 30, 1 <= k <= 30, and 1 <= target <= 1000. -/
  theorem spec_12 (n k target r : I64)
      (hn_pos : 1 ≤ n.val) (hn_bound : n.val ≤ 30)
      (hk_pos : 1 ≤ k.val) (hk_bound : k.val ≤ 30)
      (ht_pos : 1 ≤ target.val) (ht_bound : target.val ≤ 1000)
      (hr : Aegis.NumRollsToTarget.num_rolls_to_target n k target = Aeneas.Std.Result.ok r)
      (hr_ne : r.val ≠ 0) :
      0 < ways n.val k.val target.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (n k target r : I64)
        (hn_pos : 1 ≤ n.val) (hn_bound : n.val ≤ 30)
        (hk_pos : 1 ≤ k.val) (hk_bound : k.val ≤ 30)
        (ht_pos : 1 ≤ target.val) (ht_bound : target.val ≤ 1000)
        (hr : Aegis.NumRollsToTarget.num_rolls_to_target n k target = Aeneas.Std.Result.ok r)
        (hr_ne : r.val ≠ 0), 0 < ways n.val k.val target.val) := by
    sorry

  /-- Let W be the number of ordered sequences (a_1, ..., a_n) of integers such that 1 <= a_i <= k for every i and a_1 + ... + a_n = target. If W < M, where M = 1000000007, then the function returns r = W.
    Preconditions: n, k, and target are integers with 1 <= n <= 30, 1 <= k <= 30, and 1 <= target <= 1000. -/
  theorem spec_13 (n k target : I64)
      (hn_pos : 1 ≤ n.val) (hn_bound : n.val ≤ 30)
      (hk_pos : 1 ≤ k.val) (hk_bound : k.val ≤ 30)
      (ht_pos : 1 ≤ target.val) (ht_bound : target.val ≤ 1000)
      (hW : ways n.val k.val target.val < M) :
      ∃ r : I64,
        Aegis.NumRollsToTarget.num_rolls_to_target n k target = Aeneas.Std.Result.ok r ∧
          r.val = (ways n.val k.val target.val : ℤ) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (n k target : I64)
        (hn_pos : 1 ≤ n.val) (hn_bound : n.val ≤ 30)
        (hk_pos : 1 ≤ k.val) (hk_bound : k.val ≤ 30)
        (ht_pos : 1 ≤ target.val) (ht_bound : target.val ≤ 1000)
        (hW : ways n.val k.val target.val < M), ∃ r : I64,
          Aegis.NumRollsToTarget.num_rolls_to_target n k target = Aeneas.Std.Result.ok r ∧
            r.val = (ways n.val k.val target.val : ℤ)) := by
    sorry

  end AegisSpec.NumRollsToTarget
