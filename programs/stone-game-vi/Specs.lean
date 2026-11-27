import Aegis.StoneGameVi.Code.Funs

/-!
# Specifications of `Aegis.StoneGameVi.stone_game_vi`

LeetCode problem `stone-game-vi`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.StoneGameVi

local notation "stone_game_vi" => Aegis.StoneGameVi.stone_game_vi

def getI (s : Slice Std.I64) (i : Nat) : Int :=
  ((s.val[i]?).map (fun x => x.val)).getD 0

def pairSum (alice_values bob_values : Slice Std.I64) (i : Nat) : Int :=
  getI alice_values i + getI bob_values i

def sumRange (n : Nat) (f : Nat → Int) : Int :=
  ((List.range n).map f).sum

def sumEven (n : Nat) (f : Nat → Int) : Int :=
  (((List.range n).filter (fun k => k % 2 == 0)).map f).sum

def sumOdd (n : Nat) (f : Nat → Int) : Int :=
  (((List.range n).filter (fun k => k % 2 == 1)).map f).sum

def IsPermutation (n : Nat) (σ : Nat → Nat) : Prop :=
  (∀ i, i < n → σ i < n) ∧ (∀ i j, i < n → j < n → σ i = σ j → i = j)

def countVal (s : Slice Std.I64) (n : Nat) (v : Int) : Nat :=
  ((s.val.take n).filter (fun x => x.val == v)).length

def AllCountsEven (s : Slice Std.I64) (n : Nat) : Prop :=
  ∀ v : Int, 0 < countVal s n v → countVal s n v % 2 = 0

/-- For every valid input, whenever the function returns a result r, the following holds. Let sigma be any permutation of {0,...,n-1} such that alice_values[sigma(k)] + bob_values[sigma(k)] >= alice_values[sigma(k+1)] + bob_values[sigma(k+1)] for every k with 0 <= k < n-1. Define A = sum over even k with 0 <= k < n of alice_values[sigma(k)], and B = sum over odd k with 0 <= k < n of bob_values[sigma(k)]. Then r = 1 if A > B, r = 0 if A = B, and r = -1 if A < B.
  Preconditions: Let n = len(alice_values) = len(bob_values); 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= alice_values[i] <= 100 and 1 <= bob_values[i] <= 100. -/
theorem spec_1
    (n : Nat) (alice_values bob_values : Slice Std.I64)
    (h_len_alice : alice_values.val.length = n)
    (h_len_bob : bob_values.val.length = n)
    (h_n_pos : 1 ≤ n)
    (h_n_le : n ≤ 100000)
    (h_alice_bounds : ∀ i, i < n → 1 ≤ getI alice_values i ∧ getI alice_values i ≤ 100)
    (h_bob_bounds : ∀ i, i < n → 1 ≤ getI bob_values i ∧ getI bob_values i ≤ 100)
    (r : Std.I64)
    (h_ret : stone_game_vi alice_values bob_values = ok r)
    (sigma : Nat → Nat)
    (h_sigma : IsPermutation n sigma)
    (h_sigma_sorted :
      ∀ k, k + 1 < n →
        pairSum alice_values bob_values (sigma k) ≥
          pairSum alice_values bob_values (sigma (k + 1))) :
    let A := sumEven n (fun k => getI alice_values (sigma k))
    let B := sumOdd n (fun k => getI bob_values (sigma k))
    (A > B → r.val = 1) ∧ (A = B → r.val = 0) ∧ (A < B → r.val = -1) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Nat) (alice_values bob_values : Slice Std.I64)
    (h_len_alice : alice_values.val.length = n)
    (h_len_bob : bob_values.val.length = n)
    (h_n_pos : 1 ≤ n)
    (h_n_le : n ≤ 100000)
    (h_alice_bounds : ∀ i, i < n → 1 ≤ getI alice_values i ∧ getI alice_values i ≤ 100)
    (h_bob_bounds : ∀ i, i < n → 1 ≤ getI bob_values i ∧ getI bob_values i ≤ 100)
    (r : Std.I64)
    (h_ret : stone_game_vi alice_values bob_values = ok r)
    (sigma : Nat → Nat)
    (h_sigma : IsPermutation n sigma)
    (h_sigma_sorted :
      ∀ k, k + 1 < n →
        pairSum alice_values bob_values (sigma k) ≥
          pairSum alice_values bob_values (sigma (k + 1))), let A := sumEven n (fun k => getI alice_values (sigma k))
    let B := sumOdd n (fun k => getI bob_values (sigma k))
    (A > B → r.val = 1) ∧ (A = B → r.val = 0) ∧ (A < B → r.val = -1)) := by
  sorry

/-- For every valid input, whenever the function returns a result r, r is either -1, 0, or 1.
  Preconditions: Let n = len(alice_values) = len(bob_values); 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= alice_values[i] <= 100 and 1 <= bob_values[i] <= 100. -/
theorem spec_2
    (n : Nat) (alice_values bob_values : Slice Std.I64)
    (h_len_alice : alice_values.val.length = n)
    (h_len_bob : bob_values.val.length = n)
    (h_n_pos : 1 ≤ n)
    (h_n_le : n ≤ 100000)
    (h_alice_bounds : ∀ i, i < n → 1 ≤ getI alice_values i ∧ getI alice_values i ≤ 100)
    (h_bob_bounds : ∀ i, i < n → 1 ≤ getI bob_values i ∧ getI bob_values i ≤ 100)
    (r : Std.I64)
    (h_ret : stone_game_vi alice_values bob_values = ok r) :
    r.val = -1 ∨ r.val = 0 ∨ r.val = 1 := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Nat) (alice_values bob_values : Slice Std.I64)
    (h_len_alice : alice_values.val.length = n)
    (h_len_bob : bob_values.val.length = n)
    (h_n_pos : 1 ≤ n)
    (h_n_le : n ≤ 100000)
    (h_alice_bounds : ∀ i, i < n → 1 ≤ getI alice_values i ∧ getI alice_values i ≤ 100)
    (h_bob_bounds : ∀ i, i < n → 1 ≤ getI bob_values i ∧ getI bob_values i ≤ 100)
    (r : Std.I64)
    (h_ret : stone_game_vi alice_values bob_values = ok r), r.val = -1 ∨ r.val = 0 ∨ r.val = 1) := by
  sorry

/-- For every valid input, the function returns a result r; it does not fail, panic, or overflow.
  Preconditions: Let n = len(alice_values) = len(bob_values); 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= alice_values[i] <= 100 and 1 <= bob_values[i] <= 100. -/
theorem spec_3
    (n : Nat) (alice_values bob_values : Slice Std.I64)
    (h_len_alice : alice_values.val.length = n)
    (h_len_bob : bob_values.val.length = n)
    (h_n_pos : 1 ≤ n)
    (h_n_le : n ≤ 100000)
    (h_alice_bounds : ∀ i, i < n → 1 ≤ getI alice_values i ∧ getI alice_values i ≤ 100)
    (h_bob_bounds : ∀ i, i < n → 1 ≤ getI bob_values i ∧ getI bob_values i ≤ 100) :
    ∃ r : Std.I64, stone_game_vi alice_values bob_values = ok r := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : Nat) (alice_values bob_values : Slice Std.I64)
    (h_len_alice : alice_values.val.length = n)
    (h_len_bob : bob_values.val.length = n)
    (h_n_pos : 1 ≤ n)
    (h_n_le : n ≤ 100000)
    (h_alice_bounds : ∀ i, i < n → 1 ≤ getI alice_values i ∧ getI alice_values i ≤ 100)
    (h_bob_bounds : ∀ i, i < n → 1 ≤ getI bob_values i ∧ getI bob_values i ≤ 100), ∃ r : Std.I64, stone_game_vi alice_values bob_values = ok r) := by
  sorry

/-- Define alice_prime_values[k] = alice_values[pi(k)] and bob_prime_values[k] = bob_values[pi(k)] for every k with 0 <= k < n. If the function returns r on (alice_values, bob_values) and r_prime on (alice_prime_values, bob_prime_values), then r = r_prime.
  Preconditions: Let n = len(alice_values) = len(bob_values); 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= alice_values[i] <= 100 and 1 <= bob_values[i] <= 100. Let pi be any permutation of {0,...,n-1}. -/
theorem spec_4
    (n : Nat) (alice_values bob_values : Slice Std.I64)
    (h_len_alice : alice_values.val.length = n)
    (h_len_bob : bob_values.val.length = n)
    (h_n_pos : 1 ≤ n)
    (h_n_le : n ≤ 100000)
    (h_alice_bounds : ∀ i, i < n → 1 ≤ getI alice_values i ∧ getI alice_values i ≤ 100)
    (h_bob_bounds : ∀ i, i < n → 1 ≤ getI bob_values i ∧ getI bob_values i ≤ 100)
    (pi : Nat → Nat)
    (h_pi : IsPermutation n pi)
    (alice_prime_values bob_prime_values : Slice Std.I64)
    (h_len_alice_prime : alice_prime_values.val.length = n)
    (h_len_bob_prime : bob_prime_values.val.length = n)
    (h_alice_prime :
      ∀ k, k < n → getI alice_prime_values k = getI alice_values (pi k))
    (h_bob_prime :
      ∀ k, k < n → getI bob_prime_values k = getI bob_values (pi k))
    (r r_prime : Std.I64)
    (h_ret : stone_game_vi alice_values bob_values = ok r)
    (h_ret_prime : stone_game_vi alice_prime_values bob_prime_values = ok r_prime) :
    r.val = r_prime.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : Nat) (alice_values bob_values : Slice Std.I64)
    (h_len_alice : alice_values.val.length = n)
    (h_len_bob : bob_values.val.length = n)
    (h_n_pos : 1 ≤ n)
    (h_n_le : n ≤ 100000)
    (h_alice_bounds : ∀ i, i < n → 1 ≤ getI alice_values i ∧ getI alice_values i ≤ 100)
    (h_bob_bounds : ∀ i, i < n → 1 ≤ getI bob_values i ∧ getI bob_values i ≤ 100)
    (pi : Nat → Nat)
    (h_pi : IsPermutation n pi)
    (alice_prime_values bob_prime_values : Slice Std.I64)
    (h_len_alice_prime : alice_prime_values.val.length = n)
    (h_len_bob_prime : bob_prime_values.val.length = n)
    (h_alice_prime :
      ∀ k, k < n → getI alice_prime_values k = getI alice_values (pi k))
    (h_bob_prime :
      ∀ k, k < n → getI bob_prime_values k = getI bob_values (pi k))
    (r r_prime : Std.I64)
    (h_ret : stone_game_vi alice_values bob_values = ok r)
    (h_ret_prime : stone_game_vi alice_prime_values bob_prime_values = ok r_prime), r.val = r_prime.val) := by
  sorry

/-- Whenever the function returns a result r, r = 1.
  Preconditions: Let n = len(alice_values) = len(bob_values); n = 1; 1 <= alice_values[0] <= 100 and 1 <= bob_values[0] <= 100. -/
theorem spec_5
    (n : Nat) (alice_values bob_values : Slice Std.I64)
    (h_len_alice : alice_values.val.length = n)
    (h_len_bob : bob_values.val.length = n)
    (h_n : n = 1)
    (h_alice_bounds : 1 ≤ getI alice_values 0 ∧ getI alice_values 0 ≤ 100)
    (h_bob_bounds : 1 ≤ getI bob_values 0 ∧ getI bob_values 0 ≤ 100)
    (r : Std.I64)
    (h_ret : stone_game_vi alice_values bob_values = ok r) :
    r.val = 1 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : Nat) (alice_values bob_values : Slice Std.I64)
    (h_len_alice : alice_values.val.length = n)
    (h_len_bob : bob_values.val.length = n)
    (h_n : n = 1)
    (h_alice_bounds : 1 ≤ getI alice_values 0 ∧ getI alice_values 0 ≤ 100)
    (h_bob_bounds : 1 ≤ getI bob_values 0 ∧ getI bob_values 0 ≤ 100)
    (r : Std.I64)
    (h_ret : stone_game_vi alice_values bob_values = ok r), r.val = 1) := by
  sorry

/-- Let h and l be distinct indices with {h,l} = {0,1} and alice_values[h] + bob_values[h] >= alice_values[l] + bob_values[l]. Whenever the function returns a result r, r = 1 if alice_values[h] > bob_values[l], r = 0 if alice_values[h] = bob_values[l], and r = -1 if alice_values[h] < bob_values[l].
  Preconditions: Let n = len(alice_values) = len(bob_values); n = 2; for every i with 0 <= i < n, 1 <= alice_values[i] <= 100 and 1 <= bob_values[i] <= 100. -/
theorem spec_6
    (n : Nat) (alice_values bob_values : Slice Std.I64)
    (h_len_alice : alice_values.val.length = n)
    (h_len_bob : bob_values.val.length = n)
    (h_n : n = 2)
    (h_alice_bounds : ∀ i, i < n → 1 ≤ getI alice_values i ∧ getI alice_values i ≤ 100)
    (h_bob_bounds : ∀ i, i < n → 1 ≤ getI bob_values i ∧ getI bob_values i ≤ 100)
    (h l : Nat)
    (h_ne : h ≠ l)
    (h_pair : (h = 0 ∧ l = 1) ∨ (h = 1 ∧ l = 0))
    (h_ge : pairSum alice_values bob_values h ≥ pairSum alice_values bob_values l)
    (r : Std.I64)
    (h_ret : stone_game_vi alice_values bob_values = ok r) :
    (getI alice_values h > getI bob_values l → r.val = 1) ∧
    (getI alice_values h = getI bob_values l → r.val = 0) ∧
    (getI alice_values h < getI bob_values l → r.val = -1) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : Nat) (alice_values bob_values : Slice Std.I64)
    (h_len_alice : alice_values.val.length = n)
    (h_len_bob : bob_values.val.length = n)
    (h_n : n = 2)
    (h_alice_bounds : ∀ i, i < n → 1 ≤ getI alice_values i ∧ getI alice_values i ≤ 100)
    (h_bob_bounds : ∀ i, i < n → 1 ≤ getI bob_values i ∧ getI bob_values i ≤ 100)
    (h l : Nat)
    (h_ne : h ≠ l)
    (h_pair : (h = 0 ∧ l = 1) ∨ (h = 1 ∧ l = 0))
    (h_ge : pairSum alice_values bob_values h ≥ pairSum alice_values bob_values l)
    (r : Std.I64)
    (h_ret : stone_game_vi alice_values bob_values = ok r), (getI alice_values h > getI bob_values l → r.val = 1) ∧
    (getI alice_values h = getI bob_values l → r.val = 0) ∧
    (getI alice_values h < getI bob_values l → r.val = -1)) := by
  sorry

/-- Whenever the function returns a result r, define D = (sum over i with 0 <= i < n of alice_values[i]) - floor(n/2) * S. Then r = 1 if D > 0, r = 0 if D = 0, and r = -1 if D < 0.
  Preconditions: Let n = len(alice_values) = len(bob_values); 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= alice_values[i] <= 100 and 1 <= bob_values[i] <= 100. There exists an integer S such that alice_values[i] + bob_values[i] = S for every i with 0 <= i < n. -/
theorem spec_7
    (n : Nat) (alice_values bob_values : Slice Std.I64)
    (h_len_alice : alice_values.val.length = n)
    (h_len_bob : bob_values.val.length = n)
    (h_n_pos : 1 ≤ n)
    (h_n_le : n ≤ 100000)
    (h_alice_bounds : ∀ i, i < n → 1 ≤ getI alice_values i ∧ getI alice_values i ≤ 100)
    (h_bob_bounds : ∀ i, i < n → 1 ≤ getI bob_values i ∧ getI bob_values i ≤ 100)
    (S : Int)
    (h_S : ∀ i, i < n → pairSum alice_values bob_values i = S)
    (r : Std.I64)
    (h_ret : stone_game_vi alice_values bob_values = ok r) :
    let D := sumRange n (getI alice_values) - ((n / 2 : Nat) : Int) * S
    (D > 0 → r.val = 1) ∧ (D = 0 → r.val = 0) ∧ (D < 0 → r.val = -1) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : Nat) (alice_values bob_values : Slice Std.I64)
    (h_len_alice : alice_values.val.length = n)
    (h_len_bob : bob_values.val.length = n)
    (h_n_pos : 1 ≤ n)
    (h_n_le : n ≤ 100000)
    (h_alice_bounds : ∀ i, i < n → 1 ≤ getI alice_values i ∧ getI alice_values i ≤ 100)
    (h_bob_bounds : ∀ i, i < n → 1 ≤ getI bob_values i ∧ getI bob_values i ≤ 100)
    (S : Int)
    (h_S : ∀ i, i < n → pairSum alice_values bob_values i = S)
    (r : Std.I64)
    (h_ret : stone_game_vi alice_values bob_values = ok r), let D := sumRange n (getI alice_values) - ((n / 2 : Nat) : Int) * S
    (D > 0 → r.val = 1) ∧ (D = 0 → r.val = 0) ∧ (D < 0 → r.val = -1)) := by
  sorry

/-- Whenever the function returns a result r, if n is odd then r = 1, and if n is even then r is either 0 or 1.
  Preconditions: Let n = len(alice_values) = len(bob_values); 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= alice_values[i] <= 100, 1 <= bob_values[i] <= 100, and alice_values[i] >= bob_values[i]. -/
theorem spec_8
    (n : Nat) (alice_values bob_values : Slice Std.I64)
    (h_len_alice : alice_values.val.length = n)
    (h_len_bob : bob_values.val.length = n)
    (h_n_pos : 1 ≤ n)
    (h_n_le : n ≤ 100000)
    (h_alice_bounds : ∀ i, i < n → 1 ≤ getI alice_values i ∧ getI alice_values i ≤ 100)
    (h_bob_bounds : ∀ i, i < n → 1 ≤ getI bob_values i ∧ getI bob_values i ≤ 100)
    (h_pointwise : ∀ i, i < n → getI alice_values i ≥ getI bob_values i)
    (r : Std.I64)
    (h_ret : stone_game_vi alice_values bob_values = ok r) :
    (n % 2 = 1 → r.val = 1) ∧ (n % 2 = 0 → r.val = 0 ∨ r.val = 1) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n : Nat) (alice_values bob_values : Slice Std.I64)
    (h_len_alice : alice_values.val.length = n)
    (h_len_bob : bob_values.val.length = n)
    (h_n_pos : 1 ≤ n)
    (h_n_le : n ≤ 100000)
    (h_alice_bounds : ∀ i, i < n → 1 ≤ getI alice_values i ∧ getI alice_values i ≤ 100)
    (h_bob_bounds : ∀ i, i < n → 1 ≤ getI bob_values i ∧ getI bob_values i ≤ 100)
    (h_pointwise : ∀ i, i < n → getI alice_values i ≥ getI bob_values i)
    (r : Std.I64)
    (h_ret : stone_game_vi alice_values bob_values = ok r), (n % 2 = 1 → r.val = 1) ∧ (n % 2 = 0 → r.val = 0 ∨ r.val = 1)) := by
  sorry

/-- Whenever the function returns a result r, r is either 0 or 1.
  Preconditions: Let n = len(alice_values) = len(bob_values); 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= alice_values[i] <= 100 and 1 <= bob_values[i] <= 100. Also, sum over i with 0 <= i < n of alice_values[i] >= sum over i with 0 <= i < n of bob_values[i]. -/
theorem spec_9
    (n : Nat) (alice_values bob_values : Slice Std.I64)
    (h_len_alice : alice_values.val.length = n)
    (h_len_bob : bob_values.val.length = n)
    (h_n_pos : 1 ≤ n)
    (h_n_le : n ≤ 100000)
    (h_alice_bounds : ∀ i, i < n → 1 ≤ getI alice_values i ∧ getI alice_values i ≤ 100)
    (h_bob_bounds : ∀ i, i < n → 1 ≤ getI bob_values i ∧ getI bob_values i ≤ 100)
    (h_sum : sumRange n (getI alice_values) ≥ sumRange n (getI bob_values))
    (r : Std.I64)
    (h_ret : stone_game_vi alice_values bob_values = ok r) :
    r.val = 0 ∨ r.val = 1 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n : Nat) (alice_values bob_values : Slice Std.I64)
    (h_len_alice : alice_values.val.length = n)
    (h_len_bob : bob_values.val.length = n)
    (h_n_pos : 1 ≤ n)
    (h_n_le : n ≤ 100000)
    (h_alice_bounds : ∀ i, i < n → 1 ≤ getI alice_values i ∧ getI alice_values i ≤ 100)
    (h_bob_bounds : ∀ i, i < n → 1 ≤ getI bob_values i ∧ getI bob_values i ≤ 100)
    (h_sum : sumRange n (getI alice_values) ≥ sumRange n (getI bob_values))
    (r : Std.I64)
    (h_ret : stone_game_vi alice_values bob_values = ok r), r.val = 0 ∨ r.val = 1) := by
  sorry

/-- Define alice_prime_values[i] = alice_values[i] + c and bob_prime_values[i] = bob_values[i] + c for every i with 0 <= i < n. If the function returns r on (alice_values, bob_values) and r_prime on (alice_prime_values, bob_prime_values), then r = r_prime.
  Preconditions: Let n = len(alice_values) = len(bob_values); n is even; 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= alice_values[i] <= 100 and 1 <= bob_values[i] <= 100. Let c be an integer such that 1 <= alice_values[i] + c <= 100 and 1 <= bob_values[i] + c <= 100 for every i. -/
theorem spec_10
    (n : Nat) (alice_values bob_values : Slice Std.I64)
    (h_len_alice : alice_values.val.length = n)
    (h_len_bob : bob_values.val.length = n)
    (h_n_even : n % 2 = 0)
    (h_n_pos : 1 ≤ n)
    (h_n_le : n ≤ 100000)
    (h_alice_bounds : ∀ i, i < n → 1 ≤ getI alice_values i ∧ getI alice_values i ≤ 100)
    (h_bob_bounds : ∀ i, i < n → 1 ≤ getI bob_values i ∧ getI bob_values i ≤ 100)
    (c : Int)
    (h_c : ∀ i, i < n →
      1 ≤ getI alice_values i + c ∧ getI alice_values i + c ≤ 100 ∧
      1 ≤ getI bob_values i + c ∧ getI bob_values i + c ≤ 100)
    (alice_prime_values bob_prime_values : Slice Std.I64)
    (h_len_alice_prime : alice_prime_values.val.length = n)
    (h_len_bob_prime : bob_prime_values.val.length = n)
    (h_alice_prime : ∀ i, i < n → getI alice_prime_values i = getI alice_values i + c)
    (h_bob_prime : ∀ i, i < n → getI bob_prime_values i = getI bob_values i + c)
    (r r_prime : Std.I64)
    (h_ret : stone_game_vi alice_values bob_values = ok r)
    (h_ret_prime : stone_game_vi alice_prime_values bob_prime_values = ok r_prime) :
    r.val = r_prime.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n : Nat) (alice_values bob_values : Slice Std.I64)
    (h_len_alice : alice_values.val.length = n)
    (h_len_bob : bob_values.val.length = n)
    (h_n_even : n % 2 = 0)
    (h_n_pos : 1 ≤ n)
    (h_n_le : n ≤ 100000)
    (h_alice_bounds : ∀ i, i < n → 1 ≤ getI alice_values i ∧ getI alice_values i ≤ 100)
    (h_bob_bounds : ∀ i, i < n → 1 ≤ getI bob_values i ∧ getI bob_values i ≤ 100)
    (c : Int)
    (h_c : ∀ i, i < n →
      1 ≤ getI alice_values i + c ∧ getI alice_values i + c ≤ 100 ∧
      1 ≤ getI bob_values i + c ∧ getI bob_values i + c ≤ 100)
    (alice_prime_values bob_prime_values : Slice Std.I64)
    (h_len_alice_prime : alice_prime_values.val.length = n)
    (h_len_bob_prime : bob_prime_values.val.length = n)
    (h_alice_prime : ∀ i, i < n → getI alice_prime_values i = getI alice_values i + c)
    (h_bob_prime : ∀ i, i < n → getI bob_prime_values i = getI bob_values i + c)
    (r r_prime : Std.I64)
    (h_ret : stone_game_vi alice_values bob_values = ok r)
    (h_ret_prime : stone_game_vi alice_prime_values bob_prime_values = ok r_prime), r.val = r_prime.val) := by
  sorry

/-- Define alice_prime_values[i] = lambda * alice_values[i] and bob_prime_values[i] = lambda * bob_values[i] for every i with 0 <= i < n. If the function returns r on (alice_values, bob_values) and r_prime on (alice_prime_values, bob_prime_values), then r = r_prime.
  Preconditions: Let n = len(alice_values) = len(bob_values); 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= alice_values[i] <= 100 and 1 <= bob_values[i] <= 100. Let lambda be a positive integer such that 1 <= lambda * alice_values[i] <= 100 and 1 <= lambda * bob_values[i] <= 100 for every i. -/
theorem spec_11
    (n : Nat) (alice_values bob_values : Slice Std.I64)
    (h_len_alice : alice_values.val.length = n)
    (h_len_bob : bob_values.val.length = n)
    (h_n_pos : 1 ≤ n)
    (h_n_le : n ≤ 100000)
    (h_alice_bounds : ∀ i, i < n → 1 ≤ getI alice_values i ∧ getI alice_values i ≤ 100)
    (h_bob_bounds : ∀ i, i < n → 1 ≤ getI bob_values i ∧ getI bob_values i ≤ 100)
    (lam : Int)
    (h_lam_pos : 1 ≤ lam)
    (h_lam : ∀ i, i < n →
      1 ≤ lam * getI alice_values i ∧ lam * getI alice_values i ≤ 100 ∧
      1 ≤ lam * getI bob_values i ∧ lam * getI bob_values i ≤ 100)
    (alice_prime_values bob_prime_values : Slice Std.I64)
    (h_len_alice_prime : alice_prime_values.val.length = n)
    (h_len_bob_prime : bob_prime_values.val.length = n)
    (h_alice_prime : ∀ i, i < n → getI alice_prime_values i = lam * getI alice_values i)
    (h_bob_prime : ∀ i, i < n → getI bob_prime_values i = lam * getI bob_values i)
    (r r_prime : Std.I64)
    (h_ret : stone_game_vi alice_values bob_values = ok r)
    (h_ret_prime : stone_game_vi alice_prime_values bob_prime_values = ok r_prime) :
    r.val = r_prime.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (n : Nat) (alice_values bob_values : Slice Std.I64)
    (h_len_alice : alice_values.val.length = n)
    (h_len_bob : bob_values.val.length = n)
    (h_n_pos : 1 ≤ n)
    (h_n_le : n ≤ 100000)
    (h_alice_bounds : ∀ i, i < n → 1 ≤ getI alice_values i ∧ getI alice_values i ≤ 100)
    (h_bob_bounds : ∀ i, i < n → 1 ≤ getI bob_values i ∧ getI bob_values i ≤ 100)
    (lam : Int)
    (h_lam_pos : 1 ≤ lam)
    (h_lam : ∀ i, i < n →
      1 ≤ lam * getI alice_values i ∧ lam * getI alice_values i ≤ 100 ∧
      1 ≤ lam * getI bob_values i ∧ lam * getI bob_values i ≤ 100)
    (alice_prime_values bob_prime_values : Slice Std.I64)
    (h_len_alice_prime : alice_prime_values.val.length = n)
    (h_len_bob_prime : bob_prime_values.val.length = n)
    (h_alice_prime : ∀ i, i < n → getI alice_prime_values i = lam * getI alice_values i)
    (h_bob_prime : ∀ i, i < n → getI bob_prime_values i = lam * getI bob_values i)
    (r r_prime : Std.I64)
    (h_ret : stone_game_vi alice_values bob_values = ok r)
    (h_ret_prime : stone_game_vi alice_prime_values bob_prime_values = ok r_prime), r.val = r_prime.val) := by
  sorry

/-- Define alice_prime_values[k] = alice_values[k] for k != i and alice_prime_values[i] = alice_values[i] + c; let bob_prime_values = bob_values. If the function returns r on (alice_values, bob_values) and r_prime on (alice_prime_values, bob_prime_values), then r_prime >= r, comparing integers -1 < 0 < 1.
  Preconditions: Let n = len(alice_values) = len(bob_values); 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= alice_values[i] <= 100 and 1 <= bob_values[i] <= 100. Let i be an index with 0 <= i < n and let c be an integer with c >= 0 such that 1 <= alice_values[i] + c <= 100. -/
theorem spec_12
    (n : Nat) (alice_values bob_values : Slice Std.I64)
    (h_len_alice : alice_values.val.length = n)
    (h_len_bob : bob_values.val.length = n)
    (h_n_pos : 1 ≤ n)
    (h_n_le : n ≤ 100000)
    (h_alice_bounds : ∀ i, i < n → 1 ≤ getI alice_values i ∧ getI alice_values i ≤ 100)
    (h_bob_bounds : ∀ i, i < n → 1 ≤ getI bob_values i ∧ getI bob_values i ≤ 100)
    (i : Nat)
    (h_i : i < n)
    (c : Int)
    (h_c_nonneg : c ≥ 0)
    (h_c : 1 ≤ getI alice_values i + c ∧ getI alice_values i + c ≤ 100)
    (alice_prime_values bob_prime_values : Slice Std.I64)
    (h_len_alice_prime : alice_prime_values.val.length = n)
    (h_len_bob_prime : bob_prime_values.val.length = n)
    (h_alice_prime : ∀ k, k < n →
      getI alice_prime_values k = if k = i then getI alice_values k + c else getI alice_values k)
    (h_bob_prime : ∀ k, k < n → getI bob_prime_values k = getI bob_values k)
    (r r_prime : Std.I64)
    (h_ret : stone_game_vi alice_values bob_values = ok r)
    (h_ret_prime : stone_game_vi alice_prime_values bob_prime_values = ok r_prime) :
    r_prime.val ≥ r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (n : Nat) (alice_values bob_values : Slice Std.I64)
    (h_len_alice : alice_values.val.length = n)
    (h_len_bob : bob_values.val.length = n)
    (h_n_pos : 1 ≤ n)
    (h_n_le : n ≤ 100000)
    (h_alice_bounds : ∀ i, i < n → 1 ≤ getI alice_values i ∧ getI alice_values i ≤ 100)
    (h_bob_bounds : ∀ i, i < n → 1 ≤ getI bob_values i ∧ getI bob_values i ≤ 100)
    (i : Nat)
    (h_i : i < n)
    (c : Int)
    (h_c_nonneg : c ≥ 0)
    (h_c : 1 ≤ getI alice_values i + c ∧ getI alice_values i + c ≤ 100)
    (alice_prime_values bob_prime_values : Slice Std.I64)
    (h_len_alice_prime : alice_prime_values.val.length = n)
    (h_len_bob_prime : bob_prime_values.val.length = n)
    (h_alice_prime : ∀ k, k < n →
      getI alice_prime_values k = if k = i then getI alice_values k + c else getI alice_values k)
    (h_bob_prime : ∀ k, k < n → getI bob_prime_values k = getI bob_values k)
    (r r_prime : Std.I64)
    (h_ret : stone_game_vi alice_values bob_values = ok r)
    (h_ret_prime : stone_game_vi alice_prime_values bob_prime_values = ok r_prime), r_prime.val ≥ r.val) := by
  sorry

/-- Define bob_prime_values[k] = bob_values[k] for k != i and bob_prime_values[i] = bob_values[i] + c; let alice_prime_values = alice_values. If the function returns r on (alice_values, bob_values) and r_prime on (alice_prime_values, bob_prime_values), then r_prime <= r, comparing integers -1 < 0 < 1.
  Preconditions: Let n = len(alice_values) = len(bob_values); 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= alice_values[i] <= 100 and 1 <= bob_values[i] <= 100. Let i be an index with 0 <= i < n and let c be an integer with c >= 0 such that 1 <= bob_values[i] + c <= 100. -/
theorem spec_13
    (n : Nat) (alice_values bob_values : Slice Std.I64)
    (h_len_alice : alice_values.val.length = n)
    (h_len_bob : bob_values.val.length = n)
    (h_n_pos : 1 ≤ n)
    (h_n_le : n ≤ 100000)
    (h_alice_bounds : ∀ i, i < n → 1 ≤ getI alice_values i ∧ getI alice_values i ≤ 100)
    (h_bob_bounds : ∀ i, i < n → 1 ≤ getI bob_values i ∧ getI bob_values i ≤ 100)
    (i : Nat)
    (h_i : i < n)
    (c : Int)
    (h_c_nonneg : c ≥ 0)
    (h_c : 1 ≤ getI bob_values i + c ∧ getI bob_values i + c ≤ 100)
    (alice_prime_values bob_prime_values : Slice Std.I64)
    (h_len_alice_prime : alice_prime_values.val.length = n)
    (h_len_bob_prime : bob_prime_values.val.length = n)
    (h_alice_prime : ∀ k, k < n → getI alice_prime_values k = getI alice_values k)
    (h_bob_prime : ∀ k, k < n →
      getI bob_prime_values k = if k = i then getI bob_values k + c else getI bob_values k)
    (r r_prime : Std.I64)
    (h_ret : stone_game_vi alice_values bob_values = ok r)
    (h_ret_prime : stone_game_vi alice_prime_values bob_prime_values = ok r_prime) :
    r_prime.val ≤ r.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (n : Nat) (alice_values bob_values : Slice Std.I64)
    (h_len_alice : alice_values.val.length = n)
    (h_len_bob : bob_values.val.length = n)
    (h_n_pos : 1 ≤ n)
    (h_n_le : n ≤ 100000)
    (h_alice_bounds : ∀ i, i < n → 1 ≤ getI alice_values i ∧ getI alice_values i ≤ 100)
    (h_bob_bounds : ∀ i, i < n → 1 ≤ getI bob_values i ∧ getI bob_values i ≤ 100)
    (i : Nat)
    (h_i : i < n)
    (c : Int)
    (h_c_nonneg : c ≥ 0)
    (h_c : 1 ≤ getI bob_values i + c ∧ getI bob_values i + c ≤ 100)
    (alice_prime_values bob_prime_values : Slice Std.I64)
    (h_len_alice_prime : alice_prime_values.val.length = n)
    (h_len_bob_prime : bob_prime_values.val.length = n)
    (h_alice_prime : ∀ k, k < n → getI alice_prime_values k = getI alice_values k)
    (h_bob_prime : ∀ k, k < n →
      getI bob_prime_values k = if k = i then getI bob_values k + c else getI bob_values k)
    (r r_prime : Std.I64)
    (h_ret : stone_game_vi alice_values bob_values = ok r)
    (h_ret_prime : stone_game_vi alice_prime_values bob_prime_values = ok r_prime), r_prime.val ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if every distinct value v occurring among alice_values occurs an even number of times; otherwise r = 1.
  Preconditions: Let n = len(alice_values) = len(bob_values); n is even; 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= alice_values[i] <= 100 and alice_values[i] = bob_values[i]. -/
theorem spec_14
    (n : Nat) (alice_values bob_values : Slice Std.I64)
    (h_len_alice : alice_values.val.length = n)
    (h_len_bob : bob_values.val.length = n)
    (h_n_even : n % 2 = 0)
    (h_n_pos : 1 ≤ n)
    (h_n_le : n ≤ 100000)
    (h_alice_bounds : ∀ i, i < n → 1 ≤ getI alice_values i ∧ getI alice_values i ≤ 100)
    (h_eq : ∀ i, i < n → getI alice_values i = getI bob_values i)
    (r : Std.I64)
    (h_ret : stone_game_vi alice_values bob_values = ok r) :
    (r.val = 0 ↔ AllCountsEven alice_values n) ∧
    (r.val = 1 ↔ ¬ AllCountsEven alice_values n) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (n : Nat) (alice_values bob_values : Slice Std.I64)
    (h_len_alice : alice_values.val.length = n)
    (h_len_bob : bob_values.val.length = n)
    (h_n_even : n % 2 = 0)
    (h_n_pos : 1 ≤ n)
    (h_n_le : n ≤ 100000)
    (h_alice_bounds : ∀ i, i < n → 1 ≤ getI alice_values i ∧ getI alice_values i ≤ 100)
    (h_eq : ∀ i, i < n → getI alice_values i = getI bob_values i)
    (r : Std.I64)
    (h_ret : stone_game_vi alice_values bob_values = ok r), (r.val = 0 ↔ AllCountsEven alice_values n) ∧
    (r.val = 1 ↔ ¬ AllCountsEven alice_values n)) := by
  sorry

end AegisSpec.StoneGameVi
