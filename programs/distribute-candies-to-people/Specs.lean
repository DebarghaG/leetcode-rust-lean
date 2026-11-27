import Aegis.DistributeCandies.Code.Funs

/-!
# Specifications of `Aegis.DistributeCandies.distribute_candies`

LeetCode problem `distribute-candies-to-people`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.DistributeCandies

  def tri (k : ℕ) : ℕ := k * (k + 1) / 2

  def rem (candies : ℤ) (k : ℕ) : ℤ := candies - (tri k : ℤ)

  def nPeople (num_people : Std.I64) : ℕ := num_people.val.toNat

  def phaseSet (n k j : ℕ) : Finset ℕ := (Finset.Icc 1 k).filter (fun t => (t - 1) % n = j)

  def phaseSum (n k j : ℕ) : ℕ := (phaseSet n k j).sum id

  def phaseCount (n k j : ℕ) : ℕ := (phaseSet n k j).card

  def idealEntry (candies : ℤ) (n k j : ℕ) : ℤ :=
    (phaseSum n k j : ℤ) + (if 0 < rem candies k ∧ k % n = j then rem candies k else 0)

  def firstEntryValue (candies : ℤ) (n k : ℕ) : ℤ :=
    let L : ℕ := phaseCount n k 0
    (L : ℤ) + (n : ℤ) * (L : ℤ) * ((L : ℤ) - 1) / 2 +
      (if 0 < rem candies k ∧ k % n = 0 then rem candies k else 0)

  def entry (ans : alloc.vec.Vec Std.I64) (j : ℕ) : ℤ :=
    match ans.val[j]? with
    | some x => x.val
    | none => 0

  def vecSum (ans : alloc.vec.Vec Std.I64) : ℤ := (ans.val.map (fun x => x.val)).sum

  /-- Whenever the function returns a result ans, define n = num_people. Let k be the unique integer with k >= 0 and k*(k+1)/2 <= candies < (k+1)*(k+2)/2, and let r = candies - k*(k+1)/2. Then len(ans) = n, and for every index j with 0 <= j < n, ans[j] = (the sum of all integers t such that 1 <= t <= k and (t-1) mod n = j) + (r if r > 0 and k mod n = j, and 0 otherwise). An empty sum is 0.
    Preconditions: candies and num_people are integers with 1 <= candies <= 10^9 and 1 <= num_people <= 1000. -/
  theorem spec_1 (candies num_people : Std.I64)
      (hc_lo : 1 ≤ candies.val) (hc_hi : candies.val ≤ 10 ^ 9)
      (hn_lo : 1 ≤ num_people.val) (hn_hi : num_people.val ≤ 1000)
      (k : ℕ) (hk_lo : (tri k : ℤ) ≤ candies.val)
      (hk_hi : candies.val < (tri (k + 1) : ℤ))
      (ans : alloc.vec.Vec Std.I64)
      (hans : Aegis.DistributeCandies.distribute_candies candies num_people = Result.ok ans) :
      ans.val.length = nPeople num_people ∧
        ∀ j : ℕ, j < nPeople num_people →
          entry ans j = idealEntry candies.val (nPeople num_people) k j := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (candies num_people : Std.I64)
        (hc_lo : 1 ≤ candies.val) (hc_hi : candies.val ≤ 10 ^ 9)
        (hn_lo : 1 ≤ num_people.val) (hn_hi : num_people.val ≤ 1000)
        (k : ℕ) (hk_lo : (tri k : ℤ) ≤ candies.val)
        (hk_hi : candies.val < (tri (k + 1) : ℤ))
        (ans : alloc.vec.Vec Std.I64)
        (hans : Aegis.DistributeCandies.distribute_candies candies num_people = Result.ok ans), ans.val.length = nPeople num_people ∧
          ∀ j : ℕ, j < nPeople num_people →
            entry ans j = idealEntry candies.val (nPeople num_people) k j) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result ans; it does not fail due to overflow, panic, or out-of-bounds access.
    Preconditions: candies and num_people are integers with 1 <= candies <= 10^9 and 1 <= num_people <= 1000. -/
  theorem spec_2 (candies num_people : Std.I64)
      (hc_lo : 1 ≤ candies.val) (hc_hi : candies.val ≤ 10 ^ 9)
      (hn_lo : 1 ≤ num_people.val) (hn_hi : num_people.val ≤ 1000) :
      ∃ ans : alloc.vec.Vec Std.I64,
        Aegis.DistributeCandies.distribute_candies candies num_people = Result.ok ans := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (candies num_people : Std.I64)
        (hc_lo : 1 ≤ candies.val) (hc_hi : candies.val ≤ 10 ^ 9)
        (hn_lo : 1 ≤ num_people.val) (hn_hi : num_people.val ≤ 1000), ∃ ans : alloc.vec.Vec Std.I64,
          Aegis.DistributeCandies.distribute_candies candies num_people = Result.ok ans) := by
    sorry

  /-- Whenever the function returns a result ans, len(ans) = num_people.
    Preconditions: candies and num_people are integers with 1 <= candies <= 10^9 and 1 <= num_people <= 1000. -/
  theorem spec_3 (candies num_people : Std.I64)
      (hc_lo : 1 ≤ candies.val) (hc_hi : candies.val ≤ 10 ^ 9)
      (hn_lo : 1 ≤ num_people.val) (hn_hi : num_people.val ≤ 1000)
      (ans : alloc.vec.Vec Std.I64)
      (hans : Aegis.DistributeCandies.distribute_candies candies num_people = Result.ok ans) :
      ans.val.length = nPeople num_people := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (candies num_people : Std.I64)
        (hc_lo : 1 ≤ candies.val) (hc_hi : candies.val ≤ 10 ^ 9)
        (hn_lo : 1 ≤ num_people.val) (hn_hi : num_people.val ≤ 1000)
        (ans : alloc.vec.Vec Std.I64)
        (hans : Aegis.DistributeCandies.distribute_candies candies num_people = Result.ok ans), ans.val.length = nPeople num_people) := by
    sorry

  /-- Whenever the function returns a result ans, the sum of all entries of ans equals candies.
    Preconditions: candies and num_people are integers with 1 <= candies <= 10^9 and 1 <= num_people <= 1000. -/
  theorem spec_4 (candies num_people : Std.I64)
      (hc_lo : 1 ≤ candies.val) (hc_hi : candies.val ≤ 10 ^ 9)
      (hn_lo : 1 ≤ num_people.val) (hn_hi : num_people.val ≤ 1000)
      (ans : alloc.vec.Vec Std.I64)
      (hans : Aegis.DistributeCandies.distribute_candies candies num_people = Result.ok ans) :
      vecSum ans = candies.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (candies num_people : Std.I64)
        (hc_lo : 1 ≤ candies.val) (hc_hi : candies.val ≤ 10 ^ 9)
        (hn_lo : 1 ≤ num_people.val) (hn_hi : num_people.val ≤ 1000)
        (ans : alloc.vec.Vec Std.I64)
        (hans : Aegis.DistributeCandies.distribute_candies candies num_people = Result.ok ans), vecSum ans = candies.val) := by
    sorry

  /-- Whenever the function returns a result ans, for every index j with 0 <= j < len(ans), 0 <= ans[j].
    Preconditions: candies and num_people are integers with 1 <= candies <= 10^9 and 1 <= num_people <= 1000. -/
  theorem spec_5 (candies num_people : Std.I64)
      (hc_lo : 1 ≤ candies.val) (hc_hi : candies.val ≤ 10 ^ 9)
      (hn_lo : 1 ≤ num_people.val) (hn_hi : num_people.val ≤ 1000)
      (ans : alloc.vec.Vec Std.I64)
      (hans : Aegis.DistributeCandies.distribute_candies candies num_people = Result.ok ans) :
      ∀ j : ℕ, j < ans.val.length → 0 ≤ entry ans j := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (candies num_people : Std.I64)
        (hc_lo : 1 ≤ candies.val) (hc_hi : candies.val ≤ 10 ^ 9)
        (hn_lo : 1 ≤ num_people.val) (hn_hi : num_people.val ≤ 1000)
        (ans : alloc.vec.Vec Std.I64)
        (hans : Aegis.DistributeCandies.distribute_candies candies num_people = Result.ok ans), ∀ j : ℕ, j < ans.val.length → 0 ≤ entry ans j) := by
    sorry

  /-- Whenever the function returns a result ans, for every index j with 0 <= j < len(ans), ans[j] <= candies.
    Preconditions: candies and num_people are integers with 1 <= candies <= 10^9 and 1 <= num_people <= 1000. -/
  theorem spec_6 (candies num_people : Std.I64)
      (hc_lo : 1 ≤ candies.val) (hc_hi : candies.val ≤ 10 ^ 9)
      (hn_lo : 1 ≤ num_people.val) (hn_hi : num_people.val ≤ 1000)
      (ans : alloc.vec.Vec Std.I64)
      (hans : Aegis.DistributeCandies.distribute_candies candies num_people = Result.ok ans) :
      ∀ j : ℕ, j < ans.val.length → entry ans j ≤ candies.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (candies num_people : Std.I64)
        (hc_lo : 1 ≤ candies.val) (hc_hi : candies.val ≤ 10 ^ 9)
        (hn_lo : 1 ≤ num_people.val) (hn_hi : num_people.val ≤ 1000)
        (ans : alloc.vec.Vec Std.I64)
        (hans : Aegis.DistributeCandies.distribute_candies candies num_people = Result.ok ans), ∀ j : ℕ, j < ans.val.length → entry ans j ≤ candies.val) := by
    sorry

  /-- Whenever the function returns a result ans, len(ans) >= 1 and ans[0] >= 1.
    Preconditions: candies and num_people are integers with 1 <= candies <= 10^9 and 1 <= num_people <= 1000. -/
  theorem spec_7 (candies num_people : Std.I64)
      (hc_lo : 1 ≤ candies.val) (hc_hi : candies.val ≤ 10 ^ 9)
      (hn_lo : 1 ≤ num_people.val) (hn_hi : num_people.val ≤ 1000)
      (ans : alloc.vec.Vec Std.I64)
      (hans : Aegis.DistributeCandies.distribute_candies candies num_people = Result.ok ans) :
      1 ≤ ans.val.length ∧ 1 ≤ entry ans 0 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (candies num_people : Std.I64)
        (hc_lo : 1 ≤ candies.val) (hc_hi : candies.val ≤ 10 ^ 9)
        (hn_lo : 1 ≤ num_people.val) (hn_hi : num_people.val ≤ 1000)
        (ans : alloc.vec.Vec Std.I64)
        (hans : Aegis.DistributeCandies.distribute_candies candies num_people = Result.ok ans), 1 ≤ ans.val.length ∧ 1 ≤ entry ans 0) := by
    sorry

  /-- Whenever the function returns a result ans, len(ans) = 1 and ans[0] = candies.
    Preconditions: candies and num_people are integers with 1 <= candies <= 10^9, 1 <= num_people <= 1000, and num_people = 1. -/
  theorem spec_8 (candies num_people : Std.I64)
      (hc_lo : 1 ≤ candies.val) (hc_hi : candies.val ≤ 10 ^ 9)
      (hn_lo : 1 ≤ num_people.val) (hn_hi : num_people.val ≤ 1000)
      (hn_one : num_people.val = 1)
      (ans : alloc.vec.Vec Std.I64)
      (hans : Aegis.DistributeCandies.distribute_candies candies num_people = Result.ok ans) :
      ans.val.length = 1 ∧ entry ans 0 = candies.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (candies num_people : Std.I64)
        (hc_lo : 1 ≤ candies.val) (hc_hi : candies.val ≤ 10 ^ 9)
        (hn_lo : 1 ≤ num_people.val) (hn_hi : num_people.val ≤ 1000)
        (hn_one : num_people.val = 1)
        (ans : alloc.vec.Vec Std.I64)
        (hans : Aegis.DistributeCandies.distribute_candies candies num_people = Result.ok ans), ans.val.length = 1 ∧ entry ans 0 = candies.val) := by
    sorry

  /-- Whenever the function returns a result ans, len(ans) = num_people, ans[0] = 1, and for every index j with 1 <= j < num_people, ans[j] = 0.
    Preconditions: candies and num_people are integers with candies = 1 and 1 <= num_people <= 1000. -/
  theorem spec_9 (candies num_people : Std.I64)
      (hc_lo : 1 ≤ candies.val) (hc_hi : candies.val ≤ 10 ^ 9)
      (hn_lo : 1 ≤ num_people.val) (hn_hi : num_people.val ≤ 1000)
      (hc_one : candies.val = 1)
      (ans : alloc.vec.Vec Std.I64)
      (hans : Aegis.DistributeCandies.distribute_candies candies num_people = Result.ok ans) :
      ans.val.length = nPeople num_people ∧ entry ans 0 = 1 ∧
        ∀ j : ℕ, 1 ≤ j → j < nPeople num_people → entry ans j = 0 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (candies num_people : Std.I64)
        (hc_lo : 1 ≤ candies.val) (hc_hi : candies.val ≤ 10 ^ 9)
        (hn_lo : 1 ≤ num_people.val) (hn_hi : num_people.val ≤ 1000)
        (hc_one : candies.val = 1)
        (ans : alloc.vec.Vec Std.I64)
        (hans : Aegis.DistributeCandies.distribute_candies candies num_people = Result.ok ans), ans.val.length = nPeople num_people ∧ entry ans 0 = 1 ∧
          ∀ j : ℕ, 1 ≤ j → j < nPeople num_people → entry ans j = 0) := by
    sorry

  /-- Let n = num_people. Let k be the unique integer with k >= 0 and k*(k+1)/2 <= candies < (k+1)*(k+2)/2, and let r = candies - k*(k+1)/2. Whenever the function returns a result ans, for every index j with 0 <= j < n, ans[j] = j+1 when j < k, ans[j] = r when j = k and r > 0, and ans[j] = 0 when j > k or (j = k and r = 0).
    Preconditions: candies and num_people are integers with 1 <= candies <= 10^9, 1 <= num_people <= 1000, and num_people >= candies. -/
  theorem spec_10 (candies num_people : Std.I64)
      (hc_lo : 1 ≤ candies.val) (hc_hi : candies.val ≤ 10 ^ 9)
      (hn_lo : 1 ≤ num_people.val) (hn_hi : num_people.val ≤ 1000)
      (hle : candies.val ≤ (nPeople num_people : ℤ))
      (k : ℕ) (hk_lo : (tri k : ℤ) ≤ candies.val)
      (hk_hi : candies.val < (tri (k + 1) : ℤ))
      (ans : alloc.vec.Vec Std.I64)
      (hans : Aegis.DistributeCandies.distribute_candies candies num_people = Result.ok ans) :
      ∀ j : ℕ, j < nPeople num_people →
        entry ans j =
          (if j < k then (j : ℤ) + 1 else if j = k then rem candies.val k else 0) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (candies num_people : Std.I64)
        (hc_lo : 1 ≤ candies.val) (hc_hi : candies.val ≤ 10 ^ 9)
        (hn_lo : 1 ≤ num_people.val) (hn_hi : num_people.val ≤ 1000)
        (hle : candies.val ≤ (nPeople num_people : ℤ))
        (k : ℕ) (hk_lo : (tri k : ℤ) ≤ candies.val)
        (hk_hi : candies.val < (tri (k + 1) : ℤ))
        (ans : alloc.vec.Vec Std.I64)
        (hans : Aegis.DistributeCandies.distribute_candies candies num_people = Result.ok ans), ∀ j : ℕ, j < nPeople num_people →
          entry ans j =
            (if j < k then (j : ℤ) + 1 else if j = k then rem candies.val k else 0)) := by
    sorry

  /-- Whenever the function returns a result ans, for every index j with 0 <= j < num_people, ans[j] = j+1 if 0 <= j < K, and ans[j] = 0 if K <= j < num_people.
    Preconditions: candies and num_people are integers with 1 <= candies <= 10^9 and 1 <= num_people <= 1000; let K be the unique integer such that 1 <= K <= num_people and candies = K*(K+1)/2. -/
  theorem spec_11 (candies num_people : Std.I64)
      (hc_lo : 1 ≤ candies.val) (hc_hi : candies.val ≤ 10 ^ 9)
      (hn_lo : 1 ≤ num_people.val) (hn_hi : num_people.val ≤ 1000)
      (K : ℕ) (hK_lo : 1 ≤ K) (hK_hi : (K : ℤ) ≤ num_people.val)
      (hK_eq : candies.val = (tri K : ℤ))
      (ans : alloc.vec.Vec Std.I64)
      (hans : Aegis.DistributeCandies.distribute_candies candies num_people = Result.ok ans) :
      ∀ j : ℕ, j < nPeople num_people →
        entry ans j = (if j < K then (j : ℤ) + 1 else 0) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (candies num_people : Std.I64)
        (hc_lo : 1 ≤ candies.val) (hc_hi : candies.val ≤ 10 ^ 9)
        (hn_lo : 1 ≤ num_people.val) (hn_hi : num_people.val ≤ 1000)
        (K : ℕ) (hK_lo : 1 ≤ K) (hK_hi : (K : ℤ) ≤ num_people.val)
        (hK_eq : candies.val = (tri K : ℤ))
        (ans : alloc.vec.Vec Std.I64)
        (hans : Aegis.DistributeCandies.distribute_candies candies num_people = Result.ok ans), ∀ j : ℕ, j < nPeople num_people →
          entry ans j = (if j < K then (j : ℤ) + 1 else 0)) := by
    sorry

  /-- Let n = num_people. Let k be the unique integer with k >= 0 and k*(k+1)/2 <= candies < (k+1)*(k+2)/2, and let r = candies - k*(k+1)/2. Whenever the function returns a result ans, for every index j with 0 <= j < n, ans[j] > 0 if and only if either there exists an integer t with 1 <= t <= k and (t-1) mod n = j, or r > 0 and k mod n = j.
    Preconditions: candies and num_people are integers with 1 <= candies <= 10^9 and 1 <= num_people <= 1000. -/
  theorem spec_12 (candies num_people : Std.I64)
      (hc_lo : 1 ≤ candies.val) (hc_hi : candies.val ≤ 10 ^ 9)
      (hn_lo : 1 ≤ num_people.val) (hn_hi : num_people.val ≤ 1000)
      (k : ℕ) (hk_lo : (tri k : ℤ) ≤ candies.val)
      (hk_hi : candies.val < (tri (k + 1) : ℤ))
      (ans : alloc.vec.Vec Std.I64)
      (hans : Aegis.DistributeCandies.distribute_candies candies num_people = Result.ok ans) :
      ∀ j : ℕ, j < nPeople num_people →
        (0 < entry ans j ↔
          (∃ t : ℕ, 1 ≤ t ∧ t ≤ k ∧ (t - 1) % nPeople num_people = j) ∨
            (0 < rem candies.val k ∧ k % nPeople num_people = j)) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (candies num_people : Std.I64)
        (hc_lo : 1 ≤ candies.val) (hc_hi : candies.val ≤ 10 ^ 9)
        (hn_lo : 1 ≤ num_people.val) (hn_hi : num_people.val ≤ 1000)
        (k : ℕ) (hk_lo : (tri k : ℤ) ≤ candies.val)
        (hk_hi : candies.val < (tri (k + 1) : ℤ))
        (ans : alloc.vec.Vec Std.I64)
        (hans : Aegis.DistributeCandies.distribute_candies candies num_people = Result.ok ans), ∀ j : ℕ, j < nPeople num_people →
          (0 < entry ans j ↔
            (∃ t : ℕ, 1 ≤ t ∧ t ≤ k ∧ (t - 1) % nPeople num_people = j) ∨
              (0 < rem candies.val k ∧ k % nPeople num_people = j))) := by
    sorry

  /-- Let n = num_people. Let k be the unique integer with k >= 0 and k*(k+1)/2 <= candies < (k+1)*(k+2)/2, and let r = candies - k*(k+1)/2. Let L be the number of integers t such that 1 <= t <= k and (t-1) mod n = 0. Whenever the function returns a result ans, ans[0] = L + n*L*(L-1)/2 + (r if r > 0 and k mod n = 0, and 0 otherwise).
    Preconditions: candies and num_people are integers with 1 <= candies <= 10^9 and 1 <= num_people <= 1000. -/
  theorem spec_13 (candies num_people : Std.I64)
      (hc_lo : 1 ≤ candies.val) (hc_hi : candies.val ≤ 10 ^ 9)
      (hn_lo : 1 ≤ num_people.val) (hn_hi : num_people.val ≤ 1000)
      (k : ℕ) (hk_lo : (tri k : ℤ) ≤ candies.val)
      (hk_hi : candies.val < (tri (k + 1) : ℤ))
      (ans : alloc.vec.Vec Std.I64)
      (hans : Aegis.DistributeCandies.distribute_candies candies num_people = Result.ok ans) :
      entry ans 0 = firstEntryValue candies.val (nPeople num_people) k := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (candies num_people : Std.I64)
        (hc_lo : 1 ≤ candies.val) (hc_hi : candies.val ≤ 10 ^ 9)
        (hn_lo : 1 ≤ num_people.val) (hn_hi : num_people.val ≤ 1000)
        (k : ℕ) (hk_lo : (tri k : ℤ) ≤ candies.val)
        (hk_hi : candies.val < (tri (k + 1) : ℤ))
        (ans : alloc.vec.Vec Std.I64)
        (hans : Aegis.DistributeCandies.distribute_candies candies num_people = Result.ok ans), entry ans 0 = firstEntryValue candies.val (nPeople num_people) k) := by
    sorry

  end AegisSpec.DistributeCandies
