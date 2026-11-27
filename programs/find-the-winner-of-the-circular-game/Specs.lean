import Aegis.FindTheWinner.Code.Funs

/-!
# Specifications of `Aegis.FindTheWinner.find_the_winner`

LeetCode problem `find-the-winner-of-the-circular-game`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.FindTheWinner

  def circle (m : Nat) : List Int := (List.range m).map fun i => (i : Int) + 1

  def countOutStep (c : List Int) (cur kk : Nat) : List Int × Nat :=
    let j := (cur + (kk - 1)) % c.length
    (c.eraseIdx j, j % (c.length - 1))

  def countOutAux (kk : Nat) : Nat → List Int → Nat → Int
    | 0, c, _ => c.headD 0
    | fuel + 1, c, cur =>
        let s := countOutStep c cur kk
        countOutAux kk fuel s.1 s.2

  def countOutWinner (m kk : Nat) : Int := countOutAux kk (m - 1) (circle m) 0

  /-- Whenever find_the_winner(n, k) returns a result r under these preconditions, r is the label of the unique friend left by the following process. Initially the circle contains the friends 1,...,n in clockwise order, and the current friend is 1. While at least two friends remain in the circle, starting from the current friend and moving clockwise through the friends still in the circle, count k friends, with the current friend counted as 1 and with the count continuing around the circle (possibly more than once, so some friends may be counted several times) whenever it reaches the last remaining friend. Remove the k-th friend counted. If at least two friends remain, set the current friend to the friend immediately clockwise of the removed friend among the friends still in the circle. When exactly one friend remains, r is that friend's original label.
    Preconditions: n and k are integers with 1 <= k <= n <= 500 (so n >= 1). -/
  theorem spec_1 (n k : Std.I64)
      (hk1 : 1 ≤ k.val) (hkn : k.val ≤ n.val) (hn : n.val ≤ 500) :
      ∀ r, Aegis.FindTheWinner.find_the_winner n k = ok r →
        r.val = countOutWinner n.val.toNat k.val.toNat := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n k : Std.I64)
        (hk1 : 1 ≤ k.val) (hkn : k.val ≤ n.val) (hn : n.val ≤ 500), ∀ r, Aegis.FindTheWinner.find_the_winner n k = ok r →
          r.val = countOutWinner n.val.toNat k.val.toNat) := by
    sorry

  /-- Under these preconditions, find_the_winner(n, k) returns a result r; it does not fail, overflow, panic, or run out of bounds.
    Preconditions: n and k are integers with 1 <= k <= n <= 500. -/
  theorem spec_2 (n k : Std.I64)
      (hk1 : 1 ≤ k.val) (hkn : k.val ≤ n.val) (hn : n.val ≤ 500) :
      ∃ r, Aegis.FindTheWinner.find_the_winner n k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n k : Std.I64)
        (hk1 : 1 ≤ k.val) (hkn : k.val ≤ n.val) (hn : n.val ≤ 500), ∃ r, Aegis.FindTheWinner.find_the_winner n k = ok r) := by
    sorry

  /-- Whenever find_the_winner(n, k) returns a result r under these preconditions, 1 <= r <= n.
    Preconditions: n and k are integers with 1 <= k <= n <= 500. -/
  theorem spec_3 (n k : Std.I64)
      (hk1 : 1 ≤ k.val) (hkn : k.val ≤ n.val) (hn : n.val ≤ 500) :
      ∀ r, Aegis.FindTheWinner.find_the_winner n k = ok r → 1 ≤ r.val ∧ r.val ≤ n.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n k : Std.I64)
        (hk1 : 1 ≤ k.val) (hkn : k.val ≤ n.val) (hn : n.val ≤ 500), ∀ r, Aegis.FindTheWinner.find_the_winner n k = ok r → 1 ≤ r.val ∧ r.val ≤ n.val) := by
    sorry

  /-- find_the_winner(n, k) returns a result r with r = 1.
    Preconditions: 1 <= k <= n <= 500 and n = 1. -/
  theorem spec_4 (n k : Std.I64)
      (hk1 : 1 ≤ k.val) (hkn : k.val ≤ n.val) (hn : n.val ≤ 500) (hn1 : n.val = 1) :
      ∃ r, Aegis.FindTheWinner.find_the_winner n k = ok r ∧ r.val = 1 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n k : Std.I64)
        (hk1 : 1 ≤ k.val) (hkn : k.val ≤ n.val) (hn : n.val ≤ 500) (hn1 : n.val = 1), ∃ r, Aegis.FindTheWinner.find_the_winner n k = ok r ∧ r.val = 1) := by
    sorry

  /-- find_the_winner(n, k) returns a result r with r = n.
    Preconditions: 1 <= k <= n <= 500 and k = 1. -/
  theorem spec_5 (n k : Std.I64)
      (hk1 : 1 ≤ k.val) (hkn : k.val ≤ n.val) (hn : n.val ≤ 500) (hk_eq : k.val = 1) :
      ∃ r, Aegis.FindTheWinner.find_the_winner n k = ok r ∧ r.val = n.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n k : Std.I64)
        (hk1 : 1 ≤ k.val) (hkn : k.val ≤ n.val) (hn : n.val ≤ 500) (hk_eq : k.val = 1), ∃ r, Aegis.FindTheWinner.find_the_winner n k = ok r ∧ r.val = n.val) := by
    sorry

  /-- find_the_winner(n, k) returns a result r with r = 3 - k.
    Preconditions: 1 <= k <= n <= 500 and n = 2. -/
  theorem spec_6 (n k : Std.I64)
      (hk1 : 1 ≤ k.val) (hkn : k.val ≤ n.val) (hn : n.val ≤ 500) (hn2 : n.val = 2) :
      ∃ r, Aegis.FindTheWinner.find_the_winner n k = ok r ∧ r.val = 3 - k.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n k : Std.I64)
        (hk1 : 1 ≤ k.val) (hkn : k.val ≤ n.val) (hn : n.val ≤ 500) (hn2 : n.val = 2), ∃ r, Aegis.FindTheWinner.find_the_winner n k = ok r ∧ r.val = 3 - k.val) := by
    sorry

  /-- find_the_winner(n, k) returns a result r with r = 3 when k is 1 or 2, and r = 2 when k = 3.
    Preconditions: 1 <= k <= n <= 500 and n = 3. -/
  theorem spec_7 (n k : Std.I64)
      (hk1 : 1 ≤ k.val) (hkn : k.val ≤ n.val) (hn : n.val ≤ 500) (hn3 : n.val = 3) :
      ∃ r, Aegis.FindTheWinner.find_the_winner n k = ok r ∧
        (k.val = 1 ∨ k.val = 2 → r.val = 3) ∧ (k.val = 3 → r.val = 2) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n k : Std.I64)
        (hk1 : 1 ≤ k.val) (hkn : k.val ≤ n.val) (hn : n.val ≤ 500) (hn3 : n.val = 3), ∃ r, Aegis.FindTheWinner.find_the_winner n k = ok r ∧
          (k.val = 1 ∨ k.val = 2 → r.val = 3) ∧ (k.val = 3 → r.val = 2)) := by
    sorry

  /-- find_the_winner(n, k) returns a result r with r = 4 if k = 1, r = 1 if k = 2, r = 1 if k = 3, and r = 2 if k = 4.
    Preconditions: 1 <= k <= n <= 500 and n = 4. -/
  theorem spec_8 (n k : Std.I64)
      (hk1 : 1 ≤ k.val) (hkn : k.val ≤ n.val) (hn : n.val ≤ 500) (hn4 : n.val = 4) :
      ∃ r, Aegis.FindTheWinner.find_the_winner n k = ok r ∧
        (k.val = 1 → r.val = 4) ∧ (k.val = 2 → r.val = 1) ∧
        (k.val = 3 → r.val = 1) ∧ (k.val = 4 → r.val = 2) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n k : Std.I64)
        (hk1 : 1 ≤ k.val) (hkn : k.val ≤ n.val) (hn : n.val ≤ 500) (hn4 : n.val = 4), ∃ r, Aegis.FindTheWinner.find_the_winner n k = ok r ∧
          (k.val = 1 → r.val = 4) ∧ (k.val = 2 → r.val = 1) ∧
          (k.val = 3 → r.val = 1) ∧ (k.val = 4 → r.val = 2)) := by
    sorry

  /-- Let p be the unique power of two such that p <= n < 2p. Whenever find_the_winner(n, k) returns a result r under these preconditions, r = 2 * (n - p) + 1.
    Preconditions: 1 <= k <= n <= 500 and k = 2. -/
  theorem spec_9 (n k : Std.I64)
      (hk1 : 1 ≤ k.val) (hkn : k.val ≤ n.val) (hn : n.val ≤ 500) (hk2 : k.val = 2)
      (p : Int) (hp : ∃ t : Nat, p = (2 : Int) ^ t) (hlo : p ≤ n.val) (hhi : n.val < 2 * p) :
      ∀ r, Aegis.FindTheWinner.find_the_winner n k = ok r → r.val = 2 * (n.val - p) + 1 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n k : Std.I64)
        (hk1 : 1 ≤ k.val) (hkn : k.val ≤ n.val) (hn : n.val ≤ 500) (hk2 : k.val = 2)
        (p : Int) (hp : ∃ t : Nat, p = (2 : Int) ^ t) (hlo : p ≤ n.val) (hhi : n.val < 2 * p), ∀ r, Aegis.FindTheWinner.find_the_winner n k = ok r → r.val = 2 * (n.val - p) + 1) := by
    sorry

  /-- Let J(m, k) denote the winner of the same circular game played with m >= 1 friends labeled 1,...,m, starting at friend 1 and using the same positive counting parameter k; the count may wrap around the smaller circle any number of times. Whenever find_the_winner(n, k) returns a result r under these preconditions, r = ((J(n - 1, k) + k - 1) mod n) + 1.
    Preconditions: 1 <= k <= n <= 500 and n > 1. -/
  theorem spec_10 (n k : Std.I64)
      (hk1 : 1 ≤ k.val) (hkn : k.val ≤ n.val) (hn : n.val ≤ 500) (hn_gt : 1 < n.val) :
      ∀ r, Aegis.FindTheWinner.find_the_winner n k = ok r →
        r.val = (countOutWinner (n.val - 1).toNat k.val.toNat + k.val - 1) % n.val + 1 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n k : Std.I64)
        (hk1 : 1 ≤ k.val) (hkn : k.val ≤ n.val) (hn : n.val ≤ 500) (hn_gt : 1 < n.val), ∀ r, Aegis.FindTheWinner.find_the_winner n k = ok r →
          r.val = (countOutWinner (n.val - 1).toNat k.val.toNat + k.val - 1) % n.val + 1) := by
    sorry

  /-- Whenever find_the_winner(n, k) returns a result r under these preconditions, r != k.
    Preconditions: 1 <= k <= n <= 500 and n > 1. -/
  theorem spec_11 (n k : Std.I64)
      (hk1 : 1 ≤ k.val) (hkn : k.val ≤ n.val) (hn : n.val ≤ 500) (hn_gt : 1 < n.val) :
      ∀ r, Aegis.FindTheWinner.find_the_winner n k = ok r → r.val ≠ k.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (n k : Std.I64)
        (hk1 : 1 ≤ k.val) (hkn : k.val ≤ n.val) (hn : n.val ≤ 500) (hn_gt : 1 < n.val), ∀ r, Aegis.FindTheWinner.find_the_winner n k = ok r → r.val ≠ k.val) := by
    sorry

  end AegisSpec.FindTheWinner
