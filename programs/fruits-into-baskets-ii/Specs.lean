import Aegis.NumOfUnplacedFruits.Code.Funs

/-!
# Specifications of `Aegis.NumOfUnplacedFruits.num_of_unplaced_fruits`

LeetCode problem `fruits-into-baskets-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.NumOfUnplacedFruits

  open Aegis.NumOfUnplacedFruits (num_of_unplaced_fruits)

  def vals (s : Slice Std.I64) : List ℤ := s.val.map (fun x => x.val)

  def countWhere (l : List ℤ) (p : ℤ → Bool) : ℕ := (l.filter p).length

  def markFirst (fv : ℤ) : List ℤ → List Bool → List Bool
    | b :: bs, u :: us => if u = true ∨ b < fv then u :: markFirst fv bs us else true :: us
    | _, _ => []

  def simulate (fruits baskets : List ℤ) : List Bool :=
    fruits.foldl (fun used fv => markFirst fv baskets used)
      (List.replicate baskets.length false)

  def unplacedCount (fruits baskets : List ℤ) : ℕ := (simulate fruits baskets).count false

  def IsMatching (fruits baskets : List ℤ) (pairs : List (ℕ × ℕ)) : Prop :=
    (pairs.map Prod.fst).Nodup ∧ (pairs.map Prod.snd).Nodup ∧
      ∀ p ∈ pairs,
        p.1 < fruits.length ∧ p.2 < baskets.length ∧
          fruits.getD p.1 0 ≤ baskets.getD p.2 0

  noncomputable def opt (fruits baskets : List ℤ) : ℕ := by
    classical
    exact
      Nat.findGreatest
        (fun k => ∃ pairs : List (ℕ × ℕ), pairs.length = k ∧ IsMatching fruits baskets pairs)
        fruits.length

  /-- Let n = len(fruits). Define the greedy allocation as follows. Start with the set U_0 of used baskets empty. For i = 0, 1, ..., n-1 in this order, if there exists a basket index j with 0 <= j < n such that j is not in U_i and baskets[j] >= fruits[i], let p_i be the smallest such j and set U_{i+1} = U_i union {p_i}; otherwise set U_{i+1} = U_i and say fruit i is unplaced. Then the function returns a result r such that r = |{i | 0 <= i < n and fruit i is unplaced}| = n - |U_n|.
    Preconditions: len(fruits) = len(baskets) = n, 1 <= n <= 100, and 1 <= fruits[i], baskets[j] <= 1000 for every 0 <= i, j < n. -/
  theorem spec_1 (fruits baskets : Slice Std.I64) (n : ℕ)
      (hflen : fruits.val.length = n) (hblen : baskets.val.length = n)
      (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
      (hfruits : ∀ x ∈ vals fruits, 1 ≤ x ∧ x ≤ 1000)
      (hbaskets : ∀ y ∈ vals baskets, 1 ≤ y ∧ y ≤ 1000) :
      ∃ r, num_of_unplaced_fruits fruits baskets = Result.ok r ∧
        r.val = (unplacedCount (vals fruits) (vals baskets) : ℤ) ∧
        r.val = (n : ℤ) - ((simulate (vals fruits) (vals baskets)).count true : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (fruits baskets : Slice Std.I64) (n : ℕ)
        (hflen : fruits.val.length = n) (hblen : baskets.val.length = n)
        (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
        (hfruits : ∀ x ∈ vals fruits, 1 ≤ x ∧ x ≤ 1000)
        (hbaskets : ∀ y ∈ vals baskets, 1 ≤ y ∧ y ≤ 1000), ∃ r, num_of_unplaced_fruits fruits baskets = Result.ok r ∧
          r.val = (unplacedCount (vals fruits) (vals baskets) : ℤ) ∧
          r.val = (n : ℤ) - ((simulate (vals fruits) (vals baskets)).count true : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r <= n, where n = len(fruits).
    Preconditions: len(fruits) = len(baskets) = n, 1 <= n <= 100, and 1 <= fruits[i], baskets[j] <= 1000 for every 0 <= i, j < n. -/
  theorem spec_2 (fruits baskets : Slice Std.I64) (n : ℕ) (r : Std.I64)
      (hflen : fruits.val.length = n) (hblen : baskets.val.length = n)
      (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
      (hfruits : ∀ x ∈ vals fruits, 1 ≤ x ∧ x ≤ 1000)
      (hbaskets : ∀ y ∈ vals baskets, 1 ≤ y ∧ y ≤ 1000) :
      num_of_unplaced_fruits fruits baskets = Result.ok r → 0 ≤ r.val ∧ r.val ≤ (n : ℤ) := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (fruits baskets : Slice Std.I64) (n : ℕ) (r : Std.I64)
        (hflen : fruits.val.length = n) (hblen : baskets.val.length = n)
        (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
        (hfruits : ∀ x ∈ vals fruits, 1 ≤ x ∧ x ≤ 1000)
        (hbaskets : ∀ y ∈ vals baskets, 1 ≤ y ∧ y ≤ 1000), num_of_unplaced_fruits fruits baskets = Result.ok r → 0 ≤ r.val ∧ r.val ≤ (n : ℤ)) := by
    sorry

  /-- Under the preconditions, the function returns some result r; it does not fail (no panic, out-of-bounds access, or arithmetic overflow).
    Preconditions: len(fruits) = len(baskets) = n, 1 <= n <= 100, and 1 <= fruits[i], baskets[j] <= 1000 for every 0 <= i, j < n. -/
  theorem spec_3 (fruits baskets : Slice Std.I64) (n : ℕ)
      (hflen : fruits.val.length = n) (hblen : baskets.val.length = n)
      (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
      (hfruits : ∀ x ∈ vals fruits, 1 ≤ x ∧ x ≤ 1000)
      (hbaskets : ∀ y ∈ vals baskets, 1 ≤ y ∧ y ≤ 1000) :
      ∃ r, num_of_unplaced_fruits fruits baskets = Result.ok r := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (fruits baskets : Slice Std.I64) (n : ℕ)
        (hflen : fruits.val.length = n) (hblen : baskets.val.length = n)
        (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
        (hfruits : ∀ x ∈ vals fruits, 1 ≤ x ∧ x ≤ 1000)
        (hbaskets : ∀ y ∈ vals baskets, 1 ≤ y ∧ y ≤ 1000), ∃ r, num_of_unplaced_fruits fruits baskets = Result.ok r) := by
    sorry

  /-- The function returns a result r with r = 0 if baskets[0] >= fruits[0], and r = 1 if baskets[0] < fruits[0].
    Preconditions: len(fruits) = len(baskets) = n, 1 <= n <= 100, 1 <= fruits[i], baskets[j] <= 1000 for every 0 <= i, j < n, and n = 1. -/
  theorem spec_4 (fruits baskets : Slice Std.I64) (n : ℕ) (fv bv : Std.I64) (r : Std.I64)
      (hflen : fruits.val.length = n) (hblen : baskets.val.length = n)
      (hn1 : 1 ≤ n) (hn2 : n ≤ 100) (hn_eq : n = 1)
      (hfruits : ∀ x ∈ vals fruits, 1 ≤ x ∧ x ≤ 1000)
      (hbaskets : ∀ y ∈ vals baskets, 1 ≤ y ∧ y ≤ 1000)
      (hfv : fruits.val = [fv]) (hbv : baskets.val = [bv]) :
      num_of_unplaced_fruits fruits baskets = Result.ok r →
        ((fv.val ≤ bv.val → r.val = 0) ∧ (bv.val < fv.val → r.val = 1)) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (fruits baskets : Slice Std.I64) (n : ℕ) (fv bv : Std.I64) (r : Std.I64)
        (hflen : fruits.val.length = n) (hblen : baskets.val.length = n)
        (hn1 : 1 ≤ n) (hn2 : n ≤ 100) (hn_eq : n = 1)
        (hfruits : ∀ x ∈ vals fruits, 1 ≤ x ∧ x ≤ 1000)
        (hbaskets : ∀ y ∈ vals baskets, 1 ≤ y ∧ y ≤ 1000)
        (hfv : fruits.val = [fv]) (hbv : baskets.val = [bv]), num_of_unplaced_fruits fruits baskets = Result.ok r →
          ((fv.val ≤ bv.val → r.val = 0) ∧ (bv.val < fv.val → r.val = 1))) := by
    sorry

  /-- For such an input, the function returns r = |{i | 0 <= i < n and fruits[i] > c}|.
    Preconditions: len(fruits) = len(baskets) = n, 1 <= n <= 100, 1 <= fruits[i], baskets[j] <= 1000 for every 0 <= i, j < n, and there is an integer c such that baskets[j] = c for every 0 <= j < n. -/
  theorem spec_5 (fruits baskets : Slice Std.I64) (n : ℕ) (c : ℤ) (r : Std.I64)
      (hflen : fruits.val.length = n) (hblen : baskets.val.length = n)
      (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
      (hfruits : ∀ x ∈ vals fruits, 1 ≤ x ∧ x ≤ 1000)
      (hbaskets : ∀ y ∈ vals baskets, 1 ≤ y ∧ y ≤ 1000)
      (hconst : ∀ y ∈ vals baskets, y = c) :
      num_of_unplaced_fruits fruits baskets = Result.ok r →
        r.val = (countWhere (vals fruits) (fun x => decide (c < x)) : ℤ) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (fruits baskets : Slice Std.I64) (n : ℕ) (c : ℤ) (r : Std.I64)
        (hflen : fruits.val.length = n) (hblen : baskets.val.length = n)
        (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
        (hfruits : ∀ x ∈ vals fruits, 1 ≤ x ∧ x ≤ 1000)
        (hbaskets : ∀ y ∈ vals baskets, 1 ≤ y ∧ y ≤ 1000)
        (hconst : ∀ y ∈ vals baskets, y = c), num_of_unplaced_fruits fruits baskets = Result.ok r →
          r.val = (countWhere (vals fruits) (fun x => decide (c < x)) : ℤ)) := by
    sorry

  /-- For such an input, the function returns r = n - |{j | 0 <= j < n and baskets[j] >= q}|.
    Preconditions: len(fruits) = len(baskets) = n, 1 <= n <= 100, 1 <= fruits[i], baskets[j] <= 1000 for every 0 <= i, j < n, and there is an integer q such that fruits[i] = q for every 0 <= i < n. -/
  theorem spec_6 (fruits baskets : Slice Std.I64) (n : ℕ) (q : ℤ) (r : Std.I64)
      (hflen : fruits.val.length = n) (hblen : baskets.val.length = n)
      (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
      (hfruits : ∀ x ∈ vals fruits, 1 ≤ x ∧ x ≤ 1000)
      (hbaskets : ∀ y ∈ vals baskets, 1 ≤ y ∧ y ≤ 1000)
      (hconst : ∀ x ∈ vals fruits, x = q) :
      num_of_unplaced_fruits fruits baskets = Result.ok r →
        r.val = (n : ℤ) - (countWhere (vals baskets) (fun y => decide (q ≤ y)) : ℤ) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (fruits baskets : Slice Std.I64) (n : ℕ) (q : ℤ) (r : Std.I64)
        (hflen : fruits.val.length = n) (hblen : baskets.val.length = n)
        (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
        (hfruits : ∀ x ∈ vals fruits, 1 ≤ x ∧ x ≤ 1000)
        (hbaskets : ∀ y ∈ vals baskets, 1 ≤ y ∧ y ≤ 1000)
        (hconst : ∀ x ∈ vals fruits, x = q), num_of_unplaced_fruits fruits baskets = Result.ok r →
          r.val = (n : ℤ) - (countWhere (vals baskets) (fun y => decide (q ≤ y)) : ℤ)) := by
    sorry

  /-- Let M = max_{0 <= j < n} baskets[j] and let T = |{i | 0 <= i < n and fruits[i] > M}|. Whenever the function returns a result r, r >= T.
    Preconditions: len(fruits) = len(baskets) = n, 1 <= n <= 100, and 1 <= fruits[i], baskets[j] <= 1000 for every 0 <= i, j < n. -/
  theorem spec_7 (fruits baskets : Slice Std.I64) (n : ℕ) (M : ℤ) (r : Std.I64)
      (hflen : fruits.val.length = n) (hblen : baskets.val.length = n)
      (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
      (hfruits : ∀ x ∈ vals fruits, 1 ≤ x ∧ x ≤ 1000)
      (hbaskets : ∀ y ∈ vals baskets, 1 ≤ y ∧ y ≤ 1000)
      (hM : ∀ y ∈ vals baskets, y ≤ M) (hM' : ∃ y ∈ vals baskets, y = M) :
      num_of_unplaced_fruits fruits baskets = Result.ok r →
        (countWhere (vals fruits) (fun x => decide (M < x)) : ℤ) ≤ r.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (fruits baskets : Slice Std.I64) (n : ℕ) (M : ℤ) (r : Std.I64)
        (hflen : fruits.val.length = n) (hblen : baskets.val.length = n)
        (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
        (hfruits : ∀ x ∈ vals fruits, 1 ≤ x ∧ x ≤ 1000)
        (hbaskets : ∀ y ∈ vals baskets, 1 ≤ y ∧ y ≤ 1000)
        (hM : ∀ y ∈ vals baskets, y ≤ M) (hM' : ∃ y ∈ vals baskets, y = M), num_of_unplaced_fruits fruits baskets = Result.ok r →
          (countWhere (vals fruits) (fun x => decide (M < x)) : ℤ) ≤ r.val) := by
    sorry

  /-- Let m = min_{0 <= j < n} baskets[j] and let T = |{i | 0 <= i < n and fruits[i] > m}|. Whenever the function returns a result r, r <= T. Equivalently, every fruit i with fruits[i] <= m is placed.
    Preconditions: len(fruits) = len(baskets) = n, 1 <= n <= 100, and 1 <= fruits[i], baskets[j] <= 1000 for every 0 <= i, j < n. -/
  theorem spec_8 (fruits baskets : Slice Std.I64) (n : ℕ) (m : ℤ) (r : Std.I64)
      (hflen : fruits.val.length = n) (hblen : baskets.val.length = n)
      (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
      (hfruits : ∀ x ∈ vals fruits, 1 ≤ x ∧ x ≤ 1000)
      (hbaskets : ∀ y ∈ vals baskets, 1 ≤ y ∧ y ≤ 1000)
      (hm : ∀ y ∈ vals baskets, m ≤ y) (hm' : ∃ y ∈ vals baskets, y = m) :
      num_of_unplaced_fruits fruits baskets = Result.ok r →
        r.val ≤ (countWhere (vals fruits) (fun x => decide (m < x)) : ℤ) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (fruits baskets : Slice Std.I64) (n : ℕ) (m : ℤ) (r : Std.I64)
        (hflen : fruits.val.length = n) (hblen : baskets.val.length = n)
        (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
        (hfruits : ∀ x ∈ vals fruits, 1 ≤ x ∧ x ≤ 1000)
        (hbaskets : ∀ y ∈ vals baskets, 1 ≤ y ∧ y ≤ 1000)
        (hm : ∀ y ∈ vals baskets, m ≤ y) (hm' : ∃ y ∈ vals baskets, y = m), num_of_unplaced_fruits fruits baskets = Result.ok r →
          r.val ≤ (countWhere (vals fruits) (fun x => decide (m < x)) : ℤ)) := by
    sorry

  /-- Let fruits' and baskets' be defined by fruits'[i] = fruits[i] + c and baskets'[j] = baskets[j] + c for all i, j. The function returns the same result r on (fruits', baskets') as it does on (fruits, baskets).
    Preconditions: len(fruits) = len(baskets) = n, 1 <= n <= 100, 1 <= fruits[i], baskets[j] <= 1000 for every 0 <= i, j < n, and c is an integer such that 1 <= fruits[i] + c <= 1000 and 1 <= baskets[j] + c <= 1000 for all 0 <= i, j < n. -/
  theorem spec_9 (fruits baskets fruits' baskets' : Slice Std.I64) (n : ℕ) (c : ℤ)
      (hflen : fruits.val.length = n) (hblen : baskets.val.length = n)
      (hflen' : fruits'.val.length = n) (hblen' : baskets'.val.length = n)
      (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
      (hfruits : ∀ x ∈ vals fruits, 1 ≤ x ∧ x ≤ 1000)
      (hbaskets : ∀ y ∈ vals baskets, 1 ≤ y ∧ y ≤ 1000)
      (hfruits_c : ∀ x ∈ vals fruits, 1 ≤ x + c ∧ x + c ≤ 1000)
      (hbaskets_c : ∀ y ∈ vals baskets, 1 ≤ y + c ∧ y + c ≤ 1000)
      (hF : vals fruits' = (vals fruits).map (fun x => x + c))
      (hB : vals baskets' = (vals baskets).map (fun y => y + c)) :
      ∃ r, num_of_unplaced_fruits fruits baskets = Result.ok r ∧
        num_of_unplaced_fruits fruits' baskets' = Result.ok r := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (fruits baskets fruits' baskets' : Slice Std.I64) (n : ℕ) (c : ℤ)
        (hflen : fruits.val.length = n) (hblen : baskets.val.length = n)
        (hflen' : fruits'.val.length = n) (hblen' : baskets'.val.length = n)
        (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
        (hfruits : ∀ x ∈ vals fruits, 1 ≤ x ∧ x ≤ 1000)
        (hbaskets : ∀ y ∈ vals baskets, 1 ≤ y ∧ y ≤ 1000)
        (hfruits_c : ∀ x ∈ vals fruits, 1 ≤ x + c ∧ x + c ≤ 1000)
        (hbaskets_c : ∀ y ∈ vals baskets, 1 ≤ y + c ∧ y + c ≤ 1000)
        (hF : vals fruits' = (vals fruits).map (fun x => x + c))
        (hB : vals baskets' = (vals baskets).map (fun y => y + c)), ∃ r, num_of_unplaced_fruits fruits baskets = Result.ok r ∧
          num_of_unplaced_fruits fruits' baskets' = Result.ok r) := by
    sorry

  /-- Let fruits' and baskets' be defined by fruits'[i] = c * fruits[i] and baskets'[j] = c * baskets[j] for all i, j. The function returns the same result r on (fruits', baskets') as it does on (fruits, baskets).
    Preconditions: len(fruits) = len(baskets) = n, 1 <= n <= 100, 1 <= fruits[i], baskets[j] <= 1000 for every 0 <= i, j < n, and c is a positive integer such that 1 <= c * fruits[i] <= 1000 and 1 <= c * baskets[j] <= 1000 for all 0 <= i, j < n. -/
  theorem spec_10 (fruits baskets fruits' baskets' : Slice Std.I64) (n : ℕ) (c : ℤ)
      (hflen : fruits.val.length = n) (hblen : baskets.val.length = n)
      (hflen' : fruits'.val.length = n) (hblen' : baskets'.val.length = n)
      (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
      (hfruits : ∀ x ∈ vals fruits, 1 ≤ x ∧ x ≤ 1000)
      (hbaskets : ∀ y ∈ vals baskets, 1 ≤ y ∧ y ≤ 1000)
      (hc : 1 ≤ c)
      (hfruits_c : ∀ x ∈ vals fruits, 1 ≤ c * x ∧ c * x ≤ 1000)
      (hbaskets_c : ∀ y ∈ vals baskets, 1 ≤ c * y ∧ c * y ≤ 1000)
      (hF : vals fruits' = (vals fruits).map (fun x => c * x))
      (hB : vals baskets' = (vals baskets).map (fun y => c * y)) :
      ∃ r, num_of_unplaced_fruits fruits baskets = Result.ok r ∧
        num_of_unplaced_fruits fruits' baskets' = Result.ok r := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (fruits baskets fruits' baskets' : Slice Std.I64) (n : ℕ) (c : ℤ)
        (hflen : fruits.val.length = n) (hblen : baskets.val.length = n)
        (hflen' : fruits'.val.length = n) (hblen' : baskets'.val.length = n)
        (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
        (hfruits : ∀ x ∈ vals fruits, 1 ≤ x ∧ x ≤ 1000)
        (hbaskets : ∀ y ∈ vals baskets, 1 ≤ y ∧ y ≤ 1000)
        (hc : 1 ≤ c)
        (hfruits_c : ∀ x ∈ vals fruits, 1 ≤ c * x ∧ c * x ≤ 1000)
        (hbaskets_c : ∀ y ∈ vals baskets, 1 ≤ c * y ∧ c * y ≤ 1000)
        (hF : vals fruits' = (vals fruits).map (fun x => c * x))
        (hB : vals baskets' = (vals baskets).map (fun y => c * y)), ∃ r, num_of_unplaced_fruits fruits baskets = Result.ok r ∧
          num_of_unplaced_fruits fruits' baskets' = Result.ok r) := by
    sorry

  /-- Let r be the result of the function on (fruits, baskets) and let r' be its result on (fruits, baskets'). Then r' <= r.
    Preconditions: len(fruits) = len(baskets) = n, 1 <= n <= 100, 1 <= fruits[i], baskets[j] <= 1000 for every 0 <= i, j < n, and baskets' is an array of length n with 1 <= baskets'[j] <= 1000 and baskets'[j] >= baskets[j] for every 0 <= j < n. -/
  theorem spec_11 (fruits baskets baskets' : Slice Std.I64) (n : ℕ) (r r' : Std.I64)
      (hflen : fruits.val.length = n) (hblen : baskets.val.length = n)
      (hblen' : baskets'.val.length = n)
      (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
      (hfruits : ∀ x ∈ vals fruits, 1 ≤ x ∧ x ≤ 1000)
      (hbaskets : ∀ y ∈ vals baskets, 1 ≤ y ∧ y ≤ 1000)
      (hbaskets' : ∀ y ∈ vals baskets', 1 ≤ y ∧ y ≤ 1000)
      (hle : List.Forall₂ (fun a b => a ≤ b) (vals baskets) (vals baskets')) :
      num_of_unplaced_fruits fruits baskets = Result.ok r →
        num_of_unplaced_fruits fruits baskets' = Result.ok r' → r'.val ≤ r.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (fruits baskets baskets' : Slice Std.I64) (n : ℕ) (r r' : Std.I64)
        (hflen : fruits.val.length = n) (hblen : baskets.val.length = n)
        (hblen' : baskets'.val.length = n)
        (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
        (hfruits : ∀ x ∈ vals fruits, 1 ≤ x ∧ x ≤ 1000)
        (hbaskets : ∀ y ∈ vals baskets, 1 ≤ y ∧ y ≤ 1000)
        (hbaskets' : ∀ y ∈ vals baskets', 1 ≤ y ∧ y ≤ 1000)
        (hle : List.Forall₂ (fun a b => a ≤ b) (vals baskets) (vals baskets')), num_of_unplaced_fruits fruits baskets = Result.ok r →
          num_of_unplaced_fruits fruits baskets' = Result.ok r' → r'.val ≤ r.val) := by
    sorry

  /-- Let OPT be the largest integer k for which there exist k distinct fruit indices i_1, ..., i_k and k distinct basket indices j_1, ..., j_k with 0 <= i_t, j_t < n for all t and baskets[j_t] >= fruits[i_t] for every t = 1, ..., k. The function returns r = n - OPT.
    Preconditions: len(fruits) = len(baskets) = n, 1 <= n <= 100, 1 <= fruits[i], baskets[j] <= 1000 for every 0 <= i, j < n, and baskets is nondecreasing: baskets[0] <= baskets[1] <= ... <= baskets[n-1]. -/
  theorem spec_12 (fruits baskets : Slice Std.I64) (n : ℕ)
      (hflen : fruits.val.length = n) (hblen : baskets.val.length = n)
      (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
      (hfruits : ∀ x ∈ vals fruits, 1 ≤ x ∧ x ≤ 1000)
      (hbaskets : ∀ y ∈ vals baskets, 1 ≤ y ∧ y ≤ 1000)
      (hmono : List.Pairwise (· ≤ ·) (vals baskets)) :
      ∃ r, num_of_unplaced_fruits fruits baskets = Result.ok r ∧
        r.val = (n : ℤ) - (opt (vals fruits) (vals baskets) : ℤ) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (fruits baskets : Slice Std.I64) (n : ℕ)
        (hflen : fruits.val.length = n) (hblen : baskets.val.length = n)
        (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
        (hfruits : ∀ x ∈ vals fruits, 1 ≤ x ∧ x ≤ 1000)
        (hbaskets : ∀ y ∈ vals baskets, 1 ≤ y ∧ y ≤ 1000)
        (hmono : List.Pairwise (· ≤ ·) (vals baskets)), ∃ r, num_of_unplaced_fruits fruits baskets = Result.ok r ∧
          r.val = (n : ℤ) - (opt (vals fruits) (vals baskets) : ℤ)) := by
    sorry

  /-- Let r be the result on (fruits, baskets) and r' the result on (fruits', baskets). Then r' >= r: increasing fruit quantities cannot decrease the number of unplaced fruit types.
    Preconditions: len(fruits) = len(baskets) = n = len(fruits'), 1 <= n <= 100, 1 <= fruits[i], fruits'[i], baskets[j] <= 1000 for all i,j, and fruits'[i] >= fruits[i] for every i. -/
  theorem spec_13 (fruits fruits' baskets : Slice Std.I64) (n : ℕ) (r r' : Std.I64)
      (hflen : fruits.val.length = n) (hflen' : fruits'.val.length = n)
      (hblen : baskets.val.length = n)
      (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
      (hfruits : ∀ x ∈ vals fruits, 1 ≤ x ∧ x ≤ 1000)
      (hfruits' : ∀ x ∈ vals fruits', 1 ≤ x ∧ x ≤ 1000)
      (hbaskets : ∀ y ∈ vals baskets, 1 ≤ y ∧ y ≤ 1000)
      (hle : List.Forall₂ (fun a b => a ≤ b) (vals fruits) (vals fruits')) :
      num_of_unplaced_fruits fruits baskets = Result.ok r →
        num_of_unplaced_fruits fruits' baskets = Result.ok r' → r.val ≤ r'.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (fruits fruits' baskets : Slice Std.I64) (n : ℕ) (r r' : Std.I64)
        (hflen : fruits.val.length = n) (hflen' : fruits'.val.length = n)
        (hblen : baskets.val.length = n)
        (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
        (hfruits : ∀ x ∈ vals fruits, 1 ≤ x ∧ x ≤ 1000)
        (hfruits' : ∀ x ∈ vals fruits', 1 ≤ x ∧ x ≤ 1000)
        (hbaskets : ∀ y ∈ vals baskets, 1 ≤ y ∧ y ≤ 1000)
        (hle : List.Forall₂ (fun a b => a ≤ b) (vals fruits) (vals fruits')), num_of_unplaced_fruits fruits baskets = Result.ok r →
          num_of_unplaced_fruits fruits' baskets = Result.ok r' → r.val ≤ r'.val) := by
    sorry

  /-- Let OPT be the largest integer k for which there exist k distinct fruit indices i_1, ..., i_k and k distinct basket indices j_1, ..., j_k with baskets[j_t] >= fruits[i_t] for every t. If the function returns r, then r >= n - OPT; the greedy allocation places at most the maximum possible number of fruits.
    Preconditions: len(fruits) = len(baskets) = n, 1 <= n <= 100, and 1 <= fruits[i], baskets[j] <= 1000 for every 0 <= i, j < n. -/
  theorem spec_14 (fruits baskets : Slice Std.I64) (n : ℕ) (r : Std.I64)
      (hflen : fruits.val.length = n) (hblen : baskets.val.length = n)
      (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
      (hfruits : ∀ x ∈ vals fruits, 1 ≤ x ∧ x ≤ 1000)
      (hbaskets : ∀ y ∈ vals baskets, 1 ≤ y ∧ y ≤ 1000) :
      num_of_unplaced_fruits fruits baskets = Result.ok r →
        (n : ℤ) - (opt (vals fruits) (vals baskets) : ℤ) ≤ r.val := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (fruits baskets : Slice Std.I64) (n : ℕ) (r : Std.I64)
        (hflen : fruits.val.length = n) (hblen : baskets.val.length = n)
        (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
        (hfruits : ∀ x ∈ vals fruits, 1 ≤ x ∧ x ≤ 1000)
        (hbaskets : ∀ y ∈ vals baskets, 1 ≤ y ∧ y ≤ 1000), num_of_unplaced_fruits fruits baskets = Result.ok r →
          (n : ℤ) - (opt (vals fruits) (vals baskets) : ℤ) ≤ r.val) := by
    sorry

  end AegisSpec.NumOfUnplacedFruits
