import Aegis.KidsWithCandies.Code.Funs

/-!
# Specifications of `Aegis.KidsWithCandies.kids_with_candies`

LeetCode problem `kids-with-the-greatest-number-of-candies`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.KidsWithCandies

def vals (candies : Slice Std.I64) : List Int := candies.val.map (fun x => x.val)

def IsMax (l : List Int) (M : Int) : Prop := (∀ x ∈ l, x ≤ M) ∧ M ∈ l

def IsMin (l : List Int) (m : Int) : Prop := (∀ x ∈ l, m ≤ x) ∧ m ∈ l

/-- The function returns a result r, len(r) = n, and for every i with 0 <= i < n, r[i] is true if and only if candies[i] + extraCandies >= candies[j] for every j with 0 <= j < n; equivalently, r[i] is true if and only if candies[i] + extraCandies >= M, where M is the maximum of candies[0..n-1].
  Preconditions: n = len(candies); 2 <= n <= 100; for every i with 0 <= i < n, 1 <= candies[i] <= 100; 1 <= extraCandies <= 50. -/
theorem spec_1 (candies : Slice Std.I64) (extraCandies : Std.I64) (n : Nat)
    (hn : n = candies.val.length) (hn_ge : 2 ≤ n) (hn_le : n ≤ 100)
    (hcandies : ∀ (i : Nat) (hi : i < n),
      1 ≤ (candies.val[i]).val ∧ (candies.val[i]).val ≤ 100)
    (hextra : 1 ≤ extraCandies.val ∧ extraCandies.val ≤ 50) :
    ∃ r, Aegis.KidsWithCandies.kids_with_candies candies extraCandies = ok r ∧
      r.val.length = n ∧
      ∀ (i : Nat) (hi : i < n), (r.val[i]? = some true ↔
        ∀ (j : Nat) (hj : j < n), (candies.val[i]).val + extraCandies.val ≥ (candies.val[j]).val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (candies : Slice Std.I64) (extraCandies : Std.I64) (n : Nat)
    (hn : n = candies.val.length) (hn_ge : 2 ≤ n) (hn_le : n ≤ 100)
    (hcandies : ∀ (i : Nat) (hi : i < n),
      1 ≤ (candies.val[i]).val ∧ (candies.val[i]).val ≤ 100)
    (hextra : 1 ≤ extraCandies.val ∧ extraCandies.val ≤ 50), ∃ r, Aegis.KidsWithCandies.kids_with_candies candies extraCandies = ok r ∧
      r.val.length = n ∧
      ∀ (i : Nat) (hi : i < n), (r.val[i]? = some true ↔
        ∀ (j : Nat) (hj : j < n), (candies.val[i]).val + extraCandies.val ≥ (candies.val[j]).val)) := by
  sorry

/-- The function returns a result r (it does not fail). In particular every addition candies[i] + extraCandies stays within the i64 range, since 1 <= candies[i] <= 100 and 1 <= extraCandies <= 50.
  Preconditions: n = len(candies); 2 <= n <= 100; for every i with 0 <= i < n, 1 <= candies[i] <= 100; 1 <= extraCandies <= 50. -/
theorem spec_2 (candies : Slice Std.I64) (extraCandies : Std.I64) (n : Nat)
    (hn : n = candies.val.length) (hn_ge : 2 ≤ n) (hn_le : n ≤ 100)
    (hcandies : ∀ (i : Nat) (hi : i < n),
      1 ≤ (candies.val[i]).val ∧ (candies.val[i]).val ≤ 100)
    (hextra : 1 ≤ extraCandies.val ∧ extraCandies.val ≤ 50) :
    ∃ r, Aegis.KidsWithCandies.kids_with_candies candies extraCandies = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (candies : Slice Std.I64) (extraCandies : Std.I64) (n : Nat)
    (hn : n = candies.val.length) (hn_ge : 2 ≤ n) (hn_le : n ≤ 100)
    (hcandies : ∀ (i : Nat) (hi : i < n),
      1 ≤ (candies.val[i]).val ∧ (candies.val[i]).val ≤ 100)
    (hextra : 1 ≤ extraCandies.val ∧ extraCandies.val ≤ 50), ∃ r, Aegis.KidsWithCandies.kids_with_candies candies extraCandies = ok r) := by
  sorry

/-- Whenever the function returns a result r, len(r) = len(candies).
  Preconditions: n = len(candies); 2 <= n <= 100; for every i with 0 <= i < n, 1 <= candies[i] <= 100; 1 <= extraCandies <= 50. -/
theorem spec_3 (candies : Slice Std.I64) (extraCandies : Std.I64) (n : Nat)
    (hn : n = candies.val.length) (hn_ge : 2 ≤ n) (hn_le : n ≤ 100)
    (hcandies : ∀ (i : Nat) (hi : i < n),
      1 ≤ (candies.val[i]).val ∧ (candies.val[i]).val ≤ 100)
    (hextra : 1 ≤ extraCandies.val ∧ extraCandies.val ≤ 50) :
    ∀ r, Aegis.KidsWithCandies.kids_with_candies candies extraCandies = ok r →
      r.val.length = candies.val.length := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (candies : Slice Std.I64) (extraCandies : Std.I64) (n : Nat)
    (hn : n = candies.val.length) (hn_ge : 2 ≤ n) (hn_le : n ≤ 100)
    (hcandies : ∀ (i : Nat) (hi : i < n),
      1 ≤ (candies.val[i]).val ∧ (candies.val[i]).val ≤ 100)
    (hextra : 1 ≤ extraCandies.val ∧ extraCandies.val ≤ 50), ∀ r, Aegis.KidsWithCandies.kids_with_candies candies extraCandies = ok r →
      r.val.length = candies.val.length) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < n, r[i] is true if and only if candies[i] >= M - extraCandies.
  Preconditions: n = len(candies); 2 <= n <= 100; for every i with 0 <= i < n, 1 <= candies[i] <= 100; 1 <= extraCandies <= 50; M = max of candies[0..n-1]. -/
theorem spec_4 (candies : Slice Std.I64) (extraCandies : Std.I64) (n : Nat) (M : Int)
    (hn : n = candies.val.length) (hn_ge : 2 ≤ n) (hn_le : n ≤ 100)
    (hcandies : ∀ (i : Nat) (hi : i < n),
      1 ≤ (candies.val[i]).val ∧ (candies.val[i]).val ≤ 100)
    (hextra : 1 ≤ extraCandies.val ∧ extraCandies.val ≤ 50)
    (hM : IsMax (vals candies) M) :
    ∀ r, Aegis.KidsWithCandies.kids_with_candies candies extraCandies = ok r →
      ∀ (i : Nat) (hi : i < n),
        (r.val[i]? = some true ↔ (candies.val[i]).val ≥ M - extraCandies.val) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (candies : Slice Std.I64) (extraCandies : Std.I64) (n : Nat) (M : Int)
    (hn : n = candies.val.length) (hn_ge : 2 ≤ n) (hn_le : n ≤ 100)
    (hcandies : ∀ (i : Nat) (hi : i < n),
      1 ≤ (candies.val[i]).val ∧ (candies.val[i]).val ≤ 100)
    (hextra : 1 ≤ extraCandies.val ∧ extraCandies.val ≤ 50)
    (hM : IsMax (vals candies) M), ∀ r, Aegis.KidsWithCandies.kids_with_candies candies extraCandies = ok r →
      ∀ (i : Nat) (hi : i < n),
        (r.val[i]? = some true ↔ (candies.val[i]).val ≥ M - extraCandies.val)) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < n, if candies[i] = M then r[i] is true.
  Preconditions: n = len(candies); 2 <= n <= 100; for every i with 0 <= i < n, 1 <= candies[i] <= 100; 1 <= extraCandies <= 50; M = max of candies[0..n-1]. -/
theorem spec_5 (candies : Slice Std.I64) (extraCandies : Std.I64) (n : Nat) (M : Int)
    (hn : n = candies.val.length) (hn_ge : 2 ≤ n) (hn_le : n ≤ 100)
    (hcandies : ∀ (i : Nat) (hi : i < n),
      1 ≤ (candies.val[i]).val ∧ (candies.val[i]).val ≤ 100)
    (hextra : 1 ≤ extraCandies.val ∧ extraCandies.val ≤ 50)
    (hM : IsMax (vals candies) M) :
    ∀ r, Aegis.KidsWithCandies.kids_with_candies candies extraCandies = ok r →
      ∀ (i : Nat) (hi : i < n), (candies.val[i]).val = M → r.val[i]? = some true := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (candies : Slice Std.I64) (extraCandies : Std.I64) (n : Nat) (M : Int)
    (hn : n = candies.val.length) (hn_ge : 2 ≤ n) (hn_le : n ≤ 100)
    (hcandies : ∀ (i : Nat) (hi : i < n),
      1 ≤ (candies.val[i]).val ∧ (candies.val[i]).val ≤ 100)
    (hextra : 1 ≤ extraCandies.val ∧ extraCandies.val ≤ 50)
    (hM : IsMax (vals candies) M), ∀ r, Aegis.KidsWithCandies.kids_with_candies candies extraCandies = ok r →
      ∀ (i : Nat) (hi : i < n), (candies.val[i]).val = M → r.val[i]? = some true) := by
  sorry

/-- Whenever the function returns a result r, there exists at least one index i with 0 <= i < n such that r[i] is true.
  Preconditions: n = len(candies); 2 <= n <= 100; for every i with 0 <= i < n, 1 <= candies[i] <= 100; 1 <= extraCandies <= 50. -/
theorem spec_6 (candies : Slice Std.I64) (extraCandies : Std.I64) (n : Nat)
    (hn : n = candies.val.length) (hn_ge : 2 ≤ n) (hn_le : n ≤ 100)
    (hcandies : ∀ (i : Nat) (hi : i < n),
      1 ≤ (candies.val[i]).val ∧ (candies.val[i]).val ≤ 100)
    (hextra : 1 ≤ extraCandies.val ∧ extraCandies.val ≤ 50) :
    ∀ r, Aegis.KidsWithCandies.kids_with_candies candies extraCandies = ok r →
      ∃ (i : Nat) (hi : i < n), r.val[i]? = some true := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (candies : Slice Std.I64) (extraCandies : Std.I64) (n : Nat)
    (hn : n = candies.val.length) (hn_ge : 2 ≤ n) (hn_le : n ≤ 100)
    (hcandies : ∀ (i : Nat) (hi : i < n),
      1 ≤ (candies.val[i]).val ∧ (candies.val[i]).val ≤ 100)
    (hextra : 1 ≤ extraCandies.val ∧ extraCandies.val ≤ 50), ∀ r, Aegis.KidsWithCandies.kids_with_candies candies extraCandies = ok r →
      ∃ (i : Nat) (hi : i < n), r.val[i]? = some true) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < n, if r[i] is true then candies[i] + extraCandies >= candies[j] for every j with 0 <= j < n.
  Preconditions: n = len(candies); 2 <= n <= 100; for every i with 0 <= i < n, 1 <= candies[i] <= 100; 1 <= extraCandies <= 50. -/
theorem spec_7 (candies : Slice Std.I64) (extraCandies : Std.I64) (n : Nat)
    (hn : n = candies.val.length) (hn_ge : 2 ≤ n) (hn_le : n ≤ 100)
    (hcandies : ∀ (i : Nat) (hi : i < n),
      1 ≤ (candies.val[i]).val ∧ (candies.val[i]).val ≤ 100)
    (hextra : 1 ≤ extraCandies.val ∧ extraCandies.val ≤ 50) :
    ∀ r, Aegis.KidsWithCandies.kids_with_candies candies extraCandies = ok r →
      ∀ (i : Nat) (hi : i < n), r.val[i]? = some true →
        ∀ (j : Nat) (hj : j < n),
          (candies.val[i]).val + extraCandies.val ≥ (candies.val[j]).val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (candies : Slice Std.I64) (extraCandies : Std.I64) (n : Nat)
    (hn : n = candies.val.length) (hn_ge : 2 ≤ n) (hn_le : n ≤ 100)
    (hcandies : ∀ (i : Nat) (hi : i < n),
      1 ≤ (candies.val[i]).val ∧ (candies.val[i]).val ≤ 100)
    (hextra : 1 ≤ extraCandies.val ∧ extraCandies.val ≤ 50), ∀ r, Aegis.KidsWithCandies.kids_with_candies candies extraCandies = ok r →
      ∀ (i : Nat) (hi : i < n), r.val[i]? = some true →
        ∀ (j : Nat) (hj : j < n),
          (candies.val[i]).val + extraCandies.val ≥ (candies.val[j]).val) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < n, if r[i] is false then there exists j with 0 <= j < n such that candies[j] > candies[i] + extraCandies.
  Preconditions: n = len(candies); 2 <= n <= 100; for every i with 0 <= i < n, 1 <= candies[i] <= 100; 1 <= extraCandies <= 50. -/
theorem spec_8 (candies : Slice Std.I64) (extraCandies : Std.I64) (n : Nat)
    (hn : n = candies.val.length) (hn_ge : 2 ≤ n) (hn_le : n ≤ 100)
    (hcandies : ∀ (i : Nat) (hi : i < n),
      1 ≤ (candies.val[i]).val ∧ (candies.val[i]).val ≤ 100)
    (hextra : 1 ≤ extraCandies.val ∧ extraCandies.val ≤ 50) :
    ∀ r, Aegis.KidsWithCandies.kids_with_candies candies extraCandies = ok r →
      ∀ (i : Nat) (hi : i < n), r.val[i]? = some false →
        ∃ (j : Nat) (hj : j < n),
          (candies.val[j]).val > (candies.val[i]).val + extraCandies.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (candies : Slice Std.I64) (extraCandies : Std.I64) (n : Nat)
    (hn : n = candies.val.length) (hn_ge : 2 ≤ n) (hn_le : n ≤ 100)
    (hcandies : ∀ (i : Nat) (hi : i < n),
      1 ≤ (candies.val[i]).val ∧ (candies.val[i]).val ≤ 100)
    (hextra : 1 ≤ extraCandies.val ∧ extraCandies.val ≤ 50), ∀ r, Aegis.KidsWithCandies.kids_with_candies candies extraCandies = ok r →
      ∀ (i : Nat) (hi : i < n), r.val[i]? = some false →
        ∃ (j : Nat) (hj : j < n),
          (candies.val[j]).val > (candies.val[i]).val + extraCandies.val) := by
  sorry

/-- Whenever the function returns a result r, for all i, j with 0 <= i < n and 0 <= j < n, if candies[i] <= candies[j] and r[i] is true, then r[j] is true.
  Preconditions: n = len(candies); 2 <= n <= 100; for every i with 0 <= i < n, 1 <= candies[i] <= 100; 1 <= extraCandies <= 50. -/
theorem spec_9 (candies : Slice Std.I64) (extraCandies : Std.I64) (n : Nat)
    (hn : n = candies.val.length) (hn_ge : 2 ≤ n) (hn_le : n ≤ 100)
    (hcandies : ∀ (i : Nat) (hi : i < n),
      1 ≤ (candies.val[i]).val ∧ (candies.val[i]).val ≤ 100)
    (hextra : 1 ≤ extraCandies.val ∧ extraCandies.val ≤ 50) :
    ∀ r, Aegis.KidsWithCandies.kids_with_candies candies extraCandies = ok r →
      ∀ (i : Nat) (hi : i < n) (j : Nat) (hj : j < n),
        (candies.val[i]).val ≤ (candies.val[j]).val →
          r.val[i]? = some true → r.val[j]? = some true := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (candies : Slice Std.I64) (extraCandies : Std.I64) (n : Nat)
    (hn : n = candies.val.length) (hn_ge : 2 ≤ n) (hn_le : n ≤ 100)
    (hcandies : ∀ (i : Nat) (hi : i < n),
      1 ≤ (candies.val[i]).val ∧ (candies.val[i]).val ≤ 100)
    (hextra : 1 ≤ extraCandies.val ∧ extraCandies.val ≤ 50), ∀ r, Aegis.KidsWithCandies.kids_with_candies candies extraCandies = ok r →
      ∀ (i : Nat) (hi : i < n) (j : Nat) (hj : j < n),
        (candies.val[i]).val ≤ (candies.val[j]).val →
          r.val[i]? = some true → r.val[j]? = some true) := by
  sorry

/-- Whenever the function returns a result r, for all i, j with 0 <= i < n and 0 <= j < n, if candies[i] = candies[j] then r[i] = r[j].
  Preconditions: n = len(candies); 2 <= n <= 100; for every i with 0 <= i < n, 1 <= candies[i] <= 100; 1 <= extraCandies <= 50. -/
theorem spec_10 (candies : Slice Std.I64) (extraCandies : Std.I64) (n : Nat)
    (hn : n = candies.val.length) (hn_ge : 2 ≤ n) (hn_le : n ≤ 100)
    (hcandies : ∀ (i : Nat) (hi : i < n),
      1 ≤ (candies.val[i]).val ∧ (candies.val[i]).val ≤ 100)
    (hextra : 1 ≤ extraCandies.val ∧ extraCandies.val ≤ 50) :
    ∀ r, Aegis.KidsWithCandies.kids_with_candies candies extraCandies = ok r →
      ∀ (i : Nat) (hi : i < n) (j : Nat) (hj : j < n),
        (candies.val[i]).val = (candies.val[j]).val → r.val[i]? = r.val[j]? := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (candies : Slice Std.I64) (extraCandies : Std.I64) (n : Nat)
    (hn : n = candies.val.length) (hn_ge : 2 ≤ n) (hn_le : n ≤ 100)
    (hcandies : ∀ (i : Nat) (hi : i < n),
      1 ≤ (candies.val[i]).val ∧ (candies.val[i]).val ≤ 100)
    (hextra : 1 ≤ extraCandies.val ∧ extraCandies.val ≤ 50), ∀ r, Aegis.KidsWithCandies.kids_with_candies candies extraCandies = ok r →
      ∀ (i : Nat) (hi : i < n) (j : Nat) (hj : j < n),
        (candies.val[i]).val = (candies.val[j]).val → r.val[i]? = r.val[j]?) := by
  sorry

/-- Whenever the function returns a result r, if M - m <= extraCandies then r[i] is true for every i with 0 <= i < n.
  Preconditions: n = len(candies); 2 <= n <= 100; for every i with 0 <= i < n, 1 <= candies[i] <= 100; 1 <= extraCandies <= 50; m = min of candies[0..n-1]; M = max of candies[0..n-1]. -/
theorem spec_11 (candies : Slice Std.I64) (extraCandies : Std.I64) (n : Nat) (m M : Int)
    (hn : n = candies.val.length) (hn_ge : 2 ≤ n) (hn_le : n ≤ 100)
    (hcandies : ∀ (i : Nat) (hi : i < n),
      1 ≤ (candies.val[i]).val ∧ (candies.val[i]).val ≤ 100)
    (hextra : 1 ≤ extraCandies.val ∧ extraCandies.val ≤ 50)
    (hm : IsMin (vals candies) m) (hM : IsMax (vals candies) M) :
    ∀ r, Aegis.KidsWithCandies.kids_with_candies candies extraCandies = ok r →
      M - m ≤ extraCandies.val → ∀ (i : Nat) (hi : i < n), r.val[i]? = some true := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (candies : Slice Std.I64) (extraCandies : Std.I64) (n : Nat) (m M : Int)
    (hn : n = candies.val.length) (hn_ge : 2 ≤ n) (hn_le : n ≤ 100)
    (hcandies : ∀ (i : Nat) (hi : i < n),
      1 ≤ (candies.val[i]).val ∧ (candies.val[i]).val ≤ 100)
    (hextra : 1 ≤ extraCandies.val ∧ extraCandies.val ≤ 50)
    (hm : IsMin (vals candies) m) (hM : IsMax (vals candies) M), ∀ r, Aegis.KidsWithCandies.kids_with_candies candies extraCandies = ok r →
      M - m ≤ extraCandies.val → ∀ (i : Nat) (hi : i < n), r.val[i]? = some true) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < n, r[i] is exactly the boolean value expressing whether candies[i] + extraCandies is at least the greatest element of candies.
  Preconditions: n = len(candies); 2 <= n <= 100; for every i with 0 <= i < n, 1 <= candies[i] <= 100; 1 <= extraCandies <= 50. -/
theorem spec_12 (candies : Slice Std.I64) (extraCandies : Std.I64) (n : Nat) (M : Int)
    (hn : n = candies.val.length) (hn_ge : 2 ≤ n) (hn_le : n ≤ 100)
    (hcandies : ∀ (i : Nat) (hi : i < n),
      1 ≤ (candies.val[i]).val ∧ (candies.val[i]).val ≤ 100)
    (hextra : 1 ≤ extraCandies.val ∧ extraCandies.val ≤ 50)
    (hM : IsMax (vals candies) M) :
    ∀ r, Aegis.KidsWithCandies.kids_with_candies candies extraCandies = ok r →
      ∀ (i : Nat) (hi : i < n),
        r.val[i]? = some (decide (M ≤ (candies.val[i]).val + extraCandies.val)) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (candies : Slice Std.I64) (extraCandies : Std.I64) (n : Nat) (M : Int)
    (hn : n = candies.val.length) (hn_ge : 2 ≤ n) (hn_le : n ≤ 100)
    (hcandies : ∀ (i : Nat) (hi : i < n),
      1 ≤ (candies.val[i]).val ∧ (candies.val[i]).val ≤ 100)
    (hextra : 1 ≤ extraCandies.val ∧ extraCandies.val ≤ 50)
    (hM : IsMax (vals candies) M), ∀ r, Aegis.KidsWithCandies.kids_with_candies candies extraCandies = ok r →
      ∀ (i : Nat) (hi : i < n),
        r.val[i]? = some (decide (M ≤ (candies.val[i]).val + extraCandies.val))) := by
  sorry

end AegisSpec.KidsWithCandies
