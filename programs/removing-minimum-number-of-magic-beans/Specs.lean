import Aegis.MinimumRemoval.Code.Funs

/-!
# Specifications of `Aegis.MinimumRemoval.minimum_removal`

LeetCode problem `removing-minimum-number-of-magic-beans`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinimumRemoval

abbrev Beans : Type := Aeneas.Std.Slice Aeneas.Std.I64

def vals (beans : Beans) : List Int := beans.val.map (fun x => x.val)

theorem vals_length (beans : Beans) : (vals beans).length = beans.val.length := by
  simp [vals]

def totalOf (l : List Int) : Int := l.foldr (fun x acc => x + acc) 0

def countAtLeast (l : List Int) (m : Int) : Nat := l.countP (fun x => decide (m ≤ x))

def countEq (l : List Int) (m : Int) : Nat := l.countP (fun x => decide (x = m))

def costAt (l : List Int) (m : Int) : Int := totalOf l - (countAtLeast l m : Int) * m

def minOf (l : List Int) : Int :=
  match l with
  | [] => 0
  | x :: xs => xs.foldl (fun acc y => min acc y) x

def maxOf (l : List Int) : Int :=
  match l with
  | [] => 0
  | x :: xs => xs.foldl (fun acc y => max acc y) x

def achievableCosts (l : List Int) : Set Int :=
  { c | ∃ (m : Int) (S : Finset (Fin l.length)),
      1 ≤ m ∧ S.Nonempty ∧ (∀ i ∈ S, m ≤ l.get i) ∧
        c = totalOf l - (S.card : Int) * m }

def shapeCosts (l : List Int) : Set Int :=
  { c | ∃ j : Fin l.length, c = costAt l (l.get j) }

/-- Let n = len(beans) and T = sum_{i=0}^{n-1} beans[i]. The function returns a result r and r is the minimum, over all integers m with 1 <= m and all nonempty subsets S of {0,...,n-1} such that m <= beans[i] for every i in S, of T - |S|*m. Equivalently, r = min_{1 <= m <= max_{0<=i<n} beans[i]} (T - m * #{i | 0 <= i < n and beans[i] >= m}).
  Preconditions: len(beans) >= 1, len(beans) <= 100000, and for every i with 0 <= i < len(beans), 1 <= beans[i] <= 100000. -/
theorem spec_1 (beans : Beans)
    (hlen_pos : 1 ≤ beans.val.length)
    (hlen_le : beans.val.length ≤ 100000)
    (hbound : ∀ x ∈ beans.val, 1 ≤ x.val ∧ x.val ≤ 100000) :
    ∃ r, Aegis.MinimumRemoval.minimum_removal beans = ok r ∧
      IsLeast (achievableCosts (vals beans)) r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (beans : Beans)
    (hlen_pos : 1 ≤ beans.val.length)
    (hlen_le : beans.val.length ≤ 100000)
    (hbound : ∀ x ∈ beans.val, 1 ≤ x.val ∧ x.val ≤ 100000), ∃ r, Aegis.MinimumRemoval.minimum_removal beans = ok r ∧
      IsLeast (achievableCosts (vals beans)) r.val) := by
  sorry

/-- The function returns a result r (it does not fail by overflow, out-of-bounds access, or panic).
  Preconditions: len(beans) >= 1, len(beans) <= 100000, and for every i with 0 <= i < len(beans), 1 <= beans[i] <= 100000. -/
theorem spec_2 (beans : Beans)
    (hlen_pos : 1 ≤ beans.val.length)
    (hlen_le : beans.val.length ≤ 100000)
    (hbound : ∀ x ∈ beans.val, 1 ≤ x.val ∧ x.val ≤ 100000) :
    ∃ r, Aegis.MinimumRemoval.minimum_removal beans = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (beans : Beans)
    (hlen_pos : 1 ≤ beans.val.length)
    (hlen_le : beans.val.length ≤ 100000)
    (hbound : ∀ x ∈ beans.val, 1 ≤ x.val ∧ x.val ≤ 100000), ∃ r, Aegis.MinimumRemoval.minimum_removal beans = ok r) := by
  sorry

/-- Whenever the function returns a result r, r >= 0.
  Preconditions: len(beans) >= 1, len(beans) <= 100000, and for every i with 0 <= i < len(beans), 1 <= beans[i] <= 100000. -/
theorem spec_3 (beans : Beans)
    (hlen_pos : 1 ≤ beans.val.length)
    (hlen_le : beans.val.length ≤ 100000)
    (hbound : ∀ x ∈ beans.val, 1 ≤ x.val ∧ x.val ≤ 100000) :
    ∀ r, Aegis.MinimumRemoval.minimum_removal beans = ok r → 0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (beans : Beans)
    (hlen_pos : 1 ≤ beans.val.length)
    (hlen_le : beans.val.length ≤ 100000)
    (hbound : ∀ x ∈ beans.val, 1 ≤ x.val ∧ x.val ≤ 100000), ∀ r, Aegis.MinimumRemoval.minimum_removal beans = ok r → 0 ≤ r.val) := by
  sorry

/-- Let n = len(beans), T = sum_{i=0}^{n-1} beans[i], and mn = min_{0<=i<n} beans[i]. Whenever the function returns a result r, r <= T - mn*n.
  Preconditions: len(beans) >= 1, len(beans) <= 100000, and for every i with 0 <= i < len(beans), 1 <= beans[i] <= 100000. -/
theorem spec_4 (beans : Beans)
    (hlen_pos : 1 ≤ beans.val.length)
    (hlen_le : beans.val.length ≤ 100000)
    (hbound : ∀ x ∈ beans.val, 1 ≤ x.val ∧ x.val ≤ 100000) :
    ∀ r, Aegis.MinimumRemoval.minimum_removal beans = ok r →
      r.val ≤ totalOf (vals beans) - minOf (vals beans) * ((vals beans).length : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (beans : Beans)
    (hlen_pos : 1 ≤ beans.val.length)
    (hlen_le : beans.val.length ≤ 100000)
    (hbound : ∀ x ∈ beans.val, 1 ≤ x.val ∧ x.val ≤ 100000), ∀ r, Aegis.MinimumRemoval.minimum_removal beans = ok r →
      r.val ≤ totalOf (vals beans) - minOf (vals beans) * ((vals beans).length : Int)) := by
  sorry

/-- Let n = len(beans), T = sum_{i=0}^{n-1} beans[i], M = max_{0<=i<n} beans[i], and C = #{i | 0 <= i < n and beans[i] = M}. Whenever the function returns a result r, r <= T - M*C.
  Preconditions: len(beans) >= 1, len(beans) <= 100000, and for every i with 0 <= i < len(beans), 1 <= beans[i] <= 100000. -/
theorem spec_5 (beans : Beans)
    (hlen_pos : 1 ≤ beans.val.length)
    (hlen_le : beans.val.length ≤ 100000)
    (hbound : ∀ x ∈ beans.val, 1 ≤ x.val ∧ x.val ≤ 100000) :
    ∀ r, Aegis.MinimumRemoval.minimum_removal beans = ok r →
      r.val ≤ totalOf (vals beans) -
        maxOf (vals beans) * (countEq (vals beans) (maxOf (vals beans)) : Int) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (beans : Beans)
    (hlen_pos : 1 ≤ beans.val.length)
    (hlen_le : beans.val.length ≤ 100000)
    (hbound : ∀ x ∈ beans.val, 1 ≤ x.val ∧ x.val ≤ 100000), ∀ r, Aegis.MinimumRemoval.minimum_removal beans = ok r →
      r.val ≤ totalOf (vals beans) -
        maxOf (vals beans) * (countEq (vals beans) (maxOf (vals beans)) : Int)) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if there is an integer v such that beans[i] = v for every i with 0 <= i < len(beans).
  Preconditions: len(beans) >= 1, len(beans) <= 100000, and for every i with 0 <= i < len(beans), 1 <= beans[i] <= 100000. -/
theorem spec_6 (beans : Beans)
    (hlen_pos : 1 ≤ beans.val.length)
    (hlen_le : beans.val.length ≤ 100000)
    (hbound : ∀ x ∈ beans.val, 1 ≤ x.val ∧ x.val ≤ 100000) :
    ∀ r, Aegis.MinimumRemoval.minimum_removal beans = ok r →
      (r.val = 0 ↔ ∃ v : Int, ∀ x ∈ beans.val, x.val = v) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (beans : Beans)
    (hlen_pos : 1 ≤ beans.val.length)
    (hlen_le : beans.val.length ≤ 100000)
    (hbound : ∀ x ∈ beans.val, 1 ≤ x.val ∧ x.val ≤ 100000), ∀ r, Aegis.MinimumRemoval.minimum_removal beans = ok r →
      (r.val = 0 ↔ ∃ v : Int, ∀ x ∈ beans.val, x.val = v)) := by
  sorry

/-- If beans2 is any permutation of beans (there is a bijection pi on {0,...,len(beans)-1} such that beans2[i] = beans[pi(i)] for every i), and if minimum_removal(beans) returns r while minimum_removal(beans2) returns r2, then r = r2.
  Preconditions: len(beans) >= 1, len(beans) <= 100000, for every i with 0 <= i < len(beans), 1 <= beans[i] <= 100000; beans2 is a list of the same length satisfying the same bounds. -/
theorem spec_7 (beans beans2 : Beans)
    (hlen_pos : 1 ≤ beans.val.length)
    (hlen_le : beans.val.length ≤ 100000)
    (hbound : ∀ x ∈ beans.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hlen_pos2 : 1 ≤ beans2.val.length)
    (hlen_le2 : beans2.val.length ≤ 100000)
    (hbound2 : ∀ x ∈ beans2.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hsame_len : beans2.val.length = beans.val.length)
    (hperm : List.Perm (vals beans2) (vals beans)) :
    ∀ r r2, Aegis.MinimumRemoval.minimum_removal beans = ok r →
      Aegis.MinimumRemoval.minimum_removal beans2 = ok r2 → r.val = r2.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (beans beans2 : Beans)
    (hlen_pos : 1 ≤ beans.val.length)
    (hlen_le : beans.val.length ≤ 100000)
    (hbound : ∀ x ∈ beans.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hlen_pos2 : 1 ≤ beans2.val.length)
    (hlen_le2 : beans2.val.length ≤ 100000)
    (hbound2 : ∀ x ∈ beans2.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hsame_len : beans2.val.length = beans.val.length)
    (hperm : List.Perm (vals beans2) (vals beans)), ∀ r r2, Aegis.MinimumRemoval.minimum_removal beans = ok r →
      Aegis.MinimumRemoval.minimum_removal beans2 = ok r2 → r.val = r2.val) := by
  sorry

/-- If minimum_removal(beans) returns r and minimum_removal(beans2) returns r2, then r2 = k*r.
  Preconditions: len(beans) >= 1, len(beans) <= 100000, for every i with 0 <= i < len(beans), 1 <= beans[i] <= 100000; k is an integer with k >= 1 such that 1 <= k*beans[i] <= 100000 for every i, and beans2 is the list of the same length with beans2[i] = k*beans[i] for every i. -/
theorem spec_8 (beans beans2 : Beans) (k : Int)
    (hk : 1 ≤ k)
    (hlen_pos : 1 ≤ beans.val.length)
    (hlen_le : beans.val.length ≤ 100000)
    (hbound : ∀ x ∈ beans.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hscaled_bound : ∀ x ∈ beans.val, 1 ≤ k * x.val ∧ k * x.val ≤ 100000)
    (hsame_len : beans2.val.length = beans.val.length)
    (hscale : vals beans2 = (vals beans).map (fun v => k * v)) :
    ∀ r r2, Aegis.MinimumRemoval.minimum_removal beans = ok r →
      Aegis.MinimumRemoval.minimum_removal beans2 = ok r2 → r2.val = k * r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (beans beans2 : Beans) (k : Int)
    (hk : 1 ≤ k)
    (hlen_pos : 1 ≤ beans.val.length)
    (hlen_le : beans.val.length ≤ 100000)
    (hbound : ∀ x ∈ beans.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hscaled_bound : ∀ x ∈ beans.val, 1 ≤ k * x.val ∧ k * x.val ≤ 100000)
    (hsame_len : beans2.val.length = beans.val.length)
    (hscale : vals beans2 = (vals beans).map (fun v => k * v)), ∀ r r2, Aegis.MinimumRemoval.minimum_removal beans = ok r →
      Aegis.MinimumRemoval.minimum_removal beans2 = ok r2 → r2.val = k * r.val) := by
  sorry

/-- If minimum_removal(beans) returns r and minimum_removal(beans2) returns r2, then r2 >= r.
  Preconditions: beans satisfies len(beans) >= 1, len(beans) <= 99999, and for every i, 1 <= beans[i] <= 100000; v is an integer with 1 <= v <= 100000; beans2 is the list of length len(beans)+1 obtained by appending v to beans. -/
theorem spec_9 (beans beans2 : Beans) (v : Int)
    (hv_pos : 1 ≤ v)
    (hv_le : v ≤ 100000)
    (hlen_pos : 1 ≤ beans.val.length)
    (hlen_le : beans.val.length ≤ 99999)
    (hbound : ∀ x ∈ beans.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (happend : vals beans2 = vals beans ++ [v]) :
    ∀ r r2, Aegis.MinimumRemoval.minimum_removal beans = ok r →
      Aegis.MinimumRemoval.minimum_removal beans2 = ok r2 → r.val ≤ r2.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (beans beans2 : Beans) (v : Int)
    (hv_pos : 1 ≤ v)
    (hv_le : v ≤ 100000)
    (hlen_pos : 1 ≤ beans.val.length)
    (hlen_le : beans.val.length ≤ 99999)
    (hbound : ∀ x ∈ beans.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (happend : vals beans2 = vals beans ++ [v]), ∀ r r2, Aegis.MinimumRemoval.minimum_removal beans = ok r →
      Aegis.MinimumRemoval.minimum_removal beans2 = ok r2 → r.val ≤ r2.val) := by
  sorry

/-- If minimum_removal(beans) returns r and minimum_removal(beans2) returns r2, where beans2 is beans with one extra positive entry v appended, then r2 <= r + v.
  Preconditions: beans satisfies len(beans) >= 1, len(beans) <= 99999, and for every i, 1 <= beans[i] <= 100000; v is an integer with 1 <= v <= 100000; beans2 is the list of length len(beans)+1 obtained by appending v to beans. -/
theorem spec_10 (beans beans2 : Beans) (v : Int)
    (hv_pos : 1 ≤ v)
    (hv_le : v ≤ 100000)
    (hlen_pos : 1 ≤ beans.val.length)
    (hlen_le : beans.val.length ≤ 99999)
    (hbound : ∀ x ∈ beans.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (happend : vals beans2 = vals beans ++ [v]) :
    ∀ r r2, Aegis.MinimumRemoval.minimum_removal beans = ok r →
      Aegis.MinimumRemoval.minimum_removal beans2 = ok r2 → r2.val ≤ r.val + v := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (beans beans2 : Beans) (v : Int)
    (hv_pos : 1 ≤ v)
    (hv_le : v ≤ 100000)
    (hlen_pos : 1 ≤ beans.val.length)
    (hlen_le : beans.val.length ≤ 99999)
    (hbound : ∀ x ∈ beans.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (happend : vals beans2 = vals beans ++ [v]), ∀ r r2, Aegis.MinimumRemoval.minimum_removal beans = ok r →
      Aegis.MinimumRemoval.minimum_removal beans2 = ok r2 → r2.val ≤ r.val + v) := by
  sorry

/-- Let n = len(beans) and T = sum_{i=0}^{n-1} beans[i]. Whenever the function returns a result r, r = min_{0 <= j < n} (T - beans[j] * #{i | 0 <= i < n and beans[i] >= beans[j]}).
  Preconditions: len(beans) >= 1, len(beans) <= 100000, and for every i with 0 <= i < len(beans), 1 <= beans[i] <= 100000. -/
theorem spec_11 (beans : Beans)
    (hlen_pos : 1 ≤ beans.val.length)
    (hlen_le : beans.val.length ≤ 100000)
    (hbound : ∀ x ∈ beans.val, 1 ≤ x.val ∧ x.val ≤ 100000) :
    ∀ r, Aegis.MinimumRemoval.minimum_removal beans = ok r →
      IsLeast (shapeCosts (vals beans)) r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (beans : Beans)
    (hlen_pos : 1 ≤ beans.val.length)
    (hlen_le : beans.val.length ≤ 100000)
    (hbound : ∀ x ∈ beans.val, 1 ≤ x.val ∧ x.val ≤ 100000), ∀ r, Aegis.MinimumRemoval.minimum_removal beans = ok r →
      IsLeast (shapeCosts (vals beans)) r.val) := by
  sorry

/-- Whenever the function returns a result r, there exist an integer m with 1 <= m <= max_{0<=i<len(beans)} beans[i] and a nonempty subset S of {0,...,len(beans)-1} such that m <= beans[i] for every i in S and r = (sum_{i=0}^{len(beans)-1} beans[i]) - |S|*m.
  Preconditions: len(beans) >= 1, len(beans) <= 100000, and for every i with 0 <= i < len(beans), 1 <= beans[i] <= 100000. -/
theorem spec_12 (beans : Beans)
    (hlen_pos : 1 ≤ beans.val.length)
    (hlen_le : beans.val.length ≤ 100000)
    (hbound : ∀ x ∈ beans.val, 1 ≤ x.val ∧ x.val ≤ 100000) :
    ∀ r, Aegis.MinimumRemoval.minimum_removal beans = ok r →
      ∃ (m : Int) (S : Finset (Fin (vals beans).length)),
        1 ≤ m ∧ m ≤ maxOf (vals beans) ∧ S.Nonempty ∧
          (∀ i ∈ S, m ≤ (vals beans).get i) ∧
            r.val = totalOf (vals beans) - (S.card : Int) * m := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (beans : Beans)
    (hlen_pos : 1 ≤ beans.val.length)
    (hlen_le : beans.val.length ≤ 100000)
    (hbound : ∀ x ∈ beans.val, 1 ≤ x.val ∧ x.val ≤ 100000), ∀ r, Aegis.MinimumRemoval.minimum_removal beans = ok r →
      ∃ (m : Int) (S : Finset (Fin (vals beans).length)),
        1 ≤ m ∧ m ≤ maxOf (vals beans) ∧ S.Nonempty ∧
          (∀ i ∈ S, m ≤ (vals beans).get i) ∧
            r.val = totalOf (vals beans) - (S.card : Int) * m) := by
  sorry

end AegisSpec.MinimumRemoval
