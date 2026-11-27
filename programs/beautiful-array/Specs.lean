import Aegis.BeautifulArray.Code.Funs

/-!
# Specifications of `Aegis.BeautifulArray.beautiful_array`

LeetCode problem `beautiful-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.BeautifulArray

  def toList (r : alloc.vec.Vec Std.I64) : List ℤ := r.val.map (fun x => x.val)

  def occ (l : List ℤ) (v : ℤ) : ℕ := (l.filter (fun x => x = v)).length

  def Beautiful (l : List ℤ) : Prop :=
    ∀ (i k j : ℕ) (hik : i < k) (hkj : k < j) (hj : j < l.length),
      2 * l.get ⟨k, by omega⟩ ≠ l.get ⟨i, by omega⟩ + l.get ⟨j, by omega⟩

  def IsMin (l : List ℤ) (m : ℤ) : Prop := m ∈ l ∧ ∀ x ∈ l, m ≤ x

  def IsMax (l : List ℤ) (m : ℤ) : Prop := m ∈ l ∧ ∀ x ∈ l, x ≤ m

  /-- The function returns a result r such that: (1) len(r) = n; (2) for every integer v with 1 <= v <= n, the number of indices i with 0 <= i < len(r) and r[i] = v is exactly 1; (3) for every i, k, j with 0 <= i < k < j < len(r), 2 * r[k] != r[i] + r[j].
    Preconditions: n is a 64-bit signed integer with 1 <= n <= 1000. -/
  theorem spec_1 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000) :
      ∃ r : alloc.vec.Vec Std.I64,
        Aegis.BeautifulArray.beautiful_array n = ok r ∧
          ((toList r).length : ℤ) = n.val ∧
          (∀ v : ℤ, 1 ≤ v → v ≤ n.val → occ (toList r) v = 1) ∧
          Beautiful (toList r) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000), ∃ r : alloc.vec.Vec Std.I64,
          Aegis.BeautifulArray.beautiful_array n = ok r ∧
            ((toList r).length : ℤ) = n.val ∧
            (∀ v : ℤ, 1 ≤ v → v ≤ n.val → occ (toList r) v = 1) ∧
            Beautiful (toList r)) := by
    sorry

  /-- Whenever the function returns a result r, len(r) = n.
    Preconditions: n is a 64-bit signed integer with 1 <= n <= 1000. -/
  theorem spec_2 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.BeautifulArray.beautiful_array n = ok r → ((toList r).length : ℤ) = n.val := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.BeautifulArray.beautiful_array n = ok r → ((toList r).length : ℤ) = n.val) := by
    sorry

  /-- Whenever the function returns a result r, for every index i with 0 <= i < len(r), 1 <= r[i] <= n.
    Preconditions: n is a 64-bit signed integer with 1 <= n <= 1000. -/
  theorem spec_3 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.BeautifulArray.beautiful_array n = ok r →
          ∀ (i : ℕ) (hi : i < (toList r).length),
            1 ≤ (toList r).get ⟨i, hi⟩ ∧ (toList r).get ⟨i, hi⟩ ≤ n.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.BeautifulArray.beautiful_array n = ok r →
            ∀ (i : ℕ) (hi : i < (toList r).length),
              1 ≤ (toList r).get ⟨i, hi⟩ ∧ (toList r).get ⟨i, hi⟩ ≤ n.val) := by
    sorry

  /-- Whenever the function returns a result r, r is a permutation of the integers 1, 2, ..., n; formally, len(r) = n and for every integer v, the number of indices i with 0 <= i < len(r) and r[i] = v is exactly 1 if 1 <= v <= n, and is 0 otherwise. Equivalently, every element of r lies in [1, n] and each value 1, 2, ..., n occurs exactly once.
    Preconditions: n is a 64-bit signed integer with 1 <= n <= 1000. -/
  theorem spec_4 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.BeautifulArray.beautiful_array n = ok r →
          ((toList r).length : ℤ) = n.val ∧
            (∀ v : ℤ, 1 ≤ v → v ≤ n.val → occ (toList r) v = 1) ∧
            (∀ v : ℤ, ¬(1 ≤ v ∧ v ≤ n.val) → occ (toList r) v = 0) ∧
            (∀ x ∈ toList r, 1 ≤ x ∧ x ≤ n.val) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.BeautifulArray.beautiful_array n = ok r →
            ((toList r).length : ℤ) = n.val ∧
              (∀ v : ℤ, 1 ≤ v → v ≤ n.val → occ (toList r) v = 1) ∧
              (∀ v : ℤ, ¬(1 ≤ v ∧ v ≤ n.val) → occ (toList r) v = 0) ∧
              (∀ x ∈ toList r, 1 ≤ x ∧ x ≤ n.val)) := by
    sorry

  /-- Whenever the function returns a result r, for all i, j with 0 <= i < j < len(r), r[i] != r[j].
    Preconditions: n is a 64-bit signed integer with 1 <= n <= 1000. -/
  theorem spec_5 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.BeautifulArray.beautiful_array n = ok r →
          ∀ (i j : ℕ) (hij : i < j) (hj : j < (toList r).length),
            (toList r).get ⟨i, by omega⟩ ≠ (toList r).get ⟨j, hj⟩ := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.BeautifulArray.beautiful_array n = ok r →
            ∀ (i j : ℕ) (hij : i < j) (hj : j < (toList r).length),
              (toList r).get ⟨i, by omega⟩ ≠ (toList r).get ⟨j, hj⟩) := by
    sorry

  /-- Whenever the function returns a result r, for every i, k, j with 0 <= i < k < j < len(r), 2 * r[k] != r[i] + r[j].
    Preconditions: n is a 64-bit signed integer with 1 <= n <= 1000. -/
  theorem spec_6 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.BeautifulArray.beautiful_array n = ok r → Beautiful (toList r) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.BeautifulArray.beautiful_array n = ok r → Beautiful (toList r)) := by
    sorry

  /-- The function returns a result r (it does not fail).
    Preconditions: n is a 64-bit signed integer with 1 <= n <= 1000. -/
  theorem spec_7 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000) :
      ∃ r : alloc.vec.Vec Std.I64, Aegis.BeautifulArray.beautiful_array n = ok r := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000), ∃ r : alloc.vec.Vec Std.I64, Aegis.BeautifulArray.beautiful_array n = ok r) := by
    sorry

  /-- Whenever the function returns a result r, the sum of the elements of r equals n*(n+1)/2; that is, sum_{i=0}^{len(r)-1} r[i] = n*(n+1)/2.
    Preconditions: n is a 64-bit signed integer with 1 <= n <= 1000. -/
  theorem spec_8 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.BeautifulArray.beautiful_array n = ok r →
          (toList r).sum = n.val * (n.val + 1) / 2 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.BeautifulArray.beautiful_array n = ok r →
            (toList r).sum = n.val * (n.val + 1) / 2) := by
    sorry

  /-- Whenever the function returns a result r, the minimum element of r is 1 and the maximum element of r is n. (Since n >= 1, r is non-empty.)
    Preconditions: n is a 64-bit signed integer with 1 <= n <= 1000. -/
  theorem spec_9 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.BeautifulArray.beautiful_array n = ok r →
          IsMin (toList r) 1 ∧ IsMax (toList r) n.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.BeautifulArray.beautiful_array n = ok r →
            IsMin (toList r) 1 ∧ IsMax (toList r) n.val) := by
    sorry

  /-- Whenever the function returns a result r, the reversed array r' (defined by r'[i] = r[n-1-i] for 0 <= i < n) also satisfies the beautiful array condition: for every i, k, j with 0 <= i < k < j < n, 2 * r'[k] != r'[i] + r'[j].
    Preconditions: n is a 64-bit signed integer with 1 <= n <= 1000. -/
  theorem spec_10 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.BeautifulArray.beautiful_array n = ok r → Beautiful (toList r).reverse := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.BeautifulArray.beautiful_array n = ok r → Beautiful (toList r).reverse) := by
    sorry

  end AegisSpec.BeautifulArray
