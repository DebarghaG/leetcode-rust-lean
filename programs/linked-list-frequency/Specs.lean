import Aegis.FrequenciesOfElements.Code.Funs

/-!
# Specifications of `Aegis.FrequenciesOfElements.frequencies_of_elements`

LeetCode problem `linked-list-frequency`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.FrequenciesOfElements

abbrev RustList := Aegis.FrequenciesOfElements.List

open Aegis.FrequenciesOfElements (frequencies_of_elements)

def vals : RustList → List ℤ
  | .Nil => []
  | .Cons v rest => v.val :: vals rest

def countOcc (xs : List ℤ) (v : ℤ) : ℕ := xs.countP fun x => decide (x = v)

def distinctVals : List ℤ → List ℤ
  | [] => []
  | x :: xs => if x ∈ distinctVals xs then distinctVals xs else x :: distinctVals xs

def listMax : List ℤ → ℤ
  | [] => 0
  | x :: rest => rest.foldr max x

def listMin : List ℤ → ℤ
  | [] => 0
  | x :: rest => rest.foldr min x

/-- Whenever the function returns a result r, let ys be the sequence of values of the nodes of r. Then there exists a sequence (v_0, v_1, ..., v_{len(ys)-1}) that is a permutation of the elements of distinct(xs) such that for every i with 0 <= i < len(ys), ys[i] = count(v_i, xs).
  Preconditions: Let xs be the sequence of values of the nodes of the input list head, in order from head to tail. Assume len(xs) >= 1, len(xs) <= 100000, and for every i with 0 <= i < len(xs), 1 <= xs[i] <= 100000. Let distinct(xs) be the set of values appearing in xs, and for v in distinct(xs) let count(v, xs) be the number of indices i with 0 <= i < len(xs) and xs[i] = v. -/
theorem spec_1 (head : RustList)
    (hlen_ge : 1 ≤ (vals head).length) (hlen_le : (vals head).length ≤ 100000)
    (hval : ∀ v ∈ vals head, 1 ≤ v ∧ v ≤ 100000) :
    ∀ r, frequencies_of_elements head = ok r →
      ∃ vs : List ℤ, vs.Perm (distinctVals (vals head)) ∧
        vals r = vs.map (fun v => (countOcc (vals head) v : ℤ)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (head : RustList)
    (hlen_ge : 1 ≤ (vals head).length) (hlen_le : (vals head).length ≤ 100000)
    (hval : ∀ v ∈ vals head, 1 ≤ v ∧ v ≤ 100000), ∀ r, frequencies_of_elements head = ok r →
      ∃ vs : List ℤ, vs.Perm (distinctVals (vals head)) ∧
        vals r = vs.map (fun v => (countOcc (vals head) v : ℤ))) := by
  sorry

/-- Whenever the function returns a result r, let ys be the sequence of values of the nodes of r. Then len(ys) = |distinct(xs)|, where distinct(xs) is the set of values appearing in xs.
  Preconditions: Let xs be the sequence of values of the nodes of the input list head, in order from head to tail. Assume len(xs) >= 1, len(xs) <= 100000, and for every i with 0 <= i < len(xs), 1 <= xs[i] <= 100000. Let distinct(xs) be the set of values appearing in xs, and for v in distinct(xs) let count(v, xs) be the number of indices i with 0 <= i < len(xs) and xs[i] = v. -/
theorem spec_2 (head : RustList)
    (hlen_ge : 1 ≤ (vals head).length) (hlen_le : (vals head).length ≤ 100000)
    (hval : ∀ v ∈ vals head, 1 ≤ v ∧ v ≤ 100000) :
    ∀ r, frequencies_of_elements head = ok r →
      (vals r).length = (distinctVals (vals head)).length := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (head : RustList)
    (hlen_ge : 1 ≤ (vals head).length) (hlen_le : (vals head).length ≤ 100000)
    (hval : ∀ v ∈ vals head, 1 ≤ v ∧ v ≤ 100000), ∀ r, frequencies_of_elements head = ok r →
      (vals r).length = (distinctVals (vals head)).length) := by
  sorry

/-- Whenever the function returns a result r, let ys be the sequence of values of the nodes of r. Then sum(ys) = len(xs), where sum(ys) is the sum of all values in ys.
  Preconditions: Let xs be the sequence of values of the nodes of the input list head, in order from head to tail. Assume len(xs) >= 1, len(xs) <= 100000, and for every i with 0 <= i < len(xs), 1 <= xs[i] <= 100000. Let distinct(xs) be the set of values appearing in xs, and for v in distinct(xs) let count(v, xs) be the number of indices i with 0 <= i < len(xs) and xs[i] = v. -/
theorem spec_3 (head : RustList)
    (hlen_ge : 1 ≤ (vals head).length) (hlen_le : (vals head).length ≤ 100000)
    (hval : ∀ v ∈ vals head, 1 ≤ v ∧ v ≤ 100000) :
    ∀ r, frequencies_of_elements head = ok r →
      (vals r).sum = ((vals head).length : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (head : RustList)
    (hlen_ge : 1 ≤ (vals head).length) (hlen_le : (vals head).length ≤ 100000)
    (hval : ∀ v ∈ vals head, 1 ≤ v ∧ v ≤ 100000), ∀ r, frequencies_of_elements head = ok r →
      (vals r).sum = ((vals head).length : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, let ys be the sequence of values of the nodes of r. Then for every i with 0 <= i < len(ys), 1 <= ys[i] <= len(xs).
  Preconditions: Let xs be the sequence of values of the nodes of the input list head, in order from head to tail. Assume len(xs) >= 1, len(xs) <= 100000, and for every i with 0 <= i < len(xs), 1 <= xs[i] <= 100000. Let distinct(xs) be the set of values appearing in xs, and for v in distinct(xs) let count(v, xs) be the number of indices i with 0 <= i < len(xs) and xs[i] = v. -/
theorem spec_4 (head : RustList)
    (hlen_ge : 1 ≤ (vals head).length) (hlen_le : (vals head).length ≤ 100000)
    (hval : ∀ v ∈ vals head, 1 ≤ v ∧ v ≤ 100000) :
    ∀ r, frequencies_of_elements head = ok r →
      ∀ y ∈ vals r, 1 ≤ y ∧ y ≤ ((vals head).length : ℤ) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (head : RustList)
    (hlen_ge : 1 ≤ (vals head).length) (hlen_le : (vals head).length ≤ 100000)
    (hval : ∀ v ∈ vals head, 1 ≤ v ∧ v ≤ 100000), ∀ r, frequencies_of_elements head = ok r →
      ∀ y ∈ vals r, 1 ≤ y ∧ y ≤ ((vals head).length : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, let ys be the sequence of values of the nodes of r. Then for every integer m, m is an element of ys if and only if there exists a value v in distinct(xs) such that count(v, xs) = m, where count(v, xs) is the number of occurrences of v in xs.
  Preconditions: Let xs be the sequence of values of the nodes of the input list head, in order from head to tail. Assume len(xs) >= 1, len(xs) <= 100000, and for every i with 0 <= i < len(xs), 1 <= xs[i] <= 100000. Let distinct(xs) be the set of values appearing in xs, and for v in distinct(xs) let count(v, xs) be the number of indices i with 0 <= i < len(xs) and xs[i] = v. -/
theorem spec_5 (head : RustList)
    (hlen_ge : 1 ≤ (vals head).length) (hlen_le : (vals head).length ≤ 100000)
    (hval : ∀ v ∈ vals head, 1 ≤ v ∧ v ≤ 100000) :
    ∀ r, frequencies_of_elements head = ok r →
      ∀ m : ℤ, m ∈ vals r ↔
        ∃ v ∈ distinctVals (vals head), (countOcc (vals head) v : ℤ) = m := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (head : RustList)
    (hlen_ge : 1 ≤ (vals head).length) (hlen_le : (vals head).length ≤ 100000)
    (hval : ∀ v ∈ vals head, 1 ≤ v ∧ v ≤ 100000), ∀ r, frequencies_of_elements head = ok r →
      ∀ m : ℤ, m ∈ vals r ↔
        ∃ v ∈ distinctVals (vals head), (countOcc (vals head) v : ℤ) = m) := by
  sorry

/-- Whenever the function returns a result r, let ys be the sequence of values of the nodes of r. Then for every i with 0 <= i < len(ys), ys[i] = 1.
  Preconditions: Let xs be the sequence of values of the nodes of the input list head, in order from head to tail. Assume len(xs) >= 1, len(xs) <= 100000, and for every i with 0 <= i < len(xs), 1 <= xs[i] <= 100000. Let distinct(xs) be the set of values appearing in xs. Assume the values in xs are all distinct, i.e., |distinct(xs)| = len(xs). -/
theorem spec_6 (head : RustList)
    (hlen_ge : 1 ≤ (vals head).length) (hlen_le : (vals head).length ≤ 100000)
    (hval : ∀ v ∈ vals head, 1 ≤ v ∧ v ≤ 100000)
    (hdistinct : (distinctVals (vals head)).length = (vals head).length) :
    ∀ r, frequencies_of_elements head = ok r →
      ∀ y ∈ vals r, y = 1 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (head : RustList)
    (hlen_ge : 1 ≤ (vals head).length) (hlen_le : (vals head).length ≤ 100000)
    (hval : ∀ v ∈ vals head, 1 ≤ v ∧ v ≤ 100000)
    (hdistinct : (distinctVals (vals head)).length = (vals head).length), ∀ r, frequencies_of_elements head = ok r →
      ∀ y ∈ vals r, y = 1) := by
  sorry

/-- Whenever the function returns a result r, let ys be the sequence of values of the nodes of r. Then len(ys) = 1 and ys[0] = len(xs).
  Preconditions: Let xs be the sequence of values of the nodes of the input list head, in order from head to tail. Assume len(xs) >= 1, len(xs) <= 100000, and for every i with 0 <= i < len(xs), 1 <= xs[i] <= 100000. Let distinct(xs) be the set of values appearing in xs. Assume all values in xs are equal, i.e., |distinct(xs)| = 1. -/
theorem spec_7 (head : RustList)
    (hlen_ge : 1 ≤ (vals head).length) (hlen_le : (vals head).length ≤ 100000)
    (hval : ∀ v ∈ vals head, 1 ≤ v ∧ v ≤ 100000)
    (hone : (distinctVals (vals head)).length = 1) :
    ∀ r, frequencies_of_elements head = ok r →
      (vals r).length = 1 ∧ vals r = [((vals head).length : ℤ)] := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (head : RustList)
    (hlen_ge : 1 ≤ (vals head).length) (hlen_le : (vals head).length ≤ 100000)
    (hval : ∀ v ∈ vals head, 1 ≤ v ∧ v ≤ 100000)
    (hone : (distinctVals (vals head)).length = 1), ∀ r, frequencies_of_elements head = ok r →
      (vals r).length = 1 ∧ vals r = [((vals head).length : ℤ)]) := by
  sorry

/-- Whenever the function returns a result r, let ys be the sequence of values of the nodes of r. Then max(ys) = max_{v in distinct(xs)} count(v, xs), where max(ys) is the maximum value in ys.
  Preconditions: Let xs be the sequence of values of the nodes of the input list head, in order from head to tail. Assume len(xs) >= 1, len(xs) <= 100000, and for every i with 0 <= i < len(xs), 1 <= xs[i] <= 100000. Let distinct(xs) be the set of values appearing in xs, and for v in distinct(xs) let count(v, xs) be the number of indices i with 0 <= i < len(xs) and xs[i] = v. -/
theorem spec_8 (head : RustList)
    (hlen_ge : 1 ≤ (vals head).length) (hlen_le : (vals head).length ≤ 100000)
    (hval : ∀ v ∈ vals head, 1 ≤ v ∧ v ≤ 100000) :
    ∀ r, frequencies_of_elements head = ok r →
      listMax (vals r) =
        listMax ((distinctVals (vals head)).map
          (fun v => (countOcc (vals head) v : ℤ))) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (head : RustList)
    (hlen_ge : 1 ≤ (vals head).length) (hlen_le : (vals head).length ≤ 100000)
    (hval : ∀ v ∈ vals head, 1 ≤ v ∧ v ≤ 100000), ∀ r, frequencies_of_elements head = ok r →
      listMax (vals r) =
        listMax ((distinctVals (vals head)).map
          (fun v => (countOcc (vals head) v : ℤ)))) := by
  sorry

/-- Whenever the function returns a result r, let ys be the sequence of values of the nodes of r. Then min(ys) = min_{v in distinct(xs)} count(v, xs), where min(ys) is the minimum value in ys.
  Preconditions: Let xs be the sequence of values of the nodes of the input list head, in order from head to tail. Assume len(xs) >= 1, len(xs) <= 100000, and for every i with 0 <= i < len(xs), 1 <= xs[i] <= 100000. Let distinct(xs) be the set of values appearing in xs, and for v in distinct(xs) let count(v, xs) be the number of indices i with 0 <= i < len(xs) and xs[i] = v. -/
theorem spec_9 (head : RustList)
    (hlen_ge : 1 ≤ (vals head).length) (hlen_le : (vals head).length ≤ 100000)
    (hval : ∀ v ∈ vals head, 1 ≤ v ∧ v ≤ 100000) :
    ∀ r, frequencies_of_elements head = ok r →
      listMin (vals r) =
        listMin ((distinctVals (vals head)).map
          (fun v => (countOcc (vals head) v : ℤ))) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (head : RustList)
    (hlen_ge : 1 ≤ (vals head).length) (hlen_le : (vals head).length ≤ 100000)
    (hval : ∀ v ∈ vals head, 1 ≤ v ∧ v ≤ 100000), ∀ r, frequencies_of_elements head = ok r →
      listMin (vals r) =
        listMin ((distinctVals (vals head)).map
          (fun v => (countOcc (vals head) v : ℤ)))) := by
  sorry

/-- The function returns a result r (i.e., it does not panic, overflow, or otherwise fail) for every input list satisfying the preconditions.
  Preconditions: Let xs be the sequence of values of the nodes of the input list head, in order from head to tail. Assume len(xs) >= 1, len(xs) <= 100000, and for every i with 0 <= i < len(xs), 1 <= xs[i] <= 100000. -/
theorem spec_10 (head : RustList)
    (hlen_ge : 1 ≤ (vals head).length) (hlen_le : (vals head).length ≤ 100000)
    (hval : ∀ v ∈ vals head, 1 ≤ v ∧ v ≤ 100000) :
    ∃ r, frequencies_of_elements head = ok r := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (head : RustList)
    (hlen_ge : 1 ≤ (vals head).length) (hlen_le : (vals head).length ≤ 100000)
    (hval : ∀ v ∈ vals head, 1 ≤ v ∧ v ≤ 100000), ∃ r, frequencies_of_elements head = ok r) := by
  sorry

/-- Whenever the function returns a result r, let ys be the sequence of values of the nodes of r. Then len(ys) >= 1.
  Preconditions: Let xs be the sequence of values of the nodes of the input list head, in order from head to tail. Assume len(xs) >= 1, len(xs) <= 100000, and for every i with 0 <= i < len(xs), 1 <= xs[i] <= 100000. Let distinct(xs) be the set of values appearing in xs, and for v in distinct(xs) let count(v, xs) be the number of indices i with 0 <= i < len(xs) and xs[i] = v. -/
theorem spec_11 (head : RustList)
    (hlen_ge : 1 ≤ (vals head).length) (hlen_le : (vals head).length ≤ 100000)
    (hval : ∀ v ∈ vals head, 1 ≤ v ∧ v ≤ 100000) :
    ∀ r, frequencies_of_elements head = ok r → 1 ≤ (vals r).length := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (head : RustList)
    (hlen_ge : 1 ≤ (vals head).length) (hlen_le : (vals head).length ≤ 100000)
    (hval : ∀ v ∈ vals head, 1 ≤ v ∧ v ≤ 100000), ∀ r, frequencies_of_elements head = ok r → 1 ≤ (vals r).length) := by
  sorry

/-- Whenever the function returns a result r, let ys be the sequence of values of the nodes of r. Then len(ys) <= len(xs).
  Preconditions: Let xs be the sequence of values of the nodes of the input list head, in order from head to tail. Assume len(xs) >= 1, len(xs) <= 100000, and for every i with 0 <= i < len(xs), 1 <= xs[i] <= 100000. Let distinct(xs) be the set of values appearing in xs, and for v in distinct(xs) let count(v, xs) be the number of indices i with 0 <= i < len(xs) and xs[i] = v. -/
theorem spec_12 (head : RustList)
    (hlen_ge : 1 ≤ (vals head).length) (hlen_le : (vals head).length ≤ 100000)
    (hval : ∀ v ∈ vals head, 1 ≤ v ∧ v ≤ 100000) :
    ∀ r, frequencies_of_elements head = ok r →
      (vals r).length ≤ (vals head).length := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (head : RustList)
    (hlen_ge : 1 ≤ (vals head).length) (hlen_le : (vals head).length ≤ 100000)
    (hval : ∀ v ∈ vals head, 1 ≤ v ∧ v ≤ 100000), ∀ r, frequencies_of_elements head = ok r →
      (vals r).length ≤ (vals head).length) := by
  sorry

/-- Whenever the function returns results r1 for head1 and r2 for head2, let ys1 and ys2 be the sequences of values of the nodes of r1 and r2 respectively. Then ys1 and ys2 have the same multiset of values, i.e., for every integer m, the number of occurrences of m in ys1 equals the number of occurrences of m in ys2.
  Preconditions: Let xs1 and xs2 be the sequences of values of two input lists head1 and head2, each satisfying: len(xs_i) >= 1, len(xs_i) <= 100000, and for every j with 0 <= j < len(xs_i), 1 <= xs_i[j] <= 100000 (i=1,2). Assume that xs1 and xs2 have the same multiset of values, i.e., for every integer m, the number of occurrences of m in xs1 equals the number of occurrences of m in xs2. -/
theorem spec_13 (head1 head2 : RustList)
    (hlen1_ge : 1 ≤ (vals head1).length) (hlen1_le : (vals head1).length ≤ 100000)
    (hval1 : ∀ v ∈ vals head1, 1 ≤ v ∧ v ≤ 100000)
    (hlen2_ge : 1 ≤ (vals head2).length) (hlen2_le : (vals head2).length ≤ 100000)
    (hval2 : ∀ v ∈ vals head2, 1 ≤ v ∧ v ≤ 100000)
    (hsame : ∀ m : ℤ, countOcc (vals head1) m = countOcc (vals head2) m) :
    ∀ r1 r2, frequencies_of_elements head1 = ok r1 →
      frequencies_of_elements head2 = ok r2 →
      ∀ m : ℤ, countOcc (vals r1) m = countOcc (vals r2) m := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (head1 head2 : RustList)
    (hlen1_ge : 1 ≤ (vals head1).length) (hlen1_le : (vals head1).length ≤ 100000)
    (hval1 : ∀ v ∈ vals head1, 1 ≤ v ∧ v ≤ 100000)
    (hlen2_ge : 1 ≤ (vals head2).length) (hlen2_le : (vals head2).length ≤ 100000)
    (hval2 : ∀ v ∈ vals head2, 1 ≤ v ∧ v ≤ 100000)
    (hsame : ∀ m : ℤ, countOcc (vals head1) m = countOcc (vals head2) m), ∀ r1 r2, frequencies_of_elements head1 = ok r1 →
      frequencies_of_elements head2 = ok r2 →
      ∀ m : ℤ, countOcc (vals r1) m = countOcc (vals r2) m) := by
  sorry

/-- Whenever the function returns a result r, let ys be the sequence of values of the nodes of r. Then the number of indices i with 0 <= i < len(ys) and ys[i] = 1 equals the number of distinct values v in distinct(xs) such that count(v, xs) = 1.
  Preconditions: Let xs be the sequence of values of the nodes of the input list head, in order from head to tail. Assume len(xs) >= 1, len(xs) <= 100000, and for every i with 0 <= i < len(xs), 1 <= xs[i] <= 100000. Let distinct(xs) be the set of values appearing in xs, and for v in distinct(xs) let count(v, xs) be the number of indices i with 0 <= i < len(xs) and xs[i] = v. -/
theorem spec_14 (head : RustList)
    (hlen_ge : 1 ≤ (vals head).length) (hlen_le : (vals head).length ≤ 100000)
    (hval : ∀ v ∈ vals head, 1 ≤ v ∧ v ≤ 100000) :
    ∀ r, frequencies_of_elements head = ok r →
      countOcc (vals r) 1 =
        (distinctVals (vals head)).countP
          (fun v => decide (countOcc (vals head) v = 1)) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (head : RustList)
    (hlen_ge : 1 ≤ (vals head).length) (hlen_le : (vals head).length ≤ 100000)
    (hval : ∀ v ∈ vals head, 1 ≤ v ∧ v ≤ 100000), ∀ r, frequencies_of_elements head = ok r →
      countOcc (vals r) 1 =
        (distinctVals (vals head)).countP
          (fun v => decide (countOcc (vals head) v = 1))) := by
  sorry

end AegisSpec.FrequenciesOfElements
