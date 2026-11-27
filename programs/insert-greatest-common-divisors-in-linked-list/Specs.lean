import Aegis.InsertGreatestCommonDivisors.Code.Funs

/-!
# Specifications of `Aegis.InsertGreatestCommonDivisors.insert_greatest_common_divisors`

LeetCode problem `insert-greatest-common-divisors-in-linked-list`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.InsertGreatestCommonDivisors

  def vals : Aegis.InsertGreatestCommonDivisors.List → List Int
    | .Nil => []
    | .Cons v next => v.val :: vals next

  def gcdInt (x y : Int) : Int := (Int.gcd x y : Int)

  /-- The function returns a result r. Let vals(r)=[b_0,...,b_{m-1}]. Then m=2n-1; for every i with 0<=i<n, b_{2i}=a_i; and for every i with 0<=i<n-1, b_{2i+1}=gcd(a_i,a_{i+1}).
    Preconditions: Let vals(L) be the sequence of values of the nodes of L from head to tail. The input head satisfies vals(head)=[a_0,...,a_{n-1}] with n>=1, n<=5000, and 1<=a_i<=1000 for every 0<=i<n. Write gcd(x,y) for the greatest positive integer dividing both x and y. -/
  theorem spec_1
      (head : Aegis.InsertGreatestCommonDivisors.List)
      (n : Nat) (avals : List Int)
      (hvals : vals head = avals) (hlen : avals.length = n)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 5000)
      (hrange : ∀ a ∈ avals, 1 ≤ a ∧ a ≤ 1000) :
      ∃ r, Aegis.InsertGreatestCommonDivisors.insert_greatest_common_divisors head = ok r ∧
        (vals r).length = 2 * n - 1 ∧
        (∀ (i : Nat), i < n → ∀ a : Int, avals[i]? = some a → (vals r)[2 * i]? = some a) ∧
        (∀ (i : Nat), i + 1 < n → ∀ a b : Int, avals[i]? = some a → avals[i + 1]? = some b →
          (vals r)[2 * i + 1]? = some (gcdInt a b)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (head : Aegis.InsertGreatestCommonDivisors.List)
        (n : Nat) (avals : List Int)
        (hvals : vals head = avals) (hlen : avals.length = n)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 5000)
        (hrange : ∀ a ∈ avals, 1 ≤ a ∧ a ≤ 1000), ∃ r, Aegis.InsertGreatestCommonDivisors.insert_greatest_common_divisors head = ok r ∧
          (vals r).length = 2 * n - 1 ∧
          (∀ (i : Nat), i < n → ∀ a : Int, avals[i]? = some a → (vals r)[2 * i]? = some a) ∧
          (∀ (i : Nat), i + 1 < n → ∀ a b : Int, avals[i]? = some a → avals[i + 1]? = some b →
            (vals r)[2 * i + 1]? = some (gcdInt a b))) := by
    sorry

  /-- The function returns a result r (it does not fail) for every input satisfying the preconditions.
    Preconditions: Let vals(L) be the sequence of values of the nodes of L from head to tail. The input head satisfies vals(head)=[a_0,...,a_{n-1}] with n>=1, n<=5000, and 1<=a_i<=1000 for every 0<=i<n. -/
  theorem spec_2
      (head : Aegis.InsertGreatestCommonDivisors.List)
      (n : Nat) (avals : List Int)
      (hvals : vals head = avals) (hlen : avals.length = n)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 5000)
      (hrange : ∀ a ∈ avals, 1 ≤ a ∧ a ≤ 1000) :
      ∃ r, Aegis.InsertGreatestCommonDivisors.insert_greatest_common_divisors head = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (head : Aegis.InsertGreatestCommonDivisors.List)
        (n : Nat) (avals : List Int)
        (hvals : vals head = avals) (hlen : avals.length = n)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 5000)
        (hrange : ∀ a ∈ avals, 1 ≤ a ∧ a ≤ 1000), ∃ r, Aegis.InsertGreatestCommonDivisors.insert_greatest_common_divisors head = ok r) := by
    sorry

  /-- Whenever the function returns a result r, the number of nodes in r is 2n-1, where n is the number of nodes in head.
    Preconditions: Let vals(L) be the sequence of values of the nodes of L from head to tail. The input head satisfies vals(head)=[a_0,...,a_{n-1}] with n>=1, n<=5000, and 1<=a_i<=1000 for every 0<=i<n. -/
  theorem spec_3
      (head : Aegis.InsertGreatestCommonDivisors.List)
      (n : Nat) (avals : List Int)
      (hvals : vals head = avals) (hlen : avals.length = n)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 5000)
      (hrange : ∀ a ∈ avals, 1 ≤ a ∧ a ≤ 1000) :
      ∀ r, Aegis.InsertGreatestCommonDivisors.insert_greatest_common_divisors head = ok r →
        (vals r).length = 2 * n - 1 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (head : Aegis.InsertGreatestCommonDivisors.List)
        (n : Nat) (avals : List Int)
        (hvals : vals head = avals) (hlen : avals.length = n)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 5000)
        (hrange : ∀ a ∈ avals, 1 ≤ a ∧ a ≤ 1000), ∀ r, Aegis.InsertGreatestCommonDivisors.insert_greatest_common_divisors head = ok r →
          (vals r).length = 2 * n - 1) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0<=i<n, the node at 0-based position 2i of r exists and has value a_i. Thus the original nodes occur in r in the same order and with unchanged values.
    Preconditions: Let vals(L) be the sequence of values of the nodes of L from head to tail. The input head satisfies vals(head)=[a_0,...,a_{n-1}] with n>=1, n<=5000, and 1<=a_i<=1000 for every 0<=i<n. -/
  theorem spec_4
      (head : Aegis.InsertGreatestCommonDivisors.List)
      (n : Nat) (avals : List Int)
      (hvals : vals head = avals) (hlen : avals.length = n)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 5000)
      (hrange : ∀ a ∈ avals, 1 ≤ a ∧ a ≤ 1000) :
      ∀ r, Aegis.InsertGreatestCommonDivisors.insert_greatest_common_divisors head = ok r →
        ∀ (i : Nat), i < n → ∀ a : Int, avals[i]? = some a → (vals r)[2 * i]? = some a := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (head : Aegis.InsertGreatestCommonDivisors.List)
        (n : Nat) (avals : List Int)
        (hvals : vals head = avals) (hlen : avals.length = n)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 5000)
        (hrange : ∀ a ∈ avals, 1 ≤ a ∧ a ≤ 1000), ∀ r, Aegis.InsertGreatestCommonDivisors.insert_greatest_common_divisors head = ok r →
          ∀ (i : Nat), i < n → ∀ a : Int, avals[i]? = some a → (vals r)[2 * i]? = some a) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0<=i<n-1, the node at 0-based position 2i+1 of r exists and has value gcd(a_i,a_{i+1}).
    Preconditions: Let vals(L) be the sequence of values of the nodes of L from head to tail. The input head satisfies vals(head)=[a_0,...,a_{n-1}] with n>=1, n<=5000, and 1<=a_i<=1000 for every 0<=i<n. Write gcd(x,y) for the greatest positive integer dividing both x and y. -/
  theorem spec_5
      (head : Aegis.InsertGreatestCommonDivisors.List)
      (n : Nat) (avals : List Int)
      (hvals : vals head = avals) (hlen : avals.length = n)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 5000)
      (hrange : ∀ a ∈ avals, 1 ≤ a ∧ a ≤ 1000) :
      ∀ r, Aegis.InsertGreatestCommonDivisors.insert_greatest_common_divisors head = ok r →
        ∀ (i : Nat), i + 1 < n → ∀ a b : Int, avals[i]? = some a → avals[i + 1]? = some b →
          (vals r)[2 * i + 1]? = some (gcdInt a b) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (head : Aegis.InsertGreatestCommonDivisors.List)
        (n : Nat) (avals : List Int)
        (hvals : vals head = avals) (hlen : avals.length = n)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 5000)
        (hrange : ∀ a ∈ avals, 1 ≤ a ∧ a ≤ 1000), ∀ r, Aegis.InsertGreatestCommonDivisors.insert_greatest_common_divisors head = ok r →
          ∀ (i : Nat), i + 1 < n → ∀ a b : Int, avals[i]? = some a → avals[i + 1]? = some b →
            (vals r)[2 * i + 1]? = some (gcdInt a b)) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0<=i<n-1, the node at 0-based position 2i+1 of r exists, and its value divides both a_i and a_{i+1}.
    Preconditions: Let vals(L) be the sequence of values of the nodes of L from head to tail. The input head satisfies vals(head)=[a_0,...,a_{n-1}] with n>=1, n<=5000, and 1<=a_i<=1000 for every 0<=i<n. -/
  theorem spec_6
      (head : Aegis.InsertGreatestCommonDivisors.List)
      (n : Nat) (avals : List Int)
      (hvals : vals head = avals) (hlen : avals.length = n)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 5000)
      (hrange : ∀ a ∈ avals, 1 ≤ a ∧ a ≤ 1000) :
      ∀ r, Aegis.InsertGreatestCommonDivisors.insert_greatest_common_divisors head = ok r →
        ∀ (i : Nat), i + 1 < n → ∀ a b : Int, avals[i]? = some a → avals[i + 1]? = some b →
          ∃ v : Int, (vals r)[2 * i + 1]? = some v ∧ v ∣ a ∧ v ∣ b := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (head : Aegis.InsertGreatestCommonDivisors.List)
        (n : Nat) (avals : List Int)
        (hvals : vals head = avals) (hlen : avals.length = n)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 5000)
        (hrange : ∀ a ∈ avals, 1 ≤ a ∧ a ≤ 1000), ∀ r, Aegis.InsertGreatestCommonDivisors.insert_greatest_common_divisors head = ok r →
          ∀ (i : Nat), i + 1 < n → ∀ a b : Int, avals[i]? = some a → avals[i + 1]? = some b →
            ∃ v : Int, (vals r)[2 * i + 1]? = some v ∧ v ∣ a ∧ v ∣ b) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0<=i<n-1, the node at 0-based position 2i+1 of r exists; writing v for its value, for every positive integer d, if d divides both a_i and a_{i+1}, then d divides v.
    Preconditions: Let vals(L) be the sequence of values of the nodes of L from head to tail. The input head satisfies vals(head)=[a_0,...,a_{n-1}] with n>=1, n<=5000, and 1<=a_i<=1000 for every 0<=i<n. -/
  theorem spec_7
      (head : Aegis.InsertGreatestCommonDivisors.List)
      (n : Nat) (avals : List Int)
      (hvals : vals head = avals) (hlen : avals.length = n)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 5000)
      (hrange : ∀ a ∈ avals, 1 ≤ a ∧ a ≤ 1000) :
      ∀ r, Aegis.InsertGreatestCommonDivisors.insert_greatest_common_divisors head = ok r →
        ∀ (i : Nat), i + 1 < n → ∀ a b : Int, avals[i]? = some a → avals[i + 1]? = some b →
          ∃ v : Int, (vals r)[2 * i + 1]? = some v ∧
            ∀ d : Int, 0 < d → d ∣ a → d ∣ b → d ∣ v := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (head : Aegis.InsertGreatestCommonDivisors.List)
        (n : Nat) (avals : List Int)
        (hvals : vals head = avals) (hlen : avals.length = n)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 5000)
        (hrange : ∀ a ∈ avals, 1 ≤ a ∧ a ≤ 1000), ∀ r, Aegis.InsertGreatestCommonDivisors.insert_greatest_common_divisors head = ok r →
          ∀ (i : Nat), i + 1 < n → ∀ a b : Int, avals[i]? = some a → avals[i + 1]? = some b →
            ∃ v : Int, (vals r)[2 * i + 1]? = some v ∧
              ∀ d : Int, 0 < d → d ∣ a → d ∣ b → d ∣ v) := by
    sorry

  /-- Whenever the function returns a result r, every node value in r lies in the interval [1,1000].
    Preconditions: Let vals(L) be the sequence of values of the nodes of L from head to tail. The input head satisfies vals(head)=[a_0,...,a_{n-1}] with n>=1, n<=5000, and 1<=a_i<=1000 for every 0<=i<n. -/
  theorem spec_8
      (head : Aegis.InsertGreatestCommonDivisors.List)
      (n : Nat) (avals : List Int)
      (hvals : vals head = avals) (hlen : avals.length = n)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 5000)
      (hrange : ∀ a ∈ avals, 1 ≤ a ∧ a ≤ 1000) :
      ∀ r, Aegis.InsertGreatestCommonDivisors.insert_greatest_common_divisors head = ok r →
        ∀ v : Int, v ∈ vals r → 1 ≤ v ∧ v ≤ 1000 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (head : Aegis.InsertGreatestCommonDivisors.List)
        (n : Nat) (avals : List Int)
        (hvals : vals head = avals) (hlen : avals.length = n)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 5000)
        (hrange : ∀ a ∈ avals, 1 ≤ a ∧ a ≤ 1000), ∀ r, Aegis.InsertGreatestCommonDivisors.insert_greatest_common_divisors head = ok r →
          ∀ v : Int, v ∈ vals r → 1 ≤ v ∧ v ≤ 1000) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0<=i<n-1, the node at 0-based position 2i+1 of r exists; writing v for its value, 1 <= v <= a_i and 1 <= v <= a_{i+1} (equivalently, 1 <= v <= min(a_i,a_{i+1})).
    Preconditions: Let vals(L) be the sequence of values of the nodes of L from head to tail. The input head satisfies vals(head)=[a_0,...,a_{n-1}] with n>=1, n<=5000, and 1<=a_i<=1000 for every 0<=i<n. -/
  theorem spec_9
      (head : Aegis.InsertGreatestCommonDivisors.List)
      (n : Nat) (avals : List Int)
      (hvals : vals head = avals) (hlen : avals.length = n)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 5000)
      (hrange : ∀ a ∈ avals, 1 ≤ a ∧ a ≤ 1000) :
      ∀ r, Aegis.InsertGreatestCommonDivisors.insert_greatest_common_divisors head = ok r →
        ∀ (i : Nat), i + 1 < n → ∀ a b : Int, avals[i]? = some a → avals[i + 1]? = some b →
          ∃ v : Int, (vals r)[2 * i + 1]? = some v ∧ 1 ≤ v ∧ v ≤ a ∧ v ≤ b := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (head : Aegis.InsertGreatestCommonDivisors.List)
        (n : Nat) (avals : List Int)
        (hvals : vals head = avals) (hlen : avals.length = n)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 5000)
        (hrange : ∀ a ∈ avals, 1 ≤ a ∧ a ≤ 1000), ∀ r, Aegis.InsertGreatestCommonDivisors.insert_greatest_common_divisors head = ok r →
          ∀ (i : Nat), i + 1 < n → ∀ a b : Int, avals[i]? = some a → avals[i + 1]? = some b →
            ∃ v : Int, (vals r)[2 * i + 1]? = some v ∧ 1 ≤ v ∧ v ≤ a ∧ v ≤ b) := by
    sorry

  end AegisSpec.InsertGreatestCommonDivisors
