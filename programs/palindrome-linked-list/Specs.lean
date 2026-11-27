import Aegis.IsPalindrome.Code.Funs

/-!
# Specifications of `Aegis.IsPalindrome.is_palindrome`

LeetCode problem `palindrome-linked-list`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.IsPalindrome

abbrev AList : Type := Aegis.IsPalindrome.List

def vals : AList → List Int
  | Aegis.IsPalindrome.List.Nil => []
  | Aegis.IsPalindrome.List.Cons x next => x.val :: vals next

def digitsInRange (l : List Int) : Prop := ∀ v ∈ l, 0 ≤ v ∧ v ≤ 9

def IsPalindromeList (l : List Int) : Prop :=
  ∀ i : Nat, i < l.length → l[i]? = l[l.length - 1 - i]?

def MismatchAt (l : List Int) (i : Nat) : Prop := l[i]? ≠ l[l.length - 1 - i]?

def innerVals (l : List Int) : List Int := (l.drop 1).dropLast

def midlessVals (l : List Int) (k : Nat) : List Int := l.take k ++ l.drop (k + 1)

/-- Let vals(head) = [a_0, ..., a_{n-1}] be the sequence of node values obtained by following the list from head, so n = len(head). Whenever is_palindrome(head) returns a result r : Bool, r = true if and only if for every index i with 0 <= i < n we have a_i = a_{n-1-i} (equivalently, the sequence vals(head) equals its own reverse).
  Preconditions: head is a finite singly linked list. Let n = len(head). The input satisfies 1 <= n <= 100000, and every node value v is an i64 with 0 <= v <= 9. -/
theorem spec_1 (head : AList) (n : Nat)
    (hlen : (vals head).length = n)
    (hn_low : 1 ≤ n) (hn_high : n ≤ 100000)
    (hdigits : digitsInRange (vals head)) :
    ∀ r : Bool, Aegis.IsPalindrome.is_palindrome head = ok r →
      (r = true ↔ IsPalindromeList (vals head)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (head : AList) (n : Nat)
    (hlen : (vals head).length = n)
    (hn_low : 1 ≤ n) (hn_high : n ≤ 100000)
    (hdigits : digitsInRange (vals head)), ∀ r : Bool, Aegis.IsPalindrome.is_palindrome head = ok r →
      (r = true ↔ IsPalindromeList (vals head))) := by
  sorry

/-- For every input satisfying the preconditions, is_palindrome(head) returns a result r : Bool; it does not fail (no arithmetic overflow, out-of-bounds access, panic, or error result).
  Preconditions: head is a finite singly linked list. Let n = len(head). The input satisfies 1 <= n <= 100000, and every node value v is an i64 with 0 <= v <= 9. -/
theorem spec_2 (head : AList) (n : Nat)
    (hlen : (vals head).length = n)
    (hn_low : 1 ≤ n) (hn_high : n ≤ 100000)
    (hdigits : digitsInRange (vals head)) :
    ∃ r : Bool, Aegis.IsPalindrome.is_palindrome head = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (head : AList) (n : Nat)
    (hlen : (vals head).length = n)
    (hn_low : 1 ≤ n) (hn_high : n ≤ 100000)
    (hdigits : digitsInRange (vals head)), ∃ r : Bool, Aegis.IsPalindrome.is_palindrome head = ok r) := by
  sorry

/-- Let vals(head) = [a_0, ..., a_{n-1}] be the sequence of node values from head and n = len(head). Whenever is_palindrome(head) returns r = false, there exists an index i with 0 <= i < floor(n/2) such that a_i != a_{n-1-i}.
  Preconditions: head is a finite singly linked list. Let n = len(head). The input satisfies 1 <= n <= 100000, and every node value v is an i64 with 0 <= v <= 9. -/
theorem spec_3 (head : AList) (n : Nat)
    (hlen : (vals head).length = n)
    (hn_low : 1 ≤ n) (hn_high : n ≤ 100000)
    (hdigits : digitsInRange (vals head)) :
    ∀ r : Bool, Aegis.IsPalindrome.is_palindrome head = ok r → r = false →
      ∃ i : Nat, i < n / 2 ∧ MismatchAt (vals head) i := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (head : AList) (n : Nat)
    (hlen : (vals head).length = n)
    (hn_low : 1 ≤ n) (hn_high : n ≤ 100000)
    (hdigits : digitsInRange (vals head)), ∀ r : Bool, Aegis.IsPalindrome.is_palindrome head = ok r → r = false →
      ∃ i : Nat, i < n / 2 ∧ MismatchAt (vals head) i) := by
  sorry

/-- Whenever is_palindrome(head1) returns r1 and is_palindrome(head2) returns r2, r1 = r2.
  Preconditions: head1 and head2 are finite singly linked lists with the same odd length n = 2k+1 for some integer k with 0 <= k <= 49999 (so 1 <= n <= 100000). Every node value is an i64 with 0 <= v <= 9. For every index i with 0 <= i < n and i != k, the i-th value of head1 equals the i-th value of head2; the k-th values may differ. -/
theorem spec_4 (head1 head2 : AList) (k : Nat)
    (hk_high : k ≤ 49999)
    (hlen1 : (vals head1).length = 2 * k + 1)
    (hlen2 : (vals head2).length = 2 * k + 1)
    (hdigits1 : digitsInRange (vals head1))
    (hdigits2 : digitsInRange (vals head2))
    (hagree : ∀ i : Nat, i < 2 * k + 1 → i ≠ k →
      (vals head1)[i]? = (vals head2)[i]?) :
    ∀ r1 r2 : Bool,
      Aegis.IsPalindrome.is_palindrome head1 = ok r1 →
      Aegis.IsPalindrome.is_palindrome head2 = ok r2 → r1 = r2 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (head1 head2 : AList) (k : Nat)
    (hk_high : k ≤ 49999)
    (hlen1 : (vals head1).length = 2 * k + 1)
    (hlen2 : (vals head2).length = 2 * k + 1)
    (hdigits1 : digitsInRange (vals head1))
    (hdigits2 : digitsInRange (vals head2))
    (hagree : ∀ i : Nat, i < 2 * k + 1 → i ≠ k →
      (vals head1)[i]? = (vals head2)[i]?), ∀ r1 r2 : Bool,
      Aegis.IsPalindrome.is_palindrome head1 = ok r1 →
      Aegis.IsPalindrome.is_palindrome head2 = ok r2 → r1 = r2) := by
  sorry

/-- Whenever is_palindrome(head) returns r and is_palindrome(head_rev) returns r_rev, r = r_rev.
  Preconditions: head and head_rev are admissible finite singly linked lists of the same length n, where 1 <= n <= 100000, and every node value is an i64 with 0 <= value <= 9. For every index i with 0 <= i < n, the i-th value of head_rev equals the (n-1-i)-th value of head. -/
theorem spec_5 (head head_rev : AList) (n : Nat)
    (hn_low : 1 ≤ n) (hn_high : n ≤ 100000)
    (hlen : (vals head).length = n)
    (hlen_rev : (vals head_rev).length = n)
    (hdigits : digitsInRange (vals head))
    (hdigits_rev : digitsInRange (vals head_rev))
    (hrev : ∀ i : Nat, i < n → (vals head_rev)[i]? = (vals head)[n - 1 - i]?) :
    ∀ r r_rev : Bool,
      Aegis.IsPalindrome.is_palindrome head = ok r →
      Aegis.IsPalindrome.is_palindrome head_rev = ok r_rev → r = r_rev := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (head head_rev : AList) (n : Nat)
    (hn_low : 1 ≤ n) (hn_high : n ≤ 100000)
    (hlen : (vals head).length = n)
    (hlen_rev : (vals head_rev).length = n)
    (hdigits : digitsInRange (vals head))
    (hdigits_rev : digitsInRange (vals head_rev))
    (hrev : ∀ i : Nat, i < n → (vals head_rev)[i]? = (vals head)[n - 1 - i]?), ∀ r r_rev : Bool,
      Aegis.IsPalindrome.is_palindrome head = ok r →
      Aegis.IsPalindrome.is_palindrome head_rev = ok r_rev → r = r_rev) := by
  sorry

/-- Whenever is_palindrome(head) returns r and is_palindrome(inner) returns r_inner, r = r_inner.
  Preconditions: head is a finite singly linked list with n = len(head) and 3 <= n <= 100000. Every node value is an i64 with 0 <= v <= 9. Let vals(head) = [a_0, ..., a_{n-1}] and assume a_0 = a_{n-1}. Let inner be the list with value sequence [a_1, ..., a_{n-2}]; it is nonempty because n >= 3. -/
theorem spec_6 (head inner : AList) (n : Nat)
    (hlen : (vals head).length = n)
    (hn_low : 3 ≤ n) (hn_high : n ≤ 100000)
    (hdigits : digitsInRange (vals head))
    (hends : (vals head)[0]? = (vals head)[n - 1]?)
    (hinner : vals inner = innerVals (vals head)) :
    ∀ r r_inner : Bool,
      Aegis.IsPalindrome.is_palindrome head = ok r →
      Aegis.IsPalindrome.is_palindrome inner = ok r_inner → r = r_inner := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (head inner : AList) (n : Nat)
    (hlen : (vals head).length = n)
    (hn_low : 3 ≤ n) (hn_high : n ≤ 100000)
    (hdigits : digitsInRange (vals head))
    (hends : (vals head)[0]? = (vals head)[n - 1]?)
    (hinner : vals inner = innerVals (vals head)), ∀ r r_inner : Bool,
      Aegis.IsPalindrome.is_palindrome head = ok r →
      Aegis.IsPalindrome.is_palindrome inner = ok r_inner → r = r_inner) := by
  sorry

/-- Whenever is_palindrome(head) returns r and is_palindrome(midless) returns r_midless, r = r_midless.
  Preconditions: head is a finite singly linked list with n = len(head) = 2k+1 for some integer k with 1 <= k <= 49999 (so 3 <= n <= 100000). Every node value is an i64 with 0 <= v <= 9. Let vals(head) = [a_0, ..., a_{2k}]. Let midless be the list with value sequence [a_0, ..., a_{k-1}, a_{k+1}, ..., a_{2k}], of length 2k. -/
theorem spec_7 (head midless : AList) (k : Nat)
    (hk_low : 1 ≤ k) (hk_high : k ≤ 49999)
    (hlen : (vals head).length = 2 * k + 1)
    (hdigits : digitsInRange (vals head))
    (hmidless : vals midless = midlessVals (vals head) k) :
    ∀ r r_midless : Bool,
      Aegis.IsPalindrome.is_palindrome head = ok r →
      Aegis.IsPalindrome.is_palindrome midless = ok r_midless → r = r_midless := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (head midless : AList) (k : Nat)
    (hk_low : 1 ≤ k) (hk_high : k ≤ 49999)
    (hlen : (vals head).length = 2 * k + 1)
    (hdigits : digitsInRange (vals head))
    (hmidless : vals midless = midlessVals (vals head) k), ∀ r r_midless : Bool,
      Aegis.IsPalindrome.is_palindrome head = ok r →
      Aegis.IsPalindrome.is_palindrome midless = ok r_midless → r = r_midless) := by
  sorry

end AegisSpec.IsPalindrome
