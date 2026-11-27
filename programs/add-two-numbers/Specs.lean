import Aegis.AddTwoNumbers.Code.Funs

/-!
# Specifications of `Aegis.AddTwoNumbers.add_two_numbers`

LeetCode problem `add-two-numbers`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.AddTwoNumbers

  def digits : Aegis.AddTwoNumbers.List → List Int
    | .Nil => []
    | .Cons v next => v.val :: digits next

  def len (l : Aegis.AddTwoNumbers.List) : Nat := (digits l).length

  def digitAt (l : Aegis.AddTwoNumbers.List) (i : Nat) : Int := (digits l).getD i 0

  def val (l : Aegis.AddTwoNumbers.List) : Int :=
    (List.range (len l)).foldr (fun i acc => digitAt l i * 10 ^ i + acc) 0

  def lastDigit (l : Aegis.AddTwoNumbers.List) : Option Int := (digits l).getLast?

  def AllDigits (l : Aegis.AddTwoNumbers.List) : Prop := ∀ d ∈ digits l, 0 ≤ d ∧ d ≤ 9

  def CanonicalInput (l : Aegis.AddTwoNumbers.List) : Prop := 1 < len l → lastDigit l ≠ some 0

  /-- Let digits(l) be the sequence of node values of l from head to tail, and define val(l)=sum_{i=0}^{len(l)-1} digits(l)[i] * 10^i. Whenever add_two_numbers l1 l2 returns r, let S=val(l1)+val(l2). Then digits(r) is the canonical decimal representation of S written least-significant digit first: if S=0, digits(r)=[0]; if S>0, len(r)>=1, every digit of r is in [0,9], digits(r)[len(r)-1] != 0, and val(r)=S.
    Preconditions: l1 and l2 are non-empty finite linked lists; len(l1) and len(l2) are between 1 and 100; every node value in l1 and in l2 is an integer in [0,9]; and for each input list l, if len(l)>1 then the last node value (the most significant digit in reverse order) is nonzero. -/
  theorem spec_1 (l1 l2 : Aegis.AddTwoNumbers.List)
      (hne1 : l1 ≠ Aegis.AddTwoNumbers.List.Nil)
      (hne2 : l2 ≠ Aegis.AddTwoNumbers.List.Nil)
      (hlen1 : 1 ≤ len l1 ∧ len l1 ≤ 100)
      (hlen2 : 1 ≤ len l2 ∧ len l2 ≤ 100)
      (hdig1 : AllDigits l1) (hdig2 : AllDigits l2)
      (hcan1 : CanonicalInput l1) (hcan2 : CanonicalInput l2)
      {r : Aegis.AddTwoNumbers.List}
      (hr : Aegis.AddTwoNumbers.add_two_numbers l1 l2 = ok r) :
      (val l1 + val l2 = 0 → digits r = [0]) ∧
      (0 < val l1 + val l2 →
        1 ≤ len r ∧ AllDigits r ∧ lastDigit r ≠ some 0 ∧ val r = val l1 + val l2) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (l1 l2 : Aegis.AddTwoNumbers.List)
        (hne1 : l1 ≠ Aegis.AddTwoNumbers.List.Nil)
        (hne2 : l2 ≠ Aegis.AddTwoNumbers.List.Nil)
        (hlen1 : 1 ≤ len l1 ∧ len l1 ≤ 100)
        (hlen2 : 1 ≤ len l2 ∧ len l2 ≤ 100)
        (hdig1 : AllDigits l1) (hdig2 : AllDigits l2)
        (hcan1 : CanonicalInput l1) (hcan2 : CanonicalInput l2)
        {r : Aegis.AddTwoNumbers.List}
        (hr : Aegis.AddTwoNumbers.add_two_numbers l1 l2 = ok r), (val l1 + val l2 = 0 → digits r = [0]) ∧
        (0 < val l1 + val l2 →
          1 ≤ len r ∧ AllDigits r ∧ lastDigit r ≠ some 0 ∧ val r = val l1 + val l2)) := by
    sorry

  /-- For every l1 and l2 satisfying the preconditions, add_two_numbers l1 l2 returns a result r; it does not fail by arithmetic overflow, out-of-bounds access, or panic.
    Preconditions: l1 and l2 are non-empty finite linked lists; len(l1) and len(l2) are between 1 and 100; every node value in l1 and in l2 is an integer in [0,9]; and for each input list l, if len(l)>1 then the last node value (the most significant digit in reverse order) is nonzero. -/
  theorem spec_2 (l1 l2 : Aegis.AddTwoNumbers.List)
      (hne1 : l1 ≠ Aegis.AddTwoNumbers.List.Nil)
      (hne2 : l2 ≠ Aegis.AddTwoNumbers.List.Nil)
      (hlen1 : 1 ≤ len l1 ∧ len l1 ≤ 100)
      (hlen2 : 1 ≤ len l2 ∧ len l2 ≤ 100)
      (hdig1 : AllDigits l1) (hdig2 : AllDigits l2)
      (hcan1 : CanonicalInput l1) (hcan2 : CanonicalInput l2) :
      ∃ r : Aegis.AddTwoNumbers.List, Aegis.AddTwoNumbers.add_two_numbers l1 l2 = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (l1 l2 : Aegis.AddTwoNumbers.List)
        (hne1 : l1 ≠ Aegis.AddTwoNumbers.List.Nil)
        (hne2 : l2 ≠ Aegis.AddTwoNumbers.List.Nil)
        (hlen1 : 1 ≤ len l1 ∧ len l1 ≤ 100)
        (hlen2 : 1 ≤ len l2 ∧ len l2 ≤ 100)
        (hdig1 : AllDigits l1) (hdig2 : AllDigits l2)
        (hcan1 : CanonicalInput l1) (hcan2 : CanonicalInput l2), ∃ r : Aegis.AddTwoNumbers.List, Aegis.AddTwoNumbers.add_two_numbers l1 l2 = ok r) := by
    sorry

  /-- Whenever add_two_numbers l1 l2 returns r, let m=max(len(l1),len(l2)). Then m <= len(r) <= m+1.
    Preconditions: l1 and l2 are non-empty finite linked lists; len(l1) and len(l2) are between 1 and 100; every node value in l1 and in l2 is an integer in [0,9]; and for each input list l, if len(l)>1 then the last node value (the most significant digit in reverse order) is nonzero. -/
  theorem spec_3 (l1 l2 : Aegis.AddTwoNumbers.List)
      (hne1 : l1 ≠ Aegis.AddTwoNumbers.List.Nil)
      (hne2 : l2 ≠ Aegis.AddTwoNumbers.List.Nil)
      (hlen1 : 1 ≤ len l1 ∧ len l1 ≤ 100)
      (hlen2 : 1 ≤ len l2 ∧ len l2 ≤ 100)
      (hdig1 : AllDigits l1) (hdig2 : AllDigits l2)
      (hcan1 : CanonicalInput l1) (hcan2 : CanonicalInput l2)
      {r : Aegis.AddTwoNumbers.List}
      (hr : Aegis.AddTwoNumbers.add_two_numbers l1 l2 = ok r) :
      max (len l1) (len l2) ≤ len r ∧ len r ≤ max (len l1) (len l2) + 1 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (l1 l2 : Aegis.AddTwoNumbers.List)
        (hne1 : l1 ≠ Aegis.AddTwoNumbers.List.Nil)
        (hne2 : l2 ≠ Aegis.AddTwoNumbers.List.Nil)
        (hlen1 : 1 ≤ len l1 ∧ len l1 ≤ 100)
        (hlen2 : 1 ≤ len l2 ∧ len l2 ≤ 100)
        (hdig1 : AllDigits l1) (hdig2 : AllDigits l2)
        (hcan1 : CanonicalInput l1) (hcan2 : CanonicalInput l2)
        {r : Aegis.AddTwoNumbers.List}
        (hr : Aegis.AddTwoNumbers.add_two_numbers l1 l2 = ok r), max (len l1) (len l2) ≤ len r ∧ len r ≤ max (len l1) (len l2) + 1) := by
    sorry

  /-- Whenever add_two_numbers l1 l2 returns r, let m=max(len(l1),len(l2)) and S=val(l1)+val(l2). Then len(r)=m+1 if S >= 10^m, and len(r)=m if S < 10^m.
    Preconditions: l1 and l2 are non-empty finite linked lists; len(l1) and len(l2) are between 1 and 100; every node value in l1 and in l2 is an integer in [0,9]; and for each input list l, if len(l)>1 then the last node value (the most significant digit in reverse order) is nonzero. -/
  theorem spec_4 (l1 l2 : Aegis.AddTwoNumbers.List)
      (hne1 : l1 ≠ Aegis.AddTwoNumbers.List.Nil)
      (hne2 : l2 ≠ Aegis.AddTwoNumbers.List.Nil)
      (hlen1 : 1 ≤ len l1 ∧ len l1 ≤ 100)
      (hlen2 : 1 ≤ len l2 ∧ len l2 ≤ 100)
      (hdig1 : AllDigits l1) (hdig2 : AllDigits l2)
      (hcan1 : CanonicalInput l1) (hcan2 : CanonicalInput l2)
      {r : Aegis.AddTwoNumbers.List}
      (hr : Aegis.AddTwoNumbers.add_two_numbers l1 l2 = ok r) :
      ((10 : Int) ^ max (len l1) (len l2) ≤ val l1 + val l2 →
          len r = max (len l1) (len l2) + 1) ∧
      (val l1 + val l2 < (10 : Int) ^ max (len l1) (len l2) →
          len r = max (len l1) (len l2)) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (l1 l2 : Aegis.AddTwoNumbers.List)
        (hne1 : l1 ≠ Aegis.AddTwoNumbers.List.Nil)
        (hne2 : l2 ≠ Aegis.AddTwoNumbers.List.Nil)
        (hlen1 : 1 ≤ len l1 ∧ len l1 ≤ 100)
        (hlen2 : 1 ≤ len l2 ∧ len l2 ≤ 100)
        (hdig1 : AllDigits l1) (hdig2 : AllDigits l2)
        (hcan1 : CanonicalInput l1) (hcan2 : CanonicalInput l2)
        {r : Aegis.AddTwoNumbers.List}
        (hr : Aegis.AddTwoNumbers.add_two_numbers l1 l2 = ok r), ((10 : Int) ^ max (len l1) (len l2) ≤ val l1 + val l2 →
            len r = max (len l1) (len l2) + 1) ∧
        (val l1 + val l2 < (10 : Int) ^ max (len l1) (len l2) →
            len r = max (len l1) (len l2))) := by
    sorry

  /-- Whenever add_two_numbers l1 l2 returns r, if len(r)=max(len(l1),len(l2))+1, then digits(r)[len(r)-1]=1.
    Preconditions: l1 and l2 are non-empty finite linked lists; len(l1) and len(l2) are between 1 and 100; every node value in l1 and in l2 is an integer in [0,9]; and for each input list l, if len(l)>1 then the last node value (the most significant digit in reverse order) is nonzero. -/
  theorem spec_5 (l1 l2 : Aegis.AddTwoNumbers.List)
      (hne1 : l1 ≠ Aegis.AddTwoNumbers.List.Nil)
      (hne2 : l2 ≠ Aegis.AddTwoNumbers.List.Nil)
      (hlen1 : 1 ≤ len l1 ∧ len l1 ≤ 100)
      (hlen2 : 1 ≤ len l2 ∧ len l2 ≤ 100)
      (hdig1 : AllDigits l1) (hdig2 : AllDigits l2)
      (hcan1 : CanonicalInput l1) (hcan2 : CanonicalInput l2)
      {r : Aegis.AddTwoNumbers.List}
      (hr : Aegis.AddTwoNumbers.add_two_numbers l1 l2 = ok r)
      (hlen : len r = max (len l1) (len l2) + 1) :
      lastDigit r = some 1 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (l1 l2 : Aegis.AddTwoNumbers.List)
        (hne1 : l1 ≠ Aegis.AddTwoNumbers.List.Nil)
        (hne2 : l2 ≠ Aegis.AddTwoNumbers.List.Nil)
        (hlen1 : 1 ≤ len l1 ∧ len l1 ≤ 100)
        (hlen2 : 1 ≤ len l2 ∧ len l2 ≤ 100)
        (hdig1 : AllDigits l1) (hdig2 : AllDigits l2)
        (hcan1 : CanonicalInput l1) (hcan2 : CanonicalInput l2)
        {r : Aegis.AddTwoNumbers.List}
        (hr : Aegis.AddTwoNumbers.add_two_numbers l1 l2 = ok r)
        (hlen : len r = max (len l1) (len l2) + 1), lastDigit r = some 1) := by
    sorry

  /-- Whenever add_two_numbers l1 l2 returns r1 and add_two_numbers l2 l1 returns r2, digits(r1)=digits(r2).
    Preconditions: l1 and l2 are non-empty finite linked lists; len(l1) and len(l2) are between 1 and 100; every node value in l1 and in l2 is an integer in [0,9]; and for each input list l, if len(l)>1 then the last node value (the most significant digit in reverse order) is nonzero. -/
  theorem spec_6 (l1 l2 : Aegis.AddTwoNumbers.List)
      (hne1 : l1 ≠ Aegis.AddTwoNumbers.List.Nil)
      (hne2 : l2 ≠ Aegis.AddTwoNumbers.List.Nil)
      (hlen1 : 1 ≤ len l1 ∧ len l1 ≤ 100)
      (hlen2 : 1 ≤ len l2 ∧ len l2 ≤ 100)
      (hdig1 : AllDigits l1) (hdig2 : AllDigits l2)
      (hcan1 : CanonicalInput l1) (hcan2 : CanonicalInput l2)
      {r1 r2 : Aegis.AddTwoNumbers.List}
      (hr1 : Aegis.AddTwoNumbers.add_two_numbers l1 l2 = ok r1)
      (hr2 : Aegis.AddTwoNumbers.add_two_numbers l2 l1 = ok r2) :
      digits r1 = digits r2 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (l1 l2 : Aegis.AddTwoNumbers.List)
        (hne1 : l1 ≠ Aegis.AddTwoNumbers.List.Nil)
        (hne2 : l2 ≠ Aegis.AddTwoNumbers.List.Nil)
        (hlen1 : 1 ≤ len l1 ∧ len l1 ≤ 100)
        (hlen2 : 1 ≤ len l2 ∧ len l2 ≤ 100)
        (hdig1 : AllDigits l1) (hdig2 : AllDigits l2)
        (hcan1 : CanonicalInput l1) (hcan2 : CanonicalInput l2)
        {r1 r2 : Aegis.AddTwoNumbers.List}
        (hr1 : Aegis.AddTwoNumbers.add_two_numbers l1 l2 = ok r1)
        (hr2 : Aegis.AddTwoNumbers.add_two_numbers l2 l1 = ok r2), digits r1 = digits r2) := by
    sorry

  end AegisSpec.AddTwoNumbers
