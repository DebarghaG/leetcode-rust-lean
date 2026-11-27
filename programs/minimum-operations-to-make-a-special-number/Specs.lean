import Aegis.MinimumOperations.Code.Funs

/-!
# Specifications of `Aegis.MinimumOperations.minimum_operations`

LeetCode problem `minimum-operations-to-make-a-special-number`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinimumOperations

  open Aegis.MinimumOperations

  def digitsOf (num : Slice Std.U8) : List Nat := num.val.map (fun b => b.val)

  def digitAt (num : Slice Std.U8) (i : Nat) : Nat := (digitsOf num).getD i 0

  def seqValue (s : List Nat) : Nat := s.foldl (fun acc d => 10 * acc + d) 0

  def IsSubseqOf (num : Slice Std.U8) (s : List Nat) : Prop :=
    List.Sublist s (digitsOf num)

  def IsSpecial (num : Slice Std.U8) (s : List Nat) : Prop :=
    IsSubseqOf num s ∧ 25 ∣ seqValue s

  noncomputable def maxSpecialLen (num : Slice Std.U8) : Nat := by
    classical
    exact
      Nat.findGreatest
        (fun k => ∃ s : List Nat, IsSpecial num s ∧ s.length = k) num.val.length

  def Pair25 (num : Slice Std.U8) (i j : Nat) : Prop :=
    (digitAt num i = 48 ∧ digitAt num j = 48) ∨
    (digitAt num i = 50 ∧ digitAt num j = 53) ∨
    (digitAt num i = 53 ∧ digitAt num j = 48) ∨
    (digitAt num i = 55 ∧ digitAt num j = 53)

  /-- Whenever the function returns a result r, let n = len(num). A subsequence of num is a strictly increasing sequence of indices p_0 < p_1 < ... < p_{k-1} with 0 <= p_t < n. Its value is the base-10 integer represented by the digits num[p_0], num[p_1], ..., num[p_{k-1}] in that order, with leading zeros allowed; the empty subsequence (k = 0) has value 0. A subsequence is special if its value is divisible by 25. Let L be the maximum length k of a special subsequence of num. Then r = n - L. Equivalently, r is the smallest integer d with 0 <= d <= n for which there exists a subsequence of num of length n - d whose value is divisible by 25.
    Preconditions: 1 <= len(num) <= 100; for every i with 0 <= i < len(num), 48 <= num[i] <= 57 (i.e., num[i] is an ASCII digit '0' through '9'). -/
  theorem spec_1 (num : Slice Std.U8)
      (hlen1 : 1 ≤ num.val.length) (hlen_max : num.val.length ≤ 100)
      (hdig : ∀ i : Nat, i < num.val.length → 48 ≤ digitAt num i ∧ digitAt num i ≤ 57) :
      ∀ r : Std.I64, minimum_operations num = ok r →
        r.val = (num.val.length : Int) - (maxSpecialLen num : Int) ∧
        (∃ s : List Nat, IsSpecial num s ∧ (s.length : Int) = (num.val.length : Int) - r.val) ∧
        (∀ d : Int, 0 ≤ d → d < r.val →
          ¬ ∃ s : List Nat, IsSpecial num s ∧ (s.length : Int) = (num.val.length : Int) - d) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (num : Slice Std.U8)
        (hlen1 : 1 ≤ num.val.length) (hlen_max : num.val.length ≤ 100)
        (hdig : ∀ i : Nat, i < num.val.length → 48 ≤ digitAt num i ∧ digitAt num i ≤ 57), ∀ r : Std.I64, minimum_operations num = ok r →
          r.val = (num.val.length : Int) - (maxSpecialLen num : Int) ∧
          (∃ s : List Nat, IsSpecial num s ∧ (s.length : Int) = (num.val.length : Int) - r.val) ∧
          (∀ d : Int, 0 ≤ d → d < r.val →
            ¬ ∃ s : List Nat, IsSpecial num s ∧ (s.length : Int) = (num.val.length : Int) - d)) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result (it does not fail, overflow, or panic).
    Preconditions: 1 <= len(num) <= 100; for every i with 0 <= i < len(num), 48 <= num[i] <= 57 (i.e., num[i] is an ASCII digit '0' through '9'). -/
  theorem spec_2 (num : Slice Std.U8)
      (hlen1 : 1 ≤ num.val.length) (hlen_max : num.val.length ≤ 100)
      (hdig : ∀ i : Nat, i < num.val.length → 48 ≤ digitAt num i ∧ digitAt num i ≤ 57) :
      ∃ r : Std.I64, minimum_operations num = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (num : Slice Std.U8)
        (hlen1 : 1 ≤ num.val.length) (hlen_max : num.val.length ≤ 100)
        (hdig : ∀ i : Nat, i < num.val.length → 48 ≤ digitAt num i ∧ digitAt num i ≤ 57), ∃ r : Std.I64, minimum_operations num = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r <= len(num).
    Preconditions: 1 <= len(num) <= 100; for every i with 0 <= i < len(num), 48 <= num[i] <= 57 (i.e., num[i] is an ASCII digit '0' through '9'). -/
  theorem spec_3 (num : Slice Std.U8)
      (hlen1 : 1 ≤ num.val.length) (hlen_max : num.val.length ≤ 100)
      (hdig : ∀ i : Nat, i < num.val.length → 48 ≤ digitAt num i ∧ digitAt num i ≤ 57) :
      ∀ r : Std.I64, minimum_operations num = ok r →
        0 ≤ r.val ∧ r.val ≤ (num.val.length : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (num : Slice Std.U8)
        (hlen1 : 1 ≤ num.val.length) (hlen_max : num.val.length ≤ 100)
        (hdig : ∀ i : Nat, i < num.val.length → 48 ≤ digitAt num i ∧ digitAt num i ≤ 57), ∀ r : Std.I64, minimum_operations num = ok r →
          0 ≤ r.val ∧ r.val ≤ (num.val.length : Int)) := by
    sorry

  /-- Whenever the function returns a result r, if the entire string num represents a decimal integer divisible by 25, then r = 0.
    Preconditions: 1 <= len(num) <= 100; for every i with 0 <= i < len(num), 48 <= num[i] <= 57 (i.e., num[i] is an ASCII digit '0' through '9'). -/
  theorem spec_4 (num : Slice Std.U8)
      (hlen1 : 1 ≤ num.val.length) (hlen_max : num.val.length ≤ 100)
      (hdig : ∀ i : Nat, i < num.val.length → 48 ≤ digitAt num i ∧ digitAt num i ≤ 57) :
      ∀ r : Std.I64, minimum_operations num = ok r →
        25 ∣ seqValue (digitsOf num) → r.val = 0 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (num : Slice Std.U8)
        (hlen1 : 1 ≤ num.val.length) (hlen_max : num.val.length ≤ 100)
        (hdig : ∀ i : Nat, i < num.val.length → 48 ≤ digitAt num i ∧ digitAt num i ≤ 57), ∀ r : Std.I64, minimum_operations num = ok r →
          25 ∣ seqValue (digitsOf num) → r.val = 0) := by
    sorry

  /-- Whenever the function returns a result r, if len(num) = 1, then r = 0 when num[0] = '0' and r = 1 when num[0] != '0'.
    Preconditions: 1 <= len(num) <= 100; for every i with 0 <= i < len(num), 48 <= num[i] <= 57 (i.e., num[i] is an ASCII digit '0' through '9'). -/
  theorem spec_5 (num : Slice Std.U8)
      (hlen1 : 1 ≤ num.val.length) (hlen_max : num.val.length ≤ 100)
      (hdig : ∀ i : Nat, i < num.val.length → 48 ≤ digitAt num i ∧ digitAt num i ≤ 57) :
      ∀ r : Std.I64, minimum_operations num = ok r →
        num.val.length = 1 →
          ((digitAt num 0 = 48 → r.val = 0) ∧ (digitAt num 0 ≠ 48 → r.val = 1)) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (num : Slice Std.U8)
        (hlen1 : 1 ≤ num.val.length) (hlen_max : num.val.length ≤ 100)
        (hdig : ∀ i : Nat, i < num.val.length → 48 ≤ digitAt num i ∧ digitAt num i ≤ 57), ∀ r : Std.I64, minimum_operations num = ok r →
          num.val.length = 1 →
            ((digitAt num 0 = 48 → r.val = 0) ∧ (digitAt num 0 ≠ 48 → r.val = 1))) := by
    sorry

  /-- Whenever the function returns a result r, if there exists an index i with 0 <= i < len(num) and num[i] = '0', then r <= len(num) - 1.
    Preconditions: 1 <= len(num) <= 100; for every i with 0 <= i < len(num), 48 <= num[i] <= 57 (i.e., num[i] is an ASCII digit '0' through '9'). -/
  theorem spec_6 (num : Slice Std.U8)
      (hlen1 : 1 ≤ num.val.length) (hlen_max : num.val.length ≤ 100)
      (hdig : ∀ i : Nat, i < num.val.length → 48 ≤ digitAt num i ∧ digitAt num i ≤ 57) :
      ∀ r : Std.I64, minimum_operations num = ok r →
        (∃ i : Nat, i < num.val.length ∧ digitAt num i = 48) →
          r.val ≤ (num.val.length : Int) - 1 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (num : Slice Std.U8)
        (hlen1 : 1 ≤ num.val.length) (hlen_max : num.val.length ≤ 100)
        (hdig : ∀ i : Nat, i < num.val.length → 48 ≤ digitAt num i ∧ digitAt num i ≤ 57), ∀ r : Std.I64, minimum_operations num = ok r →
          (∃ i : Nat, i < num.val.length ∧ digitAt num i = 48) →
            r.val ≤ (num.val.length : Int) - 1) := by
    sorry

  /-- Whenever the function returns a result r, if there exist indices i < j with (num[i], num[j]) in {('0','0'), ('2','5'), ('5','0'), ('7','5')}, then r <= len(num) - i - 2.
    Preconditions: 1 <= len(num) <= 100; for every i with 0 <= i < len(num), 48 <= num[i] <= 57 (i.e., num[i] is an ASCII digit '0' through '9'). -/
  theorem spec_7 (num : Slice Std.U8)
      (hlen1 : 1 ≤ num.val.length) (hlen_max : num.val.length ≤ 100)
      (hdig : ∀ i : Nat, i < num.val.length → 48 ≤ digitAt num i ∧ digitAt num i ≤ 57) :
      ∀ r : Std.I64, minimum_operations num = ok r →
        ∀ i j : Nat, i < j → j < num.val.length → Pair25 num i j →
          r.val ≤ (num.val.length : Int) - (i : Int) - 2 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (num : Slice Std.U8)
        (hlen1 : 1 ≤ num.val.length) (hlen_max : num.val.length ≤ 100)
        (hdig : ∀ i : Nat, i < num.val.length → 48 ≤ digitAt num i ∧ digitAt num i ≤ 57), ∀ r : Std.I64, minimum_operations num = ok r →
          ∀ i j : Nat, i < j → j < num.val.length → Pair25 num i j →
            r.val ≤ (num.val.length : Int) - (i : Int) - 2) := by
    sorry

  /-- Whenever the function returns a result r, if there exists at least one pair of indices i < j with (num[i], num[j]) in {('0','0'), ('2','5'), ('5','0'), ('7','5')}, let i_max be the largest i for which such a j exists. Then r = len(num) - i_max - 2.
    Preconditions: 1 <= len(num) <= 100; for every i with 0 <= i < len(num), 48 <= num[i] <= 57 (i.e., num[i] is an ASCII digit '0' through '9'). -/
  theorem spec_8 (num : Slice Std.U8)
      (hlen1 : 1 ≤ num.val.length) (hlen_max : num.val.length ≤ 100)
      (hdig : ∀ i : Nat, i < num.val.length → 48 ≤ digitAt num i ∧ digitAt num i ≤ 57) :
      ∀ r : Std.I64, minimum_operations num = ok r →
        (∃ i j : Nat, i < j ∧ j < num.val.length ∧ Pair25 num i j) →
          ∃ i_max : Nat,
            (∃ j : Nat, i_max < j ∧ j < num.val.length ∧ Pair25 num i_max j) ∧
            (∀ i j : Nat, i < j → j < num.val.length → Pair25 num i j → i ≤ i_max) ∧
            r.val = (num.val.length : Int) - (i_max : Int) - 2 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (num : Slice Std.U8)
        (hlen1 : 1 ≤ num.val.length) (hlen_max : num.val.length ≤ 100)
        (hdig : ∀ i : Nat, i < num.val.length → 48 ≤ digitAt num i ∧ digitAt num i ≤ 57), ∀ r : Std.I64, minimum_operations num = ok r →
          (∃ i j : Nat, i < j ∧ j < num.val.length ∧ Pair25 num i j) →
            ∃ i_max : Nat,
              (∃ j : Nat, i_max < j ∧ j < num.val.length ∧ Pair25 num i_max j) ∧
              (∀ i j : Nat, i < j → j < num.val.length → Pair25 num i j → i ≤ i_max) ∧
              r.val = (num.val.length : Int) - (i_max : Int) - 2) := by
    sorry

  /-- Whenever the function returns a result r, if there is no pair i < j with (num[i], num[j]) in {('0','0'), ('2','5'), ('5','0'), ('7','5')}, but there exists an index i with num[i] = '0', then r = len(num) - 1.
    Preconditions: 1 <= len(num) <= 100; for every i with 0 <= i < len(num), 48 <= num[i] <= 57 (i.e., num[i] is an ASCII digit '0' through '9'). -/
  theorem spec_9 (num : Slice Std.U8)
      (hlen1 : 1 ≤ num.val.length) (hlen_max : num.val.length ≤ 100)
      (hdig : ∀ i : Nat, i < num.val.length → 48 ≤ digitAt num i ∧ digitAt num i ≤ 57) :
      ∀ r : Std.I64, minimum_operations num = ok r →
        (¬ ∃ i j : Nat, i < j ∧ j < num.val.length ∧ Pair25 num i j) →
          (∃ i : Nat, i < num.val.length ∧ digitAt num i = 48) →
            r.val = (num.val.length : Int) - 1 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (num : Slice Std.U8)
        (hlen1 : 1 ≤ num.val.length) (hlen_max : num.val.length ≤ 100)
        (hdig : ∀ i : Nat, i < num.val.length → 48 ≤ digitAt num i ∧ digitAt num i ≤ 57), ∀ r : Std.I64, minimum_operations num = ok r →
          (¬ ∃ i j : Nat, i < j ∧ j < num.val.length ∧ Pair25 num i j) →
            (∃ i : Nat, i < num.val.length ∧ digitAt num i = 48) →
              r.val = (num.val.length : Int) - 1) := by
    sorry

  /-- Whenever the function returns a result r, if num contains no '0' and there is no pair i < j with (num[i], num[j]) in {('0','0'), ('2','5'), ('5','0'), ('7','5')}, then r = len(num).
    Preconditions: 1 <= len(num) <= 100; for every i with 0 <= i < len(num), 48 <= num[i] <= 57 (i.e., num[i] is an ASCII digit '0' through '9'). -/
  theorem spec_10 (num : Slice Std.U8)
      (hlen1 : 1 ≤ num.val.length) (hlen_max : num.val.length ≤ 100)
      (hdig : ∀ i : Nat, i < num.val.length → 48 ≤ digitAt num i ∧ digitAt num i ≤ 57) :
      ∀ r : Std.I64, minimum_operations num = ok r →
        (∀ i : Nat, i < num.val.length → digitAt num i ≠ 48) →
          (¬ ∃ i j : Nat, i < j ∧ j < num.val.length ∧ Pair25 num i j) →
            r.val = (num.val.length : Int) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (num : Slice Std.U8)
        (hlen1 : 1 ≤ num.val.length) (hlen_max : num.val.length ≤ 100)
        (hdig : ∀ i : Nat, i < num.val.length → 48 ≤ digitAt num i ∧ digitAt num i ≤ 57), ∀ r : Std.I64, minimum_operations num = ok r →
          (∀ i : Nat, i < num.val.length → digitAt num i ≠ 48) →
            (¬ ∃ i j : Nat, i < j ∧ j < num.val.length ∧ Pair25 num i j) →
              r.val = (num.val.length : Int)) := by
    sorry

  /-- Whenever the function returns a result r, there exists a subsequence of num of length len(num) - r whose decimal value is divisible by 25.
    Preconditions: 1 <= len(num) <= 100; for every i with 0 <= i < len(num), 48 <= num[i] <= 57 (i.e., num[i] is an ASCII digit '0' through '9'). -/
  theorem spec_11 (num : Slice Std.U8)
      (hlen1 : 1 ≤ num.val.length) (hlen_max : num.val.length ≤ 100)
      (hdig : ∀ i : Nat, i < num.val.length → 48 ≤ digitAt num i ∧ digitAt num i ≤ 57) :
      ∀ r : Std.I64, minimum_operations num = ok r →
        ∃ s : List Nat, IsSpecial num s ∧ (s.length : Int) = (num.val.length : Int) - r.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (num : Slice Std.U8)
        (hlen1 : 1 ≤ num.val.length) (hlen_max : num.val.length ≤ 100)
        (hdig : ∀ i : Nat, i < num.val.length → 48 ≤ digitAt num i ∧ digitAt num i ≤ 57), ∀ r : Std.I64, minimum_operations num = ok r →
          ∃ s : List Nat, IsSpecial num s ∧ (s.length : Int) = (num.val.length : Int) - r.val) := by
    sorry

  /-- Whenever the function returns a result r, for every subsequence of num of length strictly greater than len(num) - r, its decimal value is not divisible by 25.
    Preconditions: 1 <= len(num) <= 100; for every i with 0 <= i < len(num), 48 <= num[i] <= 57 (i.e., num[i] is an ASCII digit '0' through '9'). -/
  theorem spec_12 (num : Slice Std.U8)
      (hlen1 : 1 ≤ num.val.length) (hlen_max : num.val.length ≤ 100)
      (hdig : ∀ i : Nat, i < num.val.length → 48 ≤ digitAt num i ∧ digitAt num i ≤ 57) :
      ∀ r : Std.I64, minimum_operations num = ok r →
        ∀ s : List Nat, IsSubseqOf num s →
          (s.length : Int) > (num.val.length : Int) - r.val → ¬ 25 ∣ seqValue s := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (num : Slice Std.U8)
        (hlen1 : 1 ≤ num.val.length) (hlen_max : num.val.length ≤ 100)
        (hdig : ∀ i : Nat, i < num.val.length → 48 ≤ digitAt num i ∧ digitAt num i ≤ 57), ∀ r : Std.I64, minimum_operations num = ok r →
          ∀ s : List Nat, IsSubseqOf num s →
            (s.length : Int) > (num.val.length : Int) - r.val → ¬ 25 ∣ seqValue s) := by
    sorry

  end AegisSpec.MinimumOperations
