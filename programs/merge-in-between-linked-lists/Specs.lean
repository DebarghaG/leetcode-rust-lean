import Aegis.MergeInBetween.Code.Funs

/-!
# Specifications of `Aegis.MergeInBetween.merge_in_between`

LeetCode problem `merge-in-between-linked-lists`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MergeInBetween

  def len : Aegis.MergeInBetween.List → Nat
    | .Nil => 0
    | .Cons _ tl => len tl + 1

  def vals : Aegis.MergeInBetween.List → List Int
    | .Nil => []
    | .Cons v tl => v.val :: vals tl

  /-- Whenever the function returns a result r, vals(r) is exactly the concatenation of three sequences: (vals(list1)[0], ..., vals(list1)[a-1]), then (vals(list2)[0], ..., vals(list2)[len(list2)-1]), then (vals(list1)[b+1], ..., vals(list1)[len(list1)-1]). Equivalently, len(r) = a + len(list2) + (len(list1) - b - 1), and for every integer i with 0 <= i < len(r): if 0 <= i < a then vals(r)[i] = vals(list1)[i]; if a <= i < a + len(list2) then vals(r)[i] = vals(list2)[i - a]; if a + len(list2) <= i < len(r) then vals(r)[i] = vals(list1)[b + 1 + (i - a - len(list2))].
    Preconditions: Let len(L) be the number of nodes in a List L and vals(L) the sequence of its node values from head to tail. The inputs satisfy 3 <= len(list1) <= 10^4, 1 <= len(list2) <= 10^4, and 1 <= a <= b < len(list1) - 1, where a and b are interpreted as mathematical integers and indices are 0-based. -/
  theorem spec_1 (list1 list2 : Aegis.MergeInBetween.List) (a b : Std.I64)
      (hlen1_lower : 3 ≤ len list1) (hlen1_upper : len list1 ≤ 10 ^ 4)
      (hlen2_lower : 1 ≤ len list2) (hlen2_upper : len list2 ≤ 10 ^ 4)
      (ha_lower : 1 ≤ a.val) (hab : a.val ≤ b.val)
      (hb_upper : b.val < (len list1 : Int) - 1) :
      ∀ r : Aegis.MergeInBetween.List,
        Aegis.MergeInBetween.merge_in_between list1 a b list2 = ok r →
          vals r = (vals list1).take a.val.toNat ++ vals list2 ++
            (vals list1).drop (b.val.toNat + 1) ∧
          len r = a.val.toNat + len list2 + (len list1 - (b.val.toNat + 1)) ∧
          (∀ i : Nat, i < len r →
            (i < a.val.toNat → (vals r)[i]? = (vals list1)[i]?) ∧
            (a.val.toNat ≤ i → i < a.val.toNat + len list2 →
              (vals r)[i]? = (vals list2)[i - a.val.toNat]?) ∧
            (a.val.toNat + len list2 ≤ i →
              (vals r)[i]? =
                (vals list1)[b.val.toNat + 1 + (i - a.val.toNat - len list2)]?)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (list1 list2 : Aegis.MergeInBetween.List) (a b : Std.I64)
        (hlen1_lower : 3 ≤ len list1) (hlen1_upper : len list1 ≤ 10 ^ 4)
        (hlen2_lower : 1 ≤ len list2) (hlen2_upper : len list2 ≤ 10 ^ 4)
        (ha_lower : 1 ≤ a.val) (hab : a.val ≤ b.val)
        (hb_upper : b.val < (len list1 : Int) - 1), ∀ r : Aegis.MergeInBetween.List,
          Aegis.MergeInBetween.merge_in_between list1 a b list2 = ok r →
            vals r = (vals list1).take a.val.toNat ++ vals list2 ++
              (vals list1).drop (b.val.toNat + 1) ∧
            len r = a.val.toNat + len list2 + (len list1 - (b.val.toNat + 1)) ∧
            (∀ i : Nat, i < len r →
              (i < a.val.toNat → (vals r)[i]? = (vals list1)[i]?) ∧
              (a.val.toNat ≤ i → i < a.val.toNat + len list2 →
                (vals r)[i]? = (vals list2)[i - a.val.toNat]?) ∧
              (a.val.toNat + len list2 ≤ i →
                (vals r)[i]? =
                  (vals list1)[b.val.toNat + 1 + (i - a.val.toNat - len list2)]?))) := by
    sorry

  /-- The function returns a result r (it does not fail, panic, or overflow) for every input satisfying the preconditions.
    Preconditions: Let len(L) be the number of nodes in a List L and vals(L) the sequence of its node values from head to tail. The inputs satisfy 3 <= len(list1) <= 10^4, 1 <= len(list2) <= 10^4, and 1 <= a <= b < len(list1) - 1, where a and b are interpreted as mathematical integers and indices are 0-based. -/
  theorem spec_2 (list1 list2 : Aegis.MergeInBetween.List) (a b : Std.I64)
      (hlen1_lower : 3 ≤ len list1) (hlen1_upper : len list1 ≤ 10 ^ 4)
      (hlen2_lower : 1 ≤ len list2) (hlen2_upper : len list2 ≤ 10 ^ 4)
      (ha_lower : 1 ≤ a.val) (hab : a.val ≤ b.val)
      (hb_upper : b.val < (len list1 : Int) - 1) :
      ∃ r : Aegis.MergeInBetween.List,
        Aegis.MergeInBetween.merge_in_between list1 a b list2 = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (list1 list2 : Aegis.MergeInBetween.List) (a b : Std.I64)
        (hlen1_lower : 3 ≤ len list1) (hlen1_upper : len list1 ≤ 10 ^ 4)
        (hlen2_lower : 1 ≤ len list2) (hlen2_upper : len list2 ≤ 10 ^ 4)
        (ha_lower : 1 ≤ a.val) (hab : a.val ≤ b.val)
        (hb_upper : b.val < (len list1 : Int) - 1), ∃ r : Aegis.MergeInBetween.List,
          Aegis.MergeInBetween.merge_in_between list1 a b list2 = ok r) := by
    sorry

  end AegisSpec.MergeInBetween
