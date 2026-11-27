import Aegis.HasGroupsSizeX.Code.Funs

/-!
# Specifications of `Aegis.HasGroupsSizeX.has_groups_size_x`

LeetCode problem `x-of-a-kind-in-a-deck-of-cards`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.HasGroupsSizeX

  def count (deck : Slice Std.I64) (v : Int) : Nat :=
    (deck.val.filter (fun x => x.val = v)).length

  def occurs (deck : Slice Std.I64) (v : Int) : Prop :=
    ∃ x ∈ deck.val, x.val = v

  def countGcd (deck : Slice Std.I64) : Nat :=
    ((deck.val.map (fun x => x.val)).dedup.map (fun v => count deck v)).foldr Nat.gcd 0

  /-- Let cnt(v) = #{j | 0 <= j < len(deck) and deck[j] = v} for each integer v. Whenever has_groups_size_x(deck) returns a result r, r = true if and only if there exists an integer x with x > 1 such that x divides cnt(v) for every value v that occurs in deck. Equivalently, r = true iff the greatest common divisor of the positive numbers cnt(v), over all values v that occur in deck, is greater than 1.
    Preconditions: 1 <= len(deck) <= 10000 and for every i with 0 <= i < len(deck), 0 <= deck[i] < 10000. -/
  theorem spec_1 (deck : Slice Std.I64)
      (hlen : 1 ≤ deck.val.length ∧ deck.val.length ≤ 10000)
      (helems : ∀ (i : Nat) (hi : i < deck.val.length),
        0 ≤ (deck.val[i]).val ∧ (deck.val[i]).val < 10000) :
      ∀ r : Bool, Aegis.HasGroupsSizeX.has_groups_size_x deck = ok r →
        ((r = true ↔
          ∃ x : Int, 1 < x ∧ ∀ v : Int, occurs deck v → x ∣ (count deck v : Int)) ∧
         (r = true ↔ 1 < countGcd deck)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (deck : Slice Std.I64)
        (hlen : 1 ≤ deck.val.length ∧ deck.val.length ≤ 10000)
        (helems : ∀ (i : Nat) (hi : i < deck.val.length),
          0 ≤ (deck.val[i]).val ∧ (deck.val[i]).val < 10000), ∀ r : Bool, Aegis.HasGroupsSizeX.has_groups_size_x deck = ok r →
          ((r = true ↔
            ∃ x : Int, 1 < x ∧ ∀ v : Int, occurs deck v → x ∣ (count deck v : Int)) ∧
           (r = true ↔ 1 < countGcd deck))) := by
    sorry

  /-- For every deck satisfying the preconditions, has_groups_size_x(deck) returns a result r; that is, the function does not fail.
    Preconditions: 1 <= len(deck) <= 10000 and for every i with 0 <= i < len(deck), 0 <= deck[i] < 10000. -/
  theorem spec_2 (deck : Slice Std.I64)
      (hlen : 1 ≤ deck.val.length ∧ deck.val.length ≤ 10000)
      (helems : ∀ (i : Nat) (hi : i < deck.val.length),
        0 ≤ (deck.val[i]).val ∧ (deck.val[i]).val < 10000) :
      ∃ r : Bool, Aegis.HasGroupsSizeX.has_groups_size_x deck = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (deck : Slice Std.I64)
        (hlen : 1 ≤ deck.val.length ∧ deck.val.length ≤ 10000)
        (helems : ∀ (i : Nat) (hi : i < deck.val.length),
          0 ≤ (deck.val[i]).val ∧ (deck.val[i]).val < 10000), ∃ r : Bool, Aegis.HasGroupsSizeX.has_groups_size_x deck = ok r) := by
    sorry

  /-- Whenever has_groups_size_x(deck) returns a result r, r = false.
    Preconditions: 1 <= len(deck) <= 10000; 0 <= deck[i] < 10000 for all i; and there exist two distinct integer values a and b that each occur in deck such that gcd(cnt(a), cnt(b)) = 1, where cnt(v) = #{j | 0 <= j < len(deck) and deck[j] = v}. -/
  theorem spec_3 (deck : Slice Std.I64)
      (hlen : 1 ≤ deck.val.length ∧ deck.val.length ≤ 10000)
      (helems : ∀ (i : Nat) (hi : i < deck.val.length),
        0 ≤ (deck.val[i]).val ∧ (deck.val[i]).val < 10000)
      (hcop : ∃ a b : Int, a ≠ b ∧ occurs deck a ∧ occurs deck b ∧
        Nat.gcd (count deck a) (count deck b) = 1) :
      ∀ r : Bool, Aegis.HasGroupsSizeX.has_groups_size_x deck = ok r → r = false := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (deck : Slice Std.I64)
        (hlen : 1 ≤ deck.val.length ∧ deck.val.length ≤ 10000)
        (helems : ∀ (i : Nat) (hi : i < deck.val.length),
          0 ≤ (deck.val[i]).val ∧ (deck.val[i]).val < 10000)
        (hcop : ∃ a b : Int, a ≠ b ∧ occurs deck a ∧ occurs deck b ∧
          Nat.gcd (count deck a) (count deck b) = 1), ∀ r : Bool, Aegis.HasGroupsSizeX.has_groups_size_x deck = ok r → r = false) := by
    sorry

  /-- Whenever has_groups_size_x(deck) returns a result r and r = true, for every value v that occurs in deck, cnt(v) >= 2, where cnt(v) = #{j | 0 <= j < len(deck) and deck[j] = v}.
    Preconditions: 1 <= len(deck) <= 10000 and for every i with 0 <= i < len(deck), 0 <= deck[i] < 10000. -/
  theorem spec_4 (deck : Slice Std.I64)
      (hlen : 1 ≤ deck.val.length ∧ deck.val.length ≤ 10000)
      (helems : ∀ (i : Nat) (hi : i < deck.val.length),
        0 ≤ (deck.val[i]).val ∧ (deck.val[i]).val < 10000) :
      ∀ r : Bool, Aegis.HasGroupsSizeX.has_groups_size_x deck = ok r → r = true →
        ∀ v : Int, occurs deck v → 2 ≤ count deck v := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (deck : Slice Std.I64)
        (hlen : 1 ≤ deck.val.length ∧ deck.val.length ≤ 10000)
        (helems : ∀ (i : Nat) (hi : i < deck.val.length),
          0 ≤ (deck.val[i]).val ∧ (deck.val[i]).val < 10000), ∀ r : Bool, Aegis.HasGroupsSizeX.has_groups_size_x deck = ok r → r = true →
          ∀ v : Int, occurs deck v → 2 ≤ count deck v) := by
    sorry

  /-- Whenever has_groups_size_x(deck) returns a result r, r = true.
    Preconditions: 1 <= len(deck) <= 10000; 0 <= deck[i] < 10000 for all i; and for every value v that occurs in deck, cnt(v) is even, where cnt(v) = #{j | 0 <= j < len(deck) and deck[j] = v}. -/
  theorem spec_5 (deck : Slice Std.I64)
      (hlen : 1 ≤ deck.val.length ∧ deck.val.length ≤ 10000)
      (helems : ∀ (i : Nat) (hi : i < deck.val.length),
        0 ≤ (deck.val[i]).val ∧ (deck.val[i]).val < 10000)
      (heven : ∀ v : Int, occurs deck v → 2 ∣ count deck v) :
      ∀ r : Bool, Aegis.HasGroupsSizeX.has_groups_size_x deck = ok r → r = true := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (deck : Slice Std.I64)
        (hlen : 1 ≤ deck.val.length ∧ deck.val.length ≤ 10000)
        (helems : ∀ (i : Nat) (hi : i < deck.val.length),
          0 ≤ (deck.val[i]).val ∧ (deck.val[i]).val < 10000)
        (heven : ∀ v : Int, occurs deck v → 2 ∣ count deck v), ∀ r : Bool, Aegis.HasGroupsSizeX.has_groups_size_x deck = ok r → r = true) := by
    sorry

  /-- Whenever has_groups_size_x(deck) returns a result r, r = true if and only if gcd(m, n) > 1.
    Preconditions: 1 <= len(deck) <= 10000; 0 <= deck[i] < 10000 for all i; and exactly two distinct integer values a and b occur in deck. Let m = #{j | 0 <= j < len(deck) and deck[j] = a} and n = #{j | 0 <= j < len(deck) and deck[j] = b}. -/
  theorem spec_6 (deck : Slice Std.I64) (a b : Int)
      (hlen : 1 ≤ deck.val.length ∧ deck.val.length ≤ 10000)
      (helems : ∀ (i : Nat) (hi : i < deck.val.length),
        0 ≤ (deck.val[i]).val ∧ (deck.val[i]).val < 10000)
      (hne : a ≠ b) (ha : occurs deck a) (hb : occurs deck b)
      (hex : ∀ v : Int, occurs deck v → v = a ∨ v = b) :
      ∀ r : Bool, Aegis.HasGroupsSizeX.has_groups_size_x deck = ok r →
        (r = true ↔ 1 < Nat.gcd (count deck a) (count deck b)) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (deck : Slice Std.I64) (a b : Int)
        (hlen : 1 ≤ deck.val.length ∧ deck.val.length ≤ 10000)
        (helems : ∀ (i : Nat) (hi : i < deck.val.length),
          0 ≤ (deck.val[i]).val ∧ (deck.val[i]).val < 10000)
        (hne : a ≠ b) (ha : occurs deck a) (hb : occurs deck b)
        (hex : ∀ v : Int, occurs deck v → v = a ∨ v = b), ∀ r : Bool, Aegis.HasGroupsSizeX.has_groups_size_x deck = ok r →
          (r = true ↔ 1 < Nat.gcd (count deck a) (count deck b))) := by
    sorry

  /-- Whenever has_groups_size_x(deck1) returns a result r1 and has_groups_size_x(deck2) returns a result r2, r1 = r2.
    Preconditions: deck1 and deck2 are two slices each satisfying 1 <= len <= 10000 and having all elements in [0, 10000). For every integer v, cnt1(v) = cnt2(v), where cnt1(v) = #{j | 0 <= j < len(deck1) and deck1[j] = v} and cnt2(v) = #{j | 0 <= j < len(deck2) and deck2[j] = v}. -/
  theorem spec_7 (deck1 deck2 : Slice Std.I64)
      (hlen1 : 1 ≤ deck1.val.length ∧ deck1.val.length ≤ 10000)
      (helems1 : ∀ (i : Nat) (hi : i < deck1.val.length),
        0 ≤ (deck1.val[i]).val ∧ (deck1.val[i]).val < 10000)
      (hlen2 : 1 ≤ deck2.val.length ∧ deck2.val.length ≤ 10000)
      (helems2 : ∀ (i : Nat) (hi : i < deck2.val.length),
        0 ≤ (deck2.val[i]).val ∧ (deck2.val[i]).val < 10000)
      (hcnt : ∀ v : Int, count deck1 v = count deck2 v) :
      ∀ r1 r2 : Bool,
        Aegis.HasGroupsSizeX.has_groups_size_x deck1 = ok r1 →
        Aegis.HasGroupsSizeX.has_groups_size_x deck2 = ok r2 → r1 = r2 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (deck1 deck2 : Slice Std.I64)
        (hlen1 : 1 ≤ deck1.val.length ∧ deck1.val.length ≤ 10000)
        (helems1 : ∀ (i : Nat) (hi : i < deck1.val.length),
          0 ≤ (deck1.val[i]).val ∧ (deck1.val[i]).val < 10000)
        (hlen2 : 1 ≤ deck2.val.length ∧ deck2.val.length ≤ 10000)
        (helems2 : ∀ (i : Nat) (hi : i < deck2.val.length),
          0 ≤ (deck2.val[i]).val ∧ (deck2.val[i]).val < 10000)
        (hcnt : ∀ v : Int, count deck1 v = count deck2 v), ∀ r1 r2 : Bool,
          Aegis.HasGroupsSizeX.has_groups_size_x deck1 = ok r1 →
          Aegis.HasGroupsSizeX.has_groups_size_x deck2 = ok r2 → r1 = r2) := by
    sorry

  /-- Whenever has_groups_size_x(deck) returns a result r and r = true, there exists an integer x such that 2 <= x <= min { cnt(v) | v occurs in deck } and x divides cnt(v) for every value v that occurs in deck, where cnt(v) = #{j | 0 <= j < len(deck) and deck[j] = v}.
    Preconditions: 1 <= len(deck) <= 10000 and for every i with 0 <= i < len(deck), 0 <= deck[i] < 10000. -/
  theorem spec_8 (deck : Slice Std.I64)
      (hlen : 1 ≤ deck.val.length ∧ deck.val.length ≤ 10000)
      (helems : ∀ (i : Nat) (hi : i < deck.val.length),
        0 ≤ (deck.val[i]).val ∧ (deck.val[i]).val < 10000) :
      ∀ r : Bool, Aegis.HasGroupsSizeX.has_groups_size_x deck = ok r → r = true →
        ∃ x : Int, 2 ≤ x ∧
          (∀ v : Int, occurs deck v → x ≤ (count deck v : Int)) ∧
          (∀ v : Int, occurs deck v → x ∣ (count deck v : Int)) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (deck : Slice Std.I64)
        (hlen : 1 ≤ deck.val.length ∧ deck.val.length ≤ 10000)
        (helems : ∀ (i : Nat) (hi : i < deck.val.length),
          0 ≤ (deck.val[i]).val ∧ (deck.val[i]).val < 10000), ∀ r : Bool, Aegis.HasGroupsSizeX.has_groups_size_x deck = ok r → r = true →
          ∃ x : Int, 2 ≤ x ∧
            (∀ v : Int, occurs deck v → x ≤ (count deck v : Int)) ∧
            (∀ v : Int, occurs deck v → x ∣ (count deck v : Int))) := by
    sorry

  end AegisSpec.HasGroupsSizeX
