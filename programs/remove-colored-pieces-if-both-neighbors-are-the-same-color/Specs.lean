import Aegis.WinnerOfGame.Code.Funs

/-!
# Specifications of `Aegis.WinnerOfGame.winner_of_game`

LeetCode problem `remove-colored-pieces-if-both-neighbors-are-the-same-color`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.WinnerOfGame

  namespace AegisSpec.WinnerOfGame

  abbrev codeA : U8 := 65#u8

  abbrev codeB : U8 := 66#u8

  abbrev windowAt (z : List U8) (i : Nat) (c : U8) : Prop :=
    z[i-1]? = some c ∧ z[i]? = some c ∧ z[i+1]? = some c

  def tripleCount (z : List U8) (c : U8) : Nat :=
    (List.range (z.length - 1)).countP (fun i => decide (1 ≤ i ∧ windowAt z i c))

  def allAB (z : List U8) : Prop :=
    ∀ i : Nat, i < z.length → z[i]? = some codeA ∨ z[i]? = some codeB

  def allA (z : List U8) : Prop :=
    ∀ i : Nat, i < z.length → z[i]? = some codeA

  def lenBounds (z : List U8) : Prop :=
    1 ≤ z.length ∧ z.length ≤ 100000

  /-- Let a be the number of indices i with 1 <= i <= n-2 such that colors[i-1] = colors[i] = colors[i+1] = 'A', and let b be the number of indices i with 1 <= i <= n-2 such that colors[i-1] = colors[i] = colors[i+1] = 'B'. Whenever winner_of_game(colors) returns a result r, r = true if and only if a > b. Equivalently, r = true exactly when Alice wins under optimal play of the described removal game (Alice moves first and loses if she has no legal move on her turn), and r = false exactly when Bob wins.
    Preconditions: Let n = len(colors). 1 <= n <= 100000, and for every i with 0 <= i < n, colors[i] is the ASCII code for 'A' or for 'B'. -/
  theorem spec_1 (colors : Slice U8) (hlen : lenBounds colors.val) (hab : allAB colors.val) :
      ∀ r : Bool, winner_of_game colors = ok r →
        (r = true ↔ tripleCount colors.val codeA > tripleCount colors.val codeB) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (colors : Slice U8) (hlen : lenBounds colors.val) (hab : allAB colors.val), ∀ r : Bool, winner_of_game colors = ok r →
          (r = true ↔ tripleCount colors.val codeA > tripleCount colors.val codeB)) := by
    sorry

  /-- For every colors satisfying the preconditions, winner_of_game(colors) returns a result r; it does not fail by arithmetic overflow, out-of-bounds indexing, or panic.
    Preconditions: Let n = len(colors). 1 <= n <= 100000, and for every i with 0 <= i < n, colors[i] is the ASCII code for 'A' or for 'B'. -/
  theorem spec_2 (colors : Slice U8) (hlen : lenBounds colors.val) (hab : allAB colors.val) :
      ∃ r : Bool, winner_of_game colors = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (colors : Slice U8) (hlen : lenBounds colors.val) (hab : allAB colors.val), ∃ r : Bool, winner_of_game colors = ok r) := by
    sorry

  /-- winner_of_game(colors) returns a result r, and r = true if and only if n >= 3.
    Preconditions: Let n = len(colors). 1 <= n <= 100000, and for every i with 0 <= i < n, colors[i] is the ASCII code for 'A'. -/
  theorem spec_3 (colors : Slice U8) (hlen : lenBounds colors.val) (ha : allA colors.val) :
      ∃ r : Bool, winner_of_game colors = ok r ∧ (r = true ↔ 3 ≤ colors.val.length) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (colors : Slice U8) (hlen : lenBounds colors.val) (ha : allA colors.val), ∃ r : Bool, winner_of_game colors = ok r ∧ (r = true ↔ 3 ≤ colors.val.length)) := by
    sorry

  /-- winner_of_game(colors) returns a result r, and r = false.
    Preconditions: Let n = len(colors). 1 <= n <= 100000, every colors[i] is the ASCII code for 'A' or for 'B', and for every i with 1 <= i <= n-2, it is not the case that colors[i-1] = colors[i] = colors[i+1] = 'A'. -/
  theorem spec_4 (colors : Slice U8) (hlen : lenBounds colors.val) (hab : allAB colors.val)
      (hnoA : ∀ i : Nat, 1 ≤ i → i ≤ colors.val.length - 2 → ¬ windowAt colors.val i codeA) :
      ∃ r : Bool, winner_of_game colors = ok r ∧ r = false := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (colors : Slice U8) (hlen : lenBounds colors.val) (hab : allAB colors.val)
        (hnoA : ∀ i : Nat, 1 ≤ i → i ≤ colors.val.length - 2 → ¬ windowAt colors.val i codeA), ∃ r : Bool, winner_of_game colors = ok r ∧ r = false) := by
    sorry

  /-- winner_of_game(colors) returns a result r, and r = true.
    Preconditions: Let n = len(colors). 1 <= n <= 100000, every colors[i] is the ASCII code for 'A' or for 'B', there is at least one i with 1 <= i <= n-2 such that colors[i-1] = colors[i] = colors[i+1] = 'A', and for every i with 1 <= i <= n-2 it is not the case that colors[i-1] = colors[i] = colors[i+1] = 'B'. -/
  theorem spec_5 (colors : Slice U8) (hlen : lenBounds colors.val) (hab : allAB colors.val)
      (hexA : ∃ i : Nat, 1 ≤ i ∧ i ≤ colors.val.length - 2 ∧ windowAt colors.val i codeA)
      (hnoB : ∀ i : Nat, 1 ≤ i → i ≤ colors.val.length - 2 → ¬ windowAt colors.val i codeB) :
      ∃ r : Bool, winner_of_game colors = ok r ∧ r = true := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (colors : Slice U8) (hlen : lenBounds colors.val) (hab : allAB colors.val)
        (hexA : ∃ i : Nat, 1 ≤ i ∧ i ≤ colors.val.length - 2 ∧ windowAt colors.val i codeA)
        (hnoB : ∀ i : Nat, 1 ≤ i → i ≤ colors.val.length - 2 → ¬ windowAt colors.val i codeB), ∃ r : Bool, winner_of_game colors = ok r ∧ r = true) := by
    sorry

  /-- If a(x) = a(y) and b(x) = b(y), then winner_of_game(x) returns a result r_x and winner_of_game(y) returns a result r_y with r_x = r_y.
    Preconditions: For each of two inputs x and y, len(x) is between 1 and 100000 inclusive and every byte is the ASCII code for 'A' or for 'B'. For a string z, define a(z) as the number of indices i with 1 <= i <= len(z)-2 and z[i-1] = z[i] = z[i+1] = 'A', and b(z) analogously with 'B'. -/
  theorem spec_6 (x y : Slice U8)
      (hxlen : lenBounds x.val) (hxab : allAB x.val)
      (hylen : lenBounds y.val) (hyab : allAB y.val)
      (ha : tripleCount x.val codeA = tripleCount y.val codeA)
      (hb : tripleCount x.val codeB = tripleCount y.val codeB) :
      ∃ rx ry : Bool, winner_of_game x = ok rx ∧ winner_of_game y = ok ry ∧ rx = ry := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (x y : Slice U8)
        (hxlen : lenBounds x.val) (hxab : allAB x.val)
        (hylen : lenBounds y.val) (hyab : allAB y.val)
        (ha : tripleCount x.val codeA = tripleCount y.val codeA)
        (hb : tripleCount x.val codeB = tripleCount y.val codeB), ∃ rx ry : Bool, winner_of_game x = ok rx ∧ winner_of_game y = ok ry ∧ rx = ry) := by
    sorry

  /-- If a(x) >= a(y), b(x) <= b(y), winner_of_game(y) returns a result r_y, and r_y = true, then winner_of_game(x) returns a result r_x and r_x = true.
    Preconditions: For each of two inputs x and y, len(x) is between 1 and 100000 inclusive and every byte is the ASCII code for 'A' or for 'B'. For a string z, define a(z) as the number of indices i with 1 <= i <= len(z)-2 and z[i-1] = z[i] = z[i+1] = 'A', and b(z) analogously with 'B'. -/
  theorem spec_7 (x y : Slice U8)
      (hxlen : lenBounds x.val) (hxab : allAB x.val)
      (hylen : lenBounds y.val) (hyab : allAB y.val)
      (ha : tripleCount x.val codeA ≥ tripleCount y.val codeA)
      (hb : tripleCount x.val codeB ≤ tripleCount y.val codeB)
      (ry : Bool) (hy : winner_of_game y = ok ry) (hry : ry = true) :
      ∃ rx : Bool, winner_of_game x = ok rx ∧ rx = true := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (x y : Slice U8)
        (hxlen : lenBounds x.val) (hxab : allAB x.val)
        (hylen : lenBounds y.val) (hyab : allAB y.val)
        (ha : tripleCount x.val codeA ≥ tripleCount y.val codeA)
        (hb : tripleCount x.val codeB ≤ tripleCount y.val codeB)
        (ry : Bool) (hy : winner_of_game y = ok ry) (hry : ry = true), ∃ rx : Bool, winner_of_game x = ok rx ∧ rx = true) := by
    sorry

  /-- Whenever winner_of_game(colors) returns true, there exists an index i with 1 <= i <= n-2 such that colors[i-1] = colors[i] = colors[i+1] = 'A'.
    Preconditions: Let n = len(colors). 1 <= n <= 100000, and every colors[i] is the ASCII code for 'A' or for 'B'. -/
  theorem spec_8 (colors : Slice U8) (hlen : lenBounds colors.val) (hab : allAB colors.val)
      (hwin : winner_of_game colors = ok true) :
      ∃ i : Nat, 1 ≤ i ∧ i ≤ colors.val.length - 2 ∧ windowAt colors.val i codeA := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (colors : Slice U8) (hlen : lenBounds colors.val) (hab : allAB colors.val)
        (hwin : winner_of_game colors = ok true), ∃ i : Nat, 1 ≤ i ∧ i ≤ colors.val.length - 2 ∧ windowAt colors.val i codeA) := by
    sorry

  /-- winner_of_game(colors) returns a result r, and r = true if and only if colors[0] = colors[1] = colors[2] = 'A'.
    Preconditions: len(colors) = 3, and every colors[i] is the ASCII code for 'A' or for 'B'. -/
  theorem spec_9 (colors : Slice U8) (hlen : colors.val.length = 3) (hab : allAB colors.val) :
      ∃ r : Bool, winner_of_game colors = ok r ∧
        (r = true ↔ colors.val[0]? = some codeA ∧ colors.val[1]? = some codeA ∧
          colors.val[2]? = some codeA) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (colors : Slice U8) (hlen : colors.val.length = 3) (hab : allAB colors.val), ∃ r : Bool, winner_of_game colors = ok r ∧
          (r = true ↔ colors.val[0]? = some codeA ∧ colors.val[1]? = some codeA ∧
            colors.val[2]? = some codeA)) := by
    sorry

  /-- If winner_of_game(colors) returns false and a > 0, then b > 0.
    Preconditions: Let n = len(colors). 1 <= n <= 100000, and every colors[i] is the ASCII code for 'A' or for 'B'. Let a be the number of indices i with 1 <= i <= n-2 and colors[i-1] = colors[i] = colors[i+1] = 'A', and b be the analogous count for 'B'. -/
  theorem spec_10 (colors : Slice U8) (hlen : lenBounds colors.val) (hab : allAB colors.val)
      (hlose : winner_of_game colors = ok false) (ha : tripleCount colors.val codeA > 0) :
      tripleCount colors.val codeB > 0 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (colors : Slice U8) (hlen : lenBounds colors.val) (hab : allAB colors.val)
        (hlose : winner_of_game colors = ok false) (ha : tripleCount colors.val codeA > 0), tripleCount colors.val codeB > 0) := by
    sorry

  end AegisSpec.WinnerOfGame
