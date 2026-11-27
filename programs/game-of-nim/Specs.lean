import Aegis.NimGame.Code.Funs

/-!
# Specifications of `Aegis.NimGame.nim_game`

LeetCode problem `game-of-nim`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.NimGame

  abbrev I64Slice := Aeneas.Std.Slice Aeneas.Std.I64

  def xorInt (a b : Int) : Int := Int.ofNat (a.toNat ^^^ b.toNat)

  def xorList (l : List Int) : Int := l.foldl xorInt 0

  def sliceVals (piles : I64Slice) : List Int := piles.val.map (fun x => x.val)

  def sliceXor (piles : I64Slice) : Int := xorList (sliceVals piles)

  def setAt : List Int → Nat → Int → List Int
    | [], _, _ => []
    | _ :: xs, 0, v => v :: xs
    | x :: xs, n + 1, v => x :: setAt xs n v

  def eraseIdx : List Int → Nat → List Int
    | [], _ => []
    | _ :: xs, 0 => xs
    | x :: xs, n + 1 => x :: eraseIdx xs n

  def countOcc (v : Int) : List Int → Nat
    | [] => 0
    | x :: xs => if x = v then countOcc v xs + 1 else countOcc v xs

  /-- Whenever the function returns a result r, r is true if and only if the bitwise exclusive-or (XOR) of all n entries piles[0], ..., piles[n-1] is nonzero.
    Preconditions: Let n = len(piles). The preconditions are: 1 <= n <= 7, and for every i with 0 <= i < n, 1 <= piles[i] <= 7. -/
  theorem spec_1 (piles : I64Slice)
      (h_n_ge : 1 ≤ piles.val.length)
      (h_n_le : piles.val.length ≤ 7)
      (h_bounds : ∀ (i : Nat) (hi : i < piles.val.length),
        1 ≤ (piles.val[i]'hi).val ∧ (piles.val[i]'hi).val ≤ 7) :
      ∀ r, Aegis.NimGame.nim_game piles = ok r → (r = true ↔ sliceXor piles ≠ 0) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (piles : I64Slice)
        (h_n_ge : 1 ≤ piles.val.length)
        (h_n_le : piles.val.length ≤ 7)
        (h_bounds : ∀ (i : Nat) (hi : i < piles.val.length),
          1 ≤ (piles.val[i]'hi).val ∧ (piles.val[i]'hi).val ≤ 7), ∀ r, Aegis.NimGame.nim_game piles = ok r → (r = true ↔ sliceXor piles ≠ 0)) := by
    sorry

  /-- The function returns a result (some Bool); it does not fail by panic, integer overflow, or out-of-bounds access.
    Preconditions: Let n = len(piles). The preconditions are: 1 <= n <= 7, and for every i with 0 <= i < n, 1 <= piles[i] <= 7. -/
  theorem spec_2 (piles : I64Slice)
      (h_n_ge : 1 ≤ piles.val.length)
      (h_n_le : piles.val.length ≤ 7)
      (h_bounds : ∀ (i : Nat) (hi : i < piles.val.length),
        1 ≤ (piles.val[i]'hi).val ∧ (piles.val[i]'hi).val ≤ 7) :
      ∃ r : Bool, Aegis.NimGame.nim_game piles = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (piles : I64Slice)
        (h_n_ge : 1 ≤ piles.val.length)
        (h_n_le : piles.val.length ≤ 7)
        (h_bounds : ∀ (i : Nat) (hi : i < piles.val.length),
          1 ≤ (piles.val[i]'hi).val ∧ (piles.val[i]'hi).val ≤ 7), ∃ r : Bool, Aegis.NimGame.nim_game piles = ok r) := by
    sorry

  /-- Whenever nim_game(piles) returns r and nim_game(q) returns rq, r = rq.
    Preconditions: Let n = len(piles). The preconditions are: 1 <= n <= 7; for every i with 0 <= i < n, 1 <= piles[i] <= 7; q is a sequence of length n; for every i with 0 <= i < n, 1 <= q[i] <= 7; and q is a permutation of piles (for every integer v, the number of occurrences of v in q equals the number of occurrences of v in piles). -/
  theorem spec_3 (piles q : I64Slice)
      (h_n_ge : 1 ≤ piles.val.length)
      (h_n_le : piles.val.length ≤ 7)
      (h_bounds : ∀ (i : Nat) (hi : i < piles.val.length),
        1 ≤ (piles.val[i]'hi).val ∧ (piles.val[i]'hi).val ≤ 7)
      (h_q_len : q.val.length = piles.val.length)
      (h_q_bounds : ∀ (i : Nat) (hi : i < q.val.length),
        1 ≤ (q.val[i]'hi).val ∧ (q.val[i]'hi).val ≤ 7)
      (h_perm : ∀ v : Int, countOcc v (sliceVals q) = countOcc v (sliceVals piles)) :
      ∀ r rq, Aegis.NimGame.nim_game piles = ok r → Aegis.NimGame.nim_game q = ok rq →
        r = rq := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (piles q : I64Slice)
        (h_n_ge : 1 ≤ piles.val.length)
        (h_n_le : piles.val.length ≤ 7)
        (h_bounds : ∀ (i : Nat) (hi : i < piles.val.length),
          1 ≤ (piles.val[i]'hi).val ∧ (piles.val[i]'hi).val ≤ 7)
        (h_q_len : q.val.length = piles.val.length)
        (h_q_bounds : ∀ (i : Nat) (hi : i < q.val.length),
          1 ≤ (q.val[i]'hi).val ∧ (q.val[i]'hi).val ≤ 7)
        (h_perm : ∀ v : Int, countOcc v (sliceVals q) = countOcc v (sliceVals piles)), ∀ r rq, Aegis.NimGame.nim_game piles = ok r → Aegis.NimGame.nim_game q = ok rq →
          r = rq) := by
    sorry

  /-- Whenever nim_game(B) returns rB and nim_game(piles) returns rP, rB = rP.
    Preconditions: Let B be a sequence and x an integer. The preconditions are: 1 <= len(B) <= 5; for every k with 0 <= k < len(B), 1 <= B[k] <= 7; 1 <= x <= 7; and piles is the concatenation of B followed by two copies of x, so len(piles) = len(B) + 2. -/
  theorem spec_4 (B piles : I64Slice) (x : Int)
      (h_B_n_ge : 1 ≤ B.val.length)
      (h_B_n_le : B.val.length ≤ 5)
      (h_B_bounds : ∀ (k : Nat) (hk : k < B.val.length),
        1 ≤ (B.val[k]'hk).val ∧ (B.val[k]'hk).val ≤ 7)
      (h_x_ge : 1 ≤ x)
      (h_x_le : x ≤ 7)
      (h_piles : sliceVals piles = sliceVals B ++ [x, x]) :
      ∀ rB rP, Aegis.NimGame.nim_game B = ok rB → Aegis.NimGame.nim_game piles = ok rP →
        rB = rP := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (B piles : I64Slice) (x : Int)
        (h_B_n_ge : 1 ≤ B.val.length)
        (h_B_n_le : B.val.length ≤ 5)
        (h_B_bounds : ∀ (k : Nat) (hk : k < B.val.length),
          1 ≤ (B.val[k]'hk).val ∧ (B.val[k]'hk).val ≤ 7)
        (h_x_ge : 1 ≤ x)
        (h_x_le : x ≤ 7)
        (h_piles : sliceVals piles = sliceVals B ++ [x, x]), ∀ rB rP, Aegis.NimGame.nim_game B = ok rB → Aegis.NimGame.nim_game piles = ok rP →
          rB = rP) := by
    sorry

  /-- Whenever the function returns a result r and r is true, there exists an index i with 0 <= i < n and an integer v with 0 <= v < piles[i] such that, letting updated be the sequence obtained from piles by replacing piles[i] with v, the XOR of all entries of updated is zero.
    Preconditions: Let n = len(piles). The preconditions are: 1 <= n <= 7, and for every i with 0 <= i < n, 1 <= piles[i] <= 7. -/
  theorem spec_5 (piles : I64Slice)
      (h_n_ge : 1 ≤ piles.val.length)
      (h_n_le : piles.val.length ≤ 7)
      (h_bounds : ∀ (i : Nat) (hi : i < piles.val.length),
        1 ≤ (piles.val[i]'hi).val ∧ (piles.val[i]'hi).val ≤ 7) :
      ∀ r, Aegis.NimGame.nim_game piles = ok r → r = true →
        ∃ (i : Nat) (hi : i < piles.val.length) (v : Int),
          0 ≤ v ∧ v < (piles.val[i]'hi).val ∧
            xorList (setAt (sliceVals piles) i v) = 0 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (piles : I64Slice)
        (h_n_ge : 1 ≤ piles.val.length)
        (h_n_le : piles.val.length ≤ 7)
        (h_bounds : ∀ (i : Nat) (hi : i < piles.val.length),
          1 ≤ (piles.val[i]'hi).val ∧ (piles.val[i]'hi).val ≤ 7), ∀ r, Aegis.NimGame.nim_game piles = ok r → r = true →
          ∃ (i : Nat) (hi : i < piles.val.length) (v : Int),
            0 ≤ v ∧ v < (piles.val[i]'hi).val ∧
              xorList (setAt (sliceVals piles) i v) = 0) := by
    sorry

  /-- Whenever the function returns a result r and r is false, for every index i with 0 <= i < n and every integer v with 0 <= v < piles[i], letting updated be the sequence obtained from piles by replacing piles[i] with v, the XOR of all entries of updated is nonzero.
    Preconditions: Let n = len(piles). The preconditions are: 1 <= n <= 7, and for every i with 0 <= i < n, 1 <= piles[i] <= 7. -/
  theorem spec_6 (piles : I64Slice)
      (h_n_ge : 1 ≤ piles.val.length)
      (h_n_le : piles.val.length ≤ 7)
      (h_bounds : ∀ (i : Nat) (hi : i < piles.val.length),
        1 ≤ (piles.val[i]'hi).val ∧ (piles.val[i]'hi).val ≤ 7) :
      ∀ r, Aegis.NimGame.nim_game piles = ok r → r = false →
        ∀ (i : Nat) (hi : i < piles.val.length) (v : Int),
          0 ≤ v → v < (piles.val[i]'hi).val →
            xorList (setAt (sliceVals piles) i v) ≠ 0 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (piles : I64Slice)
        (h_n_ge : 1 ≤ piles.val.length)
        (h_n_le : piles.val.length ≤ 7)
        (h_bounds : ∀ (i : Nat) (hi : i < piles.val.length),
          1 ≤ (piles.val[i]'hi).val ∧ (piles.val[i]'hi).val ≤ 7), ∀ r, Aegis.NimGame.nim_game piles = ok r → r = false →
          ∀ (i : Nat) (hi : i < piles.val.length) (v : Int),
            0 ≤ v → v < (piles.val[i]'hi).val →
              xorList (setAt (sliceVals piles) i v) ≠ 0) := by
    sorry

  /-- Whenever the function returns a result r, r is true.
    Preconditions: Let n = len(piles). The preconditions are: 1 <= n <= 7; for every k with 0 <= k < n, 1 <= piles[k] <= 7; and there exists an index i with 0 <= i < n such that piles[i] is strictly greater than the XOR of all entries piles[j] with j != i (the XOR of the empty set in the case n = 1 is 0). -/
  theorem spec_7 (piles : I64Slice)
      (h_n_ge : 1 ≤ piles.val.length)
      (h_n_le : piles.val.length ≤ 7)
      (h_bounds : ∀ (k : Nat) (hk : k < piles.val.length),
        1 ≤ (piles.val[k]'hk).val ∧ (piles.val[k]'hk).val ≤ 7)
      (h_witness : ∃ (i : Nat) (hi : i < piles.val.length),
        xorList (eraseIdx (sliceVals piles) i) < (piles.val[i]'hi).val) :
      ∀ r, Aegis.NimGame.nim_game piles = ok r → r = true := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (piles : I64Slice)
        (h_n_ge : 1 ≤ piles.val.length)
        (h_n_le : piles.val.length ≤ 7)
        (h_bounds : ∀ (k : Nat) (hk : k < piles.val.length),
          1 ≤ (piles.val[k]'hk).val ∧ (piles.val[k]'hk).val ≤ 7)
        (h_witness : ∃ (i : Nat) (hi : i < piles.val.length),
          xorList (eraseIdx (sliceVals piles) i) < (piles.val[i]'hi).val), ∀ r, Aegis.NimGame.nim_game piles = ok r → r = true) := by
    sorry

  end AegisSpec.NimGame
